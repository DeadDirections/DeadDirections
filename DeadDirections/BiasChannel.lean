/-
  The bias-augmented dead channel (theory paper, thm:bridge_bias).

  Two machine-checked cores. For (P1), the biased chain is affine with
  linear part exactly the weight product: differences of chain values
  satisfy chain(x) − chain(y) = W^m (x − y), so the backward chain
  never sees the biases and the dead ladder t^m is untouched, clauses
  (a) and (c). The dead coordinate itself has the closed form
  t^m·x + Σ_j t^{q_j + (m−1−j)}; at the symmetric joint case q ≡ 1 the
  forward dead moment is capped at leading rate 2 with coefficient 1
  for every depth m ≥ 2, against the bias-free 2m: the A-side capping
  that breaks the bias-free A·G layer-invariance.

  For (P3), a positive dead bias opens the deep gates: from any
  non-negative activation the biased ReLU chain has derivative exactly
  t^m, with no survival factor, and from the Gaussian input the
  full-chain derivative is t^m·1_{x > −1}, one gate in total, at
  layer 1. Its mass ∫ 1_{x>−1} φ₀ = Φ(1) strictly exceeds the
  bias-free 1/2: the constant grows, the rate stands.
-/
import DeadDirections.DeepLinearBridge
import DeadDirections.ReluChannel
import DeadDirections.SwigluChannel

namespace DeadDirections

open MeasureTheory Filter Topology

/-! ### The (P1) affine chain -/

section AffineChain

variable {n : ℕ}

/-- The bias-augmented canonical chain: layer j applies the canonical
    weight and adds the bias t^{q j} on the dead coordinate. -/
noncomputable def affChain (n : ℕ) (t : ℝ) (q : ℕ → ℕ) :
    ℕ → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)
  | 0 => id
  | m + 1 => fun x => (canonicalLayer n t).mulVec (affChain n t q m x)
      + Pi.single (Fin.last n) (t ^ q m)

/-- The linear part of the biased chain is the weight product: the
    biases cancel in differences, so the backward chain never sees
    them. thm:bridge_bias (a)/(c): the ladder is bias-independent. -/
lemma affChain_sub (t : ℝ) (q : ℕ → ℕ) (m : ℕ)
    (x y : Fin (n + 1) → ℝ) :
    affChain n t q m x - affChain n t q m y
      = (canonicalLayer n t ^ m).mulVec (x - y) := by
  induction m with
  | zero =>
    rw [pow_zero]
    exact (Matrix.one_mulVec (x - y)).symm
  | succ k ih =>
    have hx : affChain n t q (k + 1) x
        = (canonicalLayer n t).mulVec (affChain n t q k x)
          + Pi.single (Fin.last n) (t ^ q k) := rfl
    have hy : affChain n t q (k + 1) y
        = (canonicalLayer n t).mulVec (affChain n t q k y)
          + Pi.single (Fin.last n) (t ^ q k) := rfl
    rw [hx, hy, add_sub_add_right_eq_sub, ← Matrix.mulVec_sub, ih,
      Matrix.mulVec_mulVec, ← pow_succ']

/-- The dead coordinate of one canonical application. -/
lemma canonicalLayer_mulVec_last (t : ℝ) (v : Fin (n + 1) → ℝ) :
    (canonicalLayer n t).mulVec v (Fin.last n) = t * v (Fin.last n) := by
  have h := canonicalLayer_pow_mulVec_last (n := n) t 1 v
  rwa [pow_one, pow_one] at h

/-- The dead coordinate of the biased chain in closed form: the weight
    ladder plus one bias term per layer, each damped by the downstream
    weights. -/
lemma affChain_dead_eq (t : ℝ) (q : ℕ → ℕ) (m : ℕ)
    (x : Fin (n + 1) → ℝ) :
    affChain n t q m x (Fin.last n)
      = t ^ m * x (Fin.last n)
        + ∑ j ∈ Finset.range m, t ^ (q j + (m - 1 - j)) := by
  induction m with
  | zero => simp [affChain]
  | succ k ih =>
    have hstep : affChain n t q (k + 1) x
        = (canonicalLayer n t).mulVec (affChain n t q k x)
          + Pi.single (Fin.last n) (t ^ q k) := rfl
    rw [hstep, Pi.add_apply, canonicalLayer_mulVec_last, ih,
      Pi.single_eq_same, Finset.sum_range_succ]
    have hsum : t * ∑ j ∈ Finset.range k, t ^ (q j + (k - 1 - j))
        = ∑ j ∈ Finset.range k, t ^ (q j + (k + 1 - 1 - j)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : j < k := Finset.mem_range.mp hj
      rw [← pow_succ']
      congr 1
      omega
    have hlast : (t : ℝ) ^ (q k + (k + 1 - 1 - k)) = t ^ q k := by
      congr 1
      omega
    rw [hlast]
    calc t * (t ^ k * x (Fin.last n)
          + ∑ j ∈ Finset.range k, t ^ (q j + (k - 1 - j))) + t ^ q k
        = t ^ (k + 1) * x (Fin.last n)
          + (t * ∑ j ∈ Finset.range k, t ^ (q j + (k - 1 - j))
            + t ^ q k) := by ring
      _ = t ^ (k + 1) * x (Fin.last n)
          + (∑ j ∈ Finset.range k, t ^ (q j + (k + 1 - 1 - j))
            + t ^ q k) := by rw [hsum]

/-- The symmetric joint case q ≡ 1: the bias sum telescopes to the
    geometric tail Σ_{i=1..m} t^i, written top-down. -/
lemma affChain_dead_uniform (t : ℝ) (m : ℕ) (x : Fin (n + 1) → ℝ) :
    affChain n t (fun _ => 1) m x (Fin.last n)
      = t ^ m * x (Fin.last n) + ∑ j ∈ Finset.range m, t ^ (m - j) := by
  rw [affChain_dead_eq]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j < m := Finset.mem_range.mp hj
  congr 1
  omega

/-- The Gaussian second moment of an affine function of the input:
    the cross term dies with the first moment. -/
lemma integral_affine_sq_gaussMeasure (a s : ℝ) :
    ∫ x, (a * x + s) ^ 2 ∂gaussMeasure = a ^ 2 + s ^ 2 := by
  have hx1 : Integrable (fun x : ℝ => x) gaussMeasure := by
    have h := integrable_pow_gaussMeasure 1
    exact h.congr (Filter.Eventually.of_forall fun x => by simp)
  have hx2 : Integrable (fun x : ℝ => x ^ 2) gaussMeasure :=
    integrable_sq_gaussMeasure
  have hint1 : ∫ x, x ∂gaussMeasure = 0 := by
    rw [integral_gaussMeasure]
    exact integral_id_mul_gaussDensity_zero
  have hfun : (fun x : ℝ => (a * x + s) ^ 2)
      = fun x => a ^ 2 * x ^ 2 + (2 * a * s) * x + s ^ 2 := by
    funext x
    ring
  have hI1 : Integrable (fun x : ℝ => a ^ 2 * x ^ 2) gaussMeasure :=
    hx2.const_mul (a ^ 2)
  have hI2 : Integrable (fun x : ℝ => 2 * a * s * x) gaussMeasure :=
    hx1.const_mul (2 * a * s)
  have hI12 : Integrable (fun x : ℝ => a ^ 2 * x ^ 2 + 2 * a * s * x)
      gaussMeasure := by
    have h := hI1.add hI2
    exact h.congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.add_apply])
  rw [hfun, integral_add hI12 (integrable_const _),
    integral_add hI1 hI2, integral_const_mul, integral_const_mul,
    integral_sq_gaussMeasure, hint1, integral_const]
  simp [measureReal_def]

/-- thm:bridge_bias, forward cap at the symmetric joint case: for
    every depth m ≥ 2 the dead forward moment carries leading rate 2
    with coefficient 1, against the bias-free rate 2m. The bias term
    dominates the weight ladder at every depth. -/
theorem aff_forward_cap (m : ℕ) (hm : 2 ≤ m) :
    HasLeadingRate
      (fun t => ∫ x, (t ^ m * x
        + ∑ j ∈ Finset.range m, t ^ (m - j)) ^ 2 ∂gaussMeasure)
      2 1 := by
  apply hasLeadingRate_of_expansion
    (R := fun t => (t ^ (2 * m)
      + (∑ j ∈ Finset.range m, t ^ (m - j)) ^ 2) - t ^ 2)
    (M := (m : ℝ) ^ 2)
  · filter_upwards [] with t
    rw [integral_affine_sq_gaussMeasure, ← pow_mul, Nat.mul_comm m 2]
    ring
  · filter_upwards [eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with t ht0' ht1'
    have ht0 : (0:ℝ) < t := ht0'
    have ht1 : t ≤ 1 := ht1'.le
    set s := ∑ j ∈ Finset.range m, t ^ (m - j) with hs
    -- peel the j = m − 1 term, which is t itself
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have hspeel : s = (∑ j ∈ Finset.range (k + 1), t ^ (k + 2 - j)) + t := by
      rw [hs, Finset.sum_range_succ,
        show k + 2 - (k + 1) = 1 from by omega, pow_one]
    set r := ∑ j ∈ Finset.range (k + 1), t ^ (k + 2 - j) with hr
    have hrnn : 0 ≤ r := Finset.sum_nonneg fun j _ => (pow_pos ht0 _).le
    have hrle : r ≤ (k + 1 : ℝ) * t ^ 2 := by
      rw [hr]
      calc ∑ j ∈ Finset.range (k + 1), t ^ (k + 2 - j)
          ≤ ∑ _j ∈ Finset.range (k + 1), t ^ 2 :=
            Finset.sum_le_sum fun j hj => by
              have hjk : j < k + 1 := Finset.mem_range.mp hj
              exact pow_le_pow_of_le_one ht0.le ht1 (by omega)
        _ = (k + 1 : ℝ) * t ^ 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have hsle : s ≤ (k + 2 : ℝ) * t := by
      rw [hspeel]
      have h1 : r ≤ (k + 1 : ℝ) * t := by
        calc r ≤ (k + 1 : ℝ) * t ^ 2 := hrle
          _ ≤ (k + 1 : ℝ) * t := by
              nlinarith [ht0.le, ht1]
      linarith
    have hpow : t ^ (2 * (k + 2)) ≤ t ^ 3 :=
      pow_le_pow_of_le_one ht0.le ht1 (by omega)
    have hkey : (t ^ (2 * (k + 2)) + s ^ 2) - t ^ 2
        = t ^ (2 * (k + 2)) + r * (s + t) := by
      rw [hspeel]
      ring
    rw [hkey]
    have hbound : r * (s + t) ≤ ((k + 1 : ℝ) * (k + 3)) * t ^ 3 := by
      have hst : s + t ≤ (k + 3 : ℝ) * t := by linarith [hsle]
      calc r * (s + t) ≤ ((k + 1 : ℝ) * t ^ 2) * ((k + 3 : ℝ) * t) := by
            have h1 : (0:ℝ) ≤ s + t := by
              rw [hspeel]
              positivity
            exact mul_le_mul hrle hst h1 (by positivity)
        _ = ((k + 1 : ℝ) * (k + 3)) * t ^ 3 := by ring
    have hnn : 0 ≤ t ^ (2 * (k + 2)) + r * (s + t) := by
      have : (0:ℝ) ≤ s + t := by
        rw [hspeel]
        positivity
      positivity
    rw [abs_of_nonneg hnn]
    have hm2 : ((k + 2 : ℕ) : ℝ) ^ 2 = (k + 1 : ℝ) * (k + 3) + 1 := by
      push_cast
      ring
    calc t ^ (2 * (k + 2)) + r * (s + t)
        ≤ t ^ 3 + ((k + 1 : ℝ) * (k + 3)) * t ^ 3 := by
          linarith [hpow, hbound]
      _ = ((k + 1 : ℝ) * (k + 3) + 1) * t ^ (2 + 1) := by ring
      _ = ((k + 2 : ℕ) : ℝ) ^ 2 * t ^ (2 + 1) := by rw [hm2]

end AffineChain

/-! ### The (P3) biased channel -/

section BiasedRelu

/-- The biased ReLU layer at the symmetric joint case q = 1: weight t
    and bias t on the dead coordinate. -/
noncomputable def biasedRelu (t z : ℝ) : ℝ := relu (t * z + t)

noncomputable def biasedChain (t : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  (biasedRelu t)^[m] x

lemma biasedRelu_nonneg (t z : ℝ) : 0 ≤ biasedRelu t z :=
  relu_nonneg _

lemma biasedChain_nonneg (t : ℝ) (m : ℕ) (x : ℝ) (hm : 1 ≤ m) :
    0 ≤ biasedChain t m x := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  unfold biasedChain
  rw [Function.iterate_succ_apply']
  exact biasedRelu_nonneg _ _

/-- The gate is open at every non-negative input: the bias keeps the
    pre-activation strictly positive, so the layer is locally affine
    with derivative exactly t. No survival factor. -/
lemma hasDerivAt_biasedRelu_pos {t : ℝ} (ht : 0 < t) {z : ℝ}
    (hz : -1 < z) : HasDerivAt (biasedRelu t) t z := by
  have haff : HasDerivAt (fun y : ℝ => t * y + t) t z := by
    have h := (hasDerivAt_id z).const_mul t
    rw [mul_one] at h
    exact h.add_const t
  refine haff.congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds hz] with y hy
  unfold biasedRelu relu
  rw [max_eq_left (by nlinarith)]

lemma hasDerivAt_biasedRelu_neg {t : ℝ} (ht : 0 < t) {z : ℝ}
    (hz : z < -1) : HasDerivAt (biasedRelu t) 0 z := by
  have hconst : HasDerivAt (fun _ : ℝ => (0:ℝ)) 0 z := hasDerivAt_const z 0
  refine hconst.congr_of_eventuallyEq ?_
  filter_upwards [eventually_lt_nhds hz] with y hy
  unfold biasedRelu relu
  rw [max_eq_right (by nlinarith)]

/-- thm:bridge_bias (P3), deep layers: from any non-negative
    activation the m-layer biased chain has derivative exactly t^m.
    Every gate is open, and the bias-free survival factor 1/2 is
    gone: the constant doubles, the rate stands. -/
theorem biasedChain_deriv_of_nonneg {t : ℝ} (ht : 0 < t) (m : ℕ)
    {h : ℝ} (hh : 0 ≤ h) :
    HasDerivAt (biasedChain t m) (t ^ m) h := by
  induction m with
  | zero =>
    unfold biasedChain
    simpa using hasDerivAt_id' h
  | succ k ih =>
    have hfun : biasedChain t (k + 1) = biasedRelu t ∘ biasedChain t k := by
      funext y
      unfold biasedChain
      rw [Function.iterate_succ_apply']
      rfl
    rw [hfun]
    have hck : 0 ≤ biasedChain t k h := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        exact hh
      · exact biasedChain_nonneg t k h hk
    have houter := hasDerivAt_biasedRelu_pos ht
      (show -1 < biasedChain t k h by linarith)
    have hcomp := houter.comp h ih
    rw [show t * t ^ k = t ^ (k + 1) from (pow_succ' t k).symm] at hcomp
    exact hcomp

/-- thm:bridge_bias (P3), layer 1: from the Gaussian input the
    full-chain derivative is t^m times the single layer-1 gate
    1_{x > −1}. One gate in the whole chain. -/
theorem biasedChain_deriv {t : ℝ} (ht : 0 < t) (m : ℕ) (hm : 1 ≤ m)
    {x : ℝ} (hx : x ≠ -1) :
    HasDerivAt (biasedChain t m) (t ^ m * reluGate (x + 1)) x := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · -- the layer-1 gate is closed; the chain is locally constant
    have hg : reluGate (x + 1) = 0 := if_neg (by
      simp only [not_lt]
      linarith)
    rw [hg, mul_zero]
    have hchain : ∀ᶠ y in 𝓝 x, biasedChain t (k + 1) y
        = biasedChain t (k + 1) x := by
      filter_upwards [eventually_lt_nhds hneg] with y hy
      have h1 : ∀ z : ℝ, z < -1 → biasedRelu t z = 0 := fun z hz => by
        unfold biasedRelu relu
        rw [max_eq_right (by nlinarith)]
      unfold biasedChain
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        h1 y hy, h1 x hneg]
    exact (hasDerivAt_const x (biasedChain t (k + 1) x)).congr_of_eventuallyEq
      (by filter_upwards [hchain] with y hy; exact hy)
  · -- the layer-1 gate is open; compose the open first layer with the
    -- all-gates-open deep chain
    have hg : reluGate (x + 1) = 1 := if_pos (by linarith)
    rw [hg, mul_one]
    have hfun : biasedChain t (k + 1) = biasedChain t k ∘ biasedRelu t := by
      funext y
      unfold biasedChain
      rw [Function.iterate_succ_apply]
      rfl
    rw [hfun]
    have h1 := hasDerivAt_biasedRelu_pos ht hpos
    have hnn : 0 ≤ biasedRelu t x := biasedRelu_nonneg t x
    have hdeep := biasedChain_deriv_of_nonneg ht k hnn
    have hcomp := hdeep.comp x h1
    rw [show t ^ k * t = t ^ (k + 1) from (pow_succ t k).symm] at hcomp
    exact hcomp

/-- The layer-1 gate has Gaussian mass Φ(1): the backward second
    moment of the biased chain is t^{2m}·∫1_{x>−1}φ₀ exactly. -/
theorem biased_backward_moment (t : ℝ) (m : ℕ) :
    ∫ x, (t ^ m * reluGate (x + 1)) ^ 2 * gaussDensity x 0 1
      = t ^ (2 * m) * ∫ x, reluGate (x + 1) * gaussDensity x 0 1 := by
  have hfun : ∀ x : ℝ, (t ^ m * reluGate (x + 1)) ^ 2 * gaussDensity x 0 1
      = t ^ (2 * m) * (reluGate (x + 1) * gaussDensity x 0 1) := by
    intro x
    rw [mul_pow, reluGate_sq,
      show (t ^ m) ^ 2 = t ^ (2 * m) from by
        rw [← pow_mul, Nat.mul_comm]]
    ring
  simp only [hfun]
  rw [integral_const_mul]

/-- The biased gate mass strictly exceeds the bias-free 1/2: opening
    the gate at −1 instead of 0 adds the Gaussian mass of (−1, 0]. -/
theorem biased_gate_mass_gt_half :
    1 / 2 < ∫ x, reluGate (x + 1) * gaussDensity x 0 1 := by
  have hsplit : ∀ x : ℝ, reluGate (x + 1) * gaussDensity x 0 1
      = reluGate x * gaussDensity x 0 1
        + Set.indicator (Set.Ioc (-1 : ℝ) 0)
            (fun y => gaussDensity y 0 1) x := by
    intro x
    unfold reluGate
    rcases le_or_gt x (-1) with h1 | h1
    · rw [if_neg (by linarith), Set.indicator_of_notMem (by
        simp only [Set.mem_Ioc, not_and_or, not_lt]
        left
        linarith), if_neg (by linarith)]
      ring
    · rcases le_or_gt x 0 with h2 | h2
      · rw [if_pos (by linarith), if_neg (by linarith),
          Set.indicator_of_mem (by simp only [Set.mem_Ioc]; exact ⟨h1, h2⟩)]
        ring
      · rw [if_pos (by linarith), if_pos h2,
          Set.indicator_of_notMem (by
            simp only [Set.mem_Ioc, not_and_or, not_le]
            right
            exact h2)]
        ring
  have hIioc : Integrable (Set.indicator (Set.Ioc (-1 : ℝ) 0)
      (fun y => gaussDensity y 0 1)) :=
    (integrable_gaussDensity 0).indicator measurableSet_Ioc
  have hIgate : Integrable (fun x => reluGate x * gaussDensity x 0 1) := by
    refine (integrable_gaussDensity 0).mono'
      ?_ (Filter.Eventually.of_forall fun x => ?_)
    · have hind : (fun x => reluGate x * gaussDensity x 0 1)
          = Set.indicator (Set.Ioi (0:ℝ)) (fun y => gaussDensity y 0 1) := by
        funext x
        unfold reluGate
        rcases le_or_gt x 0 with hx | hx
        · rw [if_neg (not_lt.mpr hx),
            Set.indicator_of_notMem (by simpa using hx)]
          ring
        · rw [if_pos hx, Set.indicator_of_mem (by simpa using hx)]
          ring
      rw [hind]
      exact ((integrable_gaussDensity 0).indicator
        measurableSet_Ioi).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      unfold reluGate
      rcases le_or_gt x 0 with hx | hx
      · rw [if_neg (not_lt.mpr hx)]
        simp [(gaussDensity_pos x 0).le]
      · rw [if_pos hx, one_mul, abs_of_nonneg (gaussDensity_pos x 0).le]
  rw [show (fun x => reluGate (x + 1) * gaussDensity x 0 1)
      = fun x => reluGate x * gaussDensity x 0 1
        + Set.indicator (Set.Ioc (-1 : ℝ) 0)
            (fun y => gaussDensity y 0 1) x from funext hsplit,
    integral_add hIgate hIioc, integral_reluGate_gaussDensity,
    integral_indicator measurableSet_Ioc]
  have hmass : (0:ℝ) < ∫ y in Set.Ioc (-1 : ℝ) 0, gaussDensity y 0 1 := by
    have hlow : ∀ y ∈ Set.Ioc (-1 : ℝ) 0,
        gaussDensity (-1) 0 1 ≤ gaussDensity y 0 1 := by
      intro y hy
      simp only [Set.mem_Ioc] at hy
      rw [gaussDensity_one_eq, gaussDensity_one_eq]
      have hexp : Real.exp (-(1/2 : ℝ) * ((-1) - 0) ^ 2)
          ≤ Real.exp (-(1/2 : ℝ) * (y - 0) ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hy.1, hy.2]
      have hc : (0:ℝ) < (2 * Real.pi) ^ (-(1:ℝ)/2) := by
        apply Real.rpow_pos_of_pos
        positivity
      exact mul_le_mul_of_nonneg_left hexp hc.le
    have hconst : ∫ _y in Set.Ioc (-1 : ℝ) 0, gaussDensity (-1) 0 1
        = gaussDensity (-1) 0 1 := by
      rw [setIntegral_const, measureReal_def, Real.volume_Ioc]
      norm_num
    have hmono : ∫ _y in Set.Ioc (-1 : ℝ) 0, gaussDensity (-1) 0 1
        ≤ ∫ y in Set.Ioc (-1 : ℝ) 0, gaussDensity y 0 1 :=
      setIntegral_mono_on (integrable_const _)
        ((integrable_gaussDensity 0).integrableOn)
        measurableSet_Ioc hlow
    rw [hconst] at hmono
    linarith [gaussDensity_pos (-1 : ℝ) 0]
  linarith

end BiasedRelu

end DeadDirections
