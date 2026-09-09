/-
  The cross-entropy output head (theory paper, thm:bridge_ce and
  lem:ce_head).

  The CE replacement for the MSE base case is finite probability
  algebra. Under expected Fisher the conditional covariance of the
  output gradient softmax(z) − e_y is the softmax Hessian
  H = diag(p) − p pᵀ; its quadratic form is the variance of v under p,
  equal to the p-weighted sum of squared deviations from the p-mean,
  so it is non-negative, vanishes exactly on the vectors constant on
  the support of p, kills the ones vector (the logit-shift gauge zero
  of clause (c)), and is positive on {1}^⊥ at full support. The dead
  basis vector splits as its {1}^⊥ projection plus (1/C)·1, the cross
  terms die on the kernel, and the non-degeneracy constant c₀ delivers
  the base case: the dead output entry is at least c₀(1 − 1/C), the
  Θ(1) of clause (b) with c₀ in place of σ^{−2}. The backward
  recursion above the head is loss-independent and lives in the
  channel modules.
-/
import Mathlib.Data.Matrix.Basic
import DeadDirections.DeepLinearBridge

namespace DeadDirections

open Matrix Filter Topology

variable {C : ℕ}

/-- The softmax Hessian at probability vector p: H = diag(p) − p pᵀ. -/
def ceHess (p : Fin C → ℝ) : Matrix (Fin C) (Fin C) ℝ :=
  Matrix.diagonal p - Matrix.vecMulVec p p

/-- The Hessian acts as v ↦ p ⊙ v − (Σ p v)·p. -/
lemma ceHess_mulVec (p v : Fin C → ℝ) (i : Fin C) :
    (ceHess p).mulVec v i = p i * v i - p i * ∑ y, p y * v y := by
  unfold ceHess
  rw [Matrix.sub_mulVec]
  simp only [Pi.sub_apply, Matrix.mulVec_diagonal]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply]
  rw [Finset.sum_congr rfl fun y _ => mul_assoc (p i) (p y) (v y),
    ← Finset.mul_sum]

/-- lem:ce_head, covariance identity: the conditional second moment of
    the output gradient p − e_y under y ~ p is the softmax Hessian,
    entrywise. -/
lemma ceHess_expect (p : Fin C → ℝ) (hsum : ∑ y, p y = 1) (i j : Fin C) :
    ∑ y, p y * ((p i - (Pi.single y 1 : Fin C → ℝ) i)
        * (p j - (Pi.single y 1 : Fin C → ℝ) j))
      = ceHess p i j := by
  have hexp : ∀ y : Fin C,
      p y * ((p i - (Pi.single y 1 : Fin C → ℝ) i)
        * (p j - (Pi.single y 1 : Fin C → ℝ) j))
      = p y * (p i * p j)
        - p i * ((if j = y then (1:ℝ) else 0) * p y)
        - p j * ((if i = y then (1:ℝ) else 0) * p y)
        + p y * ((if i = y then (1:ℝ) else 0)
          * (if j = y then (1:ℝ) else 0)) := by
    intro y
    rw [Pi.single_apply, Pi.single_apply]
    ring
  rw [Finset.sum_congr rfl fun y _ => hexp y, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hA : ∑ y, p y * (p i * p j) = p i * p j := by
    rw [← Finset.sum_mul, hsum, one_mul]
  have hite : ∀ b : Fin C, ∑ y, (if b = y then (1:ℝ) else 0) * p y
      = p b := by
    intro b
    rw [Finset.sum_congr rfl fun y _ =>
      (by by_cases hby : b = y <;> simp [hby] :
        (if b = y then (1:ℝ) else 0) * p y = if b = y then p y else 0),
      Finset.sum_ite_eq]
    simp
  have hB : ∑ y, p i * ((if j = y then (1:ℝ) else 0) * p y)
      = p i * p j := by
    rw [← Finset.mul_sum, hite j]
  have hCsum : ∑ y, p j * ((if i = y then (1:ℝ) else 0) * p y)
      = p j * p i := by
    rw [← Finset.mul_sum, hite i]
  have hD : ∑ y, p y * ((if i = y then (1:ℝ) else 0)
      * (if j = y then (1:ℝ) else 0))
      = if i = j then p i else 0 := by
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl,
        Finset.sum_congr rfl fun y _ => (by
          by_cases hiy : i = y <;> simp [hiy] :
          p y * ((if i = y then (1:ℝ) else 0)
            * (if i = y then (1:ℝ) else 0))
          = if i = y then p y else 0),
        Finset.sum_ite_eq]
      simp
    · rw [if_neg hij]
      refine Finset.sum_eq_zero fun y _ => ?_
      by_cases hiy : i = y
      · rw [if_neg (fun h : j = y => hij (hiy.trans h.symm))]
        ring
      · rw [if_neg hiy]
        ring
  rw [hA, hB, hCsum, hD]
  unfold ceHess
  simp only [Matrix.sub_apply, Matrix.diagonal_apply,
    Matrix.vecMulVec_apply]
  ring

/-- The quadratic form is the variance of v under p. -/
lemma ceHess_quadform (p v : Fin C → ℝ) :
    v ⬝ᵥ (ceHess p).mulVec v
      = ∑ y, p y * v y ^ 2 - (∑ y, p y * v y) ^ 2 := by
  simp only [dotProduct]
  rw [Finset.sum_congr rfl fun i _ => by rw [ceHess_mulVec p v i],
    Finset.sum_congr rfl fun i _ =>
      mul_sub (v i) (p i * v i) (p i * ∑ y, p y * v y),
    Finset.sum_sub_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · rw [Finset.sum_congr rfl fun i _ =>
      (show v i * (p i * ∑ y, p y * v y)
        = p i * v i * ∑ y, p y * v y from by ring),
      ← Finset.sum_mul, sq]

/-- The variance in mean-centered form: the p-weighted sum of squared
    deviations from the p-mean. -/
lemma ceHess_quadform_eq_var (p v : Fin C → ℝ)
    (hsum : ∑ y, p y = 1) :
    v ⬝ᵥ (ceHess p).mulVec v
      = ∑ y, p y * (v y - ∑ z, p z * v z) ^ 2 := by
  rw [ceHess_quadform]
  have hrhs : ∑ y, p y * (v y - ∑ z, p z * v z) ^ 2
      = ∑ y, (p y * v y ^ 2
        - 2 * (∑ z, p z * v z) * (p y * v y)
        + (∑ z, p z * v z) ^ 2 * p y) := by
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hrhs, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hsum]
  ring

/-- The logit-shift gauge zero of thm:bridge_ce (c): the ones vector
    lies in the kernel at every p summing to one. -/
lemma ceHess_mulVec_one (p : Fin C → ℝ) (hsum : ∑ y, p y = 1) :
    (ceHess p).mulVec (fun _ => 1) = 0 := by
  funext i
  rw [ceHess_mulVec]
  simp only [mul_one, Pi.zero_apply]
  rw [hsum]
  ring

/-- The variance is non-negative. -/
lemma ceHess_quadform_nonneg (p v : Fin C → ℝ)
    (hp : ∀ y, 0 ≤ p y) (hsum : ∑ y, p y = 1) :
    0 ≤ v ⬝ᵥ (ceHess p).mulVec v := by
  rw [ceHess_quadform_eq_var p v hsum]
  exact Finset.sum_nonneg fun y _ => mul_nonneg (hp y) (sq_nonneg _)

/-- lem:ce_head, nullspace characterization: the form vanishes exactly
    when v is constant on the support of p. -/
lemma ceHess_quadform_eq_zero_iff (p v : Fin C → ℝ)
    (hp : ∀ y, 0 ≤ p y) (hsum : ∑ y, p y = 1) :
    v ⬝ᵥ (ceHess p).mulVec v = 0
      ↔ ∀ y, p y = 0 ∨ v y = ∑ z, p z * v z := by
  rw [ceHess_quadform_eq_var p v hsum,
    Finset.sum_eq_zero_iff_of_nonneg
      fun y _ => mul_nonneg (hp y) (sq_nonneg _)]
  constructor
  · intro h y
    rcases mul_eq_zero.mp (h y (Finset.mem_univ y)) with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (by nlinarith [sq_nonneg (v y - ∑ z, p z * v z)])
  · intro h y _
    rcases h y with h0 | h0
    · rw [h0, zero_mul]
    · rw [h0, sub_self]
      ring

/-- lem:ce_head, full support: the form is positive on {1}^⊥ away
    from zero, so the kernel is exactly the gauge line. -/
theorem ceHess_posdef_on_perp (p v : Fin C → ℝ)
    (hp : ∀ y, 0 < p y) (hsum : ∑ y, p y = 1)
    (hv0 : ∑ i, v i = 0) (hvne : v ≠ 0) :
    0 < v ⬝ᵥ (ceHess p).mulVec v := by
  rcases (ceHess_quadform_nonneg p v (fun y => (hp y).le)
    hsum).lt_or_eq with h | h
  · exact h
  · exfalso
    have hconst := (ceHess_quadform_eq_zero_iff p v
      (fun y => (hp y).le) hsum).mp h.symm
    have hval : ∀ y, v y = ∑ z, p z * v z := fun y => by
      rcases hconst y with h0 | h0
      · exact absurd h0 (ne_of_gt (hp y))
      · exact h0
    have hS : ∑ z, p z * v z = 0 := by
      have hsv : ∑ i, v i = ∑ _i : Fin C, ∑ z, p z * v z :=
        Finset.sum_congr rfl fun i _ => hval i
      rw [hv0, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at hsv
      rcases Nat.eq_zero_or_pos C with hC | hC
      · exact absurd (funext fun i => absurd (Fin.pos i) (by omega))
          hvne
      · have hCne : ((C:ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hCS : (C:ℝ) * (∑ z, p z * v z) = 0 := by linarith [hsv]
        rcases mul_eq_zero.mp hCS with h0 | h0
        · exact absurd h0 hCne
        · exact h0
    exact hvne (funext fun y => by
      rw [hval y, hS]
      simp)

/-- thm:bridge_ce (b), base case: for any covariance H that kills the
    ones vector on both sides and satisfies the non-degeneracy bound
    c₀ on {1}^⊥, the dead output entry is at least c₀(1 − 1/C). The
    constant c₀ replaces the MSE σ^{−2}. -/
theorem ce_dead_lower {c₀ : ℝ} (H : Matrix (Fin C) (Fin C) ℝ)
    (hC : 0 < C)
    (hker : H.mulVec (fun _ => 1) = 0)
    (hkerL : Matrix.vecMul (fun _ => (1:ℝ)) H = 0)
    (hass : ∀ v : Fin C → ℝ, (∑ i, v i) = 0 →
      c₀ * ∑ i, v i ^ 2 ≤ v ⬝ᵥ H.mulVec v) (h : Fin C) :
    c₀ * (1 - 1 / C)
      ≤ (Pi.single h 1 : Fin C → ℝ) ⬝ᵥ H.mulVec (Pi.single h 1) := by
  have hCne : ((C:ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set w : Fin C → ℝ := fun i => (Pi.single h 1 : Fin C → ℝ) i - 1 / C
    with hw
  have hsingle_sum : ∑ i, (Pi.single h 1 : Fin C → ℝ) i = 1 := by
    rw [Finset.sum_congr rfl fun i _ => Pi.single_apply h 1 i,
      Finset.sum_ite_eq' Finset.univ h fun _ => (1:ℝ)]
    simp
  have hwsum : ∑ i, w i = 0 := by
    rw [hw]
    simp only
    rw [Finset.sum_sub_distrib, hsingle_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div,
      div_self hCne]
    ring
  have hsingle_sq : ∑ i, ((Pi.single h 1 : Fin C → ℝ) i) ^ 2 = 1 := by
    have hterm : ∀ i : Fin C, ((Pi.single h 1 : Fin C → ℝ) i) ^ 2
        = if i = h then (1:ℝ) else 0 := by
      intro i
      rw [Pi.single_apply]
      by_cases hih : i = h <;> simp [hih]
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      Finset.sum_ite_eq' Finset.univ h fun _ => (1:ℝ)]
    simp
  have hwnorm : ∑ i, w i ^ 2 = 1 - 1 / C := by
    rw [hw]
    simp only
    rw [Finset.sum_congr rfl fun i _ =>
      (show ((Pi.single h 1 : Fin C → ℝ) i - 1 / C) ^ 2
        = ((Pi.single h 1 : Fin C → ℝ) i) ^ 2
          - 2 / C * (Pi.single h 1 : Fin C → ℝ) i
          + (1 / C) ^ 2 from by ring),
      Finset.sum_add_distrib, Finset.sum_sub_distrib, hsingle_sq,
      ← Finset.mul_sum, hsingle_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hsplit : (Pi.single h 1 : Fin C → ℝ)
      = w + (1 / C : ℝ) • ((fun _ => (1:ℝ)) : Fin C → ℝ) := by
    funext i
    simp only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    ring
  have hquad : (Pi.single h 1 : Fin C → ℝ) ⬝ᵥ H.mulVec (Pi.single h 1)
      = w ⬝ᵥ H.mulVec w := by
    have hone : ((fun _ => (1:ℝ)) : Fin C → ℝ) ⬝ᵥ H.mulVec w = 0 := by
      rw [dotProduct_mulVec, hkerL, zero_dotProduct]
    rw [hsplit, Matrix.mulVec_add, Matrix.mulVec_smul, hker,
      smul_zero, add_zero, add_dotProduct, smul_dotProduct, hone,
      smul_zero, add_zero]
  rw [hquad]
  calc c₀ * (1 - 1 / C) = c₀ * ∑ i, w i ^ 2 := by rw [hwnorm]
    _ ≤ w ⬝ᵥ H.mulVec w := hass w hwsum

/-- The both-sided kernel: the ones vector also kills the Hessian from
    the left, so ce_dead_lower's hypotheses are both discharged by
    ceHess itself. -/
lemma ceHess_one_vecMul (p : Fin C → ℝ) (hsum : ∑ y, p y = 1) :
    Matrix.vecMul (fun _ => (1:ℝ)) (ceHess p) = 0 := by
  funext j
  simp only [Matrix.vecMul, dotProduct, one_mul]
  unfold ceHess
  simp only [Matrix.sub_apply, Matrix.diagonal_apply,
    Matrix.vecMulVec_apply]
  rw [Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ j p, ← Finset.sum_mul, hsum]
  simp

/-! ### Clause (c): the gauge kernel through the backward chain -/

section GaugeRotation

variable {n : ℕ}

/-- The pulled-back gauge vector at depth p below the head: after
    rescaling, t^p off the dead coordinate and 1 on it. -/
noncomputable def gaugeVec (n : ℕ) (t : ℝ) (p : ℕ) : Fin (n+1) → ℝ :=
  fun i => if i = Fin.last n then 1 else t ^ p

/-- The canonical chain sends the gauge vector to t^p times the ones
    vector. -/
lemma canonical_mulVec_gaugeVec (t : ℝ) (p : ℕ) :
    (canonicalLayer n t ^ p).mulVec (gaugeVec n t p)
      = (t ^ p) • ((fun _ => (1:ℝ)) : Fin (n+1) → ℝ) := by
  funext i
  by_cases hi : i = Fin.last n
  · subst hi
    rw [canonicalLayer_pow_mulVec_last]
    simp [gaugeVec]
  · rw [canonicalLayer_pow_mulVec_ne t p _ hi]
    simp [gaugeVec, hi]

/-- thm:bridge_ce (c), kernel form: the pulled-back head covariance
    G_ℓ = Jᵀ H̄ J kills the gauge vector at every t: one exact zero
    eigenvalue at every layer and every t. -/
theorem ce_gauge_kernel (H : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hker : H.mulVec (fun _ => 1) = 0) (t : ℝ) (p : ℕ) :
    ((canonicalLayer n t ^ p)ᵀ * H * (canonicalLayer n t ^ p)).mulVec
      (gaugeVec n t p) = 0 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    canonical_mulVec_gaugeVec, Matrix.mulVec_smul, hker, smul_zero,
    Matrix.mulVec_zero]

/-- thm:bridge_ce (c), rotation form: the gauge eigenvector converges
    to the dead basis vector as t → 0⁺. The exact kernel absorbs the
    dead direction's decay. -/
theorem ce_gauge_eigen_limit (n p : ℕ) (hp : 1 ≤ p) :
    Filter.Tendsto (fun t => gaugeVec n t p) (𝓝[>] (0:ℝ))
      (𝓝 (Pi.single (Fin.last n) 1)) := by
  rw [tendsto_pi_nhds]
  intro i
  by_cases hi : i = Fin.last n
  · subst hi
    simp only [gaugeVec, if_true, Pi.single_eq_same]
    exact tendsto_const_nhds
  · simp only [gaugeVec, if_neg hi, Pi.single_eq_of_ne hi]
    have h := (continuous_pow p).tendsto (0:ℝ)
    rw [zero_pow (by omega : p ≠ 0)] at h
    exact h.mono_left nhdsWithin_le_nhds

end GaugeRotation

/-! ### The composed statement: head base times backward ladder -/

section ComposedLadder

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}

/-- thm:bridge_ce as one statement for the linear class. If the
    output-gradient second-moment matrix kills the ones vector on both
    sides and carries the non-degeneracy constant c₀ on {1}^⊥, the
    dead G-entry at depth ℓ is at least c₀(1 − 1/C)·t^{2(L−ℓ)}: the
    head base case and the backward ladder in a single inequality. -/
theorem ce_bridge_composed {c₀ : ℝ}
    (H : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (δ : Ω → Fin (n+1) → ℝ)
    (hH : ∀ v : Fin (n+1) → ℝ,
      v ⬝ᵥ H.mulVec v = ∫ ω, (∑ i, v i * δ ω i) ^ 2 ∂μ)
    (hker : H.mulVec (fun _ => 1) = 0)
    (hkerL : Matrix.vecMul (fun _ => (1:ℝ)) H = 0)
    (hass : ∀ v : Fin (n+1) → ℝ, (∑ i, v i) = 0 →
      c₀ * ∑ i, v i ^ 2 ≤ v ⬝ᵥ H.mulVec v)
    (t : ℝ) (L ℓ : ℕ) :
    c₀ * (1 - 1 / ((n:ℝ) + 1)) * t ^ (2 * (L - ℓ))
      ≤ ∫ ω, ((canonicalLayer n t ^ (L - ℓ)).mulVec (δ ω)
          (Fin.last n)) ^ 2 ∂μ := by
  rw [deep_linear_backward_rate]
  have hbase := ce_dead_lower (C := n + 1) H (by omega) hker hkerL
    hass (Fin.last n)
  have hread : (Pi.single (Fin.last n) 1 : Fin (n+1) → ℝ) ⬝ᵥ
      H.mulVec (Pi.single (Fin.last n) 1)
      = ∫ ω, (δ ω (Fin.last n)) ^ 2 ∂μ := by
    rw [hH]
    congr 1
    funext ω
    congr 1
    have hterm : ∀ i : Fin (n+1),
        (Pi.single (Fin.last n) 1 : Fin (n+1) → ℝ) i * δ ω i
        = if i = Fin.last n then δ ω i else 0 := by
      intro i
      rw [Pi.single_apply]
      by_cases hi : i = Fin.last n <;> simp [hi]
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      Finset.sum_ite_eq' Finset.univ (Fin.last n) (δ ω)]
    simp
  rw [hread] at hbase
  have hcast : ((n + 1 : ℕ) : ℝ) = (n:ℝ) + 1 := by push_cast; rfl
  rw [hcast] at hbase
  have ht2 : (0:ℝ) ≤ t ^ (2 * (L - ℓ)) := (even_two_mul _).pow_nonneg t
  nlinarith [mul_le_mul_of_nonneg_left hbase ht2]

end ComposedLadder

/-! ### Empirical against expected Fisher (cor:emp_vs_exp_ce)

The collapse separation is simplex algebra. At an observed label
carrying mass 1 − ε, the empirical per-sample gradient norm
‖p − e_y‖² sits between ε² and 2ε², while the expected-side trace
Σᵢ pᵢ(1 − pᵢ) sits between ε(1 − ε) and 2ε: the empirical side
collapses at the square of the expected side's order, with explicit
constants. -/

section EmpVsExp

variable {C : ℕ}

/-- The trace of the softmax Hessian: Σᵢ pᵢ(1 − pᵢ). -/
lemma ceHess_trace (p : Fin C → ℝ) :
    Matrix.trace (ceHess p) = ∑ i, p i * (1 - p i) := by
  unfold Matrix.trace ceHess
  simp only [Matrix.diag_apply, Matrix.sub_apply,
    Matrix.diagonal_apply_eq, Matrix.vecMulVec_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- cor:emp_vs_exp_ce, empirical side: the per-sample gradient norm
    at an observed label of mass 1 − ε sits between ε² and 2ε². -/
theorem emp_grad_sq_bounds (p : Fin C → ℝ) (y : Fin C) {ε : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hy : p y = 1 - ε) :
    ε ^ 2 ≤ ∑ i, (p i - (Pi.single y 1 : Fin C → ℝ) i) ^ 2
    ∧ ∑ i, (p i - (Pi.single y 1 : Fin C → ℝ) i) ^ 2 ≤ 2 * ε ^ 2 := by
  have hsplit : ∑ i, (p i - (Pi.single y 1 : Fin C → ℝ) i) ^ 2
      = (p y - 1) ^ 2
        + ∑ i ∈ Finset.univ.erase y, (p i) ^ 2 := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ y),
      Pi.single_eq_same]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Pi.single_eq_of_ne (Finset.mem_erase.mp hi).1, sub_zero]
  have hrest : ∑ i ∈ Finset.univ.erase y, p i = ε := by
    have h := Finset.add_sum_erase Finset.univ p (Finset.mem_univ y)
    rw [hsum, hy] at h
    linarith
  have hrest_nonneg : 0 ≤ ∑ i ∈ Finset.univ.erase y, (p i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hrest_le : ∑ i ∈ Finset.univ.erase y, (p i) ^ 2 ≤ ε ^ 2 := by
    calc ∑ i ∈ Finset.univ.erase y, (p i) ^ 2
        ≤ (∑ i ∈ Finset.univ.erase y, p i) ^ 2 :=
          Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hp i
      _ = ε ^ 2 := by rw [hrest]
  have hyterm : (p y - 1) ^ 2 = ε ^ 2 := by
    rw [hy]
    ring
  constructor
  · rw [hsplit, hyterm]
    linarith
  · rw [hsplit, hyterm]
    linarith

/-- cor:emp_vs_exp_ce, expected side: the trace of the softmax
    Hessian at an observed label of mass 1 − ε sits between ε(1 − ε)
    and 2ε. -/
theorem exp_trace_bounds (p : Fin C → ℝ) (y : Fin C) {ε : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hy : p y = 1 - ε) :
    ε * (1 - ε) ≤ ∑ i, p i * (1 - p i)
    ∧ ∑ i, p i * (1 - p i) ≤ 2 * ε := by
  have hle1 : ∀ i, p i ≤ 1 := by
    intro i
    have h := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
    linarith [hsum ▸ h]
  have hsplit : ∑ i, p i * (1 - p i)
      = p y * (1 - p y) + ∑ i ∈ Finset.univ.erase y, p i * (1 - p i) :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ y)).symm
  have hrest : ∑ i ∈ Finset.univ.erase y, p i = ε := by
    have h := Finset.add_sum_erase Finset.univ p (Finset.mem_univ y)
    rw [hsum, hy] at h
    linarith
  have hrest_nonneg : 0 ≤ ∑ i ∈ Finset.univ.erase y, p i * (1 - p i) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (hp i) (by linarith [hle1 i])
  have hrest_le : ∑ i ∈ Finset.univ.erase y, p i * (1 - p i) ≤ ε := by
    calc ∑ i ∈ Finset.univ.erase y, p i * (1 - p i)
        ≤ ∑ i ∈ Finset.univ.erase y, p i :=
          Finset.sum_le_sum fun i _ => by nlinarith [hp i, hle1 i]
      _ = ε := hrest
  have hε0 : 0 ≤ ε := by
    have h := hle1 y
    rw [hy] at h
    linarith
  constructor
  · rw [hsplit, hy]
    nlinarith
  · rw [hsplit, hy]
    nlinarith

/-- cor:emp_vs_exp_ce, the quadratic separation with explicit
    constants: (tr H)²/4 ≤ ‖p − e_y‖² ≤ 2(tr H)²/(1 − ε)². The
    empirical side collapses at the square of the expected side's
    order. -/
theorem emp_exp_quadratic_separation (p : Fin C → ℝ) (y : Fin C)
    {ε : ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hy : p y = 1 - ε) (hεlt : ε < 1) :
    (∑ i, p i * (1 - p i)) ^ 2 / 4
        ≤ ∑ i, (p i - (Pi.single y 1 : Fin C → ℝ) i) ^ 2
    ∧ ∑ i, (p i - (Pi.single y 1 : Fin C → ℝ) i) ^ 2
        ≤ 2 * (∑ i, p i * (1 - p i)) ^ 2 / (1 - ε) ^ 2 := by
  obtain ⟨hg1, hg2⟩ := emp_grad_sq_bounds p y hp hsum hy
  obtain ⟨ht1, ht2⟩ := exp_trace_bounds p y hp hsum hy
  have hε0 : 0 ≤ ε := by
    have h : p y ≤ 1 := by
      have h1 := Finset.single_le_sum (fun j _ => hp j)
        (Finset.mem_univ y)
      linarith [hsum ▸ h1]
    rw [hy] at h
    linarith
  have h1ε : (0:ℝ) < 1 - ε := by linarith
  have htr0 : 0 ≤ ∑ i, p i * (1 - p i) :=
    le_trans (mul_nonneg hε0 h1ε.le) ht1
  constructor
  · have hsq : (∑ i, p i * (1 - p i)) ^ 2 ≤ 4 * ε ^ 2 := by
      nlinarith [mul_le_mul ht2 ht2 htr0
        (by linarith : (0:ℝ) ≤ 2 * ε)]
    nlinarith [hg1, hsq]
  · have hεsq : ε ^ 2 * (1 - ε) ^ 2 ≤ (∑ i, p i * (1 - p i)) ^ 2 := by
      nlinarith [mul_le_mul ht1 ht1 (mul_nonneg hε0 h1ε.le) htr0]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (1 - ε) ^ 2)]
    nlinarith [hg2, hεsq, sq_nonneg (1 - ε)]

end EmpVsExp

/-- cor:emp_vs_exp_ce, the x-averaged form: integrating the
    per-sample bounds over the data, the empirical gradient norm
    averages between E[ε²] and 2E[ε²] while the expected trace
    averages between E[ε(1−ε)] and 2E[ε]: the empirical Fisher
    collapses at the square of the expected Fisher's order along a
    memorising trajectory. -/
theorem emp_exp_averaged {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω}
    (p : Ω → Fin C → ℝ) (y : Ω → Fin C) (ε : Ω → ℝ)
    (hp : ∀ ω i, 0 ≤ p ω i) (hsum : ∀ ω, ∑ i, p ω i = 1)
    (hy : ∀ ω, p ω (y ω) = 1 - ε ω)
    (hI1 : MeasureTheory.Integrable
      (fun ω => ∑ i, (p ω i - (Pi.single (y ω) 1 : Fin C → ℝ) i) ^ 2) μ)
    (hI2 : MeasureTheory.Integrable (fun ω => ε ω ^ 2) μ)
    (hI3 : MeasureTheory.Integrable (fun ω => ∑ i, p ω i * (1 - p ω i)) μ)
    (hI4 : MeasureTheory.Integrable ε μ)
    (hI5 : MeasureTheory.Integrable (fun ω => ε ω * (1 - ε ω)) μ) :
    (∫ ω, ε ω ^ 2 ∂μ
        ≤ ∫ ω, ∑ i, (p ω i - (Pi.single (y ω) 1 : Fin C → ℝ) i) ^ 2 ∂μ
      ∧ ∫ ω, ∑ i, (p ω i - (Pi.single (y ω) 1 : Fin C → ℝ) i) ^ 2 ∂μ
        ≤ 2 * ∫ ω, ε ω ^ 2 ∂μ)
    ∧ (∫ ω, ε ω * (1 - ε ω) ∂μ ≤ ∫ ω, ∑ i, p ω i * (1 - p ω i) ∂μ
      ∧ ∫ ω, ∑ i, p ω i * (1 - p ω i) ∂μ ≤ 2 * ∫ ω, ε ω ∂μ) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact MeasureTheory.integral_mono hI2 hI1 fun ω =>
      (emp_grad_sq_bounds (p ω) (y ω) (hp ω) (hsum ω) (hy ω)).1
  · rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_mono hI1 (hI2.const_mul 2) fun ω =>
      (emp_grad_sq_bounds (p ω) (y ω) (hp ω) (hsum ω) (hy ω)).2
  · exact MeasureTheory.integral_mono hI5 hI3 fun ω =>
      (exp_trace_bounds (p ω) (y ω) (hp ω) (hsum ω) (hy ω)).1
  · rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_mono hI3 (hI4.const_mul 2) fun ω =>
      (exp_trace_bounds (p ω) (y ω) (hp ω) (hsum ω) (hy ω)).2

end DeadDirections
