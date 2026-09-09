/-
  The ReLU dead channel (theory paper, thm:bridge class (P3), dead
  channel at the canonical configuration).

  Positive homogeneity makes the ReLU chain exact: the dead-channel
  map z ↦ ReLU(t·z), iterated L times, equals t^L·ReLU(x) with no
  remainder, which is the paper's statement that the activation-Taylor
  part of the correction vanishes identically for ReLU. The channel's
  second moment under N(0,1) is exactly t^{2L}/2: the rate 2L of the
  ladder, with the factor 1/2 the survival probability of the shared
  gate {x > 0}, the joint-gate clause of thm:bridge_composition as an
  exact constant.

  The backward side: for x ≠ 0 the chain's true derivative is
  t^L·gate(x) with gate = 1_{x>0} (relu_chain_hasDerivAt), so the
  backprop gradient at depth ℓ is t^{L−ℓ}·gate(x) and its second
  moment is exactly t^{2(L−ℓ)}/2, the same gate-survival 1/2 as the
  forward side. The A·G product at depth ℓ is t^{2L}/4 for every ℓ:
  cor:a_g_duality on the nonlinear (P3) channel, exact.
-/
import DeadDirections.MixtureScore

namespace DeadDirections

open MeasureTheory Filter Topology

/-- ReLU. -/
def relu (x : ℝ) : ℝ := max x 0

lemma relu_nonneg (x : ℝ) : 0 ≤ relu x := le_max_right x 0

lemma relu_mul_of_nonneg {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    relu (t * x) = t * relu x := by
  unfold relu
  rcases le_or_gt x 0 with hx | hx
  · rw [max_eq_right hx, max_eq_right (by nlinarith), mul_zero]
  · rw [max_eq_left hx.le, max_eq_left (by nlinarith)]

lemma relu_relu (x : ℝ) : relu (relu x) = relu x := by
  unfold relu
  rw [max_eq_left (le_max_right x 0)]

/-- The dead channel through L ReLU layers at parameter t is exactly
    t^L·ReLU: no activation-Taylor remainder. -/
lemma relu_chain_eq {t : ℝ} (ht : 0 ≤ t) (L : ℕ) (hL : 1 ≤ L) (x : ℝ) :
    (fun z => relu (t * z))^[L] x = t ^ L * relu x := by
  induction L with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [relu_mul_of_nonneg ht, pow_one]
    · rw [Function.iterate_succ_apply', ih hn,
        show t * (t ^ n * relu x) = t ^ n * t * relu x from by ring,
        relu_mul_of_nonneg (by positivity),
        relu_relu]
      ring

/-- The Gaussian half-moment: ∫ ReLU(x)²·φ₀ = 1/2, the survival
    probability of the gate {x > 0} weighting the unit second moment. -/
lemma integral_relu_sq_gaussDensity :
    ∫ x, relu x ^ 2 * gaussDensity x 0 1 = 1/2 := by
  have hind : (fun x => relu x ^ 2 * gaussDensity x 0 1)
      = Set.indicator (Set.Ioi (0:ℝ))
          (fun x => x ^ 2 * gaussDensity x 0 1) := by
    funext x
    rcases le_or_gt x 0 with hx | hx
    · rw [Set.indicator_of_notMem (by simpa using hx)]
      unfold relu
      rw [max_eq_right hx]
      ring
    · rw [Set.indicator_of_mem (by simpa using hx)]
      unfold relu
      rw [max_eq_left hx.le]
  rw [hind, integral_indicator measurableSet_Ioi]
  -- symmetry: the Ioi half is half of the whole
  have hint : Integrable (fun x => x ^ 2 * gaussDensity x 0 1) := by
    have h := integrable_sq_mul_gaussDensity 0
    exact h.congr (Filter.Eventually.of_forall fun x => by simp)
  have heven : ∀ x : ℝ, (-x) ^ 2 * gaussDensity (-x) 0 1
      = x ^ 2 * gaussDensity x 0 1 := by
    intro x
    rw [gaussDensity_one_eq, gaussDensity_one_eq]
    ring_nf
  have hneg : ∫ x in Set.Iio (0:ℝ), x ^ 2 * gaussDensity x 0 1
      = ∫ x in Set.Ioi (0:ℝ), x ^ 2 * gaussDensity x 0 1 := by
    rw [← integral_indicator measurableSet_Iio,
      ← integral_indicator measurableSet_Ioi]
    rw [show (Set.indicator (Set.Iio (0:ℝ))
        (fun x => x ^ 2 * gaussDensity x 0 1))
      = fun x => (Set.indicator (Set.Ioi (0:ℝ))
        (fun y => y ^ 2 * gaussDensity y 0 1)) (-x) from ?_]
    · exact integral_neg_eq_self (μ := volume)
        (Set.indicator (Set.Ioi (0:ℝ))
          (fun y => y ^ 2 * gaussDensity y 0 1))
    · funext x
      rcases lt_or_ge x 0 with hx | hx
      · rw [Set.indicator_of_mem (by simpa using hx),
          Set.indicator_of_mem (by simp; linarith), heven]
      · rw [Set.indicator_of_notMem (by simpa using hx),
          Set.indicator_of_notMem (by simp; linarith)]
  have hsplit := integral_add_compl (measurableSet_Iio (a := (0:ℝ))) hint
  have hIic : ∫ x in (Set.Iio (0:ℝ))ᶜ, x ^ 2 * gaussDensity x 0 1
      = ∫ x in Set.Ioi (0:ℝ), x ^ 2 * gaussDensity x 0 1 := by
    rw [Set.compl_Iio]
    exact setIntegral_congr_set Ioi_ae_eq_Ici.symm
  have hone : ∫ x, x ^ 2 * gaussDensity x 0 1 = 1 := by
    have h := integral_sq_gaussMeasure
    rw [integral_gaussMeasure] at h
    exact h
  rw [hIic, hneg] at hsplit
  linarith [hsplit, hone]

/-- thm:bridge class (P3), dead channel: exact second moment t^{2L}/2
    at every t ≥ 0 and depth L ≥ 1. -/
theorem relu_channel_moment {t : ℝ} (ht : 0 ≤ t) (L : ℕ) (hL : 1 ≤ L) :
    ∫ x, ((fun z => relu (t * z))^[L] x) ^ 2 * gaussDensity x 0 1
      = t ^ (2 * L) * (1/2) := by
  have hfun : ∀ x : ℝ, ((fun z => relu (t * z))^[L] x) ^ 2
        * gaussDensity x 0 1
      = t ^ (2 * L) * (relu x ^ 2 * gaussDensity x 0 1) := by
    intro x
    rw [relu_chain_eq ht L hL, mul_pow,
      show (t ^ L) ^ 2 = t ^ (2 * L) from by
        rw [← pow_mul, Nat.mul_comm]]
    ring
  simp only [hfun]
  rw [integral_const_mul, integral_relu_sq_gaussDensity]

/-- The P3 dead channel carries the ladder rate 2L with the
    gate-survival coefficient 1/2. -/
theorem relu_channel_hasLeadingRate (L : ℕ) (hL : 1 ≤ L) :
    HasLeadingRate
      (fun t => ∫ x, ((fun z => relu (t * z))^[L] x) ^ 2
        * gaussDensity x 0 1) (2 * L) (1/2) := by
  have h : Tendsto (fun _ : ℝ => (1/2 : ℝ)) (𝓝[>] (0:ℝ)) (𝓝 (1/2)) :=
    tendsto_const_nhds
  refine h.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  rw [relu_channel_moment (le_of_lt ht) L hL]
  have htp : t ^ (2 * L) ≠ 0 := ne_of_gt (pow_pos ht _)
  field_simp

/-! ### The backward channel and A–G duality

The gate is the backprop convention relu'(z) = 1_{z>0}. Every layer of
the dead channel shares it: the pre-activation at layer j is t^j·relu x,
positive exactly when x is. For x ≠ 0 the gate reading is the honest
one, the chain's derivative in the sense of HasDerivAt. -/

/-- The ReLU gate, backprop convention: 1 on {x > 0}, 0 elsewhere. -/
noncomputable def reluGate (x : ℝ) : ℝ := if 0 < x then 1 else 0

lemma reluGate_sq (x : ℝ) : reluGate x ^ 2 = reluGate x := by
  unfold reluGate
  split <;> norm_num

/-- Off x = 0 the chain derivative is exactly t^L·gate(x): the chain
    is locally linear on each side of the gate. -/
lemma relu_chain_hasDerivAt {t : ℝ} (ht : 0 ≤ t) (L : ℕ) (hL : 1 ≤ L)
    {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt ((fun z => relu (t * z))^[L]) (t ^ L * reluGate x) x := by
  have hfun : ((fun z => relu (t * z))^[L]) = fun y => t ^ L * relu y :=
    funext (relu_chain_eq ht L hL)
  rw [hfun]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hrelu : HasDerivAt relu 0 x := by
      have h0 : HasDerivAt (fun _ : ℝ => (0:ℝ)) 0 x := hasDerivAt_const x 0
      refine h0.congr_of_eventuallyEq ?_
      filter_upwards [eventually_lt_nhds hneg] with y hy
      unfold relu
      rw [max_eq_right hy.le]
    have h := hrelu.const_mul (t ^ L)
    rw [mul_zero] at h
    rw [show reluGate x = 0 from if_neg (not_lt.mpr hneg.le), mul_zero]
    exact h
  · have hrelu : HasDerivAt relu 1 x := by
      refine (hasDerivAt_id x).congr_of_eventuallyEq ?_
      filter_upwards [eventually_gt_nhds hpos] with y hy
      show relu y = y
      unfold relu
      rw [max_eq_left hy.le]
    have h := hrelu.const_mul (t ^ L)
    rw [mul_one] at h
    rw [show reluGate x = 1 from if_pos hpos, mul_one]
    exact h

/-- The backprop gradient at depth ℓ is the derivative of the
    downstream L − ℓ layers at the layer-ℓ activation: for x > 0 the
    activation t^ℓ·relu x is positive, the downstream chain is locally
    linear there, and the derivative is exactly t^{L−ℓ}. -/
lemma relu_backward_hasDerivAt {t : ℝ} (ht : 0 < t) (L ℓ : ℕ)
    (hℓ : ℓ < L) {x : ℝ} (hx : 0 < x) :
    HasDerivAt ((fun z => relu (t * z))^[L - ℓ]) (t ^ (L - ℓ))
      (t ^ ℓ * relu x) := by
  have hpt : (0:ℝ) < t ^ ℓ * relu x := by
    unfold relu
    rw [max_eq_left hx.le]
    positivity
  have h := relu_chain_hasDerivAt ht.le (L - ℓ) (by omega)
    (ne_of_gt hpt)
  rwa [show reluGate (t ^ ℓ * relu x) = 1 from if_pos hpt, mul_one] at h

/-- The gate survives with probability 1/2 under N(0,1). -/
lemma integral_reluGate_gaussDensity :
    ∫ x, reluGate x * gaussDensity x 0 1 = 1/2 := by
  have hind : (fun x => reluGate x * gaussDensity x 0 1)
      = Set.indicator (Set.Ioi (0:ℝ)) (fun x => gaussDensity x 0 1) := by
    funext x
    unfold reluGate
    rcases le_or_gt x 0 with hx | hx
    · rw [Set.indicator_of_notMem (by simpa using hx), if_neg (not_lt.mpr hx),
        zero_mul]
    · rw [Set.indicator_of_mem (by simpa using hx), if_pos hx, one_mul]
  rw [hind, integral_indicator measurableSet_Ioi]
  have hint : Integrable (fun x => gaussDensity x 0 1) :=
    integrable_gaussDensity 0
  have heven : ∀ x : ℝ, gaussDensity (-x) 0 1 = gaussDensity x 0 1 := by
    intro x
    rw [gaussDensity_one_eq, gaussDensity_one_eq]
    ring_nf
  have hneg : ∫ x in Set.Iio (0:ℝ), gaussDensity x 0 1
      = ∫ x in Set.Ioi (0:ℝ), gaussDensity x 0 1 := by
    rw [← integral_indicator measurableSet_Iio,
      ← integral_indicator measurableSet_Ioi]
    rw [show (Set.indicator (Set.Iio (0:ℝ)) (fun x => gaussDensity x 0 1))
        = fun x => (Set.indicator (Set.Ioi (0:ℝ))
          (fun y => gaussDensity y 0 1)) (-x) from ?_]
    · exact integral_neg_eq_self (μ := volume)
        (Set.indicator (Set.Ioi (0:ℝ)) (fun y => gaussDensity y 0 1))
    · funext x
      rcases lt_or_ge x 0 with hx | hx
      · rw [Set.indicator_of_mem (by simpa using hx),
          Set.indicator_of_mem (by simp; linarith), heven]
      · rw [Set.indicator_of_notMem (by simpa using hx),
          Set.indicator_of_notMem (by simp; linarith)]
  have hsplit := integral_add_compl (measurableSet_Iio (a := (0:ℝ))) hint
  have hIic : ∫ x in (Set.Iio (0:ℝ))ᶜ, gaussDensity x 0 1
      = ∫ x in Set.Ioi (0:ℝ), gaussDensity x 0 1 := by
    rw [Set.compl_Iio]
    exact setIntegral_congr_set Ioi_ae_eq_Ici.symm
  rw [hIic, hneg] at hsplit
  linarith [hsplit, integral_gaussDensity_eq_one 0]

/-- thm:bridge class (P3), backward side: the second moment of the
    depth-ℓ backprop gradient is exactly t^{2(L−ℓ)}/2, the same
    gate-survival 1/2 as the forward side. -/
theorem relu_channel_backward_moment {t : ℝ} (L ℓ : ℕ) :
    ∫ x, (t ^ (L - ℓ) * reluGate x) ^ 2 * gaussDensity x 0 1
      = t ^ (2 * (L - ℓ)) * (1/2) := by
  have hfun : ∀ x : ℝ, (t ^ (L - ℓ) * reluGate x) ^ 2 * gaussDensity x 0 1
      = t ^ (2 * (L - ℓ)) * (reluGate x * gaussDensity x 0 1) := by
    intro x
    rw [mul_pow, reluGate_sq,
      show (t ^ (L - ℓ)) ^ 2 = t ^ (2 * (L - ℓ)) from by
        rw [← pow_mul, Nat.mul_comm]]
    ring
  simp only [hfun]
  rw [integral_const_mul, integral_reluGate_gaussDensity]

/-- cor:a_g_duality, class (P3): the A·G product at depth ℓ is
    t^{2L}/4 for every ℓ; the forward exponent 2ℓ and the backward
    exponent 2(L−ℓ) sum to 2L at every depth, and the 1/4 is the gate
    survival squared, once per factor. -/
theorem relu_channel_ag_product {t : ℝ} (ht : 0 ≤ t) (L ℓ : ℕ)
    (hℓ1 : 1 ≤ ℓ) (hℓL : ℓ ≤ L) :
    (∫ x, ((fun z => relu (t * z))^[ℓ] x) ^ 2 * gaussDensity x 0 1)
      * (∫ x, (t ^ (L - ℓ) * reluGate x) ^ 2 * gaussDensity x 0 1)
      = t ^ (2 * L) * (1/4) := by
  rw [relu_channel_moment ht ℓ hℓ1, relu_channel_backward_moment,
    show t ^ (2 * ℓ) * (1/2) * (t ^ (2 * (L - ℓ)) * (1/2))
      = t ^ (2 * ℓ) * t ^ (2 * (L - ℓ)) * (1/4) from by ring,
    ← pow_add]
  congr 2
  omega

/-! ### The off-channel base, two channels

The minimal multivariate configuration: one dead channel at weight t
next to one live channel at fixed weight s, no mixing, the
channel-diagonal form of the canonical (P3) configuration. The joint
layer map iterates componentwise, the live moment carries no t, and
the dead moment is strictly smaller at every t < s: the Θ(1)
off-channel base of thm:bridge (b), exact for ReLU. -/

/-- The two-channel layer map iterates componentwise. -/
lemma reluPair_iterate {t s : ℝ} (L : ℕ) (p : ℝ × ℝ) :
    (fun q : ℝ × ℝ => (relu (t * q.1), relu (s * q.2)))^[L] p
      = ((fun y => relu (t * y))^[L] p.1,
         (fun z => relu (s * z))^[L] p.2) := by
  induction L with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih]

/-- thm:bridge (b), class (P3): in the two-channel configuration the
    live-coordinate second moment is s^{2L}/2 at every t, and the
    dead-coordinate moment t^{2L}/2 is strictly smaller whenever
    t < s. No asymptotics: the comparison holds at every such t. -/
theorem relu_two_channel_dead_lt_live {t s : ℝ} (ht : 0 ≤ t)
    (hts : t < s) (L : ℕ) (hL : 1 ≤ L) :
    (∫ x, ((fun q : ℝ × ℝ => (relu (t * q.1), relu (s * q.2)))^[L]
        (x, x)).1 ^ 2 * gaussDensity x 0 1)
      < ∫ x, ((fun q : ℝ × ℝ => (relu (t * q.1), relu (s * q.2)))^[L]
        (x, x)).2 ^ 2 * gaussDensity x 0 1 := by
  have hs : (0:ℝ) ≤ s := le_trans ht hts.le
  have h1 : ∀ x : ℝ, ((fun q : ℝ × ℝ =>
        (relu (t * q.1), relu (s * q.2)))^[L] (x, x)).1
      = (fun y => relu (t * y))^[L] x := fun x => by
    rw [reluPair_iterate]
  have h2 : ∀ x : ℝ, ((fun q : ℝ × ℝ =>
        (relu (t * q.1), relu (s * q.2)))^[L] (x, x)).2
      = (fun z => relu (s * z))^[L] x := fun x => by
    rw [reluPair_iterate]
  simp only [h1, h2]
  rw [relu_channel_moment ht L hL, relu_channel_moment hs L hL]
  have hpow : t ^ (2 * L) < s ^ (2 * L) :=
    pow_lt_pow_left₀ hts ht (by omega)
  linarith

/-! ### The smooth channel, one layer

For a smooth activation with φ(0) = 0 and φ'(0) = c, packaged as the
global Taylor hypothesis |φ(u) − c·u| ≤ K·u², the single-layer dead
channel carries leading rate 2 with coefficient c²: the first rung of
the (P2) ladder. The deep (P2) chain, with the compounded quadratic
remainders controlled by a polynomial envelope, lives in
SmoothChain. -/

section SmoothChannel

lemma integrable_x4_gaussDensity :
    Integrable (fun x => x ^ 4 * gaussDensity x 0 1) := by
  have h := integrable_pow_mul_exp_mul_gaussDensity 4 0
  exact h.congr (Filter.Eventually.of_forall fun x => by simp)

/-- thm:bridge class (P2), one layer: under |φ(u) − c·u| ≤ K·u², the
    dead-channel second moment expands as c²·t² + O(t³). -/
theorem smooth_channel_hasLeadingRate {φ : ℝ → ℝ} {c K : ℝ}
    (hK : 0 ≤ K) (hcont : Continuous φ)
    (hφ : ∀ u, |φ u - c * u| ≤ K * u ^ 2) :
    HasLeadingRate
      (fun t => ∫ x, φ (t * x) ^ 2 * gaussDensity x 0 1) 2 (c ^ 2) := by
  have hone : ∫ x, x ^ 2 * gaussDensity x 0 1 = 1 := by
    have h := integral_sq_gaussMeasure
    rwa [integral_gaussMeasure] at h
  have hx2 : Integrable (fun x => x ^ 2 * gaussDensity x 0 1) := by
    exact (integrable_sq_mul_gaussDensity 0).congr
      (Filter.Eventually.of_forall fun x => by simp)
  -- pointwise bound on φ(tx)
  have hφabs : ∀ u, |φ u| ≤ |c| * |u| + K * u ^ 2 := by
    intro u
    have h := hφ u
    have h1 : |φ u| ≤ |φ u - c * u| + |c * u| := by
      have h2 := abs_add_le (φ u - c * u) (c * u)
      rw [show φ u - c * u + c * u = φ u from by ring] at h2
      exact h2
    rw [abs_mul] at h1
    linarith
  -- the dominators
  have hM0 : (0:ℝ) ≤ K * (2 * |c| * (1 + ∫ x, x ^ 4 * gaussDensity x 0 1)
      + K * ∫ x, x ^ 4 * gaussDensity x 0 1) := by
    have h4 : (0:ℝ) ≤ ∫ x, x ^ 4 * gaussDensity x 0 1 :=
      integral_nonneg fun x => mul_nonneg (by positivity)
        (gaussDensity_pos x 0).le
    positivity
  apply hasLeadingRate_of_expansion
    (R := fun t => (∫ x, φ (t * x) ^ 2 * gaussDensity x 0 1) - c ^ 2 * t ^ 2)
    (M := K * (2 * |c| * (1 + ∫ x, x ^ 4 * gaussDensity x 0 1)
      + K * ∫ x, x ^ 4 * gaussDensity x 0 1))
  · exact Filter.Eventually.of_forall fun t => by ring
  · filter_upwards [eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with t ht0 ht1
    have h0t : (0:ℝ) < t := ht0
    have h1t : t ≤ 1 := le_of_lt ht1
    -- pointwise remainder bound
    have hptw : ∀ x, |φ (t * x) ^ 2 * gaussDensity x 0 1
        - c ^ 2 * t ^ 2 * (x ^ 2 * gaussDensity x 0 1)|
        ≤ t ^ 3 * (K * (2 * |c| * (1 + x ^ 4) + K * x ^ 4))
          * gaussDensity x 0 1 := by
      intro x
      have hφ1 := hφ (t * x)
      have hφ2 := hφabs (t * x)
      have hφg := (gaussDensity_pos x 0).le
      have hx3 : |x| ^ 3 ≤ 1 + x ^ 4 := by
        rcases le_or_gt |x| 1 with h | h
        · have := pow_le_one₀ (abs_nonneg x) h (n := 3)
          nlinarith [sq_nonneg (x ^ 2)]
        · have := pow_le_pow_right₀ h.le (show 3 ≤ 4 by norm_num)
          have h4 : |x| ^ 4 = x ^ 4 := by
            rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
          nlinarith
      have hfac : φ (t * x) ^ 2 - c ^ 2 * t ^ 2 * x ^ 2
          = (φ (t * x) - c * (t * x)) * (φ (t * x) + c * (t * x)) := by
        ring
      have habs2 : |φ (t * x) + c * (t * x)|
          ≤ 2 * |c| * |t * x| + K * (t * x) ^ 2 := by
        have h1 := abs_add_le (φ (t * x)) (c * (t * x))
        rw [abs_mul] at h1
        linarith [hφ2]
      have hkey : |φ (t * x) ^ 2 - c ^ 2 * t ^ 2 * x ^ 2|
          ≤ t ^ 3 * (K * (2 * |c| * (1 + x ^ 4) + K * x ^ 4)) := by
        rw [hfac, abs_mul]
        have hb := mul_le_mul hφ1 habs2 (abs_nonneg _)
          (mul_nonneg hK (sq_nonneg _))
        have htx : |t * x| = t * |x| := by rw [abs_mul, abs_of_pos h0t]
        rw [htx] at hb
        calc |φ (t * x) - c * (t * x)| * |φ (t * x) + c * (t * x)|
            ≤ K * (t * x) ^ 2 * (2 * |c| * (t * |x|) + K * (t * x) ^ 2) :=
              hb
          _ ≤ t ^ 3 * (K * (2 * |c| * (1 + x ^ 4) + K * x ^ 4)) := by
              have hxx : (t * x) ^ 2 = t ^ 2 * x ^ 2 := by ring
              rw [hxx]
              have hc1 : K * (t ^ 2 * x ^ 2) * (2 * |c| * (t * |x|))
                  = t ^ 3 * (K * (2 * |c| * (x ^ 2 * |x|))) := by ring
              have hc2 : K * (t ^ 2 * x ^ 2) * (K * (t ^ 2 * x ^ 2))
                  ≤ t ^ 3 * (K * (K * x ^ 4)) := by
                have ht4 : t ^ 4 ≤ t ^ 3 :=
                  pow_le_pow_of_le_one h0t.le h1t (by norm_num)
                calc K * (t ^ 2 * x ^ 2) * (K * (t ^ 2 * x ^ 2))
                    = t ^ 4 * (K * (K * x ^ 4)) := by ring
                  _ ≤ t ^ 3 * (K * (K * x ^ 4)) := by
                      exact mul_le_mul_of_nonneg_right ht4 (by positivity)
              have hc3 : x ^ 2 * |x| ≤ 1 + x ^ 4 := by
                have h := hx3
                have habs3 : |x| ^ 3 = x ^ 2 * |x| := by
                  rw [pow_succ, sq_abs]
                linarith [habs3 ▸ h]
              nlinarith [mul_nonneg (mul_nonneg hK (abs_nonneg c))
                  (sub_nonneg.mpr hc3), pow_pos h0t 3]
      calc |φ (t * x) ^ 2 * gaussDensity x 0 1
          - c ^ 2 * t ^ 2 * (x ^ 2 * gaussDensity x 0 1)|
          = |φ (t * x) ^ 2 - c ^ 2 * t ^ 2 * x ^ 2| * gaussDensity x 0 1 := by
            rw [show φ (t * x) ^ 2 * gaussDensity x 0 1
                - c ^ 2 * t ^ 2 * (x ^ 2 * gaussDensity x 0 1)
              = (φ (t * x) ^ 2 - c ^ 2 * t ^ 2 * x ^ 2)
                * gaussDensity x 0 1 from by ring,
              abs_mul, abs_of_nonneg hφg]
        _ ≤ t ^ 3 * (K * (2 * |c| * (1 + x ^ 4) + K * x ^ 4))
            * gaussDensity x 0 1 :=
            mul_le_mul_of_nonneg_right hkey hφg
    -- integrability of the channel
    have hIφ : Integrable (fun x => φ (t * x) ^ 2 * gaussDensity x 0 1) := by
      have hg : Integrable (fun x =>
          (2 * c ^ 2) * (x ^ 2 * gaussDensity x 0 1)
            + (2 * K ^ 2) * (x ^ 4 * gaussDensity x 0 1)) :=
        (hx2.const_mul _).add (integrable_x4_gaussDensity.const_mul _)
      refine hg.mono' (((hcont.comp
        (continuous_const.mul continuous_id)).pow 2).mul
        (continuous_gaussDensity 0)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      have hφg := (gaussDensity_pos x 0).le
      have h2 := hφabs (t * x)
      have htx2 : (t * x) ^ 2 ≤ x ^ 2 := by
        have ht2 : t ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right ht2 (sq_nonneg x)]
      have habs4 : ((t * x) ^ 2) ^ 2 ≤ x ^ 4 := by
        have h := pow_le_pow_left₀ (sq_nonneg (t * x)) htx2 2
        calc ((t * x) ^ 2) ^ 2 ≤ (x ^ 2) ^ 2 := h
          _ = x ^ 4 := by ring
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hφg)]
      have hsq : φ (t * x) ^ 2 ≤ 2 * c ^ 2 * (t * x) ^ 2
          + 2 * K ^ 2 * ((t * x) ^ 2) ^ 2 := by
        have h := hφabs (t * x)
        have hnn : 0 ≤ |φ (t * x)| := abs_nonneg _
        have hs := pow_le_pow_left₀ hnn h 2
        rw [sq_abs] at hs
        nlinarith [sq_nonneg (|c| * |t * x| - K * (t * x) ^ 2),
          sq_abs (t * x), sq_abs c,
          mul_nonneg (abs_nonneg c) (abs_nonneg (t * x))]
      nlinarith [mul_le_mul_of_nonneg_right hsq hφg,
        mul_le_mul_of_nonneg_right htx2 hφg,
        mul_le_mul_of_nonneg_right habs4 hφg, sq_nonneg c, hK]
    -- assemble the integral bound
    have hsub : (∫ x, φ (t * x) ^ 2 * gaussDensity x 0 1) - c ^ 2 * t ^ 2
        = ∫ x, (φ (t * x) ^ 2 * gaussDensity x 0 1
          - c ^ 2 * t ^ 2 * (x ^ 2 * gaussDensity x 0 1)) := by
      rw [integral_sub hIφ (hx2.const_mul _), integral_const_mul, hone,
        mul_one]
    rw [hsub]
    have hIdom : Integrable (fun x =>
        t ^ 3 * (K * (2 * |c| * (1 + x ^ 4) + K * x ^ 4))
          * gaussDensity x 0 1) := by
      have hg : Integrable (fun x =>
          (t ^ 3 * (K * 2 * |c|)) * gaussDensity x 0 1
            + (t ^ 3 * (K * 2 * |c| + K * K))
              * (x ^ 4 * gaussDensity x 0 1)) :=
        ((integrable_gaussDensity 0).const_mul _).add
          (integrable_x4_gaussDensity.const_mul _)
      exact hg.congr (Filter.Eventually.of_forall fun x => by ring)
    calc |∫ x, (φ (t * x) ^ 2 * gaussDensity x 0 1
          - c ^ 2 * t ^ 2 * (x ^ 2 * gaussDensity x 0 1))|
        ≤ ∫ x, ‖φ (t * x) ^ 2 * gaussDensity x 0 1
          - c ^ 2 * t ^ 2 * (x ^ 2 * gaussDensity x 0 1)‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_integral_norm _
      _ ≤ ∫ x, t ^ 3 * (K * (2 * |c| * (1 + x ^ 4) + K * x ^ 4))
          * gaussDensity x 0 1 := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun x => norm_nonneg _) hIdom
            (Filter.Eventually.of_forall fun x => ?_)
          simp only [Real.norm_eq_abs]
          exact hptw x
      _ ≤ K * (2 * |c| * (1 + ∫ x, x ^ 4 * gaussDensity x 0 1)
          + K * ∫ x, x ^ 4 * gaussDensity x 0 1) * t ^ (2 + 1) := by
          have hval : ∫ x, t ^ 3 * (K * (2 * |c| * (1 + x ^ 4) + K * x ^ 4))
              * gaussDensity x 0 1
              = t ^ 3 * (K * (2 * |c|
                * (1 + ∫ x, x ^ 4 * gaussDensity x 0 1)
                + K * ∫ x, x ^ 4 * gaussDensity x 0 1)) := by
            have hfun : (fun x => t ^ 3
                * (K * (2 * |c| * (1 + x ^ 4) + K * x ^ 4))
                * gaussDensity x 0 1)
                = fun x => (t ^ 3 * (K * 2 * |c|)) * gaussDensity x 0 1
                  + (t ^ 3 * (K * 2 * |c| + K * K))
                    * (x ^ 4 * gaussDensity x 0 1) := by
              funext x
              ring
            rw [hfun, integral_add
              (((integrable_gaussDensity 0)).const_mul _)
              (integrable_x4_gaussDensity.const_mul _),
              integral_const_mul, integral_const_mul,
              integral_gaussDensity_eq_one]
            ring
          rw [hval]
          have h33 : t ^ 3 = t ^ (2 + 1) := rfl
          nlinarith [hM0, pow_pos h0t 3]

end SmoothChannel

end DeadDirections
