/-
  The LayerNorm finite-t rate shift on the MLP block (theory paper,
  thm:ln_finite_t_mlp), model level.

  The theorem's core object is the three-term expansion
  G(t) = c₀ + c₂t² + c₄t⁴ (noise floor, the LN mean-subtraction
  leak's t² term, the direct t⁴ term) and its local log-slope
  α(t) = t·G'(t)/G(t). Here the derivative is certified, the slope's
  rational form is derived, and the three regimes are limits: α → 0
  at a positive noise floor, α → 2 on the t²-plateau (c₀ = 0), and
  α = 4 exactly on the direct rate (c₀ = c₂ = 0). The almost-sure
  bound on the t² prefactor is the pointwise algebra σ₀² ≥
  (d−1)/d²·x̄², and the rate-shift contrast is a pair of leading-rate
  statements: with the leak the observable above the floor has rate
  2, without LN it has rate 4.
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import DeadDirections.FisherDecay
import DeadDirections.GaussianLayer

namespace DeadDirections

open Filter Topology

/-- The three-term directional-Fisher expansion: noise floor, leak
    term, direct term. -/
def lnG (c0 c2 c4 : ℝ) : ℝ → ℝ := fun t => c0 + c2 * t ^ 2 + c4 * t ^ 4

/-- The derivative of the expansion, certified. -/
lemma lnG_hasDerivAt (c0 c2 c4 t : ℝ) :
    HasDerivAt (lnG c0 c2 c4) (2 * c2 * t + 4 * c4 * t ^ 3) t := by
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    have h := hasDerivAt_pow 2 t
    norm_num at h
    exact h
  have h4 : HasDerivAt (fun s : ℝ => s ^ 4) (4 * t ^ 3) t := by
    have h := hasDerivAt_pow 4 t
    norm_num at h
    exact h
  have hsum := ((h2.const_mul c2).const_add c0).add (h4.const_mul c4)
  have heq : c2 * (2 * t) + c4 * (4 * t ^ 3)
      = 2 * c2 * t + 4 * c4 * t ^ 3 := by ring
  rw [heq] at hsum
  exact hsum

/-- The local log-slope α(t) = t·G'(t)/G(t). -/
noncomputable def alphaSlope (c0 c2 c4 t : ℝ) : ℝ :=
  t * deriv (lnG c0 c2 c4) t / lnG c0 c2 c4 t

/-- The slope's rational form, from the certified derivative. -/
lemma alphaSlope_eq (c0 c2 c4 t : ℝ) :
    alphaSlope c0 c2 c4 t
      = (2 * c2 * t ^ 2 + 4 * c4 * t ^ 4)
        / (c0 + c2 * t ^ 2 + c4 * t ^ 4) := by
  unfold alphaSlope
  rw [(lnG_hasDerivAt c0 c2 c4 t).deriv]
  unfold lnG
  congr 1
  ring

/-- Regime 1, the noise floor: at a positive floor the local
    log-slope tends to zero, recovering the no-LN prediction at
    scale t → 0. -/
theorem noise_floor_regime {c0 : ℝ} (hc0 : 0 < c0) (c2 c4 : ℝ) :
    Tendsto (fun t => alphaSlope c0 c2 c4 t) (𝓝[>] (0:ℝ))
      (𝓝 0) := by
  have hlim : Tendsto
      (fun t : ℝ => (2 * c2 * t ^ 2 + 4 * c4 * t ^ 4)
        / (c0 + c2 * t ^ 2 + c4 * t ^ 4))
      (𝓝 (0:ℝ))
      (𝓝 ((2 * c2 * 0 ^ 2 + 4 * c4 * 0 ^ 4)
        / (c0 + c2 * 0 ^ 2 + c4 * 0 ^ 4))) := by
    apply Filter.Tendsto.div
    · exact (Continuous.tendsto (by continuity) 0)
    · exact (Continuous.tendsto (by continuity) 0)
    · simpa using hc0.ne'
  have heq : (2 * c2 * (0:ℝ) ^ 2 + 4 * c4 * 0 ^ 4)
      / (c0 + c2 * 0 ^ 2 + c4 * 0 ^ 4) = 0 := by
    simp
  rw [heq] at hlim
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [] with t
  rw [alphaSlope_eq]

/-- Regime 2, the t²-plateau: with the noise floor negligible the
    leak term carries the slope to 2. -/
theorem t2_plateau_regime {c2 : ℝ} (hc2 : 0 < c2) (c4 : ℝ) :
    Tendsto (fun t => alphaSlope 0 c2 c4 t) (𝓝[>] (0:ℝ))
      (𝓝 2) := by
  have hlim : Tendsto
      (fun t : ℝ => (2 * c2 + 4 * c4 * t ^ 2) / (c2 + c4 * t ^ 2))
      (𝓝 (0:ℝ))
      (𝓝 ((2 * c2 + 4 * c4 * 0 ^ 2) / (c2 + c4 * 0 ^ 2))) := by
    apply Filter.Tendsto.div
    · exact (Continuous.tendsto (by continuity) 0)
    · exact (Continuous.tendsto (by continuity) 0)
    · simpa using hc2.ne'
  have heq : (2 * c2 + 4 * c4 * (0:ℝ) ^ 2) / (c2 + c4 * 0 ^ 2)
      = 2 := by
    norm_num
    rw [mul_div_assoc, div_self hc2.ne', mul_one]
  rw [heq] at hlim
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht0
  have ht : t ≠ 0 := ne_of_gt ht0
  rw [alphaSlope_eq]
  rw [show 2 * c2 * t ^ 2 + 4 * c4 * t ^ 4
      = t ^ 2 * (2 * c2 + 4 * c4 * t ^ 2) by ring,
    show (0:ℝ) + c2 * t ^ 2 + c4 * t ^ 4
      = t ^ 2 * (c2 + c4 * t ^ 2) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 ht)]

/-- Regime 3, the direct rate: with floor and leak both absent the
    slope is 4 exactly at every t ≠ 0. -/
theorem direct_rate_regime {c4 : ℝ} (hc4 : c4 ≠ 0) {t : ℝ}
    (ht : t ≠ 0) :
    alphaSlope 0 0 c4 t = 4 := by
  rw [alphaSlope_eq]
  have hne : c4 * t ^ 4 ≠ 0 := mul_ne_zero hc4 (pow_ne_zero 4 ht)
  rw [show (2:ℝ) * 0 * t ^ 2 + 4 * c4 * t ^ 4 = 4 * (c4 * t ^ 4)
      by ring,
    show (0:ℝ) + 0 * t ^ 2 + c4 * t ^ 4 = c4 * t ^ 4 by ring,
    mul_div_assoc, div_self hne, mul_one]

/-- The t² prefactor is bounded almost surely, with no moment
    condition: σ₀² dominates its own mean-square term pointwise, so
    x̄²/σ₀² ≤ d²/(d−1). Stated as the product form. -/
theorem leak_prefactor_bounded {d s2 xb : ℝ} (hd : 2 ≤ d)
    (hs2 : 0 ≤ s2) :
    xb ^ 2 ≤ d ^ 2 / (d - 1)
      * ((d - 1) / d * s2 + (d - 1) / d ^ 2 * xb ^ 2) := by
  have hd0 : (0:ℝ) < d := by linarith
  have hd1 : (0:ℝ) < d - 1 := by linarith
  have hexp : d ^ 2 / (d - 1)
      * ((d - 1) / d * s2 + (d - 1) / d ^ 2 * xb ^ 2)
      = d * s2 + xb ^ 2 := by
    field_simp
  rw [hexp]
  nlinarith [mul_nonneg hd0.le hs2]

/-- The rate shift: above the noise floor the LN observable carries
    leading rate 2 with the leak coefficient. -/
theorem ln_leak_rate {c2 : ℝ} (c4 : ℝ) :
    HasLeadingRate (fun t => c2 * t ^ 2 + c4 * t ^ 4) 2 c2 := by
  have h2 : HasLeadingRate (fun t => c2 * t ^ 2) 2 c2 := by
    have h := (hasLeadingRate_pow 2).const_mul c2
    simpa using h
  have h4 : HasLeadingRate (fun t => c4 * t ^ 4) 4 c4 := by
    have h := (hasLeadingRate_pow 4).const_mul c4
    simpa using h
  exact h2.add_of_lt h4 (by omega)

/-- The no-LN contrast: without the mean-subtraction leak the
    observable above the floor has leading rate 4. -/
theorem noln_direct_rate (c4 : ℝ) :
    HasLeadingRate (fun t => c4 * t ^ 4) 4 c4 := by
  have h := (hasLeadingRate_pow 4).const_mul c4
  simpa using h

/-! ### The O(1) leak at the pointwise level

thm:ln_finite_t_mlp's mechanism is the dead post-LN channel
z_h(t) = (t·x_h − μ(t))/σ(t): at t = 0 the mean subtraction leaves
−((d−1)/d)·x̄/σ₀, so the output y_h = t·z_h(t) has derivative z_h(0)
at the singularity and is O(t) with an O(1) random amplitude, where
the no-LN output would be O(t²). The t² coefficient of the moment is
the second moment of this derivative. Here d = m + 1 with m non-dead
channels w. -/

section LeakMechanism

variable {m : ℕ}

/-- The LN mean at approach parameter t. -/
noncomputable def lnMean (w : Fin m → ℝ) (xh t : ℝ) : ℝ :=
  ((∑ j, w j) + t * xh) / (m + 1)

/-- The LN variance at t. -/
noncomputable def lnVar (w : Fin m → ℝ) (xh t : ℝ) : ℝ :=
  ((∑ j, (w j - lnMean w xh t) ^ 2) + (t * xh - lnMean w xh t) ^ 2) / (m + 1)

/-- The dead post-LN channel. -/
noncomputable def lnZ (w : Fin m → ℝ) (xh t : ℝ) : ℝ :=
  (t * xh - lnMean w xh t) / Real.sqrt (lnVar w xh t)

/-- At t = 0 the dead channel carries the mean-subtraction leak
    −x̄_{d}/σ₀ with x̄_d = Σw/(m+1): the O(1) amplitude. -/
lemma lnZ_zero (w : Fin m → ℝ) (xh : ℝ) :
    lnZ w xh 0 = -(((∑ j, w j) / (m + 1)) / Real.sqrt (lnVar w xh 0)) := by
  unfold lnZ lnMean
  rw [zero_mul, add_zero, zero_sub, neg_div]

/-- The leak amplitude in the paper's normalisation: with x̄ the mean
    of the m non-dead channels, Σw/(m+1) = (m/(m+1))·x̄. -/
lemma leak_amplitude_normalised (w : Fin m → ℝ) (hm : (m:ℝ) ≠ 0) :
    (∑ j, w j) / (m + 1) = ((m:ℝ) / (m + 1)) * ((∑ j, w j) / m) := by
  field_simp

/-- The dead output y_h = t·z_h(t) has derivative z_h(0) at t = 0:
    the O(1) leak makes it O(t), against the no-LN O(t²). -/
theorem ln_leak_derivative (w : Fin m → ℝ) (xh : ℝ)
    (hσ : 0 < lnVar w xh 0) :
    HasDerivAt (fun t => t * lnZ w xh t) (lnZ w xh 0) 0 := by
  have hz : DifferentiableAt ℝ (lnZ w xh) 0 := by
    unfold lnZ
    apply DifferentiableAt.div
    · unfold lnMean
      fun_prop
    · apply DifferentiableAt.sqrt
      · unfold lnVar lnMean
        fun_prop
      · exact ne_of_gt hσ
    · exact ne_of_gt (Real.sqrt_pos.mpr hσ)
  have h := (hasDerivAt_id (0:ℝ)).mul hz.hasDerivAt
  simpa using h

end LeakMechanism

/-! ### The t⁴ coefficient: z_h(t)² to second order, exactly

The LN variance along the approach is an exact quadratic in t, so
z_h(t)² = (t·x_h − μ(t))²/σ(t)² is a rational function of t whose
Taylor coefficients at 0 are explicit in the data. The second
coefficient p₂ is the closed-form integrand of R₂ = E[p₂]; the first
is odd in x_h, which is why R(t) is even and the moment carries no t³
term. The expansion is an exact identity with the remainder
t³·q(t)/σ(t)², bounded near 0 by continuity of σ(t)² at σ₀² > 0. -/

section SecondOrder

variable {m : ℕ}

/-- The variance coefficients: v(t) = v₀ + v₁t + v₂t² with
    v₁ = −2(Σw)x_h/d² and v₂ = m·x_h²/d², d = m + 1. -/
lemma lnVar_eq_quadratic (w : Fin m → ℝ) (xh t : ℝ) :
    lnVar w xh t = lnVar w xh 0
      + (-(2 * (∑ j, w j) * xh / ((m:ℝ) + 1) ^ 2)) * t
      + ((m:ℝ) * xh ^ 2 / ((m:ℝ) + 1) ^ 2) * t ^ 2 := by
  have hexp : ∀ μ : ℝ, ∑ j, (w j - μ) ^ 2
      = ∑ j, w j ^ 2 - 2 * μ * ∑ j, w j + (m:ℝ) * μ ^ 2 := by
    intro μ
    have h : ∀ j, (w j - μ) ^ 2 = w j ^ 2 - 2 * μ * w j + μ ^ 2 :=
      fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold lnVar lnMean
  rw [hexp, hexp]
  have hm : ((m:ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- The leak amplitude μ₀ = Σw/d. -/
noncomputable def lnMu0 (w : Fin m → ℝ) : ℝ := (∑ j, w j) / ((m:ℝ) + 1)

/-- The dead-channel slope A = m·x_h/d, so that t·x_h − μ(t) = −μ₀ + A·t. -/
noncomputable def lnA (m : ℕ) (xh : ℝ) : ℝ := (m:ℝ) * xh / ((m:ℝ) + 1)

/-- The variance's first coefficient v₁ = −2(Σw)x_h/d². -/
noncomputable def lnV1 (w : Fin m → ℝ) (xh : ℝ) : ℝ :=
  -(2 * (∑ j, w j) * xh / ((m:ℝ) + 1) ^ 2)

/-- The variance's second coefficient v₂ = m·x_h²/d². -/
noncomputable def lnV2 (m : ℕ) (xh : ℝ) : ℝ := (m:ℝ) * xh ^ 2 / ((m:ℝ) + 1) ^ 2

/-- p₀ = μ₀²/v₀, the leak's squared amplitude. -/
noncomputable def lnP0 (w : Fin m → ℝ) (xh : ℝ) : ℝ :=
  lnMu0 w ^ 2 / lnVar w xh 0

/-- p₁ = (−2μ₀Av₀ − μ₀²v₁)/v₀², odd in x_h. -/
noncomputable def lnP1 (w : Fin m → ℝ) (xh : ℝ) : ℝ :=
  (-2 * lnMu0 w * lnA m xh * lnVar w xh 0 - lnMu0 w ^ 2 * lnV1 w xh)
    / lnVar w xh 0 ^ 2

/-- p₂ = A²/v₀ + 2μ₀Av₁/v₀² + μ₀²(v₁²/v₀³ − v₂/v₀²), the closed-form
    integrand of R₂. -/
noncomputable def lnP2 (w : Fin m → ℝ) (xh : ℝ) : ℝ :=
  lnA m xh ^ 2 / lnVar w xh 0
    + 2 * lnMu0 w * lnA m xh * lnV1 w xh / lnVar w xh 0 ^ 2
    + lnMu0 w ^ 2 * (lnV1 w xh ^ 2 / lnVar w xh 0 ^ 3 - lnV2 m xh / lnVar w xh 0 ^ 2)

/-- The remainder numerator q(t) = −(p₁v₂ + p₂v₁) − p₂v₂·t. -/
noncomputable def lnQ (w : Fin m → ℝ) (xh t : ℝ) : ℝ :=
  -(lnP1 w xh * lnV2 m xh + lnP2 w xh * lnV1 w xh) - lnP2 w xh * lnV2 m xh * t

lemma lnVar_nonneg (w : Fin m → ℝ) (xh t : ℝ) : 0 ≤ lnVar w xh t := by
  unfold lnVar
  positivity

/-- The exact second-order identity:
    z_h(t)² = p₀ + p₁t + p₂t² + t³·q(t)/σ(t)² wherever σ(t)² ≠ 0. -/
theorem lnZ_sq_expansion (w : Fin m → ℝ) (xh t : ℝ)
    (hσ : 0 < lnVar w xh 0) (hv : lnVar w xh t ≠ 0) :
    lnZ w xh t ^ 2
      = lnP0 w xh + lnP1 w xh * t + lnP2 w xh * t ^ 2
        + t ^ 3 * (lnQ w xh t / lnVar w xh t) := by
  have hsq : lnZ w xh t ^ 2 = (t * xh - lnMean w xh t) ^ 2 / lnVar w xh t := by
    unfold lnZ
    rw [div_pow, Real.sq_sqrt (lnVar_nonneg w xh t)]
  have hN : t * xh - lnMean w xh t = -lnMu0 w + lnA m xh * t := by
    unfold lnMean lnMu0 lnA
    have hm : ((m:ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [hsq, hN]
  have hquad : lnVar w xh t = lnVar w xh 0 + lnV1 w xh * t + lnV2 m xh * t ^ 2 := by
    rw [lnVar_eq_quadratic]
    rfl
  rw [div_eq_iff hv, add_mul, mul_assoc, div_mul_cancel₀ _ hv, hquad]
  unfold lnQ lnP0 lnP1 lnP2
  have hv0 : lnVar w xh 0 ≠ 0 := ne_of_gt hσ
  field_simp
  ring

/-- p₁ is odd in x_h: the t³ term of the moment vanishes under the
    sign symmetry of the dead input, so R(t) is even. -/
theorem lnP1_odd (w : Fin m → ℝ) (xh : ℝ) :
    lnP1 w (-xh) = -lnP1 w xh := by
  have hv : lnVar w (-xh) 0 = lnVar w xh 0 := by
    simp [lnVar, lnMean]
  unfold lnP1
  rw [hv]
  unfold lnA lnV1
  ring

/-- The remainder is bounded near the singularity: σ(t)² stays above
    σ₀²/2 and q(t) is continuous, so |t³·q(t)/σ(t)²| ≤ M·|t|³
    eventually. -/
theorem lnZ_sq_remainder_bounded (w : Fin m → ℝ) (xh : ℝ)
    (hσ : 0 < lnVar w xh 0) :
    ∃ M : ℝ, ∀ᶠ t in 𝓝 (0:ℝ),
      |t ^ 3 * (lnQ w xh t / lnVar w xh t)| ≤ M * |t| ^ 3 := by
  have hcontv : Continuous (lnVar w xh) := by
    unfold lnVar lnMean
    fun_prop
  have hcontq : Continuous (lnQ w xh) := by
    unfold lnQ
    fun_prop
  have hv : ∀ᶠ t in 𝓝 (0:ℝ), lnVar w xh 0 / 2 < lnVar w xh t :=
    (hcontv.tendsto 0).eventually (lt_mem_nhds (half_lt_self hσ))
  have hq : ∀ᶠ t in 𝓝 (0:ℝ), |lnQ w xh t| < |lnQ w xh 0| + 1 := by
    have h := (hcontq.tendsto 0).eventually
      (Metric.ball_mem_nhds (lnQ w xh 0) one_pos)
    filter_upwards [h] with t ht
    simp only [Real.dist_eq] at ht
    calc |lnQ w xh t| = |lnQ w xh 0 + (lnQ w xh t - lnQ w xh 0)| := by ring_nf
      _ ≤ |lnQ w xh 0| + |lnQ w xh t - lnQ w xh 0| := abs_add_le _ _
      _ < |lnQ w xh 0| + 1 := by linarith
  refine ⟨(|lnQ w xh 0| + 1) / (lnVar w xh 0 / 2), ?_⟩
  filter_upwards [hv, hq] with t hvt hqt
  have hvpos : 0 < lnVar w xh t := lt_trans (by positivity) hvt
  have h1 : |lnQ w xh t| / lnVar w xh t
      ≤ (|lnQ w xh 0| + 1) / (lnVar w xh 0 / 2) := by
    rw [div_le_div_iff₀ hvpos (by positivity)]
    nlinarith [abs_nonneg (lnQ w xh t), hqt, hvt]
  calc |t ^ 3 * (lnQ w xh t / lnVar w xh t)|
      = |t| ^ 3 * (|lnQ w xh t| / lnVar w xh t) := by
        rw [abs_mul, abs_div, abs_of_pos hvpos, abs_pow]
    _ ≤ |t| ^ 3 * ((|lnQ w xh 0| + 1) / (lnVar w xh 0 / 2)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (|lnQ w xh 0| + 1) / (lnVar w xh 0 / 2) * |t| ^ 3 := by ring

end SecondOrder

/-! ### The assembled moment identity

The directional Fisher is the second moment of the residual
y_h − Y_h = t·z_h(x) − η against an independent zero-mean noise η of
variance v: the cross term vanishes and the moment is
t²·E[z_h²] + v. With the pointwise expansion of z_h² and an integrable
remainder bound this is the three-term structure of
thm:ln_finite_t_mlp (up to the factor 4 of the loss gradient):
v + t²E[p₀] + t³E[p₁] + t⁴E[p₂] + O(t⁵), E[p₁] vanishing by the sign
symmetry of the dead input. -/

section AssembledMoment

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The residual moment against independent zero-mean Gaussian noise:
    ∫ (f(x) − η)² = ∫ f² + v. -/
theorem residual_moment_product [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) (v : NNReal) :
    ∫ z : Ω × ℝ, (f z.1 - z.2) ^ 2 ∂(μ.prod (gaussianReal 0 v))
      = (∫ x, f x ^ 2 ∂μ) + v := by
  set ν := gaussianReal 0 v with hν
  have hexp : ∀ z : Ω × ℝ, (f z.1 - z.2) ^ 2
      = f z.1 ^ 2 + ((-2) * f z.1) * z.2 + z.2 ^ 2 := fun z => by ring
  have h1 : Integrable (fun z : Ω × ℝ => f z.1 ^ 2) (μ.prod ν) := hf2.comp_fst ν
  have h2 : Integrable (fun z : Ω × ℝ => ((-2) * f z.1) * z.2) (μ.prod ν) :=
    Integrable.mul_prod (hf.const_mul (-2)) (integrable_id_gaussianReal v)
  have h3 : Integrable (fun z : Ω × ℝ => z.2 ^ 2) (μ.prod ν) :=
    (integrable_sq_gaussianReal v).comp_snd μ
  calc ∫ z : Ω × ℝ, (f z.1 - z.2) ^ 2 ∂(μ.prod ν)
      = ∫ z : Ω × ℝ, (f z.1 ^ 2 + ((-2) * f z.1) * z.2 + z.2 ^ 2) ∂(μ.prod ν) := by
        congr 1
        funext z
        exact hexp z
    _ = (∫ z : Ω × ℝ, (f z.1 ^ 2 + ((-2) * f z.1) * z.2) ∂(μ.prod ν))
        + ∫ z : Ω × ℝ, z.2 ^ 2 ∂(μ.prod ν) := integral_add (h1.add h2) h3
    _ = (∫ z : Ω × ℝ, f z.1 ^ 2 ∂(μ.prod ν))
        + (∫ z : Ω × ℝ, ((-2) * f z.1) * z.2 ∂(μ.prod ν))
        + ∫ z : Ω × ℝ, z.2 ^ 2 ∂(μ.prod ν) := by rw [integral_add h1 h2]
    _ = (∫ x, f x ^ 2 ∂μ) + 0 + v := by
        have hfst : ∫ z : Ω × ℝ, f z.1 ^ 2 ∂(μ.prod ν) = ∫ x, f x ^ 2 ∂μ := by
          have hp := integral_prod_mul (μ := μ) (ν := ν)
            (f := fun x => f x ^ 2) (g := fun _ => (1:ℝ))
          beta_reduce at hp
          rw [show (fun z : Ω × ℝ => f z.1 ^ 2)
              = fun z : Ω × ℝ => f z.1 ^ 2 * 1 from funext fun z => (mul_one _).symm,
            hp]
          simp
        have hcross : ∫ z : Ω × ℝ, ((-2) * f z.1) * z.2 ∂(μ.prod ν) = 0 := by
          have hp := integral_prod_mul (μ := μ) (ν := ν)
            (f := fun x => (-2) * f x) (g := fun y => y)
          beta_reduce at hp
          rw [hp]
          have hm : ∫ y : ℝ, y ∂ν = 0 := by
            rw [hν]
            simp
          rw [hm, mul_zero]
        have hsnd : ∫ z : Ω × ℝ, z.2 ^ 2 ∂(μ.prod ν) = v := by
          have hp := integral_prod_mul (μ := μ) (ν := ν)
            (f := fun _ => (1:ℝ)) (g := fun y => y ^ 2)
          beta_reduce at hp
          rw [show (fun z : Ω × ℝ => z.2 ^ 2)
              = fun z : Ω × ℝ => 1 * z.2 ^ 2 from funext fun z => (one_mul _).symm,
            hp, integral_sq_gaussianReal]
          simp
        rw [hfst, hcross, hsnd]
    _ = (∫ x, f x ^ 2 ∂μ) + v := by ring

/-- thm:ln_finite_t_mlp's moment identity assembled: with the dead
    input (w, x_h) drawn from μ and independent noise of variance v,
    the residual moment is t²E[z_h(t)²] + v, and with integrable
    expansion coefficients and an integrable remainder bound it reads
    v + t²E[p₀] + t³E[p₁] + t⁴E[p₂] up to R·|t|⁵. -/
theorem ln_moment_assembled [IsProbabilityMeasure μ] {m : ℕ}
    (W : Ω → Fin m → ℝ) (X : Ω → ℝ) (v : NNReal)
    (hσ : ∀ ω, 0 < lnVar (W ω) (X ω) 0)
    (hz : ∀ t, Integrable (fun ω => lnZ (W ω) (X ω) t) μ)
    (hz2 : ∀ t, Integrable (fun ω => lnZ (W ω) (X ω) t ^ 2) μ)
    (hp0 : Integrable (fun ω => lnP0 (W ω) (X ω)) μ)
    (hp1 : Integrable (fun ω => lnP1 (W ω) (X ω)) μ)
    (hp2 : Integrable (fun ω => lnP2 (W ω) (X ω)) μ)
    (Mrem : Ω → ℝ) (hM : Integrable Mrem μ) {δ : ℝ}
    (hvne : ∀ ω t, |t| < δ → lnVar (W ω) (X ω) t ≠ 0)
    (hrem : ∀ ω t, |t| < δ →
      |t ^ 3 * (lnQ (W ω) (X ω) t / lnVar (W ω) (X ω) t)| ≤ Mrem ω * |t| ^ 3) :
    ∀ t, |t| < δ →
      |(∫ z : Ω × ℝ, (t * lnZ (W z.1) (X z.1) t - z.2) ^ 2 ∂(μ.prod (gaussianReal 0 v)))
          - (v + t ^ 2 * ∫ ω, lnP0 (W ω) (X ω) ∂μ
            + t ^ 3 * ∫ ω, lnP1 (W ω) (X ω) ∂μ
            + t ^ 4 * ∫ ω, lnP2 (W ω) (X ω) ∂μ)|
        ≤ (∫ ω, Mrem ω ∂μ) * |t| ^ 5 := by
  intro t ht
  have hres := residual_moment_product (μ := μ)
    (fun ω => t * lnZ (W ω) (X ω) t) ((hz t).const_mul t)
    (by
      have := (hz2 t).const_mul (t ^ 2)
      refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
      beta_reduce
      ring) v
  rw [hres]
  -- the expansion inside the integral
  have hexp : ∀ ω, (t * lnZ (W ω) (X ω) t) ^ 2
      = t ^ 2 * lnP0 (W ω) (X ω) + t ^ 3 * lnP1 (W ω) (X ω)
        + t ^ 4 * lnP2 (W ω) (X ω)
        + t ^ 2 * (t ^ 3 * (lnQ (W ω) (X ω) t / lnVar (W ω) (X ω) t)) := by
    intro ω
    rw [mul_pow, lnZ_sq_expansion (W ω) (X ω) t (hσ ω) (hvne ω t ht)]
    ring
  have hremI : Integrable
      (fun ω => t ^ 2 * (t ^ 3 * (lnQ (W ω) (X ω) t / lnVar (W ω) (X ω) t))) μ := by
    have hmeas : AEStronglyMeasurable
        (fun ω => t ^ 2 * (t ^ 3 * (lnQ (W ω) (X ω) t / lnVar (W ω) (X ω) t))) μ := by
      have h := (hz2 t).aestronglyMeasurable.const_mul (t ^ 2)
      have hpoly : AEStronglyMeasurable
          (fun ω => t ^ 2 * lnP0 (W ω) (X ω) + t ^ 3 * lnP1 (W ω) (X ω)
            + t ^ 4 * lnP2 (W ω) (X ω)) μ :=
        ((hp0.aestronglyMeasurable.const_mul _).add
          (hp1.aestronglyMeasurable.const_mul _)).add
          (hp2.aestronglyMeasurable.const_mul _)
      have := h.sub hpoly
      refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
      have e := hexp ω
      simp only [Pi.sub_apply]
      linear_combination e
    refine Integrable.mono' (hM.const_mul (t ^ 2 * |t| ^ 3)) hmeas ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg t)]
    have := hrem ω t ht
    nlinarith [sq_nonneg t, abs_nonneg (t ^ 3 * (lnQ (W ω) (X ω) t / lnVar (W ω) (X ω) t))]
  have hsplit : ∫ ω, (t * lnZ (W ω) (X ω) t) ^ 2 ∂μ
      = t ^ 2 * ∫ ω, lnP0 (W ω) (X ω) ∂μ + t ^ 3 * ∫ ω, lnP1 (W ω) (X ω) ∂μ
        + t ^ 4 * ∫ ω, lnP2 (W ω) (X ω) ∂μ
        + ∫ ω, t ^ 2 * (t ^ 3 * (lnQ (W ω) (X ω) t / lnVar (W ω) (X ω) t)) ∂μ := by
    simp_rw [hexp]
    rw [integral_add, integral_add, integral_add, integral_const_mul,
      integral_const_mul, integral_const_mul]
    · exact hp0.const_mul _
    · exact hp1.const_mul _
    · exact (hp0.const_mul _).add (hp1.const_mul _)
    · exact hp2.const_mul _
    · exact ((hp0.const_mul _).add (hp1.const_mul _)).add (hp2.const_mul _)
    · exact hremI
  rw [hsplit]
  have hbound : |∫ ω, t ^ 2 * (t ^ 3 * (lnQ (W ω) (X ω) t / lnVar (W ω) (X ω) t)) ∂μ|
      ≤ (∫ ω, Mrem ω ∂μ) * |t| ^ 5 := by
    have h1 := norm_integral_le_integral_norm
      (fun ω => t ^ 2 * (t ^ 3 * (lnQ (W ω) (X ω) t / lnVar (W ω) (X ω) t))) (μ := μ)
    rw [Real.norm_eq_abs] at h1
    have h2 : ∫ ω, ‖t ^ 2 * (t ^ 3 * (lnQ (W ω) (X ω) t / lnVar (W ω) (X ω) t))‖ ∂μ
        ≤ ∫ ω, Mrem ω * |t| ^ 5 ∂μ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _)
        (hM.mul_const _) (Filter.Eventually.of_forall fun ω => ?_)
      beta_reduce
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg t)]
      have := hrem ω t ht
      have h5 : |t| ^ 5 = t ^ 2 * |t| ^ 3 := by
        have hsq : |t| ^ 2 = t ^ 2 := sq_abs t
        calc |t| ^ 5 = |t| ^ 2 * |t| ^ 3 := by ring
          _ = t ^ 2 * |t| ^ 3 := by rw [hsq]
      rw [h5]
      nlinarith [sq_nonneg t, abs_nonneg (t ^ 3 * (lnQ (W ω) (X ω) t / lnVar (W ω) (X ω) t))]
    rw [integral_mul_const] at h2
    exact le_trans h1 h2
  have hre : (t ^ 2 * ∫ ω, lnP0 (W ω) (X ω) ∂μ + t ^ 3 * ∫ ω, lnP1 (W ω) (X ω) ∂μ
        + t ^ 4 * ∫ ω, lnP2 (W ω) (X ω) ∂μ
        + ∫ ω, t ^ 2 * (t ^ 3 * (lnQ (W ω) (X ω) t / lnVar (W ω) (X ω) t)) ∂μ) + v
      - (v + t ^ 2 * ∫ ω, lnP0 (W ω) (X ω) ∂μ + t ^ 3 * ∫ ω, lnP1 (W ω) (X ω) ∂μ
        + t ^ 4 * ∫ ω, lnP2 (W ω) (X ω) ∂μ)
      = ∫ ω, t ^ 2 * (t ^ 3 * (lnQ (W ω) (X ω) t / lnVar (W ω) (X ω) t)) ∂μ := by ring
  rw [hre]
  exact hbound

end AssembledMoment

end DeadDirections
