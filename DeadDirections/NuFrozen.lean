/-
  The frozen-Z skeleton of the ν universality theorem.

  Along a dead line of leading order k the renormalised posterior is
  π_Z(η) ∝ exp(Zη^k − η^{2k}), and the universal constant ν_LO(k)
  averages Var_{π_Z}[η^k] over Z ∼ N(0, 2); that average has no closed
  form and the paper reports it numerically. Everything the theorem
  states about the frozen posterior π₀ ∝ e^{−η^{2k}} is analytic and
  is certified here. The statistic T = η^{2k} has the Gamma(λ, 1) law
  with λ = 1/(2k), so E[T] = λ and E[√T] = Γ(λ + ½)/Γ(λ); the variance
  of η^k under π₀ is ν^{√T}(k) = λ − (Γ(λ+½)/Γ(λ))² for even k and λ
  for odd k, the odd case because η^k is odd and π₀ symmetric. The
  model-specific coefficient enters the leading-order posterior only
  through a rescaling of the dead coordinate, and every expectation
  ratio is invariant under that rescaling; this is the scale
  invariance behind "depends only on k". The central-limit step that
  makes Z Gaussian and the leading-order replacement of the posterior
  are the paper's asymptotic argument and stay outside.
-/
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance

namespace DeadDirections

open MeasureTheory Set Filter

section FrozenLaw

variable {k : ℕ}

/-- The unnormalised frozen-Z density e^{−η^{2k}}. -/
noncomputable def frozenDensity (k : ℕ) (η : ℝ) : ℝ := Real.exp (-(η ^ (2 * k)))

/-- Expectation under the frozen posterior π₀ ∝ e^{−η^{2k}}. -/
noncomputable def frozenExp (k : ℕ) (f : ℝ → ℝ) : ℝ :=
  (∫ η, f η * frozenDensity k η) / (∫ η, frozenDensity k η)

/-- Variance under the frozen posterior. -/
noncomputable def frozenVar (k : ℕ) (f : ℝ → ℝ) : ℝ :=
  frozenExp k (fun η => f η ^ 2) - (frozenExp k f) ^ 2

/-- λ = 1/(2k), the shape of the Gamma law of T = η^{2k}. -/
noncomputable def frozenShape (k : ℕ) : ℝ := 1 / (2 * k)

/-- ν^{√T}(k) = λ − (Γ(λ+½)/Γ(λ))², the frozen-Z variance of √T. -/
noncomputable def nuSqrtT (k : ℕ) : ℝ :=
  frozenShape k - (Real.Gamma (frozenShape k + 1 / 2) / Real.Gamma (frozenShape k)) ^ 2

lemma frozenShape_pos (hk : 0 < k) : 0 < frozenShape k := by
  have : (0:ℝ) < k := by exact_mod_cast hk
  unfold frozenShape
  exact div_pos one_pos (by linarith)

/-- The substitution T = x^{2k} on the half line: the pushforward of
    e^{−x^{2k}}dx is the Gamma(λ, 1) density up to the factor λ. -/
theorem frozen_half_line (hk : 0 < k) (g : ℝ → ℝ) :
    ∫ x in Ioi (0:ℝ), g (x ^ (2 * k)) * Real.exp (-(x ^ (2 * k)))
      = frozenShape k
        * ∫ y in Ioi (0:ℝ), y ^ (frozenShape k - 1) * (g y * Real.exp (-y)) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  set p : ℝ := 2 * k with hp
  have hp0 : 0 < p := by rw [hp]; linarith
  have hp' : p ≠ 0 := hp0.ne'
  set G : ℝ → ℝ := fun y => (1 / p) * (y ^ (1 / p - 1) * (g y * Real.exp (-y))) with hG
  have key := integral_comp_rpow_Ioi_of_pos (g := G) hp0
  have hL : ∫ x in Ioi (0:ℝ), (p * x ^ (p - 1)) • G (x ^ p)
      = ∫ x in Ioi (0:ℝ), g (x ^ (2 * k)) * Real.exp (-(x ^ (2 * k))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0:ℝ) < x := hx
    have h1 : (x ^ p) ^ (1 / p - 1) = x ^ (1 - p) := by
      rw [← Real.rpow_mul hx0.le]
      congr 1
      rw [mul_sub, mul_one_div_cancel hp', mul_one]
    have h2 : x ^ p = x ^ (2 * k) := by
      rw [hp, show (2:ℝ) * k = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have h3 : x ^ (1 - p) = (x ^ (p - 1))⁻¹ := by
      rw [show (1:ℝ) - p = -(p - 1) by ring, Real.rpow_neg hx0.le]
    have h4 : x ^ (p - 1) ≠ 0 := (Real.rpow_pos_of_pos hx0 _).ne'
    simp only [smul_eq_mul, hG]
    rw [h1, h2, h3]
    field_simp
  have hR : ∫ y in Ioi (0:ℝ), G y
      = frozenShape k
        * ∫ y in Ioi (0:ℝ), y ^ (frozenShape k - 1) * (g y * Real.exp (-y)) := by
    simp only [hG, frozenShape, hp]
    exact integral_const_mul _ _
  rw [← hL, key, hR]

/-- An even integrable function integrates to twice its half-line
    integral. -/
theorem integral_even_split {h : ℝ → ℝ} (hint : Integrable h)
    (heven : ∀ x, h (-x) = h x) :
    ∫ x, h x = 2 * ∫ x in Ioi (0:ℝ), h x := by
  have hsplit := integral_add_compl (μ := volume) (measurableSet_Ioi (a := (0:ℝ))) hint
  rw [compl_Ioi] at hsplit
  have hneg : ∫ x in Iic (0:ℝ), h x = ∫ x in Ioi (0:ℝ), h x := by
    have h1 := integral_comp_neg_Ioi (0:ℝ) h
    rw [neg_zero] at h1
    rw [← h1]
    exact setIntegral_congr_fun measurableSet_Ioi fun x _ => heven x
  linarith [hsplit, hneg]

/-- An odd integrable function integrates to zero. -/
theorem integral_odd_zero {h : ℝ → ℝ} (hint : Integrable h)
    (hodd : ∀ x, h (-x) = -h x) :
    ∫ x, h x = 0 := by
  have hsplit := integral_add_compl (μ := volume) (measurableSet_Ioi (a := (0:ℝ))) hint
  rw [compl_Ioi] at hsplit
  have hneg : ∫ x in Iic (0:ℝ), h x = -∫ x in Ioi (0:ℝ), h x := by
    have h1 := integral_comp_neg_Ioi (0:ℝ) h
    rw [neg_zero] at h1
    rw [← h1, ← integral_neg]
    exact setIntegral_congr_fun measurableSet_Ioi fun x _ => hodd x
  linarith [hsplit, hneg]

/-- e^{−x^{2k}} ≤ e·e^{−x²}: the frozen density is dominated by a
    Gaussian. -/
lemma exp_neg_pow_le (hk : 0 < k) (x : ℝ) :
    Real.exp (-(x ^ (2 * k))) ≤ Real.exp 1 * Real.exp (-(x ^ 2)) := by
  rw [← Real.exp_add, Real.exp_le_exp, pow_mul]
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  rcases le_or_gt (x ^ 2) 1 with h | h
  · have : 0 ≤ (x ^ 2) ^ k := pow_nonneg hx2 k
    linarith
  · have : x ^ 2 ≤ (x ^ 2) ^ k := le_self_pow₀ h.le hk.ne'
    linarith

/-- Every polynomial moment of the frozen density is integrable. -/
theorem integrable_pow_abs_mul_frozen (hk : 0 < k) (m : ℕ) :
    Integrable (fun x : ℝ => |x| ^ m * frozenDensity k x) := by
  have h1 : Integrable (fun x : ℝ => x ^ m * Real.exp (-1 * x ^ 2)) := by
    have hm : (-1:ℝ) < m := by
      have : (0:ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    refine (integrable_rpow_mul_exp_neg_mul_sq one_pos hm).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp [Real.rpow_natCast]
  have h2 := (h1.abs).const_mul (Real.exp 1)
  refine h2.mono' (Continuous.aestronglyMeasurable (by unfold frozenDensity; fun_prop))
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, frozenDensity]
  rw [abs_of_nonneg (by positivity), abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  have hle := exp_neg_pow_le hk x
  have hm0 : 0 ≤ |x| ^ m := by positivity
  calc |x| ^ m * Real.exp (-(x ^ (2 * k)))
      ≤ |x| ^ m * (Real.exp 1 * Real.exp (-(x ^ 2))) := by gcongr
    _ = Real.exp 1 * (|x| ^ m * Real.exp (-1 * x ^ 2)) := by rw [neg_one_mul]; ring

lemma frozen_gamma_integral (hk : 0 < k) :
    ∫ y in Ioi (0:ℝ), y ^ (frozenShape k - 1) * Real.exp (-y)
      = Real.Gamma (frozenShape k) := by
  rw [Real.Gamma_eq_integral (frozenShape_pos hk)]
  exact setIntegral_congr_fun measurableSet_Ioi fun y _ => mul_comm _ _

/-- The normalisation ∫ e^{−η^{2k}} dη = 2λΓ(λ). -/
theorem frozen_normalisation (hk : 0 < k) :
    ∫ η, frozenDensity k η = 2 * frozenShape k * Real.Gamma (frozenShape k) := by
  have hint : Integrable (fun x : ℝ => frozenDensity k x) := by
    simpa using integrable_pow_abs_mul_frozen hk 0
  have heven : ∀ x : ℝ, frozenDensity k (-x) = frozenDensity k x := by
    intro x
    simp [frozenDensity, Even.neg_pow (even_two_mul k)]
  rw [integral_even_split hint heven]
  have h := frozen_half_line hk (fun _ => (1:ℝ))
  simp only [one_mul] at h
  have h' : ∫ x in Ioi (0:ℝ), frozenDensity k x
      = ∫ x in Ioi (0:ℝ), Real.exp (-(x ^ (2 * k))) := rfl
  rw [h', h, frozen_gamma_integral hk]
  ring

/-- The first moment of T = η^{2k}: ∫ η^{2k} e^{−η^{2k}} = 2λ·λΓ(λ). -/
theorem frozen_T_integral (hk : 0 < k) :
    ∫ η, η ^ (2 * k) * frozenDensity k η
      = 2 * frozenShape k * (frozenShape k * Real.Gamma (frozenShape k)) := by
  have hint : Integrable (fun x : ℝ => x ^ (2 * k) * frozenDensity k x) := by
    have := integrable_pow_abs_mul_frozen hk (2 * k)
    simpa [Even.pow_abs (even_two_mul k)] using this
  have heven : ∀ x : ℝ, (-x) ^ (2 * k) * frozenDensity k (-x)
      = x ^ (2 * k) * frozenDensity k x := by
    intro x
    simp [frozenDensity, Even.neg_pow (even_two_mul k)]
  rw [integral_even_split hint heven]
  have h : ∫ x in Ioi (0:ℝ), x ^ (2 * k) * frozenDensity k x
      = frozenShape k
        * ∫ y in Ioi (0:ℝ), y ^ (frozenShape k - 1) * (y * Real.exp (-y)) :=
    frozen_half_line hk (fun y => y)
  have hsh : ∫ y in Ioi (0:ℝ), y ^ (frozenShape k - 1) * (y * Real.exp (-y))
      = ∫ y in Ioi (0:ℝ), y ^ (frozenShape k + 1 - 1) * Real.exp (-y) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : (0:ℝ) < y := hy
    rw [show frozenShape k + 1 - 1 = (frozenShape k - 1) + 1 by ring,
      Real.rpow_add_one hy0.ne']
    ring
  have hG : ∫ y in Ioi (0:ℝ), y ^ (frozenShape k + 1 - 1) * Real.exp (-y)
      = Real.Gamma (frozenShape k + 1) := by
    rw [Real.Gamma_eq_integral (by linarith [frozenShape_pos hk])]
    exact setIntegral_congr_fun measurableSet_Ioi fun y _ => mul_comm _ _
  rw [h, hsh, hG, Real.Gamma_add_one (frozenShape_pos hk).ne']
  ring

/-- The first moment of √T = |η|^k: ∫ |η|^k e^{−η^{2k}} = 2λΓ(λ + ½). -/
theorem frozen_sqrtT_integral (hk : 0 < k) :
    ∫ η, |η| ^ k * frozenDensity k η
      = 2 * frozenShape k * Real.Gamma (frozenShape k + 1 / 2) := by
  have hint := integrable_pow_abs_mul_frozen hk k
  have heven : ∀ x : ℝ, |-x| ^ k * frozenDensity k (-x) = |x| ^ k * frozenDensity k x := by
    intro x
    simp [frozenDensity, Even.neg_pow (even_two_mul k)]
  rw [integral_even_split hint heven]
  have hhalf : ∫ x in Ioi (0:ℝ), |x| ^ k * frozenDensity k x
      = ∫ x in Ioi (0:ℝ), (x ^ (2 * k)) ^ ((1:ℝ) / 2) * Real.exp (-(x ^ (2 * k))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0:ℝ) < x := hx
    rw [abs_of_pos hx0]
    congr 1
    rw [← Real.sqrt_eq_rpow, pow_mul', Real.sqrt_sq (pow_nonneg hx0.le k)]
  have h : ∫ x in Ioi (0:ℝ), (x ^ (2 * k)) ^ ((1:ℝ) / 2) * Real.exp (-(x ^ (2 * k)))
      = frozenShape k
        * ∫ y in Ioi (0:ℝ), y ^ (frozenShape k - 1) * (y ^ ((1:ℝ) / 2) * Real.exp (-y)) :=
    frozen_half_line hk (fun y => y ^ ((1:ℝ) / 2))
  have hsh : ∫ y in Ioi (0:ℝ), y ^ (frozenShape k - 1) * (y ^ ((1:ℝ) / 2) * Real.exp (-y))
      = ∫ y in Ioi (0:ℝ), y ^ (frozenShape k + 1 / 2 - 1) * Real.exp (-y) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : (0:ℝ) < y := hy
    rw [← mul_assoc, ← Real.rpow_add hy0]
    congr 2
    ring
  have hG : ∫ y in Ioi (0:ℝ), y ^ (frozenShape k + 1 / 2 - 1) * Real.exp (-y)
      = Real.Gamma (frozenShape k + 1 / 2) := by
    rw [Real.Gamma_eq_integral (by linarith [frozenShape_pos hk])]
    exact setIntegral_congr_fun measurableSet_Ioi fun y _ => mul_comm _ _
  rw [hhalf, h, hsh, hG]
  ring

/-- E_{π₀}[T] = λ. -/
theorem frozen_mean_T (hk : 0 < k) :
    frozenExp k (fun η => η ^ (2 * k)) = frozenShape k := by
  have hΓ : Real.Gamma (frozenShape k) ≠ 0 :=
    (Real.Gamma_pos_of_pos (frozenShape_pos hk)).ne'
  have ha : frozenShape k ≠ 0 := (frozenShape_pos hk).ne'
  unfold frozenExp
  rw [frozen_T_integral hk, frozen_normalisation hk]
  field_simp

/-- E_{π₀}[√T] = Γ(λ + ½)/Γ(λ). -/
theorem frozen_mean_sqrtT (hk : 0 < k) :
    frozenExp k (fun η => |η| ^ k)
      = Real.Gamma (frozenShape k + 1 / 2) / Real.Gamma (frozenShape k) := by
  have hΓ : Real.Gamma (frozenShape k) ≠ 0 :=
    (Real.Gamma_pos_of_pos (frozenShape_pos hk)).ne'
  have ha : frozenShape k ≠ 0 := (frozenShape_pos hk).ne'
  unfold frozenExp
  rw [frozen_sqrtT_integral hk, frozen_normalisation hk]
  field_simp

/-- Var_{π₀}[√T] = ν^{√T}(k) = λ − (Γ(λ+½)/Γ(λ))². -/
theorem frozen_var_sqrtT (hk : 0 < k) :
    frozenVar k (fun η => |η| ^ k) = nuSqrtT k := by
  have h2 : (fun η : ℝ => (|η| ^ k) ^ 2) = fun η => η ^ (2 * k) := by
    funext η
    rw [← pow_mul, mul_comm, Even.pow_abs (even_two_mul k)]
  simp only [frozenVar, nuSqrtT]
  rw [h2, frozen_mean_T hk, frozen_mean_sqrtT hk]

/-- Parity, even case: Var_{π₀}[η^k] = ν^{√T}(k). -/
theorem frozen_var_even (hk : 0 < k) (he : Even k) :
    frozenVar k (fun η => η ^ k) = nuSqrtT k := by
  have h : (fun η : ℝ => η ^ k) = fun η => |η| ^ k := by
    funext η
    rw [Even.pow_abs he]
  rw [h, frozen_var_sqrtT hk]

/-- The odd-k mean vanishes by symmetry. -/
theorem frozen_odd_mean_zero (hk : 0 < k) (ho : Odd k) :
    ∫ η, η ^ k * frozenDensity k η = 0 := by
  have hint : Integrable (fun x : ℝ => x ^ k * frozenDensity k x) := by
    refine (integrable_pow_abs_mul_frozen hk k).mono'
      (Continuous.aestronglyMeasurable (by unfold frozenDensity; fun_prop))
      (Filter.Eventually.of_forall fun x => ?_)
    have hpos : 0 < frozenDensity k x := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hpos]
  refine integral_odd_zero hint fun x => ?_
  rw [ho.neg_pow, frozenDensity, frozenDensity, Even.neg_pow (even_two_mul k)]
  ring

/-- Parity, odd case: Var_{π₀}[η^k] = E_{π₀}[T] = λ. -/
theorem frozen_var_odd (hk : 0 < k) (ho : Odd k) :
    frozenVar k (fun η => η ^ k) = frozenShape k := by
  have hmean : frozenExp k (fun η => η ^ k) = 0 := by
    unfold frozenExp
    rw [frozen_odd_mean_zero hk ho, zero_div]
  have h2 : (fun η : ℝ => (η ^ k) ^ 2) = fun η => η ^ (2 * k) := by
    funext η
    rw [← pow_mul, mul_comm]
  simp only [frozenVar]
  rw [h2, hmean, frozen_mean_T hk]
  ring

end FrozenLaw

section ScaleInvariance

variable {k : ℕ}

/-- The renormalised posterior density exp(Zη^k − η^{2k}). -/
noncomputable def renormDensity (k : ℕ) (Z η : ℝ) : ℝ :=
  Real.exp (Z * η ^ k - η ^ (2 * k))

noncomputable def renormExp (k : ℕ) (Z : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ η, f η * renormDensity k Z η) / (∫ η, renormDensity k Z η)

noncomputable def renormVar (k : ℕ) (Z : ℝ) (f : ℝ → ℝ) : ℝ :=
  renormExp k Z (fun η => f η ^ 2) - (renormExp k Z f) ^ 2

/-- The rescaling c = B^{1/(2k)} that takes the model coordinate to
    the dimensionless one. -/
noncomputable def scaleC (k : ℕ) (B : ℝ) : ℝ := B ^ (((2 * k : ℕ) : ℝ)⁻¹)

lemma renormDensity_zero (k : ℕ) : renormDensity k 0 = frozenDensity k := by
  funext η
  simp [renormDensity, frozenDensity]

/-- The frozen posterior is the renormalised posterior at Z = 0. -/
theorem frozenVar_eq_renormVar (k : ℕ) (f : ℝ → ℝ) :
    frozenVar k f = renormVar k 0 f := by
  simp only [frozenVar, frozenExp, renormVar, renormExp, renormDensity_zero]

lemma scaleC_pos {B : ℝ} (hB : 0 < B) : 0 < scaleC k B :=
  Real.rpow_pos_of_pos hB _

lemma scaleC_pow (hk : 0 < k) {B : ℝ} (hB : 0 < B) : scaleC k B ^ (2 * k) = B :=
  Real.rpow_inv_natCast_pow hB.le (by omega)

lemma scaleC_pow_k (hk : 0 < k) {B : ℝ} (hB : 0 < B) : scaleC k B ^ k = Real.sqrt B := by
  have h : (scaleC k B ^ k) ^ 2 = B := by
    rw [← pow_mul, mul_comm, scaleC_pow hk hB]
  rw [show Real.sqrt B = Real.sqrt ((scaleC k B ^ k) ^ 2) by rw [h],
    Real.sqrt_sq (pow_nonneg (scaleC_pos hB).le k)]

/-- The model-scale density exp(A s^k − B s^{2k}) is the renormalised
    density at η = c·s with Z = A/√B. -/
theorem scaled_density_eq (hk : 0 < k) {A B : ℝ} (hB : 0 < B) (s : ℝ) :
    Real.exp (A * s ^ k - B * s ^ (2 * k))
      = renormDensity k (A / Real.sqrt B) (scaleC k B * s) := by
  unfold renormDensity
  congr 1
  rw [mul_pow, mul_pow, scaleC_pow_k hk hB, scaleC_pow hk hB]
  have hs : Real.sqrt B ≠ 0 := (Real.sqrt_pos.mpr hB).ne'
  field_simp

/-- Every expectation ratio of the model-scale posterior, read in the
    dimensionless coordinate, is the renormalised expectation at
    Z = A/√B: the scale B cancels. -/
theorem scaled_ratio_invariant (hk : 0 < k) {A B : ℝ} (hB : 0 < B) (g : ℝ → ℝ) :
    (∫ s, g (scaleC k B * s) * Real.exp (A * s ^ k - B * s ^ (2 * k)))
        / (∫ s, Real.exp (A * s ^ k - B * s ^ (2 * k)))
      = renormExp k (A / Real.sqrt B) g := by
  have hc0 : 0 < scaleC k B := scaleC_pos hB
  have hne : |(scaleC k B)⁻¹| ≠ 0 := (abs_pos.mpr (inv_ne_zero hc0.ne')).ne'
  have h1 : (∫ s, g (scaleC k B * s) * Real.exp (A * s ^ k - B * s ^ (2 * k)))
      = |(scaleC k B)⁻¹| * ∫ η, g η * renormDensity k (A / Real.sqrt B) η := by
    have e1 : (∫ s, g (scaleC k B * s) * Real.exp (A * s ^ k - B * s ^ (2 * k)))
        = ∫ s, (fun η => g η * renormDensity k (A / Real.sqrt B) η) (scaleC k B * s) := by
      congr 1
      funext s
      rw [scaled_density_eq hk hB s]
    rw [e1]
    exact MeasureTheory.Measure.integral_comp_mul_left (fun η => g η * renormDensity k (A / Real.sqrt B) η)
      (scaleC k B)
  have h2 : (∫ s, Real.exp (A * s ^ k - B * s ^ (2 * k)))
      = |(scaleC k B)⁻¹| * ∫ η, renormDensity k (A / Real.sqrt B) η := by
    have e2 : (∫ s, Real.exp (A * s ^ k - B * s ^ (2 * k)))
        = ∫ s, (fun η => renormDensity k (A / Real.sqrt B) η) (scaleC k B * s) := by
      congr 1
      funext s
      rw [scaled_density_eq hk hB s]
    rw [e2]
    exact MeasureTheory.Measure.integral_comp_mul_left (fun η => renormDensity k (A / Real.sqrt B) η) (scaleC k B)
  unfold renormExp
  rw [h1, h2, mul_div_mul_left _ _ hne]

/-- Universality at the renormalised level: the fluctuation of the
    dimensionless coordinate η = c·s under the (A, B) posterior depends
    on (A, B) only through Z = A/√B. -/
theorem nu_scale_invariance (hk : 0 < k) {A B : ℝ} (hB : 0 < B) :
    (∫ s, ((scaleC k B * s) ^ k) ^ 2 * Real.exp (A * s ^ k - B * s ^ (2 * k)))
        / (∫ s, Real.exp (A * s ^ k - B * s ^ (2 * k)))
      - ((∫ s, (scaleC k B * s) ^ k * Real.exp (A * s ^ k - B * s ^ (2 * k)))
        / (∫ s, Real.exp (A * s ^ k - B * s ^ (2 * k)))) ^ 2
      = renormVar k (A / Real.sqrt B) (fun η => η ^ k) := by
  simp only [renormVar]
  rw [← scaled_ratio_invariant hk hB (fun η => (η ^ k) ^ 2),
    ← scaled_ratio_invariant hk hB (fun η => η ^ k)]

end ScaleInvariance

section KOne

open ProbabilityTheory
open scoped NNReal

/-- The Gaussian density at variance one half. -/
lemma gaussianPDFReal_half (m η : ℝ) :
    gaussianPDFReal m (1/2 : ℝ≥0) η = (Real.sqrt Real.pi)⁻¹ * Real.exp (-(η - m) ^ 2) := by
  simp only [gaussianPDFReal_def]
  push_cast
  have h1 : (2:ℝ) * Real.pi * (1 / 2) = Real.pi := by ring
  have h2 : (2:ℝ) * (1 / 2) = 1 := by norm_num
  rw [h1, h2, div_one]

/-- At k = 1 the renormalised density is, up to a constant, the Gaussian
    of mean Z/2 and variance 1/2. -/
lemma renormDensity_one_eq (Z η : ℝ) :
    renormDensity 1 Z η
      = (Real.exp (Z ^ 2 / 4) * Real.sqrt Real.pi) * gaussianPDFReal (Z / 2) (1/2 : ℝ≥0) η := by
  rw [gaussianPDFReal_half]
  unfold renormDensity
  have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h : Real.exp (Z * η ^ 1 - η ^ (2 * 1))
      = Real.exp (Z ^ 2 / 4) * Real.exp (-(η - Z / 2) ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h]
  field_simp

lemma integral_gaussianReal_half (m : ℝ) (g : ℝ → ℝ) :
    ∫ x, g x ∂gaussianReal m (1/2 : ℝ≥0)
      = ∫ x, gaussianPDFReal m (1/2 : ℝ≥0) x * g x := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [smul_eq_mul]

/-- At k = 1 every renormalised expectation is a Gaussian expectation
    at mean Z/2 and variance 1/2. -/
theorem renormExp_one (Z : ℝ) (g : ℝ → ℝ) :
    renormExp 1 Z g = ∫ x, g x ∂gaussianReal (Z / 2) (1/2 : ℝ≥0) := by
  unfold renormExp
  have hC : 0 < Real.exp (Z ^ 2 / 4) * Real.sqrt Real.pi := by positivity
  simp only [renormDensity_one_eq]
  rw [integral_gaussianReal_half]
  have hnum : ∫ x, g x * ((Real.exp (Z ^ 2 / 4) * Real.sqrt Real.pi)
        * gaussianPDFReal (Z / 2) (1/2 : ℝ≥0) x)
      = (Real.exp (Z ^ 2 / 4) * Real.sqrt Real.pi)
        * ∫ x, gaussianPDFReal (Z / 2) (1/2 : ℝ≥0) x * g x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  have hden : ∫ x, (Real.exp (Z ^ 2 / 4) * Real.sqrt Real.pi)
        * gaussianPDFReal (Z / 2) (1/2 : ℝ≥0) x
      = Real.exp (Z ^ 2 / 4) * Real.sqrt Real.pi := by
    rw [integral_const_mul, integral_gaussianPDFReal_eq_one _ (by norm_num), mul_one]
  rw [hnum, hden, mul_div_cancel_left₀ _ hC.ne']

/-- At k = 1 the renormalised fluctuation is 1/2 for every Z: the
    Gaussian variance. -/
theorem renormVar_one (Z : ℝ) : renormVar 1 Z (fun η => η ^ 1) = 1 / 2 := by
  unfold renormVar
  rw [renormExp_one, renormExp_one]
  have hv := variance_id_gaussianReal (μ := Z / 2) (v := (1/2 : ℝ≥0))
  rw [variance_eq_sub (memLp_id_gaussianReal 2)] at hv
  simp only [Pi.pow_apply, id, pow_one] at hv ⊢
  rw [hv]
  norm_num

/-- ν_LO(k): the renormalised fluctuation of η^k averaged over
    Z ∼ N(0, 2). The paper reports it numerically for k ≥ 2. -/
noncomputable def nuLO (k : ℕ) : ℝ :=
  ∫ Z, renormVar k Z (fun η => η ^ k) ∂gaussianReal 0 2

/-- At k = 1 the universal constant is exactly 1/2. -/
theorem nuLO_one : nuLO 1 = 1 / 2 := by
  unfold nuLO
  simp only [renormVar_one]
  simp

/-- At k = 1 the Z-average and the frozen-Z variance agree, the
    boundary case of the paper's strict inequality for k ≥ 2. -/
theorem nuLO_one_eq_frozen : nuLO 1 = frozenVar 1 (fun η => η ^ 1) := by
  rw [nuLO_one, frozen_var_odd one_pos odd_one]
  unfold frozenShape
  norm_num

end KOne

end DeadDirections
