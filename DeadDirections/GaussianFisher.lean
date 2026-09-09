/-
  Geometric Singularity Detection — Lean 4 formalization.

  Conventions (match PRIMER.md / theory paper):
    * Fisher matrix G(θ) = E_{pθ}[(∇ log pθ)(∇ log pθ)ᵀ].
    * Singularity: det G = 0 (a direction with zero information).
    * KL order k: K(θ₀ + t·u) = c·t^{2k} + O(t^{2k+1}); λ = 1/(2k).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import DeadDirections.FisherDecay

namespace DeadDirections
open Real
open MeasureTheory
open scoped ProbabilityTheory

noncomputable section

/-! ## 1. The concrete family (1-parameter Gaussian N(μ, σ²), σ² fixed) -/
/-- Density of N(μ, σ²) at x. -/
def gaussDensity (x mu sigmaSq : ℝ) : ℝ :=
  (2 * π * sigmaSq) ^ (-1 / 2 : ℝ) * Real.exp (-(x - mu) ^ 2 / (2 * sigmaSq))

/-- Log-density log p(x; μ, σ²). -/
def logGauss (x mu sigmaSq : ℝ) : ℝ :=
  -1 / 2 * Real.log (2 * π * sigmaSq) - (x - mu) ^ 2 / (2 * sigmaSq)

/-- Score: ∂/∂μ log p(x; μ, σ²). -/
def scoreMu (x mu sigmaSq : ℝ) : ℝ := (x - mu) / sigmaSq

/-- Fisher information for μ: G = E[score²] = 1/σ². -/
def fisherMu (sigmaSq : ℝ) : ℝ := 1 / sigmaSq

/-! ## 2. Proven (pipeline anchors) -/
lemma scoreMu_def (x mu s : ℝ) : scoreMu x mu s = (x - mu) / s := rfl

/-- ∂²/∂μ² log p = −1/σ²  (the Gaussian log-Hessian is constant). -/
theorem d2logGauss_dmu2 (x mu sigmaSq : ℝ) :
    deriv (fun m => scoreMu x m sigmaSq) mu = -1 / sigmaSq := by
  dsimp [scoreMu]
  rw [deriv_div_const]
  rw [deriv_const_sub]
  simp [deriv_id'']

/-! ## 3. Score identity -/
/-- ∂/∂μ log p = (x − μ)/σ²  (the score identity; chain rule). -/
theorem dlogGauss_dmu (x mu sigmaSq : ℝ) (hs : sigmaSq > 0) :
    deriv (fun m => logGauss x m sigmaSq) mu = scoreMu x mu sigmaSq := by
  -- logGauss x m σ² = C − (x−m)²/(2σ²); d/dm[(x−m)²] = −2(x−m); → (x−m)/σ².
  have hs0 : sigmaSq ≠ 0 := ne_of_gt hs
  have hs2 : 2 * sigmaSq ≠ 0 := mul_ne_zero (by norm_num) hs0
  -- d/dm (x − m) = −1
  have h1 : HasDerivAt (fun m => x - m) (-1) mu :=
    HasDerivAt.const_sub x (hasDerivAt_id mu)
  -- d/dm (x − m)² = 2(x − μ)·(−1)   (power rule)
  have h2 : HasDerivAt (fun m => (x - m) ^ 2) (2 * (x - mu) * (-1)) mu := by
    simpa [pow_one] using h1.pow 2
  -- d/dm [(x − m)² / (2σ²)] = [2(x − μ)(−1)] / (2σ²)
  have h3 : HasDerivAt (fun m => (x - m) ^ 2 / (2 * sigmaSq))
      (2 * (x - mu) * (-1) / (2 * sigmaSq)) mu :=
    h2.div_const (2 * sigmaSq)
  -- logGauss = C − (x−m)²/(2σ²); the constant C has derivative 0.
  have h4 : HasDerivAt (fun m => logGauss x m sigmaSq)
      (0 - (2 * (x - mu) * (-1) / (2 * sigmaSq))) mu := by
    dsimp only [logGauss]
    exact (hasDerivAt_const mu (-1 / 2 * Real.log (2 * π * sigmaSq))).sub h3
  -- deriv equals the HasDerivAt value; scoreMu x mu σ² = (x−μ)/σ²
  rw [h4.deriv, scoreMu_def]
  -- 0 − [2(x−μ)(−1)/(2σ²)] = (x−μ)/σ²
  field_simp [hs2, hs0]
  ring

/-! ## 4. Fisher information of the Gaussian -/
/-- The project's `gaussDensity x mu s` equals Mathlib's `gaussianPDFReal mu s x`
    (the N(μ, s) density) when `s > 0`. -/
lemma gaussDensity_eq_gaussianPDFReal (x mu s : ℝ) (hs : 0 < s) :
    gaussDensity x mu s = ProbabilityTheory.gaussianPDFReal mu ⟨s, le_of_lt hs⟩ x := by
  dsimp [gaussDensity]
  simp only [ProbabilityTheory.gaussianPDFReal_def, NNReal.coe_mk]
  -- the prefactor: (2πs)^(-1/2) = (√(2πs))⁻¹
  have hpre : (2 * π * s) ^ (-1 / 2 : ℝ) = (Real.sqrt (2 * π * s))⁻¹ := by
    have hpos : 0 ≤ 2 * π * s := by positivity
    calc
      (2 * π * s) ^ (-1 / 2 : ℝ) = (2 * π * s) ^ (-(1 / 2 : ℝ)) := by
        congr 1; norm_num
      _ = ((2 * π * s) ^ (1 / 2 : ℝ))⁻¹ := by rw [rpow_neg hpos]
      _ = (Real.sqrt (2 * π * s))⁻¹ := by rw [Real.sqrt_eq_rpow]
  rw [hpre]

/-- E_{p}[scoreMu²] = 1/σ² — the Fisher information of the Gaussian N(μ, σ²).
    Proved by identifying the Lebesgue-density integral with the integral w.r.t.
    the Gaussian measure `gaussianReal μ σ²` and using that the variance of that
    measure is `σ²`. -/
theorem fisherMu_gaussian (mu sigmaSq : ℝ) (hs : 0 < sigmaSq) :
    ∫ x : ℝ, (scoreMu x mu sigmaSq) ^ 2 * gaussDensity x mu sigmaSq = 1 / sigmaSq := by
  have hs0 : sigmaSq ≠ 0 := ne_of_gt hs
  let v : NNReal := ⟨sigmaSq, le_of_lt hs⟩
  -- The second central moment of N(μ, σ²) is σ².
  have hvar : ∫ x : ℝ, (x - mu) ^ 2 ∂ProbabilityTheory.gaussianReal mu v = sigmaSq := by
    -- E[id] = μ (the mean of the Gaussian).
    have hmean : ∫ x : ℝ, x ∂ProbabilityTheory.gaussianReal mu v = mu := by
      simp
    -- ∫(x−μ)² = Var[id; μ] = v = σ².
    calc
      (∫ x : ℝ, (x - mu) ^ 2 ∂ProbabilityTheory.gaussianReal mu v) =
          (∫ x : ℝ, (x - (∫ y : ℝ, y ∂ProbabilityTheory.gaussianReal mu v)) ^ 2 ∂ProbabilityTheory.gaussianReal mu v) := by
        congr; funext x; rw [hmean]
      _ = ProbabilityTheory.variance id (ProbabilityTheory.gaussianReal mu v) := by
        rw [← ProbabilityTheory.variance_eq_integral measurable_id'.aemeasurable]
        rfl
      _ = sigmaSq := by
        rw [ProbabilityTheory.variance_id_gaussianReal]
        rfl
  calc
    (∫ x : ℝ, (scoreMu x mu sigmaSq) ^ 2 * gaussDensity x mu sigmaSq) =
        (∫ x : ℝ, ((x - mu) ^ 2 / sigmaSq ^ 2) * gaussDensity x mu sigmaSq) := by
      simp [scoreMu_def, div_pow]
    _ = (∫ x : ℝ, ((x - mu) ^ 2 / sigmaSq ^ 2) * ProbabilityTheory.gaussianPDFReal mu v x) := by
      congr; funext x; rw [gaussDensity_eq_gaussianPDFReal x mu sigmaSq hs]
    _ = (∫ x : ℝ, ((x - mu) ^ 2 / sigmaSq ^ 2) ∂ProbabilityTheory.gaussianReal mu v) := by
      have hswap : (∫ x : ℝ, ((x - mu) ^ 2 / sigmaSq ^ 2) * ProbabilityTheory.gaussianPDFReal mu v x) =
          (∫ x : ℝ, ProbabilityTheory.gaussianPDFReal mu v x * ((x - mu) ^ 2 / sigmaSq ^ 2)) := by
        congr; funext x; ring
      have hv0 : v ≠ 0 := by
        rw [← NNReal.coe_ne_zero]
        exact hs0
      rw [hswap, ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv0]
      simp [smul_eq_mul]
    _ = (∫ x : ℝ, (x - mu) ^ 2 ∂ProbabilityTheory.gaussianReal mu v) / sigmaSq ^ 2 := by
      rw [integral_div]
    _ = sigmaSq / sigmaSq ^ 2 := by rw [hvar]
    _ = 1 / sigmaSq := by field_simp [hs0]

/-! ## 5. Two-component mixture: rank loss at the weight boundary

The mixture p_w = w·N(m,1) + (1−w)·N(0,1) in the chart (m, w) has Fisher
determinant tending to 0 as w → 0⁺: the degeneration boundary of the
book's taxonomy, where the Fisher metric loses rank.

Proof route (Cauchy–Schwarz-free): bound the three Fisher entries by
G₁₁ ≤ w·A, G₂₂ ≤ B, |G₁₂| ≤ w·C with A, B, C integrals of explicit
Gaussian-type functions (only their integrability is used, never their
values), then |det G| ≤ G₁₁G₂₂ + G₁₂² ≤ w·(AB + C²) and squeeze. The
entry bounds use p_w ≥ w·φ_m and p_w ≥ (1−w)·φ₀ pointwise. -/

open Filter Topology Set

/-- Mixture density: weight w on N(m,1), weight 1−w on N(0,1). -/
def mixDensity (m w x : ℝ) : ℝ :=
  w * gaussDensity x m 1 + (1 - w) * gaussDensity x 0 1

lemma gaussDensity_pos (x m : ℝ) : 0 < gaussDensity x m 1 := by
  unfold gaussDensity
  have h2π : (0:ℝ) < 2 * π * 1 := by positivity
  exact mul_pos (Real.rpow_pos_of_pos h2π _) (Real.exp_pos _)

lemma mixDensity_pos {w : ℝ} (h0 : 0 < w) (h1 : w < 1) (m x : ℝ) :
    0 < mixDensity m w x :=
  add_pos (mul_pos h0 (gaussDensity_pos x m))
    (mul_pos (by linarith) (gaussDensity_pos x 0))

lemma le_mixDensity_left {w : ℝ} (h1 : w ≤ 1) (m x : ℝ) :
    w * gaussDensity x m 1 ≤ mixDensity m w x :=
  le_add_of_nonneg_right
    (mul_nonneg (by linarith) (gaussDensity_pos x 0).le)

lemma le_mixDensity_right {w : ℝ} (h0 : 0 ≤ w) (m x : ℝ) :
    (1 - w) * gaussDensity x 0 1 ≤ mixDensity m w x :=
  le_add_of_nonneg_left (mul_nonneg h0 (gaussDensity_pos x m).le)

/-! ### Integrability toolkit -/

/-- gaussDensity in the exp-quadratic normal form. -/
lemma gaussDensity_one_eq (m x : ℝ) :
    gaussDensity x m 1
      = (2 * π) ^ (-1/2 : ℝ) * Real.exp (-(1/2) * (x - m) ^ 2) := by
  unfold gaussDensity
  simp only [mul_one]
  congr 1
  ring_nf

lemma continuous_gaussDensity (m : ℝ) :
    Continuous fun x => gaussDensity x m 1 := by
  have h : (fun x => gaussDensity x m 1)
      = fun x => (2 * π) ^ (-1/2 : ℝ) * Real.exp (-(1/2) * (x - m) ^ 2) :=
    funext fun x => gaussDensity_one_eq m x
  rw [h]
  fun_prop

lemma integrable_gaussDensity (m : ℝ) :
    Integrable (fun x => gaussDensity x m 1) := by
  have h : (fun x => gaussDensity x m 1)
      = ProbabilityTheory.gaussianPDFReal m ⟨1, one_pos.le⟩ :=
    funext fun x => gaussDensity_eq_gaussianPDFReal x m 1 one_pos
  rw [h]
  exact ProbabilityTheory.integrable_gaussianPDFReal m _

lemma integrable_sq_mul_gaussDensity (m : ℝ) :
    Integrable (fun x => (x - m) ^ 2 * gaussDensity x m 1) := by
  have base : Integrable fun x : ℝ => x ^ 2 * Real.exp (-(1/2) * x ^ 2) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq
      (b := 1/2) (by norm_num) (s := 2) (by norm_num)
    have h2 : ∀ x : ℝ, x ^ (2:ℝ) = x ^ (2:ℕ) := fun x => by
      rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    simpa [h2] using h
  have htr : Integrable fun x : ℝ => (x - m) ^ 2 * Real.exp (-(1/2) * (x - m) ^ 2) :=
    base.comp_sub_right m
  have h : (fun x => (x - m) ^ 2 * gaussDensity x m 1)
      = fun x => (2 * π) ^ (-1/2 : ℝ)
          * ((x - m) ^ 2 * Real.exp (-(1/2) * (x - m) ^ 2)) :=
    funext fun x => by rw [gaussDensity_one_eq]; ring
  rw [h]
  exact htr.const_mul _

/-- |x − c| times a Gaussian is integrable, for any center pair, via
    |y| ≤ 1 + y² and (x−c)² ≤ 2(x−m)² + 2(m−c)². -/
lemma integrable_abs_mul_gaussDensity (c m : ℝ) :
    Integrable (fun x => |x - c| * gaussDensity x m 1) := by
  have hg : Integrable fun x =>
      (1 + 2 * (m - c) ^ 2) * gaussDensity x m 1
        + 2 * ((x - m) ^ 2 * gaussDensity x m 1) :=
    ((integrable_gaussDensity m).const_mul _).add
      ((integrable_sq_mul_gaussDensity m).const_mul 2)
  refine hg.mono' ?_ ?_
  · exact (((continuous_abs.comp (continuous_id.sub continuous_const))).mul
      (continuous_gaussDensity m)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    have hφ := (gaussDensity_pos x m).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hφ)]
    have h1 : |x - c| ≤ 1 + 2 * (m - c) ^ 2 + 2 * (x - m) ^ 2 := by
      rcases abs_cases (x - c) with ⟨h, _⟩ | ⟨h, _⟩ <;>
        nlinarith [sq_nonneg (x - c - 1), sq_nonneg (x - c + 1),
          sq_nonneg ((x - m) - (m - c)), sq_nonneg ((x - m) + (m - c))]
    nlinarith [mul_le_mul_of_nonneg_right h1 hφ]

/-- φ_m² / φ₀ is a Gaussian at 2m scaled by e^{m²}. -/
lemma gaussDensity_sq_div (m x : ℝ) :
    gaussDensity x m 1 ^ 2 / gaussDensity x 0 1
      = Real.exp (m ^ 2) * gaussDensity x (2 * m) 1 := by
  simp only [gaussDensity_one_eq]
  have hc : ((2 * π) ^ (-1/2 : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  rw [div_eq_iff (mul_ne_zero hc (Real.exp_ne_zero _)), mul_pow]
  have hexp : Real.exp (-(1/2) * (x - m) ^ 2) ^ 2
      = Real.exp (m ^ 2) * Real.exp (-(1/2) * (x - 2 * m) ^ 2)
        * Real.exp (-(1/2) * (x - 0) ^ 2) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-! ### Fisher entries and the determinant -/

/-- Fisher entry G₁₁ = E[s_m²] in the (m, w) chart, as a density integral. -/
def mixG11 (m w : ℝ) : ℝ :=
  ∫ x, (w * ((x - m) * gaussDensity x m 1)) ^ 2 / mixDensity m w x

/-- Fisher entry G₂₂ = E[s_w²]. -/
def mixG22 (m w : ℝ) : ℝ :=
  ∫ x, (gaussDensity x m 1 - gaussDensity x 0 1) ^ 2 / mixDensity m w x

/-- Fisher entry G₁₂ = E[s_m s_w]. -/
def mixG12 (m w : ℝ) : ℝ :=
  ∫ x, (w * ((x - m) * gaussDensity x m 1))
      * (gaussDensity x m 1 - gaussDensity x 0 1) / mixDensity m w x

/-- Fisher determinant of the 2×2 mixture block. -/
def mixDet (m w : ℝ) : ℝ := mixG11 m w * mixG22 m w - mixG12 m w ^ 2

lemma mixG11_nonneg (m w : ℝ) (h0 : 0 < w) (h1 : w < 1) : 0 ≤ mixG11 m w :=
  integral_nonneg fun x =>
    div_nonneg (sq_nonneg _) (mixDensity_pos h0 h1 m x).le

lemma mixG22_nonneg (m w : ℝ) (h0 : 0 < w) (h1 : w < 1) : 0 ≤ mixG22 m w :=
  integral_nonneg fun x =>
    div_nonneg (sq_nonneg _) (mixDensity_pos h0 h1 m x).le

/-- G₁₁ ≤ w·A with A the Gaussian second moment (value not needed). -/
lemma mixG11_le {w : ℝ} (h0 : 0 < w) (h1 : w < 1) (m : ℝ) :
    mixG11 m w ≤ w * ∫ x, (x - m) ^ 2 * gaussDensity x m 1 := by
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun x =>
      div_nonneg (sq_nonneg _) (mixDensity_pos h0 h1 m x).le
  · exact (integrable_sq_mul_gaussDensity m).const_mul w
  · refine Filter.Eventually.of_forall fun x => ?_
    have hp := mixDensity_pos h0 h1 m x
    have hφ := gaussDensity_pos x m
    have hlow := le_mixDensity_left h1.le m x
    rw [div_le_iff₀ hp]
    nlinarith [mul_nonneg (mul_nonneg
      (mul_nonneg h0.le (sq_nonneg (x - m))) hφ.le)
      (sub_nonneg.mpr hlow)]

/-- G₂₂ ≤ B with B the integral of 4(φ_m²/φ₀ + φ₀) (value not needed). -/
lemma mixG22_le {w : ℝ} (h0 : 0 < w) (h2 : w ≤ 1/2) (m : ℝ) :
    mixG22 m w
      ≤ ∫ x, 4 * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1
          + gaussDensity x 0 1) := by
  have hw1 : w < 1 := lt_of_le_of_lt h2 (by norm_num)
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun x =>
      div_nonneg (sq_nonneg _) (mixDensity_pos h0 hw1 m x).le
  · have h : (fun x => 4 * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1
        + gaussDensity x 0 1))
        = fun x => 4 * (Real.exp (m ^ 2) * gaussDensity x (2 * m) 1
            + gaussDensity x 0 1) :=
      funext fun x => by rw [gaussDensity_sq_div]
    rw [h]
    exact (((integrable_gaussDensity (2 * m)).const_mul _).add
      (integrable_gaussDensity 0)).const_mul 4
  · refine Filter.Eventually.of_forall fun x => ?_
    have hp := mixDensity_pos h0 hw1 m x
    have hφ0 := gaussDensity_pos x 0
    have hφ1 := gaussDensity_pos x m
    have hhalf : (1/2 : ℝ) * gaussDensity x 0 1 ≤ mixDensity m w x := by
      have := le_mixDensity_right h0.le m x
      nlinarith
    rw [div_le_iff₀ hp]
    have key : (gaussDensity x m 1 - gaussDensity x 0 1) ^ 2
        ≤ (4 * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1
            + gaussDensity x 0 1)) * ((1/2) * gaussDensity x 0 1) := by
      have hdiv : gaussDensity x m 1 ^ 2 / gaussDensity x 0 1
          * gaussDensity x 0 1 = gaussDensity x m 1 ^ 2 :=
        div_mul_cancel₀ _ (ne_of_gt hφ0)
      nlinarith [sq_nonneg (gaussDensity x m 1 + gaussDensity x 0 1)]
    refine key.trans (mul_le_mul_of_nonneg_left hhalf ?_)
    have : 0 ≤ gaussDensity x m 1 ^ 2 / gaussDensity x 0 1 :=
      div_nonneg (sq_nonneg _) hφ0.le
    nlinarith

/-- |G₁₂| ≤ w·C with C an explicit Gaussian-type integral (value not
    needed). The w factor comes from the score numerator; the density
    lower bound p_w ≥ (1−w)φ₀ ≥ φ₀/2 supplies the rest. -/
lemma abs_mixG12_le {w : ℝ} (h0 : 0 < w) (h2 : w ≤ 1/2) (m : ℝ) :
    |mixG12 m w|
      ≤ w * ∫ x, 2 * (|x - m| * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1)
          + |x - m| * gaussDensity x m 1) := by
  have hw1 : w < 1 := lt_of_le_of_lt h2 (by norm_num)
  have hint : Integrable fun x =>
      w * (2 * (|x - m| * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1)
        + |x - m| * gaussDensity x m 1)) := by
    have h : (fun x => w * (2 * (|x - m|
          * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1)
        + |x - m| * gaussDensity x m 1)))
        = fun x => w * (2 * (Real.exp (m ^ 2)
            * (|x - m| * gaussDensity x (2 * m) 1)
          + |x - m| * gaussDensity x m 1)) :=
      funext fun x => by rw [gaussDensity_sq_div]; ring
    rw [h]
    exact ((((integrable_abs_mul_gaussDensity m (2 * m)).const_mul _).add
      (integrable_abs_mul_gaussDensity m m)).const_mul 2).const_mul w
  have hstep : ∀ x : ℝ, ‖(w * ((x - m) * gaussDensity x m 1))
      * (gaussDensity x m 1 - gaussDensity x 0 1) / mixDensity m w x‖
      ≤ w * (2 * (|x - m| * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1)
        + |x - m| * gaussDensity x m 1)) := by
    intro x
    have hp := mixDensity_pos h0 hw1 m x
    have hφ0 := gaussDensity_pos x 0
    have hφ1 := gaussDensity_pos x m
    have hφ0' : gaussDensity x 0 1 ≠ 0 := ne_of_gt hφ0
    have hhalf : (1/2 : ℝ) * gaussDensity x 0 1 ≤ mixDensity m w x := by
      have h := le_mixDensity_right h0.le m x
      nlinarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hp, div_le_iff₀ hp]
    have habs : |gaussDensity x m 1 - gaussDensity x 0 1|
        ≤ gaussDensity x m 1 + gaussDensity x 0 1 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have hnum : |w * ((x - m) * gaussDensity x m 1)
        * (gaussDensity x m 1 - gaussDensity x 0 1)|
        ≤ w * (|x - m| * gaussDensity x m 1)
          * (gaussDensity x m 1 + gaussDensity x 0 1) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos h0, abs_of_pos hφ1]
      nlinarith [mul_nonneg (mul_nonneg h0.le
        (mul_nonneg (abs_nonneg (x - m)) hφ1.le)) (sub_nonneg.mpr habs)]
    refine hnum.trans ?_
    have hRnn : 0 ≤ w * (2 * (|x - m|
          * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1)
        + |x - m| * gaussDensity x m 1)) := by
      have h1 := div_nonneg (sq_nonneg (gaussDensity x m 1)) hφ0.le
      have h2 := abs_nonneg (x - m)
      positivity
    calc w * (|x - m| * gaussDensity x m 1)
          * (gaussDensity x m 1 + gaussDensity x 0 1)
        = (w * (2 * (|x - m| * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1)
            + |x - m| * gaussDensity x m 1))) * ((1/2) * gaussDensity x 0 1) := by
          field_simp
      _ ≤ (w * (2 * (|x - m| * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1)
            + |x - m| * gaussDensity x m 1))) * mixDensity m w x :=
          mul_le_mul_of_nonneg_left hhalf hRnn
  calc |mixG12 m w|
      ≤ ∫ x, ‖(w * ((x - m) * gaussDensity x m 1))
          * (gaussDensity x m 1 - gaussDensity x 0 1) / mixDensity m w x‖ := by
        unfold mixG12
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ x, w * (2 * (|x - m| * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1)
        + |x - m| * gaussDensity x m 1)) :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => norm_nonneg _) hint
          (Filter.Eventually.of_forall hstep)
    _ = w * ∫ x, 2 * (|x - m| * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1)
        + |x - m| * gaussDensity x m 1) := integral_const_mul w _

/-! ### The rank-loss theorem -/

/-- Rank loss at the weight boundary: the Fisher determinant of the
    2-component Gaussian mixture tends to 0 as the mixture weight
    w → 0⁺. This is the degeneration boundary of the taxonomy: the
    Fisher metric loses rank in the (m, w) chart. No hypothesis on m
    is needed (at m = 0 the family is degenerate for every w and the
    limit is trivial). -/
theorem mixture_rank_loss (m : ℝ) :
    Tendsto (fun w => mixDet m w) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  set A := ∫ x, (x - m) ^ 2 * gaussDensity x m 1 with hA
  set B := ∫ x, 4 * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1
      + gaussDensity x 0 1) with hB
  set C := ∫ x, 2 * (|x - m| * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1)
      + |x - m| * gaussDensity x m 1) with hC
  have hA0 : 0 ≤ A := integral_nonneg fun x =>
    mul_nonneg (sq_nonneg _) (gaussDensity_pos x m).le
  have hB0 : 0 ≤ B := integral_nonneg fun x => by
    have := div_nonneg (sq_nonneg (gaussDensity x m 1)) (gaussDensity_pos x 0).le
    have := (gaussDensity_pos x 0).le
    positivity
  have hC0 : 0 ≤ C := integral_nonneg fun x => by
    have := div_nonneg (sq_nonneg (gaussDensity x m 1)) (gaussDensity_pos x 0).le
    have := (gaussDensity_pos x m).le
    have := abs_nonneg (x - m)
    positivity
  -- the per-w determinant bound
  have hdet : ∀ w : ℝ, 0 < w → w ≤ 1/2 → |mixDet m w| ≤ w * (A * B + C ^ 2) := by
    intro w h0 h2
    have hw1 : w < 1 := lt_of_le_of_lt h2 (by norm_num)
    have h11 := mixG11_le h0 hw1 m
    have h22 := mixG22_le h0 h2 m
    have h12 := abs_mixG12_le h0 h2 m
    have h11n := mixG11_nonneg m w h0 hw1
    have h22n := mixG22_nonneg m w h0 hw1
    have hwA : 0 ≤ w * A := mul_nonneg h0.le hA0
    calc |mixDet m w|
        ≤ mixG11 m w * mixG22 m w + mixG12 m w ^ 2 := by
          rw [mixDet]
          refine (abs_sub _ _).trans ?_
          rw [abs_of_nonneg (mul_nonneg h11n h22n), abs_of_nonneg (sq_nonneg _)]
      _ ≤ (w * A) * B + (w * C) ^ 2 := by
          have h := abs_le.mp h12
          exact add_le_add (mul_le_mul h11 h22 h22n hwA) (sq_le_sq' h.1 h.2)
      _ = w * (A * B) + w ^ 2 * C ^ 2 := by ring
      _ ≤ w * (A * B) + w * C ^ 2 := by
          have hw2 : w ^ 2 ≤ w := by nlinarith
          nlinarith [mul_nonneg (sub_nonneg.mpr hw2) (sq_nonneg C)]
      _ = w * (A * B + C ^ 2) := by ring
  -- eventual window and squeeze
  have hev : ∀ᶠ w in 𝓝[>] (0:ℝ), 0 < w ∧ w ≤ 1/2 := by
    have h1 : ∀ᶠ w in 𝓝[>] (0:ℝ), w ∈ Set.Ioi (0:ℝ) :=
      eventually_mem_nhdsWithin
    have h2 : ∀ᶠ w in 𝓝 (0:ℝ), w < 1/2 :=
      gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num)
    filter_upwards [h1, eventually_nhdsWithin_of_eventually_nhds h2]
      with w hw1 hw2
    exact ⟨hw1, hw2.le⟩
  have hg : Tendsto (fun w : ℝ => w * (A * B + C ^ 2)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h : Tendsto (fun w : ℝ => w * (A * B + C ^ 2)) (𝓝 (0:ℝ))
        (𝓝 (0 * (A * B + C ^ 2))) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hgneg : Tendsto (fun w : ℝ => -(w * (A * B + C ^ 2)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using hg.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hgneg hg ?_ ?_
  · filter_upwards [hev] with w hw
    exact (abs_le.mp (hdet w hw.1 hw.2)).1
  · filter_upwards [hev] with w hw
    exact (abs_le.mp (hdet w hw.1 hw.2)).2

/-! ### Strict positivity of the determinant off the boundary

For w ∈ (0,1) and m ≠ 0 the determinant is strictly positive, so the
w → 0⁺ limit is a genuine rank loss. The argument is elementary: with
t := −G₁₂/G₁₁, the quadratic-form value ∫ (t·s_m + s_w)² p equals
G₂₂ − G₁₂²/G₁₁, and it is positive because the integrand is continuous,
nonnegative, and nonzero at x = m, where the location score vanishes
while the weight score equals c·(1 − e^{−m²/2}) ≠ 0. The witness is
uniform in t, so no linear-independence case analysis is needed. -/

/-- A continuous nonnegative integrable function with one nonzero value
    has positive integral. -/
lemma integral_pos_of_continuous {h : ℝ → ℝ} (hc : Continuous h)
    (hnn : ∀ x, 0 ≤ h x) (hint : Integrable h) {x₀ : ℝ} (hx₀ : h x₀ ≠ 0) :
    0 < ∫ x, h x := by
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  have hopen : IsOpen (Function.support h) := by
    have hs : Function.support h = h ⁻¹' {0}ᶜ := by
      ext x; simp [Function.mem_support]
    rw [hs]
    exact isOpen_compl_singleton.preimage hc
  exact hopen.measure_pos volume ⟨x₀, hx₀⟩

lemma continuous_mixDensity (m w : ℝ) :
    Continuous fun x => mixDensity m w x := by
  unfold mixDensity
  exact (continuous_const.mul (continuous_gaussDensity m)).add
    (continuous_const.mul (continuous_gaussDensity 0))

lemma continuous_scoreNum_m (m w : ℝ) :
    Continuous fun x => w * ((x - m) * gaussDensity x m 1) :=
  continuous_const.mul
    ((continuous_id.sub continuous_const).mul (continuous_gaussDensity m))

lemma continuous_scoreNum_w (m : ℝ) :
    Continuous fun x => gaussDensity x m 1 - gaussDensity x 0 1 :=
  (continuous_gaussDensity m).sub (continuous_gaussDensity 0)

lemma integrable_G11_integrand {w : ℝ} (h0 : 0 < w) (h1 : w < 1) (m : ℝ) :
    Integrable fun x =>
      (w * ((x - m) * gaussDensity x m 1)) ^ 2 / mixDensity m w x := by
  refine ((integrable_sq_mul_gaussDensity m).const_mul w).mono' ?_ ?_
  · exact (((continuous_scoreNum_m m w).pow 2).div (continuous_mixDensity m w)
      (fun x => ne_of_gt (mixDensity_pos h0 h1 m x))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    have hp := mixDensity_pos h0 h1 m x
    have hφ := gaussDensity_pos x m
    have hlow := le_mixDensity_left h1.le m x
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hp.le),
      div_le_iff₀ hp]
    nlinarith [mul_nonneg (mul_nonneg
      (mul_nonneg h0.le (sq_nonneg (x - m))) hφ.le)
      (sub_nonneg.mpr hlow)]

lemma integrable_G22_integrand {w : ℝ} (h0 : 0 < w) (h1 : w < 1) (m : ℝ) :
    Integrable fun x =>
      (gaussDensity x m 1 - gaussDensity x 0 1) ^ 2 / mixDensity m w x := by
  have hw' : (1 : ℝ) - w ≠ 0 := by linarith
  have hint : Integrable fun x => (1/(1-w))
      * (2 * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1)
        + 2 * gaussDensity x 0 1) := by
    have hfun : (fun x => (1/(1-w))
        * (2 * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1)
          + 2 * gaussDensity x 0 1))
        = fun x => (1/(1-w))
        * (2 * (Real.exp (m ^ 2) * gaussDensity x (2 * m) 1)
          + 2 * gaussDensity x 0 1) :=
      funext fun x => by rw [gaussDensity_sq_div]
    rw [hfun]
    exact ((((integrable_gaussDensity (2 * m)).const_mul _).const_mul 2).add
      ((integrable_gaussDensity 0).const_mul 2)).const_mul _
  refine hint.mono' ?_ ?_
  · exact (((continuous_scoreNum_w m).pow 2).div (continuous_mixDensity m w)
      (fun x => ne_of_gt (mixDensity_pos h0 h1 m x))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    have hp := mixDensity_pos h0 h1 m x
    have hφ0 := gaussDensity_pos x 0
    have hφ0' : gaussDensity x 0 1 ≠ 0 := ne_of_gt hφ0
    have hφ1 := gaussDensity_pos x m
    have hDnn : 0 ≤ (1/(1-w))
        * (2 * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1)
          + 2 * gaussDensity x 0 1) := by
      have hd := div_nonneg (sq_nonneg (gaussDensity x m 1)) hφ0.le
      have hw'' : (0:ℝ) < 1 - w := by linarith
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hp.le),
      div_le_iff₀ hp]
    have hval : (1/(1-w)) * (2 * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1)
          + 2 * gaussDensity x 0 1) * ((1 - w) * gaussDensity x 0 1)
        = 2 * gaussDensity x m 1 ^ 2 + 2 * gaussDensity x 0 1 ^ 2 := by
      field_simp
    calc (gaussDensity x m 1 - gaussDensity x 0 1) ^ 2
        ≤ 2 * gaussDensity x m 1 ^ 2 + 2 * gaussDensity x 0 1 ^ 2 := by
          nlinarith [sq_nonneg (gaussDensity x m 1 + gaussDensity x 0 1)]
      _ = (1/(1-w)) * (2 * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1)
            + 2 * gaussDensity x 0 1) * ((1 - w) * gaussDensity x 0 1) :=
          hval.symm
      _ ≤ (1/(1-w)) * (2 * (gaussDensity x m 1 ^ 2 / gaussDensity x 0 1)
            + 2 * gaussDensity x 0 1) * mixDensity m w x :=
          mul_le_mul_of_nonneg_left (le_mixDensity_right h0.le m x) hDnn

lemma integrable_G12_integrand {w : ℝ} (h0 : 0 < w) (h1 : w < 1) (m : ℝ) :
    Integrable fun x =>
      (w * ((x - m) * gaussDensity x m 1))
        * (gaussDensity x m 1 - gaussDensity x 0 1) / mixDensity m w x := by
  refine (((integrable_G11_integrand h0 h1 m).const_mul (1/2)).add
    ((integrable_G22_integrand h0 h1 m).const_mul (1/2))).mono' ?_ ?_
  · exact (((continuous_scoreNum_m m w).mul (continuous_scoreNum_w m)).div
      (continuous_mixDensity m w)
      (fun x => ne_of_gt (mixDensity_pos h0 h1 m x))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    have hp := mixDensity_pos h0 h1 m x
    have hp' : mixDensity m w x ≠ 0 := ne_of_gt hp
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hp, div_le_iff₀ hp]
    have hval : ((1/2) * ((w * ((x - m) * gaussDensity x m 1)) ^ 2
          / mixDensity m w x)
        + (1/2) * ((gaussDensity x m 1 - gaussDensity x 0 1) ^ 2
          / mixDensity m w x)) * mixDensity m w x
        = ((w * ((x - m) * gaussDensity x m 1)) ^ 2
          + (gaussDensity x m 1 - gaussDensity x 0 1) ^ 2) / 2 := by
      field_simp
    simp only [Pi.add_apply]
    rw [hval]
    rcases abs_cases ((w * ((x - m) * gaussDensity x m 1))
        * (gaussDensity x m 1 - gaussDensity x 0 1)) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] <;>
      nlinarith [sq_nonneg (w * ((x - m) * gaussDensity x m 1)
          - (gaussDensity x m 1 - gaussDensity x 0 1)),
        sq_nonneg (w * ((x - m) * gaussDensity x m 1)
          + (gaussDensity x m 1 - gaussDensity x 0 1))]

/-- Off the boundary the determinant is strictly positive: for m ≠ 0 and
    w ∈ (0,1) the two scores are not proportional, and the (m, w) Fisher
    block is nondegenerate. Together with `mixture_rank_loss` this makes
    w → 0⁺ a genuine rank loss. -/
theorem mixture_det_pos {m w : ℝ} (hm : m ≠ 0) (h0 : 0 < w) (h1 : w < 1) :
    0 < mixDet m w := by
  have hIf := integrable_G11_integrand h0 h1 m
  have hIg := integrable_G22_integrand h0 h1 m
  have hIfg := integrable_G12_integrand h0 h1 m
  -- G₁₁ > 0, witnessed at x = m + 1 where the location score is nonzero.
  have hG11 : 0 < mixG11 m w := by
    refine integral_pos_of_continuous
      (((continuous_scoreNum_m m w).pow 2).div (continuous_mixDensity m w)
        (fun x => ne_of_gt (mixDensity_pos h0 h1 m x)))
      (fun x => div_nonneg (sq_nonneg _) (mixDensity_pos h0 h1 m x).le)
      hIf (x₀ := m + 1) ?_
    have hs : m + 1 - m = 1 := by ring
    have hφ := gaussDensity_pos (m + 1) m
    have hp := mixDensity_pos h0 h1 m (m + 1)
    rw [hs]
    positivity
  set G11 := mixG11 m w with hG11d
  set G12 := mixG12 m w with hG12d
  set G22 := mixG22 m w with hG22d
  set t := -G12 / G11 with ht
  -- the quadratic-form value at (t, 1)
  have hQ : (∫ x, (t * (w * ((x - m) * gaussDensity x m 1))
      + (gaussDensity x m 1 - gaussDensity x 0 1)) ^ 2 / mixDensity m w x)
      = t ^ 2 * G11 + 2 * t * G12 + G22 := by
    have hfun : ∀ x, (t * (w * ((x - m) * gaussDensity x m 1))
        + (gaussDensity x m 1 - gaussDensity x 0 1)) ^ 2 / mixDensity m w x
        = t ^ 2 * ((w * ((x - m) * gaussDensity x m 1)) ^ 2 / mixDensity m w x)
          + (2 * t) * ((w * ((x - m) * gaussDensity x m 1))
            * (gaussDensity x m 1 - gaussDensity x 0 1) / mixDensity m w x)
          + (gaussDensity x m 1 - gaussDensity x 0 1) ^ 2
            / mixDensity m w x := by
      intro x
      have hp' : mixDensity m w x ≠ 0 := ne_of_gt (mixDensity_pos h0 h1 m x)
      field_simp
      ring
    simp only [hfun]
    have ha : Integrable fun x =>
        t ^ 2 * ((w * ((x - m) * gaussDensity x m 1)) ^ 2 / mixDensity m w x) :=
      hIf.const_mul _
    have hb : Integrable fun x =>
        (2 * t) * ((w * ((x - m) * gaussDensity x m 1))
          * (gaussDensity x m 1 - gaussDensity x 0 1) / mixDensity m w x) :=
      hIfg.const_mul _
    have hab : Integrable fun x =>
        t ^ 2 * ((w * ((x - m) * gaussDensity x m 1)) ^ 2 / mixDensity m w x)
          + (2 * t) * ((w * ((x - m) * gaussDensity x m 1))
            * (gaussDensity x m 1 - gaussDensity x 0 1) / mixDensity m w x) :=
      ha.add hb
    rw [integral_add hab hIg, integral_add ha hb,
      integral_const_mul, integral_const_mul]
    rfl
  -- the quadratic-form value is positive, witnessed at x = m.
  have hQpos : 0 < ∫ x, (t * (w * ((x - m) * gaussDensity x m 1))
      + (gaussDensity x m 1 - gaussDensity x 0 1)) ^ 2 / mixDensity m w x := by
    have hcont : Continuous fun x => (t * (w * ((x - m) * gaussDensity x m 1))
        + (gaussDensity x m 1 - gaussDensity x 0 1)) ^ 2 / mixDensity m w x :=
      (((continuous_const.mul (continuous_scoreNum_m m w)).add
        (continuous_scoreNum_w m)).pow 2).div (continuous_mixDensity m w)
        (fun x => ne_of_gt (mixDensity_pos h0 h1 m x))
    have hIQ : Integrable fun x => (t * (w * ((x - m) * gaussDensity x m 1))
        + (gaussDensity x m 1 - gaussDensity x 0 1)) ^ 2 / mixDensity m w x := by
      have hfun : ∀ x, (t * (w * ((x - m) * gaussDensity x m 1))
          + (gaussDensity x m 1 - gaussDensity x 0 1)) ^ 2 / mixDensity m w x
          = t ^ 2 * ((w * ((x - m) * gaussDensity x m 1)) ^ 2 / mixDensity m w x)
            + (2 * t) * ((w * ((x - m) * gaussDensity x m 1))
              * (gaussDensity x m 1 - gaussDensity x 0 1) / mixDensity m w x)
            + (gaussDensity x m 1 - gaussDensity x 0 1) ^ 2
              / mixDensity m w x := by
        intro x
        have hp' : mixDensity m w x ≠ 0 := ne_of_gt (mixDensity_pos h0 h1 m x)
        field_simp
        ring
      simp only [hfun]
      exact ((hIf.const_mul _).add (hIfg.const_mul _)).add hIg
    refine integral_pos_of_continuous hcont
      (fun x => div_nonneg (sq_nonneg _) (mixDensity_pos h0 h1 m x).le)
      hIQ (x₀ := m) ?_
    have hzero : m - m = 0 := by ring
    have hgm : 0 < gaussDensity m m 1 - gaussDensity m 0 1 := by
      rw [gaussDensity_one_eq, gaussDensity_one_eq]
      have hm2 : 0 < m ^ 2 := by positivity
      have hexp : Real.exp (-(1/2) * (m - 0) ^ 2)
          < Real.exp (-(1/2) * (m - m) ^ 2) := by
        apply Real.exp_lt_exp.mpr
        nlinarith
      have hcpos : (0:ℝ) < (2 * π) ^ (-1/2 : ℝ) :=
        Real.rpow_pos_of_pos (by positivity) _
      nlinarith
    have hp := mixDensity_pos h0 h1 m m
    rw [hzero]
    have hnum : t * (w * (0 * gaussDensity m m 1))
        + (gaussDensity m m 1 - gaussDensity m 0 1)
        = gaussDensity m m 1 - gaussDensity m 0 1 := by ring
    rw [hnum]
    positivity
  rw [hQ] at hQpos
  -- t = −G₁₂/G₁₁ collapses the form to G₂₂ − G₁₂²/G₁₁.
  have hG11' : G11 ≠ 0 := ne_of_gt hG11
  have hcollapse : t ^ 2 * G11 + 2 * t * G12 + G22 = G22 - G12 ^ 2 / G11 := by
    rw [ht]
    field_simp
    ring
  rw [hcollapse] at hQpos
  have hdet : mixDet m w = G11 * (G22 - G12 ^ 2 / G11) := by
    rw [mixDet, ← hG11d, ← hG12d, ← hG22d]
    field_simp
  rw [hdet]
  exact mul_pos hG11 hQpos

/-! ## 6. The KL-order-k curve in the Gaussian location family

The curve μ(t) = t^k in {N(μ, 1)} realises a KL-order-k approach: the
basin-shape example of rem:fisher_decay_three_readings (quartic well at
k = 2, sextic at k = 3). Everything is exact for this family. The
moving-measure directional Fisher is k²·t^{2(k−1)} with no remainder,
the KL to the base point is t^{2k}/2, and the paper's 2k² Fisher–KL
coefficient ratio is the exact identity F(t)·t² = 2k²·K(t). The
leading-rate statement connects to the abstract layers in
fisher_decay.lean. -/

/-- Moving-measure directional Fisher along μ(t) = t^k:
    E_{p_t}[s_t²] with s_t(x) = k·t^{k−1}·(x − t^k). -/
def curveFisher (k : ℕ) (t : ℝ) : ℝ :=
  ∫ x, ((k:ℝ) * t^(k-1) * (x - t^k))^2
    ∂ProbabilityTheory.gaussianReal (t^k) ⟨1, one_pos.le⟩

/-- K(t) = KL(p₀ ‖ p_{t^k}) as a density integral. -/
def curveKL (k : ℕ) (t : ℝ) : ℝ :=
  ∫ x, (logGauss x 0 1 - logGauss x (t^k) 1) * gaussDensity x 0 1

lemma one_nnreal_ne_zero : (⟨1, one_pos.le⟩ : NNReal) ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : NNReal => (v : ℝ)) h
  exact one_ne_zero h1

/-- Second central moment of the unit-variance Gaussian measure. -/
lemma integral_central_sq_gaussianReal (m : ℝ) :
    ∫ x, (x - m) ^ 2 ∂ProbabilityTheory.gaussianReal m ⟨1, one_pos.le⟩
      = 1 := by
  have hmean : ∫ x, x ∂ProbabilityTheory.gaussianReal m ⟨1, one_pos.le⟩
      = m := by
    simp
  calc (∫ x, (x - m) ^ 2 ∂ProbabilityTheory.gaussianReal m ⟨1, one_pos.le⟩)
      = ∫ x, (x - (∫ y, y ∂ProbabilityTheory.gaussianReal m ⟨1, one_pos.le⟩)) ^ 2
          ∂ProbabilityTheory.gaussianReal m ⟨1, one_pos.le⟩ := by
        congr
        funext x
        rw [hmean]
    _ = ProbabilityTheory.variance id
          (ProbabilityTheory.gaussianReal m ⟨1, one_pos.le⟩) := by
        rw [← ProbabilityTheory.variance_eq_integral measurable_id'.aemeasurable]
        rfl
    _ = 1 := by
        rw [ProbabilityTheory.variance_id_gaussianReal]
        rfl

lemma integral_gaussDensity_eq_one (m : ℝ) :
    (∫ x, gaussDensity x m 1) = 1 := by
  have h : (fun x => gaussDensity x m 1)
      = ProbabilityTheory.gaussianPDFReal m ⟨1, one_pos.le⟩ :=
    funext fun x => gaussDensity_eq_gaussianPDFReal x m 1 one_pos
  rw [h]
  exact ProbabilityTheory.integral_gaussianPDFReal_eq_one m one_nnreal_ne_zero

lemma integrable_id_mul_gaussDensity :
    Integrable (fun x => x * gaussDensity x 0 1) := by
  refine (integrable_abs_mul_gaussDensity 0 0).mono' ?_ ?_
  · exact (continuous_id.mul (continuous_gaussDensity 0)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gaussDensity_pos x 0)]
    simp [sub_zero]

lemma integral_id_mul_gaussDensity_zero :
    (∫ x, x * gaussDensity x 0 1) = 0 := by
  have hv0 : (⟨1, one_pos.le⟩ : NNReal) ≠ 0 := one_nnreal_ne_zero
  have h1 : (∫ x, x ∂ProbabilityTheory.gaussianReal 0 ⟨1, one_pos.le⟩)
      = ∫ x, x * gaussDensity x 0 1 := by
    rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv0]
    congr
    funext x
    rw [smul_eq_mul, gaussDensity_eq_gaussianPDFReal x 0 1 one_pos]
    ring
  rw [← h1]
  simp

theorem curveFisher_eq (k : ℕ) (t : ℝ) :
    curveFisher k t = (k:ℝ)^2 * t^(2*(k-1)) := by
  unfold curveFisher
  have hfun : ∀ x : ℝ, ((k:ℝ) * t^(k-1) * (x - t^k))^2
      = ((k:ℝ)^2 * (t^(k-1))^2) * (x - t^k)^2 := fun x => by ring
  simp only [hfun]
  rw [integral_const_mul, integral_central_sq_gaussianReal, mul_one,
    mul_comm 2 (k-1), pow_mul]

theorem curveKL_eq (k : ℕ) (t : ℝ) :
    curveKL k t = t^(2*k) / 2 := by
  unfold curveKL
  have hfun : ∀ x : ℝ, (logGauss x 0 1 - logGauss x (t^k) 1)
        * gaussDensity x 0 1
      = ((t^k)^2/2) * gaussDensity x 0 1
        - t^k * (x * gaussDensity x 0 1) := by
    intro x
    unfold logGauss
    ring
  simp only [hfun]
  rw [integral_sub ((integrable_gaussDensity 0).const_mul _)
      (integrable_id_mul_gaussDensity.const_mul _),
    integral_const_mul, integral_const_mul, integral_gaussDensity_eq_one,
    integral_id_mul_gaussDensity_zero, mul_one, mul_zero, sub_zero,
    mul_comm 2 k, pow_mul]

/-- The paper's 2k² Fisher–KL coefficient ratio, exact for this family:
    F(t)·t² = 2k²·K(t). At k = 1 this is the regular case where the
    naive Hessian prediction agrees; at k ≥ 2 it is the singular-geometry
    correction of rem:leading_fisher_kl_ratio. -/
theorem curve_fisher_kl_ratio {k : ℕ} (hk : 1 ≤ k) (t : ℝ) :
    curveFisher k t * t^2 = 2 * (k:ℝ)^2 * curveKL k t := by
  rw [curveFisher_eq, curveKL_eq]
  have h : 2*(k-1) + 2 = 2*k := by omega
  rw [mul_assoc, ← pow_add, h]
  ring

/-- The curve realises the leading rate 2(k−1) with coefficient k²,
    connecting the concrete family to the abstract fisher_decay layers. -/
theorem curveFisher_hasLeadingRate (k : ℕ) :
    HasLeadingRate (curveFisher k) (2*(k-1)) ((k:ℝ)^2) := by
  have h : Filter.Tendsto (fun _ : ℝ => (k:ℝ)^2) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((k:ℝ)^2)) := tendsto_const_nhds
  refine h.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  rw [curveFisher_eq]
  have htp : t ^ (2*(k-1)) ≠ 0 := ne_of_gt (pow_pos ht _)
  field_simp

end

end DeadDirections
