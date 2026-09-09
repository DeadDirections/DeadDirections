/-
  Mixture score along the k = 2 curve (discharging thm:fisher_decay's
  hypotheses on the canonical mixture family, stage 1).

  The curve (w, m) = (t, t) in the 2-component mixture approaches the
  degeneration point along a KL-order-2 direction: the deviation
  p_t/φ₀ − 1 = t(e^{tx−t²/2} − 1) is O(t²), the first-order score
  vanishes, and a(x) = x carries the leading coefficient. This file
  builds the honest score: `mixCurve` is the curve density,
  `scoreCurve` its closed-form logarithmic t-derivative, certified by
  `hasDerivAt_log_mixCurve`, and `scoreCurve_decomp` writes it in the
  k = 2 shape 2·t·x + remainder that
  `fisher_expansion_of_score_expansion` consumes.

  Stage 2 (next): the L² remainder estimate
  ∫ scoreRemainder(t)² dμ ≤ M·t⁴ under μ = N(0,1), via the density
  lower bound mixCurve ≥ 1 − t and the algebraic split of the
  numerator h = −(3/2)t² + uv + E(1+v) with E = e^u − 1 − u.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import DeadDirections.GaussianFisher
import DeadDirections.KlOrder

namespace DeadDirections

open Real

noncomputable section

/-- The k = 2 curve in the mixture: weight t on N(t, 1). -/
def mixCurve (t x : ℝ) : ℝ := mixDensity t t x

/-- Closed-form score along the curve: ∂_t p_t / p_t. -/
def scoreCurve (t x : ℝ) : ℝ :=
  (gaussDensity x t 1 - gaussDensity x 0 1
    + t * ((x - t) * gaussDensity x t 1)) / mixCurve t x

/-- The Gaussian density moves under its mean with derivative
    (x − m)·φ_m(x). -/
lemma hasDerivAt_gaussDensity_mean (x m : ℝ) :
    HasDerivAt (fun t => gaussDensity x t 1)
      ((x - m) * gaussDensity x m 1) m := by
  have hfun : (fun t => gaussDensity x t 1)
      = fun t => (2 * π) ^ (-1/2 : ℝ) * Real.exp (-(1/2) * (x - t) ^ 2) :=
    funext fun t => gaussDensity_one_eq t x
  rw [hfun, gaussDensity_one_eq]
  have h1 : HasDerivAt (fun t : ℝ => x - t) (-1) m :=
    (hasDerivAt_id m).const_sub x
  have h2 : HasDerivAt (fun t : ℝ => (x - t) ^ 2)
      (2 * (x - m) * (-1)) m := by
    simpa [pow_one] using h1.pow 2
  have h3 : HasDerivAt (fun t : ℝ => -(1/2) * (x - t) ^ 2)
      (-(1/2) * (2 * (x - m) * (-1))) m := h2.const_mul _
  have h4 := h3.exp.const_mul ((2 * π) ^ (-1/2 : ℝ))
  convert h4 using 1
  ring

/-- t-derivative of the curve density. -/
lemma hasDerivAt_mixCurve (x t : ℝ) :
    HasDerivAt (fun s => mixCurve s x)
      (gaussDensity x t 1 - gaussDensity x 0 1
        + t * ((x - t) * gaussDensity x t 1)) t := by
  have hfun : (fun s => mixCurve s x)
      = fun s => s * gaussDensity x s 1 + (1 - s) * gaussDensity x 0 1 :=
    funext fun s => rfl
  rw [hfun]
  have h1 : HasDerivAt (fun s : ℝ => s * gaussDensity x s 1)
      (1 * gaussDensity x t 1 + t * ((x - t) * gaussDensity x t 1)) t :=
    (hasDerivAt_id t).mul (hasDerivAt_gaussDensity_mean x t)
  have h2 : HasDerivAt (fun s : ℝ => (1 - s) * gaussDensity x 0 1)
      (-1 * gaussDensity x 0 1) t := by
    have h := ((hasDerivAt_id t).const_sub 1).mul_const (gaussDensity x 0 1)
    simpa using h
  have h := h1.add h2
  convert h using 1
  ring

/-- The closed form is the logarithmic derivative: the honest score of
    the curve at parameters inside (0, 1). -/
lemma hasDerivAt_log_mixCurve {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (x : ℝ) :
    HasDerivAt (fun s => Real.log (mixCurve s x)) (scoreCurve t x) t := by
  have hpos : mixCurve t x ≠ 0 := ne_of_gt (mixDensity_pos h0 h1 t x)
  exact (hasDerivAt_mixCurve x t).log hpos

/-- Remainder of the score against its k = 2 leading term 2t·x. -/
def scoreRemainder (t x : ℝ) : ℝ := scoreCurve t x - 2 * t * x

/-- The score in the shape the abstract middle layer consumes at
    k = 2: s(t) = 2·t^{2−1}·a + r(t) with a(x) = x. -/
lemma scoreCurve_decomp (t x : ℝ) :
    scoreCurve t x = 2 * t ^ 1 * x + scoreRemainder t x := by
  unfold scoreRemainder
  ring

/-! ### Exponential-moment toolkit for the remainder estimate

The remainder dominators carry e^{c·x} factors against φ₀. The tilt
identity e^{cx}·φ₀ = e^{c²/2}·φ_c converts every such integral into a
Gaussian integral at a shifted mean, so the existing integrability
toolkit applies. -/

/-- Gaussian tilt: e^{cx}·φ₀(x) = e^{c²/2}·φ_c(x). -/
lemma gaussDensity_tilt (c x : ℝ) :
    Real.exp (c * x) * gaussDensity x 0 1
      = Real.exp (c ^ 2 / 2) * gaussDensity x c 1 := by
  simp only [gaussDensity_one_eq]
  have hexp : Real.exp (c * x) * Real.exp (-(1/2) * (x - 0) ^ 2)
      = Real.exp (c ^ 2 / 2) * Real.exp (-(1/2) * (x - c) ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  linear_combination ((2 * π) ^ (-1/2 : ℝ)) * hexp

/-- Exponentially tilted Gaussians are integrable. -/
lemma integrable_exp_mul_gaussDensity (c : ℝ) :
    MeasureTheory.Integrable (fun x => Real.exp (c * x) * gaussDensity x 0 1) := by
  have h : (fun x => Real.exp (c * x) * gaussDensity x 0 1)
      = fun x => Real.exp (c ^ 2 / 2) * gaussDensity x c 1 :=
    funext fun x => gaussDensity_tilt c x
  rw [h]
  exact (integrable_gaussDensity c).const_mul _

/-- Polynomially weighted tilted Gaussians are integrable: the tilt
    moves the weight to a shifted mean, where the second-moment
    toolkit applies. -/
lemma integrable_sq_mul_exp_mul_gaussDensity (c : ℝ) :
    MeasureTheory.Integrable
      (fun x => x ^ 2 * (Real.exp (c * x) * gaussDensity x 0 1)) := by
  have h : (fun x => x ^ 2 * (Real.exp (c * x) * gaussDensity x 0 1))
      = fun x => Real.exp (c ^ 2 / 2) * (x ^ 2 * gaussDensity x c 1) :=
    funext fun x => by rw [gaussDensity_tilt]; ring
  rw [h]
  refine ((?_ : MeasureTheory.Integrable
    (fun x => x ^ 2 * gaussDensity x c 1)).const_mul _)
  have hg : MeasureTheory.Integrable
      (fun x => (2 * c ^ 2) * gaussDensity x c 1
        + 2 * ((x - c) ^ 2 * gaussDensity x c 1)) :=
    ((integrable_gaussDensity c).const_mul _).add
      ((integrable_sq_mul_gaussDensity c).const_mul 2)
  refine hg.mono' ?_ ?_
  · exact ((continuous_pow 2).mul (continuous_gaussDensity c)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    have hφ := (gaussDensity_pos x c).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hφ)]
    nlinarith [mul_nonneg (sq_nonneg (x - c + c)) hφ,
      mul_nonneg (sq_nonneg (x - c - c)) hφ,
      mul_nonneg (sq_nonneg (x - 2 * c)) hφ]

/-! ### The elementary exponential Taylor bound

E(u) := e^u − 1 − u satisfies 0 ≤ E ≤ u²·e^{|u|} for every real u,
with no series manipulation: the window |u| ≤ 1 is Mathlib's Taylor
bound, u > 1 uses E ≤ e^u ≤ u²e^u, and u < −1 uses e^u ≤ 1. -/

lemma exp_sub_one_sub_nonneg (u : ℝ) : 0 ≤ Real.exp u - 1 - u := by
  have h := Real.add_one_le_exp u
  linarith

lemma exp_sub_one_sub_le (u : ℝ) :
    Real.exp u - 1 - u ≤ u ^ 2 * Real.exp |u| := by
  have hexp1 : (1:ℝ) ≤ Real.exp |u| := Real.one_le_exp (abs_nonneg u)
  rcases le_or_gt |u| 1 with h | h
  · have hb := Real.abs_exp_sub_one_sub_id_le h
    calc Real.exp u - 1 - u ≤ |Real.exp u - 1 - u| := le_abs_self _
      _ ≤ u ^ 2 := hb
      _ ≤ u ^ 2 * Real.exp |u| :=
          le_mul_of_one_le_right (sq_nonneg u) hexp1
  · rcases le_or_gt u 0 with hu | hu
    · have he : Real.exp u ≤ 1 := Real.exp_le_one_iff.mpr hu
      have habs : |u| = -u := abs_of_nonpos hu
      have h1 : (1:ℝ) < -u := by rwa [habs] at h
      have h2 : -u ≤ u ^ 2 := by nlinarith
      calc Real.exp u - 1 - u ≤ -u := by linarith
        _ ≤ u ^ 2 := h2
        _ ≤ u ^ 2 * Real.exp |u| :=
            le_mul_of_one_le_right (sq_nonneg u) hexp1
    · have habs : |u| = u := abs_of_pos hu
      have h1 : (1:ℝ) < u := by rwa [habs] at h
      have h2 : (1:ℝ) ≤ u ^ 2 := by nlinarith
      have h3 : Real.exp u ≤ u ^ 2 * Real.exp u :=
        le_mul_of_one_le_left (Real.exp_pos u).le h2
      rw [habs]
      have h4 : Real.exp u - 1 - u ≤ Real.exp u := by linarith
      linarith

/-! ### General tilted Gaussian moments

∫ xⁿ·e^{cx}·φ₀ is finite for every n and c: the tilt moves it to a
shifted mean and the binomial theorem reduces the shifted power to
the raw Gaussian moments. -/

open MeasureTheory in
lemma integrable_pow_mul_exp_neg_half_sq (n : ℕ) :
    Integrable (fun y : ℝ => y ^ n * Real.exp (-(1/2) * y ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1/2) (by norm_num)
    (s := n) (lt_of_lt_of_le neg_one_lt_zero (Nat.cast_nonneg n))
  have h2 : ∀ y : ℝ, y ^ (n:ℝ) = y ^ n := fun y => Real.rpow_natCast y n
  simpa [h2] using h

open MeasureTheory in
lemma integrable_pow_shift_mul_exp (n : ℕ) (c : ℝ) :
    Integrable (fun y : ℝ => (y + c) ^ n * Real.exp (-(1/2) * y ^ 2)) := by
  have hfun : (fun y : ℝ => (y + c) ^ n * Real.exp (-(1/2) * y ^ 2))
      = fun y => ∑ j ∈ Finset.range (n+1),
          (y ^ j * Real.exp (-(1/2) * y ^ 2))
            * (c ^ (n - j) * (n.choose j)) := by
    funext y
    rw [add_pow, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hfun]
  exact integrable_finset_sum _ fun j _ =>
    (integrable_pow_mul_exp_neg_half_sq j).mul_const _

open MeasureTheory in
/-- The workhorse: every polynomially weighted exponentially tilted
    Gaussian integral is finite. -/
lemma integrable_pow_mul_exp_mul_gaussDensity (n : ℕ) (c : ℝ) :
    Integrable
      (fun x : ℝ => x ^ n * (Real.exp (c * x) * gaussDensity x 0 1)) := by
  have hfun : (fun x : ℝ => x ^ n * (Real.exp (c * x) * gaussDensity x 0 1))
      = fun x => (Real.exp (c ^ 2 / 2) * (2 * π) ^ (-1/2 : ℝ))
          * (x ^ n * Real.exp (-(1/2) * (x - c) ^ 2)) := by
    funext x
    rw [gaussDensity_tilt, gaussDensity_one_eq]
    ring
  rw [hfun]
  have h := (integrable_pow_shift_mul_exp n c).comp_sub_right c
  have hfix : (fun x : ℝ => (x - c + c) ^ n * Real.exp (-(1/2) * (x - c) ^ 2))
      = fun x => x ^ n * Real.exp (-(1/2) * (x - c) ^ 2) := by
    funext x
    rw [sub_add_cancel]
  rw [hfix] at h
  exact h.const_mul _

/-! ### The remainder as a density ratio

φ_t/φ₀ = e^u with u = tx − t²/2, so the score remainder is
h·φ₀/p_t with h the numerator polynomial-exponential, and the density
lower bound p_t ≥ (1−t)φ₀ ≥ φ₀/2 converts the ratio bound into
r² ≤ 4h². The split h = −(3/2)t² + u·v + E·(1+v) isolates the t²
leading term from the Taylor-controlled corrections. -/

/-- Deviation exponent: φ_t(x)/φ₀(x) = e^{u(t,x)}. -/
def uExp (t x : ℝ) : ℝ := t * x - t ^ 2 / 2

/-- The v-polynomial of the numerator split. -/
def vPoly (t x : ℝ) : ℝ := t * x - t ^ 2 - 2 * t ^ 2 * x

/-- Numerator of the score remainder over φ₀. -/
def hNum (t x : ℝ) : ℝ :=
  Real.exp (uExp t x) * (1 + t * (x - t) - 2 * t ^ 2 * x)
    - 1 - 2 * t * x * (1 - t)

lemma gaussDensity_ratio (t x : ℝ) :
    gaussDensity x t 1 = Real.exp (uExp t x) * gaussDensity x 0 1 := by
  simp only [gaussDensity_one_eq, uExp]
  have hexp : Real.exp (-(1/2) * (x - t) ^ 2)
      = Real.exp (t * x - t ^ 2 / 2) * Real.exp (-(1/2) * (x - 0) ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  linear_combination ((2 * π) ^ (-1/2 : ℝ)) * hexp

/-- The score remainder is the ratio h·φ₀/p_t. -/
lemma scoreRemainder_eq {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (x : ℝ) :
    scoreRemainder t x = hNum t x * gaussDensity x 0 1 / mixCurve t x := by
  have hp : mixCurve t x ≠ 0 := ne_of_gt (mixDensity_pos h0 h1 t x)
  unfold scoreRemainder scoreCurve
  rw [eq_div_iff hp, sub_mul, div_mul_cancel₀ _ hp,
    show mixCurve t x
      = t * gaussDensity x t 1 + (1 - t) * gaussDensity x 0 1 from rfl,
    gaussDensity_ratio t x]
  unfold hNum
  ring

/-- The numerator split: h = −(3/2)t² + u·v + E·(1+v). -/
lemma hNum_split (t x : ℝ) :
    hNum t x = -(3/2) * t ^ 2 + uExp t x * vPoly t x
      + (Real.exp (uExp t x) - 1 - uExp t x) * (1 + vPoly t x) := by
  unfold hNum uExp vPoly
  ring

/-- The density lower bound converts the ratio into r² ≤ 4h² on
    t ∈ (0, 1/2]. -/
lemma scoreRemainder_sq_le {t : ℝ} (h0 : 0 < t) (h2 : t ≤ 1/2) (x : ℝ) :
    scoreRemainder t x ^ 2 ≤ 4 * hNum t x ^ 2 := by
  have h1 : t < 1 := lt_of_le_of_lt h2 (by norm_num)
  rw [scoreRemainder_eq h0 h1, div_pow, mul_pow]
  have hp := mixDensity_pos h0 h1 t x
  have hφ := gaussDensity_pos x 0
  have hlow := le_mixDensity_right (w := t) h0.le t x
  have hhalf : gaussDensity x 0 1 / 2 ≤ mixCurve t x := by
    have hge : (1/2 : ℝ) ≤ 1 - t := by linarith
    calc gaussDensity x 0 1 / 2 = (1/2) * gaussDensity x 0 1 := by ring
      _ ≤ (1 - t) * gaussDensity x 0 1 :=
          mul_le_mul_of_nonneg_right hge hφ.le
      _ ≤ mixCurve t x := hlow
  rw [div_le_iff₀ (by positivity)]
  have hsq : (gaussDensity x 0 1 / 2) ^ 2 ≤ mixCurve t x ^ 2 := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq
    (by positivity : (0:ℝ) ≤ 4 * hNum t x ^ 2)]

/-- e^{|x|} is dominated by the symmetric sum e^x + e^{−x}. -/
lemma exp_abs_le (x : ℝ) :
    Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
    nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

set_option maxHeartbeats 800000 in
/-- The pointwise numerator bound: on t ∈ (0, 1/2],
    h² ≤ 256·t⁴·(1+x²)³·(e^x + e^{−x}). -/
lemma hNum_sq_le {t x : ℝ} (h0 : 0 < t) (h2 : t ≤ 1/2) :
    hNum t x ^ 2
      ≤ 256 * t ^ 4 * ((1 + x ^ 2) ^ 3 * (Real.exp x + Real.exp (-x))) := by
  have hx2 : (0:ℝ) ≤ x ^ 2 := sq_nonneg x
  have ht2 : t ^ 2 ≤ 1/4 := by nlinarith
  set S := Real.exp x + Real.exp (-x) with hSdef
  have hS2 : (2:ℝ) ≤ S := by
    have hmul : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]
      simp
    nlinarith [sq_nonneg (Real.exp x - 1), Real.exp_pos x,
      Real.exp_pos (-x), hmul]
  have hu2 : uExp t x ^ 2 ≤ 2 * t ^ 2 * (1 + x ^ 2) := by
    unfold uExp
    nlinarith [sq_nonneg (t * x + t ^ 2 / 2), ht2, sq_nonneg (t * x),
      mul_le_mul_of_nonneg_right ht2 (sq_nonneg (t * x))]
  have hv2 : vPoly t x ^ 2 ≤ 6 * t ^ 2 * (1 + x ^ 2) := by
    have hfac : vPoly t x = t * (x - t - 2 * t * x) := by
      unfold vPoly
      ring
    rw [hfac, mul_pow]
    have hin : (x - t - 2 * t * x) ^ 2 ≤ 6 * (1 + x ^ 2) := by
      nlinarith [sq_nonneg (x + t), sq_nonneg (x + 2 * t * x),
        sq_nonneg (t - 2 * t * x), ht2,
        mul_le_mul_of_nonneg_right ht2 (sq_nonneg x)]
    calc t ^ 2 * (x - t - 2 * t * x) ^ 2
        ≤ t ^ 2 * (6 * (1 + x ^ 2)) :=
          mul_le_mul_of_nonneg_left hin (sq_nonneg t)
      _ = 6 * t ^ 2 * (1 + x ^ 2) := by ring
  have h1v : (1 + vPoly t x) ^ 2 ≤ 5 * (1 + x ^ 2) := by
    nlinarith [hv2, ht2, hx2, sq_nonneg (1 - vPoly t x),
      sq_nonneg (vPoly t x)]
  have habs2u : 2 * |uExp t x| ≤ |x| + 1/4 := by
    unfold uExp
    have htri : |t * x - t ^ 2 / 2| ≤ |t * x| + |t ^ 2 / 2| := abs_sub _ _
    have hax : |t * x| ≤ |x| / 2 := by
      rw [abs_mul, abs_of_pos h0]
      nlinarith [abs_nonneg x]
    have hat : |t ^ 2 / 2| ≤ 1/8 := by
      rw [abs_of_nonneg (by positivity)]
      nlinarith
    linarith
  have hE0 := exp_sub_one_sub_nonneg (uExp t x)
  have hEle := exp_sub_one_sub_le (uExp t x)
  have hexp2 : Real.exp |uExp t x| ^ 2 ≤ 3 * S := by
    have hsq : Real.exp |uExp t x| ^ 2 = Real.exp (2 * |uExp t x|) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [hsq]
    calc Real.exp (2 * |uExp t x|) ≤ Real.exp (|x| + 1/4) :=
          Real.exp_le_exp.mpr habs2u
      _ = Real.exp |x| * Real.exp (1/4) := Real.exp_add _ _
      _ ≤ S * 3 := by
          have he14 : Real.exp (1/4 : ℝ) ≤ 3 := by
            calc Real.exp (1/4 : ℝ) ≤ Real.exp 1 :=
                  Real.exp_le_exp.mpr (by norm_num)
              _ ≤ 3 := Real.exp_one_lt_three.le
          exact mul_le_mul (exp_abs_le x) he14 (Real.exp_pos _).le
            (by nlinarith [Real.exp_pos x, Real.exp_pos (-x)])
      _ = 3 * S := mul_comm _ _
  have hE2 : (Real.exp (uExp t x) - 1 - uExp t x) ^ 2
      ≤ 12 * t ^ 4 * (1 + x ^ 2) ^ 2 * S := by
    have hEsq : (Real.exp (uExp t x) - 1 - uExp t x) ^ 2
        ≤ (uExp t x ^ 2 * Real.exp |uExp t x|) ^ 2 :=
      pow_le_pow_left₀ hE0 hEle 2
    have hu4 : (uExp t x ^ 2) ^ 2 ≤ (2 * t ^ 2 * (1 + x ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) hu2 2
    have hprod : (uExp t x ^ 2 * Real.exp |uExp t x|) ^ 2
        ≤ (2 * t ^ 2 * (1 + x ^ 2)) ^ 2 * (3 * S) := by
      rw [mul_pow]
      exact mul_le_mul hu4 hexp2 (sq_nonneg _) (by positivity)
    calc (Real.exp (uExp t x) - 1 - uExp t x) ^ 2
        ≤ (2 * t ^ 2 * (1 + x ^ 2)) ^ 2 * (3 * S) := hEsq.trans hprod
      _ = 12 * t ^ 4 * (1 + x ^ 2) ^ 2 * S := by ring
  have hB : (uExp t x * vPoly t x) ^ 2
      ≤ 12 * t ^ 4 * (1 + x ^ 2) ^ 2 := by
    rw [mul_pow]
    calc uExp t x ^ 2 * vPoly t x ^ 2
        ≤ (2 * t ^ 2 * (1 + x ^ 2)) * (6 * t ^ 2 * (1 + x ^ 2)) :=
          mul_le_mul hu2 hv2 (sq_nonneg _) (by positivity)
      _ = 12 * t ^ 4 * (1 + x ^ 2) ^ 2 := by ring
  have hC : ((Real.exp (uExp t x) - 1 - uExp t x) * (1 + vPoly t x)) ^ 2
      ≤ 60 * t ^ 4 * (1 + x ^ 2) ^ 3 * S := by
    rw [mul_pow]
    calc (Real.exp (uExp t x) - 1 - uExp t x) ^ 2 * (1 + vPoly t x) ^ 2
        ≤ (12 * t ^ 4 * (1 + x ^ 2) ^ 2 * S) * (5 * (1 + x ^ 2)) :=
          mul_le_mul hE2 h1v (sq_nonneg _) (by positivity)
      _ = 60 * t ^ 4 * (1 + x ^ 2) ^ 3 * S := by ring
  have hpow1 : (1:ℝ) ≤ 1 + x ^ 2 := by nlinarith
  have hpow23 : (1 + x ^ 2) ^ 2 ≤ (1 + x ^ 2) ^ 3 := by
    nlinarith [sq_nonneg (1 + x ^ 2), hpow1, hx2]
  have hSpos : (0:ℝ) < S := by positivity
  have hp3 : (1:ℝ) ≤ (1 + x ^ 2) ^ 3 := one_le_pow₀ hpow1
  have hP3S : (2:ℝ) ≤ (1 + x ^ 2) ^ 3 * S := by nlinarith
  have h36 : 36 * (1 + x ^ 2) ^ 2 ≤ 18 * ((1 + x ^ 2) ^ 3 * S) := by
    have ha := mul_le_mul_of_nonneg_left hS2 (sq_nonneg (1 + x ^ 2))
    have hb := mul_le_mul_of_nonneg_right hpow23 hSpos.le
    nlinarith
  rw [hNum_split]
  have hsum : (-(3/2) * t ^ 2 + uExp t x * vPoly t x
      + (Real.exp (uExp t x) - 1 - uExp t x) * (1 + vPoly t x)) ^ 2
      ≤ 3 * ((3/2 * t ^ 2) ^ 2 + (uExp t x * vPoly t x) ^ 2
        + ((Real.exp (uExp t x) - 1 - uExp t x) * (1 + vPoly t x)) ^ 2) := by
    nlinarith [sq_nonneg (-(3/2) * t ^ 2 - uExp t x * vPoly t x),
      sq_nonneg (uExp t x * vPoly t x
        - (Real.exp (uExp t x) - 1 - uExp t x) * (1 + vPoly t x)),
      sq_nonneg (-(3/2) * t ^ 2
        - (Real.exp (uExp t x) - 1 - uExp t x) * (1 + vPoly t x))]
  calc (-(3/2) * t ^ 2 + uExp t x * vPoly t x
      + (Real.exp (uExp t x) - 1 - uExp t x) * (1 + vPoly t x)) ^ 2
      ≤ 3 * ((3/2 * t ^ 2) ^ 2 + (uExp t x * vPoly t x) ^ 2
        + ((Real.exp (uExp t x) - 1 - uExp t x) * (1 + vPoly t x)) ^ 2) :=
        hsum
    _ ≤ 3 * ((3/2 * t ^ 2) ^ 2 + 12 * t ^ 4 * (1 + x ^ 2) ^ 2
        + 60 * t ^ 4 * (1 + x ^ 2) ^ 3 * S) := by linarith
    _ = t ^ 4 * (27/4 + 36 * (1 + x ^ 2) ^ 2
        + 180 * ((1 + x ^ 2) ^ 3 * S)) := by ring
    _ ≤ t ^ 4 * (256 * ((1 + x ^ 2) ^ 3 * S)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = 256 * t ^ 4 * ((1 + x ^ 2) ^ 3 * S) := by ring

/-! ### Assembly: the middle layer instantiated on the mixture

μ is the base Gaussian N(0,1). The pointwise dominator
1024·t⁴·(1+x²)³·(e^x+e^{−x}) has finite Gaussian integral by the
tilted-moment workhorse, which gives the L² remainder bound hrb and
the integrability side conditions, and
`fisher_expansion_of_score_expansion` lands on the honest mixture
score: leading rate 2(k−1) = 2 with coefficient k²·E[a²] = 4. -/

section Assembly

open MeasureTheory ProbabilityTheory Filter Topology

/-- The base measure N(0, 1). -/
def gaussMeasure : Measure ℝ := gaussianReal 0 ⟨1, one_pos.le⟩

instance : IsProbabilityMeasure gaussMeasure := by
  unfold gaussMeasure
  infer_instance

/-- Integrability against N(0,1) is integrability of the φ₀-weighted
    function. -/
lemma integrable_gaussMeasure_iff {g : ℝ → ℝ} :
    Integrable g gaussMeasure
      ↔ Integrable (fun x => g x * gaussDensity x 0 1) := by
  unfold gaussMeasure
  rw [gaussianReal_of_var_ne_zero 0 one_nnreal_ne_zero,
    integrable_withDensity_iff (measurable_gaussianPDF _ _)
      (Filter.Eventually.of_forall fun x => by
        simp [ProbabilityTheory.gaussianPDF])]
  have hpt : ∀ x : ℝ,
      (ENNReal.ofReal (gaussianPDFReal 0 ⟨1, one_pos.le⟩ x)).toReal
        = gaussDensity x 0 1 := fun x => by
    rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
      ← gaussDensity_eq_gaussianPDFReal x 0 1 one_pos]
  constructor <;> intro h <;>
    exact h.congr (Filter.Eventually.of_forall fun x => by
      simp only [gaussianPDF, hpt])

/-- Integrals against N(0,1) are φ₀-weighted volume integrals. -/
lemma integral_gaussMeasure (g : ℝ → ℝ) :
    ∫ x, g x ∂gaussMeasure = ∫ x, g x * gaussDensity x 0 1 := by
  unfold gaussMeasure
  rw [integral_gaussianReal_eq_integral_smul one_nnreal_ne_zero]
  congr 1
  funext x
  rw [smul_eq_mul, gaussDensity_eq_gaussianPDFReal x 0 1 one_pos]
  ring

/-- The dominator of the score remainder. -/
def remDom (x : ℝ) : ℝ := (1 + x ^ 2) ^ 3 * (Real.exp x + Real.exp (-x))

lemma remDom_nonneg (x : ℝ) : 0 ≤ remDom x := by
  unfold remDom
  positivity

lemma integrable_remDom : Integrable remDom gaussMeasure := by
  rw [integrable_gaussMeasure_iff]
  have hc : ∀ c : ℝ, Integrable
      (fun x => (1 + x ^ 2) ^ 3 * (Real.exp (c * x) * gaussDensity x 0 1)) := by
    intro c
    have h := (((integrable_pow_mul_exp_mul_gaussDensity 0 c).add
      ((integrable_pow_mul_exp_mul_gaussDensity 2 c).const_mul 3)).add
      ((integrable_pow_mul_exp_mul_gaussDensity 4 c).const_mul 3)).add
      (integrable_pow_mul_exp_mul_gaussDensity 6 c)
    exact h.congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.add_apply]
      ring)
  have h := (hc 1).add (hc (-1))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  unfold remDom
  rw [show (1:ℝ) * x = x from one_mul x,
    show (-1:ℝ) * x = -x from neg_one_mul x]
  ring

/-- The score remainder's pointwise dominator on t ∈ (0, 1/2]. -/
lemma scoreRemainder_sq_le_dom {t x : ℝ} (h0 : 0 < t) (h2 : t ≤ 1/2) :
    scoreRemainder t x ^ 2 ≤ 1024 * t ^ 4 * remDom x := by
  have h1 := scoreRemainder_sq_le h0 h2 x
  have h3 := hNum_sq_le (x := x) h0 h2
  unfold remDom
  nlinarith

/-- Continuity of the score remainder in x. -/
lemma continuous_scoreRemainder {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    Continuous (fun x => scoreRemainder t x) := by
  have hnum : Continuous (fun x => gaussDensity x t 1 - gaussDensity x 0 1
      + t * ((x - t) * gaussDensity x t 1)) := by
    exact ((continuous_gaussDensity t).sub (continuous_gaussDensity 0)).add
      (continuous_const.mul ((continuous_id.sub continuous_const).mul
        (continuous_gaussDensity t)))
  have hden : Continuous (fun x => mixCurve t x) := by
    have : (fun x => mixCurve t x)
        = fun x => t * gaussDensity x t 1 + (1 - t) * gaussDensity x 0 1 :=
      funext fun x => rfl
    rw [this]
    exact (continuous_const.mul (continuous_gaussDensity t)).add
      (continuous_const.mul (continuous_gaussDensity 0))
  have hscore : Continuous (fun x => scoreCurve t x) :=
    hnum.div hden (fun x => ne_of_gt (mixDensity_pos h0 h1 t x))
  exact hscore.sub (continuous_const.mul continuous_id)

/-- x² is N(0,1)-integrable with integral one. -/
lemma integrable_sq_gaussMeasure :
    Integrable (fun x : ℝ => x ^ 2) gaussMeasure := by
  rw [integrable_gaussMeasure_iff]
  exact (integrable_sq_mul_gaussDensity 0).congr
    (Filter.Eventually.of_forall fun x => by simp)

lemma integral_sq_gaussMeasure : ∫ x, x ^ 2 ∂gaussMeasure = 1 := by
  unfold gaussMeasure
  have h := integral_central_sq_gaussianReal 0
  simpa using h

/-- thm:fisher_decay discharged on the mixture: the honest score of
    the k = 2 curve has Fisher leading rate 2 with coefficient 4,
    every hypothesis of the abstract middle layer proved, none
    assumed. -/
theorem mixture_fisher_expansion :
    HasLeadingRate
      (fun t => ∫ x, scoreCurve t x ^ 2 ∂gaussMeasure) 2 4 := by
  have hM0 : (0:ℝ) ≤ 1024 * ∫ x, remDom x ∂gaussMeasure := by
    have h := integral_nonneg (μ := gaussMeasure) (f := remDom)
      (fun x => remDom_nonneg x)
    positivity
  have hhalf : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ t ≤ 1/2 := by
    filter_upwards [eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num))] with t ht0 ht2
    exact ⟨ht0, ht2.le⟩
  have h := fisher_expansion_of_score_expansion
    (μ := gaussMeasure) (s := scoreCurve) (a := fun x => x)
    (r := scoreRemainder) (k := 2)
    (M := 1024 * ∫ x, remDom x ∂gaussMeasure)
    (by norm_num) hM0
    (Filter.Eventually.of_forall fun t x => by
      simpa using scoreCurve_decomp t x)
    integrable_sq_gaussMeasure
    (by
      filter_upwards [hhalf] with t ⟨ht0, ht2⟩
      have ht1 : t < 1 := lt_of_le_of_lt ht2 (by norm_num)
      refine (integrable_remDom.const_mul (1024 * t ^ 4)).mono'
        (((continuous_scoreRemainder ht0 ht1).pow 2).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have := scoreRemainder_sq_le_dom (x := x) ht0 ht2
      linarith [remDom_nonneg x])
    (by
      filter_upwards [hhalf] with t ⟨ht0, ht2⟩
      have ht1 : t < 1 := lt_of_le_of_lt ht2 (by norm_num)
      have hint : Integrable
          (fun x => (1/2) * (x ^ 2 + 1024 * t ^ 4 * remDom x))
          gaussMeasure :=
        (integrable_sq_gaussMeasure.add
          (integrable_remDom.const_mul _)).const_mul _
      refine hint.mono'
        ((continuous_id.mul (continuous_scoreRemainder ht0 ht1)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => ?_)
      have hdom := scoreRemainder_sq_le_dom (x := x) ht0 ht2
      rw [Real.norm_eq_abs]
      rcases abs_cases (x * scoreRemainder t x) with ⟨he, _⟩ | ⟨he, _⟩ <;>
        rw [he] <;>
        nlinarith [sq_nonneg (x - scoreRemainder t x),
          sq_nonneg (x + scoreRemainder t x)])
    (by
      filter_upwards [hhalf] with t ⟨ht0, ht2⟩
      have ht1 : t < 1 := lt_of_le_of_lt ht2 (by norm_num)
      calc ∫ x, scoreRemainder t x ^ 2 ∂gaussMeasure
          ≤ ∫ x, 1024 * t ^ 4 * remDom x ∂gaussMeasure := by
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun x => sq_nonneg _)
              (integrable_remDom.const_mul _)
              (Filter.Eventually.of_forall fun x =>
                scoreRemainder_sq_le_dom ht0 ht2)
        _ = (1024 * ∫ x, remDom x ∂gaussMeasure) * t ^ (2 * 2) := by
            rw [integral_const_mul]
            ring)
  convert h using 2
  rw [integral_sq_gaussMeasure]
  norm_num

/-- The slope reading on the mixture: log ∫s(t)²/log t → 2, so k̂
    recovers the KL order k = 2 on the canonical singular family. -/
theorem mixture_fisher_slope :
    Tendsto (fun t => Real.log (∫ x, scoreCurve t x ^ 2 ∂gaussMeasure)
        / Real.log t)
      (𝓝[>] (0:ℝ)) (𝓝 2) := by
  have h := mixture_fisher_expansion.log_slope (by norm_num)
  simpa using h

/-! ### The KL side of the curve

mixKL(t) = ∫ log(φ₀/p_t)·φ₀ is the divergence of the curve from the
base point. With w := t(e^u − 1) = p_t/φ₀ − 1 ≥ −t, the identity
∫w·φ₀ = 0 reduces it to ∫(w − log(1+w))·φ₀, whose quadratic part
∫w²/2·φ₀ = t²(e^{t²} − 1)/2 carries the exact leading term t⁴/2 and
whose cubic remainder is O(t⁶). The curve therefore has KL order 2,
which pairs with the Fisher reading of `mixture_fisher_expansion`. -/

section KLOrderSide

open MeasureTheory Filter Topology

/-- |e^u − 1| ≤ |u|·e^{|u|}. -/
lemma abs_exp_sub_one_le (u : ℝ) :
    |Real.exp u - 1| ≤ |u| * Real.exp |u| := by
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg (by nlinarith [Real.add_one_le_exp u]
        : (0:ℝ) ≤ Real.exp u - 1), abs_of_nonneg hu]
    have h := Real.add_one_le_exp (-u)
    have hprod : Real.exp (-u) * Real.exp u = 1 := by
      rw [← Real.exp_add]
      simp
    nlinarith [Real.exp_pos u]
  · rw [abs_of_nonpos (by
        nlinarith [Real.exp_le_one_iff.mpr hu.le] : Real.exp u - 1 ≤ 0),
      abs_of_neg hu]
    have h := Real.add_one_le_exp u
    have h2 : (1:ℝ) ≤ Real.exp (-u) := Real.one_le_exp (by linarith)
    nlinarith

/-- Quadratic log remainder: |log(1+w) − w + w²/2| ≤ 16·|w|³ on
    w ≥ −1/2. -/
lemma abs_log_quad_le {w : ℝ} (hw : -(1/2) ≤ w) :
    |Real.log (1 + w) - w + w ^ 2 / 2| ≤ 16 * |w| ^ 3 := by
  rcases le_or_gt |w| (1/2) with h | h
  · have hx : |(-w)| < 1 := by
      rw [abs_neg]
      linarith
    have hb := Real.abs_log_sub_add_sum_range_le hx 2
    have hsum : (∑ i ∈ Finset.range 2, (-w) ^ (i + 1) / ((i:ℝ) + 1))
        = -w + w ^ 2 / 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
    rw [hsum, abs_neg] at hb
    have hb' : |Real.log (1 + w) - w + w ^ 2 / 2| ≤ |w| ^ 3 / (1 - |w|) := by
      rw [show Real.log (1 + w) - w + w ^ 2 / 2
          = -w + w ^ 2 / 2 + Real.log (1 - -w) from by
        rw [sub_neg_eq_add]
        ring]
      exact hb
    have hden : (1:ℝ)/2 ≤ 1 - |w| := by linarith
    calc |Real.log (1 + w) - w + w ^ 2 / 2|
        ≤ |w| ^ 3 / (1 - |w|) := hb'
      _ ≤ |w| ^ 3 / (1/2) := by
          gcongr
      _ ≤ 16 * |w| ^ 3 := by
          have := pow_nonneg (abs_nonneg w) 3
          linarith
  · have hwpos : (0:ℝ) < w := by
      rcases le_or_gt 0 w with h0 | h0
      · rcases lt_or_eq_of_le h0 with h1 | h1
        · exact h1
        · rw [← h1] at h
          simp at h
          linarith
      · rw [abs_of_neg h0] at h
        linarith
    have habs : |w| = w := abs_of_pos hwpos
    have hw2 : (1:ℝ)/2 < w := by rwa [habs] at h
    have hlogle : Real.log (1 + w) ≤ w := by
      have h := Real.log_le_sub_one_of_pos
        (by linarith : (0:ℝ) < 1 + w)
      linarith
    have hlogge : (0:ℝ) ≤ Real.log (1 + w) :=
      Real.log_nonneg (by linarith)
    rw [habs]
    rcases abs_cases (Real.log (1 + w) - w + w ^ 2 / 2)
      with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> nlinarith

/-- The Gaussian exponential integral: ∫ e^{sx}·φ₀ = e^{s²/2}. -/
lemma integral_exp_mul_gaussDensity (s : ℝ) :
    ∫ x, Real.exp (s * x) * gaussDensity x 0 1
      = Real.exp (s ^ 2 / 2) := by
  have h : (fun x => Real.exp (s * x) * gaussDensity x 0 1)
      = fun x => Real.exp (s ^ 2 / 2) * gaussDensity x s 1 :=
    funext fun x => gaussDensity_tilt s x
  rw [h, integral_const_mul, integral_gaussDensity_eq_one, mul_one]

/-- The deviation of the curve density from the base: p_t/φ₀ − 1. -/
def wDev (t x : ℝ) : ℝ := t * (Real.exp (uExp t x) - 1)

lemma mixCurve_eq_wDev (t x : ℝ) :
    mixCurve t x = (1 + wDev t x) * gaussDensity x 0 1 := by
  show mixDensity t t x = _
  unfold mixDensity wDev
  rw [gaussDensity_ratio t x]
  ring

lemma wDev_ge {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : -t ≤ wDev t x := by
  unfold wDev
  nlinarith [Real.exp_pos (uExp t x)]

/-- Splitting e^u into the tilt form. -/
lemma exp_uExp_eq (t x : ℝ) :
    Real.exp (uExp t x)
      = Real.exp (-(t ^ 2 / 2)) * Real.exp (t * x) := by
  rw [← Real.exp_add]
  unfold uExp
  congr 1
  ring

lemma integrable_wDev_mul (t : ℝ) :
    Integrable (fun x => wDev t x * gaussDensity x 0 1) := by
  have h : (fun x => wDev t x * gaussDensity x 0 1)
      = fun x => (t * Real.exp (-(t ^ 2 / 2)))
          * (Real.exp (t * x) * gaussDensity x 0 1)
        - t * gaussDensity x 0 1 := by
    funext x
    unfold wDev
    rw [exp_uExp_eq]
    ring
  rw [h]
  exact ((integrable_exp_mul_gaussDensity t).const_mul _).sub
    ((integrable_gaussDensity 0).const_mul t)

/-- First w-moment vanishes: both densities integrate to one. -/
lemma integral_wDev (t : ℝ) :
    ∫ x, wDev t x * gaussDensity x 0 1 = 0 := by
  have h : (fun x => wDev t x * gaussDensity x 0 1)
      = fun x => (t * Real.exp (-(t ^ 2 / 2)))
          * (Real.exp (t * x) * gaussDensity x 0 1)
        - t * gaussDensity x 0 1 := by
    funext x
    unfold wDev
    rw [exp_uExp_eq]
    ring
  rw [h, integral_sub
    ((integrable_exp_mul_gaussDensity t).const_mul _)
    ((integrable_gaussDensity 0).const_mul t),
    integral_const_mul, integral_const_mul,
    integral_exp_mul_gaussDensity, integral_gaussDensity_eq_one]
  have hv : Real.exp (-(t ^ 2 / 2)) * Real.exp (t ^ 2 / 2) = 1 := by
    rw [← Real.exp_add,
      show (-(t ^ 2 / 2) + t ^ 2 / 2 : ℝ) = 0 from by ring,
      Real.exp_zero]
  linear_combination t * hv

/-- Second w-moment: ∫w²·φ₀ = t²(e^{t²} − 1). -/
lemma integral_wDev_sq (t : ℝ) :
    ∫ x, wDev t x ^ 2 * gaussDensity x 0 1
      = t ^ 2 * (Real.exp (t ^ 2) - 1) := by
  have e1 : Real.exp (-(t ^ 2 / 2)) ^ 2 = Real.exp (-(t ^ 2)) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have e2 : ∀ x : ℝ, Real.exp (t * x) ^ 2 = Real.exp (2 * t * x) := by
    intro x
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h : (fun x => wDev t x ^ 2 * gaussDensity x 0 1)
      = fun x => (t ^ 2 * Real.exp (-(t ^ 2)))
          * (Real.exp (2 * t * x) * gaussDensity x 0 1)
        - (2 * t ^ 2 * Real.exp (-(t ^ 2 / 2)))
          * (Real.exp (t * x) * gaussDensity x 0 1)
        + t ^ 2 * gaussDensity x 0 1 := by
    funext x
    unfold wDev
    rw [exp_uExp_eq]
    have hEX : (Real.exp (-(t ^ 2 / 2)) * Real.exp (t * x) - 1) ^ 2
        = Real.exp (-(t ^ 2)) * Real.exp (2 * t * x)
          - 2 * (Real.exp (-(t ^ 2 / 2)) * Real.exp (t * x)) + 1 := by
      calc (Real.exp (-(t ^ 2 / 2)) * Real.exp (t * x) - 1) ^ 2
          = Real.exp (-(t ^ 2 / 2)) ^ 2 * Real.exp (t * x) ^ 2
            - 2 * (Real.exp (-(t ^ 2 / 2)) * Real.exp (t * x)) + 1 := by
            ring
        _ = Real.exp (-(t ^ 2)) * Real.exp (2 * t * x)
            - 2 * (Real.exp (-(t ^ 2 / 2)) * Real.exp (t * x)) + 1 := by
            rw [e1, e2]
    rw [mul_pow, hEX]
    ring
  have hA : Integrable (fun x => (t ^ 2 * Real.exp (-(t ^ 2)))
      * (Real.exp (2 * t * x) * gaussDensity x 0 1)) :=
    (integrable_exp_mul_gaussDensity (2 * t)).const_mul _
  have hB : Integrable (fun x => (2 * t ^ 2 * Real.exp (-(t ^ 2 / 2)))
      * (Real.exp (t * x) * gaussDensity x 0 1)) :=
    (integrable_exp_mul_gaussDensity t).const_mul _
  have hAB : Integrable (fun x => (t ^ 2 * Real.exp (-(t ^ 2)))
      * (Real.exp (2 * t * x) * gaussDensity x 0 1)
      - (2 * t ^ 2 * Real.exp (-(t ^ 2 / 2)))
      * (Real.exp (t * x) * gaussDensity x 0 1)) := hA.sub hB
  have hC : Integrable (fun x => t ^ 2 * gaussDensity x 0 1) :=
    (integrable_gaussDensity 0).const_mul _
  rw [h, integral_add hAB hC, integral_sub hA hB,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_exp_mul_gaussDensity, integral_exp_mul_gaussDensity,
    integral_gaussDensity_eq_one]
  have hv1 : Real.exp (-(t ^ 2)) * Real.exp ((2 * t) ^ 2 / 2)
      = Real.exp (t ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hv2 : Real.exp (-(t ^ 2 / 2)) * Real.exp (t ^ 2 / 2) = 1 := by
    rw [← Real.exp_add,
      show (-(t ^ 2 / 2) + t ^ 2 / 2 : ℝ) = 0 from by ring,
      Real.exp_zero]
  linear_combination (t ^ 2 : ℝ) * hv1 - (2 * t ^ 2) * hv2

/-- The KL divergence of the base from the curve. -/
def mixKL (t : ℝ) : ℝ :=
  ∫ x, Real.log (gaussDensity x 0 1 / mixCurve t x) * gaussDensity x 0 1

/-- Dominator for the cubic remainder. -/
def klDom (x : ℝ) : ℝ :=
  (1 + x ^ 2 + x ^ 4) * (Real.exp (2 * x) + Real.exp (-(2 * x)))

lemma klDom_nonneg (x : ℝ) : 0 ≤ klDom x := by
  unfold klDom
  positivity

lemma integrable_klDom_mul :
    Integrable (fun x => klDom x * gaussDensity x 0 1) := by
  have hc : ∀ c : ℝ, Integrable (fun x => (1 + x ^ 2 + x ^ 4)
      * (Real.exp (c * x) * gaussDensity x 0 1)) := by
    intro c
    have h := ((integrable_pow_mul_exp_mul_gaussDensity 0 c).add
      (integrable_pow_mul_exp_mul_gaussDensity 2 c)).add
      (integrable_pow_mul_exp_mul_gaussDensity 4 c)
    exact h.congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.add_apply]
      ring)
  have h := (hc 2).add (hc (-2))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  unfold klDom
  rw [show (-2:ℝ) * x = -(2 * x) from by ring]
  ring

/-- The cubic dominator bound: |w|³ ≤ 15·t⁶·klDom on t ∈ (0, 1/2]. -/
lemma abs_wDev_cubed_le {t x : ℝ} (h0 : 0 < t) (h2 : t ≤ 1/2) :
    |wDev t x| ^ 3 ≤ 15 * t ^ 6 * klDom x := by
  have habs : |wDev t x| = t * |Real.exp (uExp t x) - 1| := by
    unfold wDev
    rw [abs_mul, abs_of_pos h0]
  have hu : |uExp t x| ≤ t * (|x| + 1) := by
    unfold uExp
    have h := abs_sub (t * x) (t ^ 2 / 2)
    have h1 : |t * x| = t * |x| := by rw [abs_mul, abs_of_pos h0]
    have h2' : |t ^ 2 / 2| ≤ t := by
      rw [abs_of_nonneg (by positivity)]
      nlinarith
    calc |t * x - t ^ 2 / 2| ≤ |t * x| + |t ^ 2 / 2| := h
      _ ≤ t * |x| + t := by rw [h1]; linarith
      _ = t * (|x| + 1) := by ring
  have hE := abs_exp_sub_one_le (uExp t x)
  have hexp3 : Real.exp |uExp t x| ^ 3
      ≤ 3 * (Real.exp (2 * x) + Real.exp (-(2 * x))) := by
    have h3u : 3 * |uExp t x| ≤ 2 * |x| + 1 := by
      have htri : |uExp t x| ≤ t * |x| + t ^ 2 / 2 := by
        unfold uExp
        calc |t * x - t ^ 2 / 2| ≤ |t * x| + |t ^ 2 / 2| := abs_sub _ _
          _ = t * |x| + t ^ 2 / 2 := by
              rw [abs_mul, abs_of_pos h0,
                abs_of_nonneg (show (0:ℝ) ≤ t ^ 2 / 2 by positivity)]
      nlinarith [abs_nonneg x,
        mul_nonneg (show (0:ℝ) ≤ 2 - 3 * t by linarith) (abs_nonneg x)]
    have hcube : Real.exp |uExp t x| ^ 3 = Real.exp (3 * |uExp t x|) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, sq, ← Real.exp_add,
        ← Real.exp_add]
      congr 1
      ring
    rw [hcube]
    calc Real.exp (3 * |uExp t x|) ≤ Real.exp (2 * |x| + 1) :=
          Real.exp_le_exp.mpr h3u
      _ = Real.exp (2 * |x|) * Real.exp 1 := Real.exp_add _ _
      _ ≤ (Real.exp (2 * x) + Real.exp (-(2 * x))) * 3 := by
          have habs2 : Real.exp (2 * |x|) ≤ Real.exp (2 * x)
              + Real.exp (-(2 * x)) := by
            have h := exp_abs_le (2 * x)
            rwa [show |2 * x| = 2 * |x| from by
              rw [abs_mul]; norm_num] at h
          exact mul_le_mul habs2 Real.exp_one_lt_three.le
            (Real.exp_pos 1).le (by positivity)
      _ = 3 * (Real.exp (2 * x) + Real.exp (-(2 * x))) := mul_comm _ _
  have hpoly : (|x| + 1) ^ 3 ≤ 5 * (1 + x ^ 2 + x ^ 4) := by
    have ha := abs_nonneg x
    have hb : |x| ^ 2 = x ^ 2 := sq_abs x
    have hc : |x| ≤ (1 + x ^ 2) / 2 := by nlinarith [sq_nonneg (|x| - 1)]
    nlinarith [pow_nonneg ha 3, sq_nonneg x, sq_nonneg (x ^ 2),
      mul_le_mul_of_nonneg_left hc (sq_nonneg x)]
  -- assemble
  have hw3 : |wDev t x| ^ 3
      ≤ t ^ 3 * (|uExp t x| * Real.exp |uExp t x|) ^ 3 := by
    rw [habs, mul_pow]
    have h := pow_le_pow_left₀ (abs_nonneg _) hE 3
    nlinarith [pow_nonneg (mul_nonneg (abs_nonneg (uExp t x))
      (Real.exp_pos |uExp t x|).le) 3, pow_pos h0 3]
  have hu3 : |uExp t x| ^ 3 ≤ t ^ 3 * (|x| + 1) ^ 3 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hu 3
    rwa [mul_pow] at h
  calc |wDev t x| ^ 3
      ≤ t ^ 3 * (|uExp t x| ^ 3 * Real.exp |uExp t x| ^ 3) := by
        rw [← mul_pow]
        nlinarith [hw3]
    _ ≤ t ^ 3 * ((t ^ 3 * (|x| + 1) ^ 3)
        * (3 * (Real.exp (2 * x) + Real.exp (-(2 * x))))) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_pos h0 3).le
        exact mul_le_mul hu3 hexp3 (pow_nonneg (Real.exp_pos _).le 3)
          (by positivity)
    _ ≤ t ^ 3 * ((t ^ 3 * (5 * (1 + x ^ 2 + x ^ 4)))
        * (3 * (Real.exp (2 * x) + Real.exp (-(2 * x))))) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_pos h0 3).le
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hpoly (pow_pos h0 3).le
    _ = 15 * t ^ 6 * klDom x := by
        unfold klDom
        ring

lemma continuous_wDev (t : ℝ) : Continuous fun x => wDev t x := by
  unfold wDev uExp
  fun_prop

lemma one_add_wDev_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (x : ℝ) :
    0 < 1 + wDev t x := by
  have heq := mixCurve_eq_wDev t x
  have hp : 0 < mixCurve t x := mixDensity_pos h0 h1 t x
  have hφ := gaussDensity_pos x 0
  nlinarith [hp, hφ, heq]

lemma integrable_wDev_sq_mul {t : ℝ} (h0 : 0 < t) (h2 : t ≤ 1/2) :
    Integrable (fun x => wDev t x ^ 2 * gaussDensity x 0 1) := by
  have hg : Integrable
      (fun x => (1 + 15 * t ^ 6 * klDom x) * gaussDensity x 0 1) := by
    have h := (integrable_gaussDensity 0).add
      (integrable_klDom_mul.const_mul (15 * t ^ 6))
    exact h.congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.add_apply]
      ring)
  refine hg.mono' (((continuous_wDev t).pow 2).mul
    (continuous_gaussDensity 0)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hφ := (gaussDensity_pos x 0).le
  have hcube := abs_wDev_cubed_le (x := x) h0 h2
  have hsq : wDev t x ^ 2 ≤ 1 + |wDev t x| ^ 3 := by
    rcases le_or_gt |wDev t x| 1 with h | h
    · have := pow_le_one₀ (abs_nonneg _) h (n := 2)
      have h3 := pow_nonneg (abs_nonneg (wDev t x)) 3
      rw [← sq_abs]
      nlinarith
    · have := pow_le_pow_right₀ h.le (show 2 ≤ 3 by norm_num)
      rw [← sq_abs]
      nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hφ)]
  nlinarith [mul_le_mul_of_nonneg_right hsq hφ,
    mul_le_mul_of_nonneg_right hcube hφ]

lemma integrable_abs_wDev_cubed {t : ℝ} (h0 : 0 < t) (h2 : t ≤ 1/2) :
    Integrable (fun x => |wDev t x| ^ 3 * gaussDensity x 0 1) := by
  refine (integrable_klDom_mul.const_mul (15 * t ^ 6)).mono'
    ((((continuous_wDev t).abs.pow 3).mul
      (continuous_gaussDensity 0)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  have hφ := (gaussDensity_pos x 0).le
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (pow_nonneg (abs_nonneg _) 3) hφ)]
  calc |wDev t x| ^ 3 * gaussDensity x 0 1
      ≤ (15 * t ^ 6 * klDom x) * gaussDensity x 0 1 :=
        mul_le_mul_of_nonneg_right (abs_wDev_cubed_le h0 h2) hφ
    _ = 15 * t ^ 6 * (klDom x * gaussDensity x 0 1) := by ring

lemma continuous_log_one_add_wDev {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    Continuous fun x => Real.log (1 + wDev t x) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact ((continuous_const.add (continuous_wDev t)).continuousAt).log
    (ne_of_gt (one_add_wDev_pos h0 h1 x))

lemma wDev_sub_log_nonneg {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (x : ℝ) :
    0 ≤ wDev t x - Real.log (1 + wDev t x) := by
  have h := Real.log_le_sub_one_of_pos (one_add_wDev_pos h0 h1 x)
  linarith

lemma wDev_sub_log_le {t : ℝ} (h0 : 0 < t) (h2 : t ≤ 1/2) (x : ℝ) :
    wDev t x - Real.log (1 + wDev t x)
      ≤ wDev t x ^ 2 / 2 + 16 * |wDev t x| ^ 3 := by
  have hw : -(1/2) ≤ wDev t x := by
    have h := wDev_ge h0.le x
    linarith
  have h := abs_log_quad_le hw
  have h1 := (abs_le.mp h).1
  linarith

lemma integrable_wDev_sub_log {t : ℝ} (h0 : 0 < t) (h1 : t < 1)
    (h2 : t ≤ 1/2) :
    Integrable (fun x =>
      (wDev t x - Real.log (1 + wDev t x)) * gaussDensity x 0 1) := by
  have hg : Integrable (fun x =>
      (1/2) * (wDev t x ^ 2 * gaussDensity x 0 1)
        + 16 * (|wDev t x| ^ 3 * gaussDensity x 0 1)) :=
    ((integrable_wDev_sq_mul h0 h2).const_mul _).add
      ((integrable_abs_wDev_cubed h0 h2).const_mul _)
  refine hg.mono' ((((continuous_wDev t).sub
    (continuous_log_one_add_wDev h0 h1)).mul
    (continuous_gaussDensity 0)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  have hφ := (gaussDensity_pos x 0).le
  have hnn := wDev_sub_log_nonneg h0 h1 x
  have hle := wDev_sub_log_le h0 h2 x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn hφ)]
  nlinarith [mul_le_mul_of_nonneg_right hle hφ]

/-- The reduction: ∫wφ₀ = 0 turns the KL into the nonnegative
    integrand w − log(1+w). -/
lemma mixKL_eq {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (h2 : t ≤ 1/2) :
    mixKL t = ∫ x,
      (wDev t x - Real.log (1 + wDev t x)) * gaussDensity x 0 1 := by
  unfold mixKL
  have hfun : ∀ x, Real.log (gaussDensity x 0 1 / mixCurve t x)
        * gaussDensity x 0 1
      = (wDev t x - Real.log (1 + wDev t x)) * gaussDensity x 0 1
        - wDev t x * gaussDensity x 0 1 := by
    intro x
    have hφ : gaussDensity x 0 1 ≠ 0 := ne_of_gt (gaussDensity_pos x 0)
    have h1w : (1 + wDev t x) ≠ 0 := ne_of_gt (one_add_wDev_pos h0 h1 x)
    have hdiv : gaussDensity x 0 1 / mixCurve t x
        = (1 + wDev t x)⁻¹ := by
      rw [mixCurve_eq_wDev]
      field_simp
    rw [hdiv, Real.log_inv]
    ring
  simp only [hfun]
  rw [integral_sub (integrable_wDev_sub_log h0 h1 h2)
    (integrable_wDev_mul t), integral_wDev, sub_zero]

/-- The mixture curve has KL order 2: mixKL(t) = t⁴/2 + O(t⁵). -/
theorem mixKL_hasKLOrder : HasKLOrder mixKL 2 := by
  refine ⟨1/2, by norm_num, ?_⟩
  set Ckl := ∫ x, klDom x * gaussDensity x 0 1 with hCkl
  clear_value Ckl
  have hCkl0 : 0 ≤ Ckl := by
    rw [hCkl]
    exact integral_nonneg fun x =>
      mul_nonneg (klDom_nonneg x) (gaussDensity_pos x 0).le
  apply hasLeadingRate_of_expansion
    (R := fun t => mixKL t - 1/2 * t ^ (2*2)) (M := 240 * Ckl + 2)
  · exact Filter.Eventually.of_forall fun t => by ring
  · filter_upwards [eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num))] with t ht0 ht2
    have h0t : (0:ℝ) < t := ht0
    have h2t : t ≤ 1/2 := ht2.le
    have h1t : t < 1 := lt_trans ht2 (by norm_num)
    -- step 1: distance to the quadratic part
    have hstep1 : |mixKL t - 1/2 * (t ^ 2 * (Real.exp (t ^ 2) - 1))|
        ≤ 16 * (15 * t ^ 6 * Ckl) := by
      rw [mixKL_eq h0t h1t h2t, ← integral_wDev_sq t,
        show (1/2 : ℝ) * ∫ x, wDev t x ^ 2 * gaussDensity x 0 1
          = ∫ x, (1/2) * (wDev t x ^ 2 * gaussDensity x 0 1) from
          (integral_const_mul _ _).symm,
        ← integral_sub (integrable_wDev_sub_log h0t h1t h2t)
          ((integrable_wDev_sq_mul h0t h2t).const_mul _)]
      have hptw : ∀ x,
          |(wDev t x - Real.log (1 + wDev t x)) * gaussDensity x 0 1
            - (1/2) * (wDev t x ^ 2 * gaussDensity x 0 1)|
          ≤ 16 * (|wDev t x| ^ 3 * gaussDensity x 0 1) := by
        intro x
        have hφ := (gaussDensity_pos x 0).le
        have hw : -(1/2) ≤ wDev t x := by
          have h := wDev_ge h0t.le x
          linarith
        have hq := abs_log_quad_le hw
        have habs : |(wDev t x - Real.log (1 + wDev t x)) * gaussDensity x 0 1
            - (1/2) * (wDev t x ^ 2 * gaussDensity x 0 1)|
            = |wDev t x - Real.log (1 + wDev t x) - wDev t x ^ 2 / 2|
              * gaussDensity x 0 1 := by
          rw [show (wDev t x - Real.log (1 + wDev t x)) * gaussDensity x 0 1
              - (1/2) * (wDev t x ^ 2 * gaussDensity x 0 1)
            = (wDev t x - Real.log (1 + wDev t x) - wDev t x ^ 2 / 2)
              * gaussDensity x 0 1 from by ring,
            abs_mul, abs_of_nonneg hφ]
        rw [habs]
        have hqq : |wDev t x - Real.log (1 + wDev t x) - wDev t x ^ 2 / 2|
            ≤ 16 * |wDev t x| ^ 3 := by
          rw [show wDev t x - Real.log (1 + wDev t x) - wDev t x ^ 2 / 2
            = -(Real.log (1 + wDev t x) - wDev t x + wDev t x ^ 2 / 2)
            from by ring, abs_neg]
          exact hq
        nlinarith [mul_le_mul_of_nonneg_right hqq hφ]
      calc |∫ x, ((wDev t x - Real.log (1 + wDev t x)) * gaussDensity x 0 1
            - (1/2) * (wDev t x ^ 2 * gaussDensity x 0 1))|
          ≤ ∫ x, ‖(wDev t x - Real.log (1 + wDev t x)) * gaussDensity x 0 1
            - (1/2) * (wDev t x ^ 2 * gaussDensity x 0 1)‖ := by
            rw [← Real.norm_eq_abs]
            exact norm_integral_le_integral_norm _
        _ ≤ ∫ x, 16 * (|wDev t x| ^ 3 * gaussDensity x 0 1) := by
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun x => norm_nonneg _)
              ((integrable_abs_wDev_cubed h0t h2t).const_mul 16)
              (Filter.Eventually.of_forall fun x => ?_)
            simp only [Real.norm_eq_abs]
            exact hptw x
        _ = 16 * ∫ x, |wDev t x| ^ 3 * gaussDensity x 0 1 :=
            integral_const_mul _ _
        _ ≤ 16 * (15 * t ^ 6 * Ckl) := by
            rw [hCkl]
            have h := integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun x =>
                mul_nonneg (pow_nonneg (abs_nonneg _) 3)
                  (gaussDensity_pos x 0).le)
              (integrable_klDom_mul.const_mul (15 * t ^ 6))
              (Filter.Eventually.of_forall fun x => by
                calc |wDev t x| ^ 3 * gaussDensity x 0 1
                    ≤ (15 * t ^ 6 * klDom x) * gaussDensity x 0 1 :=
                      mul_le_mul_of_nonneg_right
                        (abs_wDev_cubed_le h0t h2t)
                        (gaussDensity_pos x 0).le
                  _ = 15 * t ^ 6 * (klDom x * gaussDensity x 0 1) := by
                      ring)
            rw [integral_const_mul] at h
            linarith
    -- step 2: the quadratic part against t⁴/2
    have hstep2 : |1/2 * (t ^ 2 * (Real.exp (t ^ 2) - 1)) - 1/2 * t ^ 4|
        ≤ (3/2) * t ^ 6 := by
      have hE0 := exp_sub_one_sub_nonneg (t ^ 2)
      have hEle := exp_sub_one_sub_le (t ^ 2)
      rw [abs_of_nonneg (by nlinarith)]
      have hexp3 : Real.exp |t ^ 2| ≤ 3 := by
        rw [abs_of_nonneg (sq_nonneg t)]
        calc Real.exp (t ^ 2) ≤ Real.exp 1 :=
              Real.exp_le_exp.mpr (by nlinarith)
          _ ≤ 3 := Real.exp_one_lt_three.le
      have h4 : (t ^ 2) ^ 2 * Real.exp |t ^ 2| ≤ 3 * t ^ 4 := by
        nlinarith [sq_nonneg (t ^ 2), Real.exp_pos |t ^ 2|]
      nlinarith
    -- combine
    have hcomb := abs_add_le
      (mixKL t - 1/2 * (t ^ 2 * (Real.exp (t ^ 2) - 1)))
      (1/2 * (t ^ 2 * (Real.exp (t ^ 2) - 1)) - 1/2 * t ^ 4)
    have ht6 : t ^ 6 ≤ t ^ (2*2+1) := by
      have := pow_le_pow_of_le_one h0t.le h1t.le
        (show 2*2+1 ≤ 6 by norm_num)
      simpa using this
    have htp : (0:ℝ) < t ^ (2*2+1) := pow_pos h0t _
    calc |mixKL t - 1/2 * t ^ (2*2)|
        ≤ |mixKL t - 1/2 * (t ^ 2 * (Real.exp (t ^ 2) - 1))|
          + |1/2 * (t ^ 2 * (Real.exp (t ^ 2) - 1)) - 1/2 * t ^ 4| := by
          have h := hcomb
          rw [show mixKL t - 1/2 * (t ^ 2 * (Real.exp (t ^ 2) - 1))
              + (1/2 * (t ^ 2 * (Real.exp (t ^ 2) - 1)) - 1/2 * t ^ 4)
            = mixKL t - 1/2 * t ^ 4 from by ring] at h
          calc |mixKL t - 1/2 * t ^ (2*2)|
              = |mixKL t - 1/2 * t ^ 4| := by norm_num
            _ ≤ _ := h
      _ ≤ 16 * (15 * t ^ 6 * Ckl) + (3/2) * t ^ 6 :=
          add_le_add hstep1 hstep2
      _ = (240 * Ckl + 3/2) * t ^ 6 := by ring
      _ ≤ (240 * Ckl + 3/2) * t ^ (2*2+1) :=
          mul_le_mul_of_nonneg_left ht6 (by linarith)
      _ ≤ (240 * Ckl + 2) * t ^ (2*2+1) :=
          mul_le_mul_of_nonneg_right (by linarith)
            (pow_nonneg h0t.le _)

/-- Both bridge readings certified on the canonical singular family:
    the curve has KL order 2, and its Fisher carries leading rate
    2(k−1) = 2 with coefficient 4. -/
theorem mixture_readings :
    HasKLOrder mixKL 2
      ∧ HasLeadingRate
          (fun t => ∫ x, scoreCurve t x ^ 2 ∂gaussMeasure) 2 4 :=
  ⟨mixKL_hasKLOrder, mixture_fisher_expansion⟩

end KLOrderSide

end Assembly

end

end DeadDirections
