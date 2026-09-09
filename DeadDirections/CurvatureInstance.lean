/-
  Closed-form curvature instances (theory paper, prop:curvature_rate
  item (ii)).

  The Gaussian mean-map families μ = (t^k + w², w, tw) carry their
  Fisher metric as the pullback of the Euclidean metric, so the
  sectional curvature is the Gauss curvature of the embedded surface.
  In the determinant form
      K = (L̃·Ñ − M̃²) / (EG − F²)²,
  with L̃ = det[μ_tt, μ_t, μ_w] and companions the unnormalized second
  fundamental minors, every ingredient is polynomial in the jet: no
  square root enters. The jets along w = 0 are certified as genuine
  derivatives of the parametrization, and the closed forms follow by
  field arithmetic: K = −1/(4t²(1+t²)²) at k = 2 and −1/(9t⁴(1+t²)²)
  at k = 3, the paper's exact values, with K·t^{2(k−1)} converging to
  −1/4 and −1/9: the family curvature rate −2(k−1), attained.
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import DeadDirections.FisherDecay
import DeadDirections.RpowRate

namespace DeadDirections

open Filter Topology

/-- The scalar triple product det[a, b, c] on ℝ³. -/
def det3 (a b c : Fin 3 → ℝ) : ℝ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) - a 1 * (b 0 * c 2 - b 2 * c 0)
    + a 2 * (b 0 * c 1 - b 1 * c 0)

/-- The dot product on ℝ³, explicit. -/
def dot3 (a b : Fin 3 → ℝ) : ℝ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2

/-- The Gauss curvature of a surface jet, in the determinant form:
    the unnormalized second-fundamental minors over the squared metric
    determinant. -/
noncomputable def surfCurvAt (mt mw mtt mtw mww : Fin 3 → ℝ) : ℝ :=
  (det3 mtt mt mw * det3 mww mt mw - (det3 mtw mt mw) ^ 2)
    / (dot3 mt mt * dot3 mw mw - (dot3 mt mw) ^ 2) ^ 2

/-! ### The k = 2 family μ = (t² + w², w, tw) -/

/-- The k = 2 Gaussian mean map. -/
def fam2 (t w : ℝ) : Fin 3 → ℝ := ![t ^ 2 + w ^ 2, w, t * w]

/-- The t-partial of fam2 is (2t, 0, w): certified. -/
lemma fam2_dt (t w : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => fam2 s w i) ((![2 * t, 0, w] : Fin 3 → ℝ) i)
      t := by
  fin_cases i
  · show HasDerivAt (fun s => s ^ 2 + w ^ 2) (2 * t) t
    have h1 := hasDerivAt_pow 2 t
    norm_num at h1
    exact h1.add_const (w ^ 2)
  · show HasDerivAt (fun _ => w) 0 t
    exact hasDerivAt_const t w
  · show HasDerivAt (fun s => s * w) w t
    simpa using (hasDerivAt_id t).mul_const w

/-- The w-partial of fam2 is (2w, 1, t): certified. -/
lemma fam2_dw (t w : ℝ) (i : Fin 3) :
    HasDerivAt (fun v => fam2 t v i) ((![2 * w, 1, t] : Fin 3 → ℝ) i)
      w := by
  fin_cases i
  · show HasDerivAt (fun v => t ^ 2 + v ^ 2) (2 * w) w
    have h1 := hasDerivAt_pow 2 w
    norm_num at h1
    exact h1.const_add (t ^ 2)
  · show HasDerivAt (fun v => v) 1 w
    exact hasDerivAt_id w
  · show HasDerivAt (fun v => t * v) t w
    simpa using (hasDerivAt_id w).const_mul t

/-- The second t-partial along w = 0 is (2, 0, 0): the derivative of
    the certified t-partial. -/
lemma fam2_dtt (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => (![2 * s, 0, (0:ℝ)] : Fin 3 → ℝ) i)
      ((![2, 0, 0] : Fin 3 → ℝ) i) t := by
  fin_cases i
  · show HasDerivAt (fun s => 2 * s) 2 t
    simpa using (hasDerivAt_id t).const_mul 2
  · show HasDerivAt (fun _ => (0:ℝ)) 0 t
    exact hasDerivAt_const t (0:ℝ)
  · show HasDerivAt (fun _ => (0:ℝ)) 0 t
    exact hasDerivAt_const t (0:ℝ)

/-- The mixed partial along w = 0 is (0, 0, 1): the w-derivative of
    the t-partial (2t, 0, w). -/
lemma fam2_dtw (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun v => (![2 * t, 0, v] : Fin 3 → ℝ) i)
      ((![0, 0, 1] : Fin 3 → ℝ) i) (0:ℝ) := by
  fin_cases i
  · show HasDerivAt (fun _ => 2 * t) 0 (0:ℝ)
    exact hasDerivAt_const (0:ℝ) (2 * t)
  · show HasDerivAt (fun _ => (0:ℝ)) 0 (0:ℝ)
    exact hasDerivAt_const (0:ℝ) (0:ℝ)
  · show HasDerivAt (fun v => v) 1 (0:ℝ)
    exact hasDerivAt_id (0:ℝ)

/-- The second w-partial is (2, 0, 0): the w-derivative of the
    w-partial (2w, 1, t). -/
lemma fam2_dww (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun v => (![2 * v, 1, t] : Fin 3 → ℝ) i)
      ((![2, 0, 0] : Fin 3 → ℝ) i) (0:ℝ) := by
  fin_cases i
  · show HasDerivAt (fun v => 2 * v) 2 (0:ℝ)
    simpa using (hasDerivAt_id (0:ℝ)).const_mul 2
  · show HasDerivAt (fun _ => (1:ℝ)) 0 (0:ℝ)
    exact hasDerivAt_const (0:ℝ) (1:ℝ)
  · show HasDerivAt (fun _ => t) 0 (0:ℝ)
    exact hasDerivAt_const (0:ℝ) t

/-- prop:curvature_rate (ii), k = 2 closed form: on the trajectory
    w = 0 the Gauss curvature of the k = 2 family is exactly
    −1/(4t²(1+t²)²). -/
theorem fam2_curvature {t : ℝ} (ht : t ≠ 0) :
    surfCurvAt ![2 * t, 0, 0] ![0, 1, t] ![2, 0, 0] ![0, 0, 1]
      ![2, 0, 0]
      = -(1 / (4 * t ^ 2 * (1 + t ^ 2) ^ 2)) := by
  unfold surfCurvAt det3 dot3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  field_simp
  ring

/-- The k = 2 divergence rate: K·t² converges to −1/4, the family
    rate −2(k−1) = −2 with coefficient 1/4. -/
theorem fam2_curvature_rate :
    Tendsto (fun t : ℝ =>
      surfCurvAt ![2 * t, 0, 0] ![0, 1, t] ![2, 0, 0] ![0, 0, 1]
        ![2, 0, 0] * t ^ 2)
      (𝓝[>] (0:ℝ)) (𝓝 (-(1/4))) := by
  have hlim : Tendsto (fun t : ℝ => -(1 / (4 * (1 + t ^ 2) ^ 2)))
      (𝓝 (0:ℝ)) (𝓝 (-(1/4))) := by
    have hden : ∀ t : ℝ, 4 * (1 + t ^ 2) ^ 2 ≠ 0 := fun t => by
      positivity
    have h : Tendsto (fun t : ℝ => -(1 / (4 * (1 + t ^ 2) ^ 2)))
        (𝓝 (0:ℝ)) (𝓝 (-(1 / (4 * (1 + (0:ℝ) ^ 2) ^ 2)))) :=
      ((continuous_const.div (by continuity) hden).neg).tendsto 0
    have heq : -(1 / (4 * (1 + (0:ℝ) ^ 2) ^ 2)) = -(1/4 : ℝ) := by
      norm_num
    rwa [heq] at h
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht0
  have ht : t ≠ 0 := ne_of_gt ht0
  rw [fam2_curvature ht]
  field_simp

/-! ### The k = 3 family μ = (t³ + w², w, tw) -/

/-- The k = 3 Gaussian mean map. -/
def fam3 (t w : ℝ) : Fin 3 → ℝ := ![t ^ 3 + w ^ 2, w, t * w]

/-- The t-partial of fam3 is (3t², 0, w): certified. -/
lemma fam3_dt (t w : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => fam3 s w i)
      ((![3 * t ^ 2, 0, w] : Fin 3 → ℝ) i) t := by
  fin_cases i
  · show HasDerivAt (fun s => s ^ 3 + w ^ 2) (3 * t ^ 2) t
    have h1 := hasDerivAt_pow 3 t
    norm_num at h1
    exact h1.add_const (w ^ 2)
  · show HasDerivAt (fun _ => w) 0 t
    exact hasDerivAt_const t w
  · show HasDerivAt (fun s => s * w) w t
    simpa using (hasDerivAt_id t).mul_const w

/-- The second t-partial along w = 0 is (6t, 0, 0). -/
lemma fam3_dtt (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => (![3 * s ^ 2, 0, (0:ℝ)] : Fin 3 → ℝ) i)
      ((![6 * t, 0, 0] : Fin 3 → ℝ) i) t := by
  fin_cases i
  · show HasDerivAt (fun s => 3 * s ^ 2) (6 * t) t
    have h := (hasDerivAt_pow 2 t).const_mul 3
    norm_num at h
    convert h using 1
    ring
  · show HasDerivAt (fun _ => (0:ℝ)) 0 t
    exact hasDerivAt_const t (0:ℝ)
  · show HasDerivAt (fun _ => (0:ℝ)) 0 t
    exact hasDerivAt_const t (0:ℝ)

/-- prop:curvature_rate (ii), k = 3 closed form: on the trajectory
    w = 0 the Gauss curvature of the k = 3 family is exactly
    −1/(9t⁴(1+t²)²). -/
theorem fam3_curvature {t : ℝ} (ht : t ≠ 0) :
    surfCurvAt ![3 * t ^ 2, 0, 0] ![0, 1, t] ![6 * t, 0, 0]
      ![0, 0, 1] ![2, 0, 0]
      = -(1 / (9 * t ^ 4 * (1 + t ^ 2) ^ 2)) := by
  unfold surfCurvAt det3 dot3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  field_simp
  ring

/-- The k = 3 divergence rate: K·t⁴ converges to −1/9, the family
    rate −2(k−1) = −4 with coefficient 1/9. -/
theorem fam3_curvature_rate :
    Tendsto (fun t : ℝ =>
      surfCurvAt ![3 * t ^ 2, 0, 0] ![0, 1, t] ![6 * t, 0, 0]
        ![0, 0, 1] ![2, 0, 0] * t ^ 4)
      (𝓝[>] (0:ℝ)) (𝓝 (-(1/9))) := by
  have hlim : Tendsto (fun t : ℝ => -(1 / (9 * (1 + t ^ 2) ^ 2)))
      (𝓝 (0:ℝ)) (𝓝 (-(1/9))) := by
    have hden : ∀ t : ℝ, 9 * (1 + t ^ 2) ^ 2 ≠ 0 := fun t => by
      positivity
    have h : Tendsto (fun t : ℝ => -(1 / (9 * (1 + t ^ 2) ^ 2)))
        (𝓝 (0:ℝ)) (𝓝 (-(1 / (9 * (1 + (0:ℝ) ^ 2) ^ 2)))) :=
      ((continuous_const.div (by continuity) hden).neg).tendsto 0
    have heq : -(1 / (9 * (1 + (0:ℝ) ^ 2) ^ 2)) = -(1/9 : ℝ) := by
      norm_num
    rwa [heq] at h
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht0
  have ht : t ≠ 0 := ne_of_gt ht0
  rw [fam3_curvature ht]
  field_simp

/-! ### Volume scaling (cor:volume at the k = 2 instance)

The corollary's mechanism on the closed-form family: the curvature
magnitude is strictly antitone in t, so the high-curvature set is
exactly a transverse tube; the tube volume is a power integral; and
the two scalings come out as explicit limits, Fisher volume times the
threshold converging to 1/8 (the M⁻¹ law) and Lebesgue volume times
the square root of the threshold converging to 1/2 (the M^{-1/2}
law). -/

section VolumeScaling

/-- The curvature magnitude of the k = 2 family on the trajectory. -/
noncomputable def famKmag (t : ℝ) : ℝ := 1 / (4 * t ^ 2 * (1 + t ^ 2) ^ 2)

lemma famKmag_eq_neg_curv {t : ℝ} (ht : t ≠ 0) :
    famKmag t
      = -(surfCurvAt ![2 * t, 0, 0] ![0, 1, t] ![2, 0, 0] ![0, 0, 1]
          ![2, 0, 0]) := by
  rw [fam2_curvature ht, famKmag, neg_neg]

/-- The curvature magnitude is strictly antitone on t > 0. -/
lemma famKmag_strictAnti {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    famKmag b < famKmag a := by
  unfold famKmag
  have hb : 0 < b := ha.trans hab
  have hden : 4 * a ^ 2 * (1 + a ^ 2) ^ 2
      < 4 * b ^ 2 * (1 + b ^ 2) ^ 2 := by
    have h1 : a ^ 2 < b ^ 2 := by
      exact pow_lt_pow_left₀ hab ha.le two_ne_zero
    have h2 : (1 + a ^ 2) ^ 2 < (1 + b ^ 2) ^ 2 := by
      have : 1 + a ^ 2 < 1 + b ^ 2 := by linarith
      exact pow_lt_pow_left₀ this (by positivity) two_ne_zero
    have h3 : 4 * a ^ 2 < 4 * b ^ 2 := by linarith
    exact mul_lt_mul h3 h2.le (by positivity) (by positivity)
  exact one_div_lt_one_div_of_lt (by positivity) hden

/-- The high-curvature set is exactly the transverse tube: for
    positive t and δ, the curvature magnitude exceeds the threshold
    famKmag δ precisely when t < δ. -/
theorem highcurv_iff_tube {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) :
    famKmag δ < famKmag t ↔ t < δ := by
  constructor
  · intro h
    by_contra hle
    push Not at hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq] at h; exact lt_irrefl _ h
    · exact absurd h (not_lt.mpr (famKmag_strictAnti hδ hlt).le)
  · exact famKmag_strictAnti ht

/-- The transverse tube volume at density t^m (with m = k−1 at KL
    order k): the power integral, exact. -/
theorem tube_volume_pow (m : ℕ) (δ : ℝ) :
    ∫ t in (0:ℝ)..δ, t ^ m = δ ^ (m + 1) / (m + 1) := by
  rw [integral_pow]
  norm_num

/-- cor:volume at k = 2, Fisher side: the Fisher volume of the tube
    (density t at leading order) times the curvature threshold
    converges to 1/8. The M⁻¹ law with explicit coefficient. -/
theorem fisher_volume_scaling :
    Filter.Tendsto
      (fun δ : ℝ => (∫ t in (0:ℝ)..δ, t) * famKmag δ)
      (𝓝[>] (0:ℝ)) (𝓝 (1/8)) := by
  have hlim : Filter.Tendsto
      (fun δ : ℝ => 1 / (8 * (1 + δ ^ 2) ^ 2))
      (𝓝 (0:ℝ)) (𝓝 (1/8)) := by
    have hden : ∀ δ : ℝ, 8 * (1 + δ ^ 2) ^ 2 ≠ 0 := fun δ => by
      positivity
    have h : Filter.Tendsto
        (fun δ : ℝ => 1 / (8 * (1 + δ ^ 2) ^ 2)) (𝓝 (0:ℝ))
        (𝓝 (1 / (8 * (1 + (0:ℝ) ^ 2) ^ 2))) :=
      (continuous_const.div (by continuity) hden).tendsto 0
    have heq : 1 / (8 * (1 + (0:ℝ) ^ 2) ^ 2) = (1/8 : ℝ) := by
      norm_num
    rwa [heq] at h
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with δ hδ0
  have hδ : δ ≠ 0 := ne_of_gt hδ0
  rw [integral_id, famKmag]
  field_simp
  ring

/-- The square root of the threshold, explicit on the family. -/
lemma famKmag_sqrt {δ : ℝ} (hδ : 0 < δ) :
    Real.sqrt (famKmag δ) = 1 / (2 * δ * (1 + δ ^ 2)) := by
  have hsq : famKmag δ = (1 / (2 * δ * (1 + δ ^ 2))) ^ 2 := by
    unfold famKmag
    field_simp
    ring
  rw [hsq, Real.sqrt_sq (by positivity)]

/-- cor:volume at k = 2, Lebesgue side: the Lebesgue volume of the
    tube (density 1) times the square root of the threshold converges
    to 1/2. The M^{-1/2} law with explicit coefficient. -/
theorem lebesgue_volume_scaling :
    Filter.Tendsto
      (fun δ : ℝ => (∫ _ in (0:ℝ)..δ, (1:ℝ))
        * Real.sqrt (famKmag δ))
      (𝓝[>] (0:ℝ)) (𝓝 (1/2)) := by
  have hlim : Filter.Tendsto
      (fun δ : ℝ => 1 / (2 * (1 + δ ^ 2)))
      (𝓝 (0:ℝ)) (𝓝 (1/2)) := by
    have hden : ∀ δ : ℝ, 2 * (1 + δ ^ 2) ≠ 0 := fun δ => by
      positivity
    have h : Filter.Tendsto
        (fun δ : ℝ => 1 / (2 * (1 + δ ^ 2))) (𝓝 (0:ℝ))
        (𝓝 (1 / (2 * (1 + (0:ℝ) ^ 2)))) :=
      (continuous_const.div (by continuity) hden).tendsto 0
    have heq : 1 / (2 * (1 + (0:ℝ) ^ 2)) = (1/2 : ℝ) := by
      norm_num
    rwa [heq] at h
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with δ hδ0
  rw [intervalIntegral.integral_const, famKmag_sqrt hδ0]
  have hδ : δ ≠ 0 := ne_of_gt hδ0
  simp only [smul_eq_mul, sub_zero, mul_one]
  field_simp

/-- The k = 3 curvature magnitude on the trajectory. -/
noncomputable def famKmag3 (t : ℝ) : ℝ :=
  1 / (9 * t ^ 4 * (1 + t ^ 2) ^ 2)

/-- The 3/4-power of the k = 3 threshold, closed form: the general-k
    threshold inversion runs on real exponents, and this is its
    first non-integer instance. -/
lemma famKmag3_rpow {δ : ℝ} (hδ : 0 < δ) :
    famKmag3 δ ^ ((3:ℝ)/4)
      = 1 / (9 ^ ((3:ℝ)/4) * δ ^ 3 * (1 + δ ^ 2) ^ ((3:ℝ)/2)) := by
  have hd4 : ((δ ^ 4 : ℝ)) ^ ((3:ℝ)/4) = δ ^ 3 := by
    rw [← Real.rpow_natCast δ 4, ← Real.rpow_mul hδ.le]
    norm_num [Real.rpow_natCast]
  have hsq : (((1 + δ ^ 2) ^ 2 : ℝ)) ^ ((3:ℝ)/4)
      = (1 + δ ^ 2) ^ ((3:ℝ)/2) := by
    rw [← Real.rpow_natCast (1 + δ ^ 2) 2,
      ← Real.rpow_mul (by positivity)]
    norm_num
  unfold famKmag3
  rw [one_div]
  rw [Real.inv_rpow (by positivity),
    Real.mul_rpow (by positivity : (0:ℝ) ≤ 9 * δ ^ 4)
      (by positivity : (0:ℝ) ≤ (1 + δ ^ 2) ^ 2),
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 9) (by positivity), hd4, hsq,
    one_div]

/-- cor:volume at k = 3, Fisher side: the M^{-3/4} law. Fisher tube
    volume (density t²) times the 3/4-power of the threshold
    converges to 1/(3·9^{3/4}), the first non-integer-exponent
    instance of the M^{-k/(2(k-1))} scaling. -/
theorem fisher_volume_scaling_k3 :
    Tendsto (fun δ : ℝ =>
      (∫ t in (0:ℝ)..δ, t ^ 2) * famKmag3 δ ^ ((3:ℝ)/4))
      (𝓝[>] (0:ℝ)) (𝓝 (1 / (3 * 9 ^ ((3:ℝ)/4)))) := by
  have hbase : Tendsto (fun δ : ℝ => (1 + δ ^ 2 : ℝ)) (𝓝 0)
      (𝓝 1) := by
    have hc : Continuous (fun δ : ℝ => (1 + δ ^ 2 : ℝ)) := by
      continuity
    have h := hc.tendsto (0:ℝ)
    norm_num at h
    exact h
  have hrpow : Tendsto (fun δ : ℝ => (1 + δ ^ 2 : ℝ) ^ ((3:ℝ)/2))
      (𝓝 0) (𝓝 1) := by
    have h := (Real.continuousAt_rpow_const 1 ((3:ℝ)/2)
      (Or.inl one_ne_zero)).tendsto.comp hbase
    simpa using h
  have hden : Tendsto
      (fun δ : ℝ => 3 * 9 ^ ((3:ℝ)/4) * (1 + δ ^ 2) ^ ((3:ℝ)/2))
      (𝓝 0) (𝓝 (3 * 9 ^ ((3:ℝ)/4))) := by
    have h := hrpow.const_mul (3 * (9:ℝ) ^ ((3:ℝ)/4))
    rwa [mul_one] at h
  have hlim : Tendsto (fun δ : ℝ =>
      1 / (3 * 9 ^ ((3:ℝ)/4) * (1 + δ ^ 2) ^ ((3:ℝ)/2)))
      (𝓝 (0:ℝ)) (𝓝 (1 / (3 * 9 ^ ((3:ℝ)/4)))) := by
    exact Filter.Tendsto.div
      (tendsto_const_nhds (X := ℝ) (x := (1:ℝ)) (f := 𝓝 (0:ℝ)))
      hden (by positivity : (3:ℝ) * 9 ^ ((3:ℝ)/4) ≠ 0)
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with δ hδ0
  rw [integral_pow, famKmag3_rpow hδ0]
  have hδ3 : (δ:ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hδ0)
  have hr1 : (9:ℝ) ^ ((3:ℝ)/4) ≠ 0 := by positivity
  have hr2 : ((1 + δ ^ 2 : ℝ)) ^ ((3:ℝ)/2) ≠ 0 := by positivity
  norm_num
  field_simp
  ring_nf
  rw [mul_inv_cancel₀ (ne_of_gt (show (0:ℝ) < δ from hδ0))]

end VolumeScaling

/-! ### The uniform general-k tube law

The k = 2 and k = 3 instances above are members of one family: the
model curvature magnitude 1/(k²·t^{2(k−1)}·(1+t²)²) obeys the
M^{−k/(2(k−1))} Fisher law at every k ≥ 2, on the real-exponent
calculus. Sheet uniformity enters as the corollary's proof uses it:
any curvature profile with two-sided transverse bounds has its
high-curvature set sandwiched between two closed-form tubes, and any
Fisher density with two-sided t^{k−1} bounds integrates to the law
with the same constants, uniform in the profile. -/

section GeneralKTube

/-- The general-k curvature magnitude on the model family; k = 2 and
    k = 3 are famKmag and famKmag3. -/
noncomputable def famKmagK (k : ℕ) (t : ℝ) : ℝ :=
  1 / (k ^ 2 * t ^ (2 * (k - 1)) * (1 + t ^ 2) ^ 2)

lemma famKmagK_two : famKmagK 2 = famKmag := by
  funext t
  unfold famKmagK famKmag
  norm_num

lemma famKmagK_three : famKmagK 3 = famKmag3 := by
  funext t
  unfold famKmagK famKmag3
  norm_num

/-- The general-k threshold inversion on real exponents. -/
lemma famKmagK_rpow {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    famKmagK k δ ^ ((k:ℝ) / (2 * ((k:ℝ) - 1)))
      = 1 / (((k:ℝ) ^ 2) ^ ((k:ℝ) / (2 * ((k:ℝ) - 1))) * δ ^ k
          * (1 + δ ^ 2) ^ ((k:ℝ) / ((k:ℝ) - 1))) := by
  have hk2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hkm : (0:ℝ) < (k:ℝ) - 1 := by linarith
  have hncast : ((2 * (k - 1) : ℕ) : ℝ) = 2 * ((k:ℝ) - 1) := by
    push_cast [Nat.cast_sub (show 1 ≤ k by omega)]
    ring
  have hd : ((δ ^ (2 * (k - 1)) : ℝ)) ^ ((k:ℝ) / (2 * ((k:ℝ) - 1)))
      = δ ^ k := by
    rw [← Real.rpow_natCast δ (2 * (k - 1)), ← Real.rpow_mul hδ.le,
      hncast]
    have hexp : 2 * ((k:ℝ) - 1) * ((k:ℝ) / (2 * ((k:ℝ) - 1)))
        = (k:ℝ) := by
      field_simp
    rw [hexp, Real.rpow_natCast]
  have hsq : (((1 + δ ^ 2) ^ 2 : ℝ)) ^ ((k:ℝ) / (2 * ((k:ℝ) - 1)))
      = (1 + δ ^ 2) ^ ((k:ℝ) / ((k:ℝ) - 1)) := by
    rw [← Real.rpow_natCast (1 + δ ^ 2) 2,
      ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    field_simp
  unfold famKmagK
  rw [one_div, Real.inv_rpow (by positivity),
    Real.mul_rpow (by positivity : (0:ℝ) ≤ (k:ℝ) ^ 2 * δ ^ (2 * (k - 1)))
      (by positivity : (0:ℝ) ≤ (1 + δ ^ 2) ^ 2),
    Real.mul_rpow (by positivity : (0:ℝ) ≤ ((k:ℝ) ^ 2))
      (by positivity), hd, hsq, one_div]

/-- cor:volume, the uniform general-k Fisher law: tube volume at
    density t^{k−1} times the k/(2(k−1))-power of the threshold
    converges to 1/(k·(k²)^{k/(2(k−1))}), for every k ≥ 2. -/
theorem fisher_volume_scaling_general {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun δ : ℝ =>
      (∫ t in (0:ℝ)..δ, t ^ (k - 1))
        * famKmagK k δ ^ ((k:ℝ) / (2 * ((k:ℝ) - 1))))
      (𝓝[>] (0:ℝ))
      (𝓝 (1 / ((k:ℝ)
        * ((k:ℝ) ^ 2) ^ ((k:ℝ) / (2 * ((k:ℝ) - 1)))))) := by
  have hk2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hkm : (0:ℝ) < (k:ℝ) - 1 := by linarith
  have hkpos : (0:ℝ) < (k:ℝ) := by linarith
  have hbase : Tendsto (fun δ : ℝ => (1 + δ ^ 2 : ℝ)) (𝓝 0)
      (𝓝 1) := by
    have hc : Continuous (fun δ : ℝ => (1 + δ ^ 2 : ℝ)) := by
      continuity
    have h := hc.tendsto (0:ℝ)
    norm_num at h
    exact h
  have hrpow : Tendsto
      (fun δ : ℝ => (1 + δ ^ 2 : ℝ) ^ ((k:ℝ) / ((k:ℝ) - 1)))
      (𝓝 0) (𝓝 1) := by
    have h := (Real.continuousAt_rpow_const 1 ((k:ℝ) / ((k:ℝ) - 1))
      (Or.inl one_ne_zero)).tendsto.comp hbase
    simpa using h
  have hCpos : (0:ℝ)
      < (k:ℝ) * ((k:ℝ) ^ 2) ^ ((k:ℝ) / (2 * ((k:ℝ) - 1))) :=
    mul_pos hkpos (Real.rpow_pos_of_pos (by positivity) _)
  have hden : Tendsto (fun δ : ℝ =>
      (k:ℝ) * ((k:ℝ) ^ 2) ^ ((k:ℝ) / (2 * ((k:ℝ) - 1)))
        * (1 + δ ^ 2) ^ ((k:ℝ) / ((k:ℝ) - 1)))
      (𝓝 0) (𝓝 ((k:ℝ) * ((k:ℝ) ^ 2) ^ ((k:ℝ) / (2 * ((k:ℝ) - 1))))) := by
    have h := hrpow.const_mul
      ((k:ℝ) * ((k:ℝ) ^ 2) ^ ((k:ℝ) / (2 * ((k:ℝ) - 1))))
    rwa [mul_one] at h
  have hlim : Tendsto (fun δ : ℝ =>
      1 / ((k:ℝ) * ((k:ℝ) ^ 2) ^ ((k:ℝ) / (2 * ((k:ℝ) - 1)))
        * (1 + δ ^ 2) ^ ((k:ℝ) / ((k:ℝ) - 1))))
      (𝓝 (0:ℝ))
      (𝓝 (1 / ((k:ℝ) * ((k:ℝ) ^ 2) ^ ((k:ℝ) / (2 * ((k:ℝ) - 1)))))) :=
    Filter.Tendsto.div
      (tendsto_const_nhds (X := ℝ) (x := (1:ℝ)) (f := 𝓝 (0:ℝ)))
      hden (ne_of_gt hCpos)
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with δ hδ0
  have hδ0' : (0:ℝ) < δ := hδ0
  rw [integral_pow, famKmagK_rpow hk hδ0',
    show k - 1 + 1 = k from by omega,
    zero_pow (by omega : k ≠ 0), sub_zero]
  have hdenc : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
    push_cast [Nat.cast_sub (show 1 ≤ k by omega)]
    ring
  rw [hdenc]
  have h1 : (δ:ℝ) ^ k ≠ 0 := pow_ne_zero k (ne_of_gt hδ0')
  have h2 : ((k:ℝ) ^ 2) ^ ((k:ℝ) / (2 * ((k:ℝ) - 1))) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  have h3 : ((1 + δ ^ 2 : ℝ)) ^ ((k:ℝ) / ((k:ℝ) - 1)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  field_simp

/-- Sheet uniformity, tube identification: any curvature profile with
    two-sided transverse bounds c₁/t^{2(k−1)} ≤ K ≤ c₂/t^{2(k−1)} has
    its high-curvature set sandwiched between the two closed-form
    tubes, with constants uniform in the profile. -/
theorem highcurv_tube_sandwich {k : ℕ} (hk : 2 ≤ k) {c₁ c₂ M : ℝ}
    (hc1 : 0 < c₁) (hc2 : 0 < c₂) (hM : 0 < M) (K : ℝ → ℝ)
    (hKlow : ∀ t, 0 < t → c₁ / t ^ (2 * (k - 1)) ≤ K t)
    (hKup : ∀ t, 0 < t → K t ≤ c₂ / t ^ (2 * (k - 1))) :
    (∀ t, 0 < t →
      t < (c₁ / M) ^ ((1:ℝ) / (2 * ((k:ℝ) - 1))) → M < K t)
    ∧ (∀ t, 0 < t → M < K t →
      t < (c₂ / M) ^ ((1:ℝ) / (2 * ((k:ℝ) - 1)))) := by
  have hncast : ((2 * (k - 1) : ℕ) : ℝ) = 2 * ((k:ℝ) - 1) := by
    push_cast [Nat.cast_sub (show 1 ≤ k by omega)]
    ring
  have hkm : (0:ℝ) < (k:ℝ) - 1 := by
    have : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have hnne : (2 * (k - 1) : ℕ) ≠ 0 := by omega
  have hroot : ∀ {c : ℝ}, 0 < c →
      ((c / M) ^ ((1:ℝ) / (2 * ((k:ℝ) - 1)))) ^ (2 * (k - 1) : ℕ)
        = c / M := by
    intro c hc
    rw [← Real.rpow_natCast ((c / M) ^ ((1:ℝ) / (2 * ((k:ℝ) - 1))))
        (2 * (k - 1)),
      ← Real.rpow_mul (by positivity : (0:ℝ) ≤ c / M), hncast,
      show (1:ℝ) / (2 * ((k:ℝ) - 1)) * (2 * ((k:ℝ) - 1)) = 1 from by
        field_simp,
      Real.rpow_one]
  constructor
  · intro t ht htlt
    have htn : t ^ (2 * (k - 1)) < c₁ / M := by
      calc t ^ (2 * (k - 1))
          < ((c₁ / M) ^ ((1:ℝ) / (2 * ((k:ℝ) - 1)))) ^ (2 * (k - 1)) :=
            pow_lt_pow_left₀ htlt ht.le hnne
        _ = c₁ / M := hroot hc1
    have hMlt : M < c₁ / t ^ (2 * (k - 1)) := by
      rw [lt_div_iff₀ (pow_pos ht _)]
      rw [lt_div_iff₀ hM] at htn
      linarith [htn]
    exact lt_of_lt_of_le hMlt (hKlow t ht)
  · intro t ht hMK
    have hMlt : M < c₂ / t ^ (2 * (k - 1)) :=
      lt_of_lt_of_le hMK (hKup t ht)
    have htn : t ^ (2 * (k - 1)) < c₂ / M := by
      rw [lt_div_iff₀ hM]
      rw [lt_div_iff₀ (pow_pos ht _)] at hMlt
      linarith [hMlt]
    refine lt_of_pow_lt_pow_left₀ (2 * (k - 1))
      (Real.rpow_nonneg (by positivity) _) ?_
    rw [hroot hc2]
    exact htn

/-- Sheet uniformity, volume side: any Fisher density with two-sided
    t^{k−1} bounds integrates over a tube of radius r to the exact
    power law with the same constants, uniform in the density. -/
theorem tube_weight_sandwich {k : ℕ} (hk : 2 ≤ k) {b₁ b₂ r : ℝ}
    (hr : 0 ≤ r) {w : ℝ → ℝ}
    (hw_int : IntervalIntegrable w MeasureTheory.volume 0 r)
    (hwlow : ∀ t ∈ Set.Icc (0:ℝ) r, b₁ * t ^ (k - 1) ≤ w t)
    (hwup : ∀ t ∈ Set.Icc (0:ℝ) r, w t ≤ b₂ * t ^ (k - 1)) :
    b₁ * r ^ k / k ≤ (∫ t in (0:ℝ)..r, w t)
      ∧ (∫ t in (0:ℝ)..r, w t) ≤ b₂ * r ^ k / k := by
  have hpoly : ∀ b : ℝ,
      (∫ t in (0:ℝ)..r, b * t ^ (k - 1)) = b * r ^ k / k := by
    intro b
    rw [intervalIntegral.integral_const_mul, integral_pow,
      show k - 1 + 1 = k from by omega,
      zero_pow (by omega : k ≠ 0), sub_zero]
    have hdenc : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
      push_cast [Nat.cast_sub (show 1 ≤ k by omega)]
      ring
    rw [hdenc, mul_div_assoc]
  have hcont : ∀ b : ℝ, IntervalIntegrable
      (fun t : ℝ => b * t ^ (k - 1)) MeasureTheory.volume 0 r :=
    fun b => (continuous_const.mul (continuous_pow _)).intervalIntegrable 0 r
  constructor
  · rw [← hpoly b₁]
    exact intervalIntegral.integral_mono_on hr (hcont b₁) hw_int hwlow
  · rw [← hpoly b₂]
    exact intervalIntegral.integral_mono_on hr hw_int (hcont b₂) hwup

end GeneralKTube

end DeadDirections
