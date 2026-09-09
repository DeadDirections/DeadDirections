/-
  Cochran's theorem for the LayerNorm statistic, and the d ≥ 4
  criterion with no hypothesis left.

  The finite-t theorem's finiteness fact E[1/σ₀²] < ∞ ⟺ d ≥ 4 rests
  on Cochran's theorem: under the isotropic Gaussian the mean and the
  centred sum of squares of the non-dead channels are independent
  with Gaussian and chi-square laws. The route here is the one behind
  Cochran's proof: rotate to an orthonormal basis whose first vector
  is 𝟙/√m; the isotropic Gaussian is the product Gaussian in any
  orthonormal coordinates, the mean reads the first coordinate and
  the centred sum of squares the remaining ones, and σ₀² becomes a
  weighted sum of squares of independent standard normals. Its
  Laplace transform is a product of one-dimensional Gaussian
  integrals, (1+2u/d)^{−(d−2)/2}(1+2u/d²)^{−1/2}, and the product
  criterion of LaplaceGamma reads d ≥ 4. Stage one, this file's first
  half, is the product-space statement; stage two carries the
  isotropic Gaussian onto it.
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import DeadDirections.LaplaceGamma

namespace DeadDirections

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

section GaussianLaplace

/-- Integration against the standard Gaussian is integration against
    its density. -/
lemma integral_gaussianReal_eq (g : ℝ → ℝ) :
    ∫ x, g x ∂gaussianReal 0 1 = ∫ x, gaussianPDFReal 0 1 x * g x := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    show gaussianPDF 0 1 = fun x => ((Real.toNNReal (gaussianPDFReal 0 1 x) : ℝ≥0) : ℝ≥0∞)
      from funext fun x => by rw [gaussianPDF_def]; rfl,
    integral_withDensity_eq_integral_smul (measurable_gaussianPDFReal 0 1).real_toNNReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (gaussianPDFReal_nonneg 0 1 x), smul_eq_mul]

/-- The Laplace transform of the square of a standard normal:
    E[e^{−u y²}] = 1/√(1 + 2u). -/
theorem integral_exp_neg_mul_sq_gaussianReal {u : ℝ} (hu : 0 ≤ u) :
    ∫ y, Real.exp (-(u * y ^ 2)) ∂gaussianReal 0 1
      = 1 / Real.sqrt (1 + 2 * u) := by
  rw [integral_gaussianReal_eq]
  have hfun : ∀ y : ℝ, gaussianPDFReal 0 1 y * Real.exp (-(u * y ^ 2))
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(u + 1 / 2) * y ^ 2) := by
    intro y
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [hfun]
  rw [integral_const_mul, integral_gaussian]
  have hpos : (0:ℝ) < u + 1 / 2 := by linarith
  rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),
    show (1 + 2 * u : ℝ) = 2 * (u + 1 / 2) by ring,
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
  have hh : Real.sqrt (u + 1 / 2) ≠ 0 := by positivity
  field_simp

/-- The Laplace transform of a weighted sum of squares of independent
    standard normals is the product of the one-dimensional
    transforms. -/
theorem laplace_weighted_sq_pi {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    {u : ℝ} (hu : 0 ≤ u) :
    ∫ y, Real.exp (-(u * ∑ i, c i * y i ^ 2))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
      = ∏ i, 1 / Real.sqrt (1 + 2 * (u * c i)) := by
  have hfun : ∀ y : Fin n → ℝ, Real.exp (-(u * ∑ i, c i * y i ^ 2))
      = ∏ i, Real.exp (-(u * c i * y i ^ 2)) := by
    intro y
    rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [hfun]
  rw [integral_fintype_prod_eq_prod (fun i (t : ℝ) => Real.exp (-(u * c i * t ^ 2)))]
  exact Finset.prod_congr rfl fun i _ =>
    integral_exp_neg_mul_sq_gaussianReal (mul_nonneg hu (hc i))

end GaussianLaplace

section LaplaceAE

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Laplace representation with almost-everywhere positivity. -/
theorem lintegral_inv_eq_lintegral_laplace_ae (μ : Measure Ω) [SFinite μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (hpos : ∀ᵐ ω ∂μ, 0 < Y ω) :
    ∫⁻ ω, ENNReal.ofReal (Y ω)⁻¹ ∂μ
      = ∫⁻ u in Ioi (0:ℝ),
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-(u * Y ω))) ∂μ := by
  have hmeas : AEMeasurable
      (Function.uncurry fun (u : ℝ) (ω : Ω) =>
        ENNReal.ofReal (Real.exp (-(u * Y ω))))
      ((volume.restrict (Ioi (0:ℝ))).prod μ) := by
    refine Measurable.aemeasurable ?_
    refine Measurable.ennreal_ofReal ?_
    exact Real.measurable_exp.comp
      ((measurable_fst.mul (hY.comp measurable_snd)).neg)
  rw [lintegral_lintegral_swap hmeas]
  refine lintegral_congr_ae ?_
  filter_upwards [hpos] with ω hω
  exact (lintegral_exp_neg_mul_Ioi hω).symm

end LaplaceAE

section ProductCriterion

/-- The standard Gaussian gives no mass to a point. -/
lemma gaussianReal_singleton (a : ℝ) : gaussianReal 0 1 {a} = 0 :=
  (gaussianReal_absolutelyContinuous 0 one_ne_zero) (Real.volume_singleton)

/-- The weighted sum of squares σ₀² in rotated coordinates:
    c₀·y₀² + c·Σ_{j} y_{j+1}². -/
def rotSigma (m' : ℕ) (c₀ c : ℝ) (y : Fin (m'+1) → ℝ) : ℝ :=
  c₀ * y 0 ^ 2 + c * ∑ j : Fin m', y j.succ ^ 2

lemma rotSigma_eq_sum (m' : ℕ) (c₀ c : ℝ) (y : Fin (m'+1) → ℝ) :
    rotSigma m' c₀ c y = ∑ i, (Fin.cons c₀ (fun _ => c) : Fin (m'+1) → ℝ) i * y i ^ 2 := by
  rw [rotSigma, Fin.sum_univ_succ, Fin.cons_zero, Finset.mul_sum]
  congr 1

lemma measurable_rotSigma (m' : ℕ) (c₀ c : ℝ) : Measurable (rotSigma m' c₀ c) := by
  unfold rotSigma
  fun_prop

/-- Almost every rotated coordinate vector gives σ₀² > 0. -/
lemma rotSigma_pos_ae (m' : ℕ) {c₀ c : ℝ} (hc₀ : 0 < c₀) (hc : 0 ≤ c) :
    ∀ᵐ y ∂(Measure.pi fun _ : Fin (m'+1) => gaussianReal 0 1),
      0 < rotSigma m' c₀ c y := by
  have hnull : (Measure.pi fun _ : Fin (m'+1) => gaussianReal 0 1)
      {y : Fin (m'+1) → ℝ | y 0 = 0} = 0 := by
    have hset : {y : Fin (m'+1) → ℝ | y 0 = 0}
        = Set.pi univ (fun i => if i = 0 then ({0} : Set ℝ) else univ) := by
      ext y
      simp only [mem_setOf_eq, Set.mem_pi, mem_univ, forall_const]
      constructor
      · intro h i
        by_cases hi : i = 0
        · subst hi; simp [h]
        · simp [hi]
      · intro h
        have := h 0
        simpa using this
    rw [hset, Measure.pi_pi]
    refine Finset.prod_eq_zero (Finset.mem_univ 0) ?_
    simp [gaussianReal_singleton]
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) hnull
  simp only [mem_setOf_eq] at hy ⊢
  push Not at hy
  have hsum : 0 ≤ c * ∑ j : Fin m', y j.succ ^ 2 :=
    mul_nonneg hc (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have h0 : c₀ * y 0 ^ 2 ≤ 0 := by
    unfold rotSigma at hy
    linarith
  have := mul_nonneg hc₀.le (sq_nonneg (y 0))
  have hsq : y 0 ^ 2 = 0 := by nlinarith
  exact pow_eq_zero_iff two_ne_zero |>.mp hsq

/-- The reciprocal moment of σ₀² in rotated coordinates is finite
    exactly when m' ≥ 2, that is d = m' + 2 ≥ 4: the criterion of
    thm:ln_finite_t_mlp with the Gamma laws derived rather than
    assumed. -/
theorem inv_moment_rotSigma_lt_top_iff {m' : ℕ} (hm : 1 ≤ m') {c₀ c : ℝ}
    (hc₀ : 0 < c₀) (hc : 0 < c) :
    (∫⁻ y, ENNReal.ofReal (rotSigma m' c₀ c y)⁻¹
        ∂(Measure.pi fun _ : Fin (m'+1) => gaussianReal 0 1)) < ⊤
      ↔ 2 ≤ m' := by
  set μ := Measure.pi fun _ : Fin (m'+1) => gaussianReal 0 1 with hμ
  haveI : IsProbabilityMeasure μ := by
    rw [hμ]; infer_instance
  rw [lintegral_inv_eq_lintegral_laplace_ae μ _ (measurable_rotSigma m' c₀ c)
    (rotSigma_pos_ae m' hc₀ hc.le)]
  set a₁ : ℝ := 1 / 2 with ha₁
  set a₂ : ℝ := (m' : ℝ) / 2 with ha₂
  set κ₁ : ℝ := 2 * c₀ with hκ₁
  set κ₂ : ℝ := 2 * c with hκ₂
  have hinner : ∀ u ∈ Ioi (0:ℝ),
      (∫⁻ y, ENNReal.ofReal (Real.exp (-(u * rotSigma m' c₀ c y))) ∂μ)
        = ENNReal.ofReal ((1 + κ₁ * u) ^ (-a₁) * (1 + κ₂ * u) ^ (-a₂)) := by
    intro u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    have hint : Integrable (fun y => Real.exp (-(u * rotSigma m' c₀ c y))) μ := by
      refine Integrable.of_bound ?_ 1 ?_
      · exact (Real.measurable_exp.comp
          ((measurable_rotSigma m' c₀ c).const_mul u).neg).aestronglyMeasurable
      · filter_upwards [rotSigma_pos_ae m' hc₀ hc.le] with y hy
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (by nlinarith)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)]
    congr 1
    have hc' : ∀ i, 0 ≤ (Fin.cons c₀ (fun _ => c) : Fin (m'+1) → ℝ) i := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero]; exact hc₀.le
      · rw [Fin.cons_succ]; exact hc.le
    simp_rw [rotSigma_eq_sum]
    rw [laplace_weighted_sq_pi _ hc' hu0, Fin.prod_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    -- convert the square roots to the rpow form
    have hx1 : 0 < 1 + 2 * (u * c₀) := by positivity
    have hx2 : 0 < 1 + 2 * (u * c) := by positivity
    have e1 : 1 / Real.sqrt (1 + 2 * (u * c₀)) = (1 + κ₁ * u) ^ (-a₁) := by
      rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hx1.le, hκ₁, ha₁]
      congr 1
      ring
    have e2 : (1 / Real.sqrt (1 + 2 * (u * c))) ^ m' = (1 + κ₂ * u) ^ (-a₂) := by
      rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hx2.le,
        ← Real.rpow_natCast, ← Real.rpow_mul hx2.le, hκ₂, ha₂]
      congr 1
      · ring
      · ring
    rw [e1, e2]
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner]
  set f : ℝ → ℝ := fun u => (1 + κ₁ * u) ^ (-a₁) * (1 + κ₂ * u) ^ (-a₂) with hf
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have : (0:ℝ) < u := hu
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioi (0:ℝ))) := by
    have hcont : ContinuousOn f (Ioi 0) := by
      simp only [hf]
      apply ContinuousOn.mul
      · refine ContinuousOn.rpow_const (by fun_prop) fun u hu => Or.inl ?_
        have : (0:ℝ) < u := hu
        positivity
      · refine ContinuousOn.rpow_const (by fun_prop) fun u hu => Or.inl ?_
        have : (0:ℝ) < u := hu
        positivity
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hiff : (∫⁻ u in Ioi (0:ℝ), ENNReal.ofReal (f u)) < ⊤
      ↔ IntegrableOn f (Ioi 0) := by
    rw [IntegrableOn, Integrable, and_iff_right hfm, hasFiniteIntegral_iff_ofReal hfnn]
  rw [hiff, laplace_product_integrableOn_iff (by norm_num)
    (by rw [ha₂]; have h1 : (0:ℝ) < m' := (by exact_mod_cast hm); positivity)
    (by rw [hκ₁]; positivity) (by rw [hκ₂]; positivity), ha₁, ha₂]
  constructor
  · intro h
    have : (1:ℝ) < m' := by linarith
    exact_mod_cast this
  · intro h
    have : (2:ℝ) ≤ m' := by exact_mod_cast h
    linarith

end ProductCriterion

section Rotation

variable {m' : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (m'+1))

/-- The LayerNorm variance statistic of the non-dead channels,
    σ₀² = ‖x‖²/d − (Σᵢxᵢ)²/d² with d = m + 1 channels in all. -/
noncomputable def sigma0 (m' : ℕ) (x : EuclideanSpace ℝ (Fin (m'+1))) : ℝ :=
  ‖x‖ ^ 2 / ((m':ℝ) + 2) - (∑ i, x i) ^ 2 / ((m':ℝ) + 2) ^ 2

/-- The paper's form of σ₀²: with m = d − 1 non-dead channels,
    x̄ = Σx/m and s² = (‖x‖² − m x̄²)/m,
    ((d−1)/d)·s² + ((d−1)/d²)·x̄² = ‖x‖²/d − (Σx)²/d². -/
lemma sigma0_eq_paper_form (x : EuclideanSpace ℝ (Fin (m'+1))) :
    sigma0 m' x
      = (((m':ℝ) + 1) / ((m':ℝ) + 2))
          * ((‖x‖ ^ 2 - ((m':ℝ) + 1) * ((∑ i, x i) / ((m':ℝ) + 1)) ^ 2)
              / ((m':ℝ) + 1))
        + (((m':ℝ) + 1) / ((m':ℝ) + 2) ^ 2) * ((∑ i, x i) / ((m':ℝ) + 1)) ^ 2 := by
  unfold sigma0
  have h1 : ((m':ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((m':ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- The constant vector 𝟙 and its unit multiple w = 𝟙/√m. -/
noncomputable def onesVec (m' : ℕ) : EuclideanSpace ℝ (Fin (m'+1)) :=
  WithLp.toLp 2 (fun _ => (1:ℝ))

noncomputable def unitOnes (m' : ℕ) : EuclideanSpace ℝ (Fin (m'+1)) :=
  (1 / Real.sqrt ((m':ℝ) + 1)) • onesVec m'

lemma norm_onesVec : ‖onesVec m'‖ = Real.sqrt ((m':ℝ) + 1) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [onesVec]

lemma norm_unitOnes : ‖unitOnes m'‖ = 1 := by
  rw [unitOnes, norm_smul, norm_onesVec, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  field_simp

/-- The pairing of any vector with 𝟙 is its coordinate sum. -/
lemma inner_onesVec (x : EuclideanSpace ℝ (Fin (m'+1))) :
    inner ℝ (onesVec m') x = ∑ i, x i := by
  simp [onesVec, PiLp.inner_apply, real_inner_eq_re_inner]

lemma inner_unitOnes (x : EuclideanSpace ℝ (Fin (m'+1))) :
    inner ℝ (unitOnes m') x = (∑ i, x i) / Real.sqrt ((m':ℝ) + 1) := by
  rw [unitOnes, inner_smul_left, inner_onesVec]
  simp [div_eq_inv_mul]

/-- The rotation sending the first basis vector to 𝟙/√m. -/
noncomputable def rotIso (m' : ℕ) :
    EuclideanSpace ℝ (Fin (m'+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m'+1)) :=
  Submodule.reflection
    (ℝ ∙ (EuclideanSpace.basisFun (Fin (m'+1)) ℝ 0 - unitOnes m'))ᗮ

/-- The orthonormal basis adapted to the mean direction. -/
noncomputable def rotBasis (m' : ℕ) :
    OrthonormalBasis (Fin (m'+1)) ℝ (EuclideanSpace ℝ (Fin (m'+1))) :=
  (EuclideanSpace.basisFun (Fin (m'+1)) ℝ).map (rotIso m')

lemma rotBasis_zero : rotBasis m' 0 = unitOnes m' := by
  rw [rotBasis, OrthonormalBasis.map_apply, rotIso]
  apply Submodule.reflection_sub
  rw [norm_unitOnes]
  exact (EuclideanSpace.basisFun (Fin (m'+1)) ℝ).orthonormal.1 0

/-- Cochran's rotation: in the adapted coordinates σ₀² is the
    weighted sum of squares c₀·y₀² + c·Σ y_{j+1}² with c₀ = 1/d² and
    c = 1/d. -/
theorem sigma0_eq_rotSigma (x : EuclideanSpace ℝ (Fin (m'+1))) :
    sigma0 m' x
      = rotSigma m' (1 / ((m':ℝ) + 2) ^ 2) (1 / ((m':ℝ) + 2))
          (fun i => inner ℝ (rotBasis m' i) x) := by
  have hpar : ‖x‖ ^ 2 = ∑ i, inner ℝ (rotBasis m' i) x ^ 2 :=
    ((rotBasis m').sum_sq_inner_right x).symm
  have hsum : ∑ i, x i = Real.sqrt ((m':ℝ) + 1) * inner ℝ (rotBasis m' 0) x := by
    rw [rotBasis_zero, inner_unitOnes]
    have : Real.sqrt ((m':ℝ) + 1) ≠ 0 := by positivity
    field_simp
  unfold sigma0 rotSigma
  rw [hpar, hsum, Fin.sum_univ_succ, mul_pow, Real.sq_sqrt (by positivity)]
  have h2 : ((m':ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- The rotated coordinates of Σ yᵢ·bᵢ are y. -/
lemma inner_rotBasis_sum (y : Fin (m'+1) → ℝ) (i : Fin (m'+1)) :
    inner ℝ (rotBasis m' i) (∑ j, y j • rotBasis m' j) = y i := by
  have h := (rotBasis m').sum_repr_symm (WithLp.toLp 2 y)
  rw [h, ← OrthonormalBasis.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]

/-- Cochran's theorem for the LayerNorm statistic, the finiteness
    criterion with no hypothesis left: under the isotropic Gaussian on
    the d − 1 = m' + 1 non-dead channels, E[1/σ₀²] is finite exactly
    when d ≥ 4. -/
theorem ln_sigma0_inv_moment_lt_top_iff (hm : 1 ≤ m') :
    (∫⁻ x, ENNReal.ofReal (sigma0 m' x)⁻¹
        ∂stdGaussian (EuclideanSpace ℝ (Fin (m'+1)))) < ⊤
      ↔ 4 ≤ m' + 2 := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis (rotBasis m')]
  have hmeas : Measurable fun x : EuclideanSpace ℝ (Fin (m'+1)) =>
      ENNReal.ofReal (sigma0 m' x)⁻¹ := by
    apply Measurable.ennreal_ofReal
    apply Measurable.inv
    unfold sigma0
    fun_prop
  have hmap : Measurable fun y : Fin (m'+1) → ℝ => ∑ j, y j • rotBasis m' j := by
    fun_prop
  rw [lintegral_map hmeas hmap]
  have hpt : ∀ y : Fin (m'+1) → ℝ,
      sigma0 m' (∑ j, y j • rotBasis m' j)
        = rotSigma m' (1 / ((m':ℝ) + 2) ^ 2) (1 / ((m':ℝ) + 2)) y := by
    intro y
    rw [sigma0_eq_rotSigma]
    congr 1
    funext i
    exact inner_rotBasis_sum y i
  simp_rw [hpt]
  rw [inv_moment_rotSigma_lt_top_iff hm (by positivity) (by positivity)]
  omega

end Rotation

end DeadDirections
