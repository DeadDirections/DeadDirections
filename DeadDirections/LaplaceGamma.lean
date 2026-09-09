/-
  Reciprocal moments through the Laplace representation, and the
  Gamma law.

  The LayerNorm finite-t theorem rests on two finiteness facts about
  σ₀², the variance statistic of the non-dead channels. The second,
  E[1/σ₀²] < ∞ exactly at d ≥ 4, runs through the Laplace
  representation E[1/Y] = ∫₀^∞ E[e^{−uY}] du and the Gamma law that
  Cochran's theorem assigns to the pieces of σ₀². This module carries
  the measure-level content: the Gamma density tilts to a Gamma
  density at a shifted rate, so the Laplace transform of Gamma(a, r)
  is (r/(r+u))^a; the reciprocal moment of Gamma(a, r) is r/(a − 1)
  for a > 1, by reindexing the density through Γ(a) = (a−1)Γ(a−1);
  and for any positive random variable the Lebesgue integral of 1/Y
  is the Lebesgue integral of its Laplace transform over (0, ∞), by
  Tonelli. Cochran's law itself enters downstream as the hypothesis
  on σ₀²'s pieces.
-/
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Integration

namespace DeadDirections

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

section GammaLaw

/-- The Gamma density tilts to the Gamma density at the shifted rate. -/
lemma gammaPDFReal_mul_exp {a r u : ℝ} (hr : 0 < r) (hu : 0 ≤ u)
    (x : ℝ) :
    gammaPDFReal a r x * Real.exp (-(u * x))
      = (r / (r + u)) ^ a * gammaPDFReal a (r + u) x := by
  unfold gammaPDFReal
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, if_pos hx]
    have hru : 0 < r + u := by linarith
    have hpow : (r / (r + u)) ^ a * (r + u) ^ a = r ^ a := by
      rw [← Real.mul_rpow (div_nonneg hr.le hru.le) hru.le,
        div_mul_cancel₀ _ (ne_of_gt hru)]
    have hexp : Real.exp (-(r * x)) * Real.exp (-(u * x))
        = Real.exp (-((r + u) * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x))
          * Real.exp (-(u * x))
        = r ^ a / Real.Gamma a * x ^ (a - 1)
          * (Real.exp (-(r * x)) * Real.exp (-(u * x))) := by ring
      _ = ((r / (r + u)) ^ a * (r + u) ^ a) / Real.Gamma a * x ^ (a - 1)
          * Real.exp (-((r + u) * x)) := by rw [hpow, hexp]
      _ = (r / (r + u)) ^ a * ((r + u) ^ a / Real.Gamma a * x ^ (a - 1)
          * Real.exp (-((r + u) * x))) := by ring
  · rw [if_neg hx, if_neg hx]
    ring

/-- Almost every real is non-zero. -/
lemma ae_ne_zero_volume : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
  rw [ae_iff]
  have : {x : ℝ | ¬ x ≠ 0} = {0} := by
    ext x
    simp
  rw [this, Real.volume_singleton]

/-- The reciprocal reindexes the Gamma density one shape down. -/
lemma inv_mul_gammaPDFReal {a r : ℝ} (ha : 1 < a) (hr : 0 < r) {x : ℝ}
    (hx : x ≠ 0) :
    gammaPDFReal a r x * x⁻¹
      = (r / (a - 1)) * gammaPDFReal (a - 1) r x := by
  unfold gammaPDFReal
  by_cases hx0 : 0 ≤ x
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    rw [if_pos hx0, if_pos hx0]
    have ha1 : a - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt ha)
    have hG : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
      have := Real.Gamma_add_one ha1
      rwa [sub_add_cancel] at this
    have hr' : r ^ a = r ^ (a - 1) * r := by
      have := Real.rpow_add_one (ne_of_gt hr) (a - 1)
      rwa [sub_add_cancel] at this
    have hx' : x ^ (a - 1) = x ^ (a - 1 - 1) * x := by
      have := Real.rpow_add_one hx (a - 1 - 1)
      rwa [sub_add_cancel] at this
    have hG0 : Real.Gamma (a - 1) ≠ 0 :=
      ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
    rw [hG, hr', hx']
    field_simp
  · rw [if_neg hx0, if_neg hx0]
    ring

/-- The Gamma measure as a density written with nonnegative reals. -/
lemma gammaMeasure_eq_withDensity_toNNReal (a r : ℝ) :
    gammaMeasure a r
      = volume.withDensity
          (fun x => ((Real.toNNReal (gammaPDFReal a r x) : ℝ≥0) : ℝ≥0∞)) :=
  rfl

/-- Integration against the Gamma measure is integration against the
    density. -/
lemma integral_gammaMeasure_eq (a r : ℝ) (g : ℝ → ℝ) (ha : 0 < a)
    (hr : 0 < r) :
    ∫ x, g x ∂gammaMeasure a r = ∫ x, gammaPDFReal a r x * g x := by
  rw [gammaMeasure_eq_withDensity_toNNReal,
    integral_withDensity_eq_integral_smul
      ((measurable_gammaPDFReal a r).real_toNNReal)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (gammaPDFReal_nonneg ha hr x), smul_eq_mul]

/-- The Gamma density integrates to one (Bochner form). -/
lemma integral_gammaPDFReal {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ x, gammaPDFReal a r x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => gammaPDFReal_nonneg ha hr x)
    (measurable_gammaPDFReal a r).aestronglyMeasurable]
  have h := lintegral_gammaPDF_eq_one ha hr
  rw [show (fun x => ENNReal.ofReal (gammaPDFReal a r x)) = gammaPDF a r
    from rfl, h, ENNReal.toReal_one]

/-- The Laplace transform of Gamma(a, r): E[e^{−uY}] = (r/(r+u))^a. -/
theorem integral_exp_neg_mul_gammaMeasure {a r : ℝ} (ha : 0 < a)
    (hr : 0 < r) {u : ℝ} (hu : 0 ≤ u) :
    ∫ x, Real.exp (-(u * x)) ∂gammaMeasure a r = (r / (r + u)) ^ a := by
  have hru : 0 < r + u := by linarith
  rw [integral_gammaMeasure_eq a r _ ha hr]
  simp_rw [gammaPDFReal_mul_exp hr hu]
  rw [integral_const_mul, integral_gammaPDFReal ha hru, mul_one]

/-- The reciprocal moment of Gamma(a, r): E[1/Y] = r/(a − 1) for
    a > 1. -/
theorem integral_inv_gammaMeasure {a r : ℝ} (ha : 1 < a) (hr : 0 < r) :
    ∫ x, x⁻¹ ∂gammaMeasure a r = r / (a - 1) := by
  rw [integral_gammaMeasure_eq a r _ (by linarith) hr]
  have hcongr : (fun x : ℝ => gammaPDFReal a r x * x⁻¹)
      =ᵐ[volume] fun x => (r / (a - 1)) * gammaPDFReal (a - 1) r x := by
    filter_upwards [ae_ne_zero_volume] with x hx
    exact inv_mul_gammaPDFReal ha hr hx
  rw [integral_congr_ae hcongr, integral_const_mul,
    integral_gammaPDFReal (by linarith) hr, mul_one]

end GammaLaw

section LaplaceRepresentation

variable {Ω : Type*} [MeasurableSpace Ω]

/-- ∫₀^∞ e^{−uy} du = 1/y for y > 0, in Lebesgue form. -/
lemma lintegral_exp_neg_mul_Ioi {y : ℝ} (hy : 0 < y) :
    ∫⁻ u in Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-(u * y)))
      = ENNReal.ofReal y⁻¹ := by
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-(u * y))) (Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi (0:ℝ) hy).congr_fun
      (fun u _ => ?_) measurableSet_Ioi
    show Real.exp (-y * u) = Real.exp (-(u * y))
    ring_nf
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)]
  congr 1
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) 0 hy
  simp only [mul_zero] at h
  rw [integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  show Real.exp (-(u * y)) = Real.exp (-(y * u))
  ring_nf

/-- The Laplace representation of the reciprocal moment: for a
    positive random variable, ∫ 1/Y = ∫₀^∞ E[e^{−uY}] du in Lebesgue
    form, so the two sides are finite together. -/
theorem lintegral_inv_eq_lintegral_laplace (μ : Measure Ω) [SFinite μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (hpos : ∀ ω, 0 < Y ω) :
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
  refine lintegral_congr fun ω => ?_
  exact (lintegral_exp_neg_mul_Ioi (hpos ω)).symm

end LaplaceRepresentation

section ProductCriterion

/-- On u ≥ 1 the factor 1 + κu sits between min(1,κ)·u and
    2·max(1,κ)·u. -/
lemma one_add_mul_bounds {κ u : ℝ} (hκ : 0 < κ) (hu : 1 ≤ u) :
    min 1 κ * u ≤ 1 + κ * u ∧ 1 + κ * u ≤ 2 * max 1 κ * u := by
  constructor
  · have h1 : min 1 κ ≤ κ := min_le_right _ _
    have h2 : 0 ≤ min 1 κ := le_min zero_le_one hκ.le
    nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ u)]
  · have h1 : 1 ≤ max 1 κ := le_max_left _ _
    have h2 : κ ≤ max 1 κ := le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_right h2 (by linarith : (0:ℝ) ≤ u),
      mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ u)]

/-- The product Laplace integrand of two Gamma pieces,
    (1+κ₁u)^{−a₁}(1+κ₂u)^{−a₂}, is integrable on (0, ∞) exactly when
    the shapes sum above one: the d ≥ 4 criterion in its analytic
    form. -/
theorem laplace_product_integrableOn_iff {a₁ a₂ κ₁ κ₂ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) :
    IntegrableOn
      (fun u : ℝ => (1 + κ₁ * u) ^ (-a₁) * (1 + κ₂ * u) ^ (-a₂))
      (Ioi (0:ℝ))
    ↔ 1 < a₁ + a₂ := by
  set f : ℝ → ℝ := fun u => (1 + κ₁ * u) ^ (-a₁) * (1 + κ₂ * u) ^ (-a₂)
    with hf
  have hfnn : ∀ u, 0 ≤ u → 0 ≤ f u := fun u hu => by
    simp only [hf]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)
  have hfcont : ContinuousOn f (Ioi 0) := by
    simp only [hf]
    apply ContinuousOn.mul
    · refine ContinuousOn.rpow_const (by fun_prop) fun u hu => Or.inl ?_
      have : (0:ℝ) < u := hu
      positivity
    · refine ContinuousOn.rpow_const (by fun_prop) fun u hu => Or.inl ?_
      have : (0:ℝ) < u := hu
      positivity
  -- the two-sided comparison on u ≥ 1
  set Cl : ℝ := (2 * max 1 κ₁) ^ (-a₁) * (2 * max 1 κ₂) ^ (-a₂) with hCl
  set Cu : ℝ := (min 1 κ₁) ^ (-a₁) * (min 1 κ₂) ^ (-a₂) with hCu
  have hCl0 : 0 < Cl := by
    simp only [hCl]
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_pos_of_pos (by positivity) _)
  have hCu0 : 0 < Cu := by
    simp only [hCu]
    exact mul_pos (Real.rpow_pos_of_pos (lt_min one_pos hκ₁) _)
      (Real.rpow_pos_of_pos (lt_min one_pos hκ₂) _)
  have hlow : ∀ u, 1 ≤ u → Cl * u ^ (-(a₁ + a₂)) ≤ f u := by
    intro u hu
    have hu0 : 0 < u := by linarith
    obtain ⟨-, h1⟩ := one_add_mul_bounds hκ₁ hu
    obtain ⟨-, h2⟩ := one_add_mul_bounds hκ₂ hu
    have e1 : (2 * max 1 κ₁ * u) ^ (-a₁) ≤ (1 + κ₁ * u) ^ (-a₁) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
    have e2 : (2 * max 1 κ₂ * u) ^ (-a₂) ≤ (1 + κ₂ * u) ^ (-a₂) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
    have hsplit : Cl * u ^ (-(a₁ + a₂))
        = (2 * max 1 κ₁ * u) ^ (-a₁) * (2 * max 1 κ₂ * u) ^ (-a₂) := by
      simp only [hCl]
      rw [Real.mul_rpow (by positivity) hu0.le,
        Real.mul_rpow (by positivity) hu0.le,
        show -(a₁ + a₂) = -a₁ + -a₂ by ring, Real.rpow_add hu0]
      ring
    rw [hsplit]
    simp only [hf]
    exact mul_le_mul e1 e2 (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)
  have hupp : ∀ u, 1 ≤ u → f u ≤ Cu * u ^ (-(a₁ + a₂)) := by
    intro u hu
    have hu0 : 0 < u := by linarith
    obtain ⟨h1, -⟩ := one_add_mul_bounds hκ₁ hu
    obtain ⟨h2, -⟩ := one_add_mul_bounds hκ₂ hu
    have hm1 : 0 < min 1 κ₁ := lt_min one_pos hκ₁
    have hm2 : 0 < min 1 κ₂ := lt_min one_pos hκ₂
    have e1 : (1 + κ₁ * u) ^ (-a₁) ≤ (min 1 κ₁ * u) ^ (-a₁) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
    have e2 : (1 + κ₂ * u) ^ (-a₂) ≤ (min 1 κ₂ * u) ^ (-a₂) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
    have hsplit : Cu * u ^ (-(a₁ + a₂))
        = (min 1 κ₁ * u) ^ (-a₁) * (min 1 κ₂ * u) ^ (-a₂) := by
      simp only [hCu]
      rw [Real.mul_rpow hm1.le hu0.le, Real.mul_rpow hm2.le hu0.le,
        show -(a₁ + a₂) = -a₁ + -a₂ by ring, Real.rpow_add hu0]
      ring
    rw [hsplit]
    simp only [hf]
    exact mul_le_mul e1 e2 (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)
  have hsplitset : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext u
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro h
      by_cases h1 : u ≤ 1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (lt_of_not_ge h1)
    · rintro (⟨h, -⟩ | h)
      · exact h
      · linarith
  have hbdd : IntegrableOn f (Ioc 0 1) := by
    have hc : ContinuousOn f (Icc 0 1) := by
      simp only [hf]
      apply ContinuousOn.mul
      · refine ContinuousOn.rpow_const (by fun_prop) fun u hu => Or.inl ?_
        have : (0:ℝ) ≤ u := hu.1
        positivity
      · refine ContinuousOn.rpow_const (by fun_prop) fun u hu => Or.inl ?_
        have : (0:ℝ) ≤ u := hu.1
        positivity
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioi 1)) :=
    (hfcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi
  constructor
  · intro hint
    have htail : IntegrableOn f (Ioi 1) :=
      hint.mono_set (Ioi_subset_Ioi zero_le_one)
    have hpow : IntegrableOn (fun u : ℝ => Cl * u ^ (-(a₁ + a₂))) (Ioi 1) := by
      refine Integrable.mono' htail ?_ ?_
      · exact ((continuousOn_id.rpow_const fun u hu => Or.inl
          (ne_of_gt (lt_trans zero_lt_one hu))).const_smul Cl
          |>.aestronglyMeasurable measurableSet_Ioi)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu1 : 1 ≤ u := le_of_lt hu
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg hCl0.le (Real.rpow_nonneg (by linarith) _))]
        exact hlow u hu1
    have h2 : IntegrableOn (fun u : ℝ => u ^ (-(a₁ + a₂))) (Ioi 1) := by
      have h' : IntegrableOn (fun u : ℝ => Cl⁻¹ * (Cl * u ^ (-(a₁ + a₂)))) (Ioi 1) :=
        hpow.const_mul Cl⁻¹
      refine h'.congr_fun (fun u _ => ?_) measurableSet_Ioi
      show Cl⁻¹ * (Cl * u ^ (-(a₁ + a₂))) = u ^ (-(a₁ + a₂))
      field_simp
    have := (integrableOn_Ioi_rpow_iff zero_lt_one).mp h2
    linarith
  · intro hsum
    have h2 : IntegrableOn (fun u : ℝ => u ^ (-(a₁ + a₂))) (Ioi 1) :=
      (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by linarith)
    have htail : IntegrableOn f (Ioi 1) := by
      refine Integrable.mono' (h2.const_mul Cu) hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu1 : 1 ≤ u := le_of_lt hu
      rw [Real.norm_eq_abs, abs_of_nonneg (hfnn u (by linarith))]
      exact hupp u hu1
    rw [hsplitset]
    exact hbdd.union htail

/-- The d ≥ 4 sharpness: with the Cochran shapes (d−2)/2 and 1/2 the
    criterion reads d ≥ 4. -/
theorem ln_sigma0_shape_criterion (d : ℕ) :
    (1:ℝ) < ((d:ℝ) - 2) / 2 + 1 / 2 ↔ 4 ≤ d := by
  constructor
  · intro h
    have : (3:ℝ) < d := by linarith
    exact_mod_cast this
  · intro h
    have : (4:ℝ) ≤ d := by exact_mod_cast h
    linarith

end ProductCriterion

section GammaPair

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The Laplace transform of an independent Gamma pair: with S and X
    independent, S ∼ Gamma(a₁, r₁) and X ∼ Gamma(a₂, r₂), the Laplace
    transform of αS + βX factors into the two Gamma transforms. -/
theorem laplace_indep_gamma_pair {S X : Ω → ℝ} (hSm : Measurable S)
    (hXm : Measurable X) (hind : S ⟂ᵢ[μ] X)
    {a₁ r₁ a₂ r₂ : ℝ} (ha₁ : 0 < a₁) (hr₁ : 0 < r₁) (ha₂ : 0 < a₂)
    (hr₂ : 0 < r₂)
    (hS : μ.map S = gammaMeasure a₁ r₁) (hX : μ.map X = gammaMeasure a₂ r₂)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) {u : ℝ} (hu : 0 ≤ u) :
    ∫ ω, Real.exp (-(u * (α * S ω + β * X ω))) ∂μ
      = (r₁ / (r₁ + u * α)) ^ a₁ * (r₂ / (r₂ + u * β)) ^ a₂ := by
  have hsplit : ∀ ω, Real.exp (-(u * (α * S ω + β * X ω)))
      = Real.exp (-(u * α * S ω)) * Real.exp (-(u * β * X ω)) := by
    intro ω
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hsplit]
  have hf : AEStronglyMeasurable (fun s : ℝ => Real.exp (-(u * α * s)))
      (μ.map S) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)
      |>.aestronglyMeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => Real.exp (-(u * β * x)))
      (μ.map X) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)
      |>.aestronglyMeasurable
  rw [hind.integral_fun_comp_mul_comp hSm.aemeasurable hXm.aemeasurable hf hg,
    ← integral_map hSm.aemeasurable hf, ← integral_map hXm.aemeasurable hg,
    hS, hX,
    integral_exp_neg_mul_gammaMeasure ha₁ hr₁ (mul_nonneg hu hα),
    integral_exp_neg_mul_gammaMeasure ha₂ hr₂ (mul_nonneg hu hβ)]

/-- The Gamma Laplace factor in the (1 + κu)^{−a} form. -/
lemma gamma_laplace_factor_eq {r a α u : ℝ} (hr : 0 < r) (hα : 0 ≤ α)
    (hu : 0 ≤ u) :
    (r / (r + u * α)) ^ a = (1 + (α / r) * u) ^ (-a) := by
  have hpos : 0 < 1 + (α / r) * u := by positivity
  have heq : r / (r + u * α) = (1 + (α / r) * u)⁻¹ := by
    field_simp
  rw [heq, Real.inv_rpow hpos.le, Real.rpow_neg hpos.le]

/-- The reciprocal moment of an independent Gamma pair is finite
    exactly when the shapes sum above one: with the Cochran shapes
    this is the d ≥ 4 sharpness of thm:ln_finite_t_mlp. -/
theorem inv_moment_gamma_pair_lt_top_iff [IsProbabilityMeasure μ]
    {S X : Ω → ℝ} (hSm : Measurable S) (hXm : Measurable X)
    (hind : S ⟂ᵢ[μ] X)
    {a₁ r₁ a₂ r₂ : ℝ} (ha₁ : 0 < a₁) (hr₁ : 0 < r₁) (ha₂ : 0 < a₂)
    (hr₂ : 0 < r₂)
    (hS : μ.map S = gammaMeasure a₁ r₁) (hX : μ.map X = gammaMeasure a₂ r₂)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hpos : ∀ ω, 0 < α * S ω + β * X ω) :
    (∫⁻ ω, ENNReal.ofReal (α * S ω + β * X ω)⁻¹ ∂μ) < ∞
      ↔ 1 < a₁ + a₂ := by
  have hYm : Measurable fun ω => α * S ω + β * X ω :=
    (hSm.const_mul α).add (hXm.const_mul β)
  rw [lintegral_inv_eq_lintegral_laplace μ _ hYm hpos]
  -- the inner integral is the product Laplace factor
  have hinner : ∀ u ∈ Ioi (0:ℝ),
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-(u * (α * S ω + β * X ω)))) ∂μ)
        = ENNReal.ofReal
            ((1 + (α / r₁) * u) ^ (-a₁) * (1 + (β / r₂) * u) ^ (-a₂)) := by
    intro u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    have hint : Integrable
        (fun ω => Real.exp (-(u * (α * S ω + β * X ω)))) μ := by
      refine Integrable.of_bound ?_ 1 ?_
      · exact (Real.continuous_exp.comp
          ((continuous_const.mul continuous_id).neg)).measurable
          |>.comp hYm |>.aestronglyMeasurable
      · filter_upwards [] with ω
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (by
          have := hpos ω
          nlinarith)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le),
      laplace_indep_gamma_pair hSm hXm hind ha₁ hr₁ ha₂ hr₂ hS hX hα.le hβ.le hu0,
      gamma_laplace_factor_eq hr₁ hα.le hu0, gamma_laplace_factor_eq hr₂ hβ.le hu0]
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner]
  set f : ℝ → ℝ := fun u => (1 + (α / r₁) * u) ^ (-a₁) * (1 + (β / r₂) * u) ^ (-a₂)
    with hf
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have : (0:ℝ) < u := hu
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioi (0:ℝ))) := by
    have hc : ContinuousOn f (Ioi 0) := by
      simp only [hf]
      apply ContinuousOn.mul
      · refine ContinuousOn.rpow_const (by fun_prop) fun u hu => Or.inl ?_
        have : (0:ℝ) < u := hu
        positivity
      · refine ContinuousOn.rpow_const (by fun_prop) fun u hu => Or.inl ?_
        have : (0:ℝ) < u := hu
        positivity
    exact hc.aestronglyMeasurable measurableSet_Ioi
  have hiff : (∫⁻ u in Ioi (0:ℝ), ENNReal.ofReal (f u)) < ∞
      ↔ IntegrableOn f (Ioi 0) := by
    rw [IntegrableOn, Integrable, and_iff_right hfm, hasFiniteIntegral_iff_ofReal hfnn]
  rw [hiff]
  exact laplace_product_integrableOn_iff ha₁ ha₂ (div_pos hα hr₁) (div_pos hβ hr₂)

end GammaPair

end DeadDirections
