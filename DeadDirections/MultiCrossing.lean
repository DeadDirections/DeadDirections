/-
  Multi-component normal crossing, tied orders (theory paper,
  thm:multi_component_rates territory; Watanabe's multiplicity).

  For the 2-component crossing K(x, y) = (x·y)^{2k} with TIED orders,
  the sublevel volume on the open unit square is exact:

    vol{(x,y) ∈ (0,1)² : (xy)^{2k} < ε}
      = ε^{1/(2k)} · (1 − log ε/(2k)),   0 < ε < 1.

  The log factor is Watanabe's multiplicity m = 2 appearing in volume
  form: two components tie for the minimal 1/(2kᵢ), and the volume law
  picks up one power of log(1/ε) per extra tied component. The proof
  reduces to the hyperbola area vol{xy < δ} = δ(1 − log δ) at
  δ = ε^{1/(2k)}: slice the square at x = δ, integrate 1 on the left
  and δ/x on the right. No resolution of singularities.

  Next in this file's scope: the distinct-order case k₁ ≠ k₂, where
  the same slicing gives (a·ε^{1/a} − b·ε^{1/b})/(a − b) with
  a = 2k₁, b = 2k₂ and no log factor, and the slope corollaries.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import DeadDirections.SliceRlct

namespace DeadDirections

open MeasureTheory Set Real Filter Topology

/-- The hyperbola sublevel set on the open unit square is the region
    under the graph of min(1, δ/x). -/
lemma hyperbola_eq_regionBetween (δ : ℝ) :
    {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1 ∧ p.1 * p.2 < δ}
      = regionBetween (fun _ => 0) (fun x => min 1 (δ / x)) (Ioo 0 1) := by
  ext ⟨x, y⟩
  simp only [regionBetween, mem_setOf_eq, mem_Ioo]
  constructor
  · rintro ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, hxy⟩
    refine ⟨⟨hx0, hx1⟩, hy0, lt_min hy1 ?_⟩
    rw [lt_div_iff₀ hx0, mul_comm]
    exact hxy
  · rintro ⟨⟨hx0, hx1⟩, hy0, hym⟩
    refine ⟨⟨hx0, hx1⟩, ⟨hy0, lt_of_lt_of_le hym (min_le_left _ _)⟩, ?_⟩
    have hyd : y < δ / x := lt_of_lt_of_le hym (min_le_right _ _)
    rw [lt_div_iff₀ hx0, mul_comm] at hyd
    exact hyd

/-- The slice profile is integrable on (0, 1]. -/
lemma integrableOn_min_one_div {δ : ℝ} (h0 : 0 < δ) :
    IntegrableOn (fun x : ℝ => min 1 (δ / x)) (Ioc 0 1) := by
  have hmeas : Measurable fun x : ℝ => min 1 (δ / x) :=
    measurable_const.min (measurable_const.div measurable_id)
  refine Integrable.mono'
    (integrableOn_const (C := (1:ℝ)) (μ := volume) (s := Ioc 0 1) ?_)
    hmeas.aestronglyMeasurable.restrict ?_
  · rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg
      (le_min (by norm_num) (div_nonneg h0.le hx0.le))]
    exact min_le_left _ _

/-- The sliced integral: ∫₀¹ min(1, δ/x) = δ(1 − log δ). -/
lemma integral_min_one_div {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    ∫ x in Ioo (0:ℝ) 1, min 1 (δ / x) = δ * (1 - Real.log δ) := by
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
    show Ioc (0:ℝ) 1 = Ioc 0 δ ∪ Ioc δ 1 from
      (Ioc_union_Ioc_eq_Ioc h0.le h1.le).symm,
    setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl)
      measurableSet_Ioc
      ((integrableOn_min_one_div h0).mono_set
        (Ioc_subset_Ioc_right h1.le))
      ((integrableOn_min_one_div h0).mono_set
        (Ioc_subset_Ioc_left h0.le))]
  have hleft : ∫ x in Ioc (0:ℝ) δ, min 1 (δ / x) = δ := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (fun x hx => min_eq_left ((le_div_iff₀ hx.1).mpr (by
        rw [one_mul]; exact hx.2)))]
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
      Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    linarith
  have hright : ∫ x in Ioc δ 1, min 1 (δ / x) = -(δ * Real.log δ) := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (fun x hx => min_eq_right ((div_le_one (lt_of_lt_of_le h0 hx.1.le)).mpr
        hx.1.le))]
    rw [← intervalIntegral.integral_of_le h1.le]
    have hfun : ∀ x : ℝ, δ / x = δ * x⁻¹ := fun x => div_eq_mul_inv δ x
    simp only [hfun]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos h0 one_pos,
      Real.log_div one_ne_zero (ne_of_gt h0), Real.log_one]
    ring
  rw [hleft, hright]
  ring

/-- Exact hyperbola area: vol{(x,y) ∈ (0,1)² : xy < δ} = δ(1 − log δ). -/
theorem volume_hyperbola {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    (volume : Measure ℝ).prod volume
        {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1 ∧ p.1 * p.2 < δ}
      = ENNReal.ofReal (δ * (1 - Real.log δ)) := by
  rw [hyperbola_eq_regionBetween δ,
    volume_regionBetween_eq_integral
      (integrable_zero _ _ _).integrableOn
      ((integrableOn_min_one_div h0).mono_set Ioo_subset_Ioc_self)
      measurableSet_Ioo
      (fun x hx => le_min (by norm_num) (div_nonneg h0.le hx.1.le))]
  rw [show ((fun x => min 1 (δ / x)) - fun _ => (0:ℝ))
      = fun x => min 1 (δ / x) from by funext x; simp]
  rw [integral_min_one_div h0 h1]

/-- On nonnegative reals, the 2k-th power sublevel condition converts
    to the rpow root. -/
lemma pow_lt_iff_lt_rpow {k : ℕ} (hk : 1 ≤ k) {z ε : ℝ}
    (hz : 0 ≤ z) (hε : 0 < ε) :
    z ^ (2 * k) < ε ↔ z < ε ^ ((1:ℝ)/(2 * k)) := by
  have h2k : (2 * k : ℕ) ≠ 0 := by omega
  have hr : (ε ^ ((1:ℝ)/(2 * k))) ^ (2 * k : ℕ) = ε := by
    rw [← Real.rpow_natCast (ε ^ ((1:ℝ)/(2 * k))) (2 * k),
      ← Real.rpow_mul hε.le]
    have h1 : (1:ℝ)/(2 * k) * ((2 * k : ℕ) : ℝ) = 1 := by
      have hne : ((2 * k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h2k
      push_cast
      field_simp
    rw [h1, Real.rpow_one]
  constructor
  · intro h
    exact lt_of_pow_lt_pow_left₀ (2 * k)
      (Real.rpow_pos_of_pos hε _).le (by rw [hr]; exact h)
  · intro h
    calc z ^ (2 * k) < (ε ^ ((1:ℝ)/(2 * k))) ^ (2 * k) :=
          pow_lt_pow_left₀ h hz h2k
      _ = ε := hr

/-- Tied 2-component normal crossing: the exact volume law with the
    multiplicity log factor,
    vol{(x,y) ∈ (0,1)² : (xy)^{2k} < ε} = ε^{1/(2k)}(1 − log ε/(2k)). -/
theorem volume_crossing_tied {k : ℕ} (hk : 1 ≤ k) {ε : ℝ}
    (h0 : 0 < ε) (h1 : ε < 1) :
    (volume : Measure ℝ).prod volume
        {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1
          ∧ (p.1 * p.2) ^ (2 * k) < ε}
      = ENNReal.ofReal (ε ^ ((1:ℝ)/(2 * k))
          * (1 - Real.log ε / (2 * k))) := by
  have hδ0 : 0 < ε ^ ((1:ℝ)/(2 * k)) := Real.rpow_pos_of_pos h0 _
  have hδ1 : ε ^ ((1:ℝ)/(2 * k)) < 1 :=
    Real.rpow_lt_one h0.le h1 (by positivity)
  have hset : {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1
        ∧ (p.1 * p.2) ^ (2 * k) < ε}
      = {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1
        ∧ p.1 * p.2 < ε ^ ((1:ℝ)/(2 * k))} := by
    ext ⟨x, y⟩
    simp only [mem_setOf_eq, mem_Ioo]
    constructor
    · rintro ⟨hx, hy, h⟩
      exact ⟨hx, hy, (pow_lt_iff_lt_rpow hk
        (mul_nonneg hx.1.le hy.1.le) h0).mp h⟩
    · rintro ⟨hx, hy, h⟩
      exact ⟨hx, hy, (pow_lt_iff_lt_rpow hk
        (mul_nonneg hx.1.le hy.1.le) h0).mpr h⟩
  rw [hset, volume_hyperbola hδ0 hδ1]
  congr 1
  rw [Real.log_rpow h0]
  ring

/-! ### The slope survives the log factor

The volume-scaling estimator still reads λ = 1/(2k) at a tied
crossing: the multiplicity factor contributes log log(1/ε) to the
log-volume, which vanishes against log ε. -/

/-- log(1 + u/c)/u → 0 at u → ∞. -/
lemma tendsto_log_one_add_div_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ => Real.log (1 + u / c) / u) atTop (𝓝 0) := by
  have h1 : Tendsto (fun u : ℝ => 1 + u / c) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_id.atTop_div_const hc)
  have h2 : Tendsto (fun u : ℝ => Real.log (1 + u / c) / (1 + u / c))
      atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp h1
  have h3 : Tendsto (fun u : ℝ => (1 + u / c) / u) atTop (𝓝 (0 + 1 / c)) := by
    refine Tendsto.congr' ?_ (tendsto_inv_atTop_zero.add tendsto_const_nhds)
    filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
    field_simp
  have h4 := h2.mul h3
  rw [zero_mul] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
  have hpos : 0 < 1 + u / c := by positivity
  field_simp

/-- thm:multi_component_rates territory, tied case: the log-volume
    slope of the tied crossing still reads λ = 1/(2k); the
    multiplicity log factor drops out of the slope. -/
theorem crossing_tied_slope {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun ε => Real.log (((volume : Measure ℝ).prod volume
        {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1
          ∧ (p.1 * p.2) ^ (2 * k) < ε}).toReal) / Real.log ε)
      (𝓝[>] (0:ℝ)) (𝓝 ((1:ℝ)/(2 * k))) := by
  have hk2 : (0:ℝ) < 2 * k := by positivity
  -- the correction term dies
  have hu : Tendsto (fun ε : ℝ => -Real.log ε) (𝓝[>] (0:ℝ)) atTop :=
    tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero
  have hcorr : Tendsto (fun ε : ℝ =>
      Real.log (1 - Real.log ε / (2 * k)) / Real.log ε)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := ((tendsto_log_one_add_div_atTop hk2).comp hu).neg
    rw [neg_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with ε hε0 hε1
    have hlog : Real.log ε < 0 := Real.log_neg hε0 hε1
    have harg : 1 + -Real.log ε / (2 * k) = 1 - Real.log ε / (2 * k) := by
      ring
    simp only [Function.comp_apply, harg]
    rw [div_neg, neg_neg]
  -- assemble
  have hsum : Tendsto (fun ε : ℝ => (1:ℝ)/(2 * k)
      + Real.log (1 - Real.log ε / (2 * k)) / Real.log ε)
      (𝓝[>] (0:ℝ)) (𝓝 ((1:ℝ)/(2 * k))) := by
    have h := (tendsto_const_nhds (X := ℝ) (x := (1:ℝ)/(2 * k))
      (f := 𝓝[>] (0:ℝ))).add hcorr
    rwa [add_zero] at h
  refine hsum.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds
      (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with ε hε0 hε1
  have hε0' : (0:ℝ) < ε := hε0
  have hlog : Real.log ε < 0 := Real.log_neg hε0' hε1
  have hg : (0:ℝ) < 1 - Real.log ε / (2 * k) := by
    have h := div_neg_of_neg_of_pos hlog hk2
    linarith
  have hδ : (0:ℝ) < ε ^ ((1:ℝ)/(2 * k)) := Real.rpow_pos_of_pos hε0' _
  rw [volume_crossing_tied hk hε0' hε1, ENNReal.toReal_ofReal
    (mul_nonneg hδ.le hg.le), Real.log_mul (ne_of_gt hδ) (ne_of_gt hg),
    Real.log_rpow hε0', add_div, mul_div_assoc,
    div_self (ne_of_lt hlog), mul_one]

/-! ### Distinct orders: no log factor

For distinct orders the same slicing gives a two-term power law with
no log factor: after the b-th-root reduction the sublevel set is
{x^r y < δ} with r = a/b > 1 and δ = ε^{1/b}, the slice profile is
min(1, δ/x^r), and the split integral evaluates in closed form. -/

/-- The r-power hyperbola sublevel set as a region under a graph. -/
lemma power_hyperbola_eq_regionBetween (r δ : ℝ) :
    {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1
      ∧ p.1 ^ r * p.2 < δ}
      = regionBetween (fun _ => 0) (fun x => min 1 (δ / x ^ r)) (Ioo 0 1) := by
  ext ⟨x, y⟩
  simp only [regionBetween, mem_setOf_eq, mem_Ioo]
  constructor
  · rintro ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, hxy⟩
    refine ⟨⟨hx0, hx1⟩, hy0, lt_min hy1 ?_⟩
    rw [lt_div_iff₀ (Real.rpow_pos_of_pos hx0 r), mul_comm]
    exact hxy
  · rintro ⟨⟨hx0, hx1⟩, hy0, hym⟩
    refine ⟨⟨hx0, hx1⟩, ⟨hy0, lt_of_lt_of_le hym (min_le_left _ _)⟩, ?_⟩
    have hyd := lt_of_lt_of_le hym (min_le_right _ _)
    rw [lt_div_iff₀ (Real.rpow_pos_of_pos hx0 r), mul_comm] at hyd
    exact hyd

lemma integrableOn_min_one_div_rpow {r δ : ℝ} (h0 : 0 < δ) :
    IntegrableOn (fun x : ℝ => min 1 (δ / x ^ r)) (Ioc 0 1) := by
  have hcont : ContinuousOn (fun x : ℝ => min 1 (δ / x ^ r)) (Ioc 0 1) := by
    have hdiv : ContinuousOn (fun x : ℝ => δ / x ^ r) (Ioc 0 1) := by
      apply ContinuousOn.div continuousOn_const
      · refine ContinuousOn.congr ?_
          (fun x hx => Real.rpow_def_of_pos hx.1 r)
        exact Real.continuous_exp.comp_continuousOn
          ((Real.continuousOn_log.mono
            (fun x hx => ne_of_gt hx.1)).mul continuousOn_const)
      · exact fun x hx => ne_of_gt (Real.rpow_pos_of_pos hx.1 r)
    exact continuous_min.comp_continuousOn (continuousOn_const.prodMk hdiv)
  refine Integrable.mono'
    (integrableOn_const (C := (1:ℝ)) (μ := volume) (s := Ioc 0 1) ?_)
    (hcont.aestronglyMeasurable measurableSet_Ioc) ?_
  · rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by norm_num)
      (div_nonneg h0.le (Real.rpow_pos_of_pos hx.1 r).le))]
    exact min_le_left _ _

/-- The sliced integral for the r-power profile, r > 1:
    ∫₀¹ min(1, δ/x^r) = (r·δ^{1/r} − δ)/(r − 1). -/
lemma integral_min_one_div_rpow {r δ : ℝ} (hr : 1 < r)
    (h0 : 0 < δ) (h1 : δ < 1) :
    ∫ x in Ioo (0:ℝ) 1, min 1 (δ / x ^ r)
      = (r * δ ^ ((1:ℝ)/r) - δ) / (r - 1) := by
  have hr0 : (0:ℝ) < r := by linarith
  set c := δ ^ ((1:ℝ)/r) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos h0 _
  have hc1 : c < 1 := Real.rpow_lt_one h0.le h1 (by positivity)
  have hcr : c ^ r = δ := by
    rw [hc, ← Real.rpow_mul h0.le, one_div, inv_mul_cancel₀ (ne_of_gt hr0),
      Real.rpow_one]
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
    show Ioc (0:ℝ) 1 = Ioc 0 c ∪ Ioc c 1 from
      (Ioc_union_Ioc_eq_Ioc hc0.le hc1.le).symm,
    setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl)
      measurableSet_Ioc
      ((integrableOn_min_one_div_rpow h0).mono_set
        (Ioc_subset_Ioc_right hc1.le))
      ((integrableOn_min_one_div_rpow h0).mono_set
        (Ioc_subset_Ioc_left hc0.le))]
  have hleft : ∫ x in Ioc (0:ℝ) c, min 1 (δ / x ^ r) = c := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun x hx => min_eq_left
      ((le_div_iff₀ (Real.rpow_pos_of_pos hx.1 r)).mpr (by
        rw [one_mul, ← hcr]
        exact Real.rpow_le_rpow hx.1.le hx.2 hr0.le)))]
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
      Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    linarith
  have hright : ∫ x in Ioc c 1, min 1 (δ / x ^ r)
      = δ * ((1 - c ^ (-r + 1)) / (-r + 1)) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun x hx =>
      min_eq_right ((div_le_one (Real.rpow_pos_of_pos
        (lt_of_lt_of_le hc0 hx.1.le) r)).mpr (by
          rw [← hcr]
          exact Real.rpow_le_rpow hc0.le hx.1.le hr0.le)))]
    rw [← intervalIntegral.integral_of_le hc1.le,
      intervalIntegral.integral_congr (g := fun x => δ * x ^ (-r))
        (fun x hx => by
          rw [Set.uIcc_of_le hc1.le] at hx
          have hx0 : 0 < x := lt_of_lt_of_le hc0 hx.1
          show δ / x ^ r = δ * x ^ (-r)
          rw [Real.rpow_neg hx0.le, div_eq_mul_inv]),
      intervalIntegral.integral_const_mul,
      integral_rpow (Or.inr ⟨by linarith, notMem_uIcc_of_lt hc0 one_pos⟩),
      Real.one_rpow]
  rw [hleft, hright]
  have hcneg : c ^ (-r + 1) = δ⁻¹ * c := by
    rw [Real.rpow_add hc0, Real.rpow_one, Real.rpow_neg hc0.le, hcr]
  rw [hcneg]
  have h1 : (-r + 1) ≠ 0 := by linarith
  have h2 : r - 1 ≠ 0 := by linarith
  have hδ : δ ≠ 0 := ne_of_gt h0
  field_simp
  ring

/-- Exact r-power hyperbola area, r > 1: no log factor. -/
theorem volume_power_hyperbola {r δ : ℝ} (hr : 1 < r) (h0 : 0 < δ)
    (h1 : δ < 1) :
    (volume : Measure ℝ).prod volume
        {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1
          ∧ p.1 ^ r * p.2 < δ}
      = ENNReal.ofReal ((r * δ ^ ((1:ℝ)/r) - δ) / (r - 1)) := by
  rw [power_hyperbola_eq_regionBetween r δ,
    volume_regionBetween_eq_integral
      (integrable_zero _ _ _).integrableOn
      ((integrableOn_min_one_div_rpow h0).mono_set Ioo_subset_Ioc_self)
      measurableSet_Ioo
      (fun x hx => le_min (by norm_num)
        (div_nonneg h0.le (Real.rpow_pos_of_pos hx.1 r).le))]
  rw [show ((fun x => min 1 (δ / x ^ r)) - fun _ => (0:ℝ))
      = fun x => min 1 (δ / x ^ r) from by funext x; simp]
  rw [integral_min_one_div_rpow hr h0 h1]

/-- Distinct-order 2-component crossing: the exact two-term power law
    with no log factor. With a = 2k₁ > b = 2k₂,
    vol{x^{2k₁} y^{2k₂} < ε} = (a·ε^{1/a} − b·ε^{1/b})/(a − b), so the
    leading exponent is 1/(2k₁) = 1/(2·max kᵢ), Watanabe's λ, with
    multiplicity one. -/
theorem volume_crossing_distinct {k₁ k₂ : ℕ} (hk₂ : 1 ≤ k₂)
    (hlt : k₂ < k₁) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    (volume : Measure ℝ).prod volume
        {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1
          ∧ p.1 ^ (2 * k₁) * p.2 ^ (2 * k₂) < ε}
      = ENNReal.ofReal
          ((2 * k₁ * ε ^ ((1:ℝ)/(2 * k₁)) - 2 * k₂ * ε ^ ((1:ℝ)/(2 * k₂)))
            / (2 * k₁ - 2 * k₂)) := by
  have hb0 : (0:ℝ) < 2 * k₂ := by positivity
  have ha0 : (0:ℝ) < 2 * k₁ := by
    have : (0:ℝ) < (k₁:ℝ) := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hlt
    positivity
  have hab : (2 * (k₂:ℝ)) < 2 * k₁ := by
    have : (k₂:ℝ) < k₁ := by exact_mod_cast hlt
    linarith
  set r : ℝ := (2 * k₁) / (2 * k₂) with hrdef
  have hr : 1 < r := (one_lt_div hb0).mpr hab
  set δ : ℝ := ε ^ ((1:ℝ)/(2 * k₂)) with hδdef
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos h0 _
  have hδ1 : δ < 1 := Real.rpow_lt_one h0.le h1 (by positivity)
  have hset : {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1
        ∧ p.1 ^ (2 * k₁) * p.2 ^ (2 * k₂) < ε}
      = {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1
        ∧ p.1 ^ r * p.2 < δ} := by
    ext ⟨x, y⟩
    simp only [mem_setOf_eq, mem_Ioo]
    have key : ∀ hx : 0 < x, ∀ _ : 0 ≤ y,
        (x ^ (2 * k₁) * y ^ (2 * k₂) < ε ↔ x ^ r * y < δ) := by
      intro hx hy
      have hzpow : (x ^ r * y) ^ (2 * k₂)
          = x ^ (2 * k₁) * y ^ (2 * k₂) := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast (x ^ r) (2 * k₂), ← Real.rpow_mul hx.le,
          show r * ((2 * k₂ : ℕ) : ℝ) = ((2 * k₁ : ℕ) : ℝ) from by
            rw [hrdef]; push_cast; field_simp,
          Real.rpow_natCast]
      rw [← hzpow, hδdef]
      exact pow_lt_iff_lt_rpow hk₂
        (mul_nonneg (Real.rpow_pos_of_pos hx r).le hy) h0
    constructor
    · rintro ⟨hx, hy, h⟩
      exact ⟨hx, hy, (key hx.1 hy.1.le).mp h⟩
    · rintro ⟨hx, hy, h⟩
      exact ⟨hx, hy, (key hx.1 hy.1.le).mpr h⟩
  rw [hset, volume_power_hyperbola hr hδ0 hδ1]
  congr 1
  have hδr : δ ^ ((1:ℝ)/r) = ε ^ ((1:ℝ)/(2 * k₁)) := by
    rw [hδdef, ← Real.rpow_mul h0.le]
    congr 1
    rw [hrdef]
    field_simp
  rw [hδr, hδdef, hrdef]
  have h2 : (2 * (k₁:ℝ)) - 2 * k₂ ≠ 0 := by linarith
  have h3 : (2 * (k₁:ℝ)) / (2 * k₂) - 1 ≠ 0 := by
    have := (one_lt_div hb0).mpr hab
    linarith
  field_simp

/-! ### The distinct-order slope

The volume-scaling estimator reads λ = 1/(2·max kᵢ) at a distinct
crossing: the exact two-term law factors as ε^{1/a}·g(ε) with
g → a/(a−b) > 0, and the generalized power-law slope lemma applies. -/

/-- Slope of a modulated power law: if g → C > 0 then the log-log
    slope of ε^α·g(ε) tends to α. -/
lemma tendsto_log_div_log_rpow_mul {α C : ℝ} {g : ℝ → ℝ} (hC : 0 < C)
    (hg : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 C)) :
    Tendsto (fun ε => Real.log (ε ^ α * g ε) / Real.log ε)
      (𝓝[>] (0:ℝ)) (𝓝 α) := by
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), C / 2 < g ε :=
    hg.eventually (lt_mem_nhds (half_lt_self hC))
  have hlt1 : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε < 1 :=
    eventually_nhdsWithin_of_eventually_nhds
      (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))
  have hsplit : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      Real.log (ε ^ α * g ε) / Real.log ε
        = α + Real.log (g ε) / Real.log ε := by
    filter_upwards [hev, hlt1, eventually_mem_nhdsWithin] with ε hgε hε1 hε0
    have hεpos : (0:ℝ) < ε := hε0
    have hgpos : 0 < g ε := lt_trans (by positivity) hgε
    have hlogε : Real.log ε ≠ 0 := ne_of_lt (Real.log_neg hεpos hε1)
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hεpos α))
        (ne_of_gt hgpos),
      Real.log_rpow hεpos, add_div, mul_div_assoc, div_self hlogε, mul_one]
  have hnum : Tendsto (fun ε => Real.log (g ε)) (𝓝[>] (0:ℝ))
      (𝓝 (Real.log C)) :=
    ((Real.continuousAt_log (ne_of_gt hC)).tendsto).comp hg
  have hcorr : Tendsto (fun ε => Real.log (g ε) / Real.log ε)
      (𝓝[>] (0:ℝ)) (𝓝 0) := hnum.div_atBot Real.tendsto_log_nhdsGT_zero
  have hsum : Tendsto (fun ε => α + Real.log (g ε) / Real.log ε)
      (𝓝[>] (0:ℝ)) (𝓝 α) := by
    have h := (tendsto_const_nhds (X := ℝ) (x := α)
      (f := 𝓝[>] (0:ℝ))).add hcorr
    rwa [add_zero] at h
  exact hsum.congr' (by filter_upwards [hsplit] with ε h; exact h.symm)

/-- Small positive powers vanish at 0⁺. -/
lemma tendsto_rpow_nhdsGT_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ε : ℝ => ε ^ c) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const 0 c (Or.inr hc.le)).tendsto
  rw [Real.zero_rpow (ne_of_gt hc)] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- thm:multi_component_rates, distinct orders: the log-volume slope
    reads λ = 1/(2k₁) = 1/(2·max kᵢ), Watanabe's exponent at
    multiplicity one. -/
theorem crossing_distinct_slope {k₁ k₂ : ℕ} (hk₂ : 1 ≤ k₂)
    (hlt : k₂ < k₁) :
    Tendsto (fun ε => Real.log (((volume : Measure ℝ).prod volume
        {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1
          ∧ p.1 ^ (2 * k₁) * p.2 ^ (2 * k₂) < ε}).toReal)
        / Real.log ε)
      (𝓝[>] (0:ℝ)) (𝓝 ((1:ℝ)/(2 * k₁))) := by
  have hb0 : (0:ℝ) < 2 * k₂ := by positivity
  have ha0 : (0:ℝ) < 2 * k₁ := by
    have h : (0:ℝ) < (k₁:ℝ) := by
      exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hlt
    positivity
  have hab : (2 * (k₂:ℝ)) < 2 * k₁ := by
    have h : (k₂:ℝ) < k₁ := by exact_mod_cast hlt
    linarith
  set c : ℝ := (1:ℝ)/(2 * k₂) - (1:ℝ)/(2 * k₁) with hc
  have hcpos : 0 < c := by
    rw [hc]
    have h1 : (1:ℝ)/(2 * k₁) < 1/(2 * k₂) :=
      one_div_lt_one_div_of_lt hb0 hab
    linarith
  set g : ℝ → ℝ := fun ε =>
    (2 * k₁ - 2 * k₂ * ε ^ c) / (2 * k₁ - 2 * k₂) with hg
  have hglim : Tendsto g (𝓝[>] (0:ℝ))
      (𝓝 ((2 * k₁) / (2 * k₁ - 2 * k₂))) := by
    rw [hg]
    have h1 := (tendsto_rpow_nhdsGT_zero hcpos).const_mul (2 * (k₂:ℝ))
    rw [mul_zero] at h1
    have h2 := (tendsto_const_nhds (X := ℝ) (x := 2 * (k₁:ℝ))
      (f := 𝓝[>] (0:ℝ))).sub h1
    rw [sub_zero] at h2
    exact h2.div_const _
  have hClim : (0:ℝ) < (2 * k₁) / (2 * k₁ - 2 * k₂) :=
    div_pos ha0 (by linarith)
  refine (tendsto_log_div_log_rpow_mul hClim hglim).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds
      (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with ε hε0 hε1
  have hεpos : (0:ℝ) < ε := hε0
  have hval : (2 * k₁ * ε ^ ((1:ℝ)/(2 * k₁))
        - 2 * k₂ * ε ^ ((1:ℝ)/(2 * k₂))) / (2 * k₁ - 2 * k₂)
      = ε ^ ((1:ℝ)/(2 * k₁)) * g ε := by
    rw [hg]
    have hsplitpow : ε ^ ((1:ℝ)/(2 * k₂))
        = ε ^ ((1:ℝ)/(2 * k₁)) * ε ^ c := by
      rw [hc, ← Real.rpow_add hεpos]
      congr 1
      ring
    rw [hsplitpow]
    field_simp
  have hg0 : 0 < g ε := by
    rw [hg]
    have hpow1 : ε ^ c < 1 :=
      Real.rpow_lt_one hεpos.le hε1 hcpos
    have h1 : 2 * (k₂:ℝ) * ε ^ c < 2 * k₂ := by
      nlinarith [Real.rpow_pos_of_pos hεpos c]
    exact div_pos (by linarith) (by linarith)
  have hnn : (0:ℝ) ≤ (2 * k₁ * ε ^ ((1:ℝ)/(2 * k₁))
        - 2 * k₂ * ε ^ ((1:ℝ)/(2 * k₂))) / (2 * k₁ - 2 * k₂) := by
    rw [hval]
    exact (mul_pos (Real.rpow_pos_of_pos hεpos _) hg0).le
  rw [volume_crossing_distinct hk₂ hlt hεpos hε1,
    ENNReal.toReal_ofReal hnn, hval]

/-! ### Three tied components: the log² factor

vol{(x,y,z) ∈ (0,1)³ : xyz < δ} = δ(1 − log δ + (log δ)²/2): each
extra tied component contributes one more power of log(1/ε).
Multiplicity three in volume form, by slicing the cube over the
2-component hyperbola profile. -/

lemma hyper3_eq_regionBetween (δ : ℝ) :
    {p : (ℝ × ℝ) × ℝ | (p.1.1 ∈ Ioo (0:ℝ) 1 ∧ p.1.2 ∈ Ioo (0:ℝ) 1)
        ∧ p.2 ∈ Ioo (0:ℝ) 1 ∧ p.1.1 * p.1.2 * p.2 < δ}
      = regionBetween (fun _ => 0)
          (fun q : ℝ × ℝ => min 1 (δ / (q.1 * q.2)))
          (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) := by
  ext ⟨⟨x, y⟩, z⟩
  simp only [regionBetween, mem_setOf_eq, mem_Ioo, mem_prod]
  constructor
  · rintro ⟨⟨hx, hy⟩, ⟨hz0, hz1⟩, hxyz⟩
    refine ⟨⟨hx, hy⟩, hz0, lt_min hz1 ?_⟩
    rw [lt_div_iff₀ (mul_pos hx.1 hy.1), mul_comm]
    exact hxyz
  · rintro ⟨⟨hx, hy⟩, hz0, hzm⟩
    refine ⟨⟨hx, hy⟩, ⟨hz0, lt_of_lt_of_le hzm (min_le_left _ _)⟩, ?_⟩
    have h := lt_of_lt_of_le hzm (min_le_right _ _)
    rw [lt_div_iff₀ (mul_pos hx.1 hy.1), mul_comm] at h
    exact h

lemma integrableOn_min_slice {δ : ℝ} (h0 : 0 < δ) :
    IntegrableOn (fun q : ℝ × ℝ => min 1 (δ / (q.1 * q.2)))
      (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) ((volume : Measure ℝ).prod volume) := by
  have hmeas : Measurable fun q : ℝ × ℝ => min 1 (δ / (q.1 * q.2)) :=
    measurable_const.min
      (measurable_const.div (measurable_fst.mul measurable_snd))
  refine Integrable.mono'
    (integrableOn_const (C := (1:ℝ)) ?_)
    hmeas.aestronglyMeasurable.restrict ?_
  · rw [Measure.prod_prod, Real.volume_Ioo]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)]
      with q hq
    have hpos : 0 < q.1 * q.2 := mul_pos hq.1.1 hq.2.1
    rw [Real.norm_eq_abs, abs_of_nonneg
      (le_min (by norm_num) (div_nonneg h0.le hpos.le))]
    exact min_le_left _ _

/-- FTC piece: ∫ log x/x over [δ, 1] is −(log δ)²/2. -/
lemma integral_log_div_self {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    ∫ x in δ..(1:ℝ), Real.log x * x⁻¹ = -(Real.log δ ^ 2 / 2) := by
  have hftc : ∫ x in δ..(1:ℝ), Real.log x * x⁻¹
      = Real.log 1 ^ 2 / 2 - Real.log δ ^ 2 / 2 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x => Real.log x ^ 2 / 2) (fun x hx => ?_) ?_
    · rw [Set.uIcc_of_le h1.le] at hx
      have hx0 : 0 < x := lt_of_lt_of_le h0 hx.1
      have h := ((Real.hasDerivAt_log (ne_of_gt hx0)).pow 2).div_const 2
      convert h using 1
      ring
    · apply ContinuousOn.intervalIntegrable
      have hsub : Set.uIcc δ (1:ℝ) ⊆ {x : ℝ | x ≠ 0} := by
        rw [Set.uIcc_of_le h1.le]
        intro x hx
        exact ne_of_gt (lt_of_lt_of_le h0 hx.1)
      exact (Real.continuousOn_log.mono hsub).mul
        (continuousOn_inv₀.mono hsub)
  rw [hftc, Real.log_one]
  ring

/-- Exact three-component hyperbola volume: the log² law. -/
theorem volume_hyperbola3 {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    ((volume : Measure ℝ).prod volume).prod volume
        {p : (ℝ × ℝ) × ℝ | (p.1.1 ∈ Ioo (0:ℝ) 1 ∧ p.1.2 ∈ Ioo (0:ℝ) 1)
          ∧ p.2 ∈ Ioo (0:ℝ) 1 ∧ p.1.1 * p.1.2 * p.2 < δ}
      = ENNReal.ofReal
          (δ * (1 - Real.log δ + Real.log δ ^ 2 / 2)) := by
  rw [hyper3_eq_regionBetween δ,
    volume_regionBetween_eq_integral
      (integrable_zero _ _ _).integrableOn
      (integrableOn_min_slice h0)
      (measurableSet_Ioo.prod measurableSet_Ioo)
      (fun q hq => le_min (by norm_num)
        (div_nonneg h0.le (mul_pos hq.1.1 hq.2.1).le))]
  rw [show ((fun q : ℝ × ℝ => min 1 (δ / (q.1 * q.2))) - fun _ => (0:ℝ))
      = fun q : ℝ × ℝ => min 1 (δ / (q.1 * q.2)) from by funext q; simp]
  congr 1
  rw [setIntegral_prod _ (integrableOn_min_slice h0)]
  -- inner-integral evaluations
  have hinner1 : ∀ x ∈ Ioc (0:ℝ) δ,
      (∫ y in Ioo (0:ℝ) 1, min 1 (δ / (x * y))) = 1 := by
    intro x hx
    rw [setIntegral_congr_fun measurableSet_Ioo (fun y hy => min_eq_left (by
      rw [le_div_iff₀ (mul_pos (lt_of_lt_of_le hx.1 le_rfl) hy.1)]
      nlinarith [hx.1, hx.2, hy.1, hy.2]))]
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
      Real.volume_Ioo, ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  have hinner2 : ∀ x ∈ Ioc δ 1,
      (∫ y in Ioo (0:ℝ) 1, min 1 (δ / (x * y)))
        = (δ / x) * (1 - Real.log (δ / x)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le h0 hx.1.le
    have hfun : ∀ y : ℝ, δ / (x * y) = (δ / x) / y := fun y => by
      rw [div_div]
    simp only [hfun]
    exact integral_min_one_div (div_pos h0 hx0)
      ((div_lt_one hx0).mpr hx.1)
  -- outer split
  have hcont2 : ContinuousOn
      (fun x : ℝ => (δ / x) * (1 - Real.log (δ / x))) (Icc δ 1) := by
    have hne : ∀ x ∈ Icc δ 1, x ≠ 0 :=
      fun x hx => ne_of_gt (lt_of_lt_of_le h0 hx.1)
    have hdiv : ContinuousOn (fun x : ℝ => δ / x) (Icc δ 1) :=
      continuousOn_const.div continuousOn_id hne
    have hlog : ContinuousOn (fun x : ℝ => Real.log (δ / x)) (Icc δ 1) := by
      refine Real.continuousOn_log.comp hdiv ?_
      intro x hx
      exact ne_of_gt (div_pos h0 (lt_of_lt_of_le h0 hx.1))
    exact hdiv.mul (continuousOn_const.sub hlog)
  have hint1 : IntegrableOn
      (fun x => ∫ y in Ioo (0:ℝ) 1, min 1 (δ / (x * y))) (Ioc 0 δ) := by
    refine (integrableOn_const (C := (1:ℝ)) ?_).congr_fun
      (fun x hx => (hinner1 x hx).symm) measurableSet_Ioc
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hint2 : IntegrableOn
      (fun x => ∫ y in Ioo (0:ℝ) 1, min 1 (δ / (x * y))) (Ioc δ 1) := by
    refine ((hcont2.integrableOn_Icc).mono_set Ioc_subset_Icc_self).congr_fun
      (fun x hx => (hinner2 x hx).symm) measurableSet_Ioc
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
    show Ioc (0:ℝ) 1 = Ioc 0 δ ∪ Ioc δ 1 from
      (Ioc_union_Ioc_eq_Ioc h0.le h1.le).symm,
    setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      hint1 hint2,
    setIntegral_congr_fun measurableSet_Ioc hinner1,
    setIntegral_congr_fun measurableSet_Ioc hinner2]
  -- piece values
  have hpiece1 : ∫ _ in Ioc (0:ℝ) δ, (1:ℝ) = δ := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
      Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    linarith
  have hpiece2 : ∫ x in Ioc δ 1, (δ / x) * (1 - Real.log (δ / x))
      = δ * (-Real.log δ + Real.log δ ^ 2 / 2) := by
    rw [← intervalIntegral.integral_of_le h1.le]
    have hcongr : ∀ x ∈ Set.uIcc δ (1:ℝ),
        (δ / x) * (1 - Real.log (δ / x))
          = δ * (1 - Real.log δ) * x⁻¹ + δ * (Real.log x * x⁻¹) := by
      intro x hx
      rw [Set.uIcc_of_le h1.le] at hx
      have hx0 : 0 < x := lt_of_lt_of_le h0 hx.1
      rw [Real.log_div (ne_of_gt h0) (ne_of_gt hx0)]
      field_simp
      ring
    rw [intervalIntegral.integral_congr hcongr]
    have hi1 : IntervalIntegrable (fun x : ℝ => δ * (1 - Real.log δ) * x⁻¹)
        volume δ 1 := by
      apply ContinuousOn.intervalIntegrable
      have hne : ∀ x ∈ Set.uIcc δ (1:ℝ), x ≠ 0 := by
        rw [Set.uIcc_of_le h1.le]
        exact fun x hx => ne_of_gt (lt_of_lt_of_le h0 hx.1)
      exact continuousOn_const.mul (continuousOn_inv₀.mono hne)
    have hi2 : IntervalIntegrable (fun x : ℝ => δ * (Real.log x * x⁻¹))
        volume δ 1 := by
      apply ContinuousOn.intervalIntegrable
      have hne : Set.uIcc δ (1:ℝ) ⊆ {x : ℝ | x ≠ 0} := by
        rw [Set.uIcc_of_le h1.le]
        exact fun x hx => ne_of_gt (lt_of_lt_of_le h0 hx.1)
      exact continuousOn_const.mul
        ((Real.continuousOn_log.mono hne).mul (continuousOn_inv₀.mono hne))
    rw [intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_inv_of_pos h0 one_pos, integral_log_div_self h0 h1,
      Real.log_div one_ne_zero (ne_of_gt h0), Real.log_one]
    ring
  rw [hpiece1, hpiece2]
  ring

/-- Tied 3-component normal crossing: multiplicity three appears as
    the log² factor,
    vol{(xyz)^{2k} < ε} = ε^{1/(2k)}(1 − log ε/(2k) + (log ε)²/(8k²)). -/
theorem volume_crossing_tied3 {k : ℕ} (hk : 1 ≤ k) {ε : ℝ}
    (h0 : 0 < ε) (h1 : ε < 1) :
    ((volume : Measure ℝ).prod volume).prod volume
        {p : (ℝ × ℝ) × ℝ | (p.1.1 ∈ Ioo (0:ℝ) 1 ∧ p.1.2 ∈ Ioo (0:ℝ) 1)
          ∧ p.2 ∈ Ioo (0:ℝ) 1
          ∧ (p.1.1 * p.1.2 * p.2) ^ (2 * k) < ε}
      = ENNReal.ofReal (ε ^ ((1:ℝ)/(2 * k))
          * (1 - Real.log ε / (2 * k)
            + Real.log ε ^ 2 / (2 * k) ^ 2 / 2)) := by
  have hδ0 : 0 < ε ^ ((1:ℝ)/(2 * k)) := Real.rpow_pos_of_pos h0 _
  have hδ1 : ε ^ ((1:ℝ)/(2 * k)) < 1 :=
    Real.rpow_lt_one h0.le h1 (by positivity)
  have hset : {p : (ℝ × ℝ) × ℝ |
        (p.1.1 ∈ Ioo (0:ℝ) 1 ∧ p.1.2 ∈ Ioo (0:ℝ) 1)
          ∧ p.2 ∈ Ioo (0:ℝ) 1
          ∧ (p.1.1 * p.1.2 * p.2) ^ (2 * k) < ε}
      = {p : (ℝ × ℝ) × ℝ |
        (p.1.1 ∈ Ioo (0:ℝ) 1 ∧ p.1.2 ∈ Ioo (0:ℝ) 1)
          ∧ p.2 ∈ Ioo (0:ℝ) 1
          ∧ p.1.1 * p.1.2 * p.2 < ε ^ ((1:ℝ)/(2 * k))} := by
    ext ⟨⟨x, y⟩, z⟩
    simp only [mem_setOf_eq, mem_Ioo]
    constructor
    · rintro ⟨hxy, hz, h⟩
      exact ⟨hxy, hz, (pow_lt_iff_lt_rpow hk
        (mul_nonneg (mul_nonneg hxy.1.1.le hxy.2.1.le) hz.1.le) h0).mp h⟩
    · rintro ⟨hxy, hz, h⟩
      exact ⟨hxy, hz, (pow_lt_iff_lt_rpow hk
        (mul_nonneg (mul_nonneg hxy.1.1.le hxy.2.1.le) hz.1.le) h0).mpr h⟩
  rw [hset, volume_hyperbola3 hδ0 hδ1]
  congr 1
  rw [Real.log_rpow h0]
  ring

end DeadDirections
