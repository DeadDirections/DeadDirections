/-
  General-r tied normal crossing: the volume law at every multiplicity.

  For r tied components on the open unit cube the sublevel volume of
  the product is exact:

    vol{x ∈ (0,1)^r : x₁⋯x_r < δ} = δ · Σ_{j<r} (−log δ)^j / j!,

  Watanabe's multiplicity m = r in volume form, one power of log(1/δ)
  per extra tied component. The proof is a Fubini induction over the
  first coordinate through the piFinSuccAbove equivalence: the slice
  at x₁ ≤ δ is the whole cube, the slice at x₁ ∈ (δ, 1) is the same
  set at threshold δ/x₁, and the 1-D recursion

    δ + ∫_δ^1 P_r(δ/x) dx = P_{r+1}(δ)

  closes by one integration by parts per log power. The r ≤ 3 cases in
  MultiCrossing are instances; the (∏ xᵢ)^{2k} < ε corollary carries
  the law to the crossing form the paper reads.
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import DeadDirections.MultiCrossing
import DeadDirections.VolumeMultiG

namespace DeadDirections

open MeasureTheory Set Filter Topology

/-- The multiplicity-r log polynomial δ·Σ_{j<r} (−log δ)^j / j!. -/
noncomputable def logPoly (r : ℕ) (δ : ℝ) : ℝ :=
  δ * ∑ j ∈ Finset.range r, (-Real.log δ) ^ j / (Nat.factorial j)

lemma logPoly_one (δ : ℝ) : logPoly 1 δ = δ := by
  simp [logPoly]

/-- Every term of the log polynomial is nonnegative below threshold
    one. -/
lemma logPoly_term_nonneg {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) (j : ℕ) :
    0 ≤ (-Real.log δ) ^ j / (Nat.factorial j : ℝ) := by
  have hlog : 0 ≤ -Real.log δ := by
    have := Real.log_neg h0 h1
    linarith
  positivity

lemma logPoly_nonneg (r : ℕ) {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    0 ≤ logPoly r δ :=
  mul_nonneg h0.le
    (Finset.sum_nonneg fun j _ => logPoly_term_nonneg h0 h1 j)

/-- Below threshold one the log polynomial dominates its own
    threshold: the j = 0 term alone contributes δ. -/
lemma le_logPoly {r : ℕ} (hr : 1 ≤ r) {δ : ℝ} (h0 : 0 < δ)
    (h1 : δ < 1) : δ ≤ logPoly r δ := by
  have hmem : (0 : ℕ) ∈ Finset.range r := Finset.mem_range.mpr (by omega)
  have hsum : (1:ℝ) ≤ ∑ j ∈ Finset.range r,
      (-Real.log δ) ^ j / (Nat.factorial j) := by
    calc (1:ℝ) = (-Real.log δ) ^ 0 / (Nat.factorial 0 : ℝ) := by norm_num
      _ ≤ _ := Finset.single_le_sum
          (fun j _ => logPoly_term_nonneg h0 h1 j) hmem
  calc δ = δ * 1 := (mul_one δ).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum h0.le

/-- One integration by parts:
    ∫_δ^1 (δ/x)·log(x/δ)^j dx = δ·(−log δ)^{j+1}/(j+1). -/
lemma integral_scaled_log_pow {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1)
    (j : ℕ) :
    ∫ x in δ..1, δ * x⁻¹ * (Real.log x - Real.log δ) ^ j
      = δ * (-Real.log δ) ^ (j + 1) / (j + 1) := by
  have hne : ∀ x ∈ Set.uIcc δ (1:ℝ), x ≠ 0 := by
    rw [Set.uIcc_of_le h1.le]
    exact fun x hx => ne_of_gt (lt_of_lt_of_le h0 hx.1)
  have hftc : ∫ x in δ..1, δ * x⁻¹ * (Real.log x - Real.log δ) ^ j
      = δ * (Real.log 1 - Real.log δ) ^ (j + 1) / (j + 1)
        - δ * (Real.log δ - Real.log δ) ^ (j + 1) / (j + 1) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x => δ * (Real.log x - Real.log δ) ^ (j + 1) / ((j:ℝ) + 1))
      (fun x hx => ?_) ?_
    · have hx0 : 0 < x := by
        rw [Set.uIcc_of_le h1.le] at hx
        exact lt_of_lt_of_le h0 hx.1
      have h := (((Real.hasDerivAt_log (ne_of_gt hx0)).sub_const
        (Real.log δ)).pow (j + 1)).const_mul δ |>.div_const ((j:ℝ) + 1)
      convert h using 1
      have hj : ((j:ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
    · apply ContinuousOn.intervalIntegrable
      exact (continuousOn_const.mul (continuousOn_inv₀.mono hne)).mul
        (((Real.continuousOn_log.mono hne).sub continuousOn_const).pow j)
  rw [hftc, Real.log_one, sub_self, zero_pow (by omega : j + 1 ≠ 0)]
  ring

/-- The 1-D recursion behind the Fubini induction:
    δ + ∫_δ^1 P_r(δ/x) dx = P_{r+1}(δ). -/
lemma logPoly_recursion (r : ℕ) {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    δ + ∫ x in δ..1, logPoly r (δ / x) = logPoly (r + 1) δ := by
  have hne : ∀ x ∈ Set.uIcc δ (1:ℝ), x ≠ 0 := by
    rw [Set.uIcc_of_le h1.le]
    exact fun x hx => ne_of_gt (lt_of_lt_of_le h0 hx.1)
  have hcongr : Set.EqOn (fun x => logPoly r (δ / x))
      (fun x => ∑ j ∈ Finset.range r,
        δ * x⁻¹ * (Real.log x - Real.log δ) ^ j / (Nat.factorial j))
      (Set.uIcc δ 1) := by
    intro x hx
    have hx0 : 0 < x := by
      rw [Set.uIcc_of_le h1.le] at hx
      exact lt_of_lt_of_le h0 hx.1
    have hlog : -Real.log (δ / x) = Real.log x - Real.log δ := by
      rw [Real.log_div (ne_of_gt h0) (ne_of_gt hx0)]
      ring
    show logPoly r (δ / x) = _
    rw [logPoly, hlog, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_eq_mul_inv δ x]
    ring
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_finset_sum (fun j _ => by
      apply ContinuousOn.intervalIntegrable
      exact ((continuousOn_const.mul (continuousOn_inv₀.mono hne)).mul
        (((Real.continuousOn_log.mono hne).sub continuousOn_const).pow j)
        ).div_const _)]
  have hterm : ∀ j ∈ Finset.range r,
      (∫ x in δ..1, δ * x⁻¹ * (Real.log x - Real.log δ) ^ j
          / (Nat.factorial j))
        = δ * (-Real.log δ) ^ (j + 1) / (Nat.factorial (j + 1)) := by
    intro j _
    rw [intervalIntegral.integral_div, integral_scaled_log_pow h0 h1 j,
      Nat.factorial_succ]
    have hfj : ((Nat.factorial j : ℝ)) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.factorial_pos j))
    have hj1 : ((j:ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hterm, logPoly, Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [mul_add, mul_one, Finset.mul_sum, add_comm δ]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ => ?_) rfl
  rw [mul_div_assoc]

/-- The r-component hyperbola region on the open unit cube. -/
def cubeHyper (r : ℕ) (δ : ℝ) : Set (Fin r → ℝ) :=
  {x | (∀ i, x i ∈ Ioo (0:ℝ) 1) ∧ ∏ i, x i < δ}

lemma measurableSet_cubeHyper (r : ℕ) (δ : ℝ) :
    MeasurableSet (cubeHyper r δ) := by
  have h1 : MeasurableSet {x : Fin r → ℝ | ∀ i, x i ∈ Ioo (0:ℝ) 1} := by
    rw [show {x : Fin r → ℝ | ∀ i, x i ∈ Ioo (0:ℝ) 1}
        = ⋂ i, (fun x : Fin r → ℝ => x i) ⁻¹' Ioo (0:ℝ) 1 from by
      ext x; simp]
    exact MeasurableSet.iInter fun i =>
      (measurable_pi_apply i) measurableSet_Ioo
  have h2 : MeasurableSet {x : Fin r → ℝ | ∏ i, x i < δ} :=
    measurableSet_lt
      (Finset.univ.measurable_prod fun i _ => measurable_pi_apply i)
      measurable_const
  exact h1.inter h2

/-- The open unit cube has volume one in every dimension. -/
lemma volume_unitCube (n : ℕ) :
    volume {y : Fin n → ℝ | ∀ i, y i ∈ Ioo (0:ℝ) 1} = 1 := by
  rw [show {y : Fin n → ℝ | ∀ i, y i ∈ Ioo (0:ℝ) 1}
      = Set.pi univ fun _ => Ioo (0:ℝ) 1 from by ext y; simp]
  rw [volume_pi_pi]
  simp [Real.volume_Ioo]

/-- The general-r tied hyperbola volume:
    vol{x ∈ (0,1)^r : ∏ xᵢ < δ} = δ·Σ_{j<r} (−log δ)^j / j!. -/
theorem volume_cubeHyper :
    ∀ {r : ℕ}, 1 ≤ r → ∀ {δ : ℝ}, 0 < δ → δ < 1 →
      volume (cubeHyper r δ) = ENNReal.ofReal (logPoly r δ) := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    intro δ h0 h1
    have hset : cubeHyper 1 δ
        = Set.pi univ fun _ : Fin 1 => Ioo (0:ℝ) δ := by
      ext x
      simp only [cubeHyper, mem_setOf_eq, Set.mem_pi, mem_univ,
        forall_const, mem_Ioo, Fin.prod_univ_one]
      constructor
      · rintro ⟨hall, hprod⟩ i
        rw [Subsingleton.elim i 0]
        exact ⟨(hall 0).1, hprod⟩
      · intro h
        refine ⟨fun i => ?_, (h 0).2⟩
        rw [Subsingleton.elim i 0]
        exact ⟨(h 0).1, lt_trans (h 0).2 h1⟩
    rw [hset, volume_pi_pi]
    rw [Real.volume_Ioo, sub_zero, Fin.prod_const, pow_one, logPoly_one]
  | succ n hn ih =>
    intro δ h0 h1
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
      with he
    set A : Set (ℝ × (Fin n → ℝ)) :=
      {p | p.1 ∈ Ioo (0:ℝ) 1 ∧ (∀ i, p.2 i ∈ Ioo (0:ℝ) 1)
        ∧ p.1 * ∏ i, p.2 i < δ} with hA
    have hAmeas : MeasurableSet A := by
      have h1 : MeasurableSet {p : ℝ × (Fin n → ℝ) | p.1 ∈ Ioo (0:ℝ) 1} :=
        measurable_fst measurableSet_Ioo
      have h2 : MeasurableSet {p : ℝ × (Fin n → ℝ) | ∀ i, p.2 i ∈ Ioo (0:ℝ) 1} := by
        rw [show {p : ℝ × (Fin n → ℝ) | ∀ i, p.2 i ∈ Ioo (0:ℝ) 1}
            = ⋂ i, (fun p : ℝ × (Fin n → ℝ) => p.2 i) ⁻¹' Ioo (0:ℝ) 1
            from by ext p; simp]
        exact MeasurableSet.iInter fun i =>
          ((measurable_pi_apply i).comp measurable_snd) measurableSet_Ioo
      have h3 : MeasurableSet {p : ℝ × (Fin n → ℝ) | p.1 * ∏ i, p.2 i < δ} :=
        measurableSet_lt
          (measurable_fst.mul (Finset.univ.measurable_prod fun i _ =>
            (measurable_pi_apply i).comp measurable_snd))
          measurable_const
      exact h1.inter (h2.inter h3)
    have hpre : cubeHyper (n+1) δ = e ⁻¹' A := by
      ext x
      simp only [cubeHyper, mem_setOf_eq, mem_preimage, he,
        MeasurableEquiv.piFinSuccAbove_apply, hA]
      rw [Fin.forall_fin_succ, Fin.prod_univ_succ]
      tauto
    have hmp := MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin (n+1) => ℝ) 0
    have hAv : volume (cubeHyper (n+1) δ) = volume A := by
      rw [hpre]
      exact hmp.measure_preimage hAmeas.nullMeasurableSet
    rw [hAv, MeasureTheory.Measure.volume_eq_prod, Measure.prod_apply hAmeas]
    have hslice : ∀ t : ℝ,
        (volume : Measure (Fin n → ℝ)) (Prod.mk t ⁻¹' A)
          = Set.indicator (Ioo (0:ℝ) 1)
              (fun t => if t ≤ δ then 1
                else ENNReal.ofReal (logPoly n (δ / t))) t := by
      intro t
      by_cases ht : t ∈ Ioo (0:ℝ) 1
      · rw [Set.indicator_of_mem ht]
        by_cases htδ : t ≤ δ
        · rw [if_pos htδ]
          have hfull : Prod.mk t ⁻¹' A
              = {y : Fin n → ℝ | ∀ i, y i ∈ Ioo (0:ℝ) 1} := by
            ext y
            simp only [mem_preimage, hA, mem_setOf_eq]
            constructor
            · rintro ⟨-, hy, -⟩
              exact hy
            · intro hy
              refine ⟨ht, hy, ?_⟩
              set i0 : Fin n := ⟨0, by omega⟩ with hi0
              have hrest : ∏ i ∈ Finset.univ.erase i0, y i ≤ 1 :=
                Finset.prod_le_one (fun i _ => (hy i).1.le)
                  (fun i _ => (hy i).2.le)
              have hprod : ∏ i, y i ≤ y i0 := by
                rw [← Finset.mul_prod_erase Finset.univ y
                  (Finset.mem_univ i0)]
                calc y i0 * ∏ i ∈ Finset.univ.erase i0, y i
                    ≤ y i0 * 1 :=
                      mul_le_mul_of_nonneg_left hrest (hy i0).1.le
                  _ = y i0 := mul_one _
              have h1' : t * ∏ i, y i ≤ t * y i0 :=
                mul_le_mul_of_nonneg_left hprod ht.1.le
              have h2' : t * y i0 < t * 1 :=
                mul_lt_mul_of_pos_left (hy i0).2 ht.1
              rw [mul_one] at h2'
              linarith
          rw [hfull, volume_unitCube]
        · rw [if_neg htδ]
          push Not at htδ
          have hcube : Prod.mk t ⁻¹' A = cubeHyper n (δ / t) := by
            ext y
            simp only [mem_preimage, hA, mem_setOf_eq, cubeHyper]
            constructor
            · rintro ⟨-, hy, hlt⟩
              refine ⟨hy, ?_⟩
              rwa [lt_div_iff₀ ht.1, mul_comm]
            · rintro ⟨hy, hlt⟩
              refine ⟨ht, hy, ?_⟩
              rwa [lt_div_iff₀ ht.1, mul_comm] at hlt
          rw [hcube, ih (div_pos h0 ht.1) ((div_lt_one ht.1).mpr htδ)]
      · rw [Set.indicator_of_notMem ht]
        have hempty : Prod.mk t ⁻¹' A = ∅ := by
          ext y
          simp only [mem_preimage, hA, mem_setOf_eq,
            mem_empty_iff_false, iff_false]
          rintro ⟨ht', -, -⟩
          exact ht ht'
        rw [hempty, measure_empty]
    rw [lintegral_congr hslice, lintegral_indicator measurableSet_Ioo,
      ← Set.Ioc_union_Ioo_eq_Ioo h0.le h1]
    have hdisj : Disjoint (Ioc (0:ℝ) δ) (Ioo δ 1) := by
      rw [Set.disjoint_left]
      rintro x hx1 hx2
      exact absurd hx1.2 (not_le.mpr hx2.1)
    rw [lintegral_union measurableSet_Ioo hdisj]
    have hp1 : (∫⁻ t in Ioc (0:ℝ) δ, (if t ≤ δ then 1
          else ENNReal.ofReal (logPoly n (δ / t))))
        = ENNReal.ofReal δ := by
      rw [setLIntegral_congr_fun measurableSet_Ioc
        (fun t ht => if_pos ht.2)]
      rw [setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero]
    have hcont : ContinuousOn (fun t : ℝ => logPoly n (δ / t))
        (Icc δ 1) := by
      have htne : ∀ t ∈ Icc δ (1:ℝ), t ≠ 0 :=
        fun t ht => ne_of_gt (lt_of_lt_of_le h0 ht.1)
      have hdiv : ContinuousOn (fun t : ℝ => δ / t) (Icc δ 1) :=
        continuousOn_const.div continuousOn_id htne
      have hmaps : Set.MapsTo (fun t : ℝ => δ / t) (Icc δ 1)
          {x : ℝ | x ≠ 0} :=
        fun t ht => ne_of_gt (div_pos h0 (lt_of_lt_of_le h0 ht.1))
      unfold logPoly
      apply hdiv.mul
      apply continuousOn_finset_sum
      intro j _
      exact (((Real.continuousOn_log.comp hdiv hmaps).neg).pow j).div_const _
    have hint : IntegrableOn (fun t : ℝ => logPoly n (δ / t))
        (Ioo δ 1) :=
      (hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
    have hnn : 0 ≤ᵐ[volume.restrict (Ioo δ 1)]
        fun t : ℝ => logPoly n (δ / t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : 0 < t := lt_trans h0 ht.1
      exact logPoly_nonneg n (div_pos h0 ht0)
        ((div_lt_one ht0).mpr ht.1)
    have hp2 : (∫⁻ t in Ioo δ 1, (if t ≤ δ then 1
          else ENNReal.ofReal (logPoly n (δ / t))))
        = ENNReal.ofReal (logPoly (n+1) δ - δ) := by
      rw [setLIntegral_congr_fun measurableSet_Ioo
        (fun t ht => if_neg (not_le.mpr ht.1))]
      rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
      congr 1
      rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
        ← intervalIntegral.integral_of_le h1.le]
      have hrec := logPoly_recursion n h0 h1
      linarith
    rw [hp1, hp2, ← ENNReal.ofReal_add h0.le
      (sub_nonneg.mpr (le_logPoly (by omega) h0 h1))]
    congr 1
    ring

/-- General-r tied normal crossing: multiplicity r appears as the
    degree-(r−1) log polynomial,
    vol{x ∈ (0,1)^r : (∏ xᵢ)^{2k} < ε} = logPoly r (ε^{1/(2k)}). -/
theorem volume_crossing_tied_general {r k : ℕ} (hr : 1 ≤ r)
    (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    volume {x : Fin r → ℝ | (∀ i, x i ∈ Ioo (0:ℝ) 1)
        ∧ (∏ i, x i) ^ (2 * k) < ε}
      = ENNReal.ofReal (logPoly r (ε ^ ((1:ℝ)/(2 * k)))) := by
  have hδ0 : 0 < ε ^ ((1:ℝ)/(2 * k)) := Real.rpow_pos_of_pos h0 _
  have hδ1 : ε ^ ((1:ℝ)/(2 * k)) < 1 :=
    Real.rpow_lt_one h0.le h1 (by positivity)
  have hset : {x : Fin r → ℝ | (∀ i, x i ∈ Ioo (0:ℝ) 1)
        ∧ (∏ i, x i) ^ (2 * k) < ε}
      = cubeHyper r (ε ^ ((1:ℝ)/(2 * k))) := by
    ext x
    simp only [mem_setOf_eq, cubeHyper]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨hx, (pow_lt_iff_lt_rpow hk
        (Finset.prod_nonneg fun i _ => (hx i).1.le) h0).mp h⟩
    · rintro ⟨hx, h⟩
      exact ⟨hx, (pow_lt_iff_lt_rpow hk
        (Finset.prod_nonneg fun i _ => (hx i).1.le) h0).mpr h⟩
  rw [hset, volume_cubeHyper hr hδ0 hδ1]

/-! ### The slope at general multiplicity

The volume-scaling estimator reads λ = 1/(2k) at every tied
multiplicity: the log-polynomial modulation is squeezed between 1 and
r·(1 + x)^{r−1}, so its log contributes at most log log(1/ε) to the
log-volume, which vanishes against log ε. -/

/-- The exponential partial sum is at least its j = 0 term. -/
lemma one_le_sum_pow_div_factorial {x : ℝ} (hx : 0 ≤ x) {r : ℕ}
    (hr : 1 ≤ r) :
    (1:ℝ) ≤ ∑ j ∈ Finset.range r, x ^ j / (Nat.factorial j) := by
  calc (1:ℝ) = x ^ 0 / (Nat.factorial 0 : ℝ) := by norm_num
    _ ≤ _ := Finset.single_le_sum
        (fun j _ => div_nonneg (pow_nonneg hx j) (Nat.cast_nonneg _))
        (Finset.mem_range.mpr hr : (0:ℕ) ∈ Finset.range r)

/-- The exponential partial sum is at most r·(1 + x)^{r−1}. -/
lemma sum_pow_div_factorial_le {x : ℝ} (hx : 0 ≤ x) (r : ℕ) :
    ∑ j ∈ Finset.range r, x ^ j / (Nat.factorial j)
      ≤ r * (1 + x) ^ (r - 1) := by
  have hterm : ∀ j ∈ Finset.range r,
      x ^ j / (Nat.factorial j) ≤ (1 + x) ^ (r - 1) := by
    intro j hj
    have hj' : j ≤ r - 1 := by
      have := Finset.mem_range.mp hj
      omega
    calc x ^ j / (Nat.factorial j) ≤ x ^ j :=
          div_le_self (pow_nonneg hx j)
            (Nat.one_le_cast.mpr (Nat.factorial_pos j))
      _ ≤ (1 + x) ^ j := pow_le_pow_left₀ hx (by linarith) j
      _ ≤ (1 + x) ^ (r - 1) := pow_le_pow_right₀ (by linarith) hj'
  calc ∑ j ∈ Finset.range r, x ^ j / (Nat.factorial j)
      ≤ (Finset.range r).card • (1 + x) ^ (r - 1) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = r * (1 + x) ^ (r - 1) := by
        rw [Finset.card_range, nsmul_eq_mul]

/-- thm:multi_component_rates, general tied case: the log-volume
    slope reads λ = 1/(2k) at every multiplicity r; the degree-(r−1)
    log-polynomial factor drops out of the slope. -/
theorem crossing_tied_general_slope {r k : ℕ} (hr : 1 ≤ r)
    (hk : 1 ≤ k) :
    Tendsto (fun ε => Real.log ((volume {x : Fin r → ℝ |
          (∀ i, x i ∈ Ioo (0:ℝ) 1) ∧ (∏ i, x i) ^ (2 * k) < ε}).toReal)
        / Real.log ε)
      (𝓝[>] (0:ℝ)) (𝓝 ((1:ℝ)/(2 * k))) := by
  have hk2 : (0:ℝ) < 2 * k := by positivity
  have hu : Tendsto (fun ε : ℝ => -Real.log ε) (𝓝[>] (0:ℝ)) atTop :=
    tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero
  set c : ℝ := ((r - 1 : ℕ) : ℝ) with hc
  set S : ℝ → ℝ := fun ε => ∑ j ∈ Finset.range r,
    (-Real.log ε / (2 * k)) ^ j / (Nat.factorial j) with hSdef
  -- the lower squeeze bound tends to zero
  have hbU : Tendsto (fun u : ℝ =>
      -(Real.log r / u + c * (Real.log (1 + u / (2 * k)) / u)))
      atTop (𝓝 0) := by
    have t1 : Tendsto (fun u : ℝ => Real.log r / u) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have t2 := tendsto_log_one_add_div_atTop hk2
    have tb := t1.add (t2.const_mul c)
    rw [mul_zero, add_zero] at tb
    have := tb.neg
    rwa [neg_zero] at this
  have hb : Tendsto (fun ε : ℝ =>
      -(Real.log r / (-Real.log ε)
        + c * (Real.log (1 + (-Real.log ε) / (2 * k)) / (-Real.log ε))))
      (𝓝[>] (0:ℝ)) (𝓝 0) := hbU.comp hu
  -- squeeze the correction
  have hcorr : Tendsto (fun ε => Real.log (S ε) / Real.log ε)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hb
      (tendsto_const_nhds (x := (0:ℝ))) ?_ ?_
    · filter_upwards [eventually_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds
          (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with ε hε0 hε1
      have hε0' : (0:ℝ) < ε := hε0
      have hlog : Real.log ε < 0 := Real.log_neg hε0' hε1
      have hu0 : (0:ℝ) < -Real.log ε := by linarith
      have hx0 : (0:ℝ) ≤ -Real.log ε / (2 * k) := div_nonneg (by linarith) (by positivity)
      have hS1 : (1:ℝ) ≤ S ε := one_le_sum_pow_div_factorial hx0 hr
      have hSpos : (0:ℝ) < S ε := lt_of_lt_of_le one_pos hS1
      have hSle : S ε ≤ r * (1 + -Real.log ε / (2 * k)) ^ (r - 1) :=
        sum_pow_div_factorial_le hx0 r
      have hrpos : (0:ℝ) < (r:ℝ) := by
        exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hr
      have hbase : (0:ℝ) < 1 + -Real.log ε / (2 * k) := by linarith
      have hlogS : Real.log (S ε)
          ≤ Real.log r + c * Real.log (1 + -Real.log ε / (2 * k)) := by
        calc Real.log (S ε)
            ≤ Real.log (r * (1 + -Real.log ε / (2 * k)) ^ (r - 1)) :=
              Real.log_le_log hSpos hSle
          _ = Real.log r + c * Real.log (1 + -Real.log ε / (2 * k)) := by
              rw [Real.log_mul (ne_of_gt hrpos)
                  (ne_of_gt (pow_pos hbase _)),
                Real.log_pow, hc]
      have hdivle : Real.log (S ε) / (-Real.log ε)
          ≤ (Real.log r + c * Real.log (1 + -Real.log ε / (2 * k)))
              / (-Real.log ε) := by
        gcongr
      have heq : Real.log (S ε) / Real.log ε
          = -(Real.log (S ε) / (-Real.log ε)) := by
        rw [div_neg, neg_neg]
      rw [heq]
      have hsplit : (Real.log r
            + c * Real.log (1 + -Real.log ε / (2 * k))) / (-Real.log ε)
          = Real.log r / (-Real.log ε)
            + c * (Real.log (1 + -Real.log ε / (2 * k)) / (-Real.log ε)) := by
        rw [add_div, mul_div_assoc]
      rw [← hsplit]
      exact neg_le_neg hdivle
    · filter_upwards [eventually_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds
          (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with ε hε0 hε1
      have hε0' : (0:ℝ) < ε := hε0
      have hlog : Real.log ε < 0 := Real.log_neg hε0' hε1
      have hx0 : (0:ℝ) ≤ -Real.log ε / (2 * k) := div_nonneg (by linarith) (by positivity)
      have hS1 : (1:ℝ) ≤ S ε := one_le_sum_pow_div_factorial hx0 hr
      exact div_nonpos_of_nonneg_of_nonpos (Real.log_nonneg hS1) hlog.le
  -- assemble
  have hsum : Tendsto (fun ε : ℝ => (1:ℝ)/(2 * k)
      + Real.log (S ε) / Real.log ε)
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
  have hδ0 : (0:ℝ) < ε ^ ((1:ℝ)/(2 * k)) := Real.rpow_pos_of_pos hε0' _
  have hδ1 : ε ^ ((1:ℝ)/(2 * k)) < 1 :=
    Real.rpow_lt_one hε0'.le hε1 (by positivity)
  have hxeq : -Real.log (ε ^ ((1:ℝ)/(2 * k))) = -Real.log ε / (2 * k) := by
    rw [Real.log_rpow hε0']
    ring
  have hx0 : (0:ℝ) ≤ -Real.log ε / (2 * k) := div_nonneg (by linarith) (by positivity)
  have hS1 : (1:ℝ) ≤ S ε := one_le_sum_pow_div_factorial hx0 hr
  have hSpos : (0:ℝ) < S ε := lt_of_lt_of_le one_pos hS1
  have hSeq : logPoly r (ε ^ ((1:ℝ)/(2 * k)))
      = ε ^ ((1:ℝ)/(2 * k)) * S ε := by
    rw [logPoly, hSdef]
    simp only [hxeq]
  rw [volume_crossing_tied_general hr hk hε0' hε1,
    ENNReal.toReal_ofReal (logPoly_nonneg r hδ0 hδ1), hSeq,
    Real.log_mul (ne_of_gt hδ0) (ne_of_gt hSpos),
    Real.log_rpow hε0', add_div, mul_div_assoc,
    div_self (ne_of_lt hlog), mul_one]

/-! ### The Jacobian exponent as a prior weight

rem:multi_component_h_i leaves Watanabe's Jacobian exponents hᵢ as a
prior choice: with the weight x^h on the slice the RLCT reads
(h+1)/(2k). On the one-dimensional normal form this is exact: the
weighted volume of {x ∈ (0,1) : x^{2k} < ε} under the density x^h is
ε^{(h+1)/(2k)}/(h+1), and its log-slope is (h+1)/(2k). -/

section WeightedSlice

/-- The positive half of the sublevel set is the interval
    (0, ε^{1/(2k)}) below threshold one. -/
lemma sublevel_pow_pos_eq_Ioo {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε)
    (h1 : ε < 1) :
    {x : ℝ | x ∈ Ioo (0:ℝ) 1 ∧ x ^ (2 * k) < ε}
      = Ioo 0 (ε ^ ((1:ℝ) / (2 * k))) := by
  have hδ1 : ε ^ ((1:ℝ) / (2 * k)) < 1 :=
    Real.rpow_lt_one h0.le h1 (by positivity)
  ext x
  simp only [mem_setOf_eq, mem_Ioo]
  constructor
  · rintro ⟨⟨hx0, -⟩, hlt⟩
    refine ⟨hx0, ?_⟩
    have := sublevel_pow_eq_Ioo hk h0
    have hmem : x ∈ {t : ℝ | t ^ (2 * k) < ε} := hlt
    rw [this] at hmem
    exact hmem.2
  · rintro ⟨hx0, hxδ⟩
    refine ⟨⟨hx0, lt_trans hxδ hδ1⟩, ?_⟩
    have hmem : x ∈ Ioo (-(ε ^ ((1:ℝ)/(2 * k)))) (ε ^ ((1:ℝ)/(2 * k))) :=
      ⟨by linarith [Real.rpow_pos_of_pos h0 ((1:ℝ)/(2 * k))], hxδ⟩
    rw [← sublevel_pow_eq_Ioo hk h0] at hmem
    exact hmem

/-- The weighted slice volume: under the density x^h the sublevel
    volume is ε^{(h+1)/(2k)}/(h+1). -/
theorem weighted_volume_sublevel_pow {k h : ℕ} (hk : 1 ≤ k) {ε : ℝ}
    (h0 : 0 < ε) (h1 : ε < 1) :
    ∫ x in {x : ℝ | x ∈ Ioo (0:ℝ) 1 ∧ x ^ (2 * k) < ε}, x ^ h
      = (1 / ((h:ℝ) + 1)) * ε ^ (((h:ℝ) + 1) / (2 * k)) := by
  rw [sublevel_pow_pos_eq_Ioo hk h0 h1]
  have hδ0 : 0 < ε ^ ((1:ℝ) / (2 * k)) := Real.rpow_pos_of_pos h0 _
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le hδ0.le, integral_pow]
  have hpow : (ε ^ ((1:ℝ) / (2 * k))) ^ (h + 1)
      = ε ^ (((h:ℝ) + 1) / (2 * k)) := by
    rw [← Real.rpow_natCast _ (h + 1), ← Real.rpow_mul h0.le]
    congr 1
    push_cast
    ring
  rw [zero_pow (by omega), sub_zero, hpow]
  ring

/-- The weighted slope reads (h+1)/(2k): the Jacobian exponent enters
    the RLCT exactly as Watanabe's formula says. -/
theorem weighted_slice_rlct_slope {k h : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun ε =>
      Real.log (∫ x in {x : ℝ | x ∈ Ioo (0:ℝ) 1 ∧ x ^ (2 * k) < ε}, x ^ h)
        / Real.log ε)
      (𝓝[>] (0:ℝ)) (𝓝 (((h:ℝ) + 1) / (2 * k))) := by
  refine (tendsto_log_div_log_of_rpow (C := 1 / ((h:ℝ) + 1))
    (by positivity)).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds
      (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with ε hε0 hε1
  rw [weighted_volume_sublevel_pow hk hε0 hε1]

end WeightedSlice

/-! ### The weighted tied law, one-dimensional recursion

With the prior weight x^h on every coordinate the tied crossing's
weighted volume is (h+1)^{−r}·P_r(δ^{h+1}): the substitution
s = t^{h+1} carries the weighted slice integral onto the unweighted
recursion at threshold δ^{h+1}. This section is the 1-D step. -/

section WeightedTiedRecursion

/-- The slice profile t ↦ P_r(δ/t) is continuous on [δ, 1]. -/
lemma continuousOn_logPoly_div (r : ℕ) {δ : ℝ} (h0 : 0 < δ) :
    ContinuousOn (fun t : ℝ => logPoly r (δ / t)) (Icc δ 1) := by
  have htne : ∀ t ∈ Icc δ (1:ℝ), t ≠ 0 :=
    fun t ht => ne_of_gt (lt_of_lt_of_le h0 ht.1)
  have hdiv : ContinuousOn (fun t : ℝ => δ / t) (Icc δ 1) :=
    continuousOn_const.div continuousOn_id htne
  have hmaps : Set.MapsTo (fun t : ℝ => δ / t) (Icc δ 1) {x : ℝ | x ≠ 0} :=
    fun t ht => ne_of_gt (div_pos h0 (lt_of_lt_of_le h0 ht.1))
  unfold logPoly
  apply hdiv.mul
  apply continuousOn_finset_sum
  intro j _
  exact (((Real.continuousOn_log.comp hdiv hmaps).neg).pow j).div_const _

/-- The weighted slice integral reduces to the unweighted recursion
    at threshold δ^{h+1}:
    ∫_δ^1 t^h·P_r((δ/t)^{h+1}) dt = (P_{r+1}(δ^{h+1}) − δ^{h+1})/(h+1). -/
theorem weighted_slice_recursion (r h : ℕ) {δ : ℝ} (h0 : 0 < δ)
    (h1 : δ < 1) :
    ∫ t in δ..1, t ^ h * logPoly r ((δ / t) ^ (h + 1))
      = (logPoly (r + 1) (δ ^ (h + 1)) - δ ^ (h + 1)) / ((h:ℝ) + 1) := by
  have hδ0 : 0 < δ ^ (h + 1) := pow_pos h0 _
  have hδ1 : δ ^ (h + 1) < 1 := pow_lt_one₀ h0.le h1 (by omega)
  have hh : ((h:ℝ) + 1) ≠ 0 := by positivity
  -- the substitution s = t^{h+1}
  have hderiv : ∀ t ∈ Set.uIcc δ (1:ℝ),
      HasDerivAt (fun t : ℝ => t ^ (h + 1)) (((h:ℝ) + 1) * t ^ h) t := by
    intro t _
    have := hasDerivAt_pow (h + 1) t
    simpa using this
  have hcont' : ContinuousOn (fun t : ℝ => ((h:ℝ) + 1) * t ^ h)
      (Set.uIcc δ 1) := by fun_prop
  have himage : (fun t : ℝ => t ^ (h + 1)) '' Set.uIcc δ 1 ⊆ Icc (δ ^ (h + 1)) 1 := by
    rintro s ⟨t, ht, rfl⟩
    rw [Set.uIcc_of_le h1.le] at ht
    exact ⟨pow_le_pow_left₀ h0.le ht.1 _, pow_le_one₀ (le_trans h0.le ht.1) ht.2⟩
  have hg : ContinuousOn (fun s : ℝ => logPoly r (δ ^ (h + 1) / s))
      ((fun t : ℝ => t ^ (h + 1)) '' Set.uIcc δ 1) :=
    (continuousOn_logPoly_div r hδ0).mono himage
  have hsub := intervalIntegral.integral_comp_mul_deriv' hderiv hcont' hg
  -- identify the integrands
  have hint : ∀ t ∈ Set.uIcc δ (1:ℝ),
      t ^ h * logPoly r ((δ / t) ^ (h + 1))
        = (1 / ((h:ℝ) + 1))
          * (((fun s : ℝ => logPoly r (δ ^ (h + 1) / s))
              ∘ (fun t : ℝ => t ^ (h + 1))) t * (((h:ℝ) + 1) * t ^ h)) := by
    intro t ht
    rw [Set.uIcc_of_le h1.le] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le h0 ht.1)
    simp only [Function.comp]
    rw [div_pow]
    field_simp
  rw [intervalIntegral.integral_congr hint, intervalIntegral.integral_const_mul,
    hsub, one_pow]
  have hrec := logPoly_recursion r hδ0 hδ1
  rw [show ∫ x in δ ^ (h + 1)..1, logPoly r (δ ^ (h + 1) / x)
      = logPoly (r + 1) (δ ^ (h + 1)) - δ ^ (h + 1) by linarith]
  ring

end WeightedTiedRecursion

/-! ### The weighted tied law at every multiplicity

With the prior weight ∏ xᵢ^h the tied crossing's weighted volume is
(h+1)^{−r}·P_r(δ^{h+1}): the same Fubini induction as the unweighted
law, with the weighted slice integral reduced by the substitution
s = t^{h+1} to the unweighted recursion at threshold δ^{h+1}. -/

section WeightedTiedLaw

/-- The weighted unit cube: ∫_{(0,1)^n} ∏ yᵢ^h = (h+1)^{−n}. -/
lemma weighted_unitCube (n h : ℕ) :
    ∫ y in {y : Fin n → ℝ | ∀ i, y i ∈ Ioo (0:ℝ) 1}, ∏ i, y i ^ h
      = (1 / ((h:ℝ) + 1)) ^ n := by
  rw [show {y : Fin n → ℝ | ∀ i, y i ∈ Ioo (0:ℝ) 1}
      = Set.pi univ fun _ => Ioo (0:ℝ) 1 from by ext y; simp,
    MeasureTheory.volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun _ (u : ℝ) => u ^ h)]
  have h1 : ∫ u in Ioo (0:ℝ) 1, u ^ h = 1 / ((h:ℝ) + 1) := by
    have := integral_pow_Ioo (k := h + 1) (by omega) (δ := (1:ℝ)) zero_le_one
    rw [Nat.add_sub_cancel, one_pow] at this
    rw [this]
    push_cast
    ring
  simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The weighted tied law:
    ∫_{x ∈ (0,1)^r, ∏ xᵢ < δ} ∏ xᵢ^h = (h+1)^{−r}·P_r(δ^{h+1}). -/
theorem weighted_volume_cubeHyper (h : ℕ) :
    ∀ {r : ℕ}, 1 ≤ r → ∀ {δ : ℝ}, 0 < δ → δ < 1 →
      ∫ x in cubeHyper r δ, ∏ i, x i ^ h
        = (1 / ((h:ℝ) + 1)) ^ r * logPoly r (δ ^ (h + 1)) := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    intro δ h0 h1
    have hset : cubeHyper 1 δ
        = Set.pi univ fun _ : Fin 1 => Ioo (0:ℝ) δ := by
      ext x
      simp only [cubeHyper, mem_setOf_eq, Set.mem_pi, mem_univ,
        forall_const, mem_Ioo, Fin.prod_univ_one]
      constructor
      · rintro ⟨hall, hprod⟩ i
        rw [Subsingleton.elim i 0]
        exact ⟨(hall 0).1, hprod⟩
      · intro hx
        refine ⟨fun i => ?_, (hx 0).2⟩
        rw [Subsingleton.elim i 0]
        exact ⟨(hx 0).1, lt_trans (hx 0).2 h1⟩
    rw [hset, MeasureTheory.volume_pi, Measure.restrict_pi_pi,
      integral_fintype_prod_eq_prod (fun _ (u : ℝ) => u ^ h)]
    have h1' := integral_pow_Ioo (k := h + 1) (by omega) h0.le
    rw [Nat.add_sub_cancel] at h1'
    simp only [h1', Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one,
      logPoly_one]
    push_cast
    ring
  | succ n hn ih =>
    intro δ h0 h1
    set c : ℝ := 1 / ((h:ℝ) + 1) with hc
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
      with he
    set A : Set (ℝ × (Fin n → ℝ)) :=
      {p | p.1 ∈ Ioo (0:ℝ) 1 ∧ (∀ i, p.2 i ∈ Ioo (0:ℝ) 1)
        ∧ p.1 * ∏ i, p.2 i < δ} with hA
    set g : ℝ × (Fin n → ℝ) → ℝ := fun p => p.1 ^ h * ∏ i, p.2 i ^ h with hg
    have hAmeas : MeasurableSet A := by
      have h1 : MeasurableSet {p : ℝ × (Fin n → ℝ) | p.1 ∈ Ioo (0:ℝ) 1} :=
        measurable_fst measurableSet_Ioo
      have h2 : MeasurableSet {p : ℝ × (Fin n → ℝ) | ∀ i, p.2 i ∈ Ioo (0:ℝ) 1} := by
        rw [show {p : ℝ × (Fin n → ℝ) | ∀ i, p.2 i ∈ Ioo (0:ℝ) 1}
            = ⋂ i, (fun p : ℝ × (Fin n → ℝ) => p.2 i) ⁻¹' Ioo (0:ℝ) 1
            from by ext p; simp]
        exact MeasurableSet.iInter fun i =>
          ((measurable_pi_apply i).comp measurable_snd) measurableSet_Ioo
      have h3 : MeasurableSet {p : ℝ × (Fin n → ℝ) | p.1 * ∏ i, p.2 i < δ} :=
        measurableSet_lt
          (measurable_fst.mul (Finset.univ.measurable_prod fun i _ =>
            (measurable_pi_apply i).comp measurable_snd))
          measurable_const
      exact h1.inter (h2.inter h3)
    have hgm : Measurable g := by
      simp only [hg]
      exact (measurable_fst.pow_const h).mul
        (Finset.univ.measurable_prod fun i _ =>
          ((measurable_pi_apply i).comp measurable_snd).pow_const h)
    have hpre : cubeHyper (n+1) δ = e ⁻¹' A := by
      ext x
      simp only [cubeHyper, mem_setOf_eq, mem_preimage, he,
        MeasurableEquiv.piFinSuccAbove_apply, hA]
      rw [Fin.forall_fin_succ, Fin.prod_univ_succ]
      tauto
    have hfun : ∀ x : Fin (n+1) → ℝ, ∏ i, x i ^ h = g (e x) := by
      intro x
      rw [Fin.prod_univ_succ]
      rfl
    have hmp := MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin (n+1) => ℝ) 0
    rw [hpre, show (fun x : Fin (n+1) → ℝ => ∏ i, x i ^ h) = fun x => g (e x)
      from funext hfun]
    rw [hmp.setIntegral_preimage_emb e.measurableEmbedding g A,
      MeasureTheory.Measure.volume_eq_prod]
    -- bound and integrability on A
    have hAsub : A ⊆ Ioo (0:ℝ) 1 ×ˢ {y : Fin n → ℝ | ∀ i, y i ∈ Ioo (0:ℝ) 1} :=
      fun p hp => ⟨hp.1, hp.2.1⟩
    have hAfin : ((volume : Measure ℝ).prod volume) A ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono hAsub)
      rw [Measure.prod_prod, Real.volume_Ioo, volume_unitCube]
      simp
    have hgbound : ∀ p ∈ A, |g p| ≤ 1 := by
      intro p hp
      simp only [hg]
      have h1 : 0 ≤ p.1 ^ h := pow_nonneg hp.1.1.le h
      have h2 : p.1 ^ h ≤ 1 := pow_le_one₀ hp.1.1.le hp.1.2.le
      have h3 : 0 ≤ ∏ i, p.2 i ^ h :=
        Finset.prod_nonneg fun i _ => pow_nonneg (hp.2.1 i).1.le h
      have h4 : ∏ i, p.2 i ^ h ≤ 1 :=
        Finset.prod_le_one (fun i _ => pow_nonneg (hp.2.1 i).1.le h)
          (fun i _ => pow_le_one₀ (hp.2.1 i).1.le (hp.2.1 i).2.le)
      rw [abs_of_nonneg (mul_nonneg h1 h3)]
      nlinarith
    have hint : IntegrableOn g A ((volume : Measure ℝ).prod volume) := by
      refine Measure.integrableOn_of_bounded (M := 1) hAfin
        hgm.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem hAmeas] with p hp
      rw [Real.norm_eq_abs]
      exact hgbound p hp
    rw [← integral_indicator hAmeas,
      integral_prod _ ((integrable_indicator_iff hAmeas).mpr hint)]
    -- the slices
    have hslice : ∀ t : ℝ,
        (∫ y, A.indicator g (t, y) ∂(volume : Measure (Fin n → ℝ)))
          = Set.indicator (Ioo (0:ℝ) 1)
              (fun t => t ^ h * (if t ≤ δ then c ^ n
                else c ^ n * logPoly n ((δ / t) ^ (h + 1)))) t := by
      intro t
      have hind : ∀ y, A.indicator g (t, y)
          = (Prod.mk t ⁻¹' A).indicator (fun y => g (t, y)) y := by
        intro y
        rfl
      simp_rw [hind]
      rw [integral_indicator (measurable_prodMk_left hAmeas)]
      by_cases ht : t ∈ Ioo (0:ℝ) 1
      · rw [Set.indicator_of_mem ht]
        by_cases htδ : t ≤ δ
        · rw [if_pos htδ]
          have hfull : Prod.mk t ⁻¹' A
              = {y : Fin n → ℝ | ∀ i, y i ∈ Ioo (0:ℝ) 1} := by
            ext y
            simp only [mem_preimage, hA, mem_setOf_eq]
            constructor
            · rintro ⟨-, hy, -⟩
              exact hy
            · intro hy
              refine ⟨ht, hy, ?_⟩
              set i0 : Fin n := ⟨0, by omega⟩ with hi0
              have hrest : ∏ i ∈ Finset.univ.erase i0, y i ≤ 1 :=
                Finset.prod_le_one (fun i _ => (hy i).1.le)
                  (fun i _ => (hy i).2.le)
              have hprod : ∏ i, y i ≤ y i0 := by
                rw [← Finset.mul_prod_erase Finset.univ y
                  (Finset.mem_univ i0)]
                calc y i0 * ∏ i ∈ Finset.univ.erase i0, y i
                    ≤ y i0 * 1 :=
                      mul_le_mul_of_nonneg_left hrest (hy i0).1.le
                  _ = y i0 := mul_one _
              have h1' : t * ∏ i, y i ≤ t * y i0 :=
                mul_le_mul_of_nonneg_left hprod ht.1.le
              have h2' : t * y i0 < t * 1 :=
                mul_lt_mul_of_pos_left (hy i0).2 ht.1
              rw [mul_one] at h2'
              linarith
          rw [hfull]
          simp only [hg]
          rw [integral_const_mul, weighted_unitCube]
        · rw [if_neg htδ]
          push Not at htδ
          have hcube : Prod.mk t ⁻¹' A = cubeHyper n (δ / t) := by
            ext y
            simp only [mem_preimage, hA, mem_setOf_eq, cubeHyper]
            constructor
            · rintro ⟨-, hy, hlt⟩
              refine ⟨hy, ?_⟩
              rwa [lt_div_iff₀ ht.1, mul_comm]
            · rintro ⟨hy, hlt⟩
              refine ⟨ht, hy, ?_⟩
              rwa [lt_div_iff₀ ht.1, mul_comm] at hlt
          rw [hcube]
          simp only [hg]
          rw [integral_const_mul, ih (div_pos h0 ht.1) ((div_lt_one ht.1).mpr htδ)]
      · rw [Set.indicator_of_notMem ht]
        have hempty : Prod.mk t ⁻¹' A = ∅ := by
          ext y
          simp only [mem_preimage, hA, mem_setOf_eq,
            mem_empty_iff_false, iff_false]
          rintro ⟨ht', -, -⟩
          exact ht ht'
        rw [hempty, Measure.restrict_empty, integral_zero_measure]
    simp_rw [hslice]
    rw [integral_indicator measurableSet_Ioo,
      ← Set.Ioc_union_Ioo_eq_Ioo h0.le h1]
    have hdisj : Disjoint (Ioc (0:ℝ) δ) (Ioo δ 1) := by
      rw [Set.disjoint_left]
      rintro x hx1 hx2
      exact absurd hx1.2 (not_le.mpr hx2.1)
    -- the two pieces
    have hp1 : ∫ t in Ioc (0:ℝ) δ, t ^ h * (if t ≤ δ then c ^ n
        else c ^ n * logPoly n ((δ / t) ^ (h + 1)))
        = c ^ n * (δ ^ (h + 1) / ((h:ℝ) + 1)) := by
      rw [setIntegral_congr_fun measurableSet_Ioc
        (fun t ht => by rw [if_pos ht.2])]
      rw [← intervalIntegral.integral_of_le h0.le,
        intervalIntegral.integral_mul_const, integral_pow,
        zero_pow (by omega), sub_zero]
      ring
    have hcont2 : ContinuousOn (fun t : ℝ => t ^ h * logPoly n ((δ / t) ^ (h + 1)))
        (Icc δ 1) := by
      have hpow : ContinuousOn (fun t : ℝ => t ^ (h + 1)) (Icc δ 1) := by
        fun_prop
      have hmaps : Set.MapsTo (fun t : ℝ => t ^ (h + 1)) (Icc δ 1)
          (Icc (δ ^ (h + 1)) 1) := fun t ht =>
        ⟨pow_le_pow_left₀ h0.le ht.1 _, pow_le_one₀ (le_trans h0.le ht.1) ht.2⟩
      have hlog := (continuousOn_logPoly_div n (pow_pos h0 (h + 1))).comp hpow hmaps
      have heq : ∀ t ∈ Icc δ (1:ℝ), logPoly n ((δ / t) ^ (h + 1))
          = logPoly n (δ ^ (h + 1) / t ^ (h + 1)) := by
        intro t _
        rw [div_pow]
      refine ContinuousOn.mul (by fun_prop) ?_
      exact hlog.congr heq
    have hp2 : ∫ t in Ioo δ 1, t ^ h * (if t ≤ δ then c ^ n
        else c ^ n * logPoly n ((δ / t) ^ (h + 1)))
        = c ^ n * ((logPoly (n + 1) (δ ^ (h + 1)) - δ ^ (h + 1)) / ((h:ℝ) + 1)) := by
      rw [setIntegral_congr_fun measurableSet_Ioo
        (fun t ht => by rw [if_neg (not_le.mpr ht.1)])]
      rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
        ← intervalIntegral.integral_of_le h1.le]
      have hre : ∀ t, t ^ h * (c ^ n * logPoly n ((δ / t) ^ (h + 1)))
          = c ^ n * (t ^ h * logPoly n ((δ / t) ^ (h + 1))) := fun t => by ring
      simp_rw [hre]
      rw [intervalIntegral.integral_const_mul, weighted_slice_recursion n h h0 h1]
    have hi1 : IntegrableOn (fun t : ℝ => t ^ h * (if t ≤ δ then c ^ n
        else c ^ n * logPoly n ((δ / t) ^ (h + 1)))) (Ioc 0 δ) := by
      refine (IntegrableOn.congr_fun ?_ (fun t ht => by rw [if_pos ht.2])
        measurableSet_Ioc)
      exact (continuous_pow h |>.mul continuous_const).continuousOn.integrableOn_Icc
        |>.mono_set Ioc_subset_Icc_self
    have hi2 : IntegrableOn (fun t : ℝ => t ^ h * (if t ≤ δ then c ^ n
        else c ^ n * logPoly n ((δ / t) ^ (h + 1)))) (Ioo δ 1) := by
      refine (IntegrableOn.congr_fun ?_ (fun t ht => by rw [if_neg (not_le.mpr ht.1)])
        measurableSet_Ioo)
      have hre : (fun t : ℝ => t ^ h * (c ^ n * logPoly n ((δ / t) ^ (h + 1))))
          = fun t => c ^ n * (t ^ h * logPoly n ((δ / t) ^ (h + 1))) := by
        funext t
        ring
      rw [hre]
      exact (hcont2.const_smul (c ^ n)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    rw [setIntegral_union hdisj measurableSet_Ioo hi1 hi2, hp1, hp2]
    rw [pow_succ]
    have hh : ((h:ℝ) + 1) ≠ 0 := by positivity
    simp only [hc]
    field_simp
    have hne : (1:ℝ) + h ≠ 0 := by positivity
    have key : (h:ℝ) * (1 + (h:ℝ))⁻¹ + (1 + (h:ℝ))⁻¹ = 1 := by
      field_simp
      ring
    linear_combination (-((1 + (h:ℝ))⁻¹ ^ n * logPoly (n + 1) (δ ^ h * δ))) * key

end WeightedTiedLaw

end DeadDirections
