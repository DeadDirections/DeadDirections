/-
  prop:volume_multi: the (G⁺) Fisher-volume refinement at the model.

  Under the graded-Gram non-degeneracy (G⁺) the Fisher volume form
  factorises on the polydisc, √det F = Θ(∏|uᵢ|^{kᵢ−1}), and the
  polydisc Fisher volume is the product of the one-direction laws,
  Θ(∏ M^{−kᵢ/(2(kᵢ−1))}). The additive normal form alone does not
  fix the exponent: the twisted mean map has K = u₁⁴ + u₂⁴ exactly
  while √det F = 4|u₁³ − u₂³| degenerates on the diagonal, and its
  polydisc volume scales as M^{−5/2} against the product formula's
  M^{−2}. This module carries both halves at the model: the exact
  factorised polydisc law, and the twisted density's δ⁵ scaling with
  a positive constant against the factorised δ⁴ at k = (2, 2).
-/
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import DeadDirections.FisherDecay

namespace DeadDirections

open MeasureTheory Set Filter Topology

section Factorised

/-- One direction: ∫₀^δ u^{k−1} du = δ^k/k. -/
lemma integral_pow_Ioo {k : ℕ} (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∫ u in Ioo (0:ℝ) δ, u ^ (k - 1) = δ ^ k / k := by
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le hδ, integral_pow,
    show k - 1 + 1 = k from by omega, zero_pow (by omega), sub_zero]
  have hcast : ((k - 1 : ℕ) : ℝ) + 1 = k := by
    push_cast [Nat.cast_sub (show 1 ≤ k by omega)]
    ring
  rw [hcast]

/-- prop:volume_multi under (G⁺), two directions: the factorised
    Fisher density u₁^{k₁−1}·u₂^{k₂−1} integrates over the positive
    polydisc to the product of the one-direction laws. -/
theorem polydisc_volume_factorised {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁)
    (hk₂ : 1 ≤ k₂) {δ₁ δ₂ : ℝ} (h₁ : 0 ≤ δ₁) (h₂ : 0 ≤ δ₂) :
    ∫ z in Ioo (0:ℝ) δ₁ ×ˢ Ioo (0:ℝ) δ₂, z.1 ^ (k₁ - 1) * z.2 ^ (k₂ - 1)
        ∂((volume : Measure ℝ).prod volume)
      = (δ₁ ^ k₁ / k₁) * (δ₂ ^ k₂ / k₂) := by
  calc ∫ z in Ioo (0:ℝ) δ₁ ×ˢ Ioo (0:ℝ) δ₂,
          z.1 ^ (k₁ - 1) * z.2 ^ (k₂ - 1) ∂((volume : Measure ℝ).prod volume)
      = (∫ u in Ioo (0:ℝ) δ₁, u ^ (k₁ - 1))
          * ∫ u in Ioo (0:ℝ) δ₂, u ^ (k₂ - 1) :=
        setIntegral_prod_mul (fun u : ℝ => u ^ (k₁ - 1))
          (fun u : ℝ => u ^ (k₂ - 1)) _ _
    _ = (δ₁ ^ k₁ / k₁) * (δ₂ ^ k₂ / k₂) := by
        rw [integral_pow_Ioo hk₁ h₁, integral_pow_Ioo hk₂ h₂]

/-- The polydisc radius c·M^{−1/(2(k−1))} raised to the k-th power is
    c^k·M^{−k/(2(k−1))}: the product law's exponent per direction. -/
lemma polydisc_radius_pow {k : ℕ} (hk : 2 ≤ k) {c M : ℝ} (_hc : 0 ≤ c)
    (hM : 0 < M) :
    (c * M ^ (-(1 / (2 * ((k:ℝ) - 1))))) ^ k
      = c ^ k * M ^ (-((k:ℝ) / (2 * ((k:ℝ) - 1)))) := by
  have hkm : (0:ℝ) < (k:ℝ) - 1 := by
    have : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  rw [mul_pow, ← Real.rpow_natCast (M ^ _) k, ← Real.rpow_mul hM.le]
  congr 2
  field_simp

end Factorised

section Twisted

/-- The twisted density |u₁³ − u₂³| on the positive polydisc of
    radius δ scales as δ⁵ times its unit-square integral: one power
    above the factorised δ⁴ at k = (2, 2). -/
theorem twisted_polydisc_scaling {δ : ℝ} (hδ : 0 < δ) :
    ∫ z in Ioo (0:ℝ) δ ×ˢ Ioo (0:ℝ) δ, |z.1 ^ 3 - z.2 ^ 3|
        ∂((volume : Measure ℝ).prod volume)
      = δ ^ 5 * ∫ z in Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1, |z.1 ^ 3 - z.2 ^ 3|
        ∂((volume : Measure ℝ).prod volume) := by
  have hcont : Continuous fun z : ℝ × ℝ => |z.1 ^ 3 - z.2 ^ 3| := by
    fun_prop
  have hint : ∀ r : ℝ, IntegrableOn (fun z : ℝ × ℝ => |z.1 ^ 3 - z.2 ^ 3|)
      (Ioo (0:ℝ) r ×ˢ Ioo (0:ℝ) r) ((volume : Measure ℝ).prod volume) := by
    intro r
    have hK : IntegrableOn (fun z : ℝ × ℝ => |z.1 ^ 3 - z.2 ^ 3|)
        (Icc (0:ℝ) r ×ˢ Icc (0:ℝ) r) ((volume : Measure ℝ).prod volume) :=
      hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact hK.mono_set (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [setIntegral_prod _ (hint δ), setIntegral_prod _ (hint 1)]
  -- inner substitution y = δ w, then outer x = δ v
  have key : ∀ g : ℝ → ℝ, (∫ y in Ioo (0:ℝ) δ, g y)
      = δ * ∫ w in Ioo (0:ℝ) 1, g (δ * w) := by
    intro g
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
      setIntegral_congr_set Ioo_ae_eq_Ioc,
      ← intervalIntegral.integral_of_le hδ.le,
      ← intervalIntegral.integral_of_le zero_le_one]
    have h := intervalIntegral.smul_integral_comp_mul_left (a := (0:ℝ)) (b := 1) g δ
    rw [mul_zero, mul_one, smul_eq_mul] at h
    exact h.symm
  have hinner : ∀ x : ℝ, (∫ y in Ioo (0:ℝ) δ, |x ^ 3 - y ^ 3|)
      = δ * ∫ w in Ioo (0:ℝ) 1, |x ^ 3 - (δ * w) ^ 3| := fun x => key _
  simp_rw [hinner]
  rw [key fun x : ℝ => δ * ∫ w in Ioo (0:ℝ) 1, |x ^ 3 - (δ * w) ^ 3|]
  have hhom : ∀ v w : ℝ, |(δ * v) ^ 3 - (δ * w) ^ 3| = δ ^ 3 * |v ^ 3 - w ^ 3| := by
    intro v w
    rw [show (δ * v) ^ 3 - (δ * w) ^ 3 = δ ^ 3 * (v ^ 3 - w ^ 3) by ring,
      abs_mul, abs_of_pos (by positivity)]
  simp_rw [hhom, integral_const_mul]
  ring

/-- The unit-square constant of the twisted density is positive:
    on the sub-box [3/4, 7/8] × [1/4, 1/2] the density is at least
    19/64. -/
theorem twisted_unit_constant_pos :
    0 < ∫ z in Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1, |z.1 ^ 3 - z.2 ^ 3|
        ∂((volume : Measure ℝ).prod volume) := by
  have hcont : Continuous fun z : ℝ × ℝ => |z.1 ^ 3 - z.2 ^ 3| := by
    fun_prop
  set S : Set (ℝ × ℝ) := Icc (3/4 : ℝ) (7/8) ×ˢ Icc (1/4 : ℝ) (1/2) with hS
  have hSsub : S ⊆ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1 := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩,
      ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩
  have hint : IntegrableOn (fun z : ℝ × ℝ => |z.1 ^ 3 - z.2 ^ 3|)
      (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) ((volume : Measure ℝ).prod volume) := by
    have hK : IntegrableOn (fun z : ℝ × ℝ => |z.1 ^ 3 - z.2 ^ 3|)
        (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) ((volume : Measure ℝ).prod volume) :=
      hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact hK.mono_set (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hSmeas : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hvolS : ((volume : Measure ℝ).prod volume) S = ENNReal.ofReal (1/32) := by
    rw [hS, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hlow : ∀ z ∈ S, (19/64 : ℝ) ≤ |z.1 ^ 3 - z.2 ^ 3| := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hx3 : (27/64 : ℝ) ≤ x ^ 3 := by
      have : (3/4 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx.1 3
      linarith [this]
    have hy3 : y ^ 3 ≤ 1/8 := by
      have : y ^ 3 ≤ (1/2 : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith [hy.1]) hy.2 3
      linarith [this]
    rw [abs_of_nonneg (by linarith)]
    linarith
  have h1 : (19/64 : ℝ) * (((volume : Measure ℝ).prod volume) S).toReal
      ≤ ∫ z in S, |z.1 ^ 3 - z.2 ^ 3| ∂((volume : Measure ℝ).prod volume) := by
    have h := setIntegral_ge_of_const_le_real (f := fun z : ℝ × ℝ => |z.1 ^ 3 - z.2 ^ 3|)
      hSmeas (by rw [hvolS]; exact ENNReal.ofReal_ne_top) hlow (hint.mono_set hSsub)
    rwa [measureReal_def] at h
  have h2 : ∫ z in S, |z.1 ^ 3 - z.2 ^ 3| ∂((volume : Measure ℝ).prod volume)
      ≤ ∫ z in Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1, |z.1 ^ 3 - z.2 ^ 3|
        ∂((volume : Measure ℝ).prod volume) :=
    setIntegral_mono_set hint
      (Filter.Eventually.of_forall fun z => abs_nonneg _)
      (Filter.Eventually.of_forall hSsub)
  rw [hvolS, ENNReal.toReal_ofReal (by norm_num)] at h1
  linarith

/-- At k = (2, 2) the polydisc radius is M^{−1/2}: the factorised law
    reads M^{−2}/4 while the twisted density reads C·M^{−5/2} with
    C > 0, so the exponents differ and (G⁺) is load-bearing. -/
theorem twisted_vs_factorised {M : ℝ} (hM : 0 < M) :
    (∫ z in Ioo (0:ℝ) (M ^ (-(1/2 : ℝ))) ×ˢ Ioo (0:ℝ) (M ^ (-(1/2 : ℝ))),
        z.1 ^ (2 - 1) * z.2 ^ (2 - 1) ∂((volume : Measure ℝ).prod volume))
      = M ^ (-(2 : ℝ)) / 4
    ∧ (∫ z in Ioo (0:ℝ) (M ^ (-(1/2 : ℝ))) ×ˢ Ioo (0:ℝ) (M ^ (-(1/2 : ℝ))),
        |z.1 ^ 3 - z.2 ^ 3| ∂((volume : Measure ℝ).prod volume))
      = M ^ (-(5/2 : ℝ)) * ∫ z in Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1,
          |z.1 ^ 3 - z.2 ^ 3| ∂((volume : Measure ℝ).prod volume) := by
  have hδ : 0 < M ^ (-(1/2 : ℝ)) := Real.rpow_pos_of_pos hM _
  constructor
  · rw [polydisc_volume_factorised (k₁ := 2) (k₂ := 2) one_le_two one_le_two hδ.le hδ.le]
    have h2 : (M ^ (-(1/2 : ℝ))) ^ (2:ℕ) = M ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_natCast (M ^ (-(1/2 : ℝ))) 2, ← Real.rpow_mul hM.le]
      norm_num
    have h4 : M ^ (-(2 : ℝ)) = (M ^ (-(1 : ℝ))) ^ (2:ℕ) := by
      rw [← Real.rpow_natCast (M ^ (-(1 : ℝ))) 2, ← Real.rpow_mul hM.le]
      norm_num
    rw [h2, h4]
    push_cast
    ring
  · rw [twisted_polydisc_scaling hδ, ← Real.rpow_natCast _ 5,
      ← Real.rpow_mul hM.le]
    norm_num

end Twisted

section FactorisedPi

/-- prop:volume_multi under (G⁺) at every r: the factorised density
    ∏ uᵢ^{kᵢ−1} integrates over the positive polydisc to the product
    of the one-direction laws. -/
theorem polydisc_volume_factorised_pi {r : ℕ} (k : Fin r → ℕ)
    (hk : ∀ i, 1 ≤ k i) (δ : Fin r → ℝ) (hδ : ∀ i, 0 ≤ δ i) :
    ∫ x in Set.pi Set.univ (fun i => Ioo (0:ℝ) (δ i)),
        ∏ i, x i ^ (k i - 1)
      = ∏ i, (δ i ^ k i / k i) := by
  rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun i (u : ℝ) => u ^ (k i - 1))]
  exact Finset.prod_congr rfl fun i _ => integral_pow_Ioo (hk i) (hδ i)

end FactorisedPi

end DeadDirections
