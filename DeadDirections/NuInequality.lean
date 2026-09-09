/-
  The strict inequality of the ν universality theorem.

  With π_Z ∝ exp(Zη^k − η^{2k}) and V(Z) = Var_{π_Z}[η^k], the theorem
  compares the Z-average ν_LO(k) = E_{Z ∼ N(0,2)} V(Z) with the frozen
  value V(0). Two exact facts carry the comparison. The first holds at
  every order k: integrating the derivative of η·e^{Zη^k − η^{2k}} over
  the line gives the Gamma–Stein identity c₂ = λc + (Z/2)c₁ for the
  moments c, c₁, c₂ of the tilted density, so with m(Z) = c₁/c the
  variance satisfies the Riccati relation V(Z) = λ + m(Z)(Z/2 − m(Z)).
  The second is the sign 0 ≤ m(Z) ≤ Z/2 at Z ≥ 0 for odd k: the
  substitution s = η^k turns c(Z)e^{−Z²/4} into the Gaussian average of
  |s|^{1/k − 1}, a symmetric weight decreasing in |s|, and such an
  average decreases as the Gaussian centre moves away from zero. At odd
  k therefore V(Z) > λ = V(0) for every Z ≠ 0 and the Gaussian average
  is strictly larger than the frozen value.
-/
import DeadDirections.NuFrozen
import Mathlib.MeasureTheory.Function.Jacobian

namespace DeadDirections

open MeasureTheory Set Filter Topology

section TiltedMoments

variable {k : ℕ}

/-- The tilted density is dominated by a Gaussian. -/
lemma renormDensity_le_gauss (hk : 0 < k) (Z η : ℝ) :
    renormDensity k Z η ≤ Real.exp (Z ^ 2 / 2 + 1 / 2) * Real.exp (-(η ^ 2 / 2)) := by
  unfold renormDensity
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : Z * η ^ k ≤ η ^ (2 * k) / 2 + Z ^ 2 / 2 := by
    have h2k : η ^ (2 * k) = (η ^ k) ^ 2 := by rw [pow_mul']
    rw [h2k]
    nlinarith [sq_nonneg (η ^ k - Z)]
  have h2 : -(η ^ (2 * k) / 2) ≤ 1 / 2 - η ^ 2 / 2 := by
    have hx2 : 0 ≤ η ^ 2 := sq_nonneg η
    rw [pow_mul]
    rcases le_or_gt (η ^ 2) 1 with h | h
    · have : 0 ≤ (η ^ 2) ^ k := pow_nonneg hx2 k
      linarith
    · have : η ^ 2 ≤ (η ^ 2) ^ k := le_self_pow₀ h.le hk.ne'
      linarith
  linarith

lemma renormDensity_pos (k : ℕ) (Z η : ℝ) : 0 < renormDensity k Z η := Real.exp_pos _

/-- Every polynomial moment of the tilted density is integrable. -/
theorem integrable_pow_abs_mul_renorm (hk : 0 < k) (Z : ℝ) (m : ℕ) :
    Integrable (fun η : ℝ => |η| ^ m * renormDensity k Z η) := by
  have h1 : Integrable (fun x : ℝ => x ^ m * Real.exp (-(1 / 2) * x ^ 2)) := by
    have hm : (-1:ℝ) < m := by
      have : (0:ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    refine (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2) hm).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp [Real.rpow_natCast]
  have h2 := (h1.abs).const_mul (Real.exp (Z ^ 2 / 2 + 1 / 2))
  refine h2.mono' (Continuous.aestronglyMeasurable (by unfold renormDensity; fun_prop))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg _) _) (renormDensity_pos k Z x).le),
    abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  have hle := renormDensity_le_gauss hk Z x
  have hm0 : 0 ≤ |x| ^ m := by positivity
  calc |x| ^ m * renormDensity k Z x
      ≤ |x| ^ m * (Real.exp (Z ^ 2 / 2 + 1 / 2) * Real.exp (-(x ^ 2 / 2))) := by gcongr
    _ = Real.exp (Z ^ 2 / 2 + 1 / 2) * (|x| ^ m * Real.exp (-(1 / 2) * x ^ 2)) := by
        rw [show -(1 / 2 : ℝ) * x ^ 2 = -(x ^ 2 / 2) by ring]
        ring

theorem integrable_pow_mul_renorm (hk : 0 < k) (Z : ℝ) (m : ℕ) :
    Integrable (fun η : ℝ => η ^ m * renormDensity k Z η) := by
  refine (integrable_pow_abs_mul_renorm hk Z m).mono'
    (Continuous.aestronglyMeasurable (by unfold renormDensity; fun_prop))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (renormDensity_pos k Z x)]

theorem integrable_renorm (hk : 0 < k) (Z : ℝ) :
    Integrable (fun η : ℝ => renormDensity k Z η) := by
  simpa using integrable_pow_abs_mul_renorm hk Z 0

/-- The three moments c, c₁, c₂ of the tilted density. -/
noncomputable def tiltC (k : ℕ) (Z : ℝ) : ℝ := ∫ η, renormDensity k Z η
noncomputable def tiltC1 (k : ℕ) (Z : ℝ) : ℝ := ∫ η, η ^ k * renormDensity k Z η
noncomputable def tiltC2 (k : ℕ) (Z : ℝ) : ℝ := ∫ η, η ^ (2 * k) * renormDensity k Z η

lemma tiltC_pos (hk : 0 < k) (Z : ℝ) : 0 < tiltC k Z := by
  unfold tiltC
  rw [integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun η => (renormDensity_pos k Z η).le) (integrable_renorm hk Z)]
  have : Function.support (fun η : ℝ => renormDensity k Z η) = univ := by
    ext η
    simp [(renormDensity_pos k Z η).ne']
  rw [this]
  simp

/-- The boundary function η·e^{Zη^k − η^{2k}} vanishes at +∞. -/
lemma tendsto_mul_renorm_atTop (hk : 0 < k) (Z : ℝ) :
    Tendsto (fun η : ℝ => η * renormDensity k Z η) atTop (𝓝 0) := by
  have hC : Tendsto (fun η : ℝ => (Real.exp (Z ^ 2 / 2 + 1 / 2) * Real.exp (1 / 2))
      * (η * Real.exp (-η))) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul
      (Real.exp (Z ^ 2 / 2 + 1 / 2) * Real.exp (1 / 2))
    simpa using this
  refine squeeze_zero' ((Filter.eventually_ge_atTop 0).mono fun η hη =>
    mul_nonneg hη (renormDensity_pos k Z η).le) ?_ hC
  filter_upwards [Filter.eventually_ge_atTop 1] with η hη
  have h1 := renormDensity_le_gauss hk Z η
  have h2 : Real.exp (-(η ^ 2 / 2)) ≤ Real.exp (1 / 2) * Real.exp (-η) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith [sq_nonneg (η - 1)]
  calc η * renormDensity k Z η
      ≤ η * (Real.exp (Z ^ 2 / 2 + 1 / 2) * (Real.exp (1 / 2) * Real.exp (-η))) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by linarith)
        gcongr
    _ = _ := by ring

/-- The boundary function vanishes at −∞, by the reflection η ↦ −η. -/
lemma tendsto_mul_renorm_atBot (hk : 0 < k) (Z : ℝ) :
    Tendsto (fun η : ℝ => η * renormDensity k Z η) atBot (𝓝 0) := by
  have h := (tendsto_mul_renorm_atTop hk ((-1) ^ k * Z)).neg
  rw [neg_zero] at h
  have h' := h.comp tendsto_neg_atBot_atTop
  refine h'.congr fun η => ?_
  have hs : ((-1:ℝ) ^ k) * (-1) ^ k = 1 := by
    rw [← pow_add, ← two_mul, Even.neg_one_pow (even_two_mul k)]
  have hexp : (-1) ^ k * Z * (-η) ^ k - (-η) ^ (2 * k) = Z * η ^ k - η ^ (2 * k) := by
    rw [neg_pow η k, neg_pow η (2 * k), Even.neg_one_pow (even_two_mul k)]
    linear_combination (Z * η ^ k) * hs
  simp only [Function.comp, renormDensity, hexp]
  ring

end TiltedMoments

section Stein

variable {k : ℕ}

/-- Stein's identity for the tilted family: c₂ = λ c + (Z/2) c₁. -/
theorem tilt_stein (hk : 0 < k) (Z : ℝ) :
    tiltC2 k Z = frozenShape k * tiltC k Z + (Z / 2) * tiltC1 k Z := by
  set F : ℝ → ℝ := fun η => η * renormDensity k Z η with hF
  set F' : ℝ → ℝ := fun η =>
    renormDensity k Z η * (1 + Z * k * η ^ k - 2 * k * η ^ (2 * k)) with hF'
  have hderiv : ∀ η, HasDerivAt F (F' η) η := by
    intro η
    have h1 : HasDerivAt (fun η : ℝ => Z * η ^ k - η ^ (2 * k))
        (Z * (k * η ^ (k - 1)) - (2 * k) * η ^ (2 * k - 1)) η := by
      have := ((hasDerivAt_pow k η).const_mul Z).sub (hasDerivAt_pow (2 * k) η)
      simpa using this
    have h2 : HasDerivAt (fun η : ℝ => renormDensity k Z η)
        (Real.exp (Z * η ^ k - η ^ (2 * k))
          * (Z * (k * η ^ (k - 1)) - (2 * k) * η ^ (2 * k - 1))) η := by
      unfold renormDensity
      exact h1.exp
    have h3 := (hasDerivAt_id η).mul h2
    refine h3.congr_deriv ?_
    simp only [hF', renormDensity, id]
    have hk1 : η * η ^ (k - 1) = η ^ k := by
      rw [← pow_succ', Nat.sub_add_cancel hk]
    have hk2 : η * η ^ (2 * k - 1) = η ^ (2 * k) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    calc 1 * Real.exp (Z * η ^ k - η ^ (2 * k))
          + η * (Real.exp (Z * η ^ k - η ^ (2 * k))
            * (Z * (k * η ^ (k - 1)) - (2 * k) * η ^ (2 * k - 1)))
        = Real.exp (Z * η ^ k - η ^ (2 * k))
          * (1 + Z * k * (η * η ^ (k - 1)) - 2 * k * (η * η ^ (2 * k - 1))) := by ring
      _ = _ := by rw [hk1, hk2]
  have hint : Integrable F' := by
    have h0 := integrable_renorm hk Z
    have h1 := (integrable_pow_mul_renorm hk Z k).const_mul (Z * k)
    have h2 := (integrable_pow_mul_renorm hk Z (2 * k)).const_mul (2 * k)
    refine ((h0.add h1).sub h2).congr (Filter.Eventually.of_forall fun η => ?_)
    simp only [hF', Pi.add_apply, Pi.sub_apply]
    ring
  have hIoi := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (fun x _ => hderiv x)
    hint.integrableOn (tendsto_mul_renorm_atTop hk Z)
  have hIic := integral_Iic_of_hasDerivAt_of_tendsto' (a := 0) (fun x _ => hderiv x)
    hint.integrableOn (tendsto_mul_renorm_atBot hk Z)
  have hsplit := integral_add_compl (μ := volume) (measurableSet_Ioi (a := (0:ℝ))) hint
  rw [compl_Ioi] at hsplit
  have hzero : ∫ η, F' η = 0 := by linarith [hsplit, hIoi, hIic]
  have hexpand : ∫ η, F' η
      = tiltC k Z + (Z * k) * tiltC1 k Z - (2 * k) * tiltC2 k Z := by
    have h0 := integrable_renorm hk Z
    have h1 := (integrable_pow_mul_renorm hk Z k).const_mul (Z * k)
    have h2 := (integrable_pow_mul_renorm hk Z (2 * k)).const_mul (2 * k)
    have e : (fun η => F' η) = fun η =>
        (renormDensity k Z η + (Z * k) * (η ^ k * renormDensity k Z η))
          - (2 * k) * (η ^ (2 * k) * renormDensity k Z η) := by
      funext η
      simp only [hF']
      ring
    have h01 : Integrable (fun η : ℝ =>
        renormDensity k Z η + (Z * k) * (η ^ k * renormDensity k Z η)) := h0.add h1
    rw [e, integral_sub h01 h2, integral_add h0 h1, integral_const_mul, integral_const_mul]
    rfl
  have hk' : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [hexpand] at hzero
  unfold frozenShape
  field_simp
  linear_combination (-(1:ℝ)) * hzero

/-- The Riccati relation V(Z) = λ + m(Z)(Z/2 − m(Z)), at every order k. -/
theorem renormVar_riccati (hk : 0 < k) (Z : ℝ) :
    renormVar k Z (fun η => η ^ k)
      = frozenShape k + (tiltC1 k Z / tiltC k Z) * (Z / 2 - tiltC1 k Z / tiltC k Z) := by
  have hc : tiltC k Z ≠ 0 := (tiltC_pos hk Z).ne'
  simp only [renormVar, renormExp]
  have e2 : (∫ η, (η ^ k) ^ 2 * renormDensity k Z η) = tiltC2 k Z := by
    unfold tiltC2
    congr 1
    funext η
    rw [← pow_mul, mul_comm k 2]
  have e1 : (∫ η, η ^ k * renormDensity k Z η) = tiltC1 k Z := rfl
  have e0 : (∫ η, renormDensity k Z η) = tiltC k Z := rfl
  rw [e2, e1, e0, tilt_stein hk Z]
  field_simp
  ring

end Stein

section OddSign

variable {k : ℕ}

lemma odd_pow_surjective (ho : Odd k) : Function.Surjective (fun x : ℝ => x ^ k) := by
  have hk0 : k ≠ 0 := ho.pos.ne'
  intro y
  rcases le_or_gt 0 y with hy | hy
  · exact ⟨y ^ ((k:ℝ)⁻¹), Real.rpow_inv_natCast_pow hy hk0⟩
  · refine ⟨-((-y) ^ ((k:ℝ)⁻¹)), ?_⟩
    show (-((-y) ^ ((k:ℝ)⁻¹))) ^ k = y
    rw [ho.neg_pow, Real.rpow_inv_natCast_pow (by linarith) hk0, neg_neg]

lemma odd_pow_image_univ (ho : Odd k) : (fun x : ℝ => x ^ k) '' univ = univ := by
  rw [image_univ, (odd_pow_surjective ho).range_eq]

/-- The Jacobian weight of s = η^k cancels the power |s|^{1/k − 1}/k off η = 0. -/
lemma odd_pow_jacobian_weight (hk : 0 < k) {η : ℝ} (hη : η ≠ 0) :
    |(k:ℝ) * η ^ (k - 1)| * (|η ^ k| ^ ((1:ℝ) / k - 1) / k) = 1 := by
  have hη0 : 0 < |η| := abs_pos.mpr hη
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  rw [abs_mul, Nat.abs_cast, abs_pow, abs_pow]
  have h1 : (|η| ^ k) ^ ((1:ℝ) / k - 1) = |η| ^ ((1:ℝ) - k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη0.le]
    congr 1
    rw [mul_sub, mul_one_div_cancel hkR.ne', mul_one]
  have h2 : (|η| ^ (k - 1) : ℝ) = |η| ^ ((k:ℝ) - 1) := by
    rw [← Real.rpow_natCast, Nat.cast_sub hk, Nat.cast_one]
  rw [h1, h2]
  have h3 : |η| ^ ((k:ℝ) - 1) * |η| ^ ((1:ℝ) - k) = 1 := by
    rw [← Real.rpow_add hη0, show (k:ℝ) - 1 + (1 - k) = 0 by ring, Real.rpow_zero]
  calc (k:ℝ) * |η| ^ ((k:ℝ) - 1) * (|η| ^ ((1:ℝ) - k) / k)
      = (|η| ^ ((k:ℝ) - 1) * |η| ^ ((1:ℝ) - k)) * (k / k) := by ring
    _ = 1 := by rw [h3, div_self hkR.ne', one_mul]

/-- The substitution s = η^k on the line, for odd k. -/
theorem integral_comp_odd_pow (ho : Odd k) (G : ℝ → ℝ) :
    ∫ η, G (η ^ k) = ∫ s, |s| ^ ((1:ℝ) / k - 1) / k * G s := by
  have hk := ho.pos
  have key := integral_image_eq_integral_abs_deriv_smul (s := univ) (f := fun x : ℝ => x ^ k)
    (f' := fun x => (k:ℝ) * x ^ (k - 1)) MeasurableSet.univ
    (fun x _ => (hasDerivAt_pow k x).hasDerivWithinAt)
    ((ho.strictMono_pow).injective.injOn)
    (fun s => |s| ^ ((1:ℝ) / k - 1) / k * G s)
  rw [odd_pow_image_univ ho, setIntegral_univ, setIntegral_univ] at key
  rw [key]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ η : ℝ, η ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hae] with η hη
  simp only [smul_eq_mul]
  calc G (η ^ k)
      = (|(k:ℝ) * η ^ (k - 1)| * (|η ^ k| ^ ((1:ℝ) / k - 1) / k)) * G (η ^ k) := by
        rw [odd_pow_jacobian_weight hk hη, one_mul]
    _ = |(k:ℝ) * η ^ (k - 1)| * (|η ^ k| ^ ((1:ℝ) / k - 1) / k * G (η ^ k)) := by ring

/-- Integrability transfers across the substitution. -/
theorem integrable_comp_odd_pow_iff (ho : Odd k) (G : ℝ → ℝ) :
    Integrable (fun s => |s| ^ ((1:ℝ) / k - 1) / k * G s)
      ↔ Integrable (fun η => G (η ^ k)) := by
  have hk := ho.pos
  have key := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := univ)
    (f := fun x : ℝ => x ^ k) (f' := fun x => (k:ℝ) * x ^ (k - 1)) MeasurableSet.univ
    (fun x _ => (hasDerivAt_pow k x).hasDerivWithinAt)
    ((ho.strictMono_pow).injective.injOn)
    (fun s => |s| ^ ((1:ℝ) / k - 1) / k * G s)
  rw [odd_pow_image_univ ho, integrableOn_univ, integrableOn_univ] at key
  rw [key]
  refine integrable_congr ?_
  have hae : ∀ᵐ η : ℝ, η ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hae] with η hη
  simp only [smul_eq_mul]
  rw [← mul_assoc, odd_pow_jacobian_weight hk hη, one_mul]

/-- The gap (Z/2)c − c₁ as a shifted Gaussian integral against the
    weight |v + Z/2|^{1/k − 1}. -/
theorem tilt_gap_eq (ho : Odd k) (Z : ℝ) :
    (Z / 2) * tiltC k Z - tiltC1 k Z
      = Real.exp (Z ^ 2 / 4) / k
        * ∫ v, (-v) * Real.exp (-v ^ 2) * |v + Z / 2| ^ ((1:ℝ) / k - 1) := by
  have hk := ho.pos
  have e1 : (Z / 2) * tiltC k Z - tiltC1 k Z
      = ∫ η, (fun s : ℝ => (Z / 2 - s) * Real.exp (Z * s - s ^ 2)) (η ^ k) := by
    unfold tiltC tiltC1
    rw [← integral_const_mul, ← integral_sub ((integrable_renorm hk Z).const_mul _)
      (integrable_pow_mul_renorm hk Z k)]
    congr 1
    funext η
    simp only [renormDensity]
    rw [← pow_mul, mul_comm k 2]
    ring
  rw [e1, integral_comp_odd_pow ho (fun s : ℝ => (Z / 2 - s) * Real.exp (Z * s - s ^ 2))]
  rw [← integral_add_right_eq_self
    (fun s : ℝ => |s| ^ ((1:ℝ) / k - 1) / k * ((Z / 2 - s) * Real.exp (Z * s - s ^ 2))) (Z / 2)]
  rw [← integral_const_mul]
  congr 1
  funext v
  have he : Real.exp (Z * (v + Z / 2) - (v + Z / 2) ^ 2)
      = Real.exp (Z ^ 2 / 4) * Real.exp (-v ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

/-- The shifted integrand is integrable. -/
theorem tilt_gap_integrable (ho : Odd k) (Z : ℝ) :
    Integrable (fun v : ℝ => (-v) * Real.exp (-v ^ 2) * |v + Z / 2| ^ ((1:ℝ) / k - 1)) := by
  have hk := ho.pos
  have hη : Integrable (fun η : ℝ =>
      (fun s : ℝ => (Z / 2 - s) * Real.exp (Z * s - s ^ 2)) (η ^ k)) := by
    refine (((integrable_renorm hk Z).const_mul (Z / 2)).sub
      (integrable_pow_mul_renorm hk Z k)).congr (Filter.Eventually.of_forall fun η => ?_)
    show (Z / 2) * renormDensity k Z η - η ^ k * renormDensity k Z η
      = (Z / 2 - η ^ k) * Real.exp (Z * η ^ k - (η ^ k) ^ 2)
    unfold renormDensity
    rw [← pow_mul, mul_comm k 2]
    ring
  have hg := (integrable_comp_odd_pow_iff ho
    (fun s : ℝ => (Z / 2 - s) * Real.exp (Z * s - s ^ 2))).mpr hη
  have hshift := hg.comp_add_right (Z / 2)
  refine (hshift.const_mul (k * Real.exp (-(Z ^ 2 / 4)))).congr
    (Filter.Eventually.of_forall fun v => ?_)
  beta_reduce
  have he : Real.exp (Z * (v + Z / 2) - (v + Z / 2) ^ 2)
      = Real.exp (Z ^ 2 / 4) * Real.exp (-v ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hE : Real.exp (-(Z ^ 2 / 4)) * Real.exp (Z ^ 2 / 4) = 1 := by
    rw [← Real.exp_add]
    simp
  calc (k:ℝ) * Real.exp (-(Z ^ 2 / 4))
        * (|v + Z / 2| ^ ((1:ℝ) / k - 1) / k
          * ((Z / 2 - (v + Z / 2)) * (Real.exp (Z ^ 2 / 4) * Real.exp (-v ^ 2))))
      = (Real.exp (-(Z ^ 2 / 4)) * Real.exp (Z ^ 2 / 4)) * (k / k)
        * ((-v) * Real.exp (-v ^ 2) * |v + Z / 2| ^ ((1:ℝ) / k - 1)) := by ring
    _ = (-v) * Real.exp (-v ^ 2) * |v + Z / 2| ^ ((1:ℝ) / k - 1) := by
        rw [hE, div_self hkR, one_mul, one_mul]

/-- The paired integrand v e^{−v²}(|Z/2 − v|^{r} − |Z/2 + v|^{r}) is
    nonnegative off the two points v = ±Z/2. -/
lemma pair_nonneg (ho : Odd k) {Z : ℝ} (hZ : 0 ≤ Z) {v : ℝ}
    (h1 : v ≠ Z / 2) (h2 : v ≠ -(Z / 2)) :
    0 ≤ (-v) * Real.exp (-v ^ 2) * |v + Z / 2| ^ ((1:ℝ) / k - 1)
      + (-(-v)) * Real.exp (-(-v) ^ 2) * |-v + Z / 2| ^ ((1:ℝ) / k - 1) := by
  have hr : (1:ℝ) / k - 1 ≤ 0 := by
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast ho.pos
    have : (1:ℝ) / k ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hk1
    linarith
  have hpos1 : 0 < |v + Z / 2| := abs_pos.mpr (fun h => h2 (by linarith))
  have hpos2 : 0 < |-v + Z / 2| := abs_pos.mpr (fun h => h1 (by linarith))
  have hsq : (-v) ^ 2 = v ^ 2 := by ring
  rw [hsq, neg_neg]
  have e : (-v) * Real.exp (-v ^ 2) * |v + Z / 2| ^ ((1:ℝ) / k - 1)
      + v * Real.exp (-v ^ 2) * |-v + Z / 2| ^ ((1:ℝ) / k - 1)
      = v * Real.exp (-v ^ 2)
        * (|-v + Z / 2| ^ ((1:ℝ) / k - 1) - |v + Z / 2| ^ ((1:ℝ) / k - 1)) := by ring
  rw [e]
  rcases le_or_gt 0 v with hv | hv
  · have hle : |-v + Z / 2| ≤ |v + Z / 2| := by
      rw [abs_of_nonneg (by linarith : 0 ≤ v + Z / 2)]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have := Real.rpow_le_rpow_of_nonpos hpos2 hle hr
    exact mul_nonneg (mul_nonneg hv (Real.exp_pos _).le) (by linarith)
  · have hle : |v + Z / 2| ≤ |-v + Z / 2| := by
      rw [abs_of_nonneg (by linarith : 0 ≤ -v + Z / 2)]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have := Real.rpow_le_rpow_of_nonpos hpos1 hle hr
    have hve : 0 ≤ (-v) * Real.exp (-v ^ 2) := mul_nonneg (by linarith) (Real.exp_pos _).le
    nlinarith [hve, this]

/-- Strictly positive on 0 < v < Z/2 when k ≥ 3 and Z > 0. -/
lemma pair_pos (hk3 : 3 ≤ k) {Z v : ℝ} (hv0 : 0 < v) (hvZ : v < Z / 2) :
    0 < (-v) * Real.exp (-v ^ 2) * |v + Z / 2| ^ ((1:ℝ) / k - 1)
      + (-(-v)) * Real.exp (-(-v) ^ 2) * |-v + Z / 2| ^ ((1:ℝ) / k - 1) := by
  have hr : (1:ℝ) / k - 1 < 0 := by
    have hk1 : (3:ℝ) ≤ k := by exact_mod_cast hk3
    have : (1:ℝ) / k < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    linarith
  have hsq : (-v) ^ 2 = v ^ 2 := by ring
  rw [hsq, neg_neg]
  have e : (-v) * Real.exp (-v ^ 2) * |v + Z / 2| ^ ((1:ℝ) / k - 1)
      + v * Real.exp (-v ^ 2) * |-v + Z / 2| ^ ((1:ℝ) / k - 1)
      = v * Real.exp (-v ^ 2)
        * (|-v + Z / 2| ^ ((1:ℝ) / k - 1) - |v + Z / 2| ^ ((1:ℝ) / k - 1)) := by ring
  rw [e]
  have hlt : |-v + Z / 2| < |v + Z / 2| := by
    rw [abs_of_pos (by linarith : 0 < -v + Z / 2), abs_of_pos (by linarith : 0 < v + Z / 2)]
    linarith
  have := Real.rpow_lt_rpow_of_neg (by rw [abs_of_pos (by linarith)]; linarith) hlt hr
  exact mul_pos (mul_pos hv0 (Real.exp_pos _)) (by linarith)

theorem tilt_gap_integral_nonneg (ho : Odd k) {Z : ℝ} (hZ : 0 ≤ Z) :
    0 ≤ ∫ v, (-v) * Real.exp (-v ^ 2) * |v + Z / 2| ^ ((1:ℝ) / k - 1) := by
  set φ : ℝ → ℝ := fun v => (-v) * Real.exp (-v ^ 2) * |v + Z / 2| ^ ((1:ℝ) / k - 1) with hφ
  have hint : Integrable φ := tilt_gap_integrable ho Z
  have hsum : ∫ v, φ v = (1 / 2) * ∫ v, (φ v + φ (-v)) := by
    rw [integral_add hint hint.comp_neg, integral_neg_eq_self φ volume]
    ring
  rw [hsum]
  refine mul_nonneg (by norm_num) (integral_nonneg_of_ae ?_)
  have hae1 : ∀ᵐ v : ℝ, v ≠ Z / 2 := by
    rw [ae_iff]
    simp
  have hae2 : ∀ᵐ v : ℝ, v ≠ -(Z / 2) := by
    rw [ae_iff]
    simp
  filter_upwards [hae1, hae2] with v h1 h2
  exact pair_nonneg ho hZ h1 h2

theorem tilt_gap_integral_pos (ho : Odd k) (hk3 : 3 ≤ k) {Z : ℝ} (hZ : 0 < Z) :
    0 < ∫ v, (-v) * Real.exp (-v ^ 2) * |v + Z / 2| ^ ((1:ℝ) / k - 1) := by
  set φ : ℝ → ℝ := fun v => (-v) * Real.exp (-v ^ 2) * |v + Z / 2| ^ ((1:ℝ) / k - 1) with hφ
  have hint : Integrable φ := tilt_gap_integrable ho Z
  have hsum : ∫ v, φ v = (1 / 2) * ∫ v, (φ v + φ (-v)) := by
    rw [integral_add hint hint.comp_neg, integral_neg_eq_self φ volume]
    ring
  rw [hsum]
  refine mul_pos (by norm_num) ?_
  have hae1 : ∀ᵐ v : ℝ, v ≠ Z / 2 := by
    rw [ae_iff]
    simp
  have hae2 : ∀ᵐ v : ℝ, v ≠ -(Z / 2) := by
    rw [ae_iff]
    simp
  have hnn : 0 ≤ᵐ[volume] fun v => φ v + φ (-v) := by
    filter_upwards [hae1, hae2] with v h1 h2
    exact pair_nonneg ho hZ.le h1 h2
  rw [integral_pos_iff_support_of_nonneg_ae hnn (hint.add hint.comp_neg)]
  refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo 0 (Z / 2)) ?_)
  · rw [Real.volume_Ioo]
    simp [hZ]
  · intro v hv
    rw [Function.mem_support]
    exact (pair_pos hk3 hv.1 hv.2).ne'

/-- The reflection η ↦ −η exchanges Z and −Z at odd k. -/
lemma renormDensity_neg_odd (ho : Odd k) (Z η : ℝ) :
    renormDensity k Z (-η) = renormDensity k (-Z) η := by
  simp only [renormDensity]
  rw [ho.neg_pow, Even.neg_pow (even_two_mul k)]
  congr 1
  ring

/-- The reflected pair η^k rd_Z(η) + (−η)^k rd_Z(−η) is nonnegative at Z ≥ 0. -/
lemma pair_tilt_nonneg (ho : Odd k) {Z : ℝ} (hZ : 0 ≤ Z) (η : ℝ) :
    0 ≤ η ^ k * renormDensity k Z η + (-η) ^ k * renormDensity k Z (-η) := by
  rw [ho.neg_pow, renormDensity_neg_odd ho]
  unfold renormDensity
  rcases le_or_gt 0 (η ^ k) with h | h
  · have : Real.exp (-Z * η ^ k - η ^ (2 * k)) ≤ Real.exp (Z * η ^ k - η ^ (2 * k)) := by
      rw [Real.exp_le_exp]
      nlinarith [mul_nonneg hZ h]
    nlinarith [mul_nonneg h (sub_nonneg.mpr this)]
  · have : Real.exp (Z * η ^ k - η ^ (2 * k)) ≤ Real.exp (-Z * η ^ k - η ^ (2 * k)) := by
      rw [Real.exp_le_exp]
      nlinarith [mul_nonneg hZ (neg_nonneg.mpr h.le)]
    nlinarith [mul_nonneg (neg_nonneg.mpr h.le) (sub_nonneg.mpr this)]

lemma pair_tilt_pos (ho : Odd k) {Z : ℝ} (hZ : 0 < Z) {η : ℝ} (hη : 0 < η) :
    0 < η ^ k * renormDensity k Z η + (-η) ^ k * renormDensity k Z (-η) := by
  rw [ho.neg_pow, renormDensity_neg_odd ho]
  unfold renormDensity
  have hk0 : 0 < η ^ k := pow_pos hη k
  have : Real.exp (-Z * η ^ k - η ^ (2 * k)) < Real.exp (Z * η ^ k - η ^ (2 * k)) := by
    rw [Real.exp_lt_exp]
    nlinarith [mul_pos hZ hk0]
  nlinarith [mul_pos hk0 (sub_pos.mpr this)]

theorem tiltC1_nonneg (ho : Odd k) {Z : ℝ} (hZ : 0 ≤ Z) : 0 ≤ tiltC1 k Z := by
  have hk := ho.pos
  unfold tiltC1
  set φ : ℝ → ℝ := fun η => η ^ k * renormDensity k Z η with hφ
  have hint : Integrable φ := integrable_pow_mul_renorm hk Z k
  have hsum : ∫ η, φ η = (1 / 2) * ∫ η, (φ η + φ (-η)) := by
    rw [integral_add hint hint.comp_neg, integral_neg_eq_self φ volume]
    ring
  rw [hsum]
  exact mul_nonneg (by norm_num) (integral_nonneg fun η => pair_tilt_nonneg ho hZ η)

theorem tiltC1_pos (ho : Odd k) {Z : ℝ} (hZ : 0 < Z) : 0 < tiltC1 k Z := by
  have hk := ho.pos
  unfold tiltC1
  set φ : ℝ → ℝ := fun η => η ^ k * renormDensity k Z η with hφ
  have hint : Integrable φ := integrable_pow_mul_renorm hk Z k
  have hsum : ∫ η, φ η = (1 / 2) * ∫ η, (φ η + φ (-η)) := by
    rw [integral_add hint hint.comp_neg, integral_neg_eq_self φ volume]
    ring
  rw [hsum]
  refine mul_pos (by norm_num) ?_
  have hnn : 0 ≤ᵐ[volume] fun η => φ η + φ (-η) :=
    Filter.Eventually.of_forall fun η => pair_tilt_nonneg ho hZ.le η
  rw [integral_pos_iff_support_of_nonneg_ae hnn (hint.add hint.comp_neg)]
  refine lt_of_lt_of_le ?_ (measure_mono (s := Ioi 0) ?_)
  · simp
  · intro η hη
    rw [Function.mem_support]
    exact (pair_tilt_pos ho hZ hη).ne'

lemma tiltC_neg (ho : Odd k) (Z : ℝ) : tiltC k (-Z) = tiltC k Z := by
  calc tiltC k (-Z) = ∫ η, renormDensity k Z (-η) := by
        unfold tiltC
        congr 1
        funext η
        rw [renormDensity_neg_odd ho]
    _ = tiltC k Z := integral_neg_eq_self (fun η => renormDensity k Z η) volume

lemma tiltC1_neg (ho : Odd k) (Z : ℝ) : tiltC1 k (-Z) = -tiltC1 k Z := by
  calc tiltC1 k (-Z) = ∫ η, -((fun t : ℝ => t ^ k * renormDensity k Z t) (-η)) := by
        unfold tiltC1
        congr 1
        funext η
        beta_reduce
        rw [renormDensity_neg_odd ho, ho.neg_pow]
        ring
    _ = -tiltC1 k Z := by
        rw [integral_neg, integral_neg_eq_self (fun t : ℝ => t ^ k * renormDensity k Z t) volume]
        rfl

/-- The variance is even in Z at odd k. -/
theorem renormVar_neg_odd (ho : Odd k) (Z : ℝ) :
    renormVar k (-Z) (fun η => η ^ k) = renormVar k Z (fun η => η ^ k) := by
  have hk := ho.pos
  rw [renormVar_riccati hk, renormVar_riccati hk, tiltC_neg ho, tiltC1_neg ho]
  ring

/-- At odd k the variance never drops below the frozen value λ. -/
theorem renormVar_odd_ge (ho : Odd k) (Z : ℝ) :
    frozenShape k ≤ renormVar k Z (fun η => η ^ k) := by
  have hk := ho.pos
  have key : ∀ Z : ℝ, 0 ≤ Z → frozenShape k ≤ renormVar k Z (fun η => η ^ k) := by
    intro Z hZ
    rw [renormVar_riccati hk]
    have hc := tiltC_pos hk Z
    have hm0 : 0 ≤ tiltC1 k Z / tiltC k Z := div_nonneg (tiltC1_nonneg ho hZ) hc.le
    have hgap : 0 ≤ (Z / 2) * tiltC k Z - tiltC1 k Z := by
      rw [tilt_gap_eq ho]
      exact mul_nonneg (by positivity) (tilt_gap_integral_nonneg ho hZ)
    have hm1 : tiltC1 k Z / tiltC k Z ≤ Z / 2 := by
      rw [div_le_iff₀ hc]
      linarith
    nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hm1)]
  rcases le_or_gt 0 Z with hZ | hZ
  · exact key Z hZ
  · rw [← renormVar_neg_odd ho]
    exact key (-Z) (by linarith)

/-- At odd k ≥ 3 the variance exceeds λ strictly away from Z = 0. -/
theorem renormVar_odd_gt (ho : Odd k) (hk3 : 3 ≤ k) {Z : ℝ} (hZ : Z ≠ 0) :
    frozenShape k < renormVar k Z (fun η => η ^ k) := by
  have hk := ho.pos
  have key : ∀ Z : ℝ, 0 < Z → frozenShape k < renormVar k Z (fun η => η ^ k) := by
    intro Z hZ
    rw [renormVar_riccati hk]
    have hc := tiltC_pos hk Z
    have hm0 : 0 < tiltC1 k Z / tiltC k Z := div_pos (tiltC1_pos ho hZ) hc
    have hgap : 0 < (Z / 2) * tiltC k Z - tiltC1 k Z := by
      rw [tilt_gap_eq ho]
      exact mul_pos (by positivity) (tilt_gap_integral_pos ho hk3 hZ)
    have hm1 : tiltC1 k Z / tiltC k Z < Z / 2 := by
      rw [div_lt_iff₀ hc]
      linarith
    nlinarith [mul_pos hm0 (sub_pos.mpr hm1)]
  rcases lt_or_gt_of_ne hZ with h | h
  · rw [← renormVar_neg_odd ho]
    exact key (-Z) (by linarith)
  · exact key Z h

end OddSign

section GaussianAverage

open ProbabilityTheory

variable {k : ℕ}

lemma integrable_pow_abs_mul_gauss (m : ℕ) :
    Integrable (fun x : ℝ => |x| ^ m * Real.exp (-(1 / 2) * x ^ 2)) := by
  have h1 : Integrable (fun x : ℝ => x ^ m * Real.exp (-(1 / 2) * x ^ 2)) := by
    have hm : (-1:ℝ) < m := by
      have : (0:ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    refine (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2) hm).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp [Real.rpow_natCast]
  refine h1.abs.congr (Filter.Eventually.of_forall fun x => ?_)
  show |x ^ m * Real.exp (-(1 / 2) * x ^ 2)| = |x| ^ m * Real.exp (-(1 / 2) * x ^ 2)
  rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]

/-- Every tilted moment is continuous in Z. -/
theorem continuous_tilt_moment (hk : 0 < k) (j : ℕ) :
    Continuous (fun Z : ℝ => ∫ η, η ^ j * renormDensity k Z η) := by
  rw [continuous_iff_continuousAt]
  intro Z₀
  refine continuousAt_of_dominated
    (bound := fun η => Real.exp ((|Z₀| + 1) ^ 2 / 2 + 1 / 2)
      * (|η| ^ j * Real.exp (-(1 / 2) * η ^ 2))) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun Z =>
      Continuous.aestronglyMeasurable (by unfold renormDensity; fun_prop)
  · filter_upwards [Metric.ball_mem_nhds Z₀ one_pos] with Z hZ
    refine Filter.Eventually.of_forall fun η => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (renormDensity_pos k Z η)]
    have hle := renormDensity_le_gauss hk Z η
    have hZabs : |Z| ≤ |Z₀| + 1 := by
      have h1 := abs_sub_abs_le_abs_sub Z Z₀
      rw [Metric.mem_ball, Real.dist_eq] at hZ
      linarith
    have hZ' : Z ^ 2 ≤ (|Z₀| + 1) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg Z) hZabs 2
      rwa [sq_abs] at this
    have hexp : Real.exp (Z ^ 2 / 2 + 1 / 2) ≤ Real.exp ((|Z₀| + 1) ^ 2 / 2 + 1 / 2) := by
      rw [Real.exp_le_exp]
      linarith
    have hj : 0 ≤ |η| ^ j := by positivity
    calc |η| ^ j * renormDensity k Z η
        ≤ |η| ^ j * (Real.exp (Z ^ 2 / 2 + 1 / 2) * Real.exp (-(η ^ 2 / 2))) := by gcongr
      _ ≤ |η| ^ j * (Real.exp ((|Z₀| + 1) ^ 2 / 2 + 1 / 2) * Real.exp (-(η ^ 2 / 2))) := by
          gcongr
      _ = Real.exp ((|Z₀| + 1) ^ 2 / 2 + 1 / 2) * (|η| ^ j * Real.exp (-(1 / 2) * η ^ 2)) := by
          rw [show -(1 / 2 : ℝ) * η ^ 2 = -(η ^ 2 / 2) by ring]
          ring
  · exact (integrable_pow_abs_mul_gauss j).const_mul _
  · exact Filter.Eventually.of_forall fun η =>
      (by unfold renormDensity; fun_prop : Continuous fun Z => η ^ j * renormDensity k Z η).continuousAt

lemma continuous_tiltC (hk : 0 < k) : Continuous (tiltC k) := by
  refine (continuous_tilt_moment hk 0).congr fun Z => ?_
  unfold tiltC
  simp only [pow_zero, one_mul]

lemma continuous_tiltC1 (hk : 0 < k) : Continuous (tiltC1 k) :=
  continuous_tilt_moment hk k

/-- The variance is continuous in Z. -/
theorem continuous_renormVar (hk : 0 < k) :
    Continuous (fun Z : ℝ => renormVar k Z (fun η => η ^ k)) := by
  have e : (fun Z : ℝ => renormVar k Z (fun η => η ^ k))
      = fun Z => frozenShape k + (tiltC1 k Z / tiltC k Z) * (Z / 2 - tiltC1 k Z / tiltC k Z) :=
    funext (renormVar_riccati hk)
  rw [e]
  have hm : Continuous fun Z => tiltC1 k Z / tiltC k Z :=
    (continuous_tiltC1 hk).div (continuous_tiltC hk) fun Z => (tiltC_pos hk Z).ne'
  exact continuous_const.add (hm.mul ((continuous_id.div_const 2).sub hm))

/-- At odd k the variance is at most λ + Z²/16. -/
theorem renormVar_odd_le (ho : Odd k) (Z : ℝ) :
    renormVar k Z (fun η => η ^ k) ≤ frozenShape k + Z ^ 2 / 16 := by
  have hk := ho.pos
  have key : ∀ Z : ℝ, 0 ≤ Z → renormVar k Z (fun η => η ^ k) ≤ frozenShape k + Z ^ 2 / 16 := by
    intro Z hZ
    rw [renormVar_riccati hk]
    have hc := tiltC_pos hk Z
    have hm0 : 0 ≤ tiltC1 k Z / tiltC k Z := div_nonneg (tiltC1_nonneg ho hZ) hc.le
    have hgap : 0 ≤ (Z / 2) * tiltC k Z - tiltC1 k Z := by
      rw [tilt_gap_eq ho]
      exact mul_nonneg (by positivity) (tilt_gap_integral_nonneg ho hZ)
    have hm1 : tiltC1 k Z / tiltC k Z ≤ Z / 2 := by
      rw [div_le_iff₀ hc]
      linarith
    nlinarith [sq_nonneg (tiltC1 k Z / tiltC k Z - Z / 4)]
  rcases le_or_gt 0 Z with hZ | hZ
  · exact key Z hZ
  · rw [← renormVar_neg_odd ho]
    have := key (-Z) (by linarith)
    rwa [neg_sq] at this

theorem integrable_renormVar_gauss (ho : Odd k) :
    Integrable (fun Z : ℝ => renormVar k Z (fun η => η ^ k)) (gaussianReal 0 2) := by
  have hk := ho.pos
  have hsq : Integrable (fun Z : ℝ => Z ^ 2) (gaussianReal 0 2) := by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := 2) 2).integrable_sq
  have hbound : Integrable (fun Z : ℝ => frozenShape k + Z ^ 2 / 16) (gaussianReal 0 2) :=
    (integrable_const _).add (hsq.div_const 16)
  refine hbound.mono' (continuous_renormVar hk).aestronglyMeasurable
    (Filter.Eventually.of_forall fun Z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg ((frozenShape_pos hk).le.trans (renormVar_odd_ge ho Z))]
  exact renormVar_odd_le ho Z

/-- At odd k the Z-averaged fluctuation is at least the frozen value. -/
theorem nuLO_odd_ge (ho : Odd k) : frozenShape k ≤ nuLO k := by
  unfold nuLO
  have hint := integrable_renormVar_gauss ho
  calc frozenShape k = ∫ _Z, frozenShape k ∂gaussianReal 0 2 := by simp
    _ ≤ ∫ Z, renormVar k Z (fun η => η ^ k) ∂gaussianReal 0 2 :=
        integral_mono (integrable_const _) hint fun Z => renormVar_odd_ge ho Z

/-- The strict inequality ν_LO(k) > Var_{π₀}[η^k] at every odd k ≥ 3. -/
theorem nuLO_odd_gt (ho : Odd k) (hk3 : 3 ≤ k) : frozenShape k < nuLO k := by
  unfold nuLO
  have hint := integrable_renormVar_gauss ho
  have hsub : (∫ Z, renormVar k Z (fun η => η ^ k) ∂gaussianReal 0 2) - frozenShape k
      = ∫ Z, (renormVar k Z (fun η => η ^ k) - frozenShape k) ∂gaussianReal 0 2 := by
    rw [integral_sub hint (integrable_const _)]
    simp
  have hpos : 0 < ∫ Z, (renormVar k Z (fun η => η ^ k) - frozenShape k) ∂gaussianReal 0 2 := by
    rw [integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun Z => sub_nonneg.mpr (renormVar_odd_ge ho Z))
      (hint.sub (integrable_const _))]
    have hsub' : ({0} : Set ℝ)ᶜ
        ⊆ Function.support fun Z => renormVar k Z (fun η => η ^ k) - frozenShape k := by
      intro Z hZ
      rw [Function.mem_support]
      exact (sub_pos.mpr (renormVar_odd_gt ho hk3 (by simpa using hZ))).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsub')
    rw [measure_compl (measurableSet_singleton 0) (measure_ne_top _ _), measure_univ]
    have h0 : gaussianReal 0 2 {0} = 0 :=
      (gaussianReal_absolutelyContinuous 0 (by norm_num)) (measure_singleton 0)
    rw [h0]
    simp
  linarith [hsub, hpos]

/-- The frozen value is Var_{π₀}[η^k] = λ at odd k, so the theorem's
    inequality reads ν_LO(k) > Var_{π₀}[η^k]. -/
theorem nuLO_gt_frozenVar_odd (ho : Odd k) (hk3 : 3 ≤ k) :
    frozenVar k (fun η => η ^ k) < nuLO k := by
  rw [frozen_var_odd ho.pos ho]
  exact nuLO_odd_gt ho hk3

end GaussianAverage

end DeadDirections
