/-
  prop:curvature_rate item (i): the abstract order bounds.

  The Christoffel numerator 2∂_αF_{1α} − ∂_1F_{αα} reduces, after
  differentiating the Fisher entries under the integral with the
  score of the moving measure inserted, to E[s₁(2∂_αs_α + s_α²)]:
  the mixed partials of the scores cancel. Cauchy–Schwarz against
  F₁₁ = Θ(t^{2(k−1)}) then bounds any such pairing by O(t^{k−1}),
  the Christoffel symbol Γ¹_{αα} by O(t^{−(k−1)}) once the Gram
  determinant is Θ(t^{2(k−1)}), and the two ΓΓ products that enter
  R_{1α1α} stay bounded for k ≥ 2. Score-integration regularity
  enters as the hypothesis that the derivatives of the entries are
  the inserted-score integrals; everything after it is exact.
-/
import DeadDirections.FisherDecay

namespace DeadDirections

open Filter Topology MeasureTheory

section Identity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The Christoffel numerator identity, integrand form: with
    ∂_αF_{1α} = E[(∂_αs₁)s_α + s₁∂_αs_α + s₁s_α²] and
    ∂_1F_{αα} = E[2s_α∂_1s_α + s_α²s₁] (differentiation under the
    integral with the score inserted) and the mixed partials equal,
    2∂_αF_{1α} − ∂_1F_{αα} = E[s₁(2∂_αs_α + s_α²)]. -/
theorem christoffel_numerator_identity (s₁ sα dαs₁ d₁sα dαsα : Ω → ℝ)
    (hsym : ∀ ω, dαs₁ ω = d₁sα ω)
    (h1 : Integrable (fun ω => dαs₁ ω * sα ω) μ)
    (h2 : Integrable (fun ω => s₁ ω * dαsα ω) μ)
    (h3 : Integrable (fun ω => s₁ ω * sα ω ^ 2) μ) :
    2 * (∫ ω, (dαs₁ ω * sα ω + s₁ ω * dαsα ω + s₁ ω * sα ω ^ 2) ∂μ)
      - ∫ ω, (2 * sα ω * d₁sα ω + sα ω ^ 2 * s₁ ω) ∂μ
      = ∫ ω, s₁ ω * (2 * dαsα ω + sα ω ^ 2) ∂μ := by
  have h12 : Integrable (fun ω => dαs₁ ω * sα ω + s₁ ω * dαsα ω) μ :=
    (h1.add h2).congr (Filter.Eventually.of_forall fun ω => by
      simp only [Pi.add_apply])
  have hA : ∫ ω, (dαs₁ ω * sα ω + s₁ ω * dαsα ω + s₁ ω * sα ω ^ 2) ∂μ
      = (∫ ω, dαs₁ ω * sα ω ∂μ) + (∫ ω, s₁ ω * dαsα ω ∂μ)
        + ∫ ω, s₁ ω * sα ω ^ 2 ∂μ := by
    rw [integral_add h12 h3, integral_add h1 h2]
  have hB : ∫ ω, (2 * sα ω * d₁sα ω + sα ω ^ 2 * s₁ ω) ∂μ
      = 2 * (∫ ω, dαs₁ ω * sα ω ∂μ) + ∫ ω, s₁ ω * sα ω ^ 2 ∂μ := by
    have hfun : (fun ω => 2 * sα ω * d₁sα ω + sα ω ^ 2 * s₁ ω)
        = fun ω => 2 * (dαs₁ ω * sα ω) + s₁ ω * sα ω ^ 2 := by
      funext ω
      rw [hsym ω]
      ring
    rw [hfun, integral_add (h1.const_mul 2) h3, integral_const_mul]
  have hC : ∫ ω, s₁ ω * (2 * dαsα ω + sα ω ^ 2) ∂μ
      = 2 * (∫ ω, s₁ ω * dαsα ω ∂μ) + ∫ ω, s₁ ω * sα ω ^ 2 ∂μ := by
    have hfun : (fun ω => s₁ ω * (2 * dαsα ω + sα ω ^ 2))
        = fun ω => 2 * (s₁ ω * dαsα ω) + s₁ ω * sα ω ^ 2 := by
      funext ω
      ring
    rw [hfun, integral_add (h2.const_mul 2) h3, integral_const_mul]
  rw [hA, hB, hC]
  ring

/-- Cauchy–Schwarz for the pairing, from the weighted AM-GM bound at
    the optimal weight. -/
theorem abs_integral_mul_le_sqrt (f g : Ω → ℝ)
    (hfg : Integrable (fun ω => f ω * g ω) μ)
    (hf2 : Integrable (fun ω => f ω ^ 2) μ)
    (hg2 : Integrable (fun ω => g ω ^ 2) μ)
    (hA : 0 < ∫ ω, f ω ^ 2 ∂μ) :
    |∫ ω, f ω * g ω ∂μ|
      ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  set A := ∫ ω, f ω ^ 2 ∂μ with hAdef
  set B := ∫ ω, g ω ^ 2 ∂μ with hBdef
  have hB0 : 0 ≤ B := integral_nonneg fun ω => sq_nonneg _
  by_cases hB : B = 0
  · -- any weight gives the bound w·A/2; send w to zero
    have hw : ∀ w : ℝ, 0 < w → |∫ ω, f ω * g ω ∂μ| ≤ w * A / 2 := by
      intro w hw
      have h := abs_integral_mul_le_weighted w f g hw hfg hf2 hg2
      rw [← hAdef, ← hBdef, hB] at h
      linarith
    have hle : |∫ ω, f ω * g ω ∂μ| ≤ 0 := by
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      have h := hw (ε / A) (div_pos hε hA)
      rw [div_mul_cancel₀ _ (ne_of_gt hA)] at h
      linarith
    rw [hB, Real.sqrt_zero, mul_zero]
    exact hle
  · have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB)
    set w := Real.sqrt B / Real.sqrt A with hwdef
    have hw : 0 < w := div_pos (Real.sqrt_pos.mpr hBpos) (Real.sqrt_pos.mpr hA)
    have h := abs_integral_mul_le_weighted w f g hw hfg hf2 hg2
    rw [← hAdef, ← hBdef] at h
    have hsA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.le
    have hsB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hBpos.le
    have hsA0 : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
    have hsB0 : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBpos
    have heq : (w * A + 1 / w * B) / 2 = Real.sqrt A * Real.sqrt B := by
      rw [hwdef]
      have key : ∀ sA sB : ℝ, 0 < sA → 0 < sB →
          (sB / sA * sA ^ 2 + 1 / (sB / sA) * sB ^ 2) / 2 = sA * sB := by
        intro sA sB h1 h2
        field_simp
        ring
      have := key (Real.sqrt A) (Real.sqrt B) hsA0 hsB0
      rw [hsA, hsB] at this
      exact this
    rw [heq] at h
    exact h

end Identity

section Orders

/-- Cauchy–Schwarz at rate level: a pairing of a score with
    F₁₁ = Θ(t^{2(k−1)}) against a bounded-moment factor is
    O(t^{k−1}), with the explicit constant √(2cM). -/
theorem cross_score_order {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s₁ X : ℝ → Ω → ℝ) {k : ℕ} {c M : ℝ} (hc : 0 < c) (_hM : 0 ≤ M)
    (hF : HasLeadingRate (fun t => ∫ ω, s₁ t ω ^ 2 ∂μ) (2 * (k - 1)) c)
    (hint : ∀ᶠ t in 𝓝[>] (0:ℝ), Integrable (fun ω => s₁ t ω * X t ω) μ
      ∧ Integrable (fun ω => s₁ t ω ^ 2) μ
      ∧ Integrable (fun ω => X t ω ^ 2) μ)
    (hX : ∀ᶠ t in 𝓝[>] (0:ℝ), ∫ ω, X t ω ^ 2 ∂μ ≤ M) :
    ∀ᶠ t in 𝓝[>] (0:ℝ),
      |∫ ω, s₁ t ω * X t ω ∂μ| ≤ Real.sqrt (2 * c * M) * t ^ (k - 1) := by
  have hup : ∀ᶠ t in 𝓝[>] (0:ℝ),
      (∫ ω, s₁ t ω ^ 2 ∂μ) / t ^ (2 * (k - 1)) < 2 * c :=
    hF.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hup, hF.eventually_pos hc, hint, hX,
    eventually_mem_nhdsWithin] with t hup hpos ⟨hfg, hf2, hg2⟩ hXt ht
  have htp : (0:ℝ) < t ^ (2 * (k - 1)) := pow_pos ht _
  have hF2 : ∫ ω, s₁ t ω ^ 2 ∂μ ≤ 2 * c * t ^ (2 * (k - 1)) := by
    rw [div_lt_iff₀ htp] at hup
    exact hup.le
  have hcs := abs_integral_mul_le_sqrt (s₁ t) (X t) hfg hf2 hg2 hpos
  have hXnn : 0 ≤ ∫ ω, X t ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hsq : t ^ (2 * (k - 1)) = (t ^ (k - 1)) ^ 2 := by
    rw [← pow_mul, mul_comm]
  calc |∫ ω, s₁ t ω * X t ω ∂μ|
      ≤ Real.sqrt (∫ ω, s₁ t ω ^ 2 ∂μ) * Real.sqrt (∫ ω, X t ω ^ 2 ∂μ) := hcs
    _ ≤ Real.sqrt (2 * c * t ^ (2 * (k - 1))) * Real.sqrt M :=
        mul_le_mul (Real.sqrt_le_sqrt hF2) (Real.sqrt_le_sqrt hXt)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt (2 * c * M) * t ^ (k - 1) := by
        rw [hsq, Real.sqrt_mul (by positivity), Real.sqrt_sq (pow_pos ht _).le,
          Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * c)]
        ring

/-- A Christoffel symbol with numerator O(t^m) over a Gram determinant
    bounded below by c·t^{2m} is O(t^{−m}). -/
theorem christoffel_order_bound {num den A c : ℝ} {m : ℕ} {t : ℝ}
    (ht : 0 < t) (hc : 0 < c)
    (hnum : |num| ≤ A * t ^ m) (hden : c * t ^ (2 * m) ≤ den) :
    |num / den| ≤ (A / c) / t ^ m := by
  have hden0 : 0 < den := lt_of_lt_of_le (by positivity) hden
  rw [abs_div, abs_of_pos hden0, div_le_div_iff₀ hden0 (pow_pos ht m)]
  have h2 : t ^ (2 * m) = t ^ m * t ^ m := by rw [two_mul, pow_add]
  have hA0 : 0 ≤ A := by
    have := abs_nonneg num
    have htm : 0 < t ^ m := pow_pos ht m
    nlinarith
  calc |num| * t ^ m ≤ A * t ^ m * t ^ m :=
        mul_le_mul_of_nonneg_right hnum (pow_pos ht m).le
    _ = (A / c) * (c * t ^ (2 * m)) := by
        rw [h2]
        field_simp
    _ ≤ A / c * den := mul_le_mul_of_nonneg_left hden (div_nonneg hA0 hc.le)

/-- The ΓΓ products in R_{1α1α} stay bounded for k ≥ 2: with
    |F₁₁| ≤ B·t^{2m}, |Γ¹₁₁| ≤ D/t and |Γ¹_{αα}| ≤ E/t^m on 0 < t ≤ 1
    and m ≥ 1, the lowered product is at most B·D·E, and with
    |Γ¹_{1α}| ≤ E/t^m the square term is at most B·E². -/
theorem gamma_gamma_bounded {F Γ₁ Γ₂ B D E : ℝ} {m : ℕ} {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hm : 1 ≤ m)
    (hF : |F| ≤ B * t ^ (2 * m)) (hΓ₁ : |Γ₁| ≤ D / t)
    (hΓ₂ : |Γ₂| ≤ E / t ^ m) :
    |F * Γ₁ * Γ₂| ≤ B * D * E ∧ |F * Γ₂ ^ 2| ≤ B * E ^ 2 := by
  have htm : 0 < t ^ m := pow_pos ht m
  have hB0 : 0 ≤ B := by
    have := abs_nonneg F
    have : 0 < t ^ (2 * m) := pow_pos ht _
    nlinarith
  have hD0 : 0 ≤ D := by
    have := abs_nonneg Γ₁
    have h := div_nonneg_iff.mp (le_trans (abs_nonneg Γ₁) hΓ₁)
    rcases h with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · linarith
  have hE0 : 0 ≤ E := by
    have h := div_nonneg_iff.mp (le_trans (abs_nonneg Γ₂) hΓ₂)
    rcases h with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · linarith
  have htpow : t ^ (2 * m) ≤ t * t ^ m := by
    have : t ^ (2 * m) = t ^ (m - 1) * (t * t ^ m) := by
      rw [← pow_succ', ← pow_add]
      congr 1
      omega
    rw [this]
    have hle : t ^ (m - 1) ≤ 1 := pow_le_one₀ ht.le ht1
    nlinarith [mul_pos ht htm]
  constructor
  · rw [abs_mul, abs_mul]
    calc |F| * |Γ₁| * |Γ₂| ≤ (B * t ^ (2 * m)) * (D / t) * (E / t ^ m) := by
          gcongr
      _ = B * D * E * (t ^ (2 * m) / (t * t ^ m)) := by
          field_simp
      _ ≤ B * D * E * 1 := by
          gcongr
          rw [div_le_one (mul_pos ht htm)]
          exact htpow
      _ = B * D * E := mul_one _
  · rw [abs_mul, abs_pow]
    calc |F| * |Γ₂| ^ 2 ≤ (B * t ^ (2 * m)) * (E / t ^ m) ^ 2 := by
          gcongr
      _ = B * E ^ 2 := by
          have : t ^ (2 * m) = (t ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
          rw [this]
          field_simp

end Orders

end DeadDirections
