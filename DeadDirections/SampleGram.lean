/-
  The sample matrix: √N scaling and the strong-law identification.

  The activation corollaries read σ_min of an N × h sample matrix
  whose rows are the post-activation outputs at N data points. Two
  facts carry the population statement to the sample: the quadratic
  form of the sample Gram is N times the normalised Gram form, so
  σ_min² of the sample matrix is N times the variational minimum of
  the empirical covariance (the √N scaling, an identity), and the
  empirical covariance converges almost surely, entrywise and hence
  along every reading direction at once, to the population second
  moment (the strong law, pairwise independent identically
  distributed rows with integrable second moments). The population
  rate of the bridge rows is then the rate of the sample matrix up to
  the factor √N.
-/
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib

namespace DeadDirections

open MeasureTheory ProbabilityTheory Filter Topology Function

section Scaling

variable {n : ℕ}

/-- The √N scaling, as an identity on quadratic forms: the sample
    Gram form Σᵢ ⟨xᵢ, v⟩² is N times the normalised Gram form. -/
theorem sample_form_eq_N_mul_gram (N : ℕ) (hN : 0 < N)
    (x : Fin N → Fin (n+1) → ℝ) (v : Fin (n+1) → ℝ) :
    ∑ i, (∑ j, x i j * v j) ^ 2
      = (N:ℝ) * ((∑ i, (∑ j, x i j * v j) ^ 2) / N) := by
  have hN' : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- A lower floor on the normalised Gram form lifts to the sample
    form with the factor N: the sample σ_min² is at least N times the
    empirical floor. -/
theorem sample_form_ge_of_gram_ge (N : ℕ) {c : ℝ}
    (x : Fin N → Fin (n+1) → ℝ) (v : Fin (n+1) → ℝ)
    (h : c * ∑ j, v j ^ 2 ≤ (∑ i, (∑ j, x i j * v j) ^ 2) / N) :
    (N:ℝ) * c * ∑ j, v j ^ 2 ≤ ∑ i, (∑ j, x i j * v j) ^ 2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  · have hN' : (0:ℝ) < N := by exact_mod_cast hN
    have h2 := mul_le_mul_of_nonneg_left h hN'.le
    rw [mul_div_cancel₀ _ (ne_of_gt hN')] at h2
    linarith [h2]

end Scaling

section StrongLaw

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}

/-- The strong law for the empirical covariance: with pairwise
    independent identically distributed rows whose entry products are
    integrable, almost surely every entry of the empirical covariance
    converges to the population second moment. -/
theorem empirical_gram_strong_law (X : ℕ → Ω → Fin (n+1) → ℝ)
    (_hmeas : ∀ i, Measurable (X i))
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hint : ∀ j k, Integrable (fun ω => X 0 ω j * X 0 ω k) μ) :
    ∀ᵐ ω ∂μ, ∀ j k : Fin (n+1),
      Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, X i ω j * X i ω k) / N)
        atTop (𝓝 (∫ ω, X 0 ω j * X 0 ω k ∂μ)) := by
  rw [ae_all_iff]
  intro j
  rw [ae_all_iff]
  intro k
  set φ : (Fin (n+1) → ℝ) → ℝ := fun x => x j * x k with hφ
  have hφm : Measurable φ :=
    (measurable_pi_apply j).mul (measurable_pi_apply k)
  have h := strong_law_ae_real (μ := μ) (fun i ω => φ (X i ω))
    (hint j k)
    (fun i i' hii' => (hindep hii').comp hφm hφm)
    (fun i => (hident i).comp hφm)
  exact h

/-- The strong law along every reading direction at once: almost
    surely, for every v the normalised sample form (1/N)Σᵢ⟨Xᵢ, v⟩²
    converges to the population form vᵀΣv. -/
theorem empirical_form_strong_law (X : ℕ → Ω → Fin (n+1) → ℝ)
    (hmeas : ∀ i, Measurable (X i))
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hint : ∀ j k, Integrable (fun ω => X 0 ω j * X 0 ω k) μ) :
    ∀ᵐ ω ∂μ, ∀ v : Fin (n+1) → ℝ,
      Tendsto (fun N : ℕ =>
          (∑ i ∈ Finset.range N, (∑ j, X i ω j * v j) ^ 2) / N)
        atTop
        (𝓝 (∑ j, ∑ k, v j * v k * ∫ ω, X 0 ω j * X 0 ω k ∂μ)) := by
  filter_upwards [empirical_gram_strong_law X hmeas hindep hident hint]
    with ω hω
  intro v
  have hsum : ∀ N : ℕ,
      (∑ i ∈ Finset.range N, (∑ j, X i ω j * v j) ^ 2) / N
        = ∑ j, ∑ k, v j * v k
            * ((∑ i ∈ Finset.range N, X i ω j * X i ω k) / N) := by
    intro N
    have hsq : ∀ i, (∑ j, X i ω j * v j) ^ 2
        = ∑ j, ∑ k, v j * v k * (X i ω j * X i ω k) := by
      intro i
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    simp only [hsq, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [hsum]
  refine tendsto_finset_sum _ fun j _ => tendsto_finset_sum _ fun k _ => ?_
  exact (hω j k).const_mul _

end StrongLaw

end DeadDirections
