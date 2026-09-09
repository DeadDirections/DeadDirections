/-
  Zero sets of real-analytic functions on the line are null.

  The backbone of the non-cancellation upgrade: a function analytic
  on the whole line that is non-zero somewhere has only isolated
  zeros (the identity theorem forbids an accumulation), the zero set
  is closed and meets every compact interval in a finite set, so it
  is countable and Lebesgue-null. With this, any analytic observable
  that is non-zero at one witness configuration is non-zero at
  almost every parameter along the line: a generic-position
  hypothesis upgrades to an almost-everywhere theorem wherever a
  witness and analyticity are in hand.
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace DeadDirections

open Filter Topology MeasureTheory

/-- Sums of analytic functions, in lambda form: the Pi-sum shape of
    Finset.analyticAt_sum massaged to the pointwise sum. -/
lemma analyticAt_fun_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    {x : ℝ} (h : ∀ i ∈ s, AnalyticAt ℝ (f i) x) :
    AnalyticAt ℝ (fun t => ∑ i ∈ s, f i t) x := by
  have h2 := Finset.analyticAt_sum s h
  have heq : (∑ i ∈ s, f i) = fun t => ∑ i ∈ s, f i t := by
    funext t
    simp [Finset.sum_apply]
  rwa [heq] at h2

/-- A real-analytic function on the line with one non-zero value
    has a Lebesgue-null zero set. -/
theorem analytic_zero_set_null {f : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f Set.univ) {x₀ : ℝ} (hx₀ : f x₀ ≠ 0) :
    volume {x : ℝ | f x = 0} = 0 := by
  set Z := {x : ℝ | f x = 0} with hZ
  have hiso : ∀ z ∈ Z, ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
    intro z _
    rcases (hf z (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero
      with h | h
    · exfalso
      have hev : f =ᶠ[𝓝 z] 0 := by
        filter_upwards [h] with w hw
        exact hw
      have hzero := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ z) hev
      exact hx₀ (hzero (Set.mem_univ x₀))
    · exact h
  have hcont : Continuous f := continuousOn_univ.mp hf.continuousOn
  have hZc : IsClosed Z := isClosed_eq hcont continuous_const
  have hcount : Z.Countable := by
    have hcover : Z = ⋃ n : ℕ, Z ∩ Set.Icc (-(n:ℝ)) n := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Icc]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_ge |x|
        have hb := abs_le.mp hn
        exact ⟨n, hx, hb.1, hb.2⟩
      · rintro ⟨n, hx, -⟩
        exact hx
    rw [hcover]
    apply Set.countable_iUnion
    intro n
    apply Set.Finite.countable
    have hcomp : IsCompact (Z ∩ Set.Icc (-(n:ℝ)) n) :=
      isCompact_Icc.inter_left hZc
    have hdisc2 : DiscreteTopology ↥(Z ∩ Set.Icc (-(n:ℝ)) n) := by
      rw [discreteTopology_subtype_iff]
      intro z hz
      rw [← Filter.empty_mem_iff_bot]
      have h1 : {w : ℝ | f w ≠ 0}
          ∈ 𝓝[≠] z ⊓ Filter.principal (Z ∩ Set.Icc (-(n:ℝ)) n) :=
        Filter.mem_inf_of_left (hiso z hz.1)
      have h2 : (Z ∩ Set.Icc (-(n:ℝ)) n)
          ∈ 𝓝[≠] z ⊓ Filter.principal (Z ∩ Set.Icc (-(n:ℝ)) n) :=
        Filter.mem_inf_of_right (Filter.mem_principal_self _)
      have h3 := Filter.inter_mem h1 h2
      have hempty : {w : ℝ | f w ≠ 0} ∩ (Z ∩ Set.Icc (-(n:ℝ)) n)
          = ∅ := by
        ext w
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨hne, hZw, -⟩
        exact hne hZw
      rwa [hempty] at h3
    exact hcomp.finite (isDiscrete_iff_discreteTopology.mpr hdisc2)
  exact hcount.measure_zero volume

end DeadDirections
