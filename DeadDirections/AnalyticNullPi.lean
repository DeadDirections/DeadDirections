/-
  Zero sets of real-analytic functions on ℝⁿ are null: the
  several-parameter Fubini induction.

  The 1-D backbone (AnalyticNull) upgrades by induction on the
  dimension: slice the zero set over the first coordinate through the
  piFinSuccAbove equivalence. At any t where the slice function is not
  identically zero the slice is null by the induction hypothesis, and
  the set of t where it is identically zero sits inside the zero set
  of the one-variable function t ↦ f(cons t ȳ) through the witness
  tail ȳ, which is null by the 1-D theorem. With this, a generic
  non-cancellation hypothesis over any finite parameter block upgrades
  to an almost-everywhere theorem wherever a witness and analyticity
  are in hand.
-/
import Mathlib.MeasureTheory.Constructions.Pi
import DeadDirections.AnalyticNull

namespace DeadDirections

open Filter Topology MeasureTheory Set

/-- The insertion (t, y) ↦ cons t y as a continuous linear map. -/
noncomputable def consCLM (n : ℕ) : (ℝ × (Fin n → ℝ)) →L[ℝ] (Fin (n+1) → ℝ) :=
  ContinuousLinearMap.pi (fun i => Fin.cases
    (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ))
    (fun j => (ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ))) i)

lemma consCLM_apply {n : ℕ} (p : ℝ × (Fin n → ℝ)) :
    consCLM n p = Fin.cons p.1 p.2 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [consCLM]
  · simp [consCLM]

/-- Zero sets of real-analytic functions on ℝⁿ with one non-zero
    value are Lebesgue-null, at every dimension. -/
theorem analytic_zero_set_null_pi :
    ∀ {n : ℕ} {f : (Fin n → ℝ) → ℝ},
      AnalyticOnNhd ℝ f Set.univ →
      ∀ {x₀ : Fin n → ℝ}, f x₀ ≠ 0 →
      volume {x : Fin n → ℝ | f x = 0} = 0 := by
  intro n
  induction n with
  | zero =>
    intro f hf x₀ hx₀
    have hempty : {x : Fin 0 → ℝ | f x = 0} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      rw [Subsingleton.elim x x₀]
      exact hx₀
    rw [hempty, measure_empty]
  | succ n ih =>
    intro f hf x₀ hx₀
    -- the pair form of f and its analytic slices
    have hpairmap : AnalyticOnNhd ℝ
        (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))
        Set.univ := by
      have hL : AnalyticOnNhd ℝ (consCLM n) Set.univ :=
        fun p _ => (consCLM n).analyticAt p
      have h := hf.comp hL (Set.mapsTo_univ _ _)
      refine fun p hp => (h p hp).congr ?_
      filter_upwards [] with q
      simp [Function.comp, consCLM_apply]
    have hcons : ∀ t : ℝ, AnalyticOnNhd ℝ
        (fun y : Fin n → ℝ => f (Fin.cons t y)) Set.univ := by
      intro t
      have hin : AnalyticOnNhd ℝ
          (fun y : Fin n → ℝ => ((t, y) : ℝ × (Fin n → ℝ)))
          Set.univ :=
        analyticOnNhd_const.prod analyticOnNhd_id
      have h := hpairmap.comp hin (Set.mapsTo_univ _ _)
      exact fun y hy => (h y hy).congr (by filter_upwards [] with z; rfl)
    have hconst : ∀ y : Fin n → ℝ, AnalyticOnNhd ℝ
        (fun t : ℝ => f (Fin.cons t y)) Set.univ := by
      intro y
      have hin : AnalyticOnNhd ℝ
          (fun t : ℝ => ((t, y) : ℝ × (Fin n → ℝ))) Set.univ :=
        analyticOnNhd_id.prod analyticOnNhd_const
      have h := hpairmap.comp hin (Set.mapsTo_univ _ _)
      exact fun t ht => (h t ht).congr (by filter_upwards [] with z; rfl)
    -- transfer the zero set to the product space
    set S : Set (ℝ × (Fin n → ℝ)) :=
      {p | f (Fin.cons p.1 p.2) = 0} with hS
    have hcont : Continuous f :=
      continuousOn_univ.mp hf.continuousOn
    have hSmeas : MeasurableSet S := by
      have hcp : Continuous fun p : ℝ × (Fin n → ℝ) =>
          f (Fin.cons p.1 p.2) := by
        have h1 : Continuous fun p : ℝ × (Fin n → ℝ) => consCLM n p :=
          (consCLM n).continuous
      -- rewrite through consCLM to compose continuity
        have h2 : (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))
            = f ∘ consCLM n := by
          funext p
          simp [Function.comp, consCLM_apply]
        rw [h2]
        exact hcont.comp h1
      exact (isClosed_eq hcp continuous_const).measurableSet
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
      with he
    have hpre : {x : Fin (n+1) → ℝ | f x = 0} = e ⁻¹' S := by
      ext x
      simp only [mem_setOf_eq, mem_preimage, hS]
      have hx : Fin.cons (e x).1 (e x).2 = x := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · show x ((0 : Fin (n+1)).succAbove j) = x (Fin.succ j)
          rw [Fin.succAbove_zero]
      rw [hx]
    have hmp := MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin (n+1) => ℝ) 0
    rw [hpre, hmp.measure_preimage hSmeas.nullMeasurableSet,
      MeasureTheory.Measure.volume_eq_prod]
    -- Fubini: almost every slice is null
    rw [Measure.measure_prod_null hSmeas]
    have hA : volume {t : ℝ | f (Fin.cons t (Fin.tail x₀)) = 0} = 0 := by
      refine analytic_zero_set_null (hconst (Fin.tail x₀)) (x₀ := x₀ 0) ?_
      rw [Fin.cons_self_tail]
      exact hx₀
    have hae : ∀ᵐ t : ℝ,
        volume (Prod.mk t ⁻¹' S) = 0 := by
      rw [ae_iff]
      refine measure_mono_null (fun t ht => ?_) hA
      simp only [mem_setOf_eq] at ht ⊢
      by_contra hne
      apply ht
      have hslice : Prod.mk t ⁻¹' S
          = {y : Fin n → ℝ | f (Fin.cons t y) = 0} := rfl
      rw [hslice]
      exact ih (hcons t) hne
    filter_upwards [hae] with t ht
    exact ht

end DeadDirections
