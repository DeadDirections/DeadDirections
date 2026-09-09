/-
  Slice RLCT, single-direction case (theory paper, thm:selection_rule
  part (c) at m⊥ = 0).

  For the one-dimensional normal form K(t) = t^{2k}, the sublevel-set
  volume law is exact: vol{t : t^{2k} < ε} = 2·ε^{1/(2k)} for
  0 < ε ≤ 1, so the log-volume slope against log ε reads the RLCT
  λ = 1/(2k) with no resolution of singularities. This is the
  volume-scaling reading of the single-direction contribution, the
  quantity the ε-scan volume observable estimates.

  The m⊥ > 0 normal form u^{2k} + v₁² + ⋯ + v_{m⊥}², with slice RLCT
  1/(2k) + m⊥/2, is proved in slice_rlct_product.lean via an exact
  scaling identity.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace DeadDirections

open Filter Topology Real MeasureTheory Set

/-- The sublevel set of the one-dimensional normal form is exactly the
    interval (−ε^{1/(2k)}, ε^{1/(2k)}). -/
lemma sublevel_pow_eq_Ioo {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    {t : ℝ | t ^ (2 * k) < ε}
      = Ioo (-(ε ^ ((1:ℝ)/(2 * k)))) (ε ^ ((1:ℝ)/(2 * k))) := by
  have h2k : (2 * k : ℕ) ≠ 0 := by omega
  have hr : (ε ^ ((1:ℝ)/(2 * k))) ^ (2 * k : ℕ) = ε := by
    rw [← Real.rpow_natCast (ε ^ ((1:ℝ)/(2 * k))) (2 * k),
      ← Real.rpow_mul hε.le]
    have : (1:ℝ)/(2 * k) * ((2 * k : ℕ) : ℝ) = 1 := by
      have hne : ((2 * k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h2k
      push_cast
      field_simp
    rw [this, Real.rpow_one]
  have hrpos : 0 < ε ^ ((1:ℝ)/(2 * k)) := Real.rpow_pos_of_pos hε _
  ext t
  simp only [mem_setOf_eq, mem_Ioo]
  constructor
  · intro ht
    have habs : |t| ^ (2 * k) < (ε ^ ((1:ℝ)/(2 * k))) ^ (2 * k : ℕ) := by
      rw [hr]
      calc |t| ^ (2 * k) = t ^ (2 * k) := by
            rw [← abs_pow, abs_of_nonneg ((even_two_mul k).pow_nonneg t)]
        _ < ε := ht
    have := lt_of_pow_lt_pow_left₀ (2 * k) hrpos.le habs
    exact abs_lt.mp this
  · intro ⟨h1, h2⟩
    have habs : |t| < ε ^ ((1:ℝ)/(2 * k)) := abs_lt.mpr ⟨h1, h2⟩
    calc t ^ (2 * k) = |t| ^ (2 * k) := by
          rw [← abs_pow, abs_of_nonneg ((even_two_mul k).pow_nonneg t)]
      _ < (ε ^ ((1:ℝ)/(2 * k))) ^ (2 * k : ℕ) :=
          pow_lt_pow_left₀ habs (abs_nonneg t) h2k
      _ = ε := hr

/-- Exact volume law for the one-dimensional normal form:
    vol{t : t^{2k} < ε} = 2·ε^{1/(2k)}. -/
theorem volume_sublevel_pow {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    volume {t : ℝ | t ^ (2 * k) < ε}
      = ENNReal.ofReal (2 * ε ^ ((1:ℝ)/(2 * k))) := by
  rw [sublevel_pow_eq_Ioo hk hε, Real.volume_Ioo]
  congr 1
  ring

/-- The log-volume slope of an exact power law C·ε^α reads α: the
    volume-scaling estimator of the RLCT. -/
lemma tendsto_log_div_log_of_rpow {C α : ℝ} (hC : 0 < C) :
    Tendsto (fun ε => Real.log (C * ε ^ α) / Real.log ε)
      (𝓝[>] (0:ℝ)) (𝓝 α) := by
  have hlt1 : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε < 1 :=
    eventually_nhdsWithin_of_eventually_nhds
      (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))
  have hsplit : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      Real.log (C * ε ^ α) / Real.log ε
        = Real.log C / Real.log ε + α := by
    filter_upwards [hlt1, eventually_mem_nhdsWithin] with ε hε1 hε0
    have hεpos : (0:ℝ) < ε := hε0
    have hlogε : Real.log ε ≠ 0 := ne_of_lt (Real.log_neg hεpos hε1)
    rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.rpow_pos_of_pos hεpos α)),
      Real.log_rpow hεpos, add_div, mul_div_assoc, div_self hlogε, mul_one]
  have hcorr : Tendsto (fun ε => Real.log C / Real.log ε)
      (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_const_nhds.div_atBot Real.tendsto_log_nhdsGT_zero
  have hsum : Tendsto (fun ε => Real.log C / Real.log ε + α)
      (𝓝[>] (0:ℝ)) (𝓝 α) := by
    have h := hcorr.add (tendsto_const_nhds (X := ℝ) (x := α)
      (f := 𝓝[>] (0:ℝ)))
    rwa [zero_add] at h
  exact hsum.congr' (by filter_upwards [hsplit] with ε h; exact h.symm)

/-- thm:selection_rule (c) at m⊥ = 0, volume-scaling form: the
    log-volume slope of the normal form t^{2k} reads the slice RLCT
    λ = 1/(2k). -/
theorem slice_rlct_slope {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun ε =>
      Real.log ((volume {t : ℝ | t ^ (2 * k) < ε}).toReal) / Real.log ε)
      (𝓝[>] (0:ℝ)) (𝓝 ((1:ℝ)/(2 * k))) := by
  refine (tendsto_log_div_log_of_rpow (C := 2) (by norm_num)).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  have hεpos : (0:ℝ) < ε := hε
  rw [volume_sublevel_pow hk hεpos, ENNReal.toReal_ofReal
    (by positivity : (0:ℝ) ≤ 2 * ε ^ ((1:ℝ)/(2 * k)))]

end DeadDirections
