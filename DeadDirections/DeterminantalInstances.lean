/-
  Instances of the determinantal resolution at width one.

  The determinantal proposition returns the learning coefficient and
  multiplicity of K = ‖W₀⋯W_{L−1} − P_r‖² through an SVD change of
  variables, a Vandermonde monomialisation, and a toric formula. At
  width one the product is a scalar chain and the proposition's output
  is the tied normal-crossing law already certified: at rank zero,
  K = (∏ wᵢ)² has λ = 1/2 with multiplicity L, the volume law being the
  degree-(L−1) log polynomial; at rank one the single regular direction
  K = (w − p)² has λ = 1/2 with multiplicity one, the volume law
  carrying no logarithm. The SVD change of variables, the Vandermonde
  step, and the Newton-polyhedron formula at general widths stay
  outside.
-/
import Mathlib.Topology.Algebra.Order.Field
import DeadDirections.MultiCrossingGeneral

namespace DeadDirections

open MeasureTheory Set Filter Topology

section WidthOne

/-- Rank zero at width one: the exact volume law of K = (∏ wᵢ)² on the
    unit cube is the degree-(L−1) log polynomial in log ε, the
    multiplicity-L normal crossing. -/
theorem width_one_chain_volume (L : ℕ) (hL : 1 ≤ L) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    volume {w : Fin L → ℝ | (∀ i, w i ∈ Ioo (0:ℝ) 1) ∧ (∏ i, w i) ^ 2 < ε}
      = ENNReal.ofReal (logPoly L (ε ^ ((1:ℝ) / 2))) := by
  have h := volume_crossing_tied_general hL (le_refl 1) h0 h1
  simpa using h

/-- Rank zero at width one: λ = 1/2 at every depth L. -/
theorem width_one_chain_slope (L : ℕ) (hL : 1 ≤ L) :
    Tendsto (fun ε => Real.log ((volume {w : Fin L → ℝ |
          (∀ i, w i ∈ Ioo (0:ℝ) 1) ∧ (∏ i, w i) ^ 2 < ε}).toReal) / Real.log ε)
      (𝓝[>] (0:ℝ)) (𝓝 ((1:ℝ) / 2)) := by
  have h := crossing_tied_general_slope hL (le_refl 1)
  simpa using h

/-- The regular block: the sublevel set of K = (w − p)² is the interval
    of half-width √ε about p. -/
lemma morse_sublevel_eq (p ε : ℝ) :
    {w : ℝ | (w - p) ^ 2 < ε} = Ioo (p - Real.sqrt ε) (p + Real.sqrt ε) := by
  ext w
  simp only [mem_setOf_eq, mem_Ioo]
  constructor
  · intro h
    have h' : |w - p| < Real.sqrt ε := by
      rw [Real.lt_sqrt (abs_nonneg _), sq_abs]
      exact h
    rw [abs_lt] at h'
    constructor <;> linarith [h'.1, h'.2]
  · rintro ⟨h1, h2⟩
    have h' : |w - p| < Real.sqrt ε := by
      rw [abs_lt]
      constructor <;> linarith
    rw [Real.lt_sqrt (abs_nonneg _), sq_abs] at h'
    exact h'

/-- Rank one at width one: the volume law of the regular direction is
    2√ε, with no logarithm (multiplicity one). -/
theorem morse_block_volume (p ε : ℝ) :
    volume {w : ℝ | (w - p) ^ 2 < ε} = ENNReal.ofReal (2 * Real.sqrt ε) := by
  rw [morse_sublevel_eq p ε, Real.volume_Ioo]
  congr 1
  ring

/-- Rank one at width one: λ = 1/2 on the regular direction. -/
theorem morse_block_slope (p : ℝ) :
    Tendsto (fun ε => Real.log ((volume {w : ℝ | (w - p) ^ 2 < ε}).toReal) / Real.log ε)
      (𝓝[>] (0:ℝ)) (𝓝 ((1:ℝ) / 2)) := by
  have hlog : Tendsto Real.log (𝓝[>] (0:ℝ)) atBot := Real.tendsto_log_nhdsGT_zero
  have hc : Tendsto (fun ε : ℝ => Real.log 2 / Real.log ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_const_nhds.div_atBot hlog
  have hmain : Tendsto (fun ε : ℝ => Real.log 2 / Real.log ε + 1 / 2) (𝓝[>] (0:ℝ))
      (𝓝 (0 + 1 / 2)) := hc.add tendsto_const_nhds
  rw [zero_add] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds
      (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with ε hε0 hε1
  have hε0' : (0:ℝ) < ε := hε0
  have hlog_ne : Real.log ε ≠ 0 := (Real.log_neg hε0' hε1).ne
  rw [morse_block_volume p ε, ENNReal.toReal_ofReal (by positivity),
    Real.log_mul (by norm_num) (Real.sqrt_pos.mpr hε0').ne', Real.log_sqrt hε0'.le,
    add_div, div_div, mul_comm, ← div_div, div_self hlog_ne]

end WidthOne

end DeadDirections
