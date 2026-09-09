/-
  The real-exponent rate calculus.

  HasLeadingRateR mirrors HasLeadingRate with a real exponent through
  Real.rpow: every consumer that needs a non-integer rate (general-k
  volume scaling, crossover scales, real-order estimators) reads from
  this API. The bridge toReal embeds every natural-exponent rate, so
  the ℕ-calculus stays the working form and the R-calculus extends it
  where the exponent arithmetic leaves ℕ.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import DeadDirections.FisherDecay

namespace DeadDirections

open Filter Topology

/-- F has leading rate p ∈ ℝ with coefficient c at t → 0⁺. -/
def HasLeadingRateR (F : ℝ → ℝ) (p : ℝ) (c : ℝ) : Prop :=
  Tendsto (fun t => F t / t ^ p) (𝓝[>] (0:ℝ)) (𝓝 c)

/-- The bridge: every natural-exponent rate is a real-exponent
    rate. -/
theorem HasLeadingRate.toReal {F : ℝ → ℝ} {p : ℕ} {c : ℝ}
    (h : HasLeadingRate F p c) : HasLeadingRateR F (p : ℝ) c := by
  refine h.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht0
  rw [Real.rpow_natCast]

/-- The pure power has its exponent as leading rate with
    coefficient 1. -/
theorem hasLeadingRateR_rpow (p : ℝ) :
    HasLeadingRateR (fun t => t ^ p) p 1 := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht0
  exact (div_self (ne_of_gt (Real.rpow_pos_of_pos ht0 p))).symm

/-- Positive real powers vanish at 0⁺. -/
theorem tendsto_rpow_nhdsGT_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => t ^ a) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hlog : Tendsto (fun t : ℝ => Real.log t * a)
      (𝓝[>] (0:ℝ)) atBot :=
    Real.tendsto_log_nhdsGT_zero.atBot_mul_const ha
  have h := Real.tendsto_exp_atBot.comp hlog
  refine h.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht0
  exact (Real.rpow_def_of_pos ht0 a).symm

/-- Constant scaling preserves the rate and scales the
    coefficient. -/
theorem HasLeadingRateR.const_mul {F : ℝ → ℝ} {p a : ℝ}
    (hF : HasLeadingRateR F p a) (c : ℝ) :
    HasLeadingRateR (fun t => c * F t) p (c * a) := by
  have h := Filter.Tendsto.const_mul c hF
  refine h.congr fun t => ?_
  exact (mul_div_assoc c (F t) (t ^ p)).symm

/-- Rates add under products. -/
theorem HasLeadingRateR.mul {F G : ℝ → ℝ} {p q a b : ℝ}
    (hF : HasLeadingRateR F p a) (hG : HasLeadingRateR G q b) :
    HasLeadingRateR (fun t => F t * G t) (p + q) (a * b) := by
  have h := Filter.Tendsto.mul hF hG
  refine h.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht0
  rw [Real.rpow_add ht0, div_mul_div_comm]

/-- The smaller rate carries a sum. -/
theorem HasLeadingRateR.add_of_lt {F G : ℝ → ℝ} {p q a b : ℝ}
    (hF : HasLeadingRateR F p a) (hG : HasLeadingRateR G q b)
    (hpq : p < q) :
    HasLeadingRateR (fun t => F t + G t) p a := by
  have hGp : Tendsto (fun t => G t / t ^ q * t ^ (q - p))
      (𝓝[>] (0:ℝ)) (𝓝 (b * 0)) :=
    Filter.Tendsto.mul hG (tendsto_rpow_nhdsGT_zero (by linarith))
  rw [mul_zero] at hGp
  have hsum := Filter.Tendsto.add hF hGp
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht0
  have hqp : G t / t ^ q * t ^ (q - p) = G t / t ^ p := by
    rw [Real.rpow_sub ht0, div_mul_div_comm, mul_comm (G t) (t ^ q),
      mul_div_mul_left _ _ (ne_of_gt (Real.rpow_pos_of_pos ht0 q))]
  rw [add_div, hqp]

/-- Tied rates add coefficients. -/
theorem HasLeadingRateR.add_of_eq {F G : ℝ → ℝ} {p a b : ℝ}
    (hF : HasLeadingRateR F p a) (hG : HasLeadingRateR G p b) :
    HasLeadingRateR (fun t => F t + G t) p (a + b) := by
  have h := hF.add hG
  refine h.congr' ?_
  filter_upwards [] with t
  exact (add_div _ _ _).symm

/-- The log-log slope reads the real exponent. -/
theorem HasLeadingRateR.log_slope {F : ℝ → ℝ} {p : ℝ} {c : ℝ}
    (hc : 0 < c) (h : HasLeadingRateR F p c) :
    Tendsto (fun t => Real.log (F t) / Real.log t) (𝓝[>] (0:ℝ))
      (𝓝 p) := by
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), c / 2 < F t / t ^ p :=
    h.eventually (lt_mem_nhds (half_lt_self hc))
  have hlt1 : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
    eventually_nhdsWithin_of_eventually_nhds
      (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))
  have hsplit : ∀ᶠ t in 𝓝[>] (0:ℝ),
      Real.log (F t) / Real.log t
        = Real.log (F t / t ^ p) / Real.log t + p := by
    filter_upwards [hev, hlt1, eventually_mem_nhdsWithin]
      with t hct ht1 ht0
    have htpos : (0:ℝ) < t := ht0
    have htp : (0:ℝ) < t ^ p := Real.rpow_pos_of_pos htpos p
    have hFpos : 0 < F t := by
      have h2 : 0 < F t / t ^ p := lt_trans (by positivity) hct
      have := mul_pos h2 htp
      rwa [div_mul_cancel₀ _ (ne_of_gt htp)] at this
    have hlogt : Real.log t ≠ 0 := ne_of_lt (Real.log_neg htpos ht1)
    have hlogF : Real.log (F t)
        = Real.log (F t / t ^ p) + p * Real.log t := by
      rw [← Real.log_rpow htpos, ← Real.log_mul
        (by positivity : F t / t ^ p ≠ 0) (ne_of_gt htp),
        div_mul_cancel₀ _ (ne_of_gt htp)]
    rw [hlogF, add_div, mul_div_assoc, div_self hlogt, mul_one]
  have hnum : Tendsto (fun t => Real.log (F t / t ^ p)) (𝓝[>] (0:ℝ))
      (𝓝 (Real.log c)) :=
    ((Real.continuousAt_log (ne_of_gt hc)).tendsto).comp h
  have hden : Tendsto Real.log (𝓝[>] (0:ℝ)) atBot :=
    Real.tendsto_log_nhdsGT_zero
  have hcorr : Tendsto (fun t => Real.log (F t / t ^ p) / Real.log t)
      (𝓝[>] (0:ℝ)) (𝓝 0) := hnum.div_atBot hden
  have hsum : Tendsto
      (fun t => Real.log (F t / t ^ p) / Real.log t + p)
      (𝓝[>] (0:ℝ)) (𝓝 p) := by
    have h := hcorr.add (tendsto_const_nhds (X := ℝ) (x := p)
      (f := 𝓝[>] (0:ℝ)))
    rwa [zero_add] at h
  exact hsum.congr' (by filter_upwards [hsplit] with t h; exact h.symm)

/-- The real-order estimator: at rate 2(k−1) with k ∈ ℝ the reading
    k̂ = 1 + slope/2 recovers k, with no integrality assumption. -/
theorem HasLeadingRateR.khat_recovers {F : ℝ → ℝ} {k : ℝ} {c : ℝ}
    (hc : 0 < c) (h : HasLeadingRateR F (2 * (k - 1)) c) :
    Tendsto (fun t => 1 + Real.log (F t) / Real.log t / 2)
      (𝓝[>] (0:ℝ)) (𝓝 k) := by
  have hslope := h.log_slope hc
  have h2 : Tendsto (fun t => 1 + Real.log (F t) / Real.log t / 2)
      (𝓝[>] (0:ℝ)) (𝓝 (1 + 2 * (k - 1) / 2)) :=
    (hslope.div_const 2).const_add 1
  have heq : 1 + 2 * (k - 1) / 2 = k := by ring
  rwa [heq] at h2

end DeadDirections
