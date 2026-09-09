/-
  Fisher rate decay, top layer (theory paper, thm:fisher_decay).

  This file formalizes the asymptotic readings of the rate theorem: a
  directional Fisher F(t) with expansion F(t) = c·t^p + O(t^{p+1}) has
  leading rate p, its log-log slope tends to p as t → 0⁺, and at
  p = 2(k−1) the estimator k̂ = 1 + slope/2 recovers the KL order k.
  These are the "as a slope" readings of rem:fisher_decay_three_readings.

  The analytic middle layer lives in this file too
  (`fisher_expansion_of_score_expansion`): it derives the expansion
  from the packaged L² score expansion and feeds
  `hasLeadingRate_of_expansion` with c = k²·E[a²] and p = 2(k−1).
  The exact 2k² Fisher–KL ratio lives in gsd_gaussian_fisher.lean
  on the KL-order-k curve.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace DeadDirections

open Filter Topology Real

/-- F has leading rate p with coefficient c at t → 0⁺. -/
def HasLeadingRate (F : ℝ → ℝ) (p : ℕ) (c : ℝ) : Prop :=
  Tendsto (fun t => F t / t ^ p) (𝓝[>] (0:ℝ)) (𝓝 c)

/-- An expansion F(t) = c·t^p + R(t) with |R(t)| ≤ M·t^{p+1} near 0⁺
    gives leading rate p with coefficient c. -/
theorem hasLeadingRate_of_expansion {F R : ℝ → ℝ} {p : ℕ} {c M : ℝ}
    (hF : ∀ᶠ t in 𝓝[>] (0:ℝ), F t = c * t ^ p + R t)
    (hR : ∀ᶠ t in 𝓝[>] (0:ℝ), |R t| ≤ M * t ^ (p + 1)) :
    HasLeadingRate F p c := by
  have hMt : Tendsto (fun t : ℝ => M * t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => M * t) (𝓝 (0:ℝ)) (𝓝 (M * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hMtneg : Tendsto (fun t : ℝ => -(M * t)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using hMt.neg
  have hbound : ∀ᶠ t in 𝓝[>] (0:ℝ), |R t / t ^ p| ≤ M * t := by
    filter_upwards [hR, eventually_mem_nhdsWithin] with t hRt ht
    have ht0 : (0:ℝ) < t := ht
    have htp : (0:ℝ) < t ^ p := pow_pos ht0 p
    rw [abs_div, abs_of_pos htp, div_le_iff₀ htp]
    calc |R t| ≤ M * t ^ (p + 1) := hRt
      _ = M * t * t ^ p := by rw [pow_succ]; ring
  have h1 : Tendsto (fun t => R t / t ^ p) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hMtneg hMt ?_ ?_
    · filter_upwards [hbound] with t h
      exact (abs_le.mp h).1
    · filter_upwards [hbound] with t h
      exact (abs_le.mp h).2
  have h2 : Tendsto (fun t => c + R t / t ^ p) (𝓝[>] (0:ℝ)) (𝓝 c) := by
    have h := (tendsto_const_nhds (X := ℝ) (x := c)
      (f := 𝓝[>] (0:ℝ))).add h1
    rwa [add_zero] at h
  refine h2.congr' ?_
  filter_upwards [hF, eventually_mem_nhdsWithin] with t hFt ht
  have htp : (t:ℝ) ^ p ≠ 0 := ne_of_gt (pow_pos ht p)
  rw [hFt]
  field_simp

/-- The slope reading: with positive leading coefficient, the log-log
    slope of F tends to the leading rate p as t → 0⁺. -/
theorem HasLeadingRate.log_slope {F : ℝ → ℝ} {p : ℕ} {c : ℝ} (hc : 0 < c)
    (h : HasLeadingRate F p c) :
    Tendsto (fun t => Real.log (F t) / Real.log t) (𝓝[>] (0:ℝ)) (𝓝 p) := by
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), c / 2 < F t / t ^ p :=
    h.eventually (lt_mem_nhds (half_lt_self hc))
  have hlt1 : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
    eventually_nhdsWithin_of_eventually_nhds
      (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))
  -- log F t = log (F t / t^p) + p · log t on the window
  have hsplit : ∀ᶠ t in 𝓝[>] (0:ℝ),
      Real.log (F t) / Real.log t
        = Real.log (F t / t ^ p) / Real.log t + p := by
    filter_upwards [hev, hlt1, eventually_mem_nhdsWithin] with t hct ht1 ht0
    have htpos : (0:ℝ) < t := ht0
    have htp : (0:ℝ) < t ^ p := pow_pos htpos p
    have hFpos : 0 < F t := by
      have h2 : 0 < F t / t ^ p := lt_trans (by positivity) hct
      have := mul_pos h2 htp
      rwa [div_mul_cancel₀ _ (ne_of_gt htp)] at this
    have hlogt : Real.log t ≠ 0 := ne_of_lt (Real.log_neg htpos ht1)
    have hlogF : Real.log (F t)
        = Real.log (F t / t ^ p) + p * Real.log t := by
      rw [← Real.log_pow, ← Real.log_mul
        (by positivity : F t / t ^ p ≠ 0) (ne_of_gt htp),
        div_mul_cancel₀ _ (ne_of_gt htp)]
    rw [hlogF, add_div, mul_div_assoc, div_self hlogt, mul_one]
  -- the correction term dies: log(F/t^p) → log c, log t → −∞
  have hnum : Tendsto (fun t => Real.log (F t / t ^ p)) (𝓝[>] (0:ℝ))
      (𝓝 (Real.log c)) :=
    ((Real.continuousAt_log (ne_of_gt hc)).tendsto).comp h
  have hden : Tendsto Real.log (𝓝[>] (0:ℝ)) atBot :=
    Real.tendsto_log_nhdsGT_zero
  have hcorr : Tendsto (fun t => Real.log (F t / t ^ p) / Real.log t)
      (𝓝[>] (0:ℝ)) (𝓝 0) := hnum.div_atBot hden
  have hsum : Tendsto (fun t => Real.log (F t / t ^ p) / Real.log t + p)
      (𝓝[>] (0:ℝ)) (𝓝 (p : ℝ)) := by
    have h := hcorr.add (tendsto_const_nhds (X := ℝ) (x := (p:ℝ))
      (f := 𝓝[>] (0:ℝ)))
    rwa [zero_add] at h
  exact hsum.congr' (by filter_upwards [hsplit] with t h; exact h.symm)

/-- The KL-order reading: at rate p = 2(k−1) the estimator
    k̂ = 1 + slope/2 recovers k. -/
theorem HasLeadingRate.khat_recovers {F : ℝ → ℝ} {k : ℕ} {c : ℝ}
    (hk : 1 ≤ k) (hc : 0 < c) (h : HasLeadingRate F (2 * (k - 1)) c) :
    Tendsto (fun t => 1 + Real.log (F t) / Real.log t / 2)
      (𝓝[>] (0:ℝ)) (𝓝 (k : ℝ)) := by
  have hs := (h.log_slope hc).div_const 2
  have h1 := hs.const_add 1
  have harith : 1 + ((2 * (k - 1) : ℕ) : ℝ) / 2 = (k : ℝ) := by
    push_cast [Nat.cast_sub hk]
    ring
  rwa [harith] at h1

/-! ## Middle layer: from the score expansion to the Fisher expansion

Hypotheses (ii)–(iii) of thm:fisher_decay are packaged as: the
directional score has the form s(t) = k·t^{k−1}·a + r(t) with a the
leading coefficient (a = k·a_k in the paper's notation, absorbed here),
E[a²] finite, and the remainder r(t) of one order higher in L²:
∫r(t)² ≤ M·t^{2k}. The conclusion is the expansion the top layer
consumes: ∫s(t)² has leading rate 2(k−1) with coefficient k²·E[a²].

The cross term is handled without Cauchy–Schwarz: the weighted AM-GM
|a·r| ≤ ((t^k)²a² + r²)/(2t^k), with the weight chosen as t^k, gives
the cross integral at the same t^{2k−1} order. -/

section MiddleLayer

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The score expansion s(t) = k·t^{k−1}·a + r(t) with an L²-small
    remainder gives the Fisher expansion: ∫s(t)² has leading rate
    2(k−1) with coefficient k²·∫a². -/
theorem fisher_expansion_of_score_expansion
    {s : ℝ → Ω → ℝ} {a : Ω → ℝ} {r : ℝ → Ω → ℝ} {k : ℕ} {M : ℝ}
    (hk : 1 ≤ k) (hM : 0 ≤ M)
    (hs : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ ω, s t ω = k * t ^ (k-1) * a ω + r t ω)
    (ha2 : Integrable (fun ω => a ω ^ 2) μ)
    (hr2 : ∀ᶠ t in 𝓝[>] (0:ℝ), Integrable (fun ω => r t ω ^ 2) μ)
    (hra : ∀ᶠ t in 𝓝[>] (0:ℝ), Integrable (fun ω => a ω * r t ω) μ)
    (hrb : ∀ᶠ t in 𝓝[>] (0:ℝ), (∫ ω, r t ω ^ 2 ∂μ) ≤ M * t ^ (2*k)) :
    HasLeadingRate (fun t => ∫ ω, s t ω ^ 2 ∂μ) (2*(k-1))
      ((k:ℝ) ^ 2 * ∫ ω, a ω ^ 2 ∂μ) := by
  set A := ∫ ω, a ω ^ 2 ∂μ with hA
  have hA0 : 0 ≤ A := integral_nonneg fun ω => sq_nonneg _
  apply hasLeadingRate_of_expansion
    (R := fun t => (2*(k:ℝ)*t^(k-1)) * (∫ ω, a ω * r t ω ∂μ)
      + ∫ ω, r t ω ^ 2 ∂μ)
    (M := (k:ℝ) * (A + M) + M)
  -- (a) the expansion identity
  · filter_upwards [hs, hr2, hra] with t hst hr2t hrat
    have hpow : t ^ (2*(k-1)) = (t ^ (k-1)) ^ 2 := by
      rw [mul_comm, pow_mul]
    have hfun : ∀ ω, s t ω ^ 2
        = ((k:ℝ)^2 * (t^(k-1))^2) * a ω ^ 2
          + (2*(k:ℝ)*t^(k-1)) * (a ω * r t ω) + r t ω ^ 2 := by
      intro ω
      rw [hst ω]
      ring
    simp only [hfun]
    have h1 : Integrable (fun ω => ((k:ℝ)^2 * (t^(k-1))^2) * a ω ^ 2) μ :=
      ha2.const_mul _
    have h2 : Integrable
        (fun ω => (2*(k:ℝ)*t^(k-1)) * (a ω * r t ω)) μ :=
      hrat.const_mul _
    have h12 : Integrable
        (fun ω => ((k:ℝ)^2 * (t^(k-1))^2) * a ω ^ 2
          + (2*(k:ℝ)*t^(k-1)) * (a ω * r t ω)) μ := h1.add h2
    rw [integral_add h12 hr2t, integral_add h1 h2,
      integral_const_mul, integral_const_mul, hpow]
    ring
  -- (b) the remainder is one order higher
  · filter_upwards [hr2, hra, hrb, eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))]
      with t hr2t hrat hrbt ht0 ht1
    have htpos : (0:ℝ) < t := ht0
    have htk : (0:ℝ) < t ^ k := pow_pos htpos k
    have hr2nn : 0 ≤ ∫ ω, r t ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have hkr : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    -- the weighted AM-GM bound on the cross integral
    have hcross : |∫ ω, a ω * r t ω ∂μ|
        ≤ ((t^k)^2 * A + ∫ ω, r t ω ^ 2 ∂μ) / (2 * t^k) := by
      have hbnd : ∀ ω, |a ω * r t ω|
          ≤ ((t^k)^2 * a ω ^ 2 + r t ω ^ 2) / (2 * t^k) := by
        intro ω
        rw [le_div_iff₀ (by positivity)]
        have h1 := sq_nonneg (t^k * a ω - r t ω)
        have h2 := sq_nonneg (t^k * a ω + r t ω)
        rcases abs_cases (a ω * r t ω) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
          nlinarith
      have hint : Integrable
          (fun ω => ((t^k)^2 * a ω ^ 2 + r t ω ^ 2) / (2 * t^k)) μ :=
        ((ha2.const_mul _).add hr2t).div_const _
      calc |∫ ω, a ω * r t ω ∂μ|
          ≤ ∫ ω, |a ω * r t ω| ∂μ := by
            rw [← Real.norm_eq_abs]
            exact (norm_integral_le_integral_norm _).trans_eq
              (by simp [Real.norm_eq_abs])
        _ ≤ ∫ ω, ((t^k)^2 * a ω ^ 2 + r t ω ^ 2) / (2 * t^k) ∂μ :=
            integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun ω => abs_nonneg _)
              hint (Filter.Eventually.of_forall hbnd)
        _ = ((t^k)^2 * A + ∫ ω, r t ω ^ 2 ∂μ) / (2 * t^k) := by
            rw [integral_div, integral_add (ha2.const_mul _) hr2t,
              integral_const_mul]
    -- assemble: |R t| ≤ (k(A+M) + M) · t^{2(k−1)+1}
    have hexp : 2*(k-1)+1 = (k-1) + k := by omega
    have htsplit : t ^ (2*(k-1)+1) = t^(k-1) * t^k := by
      rw [hexp, pow_add]
    have htk1 : (0:ℝ) < t ^ (k-1) := pow_pos htpos _
    have h2k : t ^ (2*k) = (t^k)^2 := by
      rw [two_mul, pow_add, sq]
    -- cross-term contribution
    have hcross2 : (2*(k:ℝ)*t^(k-1)) * |∫ ω, a ω * r t ω ∂μ|
        ≤ (k:ℝ) * (A + M) * (t^(k-1) * t^k) := by
      have hb2 : ((t^k)^2 * A + ∫ ω, r t ω ^ 2 ∂μ) / (2 * t^k)
          ≤ ((t^k)^2 * A + M * (t^k)^2) / (2 * t^k) := by
        apply div_le_div_of_nonneg_right ?_ (by positivity)
        · have := hrbt
          rw [h2k] at this
          linarith
      have hb3 : ((t^k)^2 * A + M * (t^k)^2) / (2 * t^k)
          = (A + M) * t^k / 2 := by
        field_simp
      have hb := (hcross.trans hb2).trans_eq hb3
      calc (2*(k:ℝ)*t^(k-1)) * |∫ ω, a ω * r t ω ∂μ|
          ≤ (2*(k:ℝ)*t^(k-1)) * ((A + M) * t^k / 2) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = (k:ℝ) * (A + M) * (t^(k-1) * t^k) := by ring
    -- second-moment contribution
    have hr2b : (∫ ω, r t ω ^ 2 ∂μ) ≤ M * (t^(k-1) * t^k) := by
      refine hrbt.trans ?_
      have : t ^ (2*k) ≤ t ^ (2*(k-1)+1) :=
        pow_le_pow_of_le_one htpos.le ht1.le (by omega)
      rw [htsplit] at this
      exact mul_le_mul_of_nonneg_left this hM
    -- total
    have habs : |(2*(k:ℝ)*t^(k-1)) * (∫ ω, a ω * r t ω ∂μ)
        + ∫ ω, r t ω ^ 2 ∂μ|
        ≤ (2*(k:ℝ)*t^(k-1)) * |∫ ω, a ω * r t ω ∂μ|
          + ∫ ω, r t ω ^ 2 ∂μ := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*(k:ℝ)*t^(k-1)),
        abs_of_nonneg hr2nn]
    calc |(2*(k:ℝ)*t^(k-1)) * (∫ ω, a ω * r t ω ∂μ) + ∫ ω, r t ω ^ 2 ∂μ|
        ≤ (2*(k:ℝ)*t^(k-1)) * |∫ ω, a ω * r t ω ∂μ|
          + ∫ ω, r t ω ^ 2 ∂μ := habs
      _ ≤ (k:ℝ) * (A + M) * (t^(k-1) * t^k) + M * (t^(k-1) * t^k) := by
          exact add_le_add hcross2 hr2b
      _ = ((k:ℝ) * (A + M) + M) * (t^(k-1) * t^k) := by ring
      _ = ((k:ℝ) * (A + M) + M) * t ^ (2*(k-1)+1) := by rw [htsplit]

/-- thm:fisher_decay, abstract slope form: under the score expansion
    with nondegenerate leading coefficient, the log-log slope of the
    directional Fisher tends to 2(k−1), and k̂ = 1 + slope/2 recovers
    the KL order. -/
theorem fisher_decay_slope
    {s : ℝ → Ω → ℝ} {a : Ω → ℝ} {r : ℝ → Ω → ℝ} {k : ℕ} {M : ℝ}
    (hk : 1 ≤ k) (hM : 0 ≤ M)
    (hs : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ ω, s t ω = k * t ^ (k-1) * a ω + r t ω)
    (ha2 : Integrable (fun ω => a ω ^ 2) μ)
    (hA : 0 < ∫ ω, a ω ^ 2 ∂μ)
    (hr2 : ∀ᶠ t in 𝓝[>] (0:ℝ), Integrable (fun ω => r t ω ^ 2) μ)
    (hra : ∀ᶠ t in 𝓝[>] (0:ℝ), Integrable (fun ω => a ω * r t ω) μ)
    (hrb : ∀ᶠ t in 𝓝[>] (0:ℝ), (∫ ω, r t ω ^ 2 ∂μ) ≤ M * t ^ (2*k)) :
    Tendsto (fun t => Real.log (∫ ω, s t ω ^ 2 ∂μ) / Real.log t)
      (𝓝[>] (0:ℝ)) (𝓝 ((2*(k-1) : ℕ) : ℝ)) := by
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  exact (fisher_expansion_of_score_expansion hk hM hs ha2 hr2 hra hrb).log_slope
    (mul_pos (pow_pos hk0 2) hA)

/-- Leading rates are stable under relatively small perturbation: if
    |G(t) − F(t)| ≤ C·t·F(t) eventually, then G inherits F's leading rate and coefficient. This transfers the
    fixed-measure Fisher rate to the moving-measure convention
    whenever the density ratio is 1 + O(t). -/
theorem HasLeadingRate.of_relatively_close {F G : ℝ → ℝ} {p : ℕ}
    {c C : ℝ} (hF : HasLeadingRate F p c)
    (hclose : ∀ᶠ t in 𝓝[>] (0:ℝ), |G t - F t| ≤ C * t * F t) :
    HasLeadingRate G p c := by
  have htp : ∀ᶠ t in 𝓝[>] (0:ℝ), (0:ℝ) < t ^ p := by
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    exact pow_pos ht p
  have hCt : Tendsto (fun t : ℝ => C * t * (F t / t ^ p))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => C * t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have h : Tendsto (fun t : ℝ => C * t) (𝓝 (0:ℝ)) (𝓝 (C * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h2 := h1.mul hF
    rwa [zero_mul] at h2
  have hCtneg : Tendsto (fun t : ℝ => -(C * t * (F t / t ^ p)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using hCt.neg
  have hdiff : Tendsto (fun t => (G t - F t) / t ^ p)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hCtneg hCt ?_ ?_
    · filter_upwards [hclose, htp] with t hc ht
      have h1 := (abs_le.mp hc).1
      rw [show -(C * t * (F t / t ^ p)) = (-(C * t * F t)) / t ^ p
        from by ring]
      gcongr
    · filter_upwards [hclose, htp] with t hc ht
      have h2 := (abs_le.mp hc).2
      rw [show C * t * (F t / t ^ p) = (C * t * F t) / t ^ p
        from by ring]
      gcongr
  have hsum := hF.add hdiff
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [htp] with t ht
  rw [← add_div]
  congr 1
  ring

end MiddleLayer

/-- Leading rates multiply: rates add, coefficients multiply. This is
    the composition step behind every A·G duality product. -/
theorem HasLeadingRate.mul {F G : ℝ → ℝ} {p q : ℕ} {a b : ℝ}
    (hF : HasLeadingRate F p a) (hG : HasLeadingRate G q b) :
    HasLeadingRate (fun t => F t * G t) (p + q) (a * b) := by
  have h : Tendsto (fun t => (F t / t ^ p) * (G t / t ^ q))
      (𝓝[>] (0:ℝ)) (𝓝 (a * b)) := Filter.Tendsto.mul hF hG
  refine h.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  rw [div_mul_div_comm, ← pow_add]

/-- A positive leading rate sends the observable to zero at the
    boundary. -/
theorem HasLeadingRate.tendsto_zero {F : ℝ → ℝ} {p : ℕ} {c : ℝ}
    (hp : p ≠ 0) (h : HasLeadingRate F p c) :
    Tendsto F (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hpow : Tendsto (fun t : ℝ => t ^ p) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 := (continuous_pow p).tendsto (0:ℝ)
    rw [zero_pow hp] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun t => (F t / t ^ p) * t ^ p)
      (𝓝[>] (0:ℝ)) (𝓝 (c * 0)) := Filter.Tendsto.mul h hpow
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  exact div_mul_cancel₀ (F t) (ne_of_gt (pow_pos ht p))

section CrossMoment

open MeasureTheory

/-- cor:fisher_structure, cross entry: with the transversal score
    expanding as k·t^{k−1}·a + r₁ (remainder L²-bounded at order t^k)
    and the tangential score as b + r₂ (remainder L²-bounded at order
    t), the cross moment expands as k·t^{k−1}·E[ab] with remainder at
    order t^k. Every cross bound is a weighted AM-GM with the weight
    matched to its pairing. -/
theorem cross_moment_expansion {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω}
    {s₁ s₂ : ℝ → Ω → ℝ} {a b : Ω → ℝ} {r₁ r₂ : ℝ → Ω → ℝ} {k : ℕ}
    {M : ℝ} (hk : 1 ≤ k) (hM : 0 ≤ M)
    (hs₁ : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ ω,
      s₁ t ω = k * t ^ (k-1) * a ω + r₁ t ω)
    (hs₂ : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ ω, s₂ t ω = b ω + r₂ t ω)
    (ha2 : Integrable (fun ω => a ω ^ 2) μ)
    (hb2 : Integrable (fun ω => b ω ^ 2) μ)
    (hab : Integrable (fun ω => a ω * b ω) μ)
    (hIr₁ : ∀ᶠ t in 𝓝[>] (0:ℝ), Integrable (fun ω => r₁ t ω ^ 2) μ)
    (hIr₂ : ∀ᶠ t in 𝓝[>] (0:ℝ), Integrable (fun ω => r₂ t ω ^ 2) μ)
    (har₂ : ∀ᶠ t in 𝓝[>] (0:ℝ), Integrable (fun ω => a ω * r₂ t ω) μ)
    (hbr₁ : ∀ᶠ t in 𝓝[>] (0:ℝ), Integrable (fun ω => b ω * r₁ t ω) μ)
    (hr₁r₂ : ∀ᶠ t in 𝓝[>] (0:ℝ),
      Integrable (fun ω => r₁ t ω * r₂ t ω) μ)
    (hr₁b : ∀ᶠ t in 𝓝[>] (0:ℝ),
      (∫ ω, r₁ t ω ^ 2 ∂μ) ≤ M * t ^ (2*k))
    (hr₂b : ∀ᶠ t in 𝓝[>] (0:ℝ), (∫ ω, r₂ t ω ^ 2 ∂μ) ≤ M * t ^ 2) :
    ∀ᶠ t in 𝓝[>] (0:ℝ),
      |(∫ ω, s₁ t ω * s₂ t ω ∂μ)
          - k * t ^ (k-1) * ∫ ω, a ω * b ω ∂μ|
        ≤ ((k:ℝ) * ((∫ ω, a ω ^ 2 ∂μ) + M) / 2
            + ((∫ ω, b ω ^ 2 ∂μ) + M) / 2 + M) * t ^ k := by
  set A := ∫ ω, a ω ^ 2 ∂μ with hA
  set B := ∫ ω, b ω ^ 2 ∂μ with hB
  have hA0 : 0 ≤ A := integral_nonneg fun ω => sq_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun ω => sq_nonneg _
  have hwin : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ t ≤ 1 := by
    filter_upwards [eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with t ht0 ht1
    exact ⟨ht0, ht1.le⟩
  have amgm : ∀ (w u v : ℝ), 0 < w →
      |u * v| ≤ (w * u ^ 2 + (1 / w) * v ^ 2) / 2 := by
    intro w u v hw
    rw [abs_mul, le_div_iff₀ (by norm_num : (0:ℝ) < 2), ← sub_nonneg]
    have hkey : 0 ≤ w ^ 2 * u ^ 2 + v ^ 2 - 2 * w * (|u| * |v|) := by
      nlinarith [sq_nonneg (w * |u| - |v|), sq_abs u, sq_abs v]
    have hexp : w * u ^ 2 + 1 / w * v ^ 2 - |u| * |v| * 2
        = (w ^ 2 * u ^ 2 + v ^ 2 - 2 * w * (|u| * |v|)) / w := by
      field_simp
    rw [hexp]
    exact div_nonneg hkey hw.le
  -- a generic cross-integral bound from the AM-GM dominator
  have crossInt : ∀ (w : ℝ) (f g : Ω → ℝ), 0 < w →
      Integrable (fun ω => f ω * g ω) μ →
      Integrable (fun ω => f ω ^ 2) μ →
      Integrable (fun ω => g ω ^ 2) μ →
      |∫ ω, f ω * g ω ∂μ|
        ≤ (w * ∫ ω, f ω ^ 2 ∂μ + (1 / w) * ∫ ω, g ω ^ 2 ∂μ) / 2 := by
    intro w f g hw hfg hf2 hg2
    have hdomI : Integrable
        (fun ω => (w * f ω ^ 2 + (1 / w) * g ω ^ 2) / 2) μ := by
      have h := (hf2.const_mul w).add (hg2.const_mul (1 / w))
      exact ((h.congr (Filter.Eventually.of_forall fun ω => by
        simp only [Pi.add_apply])).div_const 2)
    calc |∫ ω, f ω * g ω ∂μ|
        ≤ ∫ ω, ‖f ω * g ω‖ ∂μ := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_integral_norm _
      _ ≤ ∫ ω, (w * f ω ^ 2 + (1 / w) * g ω ^ 2) / 2 ∂μ := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun ω => norm_nonneg _) hdomI
            (Filter.Eventually.of_forall fun ω => ?_)
          simp only [Real.norm_eq_abs]
          exact amgm w (f ω) (g ω) hw
      _ = (w * ∫ ω, f ω ^ 2 ∂μ + (1 / w) * ∫ ω, g ω ^ 2 ∂μ) / 2 := by
          rw [integral_div, integral_add (hf2.const_mul w)
            (hg2.const_mul (1 / w)), integral_const_mul,
            integral_const_mul]
  filter_upwards [hwin, hs₁, hs₂, hIr₁, hIr₂, har₂, hbr₁, hr₁r₂,
    hr₁b, hr₂b] with t ht hs₁t hs₂t hIr₁t hIr₂t har₂t hbr₁t hr₁r₂t
    hr₁bt hr₂bt
  obtain ⟨ht0, ht1⟩ := ht
  have htk : (0:ℝ) < t ^ k := pow_pos ht0 k
  have hIr₂nn : 0 ≤ ∫ ω, r₂ t ω ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg _
  have hIr₁nn : 0 ≤ ∫ ω, r₁ t ω ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg _
  -- the four-term split of the cross moment
  have hI1 : Integrable (fun ω => ((k:ℝ) * t ^ (k-1)) * (a ω * b ω)) μ :=
    hab.const_mul _
  have hI2 : Integrable
      (fun ω => ((k:ℝ) * t ^ (k-1)) * (a ω * r₂ t ω)) μ :=
    har₂t.const_mul _
  have hI34 : Integrable
      (fun ω => b ω * r₁ t ω + r₁ t ω * r₂ t ω) μ := by
    have h := hbr₁t.add hr₁r₂t
    exact h.congr (Filter.Eventually.of_forall fun ω => by
      simp only [Pi.add_apply])
  have hI234 : Integrable
      (fun ω => ((k:ℝ) * t ^ (k-1)) * (a ω * r₂ t ω)
        + (b ω * r₁ t ω + r₁ t ω * r₂ t ω)) μ := by
    have h := hI2.add hI34
    exact h.congr (Filter.Eventually.of_forall fun ω => by
      simp only [Pi.add_apply])
  have hsplit : (∫ ω, s₁ t ω * s₂ t ω ∂μ)
      - (k:ℝ) * t ^ (k-1) * ∫ ω, a ω * b ω ∂μ
      = ((k:ℝ) * t ^ (k-1)) * (∫ ω, a ω * r₂ t ω ∂μ)
        + ((∫ ω, b ω * r₁ t ω ∂μ) + ∫ ω, r₁ t ω * r₂ t ω ∂μ) := by
    have hfun : (fun ω => s₁ t ω * s₂ t ω)
        = fun ω => ((k:ℝ) * t ^ (k-1)) * (a ω * b ω)
          + (((k:ℝ) * t ^ (k-1)) * (a ω * r₂ t ω)
            + (b ω * r₁ t ω + r₁ t ω * r₂ t ω)) := by
      funext ω
      rw [hs₁t ω, hs₂t ω]
      ring
    rw [hfun, integral_add hI1 hI234, integral_add hI2 hI34,
      integral_add hbr₁t hr₁r₂t, integral_const_mul,
      integral_const_mul]
    ring
  rw [hsplit]
  -- the three cross bounds, each with its matched weight
  have hb1 : |∫ ω, a ω * r₂ t ω ∂μ| ≤ t * (A + M) / 2 := by
    have h := crossInt t a (r₂ t) ht0 har₂t ha2 hIr₂t
    have hr : (1 / t) * ∫ ω, r₂ t ω ^ 2 ∂μ ≤ M * t := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ ht0]
      calc ∫ ω, r₂ t ω ^ 2 ∂μ ≤ M * t ^ 2 := hr₂bt
        _ = M * t * t := by ring
    calc |∫ ω, a ω * r₂ t ω ∂μ|
        ≤ (t * A + (1 / t) * ∫ ω, r₂ t ω ^ 2 ∂μ) / 2 := h
      _ ≤ (t * A + M * t) / 2 := by linarith
      _ = t * (A + M) / 2 := by ring
  have hb2 : |∫ ω, b ω * r₁ t ω ∂μ| ≤ t ^ k * (B + M) / 2 := by
    have h := crossInt (t ^ k) b (r₁ t) htk hbr₁t hb2 hIr₁t
    have hr : (1 / t ^ k) * ∫ ω, r₁ t ω ^ 2 ∂μ ≤ M * t ^ k := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ htk]
      calc ∫ ω, r₁ t ω ^ 2 ∂μ ≤ M * t ^ (2*k) := hr₁bt
        _ = M * t ^ k * t ^ k := by
            rw [two_mul, pow_add]
            ring
    calc |∫ ω, b ω * r₁ t ω ∂μ|
        ≤ (t ^ k * B + (1 / t ^ k) * ∫ ω, r₁ t ω ^ 2 ∂μ) / 2 := h
      _ ≤ (t ^ k * B + M * t ^ k) / 2 := by linarith
      _ = t ^ k * (B + M) / 2 := by ring
  have hb3 : |∫ ω, r₁ t ω * r₂ t ω ∂μ| ≤ M * t ^ k := by
    have hw : (0:ℝ) < t / t ^ k := div_pos ht0 htk
    have h := crossInt (t / t ^ k) (r₁ t) (r₂ t) hw hr₁r₂t hIr₁t hIr₂t
    have hr1 : (t / t ^ k) * ∫ ω, r₁ t ω ^ 2 ∂μ ≤ M * t ^ (k+1) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ htk]
      calc t * ∫ ω, r₁ t ω ^ 2 ∂μ
          ≤ t * (M * t ^ (2*k)) :=
            mul_le_mul_of_nonneg_left hr₁bt ht0.le
        _ = M * t ^ (k+1) * t ^ k := by
            rw [two_mul, pow_add, pow_succ]
            ring
    have hr2 : (1 / (t / t ^ k)) * ∫ ω, r₂ t ω ^ 2 ∂μ
        ≤ M * t ^ (k+1) := by
      rw [one_div_div, div_mul_eq_mul_div, div_le_iff₀ ht0]
      calc t ^ k * ∫ ω, r₂ t ω ^ 2 ∂μ
          ≤ t ^ k * (M * t ^ 2) :=
            mul_le_mul_of_nonneg_left hr₂bt htk.le
        _ = M * t ^ (k+1) * t := by
            rw [pow_succ]
            ring
    have htk1 : t ^ (k+1) ≤ t ^ k :=
      pow_le_pow_of_le_one ht0.le ht1 (by omega)
    calc |∫ ω, r₁ t ω * r₂ t ω ∂μ|
        ≤ ((t / t ^ k) * ∫ ω, r₁ t ω ^ 2 ∂μ
          + (1 / (t / t ^ k)) * ∫ ω, r₂ t ω ^ 2 ∂μ) / 2 := h
      _ ≤ (M * t ^ (k+1) + M * t ^ (k+1)) / 2 := by linarith
      _ = M * t ^ (k+1) := by ring
      _ ≤ M * t ^ k := mul_le_mul_of_nonneg_left htk1 hM
  -- assemble
  have habs := abs_add_le (((k:ℝ) * t ^ (k-1))
      * (∫ ω, a ω * r₂ t ω ∂μ))
    ((∫ ω, b ω * r₁ t ω ∂μ) + ∫ ω, r₁ t ω * r₂ t ω ∂μ)
  have habs2 := abs_add_le (∫ ω, b ω * r₁ t ω ∂μ)
    (∫ ω, r₁ t ω * r₂ t ω ∂μ)
  have hfirst : |((k:ℝ) * t ^ (k-1)) * (∫ ω, a ω * r₂ t ω ∂μ)|
      ≤ (k:ℝ) * (A + M) / 2 * t ^ k := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ) * t ^ (k-1))]
    have h := mul_le_mul_of_nonneg_left hb1
      (by positivity : (0:ℝ) ≤ (k:ℝ) * t ^ (k-1))
    calc (k:ℝ) * t ^ (k-1) * |∫ ω, a ω * r₂ t ω ∂μ|
        ≤ (k:ℝ) * t ^ (k-1) * (t * (A + M) / 2) := h
      _ = (k:ℝ) * (A + M) / 2 * (t ^ (k-1) * t) := by ring
      _ = (k:ℝ) * (A + M) / 2 * t ^ k := by
          rw [← pow_succ]
          congr 2
          omega
  calc |((k:ℝ) * t ^ (k-1)) * (∫ ω, a ω * r₂ t ω ∂μ)
        + ((∫ ω, b ω * r₁ t ω ∂μ) + ∫ ω, r₁ t ω * r₂ t ω ∂μ)|
      ≤ |((k:ℝ) * t ^ (k-1)) * (∫ ω, a ω * r₂ t ω ∂μ)|
        + (|∫ ω, b ω * r₁ t ω ∂μ| + |∫ ω, r₁ t ω * r₂ t ω ∂μ|) := by
        linarith [habs, habs2]
    _ ≤ (k:ℝ) * (A + M) / 2 * t ^ k + (t ^ k * (B + M) / 2 + M * t ^ k) := by
        linarith [hfirst, hb2, hb3]
    _ = ((k:ℝ) * (A + M) / 2 + (B + M) / 2 + M) * t ^ k := by ring


/-- Weighted AM-GM for a product: |uv| ≤ (w·u² + v²/w)/2 at any
    positive weight. -/
lemma abs_mul_le_weighted_amgm (w u v : ℝ) (hw : 0 < w) :
    |u * v| ≤ (w * u ^ 2 + (1 / w) * v ^ 2) / 2 := by
  rw [abs_mul, le_div_iff₀ (by norm_num : (0:ℝ) < 2), ← sub_nonneg]
  have hkey : 0 ≤ w ^ 2 * u ^ 2 + v ^ 2 - 2 * w * (|u| * |v|) := by
    nlinarith [sq_nonneg (w * |u| - |v|), sq_abs u, sq_abs v]
  have hexp : w * u ^ 2 + 1 / w * v ^ 2 - |u| * |v| * 2
      = (w ^ 2 * u ^ 2 + v ^ 2 - 2 * w * (|u| * |v|)) / w := by
    field_simp
  rw [hexp]
  exact div_nonneg hkey hw.le

/-- The weighted cross-integral bound behind every Fisher cross
    entry. -/
lemma abs_integral_mul_le_weighted {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (w : ℝ) (f g : Ω → ℝ) (hw : 0 < w)
    (_hfg : Integrable (fun ω => f ω * g ω) μ)
    (hf2 : Integrable (fun ω => f ω ^ 2) μ)
    (hg2 : Integrable (fun ω => g ω ^ 2) μ) :
    |∫ ω, f ω * g ω ∂μ|
      ≤ (w * ∫ ω, f ω ^ 2 ∂μ + (1 / w) * ∫ ω, g ω ^ 2 ∂μ) / 2 := by
  have hdomI : Integrable
      (fun ω => (w * f ω ^ 2 + (1 / w) * g ω ^ 2) / 2) μ := by
    have h := (hf2.const_mul w).add (hg2.const_mul (1 / w))
    exact ((h.congr (Filter.Eventually.of_forall fun ω => by
      simp only [Pi.add_apply])).div_const 2)
  calc |∫ ω, f ω * g ω ∂μ|
      ≤ ∫ ω, ‖f ω * g ω‖ ∂μ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (w * f ω ^ 2 + (1 / w) * g ω ^ 2) / 2 ∂μ := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ω => norm_nonneg _) hdomI
          (Filter.Eventually.of_forall fun ω => ?_)
        simp only [Real.norm_eq_abs]
        exact abs_mul_le_weighted_amgm w (f ω) (g ω) hw
    _ = (w * ∫ ω, f ω ^ 2 ∂μ + (1 / w) * ∫ ω, g ω ^ 2 ∂μ) / 2 := by
        rw [integral_div, integral_add (hf2.const_mul w)
          (hg2.const_mul (1 / w)), integral_const_mul,
          integral_const_mul]

/-- cor:fisher_structure, tangential block: with both scores a
    bounded part plus an L²-remainder of order t, the tangential
    moment is the Gram entry up to O(t): F_αβ = g_αβ + O(t), with the
    explicit constant. -/
theorem tangential_moment_expansion {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω}
    {s₁ s₂ : ℝ → Ω → ℝ} {b₁ b₂ : Ω → ℝ} {r₁ r₂ : ℝ → Ω → ℝ}
    {M : ℝ} (hM : 0 ≤ M)
    (hs₁ : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ ω, s₁ t ω = b₁ ω + r₁ t ω)
    (hs₂ : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ ω, s₂ t ω = b₂ ω + r₂ t ω)
    (hb₁2 : Integrable (fun ω => b₁ ω ^ 2) μ)
    (hb₂2 : Integrable (fun ω => b₂ ω ^ 2) μ)
    (hbb : Integrable (fun ω => b₁ ω * b₂ ω) μ)
    (hIr₁ : ∀ᶠ t in 𝓝[>] (0:ℝ), Integrable (fun ω => r₁ t ω ^ 2) μ)
    (hIr₂ : ∀ᶠ t in 𝓝[>] (0:ℝ), Integrable (fun ω => r₂ t ω ^ 2) μ)
    (hbr₂ : ∀ᶠ t in 𝓝[>] (0:ℝ), Integrable (fun ω => b₁ ω * r₂ t ω) μ)
    (hbr₁ : ∀ᶠ t in 𝓝[>] (0:ℝ), Integrable (fun ω => b₂ ω * r₁ t ω) μ)
    (hr₁r₂ : ∀ᶠ t in 𝓝[>] (0:ℝ),
      Integrable (fun ω => r₁ t ω * r₂ t ω) μ)
    (hr₁b : ∀ᶠ t in 𝓝[>] (0:ℝ), (∫ ω, r₁ t ω ^ 2 ∂μ) ≤ M * t ^ 2)
    (hr₂b : ∀ᶠ t in 𝓝[>] (0:ℝ), (∫ ω, r₂ t ω ^ 2 ∂μ) ≤ M * t ^ 2) :
    ∀ᶠ t in 𝓝[>] (0:ℝ),
      |(∫ ω, s₁ t ω * s₂ t ω ∂μ) - ∫ ω, b₁ ω * b₂ ω ∂μ|
        ≤ (((∫ ω, b₁ ω ^ 2 ∂μ) + M) / 2
            + ((∫ ω, b₂ ω ^ 2 ∂μ) + M) / 2 + M) * t := by
  set B₁ := ∫ ω, b₁ ω ^ 2 ∂μ with hB₁
  set B₂ := ∫ ω, b₂ ω ^ 2 ∂μ with hB₂
  have hwin : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ t ≤ 1 := by
    filter_upwards [eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with t ht0 ht1
    exact ⟨ht0, ht1.le⟩
  filter_upwards [hwin, hs₁, hs₂, hIr₁, hIr₂, hbr₂, hbr₁, hr₁r₂,
    hr₁b, hr₂b] with t ht hs₁t hs₂t hIr₁t hIr₂t hbr₂t hbr₁t hr₁r₂t
    hr₁bt hr₂bt
  obtain ⟨ht0, ht1⟩ := ht
  have hI34 : Integrable
      (fun ω => b₂ ω * r₁ t ω + r₁ t ω * r₂ t ω) μ := by
    have h := hbr₁t.add hr₁r₂t
    exact h.congr (Filter.Eventually.of_forall fun ω => by
      simp only [Pi.add_apply])
  have hI234 : Integrable
      (fun ω => b₁ ω * r₂ t ω
        + (b₂ ω * r₁ t ω + r₁ t ω * r₂ t ω)) μ := by
    have h := hbr₂t.add hI34
    exact h.congr (Filter.Eventually.of_forall fun ω => by
      simp only [Pi.add_apply])
  have hsplit : (∫ ω, s₁ t ω * s₂ t ω ∂μ) - ∫ ω, b₁ ω * b₂ ω ∂μ
      = (∫ ω, b₁ ω * r₂ t ω ∂μ)
        + ((∫ ω, b₂ ω * r₁ t ω ∂μ) + ∫ ω, r₁ t ω * r₂ t ω ∂μ) := by
    have hfun : (fun ω => s₁ t ω * s₂ t ω)
        = fun ω => b₁ ω * b₂ ω
          + (b₁ ω * r₂ t ω
            + (b₂ ω * r₁ t ω + r₁ t ω * r₂ t ω)) := by
      funext ω
      rw [hs₁t ω, hs₂t ω]
      ring
    rw [hfun, integral_add hbb hI234, integral_add hbr₂t hI34,
      integral_add hbr₁t hr₁r₂t]
    ring
  rw [hsplit]
  have hb1 : |∫ ω, b₁ ω * r₂ t ω ∂μ| ≤ t * (B₁ + M) / 2 := by
    have h := abs_integral_mul_le_weighted t b₁ (r₂ t) ht0 hbr₂t
      hb₁2 hIr₂t
    have hr : (1 / t) * ∫ ω, r₂ t ω ^ 2 ∂μ ≤ M * t := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ ht0]
      calc ∫ ω, r₂ t ω ^ 2 ∂μ ≤ M * t ^ 2 := hr₂bt
        _ = M * t * t := by ring
    calc |∫ ω, b₁ ω * r₂ t ω ∂μ|
        ≤ (t * B₁ + (1 / t) * ∫ ω, r₂ t ω ^ 2 ∂μ) / 2 := h
      _ ≤ (t * B₁ + M * t) / 2 := by linarith
      _ = t * (B₁ + M) / 2 := by ring
  have hb2 : |∫ ω, b₂ ω * r₁ t ω ∂μ| ≤ t * (B₂ + M) / 2 := by
    have h := abs_integral_mul_le_weighted t b₂ (r₁ t) ht0 hbr₁t
      hb₂2 hIr₁t
    have hr : (1 / t) * ∫ ω, r₁ t ω ^ 2 ∂μ ≤ M * t := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ ht0]
      calc ∫ ω, r₁ t ω ^ 2 ∂μ ≤ M * t ^ 2 := hr₁bt
        _ = M * t * t := by ring
    calc |∫ ω, b₂ ω * r₁ t ω ∂μ|
        ≤ (t * B₂ + (1 / t) * ∫ ω, r₁ t ω ^ 2 ∂μ) / 2 := h
      _ ≤ (t * B₂ + M * t) / 2 := by linarith
      _ = t * (B₂ + M) / 2 := by ring
  have hb3 : |∫ ω, r₁ t ω * r₂ t ω ∂μ| ≤ M * t := by
    have h := abs_integral_mul_le_weighted 1 (r₁ t) (r₂ t) one_pos
      hr₁r₂t hIr₁t hIr₂t
    have ht2 : M * t ^ 2 ≤ M * t := by
      have : t ^ 2 ≤ t := by nlinarith
      exact mul_le_mul_of_nonneg_left this hM
    calc |∫ ω, r₁ t ω * r₂ t ω ∂μ|
        ≤ (1 * ∫ ω, r₁ t ω ^ 2 ∂μ
          + (1 / 1) * ∫ ω, r₂ t ω ^ 2 ∂μ) / 2 := h
      _ ≤ (M * t ^ 2 + M * t ^ 2) / 2 := by
          have h1 := hr₁bt
          have h2 := hr₂bt
          norm_num
          linarith
      _ = M * t ^ 2 := by ring
      _ ≤ M * t := ht2
  have habs := abs_add_le (∫ ω, b₁ ω * r₂ t ω ∂μ)
    ((∫ ω, b₂ ω * r₁ t ω ∂μ) + ∫ ω, r₁ t ω * r₂ t ω ∂μ)
  have habs2 := abs_add_le (∫ ω, b₂ ω * r₁ t ω ∂μ)
    (∫ ω, r₁ t ω * r₂ t ω ∂μ)
  calc |(∫ ω, b₁ ω * r₂ t ω ∂μ)
        + ((∫ ω, b₂ ω * r₁ t ω ∂μ) + ∫ ω, r₁ t ω * r₂ t ω ∂μ)|
      ≤ |∫ ω, b₁ ω * r₂ t ω ∂μ|
        + (|∫ ω, b₂ ω * r₁ t ω ∂μ| + |∫ ω, r₁ t ω * r₂ t ω ∂μ|) := by
        linarith [habs, habs2]
    _ ≤ t * (B₁ + M) / 2 + (t * (B₂ + M) / 2 + M * t) := by
        linarith [hb1, hb2, hb3]
    _ = ((B₁ + M) / 2 + (B₂ + M) / 2 + M) * t := by ring


end CrossMoment

/-- t^m has leading rate m with coefficient one. -/
theorem hasLeadingRate_pow (m : ℕ) :
    HasLeadingRate (fun t : ℝ => t ^ m) m 1 := by
  refine (tendsto_const_nhds (X := ℝ) (x := (1:ℝ))
    (f := 𝓝[>] (0:ℝ))).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  exact (div_self (ne_of_gt (pow_pos ht m))).symm

/-- The smaller rate wins in a sum: the two-route minimum. When two
    backward routes reach the same component, the measured rate is
    the smaller route's. -/
theorem HasLeadingRate.add_of_lt {F G : ℝ → ℝ} {p q : ℕ} {a b : ℝ}
    (hF : HasLeadingRate F p a) (hG : HasLeadingRate G q b)
    (hpq : p < q) :
    HasLeadingRate (fun t => F t + G t) p a := by
  have hpow : Tendsto (fun t : ℝ => t ^ (q - p)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := (continuous_pow (q - p)).tendsto (0:ℝ)
    rw [zero_pow (by omega : q - p ≠ 0)] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hG0 : Tendsto (fun t => G t / t ^ p) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h : Tendsto (fun t => (G t / t ^ q) * t ^ (q - p))
        (𝓝[>] (0:ℝ)) (𝓝 (b * 0)) := Filter.Tendsto.mul hG hpow
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    have hq : t ^ q = t ^ p * t ^ (q - p) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hq, div_mul_eq_div_div,
      div_mul_cancel₀ _ (ne_of_gt (pow_pos ht (q - p)))]
  have hsum := hF.add hG0
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [] with t
  exact (add_div _ _ _).symm

/-- Tied rates add coefficients: the tie case of the two-route
    reading. -/
theorem HasLeadingRate.add_of_eq {F G : ℝ → ℝ} {p : ℕ} {a b : ℝ}
    (hF : HasLeadingRate F p a) (hG : HasLeadingRate G p b) :
    HasLeadingRate (fun t => F t + G t) p (a + b) := by
  have h := hF.add hG
  refine h.congr' ?_
  filter_upwards [] with t
  exact (add_div _ _ _).symm

/-- Subtracting a faster-decaying term leaves the rate and
    coefficient. -/
theorem HasLeadingRate.sub_of_lt {F G : ℝ → ℝ} {p q : ℕ} {a b : ℝ}
    (hF : HasLeadingRate F p a) (hG : HasLeadingRate G q b)
    (hpq : p < q) :
    HasLeadingRate (fun t => F t - G t) p a := by
  have hneg : HasLeadingRate (fun t => -1 * G t) q (-1 * b) := by
    have h2 := Filter.Tendsto.const_mul (-1 : ℝ) hG
    refine h2.congr fun t => ?_
    exact (mul_div_assoc (-1) (G t) (t ^ q)).symm
  have h := hF.add_of_lt hneg hpq
  refine h.congr fun t => ?_
  ring_nf

/-- The minimum of two functions with one leading rate carries that
    rate with the smaller coefficient: the per-block minimum of
    same-rate blocks keeps the rate. -/
theorem HasLeadingRate.min_of_eq {F G : ℝ → ℝ} {p : ℕ} {a b : ℝ}
    (hF : HasLeadingRate F p a) (hG : HasLeadingRate G p b) :
    HasLeadingRate (fun t => min (F t) (G t)) p (min a b) := by
  have h := hF.min hG
  refine h.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht0
  have ht : (0:ℝ) < t := ht0
  have hinv : (0:ℝ) ≤ (t ^ p)⁻¹ := inv_nonneg.mpr (pow_nonneg ht.le p)
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    ← min_mul_of_nonneg _ _ hinv]

/-- A power times a factor continuous at zero has that power as its
    leading rate, with the factor's value as coefficient. -/
theorem hasLeadingRate_pow_factor (m : ℕ) {g : ℝ → ℝ}
    (hg : ContinuousAt g 0) :
    HasLeadingRate (fun t => t ^ m * g t) m (g 0) := by
  have hlim : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 (g 0)) :=
    hg.tendsto.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht0
  rw [mul_comm, mul_div_assoc, div_self (pow_ne_zero m (ne_of_gt ht0)),
    mul_one]

/-- Constant scaling preserves the leading rate and scales the
    coefficient. -/
theorem HasLeadingRate.const_mul {F : ℝ → ℝ} {p : ℕ} {a : ℝ}
    (hF : HasLeadingRate F p a) (c : ℝ) :
    HasLeadingRate (fun t => c * F t) p (c * a) := by
  have h := Filter.Tendsto.const_mul c hF
  refine h.congr fun t => ?_
  exact (mul_div_assoc c (F t) (t ^ p)).symm


/-- Rates survive reparameterisation of the approach: composing with
    any parameter change of leading rate one keeps the rate and
    multiplies the coefficient by c^p. Arc length is the instance
    with c the inverse approach speed, so the log-slope reading is
    parameterisation-independent. -/
theorem HasLeadingRate.comp_reparam {F φ : ℝ → ℝ} {p : ℕ} {a c : ℝ}
    (hF : HasLeadingRate F p a) (hφ : HasLeadingRate φ 1 c)
    (hc : 0 < c) :
    HasLeadingRate (fun s => F (φ s)) p (a * c ^ p) := by
  have hpos : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < φ s := by
    filter_upwards [hφ.eventually (lt_mem_nhds (half_lt_self hc)),
      eventually_mem_nhdsWithin] with s h hs
    rw [pow_one] at h
    have h2 : 0 < φ s / s := lt_trans (half_pos hc) h
    by_contra hneg
    push Not at hneg
    have h3 : φ s / s ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hneg (le_of_lt hs)
    linarith
  have hφ0 : Tendsto φ (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hφ.tendsto_zero one_ne_zero, ?_⟩
    filter_upwards [hpos] with s hs
    exact hs
  have h1 : Tendsto (fun s => F (φ s) / (φ s) ^ p)
      (𝓝[>] (0:ℝ)) (𝓝 a) :=
    (hF.comp hφ0).congr fun s => rfl
  have h2 : Tendsto (fun s => (φ s / s) ^ p)
      (𝓝[>] (0:ℝ)) (𝓝 (c ^ p)) := by
    have h' : Tendsto (fun s => φ s / s) (𝓝[>] (0:ℝ)) (𝓝 c) :=
      hφ.congr fun s => by rw [pow_one]
    exact h'.pow p
  have h3 := h1.mul h2
  refine h3.congr' ?_
  filter_upwards [hpos, eventually_mem_nhdsWithin] with s hφs hs
  rw [div_pow]
  have hφne : (φ s) ^ p ≠ 0 := pow_ne_zero p (ne_of_gt hφs)
  have hsne : (s:ℝ) ^ p ≠ 0 := pow_ne_zero p (ne_of_gt hs)
  field_simp

/-- The k̂ reading is invariant under approach reparameterisation:
    the reparameterised observable reads the same log-slope p. -/
theorem khat_reparam_invariant {F φ : ℝ → ℝ} {p : ℕ} {a c : ℝ}
    (hF : HasLeadingRate F p a) (hφ : HasLeadingRate φ 1 c)
    (hc : 0 < c) (ha : 0 < a) :
    Tendsto (fun s => Real.log (F (φ s)) / Real.log s)
      (𝓝[>] (0:ℝ)) (𝓝 p) :=
  (hF.comp_reparam hφ hc).log_slope (by positivity)


/-- A constant has leading rate zero with itself as coefficient. -/
theorem hasLeadingRate_const (c : ℝ) :
    HasLeadingRate (fun _ : ℝ => c) 0 c := by
  refine (tendsto_const_nhds (X := ℝ) (x := c)
    (f := 𝓝[>] (0:ℝ))).congr fun t => ?_
  rw [pow_zero, div_one]

/-- A positive leading coefficient makes the observable eventually
    positive. -/
theorem HasLeadingRate.eventually_pos {F : ℝ → ℝ} {p : ℕ} {a : ℝ}
    (hF : HasLeadingRate F p a) (ha : 0 < a) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < F t := by
  filter_upwards [hF.eventually (lt_mem_nhds (half_lt_self ha)),
    eventually_mem_nhdsWithin] with t h ht
  have htp : 0 < t ^ p := pow_pos ht p
  have h2 : 0 < F t / t ^ p := lt_trans (half_pos ha) h
  by_contra hneg
  push Not at hneg
  have h3 : F t / t ^ p ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg htp.le
  linarith

/-- Leading rates divide: rates subtract and coefficients divide when
    the denominator's coefficient is positive. -/
theorem HasLeadingRate.div {F G : ℝ → ℝ} {p q : ℕ} {a b : ℝ}
    (hF : HasLeadingRate F p a) (hG : HasLeadingRate G q b)
    (hb : 0 < b) (hqp : q ≤ p) :
    HasLeadingRate (fun t => F t / G t) (p - q) (a / b) := by
  have h : Tendsto (fun t => (F t / t ^ p) / (G t / t ^ q))
      (𝓝[>] (0:ℝ)) (𝓝 (a / b)) :=
    Filter.Tendsto.div hF hG (ne_of_gt hb)
  refine h.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin, hG.eventually_pos hb]
    with t ht hGt
  have htq : t ^ q ≠ 0 := ne_of_gt (pow_pos ht q)
  have htpq : t ^ (p - q) ≠ 0 := ne_of_gt (pow_pos ht _)
  have hGne : G t ≠ 0 := ne_of_gt hGt
  have hsplit : t ^ p = t ^ (p - q) * t ^ q := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit]
  field_simp

end DeadDirections
