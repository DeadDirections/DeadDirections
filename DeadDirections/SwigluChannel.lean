/-
  The SwiGLU dead channel (theory paper, prop:swiglu_rate and the
  composition remark).

  At canonical init all three Linear layers carry weight t on the dead
  dimension, so the dead-channel map is exactly
  t·silu(t·x)·(t·x) = t³·x²·σ(t·x) with σ the logistic sigmoid. Since
  |σ(u) − 1/2| ≤ |u|/2, the output is (1/2)·t³·x² up to an explicit
  O(t⁴) remainder: forward block rate 3, coefficient 1/2, the extra
  factor against the standard MLP's rate 2 coming from the gate. The
  second moment under N(0,1) has leading rate 6 with coefficient
  (1/4)·E[x⁴] (Mathlib carries no Gaussian moment formula, so the
  fourth moment stays as an integral).

  The composition remark is the algebra of the idealised block
  B(x) = c·t³·x²: because B is quadratic in the dead coordinate, the
  n-fold composite carries t-power 3·(2ⁿ − 1) and not 3n. Machine-
  checked below as quadBlock_iterate.
-/
import DeadDirections.MixtureScore

namespace DeadDirections

open MeasureTheory Filter Topology

/-! ### The sigmoid and its half-point expansion -/

/-- The logistic sigmoid. -/
noncomputable def sigmoid (y : ℝ) : ℝ := 1 / (1 + Real.exp (-y))

lemma sigmoid_pos (y : ℝ) : 0 < sigmoid y := by
  unfold sigmoid
  positivity

lemma sigmoid_le_one (y : ℝ) : sigmoid y ≤ 1 := by
  unfold sigmoid
  rw [div_le_one (by positivity)]
  linarith [Real.exp_pos (-y)]

lemma sigmoid_add_sigmoid_neg (y : ℝ) : sigmoid y + sigmoid (-y) = 1 := by
  unfold sigmoid
  rw [neg_neg]
  have h1 : (0:ℝ) < 1 + Real.exp (-y) := by positivity
  have h2 : (0:ℝ) < 1 + Real.exp y := by positivity
  have hmul : Real.exp (-y) * Real.exp y = 1 := by
    rw [← Real.exp_add]
    simp
  field_simp
  nlinarith [hmul]

/-- The sigmoid leaves its half-point at unit speed at worst:
    |σ(y) − 1/2| ≤ |y|/2. -/
lemma abs_sigmoid_sub_half (y : ℝ) : |sigmoid y - 1/2| ≤ |y| / 2 := by
  have key : ∀ z : ℝ, 0 ≤ z → sigmoid z - 1/2 ≤ z / 2 := by
    intro z hz
    unfold sigmoid
    have hden : (0:ℝ) < 1 + Real.exp (-z) := by positivity
    have h2 : 1 / (1 + Real.exp (-z)) - 1/2
        = (1 - Real.exp (-z)) / (2 * (1 + Real.exp (-z))) := by
      field_simp
      ring
    have hexp : 1 - z ≤ Real.exp (-z) := by
      have h := Real.add_one_le_exp (-z)
      linarith
    rw [h2, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
    nlinarith [Real.exp_pos (-z), hexp]
  have keynn : ∀ z : ℝ, 0 ≤ z → 0 ≤ sigmoid z - 1/2 := by
    intro z hz
    unfold sigmoid
    have hden : (0:ℝ) < 1 + Real.exp (-z) := by positivity
    have hexp : Real.exp (-z) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    rw [sub_nonneg, le_div_iff₀ hden]
    linarith
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg (keynn y hy), abs_of_nonneg hy]
    exact key y hy
  · have hy' : 0 ≤ -y := by linarith
    have h1 := key (-y) hy'
    have h2 := keynn (-y) hy'
    have hflip : sigmoid y - 1/2 = -(sigmoid (-y) - 1/2) := by
      have := sigmoid_add_sigmoid_neg y
      linarith
    rw [hflip, abs_neg, abs_of_nonneg h2, abs_of_neg hy]
    linarith

/-! ### The SwiGLU dead channel -/

/-- silu(y) = y·σ(y). -/
noncomputable def silu (y : ℝ) : ℝ := y * sigmoid y

/-- The SwiGLU dead-channel map at canonical init: the down-projection
    weight t times the elementwise product silu(gate)·up, with gate
    and up both t·x at the dead dimension. -/
noncomputable def swigluDead (t x : ℝ) : ℝ := t * (silu (t * x) * (t * x))

/-- The channel in closed form: t³·x²·σ(t·x). -/
lemma swigluDead_eq (t x : ℝ) :
    swigluDead t x = t ^ 3 * x ^ 2 * sigmoid (t * x) := by
  unfold swigluDead silu
  ring

/-- prop:swiglu_rate, pointwise form: the dead-channel output is
    (1/2)·t³·x² up to an explicit remainder of order t⁴. The forward
    block rate is 3 with coefficient 1/2. -/
theorem swigluDead_sub_le {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    |swigluDead t x - 1/2 * t ^ 3 * x ^ 2| ≤ t ^ 4 * |x| ^ 3 / 2 := by
  rw [swigluDead_eq,
    show t ^ 3 * x ^ 2 * sigmoid (t * x) - 1/2 * t ^ 3 * x ^ 2
      = t ^ 3 * x ^ 2 * (sigmoid (t * x) - 1/2) from by ring,
    abs_mul, abs_mul]
  have h1 := abs_sigmoid_sub_half (t * x)
  rw [abs_mul, abs_of_nonneg ht] at h1
  have hnn : (0:ℝ) ≤ |t ^ 3| * |x ^ 2| :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc |t ^ 3| * |x ^ 2| * |sigmoid (t * x) - 1/2|
      ≤ |t ^ 3| * |x ^ 2| * (t * |x| / 2) :=
        mul_le_mul_of_nonneg_left h1 hnn
    _ = t ^ 4 * |x| ^ 3 / 2 := by
        rw [abs_of_nonneg (pow_nonneg ht 3), abs_of_nonneg (sq_nonneg x),
          show x ^ 2 = |x| ^ 2 from (sq_abs x).symm]
        ring

/-- The moment integrability toolkit: |x|³, x⁴, |x|⁵, x⁶ against the
    Gaussian, from the even-moment workhorse. -/
lemma integrable_abs_pow_gaussMeasure (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) gaussMeasure := by
  rw [integrable_gaussMeasure_iff]
  have hdom : Integrable (fun x : ℝ =>
      (x ^ (2 * n) + 1) * gaussDensity x 0 1) := by
    have h1 : Integrable (fun x : ℝ => x ^ (2 * n) * gaussDensity x 0 1) :=
      (integrable_pow_mul_exp_mul_gaussDensity (2 * n) 0).congr
        (Filter.Eventually.of_forall fun x => by simp)
    have h2 := integrable_gaussDensity 0
    exact (h1.add h2).congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.add_apply]
      ring)
  refine hdom.mono' ((continuous_abs.pow n).mul
    (continuous_gaussDensity 0)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hg := (gaussDensity_pos x 0).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg
    (abs_nonneg x) n) hg)]
  have hev : |x| ^ (2 * n) = x ^ (2 * n) := by
    rw [← abs_pow, abs_of_nonneg ((even_two_mul n).pow_nonneg x)]
  have hcase : |x| ^ n ≤ x ^ (2 * n) + 1 := by
    rcases le_or_gt |x| 1 with h | h
    · have h1 := pow_le_one₀ (abs_nonneg x) h (n := n)
      have h2 : (0:ℝ) ≤ x ^ (2 * n) := (even_two_mul n).pow_nonneg x
      linarith
    · have h1 : |x| ^ n ≤ |x| ^ (2 * n) :=
        pow_le_pow_right₀ h.le (by omega)
      rw [hev] at h1
      linarith
  nlinarith [mul_le_mul_of_nonneg_right hcase hg,
    mul_nonneg (pow_nonneg (abs_nonneg x) n) hg]

lemma integrable_pow_gaussMeasure (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) gaussMeasure := by
  refine (integrable_abs_pow_gaussMeasure n).mono'
    (continuous_pow n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow]

/-- prop:swiglu_rate, moment form: the dead-channel second moment
    carries leading rate 6 = 2·3 with coefficient (1/4)·E[x⁴]. -/
theorem swiglu_channel_hasLeadingRate :
    HasLeadingRate
      (fun t => ∫ x, swigluDead t x ^ 2 ∂gaussMeasure) (2 * 3)
      (1/4 * ∫ x, x ^ 4 ∂gaussMeasure) := by
  have hwin : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ t ≤ 1 := by
    filter_upwards [eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with t ht0 ht1
    exact ⟨ht0, ht1.le⟩
  set B5 := ∫ x, |x| ^ 5 ∂gaussMeasure with hB5
  set B6 := ∫ x, |x| ^ 6 ∂gaussMeasure with hB6
  have hB50 : 0 ≤ B5 := integral_nonneg fun x => by positivity
  have hB60 : 0 ≤ B6 := integral_nonneg fun x => by positivity
  apply hasLeadingRate_of_expansion
    (R := fun t => (∫ x, swigluDead t x ^ 2 ∂gaussMeasure)
      - 1/4 * (∫ x, x ^ 4 ∂gaussMeasure) * t ^ (2 * 3))
    (M := B5 + B6 / 4)
  · exact Filter.Eventually.of_forall fun t => by ring
  · filter_upwards [hwin] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    set ρ := fun x => swigluDead t x - 1/2 * t ^ 3 * x ^ 2 with hρdef
    have hρcont : Continuous ρ := by
      have hs : Continuous sigmoid := by
        unfold sigmoid
        exact continuous_const.div
          (continuous_const.add (Real.continuous_exp.comp continuous_neg))
          (fun y => by positivity)
      have hsw : Continuous (fun x => swigluDead t x) := by
        simp only [swigluDead_eq]
        exact (continuous_const.mul (continuous_pow 2)).mul
          (hs.comp (continuous_const.mul continuous_id))
      exact hsw.sub (continuous_const.mul (continuous_pow 2))
    have hρle : ∀ x, |ρ x| ≤ t ^ 4 * |x| ^ 3 / 2 :=
      fun x => swigluDead_sub_le ht0.le x
    have hIρx2 : Integrable (fun x => x ^ 2 * ρ x) gaussMeasure := by
      refine ((integrable_abs_pow_gaussMeasure 5).const_mul
        (t ^ 4 / 2)).mono'
        ((continuous_pow 2).mul hρcont).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      calc |x ^ 2| * |ρ x| ≤ |x ^ 2| * (t ^ 4 * |x| ^ 3 / 2) :=
            mul_le_mul_of_nonneg_left (hρle x) (abs_nonneg _)
        _ = t ^ 4 / 2 * |x| ^ 5 := by
            rw [abs_of_nonneg (sq_nonneg x),
              show x ^ 2 = |x| ^ 2 from (sq_abs x).symm]
            ring
    have hIρ2 : Integrable (fun x => ρ x ^ 2) gaussMeasure := by
      refine ((integrable_abs_pow_gaussMeasure 6).const_mul
        (t ^ 8 / 4)).mono'
        (hρcont.pow 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := hρle x
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      rw [sq_abs] at h2
      calc ρ x ^ 2 ≤ (t ^ 4 * |x| ^ 3 / 2) ^ 2 := h2
        _ = t ^ 8 / 4 * |x| ^ 6 := by ring
    have hIx4 : Integrable (fun x : ℝ => x ^ 4) gaussMeasure :=
      integrable_pow_gaussMeasure 4
    have hsq : ∀ x, swigluDead t x ^ 2
        = 1/4 * t ^ 6 * x ^ 4 + (t ^ 3 * (x ^ 2 * ρ x) + ρ x ^ 2) := by
      intro x
      have : swigluDead t x = 1/2 * t ^ 3 * x ^ 2 + ρ x := by
        rw [hρdef]
        ring
      rw [this]
      ring
    have hIg2 : Integrable (fun x => swigluDead t x ^ 2) gaussMeasure := by
      have hg : Integrable (fun x =>
          1/4 * t ^ 6 * x ^ 4 + (t ^ 3 * (x ^ 2 * ρ x) + ρ x ^ 2))
          gaussMeasure := by
        have h1 := (hIx4.const_mul (1/4 * t ^ 6))
        have h2 := (hIρx2.const_mul (t ^ 3)).add hIρ2
        exact (h1.congr (Filter.Eventually.of_forall fun x => by
          ring)).add (h2.congr (Filter.Eventually.of_forall fun x => by
          simp only [Pi.add_apply]))
      exact hg.congr (Filter.Eventually.of_forall fun x => (hsq x).symm)
    have hsub : (∫ x, swigluDead t x ^ 2 ∂gaussMeasure)
        - 1/4 * (∫ x, x ^ 4 ∂gaussMeasure) * t ^ (2 * 3)
        = ∫ x, (t ^ 3 * (x ^ 2 * ρ x) + ρ x ^ 2) ∂gaussMeasure := by
      have h1 : (∫ x, swigluDead t x ^ 2 ∂gaussMeasure)
          = ∫ x, (1/4 * t ^ 6 * x ^ 4
            + (t ^ 3 * (x ^ 2 * ρ x) + ρ x ^ 2)) ∂gaussMeasure := by
        congr 1
        funext x
        exact hsq x
      have hIsum : Integrable
          (fun x => t ^ 3 * (x ^ 2 * ρ x) + ρ x ^ 2) gaussMeasure := by
        have h2 := (hIρx2.const_mul (t ^ 3)).add hIρ2
        exact h2.congr (Filter.Eventually.of_forall fun x => by
          simp only [Pi.add_apply])
      have hIc : Integrable (fun x : ℝ => 1/4 * t ^ 6 * x ^ 4)
          gaussMeasure :=
        (hIx4.const_mul (1/4 * t ^ 6)).congr
          (Filter.Eventually.of_forall fun x => by ring)
      have hval : ∫ x, 1/4 * t ^ 6 * x ^ 4 ∂gaussMeasure
          = 1/4 * t ^ 6 * ∫ x, x ^ 4 ∂gaussMeasure := by
        rw [show (fun x : ℝ => 1/4 * t ^ 6 * x ^ 4)
            = fun x => (1/4 * t ^ 6) * x ^ 4 from by funext x; ring,
          integral_const_mul]
      rw [h1, integral_add hIc hIsum, hval]
      ring
    rw [hsub]
    have hdom : ∀ x, |t ^ 3 * (x ^ 2 * ρ x) + ρ x ^ 2|
        ≤ t ^ 7 / 2 * |x| ^ 5 + t ^ 8 / 4 * |x| ^ 6 := by
      intro x
      have h1 := abs_add_le (t ^ 3 * (x ^ 2 * ρ x)) (ρ x ^ 2)
      have h2 : |t ^ 3 * (x ^ 2 * ρ x)| ≤ t ^ 7 / 2 * |x| ^ 5 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht0.le 3),
          abs_of_nonneg (sq_nonneg x),
          show x ^ 2 = |x| ^ 2 from (sq_abs x).symm]
        calc t ^ 3 * (|x| ^ 2 * |ρ x|)
            ≤ t ^ 3 * (|x| ^ 2 * (t ^ 4 * |x| ^ 3 / 2)) := by
              have := mul_le_mul_of_nonneg_left (hρle x)
                (pow_nonneg (abs_nonneg x) 2)
              exact mul_le_mul_of_nonneg_left this
                (pow_nonneg ht0.le 3)
          _ = t ^ 7 / 2 * |x| ^ 5 := by ring
      have h3 : |ρ x ^ 2| ≤ t ^ 8 / 4 * |x| ^ 6 := by
        rw [abs_of_nonneg (sq_nonneg _)]
        have h := pow_le_pow_left₀ (abs_nonneg _) (hρle x) 2
        rw [sq_abs] at h
        calc ρ x ^ 2 ≤ (t ^ 4 * |x| ^ 3 / 2) ^ 2 := h
          _ = t ^ 8 / 4 * |x| ^ 6 := by ring
      linarith
    have hIdom : Integrable (fun x =>
        t ^ 7 / 2 * |x| ^ 5 + t ^ 8 / 4 * |x| ^ 6) gaussMeasure := by
      have h := ((integrable_abs_pow_gaussMeasure 5).const_mul
        (t ^ 7 / 2)).add ((integrable_abs_pow_gaussMeasure 6).const_mul
        (t ^ 8 / 4))
      exact h.congr (Filter.Eventually.of_forall fun x => by
        simp only [Pi.add_apply])
    calc |∫ x, (t ^ 3 * (x ^ 2 * ρ x) + ρ x ^ 2) ∂gaussMeasure|
        ≤ ∫ x, ‖t ^ 3 * (x ^ 2 * ρ x) + ρ x ^ 2‖ ∂gaussMeasure := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_integral_norm _
      _ ≤ ∫ x, (t ^ 7 / 2 * |x| ^ 5 + t ^ 8 / 4 * |x| ^ 6)
            ∂gaussMeasure := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun x => norm_nonneg _) hIdom
            (Filter.Eventually.of_forall fun x => ?_)
          simp only [Real.norm_eq_abs]
          exact hdom x
      _ = t ^ 7 / 2 * B5 + t ^ 8 / 4 * B6 := by
          rw [integral_add
            ((integrable_abs_pow_gaussMeasure 5).const_mul (t ^ 7 / 2))
            ((integrable_abs_pow_gaussMeasure 6).const_mul (t ^ 8 / 4)),
            integral_const_mul, integral_const_mul, ← hB5, ← hB6]
      _ ≤ (B5 + B6 / 4) * t ^ (2 * 3 + 1) := by
          have h7 : t ^ 8 ≤ t ^ 7 :=
            pow_le_pow_of_le_one ht0.le ht1 (by omega)
          have h5 : t ^ 7 / 2 * B5 ≤ t ^ 7 * B5 := by
            nlinarith [pow_pos ht0 7]
          have h6 : t ^ 8 / 4 * B6 ≤ t ^ 7 * (B6 / 4) := by
            nlinarith [mul_le_mul_of_nonneg_right h7 hB60]
          calc t ^ 7 / 2 * B5 + t ^ 8 / 4 * B6
              ≤ t ^ 7 * B5 + t ^ 7 * (B6 / 4) := by linarith
            _ = (B5 + B6 / 4) * t ^ (2 * 3 + 1) := by ring

/-! ### The composition recursion

The idealised SwiGLU block is B(x) = c·t³·x², quadratic in the dead
coordinate. Composition therefore does not add rates: the n-fold
composite carries t-power 3·(2ⁿ − 1), against the 3n that the additive
rule of thm:bridge_composition would give, because feeding a Θ(t^e)
input returns Θ(t^{3+2e}). -/

/-- rem:swiglu_composition, model algebra: the n-fold composite of the
    quadratic block B(x) = c·t³·x² is c^{2ⁿ−1}·t^{3(2ⁿ−1)}·x^{2ⁿ}. -/
theorem quadBlock_iterate (c t x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (fun z => c * t ^ 3 * z ^ 2)^[n] x
      = c ^ (2 ^ n - 1) * t ^ (3 * (2 ^ n - 1)) * x ^ (2 ^ n) := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp [pow_one]
    · rw [Function.iterate_succ_apply', ih hm]
      have h1 : (1:ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
      set P := 2 ^ m with hP
      have hsucc : 2 ^ (m + 1) = 2 * P := by
        rw [hP, pow_succ]
        ring
      rw [hsucc, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul,
        show c * t ^ 3 * (c ^ ((P - 1) * 2) * t ^ (3 * (P - 1) * 2)
            * x ^ (P * 2))
          = (c * c ^ ((P - 1) * 2)) * (t ^ 3 * t ^ (3 * (P - 1) * 2))
            * x ^ (P * 2) from by ring,
        ← pow_succ', ← pow_add]
      have e1 : (P - 1) * 2 + 1 = 2 * P - 1 := by omega
      have e2 : 3 + 3 * (P - 1) * 2 = 3 * (2 * P - 1) := by omega
      have e3 : P * 2 = 2 * P := by omega
      rw [e1, e2, e3]

end DeadDirections
