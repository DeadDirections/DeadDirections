/-
  The deep smooth channel (theory paper, thm:bridge class (P2), dead
  channel, L layers).

  Each layer multiplies by the weight t and applies a smooth
  activation φ with φ(0) = 0 and φ'(0) = c, packaged as the global
  Taylor hypothesis |φ(u) − c·u| ≤ K·u². The obstacle to depth is the
  compounding of the quadratic remainders through composition; a
  polynomial envelope controls it. By induction on depth, for
  t ∈ (0, 1]:

    |chain_ℓ(x)|                ≤ t^ℓ·C_ℓ·(1 + x²)^(2^ℓ)
    |chain_ℓ(x) − c^ℓ·t^ℓ·x|    ≤ t^(ℓ+1)·D_ℓ·(1 + x²)^(2^ℓ)

  with C, D the recursively defined envelope constants. Every power
  of 1 + x² is integrable against N(0,1), so the abstract
  score-expansion layer of FisherDecay applies with a(x) ∝ c^L·x and
  reads the channel second moment: leading rate 2L, coefficient
  c^{2L}. The single-layer case is smooth_channel_hasLeadingRate in
  ReluChannel; this module is its closure under depth.
-/
import DeadDirections.MixtureScore

namespace DeadDirections

open MeasureTheory Filter Topology

section SmoothChain

variable {φ : ℝ → ℝ} {c K : ℝ}

/-- The dead channel through L smooth layers at weight t. -/
def smoothChain (φ : ℝ → ℝ) (t : ℝ) (L : ℕ) (x : ℝ) : ℝ :=
  (fun z => φ (t * z))^[L] x

lemma smoothChain_zero (φ : ℝ → ℝ) (t x : ℝ) :
    smoothChain φ t 0 x = x := rfl

lemma smoothChain_succ (φ : ℝ → ℝ) (t : ℝ) (L : ℕ) (x : ℝ) :
    smoothChain φ t (L + 1) x = φ (t * smoothChain φ t L x) := by
  unfold smoothChain
  rw [Function.iterate_succ_apply']

lemma continuous_smoothChain (hcont : Continuous φ) (t : ℝ) (L : ℕ) :
    Continuous (fun x => smoothChain φ t L x) := by
  induction L with
  | zero => simpa [smoothChain_zero] using continuous_id
  | succ n ih =>
    simp only [smoothChain_succ]
    exact hcont.comp (continuous_const.mul ih)

/-- The envelope constant at depth ℓ. -/
noncomputable def envC (c K : ℝ) : ℕ → ℝ
  | 0 => 1
  | ℓ + 1 => |c| * envC c K ℓ + K * envC c K ℓ ^ 2

/-- The remainder constant at depth ℓ. -/
noncomputable def remC (c K : ℝ) : ℕ → ℝ
  | 0 => 0
  | ℓ + 1 => |c| * remC c K ℓ + K * envC c K ℓ ^ 2

lemma envC_zero (c K : ℝ) : envC c K 0 = 1 := rfl

lemma envC_succ (c K : ℝ) (ℓ : ℕ) :
    envC c K (ℓ + 1) = |c| * envC c K ℓ + K * envC c K ℓ ^ 2 := rfl

lemma remC_zero (c K : ℝ) : remC c K 0 = 0 := rfl

lemma remC_succ (c K : ℝ) (ℓ : ℕ) :
    remC c K (ℓ + 1) = |c| * remC c K ℓ + K * envC c K ℓ ^ 2 := rfl

lemma envC_nonneg (hK : 0 ≤ K) (ℓ : ℕ) : 0 ≤ envC c K ℓ := by
  induction ℓ with
  | zero => exact zero_le_one
  | succ n ih =>
    rw [envC_succ]
    exact add_nonneg (mul_nonneg (abs_nonneg c) ih)
      (mul_nonneg hK (sq_nonneg _))

lemma remC_nonneg (hK : 0 ≤ K) (ℓ : ℕ) : 0 ≤ remC c K ℓ := by
  induction ℓ with
  | zero => exact le_refl 0
  | succ n ih =>
    rw [remC_succ]
    exact add_nonneg (mul_nonneg (abs_nonneg c) ih)
      (mul_nonneg hK (sq_nonneg _))

lemma one_le_one_add_sq (x : ℝ) : (1:ℝ) ≤ 1 + x ^ 2 :=
  le_add_of_nonneg_right (sq_nonneg x)

lemma one_add_sq_pow_nonneg (x : ℝ) (d : ℕ) : (0:ℝ) ≤ (1 + x ^ 2) ^ d :=
  pow_nonneg (by positivity) d

/-- Squaring the depth-ℓ envelope polynomial gives the depth-(ℓ+1)
    envelope polynomial. -/
lemma one_add_sq_pow_sq (x : ℝ) (ℓ : ℕ) :
    ((1 + x ^ 2) ^ 2 ^ ℓ) ^ 2 = (1 + x ^ 2) ^ 2 ^ (ℓ + 1) := by
  rw [← pow_mul]
  congr 1

lemma one_add_sq_pow_le_succ (x : ℝ) (ℓ : ℕ) :
    (1 + x ^ 2) ^ 2 ^ ℓ ≤ (1 + x ^ 2) ^ 2 ^ (ℓ + 1) :=
  pow_le_pow_right₀ (one_le_one_add_sq x)
    (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- The envelope: the depth-ℓ channel value is bounded by
    t^ℓ·C_ℓ·(1 + x²)^(2^ℓ) for t ∈ (0, 1]. -/
lemma smoothChain_abs_le (hK : 0 ≤ K)
    (hφ : ∀ u, |φ u - c * u| ≤ K * u ^ 2)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (L : ℕ) (x : ℝ) :
    |smoothChain φ t L x| ≤ t ^ L * envC c K L * (1 + x ^ 2) ^ 2 ^ L := by
  have hφabs : ∀ u, |φ u| ≤ |c| * |u| + K * u ^ 2 := by
    intro u
    have h := hφ u
    have h1 := abs_add_le (φ u - c * u) (c * u)
    rw [show φ u - c * u + c * u = φ u from by ring, abs_mul] at h1
    linarith
  induction L with
  | zero =>
    simp only [smoothChain_zero, pow_zero, pow_one, one_mul]
    show |x| ≤ envC c K 0 * (1 + x ^ 2)
    rw [envC_zero]
    nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x]
  | succ n ih =>
    rw [smoothChain_succ]
    set u := t * smoothChain φ t n x with hu
    have hun : |u| ≤ t ^ (n + 1) * envC c K n * (1 + x ^ 2) ^ 2 ^ n := by
      rw [hu, abs_mul, abs_of_pos ht0, pow_succ]
      calc t * |smoothChain φ t n x|
          ≤ t * (t ^ n * envC c K n * (1 + x ^ 2) ^ 2 ^ n) :=
            mul_le_mul_of_nonneg_left ih ht0.le
        _ = t ^ n * t * envC c K n * (1 + x ^ 2) ^ 2 ^ n := by ring
    have hu2 : u ^ 2
        ≤ t ^ (2 * (n + 1)) * envC c K n ^ 2 * (1 + x ^ 2) ^ 2 ^ (n + 1) := by
      have h := pow_le_pow_left₀ (abs_nonneg u) hun 2
      rw [sq_abs] at h
      calc u ^ 2
          ≤ (t ^ (n + 1) * envC c K n * (1 + x ^ 2) ^ 2 ^ n) ^ 2 := h
        _ = t ^ (2 * (n + 1)) * envC c K n ^ 2
            * ((1 + x ^ 2) ^ 2 ^ n) ^ 2 := by
            rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm (n + 1) 2]
        _ = t ^ (2 * (n + 1)) * envC c K n ^ 2
            * (1 + x ^ 2) ^ 2 ^ (n + 1) := by rw [one_add_sq_pow_sq]
    have ht2 : t ^ (2 * (n + 1)) ≤ t ^ (n + 1) :=
      pow_le_pow_of_le_one ht0.le ht1 (by omega)
    calc |φ u| ≤ |c| * |u| + K * u ^ 2 := hφabs u
      _ ≤ |c| * (t ^ (n + 1) * envC c K n * (1 + x ^ 2) ^ 2 ^ n)
          + K * (t ^ (2 * (n + 1)) * envC c K n ^ 2
            * (1 + x ^ 2) ^ 2 ^ (n + 1)) := by
          have h1 := mul_le_mul_of_nonneg_left hun (abs_nonneg c)
          have h2 := mul_le_mul_of_nonneg_left hu2 hK
          linarith
      _ ≤ |c| * (t ^ (n + 1) * envC c K n * (1 + x ^ 2) ^ 2 ^ (n + 1))
          + K * (t ^ (n + 1) * envC c K n ^ 2
            * (1 + x ^ 2) ^ 2 ^ (n + 1)) := by
          have h1 : t ^ (n + 1) * envC c K n * (1 + x ^ 2) ^ 2 ^ n
              ≤ t ^ (n + 1) * envC c K n * (1 + x ^ 2) ^ 2 ^ (n + 1) :=
            mul_le_mul_of_nonneg_left (one_add_sq_pow_le_succ x n)
              (mul_nonneg (pow_pos ht0 _).le (envC_nonneg (c := c) hK n))
          have h2 : t ^ (2 * (n + 1)) * envC c K n ^ 2
                * (1 + x ^ 2) ^ 2 ^ (n + 1)
              ≤ t ^ (n + 1) * envC c K n ^ 2 * (1 + x ^ 2) ^ 2 ^ (n + 1) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right ht2 (sq_nonneg _))
              (one_add_sq_pow_nonneg x _)
          have h3 := mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
          have h4 := mul_le_mul_of_nonneg_left h2 hK
          linarith
      _ = t ^ (n + 1) * envC c K (n + 1) * (1 + x ^ 2) ^ 2 ^ (n + 1) := by
          rw [envC_succ]
          ring

/-- The remainder: the depth-ℓ channel differs from its linearisation
    c^ℓ·t^ℓ·x by at most t^(ℓ+1)·D_ℓ·(1 + x²)^(2^ℓ) for t ∈ (0, 1]. -/
lemma smoothChain_sub_le (hK : 0 ≤ K)
    (hφ : ∀ u, |φ u - c * u| ≤ K * u ^ 2)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (L : ℕ) (x : ℝ) :
    |smoothChain φ t L x - c ^ L * t ^ L * x|
      ≤ t ^ (L + 1) * remC c K L * (1 + x ^ 2) ^ 2 ^ L := by
  induction L with
  | zero =>
    simp only [smoothChain_zero, pow_zero, one_mul, sub_self, abs_zero]
    rw [remC_zero]
    simp
  | succ n ih =>
    rw [smoothChain_succ]
    set u := t * smoothChain φ t n x with hu
    have hsplit : φ u - c ^ (n + 1) * t ^ (n + 1) * x
        = (φ u - c * u)
          + c * t * (smoothChain φ t n x - c ^ n * t ^ n * x) := by
      rw [hu]
      ring
    have hu2 : u ^ 2
        ≤ t ^ (2 * (n + 1)) * envC c K n ^ 2 * (1 + x ^ 2) ^ 2 ^ (n + 1) := by
      have hun : |u| ≤ t ^ (n + 1) * envC c K n * (1 + x ^ 2) ^ 2 ^ n := by
        rw [hu, abs_mul, abs_of_pos ht0, pow_succ]
        calc t * |smoothChain φ t n x|
            ≤ t * (t ^ n * envC c K n * (1 + x ^ 2) ^ 2 ^ n) :=
              mul_le_mul_of_nonneg_left
                (smoothChain_abs_le hK hφ ht0 ht1 n x) ht0.le
          _ = t ^ n * t * envC c K n * (1 + x ^ 2) ^ 2 ^ n := by ring
      have h := pow_le_pow_left₀ (abs_nonneg u) hun 2
      rw [sq_abs] at h
      calc u ^ 2
          ≤ (t ^ (n + 1) * envC c K n * (1 + x ^ 2) ^ 2 ^ n) ^ 2 := h
        _ = t ^ (2 * (n + 1)) * envC c K n ^ 2
            * ((1 + x ^ 2) ^ 2 ^ n) ^ 2 := by
            rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm (n + 1) 2]
        _ = t ^ (2 * (n + 1)) * envC c K n ^ 2
            * (1 + x ^ 2) ^ 2 ^ (n + 1) := by rw [one_add_sq_pow_sq]
    have ht2 : t ^ (2 * (n + 1)) ≤ t ^ (n + 2) :=
      pow_le_pow_of_le_one ht0.le ht1 (by omega)
    calc |φ u - c ^ (n + 1) * t ^ (n + 1) * x|
        ≤ |φ u - c * u|
          + |c| * t * |smoothChain φ t n x - c ^ n * t ^ n * x| := by
          have h := abs_add_le (φ u - c * u)
            (c * t * (smoothChain φ t n x - c ^ n * t ^ n * x))
          rw [← hsplit] at h
          rw [show |c * t * (smoothChain φ t n x - c ^ n * t ^ n * x)|
              = |c| * t * |smoothChain φ t n x - c ^ n * t ^ n * x| from by
            rw [abs_mul, abs_mul, abs_of_pos ht0]] at h
          exact h
      _ ≤ K * u ^ 2
          + |c| * t * (t ^ (n + 1) * remC c K n * (1 + x ^ 2) ^ 2 ^ n) := by
          have h1 := hφ u
          have h2 := mul_le_mul_of_nonneg_left ih
            (mul_nonneg (abs_nonneg c) ht0.le)
          linarith
      _ ≤ K * (t ^ (2 * (n + 1)) * envC c K n ^ 2
            * (1 + x ^ 2) ^ 2 ^ (n + 1))
          + |c| * (t ^ (n + 2) * remC c K n * (1 + x ^ 2) ^ 2 ^ (n + 1)) := by
          have h1 := mul_le_mul_of_nonneg_left hu2 hK
          have h2 : |c| * t * (t ^ (n + 1) * remC c K n
                * (1 + x ^ 2) ^ 2 ^ n)
              ≤ |c| * (t ^ (n + 2) * remC c K n
                * (1 + x ^ 2) ^ 2 ^ (n + 1)) := by
            have hle := one_add_sq_pow_le_succ x n
            have hnn : (0:ℝ) ≤ |c| * t ^ (n + 2) * remC c K n :=
              mul_nonneg (mul_nonneg (abs_nonneg c) (pow_pos ht0 _).le)
                (remC_nonneg hK n)
            calc |c| * t * (t ^ (n + 1) * remC c K n
                  * (1 + x ^ 2) ^ 2 ^ n)
                = |c| * t ^ (n + 2) * remC c K n
                  * (1 + x ^ 2) ^ 2 ^ n := by ring
              _ ≤ |c| * t ^ (n + 2) * remC c K n
                  * (1 + x ^ 2) ^ 2 ^ (n + 1) :=
                  mul_le_mul_of_nonneg_left hle hnn
              _ = |c| * (t ^ (n + 2) * remC c K n
                  * (1 + x ^ 2) ^ 2 ^ (n + 1)) := by ring
          linarith
      _ ≤ K * (t ^ (n + 2) * envC c K n ^ 2 * (1 + x ^ 2) ^ 2 ^ (n + 1))
          + |c| * (t ^ (n + 2) * remC c K n * (1 + x ^ 2) ^ 2 ^ (n + 1)) := by
          have h : t ^ (2 * (n + 1)) * envC c K n ^ 2
                * (1 + x ^ 2) ^ 2 ^ (n + 1)
              ≤ t ^ (n + 2) * envC c K n ^ 2 * (1 + x ^ 2) ^ 2 ^ (n + 1) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right ht2 (sq_nonneg _))
              (one_add_sq_pow_nonneg x _)
          have h2 := mul_le_mul_of_nonneg_left h hK
          linarith
      _ = t ^ (n + 1 + 1) * remC c K (n + 1) * (1 + x ^ 2) ^ 2 ^ (n + 1) := by
          rw [remC_succ]
          ring

/-- Every power of 1 + x² is integrable against the Gaussian weight:
    the binomial expansion reduces it to the moment workhorse. -/
lemma integrable_one_add_sq_pow_mul_gaussDensity (d : ℕ) :
    Integrable (fun x : ℝ => (1 + x ^ 2) ^ d * gaussDensity x 0 1) := by
  have hexp : (fun x : ℝ => (1 + x ^ 2) ^ d * gaussDensity x 0 1)
      = fun x => ∑ k ∈ Finset.range (d + 1),
          (d.choose k : ℝ) * (x ^ (2 * (d - k)) * gaussDensity x 0 1) := by
    funext x
    rw [add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_pow, one_mul, ← pow_mul]
    ring
  rw [hexp]
  refine integrable_finset_sum _ fun k _ => ?_
  exact ((integrable_pow_mul_exp_mul_gaussDensity (2 * (d - k)) 0).congr
    (Filter.Eventually.of_forall fun x => by simp)).const_mul _

lemma integrable_one_add_sq_pow_gaussMeasure (d : ℕ) :
    Integrable (fun x : ℝ => (1 + x ^ 2) ^ d) gaussMeasure := by
  rw [integrable_gaussMeasure_iff]
  exact integrable_one_add_sq_pow_mul_gaussDensity d

/-- thm:bridge class (P2), deep chain: under |φ(u) − c·u| ≤ K·u², the
    L-layer dead-channel second moment carries leading rate 2L with
    coefficient c^{2L}. The compounded activation remainders enter at
    order t^{2L+2} and never touch the leading term. -/
theorem smooth_chain_hasLeadingRate (hK : 0 ≤ K) (hcont : Continuous φ)
    (hφ : ∀ u, |φ u - c * u| ≤ K * u ^ 2) (L : ℕ) :
    HasLeadingRate
      (fun t => ∫ x, smoothChain φ t L x ^ 2 ∂gaussMeasure) (2 * L)
      (c ^ (2 * L)) := by
  set B := ∫ x, (1 + x ^ 2) ^ 2 ^ (L + 1) ∂gaussMeasure with hB
  have hB0 : 0 ≤ B :=
    integral_nonneg fun x => one_add_sq_pow_nonneg x _
  have hL1 : ((L:ℝ) + 1) ≠ 0 := by positivity
  have hq : (c ^ L / ((L:ℝ) + 1)) * ((L:ℝ) + 1) = c ^ L := by
    field_simp
  -- the eventual (0,1] window
  have hwin : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ t ≤ 1 := by
    filter_upwards [eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with t ht0 ht1
    exact ⟨ht0, ht1.le⟩
  -- pointwise remainder bound squared, on the window
  have hptw : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x : ℝ,
      (smoothChain φ t L x - c ^ L * t ^ L * x) ^ 2
        ≤ t ^ (2 * (L + 1)) * remC c K L ^ 2
          * (1 + x ^ 2) ^ 2 ^ (L + 1) := by
    intro t ht0 ht1 x
    have h := smoothChain_sub_le hK hφ ht0 ht1 L x
    have hnn : (0:ℝ) ≤ t ^ (L + 1) * remC c K L * (1 + x ^ 2) ^ 2 ^ L :=
      mul_nonneg (mul_nonneg (pow_pos ht0 _).le (remC_nonneg hK L))
        (one_add_sq_pow_nonneg x _)
    have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at hsq
    calc (smoothChain φ t L x - c ^ L * t ^ L * x) ^ 2
        ≤ (t ^ (L + 1) * remC c K L * (1 + x ^ 2) ^ 2 ^ L) ^ 2 := hsq
      _ = t ^ (2 * (L + 1)) * remC c K L ^ 2
          * ((1 + x ^ 2) ^ 2 ^ L) ^ 2 := by
          rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm (L + 1) 2]
      _ = t ^ (2 * (L + 1)) * remC c K L ^ 2
          * (1 + x ^ 2) ^ 2 ^ (L + 1) := by rw [one_add_sq_pow_sq]
  -- continuity of the remainder in x
  have hrcont : ∀ t : ℝ, Continuous
      (fun x => smoothChain φ t L x - c ^ L * t ^ L * x) :=
    fun t => (continuous_smoothChain hcont t L).sub
      (continuous_const.mul continuous_id)
  -- the abstract score-expansion layer
  have h := fisher_expansion_of_score_expansion (μ := gaussMeasure)
    (s := fun t x => smoothChain φ t L x)
    (a := fun x => (c ^ L / ((L:ℝ) + 1)) * x)
    (r := fun t x => smoothChain φ t L x - c ^ L * t ^ L * x)
    (k := L + 1) (M := remC c K L ^ 2 * B)
    (by omega)
    (mul_nonneg (sq_nonneg _) hB0)
    (Filter.Eventually.of_forall fun t => fun x => by
      push_cast
      have hone : ((L:ℝ) + 1) * t ^ L * (c ^ L / ((L:ℝ) + 1) * x)
          = c ^ L * t ^ L * x := by
        linear_combination t ^ L * x * hq
      rw [hone]
      ring)
    (by
      have hI := (integrable_sq_gaussMeasure).const_mul
        ((c ^ L / ((L:ℝ) + 1)) ^ 2)
      exact hI.congr (Filter.Eventually.of_forall fun x => by ring))
    (by
      filter_upwards [hwin] with t ht
      obtain ⟨ht0, ht1⟩ := ht
      refine ((integrable_one_add_sq_pow_gaussMeasure
        (2 ^ (L + 1))).const_mul (remC c K L ^ 2)).mono'
        (((hrcont t).pow 2).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 := hptw t ht0 ht1 x
      have ht2 : t ^ (2 * (L + 1)) ≤ 1 :=
        pow_le_one₀ ht0.le ht1
      nlinarith [one_add_sq_pow_nonneg x (2 ^ (L + 1)),
        sq_nonneg (remC c K L),
        mul_le_mul_of_nonneg_right ht2
          (mul_nonneg (sq_nonneg (remC c K L))
            (one_add_sq_pow_nonneg x (2 ^ (L + 1))))])
    (by
      filter_upwards [hwin] with t ht
      obtain ⟨ht0, ht1⟩ := ht
      refine ((integrable_one_add_sq_pow_gaussMeasure
        (2 ^ (L + 1) + 1)).const_mul
        (|c ^ L / ((L:ℝ) + 1)| * remC c K L)).mono'
        ((continuous_const.mul continuous_id).mul (hrcont t)
          |>.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := smoothChain_sub_le hK hφ ht0 ht1 L x
      have htL : t ^ (L + 1) ≤ 1 := pow_le_one₀ ht0.le ht1
      have h2 : |smoothChain φ t L x - c ^ L * t ^ L * x|
          ≤ remC c K L * (1 + x ^ 2) ^ 2 ^ L := by
        have hnn : (0:ℝ) ≤ remC c K L * (1 + x ^ 2) ^ 2 ^ L :=
          mul_nonneg (remC_nonneg hK L) (one_add_sq_pow_nonneg x _)
        calc |smoothChain φ t L x - c ^ L * t ^ L * x|
            ≤ t ^ (L + 1) * remC c K L * (1 + x ^ 2) ^ 2 ^ L := h1
          _ = t ^ (L + 1) * (remC c K L * (1 + x ^ 2) ^ 2 ^ L) := by ring
          _ ≤ 1 * (remC c K L * (1 + x ^ 2) ^ 2 ^ L) :=
              mul_le_mul_of_nonneg_right htL hnn
          _ = remC c K L * (1 + x ^ 2) ^ 2 ^ L := by ring
      have hax : |(c ^ L / ((L:ℝ) + 1)) * x|
          = |c ^ L / ((L:ℝ) + 1)| * |x| := abs_mul _ _
      have hxb : |x| ≤ 1 + x ^ 2 := by
        nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x]
      have hPle : (1 + x ^ 2) ^ 2 ^ L ≤ (1 + x ^ 2) ^ 2 ^ (L + 1) :=
        one_add_sq_pow_le_succ x L
      have hstep : |x| * (1 + x ^ 2) ^ 2 ^ L
          ≤ (1 + x ^ 2) ^ (2 ^ (L + 1) + 1) := by
        calc |x| * (1 + x ^ 2) ^ 2 ^ L
            ≤ (1 + x ^ 2) * (1 + x ^ 2) ^ 2 ^ (L + 1) :=
              mul_le_mul hxb hPle (one_add_sq_pow_nonneg x _)
                (by positivity)
          _ = (1 + x ^ 2) ^ (2 ^ (L + 1) + 1) := by
              rw [pow_succ]
              ring
      calc |(c ^ L / ((L:ℝ) + 1)) * x|
            * |smoothChain φ t L x - c ^ L * t ^ L * x|
          ≤ (|c ^ L / ((L:ℝ) + 1)| * |x|)
            * (remC c K L * (1 + x ^ 2) ^ 2 ^ L) := by
            rw [hax]
            exact mul_le_mul_of_nonneg_left h2
              (mul_nonneg (abs_nonneg _) (abs_nonneg x))
        _ = (|c ^ L / ((L:ℝ) + 1)| * remC c K L)
            * (|x| * (1 + x ^ 2) ^ 2 ^ L) := by ring
        _ ≤ (|c ^ L / ((L:ℝ) + 1)| * remC c K L)
            * (1 + x ^ 2) ^ (2 ^ (L + 1) + 1) :=
            mul_le_mul_of_nonneg_left hstep
              (mul_nonneg (abs_nonneg _) (remC_nonneg hK L)))
    (by
      filter_upwards [hwin] with t ht
      obtain ⟨ht0, ht1⟩ := ht
      have hInt : Integrable
          (fun x => (smoothChain φ t L x - c ^ L * t ^ L * x) ^ 2)
          gaussMeasure := by
        refine ((integrable_one_add_sq_pow_gaussMeasure
          (2 ^ (L + 1))).const_mul
          (t ^ (2 * (L + 1)) * remC c K L ^ 2)).mono'
          (((hrcont t).pow 2).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h1 := hptw t ht0 ht1 x
        linarith [h1]
      calc ∫ x, (smoothChain φ t L x - c ^ L * t ^ L * x) ^ 2 ∂gaussMeasure
          ≤ ∫ x, t ^ (2 * (L + 1)) * remC c K L ^ 2
            * (1 + x ^ 2) ^ 2 ^ (L + 1) ∂gaussMeasure := by
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun x => sq_nonneg _)
              (((integrable_one_add_sq_pow_gaussMeasure
                (2 ^ (L + 1))).const_mul
                  (t ^ (2 * (L + 1)) * remC c K L ^ 2)).congr
                (Filter.Eventually.of_forall fun x => by ring))
              (Filter.Eventually.of_forall fun x => hptw t ht0 ht1 x)
        _ = remC c K L ^ 2 * B * t ^ (2 * (L + 1)) := by
            rw [show (fun x : ℝ => t ^ (2 * (L + 1)) * remC c K L ^ 2
                * (1 + x ^ 2) ^ 2 ^ (L + 1))
              = fun x => (t ^ (2 * (L + 1)) * remC c K L ^ 2)
                * (1 + x ^ 2) ^ 2 ^ (L + 1) from by
                funext x; ring, integral_const_mul, ← hB]
            ring)
  -- massage the coefficient: (L+1)²·∫((c^L/(L+1))·x)² = c^{2L}
  have hcoef : ((L + 1 : ℕ) : ℝ) ^ 2
      * ∫ x, ((c ^ L / ((L:ℝ) + 1)) * x) ^ 2 ∂gaussMeasure
      = c ^ (2 * L) := by
    have hval : ∫ x, ((c ^ L / ((L:ℝ) + 1)) * x) ^ 2 ∂gaussMeasure
        = (c ^ L / ((L:ℝ) + 1)) ^ 2 := by
      rw [show (fun x : ℝ => ((c ^ L / ((L:ℝ) + 1)) * x) ^ 2)
          = fun x => (c ^ L / ((L:ℝ) + 1)) ^ 2 * x ^ 2 from by
          funext x; ring, integral_const_mul, integral_sq_gaussMeasure,
        mul_one]
    rw [hval]
    push_cast
    rw [show (2 * L) = L * 2 from by ring, pow_mul]
    field_simp
  rw [Nat.add_sub_cancel] at h
  rw [← hcoef]
  exact h

/-- The log-log reading of the deep smooth channel: for c ≠ 0 the
    slope recovers the depth. -/
theorem smooth_chain_slope (hK : 0 ≤ K) (hcont : Continuous φ)
    (hφ : ∀ u, |φ u - c * u| ≤ K * u ^ 2) (L : ℕ) (hc : c ≠ 0) :
    Tendsto
      (fun t => Real.log (∫ x, smoothChain φ t L x ^ 2 ∂gaussMeasure)
        / Real.log t)
      (𝓝[>] (0:ℝ)) (𝓝 (2 * L)) := by
  have hpos : (0:ℝ) < c ^ (2 * L) := by
    rw [Nat.mul_comm 2 L, pow_mul]
    positivity
  have h := (smooth_chain_hasLeadingRate hK hcont hφ L).log_slope hpos
  simpa using h

end SmoothChain

/-! ### The backward channel and A–G duality for (P2)

The backward side needs the derivative: the hypotheses gain a
derivative function φ' with |φ'(u) − c| ≤ K'·|u| and the certification
that φ' is the derivative of φ everywhere. The backprop gradient
through m layers is the product ∏_j t·φ'(t·chain_j), certified below
as the true derivative of the m-layer chain; a second envelope
induction bounds its distance from (c·t)^m, and the depth-ℓ backward
moment reads rate 2(L−ℓ) with coefficient c^{2(L−ℓ)}. The A·G product
then has rate 2L with coefficient c^{2L} at every depth, the (P2)
duality at leading order. -/

section SmoothBackward

variable {φ φ' : ℝ → ℝ} {c K K' : ℝ}

/-- Splitting the chain at depth ℓ: the downstream layers are the
    same chain started at the depth-ℓ activation. -/
lemma smoothChain_add (φ : ℝ → ℝ) (t : ℝ) (m ℓ : ℕ) (x : ℝ) :
    smoothChain φ t (m + ℓ) x = smoothChain φ t m (smoothChain φ t ℓ x) :=
  Function.iterate_add_apply _ m ℓ x

/-- The backprop gradient through m layers started at h: the product
    of the per-layer factors t·φ'(t·chain_j(h)). -/
noncomputable def backDeriv (φ φ' : ℝ → ℝ) (t : ℝ) (m : ℕ) (h : ℝ) : ℝ :=
  ∏ j ∈ Finset.range m, (t * φ' (t * smoothChain φ t j h))

lemma backDeriv_zero (φ φ' : ℝ → ℝ) (t h : ℝ) :
    backDeriv φ φ' t 0 h = 1 := by
  unfold backDeriv
  exact Finset.prod_range_zero _

lemma backDeriv_succ (φ φ' : ℝ → ℝ) (t : ℝ) (m : ℕ) (h : ℝ) :
    backDeriv φ φ' t (m + 1) h
      = backDeriv φ φ' t m h * (t * φ' (t * smoothChain φ t m h)) := by
  unfold backDeriv
  exact Finset.prod_range_succ _ _

/-- The backprop product is the true derivative of the m-layer chain
    at every point. -/
lemma hasDerivAt_smoothChain (hd : ∀ u, HasDerivAt φ (φ' u) u)
    (t : ℝ) (m : ℕ) (h : ℝ) :
    HasDerivAt (fun y => smoothChain φ t m y) (backDeriv φ φ' t m h) h := by
  induction m with
  | zero =>
    rw [backDeriv_zero]
    simp only [smoothChain_zero]
    exact hasDerivAt_id' h
  | succ n ih =>
    have hfun : (fun y => smoothChain φ t (n + 1) y)
        = fun y => φ (t * smoothChain φ t n y) := by
      funext y
      rw [smoothChain_succ]
    rw [hfun, backDeriv_succ]
    have hinner : HasDerivAt (fun y => t * smoothChain φ t n y)
        (t * backDeriv φ φ' t n h) h := ih.const_mul t
    have hcomp := (hd (t * smoothChain φ t n h)).comp h hinner
    have hval : backDeriv φ φ' t n h * (t * φ' (t * smoothChain φ t n h))
        = φ' (t * smoothChain φ t n h) * (t * backDeriv φ φ' t n h) := by
      ring
    rw [hval]
    exact hcomp

/-- The backward envelope constant at depth m. -/
noncomputable def backC (c K K' : ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => |c| * backC c K K' m
      + K' * envC c K m * (|c| ^ m + backC c K K' m)

lemma backC_zero (c K K' : ℝ) : backC c K K' 0 = 0 := rfl

lemma backC_succ (c K K' : ℝ) (m : ℕ) :
    backC c K K' (m + 1) = |c| * backC c K K' m
      + K' * envC c K m * (|c| ^ m + backC c K K' m) := rfl

lemma backC_nonneg (hK : 0 ≤ K) (hK' : 0 ≤ K') (m : ℕ) :
    0 ≤ backC c K K' m := by
  induction m with
  | zero => exact le_refl 0
  | succ n ih =>
    rw [backC_succ]
    have h1 : (0:ℝ) ≤ |c| ^ n + backC c K K' n :=
      add_nonneg (pow_nonneg (abs_nonneg c) n) ih
    exact add_nonneg (mul_nonneg (abs_nonneg c) ih)
      (mul_nonneg (mul_nonneg hK' (envC_nonneg (c := c) hK n)) h1)

/-- The backward envelope: the backprop product differs from (c·t)^m
    by at most t^(m+1)·bC_m·(1 + h²)^(2^m) for t ∈ (0, 1]. -/
lemma backDeriv_sub_le (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hφ : ∀ u, |φ u - c * u| ≤ K * u ^ 2)
    (hφ' : ∀ u, |φ' u - c| ≤ K' * |u|)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (m : ℕ) (h : ℝ) :
    |backDeriv φ φ' t m h - (c * t) ^ m|
      ≤ t ^ (m + 1) * backC c K K' m * (1 + h ^ 2) ^ 2 ^ m := by
  induction m with
  | zero =>
    rw [backDeriv_zero, backC_zero, pow_zero, sub_self, abs_zero]
    simp
  | succ n ih =>
    have hP1 : (1:ℝ) ≤ (1 + h ^ 2) ^ 2 ^ n :=
      one_le_pow₀ (one_le_one_add_sq h)
    have hPn : (0:ℝ) ≤ (1 + h ^ 2) ^ 2 ^ n := by positivity
    have hPP : ((1 + h ^ 2) ^ 2 ^ n) ^ 2 = (1 + h ^ 2) ^ 2 ^ (n + 1) :=
      one_add_sq_pow_sq h n
    have hPle : (1 + h ^ 2) ^ 2 ^ n ≤ (1 + h ^ 2) ^ 2 ^ (n + 1) :=
      one_add_sq_pow_le_succ h n
    -- the split into the two error channels
    have hkey : backDeriv φ φ' t (n + 1) h - (c * t) ^ (n + 1)
        = t * (c * (backDeriv φ φ' t n h - (c * t) ^ n)
          + backDeriv φ φ' t n h
            * (φ' (t * smoothChain φ t n h) - c)) := by
      rw [backDeriv_succ]
      ring
    -- the derivative-side deviation along the trajectory
    have hchain : |t * smoothChain φ t n h|
        ≤ t ^ (n + 1) * envC c K n * (1 + h ^ 2) ^ 2 ^ n := by
      rw [abs_mul, abs_of_pos ht0, pow_succ]
      calc t * |smoothChain φ t n h|
          ≤ t * (t ^ n * envC c K n * (1 + h ^ 2) ^ 2 ^ n) :=
            mul_le_mul_of_nonneg_left
              (smoothChain_abs_le hK hφ ht0 ht1 n h) ht0.le
        _ = t ^ n * t * envC c K n * (1 + h ^ 2) ^ 2 ^ n := by ring
    have hδ : |φ' (t * smoothChain φ t n h) - c|
        ≤ t ^ (n + 1) * (K' * envC c K n * (1 + h ^ 2) ^ 2 ^ n) := by
      calc |φ' (t * smoothChain φ t n h) - c|
          ≤ K' * |t * smoothChain φ t n h| := hφ' _
        _ ≤ K' * (t ^ (n + 1) * envC c K n * (1 + h ^ 2) ^ 2 ^ n) :=
            mul_le_mul_of_nonneg_left hchain hK'
        _ = t ^ (n + 1) * (K' * envC c K n * (1 + h ^ 2) ^ 2 ^ n) := by
            ring
    -- the product magnitude
    have hD : |(c * t) ^ n| = |c| ^ n * t ^ n := by
      rw [abs_pow, abs_mul, abs_of_pos ht0, mul_pow]
    have hE : |backDeriv φ φ' t n h|
        ≤ t ^ n * ((|c| ^ n + backC c K K' n) * (1 + h ^ 2) ^ 2 ^ n) := by
      have h1 := abs_add_le ((c * t) ^ n)
        (backDeriv φ φ' t n h - (c * t) ^ n)
      rw [show (c * t) ^ n + (backDeriv φ φ' t n h - (c * t) ^ n)
          = backDeriv φ φ' t n h from by ring, hD] at h1
      have htn : t ^ (n + 1) ≤ t ^ n :=
        pow_le_pow_of_le_one ht0.le ht1 (by omega)
      have h2 : t ^ (n + 1) * backC c K K' n * (1 + h ^ 2) ^ 2 ^ n
          ≤ t ^ n * backC c K K' n * (1 + h ^ 2) ^ 2 ^ n := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right htn (backC_nonneg (c := c) hK hK' n)) hPn
        linarith
      have h3 : |c| ^ n * t ^ n
          ≤ |c| ^ n * t ^ n * (1 + h ^ 2) ^ 2 ^ n := by
        nlinarith [mul_nonneg (pow_nonneg (abs_nonneg c) n)
          (pow_pos ht0 n).le]
      calc |backDeriv φ φ' t n h|
          ≤ |c| ^ n * t ^ n
            + t ^ (n + 1) * backC c K K' n * (1 + h ^ 2) ^ 2 ^ n := by
            linarith [ih]
        _ ≤ |c| ^ n * t ^ n * (1 + h ^ 2) ^ 2 ^ n
            + t ^ n * backC c K K' n * (1 + h ^ 2) ^ 2 ^ n := by
            linarith
        _ = t ^ n * ((|c| ^ n + backC c K K' n) * (1 + h ^ 2) ^ 2 ^ n) := by
            ring
    -- channel A: the propagated error
    have hA : t * (|c| * |backDeriv φ φ' t n h - (c * t) ^ n|)
        ≤ t ^ (n + 1 + 1) * (|c| * backC c K K' n)
          * (1 + h ^ 2) ^ 2 ^ (n + 1) := by
      have h1 := mul_le_mul_of_nonneg_left ih (abs_nonneg c)
      have h2 : |c| * (t ^ (n + 1) * backC c K K' n * (1 + h ^ 2) ^ 2 ^ n)
          ≤ |c| * (t ^ (n + 1) * backC c K K' n
            * (1 + h ^ 2) ^ 2 ^ (n + 1)) := by
        have := mul_le_mul_of_nonneg_left hPle
          (mul_nonneg (mul_nonneg (pow_pos ht0 (n + 1)).le
            (backC_nonneg (c := c) hK hK' n)) (abs_nonneg c))
        nlinarith [mul_nonneg (pow_pos ht0 (n + 1)).le
          (backC_nonneg (c := c) hK hK' n), abs_nonneg c, hPle,
          mul_le_mul_of_nonneg_left hPle
            (mul_nonneg (mul_nonneg (abs_nonneg c)
              (pow_pos ht0 (n + 1)).le) (backC_nonneg (c := c) hK hK' n))]
      calc t * (|c| * |backDeriv φ φ' t n h - (c * t) ^ n|)
          ≤ t * (|c| * (t ^ (n + 1) * backC c K K' n
            * (1 + h ^ 2) ^ 2 ^ (n + 1))) := by
            have := le_trans h1 h2
            exact mul_le_mul_of_nonneg_left this ht0.le
        _ = t ^ (n + 1 + 1) * (|c| * backC c K K' n)
            * (1 + h ^ 2) ^ 2 ^ (n + 1) := by
            rw [pow_succ]
            ring
    -- channel B: the fresh deviation against the product magnitude
    have hB : t * (|backDeriv φ φ' t n h|
          * |φ' (t * smoothChain φ t n h) - c|)
        ≤ t ^ (n + 1 + 1) * (K' * envC c K n * (|c| ^ n + backC c K K' n))
          * (1 + h ^ 2) ^ 2 ^ (n + 1) := by
      have hEnn : (0:ℝ) ≤ t ^ n * ((|c| ^ n + backC c K K' n)
          * (1 + h ^ 2) ^ 2 ^ n) := by
        have := backC_nonneg (c := c) hK hK' n
        positivity
      have hprod := mul_le_mul hE hδ (abs_nonneg _) hEnn
      have hcollect : t ^ n * ((|c| ^ n + backC c K K' n)
            * (1 + h ^ 2) ^ 2 ^ n)
          * (t ^ (n + 1) * (K' * envC c K n * (1 + h ^ 2) ^ 2 ^ n))
          = t ^ (2 * n + 1)
            * (K' * envC c K n * (|c| ^ n + backC c K K' n))
            * (1 + h ^ 2) ^ 2 ^ (n + 1) := by
        rw [← hPP]
        ring
      have htdrop : t ^ (2 * n + 1 + 1) ≤ t ^ (n + 1 + 1) :=
        pow_le_pow_of_le_one ht0.le ht1 (by omega)
      calc t * (|backDeriv φ φ' t n h|
            * |φ' (t * smoothChain φ t n h) - c|)
          ≤ t * (t ^ (2 * n + 1)
            * (K' * envC c K n * (|c| ^ n + backC c K K' n))
            * (1 + h ^ 2) ^ 2 ^ (n + 1)) := by
            rw [← hcollect]
            exact mul_le_mul_of_nonneg_left hprod ht0.le
        _ = t ^ (2 * n + 1 + 1)
            * (K' * envC c K n * (|c| ^ n + backC c K K' n))
            * (1 + h ^ 2) ^ 2 ^ (n + 1) := by
            rw [pow_succ]
            ring
        _ ≤ t ^ (n + 1 + 1)
            * (K' * envC c K n * (|c| ^ n + backC c K K' n))
            * (1 + h ^ 2) ^ 2 ^ (n + 1) := by
            have hnn : (0:ℝ) ≤ (K' * envC c K n
                * (|c| ^ n + backC c K K' n))
                * (1 + h ^ 2) ^ 2 ^ (n + 1) := by
              have h1 := backC_nonneg (c := c) hK hK' n
              have h2 := envC_nonneg (c := c) hK n
              positivity
            have := mul_le_mul_of_nonneg_right htdrop hnn
            calc t ^ (2 * n + 1 + 1)
                * (K' * envC c K n * (|c| ^ n + backC c K K' n))
                * (1 + h ^ 2) ^ 2 ^ (n + 1)
                = t ^ (2 * n + 1 + 1)
                  * ((K' * envC c K n * (|c| ^ n + backC c K K' n))
                    * (1 + h ^ 2) ^ 2 ^ (n + 1)) := by ring
              _ ≤ t ^ (n + 1 + 1)
                  * ((K' * envC c K n * (|c| ^ n + backC c K K' n))
                    * (1 + h ^ 2) ^ 2 ^ (n + 1)) := this
              _ = t ^ (n + 1 + 1)
                  * (K' * envC c K n * (|c| ^ n + backC c K K' n))
                  * (1 + h ^ 2) ^ 2 ^ (n + 1) := by ring
    -- assemble
    calc |backDeriv φ φ' t (n + 1) h - (c * t) ^ (n + 1)|
        = |t * (c * (backDeriv φ φ' t n h - (c * t) ^ n)
          + backDeriv φ φ' t n h
            * (φ' (t * smoothChain φ t n h) - c))| := by rw [hkey]
      _ ≤ t * (|c| * |backDeriv φ φ' t n h - (c * t) ^ n|
          + |backDeriv φ φ' t n h|
            * |φ' (t * smoothChain φ t n h) - c|) := by
          rw [abs_mul, abs_of_pos ht0]
          have h1 := abs_add_le (c * (backDeriv φ φ' t n h - (c * t) ^ n))
            (backDeriv φ φ' t n h * (φ' (t * smoothChain φ t n h) - c))
          rw [abs_mul, abs_mul] at h1
          exact mul_le_mul_of_nonneg_left h1 ht0.le
      _ ≤ t ^ (n + 1 + 1) * (|c| * backC c K K' n)
            * (1 + h ^ 2) ^ 2 ^ (n + 1)
          + t ^ (n + 1 + 1)
            * (K' * envC c K n * (|c| ^ n + backC c K K' n))
            * (1 + h ^ 2) ^ 2 ^ (n + 1) := by
          have hsplit : t * (|c| * |backDeriv φ φ' t n h - (c * t) ^ n|
              + |backDeriv φ φ' t n h|
                * |φ' (t * smoothChain φ t n h) - c|)
              = t * (|c| * |backDeriv φ φ' t n h - (c * t) ^ n|)
                + t * (|backDeriv φ φ' t n h|
                  * |φ' (t * smoothChain φ t n h) - c|) := by ring
          rw [hsplit]
          linarith [hA, hB]
      _ = t ^ (n + 1 + 1) * backC c K K' (n + 1)
          * (1 + h ^ 2) ^ 2 ^ (n + 1) := by
          rw [backC_succ]
          ring

/-- thm:bridge class (P2), backward side: the second moment of the
    backprop gradient through m downstream layers, taken at the
    depth-ℓ activation, carries leading rate 2m with coefficient
    c^{2m}. With m = L − ℓ this is the per-layer G-factor ladder. -/
theorem smooth_chain_backward_hasLeadingRate (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hcont : Continuous φ) (hcont' : Continuous φ')
    (hφ : ∀ u, |φ u - c * u| ≤ K * u ^ 2)
    (hφ' : ∀ u, |φ' u - c| ≤ K' * |u|) (m ℓ : ℕ) :
    HasLeadingRate
      (fun t => ∫ x, backDeriv φ φ' t m (smoothChain φ t ℓ x) ^ 2
        ∂gaussMeasure) (2 * m) (c ^ (2 * m)) := by
  set W := backC c K K' m * (1 + envC c K ℓ ^ 2) ^ 2 ^ m with hW
  have hW0 : 0 ≤ W := by
    rw [hW]
    have h1 := backC_nonneg (c := c) hK hK' m
    positivity
  set D := 2 ^ (ℓ + 1) * 2 ^ m with hD
  set B₁ := ∫ x, (1 + x ^ 2) ^ D ∂gaussMeasure with hB₁
  set B₂ := ∫ x, (1 + x ^ 2) ^ (D * 2) ∂gaussMeasure with hB₂
  have hB₁0 : 0 ≤ B₁ := integral_nonneg fun x => one_add_sq_pow_nonneg x _
  have hB₂0 : 0 ≤ B₂ := integral_nonneg fun x => one_add_sq_pow_nonneg x _
  have hwin : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ t ≤ 1 := by
    filter_upwards [eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with t ht0 ht1
    exact ⟨ht0, ht1.le⟩
  -- pointwise deviation bound along the trajectory
  have hρ : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x : ℝ,
      |backDeriv φ φ' t m (smoothChain φ t ℓ x) - (c * t) ^ m|
        ≤ t ^ (m + 1) * W * (1 + x ^ 2) ^ D := by
    intro t ht0 ht1 x
    have h1 := backDeriv_sub_le hK hK' hφ hφ' ht0 ht1 m
      (smoothChain φ t ℓ x)
    have hcb : smoothChain φ t ℓ x ^ 2
        ≤ envC c K ℓ ^ 2 * (1 + x ^ 2) ^ 2 ^ (ℓ + 1) := by
      have h2 := smoothChain_abs_le hK hφ ht0 ht1 ℓ x
      have h3 : |smoothChain φ t ℓ x|
          ≤ envC c K ℓ * (1 + x ^ 2) ^ 2 ^ ℓ := by
        have htℓ : t ^ ℓ ≤ 1 := pow_le_one₀ ht0.le ht1
        have hnn : (0:ℝ) ≤ envC c K ℓ * (1 + x ^ 2) ^ 2 ^ ℓ :=
          mul_nonneg (envC_nonneg (c := c) hK ℓ) (one_add_sq_pow_nonneg x _)
        calc |smoothChain φ t ℓ x|
            ≤ t ^ ℓ * envC c K ℓ * (1 + x ^ 2) ^ 2 ^ ℓ := h2
          _ = t ^ ℓ * (envC c K ℓ * (1 + x ^ 2) ^ 2 ^ ℓ) := by ring
          _ ≤ 1 * (envC c K ℓ * (1 + x ^ 2) ^ 2 ^ ℓ) :=
              mul_le_mul_of_nonneg_right htℓ hnn
          _ = envC c K ℓ * (1 + x ^ 2) ^ 2 ^ ℓ := by ring
      have h4 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      rw [sq_abs] at h4
      calc smoothChain φ t ℓ x ^ 2
          ≤ (envC c K ℓ * (1 + x ^ 2) ^ 2 ^ ℓ) ^ 2 := h4
        _ = envC c K ℓ ^ 2 * ((1 + x ^ 2) ^ 2 ^ ℓ) ^ 2 := by ring
        _ = envC c K ℓ ^ 2 * (1 + x ^ 2) ^ 2 ^ (ℓ + 1) := by
            rw [one_add_sq_pow_sq]
    have hone : (1:ℝ) + smoothChain φ t ℓ x ^ 2
        ≤ (1 + envC c K ℓ ^ 2) * (1 + x ^ 2) ^ 2 ^ (ℓ + 1) := by
      have hQ1 : (1:ℝ) ≤ (1 + x ^ 2) ^ 2 ^ (ℓ + 1) :=
        one_le_pow₀ (one_le_one_add_sq x)
      nlinarith [hcb, sq_nonneg (envC c K ℓ)]
    have hpow : (1 + smoothChain φ t ℓ x ^ 2) ^ 2 ^ m
        ≤ (1 + envC c K ℓ ^ 2) ^ 2 ^ m * (1 + x ^ 2) ^ D := by
      have h5 := pow_le_pow_left₀ (by positivity) hone (2 ^ m)
      calc (1 + smoothChain φ t ℓ x ^ 2) ^ 2 ^ m
          ≤ ((1 + envC c K ℓ ^ 2) * (1 + x ^ 2) ^ 2 ^ (ℓ + 1)) ^ 2 ^ m :=
            h5
        _ = (1 + envC c K ℓ ^ 2) ^ 2 ^ m
            * ((1 + x ^ 2) ^ 2 ^ (ℓ + 1)) ^ 2 ^ m := mul_pow _ _ _
        _ = (1 + envC c K ℓ ^ 2) ^ 2 ^ m * (1 + x ^ 2) ^ D := by
            rw [← pow_mul]
    have hbCnn : (0:ℝ) ≤ t ^ (m + 1) * backC c K K' m :=
      mul_nonneg (pow_pos ht0 _).le (backC_nonneg (c := c) hK hK' m)
    calc |backDeriv φ φ' t m (smoothChain φ t ℓ x) - (c * t) ^ m|
        ≤ t ^ (m + 1) * backC c K K' m
          * (1 + smoothChain φ t ℓ x ^ 2) ^ 2 ^ m := h1
      _ ≤ t ^ (m + 1) * backC c K K' m
          * ((1 + envC c K ℓ ^ 2) ^ 2 ^ m * (1 + x ^ 2) ^ D) :=
          mul_le_mul_of_nonneg_left hpow hbCnn
      _ = t ^ (m + 1) * W * (1 + x ^ 2) ^ D := by
          rw [hW]
          ring
  -- continuity of the backward gradient in x
  have hgcont : ∀ t : ℝ, Continuous
      (fun x => backDeriv φ φ' t m (smoothChain φ t ℓ x)) := by
    intro t
    unfold backDeriv
    apply continuous_finset_prod
    intro j _
    exact continuous_const.mul (hcont'.comp (continuous_const.mul
      ((continuous_smoothChain hcont t j).comp
        (continuous_smoothChain hcont t ℓ))))
  -- the coefficient identity
  have ha : ∀ t : ℝ, c ^ (2 * m) * t ^ (2 * m) = ((c * t) ^ m) ^ 2 := by
    intro t
    rw [← mul_pow, ← pow_mul, Nat.mul_comm m 2]
  apply hasLeadingRate_of_expansion
    (R := fun t => (∫ x, backDeriv φ φ' t m (smoothChain φ t ℓ x) ^ 2
      ∂gaussMeasure) - c ^ (2 * m) * t ^ (2 * m))
    (M := 2 * |c| ^ m * W * B₁ + W ^ 2 * B₂)
  · exact Filter.Eventually.of_forall fun t => by ring
  · filter_upwards [hwin] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    set ρ := fun x => backDeriv φ φ' t m (smoothChain φ t ℓ x)
      - (c * t) ^ m with hρdef
    have hρcont : Continuous ρ := (hgcont t).sub continuous_const
    have hIρ : Integrable ρ gaussMeasure := by
      refine ((integrable_one_add_sq_pow_gaussMeasure D).const_mul
        (t ^ (m + 1) * W)).mono' hρcont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs]
      calc |ρ x| ≤ t ^ (m + 1) * W * (1 + x ^ 2) ^ D := hρ t ht0 ht1 x
        _ = t ^ (m + 1) * W * (1 + x ^ 2) ^ D := rfl
    have hIρ2 : Integrable (fun x => ρ x ^ 2) gaussMeasure := by
      refine ((integrable_one_add_sq_pow_gaussMeasure (D * 2)).const_mul
        ((t ^ (m + 1) * W) ^ 2)).mono'
        (hρcont.pow 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 := hρ t ht0 ht1 x
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs] at h2
      calc ρ x ^ 2 ≤ (t ^ (m + 1) * W * (1 + x ^ 2) ^ D) ^ 2 := h2
        _ = (t ^ (m + 1) * W) ^ 2 * ((1 + x ^ 2) ^ D) ^ 2 := by ring
        _ = (t ^ (m + 1) * W) ^ 2 * (1 + x ^ 2) ^ (D * 2) := by
            rw [← pow_mul]
    have hgsq : ∀ x : ℝ,
        backDeriv φ φ' t m (smoothChain φ t ℓ x) ^ 2
          = c ^ (2 * m) * t ^ (2 * m)
            + (2 * (c * t) ^ m * ρ x + ρ x ^ 2) := by
      intro x
      rw [ha t, hρdef]
      ring
    have hIg2 : Integrable
        (fun x => backDeriv φ φ' t m (smoothChain φ t ℓ x) ^ 2)
        gaussMeasure := by
      have hg : Integrable (fun x => c ^ (2 * m) * t ^ (2 * m)
          + (2 * (c * t) ^ m * ρ x + ρ x ^ 2)) gaussMeasure :=
        (integrable_const _).add ((hIρ.const_mul _).add hIρ2)
      exact hg.congr (Filter.Eventually.of_forall fun x =>
        (hgsq x).symm)
    have hsub : (∫ x, backDeriv φ φ' t m (smoothChain φ t ℓ x) ^ 2
          ∂gaussMeasure) - c ^ (2 * m) * t ^ (2 * m)
        = ∫ x, (2 * (c * t) ^ m * ρ x + ρ x ^ 2) ∂gaussMeasure := by
      have h1 : (∫ x, backDeriv φ φ' t m (smoothChain φ t ℓ x) ^ 2
            ∂gaussMeasure)
          = ∫ x, (c ^ (2 * m) * t ^ (2 * m)
            + (2 * (c * t) ^ m * ρ x + ρ x ^ 2)) ∂gaussMeasure := by
        congr 1
        funext x
        exact hgsq x
      have hI2 : Integrable (fun x => 2 * (c * t) ^ m * ρ x + ρ x ^ 2)
          gaussMeasure := by
        have h2 := (hIρ.const_mul (2 * (c * t) ^ m)).add hIρ2
        exact h2.congr (Filter.Eventually.of_forall fun x => by
          simp only [Pi.add_apply])
      rw [h1, integral_add (integrable_const _) hI2, integral_const]
      simp [measureReal_def]
    rw [hsub]
    have hdom : ∀ x : ℝ, |2 * (c * t) ^ m * ρ x + ρ x ^ 2|
        ≤ 2 * (|c| ^ m * t ^ m) * (t ^ (m + 1) * W * (1 + x ^ 2) ^ D)
          + (t ^ (m + 1) * W) ^ 2 * (1 + x ^ 2) ^ (D * 2) := by
      intro x
      have h1 := abs_add_le (2 * (c * t) ^ m * ρ x) (ρ x ^ 2)
      have h2 : |2 * (c * t) ^ m * ρ x|
          ≤ 2 * (|c| ^ m * t ^ m) * (t ^ (m + 1) * W * (1 + x ^ 2) ^ D) := by
        rw [abs_mul, abs_mul, abs_two, abs_pow, abs_mul, abs_of_pos ht0,
          mul_pow]
        have hnn : (0:ℝ) ≤ 2 * (|c| ^ m * t ^ m) := by positivity
        exact mul_le_mul_of_nonneg_left (hρ t ht0 ht1 x) hnn
      have h3 : |ρ x ^ 2|
          ≤ (t ^ (m + 1) * W) ^ 2 * (1 + x ^ 2) ^ (D * 2) := by
        rw [abs_of_nonneg (sq_nonneg _)]
        have h4 := hρ t ht0 ht1 x
        have h5 := pow_le_pow_left₀ (abs_nonneg _) h4 2
        rw [sq_abs] at h5
        calc ρ x ^ 2 ≤ (t ^ (m + 1) * W * (1 + x ^ 2) ^ D) ^ 2 := h5
          _ = (t ^ (m + 1) * W) ^ 2 * ((1 + x ^ 2) ^ D) ^ 2 := by ring
          _ = (t ^ (m + 1) * W) ^ 2 * (1 + x ^ 2) ^ (D * 2) := by
              rw [← pow_mul]
      calc |2 * (c * t) ^ m * ρ x + ρ x ^ 2|
          ≤ |2 * (c * t) ^ m * ρ x| + |ρ x ^ 2| := h1
        _ ≤ 2 * (|c| ^ m * t ^ m) * (t ^ (m + 1) * W * (1 + x ^ 2) ^ D)
            + (t ^ (m + 1) * W) ^ 2 * (1 + x ^ 2) ^ (D * 2) := by
            linarith
    have hIdom : Integrable (fun x =>
        2 * (|c| ^ m * t ^ m) * (t ^ (m + 1) * W * (1 + x ^ 2) ^ D)
          + (t ^ (m + 1) * W) ^ 2 * (1 + x ^ 2) ^ (D * 2))
        gaussMeasure := by
      have hg : Integrable (fun x =>
          (2 * (|c| ^ m * t ^ m) * (t ^ (m + 1) * W))
            * (1 + x ^ 2) ^ D
          + ((t ^ (m + 1) * W) ^ 2) * (1 + x ^ 2) ^ (D * 2))
          gaussMeasure :=
        ((integrable_one_add_sq_pow_gaussMeasure D).const_mul _).add
          ((integrable_one_add_sq_pow_gaussMeasure (D * 2)).const_mul _)
      exact hg.congr (Filter.Eventually.of_forall fun x => by ring)
    calc |∫ x, (2 * (c * t) ^ m * ρ x + ρ x ^ 2) ∂gaussMeasure|
        ≤ ∫ x, ‖2 * (c * t) ^ m * ρ x + ρ x ^ 2‖ ∂gaussMeasure := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_integral_norm _
      _ ≤ ∫ x, (2 * (|c| ^ m * t ^ m)
            * (t ^ (m + 1) * W * (1 + x ^ 2) ^ D)
          + (t ^ (m + 1) * W) ^ 2 * (1 + x ^ 2) ^ (D * 2))
            ∂gaussMeasure := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun x => norm_nonneg _) hIdom
            (Filter.Eventually.of_forall fun x => ?_)
          simp only [Real.norm_eq_abs]
          exact hdom x
      _ = 2 * |c| ^ m * W * B₁ * t ^ (2 * m + 1)
          + W ^ 2 * B₂ * t ^ (2 * m + 2) := by
          have hfun : (fun x : ℝ =>
              2 * (|c| ^ m * t ^ m)
                * (t ^ (m + 1) * W * (1 + x ^ 2) ^ D)
              + (t ^ (m + 1) * W) ^ 2 * (1 + x ^ 2) ^ (D * 2))
              = fun x => (2 * (|c| ^ m * t ^ m) * (t ^ (m + 1) * W))
                * (1 + x ^ 2) ^ D
              + ((t ^ (m + 1) * W) ^ 2) * (1 + x ^ 2) ^ (D * 2) := by
            funext x
            ring
          rw [hfun, integral_add
            ((integrable_one_add_sq_pow_gaussMeasure D).const_mul _)
            ((integrable_one_add_sq_pow_gaussMeasure (D * 2)).const_mul _),
            integral_const_mul, integral_const_mul, ← hB₁, ← hB₂]
          rw [show (2 * m + 1) = m + (m + 1) from by omega,
            show (2 * m + 2) = (m + 1) + (m + 1) from by omega,
            pow_add, pow_add]
          ring
      _ ≤ (2 * |c| ^ m * W * B₁ + W ^ 2 * B₂) * t ^ (2 * m + 1) := by
          have h1 : t ^ (2 * m + 2) ≤ t ^ (2 * m + 1) :=
            pow_le_pow_of_le_one ht0.le ht1 (by omega)
          have h2 : (0:ℝ) ≤ W ^ 2 * B₂ := by positivity
          nlinarith [mul_le_mul_of_nonneg_left h1 h2,
            pow_pos ht0 (2 * m + 1)]

/-- cor:a_g_duality, class (P2): the product of the depth-ℓ forward
    moment and the depth-ℓ backward moment has leading rate 2L with
    coefficient c^{2L}, for every ℓ ≤ L. The forward rate 2ℓ and the
    backward rate 2(L−ℓ) sum to 2L at every depth: the duality of the
    exact (P1)/(P3) products, at leading order. -/
theorem smooth_chain_ag_product (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hcont : Continuous φ) (hcont' : Continuous φ')
    (hφ : ∀ u, |φ u - c * u| ≤ K * u ^ 2)
    (hφ' : ∀ u, |φ' u - c| ≤ K' * |u|) (L ℓ : ℕ) (hℓ : ℓ ≤ L) :
    HasLeadingRate
      (fun t => (∫ x, smoothChain φ t ℓ x ^ 2 ∂gaussMeasure)
        * ∫ x, backDeriv φ φ' t (L - ℓ) (smoothChain φ t ℓ x) ^ 2
          ∂gaussMeasure)
      (2 * L) (c ^ (2 * L)) := by
  have h := (smooth_chain_hasLeadingRate hK hcont hφ ℓ).mul
    (smooth_chain_backward_hasLeadingRate hK hK' hcont hcont' hφ hφ'
      (L - ℓ) ℓ)
  have hp : 2 * ℓ + 2 * (L - ℓ) = 2 * L := by omega
  have hc : c ^ (2 * ℓ) * c ^ (2 * (L - ℓ)) = c ^ (2 * L) := by
    rw [← pow_add]
    congr 1
  rw [hp, hc] at h
  exact h

/-- The two-channel smooth layer map iterates componentwise. -/
lemma smoothPair_iterate {t s : ℝ} (L : ℕ) (p : ℝ × ℝ) :
    (fun q : ℝ × ℝ => (φ (t * q.1), φ (s * q.2)))^[L] p
      = (smoothChain φ t L p.1, smoothChain φ s L p.2) := by
  induction L with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, smoothChain_succ,
      smoothChain_succ]

/-- thm:bridge (b), class (P2): in the two-channel configuration the
    live-coordinate moment carries no t; when it is positive, the
    dead-coordinate moment eventually drops below it, since the dead
    moment has positive leading rate and tends to zero. -/
theorem smooth_two_channel_dead_eventually_lt (hK : 0 ≤ K)
    (hcont : Continuous φ)
    (hφ : ∀ u, |φ u - c * u| ≤ K * u ^ 2) (L : ℕ) (hL : 1 ≤ L) {s : ℝ}
    (hlive : 0 < ∫ z, smoothChain φ s L z ^ 2 ∂gaussMeasure) :
    ∀ᶠ t in 𝓝[>] (0:ℝ),
      (∫ x, ((fun q : ℝ × ℝ => (φ (t * q.1), φ (s * q.2)))^[L]
          (x, x)).1 ^ 2 ∂gaussMeasure)
        < ∫ x, ((fun q : ℝ × ℝ => (φ (t * q.1), φ (s * q.2)))^[L]
          (x, x)).2 ^ 2 ∂gaussMeasure := by
  have hco : ∀ t : ℝ, ∀ x : ℝ,
      (fun q : ℝ × ℝ => (φ (t * q.1), φ (s * q.2)))^[L] (x, x)
      = (smoothChain φ t L x, smoothChain φ s L x) := fun t x =>
    smoothPair_iterate L (x, x)
  have hdead := (smooth_chain_hasLeadingRate hK hcont hφ L).tendsto_zero
    (show 2 * L ≠ 0 by omega)
  have hev := hdead.eventually_lt_const hlive
  filter_upwards [hev] with t hlt
  have h1 : (fun x => ((fun q : ℝ × ℝ =>
        (φ (t * q.1), φ (s * q.2)))^[L] (x, x)).1 ^ 2)
      = fun x => smoothChain φ t L x ^ 2 := by
    funext x
    rw [hco t x]
  have h2 : (fun x => ((fun q : ℝ × ℝ =>
        (φ (t * q.1), φ (s * q.2)))^[L] (x, x)).2 ^ 2)
      = fun x => smoothChain φ s L x ^ 2 := by
    funext x
    rw [hco t x]
  rw [h1, h2]
  exact hlt

end SmoothBackward

end DeadDirections
