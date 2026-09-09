/-
  The LayerNorm reset channel (theory paper, thm:bridge_ln).

  The proposition brackets the dead-direction rate between the
  post-crossing weight count and the full weight count, and its
  mechanism is the normalizer's scale invariance: a crossing erases
  the decay accumulated above it. The scalar model realises both ends
  of the bracket exactly. The normalize map z ↦ z/|z| is invariant
  under every positive scaling, so a channel decayed to t^{k_pre}
  crosses it and returns to unit moment; the k_post weights below the
  crossing then contribute their factors, and the composed moment is
  t^{2·k_post} exactly, the plateau end 2·K_lower with the upstream
  decay erased. Without a crossing the same channel reads
  t^{2(k_pre + k_post)}, the regime-(i) end. The bracket inequality on
  the full LN backward Jacobian stays with the paper.
-/
import DeadDirections.MixtureScore

namespace DeadDirections

open MeasureTheory Filter Topology

/-- The scalar normalizer: z/|z|, the sign of z, with the junk value 0
    at z = 0. -/
noncomputable def normalizeS (z : ℝ) : ℝ := z / |z|

/-- Scale invariance: the normalizer erases every positive factor.
    This is the reset mechanism of thm:bridge_ln's plateau. -/
lemma normalizeS_scale {c : ℝ} (hc : 0 < c) (z : ℝ) :
    normalizeS (c * z) = normalizeS z := by
  unfold normalizeS
  rw [abs_mul, abs_of_pos hc]
  rcases eq_or_ne z 0 with hz | hz
  · simp [hz]
  · rw [mul_div_mul_left _ _ (ne_of_gt hc)]

lemma normalizeS_sq_of_ne {z : ℝ} (hz : z ≠ 0) : normalizeS z ^ 2 = 1 := by
  unfold normalizeS
  rw [div_pow, sq_abs]
  exact div_self (pow_ne_zero 2 hz)

/-- The reset identity: a channel decayed to t^k crosses the
    normalizer and returns to unit second moment, at every t > 0. The
    accumulated decay is erased, not damped. -/
theorem ln_reset_moment {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ∫ x, normalizeS (t ^ k * x) ^ 2 * gaussDensity x 0 1 = 1 := by
  have hscale : ∀ x : ℝ, normalizeS (t ^ k * x) = normalizeS x :=
    fun x => normalizeS_scale (pow_pos ht k) x
  simp only [hscale]
  have hae : (fun x => normalizeS x ^ 2 * gaussDensity x 0 1)
      =ᵐ[volume] fun x => gaussDensity x 0 1 := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
      (measure_singleton (0:ℝ))] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    rw [normalizeS_sq_of_ne hx0, one_mul]
  rw [integral_congr_ae hae]
  exact integral_gaussDensity_eq_one 0

/-- thm:bridge_ln, plateau end: k_post weights below the crossing act
    on the reset channel, and the composed moment is t^{2·k_post}
    exactly, whatever decay k_pre accumulated above the crossing. The
    upper end of the bracket is attained. -/
theorem ln_bracket_plateau {t : ℝ} (ht : 0 < t) (kpre kpost : ℕ) :
    ∫ x, (t ^ kpost * normalizeS (t ^ kpre * x)) ^ 2 * gaussDensity x 0 1
      = t ^ (2 * kpost) := by
  have hfun : ∀ x : ℝ,
      (t ^ kpost * normalizeS (t ^ kpre * x)) ^ 2 * gaussDensity x 0 1
      = t ^ (2 * kpost)
        * (normalizeS (t ^ kpre * x) ^ 2 * gaussDensity x 0 1) := by
    intro x
    rw [mul_pow, show (t ^ kpost) ^ 2 = t ^ (2 * kpost) from by
      rw [← pow_mul, Nat.mul_comm]]
    ring
  simp only [hfun]
  rw [integral_const_mul, ln_reset_moment ht kpre, mul_one]

/-- The no-crossing end: the same channel without a normalizer reads
    the full weight count, t^{2(k_pre + k_post)}, the regime-(i) tight
    case. Both ends of the bracket are realised on the model. -/
theorem ln_bracket_no_crossing (t : ℝ) (kpre kpost : ℕ) :
    ∫ x, (t ^ kpost * (t ^ kpre * x)) ^ 2 * gaussDensity x 0 1
      = t ^ (2 * (kpre + kpost)) := by
  have hfun : ∀ x : ℝ,
      (t ^ kpost * (t ^ kpre * x)) ^ 2 * gaussDensity x 0 1
      = t ^ (2 * (kpre + kpost)) * (x ^ 2 * gaussDensity x 0 1) := by
    intro x
    rw [show t ^ kpost * (t ^ kpre * x) = t ^ (kpre + kpost) * x from by
        rw [pow_add]
        ring,
      mul_pow, show (t ^ (kpre + kpost)) ^ 2 = t ^ (2 * (kpre + kpost))
        from by rw [← pow_mul, Nat.mul_comm]]
    ring
  simp only [hfun]
  rw [integral_const_mul]
  have hone : ∫ x, x ^ 2 * gaussDensity x 0 1 = 1 := by
    have h := integral_sq_gaussMeasure
    rwa [integral_gaussMeasure] at h
  rw [hone, mul_one]

end DeadDirections
