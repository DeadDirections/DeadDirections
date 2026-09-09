/-
  Nonlinear rotation breaks the rate (theory paper,
  prop:bridge_nonlinear_rot_negative), exact witness.

  The paper presents this as an empirical demonstration and sketches
  the mechanism: elementwise masks commute with canonical directions
  only, so a rotated dead direction picks up a Θ(1) live overlap
  through the activation Jacobian, and the asymptotic exponent
  collapses to 0. Here the mechanism is proved exactly in the plane
  with the 3-4-5 rotation, live direction v = (3/5, 4/5) and dead
  direction u = (−4/5, 3/5). At the dead-probe input the
  pre-activation is t·u, whose coordinates carry opposite signs, so
  the ReLU mask is exactly (0, 1) for every t > 0: the masked dead
  direction leaves its own line with live overlap 12/25. The dead
  reading of a live backward flow then has leading rate 0 with
  coefficient 12c/25 (the collapse), a canonical reading keeps its
  rate K under any mask value (masks scale canonical directions in
  place), and the two exponents differ for every K ≥ 1.
-/
import Mathlib.Data.Fin.VecNotation
import DeadDirections.FisherDecay
import DeadDirections.RpowRate

namespace DeadDirections

open Filter Topology

/-- The live direction of the 3-4-5 rotation. -/
noncomputable def rotV : Fin 2 → ℝ := ![3/5, 4/5]

/-- The rotated dead direction. -/
noncomputable def rotU : Fin 2 → ℝ := ![-(4/5), 3/5]

lemma rotU_unit : rotU 0 ^ 2 + rotU 1 ^ 2 = 1 := by
  norm_num [rotU]

lemma rot_orth : rotV 0 * rotU 0 + rotV 1 * rotU 1 = 0 := by
  norm_num [rotV, rotU]

/-- The ReLU derivative away from the kink. -/
noncomputable def reluDeriv (z : ℝ) : ℝ := if 0 < z then 1 else 0

/-- At the dead-probe input the pre-activation is t·u, and its
    coordinates carry opposite signs, so the mask is exactly (0, 1)
    for every t > 0. -/
lemma witness_mask {t : ℝ} (ht : 0 < t) (i : Fin 2) :
    reluDeriv (t * rotU i) = (![0, 1] : Fin 2 → ℝ) i := by
  fin_cases i
  · show reluDeriv (t * rotU 0) = 0
    have hval : t * rotU 0 = t * (-(4/5)) := by norm_num [rotU]
    have hneg : t * rotU 0 < 0 := by rw [hval]; nlinarith
    unfold reluDeriv
    rw [if_neg (not_lt.mpr hneg.le)]
  · show reluDeriv (t * rotU 1) = 1
    have hval : t * rotU 1 = t * (3/5) := by norm_num [rotU]
    have hpos : 0 < t * rotU 1 := by rw [hval]; nlinarith
    unfold reluDeriv
    rw [if_pos hpos]

/-- The masked dead direction leaves its own line: its overlap with
    the live direction is 12/25, not 0. Canonical directions never do
    this (the lemma after next). -/
lemma masked_dead_live_overlap :
    ((![0, 1] : Fin 2 → ℝ) 0 * rotU 0 * rotV 0
      + (![0, 1] : Fin 2 → ℝ) 1 * rotU 1 * rotV 1) = 12/25 := by
  norm_num [rotU, rotV]

/-- Masks scale canonical directions in place: the elementwise
    product of any mask with e₂ stays on the e₂ line. -/
lemma canonical_mask_in_line (D : Fin 2 → ℝ) (i : Fin 2) :
    D i * (Pi.single 1 1 : Fin 2 → ℝ) i
      = D 1 * (Pi.single 1 1 : Fin 2 → ℝ) i := by
  fin_cases i
  · simp
  · simp

/-- The dead reading at the witness: the live backward flow c along
    v plus a t-order remainder, masked by the ReLU Jacobian at the
    probe pre-activation, projected on the rotated dead direction. -/
noncomputable def deadRead (c : ℝ) (r : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ i, rotU i * reluDeriv (t * rotU i) * (c * rotV i + t * r t)

/-- prop:bridge_nonlinear_rot_negative, proved at the witness: with
    a bounded remainder the dead reading has leading rate 0 with
    coefficient 12c/25. The mixed contribution enters at Θ(1) and
    the asymptotic exponent collapses to 0. -/
theorem rotated_rate_collapse (c : ℝ) {r : ℝ → ℝ} {M : ℝ}
    (hr : ∀ᶠ t in 𝓝[>] (0:ℝ), |r t| ≤ M) :
    HasLeadingRate (deadRead c r) 0 (12 * c / 25) := by
  have hform : ∀ᶠ t in 𝓝[>] (0:ℝ),
      deadRead c r t = 12 * c / 25 + 3/5 * (t * r t) := by
    filter_upwards [eventually_mem_nhdsWithin] with t ht0
    unfold deadRead
    rw [Fin.sum_univ_two]
    have h0 := witness_mask ht0 0
    have h1 := witness_mask ht0 1
    rw [h0, h1]
    norm_num [rotU, rotV]
    ring
  have hbound : ∀ᶠ t in 𝓝[>] (0:ℝ), ‖t * r t‖ ≤ t * M := by
    filter_upwards [hr, eventually_mem_nhdsWithin] with t htM ht0
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos ht0]
    exact mul_le_mul_of_nonneg_left htM ht0.le
  have hgM : Tendsto (fun t : ℝ => t * M) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => t * M) (𝓝 (0:ℝ))
        (𝓝 (0 * M)) := (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hrem : Tendsto (fun t => t * r t) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    squeeze_zero_norm' hbound hgM
  have hlim : Tendsto (fun t => 12 * c / 25 + 3/5 * (t * r t))
      (𝓝[>] (0:ℝ)) (𝓝 (12 * c / 25)) := by
    have h := (hrem.const_mul (3/5 : ℝ)).const_add (12 * c / 25)
    simpa using h
  unfold HasLeadingRate
  simp only [pow_zero, div_one]
  exact hlim.congr' (by filter_upwards [hform] with t h; rw [h])

/-- The canonical contrast: a canonical reading keeps its rate under
    any mask value, because masks scale canonical directions in
    place. -/
theorem canonical_reading_rate (m2 : ℝ) {g : ℝ → ℝ}
    (hg : ContinuousAt g 0) (K : ℕ) :
    HasLeadingRate (fun t => m2 * (t ^ K * g t)) K (m2 * g 0) :=
  (hasLeadingRate_pow_factor K hg).const_mul m2

/-- The collapse is a genuine rate disagreement at every positive
    depth. -/
theorem rotated_canonical_rates_differ (K : ℕ) (hK : 1 ≤ K) :
    (0 : ℕ) ≠ K := by omega

/-! ### The window bound and the crossover scale

The paper leaves two open items here: a quantitative finite-window
bound under controlled rotation, and the near-canonical crossover
scale as a function of the rotation amount. Both close at the model
level. The general-rotation witness shows the leak amplitude is
exactly γ·s·c (linear in the rotation sine s), so the observable is
G(t) = (γsc)² + b·t^m: a leak floor plus the canonical term. Its
local log-slope has two-sided window bounds (at least m(1−δ) above
the window edge, at most mδ below it) and a single half-maximum
crossover at b·t^m = (γsc)², so the crossover scale is
t_× = ((γsc)²/b)^{1/m}: as the rotation s → 0 the scale vanishes
and the canonical window extends to every t, which is exactly how
the two limits fail to commute. -/

section Window

/-- The general-rotation frame: dead direction (−s, c). At the
    dead-probe input the pre-activation coordinates carry opposite
    signs for every s, c, t > 0, so the mask is (0, 1) throughout
    the rotation family. -/
lemma witness_mask_general {s c t : ℝ} (hs : 0 < s) (hc : 0 < c)
    (ht : 0 < t) :
    reluDeriv (t * (-s)) = 0 ∧ reluDeriv (t * c) = 1 := by
  constructor
  · unfold reluDeriv
    rw [if_neg (not_lt.mpr (by nlinarith))]
  · unfold reluDeriv
    rw [if_pos (by nlinarith)]

/-- The leak amplitude at the general rotation: the masked dead
    direction (−s, c) overlaps the live direction (c, s) in exactly
    c·s, linear in the rotation sine. -/
lemma leak_amplitude_general (s c : ℝ) :
    (0 : ℝ) * (-s) * c + 1 * c * s = c * s := by ring

/-- The local log-slope of the leak-plus-canonical observable
    G(t) = c0 + b·t^m. -/
noncomputable def winSlope (c0 b : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  m * b * t ^ m / (c0 + b * t ^ m)

/-- The canonical window: above the window edge
    b·t^m ≥ (1/δ − 1)·c0 the slope is at least m(1−δ). -/
theorem window_canonical {c0 b δ : ℝ} (hc0 : 0 < c0) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (m : ℕ) {t : ℝ}
    (hwin : (1/δ - 1) * c0 ≤ b * t ^ m) :
    (m : ℝ) * (1 - δ) ≤ winSlope c0 b m t := by
  have h1δ : 1 < 1/δ := by
    rw [lt_div_iff₀ hδ0]
    linarith
  have hedge : 0 < (1/δ - 1) * c0 := mul_pos (by linarith) hc0
  have hxnn : 0 ≤ b * t ^ m := le_trans hedge.le hwin
  have hden : 0 < c0 + b * t ^ m := by linarith
  have hδx : (1 - δ) * c0 ≤ δ * (b * t ^ m) := by
    have h2 : δ * ((1/δ - 1) * c0) = (1 - δ) * c0 := by
      field_simp
    have h3 := mul_le_mul_of_nonneg_left hwin hδ0.le
    linarith
  have key : (m : ℝ) * (1 - δ) * (c0 + b * t ^ m)
      ≤ m * b * t ^ m := by
    have hfac : 0 ≤ δ * (b * t ^ m) - (1 - δ) * c0 := by linarith
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) hfac]
  have hnum : 0 ≤ (m : ℝ) * b * t ^ m
      - (m : ℝ) * (1 - δ) * (c0 + b * t ^ m) := by linarith
  have hq := div_nonneg hnum hden.le
  have heq : winSlope c0 b m t - (m : ℝ) * (1 - δ)
      = ((m : ℝ) * b * t ^ m
        - (m : ℝ) * (1 - δ) * (c0 + b * t ^ m)) / (c0 + b * t ^ m) := by
    unfold winSlope
    field_simp
  rw [← heq] at hq
  linarith

/-- The collapsed window: below b·t^m ≤ δ·c0 the slope is at most
    mδ. -/
theorem window_collapsed {c0 b δ : ℝ} (hc0 : 0 < c0) (hδ0 : 0 < δ)
    (m : ℕ) {t : ℝ} (hxnn : 0 ≤ b * t ^ m)
    (hwin : b * t ^ m ≤ δ * c0) :
    winSlope c0 b m t ≤ (m : ℝ) * δ := by
  have hden : 0 < c0 + b * t ^ m := by linarith
  have key : (m : ℝ) * b * t ^ m
      ≤ (m : ℝ) * δ * (c0 + b * t ^ m) := by
    have hfac : 0 ≤ δ * c0 - b * t ^ m := by linarith
    have hδx : 0 ≤ δ * (b * t ^ m) := by positivity
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) hfac,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) m) hδx]
  have hnum : 0 ≤ (m : ℝ) * δ * (c0 + b * t ^ m)
      - (m : ℝ) * b * t ^ m := by linarith
  have hq := div_nonneg hnum hden.le
  have heq : (m : ℝ) * δ - winSlope c0 b m t
      = ((m : ℝ) * δ * (c0 + b * t ^ m)
        - (m : ℝ) * b * t ^ m) / (c0 + b * t ^ m) := by
    unfold winSlope
    field_simp
  rw [← heq] at hq
  linarith

/-- The crossover: at b·t^m = c0 exactly, the slope is exactly half
    its maximum m. The crossover scale is t_× = (c0/b)^{1/m}. -/
theorem window_crossover {c0 b : ℝ} (hc0 : 0 < c0) (m : ℕ) {t : ℝ}
    (hcross : b * t ^ m = c0) :
    winSlope c0 b m t = m / 2 := by
  unfold winSlope
  rw [hcross]
  rw [show c0 + c0 = 2 * c0 by ring]
  rw [div_eq_div_iff (by linarith) (by norm_num : (2:ℝ) ≠ 0)]
  linear_combination 2 * (m : ℝ) * hcross

/-- The rotation-scaled crossover: with the leak floor (γsc)² the
    half-maximum crossover sits exactly at b·t^m = (γsc)², so the
    crossover scale is Θ(s^{2/m}) in the rotation sine and vanishes
    as s → 0: the non-commuting limits pass through this scale. -/
theorem rot_crossover_scale {γ s c b : ℝ} (hγ : γ ≠ 0) (hs : s ≠ 0)
    (hc : c ≠ 0) (m : ℕ) {t : ℝ}
    (hcross : b * t ^ m = (γ * s * c) ^ 2) :
    winSlope ((γ * s * c) ^ 2) b m t = m / 2 :=
  window_crossover (by positivity) m hcross

/-- The crossover scale in closed form: t_× = (c0/b)^{1/m} satisfies
    the crossover equation exactly, so the slope reads m/2 there.
    With the rotation-scaled floor c0 = (γsc)² this is the
    Θ(s^{2/m}) scale of the window remark. -/
theorem crossover_scale_closed_form {c0 b : ℝ} (hc0 : 0 < c0)
    (hb : 0 < b) {m : ℕ} (hm : 1 ≤ m) :
    winSlope c0 b m ((c0 / b) ^ ((1:ℝ)/m)) = m / 2 := by
  apply window_crossover hc0
  have hx : (0:ℝ) ≤ c0 / b := by positivity
  have hmne : ((m:ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpow : (((c0 / b) ^ ((1:ℝ)/m)) : ℝ) ^ m = c0 / b := by
    rw [← Real.rpow_natCast ((c0 / b) ^ ((1:ℝ)/m)) m,
      ← Real.rpow_mul hx, one_div, inv_mul_cancel₀ hmne,
      Real.rpow_one]
  rw [hpow, mul_comm, div_mul_cancel₀ c0 (ne_of_gt hb)]

end Window

end DeadDirections
