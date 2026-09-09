/-
  The single-head attention block rates (theory paper,
  thm:bridge_attn and thm:bridge_attn_backward), two-position scalar
  model.

  The softmax is genuinely present here as a logistic on the score
  gap of a two-position row. The forward mechanism: the bilinear
  QK dead entry carries two t-factors, so the attention weight moves
  by O(t²) (here: continuity of the logistic in t²), the V dead
  column contributes one t, and the O dead row the other, so the
  dead output is t² times an attention-weighted average and the
  forward block rate is 2. The backward mechanism: the V-route and
  the QK-route each carry two t-factors, the composite coefficient
  is the sum of the route coefficients, and rate 2 holds exactly
  when they do not cancel, the theorem's generic non-cancellation
  condition.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import DeadDirections.FisherDecay

namespace DeadDirections

open Filter Topology

/-- The two-position softmax: the logistic of the score gap. -/
noncomputable def logistic (z : ℝ) : ℝ := 1 / (1 + Real.exp (-z))

lemma logistic_continuous : Continuous logistic := by
  unfold logistic
  apply Continuous.div continuous_const
  · continuity
  · intro z
    positivity

/-- The bilinear score mechanism: the dead entry of QKᵀ carries two
    t-factors. -/
theorem score_bilinear (s x x' t : ℝ) :
    s + (t * x) * (t * x') = s + t ^ 2 * (x * x') := by ring

/-- The two-position attention weight along the approach: the
    logistic of the perturbed score gap. -/
noncomputable def attnA (ds db : ℝ) (t : ℝ) : ℝ :=
  logistic (ds + t ^ 2 * db)

/-- The dead-channel output of the block: one t from the V dead
    column, one from the O dead row, times the attention-weighted
    average of the dead-channel data. -/
noncomputable def attnDeadOut (ds db x1 x2 : ℝ) (t : ℝ) : ℝ :=
  t ^ 2 * (attnA ds db t * x1 + (1 - attnA ds db t) * x2)

/-- thm:bridge_attn, two-position model: the forward block rate is
    2, with coefficient the A₀-weighted average of the dead-channel
    data. -/
theorem bridge_attn_forward (ds db x1 x2 : ℝ) :
    HasLeadingRate (attnDeadOut ds db x1 x2) 2
      (logistic ds * x1 + (1 - logistic ds) * x2) := by
  have hg : ContinuousAt
      (fun t : ℝ => attnA ds db t * x1 + (1 - attnA ds db t) * x2)
      0 := by
    have hA : Continuous (fun t : ℝ => attnA ds db t) := by
      unfold attnA
      exact logistic_continuous.comp (by continuity)
    exact ((hA.mul continuous_const).add
      ((continuous_const.sub hA).mul continuous_const)).continuousAt
  have h := hasLeadingRate_pow_factor 2 hg
  have hval : attnA ds db 0 * x1 + (1 - attnA ds db 0) * x2
      = logistic ds * x1 + (1 - logistic ds) * x2 := by
    unfold attnA
    norm_num
  rw [hval] at h
  exact h

/-- The backward routes: each of the V-route and the QK-route
    carries two t-factors with a factor continuous at zero. -/
noncomputable def attnBackDead (gV gQ : ℝ → ℝ) (t : ℝ) : ℝ :=
  t ^ 2 * gV t + t ^ 2 * gQ t

/-- thm:bridge_attn_backward, model form: the composite carries rate
    2 with coefficient the sum of the route coefficients. The rate
    reading is informative exactly when gV 0 + gQ 0 ≠ 0, the
    theorem's generic non-cancellation condition. -/
theorem bridge_attn_backward {gV gQ : ℝ → ℝ}
    (hgV : ContinuousAt gV 0) (hgQ : ContinuousAt gQ 0) :
    HasLeadingRate (attnBackDead gV gQ) 2 (gV 0 + gQ 0) :=
  (hasLeadingRate_pow_factor 2 hgV).add_of_eq
    (hasLeadingRate_pow_factor 2 hgQ)

/-! ### The route inventory (prop:attn_chain_softmax)

The two backward routes built as per-block products: the V–O route
carries the two dead factors t² through each of the k blocks above
the probe, and the score route carries t² through each of the p
forward blocks below the probe plus the two QK-pair factors t⁴,
which softmaxN_hasDerivAt_dir certifies as the softmax Jacobian's
contribution. The composite moment is the squared route sum, and its
leading rate is the min(4k, 4p+8) trichotomy: the V–O route carries
it below the crossing, the floor carries it above, and at the
crossing k = p + 2 the two routes share the leading order with
coefficient (a+b)², the peak of the paper's non-monotone profile. -/

section RouteInventory

/-- The V–O route amplitude: k blocks, two dead factors each. -/
noncomputable def voRoute (a : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  a * ∏ _j : Fin k, t ^ 2

/-- The score route amplitude: p forward blocks plus the QK pair. -/
noncomputable def scoreRoute (b : ℝ) (p : ℕ) (t : ℝ) : ℝ :=
  b * (∏ _j : Fin p, t ^ 2) * t ^ 4

lemma voRoute_eq (a : ℝ) (k : ℕ) (t : ℝ) :
    voRoute a k t = a * t ^ (2 * k) := by
  unfold voRoute
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul]

lemma scoreRoute_eq (b : ℝ) (p : ℕ) (t : ℝ) :
    scoreRoute b p t = b * t ^ (2 * p + 4) := by
  unfold scoreRoute
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul, mul_assoc, ← pow_add]

/-- The composite moment: the squared sum of the two routes. -/
noncomputable def routeMoment (a b : ℝ) (k p : ℕ) (t : ℝ) : ℝ :=
  (voRoute a k t + scoreRoute b p t) ^ 2

lemma routeMoment_expand (a b : ℝ) (k p : ℕ) (t : ℝ) :
    routeMoment a b k p t
      = a ^ 2 * t ^ (4 * k)
        + (2 * (a * b) * t ^ (2 * k + (2 * p + 4))
          + b ^ 2 * t ^ (4 * p + 8)) := by
  unfold routeMoment
  rw [voRoute_eq, scoreRoute_eq]
  ring

/-- Below the crossing the V–O chain carries the rate: 4k with
    coefficient a². -/
theorem route_moment_vo_wins (a b : ℝ) {k p : ℕ} (h : k < p + 2) :
    HasLeadingRate (routeMoment a b k p) (4 * k) (a ^ 2) := by
  have h1 : HasLeadingRate (fun t => a ^ 2 * t ^ (4 * k)) (4 * k)
      (a ^ 2) := by
    simpa using (hasLeadingRate_pow (4 * k)).const_mul (a ^ 2)
  have h2 : HasLeadingRate
      (fun t => 2 * (a * b) * t ^ (2 * k + (2 * p + 4)))
      (2 * k + (2 * p + 4)) (2 * (a * b)) := by
    simpa using
      (hasLeadingRate_pow (2 * k + (2 * p + 4))).const_mul
        (2 * (a * b))
  have h3 : HasLeadingRate (fun t => b ^ 2 * t ^ (4 * p + 8))
      (4 * p + 8) (b ^ 2) := by
    simpa using (hasLeadingRate_pow (4 * p + 8)).const_mul (b ^ 2)
  have h23 := h2.add_of_lt h3 (by omega)
  have h123 := h1.add_of_lt h23 (by omega)
  refine h123.congr fun t => ?_
  rw [routeMoment_expand]

/-- At the crossing k = p + 2 the routes share the leading order:
    rate 4k with coefficient (a+b)², the profile peak. -/
theorem route_moment_tie (a b : ℝ) {k p : ℕ} (h : k = p + 2) :
    HasLeadingRate (routeMoment a b k p) (4 * k) ((a + b) ^ 2) := by
  subst h
  have hexp1 : 2 * (p + 2) + (2 * p + 4) = 4 * (p + 2) := by omega
  have hexp2 : 4 * p + 8 = 4 * (p + 2) := by omega
  have h1 : HasLeadingRate (fun t => a ^ 2 * t ^ (4 * (p + 2)))
      (4 * (p + 2)) (a ^ 2) := by
    simpa using (hasLeadingRate_pow (4 * (p + 2))).const_mul (a ^ 2)
  have h2 : HasLeadingRate
      (fun t => 2 * (a * b) * t ^ (4 * (p + 2))) (4 * (p + 2))
      (2 * (a * b)) := by
    simpa using
      (hasLeadingRate_pow (4 * (p + 2))).const_mul (2 * (a * b))
  have h3 : HasLeadingRate (fun t => b ^ 2 * t ^ (4 * (p + 2)))
      (4 * (p + 2)) (b ^ 2) := by
    simpa using (hasLeadingRate_pow (4 * (p + 2))).const_mul (b ^ 2)
  have h123 := h1.add_of_eq (h2.add_of_eq h3)
  have hcoeff : a ^ 2 + (2 * (a * b) + b ^ 2) = (a + b) ^ 2 := by
    ring
  rw [hcoeff] at h123
  refine h123.congr fun t => ?_
  rw [routeMoment_expand, hexp1, hexp2]

/-- Above the crossing the score-path floor carries the rate: 4p + 8
    with coefficient b², the sum overstating the rate. -/
theorem route_moment_floor_wins (a b : ℝ) {k p : ℕ}
    (h : p + 2 < k) :
    HasLeadingRate (routeMoment a b k p) (4 * p + 8) (b ^ 2) := by
  have h1 : HasLeadingRate (fun t => a ^ 2 * t ^ (4 * k)) (4 * k)
      (a ^ 2) := by
    simpa using (hasLeadingRate_pow (4 * k)).const_mul (a ^ 2)
  have h2 : HasLeadingRate
      (fun t => 2 * (a * b) * t ^ (2 * k + (2 * p + 4)))
      (2 * k + (2 * p + 4)) (2 * (a * b)) := by
    simpa using
      (hasLeadingRate_pow (2 * k + (2 * p + 4))).const_mul
        (2 * (a * b))
  have h3 : HasLeadingRate (fun t => b ^ 2 * t ^ (4 * p + 8))
      (4 * p + 8) (b ^ 2) := by
    simpa using (hasLeadingRate_pow (4 * p + 8)).const_mul (b ^ 2)
  have h32 := h3.add_of_lt h2 (by omega)
  have h321 := h32.add_of_lt h1 (by omega)
  refine h321.congr fun t => ?_
  rw [routeMoment_expand]
  ring

end RouteInventory

end DeadDirections
