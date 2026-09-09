/-
  The route amplitudes derived from the network graph
  (prop:attn_chain_softmax), conditional on the attention pattern.

  The trichotomy of AttnBridge takes the route amplitudes a and b as
  parameters. Here they are derived: each block's attention matrix is
  built row-wise from the certified softmax, the backward action
  through a stack of blocks is the list product of those matrices,
  the V–O amplitude is the dead-channel reading of the composed
  action applied to the output gradient, and the score amplitude is
  the certified softmax-Jacobian reading times the composed forward
  reading of the dead-channel data. The route rates then hold with
  these derived coefficients: the reading at t = 0 is the
  coefficient, by continuity of every ingredient.

  Three structural facts come with the derivation. The composed
  action is row-stochastic, so the constant direction survives every
  block with amplitude exactly one (the shift-gauge structure at
  chain level). The composed action has non-negative entries, so on
  output gradients bounded below by a positive floor the V–O
  amplitude keeps that floor: non-degeneracy of the V–O route is
  unconditional on the positive cone, with no genericity needed.
  Generic non-cancellation of the signed sum stays where the paper
  puts it, as a hypothesis, now attached to derived objects.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import DeadDirections.SoftmaxN
import DeadDirections.AttnBridge
import DeadDirections.AnalyticNull

namespace DeadDirections

open Filter Topology

variable {N : ℕ}

/-- One block's data: base scores and their t²-perturbation, one row
    per position. -/
abbrev AttnSpec (N : ℕ) :=
  (Fin (N+1) → Fin (N+1) → ℝ) × (Fin (N+1) → Fin (N+1) → ℝ)

/-- The block's attention matrix along the approach: row i is the
    softmax of the perturbed score row i. -/
noncomputable def attnBlock (s : AttnSpec N) (t : ℝ) :
    Matrix (Fin (N+1)) (Fin (N+1)) ℝ :=
  fun i j => softmaxN (fun m => s.1 i m + t ^ 2 * s.2 i m) j

lemma attnBlock_entry_continuous (s : AttnSpec N) (i j : Fin (N+1)) :
    Continuous (fun t => attnBlock s t i j) := by
  unfold attnBlock
  exact (softmaxN_continuous j).comp
    (by continuity :
      Continuous (fun t : ℝ => fun m => s.1 i m + t ^ 2 * s.2 i m))

lemma attnBlock_nonneg (s : AttnSpec N) (t : ℝ) (i j : Fin (N+1)) :
    0 ≤ attnBlock s t i j :=
  (softmaxN_pos _ j).le

lemma attnBlock_row_one (s : AttnSpec N) (t : ℝ) (i : Fin (N+1)) :
    ∑ j, attnBlock s t i j = 1 :=
  softmaxN_sum_one _

/-- The composed backward action of a stack of blocks: the list
    product of the attention matrices. -/
noncomputable def chainA (bs : List (AttnSpec N)) (t : ℝ) :
    Matrix (Fin (N+1)) (Fin (N+1)) ℝ :=
  (bs.map (fun s => attnBlock s t)).prod

lemma chainA_nil (t : ℝ) : chainA ([] : List (AttnSpec N)) t = 1 :=
  rfl

lemma chainA_cons (s : AttnSpec N) (bs : List (AttnSpec N)) (t : ℝ) :
    chainA (s :: bs) t = attnBlock s t * chainA bs t := by
  unfold chainA
  rw [List.map_cons, List.prod_cons]

/-- Entries of the composed action are continuous in t. -/
lemma chainA_entry_continuous (bs : List (AttnSpec N))
    (i j : Fin (N+1)) :
    Continuous (fun t => chainA bs t i j) := by
  induction bs generalizing i j with
  | nil =>
    simp only [chainA_nil]
    exact continuous_const
  | cons s bs ih =>
    have heq : (fun t => chainA (s :: bs) t i j)
        = fun t => ∑ k, attnBlock s t i k * chainA bs t k j := by
      funext t
      rw [chainA_cons, Matrix.mul_apply]
    rw [heq]
    exact continuous_finset_sum _ fun k _ =>
      (attnBlock_entry_continuous s i k).mul (ih k j)

/-- Entries of the composed action are non-negative. -/
lemma chainA_nonneg (bs : List (AttnSpec N)) (t : ℝ)
    (i j : Fin (N+1)) :
    0 ≤ chainA bs t i j := by
  induction bs generalizing i j with
  | nil =>
    simp only [chainA_nil, Matrix.one_apply]
    split <;> norm_num
  | cons s bs ih =>
    rw [chainA_cons, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (attnBlock_nonneg s t i k) (ih k j)

/-- The composed action is row-stochastic: products of row-stochastic
    matrices keep unit row sums. -/
theorem chainA_row_stochastic (bs : List (AttnSpec N)) (t : ℝ)
    (i : Fin (N+1)) :
    ∑ j, chainA bs t i j = 1 := by
  induction bs generalizing i with
  | nil =>
    simp [chainA_nil, Matrix.one_apply]
  | cons s bs ih =>
    have heq : ∀ j, chainA (s :: bs) t i j
        = ∑ k, attnBlock s t i k * chainA bs t k j := by
      intro j
      rw [chainA_cons, Matrix.mul_apply]
    rw [Finset.sum_congr rfl fun j _ => heq j, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm]
    rw [Finset.sum_congr rfl fun k _ => by rw [ih k]]
    simpa using attnBlock_row_one s t i

/-- The constant direction survives the whole chain with amplitude
    exactly one: the shift-gauge structure at chain level. -/
theorem chainA_const (bs : List (AttnSpec N)) (t : ℝ) (c : ℝ)
    (n : Fin (N+1)) :
    (chainA bs t).mulVec (fun _ => c) n = c := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl fun k _ => rfl, ← Finset.sum_mul,
    chainA_row_stochastic, one_mul]

/-- The derived V–O amplitude: the dead-channel reading of the
    composed action applied to the output gradient, at the base
    attention pattern. -/
noncomputable def voAmp (bs : List (AttnSpec N)) (δ : Fin (N+1) → ℝ)
    (n : Fin (N+1)) : ℝ :=
  (chainA bs 0).mulVec δ n

/-- The positive-cone floor: on output gradients bounded below by a
    positive floor, the derived V–O amplitude keeps that floor.
    Non-degeneracy of the V–O route is unconditional here, with no
    genericity argument. -/
theorem voAmp_floor (bs : List (AttnSpec N)) {δ : Fin (N+1) → ℝ}
    {m : ℝ} (hm : ∀ k, m ≤ δ k) (n : Fin (N+1)) :
    m ≤ voAmp bs δ n := by
  unfold voAmp
  simp only [Matrix.mulVec, dotProduct]
  calc m = ∑ k, chainA bs 0 n k * m := by
        rw [← Finset.sum_mul, chainA_row_stochastic, one_mul]
    _ ≤ ∑ k, chainA bs 0 n k * δ k :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (hm k) (chainA_nonneg bs 0 n k)

/-- The V–O route with its derived coefficient: k blocks contribute
    the amplitude t^{2k}, the reading moves continuously in t, and
    the leading coefficient is exactly the derived amplitude at the
    base pattern. -/
theorem vo_route_derived (bs : List (AttnSpec N))
    (δ : Fin (N+1) → ℝ) (n : Fin (N+1)) :
    HasLeadingRate
      (fun t => t ^ (2 * bs.length) * (chainA bs t).mulVec δ n)
      (2 * bs.length) (voAmp bs δ n) := by
  have hg : Continuous (fun t => (chainA bs t).mulVec δ n) := by
    have heq : (fun t => (chainA bs t).mulVec δ n)
        = fun t => ∑ k, chainA bs t n k * δ k := by
      funext t
      simp [Matrix.mulVec, dotProduct]
    rw [heq]
    exact continuous_finset_sum _ fun k _ =>
      (chainA_entry_continuous bs n k).mul continuous_const
  exact hasLeadingRate_pow_factor (2 * bs.length) hg.continuousAt

/-- The certified softmax-Jacobian reading: the value of
    softmaxN_hasDerivAt_dir at direction h, read at position n. -/
noncomputable def scoreJac (z h : Fin (N+1) → ℝ) (n : Fin (N+1)) :
    ℝ :=
  softmaxN z n * (h n - ∑ j, softmaxN z j * h j)

/-- The derived score amplitude: the Jacobian reading at the probe
    scores times the composed forward reading of the dead-channel
    data. -/
noncomputable def scoreAmp (bs : List (AttnSpec N))
    (z h x : Fin (N+1) → ℝ) (n : Fin (N+1)) : ℝ :=
  scoreJac z h n * (chainA bs 0).mulVec x n

/-- The score route with its derived coefficient: p forward blocks
    plus the QK pair contribute t^{2p+4}, the Jacobian reading and
    the composed forward reading move continuously in t, and the
    leading coefficient is the derived score amplitude. -/
theorem score_route_derived (bs : List (AttnSpec N))
    (z bz h x : Fin (N+1) → ℝ) (n : Fin (N+1)) :
    HasLeadingRate
      (fun t => t ^ (2 * bs.length + 4)
        * (scoreJac (fun m => z m + t ^ 2 * bz m) h n
          * (chainA bs t).mulVec x n))
      (2 * bs.length + 4) (scoreAmp bs z h x n) := by
  have hjac : Continuous
      (fun t => scoreJac (fun m => z m + t ^ 2 * bz m) h n) := by
    unfold scoreJac
    have hz : Continuous
        (fun t : ℝ => fun m => z m + t ^ 2 * bz m) := by
      continuity
    apply Continuous.mul ((softmaxN_continuous n).comp hz)
    apply Continuous.sub continuous_const
    exact continuous_finset_sum _ fun j _ =>
      ((softmaxN_continuous j).comp hz).mul continuous_const
  have hread : Continuous (fun t => (chainA bs t).mulVec x n) := by
    have heq : (fun t => (chainA bs t).mulVec x n)
        = fun t => ∑ k, chainA bs t n k * x k := by
      funext t
      simp [Matrix.mulVec, dotProduct]
    rw [heq]
    exact continuous_finset_sum _ fun k _ =>
      (chainA_entry_continuous bs n k).mul continuous_const
  have hg : Continuous (fun t =>
      scoreJac (fun m => z m + t ^ 2 * bz m) h n
        * (chainA bs t).mulVec x n) := hjac.mul hread
  have hrate := hasLeadingRate_pow_factor (2 * bs.length + 4)
    hg.continuousAt
  have hval : scoreJac (fun m => z m + (0:ℝ) ^ 2 * bz m) h n
      * (chainA bs 0).mulVec x n = scoreAmp bs z h x n := by
    unfold scoreAmp
    congr 2
    funext m
    ring
  rw [hval] at hrate
  exact hrate

/-- The trichotomy with derived coefficients, below the crossing:
    the V–O chain carries rate 4k with coefficient voAmp². -/
theorem route_trichotomy_derived_vo (up down : List (AttnSpec N))
    (δ z h x : Fin (N+1) → ℝ) (n : Fin (N+1))
    (hlt : up.length < down.length + 2) :
    HasLeadingRate
      (routeMoment (voAmp up δ n) (scoreAmp down z h x n)
        up.length down.length)
      (4 * up.length) ((voAmp up δ n) ^ 2) :=
  route_moment_vo_wins _ _ hlt

/-- The trichotomy with derived coefficients, at the crossing: the
    routes share the leading order with the squared summed
    amplitudes, the profile peak. -/
theorem route_trichotomy_derived_tie (up down : List (AttnSpec N))
    (δ z h x : Fin (N+1) → ℝ) (n : Fin (N+1))
    (heq : up.length = down.length + 2) :
    HasLeadingRate
      (routeMoment (voAmp up δ n) (scoreAmp down z h x n)
        up.length down.length)
      (4 * up.length)
      ((voAmp up δ n + scoreAmp down z h x n) ^ 2) :=
  route_moment_tie _ _ heq

/-- The trichotomy with derived coefficients, above the crossing:
    the score-path floor carries rate 4p+8 with coefficient
    scoreAmp². -/
theorem route_trichotomy_derived_floor (up down : List (AttnSpec N))
    (δ z h x : Fin (N+1) → ℝ) (n : Fin (N+1))
    (hgt : down.length + 2 < up.length) :
    HasLeadingRate
      (routeMoment (voAmp up δ n) (scoreAmp down z h x n)
        up.length down.length)
      (4 * down.length + 8) ((scoreAmp down z h x n) ^ 2) :=
  route_moment_floor_wins _ _ hgt

/-! ### The non-cancellation upgrade

The paper takes generic non-cancellation of the two routes as a
hypothesis, calling cancellation a measure-zero coincidence. Two
pieces replace most of that hypothesis with theorems. At every
configuration whose score direction is constant across positions,
non-cancellation holds unconditionally: the softmax Jacobian kills
constants, so the score amplitude vanishes and the route sum is the
V–O amplitude, which the positive-cone floor bounds away from zero.
And along any one-parameter family on which the route sum is
analytic and passes through such a configuration, cancellation
happens at most on a Lebesgue-null set of parameters: the
analytic-zero-set lemma turns the witness into an almost-everywhere
statement. What remains of the hypothesis is the analyticity of the
route sum along the family, mechanical for affine score paths
through the exponential, and the several-parameter version, which
needs the Fubini induction over coordinates. -/

section NonCancellation

variable {N : ℕ}

/-- At a constant score direction the score amplitude vanishes: the
    softmax Jacobian kills constants. -/
lemma scoreAmp_const_dir (bs : List (AttnSpec N))
    (z x : Fin (N+1) → ℝ) (c : ℝ) (n : Fin (N+1)) :
    scoreAmp bs z (fun _ => c) x n = 0 := by
  unfold scoreAmp scoreJac
  rw [softmaxN_jacobian_const, zero_mul]

/-- The witness: at every constant-score-direction configuration
    with a positive-floor gradient, the route sum is positive.
    Non-cancellation holds unconditionally on this set. -/
theorem route_noncancellation_witness (bs bs' : List (AttnSpec N))
    (z x : Fin (N+1) → ℝ) (c : ℝ) {δ : Fin (N+1) → ℝ} {m : ℝ}
    (hm : 0 < m) (hδ : ∀ k, m ≤ δ k) (n : Fin (N+1)) :
    0 < voAmp bs δ n + scoreAmp bs' z (fun _ => c) x n := by
  rw [scoreAmp_const_dir, add_zero]
  exact lt_of_lt_of_le hm (voAmp_floor bs hδ n)

/-- The almost-everywhere upgrade: along any one-parameter family on
    which the route sum is analytic and which passes through a
    non-cancelling configuration, cancellation happens on a
    Lebesgue-null set of parameters. -/
theorem route_noncancellation_ae {F : ℝ → ℝ}
    (hF : AnalyticOnNhd ℝ F Set.univ) {t₀ : ℝ} (ht₀ : F t₀ ≠ 0) :
    MeasureTheory.volume {t : ℝ | F t = 0} = 0 :=
  analytic_zero_set_null hF ht₀

/-- The analyticity building block: every softmax entry is analytic
    along every affine score path, as the quotient of an exponential
    of an affine map by a positive sum of the same. The chain and
    route assemblies compose from this by products and sums. -/
lemma analyticOnNhd_softmax_path (z b : Fin (N+1) → ℝ)
    (i : Fin (N+1)) :
    AnalyticOnNhd ℝ
      (fun t => softmaxN (fun m => z m + t * b m) i) Set.univ := by
  intro t _
  have haff : ∀ j : Fin (N+1),
      AnalyticAt ℝ (fun t : ℝ => z j + t * b j) t :=
    fun j => analyticAt_const.add
      ((analyticAt_id).mul analyticAt_const)
  have hnum : AnalyticAt ℝ
      (fun t : ℝ => Real.exp (z i + t * b i)) t :=
    analyticAt_rexp.comp (haff i)
  have hden : AnalyticAt ℝ
      (fun t : ℝ => ∑ j, Real.exp (z j + t * b j)) t := by
    have h := Finset.analyticAt_sum (Finset.univ)
      (fun j (_ : j ∈ Finset.univ) => analyticAt_rexp.comp (haff j))
    have heq : (∑ j ∈ Finset.univ,
        Real.exp ∘ fun t : ℝ => z j + t * b j)
        = fun t : ℝ => ∑ j, Real.exp (z j + t * b j) := by
      funext t
      simp [Function.comp, Finset.sum_apply]
    rwa [heq] at h
  have hpos : (∑ j, Real.exp (z j + t * b j)) ≠ 0 :=
    ne_of_gt (sum_exp_pos _)
  exact hnum.div hden hpos

/-- Softmax along any analytic score path is analytic. -/
lemma analyticOnNhd_softmax_comp {z : ℝ → Fin (N+1) → ℝ}
    (hz : ∀ m, AnalyticOnNhd ℝ (fun s => z s m) Set.univ)
    (i : Fin (N+1)) :
    AnalyticOnNhd ℝ (fun s => softmaxN (z s) i) Set.univ := by
  intro t _
  have hnum : AnalyticAt ℝ (fun s => Real.exp (z s i)) t :=
    analyticAt_rexp.comp (hz i t (Set.mem_univ t))
  have hden : AnalyticAt ℝ
      (fun s => ∑ j, Real.exp (z s j)) t :=
    analyticAt_fun_sum Finset.univ fun j _ =>
      analyticAt_rexp.comp (hz j t (Set.mem_univ t))
  exact hnum.div hden (ne_of_gt (sum_exp_pos _))

/-- The one-parameter configuration family: base scores and their
    variation for each block, moved affinely, with no approach
    perturbation. -/
def specsAt (qs : List ((Fin (N+1) → Fin (N+1) → ℝ)
    × (Fin (N+1) → Fin (N+1) → ℝ))) (s : ℝ) : List (AttnSpec N) :=
  qs.map (fun q => (fun i m => q.1 i m + s * q.2 i m, fun _ _ => 0))

/-- Entries of the composed action are analytic along the family. -/
lemma analyticOnNhd_chainA_entry
    (qs : List ((Fin (N+1) → Fin (N+1) → ℝ)
      × (Fin (N+1) → Fin (N+1) → ℝ))) (t₀ : ℝ) (i j : Fin (N+1)) :
    AnalyticOnNhd ℝ (fun s => chainA (specsAt qs s) t₀ i j)
      Set.univ := by
  induction qs generalizing i j with
  | nil =>
    intro t _
    have heq : (fun s : ℝ => chainA (specsAt [] s) t₀ i j)
        = fun _ => (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) i j := by
      funext s
      rfl
    rw [heq]
    exact analyticAt_const
  | cons q qs ih =>
    have heq : (fun s => chainA (specsAt (q :: qs) s) t₀ i j)
        = fun s => ∑ k,
            softmaxN (fun m => (q.1 i m + s * q.2 i m)
              + t₀ ^ 2 * 0) k
            * chainA (specsAt qs s) t₀ k j := by
      funext s
      rw [show specsAt (q :: qs) s
          = (fun i m => q.1 i m + s * q.2 i m, fun _ _ => 0)
            :: specsAt qs s from rfl,
        chainA_cons, Matrix.mul_apply]
      rfl
    rw [heq]
    intro t _
    apply analyticAt_fun_sum
    intro k _
    apply AnalyticAt.mul
    · have hz : ∀ m, AnalyticOnNhd ℝ
          (fun s : ℝ => (q.1 i m + s * q.2 i m) + t₀ ^ 2 * 0)
          Set.univ := by
        intro m t' _
        exact (analyticAt_const.add
          ((analyticAt_id).mul analyticAt_const)).add analyticAt_const
      exact analyticOnNhd_softmax_comp hz k t (Set.mem_univ t)
    · exact ih k j t (Set.mem_univ t)

/-- The route sum is analytic along every affine configuration
    family: the V–O reading, the Jacobian factor, and the forward
    reading all compose from softmax entries. -/
lemma analyticOnNhd_route_sum
    (qs qs' : List ((Fin (N+1) → Fin (N+1) → ℝ)
      × (Fin (N+1) → Fin (N+1) → ℝ)))
    (z dz h₀ dh x δ : Fin (N+1) → ℝ) (n : Fin (N+1)) :
    AnalyticOnNhd ℝ (fun s =>
      voAmp (specsAt qs s) δ n
      + scoreAmp (specsAt qs' s) (fun m => z m + s * dz m)
          (fun m => h₀ m + s * dh m) x n) Set.univ := by
  have hread : ∀ (qs₂ : List ((Fin (N+1) → Fin (N+1) → ℝ)
      × (Fin (N+1) → Fin (N+1) → ℝ))) (v : Fin (N+1) → ℝ),
      AnalyticOnNhd ℝ
        (fun s => (chainA (specsAt qs₂ s) 0).mulVec v n)
        Set.univ := by
    intro qs₂ v t _
    have heq : (fun s => (chainA (specsAt qs₂ s) 0).mulVec v n)
        = fun s => ∑ k, chainA (specsAt qs₂ s) 0 n k * v k := by
      funext s
      simp [Matrix.mulVec, dotProduct]
    rw [heq]
    exact analyticAt_fun_sum Finset.univ fun k _ =>
      (analyticOnNhd_chainA_entry qs₂ 0 n k t
        (Set.mem_univ t)).mul analyticAt_const
  have hzpath : ∀ m, AnalyticOnNhd ℝ
      (fun s : ℝ => z m + s * dz m) Set.univ := by
    intro m t _
    exact analyticAt_const.add ((analyticAt_id).mul analyticAt_const)
  have hjac : AnalyticOnNhd ℝ (fun s =>
      scoreJac (fun m => z m + s * dz m)
        (fun m => h₀ m + s * dh m) n) Set.univ := by
    intro t _
    unfold scoreJac
    apply AnalyticAt.mul
    · exact analyticOnNhd_softmax_comp hzpath n t (Set.mem_univ t)
    · apply AnalyticAt.sub
      · exact analyticAt_const.add
          ((analyticAt_id).mul analyticAt_const)
      · exact analyticAt_fun_sum Finset.univ fun j _ =>
          (analyticOnNhd_softmax_comp hzpath j t
            (Set.mem_univ t)).mul
            (analyticAt_const.add
              ((analyticAt_id).mul analyticAt_const))
  intro t _
  apply AnalyticAt.add
  · exact hread qs δ t (Set.mem_univ t)
  · exact (hjac t (Set.mem_univ t)).mul
      (hread qs' x t (Set.mem_univ t))

/-- The concrete almost-everywhere non-cancellation: along every
    affine configuration family through a constant-score-direction
    configuration with a positive-floor gradient, the route sum
    cancels on at most a Lebesgue-null set of parameters. No
    analyticity hypothesis remains. -/
theorem route_noncancellation_ae_concrete
    (qs qs' : List ((Fin (N+1) → Fin (N+1) → ℝ)
      × (Fin (N+1) → Fin (N+1) → ℝ)))
    (z dz dh x : Fin (N+1) → ℝ) (c : ℝ) {δ : Fin (N+1) → ℝ}
    {m : ℝ} (hm : 0 < m) (hδ : ∀ k, m ≤ δ k) (n : Fin (N+1)) :
    MeasureTheory.volume {s : ℝ |
      voAmp (specsAt qs s) δ n
      + scoreAmp (specsAt qs' s) (fun k => z k + s * dz k)
          (fun k => (fun _ => c) k + s * dh k) x n = 0} = 0 := by
  apply analytic_zero_set_null
    (analyticOnNhd_route_sum qs qs' z dz (fun _ => c) dh x δ n)
    (x₀ := 0)
  have hz : (fun k => z k + (0:ℝ) * dz k) = z :=
    funext fun k => by ring
  have hh : (fun k => (fun _ => c) k + (0:ℝ) * dh k)
      = fun _ => c := funext fun k => by ring
  rw [hz, hh]
  exact ne_of_gt (route_noncancellation_witness _ _ _ _ c hm hδ n)

end NonCancellation

/-- cor:g10_composition's scope caveat: the additive reading 4k is
    the smaller route exactly where k ≤ p + 2, and the score-path
    floor 4p + 8 takes over beyond it. -/
theorem g10_anomaly_scope (k p : ℕ) :
    (4 * k ≤ 4 * p + 8 ↔ k ≤ p + 2) ∧ (4 * p + 8 < 4 * k ↔ p + 2 < k) := by
  constructor <;> constructor <;> intro h <;> omega

end DeadDirections
