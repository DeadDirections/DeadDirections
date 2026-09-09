/-
  The residual DAG in Bellman form: multi-path interference at rate
  level (thm:bridge_res, def:path_distance, cor:sigma-min-res).

  The backward delta on a residual computational graph is a sum over
  backward paths from the output, each weight edge contributing a
  factor c·t and each skip edge a factor one. The shortest-weighted-
  path distance K of def:path_distance is the Bellman recursion
  K(m+1) = min(K(m) + 1, min over skips K(m')), and the backward
  delta obeys the matching recursion T(m+1) = c·t·T(m) + Σ_skips T(m').
  Rates compose through the recursion by the two-route law: a sum of
  leading rates carries the smaller rate, and tied rates add their
  coefficients. With every weight coefficient positive (the
  φ′(0) > 0 classes) no tie cancels, so T(m) has leading rate exactly
  K(m) with a positive coefficient, and the dead moment reads
  t^{2K(m)}: the framework behind the residual corollaries, with the
  multi-path interference made explicit in the coefficient.
-/
import DeadDirections.FisherDecay

namespace DeadDirections

open Filter Topology

/-- Two leading rates with positive coefficients add at the smaller
    rate, with a positive coefficient: the smaller wins, and a tie
    adds. -/
theorem HasLeadingRate.add_min {F G : ℝ → ℝ} {p q : ℕ} {a b : ℝ}
    (hF : HasLeadingRate F p a) (hG : HasLeadingRate G q b)
    (ha : 0 < a) (hb : 0 < b) :
    ∃ c, 0 < c ∧ HasLeadingRate (fun t => F t + G t) (min p q) c := by
  rcases lt_trichotomy p q with h | h | h
  · refine ⟨a, ha, ?_⟩
    rw [min_eq_left h.le]
    exact hF.add_of_lt hG h
  · subst h
    refine ⟨a + b, by linarith, ?_⟩
    rw [min_self]
    exact hF.add_of_eq hG
  · refine ⟨b, hb, ?_⟩
    rw [min_eq_right h.le]
    have h2 := hG.add_of_lt hF h
    refine h2.congr fun t => ?_
    simp only [add_comm]

/-- A finite sum of leading rates with positive coefficients carries
    the minimum rate with a positive coefficient. -/
theorem hasLeadingRate_finset_sum_pos {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) (F : ι → ℝ → ℝ) (p : ι → ℕ) (a : ι → ℝ)
    (hF : ∀ i ∈ s, HasLeadingRate (F i) (p i) (a i))
    (ha : ∀ i ∈ s, 0 < a i) :
    ∃ c, 0 < c ∧ HasLeadingRate (fun t => ∑ i ∈ s, F i t) (s.inf' hs p) c := by
  revert hF ha
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
    intro hF ha
    refine ⟨a i, ha i (Finset.mem_singleton_self i), ?_⟩
    rw [Finset.inf'_singleton]
    refine (hF i (Finset.mem_singleton_self i)).congr fun t => ?_
    simp only [Finset.sum_singleton]
  | cons i s hi hs ih =>
    intro hF ha
    obtain ⟨c, hc, hsum⟩ := ih
      (fun j hj => hF j (Finset.mem_cons_of_mem hj))
      (fun j hj => ha j (Finset.mem_cons_of_mem hj))
    obtain ⟨c', hc', h'⟩ := (hF i (Finset.mem_cons_self i s)).add_min hsum
      (ha i (Finset.mem_cons_self i s)) hc
    refine ⟨c', hc', ?_⟩
    rw [Finset.inf'_cons (H := hs)]
    refine h'.congr fun t => ?_
    simp only [Finset.sum_cons]

/-- The residual DAG in Bellman form, nodes indexed by distance from
    the output: with K the shortest-weighted-path distance (the
    Bellman recursion over weight edges of cost one and skip edges of
    cost zero) and T the backward delta (the matching recursion with
    positive weight coefficients), T(m) has leading rate K(m) with a
    positive coefficient at every node. Multi-path interference is
    the coefficient: tied shortest paths add, and positivity keeps
    the sum from cancelling. -/
theorem dag_backward_rate (sk : ℕ → Finset ℕ)
    (hsk : ∀ m, ∀ m' ∈ sk (m+1), m' ≤ m)
    (K : ℕ → ℕ) (hK0 : K 0 = 0)
    (hKe : ∀ m, sk (m+1) = ∅ → K (m+1) = K m + 1)
    (hKn : ∀ m (h : (sk (m+1)).Nonempty),
      K (m+1) = min (K m + 1) ((sk (m+1)).inf' h K))
    (c : ℕ → ℝ) (hc : ∀ m, 0 < c m)
    (T : ℕ → ℝ → ℝ) (hT0 : ∀ t, T 0 t = 1)
    (hTs : ∀ m t, T (m+1) t
      = c (m+1) * t * T m t + ∑ m' ∈ sk (m+1), T m' t) :
    ∀ m, ∃ coef, 0 < coef ∧ HasLeadingRate (T m) (K m) coef := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero =>
      refine ⟨1, one_pos, ?_⟩
      rw [hK0]
      refine (hasLeadingRate_const 1).congr fun t => ?_
      rw [hT0]
    | succ m =>
      obtain ⟨a, ha, hTm⟩ := ih m (Nat.lt_succ_self m)
      have hw : HasLeadingRate (fun t => c (m+1) * t * T m t) (K m + 1)
          (c (m+1) * a) := by
        have h1 : HasLeadingRate (fun t => c (m+1) * t) 1 (c (m+1)) := by
          have := (hasLeadingRate_pow 1).const_mul (c (m+1))
          simpa using this
        have h2 := h1.mul hTm
        rw [show 1 + K m = K m + 1 from Nat.add_comm 1 (K m)] at h2
        exact h2
      have hwpos : 0 < c (m+1) * a := mul_pos (hc _) ha
      by_cases hemp : sk (m+1) = ∅
      · refine ⟨c (m+1) * a, hwpos, ?_⟩
        rw [hKe m hemp]
        refine hw.congr fun t => ?_
        rw [hTs, hemp, Finset.sum_empty, add_zero]
      · have hne : (sk (m+1)).Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
        have hall : ∀ m' ∈ sk (m+1), ∃ coef, 0 < coef
            ∧ HasLeadingRate (T m') (K m') coef :=
          fun m' hm' => ih m' (Nat.lt_succ_of_le (hsk m m' hm'))
        choose! coefF hpos hrate using hall
        obtain ⟨cs, hcs, hS⟩ := hasLeadingRate_finset_sum_pos hne
          (fun m' => T m') K coefF hrate hpos
        obtain ⟨c', hc', h'⟩ := hw.add_min hS hwpos hcs
        refine ⟨c', hc', ?_⟩
        rw [hKn m hne]
        refine h'.congr fun t => ?_
        rw [hTs]

/-- The dead moment along the DAG reads the squared rate 2K(m) with a
    positive coefficient: thm:bridge_res in Bellman form. -/
theorem dag_backward_moment_rate (sk : ℕ → Finset ℕ)
    (hsk : ∀ m, ∀ m' ∈ sk (m+1), m' ≤ m)
    (K : ℕ → ℕ) (hK0 : K 0 = 0)
    (hKe : ∀ m, sk (m+1) = ∅ → K (m+1) = K m + 1)
    (hKn : ∀ m (h : (sk (m+1)).Nonempty),
      K (m+1) = min (K m + 1) ((sk (m+1)).inf' h K))
    (c : ℕ → ℝ) (hc : ∀ m, 0 < c m)
    (T : ℕ → ℝ → ℝ) (hT0 : ∀ t, T 0 t = 1)
    (hTs : ∀ m t, T (m+1) t
      = c (m+1) * t * T m t + ∑ m' ∈ sk (m+1), T m' t) (m : ℕ) :
    ∃ coef, 0 < coef ∧ HasLeadingRate (fun t => T m t ^ 2) (2 * K m) coef := by
  obtain ⟨a, ha, hT⟩ := dag_backward_rate sk hsk K hK0 hKe hKn c hc T hT0 hTs m
  refine ⟨a ^ 2, by positivity, ?_⟩
  have h := hT.mul hT
  rw [← two_mul, ← sq] at h
  refine h.congr fun t => ?_
  simp only [sq]

/-- With no skips the Bellman distance is the depth: the feedforward
    ladder K(m) = m. -/
theorem dag_no_skip_K (sk : ℕ → Finset ℕ) (hsk0 : ∀ m, sk (m+1) = ∅)
    (K : ℕ → ℕ) (hK0 : K 0 = 0)
    (hKe : ∀ m, sk (m+1) = ∅ → K (m+1) = K m + 1) :
    ∀ m, K m = m := by
  intro m
  induction m with
  | zero => exact hK0
  | succ m ih => rw [hKe m (hsk0 m), ih]

/-- A skip across the whole graph pins the distance at zero: the
    all-residual floor K = 0 at the skip's source, whatever the
    weight chain between. -/
theorem dag_full_skip_K (sk : ℕ → Finset ℕ) (K : ℕ → ℕ) (hK0 : K 0 = 0)
    (hKn : ∀ m (h : (sk (m+1)).Nonempty),
      K (m+1) = min (K m + 1) ((sk (m+1)).inf' h K))
    (m : ℕ) (h0 : 0 ∈ sk (m+1)) :
    K (m+1) = 0 := by
  have hne : (sk (m+1)).Nonempty := ⟨0, h0⟩
  rw [hKn m hne]
  have hinf : (sk (m+1)).inf' hne K ≤ K 0 := Finset.inf'_le K h0
  rw [hK0] at hinf
  omega

/-! ### The nonlinear gating clause

On the ReLU class every weight edge carries the survival gate and
skip edges pass the delta unchanged. With a shared gate g ∈ {0, 1}
the gated delta T_g obeys the recursion with c·t·g on weight edges.
Every path to a node of positive distance crosses at least one weight
edge, so every term carries the gate and T_g = g·T there; the
skip-only part T₀ counts pure-skip paths and vanishes exactly where
K ≥ 1. The dead moment of the gated delta is then E[g]·T², the
ungated rate 2K with the base case scaled by the survival
probability. -/

/-- The skip-only path count is nonnegative and vanishes exactly at
    the nodes of positive Bellman distance. -/
theorem dag_skiponly_zero_iff (sk : ℕ → Finset ℕ)
    (hsk : ∀ m, ∀ m' ∈ sk (m+1), m' ≤ m)
    (K : ℕ → ℕ) (hK0 : K 0 = 0)
    (hKe : ∀ m, sk (m+1) = ∅ → K (m+1) = K m + 1)
    (hKn : ∀ m (h : (sk (m+1)).Nonempty),
      K (m+1) = min (K m + 1) ((sk (m+1)).inf' h K))
    (T0 : ℕ → ℝ) (hT00 : T0 0 = 1)
    (hT0s : ∀ m, T0 (m+1) = ∑ m' ∈ sk (m+1), T0 m') :
    ∀ m, 0 ≤ T0 m ∧ (T0 m = 0 ↔ 1 ≤ K m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero =>
      rw [hT00, hK0]
      constructor
      · exact zero_le_one
      · constructor
        · intro h; norm_num at h
        · intro h; omega
    | succ m =>
      have hnn : ∀ m' ∈ sk (m+1), 0 ≤ T0 m' :=
        fun m' hm' => (ih m' (Nat.lt_succ_of_le (hsk m m' hm'))).1
      have hiff : ∀ m' ∈ sk (m+1), (T0 m' = 0 ↔ 1 ≤ K m') :=
        fun m' hm' => (ih m' (Nat.lt_succ_of_le (hsk m m' hm'))).2
      rw [hT0s]
      refine ⟨Finset.sum_nonneg hnn, ?_⟩
      by_cases hemp : sk (m+1) = ∅
      · rw [hemp, Finset.sum_empty, hKe m hemp]
        constructor
        · intro _; omega
        · intro _; rfl
      · have hne : (sk (m+1)).Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
        rw [Finset.sum_eq_zero_iff_of_nonneg hnn, hKn m hne, le_min_iff,
          Finset.le_inf'_iff]
        constructor
        · intro h
          exact ⟨by omega, fun m' hm' => (hiff m' hm').mp (h m' hm')⟩
        · intro h m' hm'
          exact (hiff m' hm').mpr (h.2 m' hm')

/-- With a shared gate g ∈ {0, 1} on every weight edge, the gated
    delta equals g times the ungated delta at every node of positive
    distance. -/
theorem dag_gated_eq (sk : ℕ → Finset ℕ)
    (hsk : ∀ m, ∀ m' ∈ sk (m+1), m' ≤ m)
    (K : ℕ → ℕ) (hK0 : K 0 = 0)
    (hKe : ∀ m, sk (m+1) = ∅ → K (m+1) = K m + 1)
    (hKn : ∀ m (h : (sk (m+1)).Nonempty),
      K (m+1) = min (K m + 1) ((sk (m+1)).inf' h K))
    (c : ℕ → ℝ) (T : ℕ → ℝ → ℝ) (hT0 : ∀ t, T 0 t = 1)
    (hTs : ∀ m t, T (m+1) t
      = c (m+1) * t * T m t + ∑ m' ∈ sk (m+1), T m' t)
    (T0 : ℕ → ℝ) (hT00 : T0 0 = 1)
    (hT0s : ∀ m, T0 (m+1) = ∑ m' ∈ sk (m+1), T0 m')
    (Tg : ℕ → ℝ → ℝ) (g : ℝ) (hg : g = 0 ∨ g = 1)
    (hTg0 : ∀ t, Tg 0 t = 1)
    (hTgs : ∀ m t, Tg (m+1) t
      = c (m+1) * t * g * Tg m t + ∑ m' ∈ sk (m+1), Tg m' t) :
    ∀ m t, 1 ≤ K m → Tg m t = g * T m t := by
  rcases hg with hg | hg
  · -- gate closed: the gated delta is the skip-only count
    have hT0eq : ∀ m t, Tg m t = T0 m := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro t
        cases m with
        | zero => rw [hTg0, hT00]
        | succ m =>
          rw [hTgs, hT0s, hg, mul_zero, zero_mul, zero_add]
          exact Finset.sum_congr rfl fun m' hm' =>
            ih m' (Nat.lt_succ_of_le (hsk m m' hm')) t
    intro m t hK
    rw [hT0eq m t, hg, zero_mul]
    exact ((dag_skiponly_zero_iff sk hsk K hK0 hKe hKn T0 hT00 hT0s m).2).mpr hK
  · -- gate open: the recursions coincide
    have hTeq : ∀ m t, Tg m t = T m t := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro t
        cases m with
        | zero => rw [hTg0, hT0]
        | succ m =>
          rw [hTgs, hTs, hg, mul_one, ih m (Nat.lt_succ_self m) t]
          congr 1
          exact Finset.sum_congr rfl fun m' hm' =>
            ih m' (Nat.lt_succ_of_le (hsk m m' hm')) t
    intro m t _
    rw [hTeq m t, hg, one_mul]

/-- The gated dead moment: with an idempotent gate, the second moment
    of g·x is E[g]·x², the base case scaled by the survival
    probability. -/
theorem gated_moment_factor {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} (g : Ω → ℝ) (hg : ∀ ω, g ω = 0 ∨ g ω = 1)
    (x : ℝ) :
    ∫ ω, (g ω * x) ^ 2 ∂μ = (∫ ω, g ω ∂μ) * x ^ 2 := by
  have hfun : ∀ ω, (g ω * x) ^ 2 = g ω * x ^ 2 := by
    intro ω
    rcases hg ω with h | h <;> rw [h] <;> ring
  simp_rw [hfun]
  exact MeasureTheory.integral_mul_const _ _

/-! ### The explicit Schur constant

The coefficient of the backward delta is the sum over shortest paths
of the products of weight coefficients: at each node the weight-edge
term contributes when the chain through the parent is shortest, and
each skip contributes when its source is shortest. The explicit
two-term and finite-sum laws below carry the coefficient without any
positivity, and the DAG recursion for the constant follows. -/

/-- Two leading rates add at the smaller rate; the coefficient is the
    smaller rate's, or the sum at a tie. -/
theorem HasLeadingRate.add_min_coeff {F G : ℝ → ℝ} {p q : ℕ} {a b : ℝ}
    (hF : HasLeadingRate F p a) (hG : HasLeadingRate G q b) :
    HasLeadingRate (fun t => F t + G t) (min p q)
      (if p < q then a else if q < p then b else a + b) := by
  rcases lt_trichotomy p q with h | h | h
  · rw [min_eq_left h.le, if_pos h]
    exact hF.add_of_lt hG h
  · subst h
    rw [min_self, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
    exact hF.add_of_eq hG
  · rw [min_eq_right h.le, if_neg (not_lt.mpr h.le), if_pos h]
    have h2 := hG.add_of_lt hF h
    refine h2.congr fun t => ?_
    simp only [add_comm]

/-- A finite sum of leading rates carries the minimum rate with
    coefficient the sum of the coefficients at the minimum. -/
theorem hasLeadingRate_finset_sum {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) (F : ι → ℝ → ℝ) (p : ι → ℕ) (a : ι → ℝ)
    (hF : ∀ i ∈ s, HasLeadingRate (F i) (p i) (a i)) :
    HasLeadingRate (fun t => ∑ i ∈ s, F i t) (s.inf' hs p)
      (∑ i ∈ s.filter (fun i => p i = s.inf' hs p), a i) := by
  revert hF
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
    intro hF
    rw [Finset.inf'_singleton, Finset.filter_singleton, if_pos rfl,
      Finset.sum_singleton]
    refine (hF i (Finset.mem_singleton_self i)).congr fun t => ?_
    simp only [Finset.sum_singleton]
  | cons i s hi hs ih =>
    intro hF
    have hsum := ih (fun j hj => hF j (Finset.mem_cons_of_mem hj))
    have hi' := hF i (Finset.mem_cons_self i s)
    have hmin := hi'.add_min_coeff hsum
    simp_rw [Finset.inf'_cons (H := hs)]
    rw [Finset.filter_cons]
    rcases lt_trichotomy (p i) (s.inf' hs p) with h | h | h
    · rw [min_eq_left h.le] at hmin ⊢
      rw [if_pos h] at hmin
      have hfilt : s.filter (fun j => p j = p i) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro j hj hpj
        have := Finset.inf'_le p hj
        omega
      rw [if_pos rfl, Finset.sum_cons, hfilt, Finset.sum_empty, add_zero]
      refine hmin.congr fun t => ?_
      simp only [Finset.sum_cons]
    · rw [h, min_self] at hmin ⊢
      rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)] at hmin
      rw [if_pos rfl, Finset.sum_cons]
      refine hmin.congr fun t => ?_
      simp only [Finset.sum_cons]
    · rw [min_eq_right h.le] at hmin ⊢
      rw [if_neg (not_lt.mpr h.le), if_pos h] at hmin
      rw [if_neg (ne_of_gt h)]
      refine hmin.congr fun t => ?_
      simp only [Finset.sum_cons]

/-- The explicit constant: with coef obeying the shortest-path
    recursion (the weight term enters when the parent chain is
    shortest, each skip when its source is shortest), T(m) has leading
    rate K(m) with coefficient exactly coef(m), the sum over shortest
    paths of the edge products. -/
theorem dag_backward_coeff (sk : ℕ → Finset ℕ)
    (hsk : ∀ m, ∀ m' ∈ sk (m+1), m' ≤ m)
    (K : ℕ → ℕ) (hK0 : K 0 = 0)
    (hKe : ∀ m, sk (m+1) = ∅ → K (m+1) = K m + 1)
    (hKn : ∀ m (h : (sk (m+1)).Nonempty),
      K (m+1) = min (K m + 1) ((sk (m+1)).inf' h K))
    (c : ℕ → ℝ) (T : ℕ → ℝ → ℝ) (hT0 : ∀ t, T 0 t = 1)
    (hTs : ∀ m t, T (m+1) t
      = c (m+1) * t * T m t + ∑ m' ∈ sk (m+1), T m' t)
    (coef : ℕ → ℝ) (hc0 : coef 0 = 1)
    (hcs : ∀ m, coef (m+1)
      = (if K m + 1 = K (m+1) then c (m+1) * coef m else 0)
        + ∑ m' ∈ (sk (m+1)).filter (fun m' => K m' = K (m+1)), coef m') :
    ∀ m, HasLeadingRate (T m) (K m) (coef m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero =>
      rw [hK0, hc0]
      refine (hasLeadingRate_const 1).congr fun t => ?_
      rw [hT0]
    | succ m =>
      have hTm := ih m (Nat.lt_succ_self m)
      have hw : HasLeadingRate (fun t => c (m+1) * t * T m t) (K m + 1)
          (c (m+1) * coef m) := by
        have h1 : HasLeadingRate (fun t => c (m+1) * t) 1 (c (m+1)) := by
          have := (hasLeadingRate_pow 1).const_mul (c (m+1))
          simpa using this
        have h2 := h1.mul hTm
        rw [show 1 + K m = K m + 1 from Nat.add_comm 1 (K m)] at h2
        exact h2
      by_cases hemp : sk (m+1) = ∅
      · rw [hKe m hemp, hcs m, hemp, hKe m hemp, if_pos rfl,
          Finset.filter_empty, Finset.sum_empty, add_zero]
        refine hw.congr fun t => ?_
        rw [hTs, hemp, Finset.sum_empty, add_zero]
      · have hne : (sk (m+1)).Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
        have hS := hasLeadingRate_finset_sum hne (fun m' => T m') K coef
          (fun m' hm' => ih m' (Nat.lt_succ_of_le (hsk m m' hm')))
        have hmin := hw.add_min_coeff hS
        rw [hKn m hne, hcs m, hKn m hne]
        have hfun : (fun t => c (m+1) * t * T m t + ∑ m' ∈ sk (m+1), T m' t)
            = T (m+1) := by
          funext t
          rw [hTs]
        rw [hfun] at hmin
        rcases lt_trichotomy (K m + 1) ((sk (m+1)).inf' hne K) with h | h | h
        · rw [min_eq_left h.le] at hmin ⊢
          rw [if_pos h] at hmin
          have hfilt : (sk (m+1)).filter (fun m' => K m' = K m + 1) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro m' hm' heq
            have := Finset.inf'_le K hm'
            omega
          rw [if_pos rfl, hfilt, Finset.sum_empty, add_zero]
          exact hmin
        · rw [h, min_self] at hmin ⊢
          rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)] at hmin
          rw [if_pos rfl]
          exact hmin
        · rw [min_eq_right h.le] at hmin ⊢
          rw [if_neg (not_lt.mpr h.le), if_pos h] at hmin
          rw [if_neg (ne_of_gt h), zero_add]
          exact hmin

/-- The explicit constant is positive when every weight coefficient
    is: leading coefficients are unique, so the explicit recursion
    returns the positive coefficient of dag_backward_rate. -/
theorem dag_coeff_pos (sk : ℕ → Finset ℕ)
    (hsk : ∀ m, ∀ m' ∈ sk (m+1), m' ≤ m)
    (K : ℕ → ℕ) (hK0 : K 0 = 0)
    (hKe : ∀ m, sk (m+1) = ∅ → K (m+1) = K m + 1)
    (hKn : ∀ m (h : (sk (m+1)).Nonempty),
      K (m+1) = min (K m + 1) ((sk (m+1)).inf' h K))
    (c : ℕ → ℝ) (hc : ∀ m, 0 < c m)
    (T : ℕ → ℝ → ℝ) (hT0 : ∀ t, T 0 t = 1)
    (hTs : ∀ m t, T (m+1) t
      = c (m+1) * t * T m t + ∑ m' ∈ sk (m+1), T m' t)
    (coef : ℕ → ℝ) (hc0 : coef 0 = 1)
    (hcs : ∀ m, coef (m+1)
      = (if K m + 1 = K (m+1) then c (m+1) * coef m else 0)
        + ∑ m' ∈ (sk (m+1)).filter (fun m' => K m' = K (m+1)), coef m')
    (m : ℕ) : 0 < coef m := by
  obtain ⟨a, ha, hTa⟩ := dag_backward_rate sk hsk K hK0 hKe hKn c hc T hT0 hTs m
  have hTc := dag_backward_coeff sk hsk K hK0 hKe hKn c T hT0 hTs coef hc0 hcs m
  have : coef m = a := tendsto_nhds_unique hTc hTa
  rw [this]
  exact ha

/-! ### The finite-t skip-correction clause

Below t = 1 the backward delta is its leading term coef·t^K up to a
remainder one order higher: every longer path through an unused skip
and every weight-edge continuation of a non-shortest parent chain
enters at order t^{K+1} or beyond. The constant is explicit, built
from the parents' constants and coefficients. -/

/-- The Bellman distance grows by at most one per weight edge. -/
lemma dag_K_succ_le (sk : ℕ → Finset ℕ) (K : ℕ → ℕ)
    (hKe : ∀ m, sk (m+1) = ∅ → K (m+1) = K m + 1)
    (hKn : ∀ m (h : (sk (m+1)).Nonempty),
      K (m+1) = min (K m + 1) ((sk (m+1)).inf' h K)) (m : ℕ) :
    K (m+1) ≤ K m + 1 := by
  by_cases hemp : sk (m+1) = ∅
  · rw [hKe m hemp]
  · rw [hKn m (Finset.nonempty_iff_ne_empty.mpr hemp)]
    exact min_le_left _ _

/-- A skip never lands closer than the node it serves. -/
lemma dag_K_le_skip (sk : ℕ → Finset ℕ) (K : ℕ → ℕ)
    (hKn : ∀ m (h : (sk (m+1)).Nonempty),
      K (m+1) = min (K m + 1) ((sk (m+1)).inf' h K)) (m m' : ℕ)
    (hm' : m' ∈ sk (m+1)) : K (m+1) ≤ K m' := by
  rw [hKn m ⟨m', hm'⟩]
  exact le_trans (min_le_right _ _) (Finset.inf'_le K hm')

/-- cor:res_block's finite-t clause on the DAG: for 0 < t ≤ 1 the
    backward delta differs from its leading term coef(m)·t^{K(m)} by
    at most R(m)·t^{K(m)+1}, with R(m) explicit from the parents. -/
theorem dag_backward_remainder (sk : ℕ → Finset ℕ)
    (hsk : ∀ m, ∀ m' ∈ sk (m+1), m' ≤ m)
    (K : ℕ → ℕ) (hK0 : K 0 = 0)
    (hKe : ∀ m, sk (m+1) = ∅ → K (m+1) = K m + 1)
    (hKn : ∀ m (h : (sk (m+1)).Nonempty),
      K (m+1) = min (K m + 1) ((sk (m+1)).inf' h K))
    (c : ℕ → ℝ) (T : ℕ → ℝ → ℝ) (hT0 : ∀ t, T 0 t = 1)
    (hTs : ∀ m t, T (m+1) t
      = c (m+1) * t * T m t + ∑ m' ∈ sk (m+1), T m' t)
    (coef : ℕ → ℝ) (hc0 : coef 0 = 1)
    (hcs : ∀ m, coef (m+1)
      = (if K m + 1 = K (m+1) then c (m+1) * coef m else 0)
        + ∑ m' ∈ (sk (m+1)).filter (fun m' => K m' = K (m+1)), coef m') :
    ∀ m, ∃ R : ℝ, 0 ≤ R ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      |T m t - coef m * t ^ K m| ≤ R * t ^ (K m + 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero =>
      refine ⟨0, le_rfl, fun t _ _ => ?_⟩
      rw [hT0, hc0, hK0, pow_zero, mul_one, sub_self, abs_zero, zero_mul]
    | succ m =>
      obtain ⟨Rm, hRm, hm⟩ := ih m (Nat.lt_succ_self m)
      have hall : ∀ m' ∈ sk (m+1), ∃ R : ℝ, 0 ≤ R ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
          |T m' t - coef m' * t ^ K m'| ≤ R * t ^ (K m' + 1) :=
        fun m' hm' => ih m' (Nat.lt_succ_of_le (hsk m m' hm'))
      choose! Rf hRf hbound using hall
      have hKle := dag_K_succ_le sk K hKe hKn m
      set N := K (m+1) with hN
      refine ⟨|c (m+1)| * Rm + |c (m+1)| * |coef m|
        + ∑ m' ∈ sk (m+1), Rf m' + ∑ m' ∈ sk (m+1), |coef m'|, ?_,
        fun t ht ht1 => ?_⟩
      · have h1 : 0 ≤ ∑ m' ∈ sk (m+1), Rf m' :=
          Finset.sum_nonneg fun m' hm' => hRf m' hm'
        have h2 : 0 ≤ ∑ m' ∈ sk (m+1), |coef m'| :=
          Finset.sum_nonneg fun _ _ => abs_nonneg _
        positivity
      · have htN : 0 < t ^ (N + 1) := pow_pos ht _
        -- the four pieces
        set A := c (m+1) * t * (T m t - coef m * t ^ K m) with hA
        set B := c (m+1) * coef m * t ^ (K m + 1)
          - (if K m + 1 = N then c (m+1) * coef m else 0) * t ^ N with hB
        set C := ∑ m' ∈ sk (m+1), (T m' t - coef m' * t ^ K m') with hC
        set D := ∑ m' ∈ sk (m+1), coef m' * t ^ K m'
          - (∑ m' ∈ (sk (m+1)).filter (fun m' => K m' = N), coef m') * t ^ N
          with hD
        have hsplit : T (m+1) t - coef (m+1) * t ^ N = A + B + C + D := by
          rw [hTs, hcs m, hA, hB, hC, hD, Finset.sum_sub_distrib]
          rw [← hN]
          ring
        rw [hsplit]
        -- piece A
        have hAb : |A| ≤ |c (m+1)| * Rm * t ^ (N + 1) := by
          rw [hA, abs_mul, abs_mul, abs_of_pos ht]
          have h := hm t ht ht1
          have hpow : t ^ (K m + 1) * t ≤ t ^ (N + 1) := by
            rw [← pow_succ]
            exact pow_le_pow_of_le_one ht.le ht1 (by omega)
          calc |c (m+1)| * t * |T m t - coef m * t ^ K m|
              ≤ |c (m+1)| * t * (Rm * t ^ (K m + 1)) := by gcongr
            _ = |c (m+1)| * Rm * (t ^ (K m + 1) * t) := by ring
            _ ≤ |c (m+1)| * Rm * t ^ (N + 1) := by gcongr
        -- piece B
        have hBb : |B| ≤ |c (m+1)| * |coef m| * t ^ (N + 1) := by
          rw [hB]
          by_cases heq : K m + 1 = N
          · rw [if_pos heq, heq, sub_self, abs_zero]
            positivity
          · rw [if_neg heq, zero_mul, sub_zero, abs_mul, abs_mul,
              abs_of_pos (pow_pos ht _)]
            have hle : t ^ (K m + 1) ≤ t ^ (N + 1) :=
              pow_le_pow_of_le_one ht.le ht1 (by omega)
            gcongr
        -- piece C
        have hCb : |C| ≤ (∑ m' ∈ sk (m+1), Rf m') * t ^ (N + 1) := by
          rw [hC, Finset.sum_mul]
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun m' hm' => ?_)
          have h := hbound m' hm' t ht ht1
          have hle : t ^ (K m' + 1) ≤ t ^ (N + 1) :=
            pow_le_pow_of_le_one ht.le ht1
              (Nat.succ_le_succ (dag_K_le_skip sk K hKn m m' hm'))
          calc |T m' t - coef m' * t ^ K m'| ≤ Rf m' * t ^ (K m' + 1) := h
            _ ≤ Rf m' * t ^ (N + 1) :=
                mul_le_mul_of_nonneg_left hle (hRf m' hm')
        -- piece D
        have hDb : |D| ≤ (∑ m' ∈ sk (m+1), |coef m'|) * t ^ (N + 1) := by
          rw [hD]
          have hdecomp : ∑ m' ∈ sk (m+1), coef m' * t ^ K m'
              = (∑ m' ∈ (sk (m+1)).filter (fun m' => K m' = N), coef m') * t ^ N
                + ∑ m' ∈ (sk (m+1)).filter (fun m' => ¬ K m' = N),
                    coef m' * t ^ K m' := by
            rw [← Finset.sum_filter_add_sum_filter_not (sk (m+1))
              (fun m' => K m' = N), Finset.sum_mul]
            congr 1
            refine Finset.sum_congr rfl fun m' hm' => ?_
            rw [(Finset.mem_filter.mp hm').2]
          rw [hdecomp, add_sub_cancel_left]
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          calc ∑ m' ∈ (sk (m+1)).filter (fun m' => ¬ K m' = N), |coef m' * t ^ K m'|
              ≤ ∑ m' ∈ (sk (m+1)).filter (fun m' => ¬ K m' = N),
                  |coef m'| * t ^ (N + 1) := by
                refine Finset.sum_le_sum fun m' hm' => ?_
                obtain ⟨hmem, hne⟩ := Finset.mem_filter.mp hm'
                rw [abs_mul, abs_of_pos (pow_pos ht _)]
                have hge : N + 1 ≤ K m' := by
                  have := dag_K_le_skip sk K hKn m m' hmem
                  omega
                exact mul_le_mul_of_nonneg_left
                  (pow_le_pow_of_le_one ht.le ht1 hge) (abs_nonneg _)
            _ ≤ ∑ m' ∈ sk (m+1), |coef m'| * t ^ (N + 1) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  (fun _ _ _ => by positivity)
            _ = (∑ m' ∈ sk (m+1), |coef m'|) * t ^ (N + 1) := by
                rw [Finset.sum_mul]
        calc |A + B + C + D| ≤ |A| + |B| + |C| + |D| := by
              have h1 := abs_add_le (A + B + C) D
              have h2 := abs_add_le (A + B) C
              have h3 := abs_add_le A B
              linarith
          _ ≤ |c (m+1)| * Rm * t ^ (N + 1) + |c (m+1)| * |coef m| * t ^ (N + 1)
              + (∑ m' ∈ sk (m+1), Rf m') * t ^ (N + 1)
              + (∑ m' ∈ sk (m+1), |coef m'|) * t ^ (N + 1) := by
              linarith [hAb, hBb, hCb, hDb]
          _ = (|c (m+1)| * Rm + |c (m+1)| * |coef m|
              + ∑ m' ∈ sk (m+1), Rf m' + ∑ m' ∈ sk (m+1), |coef m'|) * t ^ (N + 1) := by
              ring

end DeadDirections
