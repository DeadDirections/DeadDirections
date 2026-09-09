/-
  The matrix quotient, deliverable A1 of the standing project
  (proofs/QUOTIENT-PLAN.md): the product map and its fibers.

  The gauge action threads a group element through each interface of
  a layer list: layer W_j becomes g_{j−1} W_j g_j⁻¹ with identity at
  both ends. Two facts constitute A1. The product is invariant: the
  telescoping cancels every interior gauge. And on the invertible
  stratum the fibers of the product map are exactly the gauge
  orbits: two lists of equal length with equal products are
  connected by the interpolating gauge built from partial products.
  Both facts are proved in any group and instantiated to matrices
  through the units embedding, so the group lemma is the reusable
  artifact and the invertible stratum is its image.
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import DeadDirections.FisherDecay
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Group

namespace DeadDirections

section GroupChain

variable {G : Type*} [Group G]

/-- The gauge action from a carried left factor: the head layer
    absorbs the carried gauge on the left and the next interface
    gauge inverse on the right, and the recursion carries that
    interface gauge forward. -/
def gaugeActFrom : G → List G → List G → List G
  | _, _, [] => []
  | g, [], W :: rest => (g * W) :: rest
  | g, h :: gs, W :: rest => (g * W * h⁻¹) :: gaugeActFrom h gs rest

@[simp] lemma gaugeActFrom_nil_right (g : G) (gs : List G) :
    gaugeActFrom g gs [] = [] := by
  cases gs <;> rfl

@[simp] lemma gaugeActFrom_nil_gauges (g : G) (W : G)
    (rest : List G) :
    gaugeActFrom g [] (W :: rest) = (g * W) :: rest := rfl

@[simp] lemma gaugeActFrom_cons (g h : G) (gs : List G) (W : G)
    (rest : List G) :
    gaugeActFrom g (h :: gs) (W :: rest)
      = (g * W * h⁻¹) :: gaugeActFrom h gs rest := rfl

/-- Gauge invariance of the product, with the carried factor: the
    telescoping cancels every interior gauge. -/
theorem prod_gaugeActFrom (g : G) (gs Ws : List G)
    (hlen : gs.length + 1 = Ws.length) :
    (gaugeActFrom g gs Ws).prod = g * Ws.prod := by
  induction Ws generalizing g gs with
  | nil => simp at hlen
  | cons W rest ih =>
    cases rest with
    | nil =>
      have hgs : gs = [] := by
        cases gs with
        | nil => rfl
        | cons _ _ => simp at hlen
      subst hgs
      simp only [gaugeActFrom_nil_gauges, List.prod_cons,
        List.prod_nil, mul_one]
    | cons R rest' =>
      cases gs with
      | nil => simp at hlen
      | cons h gs' =>
        have hlen' : gs'.length + 1 = (R :: rest').length := by
          simpa using hlen
        rw [gaugeActFrom_cons, List.prod_cons, ih h gs' hlen',
          show ((W :: R :: rest') : List G).prod
            = W * (R :: rest').prod from List.prod_cons]
        group

/-- Gauge invariance at trivial carried factor: the interior gauges
    leave the end-to-end product unchanged. -/
theorem prod_gaugeAct (gs Ws : List G)
    (hlen : gs.length + 1 = Ws.length) :
    (gaugeActFrom 1 gs Ws).prod = Ws.prod := by
  rw [prod_gaugeActFrom 1 gs Ws hlen, one_mul]

/-- The fiber characterization, with the carried factor: whenever
    g·(product of Ws) equals the product of Ws', the interpolating
    gauge family connects them. The gauge at interface j is the
    partial-product solution h = W'⁻¹ g W carried forward. -/
theorem exists_gauge_of_prod_eq_from (g : G) (Ws Ws' : List G)
    (hlen : Ws.length = Ws'.length) (hne : Ws ≠ [])
    (hprod : g * Ws.prod = Ws'.prod) :
    ∃ gs : List G, gs.length + 1 = Ws.length
      ∧ gaugeActFrom g gs Ws = Ws' := by
  induction Ws generalizing g Ws' with
  | nil => exact absurd rfl hne
  | cons W rest ih =>
    cases Ws' with
    | nil => simp at hlen
    | cons W' rest' =>
      cases rest with
      | nil =>
        have hrest' : rest' = [] := by
          cases rest' with
          | nil => rfl
          | cons _ _ => simp at hlen
        subst hrest'
        refine ⟨[], by simp, ?_⟩
        simp only [gaugeActFrom_nil_gauges]
        simp only [List.prod_cons, List.prod_nil, mul_one] at hprod
        rw [hprod]
      | cons R rest2 =>
        have hlen2 : (R :: rest2).length = rest'.length := by
          simpa using hlen
        have hne2 : rest' ≠ [] := by
          intro h
          rw [h] at hlen2
          simp at hlen2
        have hprod2 : (W'⁻¹ * g * W) * (R :: rest2).prod
            = rest'.prod := by
          have h1 : g * ((W :: R :: rest2).prod) = (W' :: rest').prod :=
            hprod
          rw [show ((W :: R :: rest2).prod)
              = W * (R :: rest2).prod from List.prod_cons,
            show ((W' :: rest').prod) = W' * rest'.prod from
              List.prod_cons] at h1
          calc (W'⁻¹ * g * W) * (R :: rest2).prod
              = W'⁻¹ * (g * (W * (R :: rest2).prod)) := by group
            _ = W'⁻¹ * (W' * rest'.prod) := by rw [h1]
            _ = rest'.prod := by group
        obtain ⟨gs', hlen', hact⟩ := ih (W'⁻¹ * g * W) rest'
          (by simpa using hlen2) (by simp) hprod2
        refine ⟨(W'⁻¹ * g * W) :: gs', by simpa using hlen', ?_⟩
        rw [gaugeActFrom_cons, hact]
        congr 1
        group

/-- The fibers of the product map are the gauge orbits: two layer
    lists of equal length with equal products are connected by the
    interpolating gauge family. -/
theorem exists_gauge_of_prod_eq (Ws Ws' : List G)
    (hlen : Ws.length = Ws'.length) (hne : Ws ≠ [])
    (hprod : Ws.prod = Ws'.prod) :
    ∃ gs : List G, gs.length + 1 = Ws.length
      ∧ gaugeActFrom 1 gs Ws = Ws' :=
  exists_gauge_of_prod_eq_from 1 Ws Ws' hlen hne
    (by rw [one_mul, hprod])

/-- The units embedding carries list products to list products. -/
lemma units_val_prod {M : Type*} [Monoid M] (l : List Mˣ) :
    (l.map Units.val).prod = ↑l.prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Deliverable A5, the optimizer side: an update that commutes with
    the gauge action has a gauge-independent projected readout. The
    quotient trajectory of an equivariant optimizer is well-defined
    regardless of the lift, at chain level in any group; the flow
    identities of the scalar model transfer to the diagonal slice
    through chainDeriv_map_diagonal. -/
theorem equivariant_update_prod (U : List G → List G)
    (hUlen : ∀ Ws, (U Ws).length = Ws.length)
    (hU : ∀ gs Ws, gs.length + 1 = Ws.length
      → U (gaugeActFrom 1 gs Ws) = gaugeActFrom 1 gs (U Ws))
    (gs Ws : List G) (hlen : gs.length + 1 = Ws.length) :
    (U (gaugeActFrom 1 gs Ws)).prod = (U Ws).prod := by
  rw [hU gs Ws hlen, prod_gaugeAct gs (U Ws)
    (by rw [hUlen Ws]; exact hlen)]


omit [Group G] in
/-- Equivariant updates preserve chain length along the whole
    trajectory. -/
lemma iterate_length_preserved (U : List G → List G)
    (hUlen : ∀ Ws, (U Ws).length = Ws.length) (n : ℕ) (Ws : List G) :
    (U^[n] Ws).length = Ws.length := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', hUlen, ih]

/-- Iterates of an equivariant update are equivariant: the
    trajectory-level composition. -/
theorem equivariant_iterate (U : List G → List G)
    (hUlen : ∀ Ws, (U Ws).length = Ws.length)
    (hU : ∀ gs Ws, gs.length + 1 = Ws.length
      → U (gaugeActFrom 1 gs Ws) = gaugeActFrom 1 gs (U Ws))
    (n : ℕ) (gs Ws : List G) (hlen : gs.length + 1 = Ws.length) :
    U^[n] (gaugeActFrom 1 gs Ws) = gaugeActFrom 1 gs (U^[n] Ws) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih]
    exact hU gs (U^[m] Ws)
      (by rw [iterate_length_preserved U hUlen m Ws]; exact hlen)

/-- The projected trajectory of an equivariant optimizer is
    gauge-independent at every step of the approach: iterating the
    update along a trajectory commutes with projection. -/
theorem equivariant_iterate_prod (U : List G → List G)
    (hUlen : ∀ Ws, (U Ws).length = Ws.length)
    (hU : ∀ gs Ws, gs.length + 1 = Ws.length
      → U (gaugeActFrom 1 gs Ws) = gaugeActFrom 1 gs (U Ws))
    (n : ℕ) (gs Ws : List G) (hlen : gs.length + 1 = Ws.length) :
    (U^[n] (gaugeActFrom 1 gs Ws)).prod = (U^[n] Ws).prod := by
  rw [equivariant_iterate U hUlen hU n gs Ws hlen]
  exact prod_gaugeAct gs (U^[n] Ws)
    (by rw [iterate_length_preserved U hUlen n Ws]; exact hlen)

end GroupChain

section MatrixInstance

variable {h : ℕ}

/-- The end-to-end product of a layer list: the quotient
    coordinate of the matrix chain. -/
def matProdMap (Ws : List (Matrix (Fin h) (Fin h) ℝ)) :
    Matrix (Fin h) (Fin h) ℝ :=
  Ws.prod

/-- Gauge invariance on the invertible stratum, at matrix level:
    interior gauges leave the end-to-end matrix product unchanged. -/
theorem matProdMap_gauge_invariant
    (gs Ws : List (Matrix (Fin h) (Fin h) ℝ)ˣ)
    (hlen : gs.length + 1 = Ws.length) :
    matProdMap ((gaugeActFrom 1 gs Ws).map Units.val)
      = matProdMap (Ws.map Units.val) := by
  unfold matProdMap
  rw [units_val_prod, units_val_prod]
  exact congrArg Units.val (prod_gaugeAct gs Ws hlen)

/-- The fiber characterization on the invertible stratum: two layer
    lists of units with the same end-to-end matrix product are
    gauge-connected. -/
theorem matProdMap_fiber
    (Ws Ws' : List (Matrix (Fin h) (Fin h) ℝ)ˣ)
    (hlen : Ws.length = Ws'.length) (hne : Ws ≠ [])
    (hprod : matProdMap (Ws.map Units.val)
      = matProdMap (Ws'.map Units.val)) :
    ∃ gs : List (Matrix (Fin h) (Fin h) ℝ)ˣ,
      gs.length + 1 = Ws.length ∧ gaugeActFrom 1 gs Ws = Ws' := by
  apply exists_gauge_of_prod_eq Ws Ws' hlen hne
  apply Units.ext
  unfold matProdMap at hprod
  rw [units_val_prod, units_val_prod] at hprod
  exact hprod

end MatrixInstance

section DerivativeAlg

/-! ### Deliverable A2, algebraic half: the chain derivative and the
vertical family

The chain derivative is the product rule's value at the base point:
V₁·W₂⋯W_L + W₁·(recursion). The vertical family threads interface
generators the way gaugeActFrom threads gauges: layer j receives
x_{j−1}·W_j − W_j·x_j with zero at both ends. The pairing telescopes:
the chain derivative of a vertical family is the carried generator
times the product, so at zero carried generator the derivative kills
every vertical family exactly, at every point of the chain. This is
lem:quotient_F's mechanism at matrix level, stated in any ring. -/

variable {M : Type*} [Ring M]

/-- The chain derivative: the value of the product rule on the
    layer list at direction list Vs. -/
def chainDeriv : List M → List M → M
  | [], _ => 0
  | _ :: _, [] => 0
  | W :: Ws, V :: Vs => V * Ws.prod + W * chainDeriv Ws Vs

@[simp] lemma chainDeriv_nil_left (Vs : List M) :
    chainDeriv [] Vs = 0 := rfl

@[simp] lemma chainDeriv_cons (W V : M) (Ws Vs : List M) :
    chainDeriv (W :: Ws) (V :: Vs)
      = V * Ws.prod + W * chainDeriv Ws Vs := rfl

/-- The vertical family from a carried generator: layer j receives
    the carried generator on the left and the next interface
    generator on the right, both as commutator-style terms. -/
def vertFrom : M → List M → List M → List M
  | _, _, [] => []
  | x, [], W :: rest => (x * W) :: vertFrom 0 [] rest
  | x, y :: xs, W :: rest => (x * W - W * y) :: vertFrom y xs rest

@[simp] lemma vertFrom_nil_right (x : M) (xs : List M) :
    vertFrom x xs [] = [] := by
  cases xs <;> rfl

@[simp] lemma vertFrom_nil_gens (x : M) (W : M) (rest : List M) :
    vertFrom x [] (W :: rest) = (x * W) :: vertFrom 0 [] rest := rfl

@[simp] lemma vertFrom_cons (x y : M) (xs : List M) (W : M)
    (rest : List M) :
    vertFrom x (y :: xs) (W :: rest)
      = (x * W - W * y) :: vertFrom y xs rest := rfl

@[simp] lemma vertFrom_length (x : M) (xs Ws : List M) :
    (vertFrom x xs Ws).length = Ws.length := by
  induction Ws generalizing x xs with
  | nil => simp
  | cons W rest ih =>
    cases xs with
    | nil =>
      rw [vertFrom_nil_gens]
      simp [ih]
    | cons y ys =>
      rw [vertFrom_cons]
      simp [ih]

/-- The telescoping pairing: the chain derivative of a vertical
    family is the carried generator times the product. -/
theorem chainDeriv_vertFrom (x : M) (xs Ws : List M)
    (hlen : xs.length + 1 = Ws.length) :
    chainDeriv Ws (vertFrom x xs Ws) = x * Ws.prod := by
  induction Ws generalizing x xs with
  | nil => simp at hlen
  | cons W rest ih =>
    cases rest with
    | nil =>
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons _ _ => simp at hlen
      subst hxs
      simp only [vertFrom_nil_gens, vertFrom_nil_right,
        chainDeriv_cons, chainDeriv_nil_left, List.prod_nil,
        List.prod_cons, mul_one, mul_zero, add_zero]
    | cons R rest2 =>
      cases xs with
      | nil => simp at hlen
      | cons y ys =>
        have hlen' : ys.length + 1 = (R :: rest2).length := by
          simpa using hlen
        rw [vertFrom_cons, chainDeriv_cons, ih y ys hlen',
          show ((W :: R :: rest2) : List M).prod
            = W * (R :: rest2).prod from List.prod_cons]
        rw [sub_mul, mul_assoc W y, sub_add_cancel, mul_assoc]

/-- Vertical annihilation: with zero carried generator the chain
    derivative kills every vertical family exactly, at every point
    of the chain. -/
theorem chainDeriv_vertical (xs Ws : List M)
    (hlen : xs.length + 1 = Ws.length) :
    chainDeriv Ws (vertFrom 0 xs Ws) = 0 := by
  rw [chainDeriv_vertFrom 0 xs Ws hlen, zero_mul]

end DerivativeAlg

section MatrixDerivative

/-! ### Deliverable A2, analytic half: the chain derivative is the
derivative

The perturbed layer list moves every layer along its direction, and
the entrywise derivative of the end-to-end product at t = 0 is
exactly the chain derivative's entry: the product rule composed down
the list, certified. -/

variable {h : ℕ}

/-- The perturbed layer list: every layer moves along its
    direction. -/
noncomputable def pertList (Ws Vs : List (Matrix (Fin h) (Fin h) ℝ))
    (t : ℝ) : List (Matrix (Fin h) (Fin h) ℝ) :=
  (Ws.zip Vs).map (fun p => p.1 + t • p.2)

@[simp] lemma pertList_nil (Vs : List (Matrix (Fin h) (Fin h) ℝ))
    (t : ℝ) : pertList [] Vs t = [] := rfl

@[simp] lemma pertList_cons (W V : Matrix (Fin h) (Fin h) ℝ)
    (Ws Vs : List (Matrix (Fin h) (Fin h) ℝ)) (t : ℝ) :
    pertList (W :: Ws) (V :: Vs) t
      = (W + t • V) :: pertList Ws Vs t := rfl

lemma pertList_zero (Ws Vs : List (Matrix (Fin h) (Fin h) ℝ))
    (hlen : Ws.length ≤ Vs.length) :
    pertList Ws Vs 0 = Ws := by
  unfold pertList
  have hfun : (fun p : Matrix (Fin h) (Fin h) ℝ
        × Matrix (Fin h) (Fin h) ℝ => p.1 + (0:ℝ) • p.2)
      = Prod.fst := by
    funext p
    simp
  rw [hfun]
  exact List.map_fst_zip hlen

/-- The product rule down the list, certified entrywise: the
    derivative of the end-to-end product's entry at t = 0 is the
    chain derivative's entry. -/
theorem hasDerivAt_pertList_prod
    (Ws Vs : List (Matrix (Fin h) (Fin h) ℝ))
    (hlen : Ws.length = Vs.length) (i j : Fin h) :
    HasDerivAt (fun t => (pertList Ws Vs t).prod i j)
      (chainDeriv Ws Vs i j) 0 := by
  induction Ws generalizing Vs i j with
  | nil =>
    simp only [pertList_nil, List.prod_nil, chainDeriv_nil_left,
      Matrix.zero_apply]
    exact hasDerivAt_const 0 _
  | cons W rest ih =>
    cases Vs with
    | nil => simp at hlen
    | cons V Vs' =>
      have hlen' : rest.length = Vs'.length := by simpa using hlen
      have heq : (fun t => (pertList (W :: rest) (V :: Vs') t).prod
            i j)
          = fun t => ∑ k, (W i k + t * V i k)
              * (pertList rest Vs' t).prod k j := by
        funext t
        rw [pertList_cons, List.prod_cons, Matrix.mul_apply]
        exact Finset.sum_congr rfl fun k _ => by
          rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [heq]
      have hterm : ∀ k : Fin h, HasDerivAt
          (fun t => (W i k + t * V i k)
            * (pertList rest Vs' t).prod k j)
          (V i k * rest.prod k j
            + W i k * chainDeriv rest Vs' k j) 0 := by
        intro k
        have h1 : HasDerivAt (fun t : ℝ => W i k + t * V i k)
            (V i k) 0 := by
          simpa using
            ((hasDerivAt_id (0:ℝ)).mul_const (V i k)).const_add
              (W i k)
        have h2 := ih Vs' hlen' k j
        have h := h1.mul h2
        have hzero : (pertList rest Vs' 0).prod = rest.prod := by
          rw [pertList_zero rest Vs' (le_of_eq hlen')]
        rw [hzero] at h
        simpa using h
      have hsum : HasDerivAt
          (fun t => ∑ k, (W i k + t * V i k)
            * (pertList rest Vs' t).prod k j)
          (∑ k, (V i k * rest.prod k j
            + W i k * chainDeriv rest Vs' k j)) 0 :=
        HasDerivAt.fun_sum fun k _ => hterm k
      have hval : ∑ k, (V i k * rest.prod k j
            + W i k * chainDeriv rest Vs' k j)
          = chainDeriv (W :: rest) (V :: Vs') i j := by
        rw [chainDeriv_cons, Matrix.add_apply, Matrix.mul_apply,
          Matrix.mul_apply, ← Finset.sum_add_distrib]
      rw [hval] at hsum
      exact hsum

/-! ### Deliverable A3: the concrete submersion

Surjectivity and the kernel, both exact on the invertible stratum.
The chain derivative is onto: the single-slot direction through the
inverse tail product hits any target. And the kernel is exactly the
vertical space: solving the interface recursion x_j = W_j⁻¹(x_{j−1}
W_j − V_j) from zero gives the closed-form pairing chainDeriv =
x₀·P − P·x_L, so the derivative vanishes precisely when the terminal
generator does, and in that case the direction list is a vertical
family. Together with A2 this is the exact sequence
0 → vertical → directions → M → 0; the plan's orthogonal-complement
reading follows by rank-nullity and enters here only as the
dimension count L·h² = (L−1)·h² + h² in this comment, since the
kernel characterization is metric-free and stronger. -/

section Submersion

variable {M : Type*} [Ring M]

/-- The zero direction list has zero chain derivative. -/
lemma chainDeriv_zero (Ws : List M) :
    chainDeriv Ws (List.replicate Ws.length 0) = 0 := by
  induction Ws with
  | nil => rfl
  | cons W rest ih =>
    rw [List.length_cons, List.replicate_succ, chainDeriv_cons,
      ih, zero_mul, mul_zero, add_zero]

/-- The concrete submersion: on the invertible stratum the chain
    derivative is onto, through the single-slot direction with the
    inverse tail product. -/
theorem chainDeriv_surjective (W : Mˣ) (rest : List Mˣ) (U : M) :
    ∃ Vs : List M, Vs.length = rest.length + 1
      ∧ chainDeriv ((W :: rest).map Units.val) Vs = U := by
  refine ⟨(U * ↑(rest.prod)⁻¹) :: List.replicate rest.length 0,
    by simp, ?_⟩
  rw [List.map_cons, chainDeriv_cons]
  have hzero : chainDeriv (rest.map Units.val)
      (List.replicate rest.length 0) = 0 := by
    have h := chainDeriv_zero (rest.map Units.val)
    rwa [List.length_map] at h
  rw [hzero, mul_zero, add_zero, units_val_prod, mul_assoc]
  rw [show (↑(rest.prod)⁻¹ : M) * ↑rest.prod = 1 from
    Units.inv_mul _]
  rw [mul_one]

/-- The terminal generator of the interface recursion: solving
    x_j = W_j⁻¹(x_{j−1} W_j − V_j) down the chain. -/
def termGen : M → List Mˣ → List M → M
  | x, [], _ => x
  | x, _ :: _, [] => x
  | x, W :: rest, V :: Vs =>
      termGen (↑W⁻¹ * (x * ↑W - V)) rest Vs

@[simp] lemma termGen_nil (x : M) (Vs : List M) :
    termGen x ([] : List Mˣ) Vs = x := by
  cases Vs <;> rfl

@[simp] lemma termGen_cons (x : M) (W : Mˣ) (rest : List Mˣ)
    (V : M) (Vs : List M) :
    termGen x (W :: rest) (V :: Vs)
      = termGen (↑W⁻¹ * (x * ↑W - V)) rest Vs := rfl

/-- The closed-form pairing: the chain derivative equals the carried
    generator against the product minus the product against the
    terminal generator. -/
theorem chainDeriv_eq_termGen (x : M) (Ws : List Mˣ) (Vs : List M)
    (hlen : Ws.length = Vs.length) :
    chainDeriv (Ws.map Units.val) Vs
      = x * (Ws.map Units.val).prod
        - (Ws.map Units.val).prod * termGen x Ws Vs := by
  induction Ws generalizing x Vs with
  | nil =>
    cases Vs with
    | nil => simp
    | cons _ _ => simp at hlen
  | cons W rest ih =>
    cases Vs with
    | nil => simp at hlen
    | cons V Vs' =>
      have hlen' : rest.length = Vs'.length := by simpa using hlen
      rw [List.map_cons, chainDeriv_cons, termGen_cons,
        ih (↑W⁻¹ * (x * ↑W - V)) Vs' hlen',
        show ((↑W :: rest.map Units.val) : List M).prod
          = ↑W * (rest.map Units.val).prod from List.prod_cons]
      have hWx : (↑W : M) * (↑W⁻¹ * (x * ↑W - V)) = x * ↑W - V :=
        Units.mul_inv_cancel_left W _
      rw [mul_sub, ← mul_assoc, hWx]
      noncomm_ring

/-- The kernel criterion: on the invertible stratum the chain
    derivative vanishes exactly when the terminal generator of the
    zero-carried recursion does. -/
theorem chainDeriv_eq_zero_iff (Ws : List Mˣ) (Vs : List M)
    (hlen : Ws.length = Vs.length) :
    chainDeriv (Ws.map Units.val) Vs = 0
      ↔ termGen 0 Ws Vs = 0 := by
  rw [chainDeriv_eq_termGen 0 Ws Vs hlen, zero_mul, zero_sub,
    neg_eq_zero]
  constructor
  · intro h
    have hu := units_val_prod Ws
    rw [hu] at h
    exact (Units.mul_right_eq_zero _).mp h
  · intro h
    rw [h, mul_zero]

/-- The kernel is vertical: a direction list with vanishing terminal
    generator is a vertical family, with the interface generators
    the recursion's own solutions. -/
theorem exists_vert_of_termGen_zero (x : M) (Ws : List Mˣ)
    (Vs : List M) (hlen : Ws.length = Vs.length) (hne : Ws ≠ [])
    (hterm : termGen x Ws Vs = 0) :
    ∃ gs : List M, gs.length + 1 = Ws.length
      ∧ Vs = vertFrom x gs (Ws.map Units.val) := by
  induction Ws generalizing x Vs with
  | nil => exact absurd rfl hne
  | cons W rest ih =>
    cases Vs with
    | nil => simp at hlen
    | cons V Vs' =>
      cases rest with
      | nil =>
        have hVs' : Vs' = [] := by
          cases Vs' with
          | nil => rfl
          | cons _ _ => simp at hlen
        subst hVs'
        refine ⟨[], by simp, ?_⟩
        rw [termGen_cons, termGen_nil] at hterm
        have hV : V = x * ↑W := by
          have h3 : x * ↑W - V = 0 := by
            rwa [Units.mul_right_eq_zero] at hterm
          rwa [sub_eq_zero, eq_comm] at h3
        rw [List.map_cons, List.map_nil, vertFrom_nil_gens, hV]
        rfl
      | cons R rest2 =>
        have hlen' : (R :: rest2).length = Vs'.length := by
          simpa using hlen
        rw [termGen_cons] at hterm
        obtain ⟨gs', hlen2, hact⟩ := ih (↑W⁻¹ * (x * ↑W - V)) Vs'
          hlen' (by simp) hterm
        refine ⟨(↑W⁻¹ * (x * ↑W - V)) :: gs',
          by simpa using hlen2, ?_⟩
        rw [List.map_cons, vertFrom_cons, ← hact]
        congr 1
        rw [Units.mul_inv_cancel_left]
        noncomm_ring

end Submersion

end MatrixDerivative

/-! ### Deliverable A4: the quotient Fisher and its rate

The model quotient Fisher is the Frobenius pairing of the chain
derivative with itself: the pullback of the flat form on the product
space. It vanishes on vertical families by A2. Diagonal layer lists
transport the matrix chain derivative to per-entry scalar chain
derivatives, the canonical approach reads L·t^{L−1} at the dead slot
and zero at every live entry, and the normalised reading carries
leading rate 2(L−1) with coefficient L: the multivariate form of the
scalar quotient_rate_model, cor:quotient_rate at matrix level. -/

section QuotientFisher

variable {n : ℕ}

/-- The model quotient Fisher: the Frobenius pairing of the chain
    derivative with itself. -/
noncomputable def quotFisher
    (Ws Vs : List (Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) : ℝ :=
  ∑ i, ∑ j, (chainDeriv Ws Vs i j) ^ 2

/-- The quotient Fisher vanishes on every vertical family: A2's
    annihilation at quadratic-form level. -/
theorem quotFisher_vertical
    (xs Ws : List (Matrix (Fin (n+1)) (Fin (n+1)) ℝ))
    (hlen : xs.length + 1 = Ws.length) :
    quotFisher Ws (vertFrom 0 xs Ws) = 0 := by
  unfold quotFisher
  rw [chainDeriv_vertical xs Ws hlen]
  simp

/-- Products of diagonal lists are diagonal, entrywise. -/
lemma prod_map_diagonal (ds : List (Fin (n+1) → ℝ)) :
    (ds.map Matrix.diagonal).prod
      = Matrix.diagonal (fun i => (ds.map (fun d => d i)).prod) := by
  induction ds with
  | nil =>
    simp [Matrix.diagonal_one]
  | cons d ds ih =>
    rw [List.map_cons, List.prod_cons, ih,
      Matrix.diagonal_mul_diagonal]
    congr 1

/-- The chain derivative of diagonal lists is diagonal, with the
    scalar chain derivative at every entry. -/
lemma chainDeriv_map_diagonal (ds es : List (Fin (n+1) → ℝ)) :
    chainDeriv (ds.map Matrix.diagonal) (es.map Matrix.diagonal)
      = Matrix.diagonal (fun i =>
          chainDeriv (ds.map (fun d => d i))
            (es.map (fun e => e i))) := by
  induction ds generalizing es with
  | nil =>
    cases es <;> simp [Matrix.diagonal_zero]
  | cons d ds ih =>
    cases es with
    | nil =>
      exact Matrix.diagonal_zero.symm
    | cons e es' =>
      rw [List.map_cons, List.map_cons, chainDeriv_cons, ih,
        prod_map_diagonal, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
      congr 1

/-- The scalar canonical chain derivative: L equal layers t with
    unit directions read L·t^{L−1}. -/
lemma chainDeriv_replicate_scalar (L : ℕ) (t : ℝ) :
    chainDeriv (List.replicate L t) (List.replicate L (1:ℝ))
      = L * t ^ (L - 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.replicate_succ, List.replicate_succ, chainDeriv_cons,
      List.prod_replicate, ih]
    cases L with
    | zero => simp
    | succ L' =>
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

/-- The canonical diagonal layer list: L layers of diag(1, …, 1, t). -/
noncomputable def canonDiag (L : ℕ) (t : ℝ) :
    List (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :=
  (List.replicate L
    (fun i => if i = Fin.last n then t else 1)).map Matrix.diagonal

/-- The dead-slot direction list: the symmetric perturbation at the
    dead diagonal entry of every layer. -/
noncomputable def deadDir (L : ℕ) :
    List (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :=
  (List.replicate L
    (fun i => if i = Fin.last n then (1:ℝ) else 0)).map
      Matrix.diagonal

/-- The Frobenius square of a diagonal matrix is the sum of squared
    entries. -/
lemma frobSq_diagonal (f : Fin (n+1) → ℝ) :
    ∑ i, ∑ j, (Matrix.diagonal f i j) ^ 2 = ∑ i, (f i) ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro j _ hji
    rw [Matrix.diagonal_apply_ne' _ hji]
    ring
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- cor:quotient_rate at matrix level: the normalised quotient
    Fisher reading of the dead-slot direction along the canonical
    approach has leading rate 2(L−1) with coefficient L. -/
theorem quotient_rate_matrix (L : ℕ) (hL : 1 ≤ L) :
    HasLeadingRate
      (fun t => quotFisher (canonDiag (n := n) L t) (deadDir L) / L)
      (2 * (L - 1)) L := by
  have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have heq : ∀ t : ℝ,
      quotFisher (canonDiag (n := n) L t) (deadDir L) / L
      = (L : ℝ) * t ^ (2 * (L - 1)) := by
    intro t
    unfold quotFisher canonDiag deadDir
    rw [chainDeriv_map_diagonal, frobSq_diagonal]
    have hentry : ∀ i : Fin (n+1),
        chainDeriv
          ((List.replicate L
            (fun k => if k = Fin.last n then t else 1)).map
              (fun d => d i))
          ((List.replicate L
            (fun k => if k = Fin.last n then (1:ℝ) else 0)).map
              (fun e => e i))
        = if i = Fin.last n then (L : ℝ) * t ^ (L - 1) else 0 := by
      intro i
      rw [List.map_replicate, List.map_replicate]
      by_cases hi : i = Fin.last n
      · rw [if_pos hi]
        simp only [if_pos hi]
        exact chainDeriv_replicate_scalar L t
      · rw [if_neg hi]
        simp only [if_neg hi]
        have h := chainDeriv_zero (List.replicate L (1:ℝ))
        rwa [List.length_replicate] at h
    rw [Finset.sum_congr rfl fun i _ => by rw [hentry i]]
    have hsq : ∀ i : Fin (n+1),
        ((if i = Fin.last n then (L : ℝ) * t ^ (L - 1) else 0)) ^ 2
        = if i = Fin.last n then ((L : ℝ) * t ^ (L - 1)) ^ 2
          else 0 := fun i => by
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun i _ => hsq i]
    rw [Finset.sum_ite_eq' Finset.univ (Fin.last n)
      (fun _ => ((L : ℝ) * t ^ (L - 1)) ^ 2)]
    simp only [Finset.mem_univ, if_pos]
    have hexp : ((L : ℝ) * t ^ (L - 1)) ^ 2
        = (L : ℝ) ^ 2 * t ^ (2 * (L - 1)) := by
      rw [mul_pow, ← pow_mul]
      congr 2
      omega
    rw [hexp, div_eq_iff hLne]
    ring
  have h := (hasLeadingRate_pow (2 * (L - 1))).const_mul (L : ℝ)
  have h2 : HasLeadingRate (fun t => (L : ℝ) * t ^ (2 * (L - 1)))
      (2 * (L - 1)) L := by simpa using h
  refine h2.congr fun t => ?_
  simp only [heq]

end QuotientFisher

/-! ### The balanced flow in general position

The deep-linear flow identities, at every configuration. Layer
gradients of a loss that factors through the end-to-end product have
the form G_W = AᵀḠ(W'S)ᵀ and G_{W'} = (AW)ᵀḠSᵀ for consecutive
layers with shared prefix A and suffix S. The transport identity
WᵀG_W = G_{W'}W'ᵀ is pure algebra and needs no balance and no
invertibility: general position in the strongest sense. It forces
the conservation law: along Euclidean gradient flow the balance
defect W'W'ᵀ − WᵀW has derivative zero, certified entrywise. The
fractional-power closed form of the end-to-end dynamics on the
balanced manifold needs matrix root calculus and stays with the
paper and Track B. -/

section BalancedFlow

open Matrix

variable {n : ℕ}

/-- The layer gradient at W: the prefix and the tail of the chain
    sandwich the end-to-end gradient. -/
noncomputable def layerGradFst (A W' S Gbar :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Aᵀ * Gbar * (W' * S)ᵀ

/-- The layer gradient at W': the extended prefix and the suffix
    sandwich the end-to-end gradient. -/
noncomputable def layerGradSnd (A W S Gbar :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  (A * W)ᵀ * Gbar * Sᵀ

/-- The transport identity, at every configuration: the layer-paired
    gradients agree across the interface. No balance and no
    invertibility enter. -/
theorem balance_transport (A W W' S Gbar :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Wᵀ * layerGradFst A W' S Gbar
      = layerGradSnd A W S Gbar * W'ᵀ := by
  unfold layerGradFst layerGradSnd
  rw [Matrix.transpose_mul, Matrix.transpose_mul]
  noncomm_ring

/-- The Gram-derivative equality: the two consecutive layers' Gram
    flows match, so the balance defect is conserved. From the
    transport identity and its transpose. -/
theorem balance_gram_derivative_eq (A W W' S Gbar :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Wᵀ * layerGradFst A W' S Gbar + (layerGradFst A W' S Gbar)ᵀ * W
      = layerGradSnd A W S Gbar * W'ᵀ
        + W' * (layerGradSnd A W S Gbar)ᵀ := by
  have h := balance_transport A W W' S Gbar
  have ht := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_transpose] at ht
  rw [h, ht]

/-- The conservation law, certified: along the Euclidean gradient
    flow directions the balance defect W'W'ᵀ − WᵀW has derivative
    zero at every entry, at every configuration. -/
theorem balance_defect_hasDerivAt (A W W' S Gbar :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (i j : Fin (n+1)) :
    HasDerivAt (fun t : ℝ =>
      ((W' + t • (-(layerGradSnd A W S Gbar)))
          * (W' + t • (-(layerGradSnd A W S Gbar)))ᵀ
        - (W + t • (-(layerGradFst A W' S Gbar)))ᵀ
          * (W + t • (-(layerGradFst A W' S Gbar)))) i j)
      0 0 := by
  set GW := layerGradFst A W' S Gbar with hGW
  set GW' := layerGradSnd A W S Gbar with hGW'
  have hentry : ∀ (X V Y U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ),
      HasDerivAt (fun t : ℝ =>
        ((X + t • V) * (Y + t • U)) i j)
        ((V * Y + X * U) i j) 0 := by
    intro X V Y U
    have heq : (fun t : ℝ => ((X + t • V) * (Y + t • U)) i j)
        = fun t : ℝ => ∑ k, (X i k + t * V i k)
            * (Y k j + t * U k j) := by
      funext t
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply,
          Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [heq]
    have hterm : ∀ k : Fin (n+1), HasDerivAt
        (fun t : ℝ => (X i k + t * V i k) * (Y k j + t * U k j))
        (V i k * Y k j + X i k * U k j) 0 := by
      intro k
      have h1 : HasDerivAt (fun t : ℝ => X i k + t * V i k)
          (V i k) 0 := by
        simpa using
          ((hasDerivAt_id (0:ℝ)).mul_const (V i k)).const_add (X i k)
      have h2 : HasDerivAt (fun t : ℝ => Y k j + t * U k j)
          (U k j) 0 := by
        simpa using
          ((hasDerivAt_id (0:ℝ)).mul_const (U k j)).const_add (Y k j)
      have h := h1.mul h2
      simpa using h
    have hsum : HasDerivAt
        (fun t : ℝ => ∑ k, (X i k + t * V i k) * (Y k j + t * U k j))
        (∑ k, (V i k * Y k j + X i k * U k j)) 0 :=
      HasDerivAt.fun_sum fun k _ => hterm k
    have hval : ∑ k, (V i k * Y k j + X i k * U k j)
        = (V * Y + X * U) i j := by
      rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
        ← Finset.sum_add_distrib]
    rwa [hval] at hsum
  have htr : ∀ t : ℝ, (W + t • (-GW))ᵀ
      = Wᵀ + t • (-GW)ᵀ := fun t => by
    rw [Matrix.transpose_add, Matrix.transpose_smul]
  have htr' : ∀ t : ℝ, (W' + t • (-GW'))ᵀ
      = W'ᵀ + t • (-GW')ᵀ := fun t => by
    rw [Matrix.transpose_add, Matrix.transpose_smul]
  have h1 := hentry W' (-GW') W'ᵀ (-GW')ᵀ
  have h2 := hentry Wᵀ (-GW)ᵀ W (-GW)
  have hcomb := h1.sub h2
  have heqf : (fun t : ℝ =>
      ((W' + t • (-GW')) * (W' + t • (-GW'))ᵀ
        - (W + t • (-GW))ᵀ * (W + t • (-GW))) i j)
      = fun t : ℝ =>
        ((W' + t • (-GW')) * (W'ᵀ + t • (-GW')ᵀ)) i j
        - ((Wᵀ + t • (-GW)ᵀ) * (W + t • (-GW))) i j := by
    funext t
    rw [Matrix.sub_apply, htr' t, htr t]
  rw [heqf]
  have hzero : ((-GW') * W'ᵀ + W' * (-GW')ᵀ) i j
      - ((-GW)ᵀ * W + Wᵀ * (-GW)) i j = 0 := by
    have h := balance_gram_derivative_eq A W W' S Gbar
    have hij := congrArg (fun X => X i j) h
    simp only [Matrix.add_apply] at hij
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.neg_apply,
      Matrix.transpose_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at hij
    simp only [neg_mul, mul_neg, Finset.sum_neg_distrib]
    linarith [hij]
  rw [hzero] at hcomb
  exact hcomb

/-- Real matrices: the conjugate transpose is the transpose. -/
lemma conjTranspose_eq_transpose_bal {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Aᴴ = Aᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply]

/-- The balanced closed form at L = 2, constructively: under the
    balance condition the end-to-end flow closes in P and the two
    Gram factors, and the Gram factors are the square roots of PPᵀ
    and PᵀP: they square to them and they are positive
    semidefinite. The flow identity itself needs no roots; the
    roots enter only as the names of the Gram factors, and Mathlib
    has no real-matrix square root yet, so the abstract sqrt
    packaging waits with the upstream material. -/
theorem balanced_flow_closed_L2 {n : ℕ}
    (W₁ W₂ Gbar : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hbal : W₂ * W₂ᵀ = W₁ᵀ * W₁) :
    ((-(Gbar * (W₂ * 1)ᵀ)) * W₂ + W₁ * (-((1 * W₁)ᵀ * Gbar * 1ᵀ))
        = -(Gbar * (W₂ᵀ * W₂) + (W₁ * W₁ᵀ) * Gbar))
    ∧ ((W₁ * W₁ᵀ) * (W₁ * W₁ᵀ) = (W₁ * W₂) * (W₁ * W₂)ᵀ)
    ∧ ((W₂ᵀ * W₂) * (W₂ᵀ * W₂) = (W₁ * W₂)ᵀ * (W₁ * W₂))
    ∧ (W₁ * W₁ᵀ).PosSemidef ∧ (W₂ᵀ * W₂).PosSemidef := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_one]
    noncomm_ring
  · rw [Matrix.transpose_mul]
    calc (W₁ * W₁ᵀ) * (W₁ * W₁ᵀ)
        = W₁ * (W₁ᵀ * W₁) * W₁ᵀ := by noncomm_ring
      _ = W₁ * (W₂ * W₂ᵀ) * W₁ᵀ := by rw [hbal]
      _ = W₁ * W₂ * (W₂ᵀ * W₁ᵀ) := by noncomm_ring
  · rw [Matrix.transpose_mul]
    calc (W₂ᵀ * W₂) * (W₂ᵀ * W₂)
        = W₂ᵀ * (W₂ * W₂ᵀ) * W₂ := by noncomm_ring
      _ = W₂ᵀ * (W₁ᵀ * W₁) * W₂ := by rw [hbal]
      _ = W₂ᵀ * W₁ᵀ * (W₁ * W₂) := by noncomm_ring
  · have h := Matrix.posSemidef_self_mul_conjTranspose W₁
    rwa [conjTranspose_eq_transpose_bal] at h
  · have h := Matrix.posSemidef_conjTranspose_mul_self W₂
    rwa [conjTranspose_eq_transpose_bal] at h

end BalancedFlow

/-! ### Deliverable B4 at the model: the quotient metric

The Riemannian-submersion content the model supports exactly. The
chain derivative is additive in the direction, so the quotient form
does not see vertical translates of a lift: the pushforward of the
Frobenius form is well-defined on the quotient. And the constant
slice through the base realizes it: the slice lift of a base
direction has chain derivative exactly that direction, so the
quotient form pulled through the slice is the flat Frobenius form on
the base, with the rate along the canonical approach given by A4.
The O'Neill machinery in abstract generality stays upstream with
B3's slice theorem. -/

section QuotientMetric

section AddLinear

variable {M : Type*} [Ring M]

/-- The chain derivative is additive in the direction list. -/
lemma chainDeriv_add (Ws Vs Vs' : List M)
    (hlen : Ws.length = Vs.length)
    (hlen' : Ws.length = Vs'.length) :
    chainDeriv Ws (List.zipWith (· + ·) Vs Vs')
      = chainDeriv Ws Vs + chainDeriv Ws Vs' := by
  induction Ws generalizing Vs Vs' with
  | nil => simp
  | cons W rest ih =>
    cases Vs with
    | nil => simp at hlen
    | cons V Vs2 =>
      cases Vs' with
      | nil => simp at hlen'
      | cons V' Vs2' =>
        rw [List.zipWith_cons_cons, chainDeriv_cons, chainDeriv_cons,
          chainDeriv_cons,
          ih Vs2 Vs2' (by simpa using hlen) (by simpa using hlen')]
        noncomm_ring

end AddLinear

variable {n : ℕ}

/-- The quotient form does not see vertical translates: the
    pushforward of the Frobenius form is well-defined on lifts. -/
theorem quotFisher_vert_translate
    (Ws Vs : List (Matrix (Fin (n+1)) (Fin (n+1)) ℝ))
    (xs : List (Matrix (Fin (n+1)) (Fin (n+1)) ℝ))
    (hlen : Ws.length = Vs.length)
    (hxs : xs.length + 1 = Ws.length) :
    quotFisher Ws
      (List.zipWith (· + ·) Vs (vertFrom 0 xs Ws))
      = quotFisher Ws Vs := by
  unfold quotFisher
  rw [chainDeriv_add Ws Vs (vertFrom 0 xs Ws) hlen (by
    rw [vertFrom_length]),
    chainDeriv_vertical xs Ws hxs, add_zero]

/-- The constant slice through the base. -/
noncomputable def sliceList (k : ℕ)
    (P : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    List (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :=
  List.replicate k 1 ++ [P]

/-- The slice lift of a base direction: zero on the constant
    layers, the direction in the base slot. -/
noncomputable def sliceLift (k : ℕ)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    List (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :=
  List.replicate k 0 ++ [U]

/-- The slice lift's chain derivative is the base direction
    exactly. -/
lemma chainDeriv_sliceLift (k : ℕ)
    (P U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    chainDeriv (sliceList k P) (sliceLift k U) = U := by
  induction k with
  | zero =>
    show chainDeriv [P] [U] = U
    rw [chainDeriv_cons]
    simp
  | succ k ih =>
    show chainDeriv (1 :: (List.replicate k 1 ++ [P]))
      (0 :: (List.replicate k 0 ++ [U])) = U
    rw [chainDeriv_cons, zero_mul, one_mul, zero_add]
    exact ih

/-- The slice isometry: the quotient form pulled through the slice
    is the flat Frobenius form on the base. -/
theorem slice_isometric (k : ℕ)
    (P U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    quotFisher (sliceList k P) (sliceLift k U)
      = ∑ i, ∑ j, (U i j) ^ 2 := by
  unfold quotFisher
  rw [chainDeriv_sliceLift]

end QuotientMetric

end DeadDirections
