/-
  Track B, deliverable B2, first arc: the gauge action as a group
  action.

  Mathlib already carries the separation half of B2: the orbit space
  of any proper action is T2 (t2Space_quotient_mulAction_of_properSMul,
  an instance), and topological groups act properly on themselves.
  What the quotient program owes is the action itself: the interface
  gauges form the pointwise product group, they act on layer tuples
  by g_{j−1} W_j g_j⁻¹ with identity at both ends, and the action is
  free on the invertible stratum, the interface recursion forcing
  every gauge to the identity. Properness of the gauge action and
  the equivariant trivialization of the stratum are the next arcs;
  with them the upstream instance hands back the Hausdorff orbit
  space.
-/
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Order.Fin.Basic
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Homeomorph.Defs
import DeadDirections.MatrixQuotient

namespace DeadDirections

open Topology

section GaugeAction

variable {M : Type*} [Monoid M] {L : ℕ}

/-- The gauge on the left interface of entry j: identity at the
    boundary. -/
def prevG (g : Fin L → Mˣ) (j : Fin (L+1)) : Mˣ :=
  if h : j = 0 then 1 else g (j.pred h)

/-- The gauge on the right interface of entry j: identity at the
    boundary. -/
def nextG (g : Fin L → Mˣ) (j : Fin (L+1)) : Mˣ :=
  if h : j = Fin.last L then 1 else g (j.castPred h)

/-- The interface gauge action on layer tuples. -/
def gaugeSMul (g : Fin L → Mˣ) (W : Fin (L+1) → M) :
    Fin (L+1) → M :=
  fun j => ↑(prevG g j) * W j * ↑(nextG g j)⁻¹

lemma prevG_one (j : Fin (L+1)) :
    prevG (1 : Fin L → Mˣ) j = 1 := by
  unfold prevG
  split <;> rfl

lemma nextG_one (j : Fin (L+1)) :
    nextG (1 : Fin L → Mˣ) j = 1 := by
  unfold nextG
  split <;> rfl

lemma prevG_mul (a b : Fin L → Mˣ) (j : Fin (L+1)) :
    prevG (a * b) j = prevG a j * prevG b j := by
  unfold prevG
  split <;> simp

lemma nextG_mul (a b : Fin L → Mˣ) (j : Fin (L+1)) :
    nextG (a * b) j = nextG a j * nextG b j := by
  unfold nextG
  split <;> simp

/-- The gauge group acts on layer tuples through the interfaces. -/
instance : MulAction (Fin L → Mˣ) (Fin (L+1) → M) where
  smul := gaugeSMul
  one_smul W := by
    funext j
    show ↑(prevG (1 : Fin L → Mˣ) j) * W j
        * ↑(nextG (1 : Fin L → Mˣ) j)⁻¹ = W j
    rw [prevG_one, nextG_one]
    simp
  mul_smul a b W := by
    funext j
    show ↑(prevG (a * b) j) * W j * ↑(nextG (a * b) j)⁻¹
      = ↑(prevG a j) * (↑(prevG b j) * W j * ↑(nextG b j)⁻¹)
        * ↑(nextG a j)⁻¹
    rw [prevG_mul, nextG_mul, mul_inv_rev]
    push_cast
    simp only [mul_assoc]

lemma gaugeSMul_def (g : Fin L → Mˣ) (W : Fin (L+1) → M)
    (j : Fin (L+1)) :
    (g • W) j = ↑(prevG g j) * W j * ↑(nextG g j)⁻¹ := rfl

/-- The interface recursion behind freeness: on an invertible tuple,
    a fixing gauge satisfies the conjugation recursion, so equality
    at one interface propagates to the next. -/
lemma gauge_fix_step {g : Fin L → Mˣ} {Wu : Fin (L+1) → Mˣ}
    (hfix : g • (fun i => (↑(Wu i) : M)) = fun i => ↑(Wu i))
    (j : Fin (L+1)) :
    prevG g j * Wu j * (nextG g j)⁻¹ = Wu j := by
  have h := congrFun hfix j
  rw [gaugeSMul_def] at h
  exact Units.ext (by simpa using h)

/-- The cancellation step: a conjugation-fixing relation with
    identity left gauge forces the right gauge to the identity. -/
lemma gauge_forced {G : Type*} [Group G] {a u v : G}
    (h : u * a * v⁻¹ = a) (hu : u = 1) : v = 1 := by
  rw [hu, one_mul] at h
  have h2 : a * v⁻¹ = a * 1 := by rw [mul_one]; exact h
  have h3 := mul_left_cancel h2
  rwa [inv_eq_one] at h3

/-- Freeness on the invertible stratum: a gauge fixing an invertible
    tuple is the identity, every interface forced in turn by the
    conjugation recursion. -/
theorem gaugeSMul_free {g : Fin L → Mˣ} {Wu : Fin (L+1) → Mˣ}
    (hfix : g • (fun i => (↑(Wu i) : M)) = fun i => ↑(Wu i)) :
    g = 1 := by
  cases L with
  | zero =>
    funext i
    exact i.elim0
  | succ L' =>
    funext i
    show g i = 1
    induction i using Fin.induction with
    | zero =>
      have h := gauge_fix_step hfix 0
      have hprev : prevG g (0 : Fin (L'+2)) = 1 := by
        unfold prevG
        rw [dif_pos rfl]
      have hnext : nextG g (0 : Fin (L'+2)) = g 0 := by
        unfold nextG
        rw [dif_neg (Fin.last_pos).ne]
        congr 1
      rw [hprev, hnext] at h
      exact gauge_forced h rfl
    | succ i ih =>
      have h := gauge_fix_step hfix i.succ.castSucc
      have hne0 : (i.succ.castSucc : Fin (L'+2)) ≠ 0 := by
        simp [Fin.ext_iff]
      have hnelast : (i.succ.castSucc : Fin (L'+2))
          ≠ Fin.last (L'+1) := by
        intro hcon
        have h2 := congrArg Fin.val hcon
        simp only [Fin.val_last] at h2
        have h3 : (i : ℕ) + 1 = L' + 1 := by simpa using h2
        have h4 := i.isLt
        omega
      have hprev : prevG g i.succ.castSucc = g i.castSucc := by
        unfold prevG
        rw [dif_neg hne0]
        congr 1
      have hnext : nextG g i.succ.castSucc = g i.succ := by
        unfold nextG
        rw [dif_neg hnelast]
        congr 1
      rw [hprev, hnext] at h
      exact gauge_forced h ih

/-! ### The trivialization, equivariance half

The partial products of a layer tuple are the interpolating gauges
of A1, and they trivialize the action: under a gauge h the k-th
partial product moves by right multiplication with the interface
gauge inverse, and the total product does not move at all. So the
stratum carries the structure of gauge-group times invariant, which
is what properness will consume: the action is conjugate to
right-translation on the gauge factor. The explicit inverse (the
tuple reconstructed from its partial products) is the next arc. -/

section Trivialization

variable {M : Type*} [Monoid M] {L : ℕ}

/-- The gauge action at unit level: the same interface formula,
    valued in units. -/
def uAct (g : Fin L → Mˣ) (Wu : Fin (L+1) → Mˣ) :
    Fin (L+1) → Mˣ :=
  fun j => prevG g j * Wu j * (nextG g j)⁻¹

/-- The unit-level action lifts the tuple action through the
    embedding. -/
lemma uAct_coe (g : Fin L → Mˣ) (Wu : Fin (L+1) → Mˣ) :
    (fun i => (↑(uAct g Wu i) : M)) = g • (fun i => (↑(Wu i) : M)) := by
  funext j
  rw [gaugeSMul_def]
  unfold uAct
  push_cast
  rfl

/-- The k-th partial product: the interpolating gauge of A1. -/
def partialU (Wu : Fin (L+1) → Mˣ) (k : ℕ) : Mˣ :=
  ((List.ofFn Wu).take (k+1)).prod

lemma partialU_zero (Wu : Fin (L+1) → Mˣ) :
    partialU Wu 0 = Wu 0 := by
  unfold partialU
  rw [List.prod_take_succ _ _ (by simp)]
  simp

lemma partialU_succ (Wu : Fin (L+1) → Mˣ) (k : ℕ)
    (hk : k + 1 < L + 1) :
    partialU Wu (k+1) = partialU Wu k * Wu ⟨k+1, hk⟩ := by
  unfold partialU
  rw [List.prod_take_succ _ _ (by simpa using hk)]
  congr 1
  simp

/-- The total product is the last partial product. -/
lemma partialU_last (Wu : Fin (L+1) → Mˣ) :
    partialU Wu L = (List.ofFn Wu).prod := by
  unfold partialU
  rw [List.take_of_length_le (by simp)]

/-- The interface identity: the right gauge of entry k is the left
    gauge of entry k+1, away from the boundary. -/
lemma nextG_eq_prevG_succ (g : Fin L → Mˣ) (k : ℕ) (hk : k < L) :
    nextG g ⟨k, by omega⟩ = prevG g ⟨k+1, by omega⟩ := by
  unfold nextG prevG
  rw [dif_neg (by
    intro hcon
    have h2 := congrArg Fin.val hcon
    simp only [Fin.val_last] at h2
    omega)]
  rw [dif_neg (by
    intro hcon
    have h2 := congrArg Fin.val hcon
    simp at h2)]
  congr 1

/-- Equivariance of the partial products: under a gauge the k-th
    partial product moves by right multiplication with the interface
    gauge inverse. -/
theorem partialU_uAct (g : Fin L → Mˣ) (Wu : Fin (L+1) → Mˣ) :
    ∀ k (hk : k < L + 1),
      partialU (uAct g Wu) k
        = partialU Wu k * (nextG g ⟨k, hk⟩)⁻¹ := by
  intro k
  induction k with
  | zero =>
    intro hk
    rw [partialU_zero, partialU_zero]
    show prevG g 0 * Wu 0 * (nextG g 0)⁻¹ = _
    have hprev : prevG g (0 : Fin (L+1)) = 1 := by
      unfold prevG
      rw [dif_pos rfl]
    rw [hprev, one_mul]
    rfl
  | succ k ih =>
    intro hk
    have hk' : k < L + 1 := by omega
    have hkL : k < L := by omega
    rw [partialU_succ _ k hk, partialU_succ _ k hk, ih hk']
    show partialU Wu k * (nextG g ⟨k, hk'⟩)⁻¹
        * (prevG g ⟨k+1, hk⟩ * Wu ⟨k+1, hk⟩
          * (nextG g ⟨k+1, hk⟩)⁻¹) = _
    rw [nextG_eq_prevG_succ g k hkL]
    group

/-- The total product is gauge invariant: the complete invariant of
    the orbit. -/
theorem total_uAct (g : Fin L → Mˣ) (Wu : Fin (L+1) → Mˣ) :
    (List.ofFn (uAct g Wu)).prod = (List.ofFn Wu).prod := by
  rw [← partialU_last, ← partialU_last,
    partialU_uAct g Wu L (by omega)]
  have hlast : nextG g (⟨L, by omega⟩ : Fin (L+1)) = 1 := by
    unfold nextG
    rw [dif_pos (by apply Fin.ext; simp)]
  rw [hlast]
  simp

/-- The right-interface data of the reconstruction: the next partial
    product, with the total at the boundary. -/
def nextP (g : Fin L → Mˣ) (P : Mˣ) (j : Fin (L+1)) : Mˣ :=
  if h : j = Fin.last L then P else g (j.castPred h)

/-- The reconstruction: the tuple whose partial products are the
    given gauges with the given total. Uniform across the boundary,
    including the single-layer case. -/
def trivInv (g : Fin L → Mˣ) (P : Mˣ) : Fin (L+1) → Mˣ :=
  fun j => (prevG g j)⁻¹ * nextP g P j

/-- Reconstruction from partial products: trivInv inverts the
    partial-product map on the left. -/
theorem trivInv_partialU (Wu : Fin (L+1) → Mˣ) :
    trivInv (fun j : Fin L => partialU Wu j.val)
      ((List.ofFn Wu).prod) = Wu := by
  funext j
  unfold trivInv prevG nextP
  beta_reduce
  by_cases h0 : j = 0
  · subst h0
    rw [dif_pos rfl]
    by_cases hL : (0 : Fin (L+1)) = Fin.last L
    · rw [dif_pos hL]
      have hL0 : L = 0 := by
        have h2 : (0:ℕ) = L := by
          simpa using congrArg Fin.val hL
        omega
      subst hL0
      rw [← partialU_last, partialU_zero]
      simp
    · rw [dif_neg hL]
      have hval : ((0 : Fin (L+1)).castPred hL).val = 0 := by
        simp
      rw [hval, partialU_zero]
      simp
  · rw [dif_neg h0]
    have hpos : 1 ≤ j.val := by
      rcases Nat.eq_zero_or_pos j.val with h | h
      · exact absurd (Fin.ext h) h0
      · exact h
    have hpred : (j.pred h0).val = j.val - 1 := by simp
    have hkey : partialU Wu j.val
        = partialU Wu (j.val - 1) * Wu j := by
      have hj : j.val - 1 + 1 = j.val := by omega
      have hlt : j.val - 1 + 1 < L + 1 := by
        have := j.isLt
        omega
      have h := partialU_succ Wu (j.val - 1) hlt
      rw [show (⟨j.val - 1 + 1, hlt⟩ : Fin (L+1)) = j from
        Fin.ext (by omega)] at h
      rw [← hj]
      exact h
    by_cases hL : j = Fin.last L
    · rw [dif_pos hL]
      have hvL : j.val = L := by
        have h2 := congrArg Fin.val hL
        simpa using h2
      rw [hvL] at hkey
      rw [hpred, ← partialU_last, hvL, hkey]
      exact inv_mul_cancel_left _ _
    · rw [dif_neg hL]
      have hval : (j.castPred hL).val = j.val := by simp
      rw [hpred, hval, hkey]
      exact inv_mul_cancel_left _ _

/-- The reconstructed tuple has the given partial products: trivInv
    inverts on the right, gauge component. -/
theorem partialU_trivInv (g : Fin L → Mˣ) (P : Mˣ) :
    ∀ k (hk : k < L), partialU (trivInv g P) k = g ⟨k, hk⟩ := by
  intro k
  induction k with
  | zero =>
    intro hk
    rw [partialU_zero]
    unfold trivInv prevG nextP
    rw [dif_pos rfl]
    rw [dif_neg (by
      intro hcon
      have h2 := congrArg Fin.val hcon
      simp only [Fin.val_zero, Fin.val_last] at h2
      omega)]
    simp only [inv_one, one_mul]
    congr 1
  | succ k ih =>
    intro hk
    have hk' : k < L := by omega
    have hlt : k + 1 < L + 1 := by omega
    rw [partialU_succ _ k hlt, ih hk']
    unfold trivInv prevG nextP
    rw [dif_neg (by
      intro hcon
      have h2 := congrArg Fin.val hcon
      simp at h2)]
    rw [dif_neg (by
      intro hcon
      have h2 := congrArg Fin.val hcon
      simp only [Fin.val_last] at h2
      omega)]
    have hpredv : ((⟨k+1, hlt⟩ : Fin (L+1)).pred (by
        intro hcon
        have h2 := congrArg Fin.val hcon
        simp at h2)) = ⟨k, by omega⟩ := by
      apply Fin.ext
      simp
    have hcastv : ((⟨k+1, hlt⟩ : Fin (L+1)).castPred (by
        intro hcon
        have h2 := congrArg Fin.val hcon
        simp only [Fin.val_last] at h2
        omega)) = ⟨k+1, by omega⟩ := by
      apply Fin.ext
      simp
    rw [hpredv, hcastv]
    rw [show (⟨k, by omega⟩ : Fin L) = ⟨k, hk'⟩ from rfl]
    exact mul_inv_cancel_left _ _

/-- The reconstructed tuple has the given total: trivInv inverts on
    the right, invariant component. -/
theorem total_trivInv (g : Fin L → Mˣ) (P : Mˣ) :
    (List.ofFn (trivInv g P)).prod = P := by
  rw [← partialU_last]
  cases L with
  | zero =>
    rw [partialU_zero]
    unfold trivInv prevG nextP
    rw [dif_pos rfl, dif_pos (by apply Fin.ext; simp)]
    simp
  | succ L' =>
    have hlt : L' + 1 < L' + 1 + 1 := by omega
    rw [partialU_succ _ L' hlt, partialU_trivInv g P L' (by omega)]
    unfold trivInv prevG nextP
    rw [dif_neg (by
      intro hcon
      have h2 := congrArg Fin.val hcon
      simp at h2)]
    rw [dif_pos (by apply Fin.ext; simp)]
    have hpredv : ((⟨L'+1, hlt⟩ : Fin (L'+2)).pred (by
        intro hcon
        have h2 := congrArg Fin.val hcon
        simp at h2)) = ⟨L', by omega⟩ := by
      apply Fin.ext
      simp
    rw [hpredv]
    exact mul_inv_cancel_left _ _

/-- The bundle equivalence: layer tuples of units correspond to
    gauge families with a total, through partial products and the
    reconstruction. The stratum is globally trivial. -/
noncomputable def trivEquiv :
    (Fin (L+1) → Mˣ) ≃ (Fin L → Mˣ) × Mˣ where
  toFun Wu := (fun j => partialU Wu j.val, (List.ofFn Wu).prod)
  invFun p := trivInv p.1 p.2
  left_inv Wu := trivInv_partialU Wu
  right_inv p := by
    ext j
    · exact congrArg Units.val
        (partialU_trivInv p.1 p.2 j.val j.isLt)
    · exact congrArg Units.val (total_trivInv p.1 p.2)

end Trivialization

/-! ### The trivialization is a homeomorphism

The units of a topological monoid carry the topology induced by the
two-sided embedding, and the pin has no ContinuousMul instance for
them, so the two continuity workhorses (products and inverses of
continuous unit-valued maps) are proved here through
Units.continuous_iff and belong upstream. On top of them the partial
products are continuous by their recursion, the reconstruction is
continuous entrywise, and the bundle equivalence upgrades to a
homeomorphism: the stratum is topologically the gauge families
times the total. -/

section Continuity

variable {M : Type*} [Monoid M] [TopologicalSpace M]
  [ContinuousMul M] {X : Type*} [TopologicalSpace X] {L : ℕ}

/-- Products of continuous unit-valued maps are continuous: the
    missing mul-continuity of the units topology. -/
lemma continuous_units_mul {f g : X → Mˣ} (hf : Continuous f)
    (hg : Continuous g) : Continuous (fun x => f x * g x) := by
  rw [Units.continuous_iff]
  constructor
  · exact ((Units.continuous_val.comp hf).mul
      (Units.continuous_val.comp hg))
  · show Continuous fun x => (↑(f x * g x)⁻¹ : M)
    have heq : (fun x => (↑(f x * g x)⁻¹ : M))
        = fun x => (↑(g x)⁻¹ : M) * (↑(f x)⁻¹ : M) := by
      funext x
      rw [mul_inv_rev]
      push_cast
      rfl
    rw [heq]
    exact ((Units.continuous_coe_inv.comp hg).mul
      (Units.continuous_coe_inv.comp hf))

omit [ContinuousMul M] in
/-- Inverses of continuous unit-valued maps are continuous. -/
lemma continuous_units_inv {f : X → Mˣ} (hf : Continuous f) :
    Continuous (fun x => (f x)⁻¹) := by
  rw [Units.continuous_iff]
  constructor
  · exact Units.continuous_coe_inv.comp hf
  · show Continuous fun x => (↑(f x)⁻¹⁻¹ : M)
    have heq : (fun x => (↑(f x)⁻¹⁻¹ : M)) = fun x => (↑(f x) : M) := by
      funext x
      rw [inv_inv]
    rw [heq]
    exact Units.continuous_val.comp hf

/-- The partial products are continuous in the tuple. -/
lemma continuous_partialU (k : ℕ) (hk : k < L + 1) :
    Continuous (fun Wu : Fin (L+1) → Mˣ => partialU Wu k) := by
  induction k with
  | zero =>
    have heq : (fun Wu : Fin (L+1) → Mˣ => partialU Wu 0)
        = fun Wu => Wu 0 := funext fun Wu => partialU_zero Wu
    rw [heq]
    exact continuous_apply 0
  | succ k ih =>
    have hk' : k < L + 1 := by omega
    have heq : (fun Wu : Fin (L+1) → Mˣ => partialU Wu (k+1))
        = fun Wu => partialU Wu k * Wu ⟨k+1, hk⟩ :=
      funext fun Wu => partialU_succ Wu k hk
    rw [heq]
    exact continuous_units_mul (ih hk') (continuous_apply _)

/-- The forward trivialization is continuous. -/
lemma continuous_trivEquiv :
    Continuous (trivEquiv (M := M) (L := L)) := by
  apply Continuous.prodMk
  · exact continuous_pi fun j =>
      continuous_partialU j.val (by have := j.isLt; omega)
  · have heq : (fun Wu : Fin (L+1) → Mˣ => (List.ofFn Wu).prod)
        = fun Wu => partialU Wu L :=
      funext fun Wu => (partialU_last Wu).symm
    show Continuous fun Wu : Fin (L+1) → Mˣ => (List.ofFn Wu).prod
    rw [heq]
    exact continuous_partialU L (by omega)

/-- The reconstruction is continuous. -/
lemma continuous_trivInv :
    Continuous (fun p : (Fin L → Mˣ) × Mˣ =>
      trivInv p.1 p.2) := by
  apply continuous_pi
  intro j
  show Continuous fun p : (Fin L → Mˣ) × Mˣ =>
    (prevG p.1 j)⁻¹ * nextP p.1 p.2 j
  have hprev : Continuous
      (fun p : (Fin L → Mˣ) × Mˣ => prevG p.1 j) := by
    unfold prevG
    by_cases h0 : j = 0
    · simp only [dif_pos h0]
      exact continuous_const
    · simp only [dif_neg h0]
      exact (continuous_apply _).comp continuous_fst
  have hnext : Continuous
      (fun p : (Fin L → Mˣ) × Mˣ => nextP p.1 p.2 j) := by
    unfold nextP
    by_cases hL : j = Fin.last L
    · simp only [dif_pos hL]
      exact continuous_snd
    · simp only [dif_neg hL]
      exact (continuous_apply _).comp continuous_fst
  exact continuous_units_mul (continuous_units_inv hprev) hnext

/-- The bundle trivialization as a homeomorphism: the stratum is
    topologically the gauge families times the total. -/
noncomputable def trivHomeo :
    (Fin (L+1) → Mˣ) ≃ₜ (Fin L → Mˣ) × Mˣ where
  toEquiv := trivEquiv
  continuous_toFun := continuous_trivEquiv
  continuous_invFun := continuous_trivInv

omit [TopologicalSpace M] [ContinuousMul M] in
/-- The conjugation statement: through the trivialization the gauge
    action is right translation on the gauge factor with the total
    untouched. -/
theorem trivEquiv_uAct (g : Fin L → Mˣ) (Wu : Fin (L+1) → Mˣ) :
    trivEquiv (uAct g Wu)
      = ((fun j => (trivEquiv Wu).1 j * (nextG g (Fin.castSucc j))⁻¹),
        (trivEquiv Wu).2) := by
  unfold trivEquiv
  simp only [Equiv.coe_fn_mk]
  refine Prod.ext ?_ ?_
  · funext j
    show partialU (uAct g Wu) j.val = _
    rw [partialU_uAct g Wu j.val (by have := j.isLt; omega)]
    rfl
  · exact total_uAct g Wu

end Continuity

/-! ### Properness and the Hausdorff orbit space

The final B2 arc, by the shortest route: the action-pair map
(g, W) ↦ (g • W, W) is a closed embedding directly. The gauge
retraction recovers g continuously from the pair through the partial
products, giving a continuous left inverse; the range is exactly the
equal-total set, closed whenever the base is Hausdorff, because the
total product is a complete orbit invariant in both directions.
Closed embeddings are proper, so the action is proper, and Mathlib's
own instance then makes the orbit space Hausdorff: the quotient of
the invertible stratum by the gauge group is a Hausdorff space,
machine-checked end to end. -/

section UnitAction

variable {M : Type*} [Monoid M] {L : ℕ}

/-- The unit-level gauge action as a group action. -/
instance : MulAction (Fin L → Mˣ) (Fin (L+1) → Mˣ) where
  smul := uAct
  one_smul Wu := by
    funext j
    show prevG (1 : Fin L → Mˣ) j * Wu j
        * (nextG (1 : Fin L → Mˣ) j)⁻¹ = Wu j
    rw [prevG_one, nextG_one]
    simp
  mul_smul a b Wu := by
    funext j
    show prevG (a * b) j * Wu j * (nextG (a * b) j)⁻¹
      = prevG a j * (prevG b j * Wu j * (nextG b j)⁻¹)
        * (nextG a j)⁻¹
    rw [prevG_mul, nextG_mul, mul_inv_rev]
    simp only [mul_assoc]

lemma uSMul_def (g : Fin L → Mˣ) (Wu : Fin (L+1) → Mˣ) :
    g • Wu = uAct g Wu := rfl

lemma nextG_castSucc (g : Fin L → Mˣ) (j : Fin L) :
    nextG g (Fin.castSucc j) = g j := by
  unfold nextG
  rw [dif_neg (by
    intro hcon
    have h2 := congrArg Fin.val hcon
    simp only [Fin.val_castSucc, Fin.val_last] at h2
    have := j.isLt
    omega)]
  congr 1

/-- The clean conjugation: through the trivialization the action is
    pointwise right translation by the inverse gauge on the gauge
    factor, with the total untouched. -/
theorem trivEquiv_smul (g : Fin L → Mˣ) (Wu : Fin (L+1) → Mˣ) :
    trivEquiv (g • Wu)
      = ((trivEquiv Wu).1 * g⁻¹, (trivEquiv Wu).2) := by
  rw [uSMul_def, trivEquiv_uAct]
  refine Prod.ext ?_ rfl
  funext j
  show (trivEquiv Wu).1 j * (nextG g (Fin.castSucc j))⁻¹ = _
  rw [nextG_castSucc]
  rfl

/-- The gauge retraction: the connecting gauge of a pair, from the
    partial products. -/
def gaugeOf (W' W : Fin (L+1) → Mˣ) : Fin L → Mˣ :=
  fun j => (partialU W' j.val)⁻¹ * partialU W j.val

/-- The retraction recovers the acting gauge. -/
lemma gaugeOf_smul (g : Fin L → Mˣ) (Wu : Fin (L+1) → Mˣ) :
    gaugeOf (g • Wu) Wu = g := by
  funext j
  unfold gaugeOf
  have h := congrFun (congrArg Prod.fst (trivEquiv_smul g Wu)) j
  have hval : partialU (g • Wu) j.val
      = partialU Wu j.val * (g j)⁻¹ := h
  rw [hval]
  group

/-- Orbits are the fibers of the total product, in both
    directions. -/
theorem exists_smul_eq_iff_total_eq (W' W : Fin (L+1) → Mˣ) :
    (∃ g : Fin L → Mˣ, g • W = W')
      ↔ (List.ofFn W').prod = (List.ofFn W).prod := by
  constructor
  · rintro ⟨g, rfl⟩
    exact total_uAct g W
  · intro htot
    refine ⟨gaugeOf W' W, ?_⟩
    apply trivEquiv.injective
    rw [trivEquiv_smul]
    refine Prod.ext ?_ ?_
    · funext j
      show partialU W j.val * ((gaugeOf W' W)⁻¹) j
          = partialU W' j.val
      show partialU W j.val
          * ((partialU W' j.val)⁻¹ * partialU W j.val)⁻¹
          = partialU W' j.val
      group
    · exact htot.symm

end UnitAction

section Properness

variable {M : Type*} [Monoid M] [TopologicalSpace M]
  [ContinuousMul M] {L : ℕ}

lemma continuous_gaugeOf : Continuous
    (fun p : (Fin (L+1) → Mˣ) × (Fin (L+1) → Mˣ) =>
      gaugeOf p.1 p.2) :=
  continuous_pi fun j =>
    continuous_units_mul
      (continuous_units_inv
        ((continuous_partialU j.val (by have := j.isLt; omega)).comp
          continuous_fst))
      ((continuous_partialU j.val (by have := j.isLt; omega)).comp
        continuous_snd)

/-- The action-pair map is a closed embedding: the retraction gives
    the continuous left inverse, and the range is the equal-total
    set. -/
theorem isClosedEmbedding_smul_pair [T2Space M] :
    IsClosedEmbedding
      (fun p : (Fin L → Mˣ) × (Fin (L+1) → Mˣ) =>
        (p.1 • p.2, p.2)) := by
  have hconts : Continuous
      (fun p : (Fin L → Mˣ) × (Fin (L+1) → Mˣ) =>
        (p.1 • p.2, p.2)) := by
    apply Continuous.prodMk _ continuous_snd
    apply continuous_pi
    intro j
    show Continuous fun p : (Fin L → Mˣ) × (Fin (L+1) → Mˣ) =>
      prevG p.1 j * p.2 j * (nextG p.1 j)⁻¹
    have hprev : Continuous
        (fun p : (Fin L → Mˣ) × (Fin (L+1) → Mˣ) =>
          prevG p.1 j) := by
      unfold prevG
      by_cases h0 : j = 0
      · simp only [dif_pos h0]
        exact continuous_const
      · simp only [dif_neg h0]
        exact (continuous_apply _).comp continuous_fst
    have hnext : Continuous
        (fun p : (Fin L → Mˣ) × (Fin (L+1) → Mˣ) =>
          nextG p.1 j) := by
      unfold nextG
      by_cases hL : j = Fin.last L
      · simp only [dif_pos hL]
        exact continuous_const
      · simp only [dif_neg hL]
        exact (continuous_apply _).comp continuous_fst
    exact continuous_units_mul
      (continuous_units_mul hprev
        ((continuous_apply j).comp continuous_snd))
      (continuous_units_inv hnext)
  have hretr : Continuous
      (fun q : (Fin (L+1) → Mˣ) × (Fin (L+1) → Mˣ) =>
        (gaugeOf q.1 q.2, q.2)) :=
    continuous_gaugeOf.prodMk continuous_snd
  have hleft : ∀ p : (Fin L → Mˣ) × (Fin (L+1) → Mˣ),
      (fun q : (Fin (L+1) → Mˣ) × (Fin (L+1) → Mˣ) =>
        (gaugeOf q.1 q.2, q.2)) ((p.1 • p.2, p.2)) = p := by
    intro p
    simp only [gaugeOf_smul]
  have hinj : Function.Injective
      (fun p : (Fin L → Mˣ) × (Fin (L+1) → Mˣ) =>
        (p.1 • p.2, p.2)) := by
    intro p p' hpp
    have h2 := congrArg (fun q :
        (Fin (L+1) → Mˣ) × (Fin (L+1) → Mˣ) =>
        (gaugeOf q.1 q.2, q.2)) hpp
    rwa [hleft p, hleft p'] at h2
  have hind : IsInducing
      (fun p : (Fin L → Mˣ) × (Fin (L+1) → Mˣ) =>
        (p.1 • p.2, p.2)) := by
    apply IsInducing.of_comp hconts hretr
    have hcomp : ((fun q : (Fin (L+1) → Mˣ) × (Fin (L+1) → Mˣ) =>
        (gaugeOf q.1 q.2, q.2))
          ∘ (fun p : (Fin L → Mˣ) × (Fin (L+1) → Mˣ) =>
            (p.1 • p.2, p.2))) = id := funext hleft
    rw [hcomp]
    exact IsInducing.id
  have hrange : Set.range
      (fun p : (Fin L → Mˣ) × (Fin (L+1) → Mˣ) =>
        (p.1 • p.2, p.2))
      = {q : (Fin (L+1) → Mˣ) × (Fin (L+1) → Mˣ) |
          (List.ofFn q.1).prod = (List.ofFn q.2).prod} := by
    ext q
    constructor
    · rintro ⟨p, rfl⟩
      exact total_uAct p.1 p.2
    · intro hq
      obtain ⟨g, hg⟩ :=
        (exists_smul_eq_iff_total_eq q.1 q.2).mpr hq
      exact ⟨(g, q.2), by rw [Prod.mk.injEq]; exact ⟨hg, rfl⟩⟩
  refine ⟨⟨hind, hinj⟩, ?_⟩
  rw [hrange]
  have htotc : Continuous
      (fun Wu : Fin (L+1) → Mˣ => (List.ofFn Wu).prod) := by
    have heq : (fun Wu : Fin (L+1) → Mˣ => (List.ofFn Wu).prod)
        = fun Wu => partialU Wu L :=
      funext fun Wu => (partialU_last Wu).symm
    rw [heq]
    exact continuous_partialU L (by omega)
  exact isClosed_eq (htotc.comp continuous_fst)
    (htotc.comp continuous_snd)

/-- The gauge action on the invertible stratum is proper. -/
theorem properSMul_stratum [T2Space M] :
    ProperSMul (Fin L → Mˣ) (Fin (L+1) → Mˣ) :=
  ⟨(isClosedEmbedding_smul_pair).isProperMap⟩

/-- The capstone: the orbit space of the invertible stratum by the
    gauge group is Hausdorff, machine-checked end to end. -/
theorem t2Space_orbitSpace [T2Space M] :
    T2Space (Quotient
      (MulAction.orbitRel (Fin L → Mˣ) (Fin (L+1) → Mˣ))) := by
  have := properSMul_stratum (M := M) (L := L)
  infer_instance

end Properness

/-! ### Deliverable B3 at the family: the orbit space identified

The quotient manifold theorem's conclusion, concretely: the orbit
space of the invertible stratum by the gauge group is homeomorphic
to the units themselves, through the descended total product. The
constant-tuple slice P ↦ (1, …, 1, P) is a global section: it meets
every orbit exactly once, its composite with the orbit map inverts
the descended total, and both directions are continuous, the
forward one because quotient lifts of continuous invariants are
continuous and the backward one because the slice is. For this
family the global trivialization doubles as a global slice, so the
abstract slice theorem's content at the concrete instance is this
identification. -/

section OrbitIdentification

variable {M : Type*} [Monoid M] [TopologicalSpace M]
  [ContinuousMul M] {L : ℕ}

/-- The global slice: the constant tuple with the total in the last
    slot. -/
def sliceTuple (P : Mˣ) : Fin (L+1) → Mˣ := trivInv 1 P

omit [TopologicalSpace M] [ContinuousMul M] in
lemma total_sliceTuple (P : Mˣ) :
    (List.ofFn (sliceTuple (L := L) P)).prod = P :=
  total_trivInv 1 P

lemma continuous_sliceTuple :
    Continuous (fun P : Mˣ => sliceTuple (L := L) P) := by
  have h := continuous_trivInv (M := M) (L := L)
  exact h.comp (continuous_const.prodMk continuous_id)

omit [TopologicalSpace M] [ContinuousMul M] in
/-- The slice meets every orbit exactly once: two slice points on
    one orbit are equal. -/
theorem sliceTuple_orbit_unique {P P' : Mˣ}
    (h : ∃ g : Fin L → Mˣ,
      g • sliceTuple (L := L) P = sliceTuple (L := L) P') :
    P = P' := by
  have htot := (exists_smul_eq_iff_total_eq _ _).mp h
  rw [total_sliceTuple, total_sliceTuple] at htot
  exact htot.symm

/-- B3's conclusion at the family: the orbit space of the invertible
    stratum by the gauge group is homeomorphic to the units, through
    the descended total product with the slice as inverse. -/
noncomputable def orbitSpaceHomeo :
    Quotient (MulAction.orbitRel (Fin L → Mˣ) (Fin (L+1) → Mˣ))
      ≃ₜ Mˣ where
  toFun := Quotient.lift (fun Wu => (List.ofFn Wu).prod)
    (by
      intro Wu Wu' hrel
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hrel
      rw [← hg]
      exact total_uAct g Wu')
  invFun P := Quotient.mk _ (sliceTuple P)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h Wu =>
      apply Quotient.sound
      show sliceTuple ((List.ofFn Wu).prod)
        ∈ MulAction.orbit (Fin L → Mˣ) Wu
      exact MulAction.mem_orbit_iff.mpr
        ((exists_smul_eq_iff_total_eq _ _).mpr (total_sliceTuple _))
  right_inv P := by
    show (List.ofFn (sliceTuple P)).prod = P
    exact total_sliceTuple P
  continuous_toFun := by
    apply Continuous.quotient_lift
    have heq : (fun Wu : Fin (L+1) → Mˣ => (List.ofFn Wu).prod)
        = fun Wu => partialU Wu L :=
      funext fun Wu => (partialU_last Wu).symm
    rw [heq]
    exact continuous_partialU L (by omega)
  continuous_invFun :=
    continuous_quotient_mk'.comp continuous_sliceTuple

end OrbitIdentification

end GaugeAction

end DeadDirections
