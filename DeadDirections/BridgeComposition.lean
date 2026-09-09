/-
  Composition additivity (theory paper, thm:bridge_composition, part (a)).

  Formal model of the scalar-linear-jointly-gated transfer hypothesis:
  each block multiplies the dead-direction component by c_i·t^{k_i}·g,
  with c_i a deterministic constant and g one shared indicator gate
  (the joint-gate clause: for the covered chains every gate is the
  single survival event, or identically 1). Under this hypothesis the
  composed second moment is exactly

    (∏ c_i)² · t^{2 Σ k_i} · E[g·X²],

  so the backward rate of a chain is the sum of the per-block rates.
  The clauses of the hypothesis appear as exactly the algebra used:
  the deterministic constant enters as c², so its sign never matters
  (no cross-block destructive interference); the shared gate enters
  through idempotence g·g = g (disjoint gates fall outside the model,
  matching the theorem's exclusion); linearity in the dead component
  is the model itself (a polynomial transfer of degree ≥ 2, the SwiGLU
  case, is not expressible as a block here). The forward direction is
  the same statement read with X the input signal.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import DeadDirections.FisherDecay
import DeadDirections.DeepLinearBridge

namespace DeadDirections

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Composed dead-direction signal through a chain of gated scalar
    blocks: block (c, k) multiplies by c·t^k·g. -/
def composedSignal (bs : List (ℝ × ℕ)) (g X : Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  match bs with
  | [] => X
  | (c, k) :: bs' => fun ω => c * t^k * g ω * composedSignal bs' g X t ω

/-- Total transfer coefficient ∏ c_i of a chain. -/
def chainCoeff (bs : List (ℝ × ℕ)) : ℝ := (bs.map Prod.fst).prod

/-- Total rate Σ k_i of a chain. -/
def chainRate (bs : List (ℝ × ℕ)) : ℕ := (bs.map Prod.snd).sum

/-- Rates add under chain concatenation: the additivity reading. -/
lemma chainRate_append (bs bs' : List (ℝ × ℕ)) :
    chainRate (bs ++ bs') = chainRate bs + chainRate bs' := by
  simp [chainRate]

/-- Coefficients multiply under chain concatenation. -/
lemma chainCoeff_append (bs bs' : List (ℝ × ℕ)) :
    chainCoeff (bs ++ bs') = chainCoeff bs * chainCoeff bs' := by
  simp [chainCoeff]

omit [MeasurableSpace Ω] in
/-- Pointwise collapse of a nonempty chain: the shared idempotent gate
    survives exactly once. -/
lemma composedSignal_eq (g X : Ω → ℝ) (hg : ∀ ω, g ω = 0 ∨ g ω = 1)
    (t : ℝ) {bs : List (ℝ × ℕ)} (hbs : bs ≠ []) (ω : Ω) :
    composedSignal bs g X t ω
      = chainCoeff bs * t ^ chainRate bs * (g ω * X ω) := by
  induction bs with
  | nil => exact absurd rfl hbs
  | cons b bs' ih =>
    obtain ⟨c, k⟩ := b
    rcases eq_or_ne bs' [] with h' | h'
    · subst h'
      simp only [composedSignal, chainCoeff, chainRate, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, List.sum_cons,
        List.sum_nil, mul_one, add_zero]
      ring
    · have hgg : g ω * g ω = g ω := by
        rcases hg ω with h | h <;> rw [h] <;> ring
      simp only [composedSignal, ih h']
      rw [show c * t^k * g ω
            * (chainCoeff bs' * t ^ chainRate bs' * (g ω * X ω))
          = (c * chainCoeff bs') * (t^k * t ^ chainRate bs')
            * ((g ω * g ω) * X ω) from by ring,
        hgg, ← pow_add]
      simp only [chainCoeff, chainRate, List.map_cons, List.prod_cons,
        List.sum_cons]

/-- thm:bridge_composition (a) in the gated-scalar model: the composed
    second moment is exactly (∏c)²·t^{2Σk}·E[g·X²]. The rate of the
    chain is the sum of the per-block rates. -/
theorem composedSignal_sq_integral (g X : Ω → ℝ)
    (hg : ∀ ω, g ω = 0 ∨ g ω = 1)
    {bs : List (ℝ × ℕ)} (hbs : bs ≠ []) (t : ℝ) :
    ∫ ω, composedSignal bs g X t ω ^ 2 ∂μ
      = chainCoeff bs ^ 2 * t ^ (2 * chainRate bs)
        * ∫ ω, g ω * X ω ^ 2 ∂μ := by
  have hfun : ∀ ω, composedSignal bs g X t ω ^ 2
      = (chainCoeff bs ^ 2 * t ^ (2 * chainRate bs)) * (g ω * X ω ^ 2) := by
    intro ω
    rw [composedSignal_eq g X hg t hbs ω]
    have hgg : g ω * g ω = g ω := by
      rcases hg ω with h | h <;> rw [h] <;> ring
    have hpow : t ^ (2 * chainRate bs) = (t ^ chainRate bs) ^ 2 := by
      rw [mul_comm, pow_mul]
    rw [hpow]
    calc (chainCoeff bs * t ^ chainRate bs * (g ω * X ω)) ^ 2
        = chainCoeff bs ^ 2 * (t ^ chainRate bs) ^ 2
          * ((g ω * g ω) * X ω ^ 2) := by ring
      _ = chainCoeff bs ^ 2 * (t ^ chainRate bs) ^ 2
          * (g ω * X ω ^ 2) := by rw [hgg]
  simp only [hfun]
  rw [integral_const_mul]

/-- The chain realises the leading rate 2·Σk_i with coefficient
    (∏c)²·E[g·X²], connecting to the abstract fisher_decay layers. -/
theorem composedSignal_hasLeadingRate (g X : Ω → ℝ)
    (hg : ∀ ω, g ω = 0 ∨ g ω = 1) {bs : List (ℝ × ℕ)} (hbs : bs ≠ []) :
    HasLeadingRate (fun t => ∫ ω, composedSignal bs g X t ω ^ 2 ∂μ)
      (2 * chainRate bs)
      (chainCoeff bs ^ 2 * ∫ ω, g ω * X ω ^ 2 ∂μ) := by
  have h : Tendsto
      (fun _ : ℝ => chainCoeff bs ^ 2 * ∫ ω, g ω * X ω ^ 2 ∂μ)
      (𝓝[>] (0:ℝ))
      (𝓝 (chainCoeff bs ^ 2 * ∫ ω, g ω * X ω ^ 2 ∂μ)) :=
    tendsto_const_nhds
  refine h.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  rw [composedSignal_sq_integral g X hg hbs t]
  have htp : t ^ (2 * chainRate bs) ≠ 0 :=
    ne_of_gt (pow_pos ht _)
  field_simp

/-! ### Composition corollaries

Evaluations of the chain model at the block types the paper composes.
Unit-rate matmuls recover the thm:bridge ladder (cor:composition_reduces,
cor:composition_reduces_sub); rate-0 residual blocks leave the moment
t-free at every t, the exact form of rate 0; a block chain equals its
flattened weight chain (the graph-distance reading); uniform rate-2
blocks give the α = 4(L − ℓ) profile of cor:composition_heterogeneous
and cor:g10_composition; and one extra Linear shifts the moment rate by
exactly 2, the α_{W_V} − α_{W_O} = 2 invariant of
prop:attn_VO_invariant. -/

section CompositionCorollaries

lemma chainRate_replicate (n : ℕ) (c : ℝ) (k : ℕ) :
    chainRate (List.replicate n (c, k)) = n * k := by
  simp [chainRate, List.map_replicate, List.sum_replicate, smul_eq_mul]

lemma chainCoeff_replicate (n : ℕ) (c : ℝ) (k : ℕ) :
    chainCoeff (List.replicate n (c, k)) = c ^ n := by
  simp [chainCoeff, List.map_replicate, List.prod_replicate]

lemma replicate_ne_nil {α : Type*} (n : ℕ) (hn : 1 ≤ n) (a : α) :
    List.replicate n a ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this
  omega

/-- cor:composition_reduces / cor:composition_reduces_sub, matmul
    case: n unit-rate blocks read moment rate 2n, the thm:bridge
    ladder at n = L − ℓ. -/
theorem composition_matmul_hasLeadingRate (g X : Ω → ℝ)
    (hg : ∀ ω, g ω = 0 ∨ g ω = 1) (c : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    HasLeadingRate
      (fun t => ∫ ω, composedSignal (List.replicate n (c, 1)) g X t ω ^ 2
        ∂μ)
      (2 * n) (c ^ (2 * n) * ∫ ω, g ω * X ω ^ 2 ∂μ) := by
  have h := composedSignal_hasLeadingRate (μ := μ) g X hg
    (bs := List.replicate n (c, 1)) (replicate_ne_nil n hn _)
  rw [chainRate_replicate, chainCoeff_replicate, Nat.mul_one,
    show (c ^ n) ^ 2 = c ^ (2 * n) from by
      rw [← pow_mul, Nat.mul_comm]] at h
  exact h

/-- cor:composition_reduces, residual case: rate-0 blocks leave the
    composed moment t-free, the same value at every t. Rate 0 in its
    exact form. -/
theorem composition_residual_const (g X : Ω → ℝ)
    (hg : ∀ ω, g ω = 0 ∨ g ω = 1) (c : ℝ) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ∫ ω, composedSignal (List.replicate n (c, 0)) g X t ω ^ 2 ∂μ
      = c ^ (2 * n) * ∫ ω, g ω * X ω ^ 2 ∂μ := by
  rw [composedSignal_sq_integral g X hg (replicate_ne_nil n hn _) t,
    chainRate_replicate, chainCoeff_replicate]
  rw [Nat.mul_zero, Nat.mul_zero, pow_zero, ← pow_mul, Nat.mul_comm n 2]
  ring

/-- The flattened weight chain of one block: its coefficient on one
    unit-rate matmul, then unit matmuls for the rest of its rate. -/
def flattenBlock : ℝ × ℕ → List (ℝ × ℕ) :=
  fun b => (b.1, 1) :: List.replicate (b.2 - 1) ((1 : ℝ), 1)

lemma chainRate_flattenBlock (b : ℝ × ℕ) (hb : 1 ≤ b.2) :
    chainRate (flattenBlock b) = b.2 := by
  unfold flattenBlock
  simp [chainRate, List.map_replicate, List.sum_replicate, smul_eq_mul]
  omega

lemma chainCoeff_flattenBlock (b : ℝ × ℕ) :
    chainCoeff (flattenBlock b) = b.1 := by
  unfold flattenBlock
  simp [chainCoeff, List.map_replicate, List.prod_replicate]

/-- cor:composition_reduces, graph-distance reading: a block chain
    carries the same rate as its flattened weight chain. -/
theorem chainRate_flatMap (bs : List (ℝ × ℕ))
    (hbs : ∀ b ∈ bs, 1 ≤ b.2) :
    chainRate (bs.flatMap flattenBlock) = chainRate bs := by
  induction bs with
  | nil => rfl
  | cons b bs' ih =>
    rw [List.flatMap_cons, chainRate_append,
      chainRate_flattenBlock b (hbs b List.mem_cons_self),
      ih fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb')]
    simp [chainRate]

/-- The flattened chain carries the same coefficient. -/
theorem chainCoeff_flatMap (bs : List (ℝ × ℕ)) :
    chainCoeff (bs.flatMap flattenBlock) = chainCoeff bs := by
  induction bs with
  | nil => rfl
  | cons b bs' ih =>
    rw [List.flatMap_cons, chainCoeff_append, chainCoeff_flattenBlock,
      ih]
    simp [chainCoeff]

/-- cor:composition_heterogeneous / cor:g10_composition, additive
    reading: n rate-2 blocks above the probe compose at moment rate
    4n, the α = 4(L − ℓ) profile. -/
theorem composition_rate_two_hasLeadingRate (g X : Ω → ℝ)
    (hg : ∀ ω, g ω = 0 ∨ g ω = 1) (c : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    HasLeadingRate
      (fun t => ∫ ω, composedSignal (List.replicate n (c, 2)) g X t ω ^ 2
        ∂μ)
      (4 * n) (c ^ (2 * n) * ∫ ω, g ω * X ω ^ 2 ∂μ) := by
  have h := composedSignal_hasLeadingRate (μ := μ) g X hg
    (bs := List.replicate n (c, 2)) (replicate_ne_nil n hn _)
  rw [chainRate_replicate,
    show 2 * (n * 2) = 4 * n from by ring, chainCoeff_replicate,
    show (c ^ n) ^ 2 = c ^ (2 * n) from by
      rw [← pow_mul, Nat.mul_comm]] at h
  exact h

/-- prop:attn_VO_invariant, offset form: one extra Linear multiplies
    the gradient by t and shifts the moment rate by exactly 2, with
    the coefficient untouched: the α_{W_V} − α_{W_O} = 2 invariant. -/
theorem HasLeadingRate.extra_linear {F : ℝ → ℝ} {p : ℕ} {a : ℝ}
    (h : HasLeadingRate F p a) :
    HasLeadingRate (fun t => t ^ 2 * F t) (2 + p) a := by
  have hsq : HasLeadingRate (fun t : ℝ => t ^ 2) 2 1 := by
    refine (tendsto_const_nhds (X := ℝ) (x := (1:ℝ))
      (f := 𝓝[>] (0:ℝ))).congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    exact (div_self (ne_of_gt (pow_pos ht 2))).symm
  have hmul := hsq.mul h
  rwa [one_mul] at hmul

end CompositionCorollaries

/-! ### The exclusion clauses (thm:bridge_composition, hypotheses)

Each clause of the scalar-linear-jointly-gated hypothesis excludes an
exact failure, and each failure is a theorem of the model. Disjoint
gates kill the composed moment identically, so no finite rate exists
with a non-zero coefficient. A quadratic dead-direction map compounds
the arriving order: on a t^e input a (c, k) block returns order
k + 2e, so the stack rate is not a sum as soon as e ≥ 1. A block that
injects non-dead signal at a fixed order caps the composed rate at
that order once the arriving order passes it, the LN reset of the
no-leakage clause. Clause (b), the forward direction, is the same
chain statement read with X the dead-direction input signal. -/

section ExclusionClauses

/-- thm:bridge_composition (b), forward: the chain model read with X
    the dead-direction input signal. The forward moment carries rate
    2·Σ k_i^fwd with coefficient (∏c)²·E[g·X²]; for gate-free chains
    take g ≡ 1. -/
theorem composedSignal_forward_hasLeadingRate (g X : Ω → ℝ)
    (hg : ∀ ω, g ω = 0 ∨ g ω = 1) {bs : List (ℝ × ℕ)} (hbs : bs ≠ []) :
    HasLeadingRate (fun t => ∫ ω, composedSignal bs g X t ω ^ 2 ∂μ)
      (2 * chainRate bs)
      (chainCoeff bs ^ 2 * ∫ ω, g ω * X ω ^ 2 ∂μ) :=
  composedSignal_hasLeadingRate g X hg hbs

/-- The joint-gate clause is sharp: with disjoint gates the composed
    second moment vanishes at every t, so the chain has no rate with a
    non-zero coefficient. -/
theorem disjoint_gates_moment_zero (g₁ g₂ X : Ω → ℝ)
    (hdisj : ∀ ω, g₁ ω * g₂ ω = 0)
    (c₁ c₂ : ℝ) (k₁ k₂ : ℕ) (t : ℝ) :
    ∫ ω, (c₁ * t^k₁ * g₁ ω * (c₂ * t^k₂ * g₂ ω * X ω)) ^ 2 ∂μ = 0 := by
  have hfun : ∀ ω,
      (c₁ * t^k₁ * g₁ ω * (c₂ * t^k₂ * g₂ ω * X ω)) ^ 2 = 0 := by
    intro ω
    have h : c₁ * t^k₁ * g₁ ω * (c₂ * t^k₂ * g₂ ω * X ω)
        = c₁ * t^k₁ * (c₂ * t^k₂) * X ω * (g₁ ω * g₂ ω) := by ring
    rw [h, hdisj ω, mul_zero]
    exact zero_pow (by omega)
  simp only [hfun]
  exact integral_zero _ _

/-- The linearity clause is sharp: a quadratic dead-direction map on a
    t^e input returns order k + 2e, and the squared moment carries
    rate 2(k + 2e). -/
theorem quad_block_compounds (c a : ℝ) (k e : ℕ) :
    HasLeadingRate (fun t => (c * t^k * (a * t^e) ^ 2) ^ 2)
      (2 * (k + 2 * e)) (c ^ 2 * a ^ 4) := by
  have h := (hasLeadingRate_pow (2 * (k + 2 * e))).const_mul
    (c ^ 2 * a ^ 4)
  rw [mul_one] at h
  refine h.congr fun t => ?_
  congr 1
  ring

/-- The compounded rate disagrees with the additive rate at every
    arriving order e ≥ 1. -/
theorem quad_rate_ne_additive (k e : ℕ) (he : 1 ≤ e) :
    2 * (k + 2 * e) ≠ 2 * (k + e) := by omega

/-- The no-leakage clause is sharp: a block injecting non-dead signal
    at fixed order cap below the arriving order k + e caps the
    composed squared moment at rate 2·cap with the injection
    coefficient. -/
theorem leak_caps_rate (ck a : ℝ) (cap ke : ℕ) (hlt : cap < ke) :
    HasLeadingRate (fun t => (a * t^cap + ck * t^ke) ^ 2)
      (2 * cap) (a ^ 2) := by
  have h1 : HasLeadingRate (fun t => a ^ 2 * t ^ (2 * cap))
      (2 * cap) (a ^ 2) := by
    have h := (hasLeadingRate_pow (2 * cap)).const_mul (a ^ 2)
    rwa [mul_one] at h
  have h2 : HasLeadingRate
      (fun t => (2 * a * ck) * t ^ (cap + ke)) (cap + ke)
      (2 * a * ck) := by
    have h := (hasLeadingRate_pow (cap + ke)).const_mul (2 * a * ck)
    rwa [mul_one] at h
  have h3 : HasLeadingRate (fun t => ck ^ 2 * t ^ (2 * ke))
      (2 * ke) (ck ^ 2) := by
    have h := (hasLeadingRate_pow (2 * ke)).const_mul (ck ^ 2)
    rwa [mul_one] at h
  have h23 := h2.add_of_lt h3 (by omega)
  have h := h1.add_of_lt h23 (by omega)
  refine h.congr fun t => ?_
  congr 1
  ring

/-- The capped rate disagrees with the additive rate. -/
theorem leak_cap_ne_additive (cap ke : ℕ) (hlt : cap < ke) :
    2 * cap ≠ 2 * ke := by omega

end ExclusionClauses

/-! ### The rotation-window constants from the two chains

rem:rot_window_bound writes the rotated dead reading as
G(t) = (γsc)² + b·t^{2K} and leaves γ and b to the architecture. At
the chain model both are read off the two routes that reach the
probe: the live route, a rate-0 chain whose coefficient is γ, leaks
through the rotated mask with the factor s·c of the planar witness;
the canonical dead route is a chain of rate K whose squared
coefficient is b. With the two route signals uncorrelated and unit
normalised, the moment of the sum is exactly the window form. -/

section RotConstants

/-- The window constants from the chains: γ is the live chain's
    coefficient, b the square of the dead chain's coefficient, and
    the moment of leak-plus-canonical is (γsc)² + b·t^{2K} exactly,
    with K the dead chain's rate. -/
theorem rot_constants_from_chains (g X₁ X₂ : Ω → ℝ)
    (hg : ∀ ω, g ω = 0 ∨ g ω = 1)
    {live dead : List (ℝ × ℕ)} (hlive : live ≠ []) (hdead : dead ≠ [])
    (hrate0 : chainRate live = 0)
    (h1 : Integrable (fun ω => g ω * X₁ ω ^ 2) μ)
    (h2 : Integrable (fun ω => g ω * X₂ ω ^ 2) μ)
    (h12 : Integrable (fun ω => g ω * (X₁ ω * X₂ ω)) μ)
    (hn1 : ∫ ω, g ω * X₁ ω ^ 2 ∂μ = 1)
    (hn2 : ∫ ω, g ω * X₂ ω ^ 2 ∂μ = 1)
    (hunc : ∫ ω, g ω * (X₁ ω * X₂ ω) ∂μ = 0)
    (s c t : ℝ) :
    ∫ ω, (s * c * composedSignal live g X₁ t ω
        + composedSignal dead g X₂ t ω) ^ 2 ∂μ
      = (chainCoeff live * s * c) ^ 2
        + chainCoeff dead ^ 2 * t ^ (2 * chainRate dead) := by
  have hgg : ∀ ω, g ω * g ω = g ω := fun ω => by
    rcases hg ω with h | h <;> rw [h] <;> ring
  have hfun : ∀ ω, (s * c * composedSignal live g X₁ t ω
        + composedSignal dead g X₂ t ω) ^ 2
      = (chainCoeff live * s * c) ^ 2 * (g ω * X₁ ω ^ 2)
        + (2 * (chainCoeff live * s * c)
            * (chainCoeff dead * t ^ chainRate dead))
          * (g ω * (X₁ ω * X₂ ω))
        + (chainCoeff dead ^ 2 * t ^ (2 * chainRate dead))
          * (g ω * X₂ ω ^ 2) := by
    intro ω
    rw [composedSignal_eq g X₁ hg t hlive ω,
      composedSignal_eq g X₂ hg t hdead ω, hrate0, pow_zero]
    have hpow : t ^ (2 * chainRate dead) = (t ^ chainRate dead) ^ 2 := by
      rw [mul_comm, pow_mul]
    rw [hpow]
    have hg2 := hgg ω
    linear_combination
      ((chainCoeff live * s * c) ^ 2 * X₁ ω ^ 2
        + 2 * (chainCoeff live * s * c)
          * (chainCoeff dead * t ^ chainRate dead) * (X₁ ω * X₂ ω)
        + (chainCoeff dead * t ^ chainRate dead) ^ 2 * X₂ ω ^ 2) * hg2
  simp only [hfun]
  rw [integral_add (by
        exact (h1.const_mul _).add (h12.const_mul _))
      (h2.const_mul _),
    integral_add (h1.const_mul _) (h12.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul,
    hn1, hn2, hunc]
  ring

/-- At the planar witness the leak factor is s·c exactly, so the
    crossover scale of rem:rot_window_bound reads
    t_× = ((γsc)²/b)^{1/(2K)} with γ and b the two chain
    coefficients: the rotation constants derived from the
    architecture at model level. -/
theorem rot_constants_crossover {live dead : List (ℝ × ℕ)}
    (hb : chainCoeff dead ≠ 0) (s c : ℝ) (hK : 1 ≤ chainRate dead) :
    chainCoeff dead ^ 2
        * (((chainCoeff live * s * c) ^ 2 / chainCoeff dead ^ 2)
            ^ ((1:ℝ) / (2 * chainRate dead))) ^ (2 * chainRate dead)
      = (chainCoeff live * s * c) ^ 2 := by
  have hb2 : (0:ℝ) < chainCoeff dead ^ 2 := by positivity
  have hnum : (0:ℝ) ≤ (chainCoeff live * s * c) ^ 2 / chainCoeff dead ^ 2 :=
    div_nonneg (sq_nonneg _) hb2.le
  have hn : (2 * chainRate dead : ℕ) ≠ 0 := by omega
  rw [← Real.rpow_natCast _ (2 * chainRate dead), ← Real.rpow_mul hnum]
  have hexp : (1:ℝ) / (2 * (chainRate dead : ℝ)) * ((2 * chainRate dead : ℕ) : ℝ)
      = 1 := by
    have : ((chainRate dead : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (show chainRate dead ≠ 0 by omega)
    push_cast
    field_simp
  rw [hexp, Real.rpow_one, mul_div_cancel₀ _ (ne_of_gt hb2)]

end RotConstants

/-! ### The residual graph (thm:bridge_res, res_ff, res_all, res_block)

The backward route through a residual computational graph is a list of
segments: a weight edge transfers c·t and costs one unit of weighted
path length; a residual block spanning k weights transfers 1 + c·t^k,
the skip route plus the k-weight chain, and costs nothing. The
composed moment carries leading rate 2·K with K the total weighted
path length: the shortest-path distance of Definition path_distance,
with the skip-saves-k accounting visible in the cost function. -/

section ResidualGraph

/-- A backward segment: a weight edge with coefficient c, or a
    residual block spanning k internal weights. -/
inductive ResSeg where
  | weight : ℝ → ResSeg
  | resblock : ℝ → ℕ → ResSeg

/-- The transfer factor of one segment. -/
noncomputable def ResSeg.transfer : ResSeg → ℝ → ℝ
  | .weight c, t => c * t
  | .resblock c k, t => 1 + c * t ^ k

/-- The weighted path cost: weight edges cost one, skips let the
    block cost nothing. -/
def ResSeg.kdist : ResSeg → ℕ
  | .weight _ => 1
  | .resblock _ _ => 0

/-- The leading coefficient: c on a weight edge, 1 on a block (the
    skip route dominates). -/
def ResSeg.coeff : ResSeg → ℝ
  | .weight c => c
  | .resblock _ _ => 1

/-- Well-formed segments: residual blocks span at least one weight. -/
def ResSeg.wf : ResSeg → Prop
  | .weight _ => True
  | .resblock _ k => 1 ≤ k

noncomputable def chainTransfer (l : List ResSeg) (t : ℝ) : ℝ :=
  (l.map (fun s => s.transfer t)).prod

def chainKdist (l : List ResSeg) : ℕ := (l.map ResSeg.kdist).sum

def chainCoeffR (l : List ResSeg) : ℝ := (l.map ResSeg.coeff).prod

lemma chainTransfer_cons (s : ResSeg) (l : List ResSeg) (t : ℝ) :
    chainTransfer (s :: l) t = s.transfer t * chainTransfer l t := by
  unfold chainTransfer
  rw [List.map_cons, List.prod_cons]

/-- One segment's squared transfer has leading rate 2·cost with
    coefficient coeff². -/
theorem seg_sq_hasLeadingRate (s : ResSeg) (hs : s.wf) :
    HasLeadingRate (fun t => (s.transfer t) ^ 2)
      (2 * s.kdist) (s.coeff ^ 2) := by
  cases s with
  | weight c =>
    simp only [ResSeg.transfer, ResSeg.kdist, ResSeg.coeff]
    refine (tendsto_const_nhds (X := ℝ) (x := c ^ 2)
      (f := 𝓝[>] (0:ℝ))).congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    have ht2 : t ^ (2 * 1) ≠ 0 := ne_of_gt (pow_pos ht _)
    field_simp
  | resblock c k =>
    simp only [ResSeg.transfer, ResSeg.kdist, ResSeg.coeff, one_pow]
    show HasLeadingRate (fun t => (1 + c * t ^ k) ^ 2) (2 * 0) 1
    have hcont : Filter.Tendsto (fun t : ℝ => (1 + c * t ^ k) ^ 2)
        (𝓝 (0:ℝ)) (𝓝 ((1 + c * 0 ^ k) ^ 2)) := by
      exact (Continuous.tendsto (by continuity) 0)
    have hk : (1:ℕ) ≤ k := hs
    have hval : (1 + c * (0:ℝ) ^ k) ^ 2 = 1 := by
      rw [zero_pow (by omega : k ≠ 0)]
      ring
    rw [hval] at hcont
    have h : Filter.Tendsto (fun t : ℝ => (1 + c * t ^ k) ^ 2)
        (𝓝[>] (0:ℝ)) (𝓝 1) := hcont.mono_left nhdsWithin_le_nhds
    refine h.congr' ?_
    filter_upwards [] with t
    rw [Nat.mul_zero, pow_zero, div_one]

/-- thm:bridge_res in the segment model: the composed squared
    transfer has leading rate 2·K with K the total weighted path
    cost, and coefficient the squared product of leading
    coefficients. -/
theorem chainTransfer_sq_hasLeadingRate (l : List ResSeg)
    (hl : ∀ s ∈ l, s.wf) :
    HasLeadingRate (fun t => (chainTransfer l t) ^ 2)
      (2 * chainKdist l) (chainCoeffR l ^ 2) := by
  induction l with
  | nil =>
    show HasLeadingRate (fun t => (chainTransfer [] t) ^ 2) _ _
    have hone : ∀ t : ℝ, chainTransfer [] t = 1 := fun t => rfl
    refine (tendsto_const_nhds (X := ℝ) (x := chainCoeffR [] ^ 2)
      (f := 𝓝[>] (0:ℝ))).congr' ?_
    filter_upwards [] with t
    rw [hone]
    show chainCoeffR [] ^ 2 = 1 ^ 2 / t ^ (2 * chainKdist [])
    have hK : chainKdist [] = 0 := rfl
    have hC : chainCoeffR [] = 1 := rfl
    rw [hK, hC, Nat.mul_zero, pow_zero, div_one]
  | cons s l' ih =>
    have hseg := seg_sq_hasLeadingRate s (hl s List.mem_cons_self)
    have hrest := ih fun s' hs' => hl s' (List.mem_cons_of_mem _ hs')
    have hmul := hseg.mul hrest
    have hfun : (fun t => (s.transfer t) ^ 2 * (chainTransfer l' t) ^ 2)
        = fun t => (chainTransfer (s :: l') t) ^ 2 := by
      funext t
      rw [chainTransfer_cons]
      ring
    rw [hfun] at hmul
    have hK : 2 * s.kdist + 2 * chainKdist l'
        = 2 * chainKdist (s :: l') := by
      have : chainKdist (s :: l') = s.kdist + chainKdist l' := by
        unfold chainKdist
        rw [List.map_cons, List.sum_cons]
      omega
    have hC : s.coeff ^ 2 * chainCoeffR l' ^ 2
        = chainCoeffR (s :: l') ^ 2 := by
      have : chainCoeffR (s :: l') = s.coeff * chainCoeffR l' := by
        unfold chainCoeffR
        rw [List.map_cons, List.prod_cons]
      rw [this]
      ring
    rw [hK, hC] at hmul
    exact hmul

/-- cor:res_ff: with no residual edges the cost is the depth, and the
    ladder rate 2(L − ℓ) returns. -/
theorem res_ff_kdist (c : ℝ) (m : ℕ) :
    chainKdist (List.replicate m (ResSeg.weight c)) = m := by
  unfold chainKdist
  rw [List.map_replicate, List.sum_replicate, smul_eq_mul]
  simp [ResSeg.kdist]

/-- cor:res_all: with every layer wrapped in a residual, the cost is
    zero at every depth and the composed moment is Θ(1): rate 0 with
    coefficient 1. -/
theorem res_all_hasLeadingRate (c : ℝ) (k m : ℕ) (hk : 1 ≤ k) :
    HasLeadingRate
      (fun t => (chainTransfer
        (List.replicate m (ResSeg.resblock c k)) t) ^ 2) 0 1 := by
  have h := chainTransfer_sq_hasLeadingRate
    (List.replicate m (ResSeg.resblock c k))
    (fun s hs => by
      rw [List.eq_of_mem_replicate hs]
      exact hk)
  have hK : chainKdist (List.replicate m (ResSeg.resblock c k)) = 0 := by
    unfold chainKdist
    rw [List.map_replicate, List.sum_replicate, smul_eq_mul]
    simp [ResSeg.kdist]
  have hC : chainCoeffR (List.replicate m (ResSeg.resblock c k)) = 1 := by
    unfold chainCoeffR
    rw [List.map_replicate, List.prod_replicate]
    simp [ResSeg.coeff]
  rw [hK, hC, Nat.mul_zero, one_pow] at h
  exact h

/-- cor:res_block, the skip-saves-k accounting: a residual block
    between a post-chain of length b and a pre-chain of length a
    contributes nothing to the cost, so K = a + b whatever k the
    block spans. -/
theorem res_block_kdist (a b k : ℕ) (c c' c'' : ℝ) :
    chainKdist (List.replicate b (ResSeg.weight c)
        ++ ResSeg.resblock c' k :: List.replicate a (ResSeg.weight c''))
      = a + b := by
  unfold chainKdist
  rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    List.map_replicate, List.sum_replicate, List.map_replicate,
    List.sum_replicate, smul_eq_mul, smul_eq_mul]
  simp [ResSeg.kdist]
  omega

/-- The sign hypothesis of the forward residual lemma is sharp: two
    tied shortest routes with coefficients c₁ and c₂ compose to the
    transfer (c₁ + c₂)·t, the moment coefficient is (c₁ + c₂)², and it
    vanishes exactly at c₂ = −c₁. A negative activation slope on one
    of two tied routes cancels the tie at leading order and the rate
    jumps, which is why φ'(0) > 0 is load-bearing. -/
theorem tied_routes_coeff (c₁ c₂ : ℝ) :
    HasLeadingRate (fun t => ((c₁ + c₂) * t) ^ 2) 2 ((c₁ + c₂) ^ 2)
    ∧ ((c₁ + c₂) ^ 2 = 0 ↔ c₂ = -c₁) := by
  constructor
  · have h := seg_sq_hasLeadingRate (ResSeg.weight (c₁ + c₂)) trivial
    simp only [ResSeg.transfer, ResSeg.kdist, ResSeg.coeff] at h
    rwa [Nat.mul_one] at h
  · rw [sq_eq_zero_iff]
    constructor
    · intro h
      linarith
    · intro h
      rw [h]
      ring

/-- The residual G-model: the dead entry carries the squared chain
    transfer, live entries are constant. -/
noncomputable def resGModel {n : ℕ} (l : List ResSeg) (mdead : ℝ)
    (mlive : Fin (n+1) → ℝ) (j₀ : Fin (n+1)) :
    ℝ → Fin (n+1) → ℝ :=
  fun t i => if i = j₀ then (chainTransfer l t) ^ 2 * mdead
    else mlive i

/-- cor:res_lambda_min, diagonal-model slice: the residual G-model's
    dead entry tends to zero when the path cost is positive, the live
    entries are Θ(1), and eventually the dead entry is the variational
    minimum of the diagonal form. -/
theorem res_lambda_min_slice {n : ℕ} (l : List ResSeg)
    (hl : ∀ s ∈ l, s.wf) (hK : 1 ≤ chainKdist l)
    (mdead : ℝ) (mlive : Fin (n+1) → ℝ) (j₀ : Fin (n+1))
    (hml : ∀ i, i ≠ j₀ → 0 < mlive i) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ v : Fin (n+1) → ℝ,
      resGModel l mdead mlive j₀ t j₀ * ∑ i, v i ^ 2
      ≤ ∑ i, resGModel l mdead mlive j₀ t i * v i ^ 2 := by
  apply diag_lambda_min_slice_general
  · have hred : (fun t => resGModel l mdead mlive j₀ t j₀)
        = fun t => (chainTransfer l t) ^ 2 * mdead := by
      funext t
      simp [resGModel]
    rw [hred]
    have h := (chainTransfer_sq_hasLeadingRate l hl).tendsto_zero
      (by omega : 2 * chainKdist l ≠ 0)
    have h2 : Filter.Tendsto
        (fun t => (chainTransfer l t) ^ 2 * mdead) (𝓝[>] (0:ℝ))
        (𝓝 (0 * mdead)) := h.mul_const mdead
    rwa [zero_mul] at h2
  · intro i hij
    refine ⟨mlive i, hml i hij, ?_⟩
    filter_upwards [] with t
    simp [resGModel, hij]

end ResidualGraph

/-! ### Near-canonical non-commuting limits (cor:bridge_near_canonical)

The paper states near-canonical continuity as an open problem and
constrains the answer's shape: at zero rotation the canonical rate is
exact, at any fixed rotation the asymptotic exponent collapses to the
mixed contribution's rate, and the two iterated limits disagree. The
model below carries that shape exactly: the perturbed observable
t^{2k} + ε²t² has leading rate 2 with coefficient ε² for every ε ≠ 0,
leading rate 2k at ε = 0, and the rates differ for every k ≥ 2. The
open question itself, a quantitative window bound as a function of ε,
stays open here as in the paper. -/

section NearCanonical

/-- At fixed ε the mixed contribution carries the rate: the perturbed
    observable has leading rate 2 with coefficient ε². The reading is
    informative for ε ≠ 0; at ε = 0 the coefficient vanishes and the
    canonical statement below applies. -/
theorem near_canonical_rate_perturbed (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) :
    HasLeadingRate (fun t => ε ^ 2 * t ^ 2 + t ^ (2 * k)) 2
      (ε ^ 2) := by
  have h1 : HasLeadingRate (fun t => ε ^ 2 * t ^ 2) 2 (ε ^ 2) := by
    have h := (hasLeadingRate_pow 2).const_mul (ε ^ 2)
    simpa using h
  have h2 : HasLeadingRate (fun t => t ^ (2 * k)) (2 * k) 1 :=
    hasLeadingRate_pow (2 * k)
  exact h1.add_of_lt h2 (by omega)

/-- At ε = 0 the canonical rate is exact: leading rate 2k with
    coefficient 1. -/
theorem near_canonical_rate_zero (k : ℕ) :
    HasLeadingRate (fun t => (0:ℝ) ^ 2 * t ^ 2 + t ^ (2 * k))
      (2 * k) 1 := by
  have h := hasLeadingRate_pow (2 * k)
  refine h.congr fun t => ?_
  ring_nf

/-- The two iterated limits disagree: the perturbed rate 2 and the
    canonical rate 2k differ for every k ≥ 2. -/
theorem near_canonical_rates_differ (k : ℕ) (hk : 2 ≤ k) :
    (2 : ℕ) ≠ 2 * k := by omega

end NearCanonical

end DeadDirections
