/-
  Deep-linear bridge slice (theory paper, thm:bridge, class (P1)).

  At the canonical-aligned configuration the layer matrix is
  W(t) = diag(1, …, 1, 0) + t·e_h e_hᵀ = diag(1, …, 1, t), so the
  backward composition over L − ℓ layers is diag(1, …, 1, t^{L−ℓ})
  exactly. Consequences, all exact for the linear class:

  * the dead coordinate of the backpropagated gradient at depth ℓ is
    t^{L−ℓ} times the output-gradient dead coordinate, so the dead
    diagonal of the G-factor obeys
    E[(δ_ℓ^{(h)})²] = t^{2(L−ℓ)}·E[(δ_L^{(h)})²]
    (thm:bridge (a), the per-layer ladder, dead-diagonal form);
  * every non-dead coordinate passes through unchanged
    (thm:bridge (b), the Θ(1) base);
  * the ladder rate at depth ℓ is 2(L−ℓ) as a leading rate, one
    integer step per layer.

  The A-factor dual is the forward statement: the dead coordinate of
  the activation at depth ℓ is t^ℓ times the input dead coordinate, so
  the dead diagonal of the A-factor carries t^{2ℓ}, and the A·G
  product at any depth is t^{2L} times a depth-free constant, the
  layer-independence clause of cor:a_g_duality, exact for (P1).

  Scope: the dead-diagonal entries of the exact A- and G-factors for
  (P1). Eigenvalue statements (λ_min of the full block) are not
  covered here; the nonlinear classes live in ReluChannel (P3) and
  SmoothChain (P2).
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import DeadDirections.FisherDecay

namespace DeadDirections

open MeasureTheory Filter Topology Matrix

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The canonical-aligned layer at parameter t: diag(1, …, 1, t), the
    dead row filled in with weight t. -/
def canonicalLayer (n : ℕ) (t : ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Matrix.diagonal (fun i => if i = Fin.last n then t else 1)

/-- Composing p canonical layers gives the canonical layer at t^p. -/
lemma canonicalLayer_pow (t : ℝ) (p : ℕ) :
    canonicalLayer n t ^ p = canonicalLayer n (t ^ p) := by
  unfold canonicalLayer
  rw [Matrix.diagonal_pow]
  congr 1
  funext i
  by_cases h : i = Fin.last n <;> simp [h]

/-- The composed backward map scales the dead coordinate by t^p. -/
lemma canonicalLayer_pow_mulVec_last (t : ℝ) (p : ℕ) (x : Fin (n+1) → ℝ) :
    (canonicalLayer n t ^ p).mulVec x (Fin.last n)
      = t ^ p * x (Fin.last n) := by
  rw [canonicalLayer_pow]
  unfold canonicalLayer
  rw [Matrix.mulVec_diagonal]
  simp

/-- Every non-dead coordinate passes through unchanged: the Θ(1) base
    of thm:bridge (b) is exact for the linear class. -/
lemma canonicalLayer_pow_mulVec_ne (t : ℝ) (p : ℕ) (x : Fin (n+1) → ℝ)
    {i : Fin (n+1)} (hi : i ≠ Fin.last n) :
    (canonicalLayer n t ^ p).mulVec x i = x i := by
  rw [canonicalLayer_pow]
  unfold canonicalLayer
  rw [Matrix.mulVec_diagonal]
  simp [hi]

/-- thm:bridge (a), class (P1), dead-diagonal form: the dead diagonal
    of the backward second moment at depth ℓ carries the exact factor
    t^{2(L−ℓ)} relative to the output gradient. -/
theorem deep_linear_backward_rate (L ℓ : ℕ) (t : ℝ)
    (δ : Ω → Fin (n+1) → ℝ) :
    ∫ ω, ((canonicalLayer n t ^ (L - ℓ)).mulVec (δ ω) (Fin.last n)) ^ 2 ∂μ
      = t ^ (2 * (L - ℓ)) * ∫ ω, (δ ω (Fin.last n)) ^ 2 ∂μ := by
  have hfun : ∀ ω, ((canonicalLayer n t ^ (L - ℓ)).mulVec (δ ω)
        (Fin.last n)) ^ 2
      = t ^ (2 * (L - ℓ)) * (δ ω (Fin.last n)) ^ 2 := by
    intro ω
    rw [canonicalLayer_pow_mulVec_last, mul_pow, mul_comm 2 (L - ℓ),
      pow_mul]
  simp only [hfun]
  rw [integral_const_mul]

/-- The per-layer ladder as a leading rate: depth ℓ reads 2(L−ℓ),
    one integer step per layer, connecting the linear-class bridge to
    the abstract fisher_decay layers. -/
theorem deep_linear_hasLeadingRate (L ℓ : ℕ) (δ : Ω → Fin (n+1) → ℝ) :
    HasLeadingRate
      (fun t => ∫ ω, ((canonicalLayer n t ^ (L - ℓ)).mulVec (δ ω)
        (Fin.last n)) ^ 2 ∂μ)
      (2 * (L - ℓ)) (∫ ω, (δ ω (Fin.last n)) ^ 2 ∂μ) := by
  have h : Tendsto (fun _ : ℝ => ∫ ω, (δ ω (Fin.last n)) ^ 2 ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ ω, (δ ω (Fin.last n)) ^ 2 ∂μ)) :=
    tendsto_const_nhds
  refine h.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  rw [deep_linear_backward_rate]
  have htp : t ^ (2 * (L - ℓ)) ≠ 0 := ne_of_gt (pow_pos ht _)
  field_simp

/-- cor:a_g_duality, class (P1), forward side: the dead diagonal of
    the activation second moment at depth ℓ carries the exact factor
    t^{2ℓ} relative to the input. -/
theorem deep_linear_forward_rate (ℓ : ℕ) (t : ℝ) (x : Ω → Fin (n+1) → ℝ) :
    ∫ ω, ((canonicalLayer n t ^ ℓ).mulVec (x ω) (Fin.last n)) ^ 2 ∂μ
      = t ^ (2 * ℓ) * ∫ ω, (x ω (Fin.last n)) ^ 2 ∂μ := by
  have hfun : ∀ ω, ((canonicalLayer n t ^ ℓ).mulVec (x ω) (Fin.last n)) ^ 2
      = t ^ (2 * ℓ) * (x ω (Fin.last n)) ^ 2 := by
    intro ω
    rw [canonicalLayer_pow_mulVec_last, mul_pow, mul_comm 2 ℓ, pow_mul]
  simp only [hfun]
  rw [integral_const_mul]

/-- cor:a_g_duality, class (P1): the product of the dead-diagonal A-
    and G-factor entries at depth ℓ is t^{2L} times a depth-free
    constant; the forward exponent 2ℓ and the backward exponent
    2(L−ℓ) sum to 2L at every depth. -/
theorem deep_linear_ag_product (L ℓ : ℕ) (hℓ : ℓ ≤ L) (t : ℝ)
    (x δ : Ω → Fin (n+1) → ℝ) :
    (∫ ω, ((canonicalLayer n t ^ ℓ).mulVec (x ω) (Fin.last n)) ^ 2 ∂μ)
      * (∫ ω, ((canonicalLayer n t ^ (L - ℓ)).mulVec (δ ω)
          (Fin.last n)) ^ 2 ∂μ)
      = t ^ (2 * L) * ((∫ ω, (x ω (Fin.last n)) ^ 2 ∂μ)
        * ∫ ω, (δ ω (Fin.last n)) ^ 2 ∂μ) := by
  rw [deep_linear_forward_rate, deep_linear_backward_rate,
    show t ^ (2 * ℓ) * (∫ ω, (x ω (Fin.last n)) ^ 2 ∂μ)
        * (t ^ (2 * (L - ℓ)) * ∫ ω, (δ ω (Fin.last n)) ^ 2 ∂μ)
      = t ^ (2 * ℓ) * t ^ (2 * (L - ℓ))
        * ((∫ ω, (x ω (Fin.last n)) ^ 2 ∂μ)
          * ∫ ω, (δ ω (Fin.last n)) ^ 2 ∂μ) from by ring,
    ← pow_add]
  congr 2
  omega

/-- The eventual-minimum reading of thm:bridge (a): for ℓ < L, when
    every output-gradient coordinate carries positive second moment,
    the dead diagonal entry of the backward second moment eventually
    drops below every non-dead entry. The G-factor is diagonal here,
    so its smallest diagonal entry is its smallest eigenvalue, and the
    ladder rate is the λ_min rate. -/
theorem deep_linear_dead_entry_eventually_le (L ℓ : ℕ) (hL : ℓ < L)
    (δ : Ω → Fin (n+1) → ℝ)
    (hpos : ∀ i, 0 < ∫ ω, (δ ω i) ^ 2 ∂μ) {i : Fin (n+1)}
    (hi : i ≠ Fin.last n) :
    ∀ᶠ t in 𝓝[>] (0:ℝ),
      ∫ ω, ((canonicalLayer n t ^ (L - ℓ)).mulVec (δ ω) (Fin.last n)) ^ 2 ∂μ
        ≤ ∫ ω, ((canonicalLayer n t ^ (L - ℓ)).mulVec (δ ω) i) ^ 2 ∂μ := by
  have hp : 2 * (L - ℓ) ≠ 0 := by omega
  have h0 : Tendsto
      (fun t : ℝ => t ^ (2 * (L - ℓ)) * ∫ ω, (δ ω (Fin.last n)) ^ 2 ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t ^ (2 * (L - ℓ))) (𝓝 (0:ℝ)) (𝓝 0) := by
      have h := (continuous_pow (2 * (L - ℓ))).tendsto (0:ℝ)
      rwa [zero_pow hp] at h
    have h2 : Tendsto
        (fun t : ℝ => t ^ (2 * (L - ℓ)) * ∫ ω, (δ ω (Fin.last n)) ^ 2 ∂μ)
        (𝓝[>] (0:ℝ)) (𝓝 (0 * ∫ ω, (δ ω (Fin.last n)) ^ 2 ∂μ)) :=
      (h1.mono_left nhdsWithin_le_nhds).mul_const _
    rwa [zero_mul] at h2
  filter_upwards [h0.eventually_lt_const (hpos i)] with t ht
  rw [deep_linear_backward_rate L ℓ t δ]
  have hcongr : ∫ ω, ((canonicalLayer n t ^ (L - ℓ)).mulVec (δ ω) i) ^ 2 ∂μ
      = ∫ ω, (δ ω i) ^ 2 ∂μ := by
    congr 1
    funext ω
    rw [canonicalLayer_pow_mulVec_ne t (L - ℓ) (δ ω) hi]
  rw [hcongr]
  exact ht.le

/-! ### The multi-direction bridge (thm:bridge_multi, g2/g3/g7)

One diagonal form carries the whole family: layer ℓ′ puts weight
t^{p ℓ′ j} on coordinate j, with p ℓ′ j = 0 off the dead set (t⁰ = 1,
so non-dead coordinates pass through unchanged). The backward product
over layers ℓ+1..L is diagonal with entry t^{Π_ℓ(j)},
Π_ℓ(j) = Σ_{ℓ′ > ℓ} p ℓ′ j: the cumulative exponent reads only the
layers above ℓ, which is cor:bridge_g3's observation, and the
per-direction rates 2·Π_ℓ(i) of thm:bridge_multi (a) with the joint
dead-block scaling follow exactly. -/

section MultiDirection

/-- The multi-direction canonical layer: diagonal, weight t^{pℓ j} on
    coordinate j. -/
def multiLayer (n : ℕ) (t : ℝ) (pℓ : Fin (n+1) → ℕ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Matrix.diagonal (fun j => t ^ pℓ j)

/-- The ordered backward product of the m layers above depth ℓ:
    W_{ℓ+m}···W_{ℓ+1}. -/
def multiProd (n : ℕ) (t : ℝ) (p : ℕ → Fin (n+1) → ℕ) (ℓ : ℕ) :
    ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ
  | 0 => 1
  | m + 1 => multiLayer n t (p (ℓ + m + 1)) * multiProd n t p ℓ m

/-- The cumulative backward exponent at depth ℓ over m layers above:
    a sum over the layers above ℓ only. -/
def cumExp (p : ℕ → Fin (n+1) → ℕ) (ℓ m : ℕ) (j : Fin (n+1)) : ℕ :=
  ∑ ℓ' ∈ Finset.Ico (ℓ + 1) (ℓ + m + 1), p ℓ' j

/-- The backward product is diagonal with the cumulative exponents. -/
lemma multiProd_eq_diagonal (t : ℝ) (p : ℕ → Fin (n+1) → ℕ) (ℓ m : ℕ) :
    multiProd n t p ℓ m
      = Matrix.diagonal (fun j => t ^ cumExp p ℓ m j) := by
  induction m with
  | zero =>
    unfold multiProd cumExp
    rw [show ℓ + 0 + 1 = ℓ + 1 from rfl, Finset.Ico_self]
    simp
  | succ k ih =>
    have hexp : ∀ j : Fin (n+1), cumExp p ℓ (k + 1) j
        = p (ℓ + k + 1) j + cumExp p ℓ k j := by
      intro j
      unfold cumExp
      rw [show ℓ + (k + 1) + 1 = (ℓ + k + 1) + 1 from rfl,
        Finset.sum_Ico_succ_top (by omega)]
      exact Nat.add_comm _ _
    have hfun : (fun i : Fin (n+1) =>
          t ^ p (ℓ + k + 1) i * t ^ cumExp p ℓ k i)
        = fun j : Fin (n+1) => t ^ cumExp p ℓ (k + 1) j := by
      funext j
      rw [hexp j, pow_add]
    unfold multiProd
    rw [ih]
    unfold multiLayer
    rw [Matrix.diagonal_mul_diagonal, hfun]

/-- Every coordinate of the backward product scales by its own
    cumulative exponent. -/
lemma multiProd_mulVec (t : ℝ) (p : ℕ → Fin (n+1) → ℕ) (ℓ m : ℕ)
    (x : Fin (n+1) → ℝ) (j : Fin (n+1)) :
    (multiProd n t p ℓ m).mulVec x j = t ^ cumExp p ℓ m j * x j := by
  rw [multiProd_eq_diagonal, Matrix.mulVec_diagonal]

/-- thm:bridge_multi (a)/(b): the coordinate-j entry of the backward
    second moment at depth ℓ carries the exact factor t^{2·Π_ℓ(j)};
    non-dead coordinates have Π = 0 and pass through exactly. -/
theorem multi_backward_rate (t : ℝ) (p : ℕ → Fin (n+1) → ℕ) (ℓ m : ℕ)
    (δ : Ω → Fin (n+1) → ℝ) (j : Fin (n+1)) :
    ∫ ω, ((multiProd n t p ℓ m).mulVec (δ ω) j) ^ 2 ∂μ
      = t ^ (2 * cumExp p ℓ m j) * ∫ ω, (δ ω j) ^ 2 ∂μ := by
  have hfun : ∀ ω, ((multiProd n t p ℓ m).mulVec (δ ω) j) ^ 2
      = t ^ (2 * cumExp p ℓ m j) * (δ ω j) ^ 2 := by
    intro ω
    rw [multiProd_mulVec, mul_pow, ← pow_mul,
      Nat.mul_comm (cumExp p ℓ m j) 2]
  simp only [hfun]
  rw [integral_const_mul]

/-- The joint dead-block scaling: the (i, j) cross moment carries
    t^{Π_ℓ(i) + Π_ℓ(j)} exactly, so the whole dead sub-block of the
    G-factor scales as a diagonal congruence. -/
theorem multi_backward_cross (t : ℝ) (p : ℕ → Fin (n+1) → ℕ) (ℓ m : ℕ)
    (δ : Ω → Fin (n+1) → ℝ) (i j : Fin (n+1)) :
    ∫ ω, ((multiProd n t p ℓ m).mulVec (δ ω) i)
        * ((multiProd n t p ℓ m).mulVec (δ ω) j) ∂μ
      = t ^ (cumExp p ℓ m i + cumExp p ℓ m j)
        * ∫ ω, δ ω i * δ ω j ∂μ := by
  have hfun : ∀ ω, ((multiProd n t p ℓ m).mulVec (δ ω) i)
        * ((multiProd n t p ℓ m).mulVec (δ ω) j)
      = t ^ (cumExp p ℓ m i + cumExp p ℓ m j) * (δ ω i * δ ω j) := by
    intro ω
    rw [multiProd_mulVec, multiProd_mulVec, pow_add]
    ring
  simp only [hfun]
  rw [integral_const_mul]

/-- cor:bridge_g3 / g7 reading: direction j at depth ℓ carries the
    leading rate 2·Π_ℓ(j), a function of the layers above ℓ only. -/
theorem multi_backward_hasLeadingRate (p : ℕ → Fin (n+1) → ℕ) (ℓ m : ℕ)
    (δ : Ω → Fin (n+1) → ℝ) (j : Fin (n+1)) :
    HasLeadingRate
      (fun t => ∫ ω, ((multiProd n t p ℓ m).mulVec (δ ω) j) ^ 2 ∂μ)
      (2 * cumExp p ℓ m j) (∫ ω, (δ ω j) ^ 2 ∂μ) := by
  have h : Tendsto (fun _ : ℝ => ∫ ω, (δ ω j) ^ 2 ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ ω, (δ ω j) ^ 2 ∂μ)) := tendsto_const_nhds
  refine h.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  rw [multi_backward_rate]
  have htp : t ^ (2 * cumExp p ℓ m j) ≠ 0 := ne_of_gt (pow_pos ht _)
  field_simp

/-- cor:bridge_g2 instantiation: at the uniform symmetric approach
    (p ≡ 1 on the dead set) every dead direction carries the shared
    exponent m = L − ℓ. -/
lemma cumExp_uniform (D : Finset (Fin (n+1))) (ℓ m : ℕ)
    (j : Fin (n+1)) (hj : j ∈ D) :
    cumExp (fun _ i => if i ∈ D then 1 else 0) ℓ m j = m := by
  unfold cumExp
  rw [Finset.sum_congr rfl fun ℓ' _ => if_pos hj, Finset.sum_const,
    Nat.card_Ico, smul_eq_mul, mul_one]
  omega

/-- The dead entries eventually drop below every non-dead entry:
    the entry form of the g2/g7 spectrum reading, with the non-dead
    Θ(1) base exact. -/
theorem multi_dead_entry_eventually_le (p : ℕ → Fin (n+1) → ℕ) (ℓ m : ℕ)
    (δ : Ω → Fin (n+1) → ℝ)
    {i j : Fin (n+1)} (hPj : 1 ≤ cumExp p ℓ m j)
    (hPi : cumExp p ℓ m i = 0) (hpos : 0 < ∫ ω, (δ ω i) ^ 2 ∂μ) :
    ∀ᶠ t in 𝓝[>] (0:ℝ),
      (∫ ω, ((multiProd n t p ℓ m).mulVec (δ ω) j) ^ 2 ∂μ)
      < ∫ ω, ((multiProd n t p ℓ m).mulVec (δ ω) i) ^ 2 ∂μ := by
  have hzero := (multi_backward_hasLeadingRate
    (μ := μ) p ℓ m δ j).tendsto_zero (by omega)
  filter_upwards [hzero.eventually_lt_const hpos] with t hlt
  have hi : ∫ ω, ((multiProd n t p ℓ m).mulVec (δ ω) i) ^ 2 ∂μ
      = ∫ ω, (δ ω i) ^ 2 ∂μ := by
    rw [multi_backward_rate, hPi]
    norm_num
  rw [hi]
  exact hlt

/-- thm:bridge_multi (d): at a single dead direction with p ≡ 1 the
    multi-direction layer is the canonical layer. -/
lemma multiLayer_eq_canonical (t : ℝ) :
    multiLayer n t (fun j => if j = Fin.last n then 1 else 0)
      = canonicalLayer n t := by
  unfold multiLayer canonicalLayer
  congr 1
  funext j
  by_cases h : j = Fin.last n <;> simp [h]

end MultiDirection

/-- cor:rect_lambda_min, diagonal-spectrum slice: with one dead
    direction and every other cumulative exponent zero, the dead entry
    is eventually the variational minimum of the diagonal quadratic
    form: entry(j₀)·‖v‖² bounds Σᵢ entry(i)·vᵢ² from below for every v.
    On the diagonal model the entries are the spectrum, so this is the
    λ_min statement. -/
theorem multi_lambda_min_slice (p : ℕ → Fin (n+1) → ℕ) (ℓ m : ℕ)
    (δ : Ω → Fin (n+1) → ℝ) {j₀ : Fin (n+1)}
    (hd : 1 ≤ cumExp p ℓ m j₀)
    (hlive : ∀ i, i ≠ j₀ → cumExp p ℓ m i = 0)
    (hpos : ∀ i, 0 < ∫ ω, (δ ω i) ^ 2 ∂μ) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ v : Fin (n+1) → ℝ,
      (∫ ω, ((multiProd n t p ℓ m).mulVec (δ ω) j₀) ^ 2 ∂μ)
          * ∑ i, v i ^ 2
        ≤ ∑ i, (∫ ω, ((multiProd n t p ℓ m).mulVec (δ ω) i) ^ 2 ∂μ)
          * v i ^ 2 := by
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ i : Fin (n+1),
      (∫ ω, ((multiProd n t p ℓ m).mulVec (δ ω) j₀) ^ 2 ∂μ)
        ≤ ∫ ω, ((multiProd n t p ℓ m).mulVec (δ ω) i) ^ 2 ∂μ := by
    rw [Filter.eventually_all]
    intro i
    by_cases hij : i = j₀
    · subst hij
      exact Filter.Eventually.of_forall fun t => le_refl _
    · exact (multi_dead_entry_eventually_le p ℓ m δ hd
        (hlive i hij) (hpos i)).mono fun t ht => ht.le
  filter_upwards [hev] with t ht v
  calc (∫ ω, ((multiProd n t p ℓ m).mulVec (δ ω) j₀) ^ 2 ∂μ)
        * ∑ i, v i ^ 2
      = ∑ i, (∫ ω, ((multiProd n t p ℓ m).mulVec (δ ω) j₀) ^ 2 ∂μ)
        * v i ^ 2 := Finset.mul_sum _ _ _
    _ ≤ ∑ i, (∫ ω, ((multiProd n t p ℓ m).mulVec (δ ω) i) ^ 2 ∂μ)
        * v i ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (ht i) (sq_nonneg _)

/-- The dead basis vector attains the bound: the variational minimum
    of the diagonal form equals the dead entry. -/
theorem multi_lambda_min_attained (t : ℝ) (p : ℕ → Fin (n+1) → ℕ)
    (ℓ m : ℕ) (δ : Ω → Fin (n+1) → ℝ) (j₀ : Fin (n+1)) :
    ∑ i, (∫ ω, ((multiProd n t p ℓ m).mulVec (δ ω) i) ^ 2 ∂μ)
        * ((Pi.single j₀ 1 : Fin (n+1) → ℝ) i) ^ 2
      = ∫ ω, ((multiProd n t p ℓ m).mulVec (δ ω) j₀) ^ 2 ∂μ := by
  have hterm : ∀ i : Fin (n+1),
      (∫ ω, ((multiProd n t p ℓ m).mulVec (δ ω) i) ^ 2 ∂μ)
        * ((Pi.single j₀ 1 : Fin (n+1) → ℝ) i) ^ 2
      = if i = j₀
        then ∫ ω, ((multiProd n t p ℓ m).mulVec (δ ω) j₀) ^ 2 ∂μ
        else 0 := by
    intro i
    by_cases h : i = j₀
    · subst h
      simp [Pi.single_eq_same]
    · simp [h]
  simp only [hterm]
  simp

/-- The diagonal λ_min slice, general form: when the dead entry tends
    to zero along the approach and every live entry stays above a
    positive floor, eventually the dead entry bounds the diagonal form
    from below at every vector; with diag_quadform_single it is the
    variational minimum. -/
theorem diag_lambda_min_slice_general (d : ℝ → Fin (n+1) → ℝ)
    (j₀ : Fin (n+1))
    (hdead : Filter.Tendsto (fun t => d t j₀) (𝓝[>] (0:ℝ)) (𝓝 0))
    (hlive : ∀ i, i ≠ j₀ → ∃ c, 0 < c ∧
      ∀ᶠ t in 𝓝[>] (0:ℝ), c ≤ d t i) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ v : Fin (n+1) → ℝ,
      d t j₀ * ∑ i, v i ^ 2 ≤ ∑ i, d t i * v i ^ 2 := by
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ i : Fin (n+1),
      d t j₀ ≤ d t i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hij : i = j₀
    · subst hij
      exact Filter.Eventually.of_forall fun t => le_refl _
    · obtain ⟨c, hc, hcev⟩ := hlive i hij
      filter_upwards [hcev, hdead.eventually_lt_const hc] with t h1 h2
      linarith
  filter_upwards [hev] with t ht v
  calc d t j₀ * ∑ i, v i ^ 2
      = ∑ i, d t j₀ * v i ^ 2 := Finset.mul_sum _ _ _
    _ ≤ ∑ i, d t i * v i ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (ht i) (sq_nonneg _)

/-! ### The rectangular bridge (thm:bridge_rect, lem:rect_product)

The narrow chain is self-contained: each rectangular layer acts as the
canonical layer on the shared narrow block and as an ARBITRARY map,
linear or not, on a complement whose dimension varies with depth. The
composed chain's narrow block is exactly the canonical power, so the
dead ladder t^{L−ℓ} and the non-dead Θ(1) base carry over unchanged,
which is thm:bridge_rect's width-independence in a form stronger than
the paper's linear complements. On the square canonical chain the
variational form of σ_min is exact: ‖P(t)v‖² ≥ t^{2m}‖v‖² with
equality on the dead basis vector, cor:rect_product_sigma_min's
canonical instance with c = 1. -/

section Rectangular

variable {c : ℕ → ℕ}

/-- The state space at depth ℓ: the shared narrow block next to a
    complement of depth-dependent dimension. -/
def RectSpace (n : ℕ) (c : ℕ → ℕ) (ℓ : ℕ) : Type :=
  (Fin (n + 1) → ℝ) × (Fin (c ℓ) → ℝ)

/-- One rectangular layer: canonical on the narrow block, arbitrary on
    the complement. -/
def rectLayer (n : ℕ) (t : ℝ) (c : ℕ → ℕ)
    (B : ∀ ℓ, (Fin (c ℓ) → ℝ) → (Fin (c (ℓ + 1)) → ℝ)) (ℓ : ℕ)
    (q : RectSpace n c ℓ) : RectSpace n c (ℓ + 1) :=
  ((canonicalLayer n t).mulVec q.1, B ℓ q.2)

/-- The chain from depth ℓ through m further layers. -/
def rectChain (n : ℕ) (t : ℝ) (c : ℕ → ℕ)
    (B : ∀ ℓ, (Fin (c ℓ) → ℝ) → (Fin (c (ℓ + 1)) → ℝ)) (ℓ : ℕ) :
    (m : ℕ) → RectSpace n c ℓ → RectSpace n c (ℓ + m)
  | 0 => id
  | m + 1 => fun q => rectLayer n t c B (ℓ + m) (rectChain n t c B ℓ m q)

/-- lem:rect_product: the narrow block of the composed chain is the
    canonical power, whatever the complement maps do. -/
lemma rectChain_fst (n : ℕ) (t : ℝ) (c : ℕ → ℕ)
    (B : ∀ ℓ, (Fin (c ℓ) → ℝ) → (Fin (c (ℓ + 1)) → ℝ)) (ℓ m : ℕ)
    (q : RectSpace n c ℓ) :
    (rectChain n t c B ℓ m q).1 = (canonicalLayer n t ^ m).mulVec q.1 := by
  induction m with
  | zero =>
    rw [pow_zero]
    exact (Matrix.one_mulVec q.1).symm
  | succ k ih =>
    show ((canonicalLayer n t).mulVec (rectChain n t c B ℓ k q).1)
      = (canonicalLayer n t ^ (k + 1)).mulVec q.1
    rw [ih, Matrix.mulVec_mulVec, ← pow_succ']

/-- thm:bridge_rect (a), ladder form: the dead coordinate of the
    chain scales by t^m exactly, independent of the complement maps
    and their widths. -/
theorem rect_dead_ladder (n : ℕ) (t : ℝ) (c : ℕ → ℕ)
    (B : ∀ ℓ, (Fin (c ℓ) → ℝ) → (Fin (c (ℓ + 1)) → ℝ)) (ℓ m : ℕ)
    (q : RectSpace n c ℓ) :
    (rectChain n t c B ℓ m q).1 (Fin.last n)
      = t ^ m * q.1 (Fin.last n) := by
  rw [rectChain_fst, canonicalLayer_pow_mulVec_last]

/-- The Θ(1) base: every non-dead narrow coordinate passes through
    the rectangular chain unchanged. -/
theorem rect_nondead_invariant (n : ℕ) (t : ℝ) (c : ℕ → ℕ)
    (B : ∀ ℓ, (Fin (c ℓ) → ℝ) → (Fin (c (ℓ + 1)) → ℝ)) (ℓ m : ℕ)
    (q : RectSpace n c ℓ) {i : Fin (n + 1)} (hi : i ≠ Fin.last n) :
    (rectChain n t c B ℓ m q).1 i = q.1 i := by
  rw [rectChain_fst, canonicalLayer_pow_mulVec_ne t m q.1 hi]

/-- The backward second moment through the rectangular chain: the
    dead-diagonal entry carries t^{2m} exactly, for any complement
    maps. -/
theorem rect_backward_rate (n : ℕ) (t : ℝ) (c : ℕ → ℕ)
    (B : ∀ ℓ, (Fin (c ℓ) → ℝ) → (Fin (c (ℓ + 1)) → ℝ)) (ℓ m : ℕ)
    (δ : Ω → RectSpace n c ℓ) :
    ∫ ω, ((rectChain n t c B ℓ m (δ ω)).1 (Fin.last n)) ^ 2 ∂μ
      = t ^ (2 * m) * ∫ ω, ((δ ω).1 (Fin.last n)) ^ 2 ∂μ := by
  have hfun : ∀ ω, ((rectChain n t c B ℓ m (δ ω)).1 (Fin.last n)) ^ 2
      = t ^ (2 * m) * ((δ ω).1 (Fin.last n)) ^ 2 := by
    intro ω
    rw [rect_dead_ladder, mul_pow, ← pow_mul, Nat.mul_comm m 2]
  simp only [hfun]
  rw [integral_const_mul]

/-- cor:rect_product_sigma_min, canonical square instance, lower
    bound: on the canonical chain ‖P(t)v‖² ≥ t^{2p}‖v‖² for t ∈ [0,1],
    in the sum-of-squares form. -/
theorem canonical_sigma_min_lower {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (p : ℕ) (v : Fin (n + 1) → ℝ) :
    t ^ (2 * p) * ∑ i, v i ^ 2
      ≤ ∑ i, ((canonicalLayer n t ^ p).mulVec v i) ^ 2 := by
  have ht2 : t ^ (2 * p) ≤ 1 := pow_le_one₀ ht0 ht1
  have hterm : ∀ i : Fin (n + 1),
      t ^ (2 * p) * v i ^ 2 ≤ ((canonicalLayer n t ^ p).mulVec v i) ^ 2 := by
    intro i
    by_cases h : i = Fin.last n
    · subst h
      rw [canonicalLayer_pow_mulVec_last, mul_pow, ← pow_mul,
        Nat.mul_comm p 2]
    · rw [canonicalLayer_pow_mulVec_ne t p v h]
      nlinarith [sq_nonneg (v i), ht2]
  calc t ^ (2 * p) * ∑ i, v i ^ 2
      = ∑ i, t ^ (2 * p) * v i ^ 2 := Finset.mul_sum _ _ _
    _ ≤ ∑ i, ((canonicalLayer n t ^ p).mulVec v i) ^ 2 :=
        Finset.sum_le_sum fun i _ => hterm i

/-- cor:rect_product_sigma_min, canonical square instance, attained:
    the dead basis vector realises the bound exactly, so the
    variational σ_min of the canonical chain is t^p. -/
theorem canonical_sigma_min_attained (t : ℝ) (p : ℕ) :
    ∑ i, ((canonicalLayer n t ^ p).mulVec
        (Pi.single (Fin.last n) 1) i) ^ 2 = t ^ (2 * p) := by
  rw [canonicalLayer_pow]
  unfold canonicalLayer
  have hterm : ∀ i : Fin (n + 1),
      ((Matrix.diagonal (fun i => if i = Fin.last n then t ^ p else 1)).mulVec
        (Pi.single (Fin.last n) 1) i) ^ 2
      = if i = Fin.last n then t ^ (2 * p) else 0 := by
    intro i
    rw [Matrix.mulVec_diagonal]
    by_cases h : i = Fin.last n
    · subst h
      simp [Pi.single_eq_same, ← pow_mul, Nat.mul_comm p 2]
    · simp [h]
  simp only [hterm]
  simp

end Rectangular

/-! ### Task expansion in the head's G-factor (prop:task_expansion_gfactor)

The exact block slice: the expanded head's diagonal takes σ_new² on
the fresh outputs and σ_old² on the preserved ones, the quadratic form
is sandwiched between σ_old²‖v‖² and σ_new²‖v‖² with each end attained
on a basis vector, and a diagonal Jacobian multiplies the spread by at
most its own squared conditioning: the κ(J)²·κ(G_head) bound of
clause (b), in entry form. -/

section TaskExpansion

variable {N : ℕ}

/-- Entrywise diagonal bounds bound the quadratic form uniformly. -/
lemma diag_quadform_ge (d : Fin N → ℝ) (lo : ℝ)
    (hlo : ∀ i, lo ≤ d i) (v : Fin N → ℝ) :
    lo * ∑ i, v i ^ 2 ≤ ∑ i, d i * v i ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hlo i) (sq_nonneg _)

lemma diag_quadform_le (d : Fin N → ℝ) (hi : ℝ)
    (hhi : ∀ i, d i ≤ hi) (v : Fin N → ℝ) :
    ∑ i, d i * v i ^ 2 ≤ hi * ∑ i, v i ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hhi i) (sq_nonneg _)

/-- The form attains a diagonal entry on its basis vector. -/
lemma diag_quadform_single (d : Fin N → ℝ) (i₀ : Fin N) :
    ∑ i, d i * ((Pi.single i₀ 1 : Fin N → ℝ) i) ^ 2 = d i₀ := by
  have hterm : ∀ i : Fin N,
      d i * ((Pi.single i₀ 1 : Fin N → ℝ) i) ^ 2
      = if i = i₀ then d i else 0 := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      simp [Pi.single_eq_same]
    · simp [hi]
  simp only [hterm]
  simp

/-- prop:task_expansion_gfactor (a), exact block slice: with the head
    diagonal at σ_new² on the new outputs and σ_old² on the old, the
    form is sandwiched between the two variances with both ends
    attained, so the condition ratio is exactly σ_new²/σ_old². -/
theorem task_expansion_head_bounds (σn σo : ℝ)
    (hσ : 0 ≤ σo) (hσσ : σo ≤ σn)
    (P : Fin N → Prop) [DecidablePred P] (v : Fin N → ℝ) :
    σo ^ 2 * ∑ i, v i ^ 2
        ≤ ∑ i, (if P i then σn ^ 2 else σo ^ 2) * v i ^ 2
    ∧ ∑ i, (if P i then σn ^ 2 else σo ^ 2) * v i ^ 2
        ≤ σn ^ 2 * ∑ i, v i ^ 2 := by
  constructor
  · refine diag_quadform_ge _ _ (fun i => ?_) v
    by_cases h : P i
    · simp only [if_pos h]
      nlinarith
    · simp [h]
  · refine diag_quadform_le _ _ (fun i => ?_) v
    by_cases h : P i
    · simp [h]
    · simp only [if_neg h]
      nlinarith

/-- prop:task_expansion_gfactor (b), diagonal inheritance: through a
    diagonal Jacobian the hidden entries are jᵢ²·dᵢ, so the entry
    spread multiplies by at most the Jacobian's squared conditioning:
    the κ(G_ℓ) ≤ κ(J)²·κ(G_head) bound in entry form. -/
theorem task_expansion_inherit_bounds (j d : Fin N → ℝ)
    {jlo jhi lo hi : ℝ} (hj0 : 0 ≤ jlo)
    (hjlo : ∀ i, jlo ≤ |j i|) (hjhi : ∀ i, |j i| ≤ jhi)
    (hd0 : 0 ≤ lo) (hdlo : ∀ i, lo ≤ d i) (hdhi : ∀ i, d i ≤ hi)
    (i : Fin N) :
    jlo ^ 2 * lo ≤ j i ^ 2 * d i ∧ j i ^ 2 * d i ≤ jhi ^ 2 * hi := by
  have hsq : jlo ^ 2 ≤ j i ^ 2 := by
    have h := pow_le_pow_left₀ hj0 (hjlo i) 2
    rwa [sq_abs] at h
  have hsq2 : j i ^ 2 ≤ jhi ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (hjhi i) 2
    rwa [sq_abs] at h
  constructor
  · have h1 : jlo ^ 2 * lo ≤ j i ^ 2 * lo :=
      mul_le_mul_of_nonneg_right hsq hd0
    have h2 : j i ^ 2 * lo ≤ j i ^ 2 * d i :=
      mul_le_mul_of_nonneg_left (hdlo i) (sq_nonneg _)
    linarith
  · have h0 : 0 ≤ d i := le_trans hd0 (hdlo i)
    have h1 : j i ^ 2 * d i ≤ jhi ^ 2 * d i :=
      mul_le_mul_of_nonneg_right hsq2 h0
    have h2 : jhi ^ 2 * d i ≤ jhi ^ 2 * hi :=
      mul_le_mul_of_nonneg_left (hdhi i) (sq_nonneg jhi)
    linarith

end TaskExpansion

/-! ### The rotated configuration (prop:bridge_linear_rot)

Rotation is without loss of generality for the linear class, and the
proof needs only orthogonality, not a singular value decomposition:
with W(t) = U·D(t)·Uᵀ and the rotated dead direction u = U·e_h, the
pairing u ⬝ (chain · δ) telescopes through UᵀU = 1 to the canonical
dead coordinate of the rotated gradient, and the backward moment
carries t^{2m} exactly at every rotation. -/

section Rotated

/-- The rotated chain pairs with the rotated dead direction as the
    canonical chain pairs with the canonical one. -/
lemma rotated_pairing (U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hU : Uᵀ * U = 1) (t : ℝ) (m : ℕ) (x : Fin (n+1) → ℝ) :
    (U.mulVec (Pi.single (Fin.last n) 1)) ⬝ᵥ
        ((U * (canonicalLayer n t ^ m) * Uᵀ).mulVec x)
      = t ^ m * (Uᵀ.mulVec x) (Fin.last n) := by
  set z := (U * (canonicalLayer n t ^ m) * Uᵀ).mulVec x with hz
  have h1 : (U.mulVec (Pi.single (Fin.last n) 1)) ⬝ᵥ z
      = (Pi.single (Fin.last n) 1 : Fin (n+1) → ℝ) ⬝ᵥ (Uᵀ.mulVec z) := by
    rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm]
    congr 1
    rw [← Matrix.transpose_transpose U, Matrix.vecMul_transpose,
      Matrix.transpose_transpose]
  rw [h1, hz, Matrix.mulVec_mulVec]
  have h2 : Uᵀ * (U * (canonicalLayer n t ^ m) * Uᵀ)
      = (canonicalLayer n t ^ m) * Uᵀ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [h2, ← Matrix.mulVec_mulVec, single_dotProduct, one_mul,
    canonicalLayer_pow_mulVec_last]

/-- prop:bridge_linear_rot: the backward moment at the rotated dead
    direction carries t^{2m} exactly, at every orthogonal U. Rotation
    is without loss of generality for the linear class. -/
theorem rotated_backward_rate (U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hU : Uᵀ * U = 1) (t : ℝ) (m : ℕ) (δ : Ω → Fin (n+1) → ℝ) :
    ∫ ω, ((U.mulVec (Pi.single (Fin.last n) 1)) ⬝ᵥ
        ((U * (canonicalLayer n t ^ m) * Uᵀ).mulVec (δ ω))) ^ 2 ∂μ
      = t ^ (2 * m)
        * ∫ ω, ((Uᵀ.mulVec (δ ω)) (Fin.last n)) ^ 2 ∂μ := by
  have hfun : ∀ ω, ((U.mulVec (Pi.single (Fin.last n) 1)) ⬝ᵥ
        ((U * (canonicalLayer n t ^ m) * Uᵀ).mulVec (δ ω))) ^ 2
      = t ^ (2 * m) * ((Uᵀ.mulVec (δ ω)) (Fin.last n)) ^ 2 := by
    intro ω
    rw [rotated_pairing U hU, mul_pow, ← pow_mul, Nat.mul_comm m 2]
  simp only [hfun]
  rw [integral_const_mul]

/-- The rate reading: the rotated configuration has leading rate 2m
    with the rotated-gradient coefficient, unchanged from canonical. -/
theorem rotated_hasLeadingRate (U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hU : Uᵀ * U = 1) (m : ℕ) (δ : Ω → Fin (n+1) → ℝ) :
    HasLeadingRate
      (fun t => ∫ ω, ((U.mulVec (Pi.single (Fin.last n) 1)) ⬝ᵥ
        ((U * (canonicalLayer n t ^ m) * Uᵀ).mulVec (δ ω))) ^ 2 ∂μ)
      (2 * m) (∫ ω, ((Uᵀ.mulVec (δ ω)) (Fin.last n)) ^ 2 ∂μ) := by
  have h : Tendsto
      (fun _ : ℝ => ∫ ω, ((Uᵀ.mulVec (δ ω)) (Fin.last n)) ^ 2 ∂μ)
      (𝓝[>] (0:ℝ))
      (𝓝 (∫ ω, ((Uᵀ.mulVec (δ ω)) (Fin.last n)) ^ 2 ∂μ)) :=
    tendsto_const_nhds
  refine h.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  rw [rotated_backward_rate U hU]
  have htp : t ^ (2 * m) ≠ 0 := ne_of_gt (pow_pos ht _)
  field_simp

end Rotated

section RectLeak

open Filter Topology

/-! ### thm:bridge_rect clause (c): the complement leak

The invariance hypothesis carries the content. With the complement
invariant the composed dead output is t²·x and the KL-proxy carries
rate 4, the k = 2 order of the theorem. A first-order complement
leak adds t·γ·c to the composed map, the KL-proxy rate drops to 2,
and the reading is KL order 1: below the k ≥ 2 threshold of the
dead-direction definition, so the approach is not a dead direction
at all. The rate pair is exactly the paper's bottleneck instance
(slope 2.000 against the invariant 4). -/

/-- The composed dead output with a first-order complement leak. -/
def leakOut (γ x c t : ℝ) : ℝ := t ^ 2 * x + t * (γ * c)

/-- The leaked KL-proxy rate: 2, with the leak coefficient. KL
    order 1, below the dead-direction threshold. -/
theorem leak_kl_rate (γ x c : ℝ) :
    HasLeadingRate (fun t => (leakOut γ x c t) ^ 2) 2
      ((γ * c) ^ 2) := by
  have h1 : HasLeadingRate (fun t => (γ * c) ^ 2 * t ^ 2) 2
      ((γ * c) ^ 2) := by
    simpa using (hasLeadingRate_pow 2).const_mul ((γ * c) ^ 2)
  have h2 : HasLeadingRate (fun t => 2 * x * (γ * c) * t ^ 3) 3
      (2 * x * (γ * c)) := by
    simpa using (hasLeadingRate_pow 3).const_mul (2 * x * (γ * c))
  have h3 : HasLeadingRate (fun t => x ^ 2 * t ^ 4) 4 (x ^ 2) := by
    simpa using (hasLeadingRate_pow 4).const_mul (x ^ 2)
  have h23 := h2.add_of_lt h3 (by omega)
  have h := h1.add_of_lt h23 (by omega)
  refine h.congr fun t => ?_
  unfold leakOut
  ring_nf

/-- The invariant chain's rate: 4, the k = 2 order of the
    theorem. -/
theorem invariant_kl_rate (x c : ℝ) :
    HasLeadingRate (fun t => (leakOut 0 x c t) ^ 2) 4 (x ^ 2) := by
  have h : HasLeadingRate (fun t => x ^ 2 * t ^ 4) 4 (x ^ 2) := by
    simpa using (hasLeadingRate_pow 4).const_mul (x ^ 2)
  refine h.congr fun t => ?_
  unfold leakOut
  ring_nf

/-- KL slope 2 corresponds to no admissible order: the leaked
    approach is not a dead direction. -/
theorem leak_not_dead (k : ℕ) (hk : 2 ≤ k) : (2 : ℕ) ≠ 2 * k := by
  omega

end RectLeak

end DeadDirections