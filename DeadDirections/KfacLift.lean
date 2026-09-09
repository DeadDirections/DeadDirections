/-
  The Kronecker lift of the dead direction (theory paper,
  cor:kfac_lift and rem:kfac_lift_crosslayer), diagonal model.

  The per-layer K-FAC factor is A ⊗ G. In the diagonal model both
  factors are entry arrays and the Kronecker product is the product
  array on the product index. The corollary's mechanism: the bottom
  eigenvalue of the product array is the product of the bottom factor
  eigenvalues (non-negativity makes products smallest at the pair of
  minima), the bottom direction is the pair index (the rank-one lift
  g_min a_minᵀ), and at the canonical singular configuration the
  bottom pair is the dead unit with eigenvalue t^{2(a+b)}: the A–G
  duality product, read from the two factor arrays with the parameter
  Fisher never formed. The cross-layer remark's gauge-ray flatness is
  the other layer contributing the factor zero.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Kronecker
import DeadDirections.FisherDecay
import DeadDirections.SigmaMin

namespace DeadDirections

/-- The diagonal-model Kronecker product: the product array on the
    product index. -/
def kron {n m : ℕ} (α : Fin n → ℝ) (γ : Fin m → ℝ) :
    Fin n × Fin m → ℝ :=
  fun p => α p.1 * γ p.2

/-- The bottom of the product array is the product of the factor
    bottoms: with non-negative floors below each factor, the product
    of the floors sits below every product entry. -/
theorem kron_min {n m : ℕ} {α : Fin n → ℝ} {γ : Fin m → ℝ}
    {a0 g0 : ℝ} (ha0 : 0 ≤ a0) (hg0 : 0 ≤ g0)
    (hα : ∀ i, a0 ≤ α i) (hγ : ∀ j, g0 ≤ γ j) :
    ∀ p : Fin n × Fin m, a0 * g0 ≤ kron α γ p := by
  intro p
  have h1 : a0 * g0 ≤ α p.1 * g0 :=
    mul_le_mul_of_nonneg_right (hα p.1) hg0
  have h2 : α p.1 * g0 ≤ α p.1 * γ p.2 :=
    mul_le_mul_of_nonneg_left (hγ p.2) (ha0.trans (hα p.1))
  exact h1.trans h2

/-- The floor is attained at the pair of attaining indices: the
    bottom direction of the lift is the pair (i₀, j₀), the rank-one
    weight increment. -/
theorem kron_min_attained {n m : ℕ} (α : Fin n → ℝ) (γ : Fin m → ℝ)
    (i₀ : Fin n) (j₀ : Fin m) :
    kron α γ (i₀, j₀) = α i₀ * γ j₀ := rfl

/-- The variational form: the product floor bounds the diagonal
    quadratic form of the lifted factor at every parameter vector. -/
theorem kron_quadform {n m : ℕ} {α : Fin n → ℝ} {γ : Fin m → ℝ}
    {a0 g0 : ℝ} (ha0 : 0 ≤ a0) (hg0 : 0 ≤ g0)
    (hα : ∀ i, a0 ≤ α i) (hγ : ∀ j, g0 ≤ γ j)
    (v : Fin n × Fin m → ℝ) :
    a0 * g0 * ∑ p, v p ^ 2 ≤ ∑ p, kron α γ p * v p ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  exact mul_le_mul_of_nonneg_right (kron_min ha0 hg0 hα hγ p)
    (sq_nonneg _)

section Canonical

variable {n m : ℕ}

/-- The canonical input factor: unit entries except t^{2a} at the
    dead unit. -/
noncomputable def canonicalFactor (t : ℝ) (a : ℕ) (h : Fin n) :
    Fin n → ℝ :=
  fun i => if i = h then t ^ (2 * a) else 1

/-- At the canonical configuration the dead-unit pair of the lift
    carries exactly the A–G duality product t^{2(a+b)}. -/
theorem canonical_kron_dead (t : ℝ) (a b : ℕ) (h : Fin n)
    (h' : Fin m) :
    kron (canonicalFactor t a h) (canonicalFactor t b h') (h, h')
      = t ^ (2 * (a + b)) := by
  have hexp : 2 * (a + b) = 2 * a + 2 * b := by ring
  simp only [kron, canonicalFactor, if_pos]
  rw [hexp, pow_add]

/-- For 0 < t ≤ 1 the dead-unit pair is the bottom of the lifted
    array: every other pair carries at least one unit factor and sits
    above it. -/
theorem canonical_kron_bottom {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (a b : ℕ) (h : Fin n) (h' : Fin m) :
    ∀ p : Fin n × Fin m,
      kron (canonicalFactor t a h) (canonicalFactor t b h') (h, h')
        ≤ kron (canonicalFactor t a h) (canonicalFactor t b h') p := by
  intro p
  have hpa : t ^ (2 * a) ≤ 1 := pow_le_one₀ ht0 ht1
  have hpb : t ^ (2 * b) ≤ 1 := pow_le_one₀ ht0 ht1
  have hna : 0 ≤ t ^ (2 * a) := pow_nonneg ht0 _
  have hnb : 0 ≤ t ^ (2 * b) := pow_nonneg ht0 _
  rw [canonical_kron_dead]
  have hexp : 2 * (a + b) = 2 * a + 2 * b := by ring
  rw [hexp, pow_add]
  simp only [kron, canonicalFactor]
  by_cases h1 : p.1 = h
  · by_cases h2 : p.2 = h'
    · rw [if_pos h1, if_pos h2]
    · rw [if_pos h1, if_neg h2, mul_one]
      have h := mul_le_mul_of_nonneg_left hpb hna
      simpa using h
  · rw [if_neg h1, one_mul]
    by_cases h2 : p.2 = h'
    · rw [if_pos h2]
      have h := mul_le_mul_of_nonneg_right hpa hnb
      simpa using h
    · rw [if_neg h2]
      calc t ^ (2 * a) * t ^ (2 * b) ≤ 1 * 1 :=
            mul_le_mul hpa hpb hnb (by norm_num)
        _ = 1 := by norm_num

/-- The per-layer factor ladder (thm:multilayer-A at the diagonal
    model): the layer-ℓ factor array carries exactly t^{2a} at the
    dead unit (a = ℓ−1 on the A side, L−ℓ on the G side), and for
    0 < t ≤ 1 that entry is the bottom of the array. -/
theorem canonical_factor_bottom {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (a : ℕ) (h : Fin n) :
    canonicalFactor t a h h = t ^ (2 * a)
      ∧ ∀ i, canonicalFactor t a h h ≤ canonicalFactor t a h i := by
  have hval : canonicalFactor t a h h = t ^ (2 * a) := by
    simp [canonicalFactor]
  refine ⟨hval, fun i => ?_⟩
  rw [hval]
  unfold canonicalFactor
  by_cases hi : i = h
  · rw [if_pos hi]
  · rw [if_neg hi]
    exact pow_le_one₀ ht0 ht1

end Canonical

section MatrixKron

open Matrix Kronecker

/-- The Kronecker product of vectors on the product index: the
    vectorisation of the rank-one matrix g aᵀ. -/
def vecKron {n m : ℕ} (a : Fin n → ℝ) (g : Fin m → ℝ) :
    Fin n × Fin m → ℝ :=
  fun p => a p.1 * g p.2

/-- The rank-one identification: the (i, j) entry of the lifted
    vector is the (j, i) entry of g aᵀ, the weight increment of the
    corollary. -/
theorem vecKron_rankOne {n m : ℕ} (a : Fin n → ℝ) (g : Fin m → ℝ)
    (i : Fin n) (j : Fin m) :
    vecKron a g (i, j) = g j * a i := mul_comm _ _

/-- The mixed-product property in vector form: the true Kronecker
    matrix acts factorwise on lifted vectors. -/
theorem kron_mulVec_vecKron {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin m) (Fin m) ℝ)
    (a : Fin n → ℝ) (g : Fin m → ℝ) :
    (A ⊗ₖ G).mulVec (vecKron a g)
      = vecKron (A.mulVec a) (G.mulVec g) := by
  funext p
  simp only [Matrix.mulVec, dotProduct, vecKron,
    Matrix.kroneckerMap_apply]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- cor:kfac_lift on true matrices: factor eigenpairs multiply, so
    the lifted vector a ⊗ g is an eigenvector of A ⊗ₖ G with
    eigenvalue α·γ. -/
theorem kron_eigen {n m : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin m) (Fin m) ℝ}
    {a : Fin n → ℝ} {g : Fin m → ℝ} {α γ : ℝ}
    (ha : A.mulVec a = α • a) (hg : G.mulVec g = γ • g) :
    (A ⊗ₖ G).mulVec (vecKron a g) = (α * γ) • vecKron a g := by
  rw [kron_mulVec_vecKron, ha, hg]
  funext p
  simp only [vecKron, Pi.smul_apply, smul_eq_mul]
  ring

/-- Transposes distribute over the Kronecker product. -/
lemma kron_transpose {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℝ)
    (G : Matrix (Fin b) (Fin b) ℝ) :
    (A ⊗ₖ G)ᵀ = Aᵀ ⊗ₖ Gᵀ :=
  Matrix.kroneckerMap_transpose _ A G

/-- Spectral exhaustiveness: the Kronecker product of two real
    symmetric matrices has the complete spectral decomposition with
    the lifted eigenvector matrix and the product eigenvalues on the
    product index. The lifted eigenpairs are all of the spectrum,
    with multiplicity. -/
theorem kron_spectral {a b : ℕ}
    {A : Matrix (Fin (a+1)) (Fin (a+1)) ℝ}
    {G : Matrix (Fin (b+1)) (Fin (b+1)) ℝ}
    (hA : A.IsHermitian) (hG : G.IsHermitian) :
    A ⊗ₖ G = (eigU hA ⊗ₖ eigU hG)
        * Matrix.diagonal (fun p : Fin (a+1) × Fin (b+1) =>
            hA.eigenvalues p.1 * hG.eigenvalues p.2)
        * (eigU hA ⊗ₖ eigU hG)ᵀ
      ∧ (eigU hA ⊗ₖ eigU hG)ᵀ * (eigU hA ⊗ₖ eigU hG) = 1 := by
  constructor
  · conv_lhs => rw [spectral_real hA, spectral_real hG]
    rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul,
      Matrix.diagonal_kronecker_diagonal, kron_transpose]
  · rw [kron_transpose, ← Matrix.mul_kronecker_mul,
      eigU_star_mul_self hA, eigU_star_mul_self hG,
      Matrix.one_kronecker_one]

end MatrixKron

section GlobalRate

/-! ### The quotient global rate (cor:global-rate), scalar model

The two-layer scalar product network at the symmetric point has raw
Fisher quadratic form t²(v₁ + v₂)²: rank one. The gauge direction
(1, −1) (the inner reparameterisation orbit) is null at every t, so
the raw parameter Fisher never attains the rate; the symmetric
horizontal direction reads the quotient eigenvalue 2t², the paper's
own value at L = 2, with leading rate 2(L−1) = 2. The per-block
minimum over same-rate blocks keeps the rate
(`HasLeadingRate.min_of_eq`). -/

/-- The raw two-layer Fisher quadratic form at the symmetric point,
    scalar model. -/
def gaugeQuad (t : ℝ) (v : Fin 2 → ℝ) : ℝ := t ^ 2 * (v 0 + v 1) ^ 2

/-- Every gauge-orbit direction is null at every t: the raw Fisher
    does not attain the rate at its smallest eigenvalue. -/
theorem gauge_null (t : ℝ) (v : Fin 2 → ℝ) (hv : v 0 + v 1 = 0) :
    gaugeQuad t v = 0 := by
  unfold gaugeQuad
  rw [hv]
  ring

/-- The gauge witness (1, −1) is a non-zero null direction. -/
theorem gauge_null_witness (t : ℝ) :
    gaugeQuad t ![1, -1] = 0 ∧ (![1, -1] : Fin 2 → ℝ) 0 ≠ 0 := by
  constructor
  · apply gauge_null
    norm_num
  · norm_num

/-- The horizontal (quotient) eigenvalue: the symmetric direction
    reads 2t², leading rate 2(L−1) = 2 with coefficient 2. -/
theorem horizontal_rate :
    HasLeadingRate (fun t => gaugeQuad t ![1, 1] / 2) 2 2 := by
  have h := (hasLeadingRate_pow 2).const_mul (2:ℝ)
  norm_num at h
  refine h.congr fun t => ?_
  unfold gaugeQuad
  norm_num
  ring

end GlobalRate

/-- rem:kfac_lift_crosslayer, the gauge ray: stepping one layer's
    dead row alone leaves the two-layer map unchanged for every step
    size, because the other layer contributes the factor zero. K is
    identically zero along the ray and no KL order exists there. -/
theorem gauge_ray_flat (w s : ℝ) :
    ((w + s) * 0 - w * 0) ^ 2 = 0 := by ring

end DeadDirections
