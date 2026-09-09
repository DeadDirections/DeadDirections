/-
  Variational σ_min from the spectral theorem (the SVD-milestone
  foundation).

  For a real square matrix A, the Gram matrix AᵀA is symmetric
  positive semidefinite, its eigenvalues are the squared singular
  values, and Mathlib's spectral theorem diagonalizes it by the
  eigenvector unitary. The change of variables w = Uᵀv turns the Gram
  quadratic form into a diagonal form in w with ‖w‖ = ‖v‖, so the
  smallest eigenvalue bounds ‖Av‖²/‖v‖² from below with attainment on
  the corresponding eigenvector column: the variational σ_min, with no
  singular value decomposition assembled. This is the machinery the
  general rectangular σ_min corollary, the mixing side of thm:bridge,
  and the residual family consume.
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import DeadDirections.DeepLinearBridge
import Mathlib.Algebra.Order.Chebyshev

namespace DeadDirections

open Matrix Filter Topology

variable {n : ℕ}

/-- Over ℝ the conjugate transpose is the transpose. -/
lemma conjTranspose_eq_transpose_real
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Aᴴ = Aᵀ := by
  ext i j
  simp [conjTranspose_apply]

/-- The Gram matrix AᵀA is Hermitian. -/
lemma gram_isHermitian (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    (Aᵀ * A).IsHermitian := by
  have h := isHermitian_conjTranspose_mul_self A
  rwa [conjTranspose_eq_transpose_real] at h

/-- The squared norm of Av is the Gram quadratic form at v. -/
lemma sq_sum_mulVec (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (v : Fin (n+1) → ℝ) :
    ∑ i, (A.mulVec v i) ^ 2 = v ⬝ᵥ ((Aᵀ * A).mulVec v) := by
  have h1 : ∑ i, (A.mulVec v i) ^ 2 = (A.mulVec v) ⬝ᵥ (A.mulVec v) := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => pow_two _
  have h2 : (A.mulVec v) ⬝ᵥ (A.mulVec v)
      = v ⬝ᵥ ((Aᵀ * A).mulVec v) := by
    rw [dotProduct_comm, dotProduct_mulVec]
    have h3 : (A.mulVec v) ᵥ* A = (Aᵀ * A).mulVec v := by
      rw [← Matrix.transpose_transpose A, Matrix.vecMul_transpose,
        Matrix.transpose_transpose, Matrix.mulVec_mulVec]
    rw [h3, dotProduct_comm]
  rw [h1, h2]

section Spectral

variable {S : Matrix (Fin (n+1)) (Fin (n+1)) ℝ} (hS : S.IsHermitian)

/-- The eigenvector unitary as a real matrix. -/
noncomputable def eigU (hS : S.IsHermitian) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  (hS.eigenvectorUnitary : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)

lemma eigU_star_mul_self : (eigU hS)ᵀ * eigU hS = 1 := by
  have h := Unitary.coe_star_mul_self hS.eigenvectorUnitary
  rw [Matrix.star_eq_conjTranspose,
    conjTranspose_eq_transpose_real] at h
  unfold eigU
  exact h

lemma eigU_mul_star_self : eigU hS * (eigU hS)ᵀ = 1 := by
  have h := Unitary.coe_mul_star_self hS.eigenvectorUnitary
  rw [Unitary.coe_star, Matrix.star_eq_conjTranspose,
    conjTranspose_eq_transpose_real] at h
  unfold eigU
  exact h

/-- The real spectral theorem in matrix form:
    S = U · diagonal(eigenvalues) · Uᵀ. -/
lemma spectral_real :
    S = eigU hS * Matrix.diagonal hS.eigenvalues * (eigU hS)ᵀ := by
  have h := hS.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  conv_lhs => rw [h]
  have hd : Matrix.diagonal (RCLike.ofReal ∘ hS.eigenvalues)
      = Matrix.diagonal hS.eigenvalues := rfl
  rw [hd]
  unfold eigU
  rw [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_real]

/-- The change of variables: the Hermitian quadratic form is the
    diagonal form in the rotated coordinates w = Uᵀv. -/
lemma hermitian_quadform_eq (v : Fin (n+1) → ℝ) :
    v ⬝ᵥ (S.mulVec v)
      = ∑ i, hS.eigenvalues i * (((eigU hS)ᵀ.mulVec v) i) ^ 2 := by
  conv_lhs => rw [spectral_real hS]
  have hsplit : (eigU hS * Matrix.diagonal hS.eigenvalues
        * (eigU hS)ᵀ).mulVec v
      = (eigU hS).mulVec ((Matrix.diagonal hS.eigenvalues).mulVec
        ((eigU hS)ᵀ.mulVec v)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hsplit, dotProduct_mulVec]
  have hvecmul : v ᵥ* eigU hS = (eigU hS)ᵀ.mulVec v := by
    rw [← Matrix.transpose_transpose (eigU hS),
      Matrix.vecMul_transpose, Matrix.transpose_transpose]
  rw [hvecmul]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Rotation preserves the sum of squares: ‖Uᵀv‖² = ‖v‖². -/
lemma rotated_sq_sum (v : Fin (n+1) → ℝ) :
    ∑ i, (((eigU hS)ᵀ.mulVec v) i) ^ 2 = ∑ i, v i ^ 2 := by
  have h1 : ∑ i, (((eigU hS)ᵀ.mulVec v) i) ^ 2
      = ((eigU hS)ᵀ.mulVec v) ⬝ᵥ ((eigU hS)ᵀ.mulVec v) := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => by rw [sq]
  have h2 : ((eigU hS)ᵀ.mulVec v) ⬝ᵥ ((eigU hS)ᵀ.mulVec v)
      = v ⬝ᵥ v := by
    rw [dotProduct_comm, dotProduct_mulVec]
    have h3 : ((eigU hS)ᵀ.mulVec v) ᵥ* (eigU hS)ᵀ
        = (eigU hS * (eigU hS)ᵀ).mulVec v := by
      rw [Matrix.vecMul_transpose, Matrix.mulVec_mulVec]
    rw [h3, eigU_mul_star_self, Matrix.one_mulVec]
  rw [h1, h2]
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [sq]

/-- The eigenvalue sandwich for the Hermitian quadratic form: the
    smallest and largest eigenvalues bound the Rayleigh quotient. -/
theorem hermitian_quadform_ge (lo : ℝ) (hlo : ∀ i, lo ≤ hS.eigenvalues i)
    (v : Fin (n+1) → ℝ) :
    lo * ∑ i, v i ^ 2 ≤ v ⬝ᵥ (S.mulVec v) := by
  rw [hermitian_quadform_eq hS v, ← rotated_sq_sum hS v]
  exact diag_quadform_ge _ _ hlo _

theorem hermitian_quadform_le (hi : ℝ) (hhi : ∀ i, hS.eigenvalues i ≤ hi)
    (v : Fin (n+1) → ℝ) :
    v ⬝ᵥ (S.mulVec v) ≤ hi * ∑ i, v i ^ 2 := by
  rw [hermitian_quadform_eq hS v, ← rotated_sq_sum hS v]
  exact diag_quadform_le _ _ hhi _

/-- The eigenvector column attains its eigenvalue: at v = U·e_j the
    quadratic form is exactly the j-th eigenvalue, at unit norm. -/
theorem hermitian_quadform_attained (j : Fin (n+1)) :
    (eigU hS).mulVec (Pi.single j 1)
        ⬝ᵥ (S.mulVec ((eigU hS).mulVec (Pi.single j 1)))
      = hS.eigenvalues j
    ∧ ∑ i, ((eigU hS).mulVec (Pi.single j 1) i) ^ 2 = 1 := by
  have hUe : (eigU hS)ᵀ.mulVec ((eigU hS).mulVec (Pi.single j 1))
      = Pi.single j 1 := by
    rw [Matrix.mulVec_mulVec, eigU_star_mul_self, Matrix.one_mulVec]
  constructor
  · rw [hermitian_quadform_eq hS, hUe, diag_quadform_single]
  · have h := rotated_sq_sum hS ((eigU hS).mulVec (Pi.single j 1))
    rw [hUe] at h
    rw [← h]
    have hterm : ∀ i : Fin (n+1),
        ((Pi.single j 1 : Fin (n+1) → ℝ) i) ^ 2
        = if i = j then (1:ℝ) else 0 := by
      intro i
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      Finset.sum_ite_eq' Finset.univ j fun _ => (1:ℝ)]
    simp

end Spectral

/-! ### The variational σ_min -/

/-- The squared smallest singular value: the smallest eigenvalue of
    the Gram matrix. -/
noncomputable def sigmaMinSq (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : ℝ :=
  Finset.univ.inf' ⟨Fin.last n, Finset.mem_univ _⟩
    (gram_isHermitian A).eigenvalues

lemma sigmaMinSq_le_eigenvalues (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (i : Fin (n+1)) :
    sigmaMinSq A ≤ (gram_isHermitian A).eigenvalues i :=
  Finset.inf'_le _ (Finset.mem_univ i)

/-- The variational lower bound: σ_min² · ‖v‖² ≤ ‖Av‖² at every v. -/
theorem sigmaMinSq_le_sq_sum (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (v : Fin (n+1) → ℝ) :
    sigmaMinSq A * ∑ i, v i ^ 2 ≤ ∑ i, (A.mulVec v i) ^ 2 := by
  rw [sq_sum_mulVec]
  exact hermitian_quadform_ge (gram_isHermitian A) _
    (sigmaMinSq_le_eigenvalues A) v

/-- The bound is attained: some unit vector realises σ_min² exactly,
    so the variational minimum of ‖Av‖² over the unit sphere equals
    the smallest Gram eigenvalue. -/
theorem sigmaMinSq_attained (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    ∃ v : Fin (n+1) → ℝ, (∑ i, v i ^ 2 = 1)
      ∧ ∑ i, (A.mulVec v i) ^ 2 = sigmaMinSq A := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf'
    (⟨Fin.last n, Finset.mem_univ _⟩ :
      (Finset.univ : Finset (Fin (n+1))).Nonempty)
    (gram_isHermitian A).eigenvalues
  obtain ⟨hval, hnorm⟩ :=
    hermitian_quadform_attained (gram_isHermitian A) j
  refine ⟨(eigU (gram_isHermitian A)).mulVec (Pi.single j 1),
    hnorm, ?_⟩
  rw [sq_sum_mulVec, hval, sigmaMinSq, hj]

/-- σ_min² is non-negative: it is an attained value of a sum of
    squares. -/
lemma sigmaMinSq_nonneg (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    0 ≤ sigmaMinSq A := by
  obtain ⟨v, _, hv2⟩ := sigmaMinSq_attained A
  rw [← hv2]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-! ### The mixing bounds

An arbitrary live mixing layer changes the dead rate's constant and
never the exponent: the product's σ_min² is squeezed between
σ_min²(A)·σ_min²(B) (supermultiplicativity, below at
`le_sigmaMinSq_mul`) and σ_max²(A)·σ_min²(B) (the cap here), so any
fixed invertible A preserves the Θ-class of σ_min²(B(t)). -/

/-- The squared largest singular value: the largest eigenvalue of
    the Gram matrix. -/
noncomputable def sigmaMaxSq (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : ℝ :=
  Finset.univ.sup' ⟨Fin.last n, Finset.mem_univ _⟩
    (gram_isHermitian A).eigenvalues

lemma eigenvalues_le_sigmaMaxSq (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (i : Fin (n+1)) :
    (gram_isHermitian A).eigenvalues i ≤ sigmaMaxSq A :=
  Finset.le_sup' _ (Finset.mem_univ i)

/-- The variational upper bound: ‖Av‖² ≤ σ_max²·‖v‖² at every v. -/
theorem sq_sum_le_sigmaMaxSq (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (v : Fin (n+1) → ℝ) :
    ∑ i, (A.mulVec v i) ^ 2 ≤ sigmaMaxSq A * ∑ i, v i ^ 2 := by
  rw [sq_sum_mulVec]
  exact hermitian_quadform_le (gram_isHermitian A) _
    (eigenvalues_le_sigmaMaxSq A) v

/-- The mixing cap: σ_min²(AB) ≤ σ_max²(A)·σ_min²(B), through B's
    attaining vector. -/
theorem sigmaMinSq_mul_le (A B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    sigmaMinSq (A * B) ≤ sigmaMaxSq A * sigmaMinSq B := by
  obtain ⟨w, hw1, hw2⟩ := sigmaMinSq_attained B
  have h1 := sigmaMinSq_le_sq_sum (A * B) w
  rw [hw1, mul_one] at h1
  have h2 : (A * B).mulVec w = A.mulVec (B.mulVec w) :=
    (Matrix.mulVec_mulVec w A B).symm
  have h3 := sq_sum_le_sigmaMaxSq A (B.mulVec w)
  rw [hw2] at h3
  calc sigmaMinSq (A * B) ≤ ∑ i, ((A * B).mulVec w i) ^ 2 := h1
    _ = ∑ i, (A.mulVec (B.mulVec w) i) ^ 2 := by rw [h2]
    _ ≤ sigmaMaxSq A * sigmaMinSq B := h3

/-- σ_min² is positive at invertible matrices: the attaining unit
    vector cannot be annihilated. -/
theorem sigmaMinSq_pos_of_unit (A : (Matrix (Fin (n+1)) (Fin (n+1)) ℝ)ˣ) :
    0 < sigmaMinSq (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) := by
  rcases lt_or_eq_of_le (sigmaMinSq_nonneg
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) with h | h
  · exact h
  · exfalso
    obtain ⟨v, hv1, hv2⟩ := sigmaMinSq_attained
      (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    rw [← h] at hv2
    have hAv : (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ).mulVec v
        = 0 := by
      funext i
      have hterm := Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ Finset.univ) => sq_nonneg
          ((A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ).mulVec v j))
        |>.mp hv2 i (Finset.mem_univ i)
      exact pow_eq_zero_iff (two_ne_zero) |>.mp hterm
    have hv0 : v = 0 := by
      have h2 := congrArg
        ((A⁻¹ : (Matrix (Fin (n+1)) (Fin (n+1)) ℝ)ˣ) :
          Matrix (Fin (n+1)) (Fin (n+1)) ℝ).mulVec hAv
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    rw [hv0] at hv1
    simp at hv1

/-- The Θ comparison through any invertible mixing matrix: the
    squared reading is sandwiched between σ_min² and σ_max² times
    the squared input, both sides deterministic in the input, so the
    comparison survives every expectation. The attn_VO_invariant
    non-degeneracy with the constant named. -/
theorem mixing_theta_comparison
    (A : (Matrix (Fin (n+1)) (Fin (n+1)) ℝ)ˣ)
    (Δ : Fin (n+1) → ℝ) :
    sigmaMinSq ((A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)ᵀ)
        * ∑ i, Δ i ^ 2
      ≤ ∑ i, (((A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)ᵀ).mulVec Δ
          i) ^ 2
    ∧ ∑ i, (((A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)ᵀ).mulVec Δ
          i) ^ 2
      ≤ sigmaMaxSq ((A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)ᵀ)
        * ∑ i, Δ i ^ 2 :=
  ⟨sigmaMinSq_le_sq_sum _ Δ, sq_sum_le_sigmaMaxSq _ Δ⟩

/-- The Schur bound at non-diagonal moments, Cauchy-Schwarz-free:
    the dead reading of a block quadratic form survives the cross
    moments up to the correction ‖b‖²/c, by per-coordinate weighted
    AM-GM against the live floor. -/
theorem schur_dead_lower {c : ℝ} (hc : 0 < c) (g : ℝ)
    (b : Fin (n+1) → ℝ) (Qlive : (Fin (n+1) → ℝ) → ℝ)
    (hlive : ∀ w, c * ∑ i, w i ^ 2 ≤ Qlive w)
    (v₀ : ℝ) (w : Fin (n+1) → ℝ) :
    (g - (∑ i, b i ^ 2) / c) * v₀ ^ 2
      ≤ g * v₀ ^ 2 + 2 * v₀ * (∑ i, b i * w i) + Qlive w := by
  have hsum : -(v₀ ^ 2 * ∑ i, b i ^ 2)
      - c ^ 2 * ∑ i, w i ^ 2
      ≤ 2 * c * v₀ * ∑ i, b i * w i := by
    have hterm : ∀ i : Fin (n+1),
        -(v₀ ^ 2 * b i ^ 2) - c ^ 2 * w i ^ 2
        ≤ 2 * c * v₀ * (b i * w i) := fun i => by
      nlinarith [sq_nonneg (v₀ * b i + c * w i)]
    calc -(v₀ ^ 2 * ∑ i, b i ^ 2) - c ^ 2 * ∑ i, w i ^ 2
        = ∑ i, (-(v₀ ^ 2 * b i ^ 2) - c ^ 2 * w i ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
            ← Finset.sum_sub_distrib]
      _ ≤ ∑ i, 2 * c * v₀ * (b i * w i) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = 2 * c * v₀ * ∑ i, b i * w i := by
          rw [Finset.mul_sum]
  have hlive' : c * (c * ∑ i, w i ^ 2) ≤ c * Qlive w :=
    mul_le_mul_of_nonneg_left (hlive w) hc.le
  have key : (c * g - ∑ i, b i ^ 2) * v₀ ^ 2
      ≤ c * (g * v₀ ^ 2 + 2 * v₀ * (∑ i, b i * w i) + Qlive w) := by
    nlinarith [hsum, hlive']
  have heq : (g - (∑ i, b i ^ 2) / c) * v₀ ^ 2
      = ((c * g - ∑ i, b i ^ 2) * v₀ ^ 2) / c := by
    field_simp
  rw [heq, div_le_iff₀ hc]
  calc (c * g - ∑ i, b i ^ 2) * v₀ ^ 2
      ≤ c * (g * v₀ ^ 2 + 2 * v₀ * (∑ i, b i * w i) + Qlive w) :=
        key
    _ = (g * v₀ ^ 2 + 2 * v₀ * (∑ i, b i * w i) + Qlive w) * c := by
        ring

/-! ### Consumers: the canonical chain and orthogonal invariance -/

/-- The squeeze characterization: any constant that bounds the form
    from below at every vector and is attained on the unit sphere is
    σ_min². -/
theorem sigmaMinSq_eq_of_bounds (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    {c : ℝ}
    (hle : ∀ v : Fin (n+1) → ℝ,
      c * ∑ i, v i ^ 2 ≤ ∑ i, (A.mulVec v i) ^ 2)
    (hatt : ∃ v : Fin (n+1) → ℝ, (∑ i, v i ^ 2 = 1)
      ∧ ∑ i, (A.mulVec v i) ^ 2 = c) :
    sigmaMinSq A = c := by
  obtain ⟨v, hv1, hv2⟩ := hatt
  obtain ⟨w, hw1, hw2⟩ := sigmaMinSq_attained A
  have h1 : sigmaMinSq A ≤ c := by
    have h := sigmaMinSq_le_sq_sum A v
    rw [hv1, mul_one, hv2] at h
    exact h
  have h2 : c ≤ sigmaMinSq A := by
    have h := hle w
    rw [hw1, mul_one, hw2] at h
    exact h
  linarith

lemma single_sq_sum_last :
    ∑ i, ((Pi.single (Fin.last n) 1 : Fin (n+1) → ℝ) i) ^ 2 = 1 := by
  have hterm : ∀ i : Fin (n+1),
      ((Pi.single (Fin.last n) 1 : Fin (n+1) → ℝ) i) ^ 2
      = if i = Fin.last n then (1:ℝ) else 0 := by
    intro i
    by_cases hi : i = Fin.last n
    · subst hi
      simp
    · simp [hi]
  rw [Finset.sum_congr rfl fun i _ => hterm i,
    Finset.sum_ite_eq' Finset.univ (Fin.last n) fun _ => (1:ℝ)]
  simp

/-- cor:rect_product_sigma_min, canonical instance as a genuine
    σ_min: the variational minimum of the canonical chain is t^{2p}
    exactly, for t ∈ [0, 1]. -/
theorem sigmaMinSq_canonical {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (p : ℕ) :
    sigmaMinSq (canonicalLayer n t ^ p) = t ^ (2 * p) :=
  sigmaMinSq_eq_of_bounds _
    (fun v => canonical_sigma_min_lower ht0 ht1 p v)
    ⟨Pi.single (Fin.last n) 1, single_sq_sum_last,
      canonical_sigma_min_attained t p⟩

/-- Orthogonal maps preserve the sum of squares. -/
lemma orthogonal_mulVec_sq_sum (U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hU : Uᵀ * U = 1) (y : Fin (n+1) → ℝ) :
    ∑ i, (U.mulVec y i) ^ 2 = ∑ i, y i ^ 2 := by
  rw [sq_sum_mulVec U y, hU, Matrix.one_mulVec]
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun i _ => (pow_two _).symm

/-- σ_min² is invariant under orthogonal conjugation: the mixing
    side of the bridge sees the same variational minimum as the
    canonical form. -/
theorem sigmaMinSq_conjugate (U A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) :
    sigmaMinSq (U * A * Uᵀ) = sigmaMinSq A := by
  have hUT : (Uᵀ)ᵀ * Uᵀ = 1 := by
    rw [Matrix.transpose_transpose]
    exact hU'
  apply sigmaMinSq_eq_of_bounds
  · intro v
    have hsplit : (U * A * Uᵀ).mulVec v
        = U.mulVec (A.mulVec (Uᵀ.mulVec v)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hsplit, orthogonal_mulVec_sq_sum U hU]
    have hnormT : ∑ i, (Uᵀ.mulVec v i) ^ 2 = ∑ i, v i ^ 2 :=
      orthogonal_mulVec_sq_sum Uᵀ hUT v
    calc sigmaMinSq A * ∑ i, v i ^ 2
        = sigmaMinSq A * ∑ i, (Uᵀ.mulVec v i) ^ 2 := by rw [hnormT]
      _ ≤ ∑ i, (A.mulVec (Uᵀ.mulVec v) i) ^ 2 :=
          sigmaMinSq_le_sq_sum A _
  · obtain ⟨w, hw1, hw2⟩ := sigmaMinSq_attained A
    refine ⟨U.mulVec w, ?_, ?_⟩
    · rw [orthogonal_mulVec_sq_sum U hU, hw1]
    · have hval : (U * A * Uᵀ).mulVec (U.mulVec w)
          = U.mulVec (A.mulVec w) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (U * A) Uᵀ U, hU,
          Matrix.mul_one, ← Matrix.mulVec_mulVec]
      rw [hval, orthogonal_mulVec_sq_sum U hU, hw2]

/-- The rotated configuration's σ_min: at every orthogonal U the
    conjugated canonical chain has variational minimum t^{2p}
    exactly. The mixing rotation moves nothing. -/
theorem sigmaMinSq_rotated_canonical
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (p : ℕ) :
    sigmaMinSq (U * canonicalLayer n t ^ p * Uᵀ) = t ^ (2 * p) := by
  rw [sigmaMinSq_conjugate U _ hU hU', sigmaMinSq_canonical ht0 ht1]

/-! ### The residual family (cor:sigma-min-res)

The identity skip floors the stream. Per sample: when the branch does
not anti-align with the stream (the no-cancellation pairing
Σᵢ xᵢ·fᵢ ≥ 0), the sum of squares of x + f is at least that of x, and
the floor telescopes along any residual chain. At the operator level:
σ_min² is supermultiplicative on products, a residual block 1 + B with
positive-semidefinite pairing has σ_min² ≥ 1, and a chain of such
blocks keeps σ_min² ≥ 1 at every depth: the depth-invariance profile
σ_min(X_ℓ)/σ_min(X_0) ≥ 1 with the mechanism exact. -/

/-- Operator-norm perturbation from entrywise bounds: a matrix with
    every entry at most ε in absolute value moves any quadratic form
    by at most ε·(n+1)·‖v‖². -/
theorem quadform_entrywise_bound
    (E : Fin (n+1) → Fin (n+1) → ℝ) {ε : ℝ}
    (hE : ∀ i j, |E i j| ≤ ε) (v : Fin (n+1) → ℝ) :
    |∑ i, ∑ j, E i j * v i * v j|
      ≤ ε * (n+1) * ∑ i, v i ^ 2 := by
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) (hE 0 0)
  have habs : |∑ i, ∑ j, E i j * v i * v j|
      ≤ ∑ i, ∑ j, |E i j| * |v i| * |v j| := by
    calc |∑ i, ∑ j, E i j * v i * v j|
        ≤ ∑ i, |∑ j, E i j * v i * v j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |E i j * v i * v j| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, ∑ j, |E i j| * |v i| * |v j| := by
          simp [abs_mul]
  have hstep : (∑ i, ∑ j, |E i j| * |v i| * |v j|)
      ≤ ε * (∑ i, |v i|) ^ 2 := by
    have hterm : ∀ i, (∑ j, |E i j| * |v i| * |v j|)
        ≤ ε * |v i| * ∑ j, |v j| := by
      intro i
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have h1 : |E i j| * |v i| ≤ ε * |v i| :=
        mul_le_mul_of_nonneg_right (hE i j) (abs_nonneg _)
      exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    calc (∑ i, ∑ j, |E i j| * |v i| * |v j|)
        ≤ ∑ i, ε * |v i| * ∑ j, |v j| :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = ε * (∑ i, |v i|) ^ 2 := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, sq]
          ring
  have hcs : (∑ i, |v i|) ^ 2 ≤ (n+1) * ∑ i, v i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin (n+1)))) (f := fun i => |v i|)
    simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at h
    exact_mod_cast h
  calc |∑ i, ∑ j, E i j * v i * v j|
      ≤ ε * (∑ i, |v i|) ^ 2 := le_trans habs hstep
    _ ≤ ε * ((n+1) * ∑ i, v i ^ 2) :=
        mul_le_mul_of_nonneg_left hcs hε0
    _ = ε * (n+1) * ∑ i, v i ^ 2 := by ring

/-- The assembled Fisher slice: the block form with any perturbation
    of entrywise size ε is bounded below by the Schur complement of
    the live block minus the perturbation cost. Combines
    schur_dead_lower with quadform_entrywise_bound. -/
theorem assembled_schur_slice {c : ℝ} (hc : 0 < c) (g : ℝ)
    (b : Fin (n+1) → ℝ) (Qlive : (Fin (n+1) → ℝ) → ℝ)
    (hlive : ∀ w, c * ∑ i, w i ^ 2 ≤ Qlive w)
    {ε : ℝ} (v₀ : ℝ) (w : Fin (n+1) → ℝ) {QE : ℝ}
    (hQE : |QE| ≤ ε * (v₀ ^ 2 + ∑ i, w i ^ 2)) :
    (g - (∑ i, b i ^ 2) / c) * v₀ ^ 2
        - ε * (v₀ ^ 2 + ∑ i, w i ^ 2)
      ≤ g * v₀ ^ 2 + 2 * v₀ * (∑ i, b i * w i) + Qlive w + QE := by
  have h := schur_dead_lower hc g b Qlive hlive v₀ w
  have h2 := (abs_le.mp hQE).1
  linarith


/-- The weighted Schur bound: the block form dominates
    (g/2)·v₀² + (c − 2‖b‖²/g)·‖w‖², the cross term absorbed by AM-GM
    at weight g and Cauchy–Schwarz on the pairing. -/
theorem block_form_lower_weighted {c g : ℝ} (hg : 0 < g)
    (b : Fin (n+1) → ℝ) (Qlive : (Fin (n+1) → ℝ) → ℝ)
    (hlive : ∀ w, c * ∑ i, w i ^ 2 ≤ Qlive w)
    (v₀ : ℝ) (w : Fin (n+1) → ℝ) :
    (g / 2) * v₀ ^ 2 + (c - 2 * (∑ i, b i ^ 2) / g) * ∑ i, w i ^ 2
      ≤ g * v₀ ^ 2 + 2 * v₀ * (∑ i, b i * w i) + Qlive w := by
  set s := ∑ i, b i * w i with hs
  set B := ∑ i, b i ^ 2 with hB
  set W := ∑ i, w i ^ 2 with hW
  have hcs : s ^ 2 ≤ B * W := by
    rw [hs, hB, hW]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hamgm : -(g / 2) * v₀ ^ 2 - (2 / g) * s ^ 2 ≤ 2 * v₀ * s := by
    have h : 0 ≤ (g * v₀ + 2 * s) ^ 2 / (2 * g) := by positivity
    have heq : (g * v₀ + 2 * s) ^ 2 / (2 * g)
        = (g / 2) * v₀ ^ 2 + 2 * v₀ * s + (2 / g) * s ^ 2 := by
      field_simp
      ring
    linarith
  have hcross : (2 / g) * s ^ 2 ≤ (2 / g) * (B * W) :=
    mul_le_mul_of_nonneg_left hcs (by positivity)
  have hl := hlive w
  rw [← hW] at hl
  have hfinal : (c - 2 * B / g) * W = c * W - (2 / g) * (B * W) := by
    ring
  rw [hfinal]
  linarith

/-- The two-block rate sandwich behind thm:selection_rule (a) and (b):
    an entry g of leading rate q against a block with floor c of
    leading rate p < q and cross entries of squared norm B at rate
    p + q, with the Schur-type margin 2β/d < a. Eventually the whole
    form dominates (g/2)·‖v‖², so the variational minimum sits between
    g/2 and the axis value g: the entry's own rate q. -/
theorem block_lambda_min_sandwich {p q : ℕ} (hpq : p < q)
    {g B c : ℝ → ℝ} {d a β : ℝ}
    (hg : HasLeadingRate g q d) (hd : 0 < d)
    (hc : HasLeadingRate c p a)
    (hB : HasLeadingRate B (p + q) β) (hcond : 2 * β / d < a)
    (b : ℝ → Fin (n+1) → ℝ) (hb : ∀ t, ∑ i, b t i ^ 2 = B t)
    (Qlive : ℝ → (Fin (n+1) → ℝ) → ℝ)
    (hlive : ∀ t w, c t * ∑ i, w i ^ 2 ≤ Qlive t w) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ (v₀ : ℝ) (w : Fin (n+1) → ℝ),
      (g t / 2) * (v₀ ^ 2 + ∑ i, w i ^ 2)
        ≤ g t * v₀ ^ 2 + 2 * v₀ * (∑ i, b t i * w i) + Qlive t w := by
  have hBg : HasLeadingRate (fun t => B t / g t) p (β / d) := by
    have h := hB.div hg hd (by omega)
    rwa [show p + q - q = p from by omega] at h
  have h2 : HasLeadingRate (fun t => -2 * (B t / g t)) p (-2 * (β / d)) :=
    HasLeadingRate.const_mul hBg (-2)
  have hsum : HasLeadingRate (fun t => c t + -2 * (B t / g t)) p
      (a + -2 * (β / d)) :=
    hc.add_of_eq h2
  have hhalf : HasLeadingRate (fun t => g t / 2) q (1 / 2 * d) := by
    have h := HasLeadingRate.const_mul hg (1 / 2)
    refine h.congr fun t => ?_
    ring
  have hmargin : HasLeadingRate
      (fun t => c t + -2 * (B t / g t) - g t / 2) p (a + -2 * (β / d)) :=
    hsum.sub_of_lt hhalf hpq
  have hpos : 0 < a + -2 * (β / d) := by
    have : 2 * β / d = 2 * (β / d) := by ring
    linarith
  filter_upwards [hmargin.eventually_pos hpos, hg.eventually_pos hd]
    with t hm hgt
  intro v₀ w
  have hlow := block_form_lower_weighted (n := n) hgt (b t) (Qlive t)
    (hlive t) v₀ w
  rw [hb t] at hlow
  have hW0 : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcoef : g t / 2 ≤ c t - 2 * B t / g t := by
    have e : 2 * B t / g t = 2 * (B t / g t) := by ring
    linarith
  have hmono : (g t / 2) * ∑ i, w i ^ 2
      ≤ (c t - 2 * B t / g t) * ∑ i, w i ^ 2 :=
    mul_le_mul_of_nonneg_right hcoef hW0
  linarith

/-- thm:selection_rule (a), model form: against a Θ(1) live block the
    transversal entry of rate 2(k−1) sets the rate of the variational
    minimum. -/
theorem selection_rule_transversal_lower {k : ℕ} (hk : 2 ≤ k)
    {g B : ℝ → ℝ} {cF β c : ℝ}
    (hg : HasLeadingRate g (2 * (k - 1)) cF) (hcF : 0 < cF)
    (hB : HasLeadingRate B (2 * (k - 1)) β) (hcond : 2 * β / cF < c)
    (b : ℝ → Fin (n+1) → ℝ) (hb : ∀ t, ∑ i, b t i ^ 2 = B t)
    (Qlive : ℝ → (Fin (n+1) → ℝ) → ℝ)
    (hlive : ∀ t w, c * ∑ i, w i ^ 2 ≤ Qlive t w) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ (v₀ : ℝ) (w : Fin (n+1) → ℝ),
      (g t / 2) * (v₀ ^ 2 + ∑ i, w i ^ 2)
        ≤ g t * v₀ ^ 2 + 2 * v₀ * (∑ i, b t i * w i) + Qlive t w := by
  have hB' : HasLeadingRate B (0 + 2 * (k - 1)) β := by
    rwa [zero_add]
  exact block_lambda_min_sandwich (by omega) hg hcF
    (hasLeadingRate_const c) hB' hcond b hb Qlive hlive

/-- thm:selection_rule (b), model form: a tangential entry of rate
    2j₂ against a block of rate 2j₁ < 2j₂ with cross entries at order
    j₁ + j₂ keeps its own eigenvalue rate; the (G⁺)-type margin
    2β/d < a keeps the Schur complement positive. -/
theorem selection_rule_tangential_lower {j₁ j₂ : ℕ} (hj : j₁ < j₂)
    {g B c : ℝ → ℝ} {d a β : ℝ}
    (hg : HasLeadingRate g (2 * j₂) d) (hd : 0 < d)
    (hc : HasLeadingRate c (2 * j₁) a)
    (hB : HasLeadingRate B (2 * (j₁ + j₂)) β) (hcond : 2 * β / d < a)
    (b : ℝ → Fin (n+1) → ℝ) (hb : ∀ t, ∑ i, b t i ^ 2 = B t)
    (Qlive : ℝ → (Fin (n+1) → ℝ) → ℝ)
    (hlive : ∀ t w, c t * ∑ i, w i ^ 2 ≤ Qlive t w) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ (v₀ : ℝ) (w : Fin (n+1) → ℝ),
      (g t / 2) * (v₀ ^ 2 + ∑ i, w i ^ 2)
        ≤ g t * v₀ ^ 2 + 2 * v₀ * (∑ i, b t i * w i) + Qlive t w := by
  have hB' : HasLeadingRate B (2 * j₁ + 2 * j₂) β := by
    rwa [show 2 * j₁ + 2 * j₂ = 2 * (j₁ + j₂) from by ring]
  exact block_lambda_min_sandwich (by omega) hg hd hc hB' hcond b hb
    Qlive hlive

/-- The axis value: on the unit vector along the entry's coordinate
    the form equals the entry itself, the upper end of the sandwich. -/
theorem block_form_dead_axis (g : ℝ) (b : Fin (n+1) → ℝ)
    (Qlive : (Fin (n+1) → ℝ) → ℝ) (h0 : Qlive 0 = 0) :
    g * (1:ℝ) ^ 2 + 2 * 1 * (∑ i, b i * (0 : Fin (n+1) → ℝ) i)
      + Qlive 0 = g := by
  simp [h0]


/-- cor:res_lambda_min's caveat: a null direction of the live
    complement (a gauge zero, or tied shortest paths with linearly
    dependent products) is a zero of the whole block form, so the
    variational minimum reads zero whatever the dead entry does. -/
theorem complement_zero_caveat (g : ℝ) (b : Fin (n+1) → ℝ)
    (Qlive : (Fin (n+1) → ℝ) → ℝ) (w₀ : Fin (n+1) → ℝ)
    (hw₀ : Qlive w₀ = 0) :
    g * (0:ℝ) ^ 2 + 2 * 0 * (∑ i, b i * w₀ i) + Qlive w₀ = 0 := by
  simp [hw₀]

/-- prop:task_expansion_gfactor with the perturbation term: a diagonal
    block with entries in [lo, hi] plus an entrywise perturbation of
    size ε keeps the quadratic form within
    [lo − ε(n+1), hi + ε(n+1)]·‖v‖², the operator-norm form of the
    sandwich. -/
theorem task_expansion_perturbed (d : Fin (n+1) → ℝ) {lo hi : ℝ}
    (hlo : ∀ i, lo ≤ d i) (hhi : ∀ i, d i ≤ hi)
    (E : Fin (n+1) → Fin (n+1) → ℝ) {ε : ℝ} (hE : ∀ i j, |E i j| ≤ ε)
    (v : Fin (n+1) → ℝ) :
    (lo - ε * (n+1)) * ∑ i, v i ^ 2
        ≤ ∑ i, d i * v i ^ 2 + ∑ i, ∑ j, E i j * v i * v j
    ∧ ∑ i, d i * v i ^ 2 + ∑ i, ∑ j, E i j * v i * v j
        ≤ (hi + ε * (n+1)) * ∑ i, v i ^ 2 := by
  have hq := quadform_entrywise_bound E hE v
  have hq1 := (abs_le.mp hq).1
  have hq2 := (abs_le.mp hq).2
  have hd1 : lo * ∑ i, v i ^ 2 ≤ ∑ i, d i * v i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hlo i) (sq_nonneg _)
  have hd2 : ∑ i, d i * v i ^ 2 ≤ hi * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hhi i) (sq_nonneg _)
  constructor <;> nlinarith [hq1, hq2, hd1, hd2]

/-- thm:selection_rule (b), the eigenvector clause at the two-block
    model: for the symmetric block [[A, B], [B, D]] with D < A, any
    eigenvalue λ ≤ D has the eigenvector (B, λ − A), whose tilt toward
    the first axis is at most |B|/(A − D). As the cross entry vanishes
    the eigenvector converges to the second axis. -/
theorem two_by_two_eigvec_tilt {A B D lam : ℝ}
    (hchar : lam ^ 2 - (A + D) * lam + (A * D - B ^ 2) = 0)
    (hlam : lam ≤ D) (hAD : D < A) :
    (A * B + B * (lam - A) = lam * B
      ∧ B * B + D * (lam - A) = lam * (lam - A))
    ∧ |B| / |lam - A| ≤ |B| / (A - D) := by
  refine ⟨⟨by ring, by linear_combination (-1 : ℝ) * hchar⟩, ?_⟩
  have h1 : A - D ≤ |lam - A| := by
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  exact div_le_div_of_nonneg_left (abs_nonneg B) (by linarith) h1

/-- cor:rect_product_sigma_min's general composed-complement case,
    the distance-to-image argument: if the complement's image keeps
    a positive angle from the dead output direction,
    |⟨e, Bw⟩| ≤ (1 − ρ)‖Bw‖, and the complement map has floor c, then
    the composed map's squared norm on (v₀, w) is at least
    ρ·min(a², c²)·‖(v₀, w)‖² where a is the narrow block's scalar: the
    narrow chain's t^{2L} survives the complement exactly when the
    complement cannot occupy the vacated direction. -/
theorem distance_to_image_lower {a c ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) (v₀ : ℝ) (y : Fin (n+1) → ℝ) (e : Fin (n+1) → ℝ)
    (he : ∑ i, e i ^ 2 = 1)
    (hangle : |∑ i, e i * y i| ≤ (1 - ρ) * Real.sqrt (∑ i, y i ^ 2))
    (w : Fin (n+1) → ℝ) (hfloor : c ^ 2 * ∑ i, w i ^ 2 ≤ ∑ i, y i ^ 2) :
    ρ * min (a ^ 2) (c ^ 2) * (v₀ ^ 2 + ∑ i, w i ^ 2)
      ≤ ∑ i, (a * v₀ * e i + y i) ^ 2 := by
  set Y := ∑ i, y i ^ 2 with hY
  set s := ∑ i, e i * y i with hs
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hexp : ∑ i, (a * v₀ * e i + y i) ^ 2
      = (a * v₀) ^ 2 + 2 * (a * v₀) * s + Y := by
    have h' : ∑ i, (a * v₀ * e i + y i) ^ 2
        = (a * v₀) ^ 2 * (∑ i, e i ^ 2) + 2 * (a * v₀) * (∑ i, e i * y i)
          + ∑ i, y i ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h', he, mul_one]
  rw [hexp]
  have hsq : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY0
  have hsqrt0 : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg _
  -- the cross term is absorbed by AM-GM at weight one
  have hcross : -(2 * (a * v₀) * s) ≤ (1 - ρ) * ((a * v₀) ^ 2 + Y) := by
    have h1 : |2 * (a * v₀) * s| ≤ 2 * |a * v₀| * ((1 - ρ) * Real.sqrt Y) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left hangle (by positivity)
    have h2 : 2 * |a * v₀| * Real.sqrt Y ≤ (a * v₀) ^ 2 + Y := by
      nlinarith [sq_nonneg (|a * v₀| - Real.sqrt Y), sq_abs (a * v₀), hsq]
    have h3 := neg_abs_le (2 * (a * v₀) * s)
    have h4 : 2 * |a * v₀| * ((1 - ρ) * Real.sqrt Y)
        = (1 - ρ) * (2 * |a * v₀| * Real.sqrt Y) := by ring
    have hρ' : 0 ≤ 1 - ρ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hρ']
  have hmin1 : min (a ^ 2) (c ^ 2) * v₀ ^ 2 ≤ (a * v₀) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
  have hmin2 : min (a ^ 2) (c ^ 2) * ∑ i, w i ^ 2 ≤ Y := by
    calc min (a ^ 2) (c ^ 2) * ∑ i, w i ^ 2 ≤ c ^ 2 * ∑ i, w i ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_right _ _)
            (Finset.sum_nonneg fun i _ => sq_nonneg _)
      _ ≤ Y := hfloor
  nlinarith [hcross, hmin1, hmin2]

section Residual

/-- Per-sample floor: a residual step with non-negative pairing does
    not shrink the stream. -/
theorem residual_sq_sum_ge (x f : Fin (n+1) → ℝ)
    (hnc : 0 ≤ ∑ i, x i * f i) :
    ∑ i, x i ^ 2 ≤ ∑ i, (x i + f i) ^ 2 := by
  have hexp : ∑ i, (x i + f i) ^ 2
      = ∑ i, x i ^ 2 + 2 * ∑ i, x i * f i + ∑ i, f i ^ 2 := by
    rw [Finset.sum_congr rfl fun i _ =>
      (show (x i + f i) ^ 2 = x i ^ 2 + 2 * (x i * f i) + f i ^ 2
        from by ring),
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  rw [hexp]
  have hf2 : 0 ≤ ∑ i, f i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

/-- The floor telescopes: along a residual trajectory with
    no-cancellation at every step, the stream's sum of squares is
    monotone in depth. -/
theorem residual_chain_sq_sum_ge (X f : ℕ → Fin (n+1) → ℝ)
    (hstep : ∀ ℓ, X (ℓ+1) = X ℓ + f ℓ)
    (hnc : ∀ ℓ, 0 ≤ ∑ i, X ℓ i * f ℓ i) (L : ℕ) :
    ∑ i, X 0 i ^ 2 ≤ ∑ i, X L i ^ 2 := by
  induction L with
  | zero => exact le_refl _
  | succ m ih =>
    refine le_trans ih ?_
    have h := residual_sq_sum_ge (X m) (f m) (hnc m)
    have hXm : X (m+1) = fun i => X m i + f m i := by
      rw [hstep m]
      rfl
    rw [hXm]
    exact h

/-- σ_min² of the identity is one. -/
lemma sigmaMinSq_one : sigmaMinSq (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    = 1 := by
  apply sigmaMinSq_eq_of_bounds
  · intro v
    rw [Matrix.one_mulVec, one_mul]
  · exact ⟨Pi.single (Fin.last n) 1, single_sq_sum_last, by
      rw [Matrix.one_mulVec]
      exact single_sq_sum_last⟩

/-- σ_min² is supermultiplicative on products. -/
theorem le_sigmaMinSq_mul (A B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    sigmaMinSq A * sigmaMinSq B ≤ sigmaMinSq (A * B) := by
  obtain ⟨w, hw1, hw2⟩ := sigmaMinSq_attained (A * B)
  rw [← hw2]
  have h1 : sigmaMinSq A * sigmaMinSq B
      = sigmaMinSq A * (sigmaMinSq B * ∑ i, w i ^ 2) := by
    rw [hw1, mul_one]
  rw [h1]
  have h2 : sigmaMinSq B * ∑ i, w i ^ 2 ≤ ∑ i, (B.mulVec w i) ^ 2 :=
    sigmaMinSq_le_sq_sum B w
  have h3 : sigmaMinSq A * ∑ i, (B.mulVec w i) ^ 2
      ≤ ∑ i, (A.mulVec (B.mulVec w) i) ^ 2 :=
    sigmaMinSq_le_sq_sum A _
  have h4 : (A * B).mulVec w = A.mulVec (B.mulVec w) := by
    rw [Matrix.mulVec_mulVec]
  rw [h4]
  calc sigmaMinSq A * (sigmaMinSq B * ∑ i, w i ^ 2)
      ≤ sigmaMinSq A * ∑ i, (B.mulVec w i) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (sigmaMinSq_nonneg A)
    _ ≤ ∑ i, (A.mulVec (B.mulVec w) i) ^ 2 := h3

/-- A residual block with positive-semidefinite pairing has
    σ_min² ≥ 1: the identity skip floors the operator. -/
theorem one_le_sigmaMinSq_one_add
    (B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hB : ∀ v : Fin (n+1) → ℝ, 0 ≤ v ⬝ᵥ B.mulVec v) :
    1 ≤ sigmaMinSq (1 + B) := by
  obtain ⟨w, hw1, hw2⟩ := sigmaMinSq_attained (1 + B)
  rw [← hw2]
  have hexp : (1 + B).mulVec w = fun i => w i + B.mulVec w i := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
    rfl
  rw [hexp]
  have hpair : ∑ i, w i * B.mulVec w i = w ⬝ᵥ B.mulVec w := rfl
  have h := residual_sq_sum_ge w (B.mulVec w) (by
    rw [hpair]
    exact hB w)
  rw [hw1] at h
  exact h

/-- The residual chain: depth-many identity-skip blocks. -/
noncomputable def resChain (B : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ
  | 0 => 1
  | m + 1 => (1 + B m) * resChain B m

/-- cor:sigma-min-res, depth invariance: a chain of residual blocks
    with positive-semidefinite pairings keeps σ_min² ≥ 1 at every
    depth. The stream never drops below the input. -/
theorem one_le_sigmaMinSq_resChain
    (B : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hB : ∀ m, ∀ v : Fin (n+1) → ℝ, 0 ≤ v ⬝ᵥ (B m).mulVec v)
    (m : ℕ) :
    1 ≤ sigmaMinSq (resChain B m) := by
  induction m with
  | zero =>
    show 1 ≤ sigmaMinSq (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    rw [sigmaMinSq_one]
  | succ k ih =>
    show 1 ≤ sigmaMinSq ((1 + B k) * resChain B k)
    have h1 := one_le_sigmaMinSq_one_add (B k) (hB k)
    have h2 := le_sigmaMinSq_mul (1 + B k) (resChain B k)
    have h3 : (1:ℝ) ≤ sigmaMinSq (1 + B k) * sigmaMinSq (resChain B k) := by
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ sigmaMinSq (1 + B k) * sigmaMinSq (resChain B k) :=
            mul_le_mul h1 ih (by norm_num) (by linarith)
    linarith

end Residual

end DeadDirections
