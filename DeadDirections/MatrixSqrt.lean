/-
  The real PSD square root, with uniqueness.

  Mathlib has no square root for real symmetric matrices (found
  2026-08-16), so the package builds one on its own spectral
  machinery: the root of U·diag(λ)·Uᵀ is U·diag(√λ)·Uᵀ, symmetric,
  positive semidefinite, and squaring to the original. Uniqueness is
  the trace trick, self-hosted: for any symmetric PSD B with B² = S,
  the eight-term expansion of trace((B+C)(B−C)²) cancels by
  cyclicity and B² = C² alone, both conjugation traces are
  non-negative because B and C decompose through their own roots, so
  both vanish, forcing BD = CD = 0, then D² = 0 and D = 0. The
  balanced-flow corollary follows: under balance the Gram factor is
  the square root of PPᵀ as an identity of the operator.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.SpecialFunctions.Sqrt
import DeadDirections.SigmaMin
import DeadDirections.MatrixQuotient

namespace DeadDirections

open Matrix

variable {n : ℕ}

/-- The quadratic form of a diagonal conjugation, generically. -/
lemma quadform_conj_diagonal (U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (d : Fin (n+1) → ℝ) (v : Fin (n+1) → ℝ) :
    v ⬝ᵥ ((U * Matrix.diagonal d * Uᵀ).mulVec v)
      = ∑ i, d i * ((Uᵀ.mulVec v) i) ^ 2 := by
  have h1 : (U * Matrix.diagonal d * Uᵀ).mulVec v
      = U.mulVec ((Matrix.diagonal d).mulVec (Uᵀ.mulVec v)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [h1]
  have h2 : v ⬝ᵥ (U.mulVec ((Matrix.diagonal d).mulVec
      (Uᵀ.mulVec v)))
      = (Uᵀ.mulVec v) ⬝ᵥ ((Matrix.diagonal d).mulVec
        (Uᵀ.mulVec v)) := by
    rw [Matrix.dotProduct_mulVec]
    congr 1
    rw [← Matrix.transpose_transpose U, Matrix.vecMul_transpose,
      Matrix.transpose_transpose]
  rw [h2]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal]
  ring

/-- Eigenvalues of a positive semidefinite real symmetric matrix are
    non-negative: attained values of a non-negative form. -/
lemma eigenvalues_nonneg_of_posSemidef
    {S : Matrix (Fin (n+1)) (Fin (n+1)) ℝ} (hS : S.IsHermitian)
    (hpsd : S.PosSemidef) (i : Fin (n+1)) :
    0 ≤ hS.eigenvalues i := by
  obtain ⟨hval, -⟩ := hermitian_quadform_attained hS i
  rw [← hval]
  have h := hpsd.dotProduct_mulVec_nonneg
    ((eigU hS).mulVec (Pi.single i 1))
  simpa using h

/-- The square root of a real symmetric matrix through its spectral
    decomposition. -/
noncomputable def matSqrt {S : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hS : S.IsHermitian) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  eigU hS * Matrix.diagonal (fun i => Real.sqrt (hS.eigenvalues i))
    * (eigU hS)ᵀ

/-- The root is symmetric. -/
theorem matSqrt_transpose {S : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hS : S.IsHermitian) : (matSqrt hS)ᵀ = matSqrt hS := by
  unfold matSqrt
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.diagonal_transpose,
    Matrix.mul_assoc]

/-- The root squares to the matrix, on the PSD cone. -/
theorem matSqrt_sq {S : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hS : S.IsHermitian) (hpsd : S.PosSemidef) :
    matSqrt hS * matSqrt hS = S := by
  set Dg := Matrix.diagonal
    (fun i => Real.sqrt (hS.eigenvalues i)) with hDg
  show eigU hS * Dg * (eigU hS)ᵀ * (eigU hS * Dg * (eigU hS)ᵀ) = S
  have hU := eigU_star_mul_self hS
  have h1 : eigU hS * Dg * (eigU hS)ᵀ * (eigU hS * Dg * (eigU hS)ᵀ)
      = eigU hS * Dg * ((eigU hS)ᵀ * eigU hS) * Dg
        * (eigU hS)ᵀ := by
    noncomm_ring
  rw [h1, hU]
  have h2 : eigU hS * Dg * 1 * Dg * (eigU hS)ᵀ
      = eigU hS * (Dg * Dg) * (eigU hS)ᵀ := by
    noncomm_ring
  rw [h2, hDg, Matrix.diagonal_mul_diagonal]
  have hd : (fun i => Real.sqrt (hS.eigenvalues i)
      * Real.sqrt (hS.eigenvalues i)) = hS.eigenvalues := by
    funext i
    exact Real.mul_self_sqrt
      (eigenvalues_nonneg_of_posSemidef hS hpsd i)
  rw [hd]
  exact (spectral_real hS).symm

/-- The root is positive semidefinite. -/
theorem matSqrt_posSemidef {S : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hS : S.IsHermitian) : (matSqrt hS).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · have h := matSqrt_transpose hS
    rw [Matrix.IsHermitian, conjTranspose_eq_transpose_real, h]
  · intro v
    have h := quadform_conj_diagonal (eigU hS)
      (fun i => Real.sqrt (hS.eigenvalues i)) v
    have hnn : (0:ℝ) ≤ ∑ i, Real.sqrt (hS.eigenvalues i)
        * (((eigU hS)ᵀ.mulVec v) i) ^ 2 :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
    have hstar : (star v : Fin (n+1) → ℝ) = v := by
      funext i
      simp
    rw [hstar]
    show (0:ℝ) ≤ v ⬝ᵥ (matSqrt hS).mulVec v
    unfold matSqrt
    rw [h]
    exact hnn

/-- Uniqueness: any symmetric positive semidefinite root agrees with
    matSqrt. The trace trick, self-hosted through the roots of the
    candidates themselves. -/
theorem matSqrt_unique {S B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hS : S.IsHermitian) (hSpsd : S.PosSemidef)
    (hBt : Bᵀ = B) (hBpsd : B.PosSemidef) (hsq : B * B = S) :
    B = matSqrt hS := by
  set C := matSqrt hS with hC
  have hCt : Cᵀ = C := matSqrt_transpose hS
  have hCsq : C * C = S := matSqrt_sq hS hSpsd
  set D := B - C with hD
  have hDt : Dᵀ = D := by
    rw [hD, Matrix.transpose_sub, hBt, hCt]
  have h3 : B * B = C * C := by rw [hsq, hCsq]
  -- the eight-term cyclic cancellation
  have hexp : (B + C) * (D * D)
      = B * B * B - B * B * C - B * C * B + B * C * C
        + C * B * B - C * B * C - C * C * B + C * C * C := by
    rw [hD]
    noncomm_ring
  have e1 : (B * C * B).trace = (C * C * C).trace := by
    rw [Matrix.trace_mul_comm (B * C) B, ← Matrix.mul_assoc, h3]
  have e2 : (B * C * C).trace = (B * B * B).trace := by
    rw [Matrix.mul_assoc, ← h3, ← Matrix.mul_assoc]
  have e3 : (C * B * B).trace = (C * C * C).trace := by
    rw [Matrix.mul_assoc, h3, ← Matrix.mul_assoc]
  have e4 : (C * B * C).trace = (B * B * B).trace := by
    rw [Matrix.trace_mul_comm (C * B) C, ← Matrix.mul_assoc, ← h3]
  have e5 : (B * B * C).trace = (C * C * C).trace := by
    rw [h3]
  have e6 : (C * C * B).trace = (B * B * B).trace := by
    rw [← h3]
  have hcyc : ((B + C) * (D * D)).trace = 0 := by
    rw [hexp]
    simp only [Matrix.trace_add, Matrix.trace_sub]
    rw [e1, e2, e3, e4, e5, e6]
    ring
  -- split into the two conjugation traces
  have hB' : (D * B * D).trace = (B * (D * D)).trace := by
    rw [Matrix.trace_mul_comm (D * B) D, ← Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm (D * D) B]
  have hC' : (D * C * D).trace = (C * (D * D)).trace := by
    rw [Matrix.trace_mul_comm (D * C) D, ← Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm (D * D) C]
  have hsplit : ((B + C) * (D * D)).trace
      = (D * B * D).trace + (D * C * D).trace := by
    rw [hB', hC', ← Matrix.trace_add, ← Matrix.add_mul]
  -- decompose through the candidates' own roots
  have hBherm : B.IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_eq_transpose_real, hBt]
  have hCherm : C.IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_eq_transpose_real, hCt]
  set EB := matSqrt hBherm with hEB
  set EC := matSqrt hCherm with hEC
  have hEBt : EBᵀ = EB := matSqrt_transpose hBherm
  have hECt : ECᵀ = EC := matSqrt_transpose hCherm
  have hEBsq : EB * EB = B := matSqrt_sq hBherm hBpsd
  have hECsq : EC * EC = C :=
    matSqrt_sq hCherm (matSqrt_posSemidef hS)
  have hconjB : (EB * D)ᵀ * (EB * D) = D * B * D := by
    rw [Matrix.transpose_mul, hEBt, hDt, ← hEBsq]
    noncomm_ring
  have hconjC : (EC * D)ᵀ * (EC * D) = D * C * D := by
    rw [Matrix.transpose_mul, hECt, hDt, ← hECsq]
    noncomm_ring
  have hnnB : 0 ≤ (D * B * D).trace := by
    rw [← hconjB, ← conjTranspose_eq_transpose_real]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg
  have hnnC : 0 ≤ (D * C * D).trace := by
    rw [← hconjC, ← conjTranspose_eq_transpose_real]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg
  have hzB : (D * B * D).trace = 0 := by
    have h := hsplit
    rw [hcyc] at h
    linarith
  have hzC : (D * C * D).trace = 0 := by
    have h := hsplit
    rw [hcyc] at h
    linarith
  -- vanishing traces kill the products
  have hEBD : EB * D = 0 := by
    have h := hzB
    rw [← hconjB, ← conjTranspose_eq_transpose_real] at h
    exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h
  have hECD : EC * D = 0 := by
    have h := hzC
    rw [← hconjC, ← conjTranspose_eq_transpose_real] at h
    exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h
  have hBD : B * D = 0 := by
    rw [← hEBsq, Matrix.mul_assoc, hEBD, Matrix.mul_zero]
  have hCD : C * D = 0 := by
    rw [← hECsq, Matrix.mul_assoc, hECD, Matrix.mul_zero]
  have hDD : D * D = 0 := by
    have h : D * D = B * D - C * D := by
      rw [hD]
      noncomm_ring
    rw [h, hBD, hCD, sub_zero]
  have hDzero : D = 0 := by
    have h2 : (Dᴴ * D).trace = 0 := by
      rw [conjTranspose_eq_transpose_real, hDt, hDD,
        Matrix.trace_zero]
    exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h2
  have hfinal : B - C = 0 := by rw [← hD]; exact hDzero
  exact sub_eq_zero.mp hfinal

/-- The balanced-flow roots, packaged: under balance the first Gram
    factor is the matSqrt of PPᵀ. -/
theorem balanced_gram_eq_sqrt
    (W₁ W₂ : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hbal : W₂ * W₂ᵀ = W₁ᵀ * W₁)
    (hP : ((W₁ * W₂) * (W₁ * W₂)ᵀ).IsHermitian) :
    W₁ * W₁ᵀ = matSqrt hP := by
  obtain ⟨-, hsq₁, -, hpsd₁, -⟩ :=
    balanced_flow_closed_L2 W₁ W₂ 0 hbal
  apply matSqrt_unique hP
  · have h := Matrix.posSemidef_self_mul_conjTranspose (W₁ * W₂)
    rwa [conjTranspose_eq_transpose_bal] at h
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  · exact hpsd₁
  · exact hsq₁

end DeadDirections
