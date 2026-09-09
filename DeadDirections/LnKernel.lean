/-
  LayerNorm kernel direction (theory paper, prop:ln_kernel, part (a)).

  Paper statement (a)(i): for LN(x) = γ ⊙ (√d · Px/‖Px‖) + β with
  P = I − 𝟙𝟙ᵀ/d and γ having no zero coordinate, the covariance
  C = Cov(LN(X)) satisfies C · γ⁻¹ = 0, so v* = γ⁻¹/‖γ⁻¹‖ is a
  deterministic kernel direction for any input distribution.
  Part (a)(ii): coordinates i with γ_i = 0 give C · e_i = 0.

  Formalization notes.
  * `lnLike` takes an arbitrary scalar normaliser s(x), covering the
    exact LN normaliser √d/‖Px‖, the ε-regularised form used in
    practice, and RMS-style scalings of Px. The kernel identity only
    uses that the mean-subtracted vector sums to zero.
  * The identity is pointwise and total: at Px = 0 Lean's division
    convention gives LN(x) = β, so the paper's hypothesis that X puts
    no mass on span(𝟙) is not needed for the covariance statement.
  * Both cases (a)(i) and (a)(ii) follow from one probability lemma,
    `covMatrix_vecMul_eq_zero_of_sum_const`: a coefficient vector v
    whose pairing ∑ v_j Y_j is pointwise constant lies in the kernel
    of the covariance matrix of Y.

  Part (b), prop:rmsnorm_no_kernel, is at the bottom of the file: one
  admissible witness distribution, uniform mass on the 2d points ±e_i,
  gives every candidate direction strictly positive variance at once,
  so RMSNorm admits no kernel direction built from γ or from anything
  else.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace DeadDirections

open MeasureTheory Finset

noncomputable section

variable {d : ℕ}

/-! ## 1. Mean subtraction and the LN family -/

/-- Coordinate mean of a vector in ℝ^d. -/
def vmean (x : Fin d → ℝ) : ℝ := (∑ i, x i) / d

/-- Mean subtraction, the projector P = I − 𝟙𝟙ᵀ/d applied to x. -/
def msub (x : Fin d → ℝ) : Fin d → ℝ := fun i => x i - vmean x

/-- The mean-subtracted vector sums to zero: 𝟙ᵀ P x = 0. -/
lemma sum_msub (x : Fin d → ℝ) : ∑ i, msub x i = 0 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp [msub]
  · have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd)
    simp only [msub, vmean, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

/-- LayerNorm-like map with an arbitrary scalar normaliser `s`:
    x ↦ γ ⊙ (s(x) · Px) + β. The exact LN takes s(x) = √d/‖Px‖. -/
def lnLike (s : (Fin d → ℝ) → ℝ) (γ β : Fin d → ℝ) (x : Fin d → ℝ) :
    Fin d → ℝ :=
  fun i => γ i * (s x * msub x i) + β i

/-- Exact LayerNorm: s(x) = √d / ‖Px‖ (Euclidean norm). At Px = 0 the
    junk value 0 gives LN(x) = β, which the kernel theorem absorbs. -/
def layerNorm (γ β : Fin d → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  lnLike (fun x => Real.sqrt d / Real.sqrt (∑ i, msub x i ^ 2)) γ β x

/-! ## 2. Core algebraic identity -/

/-- ⟨γ⁻¹, LN(x)⟩ = ⟨γ⁻¹, β⟩ for every x: the γ⁻¹-pairing of the LN
    output is independent of the input. -/
theorem sum_ginv_mul_lnLike (s : (Fin d → ℝ) → ℝ) (γ β x : Fin d → ℝ)
    (hγ : ∀ i, γ i ≠ 0) :
    ∑ i, (γ i)⁻¹ * lnLike s γ β x i = ∑ i, (γ i)⁻¹ * β i := by
  have h : ∀ i, (γ i)⁻¹ * lnLike s γ β x i
      = s x * msub x i + (γ i)⁻¹ * β i := by
    intro i
    simp only [lnLike, mul_add]
    rw [inv_mul_cancel_left₀ (hγ i)]
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, sum_msub,
    mul_zero, zero_add]

/-- A coordinate with γ_i = 0 outputs the constant β_i. -/
theorem lnLike_apply_of_gamma_zero (s : (Fin d → ℝ) → ℝ) (γ β x : Fin d → ℝ)
    (i : Fin d) (hi : γ i = 0) : lnLike s γ β x i = β i := by
  simp [lnLike, hi]

/-! ## 3. Covariance kernel -/

section Covariance

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Entrywise covariance matrix of a random vector Y : Ω → ℝ^d. -/
def covMatrix (μ : Measure Ω) (Y : Ω → Fin d → ℝ) (i j : Fin d) : ℝ :=
  ∫ ω, (Y ω i - ∫ ω', Y ω' i ∂μ) * (Y ω j - ∫ ω', Y ω' j ∂μ) ∂μ

/-- If the pairing ∑_j v_j Y_j is pointwise constant, then v lies in the
    kernel of the covariance matrix: ∑_j C_{ij} v_j = 0 for every i.
    Integrability hypotheses state that each coordinate and each
    centred product is integrable (the covariance matrix exists). -/
theorem covMatrix_vecMul_eq_zero_of_sum_const
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → Fin d → ℝ) (v : Fin d → ℝ) (K : ℝ)
    (hconst : ∀ ω, ∑ j, v j * Y ω j = K)
    (hInt : ∀ i, Integrable (fun ω => Y ω i) μ)
    (hInt2 : ∀ i j, Integrable (fun ω =>
      (Y ω i - ∫ ω', Y ω' i ∂μ) * (Y ω j - ∫ ω', Y ω' j ∂μ)) μ)
    (i : Fin d) :
    ∑ j, covMatrix μ Y i j * v j = 0 := by
  -- The mean vector pairs to the same constant K.
  have hmean : ∑ j, v j * ∫ ω, Y ω j ∂μ = K := by
    have h1 : ∑ j, v j * ∫ ω, Y ω j ∂μ
        = ∫ ω, ∑ j, v j * Y ω j ∂μ := by
      rw [integral_finset_sum univ fun j _ => (hInt j).const_mul (v j)]
      exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
    rw [h1]
    simp only [hconst]
    simp
  -- Hence the centred pairing vanishes pointwise.
  have hdev : ∀ ω, ∑ j, v j * (Y ω j - ∫ ω', Y ω' j ∂μ) = 0 := by
    intro ω
    simp only [mul_sub, Finset.sum_sub_distrib, hconst ω, hmean, sub_self]
  -- Pull the sum inside the integral and use the pointwise zero.
  have hswap : ∑ j, covMatrix μ Y i j * v j
      = ∫ ω, ∑ j, ((Y ω i - ∫ ω', Y ω' i ∂μ)
          * (Y ω j - ∫ ω', Y ω' j ∂μ)) * v j ∂μ := by
    rw [integral_finset_sum univ fun j _ => (hInt2 i j).mul_const (v j)]
    exact Finset.sum_congr rfl fun j _ => (integral_mul_const _ _).symm
  rw [hswap]
  have hzero : ∀ ω, ∑ j, ((Y ω i - ∫ ω', Y ω' i ∂μ)
      * (Y ω j - ∫ ω', Y ω' j ∂μ)) * v j = 0 := by
    intro ω
    have h2 : ∀ j, ((Y ω i - ∫ ω', Y ω' i ∂μ)
        * (Y ω j - ∫ ω', Y ω' j ∂μ)) * v j
        = (Y ω i - ∫ ω', Y ω' i ∂μ)
          * (v j * (Y ω j - ∫ ω', Y ω' j ∂μ)) := by
      intro j; ring
    simp only [h2, ← Finset.mul_sum, hdev ω, mul_zero]
  simp only [hzero, integral_zero]

/-- prop:ln_kernel (a)(i). For γ with no zero coordinate, γ⁻¹ is in the
    kernel of the output covariance: ∑_j Cov(LN(X))_{ij} (γ_j)⁻¹ = 0.
    Holds for any scalar normaliser s and any input distribution X for
    which the covariance exists. -/
theorem covMatrix_lnLike_ginv_eq_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : (Fin d → ℝ) → ℝ) (γ β : Fin d → ℝ) (hγ : ∀ i, γ i ≠ 0)
    (X : Ω → Fin d → ℝ)
    (hInt : ∀ i, Integrable (fun ω => lnLike s γ β (X ω) i) μ)
    (hInt2 : ∀ i j, Integrable (fun ω =>
      (lnLike s γ β (X ω) i - ∫ ω', lnLike s γ β (X ω') i ∂μ)
      * (lnLike s γ β (X ω) j - ∫ ω', lnLike s γ β (X ω') j ∂μ)) μ)
    (i : Fin d) :
    ∑ j, covMatrix μ (fun ω => lnLike s γ β (X ω)) i j * (γ j)⁻¹ = 0 :=
  covMatrix_vecMul_eq_zero_of_sum_const μ _ (fun j => (γ j)⁻¹)
    (∑ j, (γ j)⁻¹ * β j)
    (fun ω => sum_ginv_mul_lnLike s γ β (X ω) hγ) hInt hInt2 i

/-- prop:ln_kernel (a)(ii). A zero coordinate of γ gives a coordinate
    kernel direction: Cov(LN(X))_{i i₀} = 0 for every i when γ_{i₀} = 0.
    (This clause needs no hypothesis on the other coordinates of γ.) -/
theorem covMatrix_lnLike_zero_coord
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : (Fin d → ℝ) → ℝ) (γ β : Fin d → ℝ) (i₀ : Fin d) (hγ0 : γ i₀ = 0)
    (X : Ω → Fin d → ℝ)
    (hInt : ∀ i, Integrable (fun ω => lnLike s γ β (X ω) i) μ)
    (hInt2 : ∀ i j, Integrable (fun ω =>
      (lnLike s γ β (X ω) i - ∫ ω', lnLike s γ β (X ω') i ∂μ)
      * (lnLike s γ β (X ω) j - ∫ ω', lnLike s γ β (X ω') j ∂μ)) μ)
    (i : Fin d) :
    covMatrix μ (fun ω => lnLike s γ β (X ω)) i i₀ = 0 := by
  have h := covMatrix_vecMul_eq_zero_of_sum_const μ
    (fun ω => lnLike s γ β (X ω)) (fun j => if j = i₀ then 1 else 0)
    (β i₀)
    (fun ω => by
      simp [ite_mul, lnLike_apply_of_gamma_zero s γ β (X ω) i₀ hγ0])
    hInt hInt2 i
  simpa [mul_ite] using h

/-- prop:ln_kernel (a)(i) instantiated at the exact LayerNorm
    normaliser √d/‖Px‖. -/
theorem covMatrix_layerNorm_ginv_eq_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (γ β : Fin d → ℝ) (hγ : ∀ i, γ i ≠ 0)
    (X : Ω → Fin d → ℝ)
    (hInt : ∀ i, Integrable (fun ω => layerNorm γ β (X ω) i) μ)
    (hInt2 : ∀ i j, Integrable (fun ω =>
      (layerNorm γ β (X ω) i - ∫ ω', layerNorm γ β (X ω') i ∂μ)
      * (layerNorm γ β (X ω) j - ∫ ω', layerNorm γ β (X ω') j ∂μ)) μ)
    (i : Fin d) :
    ∑ j, covMatrix μ (fun ω => layerNorm γ β (X ω)) i j * (γ j)⁻¹ = 0 :=
  covMatrix_lnLike_ginv_eq_zero μ _ γ β hγ X hInt hInt2 i

end Covariance

end


noncomputable section RmsNormNegative

variable {d : ℕ}

/-! ## RMSNorm has no kernel direction (prop:rmsnorm_no_kernel)

One admissible witness defeats every candidate at once. The input with
uniform mass on the 2d points ±e_i has covariance I/d, positive
definite, and the variance of any reading v of RMSNorm on it equals
Σᵢ (vᵢ γᵢ)², positive whenever v ≠ 0 and γ has no zero coordinate.
The distribution enters as explicit weights on a finite support, so
every expectation below is a finite sum. -/

/-- RMSNorm with gain γ: no mean subtraction, scaling √d/‖x‖. -/
def rmsNorm (γ x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => Real.sqrt d * γ i * x i / Real.sqrt (∑ j, x j ^ 2)

lemma single_sq_sum (i : Fin d) :
    ∑ j, ((Pi.single i 1 : Fin d → ℝ) j) ^ 2 = 1 := by
  have hterm : ∀ j : Fin d, ((Pi.single i 1 : Fin d → ℝ) j) ^ 2
      = if j = i then (1:ℝ) else 0 := by
    intro j
    rw [Pi.single_apply]
    by_cases hji : j = i <;> simp [hji]
  rw [Finset.sum_congr rfl fun j _ => hterm j,
    Finset.sum_ite_eq' Finset.univ i fun _ => (1:ℝ)]
  simp

lemma rmsNorm_single_apply (γ : Fin d → ℝ) (i j : Fin d) :
    rmsNorm γ (Pi.single i 1) j
      = Real.sqrt d * γ j * (Pi.single i 1 : Fin d → ℝ) j := by
  unfold rmsNorm
  rw [single_sq_sum, Real.sqrt_one, div_one]

lemma rmsNorm_neg_single_apply (γ : Fin d → ℝ) (i j : Fin d) :
    rmsNorm γ (-Pi.single i 1) j
      = -(Real.sqrt d * γ j * (Pi.single i 1 : Fin d → ℝ) j) := by
  unfold rmsNorm
  have hsq : ∑ k, ((-Pi.single i 1 : Fin d → ℝ) k) ^ 2 = 1 := by
    rw [Finset.sum_congr rfl fun k _ => by rw [Pi.neg_apply, neg_sq]]
    exact single_sq_sum i
  rw [hsq, Real.sqrt_one, div_one, Pi.neg_apply]
  ring

/-- The v-reading of RMSNorm at the witness point e_i. -/
lemma rmsNorm_reading_single (γ v : Fin d → ℝ) (i : Fin d) :
    ∑ j, v j * rmsNorm γ (Pi.single i 1) j
      = Real.sqrt d * (v i * γ i) := by
  have hterm : ∀ j : Fin d, v j * rmsNorm γ (Pi.single i 1) j
      = if j = i then Real.sqrt d * (v j * γ j) else 0 := by
    intro j
    rw [rmsNorm_single_apply, Pi.single_apply]
    by_cases hji : j = i <;> simp [hji]
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j,
    Finset.sum_ite_eq' Finset.univ i
      fun j => Real.sqrt d * (v j * γ j)]
  simp

lemma rmsNorm_reading_neg_single (γ v : Fin d → ℝ) (i : Fin d) :
    ∑ j, v j * rmsNorm γ (-Pi.single i 1) j
      = -(Real.sqrt d * (v i * γ i)) := by
  have hterm : ∀ j : Fin d, v j * rmsNorm γ (-Pi.single i 1) j
      = -(v j * rmsNorm γ (Pi.single i 1) j) := fun j => by
    rw [rmsNorm_neg_single_apply, rmsNorm_single_apply]
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_neg_distrib,
    rmsNorm_reading_single]

/-- prop:rmsnorm_no_kernel: on the admissible witness (uniform mass on
    the 2d points ±e_i) every candidate direction v with v ≠ 0 reads
    RMSNorm with strictly positive variance, whatever γ without zero
    coordinates. No direction, built from γ or otherwise, is a kernel
    direction for every admissible input. The variance is
    Σᵢ (vᵢ γᵢ)² exactly. -/
theorem rmsnorm_no_kernel (γ v : Fin d → ℝ) (hγ : ∀ i, γ i ≠ 0)
    (hv : v ≠ 0) :
    0 < (∑ i, (1 / (2 * (d:ℝ)))
          * ((∑ j, v j * rmsNorm γ (Pi.single i 1) j) ^ 2
            + (∑ j, v j * rmsNorm γ (-Pi.single i 1) j) ^ 2))
        - (∑ i, (1 / (2 * (d:ℝ)))
          * ((∑ j, v j * rmsNorm γ (Pi.single i 1) j)
            + (∑ j, v j * rmsNorm γ (-Pi.single i 1) j))) ^ 2 := by
  obtain ⟨i₀, hvi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (funext fun i => hcon i)
  have hd : 0 < d := i₀.pos
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hsqd : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
  have hmean : ∑ i, (1 / (2 * (d:ℝ)))
      * ((∑ j, v j * rmsNorm γ (Pi.single i 1) j)
        + (∑ j, v j * rmsNorm γ (-Pi.single i 1) j)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [rmsNorm_reading_single, rmsNorm_reading_neg_single]
    ring
  have hsec : ∑ i, (1 / (2 * (d:ℝ)))
      * ((∑ j, v j * rmsNorm γ (Pi.single i 1) j) ^ 2
        + (∑ j, v j * rmsNorm γ (-Pi.single i 1) j) ^ 2)
      = ∑ i, (v i * γ i) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rmsNorm_reading_single, rmsNorm_reading_neg_single]
    have hexpand : (Real.sqrt d * (v i * γ i)) ^ 2
        = d * (v i * γ i) ^ 2 := by
      rw [mul_pow, hsqd]
    rw [neg_sq, hexpand]
    field_simp
    ring
  rw [hmean, hsec]
  have hpos : 0 < ∑ i, (v i * γ i) ^ 2 :=
    Finset.sum_pos' (fun i _ => sq_nonneg _)
      ⟨i₀, Finset.mem_univ i₀,
        lt_of_le_of_ne (sq_nonneg _)
          (Ne.symm (pow_ne_zero 2 (mul_ne_zero hvi₀ (hγ i₀))))⟩
  nlinarith

/-- The witness is admissible: its input covariance form is (1/d)·‖u‖²,
    positive at every u ≠ 0, so cov(X) is positive definite. -/
theorem rmsnorm_witness_input_posdef (u : Fin d → ℝ) (hu : u ≠ 0) :
    0 < ∑ i, (1 / (2 * (d:ℝ)))
        * ((∑ j, u j * (Pi.single i 1 : Fin d → ℝ) j) ^ 2
          + (∑ j, u j * (-Pi.single i 1 : Fin d → ℝ) j) ^ 2) := by
  obtain ⟨i₀, hui₀⟩ : ∃ i, u i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu (funext fun i => hcon i)
  have hd : 0 < d := i₀.pos
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hread : ∀ i : Fin d,
      ∑ j, u j * (Pi.single i 1 : Fin d → ℝ) j = u i := by
    intro i
    have hterm : ∀ j : Fin d, u j * (Pi.single i 1 : Fin d → ℝ) j
        = if j = i then u j else 0 := by
      intro j
      rw [Pi.single_apply]
      by_cases hji : j = i <;> simp [hji]
    rw [Finset.sum_congr rfl fun j _ => hterm j,
      Finset.sum_ite_eq' Finset.univ i u]
    simp
  have hreadneg : ∀ i : Fin d,
      ∑ j, u j * (-Pi.single i 1 : Fin d → ℝ) j = -u i := by
    intro i
    have hterm2 : ∀ j : Fin d, u j * (-Pi.single i 1 : Fin d → ℝ) j
        = -(u j * (Pi.single i 1 : Fin d → ℝ) j) := fun j => by
      rw [Pi.neg_apply]
      ring
    rw [Finset.sum_congr rfl fun j _ => hterm2 j,
      Finset.sum_neg_distrib, hread]
  have hterm : ∀ i : Fin d, (1 / (2 * (d:ℝ)))
      * ((∑ j, u j * (Pi.single i 1 : Fin d → ℝ) j) ^ 2
        + (∑ j, u j * (-Pi.single i 1 : Fin d → ℝ) j) ^ 2)
      = u i ^ 2 / d := by
    intro i
    rw [hread i, hreadneg i]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  refine Finset.sum_pos' (fun i _ => by positivity)
    ⟨i₀, Finset.mem_univ i₀, ?_⟩
  have h2 : 0 < u i₀ ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hui₀))
  positivity

end RmsNormNegative

/-- The post-LN exclusion clause (cor:sigma-min-res): on any sample,
    the centred LN outputs pair to zero with γ⁻¹ row by row, so the
    centred sample Gram form vanishes at γ⁻¹ and σ_min(LN(X)) = 0
    identically at post-LN nodes. -/
theorem post_ln_sample_kernel {d : ℕ} (s : (Fin d → ℝ) → ℝ) (γ β : Fin d → ℝ)
    (hγ : ∀ i, γ i ≠ 0) {N : ℕ} (x : Fin N → Fin d → ℝ) :
    ∑ a, (∑ j, (γ j)⁻¹
        * (lnLike s γ β (x a) j - (∑ b, lnLike s γ β (x b) j) / N)) ^ 2 = 0 := by
  refine Finset.sum_eq_zero fun a _ => ?_
  have hN : (N:ℝ) ≠ 0 := by
    have := a.pos
    exact_mod_cast this.ne'
  have hrow : ∑ j, (γ j)⁻¹
      * (lnLike s γ β (x a) j - (∑ b, lnLike s γ β (x b) j) / N) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, sum_ginv_mul_lnLike s γ β (x a) hγ]
    have e : ∑ j, (γ j)⁻¹ * ((∑ b, lnLike s γ β (x b) j) / N)
        = (∑ b, ∑ j, (γ j)⁻¹ * lnLike s γ β (x b) j) / N := by
      rw [Finset.sum_comm, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.mul_sum, mul_div_assoc]
    rw [e, Finset.sum_congr rfl fun b _ => sum_ginv_mul_lnLike s γ β (x b) hγ,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  rw [hrow]
  ring

end DeadDirections
