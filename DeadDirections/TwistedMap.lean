/-
  The twisted mean map, symbolically: K = u₁⁴ + u₂⁴ exactly while
  √det F = 4|u₁³ − u₂³| (prop:volume_multi's (G⁺) witness).

  The map μ = (ρ cos φ, ρ sin φ) with ρ² = 2(u₁⁴ + u₂⁴) and
  φ = u₁ + u₂ has KL divergence ‖μ‖²/2 = u₁⁴ + u₂⁴, the additive
  normal form on the nose. Its Fisher metric is the pullback JᵀJ of
  the Euclidean metric, so √det F = |det J|. In the polar frame the
  Jacobian determinant is ρ(∂₁ρ − ∂₂ρ), and ρ∂ᵢρ = 4uᵢ³, so
  det J = 4(u₁³ − u₂³): the volume density degenerates on the
  diagonal, where the two leading scores share their angular
  component and (G⁺) fails. Each partial derivative is certified as
  a derivative of the coordinate map.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

namespace DeadDirections

/-- The twisted radius ρ = √(2(u₁⁴ + u₂⁴)). -/
noncomputable def twRho (u₁ u₂ : ℝ) : ℝ := Real.sqrt (2 * (u₁ ^ 4 + u₂ ^ 4))

/-- The twisted angle φ = u₁ + u₂. -/
def twPhi (u₁ u₂ : ℝ) : ℝ := u₁ + u₂

/-- The twisted mean map. -/
noncomputable def twMu (u₁ u₂ : ℝ) : Fin 2 → ℝ :=
  ![twRho u₁ u₂ * Real.cos (twPhi u₁ u₂), twRho u₁ u₂ * Real.sin (twPhi u₁ u₂)]

lemma twRho_sq (u₁ u₂ : ℝ) : twRho u₁ u₂ ^ 2 = 2 * (u₁ ^ 4 + u₂ ^ 4) :=
  Real.sq_sqrt (by positivity)

lemma twRho_pos {u₁ u₂ : ℝ} (h : u₁ ≠ 0 ∨ u₂ ≠ 0) : 0 < twRho u₁ u₂ := by
  unfold twRho
  apply Real.sqrt_pos.mpr
  rcases h with h | h
  · have : 0 < u₁ ^ 4 := by positivity
    positivity
  · have : 0 < u₂ ^ 4 := by positivity
    positivity

/-- The KL divergence of the twisted map is the additive normal form
    exactly: ‖μ‖²/2 = u₁⁴ + u₂⁴. -/
theorem twisted_kl (u₁ u₂ : ℝ) :
    (twMu u₁ u₂ 0 ^ 2 + twMu u₁ u₂ 1 ^ 2) / 2 = u₁ ^ 4 + u₂ ^ 4 := by
  simp only [twMu, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hcs := Real.cos_sq_add_sin_sq (twPhi u₁ u₂)
  have hρ := twRho_sq u₁ u₂
  linear_combination (1/2 : ℝ) * (2 * (u₁ ^ 4 + u₂ ^ 4)) * hcs
    + (1/2 : ℝ) * (Real.cos (twPhi u₁ u₂) ^ 2 + Real.sin (twPhi u₁ u₂) ^ 2) * hρ

/-- ∂ρ/∂u₁ = 4u₁³/ρ off the origin. -/
lemma twRho_hasDerivAt_fst {u₁ u₂ : ℝ} (h : u₁ ≠ 0 ∨ u₂ ≠ 0) :
    HasDerivAt (fun x => twRho x u₂) (4 * u₁ ^ 3 / twRho u₁ u₂) u₁ := by
  have hρ := twRho_pos h
  have hpos : 0 < 2 * (u₁ ^ 4 + u₂ ^ 4) := by
    have := hρ
    unfold twRho at this
    exact Real.sqrt_pos.mp this
  have hin : HasDerivAt (fun x : ℝ => 2 * (x ^ 4 + u₂ ^ 4))
      (2 * (4 * u₁ ^ 3)) u₁ := by
    have := ((hasDerivAt_pow 4 u₁).add_const (u₂ ^ 4)).const_mul (2:ℝ)
    simpa using this
  have hs := (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp u₁ hin
  unfold twRho
  convert hs using 1
  have hsq : Real.sqrt (2 * (u₁ ^ 4 + u₂ ^ 4)) ≠ 0 := ne_of_gt hρ
  field_simp

/-- ∂ρ/∂u₂ = 4u₂³/ρ off the origin. -/
lemma twRho_hasDerivAt_snd {u₁ u₂ : ℝ} (h : u₁ ≠ 0 ∨ u₂ ≠ 0) :
    HasDerivAt (fun y => twRho u₁ y) (4 * u₂ ^ 3 / twRho u₁ u₂) u₂ := by
  have hρ := twRho_pos h
  have hpos : 0 < 2 * (u₁ ^ 4 + u₂ ^ 4) := by
    have := hρ
    unfold twRho at this
    exact Real.sqrt_pos.mp this
  have hin : HasDerivAt (fun y : ℝ => 2 * (u₁ ^ 4 + y ^ 4))
      (2 * (4 * u₂ ^ 3)) u₂ := by
    have := ((hasDerivAt_pow 4 u₂).const_add (u₁ ^ 4)).const_mul (2:ℝ)
    simpa using this
  have hs := (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp u₂ hin
  unfold twRho
  convert hs using 1
  have hsq : Real.sqrt (2 * (u₁ ^ 4 + u₂ ^ 4)) ≠ 0 := ne_of_gt hρ
  field_simp

/-- The first coordinate's u₁-partial: ρ₁cos φ − ρ sin φ. -/
lemma twMu0_hasDerivAt_fst {u₁ u₂ : ℝ} (h : u₁ ≠ 0 ∨ u₂ ≠ 0) :
    HasDerivAt (fun x => twMu x u₂ 0)
      (4 * u₁ ^ 3 / twRho u₁ u₂ * Real.cos (twPhi u₁ u₂)
        - twRho u₁ u₂ * Real.sin (twPhi u₁ u₂)) u₁ := by
  have hφ : HasDerivAt (fun x : ℝ => Real.cos (x + u₂))
      (-Real.sin (u₁ + u₂)) u₁ := by
    have := (Real.hasDerivAt_cos (u₁ + u₂)).comp u₁
      ((hasDerivAt_id u₁).add_const u₂)
    simpa using this
  have hm := (twRho_hasDerivAt_fst h).mul hφ
  simp only [twMu, Matrix.cons_val_zero, twPhi]
  convert hm using 1
  ring

/-- The first coordinate's u₂-partial: ρ₂cos φ − ρ sin φ. -/
lemma twMu0_hasDerivAt_snd {u₁ u₂ : ℝ} (h : u₁ ≠ 0 ∨ u₂ ≠ 0) :
    HasDerivAt (fun y => twMu u₁ y 0)
      (4 * u₂ ^ 3 / twRho u₁ u₂ * Real.cos (twPhi u₁ u₂)
        - twRho u₁ u₂ * Real.sin (twPhi u₁ u₂)) u₂ := by
  have hφ : HasDerivAt (fun y : ℝ => Real.cos (u₁ + y))
      (-Real.sin (u₁ + u₂)) u₂ := by
    have := (Real.hasDerivAt_cos (u₁ + u₂)).comp u₂
      ((hasDerivAt_id u₂).const_add u₁)
    simpa using this
  have hm := (twRho_hasDerivAt_snd h).mul hφ
  simp only [twMu, Matrix.cons_val_zero, twPhi]
  convert hm using 1
  ring

/-- The second coordinate's u₁-partial: ρ₁sin φ + ρ cos φ. -/
lemma twMu1_hasDerivAt_fst {u₁ u₂ : ℝ} (h : u₁ ≠ 0 ∨ u₂ ≠ 0) :
    HasDerivAt (fun x => twMu x u₂ 1)
      (4 * u₁ ^ 3 / twRho u₁ u₂ * Real.sin (twPhi u₁ u₂)
        + twRho u₁ u₂ * Real.cos (twPhi u₁ u₂)) u₁ := by
  have hφ : HasDerivAt (fun x : ℝ => Real.sin (x + u₂))
      (Real.cos (u₁ + u₂)) u₁ := by
    have := (Real.hasDerivAt_sin (u₁ + u₂)).comp u₁
      ((hasDerivAt_id u₁).add_const u₂)
    simpa using this
  have hm := (twRho_hasDerivAt_fst h).mul hφ
  simp only [twMu, Matrix.cons_val_one, twPhi]
  convert hm using 1

/-- The second coordinate's u₂-partial: ρ₂sin φ + ρ cos φ. -/
lemma twMu1_hasDerivAt_snd {u₁ u₂ : ℝ} (h : u₁ ≠ 0 ∨ u₂ ≠ 0) :
    HasDerivAt (fun y => twMu u₁ y 1)
      (4 * u₂ ^ 3 / twRho u₁ u₂ * Real.sin (twPhi u₁ u₂)
        + twRho u₁ u₂ * Real.cos (twPhi u₁ u₂)) u₂ := by
  have hφ : HasDerivAt (fun y : ℝ => Real.sin (u₁ + y))
      (Real.cos (u₁ + u₂)) u₂ := by
    have := (Real.hasDerivAt_sin (u₁ + u₂)).comp u₂
      ((hasDerivAt_id u₂).const_add u₁)
    simpa using this
  have hm := (twRho_hasDerivAt_snd h).mul hφ
  simp only [twMu, Matrix.cons_val_one, twPhi]
  convert hm using 1

/-- The Jacobian of the twisted map, entries the certified partials. -/
noncomputable def twJac (u₁ u₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![4 * u₁ ^ 3 / twRho u₁ u₂ * Real.cos (twPhi u₁ u₂)
      - twRho u₁ u₂ * Real.sin (twPhi u₁ u₂),
    4 * u₂ ^ 3 / twRho u₁ u₂ * Real.cos (twPhi u₁ u₂)
      - twRho u₁ u₂ * Real.sin (twPhi u₁ u₂);
    4 * u₁ ^ 3 / twRho u₁ u₂ * Real.sin (twPhi u₁ u₂)
      + twRho u₁ u₂ * Real.cos (twPhi u₁ u₂),
    4 * u₂ ^ 3 / twRho u₁ u₂ * Real.sin (twPhi u₁ u₂)
      + twRho u₁ u₂ * Real.cos (twPhi u₁ u₂)]

/-- det J = 4(u₁³ − u₂³): the polar frame is orthonormal, so the
    determinant is ρ(∂₁ρ − ∂₂ρ), and ρ∂ᵢρ = 4uᵢ³. -/
theorem twisted_jacobian_det {u₁ u₂ : ℝ} (h : u₁ ≠ 0 ∨ u₂ ≠ 0) :
    (twJac u₁ u₂).det = 4 * (u₁ ^ 3 - u₂ ^ 3) := by
  have hρ : twRho u₁ u₂ ≠ 0 := ne_of_gt (twRho_pos h)
  rw [twJac, Matrix.det_fin_two_of]
  set ρ := twRho u₁ u₂ with hρdef
  set c := Real.cos (twPhi u₁ u₂)
  set s := Real.sin (twPhi u₁ u₂)
  have hcs : c ^ 2 + s ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have e1 : ρ * (4 * u₁ ^ 3 / ρ) = 4 * u₁ ^ 3 := mul_div_cancel₀ _ hρ
  have e2 : ρ * (4 * u₂ ^ 3 / ρ) = 4 * u₂ ^ 3 := mul_div_cancel₀ _ hρ
  have key : (4 * u₁ ^ 3 / ρ * c - ρ * s) * (4 * u₂ ^ 3 / ρ * s + ρ * c)
      - (4 * u₂ ^ 3 / ρ * c - ρ * s) * (4 * u₁ ^ 3 / ρ * s + ρ * c)
      = (ρ * (4 * u₁ ^ 3 / ρ) - ρ * (4 * u₂ ^ 3 / ρ)) * (c ^ 2 + s ^ 2) := by
    ring
  rw [key, hcs, mul_one, e1, e2]
  ring

/-- The Fisher metric of the twisted map is the pullback JᵀJ, and its
    volume density is √det F = |det J| = 4|u₁³ − u₂³|: it vanishes on
    the diagonal, where (G⁺) fails. -/
theorem twisted_sqrt_det_fisher {u₁ u₂ : ℝ} (h : u₁ ≠ 0 ∨ u₂ ≠ 0) :
    Real.sqrt ((twJac u₁ u₂).transpose * twJac u₁ u₂).det
      = 4 * |u₁ ^ 3 - u₂ ^ 3| := by
  rw [Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs,
    twisted_jacobian_det h, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]

/-- The density vanishes exactly on the diagonal u₁ = u₂. -/
theorem twisted_density_zero_iff {u₁ u₂ : ℝ} :
    4 * |u₁ ^ 3 - u₂ ^ 3| = 0 ↔ u₁ = u₂ := by
  constructor
  · intro h0
    have : u₁ ^ 3 - u₂ ^ 3 = 0 := by
      have := abs_eq_zero.mp (by linarith [h0] : |u₁ ^ 3 - u₂ ^ 3| = 0)
      exact this
    have h3 : u₁ ^ 3 = u₂ ^ 3 := by linarith
    exact (Odd.strictMono_pow (⟨1, by norm_num⟩ : Odd 3)).injective h3
  · intro h
    rw [h]
    simp

end DeadDirections
