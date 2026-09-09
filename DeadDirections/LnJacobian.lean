/-
  The LayerNorm backward Jacobian, exactly (thm:bridge_ln's bracket
  on the full Jacobian).

  With γ = 1, β = 0 the normalised map is ẑ(x) = √d·Px/‖Px‖ with P the
  mean-subtraction projector. Its Jacobian is
  J = (√d/‖Px‖)·(P − ẑẑᵀ/d) = (1/σ)·(P − ẑẑᵀ/d), certified here as the
  directional derivative in every direction. The dead component of
  its action on a backward vector δ splits into two terms: the dead
  input δ_h passes with the factor (1/σ)(1 − 1/d − ẑ_h²/d), no chain
  power lost, which is the bracket's lower end (LN adds no decay);
  and the live components δ_j, j ≠ h, are injected through the mean
  subtraction and the ẑ-projection with amplitude of order 1/σ, the
  same leak form as the rotation witness, which is the bracket's
  plateau end (a crossing resets the accumulated decay). The
  amplification factor 1/σ grows as the dead activation collapses,
  as the paper's upper-bound argument says.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import DeadDirections.LnKernel

namespace DeadDirections

open Finset

variable {d : ℕ}

/-- Mean subtraction is linear along a direction. -/
lemma msub_add_smul (x v : Fin d → ℝ) (ε : ℝ) (i : Fin d) :
    msub (x + ε • v) i = msub x i + ε * msub v i := by
  unfold msub vmean
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

/-- The mean-subtracted vector pairs with v through the projector:
    Σⱼ (Px)ⱼ (Pv)ⱼ = Σⱼ (Px)ⱼ vⱼ. -/
lemma sum_msub_mul_msub (x v : Fin d → ℝ) :
    ∑ j, msub x j * msub v j = ∑ j, msub x j * v j := by
  have h : ∀ j, msub x j * msub v j = msub x j * v j - vmean v * msub x j := by
    intro j
    unfold msub
    ring
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_msub, mul_zero, sub_zero]

/-- The normalised map ẑ(x) = √d·Px/‖Px‖, coordinatewise. -/
noncomputable def znorm (x : Fin d → ℝ) (i : Fin d) : ℝ :=
  Real.sqrt d / Real.sqrt (∑ j, msub x j ^ 2) * msub x i

/-- ẑ is LayerNorm at γ = 1, β = 0. -/
lemma znorm_eq_layerNorm (x : Fin d → ℝ) :
    znorm x = layerNorm (fun _ => (1:ℝ)) (fun _ => (0:ℝ)) x := by
  funext i
  simp [znorm, layerNorm, lnLike]

/-- The Jacobian entry: (√d/‖Px‖)·(δᵢⱼ − 1/d − (Px)ᵢ(Px)ⱼ/‖Px‖²). -/
noncomputable def lnJac (x : Fin d → ℝ) (i j : Fin d) : ℝ :=
  Real.sqrt d / Real.sqrt (∑ k, msub x k ^ 2)
    * ((if i = j then 1 else 0) - 1 / d - msub x i * msub x j / ∑ k, msub x k ^ 2)

/-- The directional derivative of the normalised map, exactly: in
    direction v the i-th coordinate moves with
    (√d/‖Px‖)·((Pv)ᵢ − (Px)ᵢ⟨Px, Pv⟩/‖Px‖²). -/
theorem znorm_hasDerivAt_dir (x v : Fin d → ℝ) (i : Fin d)
    (hS : 0 < ∑ j, msub x j ^ 2) :
    HasDerivAt (fun ε : ℝ => znorm (x + ε • v) i)
      (Real.sqrt d / Real.sqrt (∑ j, msub x j ^ 2)
        * (msub v i - msub x i * (∑ j, msub x j * msub v j) / ∑ j, msub x j ^ 2)) 0 := by
  set S₀ := ∑ j, msub x j ^ 2 with hS₀
  set c := ∑ j, msub x j * msub v j with hc
  -- the numerator and the squared norm along the direction
  have hfun : (fun ε : ℝ => znorm (x + ε • v) i)
      = fun ε => (Real.sqrt d * (msub x i + ε * msub v i))
          / Real.sqrt (∑ j, (msub x j + ε * msub v j) ^ 2) := by
    funext ε
    simp only [znorm, msub_add_smul]
    ring
  rw [hfun]
  have hN : HasDerivAt (fun ε : ℝ => Real.sqrt d * (msub x i + ε * msub v i))
      (Real.sqrt d * msub v i) 0 := by
    have := (((hasDerivAt_id (0:ℝ)).mul_const (msub v i)).const_add (msub x i)).const_mul
      (Real.sqrt d)
    simpa using this
  have hSd : HasDerivAt (fun ε : ℝ => ∑ j, (msub x j + ε * msub v j) ^ 2)
      (∑ j, 2 * msub x j * msub v j) 0 := by
    have h : ∀ j ∈ (Finset.univ : Finset (Fin d)),
        HasDerivAt (fun ε : ℝ => (msub x j + ε * msub v j) ^ 2)
          (2 * msub x j * msub v j) 0 := by
      intro j _
      have := (((hasDerivAt_id (0:ℝ)).mul_const (msub v j)).const_add (msub x j)).pow 2
      simpa using this
    exact HasDerivAt.fun_sum h
  have hS0 : (∑ j, (msub x j + 0 * msub v j) ^ 2) = S₀ := by
    simp [hS₀]
  have hsqrt : HasDerivAt (fun ε : ℝ => Real.sqrt (∑ j, (msub x j + ε * msub v j) ^ 2))
      ((∑ j, 2 * msub x j * msub v j) / (2 * Real.sqrt S₀)) 0 := by
    have := hSd.sqrt (by rw [hS0]; exact ne_of_gt hS)
    rwa [hS0] at this
  have hden : Real.sqrt (∑ j, (msub x j + 0 * msub v j) ^ 2) ≠ 0 := by
    rw [hS0]
    exact ne_of_gt (Real.sqrt_pos.mpr hS)
  have hq := hN.div hsqrt hden
  convert hq using 1
  rw [hS0]
  have hsq : Real.sqrt S₀ ^ 2 = S₀ := Real.sq_sqrt hS.le
  have hsqrt0 : Real.sqrt S₀ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hS)
  have hsum2 : ∑ j, 2 * msub x j * msub v j = 2 * c := by
    rw [hc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum2]
  simp only [zero_mul, add_zero]
  field_simp
  rw [hsq]
  ring

/-- The directional derivative is the Jacobian's action: the vector of
    derivatives equals lnJac x *ᵥ v. -/
theorem lnJac_mulVec (x v : Fin d → ℝ) (hd : 0 < d) (i : Fin d) :
    Matrix.mulVec (lnJac x) v i
      = Real.sqrt d / Real.sqrt (∑ j, msub x j ^ 2)
        * (msub v i - msub x i * (∑ j, msub x j * msub v j) / ∑ j, msub x j ^ 2) := by
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [Matrix.mulVec, dotProduct, lnJac]
  rw [sum_msub_mul_msub]
  have hexp : ∀ j, Real.sqrt d / Real.sqrt (∑ k, msub x k ^ 2)
        * ((if i = j then 1 else 0) - 1 / d - msub x i * msub x j / ∑ k, msub x k ^ 2) * v j
      = Real.sqrt d / Real.sqrt (∑ k, msub x k ^ 2)
        * ((if i = j then v j else 0) - v j / d
          - msub x i * (msub x j * v j) / ∑ k, msub x k ^ 2) := by
    intro j
    by_cases h : i = j <;> simp [h] <;> ring
  rw [Finset.sum_congr rfl fun j _ => hexp j, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ i),
    ← Finset.sum_div, ← Finset.sum_div, ← Finset.mul_sum]
  unfold msub vmean
  ring

/-- The dead component of the backward action, exactly: the dead
    input passes with the factor (1/σ)(1 − 1/d − ẑ_h²/d) and the live
    components are injected through the mean subtraction and the
    ẑ-projection. -/
theorem ln_jacobian_dead_component (x δ : Fin d → ℝ) (hd : 0 < d) (h : Fin d) :
    Matrix.mulVec (lnJac x) δ h
      = Real.sqrt d / Real.sqrt (∑ k, msub x k ^ 2)
        * ((1 - 1 / d - msub x h ^ 2 / ∑ k, msub x k ^ 2) * δ h
          - (1 / d) * ∑ j ∈ Finset.univ.erase h, δ j
          - (msub x h / ∑ k, msub x k ^ 2) * ∑ j ∈ Finset.univ.erase h, msub x j * δ j) := by
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [Matrix.mulVec, dotProduct, lnJac, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.add_sum_erase Finset.univ
    (fun j => ((if h = j then (1:ℝ) else 0) - 1 / d
      - msub x h * msub x j / ∑ k, msub x k ^ 2) * δ j) (Finset.mem_univ h)]
  congr 1
  rw [if_pos rfl]
  have hrest : ∑ j ∈ Finset.univ.erase h,
      ((if h = j then (1:ℝ) else 0) - 1 / d - msub x h * msub x j / ∑ k, msub x k ^ 2) * δ j
      = -(1 / d) * ∑ j ∈ Finset.univ.erase h, δ j
        - (msub x h / ∑ k, msub x k ^ 2) * ∑ j ∈ Finset.univ.erase h, msub x j * δ j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hne : h ≠ j := fun heq => (Finset.mem_erase.mp hj).1 heq.symm
    rw [if_neg hne]
    ring
  rw [hrest]
  ring

/-- The bracket's lower end: with no live components the dead input
    passes with a t-free factor; it is positive whenever the dead
    activation does not dominate, ẑ_h² < d − 1. -/
theorem ln_jacobian_dead_passes (x δ : Fin d → ℝ) (hd : 0 < d) (h : Fin d)
    (hlive : ∀ j, j ≠ h → δ j = 0) :
    Matrix.mulVec (lnJac x) δ h
      = Real.sqrt d / Real.sqrt (∑ k, msub x k ^ 2)
        * (1 - 1 / d - msub x h ^ 2 / ∑ k, msub x k ^ 2) * δ h := by
  rw [ln_jacobian_dead_component x δ hd h]
  have h1 : ∑ j ∈ Finset.univ.erase h, δ j = 0 :=
    Finset.sum_eq_zero fun j hj => hlive j (Finset.mem_erase.mp hj).1
  have h2 : ∑ j ∈ Finset.univ.erase h, msub x j * δ j = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [hlive j (Finset.mem_erase.mp hj).1, mul_zero]
  rw [h1, h2]
  ring

/-- The bracket's plateau end: with the dead input fully decayed, the
    dead output is the live injection, an amplitude of order 1/σ with
    no chain power at all, the same leak form as the rotation
    witness. -/
theorem ln_jacobian_leak (x δ : Fin d → ℝ) (hd : 0 < d) (h : Fin d)
    (hdead : δ h = 0) :
    Matrix.mulVec (lnJac x) δ h
      = -(Real.sqrt d / Real.sqrt (∑ k, msub x k ^ 2))
        * ((1 / d) * ∑ j ∈ Finset.univ.erase h, δ j
          + (msub x h / ∑ k, msub x k ^ 2) * ∑ j ∈ Finset.univ.erase h, msub x j * δ j) := by
  rw [ln_jacobian_dead_component x δ hd h, hdead]
  ring

end DeadDirections
