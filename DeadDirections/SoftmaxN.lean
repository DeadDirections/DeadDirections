/-
  The N-position softmax and its Jacobian.

  The two-position logistic model of AttnBridge upgrades here to the
  full softmax row on N+1 positions. The Jacobian is certified as a
  directional derivative: along direction h the i-th component moves
  by aᵢ(hᵢ − ⟨a, h⟩), the diag(a) − a aᵀ action of the paper. Its
  structural consequences follow exactly: constant directions are
  killed (the shift gauge zero of the softmax), and at uniform scores
  the Jacobian is the centred projector scaled by 1/(N+1), the
  sequence-space projector J^∞ = P_seq/N_seq of the attention
  extension. The forward-rate consumer replaces the logistic with the
  true softmax row: the dead output is t² times the A₀-weighted
  average with the attention weights moving continuously in t².
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import DeadDirections.FisherDecay

namespace DeadDirections

open Filter Topology

variable {N : ℕ}

/-- The softmax row on N+1 positions. -/
noncomputable def softmaxN (z : Fin (N+1) → ℝ) (i : Fin (N+1)) : ℝ :=
  Real.exp (z i) / ∑ j, Real.exp (z j)

lemma sum_exp_pos (z : Fin (N+1) → ℝ) :
    0 < ∑ j, Real.exp (z j) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem softmaxN_pos (z : Fin (N+1) → ℝ) (i : Fin (N+1)) :
    0 < softmaxN z i :=
  div_pos (Real.exp_pos _) (sum_exp_pos z)

theorem softmaxN_sum_one (z : Fin (N+1) → ℝ) :
    ∑ i, softmaxN z i = 1 := by
  unfold softmaxN
  rw [← Finset.sum_div, div_self (ne_of_gt (sum_exp_pos z))]

theorem softmaxN_continuous (i : Fin (N+1)) :
    Continuous (fun z : Fin (N+1) → ℝ => softmaxN z i) := by
  unfold softmaxN
  apply Continuous.div
  · exact Real.continuous_exp.comp (continuous_apply i)
  · exact continuous_finset_sum _
      (fun j _ => Real.continuous_exp.comp (continuous_apply j))
  · intro z
    exact ne_of_gt (sum_exp_pos z)

/-- The quantitative bound at the operating point, multiplicative
    form: a perturbation bounded by ε moves every softmax entry by a
    factor between e^{−2ε} and e^{2ε}. Exact, with no derivative:
    the numerator and denominator each move by at most e^{±ε}. -/
theorem softmaxN_ratio_bound (z d : Fin (N+1) → ℝ) {ε : ℝ}
    (hd : ∀ j, |d j| ≤ ε) (i : Fin (N+1)) :
    Real.exp (-(2*ε)) * softmaxN z i
        ≤ softmaxN (fun j => z j + d j) i
      ∧ softmaxN (fun j => z j + d j) i
        ≤ Real.exp (2*ε) * softmaxN z i := by
  have hDz : (0:ℝ) < ∑ j, Real.exp (z j) := sum_exp_pos z
  have hDz' : (0:ℝ) < ∑ j, Real.exp (z j + d j) := sum_exp_pos _
  have hnlo : Real.exp (z i) * Real.exp (-ε)
      ≤ Real.exp (z i + d i) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hd i)).1])
  have hnhi : Real.exp (z i + d i)
      ≤ Real.exp (z i) * Real.exp ε := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hd i)).2])
  have hdlo : (∑ j, Real.exp (z j)) * Real.exp (-ε)
      ≤ ∑ j, Real.exp (z j + d j) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hd j)).1])
  have hdhi : (∑ j, Real.exp (z j + d j))
      ≤ (∑ j, Real.exp (z j)) * Real.exp ε := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hd j)).2])
  constructor
  · have h := div_le_div₀ (le_of_lt (Real.exp_pos _)) hnlo hDz' hdhi
    calc Real.exp (-(2*ε)) * softmaxN z i
        = (Real.exp (z i) * Real.exp (-ε))
          / ((∑ j, Real.exp (z j)) * Real.exp ε) := by
          show Real.exp (-(2*ε))
              * (Real.exp (z i) / ∑ j, Real.exp (z j)) = _
          rw [← div_mul_div_comm, ← Real.exp_sub]
          rw [show -ε - ε = -(2*ε) by ring]
          ring
      _ ≤ Real.exp (z i + d i) / ∑ j, Real.exp (z j + d j) := h
  · have h := div_le_div₀ (by positivity) hnhi
      (by positivity : (0:ℝ) < (∑ j, Real.exp (z j))
        * Real.exp (-ε)) hdlo
    calc softmaxN (fun j => z j + d j) i
        ≤ (Real.exp (z i) * Real.exp ε)
          / ((∑ j, Real.exp (z j)) * Real.exp (-ε)) := h
      _ = Real.exp (2*ε) * softmaxN z i := by
          show _ = Real.exp (2*ε)
              * (Real.exp (z i) / ∑ j, Real.exp (z j))
          rw [← div_mul_div_comm, ← Real.exp_sub]
          rw [show ε - -ε = 2*ε by ring]
          ring

/-- The additive Lipschitz bound at the operating point: the entry
    moves by at most (e^{2ε} − 1) times its own value, which is the
    operating-point dependence the attention theorems name. -/
theorem softmaxN_abs_sub_le (z d : Fin (N+1) → ℝ) {ε : ℝ}
    (hd : ∀ j, |d j| ≤ ε) (i : Fin (N+1)) :
    |softmaxN (fun j => z j + d j) i - softmaxN z i|
      ≤ (Real.exp (2*ε) - 1) * softmaxN z i := by
  obtain ⟨hlo, hhi⟩ := softmaxN_ratio_bound z d hd i
  have hpos := softmaxN_pos z i
  have hconv : 1 - Real.exp (-(2*ε)) ≤ Real.exp (2*ε) - 1 := by
    have hu : (0:ℝ) < Real.exp (2*ε) := Real.exp_pos _
    have hinv : Real.exp (-(2*ε)) = (Real.exp (2*ε))⁻¹ :=
      Real.exp_neg _
    rw [hinv]
    nlinarith [mul_inv_cancel₀ (ne_of_gt hu),
      sq_nonneg (Real.exp (2*ε) - 1), inv_pos.mpr hu]
  apply abs_le.mpr
  constructor
  · have h2 : (Real.exp (-(2*ε)) - 1) * softmaxN z i
        ≤ softmaxN (fun j => z j + d j) i - softmaxN z i := by
      nlinarith
    have h3 : -((Real.exp (2*ε) - 1) * softmaxN z i)
        ≤ (Real.exp (-(2*ε)) - 1) * softmaxN z i := by
      nlinarith
    linarith
  · nlinarith

/-- The softmax Jacobian, certified: along direction h the i-th
    component moves by aᵢ(hᵢ − ⟨a, h⟩), the diag(a) − a aᵀ action. -/
theorem softmaxN_hasDerivAt_dir (z h : Fin (N+1) → ℝ)
    (i : Fin (N+1)) :
    HasDerivAt (fun s : ℝ => softmaxN (fun j => z j + s * h j) i)
      (softmaxN z i * (h i - ∑ j, softmaxN z j * h j)) 0 := by
  have hlin : ∀ j, HasDerivAt (fun s : ℝ => z j + s * h j) (h j) 0 := by
    intro j
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (h j)).const_add (z j)
  have hexpj : ∀ j, HasDerivAt
      (fun s : ℝ => Real.exp (z j + s * h j))
      (Real.exp (z j) * h j) 0 := by
    intro j
    have h := (hlin j).exp
    simpa using h
  have hden : HasDerivAt
      (fun s : ℝ => ∑ j, Real.exp (z j + s * h j))
      (∑ j, Real.exp (z j) * h j) 0 :=
    HasDerivAt.fun_sum (fun j _ => hexpj j)
  have hquot := (hexpj i).div hden (ne_of_gt (by
    simpa using sum_exp_pos z))
  have hfun : (fun s : ℝ => softmaxN (fun j => z j + s * h j) i)
      = fun s : ℝ => Real.exp (z i + s * h i)
        / ∑ j, Real.exp (z j + s * h j) := by
    funext s
    unfold softmaxN
    rfl
  rw [hfun]
  have hval : (Real.exp (z i) * h i * ∑ j, Real.exp (z j + 0 * h j)
        - Real.exp (z i + 0 * h i) * ∑ j, Real.exp (z j) * h j)
      / (∑ j, Real.exp (z j + 0 * h j)) ^ 2
      = softmaxN z i * (h i - ∑ j, softmaxN z j * h j) := by
    have hS : ∀ j, z j + 0 * h j = z j := fun j => by ring
    simp only [hS]
    unfold softmaxN
    have hSne : (∑ j, Real.exp (z j)) ≠ 0 :=
      ne_of_gt (sum_exp_pos z)
    have hsum : ∑ j, Real.exp (z j) / (∑ k, Real.exp (z k)) * h j
        = (∑ j, Real.exp (z j) * h j) / (∑ k, Real.exp (z k)) :=
      calc ∑ j, Real.exp (z j) / (∑ k, Real.exp (z k)) * h j
          = ∑ j, Real.exp (z j) * h j / (∑ k, Real.exp (z k)) :=
            Finset.sum_congr rfl fun j _ => by ring
        _ = (∑ j, Real.exp (z j) * h j) / (∑ k, Real.exp (z k)) :=
            (Finset.sum_div _ _ _).symm
    rw [hsum]
    field_simp
  rw [← hval]
  simpa using hquot

/-- The Jacobian kills constant directions: the shift gauge zero of
    the softmax. -/
theorem softmaxN_jacobian_const (z : Fin (N+1) → ℝ) (i : Fin (N+1))
    (c : ℝ) :
    softmaxN z i * (c - ∑ j, softmaxN z j * c) = 0 := by
  rw [← Finset.sum_mul, softmaxN_sum_one, one_mul, sub_self,
    mul_zero]

/-- Uniform scores give the uniform row. -/
theorem softmaxN_uniform (c : ℝ) (i : Fin (N+1)) :
    softmaxN (fun _ => c) i = 1 / (N + 1) := by
  unfold softmaxN
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  rw [div_mul_eq_div_div_swap, div_self (ne_of_gt (Real.exp_pos c))]

/-- At uniform scores the Jacobian is the centred projector scaled
    by 1/(N+1): the sequence-space projector of the attention
    extension. -/
theorem softmaxN_uniform_jacobian (c : ℝ) (h : Fin (N+1) → ℝ)
    (i : Fin (N+1)) :
    softmaxN (fun _ => c) i
        * (h i - ∑ j, softmaxN (fun _ => c) j * h j)
      = 1 / (N + 1) * (h i - (∑ j, h j) / (N + 1)) := by
  rw [softmaxN_uniform]
  congr 1
  congr 1
  calc ∑ j, softmaxN (fun _ => c) j * h j
      = ∑ j, h j / (N + 1) := Finset.sum_congr rfl fun j _ => by
        rw [softmaxN_uniform]
        ring
    _ = (∑ j, h j) / (N + 1) := (Finset.sum_div _ _ _).symm

/-- thm:bridge_attn at N positions: the dead output is t² times the
    A₀-weighted average, with the attention weights moving
    continuously in t² through the true softmax row. Forward block
    rate 2 with the theorem's coefficient. -/
theorem bridge_attn_forward_N (S B x : Fin (N+1) → ℝ) :
    HasLeadingRate
      (fun t => t ^ 2
        * ∑ m, softmaxN (fun j => S j + t ^ 2 * B j) m * x m) 2
      (∑ m, softmaxN S m * x m) := by
  have hg : ContinuousAt
      (fun t : ℝ => ∑ m, softmaxN (fun j => S j + t ^ 2 * B j) m
        * x m) 0 := by
    have hc : Continuous (fun t : ℝ =>
        ∑ m, softmaxN (fun j => S j + t ^ 2 * B j) m * x m) := by
      apply continuous_finset_sum
      intro m _
      apply Continuous.mul _ continuous_const
      exact (softmaxN_continuous m).comp
        (by continuity :
          Continuous (fun t : ℝ => fun j => S j + t ^ 2 * B j))
    exact hc.continuousAt
  have h := hasLeadingRate_pow_factor 2 hg
  have hval : (∑ m, softmaxN (fun j => S j + (0:ℝ) ^ 2 * B j) m
      * x m) = ∑ m, softmaxN S m * x m := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show (fun j => S j + (0:ℝ) ^ 2 * B j) = S from
      funext fun j => by ring]
  rw [hval] at h
  exact h

end DeadDirections
