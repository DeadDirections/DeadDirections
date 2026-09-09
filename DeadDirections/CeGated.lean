/-
  Cross-entropy composition through the nonlinear channels: the
  joint gate-and-gradient model.

  thm:bridge_ce composes the cross-entropy head base case with the
  backward ladder; the linear-class composition is ce_bridge_composed.
  The nonlinear channels add a survival gate, and the composed moment
  then depends on the joint law of the gate and the output gradient:
  E[g·δ_h²], not E[g]·E[δ_h²]. The joint gate-and-gradient model
  enters as one hypothesis, a gated base floor q·E[δ_h²] ≤ E[g·δ_h²]
  (independence gives it with q the survival probability, and any
  positive correlation between surviving and a large gradient only
  raises it). Under it the gated chain reads the same ladder with the
  base case scaled by q: the dead G-entry at the probe is at least
  (∏c)²·q·c₀(1 − 1/C)·t^{2Σk}.
-/
import Mathlib.Probability.Independence.Integration
import DeadDirections.CeHead
import DeadDirections.BridgeComposition

namespace DeadDirections

open MeasureTheory ProbabilityTheory Filter Topology Matrix

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The dead-axis reading of the head Hessian is the second moment of
    the dead output-gradient component. -/
lemma head_dead_axis_eq_moment (H : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (δ : Ω → Fin (n+1) → ℝ)
    (hH : ∀ v : Fin (n+1) → ℝ,
      v ⬝ᵥ H.mulVec v = ∫ ω, (∑ i, v i * δ ω i) ^ 2 ∂μ) :
    (Pi.single (Fin.last n) 1 : Fin (n+1) → ℝ) ⬝ᵥ
        H.mulVec (Pi.single (Fin.last n) 1)
      = ∫ ω, (δ ω (Fin.last n)) ^ 2 ∂μ := by
  rw [hH]
  congr 1
  funext ω
  congr 1
  have hterm : ∀ i : Fin (n+1),
      (Pi.single (Fin.last n) 1 : Fin (n+1) → ℝ) i * δ ω i
      = if i = Fin.last n then δ ω i else 0 := by
    intro i
    rw [Pi.single_apply]
    by_cases hi : i = Fin.last n <;> simp [hi]
  rw [Finset.sum_congr rfl fun i _ => hterm i,
    Finset.sum_ite_eq' Finset.univ (Fin.last n) (δ ω)]
  simp

/-- thm:bridge_ce through the nonlinear channels, the joint
    gate-and-gradient model: with the head Hessian carrying the ones
    vector in its kernel on both sides and the non-degeneracy constant
    c₀ on {1}^⊥, and the gated base floor q·E[δ_h²] ≤ E[g·δ_h²], the
    gated chain's dead moment is at least
    (∏c)²·q·c₀(1 − 1/C)·t^{2Σk}. -/
theorem ce_gated_chain_lower {c₀ q : ℝ} (_hc₀ : 0 ≤ c₀) (hq : 0 ≤ q)
    (H : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (δ : Ω → Fin (n+1) → ℝ)
    (hH : ∀ v : Fin (n+1) → ℝ,
      v ⬝ᵥ H.mulVec v = ∫ ω, (∑ i, v i * δ ω i) ^ 2 ∂μ)
    (hker : H.mulVec (fun _ => 1) = 0)
    (hkerL : Matrix.vecMul (fun _ => (1:ℝ)) H = 0)
    (hass : ∀ v : Fin (n+1) → ℝ, (∑ i, v i) = 0 →
      c₀ * ∑ i, v i ^ 2 ≤ v ⬝ᵥ H.mulVec v)
    (g : Ω → ℝ) (hg : ∀ ω, g ω = 0 ∨ g ω = 1)
    (hjoint : q * ∫ ω, (δ ω (Fin.last n)) ^ 2 ∂μ
      ≤ ∫ ω, g ω * (δ ω (Fin.last n)) ^ 2 ∂μ)
    {bs : List (ℝ × ℕ)} (hbs : bs ≠ []) (t : ℝ) :
    chainCoeff bs ^ 2 * t ^ (2 * chainRate bs)
        * (q * (c₀ * (1 - 1 / ((n:ℝ) + 1))))
      ≤ ∫ ω, composedSignal bs g (fun ω => δ ω (Fin.last n)) t ω ^ 2 ∂μ := by
  rw [composedSignal_sq_integral g _ hg hbs t]
  have hbase := ce_dead_lower (C := n + 1) H (by omega) hker hkerL
    hass (Fin.last n)
  rw [head_dead_axis_eq_moment H δ hH] at hbase
  have hcast : ((n + 1 : ℕ) : ℝ) = (n:ℝ) + 1 := by push_cast; rfl
  rw [hcast] at hbase
  have hA : 0 ≤ chainCoeff bs ^ 2 * t ^ (2 * chainRate bs) :=
    mul_nonneg (sq_nonneg _) ((even_two_mul _).pow_nonneg t)
  have hB : q * (c₀ * (1 - 1 / ((n:ℝ) + 1)))
      ≤ ∫ ω, g ω * (δ ω (Fin.last n)) ^ 2 ∂μ :=
    le_trans (mul_le_mul_of_nonneg_left hbase hq) hjoint
  exact mul_le_mul_of_nonneg_left hB hA

/-- Independence supplies the joint model: with the gate independent
    of the dead output-gradient component, the gated base floor holds
    with q the survival probability E[g], and the gated chain reads
    (∏c)²·E[g]·c₀(1 − 1/C)·t^{2Σk}. -/
theorem ce_gated_chain_lower_of_indep {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (H : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (δ : Ω → Fin (n+1) → ℝ)
    (hH : ∀ v : Fin (n+1) → ℝ,
      v ⬝ᵥ H.mulVec v = ∫ ω, (∑ i, v i * δ ω i) ^ 2 ∂μ)
    (hker : H.mulVec (fun _ => 1) = 0)
    (hkerL : Matrix.vecMul (fun _ => (1:ℝ)) H = 0)
    (hass : ∀ v : Fin (n+1) → ℝ, (∑ i, v i) = 0 →
      c₀ * ∑ i, v i ^ 2 ≤ v ⬝ᵥ H.mulVec v)
    (g : Ω → ℝ) (hg : ∀ ω, g ω = 0 ∨ g ω = 1)
    (hgm : AEStronglyMeasurable g μ)
    (hδm : AEStronglyMeasurable (fun ω => δ ω (Fin.last n)) μ)
    (hind : g ⟂ᵢ[μ] fun ω => δ ω (Fin.last n))
    {bs : List (ℝ × ℕ)} (hbs : bs ≠ []) (t : ℝ) :
    chainCoeff bs ^ 2 * t ^ (2 * chainRate bs)
        * ((∫ ω, g ω ∂μ) * (c₀ * (1 - 1 / ((n:ℝ) + 1))))
      ≤ ∫ ω, composedSignal bs g (fun ω => δ ω (Fin.last n)) t ω ^ 2 ∂μ := by
  have hq : 0 ≤ ∫ ω, g ω ∂μ :=
    integral_nonneg fun ω => by rcases hg ω with h | h <;> rw [h] <;> norm_num
  have hind2 : g ⟂ᵢ[μ] fun ω => (δ ω (Fin.last n)) ^ 2 := by
    have h := hind.comp measurable_id (measurable_id.pow_const 2)
    exact h
  have hprod : ∫ ω, g ω * (δ ω (Fin.last n)) ^ 2 ∂μ
      = (∫ ω, g ω ∂μ) * ∫ ω, (δ ω (Fin.last n)) ^ 2 ∂μ :=
    hind2.integral_fun_mul_eq_mul_integral hgm (hδm.pow 2)
  exact ce_gated_chain_lower hc₀ hq H δ hH hker hkerL hass g hg
    (le_of_eq hprod.symm) hbs t

end DeadDirections
