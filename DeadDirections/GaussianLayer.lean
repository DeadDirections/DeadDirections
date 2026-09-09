/-
  The Gaussian-expectation layer.

  Three hypothesis classes recur across the bridge rows as
  assumptions on moments: the MSE output base case (the σ⁻² noise
  computation enters the linear-model rows as moment hypotheses on
  the output gradient), the second-moment normalisations, and the
  almost-sure non-degeneracy of weighted averages. This module
  discharges them at the measure level: the second moment of the
  centred Gaussian is its variance parameter, the MSE base case is
  exact on the independent product (the squared residual of the dead
  output c·x against the noise target integrates to c² + v, the
  cross term vanishing by independence and zero mean), and any
  non-zero weighted-sum reading is non-degenerate off a null set,
  because its zero set is the kernel of a non-zero linear functional
  and proper submodules are Haar-null.
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import DeadDirections.FisherDecay
import DeadDirections.DeepLinearBridge

namespace DeadDirections

open MeasureTheory ProbabilityTheory

/-- The second moment of the centred Gaussian is its variance
    parameter. -/
lemma integral_sq_gaussianReal (v : NNReal) :
    ∫ x, x ^ 2 ∂gaussianReal 0 v = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

lemma integrable_sq_gaussianReal (v : NNReal) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
  have h := memLp_id_gaussianReal (μ := 0) (v := v) 2
  have h2 := h.integrable_sq
  simpa using h2

lemma integrable_id_gaussianReal (v : NNReal) :
    Integrable (fun x : ℝ => x) (gaussianReal 0 v) := by
  have h := memLp_id_gaussianReal (μ := 0) (v := v) 1
  exact memLp_one_iff_integrable.mp (by simpa using h)

/-- The MSE base case, exact on the independent product: the squared
    residual of the dead output c·x against the noise target
    integrates to c² + v. The cross term vanishes by independence
    and zero mean; this is the moment hypothesis the linear-model
    backward rows consume. -/
theorem mse_base_case (c : ℝ) (v : NNReal) :
    ∫ z : ℝ × ℝ, (c * z.1 - z.2) ^ 2
      ∂((gaussianReal 0 (1 : NNReal)).prod (gaussianReal 0 v))
      = c ^ 2 + v := by
  set μ1 := gaussianReal 0 (1 : NNReal) with hμ1
  set μ2 := gaussianReal 0 v with hμ2
  have hexp : ∀ z : ℝ × ℝ, (c * z.1 - z.2) ^ 2
      = c ^ 2 * z.1 ^ 2 + ((-2 * c) * z.1) * z.2 + z.2 ^ 2 :=
    fun z => by ring
  have h1 : Integrable (fun z : ℝ × ℝ => c ^ 2 * z.1 ^ 2)
      (μ1.prod μ2) :=
    ((integrable_sq_gaussianReal _).const_mul (c ^ 2)).comp_fst μ2
  have h2 : Integrable (fun z : ℝ × ℝ => ((-2 * c) * z.1) * z.2)
      (μ1.prod μ2) :=
    Integrable.mul_prod
      ((integrable_id_gaussianReal _).const_mul (-2 * c))
      (integrable_id_gaussianReal v)
  have h3 : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) (μ1.prod μ2) :=
    (integrable_sq_gaussianReal v).comp_snd μ1
  calc ∫ z : ℝ × ℝ, (c * z.1 - z.2) ^ 2 ∂(μ1.prod μ2)
      = ∫ z : ℝ × ℝ, (c ^ 2 * z.1 ^ 2 + ((-2 * c) * z.1) * z.2
          + z.2 ^ 2) ∂(μ1.prod μ2) := by
        congr 1
        funext z
        exact hexp z
    _ = (∫ z : ℝ × ℝ, (c ^ 2 * z.1 ^ 2 + ((-2 * c) * z.1) * z.2)
          ∂(μ1.prod μ2))
        + ∫ z : ℝ × ℝ, z.2 ^ 2 ∂(μ1.prod μ2) :=
        integral_add (h1.add h2) h3
    _ = (∫ z : ℝ × ℝ, c ^ 2 * z.1 ^ 2 ∂(μ1.prod μ2))
        + (∫ z : ℝ × ℝ, ((-2 * c) * z.1) * z.2 ∂(μ1.prod μ2))
        + ∫ z : ℝ × ℝ, z.2 ^ 2 ∂(μ1.prod μ2) := by
        rw [integral_add h1 h2]
    _ = c ^ 2 + 0 + v := by
        have hfst : ∫ z : ℝ × ℝ, c ^ 2 * z.1 ^ 2 ∂(μ1.prod μ2)
            = c ^ 2 := by
          have hp := integral_prod_mul (μ := μ1) (ν := μ2)
            (f := fun x => c ^ 2 * x ^ 2) (g := fun _ => (1:ℝ))
          beta_reduce at hp
          rw [show (fun z : ℝ × ℝ => c ^ 2 * z.1 ^ 2)
              = fun z : ℝ × ℝ => c ^ 2 * z.1 ^ 2 * 1 from
              funext fun z => (mul_one _).symm]
          rw [hp, integral_const_mul, integral_sq_gaussianReal]
          simp
        have hcross : ∫ z : ℝ × ℝ, ((-2 * c) * z.1) * z.2
            ∂(μ1.prod μ2) = 0 := by
          have hp := integral_prod_mul (μ := μ1) (ν := μ2)
            (f := fun x => (-2 * c) * x) (g := fun y => y)
          beta_reduce at hp
          rw [hp]
          have hm : ∫ y : ℝ, y ∂μ2 = 0 := by
            rw [hμ2]
            simp
          rw [hm, mul_zero]
        have hsnd : ∫ z : ℝ × ℝ, z.2 ^ 2 ∂(μ1.prod μ2) = v := by
          have hp := integral_prod_mul (μ := μ1) (ν := μ2)
            (f := fun _ => (1:ℝ)) (g := fun y => y ^ 2)
          beta_reduce at hp
          rw [show (fun z : ℝ × ℝ => z.2 ^ 2)
              = fun z : ℝ × ℝ => 1 * z.2 ^ 2 from
              funext fun z => (one_mul _).symm]
          rw [hp, integral_sq_gaussianReal]
          simp
        rw [hfst, hcross, hsnd]
    _ = c ^ 2 + v := by ring

/-- The zero set of a non-zero weighted-sum reading is Haar-null:
    the almost-sure non-degeneracy behind the Θ(1) coefficients. -/
theorem hyperplane_null {n : ℕ} (a : Fin n → ℝ) (ha : a ≠ 0) :
    volume {x : Fin n → ℝ | ∑ i, a i * x i = 0} = 0 := by
  let φ : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ i, a i * x i
      map_add' := fun x y => by
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      map_smul' := fun r x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring }
  have hi : ∃ i, a i ≠ 0 := by
    by_contra h'
    push Not at h'
    exact ha (funext h')
  obtain ⟨i, hai⟩ := hi
  have hne : LinearMap.ker φ ≠ ⊤ := by
    intro htop
    have hmem : a ∈ LinearMap.ker φ := by
      rw [htop]
      trivial
    have hzero : ∑ j, a j * a j = 0 := hmem
    have hpos : 0 < ∑ j, a j * a j :=
      Finset.sum_pos' (fun j _ => mul_self_nonneg _)
        ⟨i, Finset.mem_univ i, mul_self_pos.mpr hai⟩
    linarith
  have h := Measure.addHaar_submodule
    (volume : Measure (Fin n → ℝ)) (LinearMap.ker φ) hne
  have hset : {x : Fin n → ℝ | ∑ i, a i * x i = 0}
      = (LinearMap.ker φ : Set (Fin n → ℝ)) := by
    ext x
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.mem_ker]
    rfl
  rw [hset]
  exact h

/-- The composed backward row: the dead-channel backward moment with
    the output gradient given by the Gaussian residual model. The
    chain contributes the amplitude t^K, the base case contributes
    c² + v, and the moment has leading rate 2K with coefficient
    exactly c² + v: the linear-model backward rows no longer assume
    their base case, they derive it through mse_base_case. -/
theorem backward_dead_moment (c : ℝ) (v : NNReal) (K : ℕ) :
    HasLeadingRate
      (fun t => ∫ z : ℝ × ℝ, (t ^ K * (c * z.1 - z.2)) ^ 2
        ∂((gaussianReal 0 (1 : NNReal)).prod (gaussianReal 0 v)))
      (2 * K) (c ^ 2 + v) := by
  have hpt : ∀ t : ℝ,
      (∫ z : ℝ × ℝ, (t ^ K * (c * z.1 - z.2)) ^ 2
        ∂((gaussianReal 0 (1 : NNReal)).prod (gaussianReal 0 v)))
      = (c ^ 2 + v) * t ^ (2 * K) := by
    intro t
    have hfun : (fun z : ℝ × ℝ => (t ^ K * (c * z.1 - z.2)) ^ 2)
        = fun z : ℝ × ℝ => (t ^ K) ^ 2 * (c * z.1 - z.2) ^ 2 :=
      funext fun z => by ring
    rw [hfun, integral_const_mul, mse_base_case]
    rw [← pow_mul]
    ring_nf
  have h := (hasLeadingRate_pow (2 * K)).const_mul (c ^ 2 + (v : ℝ))
  have h2 : HasLeadingRate
      (fun t => (c ^ 2 + (v : ℝ)) * t ^ (2 * K)) (2 * K)
      (c ^ 2 + v) := by simpa using h
  refine h2.congr fun t => ?_
  simp only [hpt]

/-- thm:bridge with its base case derived: on the independent Gaussian
    product, an output gradient whose dead component is the residual
    c·x − y composes with the canonical backward chain to the dead
    G-entry t^{2(L−ℓ)}·(c² + v) exactly, the ladder and the σ⁻²-type
    floor in one identity. -/
theorem mse_bridge_composed {n : ℕ} (c : ℝ) (v : NNReal) (L ℓ : ℕ) (t : ℝ)
    (δ : ℝ × ℝ → Fin (n+1) → ℝ)
    (hδ : ∀ z, δ z (Fin.last n) = c * z.1 - z.2) :
    ∫ z, ((canonicalLayer n t ^ (L - ℓ)).mulVec (δ z) (Fin.last n)) ^ 2
        ∂((gaussianReal 0 (1 : NNReal)).prod (gaussianReal 0 v))
      = t ^ (2 * (L - ℓ)) * (c ^ 2 + v) := by
  refine (deep_linear_backward_rate L ℓ t δ).trans ?_
  congr 1
  rw [← mse_base_case c v]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show δ z (Fin.last n) ^ 2 = (c * z.1 - z.2) ^ 2
  rw [hδ z]

end DeadDirections
