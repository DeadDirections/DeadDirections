/-
  The stochastic side of the quotient (cor:sgd_quotient), model
  level.

  Continuous-time SGD with metric-isotropic noise projects to the
  quotient with metric-isotropic noise, and the projection uses that
  the gauge orbits are minimal. At the scalar-chain model of
  Quotient the invariant metric is the log-coordinate Euclidean
  metric, the quotient coordinate is the sum of the log weights, and
  a gauge orbit is a straight line in the log chart along a direction
  of zero coordinate sum. Three facts carry the stochastic statement:
  the quotient coordinate of pairwise independent increments with
  common variance σ² has variance L·σ², the quotient-metric variance
  of isotropic noise (the quotient metric is 1/L in that coordinate);
  the quotient coordinate is uncorrelated with every vertical
  direction, so the noise splits along the horizontal-vertical
  decomposition; and the orbit lines have zero acceleration, which is
  minimality in the flat chart and kills the Itô drift correction.
-/
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Calculus.Deriv.Basic
import DeadDirections.Quotient

namespace DeadDirections

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

section NoiseProjection

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {L : ℕ}

/-- Pairwise independent increments with a common variance have a
    diagonal covariance table. -/
lemma covariance_table (ξ : Fin L → Ω → ℝ) (hL2 : ∀ i, MemLp (ξ i) 2 μ)
    (hind : Pairwise fun i j => ξ i ⟂ᵢ[μ] ξ j) {σ2 : ℝ}
    (hvar : ∀ i, Var[ξ i; μ] = σ2) (i j : Fin L) :
    cov[ξ i, ξ j; μ] = if i = j then σ2 else 0 := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, ← hvar i]
    first
      | exact covariance_self
      | exact covariance_self (hL2 i).aemeasurable
  · rw [if_neg h]
    exact (hind h).covariance_eq_zero (hL2 i) (hL2 j)

/-- The quotient coordinate of isotropic noise: with pairwise
    independent log-weight increments of common variance σ², the sum
    has variance L·σ², the isotropic variance for the quotient
    metric 1/L. -/
theorem quotient_noise_variance [IsFiniteMeasure μ] (ξ : Fin L → Ω → ℝ)
    (hL2 : ∀ i, MemLp (ξ i) 2 μ)
    (hind : Pairwise fun i j => ξ i ⟂ᵢ[μ] ξ j) {σ2 : ℝ}
    (hvar : ∀ i, Var[ξ i; μ] = σ2) :
    Var[fun ω => ∑ i, ξ i ω; μ] = L * σ2 := by
  rw [variance_fun_sum hL2]
  have hrow : ∀ i, (∑ j, cov[ξ i, ξ j; μ]) = σ2 := by
    intro i
    simp_rw [covariance_table ξ hL2 hind hvar i]
    simp
  simp_rw [hrow]
  simp [Finset.sum_const, Finset.card_univ]

/-- The quotient coordinate is uncorrelated with every vertical
    direction (coefficient sum zero): the noise splits along the
    horizontal-vertical decomposition. -/
theorem quotient_noise_vertical_uncorrelated [IsFiniteMeasure μ]
    (ξ : Fin L → Ω → ℝ) (hL2 : ∀ i, MemLp (ξ i) 2 μ)
    (hind : Pairwise fun i j => ξ i ⟂ᵢ[μ] ξ j) {σ2 : ℝ}
    (hvar : ∀ i, Var[ξ i; μ] = σ2) (a : Fin L → ℝ) (ha : ∑ i, a i = 0) :
    cov[∑ i, ξ i, ∑ i, a i • ξ i; μ] = 0 := by
  have hY : ∀ i, MemLp (a i • ξ i) 2 μ := fun i => (hL2 i).const_smul (a i)
  rw [covariance_sum_left hL2 (memLp_finset_sum' _ fun i _ => hY i)]
  have hrow : ∀ i, cov[ξ i, ∑ j, a j • ξ j; μ] = a i * σ2 := by
    intro i
    rw [covariance_sum_right hY (hL2 i)]
    simp_rw [covariance_smul_right, covariance_table ξ hL2 hind hvar]
    simp [mul_ite]
  simp_rw [hrow]
  rw [← Finset.sum_mul, ha, zero_mul]

end NoiseProjection

section OrbitLines

variable {L : ℕ}

/-- A gauge orbit in the log chart: the line through x along a
    direction v of zero coordinate sum (the log of a unit-product
    rescaling). -/
def orbitLine (x v : Fin L → ℝ) (s : ℝ) : Fin L → ℝ := x + s • v

lemma orbitLine_hasDerivAt (x v : Fin L → ℝ) (s : ℝ) :
    HasDerivAt (orbitLine x v) v s := by
  unfold orbitLine
  have h := ((hasDerivAt_id s).smul_const v).const_add x
  simpa using h

/-- Orbit lines have zero acceleration: the velocity is constant, so
    the orbits are minimal in the flat invariant chart and the Itô
    correction to the projected drift vanishes. -/
lemma orbitLine_accel_zero (v : Fin L → ℝ) (s : ℝ) :
    HasDerivAt (fun _ : ℝ => v) 0 s :=
  hasDerivAt_const s v

/-- The orbit direction is vertical: its coordinate sum is zero
    exactly when the rescaling has unit product, the log form of
    prodMap_gauge_invariant. -/
lemma orbitLine_sum (x v : Fin L → ℝ) (hv : ∑ i, v i = 0) (s : ℝ) :
    ∑ i, orbitLine x v s i = ∑ i, x i := by
  unfold orbitLine
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hv, mul_zero, add_zero]

end OrbitLines

end DeadDirections
