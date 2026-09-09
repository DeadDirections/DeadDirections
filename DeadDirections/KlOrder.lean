/-
  KL order as a trajectory invariant (def:dead_direction's bridge
  invariant, phrased on the curve).

  A curve of models has KL order k when its divergence from the base
  point has exact leading rate 2k with positive coefficient. This is
  the quantity both traditions read: Watanabe through the normal form,
  Amari through the Fisher slope 2(k−1). The Gaussian location curve
  is the certified instance: `curveKL_hasKLOrder` pairs with
  `curveFisher_hasLeadingRate` in `gaussian_curve_readings`, and the
  mixture instantiation of MixtureScore.lean reads the same invariant
  through the Fisher side at k = 2.
-/
import DeadDirections.FisherDecay
import DeadDirections.GaussianFisher

namespace DeadDirections

open Filter Topology

/-- A KL trajectory has order k when K(t) = c·t^{2k} + o(t^{2k}) with
    c > 0 as t → 0⁺. -/
def HasKLOrder (K : ℝ → ℝ) (k : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ HasLeadingRate K (2 * k) c

/-- The Gaussian curve μ(t) = t^k has KL order k: its divergence is
    t^{2k}/2 exactly. -/
theorem curveKL_hasKLOrder (k : ℕ) : HasKLOrder (curveKL k) k := by
  refine ⟨1/2, by norm_num, ?_⟩
  have h : Filter.Tendsto (fun _ : ℝ => (1/2 : ℝ)) (𝓝[>] (0:ℝ))
      (𝓝 (1/2)) := tendsto_const_nhds
  refine h.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  rw [curveKL_eq]
  have htp : t ^ (2 * k) ≠ 0 := ne_of_gt (pow_pos ht _)
  field_simp

/-- The two readings agree on the worked family: the curve has KL
    order k, and its moving-measure Fisher carries leading rate
    2(k−1) with coefficient k². -/
theorem gaussian_curve_readings (k : ℕ) :
    HasKLOrder (curveKL k) k
      ∧ HasLeadingRate (curveFisher k) (2 * (k - 1)) ((k:ℝ) ^ 2) :=
  ⟨curveKL_hasKLOrder k, curveFisher_hasLeadingRate k⟩

end DeadDirections
