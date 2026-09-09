/-
  The gauge quotient (theory paper, lem:quotient_F, cor:quotient_rate,
  cor:sgd_quotient, cor:ddcadam_quotient_rate), scalar L-layer model.

  The rescaling gauge acts on the layer scalars by product-one
  families, the quotient coordinate is the layer product, and every
  mechanism of the quotient corollaries is exact here. The score of
  the quotient coordinate annihilates the vertical directions at
  every point (lem:quotient_F): the layer-weighted score is the
  product itself, so the vertical pairing is the product times the
  gauge trace, zero. The horizontal Fisher reading at the symmetric
  point is L·t^{2(L−1)}: the quotient rate. Euclidean SGD fails to
  project (the horizontal metric factor varies along an orbit, with
  an explicit L = 2 witness), the log-coordinate invariant metric
  projects exactly (the flow factor is L·p², a function of the
  quotient coordinate alone), and any gauge-equivariant update has a
  gauge-independent projected readout, which is what the DDCAdam
  corollary needs from the optimizer.
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import DeadDirections.FisherDecay

namespace DeadDirections

open Filter Topology

variable {L : ℕ}

/-- The quotient coordinate: the layer product. -/
def prodMap (w : Fin L → ℝ) : ℝ := ∏ i, w i

/-- Gauge invariance: product-one scalings fix the quotient
    coordinate. -/
theorem prodMap_gauge_invariant (w lam : Fin L → ℝ)
    (hlam : ∏ i, lam i = 1) :
    prodMap (fun i => lam i * w i) = prodMap w := by
  unfold prodMap
  rw [Finset.prod_mul_distrib, hlam, one_mul]

/-- The score of the quotient coordinate: the erased product. -/
def prodGrad (w : Fin L → ℝ) (i : Fin L) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, w j

/-- The score is certified as the partial derivative of the quotient
    coordinate in the i-th layer. -/
lemma prodMap_hasDerivAt (w : Fin L → ℝ) (i : Fin L) :
    HasDerivAt (fun s => prodMap (Function.update w i s))
      (prodGrad w i) (w i) := by
  have hval : ∀ s, prodMap (Function.update w i s)
      = s * prodGrad w i := by
    intro s
    unfold prodMap prodGrad
    rw [Finset.prod_update_of_mem (Finset.mem_univ i),
      ← Finset.erase_eq]
  have heq : (fun s => prodMap (Function.update w i s))
      = fun s => s * prodGrad w i := funext hval
  rw [heq]
  simpa using (hasDerivAt_id (w i)).mul_const (prodGrad w i)

/-- The layer-weighted score is the product itself, at every layer
    and every point. -/
lemma mul_prodGrad (w : Fin L → ℝ) (i : Fin L) :
    w i * prodGrad w i = prodMap w :=
  Finset.mul_prod_erase Finset.univ w (Finset.mem_univ i)

/-- lem:quotient_F at the model: the score annihilates every
    vertical direction (X_i w_i with gauge trace zero) at every
    point, exactly. -/
theorem quotient_F_vertical (w X : Fin L → ℝ)
    (hX : ∑ i, X i = 0) :
    ∑ i, prodGrad w i * (X i * w i) = 0 := by
  have h : ∀ i ∈ Finset.univ, prodGrad w i * (X i * w i)
      = prodMap w * X i := by
    intro i _
    rw [← mul_prodGrad w i]
    ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, hX, mul_zero]

/-- The rank-one model Fisher vanishes on vertical directions:
    the quadratic form of the vertical pairing is zero. -/
theorem quotient_F_vertical_quadform (w X : Fin L → ℝ)
    (hX : ∑ i, X i = 0) :
    (∑ i, prodGrad w i * (X i * w i)) ^ 2 = 0 := by
  rw [quotient_F_vertical w X hX]
  ring

/-- lem:quotient_K at the model: the KL factors through the quotient
    coordinate, so it is gauge invariant. -/
theorem quotient_K_invariant (w lam : Fin L → ℝ) (pstar : ℝ)
    (hlam : ∏ i, lam i = 1) :
    (prodMap (fun i => lam i * w i) - pstar) ^ 2
      = (prodMap w - pstar) ^ 2 := by
  rw [prodMap_gauge_invariant w lam hlam]

/-- The symmetric-point score: every layer reads t^{L−1}. -/
lemma prodGrad_const (t : ℝ) (i : Fin L) :
    prodGrad (fun _ => t) i = t ^ (L - 1) := by
  unfold prodGrad
  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]

/-- cor:quotient_rate at the model: the horizontal Fisher reading at
    the symmetric point, the squared score sum normalised by the
    direction's squared norm L, has leading rate 2(L−1) with
    coefficient L. -/
theorem quotient_rate_model (hL : 1 ≤ L) :
    HasLeadingRate
      (fun t => (∑ _i : Fin L, prodGrad (fun _ => t) _i) ^ 2 / L)
      (2 * (L - 1)) L := by
  have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have heq : ∀ t : ℝ,
      (∑ _i : Fin L, prodGrad (fun _ => t) _i) ^ 2 / L
      = (L : ℝ) * t ^ (2 * (L - 1)) := by
    intro t
    rw [Finset.sum_congr rfl fun i _ => prodGrad_const t i,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hexp : ((L : ℝ) * t ^ (L - 1)) ^ 2
        = (L : ℝ) ^ 2 * t ^ (2 * (L - 1)) := by
      rw [mul_pow, ← pow_mul]
      congr 2
      omega
    rw [hexp, div_eq_iff hLne]
    ring
  have h := (hasLeadingRate_pow (2 * (L - 1))).const_mul (L : ℝ)
  have h2 : HasLeadingRate (fun t => (L : ℝ) * t ^ (2 * (L - 1)))
      (2 * (L - 1)) L := by simpa using h
  refine h2.congr fun t => ?_
  simp only [heq]

/-- Euclidean SGD does not project: the horizontal metric factor
    (the squared score norm) varies along a gauge orbit. Witness at
    L = 2: the points (1, 1) and (2, 1/2) share the quotient
    coordinate and read different factors. -/
theorem euclidean_projection_obstruction :
    ∃ w₁ w₂ : Fin 2 → ℝ, prodMap w₁ = prodMap w₂
      ∧ (∑ i, (prodGrad w₁ i) ^ 2) ≠ (∑ i, (prodGrad w₂ i) ^ 2) := by
  refine ⟨![1, 1], ![2, 1/2], ?_, ?_⟩
  · unfold prodMap
    rw [Fin.prod_univ_two, Fin.prod_univ_two]
    norm_num
  · have hg : ∀ (w : Fin 2 → ℝ),
        prodGrad w 0 = w 1 ∧ prodGrad w 1 = w 0 := by
      intro w
      constructor
      · unfold prodGrad
        rw [show (Finset.univ.erase (0 : Fin 2)) = {1} by decide,
          Finset.prod_singleton]
      · unfold prodGrad
        rw [show (Finset.univ.erase (1 : Fin 2)) = {0} by decide,
          Finset.prod_singleton]
    rw [Fin.sum_univ_two, Fin.sum_univ_two,
      (hg (![1, 1] : Fin 2 → ℝ)).1, (hg (![1, 1] : Fin 2 → ℝ)).2,
      (hg (![2, 1/2] : Fin 2 → ℝ)).1,
      (hg (![2, 1/2] : Fin 2 → ℝ)).2]
    norm_num

/-- cor:sgd_quotient at the model: the log-coordinate invariant
    metric projects exactly. The flow factor of the projected
    dynamics is the layer-weighted squared score sum, which equals
    L·p²: a function of the quotient coordinate alone, so the
    projected flow closes on the quotient. -/
theorem invariant_metric_projects (w : Fin L → ℝ) (c : ℝ) :
    ∑ i, c * ((w i) ^ 2 * (prodGrad w i) ^ 2)
      = c * L * (prodMap w) ^ 2 := by
  have h : ∀ i ∈ Finset.univ,
      c * ((w i) ^ 2 * (prodGrad w i) ^ 2)
      = c * (prodMap w) ^ 2 := by
    intro i _
    rw [show (w i) ^ 2 * (prodGrad w i) ^ 2
      = (w i * prodGrad w i) ^ 2 by ring, mul_prodGrad w i]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- cor:ddcadam_quotient_rate at the model, the optimizer side: a
    gauge-equivariant update has a gauge-independent projected
    readout, so the quotient trajectory and its rate reading are
    well-defined regardless of the lift. -/
theorem equivariant_update_projects
    (U : (Fin L → ℝ) → (Fin L → ℝ))
    (hU : ∀ (lam w : Fin L → ℝ), (∏ i, lam i) = 1
      → U (fun i => lam i * w i) = fun i => lam i * U w i)
    (lam w : Fin L → ℝ) (hlam : ∏ i, lam i = 1) :
    prodMap (U (fun i => lam i * w i)) = prodMap (U w) := by
  rw [hU lam w hlam, prodMap_gauge_invariant (U w) lam hlam]

end DeadDirections
