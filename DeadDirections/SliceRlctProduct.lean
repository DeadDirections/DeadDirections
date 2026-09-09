/-
  Slice RLCT, product normal form (theory paper, thm:selection_rule
  part (c), general m⊥).

  For K(u, v) = u^{2k} + ‖v‖² on ℝ × ℝ^{m}, the sublevel-set volume
  obeys the exact scaling law V(ε) = ε^{1/(2k) + m/2} · V(1): the
  diagonal map (s, w) ↦ (ε^{1/(2k)}·s, ε^{1/2}·w) carries the unit
  sublevel set onto the ε-sublevel set and multiplies volume by its
  determinant ε^{1/(2k)}·ε^{m/2}. With 0 < V(1) < ∞ the log-volume
  slope reads the slice RLCT λ = 1/(2k) + m⊥/2 via
  tendsto_log_div_log_of_rpow. The file carries the set-level scaling
  identity, the volume identity, positivity and finiteness of V(1),
  and the slope corollary slice_rlct_product_slope.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import DeadDirections.SliceRlct

namespace DeadDirections

open Filter Topology Real MeasureTheory Set

variable {m : ℕ}

/-- The product normal form K(u, v) = u^{2k} + Σᵢ vᵢ². -/
def normalForm (k : ℕ) (p : ℝ × (Fin m → ℝ)) : ℝ :=
  p.1 ^ (2 * k) + ∑ i, p.2 i ^ 2

/-- The diagonal scaling (s, w) ↦ (a·s, b·w). -/
def diagScale (a b : ℝ) (p : ℝ × (Fin m → ℝ)) : ℝ × (Fin m → ℝ) :=
  (a * p.1, fun i => b * p.2 i)

/-- The scaling carries the unit sublevel set onto the ε-sublevel set:
    with a = ε^{1/(2k)} and b = ε^{1/2},
    K(a·s, b·w) = ε · K(s, w). -/
lemma normalForm_diagScale {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε)
    (p : ℝ × (Fin m → ℝ)) :
    normalForm k (diagScale (ε ^ ((1:ℝ)/(2*k))) (ε ^ ((1:ℝ)/2)) p)
      = ε * normalForm k p := by
  have h2k : (2 * k : ℕ) ≠ 0 := by omega
  have hr : (ε ^ ((1:ℝ)/(2 * k))) ^ (2 * k : ℕ) = ε := by
    rw [← Real.rpow_natCast (ε ^ ((1:ℝ)/(2 * k))) (2 * k),
      ← Real.rpow_mul hε.le]
    have h1 : (1:ℝ)/(2 * k) * ((2 * k : ℕ) : ℝ) = 1 := by
      have hne : ((2 * k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h2k
      push_cast
      field_simp
    rw [h1, Real.rpow_one]
  have hs : (ε ^ ((1:ℝ)/2)) ^ (2 : ℕ) = ε := by
    rw [← Real.rpow_natCast (ε ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul hε.le]
    norm_num
  unfold normalForm diagScale
  simp only [mul_pow]
  rw [hr, hs, ← Finset.mul_sum]
  ring

/-- Set-level scaling: the ε-sublevel set is the image of the unit
    sublevel set under the diagonal scaling. -/
lemma sublevel_normalForm_eq_image {k : ℕ} (hk : 1 ≤ k) {ε : ℝ}
    (hε : 0 < ε) :
    {p : ℝ × (Fin m → ℝ) | normalForm k p < ε}
      = diagScale (ε ^ ((1:ℝ)/(2*k))) (ε ^ ((1:ℝ)/2))
          '' {p | normalForm k p < 1} := by
  have ha : (0:ℝ) < ε ^ ((1:ℝ)/(2*k)) := Real.rpow_pos_of_pos hε _
  have hb : (0:ℝ) < ε ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hε _
  ext p
  simp only [mem_setOf_eq, mem_image]
  constructor
  · intro hp
    refine ⟨((ε ^ ((1:ℝ)/(2*k)))⁻¹ * p.1,
      fun i => (ε ^ ((1:ℝ)/2))⁻¹ * p.2 i), ?_, ?_⟩
    · have h := normalForm_diagScale (m := m) hk hε
        (((ε ^ ((1:ℝ)/(2*k)))⁻¹ * p.1,
          fun i => (ε ^ ((1:ℝ)/2))⁻¹ * p.2 i))
      have hback : diagScale (ε ^ ((1:ℝ)/(2*k))) (ε ^ ((1:ℝ)/2))
          (((ε ^ ((1:ℝ)/(2*k)))⁻¹ * p.1,
            fun i => (ε ^ ((1:ℝ)/2))⁻¹ * p.2 i)) = p := by
        unfold diagScale
        ext
        · simp only
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt ha), one_mul]
        · simp only
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hb), one_mul]
      rw [hback] at h
      have h2 : ε * normalForm k (((ε ^ ((1:ℝ)/(2*k)))⁻¹ * p.1,
          fun i => (ε ^ ((1:ℝ)/2))⁻¹ * p.2 i)) < ε * 1 := by
        rw [mul_one]
        exact h.symm.trans_lt hp
      exact lt_of_mul_lt_mul_left h2 hε.le
    · unfold diagScale
      ext
      · simp only
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt ha), one_mul]
      · simp only
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hb), one_mul]
  · rintro ⟨q, hq, rfl⟩
    rw [normalForm_diagScale hk hε q]
    calc ε * normalForm k q < ε * 1 :=
          mul_lt_mul_of_pos_left hq hε
      _ = ε := mul_one ε

/-! ### The volume identity -/

instance : (volume : Measure (ℝ × (Fin m → ℝ))).IsAddHaarMeasure :=
  inferInstanceAs (((volume : Measure ℝ).prod volume).IsAddHaarMeasure)

/-- The diagonal scaling as a linear map. -/
noncomputable def diagScaleL (m : ℕ) (a b : ℝ) :
    (ℝ × (Fin m → ℝ)) →ₗ[ℝ] (ℝ × (Fin m → ℝ)) :=
  LinearMap.prodMap (a • LinearMap.id) (b • LinearMap.id)

lemma coe_diagScaleL (a b : ℝ) :
    ⇑(diagScaleL m a b) = (diagScale a b : ℝ × (Fin m → ℝ) → _) := by
  funext p
  simp [diagScaleL, diagScale, smul_eq_mul]
  rfl

lemma det_diagScaleL (a b : ℝ) :
    LinearMap.det (diagScaleL m a b) = a * b ^ m := by
  unfold diagScaleL
  rw [LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_smul,
    LinearMap.det_id, Module.finrank_self, Module.finrank_pi]
  simp

/-- Exact volume scaling for the product normal form:
    V(ε) = ε^{1/(2k) + m/2} · V(1). -/
theorem volume_sublevel_normalForm {k : ℕ} (hk : 1 ≤ k) {ε : ℝ}
    (hε : 0 < ε) :
    volume {p : ℝ × (Fin m → ℝ) | normalForm k p < ε}
      = ENNReal.ofReal (ε ^ ((1:ℝ)/(2*k) + m/2))
        * volume {p : ℝ × (Fin m → ℝ) | normalForm k p < 1} := by
  have ha : (0:ℝ) < ε ^ ((1:ℝ)/(2*k)) := Real.rpow_pos_of_pos hε _
  have hb : (0:ℝ) < ε ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hε _
  rw [sublevel_normalForm_eq_image hk hε, ← coe_diagScaleL,
    Measure.addHaar_image_linearMap, det_diagScaleL]
  congr 2
  rw [abs_of_pos (by positivity)]
  rw [← Real.rpow_natCast (ε ^ ((1:ℝ)/2)) m, ← Real.rpow_mul hε.le,
    ← Real.rpow_add hε]
  congr 1
  ring

/-! ### The unit sublevel volume is positive and finite -/

lemma sublevel_normalForm_subset {k : ℕ} (hk : 1 ≤ k) :
    {p : ℝ × (Fin m → ℝ) | normalForm k p < 1}
      ⊆ (Ioo (-1:ℝ) 1) ×ˢ Set.pi univ (fun _ => Ioo (-1:ℝ) 1) := by
  intro p hp
  have h2k : (2 * k : ℕ) ≠ 0 := by omega
  have hvnn : (0:ℝ) ≤ ∑ i, p.2 i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hunn : (0:ℝ) ≤ p.1 ^ (2*k) := (even_two_mul k).pow_nonneg _
  have hK : normalForm k p < 1 := hp
  unfold normalForm at hK
  constructor
  · have hu : p.1 ^ (2*k) < 1 := by linarith
    have habs : |p.1| ^ (2*k) < 1 ^ (2*k) := by
      rw [one_pow, ← abs_pow, abs_of_nonneg hunn]
      exact hu
    have := lt_of_pow_lt_pow_left₀ (2*k) (by norm_num) habs
    exact abs_lt.mp this
  · intro i _
    have hvi : p.2 i ^ 2 ≤ ∑ j, p.2 j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (p.2 j)) (Finset.mem_univ i)
    have hv1 : p.2 i ^ 2 < 1 := by linarith
    have habs : |p.2 i| ^ 2 < 1 ^ 2 := by
      rw [one_pow, sq_abs]
      exact hv1
    have := lt_of_pow_lt_pow_left₀ 2 (by norm_num) habs
    exact abs_lt.mp this

lemma volume_sublevel_normalForm_one_lt_top {k : ℕ} (hk : 1 ≤ k) :
    volume {p : ℝ × (Fin m → ℝ) | normalForm k p < 1} < ⊤ := by
  refine lt_of_le_of_lt (measure_mono (sublevel_normalForm_subset hk)) ?_
  rw [Measure.volume_eq_prod ℝ (Fin m → ℝ), Measure.prod_prod, Real.volume_Ioo,
    volume_pi_pi]
  simp only [Real.volume_Ioo]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top)

lemma sublevel_normalForm_superset {k : ℕ} (hk : 1 ≤ k) :
    (Ioo (-(1/2):ℝ) (1/2)) ×ˢ
        Set.pi univ (fun _ : Fin m => Ioo (-(1/(2*(m+1)):ℝ)) (1/(2*(m+1))))
      ⊆ {p : ℝ × (Fin m → ℝ) | normalForm k p < 1} := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  simp only [mem_Ioo] at hu
  have hr : (0:ℝ) < 1/(2*(m+1)) := by positivity
  have huabs : |u| < 1/2 := abs_lt.mpr hu
  have hu2 : u ^ (2*k) ≤ (1/2 : ℝ) ^ 2 := by
    calc u ^ (2*k) = |u| ^ (2*k) := by
          rw [← abs_pow, abs_of_nonneg ((even_two_mul k).pow_nonneg u)]
      _ ≤ (1/2 : ℝ) ^ (2*k) :=
          pow_le_pow_left₀ (abs_nonneg u) huabs.le (2*k)
      _ ≤ (1/2 : ℝ) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hsum : ∑ i, v i ^ 2 ≤ (m : ℝ) * (1/(2*(m+1))) ^ 2 := by
    have hvi : ∀ i, v i ^ 2 ≤ (1/(2*(m+1))) ^ 2 := fun i => by
      have h := hv i (Set.mem_univ i)
      simp only [mem_Ioo] at h
      have := abs_lt.mpr h
      calc v i ^ 2 = |v i| ^ 2 := (sq_abs _).symm
        _ ≤ (1/(2*(m+1))) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) this.le 2
    calc ∑ i, v i ^ 2 ≤ ∑ _i : Fin m, (1/(2*(m+1)):ℝ) ^ 2 :=
          Finset.sum_le_sum fun i _ => hvi i
      _ = (m : ℝ) * (1/(2*(m+1))) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  have hm : (m : ℝ) * (1/(2*(m+1))) ^ 2 ≤ 1/4 := by
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    rw [div_pow, one_pow, mul_one_div,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg ((m:ℝ))]
  show normalForm k (u, v) < 1
  unfold normalForm
  simp only
  nlinarith

lemma volume_sublevel_normalForm_one_pos {k : ℕ} (hk : 1 ≤ k) :
    0 < volume {p : ℝ × (Fin m → ℝ) | normalForm k p < 1} := by
  refine lt_of_lt_of_le ?_ (measure_mono (sublevel_normalForm_superset hk))
  rw [Measure.volume_eq_prod ℝ (Fin m → ℝ), Measure.prod_prod, Real.volume_Ioo,
    volume_pi_pi]
  simp only [Real.volume_Ioo]
  have hr : (0:ℝ) < 1/(2*(m+1)) := by positivity
  refine ENNReal.mul_pos ?_ ?_
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    norm_num
  · rw [Finset.prod_const]
    refine pow_ne_zero _ ?_
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith

/-- thm:selection_rule (c), volume-scaling form at general m⊥: the
    log-volume slope of the normal form u^{2k} + Σvᵢ² reads the slice
    RLCT λ = 1/(2k) + m⊥/2. -/
theorem slice_rlct_product_slope {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun ε =>
      Real.log ((volume {p : ℝ × (Fin m → ℝ) | normalForm k p < ε}).toReal)
        / Real.log ε)
      (𝓝[>] (0:ℝ)) (𝓝 ((1:ℝ)/(2*k) + m/2)) := by
  set V1 := volume {p : ℝ × (Fin m → ℝ) | normalForm k p < 1} with hV1
  have hpos : 0 < V1.toReal :=
    ENNReal.toReal_pos (ne_of_gt (volume_sublevel_normalForm_one_pos hk))
      (ne_of_lt (volume_sublevel_normalForm_one_lt_top hk))
  refine (tendsto_log_div_log_of_rpow (C := V1.toReal) hpos).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  have hεpos : (0:ℝ) < ε := hε
  rw [volume_sublevel_normalForm hk hεpos, ← hV1, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_pos_of_pos hεpos _).le, mul_comm]

/-! ### The multi-direction normal form (prop:volume_multi)

K(u, v) = Σᵢ uᵢ^{2kᵢ} + Σⱼ vⱼ² with per-coordinate KL orders. The same
diagonal-scaling route applies with the per-coordinate factors
ε^{1/(2kᵢ)}, and the volume law is exact:
V(ε) = ε^{Σᵢ 1/(2kᵢ) + m/2} · V(1). -/

section MultiDirection

variable {r : ℕ}

/-- The multi-direction normal form K(u, v) = Σᵢ uᵢ^{2kᵢ} + Σⱼ vⱼ². -/
def normalFormMulti (k : Fin r → ℕ) (p : (Fin r → ℝ) × (Fin m → ℝ)) : ℝ :=
  ∑ i, p.1 i ^ (2 * k i) + ∑ j, p.2 j ^ 2

/-- Per-coordinate diagonal scaling on the u-block, uniform on the
    v-block. -/
def diagScaleMulti (a : Fin r → ℝ) (b : ℝ)
    (p : (Fin r → ℝ) × (Fin m → ℝ)) : (Fin r → ℝ) × (Fin m → ℝ) :=
  (fun i => a i * p.1 i, fun j => b * p.2 j)

lemma rpow_inv_two_mul_pow {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    (ε ^ ((1:ℝ)/(2*k))) ^ (2 * k : ℕ) = ε := by
  have h2k : (2 * k : ℕ) ≠ 0 := by omega
  rw [← Real.rpow_natCast (ε ^ ((1:ℝ)/(2*k))) (2 * k),
    ← Real.rpow_mul hε.le]
  have h1 : (1:ℝ)/(2*k) * ((2 * k : ℕ) : ℝ) = 1 := by
    have hne : ((2 * k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h2k
    push_cast
    field_simp
  rw [h1, Real.rpow_one]

/-- The per-coordinate scaling carries the unit sublevel set onto the
    ε-sublevel set. -/
lemma normalFormMulti_diagScale {k : Fin r → ℕ} (hk : ∀ i, 1 ≤ k i)
    {ε : ℝ} (hε : 0 < ε) (p : (Fin r → ℝ) × (Fin m → ℝ)) :
    normalFormMulti k (diagScaleMulti (fun i => ε ^ ((1:ℝ)/(2*k i)))
        (ε ^ ((1:ℝ)/2)) p)
      = ε * normalFormMulti k p := by
  have hs : (ε ^ ((1:ℝ)/2)) ^ (2 : ℕ) = ε := by
    rw [← Real.rpow_natCast (ε ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul hε.le]
    norm_num
  unfold normalFormMulti diagScaleMulti
  simp only [mul_pow]
  have hu : ∀ i : Fin r,
      (ε ^ ((1:ℝ)/(2*k i))) ^ (2 * k i) * p.1 i ^ (2 * k i)
        = ε * p.1 i ^ (2 * k i) := fun i => by
    rw [rpow_inv_two_mul_pow (hk i) hε]
  rw [Finset.sum_congr rfl fun i _ => hu i, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) =>
    (by rw [hs] : (ε ^ ((1:ℝ)/2)) ^ 2 * p.2 j ^ 2 = ε * p.2 j ^ 2),
    ← Finset.mul_sum]
  ring

/-- Set-level scaling for the multi-direction form. -/
lemma sublevel_normalFormMulti_eq_image {k : Fin r → ℕ}
    (hk : ∀ i, 1 ≤ k i) {ε : ℝ} (hε : 0 < ε) :
    {p : (Fin r → ℝ) × (Fin m → ℝ) | normalFormMulti k p < ε}
      = diagScaleMulti (fun i => ε ^ ((1:ℝ)/(2*k i))) (ε ^ ((1:ℝ)/2))
          '' {p | normalFormMulti k p < 1} := by
  have ha : ∀ i : Fin r, (0:ℝ) < ε ^ ((1:ℝ)/(2*k i)) :=
    fun i => Real.rpow_pos_of_pos hε _
  have hb : (0:ℝ) < ε ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hε _
  ext p
  simp only [mem_setOf_eq, mem_image]
  constructor
  · intro hp
    refine ⟨(fun i => (ε ^ ((1:ℝ)/(2*k i)))⁻¹ * p.1 i,
      fun j => (ε ^ ((1:ℝ)/2))⁻¹ * p.2 j), ?_, ?_⟩
    · have hback : diagScaleMulti (fun i => ε ^ ((1:ℝ)/(2*k i)))
          (ε ^ ((1:ℝ)/2))
          ((fun i => (ε ^ ((1:ℝ)/(2*k i)))⁻¹ * p.1 i,
            fun j => (ε ^ ((1:ℝ)/2))⁻¹ * p.2 j)) = p := by
        unfold diagScaleMulti
        ext
        · simp only
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (ha _)), one_mul]
        · simp only
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hb), one_mul]
      have h := normalFormMulti_diagScale (m := m) hk hε
        ((fun i => (ε ^ ((1:ℝ)/(2*k i)))⁻¹ * p.1 i,
          fun j => (ε ^ ((1:ℝ)/2))⁻¹ * p.2 j))
      rw [hback] at h
      have h2 : ε * normalFormMulti k
          ((fun i => (ε ^ ((1:ℝ)/(2*k i)))⁻¹ * p.1 i,
            fun j => (ε ^ ((1:ℝ)/2))⁻¹ * p.2 j)) < ε * 1 := by
        rw [mul_one]
        exact h.symm.trans_lt hp
      exact lt_of_mul_lt_mul_left h2 hε.le
    · unfold diagScaleMulti
      ext
      · simp only
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (ha _)), one_mul]
      · simp only
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hb), one_mul]
  · rintro ⟨q, hq, rfl⟩
    rw [normalFormMulti_diagScale hk hε q]
    calc ε * normalFormMulti k q < ε * 1 :=
          mul_lt_mul_of_pos_left hq hε
      _ = ε := mul_one ε

/- Instance search does not find the prod-of-Haar instance on the
   pi × pi shape by itself; apply it directly. -/
instance : (volume : Measure ((Fin r → ℝ) × (Fin m → ℝ))).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

/-- The per-coordinate diagonal scaling as a linear map. -/
noncomputable def diagScaleMultiL (r m : ℕ) (a : Fin r → ℝ) (b : ℝ) :
    ((Fin r → ℝ) × (Fin m → ℝ)) →ₗ[ℝ] ((Fin r → ℝ) × (Fin m → ℝ)) :=
  LinearMap.prodMap (Matrix.toLin' (Matrix.diagonal a)) (b • LinearMap.id)

lemma coe_diagScaleMultiL (a : Fin r → ℝ) (b : ℝ) :
    ⇑(diagScaleMultiL r m a b)
      = (diagScaleMulti a b : (Fin r → ℝ) × (Fin m → ℝ) → _) := by
  funext p
  unfold diagScaleMultiL diagScaleMulti
  simp only [LinearMap.prodMap_apply, Prod.mk.injEq]
  constructor
  · funext i
    rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  · rfl

lemma det_diagScaleMultiL (a : Fin r → ℝ) (b : ℝ) :
    LinearMap.det (diagScaleMultiL r m a b) = (∏ i, a i) * b ^ m := by
  unfold diagScaleMultiL
  rw [LinearMap.det_prodMap, LinearMap.det_toLin', Matrix.det_diagonal,
    LinearMap.det_smul, LinearMap.det_id, Module.finrank_pi]
  simp

/-- ε^{Σ f i} = ∏ ε^{f i} for a positive base. -/
lemma rpow_sum_eq_prod {ε : ℝ} (hε : 0 < ε) (f : Fin r → ℝ) :
    ε ^ (∑ i, f i) = ∏ i, ε ^ (f i) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ, Fin.prod_univ_succ, Real.rpow_add hε,
      ih (fun i => f i.succ)]

/-- prop:volume_multi, normal-form content: exact volume scaling
    V(ε) = ε^{Σᵢ 1/(2kᵢ) + m/2} · V(1). -/
theorem volume_sublevel_normalFormMulti {k : Fin r → ℕ}
    (hk : ∀ i, 1 ≤ k i) {ε : ℝ} (hε : 0 < ε) :
    volume {p : (Fin r → ℝ) × (Fin m → ℝ) | normalFormMulti k p < ε}
      = ENNReal.ofReal (ε ^ ((∑ i, (1:ℝ)/(2*k i)) + m/2))
        * volume {p : (Fin r → ℝ) × (Fin m → ℝ) |
            normalFormMulti k p < 1} := by
  have ha : ∀ i : Fin r, (0:ℝ) < ε ^ ((1:ℝ)/(2*k i)) :=
    fun i => Real.rpow_pos_of_pos hε _
  have hb : (0:ℝ) < ε ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hε _
  rw [sublevel_normalFormMulti_eq_image hk hε, ← coe_diagScaleMultiL,
    Measure.addHaar_image_linearMap, det_diagScaleMultiL]
  congr 2
  rw [abs_of_pos (by positivity)]
  rw [← Real.rpow_natCast (ε ^ ((1:ℝ)/2)) m, ← Real.rpow_mul hε.le,
    Real.rpow_add hε, rpow_sum_eq_prod hε]
  congr 1
  ring

/-! ### The unit sublevel volume, multi-direction -/

lemma sublevel_normalFormMulti_subset (k : Fin r → ℕ) :
    {p : (Fin r → ℝ) × (Fin m → ℝ) | normalFormMulti k p < 1}
      ⊆ Set.pi univ (fun _ : Fin r => Ioo (-1:ℝ) 1)
        ×ˢ Set.pi univ (fun _ : Fin m => Ioo (-1:ℝ) 1) := by
  intro p hp
  have hvnn : (0:ℝ) ≤ ∑ j, p.2 j ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hunn : ∀ i, (0:ℝ) ≤ p.1 i ^ (2 * k i) :=
    fun i => (even_two_mul (k i)).pow_nonneg _
  have husum : (0:ℝ) ≤ ∑ i, p.1 i ^ (2 * k i) :=
    Finset.sum_nonneg fun i _ => hunn i
  have hK : normalFormMulti k p < 1 := hp
  unfold normalFormMulti at hK
  constructor
  · intro i _
    have hui : p.1 i ^ (2 * k i) ≤ ∑ j, p.1 j ^ (2 * k j) :=
      Finset.single_le_sum (fun j _ => hunn j) (Finset.mem_univ i)
    have hu : p.1 i ^ (2 * k i) < 1 := by linarith
    have habs : |p.1 i| ^ (2 * k i) < 1 ^ (2 * k i) := by
      rw [one_pow, ← abs_pow, abs_of_nonneg (hunn i)]
      exact hu
    have := lt_of_pow_lt_pow_left₀ (2 * k i) (by norm_num) habs
    exact abs_lt.mp this
  · intro j _
    have hvj : p.2 j ^ 2 ≤ ∑ i, p.2 i ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (p.2 i))
        (Finset.mem_univ j)
    have hv1 : p.2 j ^ 2 < 1 := by linarith
    have habs : |p.2 j| ^ 2 < 1 ^ 2 := by
      rw [one_pow, sq_abs]
      exact hv1
    have := lt_of_pow_lt_pow_left₀ 2 (by norm_num) habs
    exact abs_lt.mp this

lemma volume_sublevel_normalFormMulti_one_lt_top (k : Fin r → ℕ) :
    volume {p : (Fin r → ℝ) × (Fin m → ℝ) | normalFormMulti k p < 1}
      < ⊤ := by
  refine lt_of_le_of_lt
    (measure_mono (sublevel_normalFormMulti_subset k)) ?_
  rw [Measure.volume_eq_prod (Fin r → ℝ) (Fin m → ℝ), Measure.prod_prod,
    volume_pi_pi, volume_pi_pi]
  simp only [Real.volume_Ioo]
  exact ENNReal.mul_lt_top
    (ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top)
    (ENNReal.prod_lt_top fun j _ => ENNReal.ofReal_lt_top)

lemma sublevel_normalFormMulti_superset {k : Fin r → ℕ}
    (hk : ∀ i, 1 ≤ k i) :
    Set.pi univ (fun _ : Fin r => Ioo (-(1/(2*(r+1))):ℝ) (1/(2*(r+1))))
      ×ˢ Set.pi univ
        (fun _ : Fin m => Ioo (-(1/(2*(m+1)):ℝ)) (1/(2*(m+1))))
      ⊆ {p : (Fin r → ℝ) × (Fin m → ℝ) | normalFormMulti k p < 1} := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  have hrpos : (0:ℝ) < 1/(2*(r+1)) := by positivity
  have hmpos : (0:ℝ) < 1/(2*(m+1)) := by positivity
  have husum : ∑ i, u i ^ (2 * k i) ≤ (r : ℝ) * (1/(2*(r+1))) ^ 2 := by
    have hui : ∀ i, u i ^ (2 * k i) ≤ (1/(2*(r+1))) ^ 2 := fun i => by
      have h := hu i (Set.mem_univ i)
      simp only [mem_Ioo] at h
      have habs : |u i| < 1/(2*(r+1)) := abs_lt.mpr h
      have h1 : |u i| ≤ 1 := by
        have : (1:ℝ)/(2*(r+1)) ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith [Nat.cast_nonneg (α := ℝ) r]
        linarith
      calc u i ^ (2 * k i) = |u i| ^ (2 * k i) := by
            rw [← abs_pow, abs_of_nonneg ((even_two_mul (k i)).pow_nonneg _)]
        _ ≤ |u i| ^ 2 :=
            pow_le_pow_of_le_one (abs_nonneg _) h1 (by
              have := hk i
              omega)
        _ ≤ (1/(2*(r+1))) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) habs.le 2
    calc ∑ i, u i ^ (2 * k i)
        ≤ ∑ _i : Fin r, (1/(2*(r+1)):ℝ) ^ 2 :=
          Finset.sum_le_sum fun i _ => hui i
      _ = (r : ℝ) * (1/(2*(r+1))) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  have hvsum : ∑ j, v j ^ 2 ≤ (m : ℝ) * (1/(2*(m+1))) ^ 2 := by
    have hvj : ∀ j, v j ^ 2 ≤ (1/(2*(m+1))) ^ 2 := fun j => by
      have h := hv j (Set.mem_univ j)
      simp only [mem_Ioo] at h
      have := abs_lt.mpr h
      calc v j ^ 2 = |v j| ^ 2 := (sq_abs _).symm
        _ ≤ (1/(2*(m+1))) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) this.le 2
    calc ∑ j, v j ^ 2 ≤ ∑ _j : Fin m, (1/(2*(m+1)):ℝ) ^ 2 :=
          Finset.sum_le_sum fun j _ => hvj j
      _ = (m : ℝ) * (1/(2*(m+1))) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  have hru : (r : ℝ) * (1/(2*(r+1))) ^ 2 ≤ 1/4 := by
    have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
    rw [div_pow, one_pow, mul_one_div,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg ((r:ℝ))]
  have hmv : (m : ℝ) * (1/(2*(m+1))) ^ 2 ≤ 1/4 := by
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    rw [div_pow, one_pow, mul_one_div,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg ((m:ℝ))]
  show normalFormMulti k (u, v) < 1
  unfold normalFormMulti
  simp only
  nlinarith

lemma volume_sublevel_normalFormMulti_one_pos {k : Fin r → ℕ}
    (hk : ∀ i, 1 ≤ k i) :
    0 < volume {p : (Fin r → ℝ) × (Fin m → ℝ) |
        normalFormMulti k p < 1} := by
  refine lt_of_lt_of_le ?_
    (measure_mono (sublevel_normalFormMulti_superset hk))
  rw [Measure.volume_eq_prod (Fin r → ℝ) (Fin m → ℝ), Measure.prod_prod,
    volume_pi_pi, volume_pi_pi]
  simp only [Real.volume_Ioo]
  have hrpos : (0:ℝ) < 1/(2*(r+1)) := by positivity
  have hmpos : (0:ℝ) < 1/(2*(m+1)) := by positivity
  refine ENNReal.mul_pos ?_ ?_
  · rw [Finset.prod_const]
    refine pow_ne_zero _ ?_
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  · rw [Finset.prod_const]
    refine pow_ne_zero _ ?_
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith

/-- prop:volume_multi, slope form: the log-volume slope of the
    multi-direction normal form reads λ = Σᵢ 1/(2kᵢ) + m⊥/2, the sum
    of the per-direction slice RLCTs. -/
theorem volume_multi_slope {k : Fin r → ℕ} (hk : ∀ i, 1 ≤ k i) :
    Tendsto (fun ε =>
      Real.log ((volume {p : (Fin r → ℝ) × (Fin m → ℝ) |
          normalFormMulti k p < ε}).toReal)
        / Real.log ε)
      (𝓝[>] (0:ℝ)) (𝓝 ((∑ i, (1:ℝ)/(2*k i)) + m/2)) := by
  set V1 := volume {p : (Fin r → ℝ) × (Fin m → ℝ) |
    normalFormMulti k p < 1} with hV1
  have hpos : 0 < V1.toReal :=
    ENNReal.toReal_pos
      (ne_of_gt (volume_sublevel_normalFormMulti_one_pos hk))
      (ne_of_lt (volume_sublevel_normalFormMulti_one_lt_top k))
  refine (tendsto_log_div_log_of_rpow (C := V1.toReal) hpos).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  have hεpos : (0:ℝ) < ε := hε
  rw [volume_sublevel_normalFormMulti hk hεpos, ← hV1,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_pos_of_pos hεpos _).le, mul_comm]

end MultiDirection

end DeadDirections
