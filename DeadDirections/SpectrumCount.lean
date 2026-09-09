/-
  The spectrum-count form (cor:bridge_g2, thm:bridge_multi (c),
  cor:bridge_g7): how many eigenvalues decay.

  A quadratic form that is small on an m-dimensional subspace and
  bounded below by c on a complementary subspace of dimension h − m
  has exactly m small eigenvalues, by the min-max principle. The
  subspace form of that count needs no eigenvalue theory: any subspace
  on which the form is at most a·‖v‖² with a < c meets the live
  complement trivially, so its dimension is at most m, and the dead
  subspace itself attains m. With the dead bound C·t^{2k} and a live
  floor c this is the count "m eigenvalues at the dead rate, h − m of
  order one" at every small t. The smooth-activation correction of the
  biased chain rides along as a Lipschitz bound on the gate.
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Matrix.Spectrum

namespace DeadDirections

section Count

variable {h : ℕ}

/-- The dimension bound: a subspace on which the form is at most
    a·‖v‖² meets a subspace where it is at least c·‖v‖² (c > a) only
    in zero, so its dimension is at most h − dim(live). -/
theorem small_subspace_dim_le (Q : (Fin h → ℝ) → ℝ) {a c : ℝ} (hac : a < c)
    (L : Submodule ℝ (Fin h → ℝ))
    (hL : ∀ v ∈ L, c * ∑ i, v i ^ 2 ≤ Q v)
    (S : Submodule ℝ (Fin h → ℝ))
    (hS : ∀ v ∈ S, Q v ≤ a * ∑ i, v i ^ 2) :
    Module.finrank ℝ S + Module.finrank ℝ L ≤ h := by
  have hinf : S ⊓ L = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hvS, hvL⟩ := Submodule.mem_inf.mp hv
    have h1 := hS v hvS
    have h2 := hL v hvL
    have hsq : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hzero : ∑ i, v i ^ 2 = 0 := by
      by_contra hne
      have hpos : 0 < ∑ i, v i ^ 2 := lt_of_le_of_ne hsq (Ne.symm hne)
      nlinarith
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (v j)).mp hzero i
      (Finset.mem_univ i)
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq S L
  rw [hinf, finrank_bot, add_zero] at h1
  have h2 : Module.finrank ℝ ↥(S ⊔ L) ≤ Module.finrank ℝ (Fin h → ℝ) :=
    Submodule.finrank_le _
  rw [Module.finrank_fin_fun] at h2
  omega

/-- The spectrum-count form: with a dead subspace of dimension m on
    which the form is at most a·‖v‖² and a live complement of
    dimension h − m on which it is at least c·‖v‖² (a < c), every
    subspace carrying the form at most a·‖v‖² has dimension at most m,
    and the dead subspace attains m. By min-max this is exactly m
    eigenvalues at most a and h − m at least c. -/
theorem spectrum_count_form (Q : (Fin h → ℝ) → ℝ) {a c : ℝ} (hac : a < c)
    {m : ℕ} (D L : Submodule ℝ (Fin h → ℝ))
    (hD : Module.finrank ℝ D = m) (hLdim : Module.finrank ℝ L = h - m)
    (hm : m ≤ h)
    (_hDle : ∀ v ∈ D, Q v ≤ a * ∑ i, v i ^ 2)
    (hL : ∀ v ∈ L, c * ∑ i, v i ^ 2 ≤ Q v) :
    (∀ S : Submodule ℝ (Fin h → ℝ),
      (∀ v ∈ S, Q v ≤ a * ∑ i, v i ^ 2) → Module.finrank ℝ S ≤ m)
    ∧ Module.finrank ℝ D = m := by
  refine ⟨fun S hS => ?_, hD⟩
  have := small_subspace_dim_le Q hac L hL S hS
  omega

end Count

section BiasCorrection

/-- thm:bridge_bias's (P2) Taylor correction: a smooth activation's
    gate at the biased pre-activation a + t·x differs from its value
    at a by at most K·|t|·|x| when the derivative is K-Lipschitz, the
    O(t) correction r^bias. -/
theorem bias_taylor_correction (φ' : ℝ → ℝ) {K : NNReal}
    (hL : LipschitzWith K φ') (a x t : ℝ) :
    |φ' (a + t * x) - φ' a| ≤ K * (|t| * |x|) := by
  have h := hL.dist_le_mul (a + t * x) a
  rw [Real.dist_eq, Real.dist_eq, add_sub_cancel_left, abs_mul] at h
  exact h

end BiasCorrection

section WidthCondition

/-- cor:rect_lambda_min's width condition is not removable: a backward
    operator into layer ℓ that factors through a narrower layer above
    (a < b) has a non-trivial kernel, so the Gram form has an exact
    zero direction at every t and the smallest eigenvalue is zero
    whatever the dead entry does. -/
theorem width_condition_failure {a b : ℕ} (hab : a < b)
    (B : Matrix (Fin a) (Fin b) ℝ) :
    ∃ v : Fin b → ℝ, v ≠ 0 ∧ B.mulVec v = 0
      ∧ ∑ i, (B.mulVec v i) ^ 2 = 0 := by
  have hlt : Module.finrank ℝ (Fin a → ℝ) < Module.finrank ℝ (Fin b → ℝ) := by
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
    exact hab
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := Matrix.mulVecLin B) hlt
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hBv : B.mulVec v = 0 := by
    have := LinearMap.mem_ker.mp hv
    rwa [Matrix.mulVecLin_apply] at this
  refine ⟨v, hv0, hBv, ?_⟩
  rw [hBv]
  simp

end WidthCondition

/-! ### The ordered spectrum: exactly m eigenvalues at the dead rate

The subspace count becomes an eigenvalue count through the spectral
theorem. In the eigenvector basis the quadratic form is Σ λᵢ cᵢ² and
the norm Σ cᵢ², so the span of the eigenvectors with λ < c carries
the form below c·‖v‖² and meets the live complement trivially, while
the span of those with λ > a carries it above a·‖v‖² and meets the
dead subspace trivially. The two dimension bounds pin the counts:
exactly m eigenvalues at most a, exactly h − m at least c, none in
between. This is the ordered-spectrum clause of thm:bridge at the
level the rate claims use, with no minimax theorem needed. -/

section EigenvalueCount

open Matrix

variable {h : ℕ} (A : Matrix (Fin h) (Fin h) ℝ) (hA : A.IsHermitian)

/-- The eigenvectors as plain vectors. -/
noncomputable def eigVec (i : Fin h) : Fin h → ℝ :=
  WithLp.ofLp (hA.eigenvectorBasis i)

lemma eigVec_dot (i j : Fin h) :
    eigVec A hA i ⬝ᵥ eigVec A hA j = if i = j then 1 else 0 := by
  have h := orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal i j
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
  rw [dotProduct_comm]
  exact h

lemma mulVec_eigVec (i : Fin h) :
    A *ᵥ eigVec A hA i = hA.eigenvalues i • eigVec A hA i := by
  simpa [eigVec] using hA.mulVec_eigenvectorBasis i

/-- Every vector expands in the eigenvectors with coefficients the
    pairings. -/
lemma eigVec_expand (v : Fin h → ℝ) :
    v = ∑ i, (eigVec A hA i ⬝ᵥ v) • eigVec A hA i := by
  have hb := hA.eigenvectorBasis.sum_repr' (WithLp.toLp 2 v)
  have key : ∑ i, (v ⬝ᵥ eigVec A hA i) • eigVec A hA i = v := by
    have := congrArg WithLp.ofLp hb
    simpa [eigVec, WithLp.ofLp_sum, WithLp.ofLp_smul,
      EuclideanSpace.inner_eq_star_dotProduct] using this
  calc v = ∑ i, (v ⬝ᵥ eigVec A hA i) • eigVec A hA i := key.symm
    _ = ∑ i, (eigVec A hA i ⬝ᵥ v) • eigVec A hA i := by
        simp_rw [dotProduct_comm v]

/-- The quadratic form in eigen-coordinates. -/
lemma quadform_eigen (v : Fin h → ℝ) :
    v ⬝ᵥ A *ᵥ v = ∑ i, hA.eigenvalues i * (eigVec A hA i ⬝ᵥ v) ^ 2 := by
  conv_lhs => rw [eigVec_expand A hA v]
  rw [mulVec_sum]
  simp_rw [mulVec_smul, mulVec_eigVec, smul_smul]
  rw [dotProduct_sum]
  simp_rw [dotProduct_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : v ⬝ᵥ eigVec A hA i = eigVec A hA i ⬝ᵥ v := dotProduct_comm _ _
  have hvv : (∑ j, (eigVec A hA j ⬝ᵥ v) • eigVec A hA j) ⬝ᵥ eigVec A hA i
      = eigVec A hA i ⬝ᵥ v := by
    rw [← eigVec_expand A hA v]
    exact dotProduct_comm _ _
  rw [hvv]
  ring

/-- The norm in eigen-coordinates. -/
lemma normsq_eigen (v : Fin h → ℝ) :
    ∑ i, v i ^ 2 = ∑ i, (eigVec A hA i ⬝ᵥ v) ^ 2 := by
  have h1 : ∑ i, v i ^ 2 = v ⬝ᵥ v := by
    simp only [dotProduct, sq]
  rw [h1]
  conv_lhs => rw [eigVec_expand A hA v]
  rw [dotProduct_sum]
  simp_rw [dotProduct_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hvv : (∑ j, (eigVec A hA j ⬝ᵥ v) • eigVec A hA j) ⬝ᵥ eigVec A hA i
      = eigVec A hA i ⬝ᵥ v := by
    rw [← eigVec_expand A hA v]
    exact dotProduct_comm _ _
  rw [hvv]
  ring

lemma eigVec_linearIndependent : LinearIndependent ℝ (eigVec A hA) := by
  have hli := hA.eigenvectorBasis.orthonormal.linearIndependent
  have := hli.map' (WithLp.linearEquiv 2 ℝ (Fin h → ℝ)).toLinearMap
    (LinearEquiv.ker _)
  exact this

lemma eigVec_injective : Function.Injective (eigVec A hA) :=
  (eigVec_linearIndependent A hA).injective

/-- The span of a set of eigenvectors. -/
noncomputable def eigSpan (T : Finset (Fin h)) : Submodule ℝ (Fin h → ℝ) :=
  Submodule.span ℝ ((T.image (eigVec A hA) : Finset (Fin h → ℝ)) : Set (Fin h → ℝ))

lemma finrank_eigSpan (T : Finset (Fin h)) :
    Module.finrank ℝ (eigSpan A hA T) = T.card := by
  rw [eigSpan, finrank_span_finset_eq_card, Finset.card_image_of_injective _ (eigVec_injective A hA)]
  refine (eigVec_linearIndependent A hA).linearIndepOn_id.mono ?_
  rw [Finset.coe_image]
  exact Set.image_subset_range _ _

lemma eigSpan_dot_eq_zero {T : Finset (Fin h)} {v : Fin h → ℝ}
    (hv : v ∈ eigSpan A hA T) {j : Fin h} (hj : j ∉ T) :
    eigVec A hA j ⬝ᵥ v = 0 := by
  rw [eigSpan, Submodule.mem_span_finset] at hv
  obtain ⟨f, -, rfl⟩ := hv
  rw [dotProduct_sum]
  refine Finset.sum_eq_zero fun w hw => ?_
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
  rw [dotProduct_smul, eigVec_dot, if_neg (fun heq => hj (by subst heq; exact hi))]
  simp

lemma quadform_le_on_eigSpan {T : Finset (Fin h)} {μ : ℝ}
    (hμ : ∀ i ∈ T, hA.eigenvalues i ≤ μ) {v : Fin h → ℝ}
    (hv : v ∈ eigSpan A hA T) :
    v ⬝ᵥ A *ᵥ v ≤ μ * ∑ i, v i ^ 2 := by
  rw [quadform_eigen, normsq_eigen A hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ T
  · exact mul_le_mul_of_nonneg_right (hμ i hi) (sq_nonneg _)
  · rw [eigSpan_dot_eq_zero A hA hv hi]
    simp

lemma quadform_ge_on_eigSpan {T : Finset (Fin h)} {μ : ℝ}
    (hμ : ∀ i ∈ T, μ ≤ hA.eigenvalues i) {v : Fin h → ℝ}
    (hv : v ∈ eigSpan A hA T) :
    μ * ∑ i, v i ^ 2 ≤ v ⬝ᵥ A *ᵥ v := by
  rw [quadform_eigen, normsq_eigen A hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ T
  · exact mul_le_mul_of_nonneg_right (hμ i hi) (sq_nonneg _)
  · rw [eigSpan_dot_eq_zero A hA hv hi]
    simp

/-- The eigenvalue count: with a dead subspace of dimension m carrying
    the form at most a·‖v‖² and a live complement of dimension h − m
    carrying at least c·‖v‖² (a < c), exactly m eigenvalues are at
    most a, exactly h − m are at least c, and none lies between. -/
theorem eigenvalue_count_of_block_bounds {a c : ℝ} (hac : a < c) {m : ℕ}
    (D L : Submodule ℝ (Fin h → ℝ))
    (hD : Module.finrank ℝ D = m) (hLdim : Module.finrank ℝ L = h - m)
    (hm : m ≤ h)
    (hDle : ∀ v ∈ D, v ⬝ᵥ A *ᵥ v ≤ a * ∑ i, v i ^ 2)
    (hL : ∀ v ∈ L, c * ∑ i, v i ^ 2 ≤ v ⬝ᵥ A *ᵥ v) :
    (Finset.univ.filter fun i => hA.eigenvalues i ≤ a).card = m
    ∧ (Finset.univ.filter fun i => c ≤ hA.eigenvalues i).card = h - m
    ∧ ∀ i, hA.eigenvalues i ≤ a ∨ c ≤ hA.eigenvalues i := by
  set Q : (Fin h → ℝ) → ℝ := fun v => v ⬝ᵥ A *ᵥ v with hQ
  -- (i) eigenvectors below c meet L trivially
  have hbelow : (Finset.univ.filter fun i => hA.eigenvalues i < c).card ≤ m := by
    set T := Finset.univ.filter fun i => hA.eigenvalues i < c with hT
    rcases T.eq_empty_or_nonempty with hemp | hne
    · rw [hemp]; simp
    · set a' := T.sup' hne hA.eigenvalues with ha'
      have ha'c : a' < c := (Finset.sup'_lt_iff hne).mpr fun i hi =>
        (Finset.mem_filter.mp hi).2
      have hbound : ∀ v ∈ eigSpan A hA T, Q v ≤ a' * ∑ i, v i ^ 2 :=
        fun v hv => quadform_le_on_eigSpan A hA
          (fun i hi => Finset.le_sup' hA.eigenvalues hi) hv
      have := small_subspace_dim_le Q ha'c L hL (eigSpan A hA T) hbound
      rw [finrank_eigSpan, hLdim] at this
      omega
  -- (ii) eigenvectors above a meet D trivially
  have habove : (Finset.univ.filter fun i => a < hA.eigenvalues i).card ≤ h - m := by
    set T := Finset.univ.filter fun i => a < hA.eigenvalues i with hT
    rcases T.eq_empty_or_nonempty with hemp | hne
    · rw [hemp]; simp
    · set c' := T.inf' hne hA.eigenvalues with hc'
      have hac' : a < c' := (Finset.lt_inf'_iff hne).mpr fun i hi =>
        (Finset.mem_filter.mp hi).2
      have hbound : ∀ v ∈ eigSpan A hA T, c' * ∑ i, v i ^ 2 ≤ Q v :=
        fun v hv => quadform_ge_on_eigSpan A hA
          (fun i hi => Finset.inf'_le hA.eigenvalues hi) hv
      have := small_subspace_dim_le Q hac' (eigSpan A hA T) hbound D hDle
      rw [finrank_eigSpan, hD] at this
      omega
  -- (iii) the counts
  have hsplit1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin h))) (fun i => hA.eigenvalues i ≤ a)
  have hsplit2 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin h))) (fun i => hA.eigenvalues i < c)
  simp only [not_le, not_lt, Finset.card_univ, Fintype.card_fin] at hsplit1 hsplit2
  have hsub : (Finset.univ.filter fun i => hA.eigenvalues i ≤ a)
      ⊆ Finset.univ.filter fun i => hA.eigenvalues i < c := by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, lt_of_le_of_lt hi.2 hac⟩
  have hcardS := Finset.card_le_card hsub
  have hS : (Finset.univ.filter fun i => hA.eigenvalues i ≤ a).card = m := by omega
  have hlt : (Finset.univ.filter fun i => hA.eigenvalues i < c).card = m := by omega
  have hB : (Finset.univ.filter fun i => c ≤ hA.eigenvalues i).card = h - m := by omega
  refine ⟨hS, hB, fun i => ?_⟩
  have heq : (Finset.univ.filter fun i => hA.eigenvalues i ≤ a)
      = Finset.univ.filter fun i => hA.eigenvalues i < c :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  by_cases hi : hA.eigenvalues i < c
  · left
    have : i ∈ Finset.univ.filter fun i => hA.eigenvalues i < c :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    rw [← heq] at this
    exact (Finset.mem_filter.mp this).2
  · right
    exact not_lt.mp hi

end EigenvalueCount

/-! ### The singular-value reading

The singular values of a map W are the square roots of the
eigenvalues of its Gram matrix WᵀW, and vᵀ(WᵀW)v = ‖Wv‖². The
eigenvalue count therefore reads singular values directly: a map
that contracts an m-dimensional subspace below √a and keeps a
complementary subspace above √c has exactly m squared singular values
at most a and h − m at least c. -/

section SingularValues

open Matrix

variable {h k : ℕ} (W : Matrix (Fin k) (Fin h) ℝ)

/-- The Gram form is the squared image norm. -/
lemma gram_quadform (v : Fin h → ℝ) :
    v ⬝ᵥ (Wᵀ * W) *ᵥ v = ∑ j, (W *ᵥ v) j ^ 2 := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, sq]

set_option linter.deprecated false in
/-- The singular-value count: exactly m squared singular values of W
    (eigenvalues of WᵀW) are at most a and h − m are at least c. -/
theorem singular_value_count_of_block_bounds {a c : ℝ} (hac : a < c) {m : ℕ}
    (D L : Submodule ℝ (Fin h → ℝ))
    (hD : Module.finrank ℝ D = m) (hLdim : Module.finrank ℝ L = h - m)
    (hm : m ≤ h)
    (hDle : ∀ v ∈ D, ∑ j, (W *ᵥ v) j ^ 2 ≤ a * ∑ i, v i ^ 2)
    (hL : ∀ v ∈ L, c * ∑ i, v i ^ 2 ≤ ∑ j, (W *ᵥ v) j ^ 2) :
    (Finset.univ.filter fun i =>
        (isHermitian_transpose_mul_self W).eigenvalues i ≤ a).card = m
    ∧ (Finset.univ.filter fun i =>
        c ≤ (isHermitian_transpose_mul_self W).eigenvalues i).card = h - m
    ∧ ∀ i, (isHermitian_transpose_mul_self W).eigenvalues i ≤ a
        ∨ c ≤ (isHermitian_transpose_mul_self W).eigenvalues i := by
  refine eigenvalue_count_of_block_bounds (Wᵀ * W) (isHermitian_transpose_mul_self W)
    hac D L hD hLdim hm (fun v hv => ?_) (fun v hv => ?_)
  · rw [gram_quadform]; exact hDle v hv
  · rw [gram_quadform]; exact hL v hv

end SingularValues

end DeadDirections
