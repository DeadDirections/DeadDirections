/-
  Track B, deliverable B1, first arc: submersions between normed
  spaces.

  Mathlib has immersions and the implicit function theorem and no
  submersion API (surveyed 2026-08-16 against the pin). This module
  starts one at the normed-space level, where the quotient program
  needs it and where the eventual manifold definition will factor
  through charts: a submersion at a point is a strict derivative
  that is surjective with closed-complemented kernel, the
  complement being automatic in finite dimension. The implicit
  function theorem then produces the local right inverse: a section
  through the point with f ∘ g = id near the image. The concrete
  submersion of the matrix quotient (A3) is the motivating instance;
  its Fréchet packaging, stability lemmas, section continuity, and
  the openness of submersions are the next arcs of B1.
-/
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed
import DeadDirections.MatrixQuotient

namespace DeadDirections

open Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A submersion at a point: a strict derivative, surjective, with
    closed-complemented kernel. -/
def IsSubmersionAt (f : E → F) (a : E) : Prop :=
  ∃ f' : E →L[ℝ] F, HasStrictFDerivAt f f' a
    ∧ f'.range = ⊤
    ∧ f'.ker.ClosedComplemented

/-- In finite dimension the kernel complement is automatic: a
    surjective strict derivative is a submersion. -/
theorem isSubmersionAt_of_finiteDimensional [CompleteSpace E]
    [FiniteDimensional ℝ F]
    {f : E → F} {f' : E →L[ℝ] F} {a : E}
    (hf : HasStrictFDerivAt f f' a)
    (hsurj : f'.range = ⊤) :
    IsSubmersionAt f a :=
  ⟨f', hf, hsurj,
    f'.ker_closedComplemented_of_finiteDimensional_range⟩

/-- The local section: a submersion admits a right inverse through
    the point, continuous at the image, with f ∘ g the identity near
    the image. The implicit function theorem's zero-kernel slice,
    read through the partial homeomorphism. -/
theorem IsSubmersionAt.exists_local_section [CompleteSpace E]
    [CompleteSpace F] {f : E → F} {a : E}
    (h : IsSubmersionAt f a) :
    ∃ g : F → E, g (f a) = a ∧ ContinuousAt g (f a)
      ∧ ∀ᶠ z in 𝓝 (f a), f (g z) = z := by
  obtain ⟨f', hf, hsurj, hker⟩ := h
  set e := hf.implicitToOpenPartialHomeomorphOfComplemented f f'
    hsurj hker with he
  have hmemS : a ∈ e.source :=
    hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source
      hsurj hker
  have hmemT : (f a, (0 : f'.ker)) ∈ e.target :=
    hf.mem_implicitToOpenPartialHomeomorphOfComplemented_target
      hsurj hker
  have hcomp : Tendsto (fun z : F => (z, (0 : f'.ker)))
      (𝓝 (f a)) (𝓝 (f a, (0 : f'.ker))) := by
    rw [nhds_prod_eq]
    exact tendsto_id.prodMk tendsto_const_nhds
  refine ⟨fun z => e.symm (z, 0), ?_, ?_, ?_⟩
  · show e.symm (f a, (0 : f'.ker)) = a
    have hself :
        e a = (f a, (0 : f'.ker)) :=
      hf.implicitToOpenPartialHomeomorphOfComplemented_self hsurj
        hker
    rw [← hself]
    exact e.left_inv hmemS
  · have hsymm : ContinuousAt e.symm (f a, (0 : f'.ker)) :=
      e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hmemT)
    exact hsymm.tendsto.comp hcomp
  · have hev := e.eventually_right_inverse hmemT
    filter_upwards [hcomp.eventually hev] with z hz
    have h1 : (e (e.symm (z, (0 : f'.ker)))).1
        = ((z, (0 : f'.ker)) : F × f'.ker).1 := congrArg Prod.fst hz
    rw [hf.implicitToOpenPartialHomeomorphOfComplemented_fst hsurj
      hker] at h1
    exact h1

/-- Submersions compose, in the finite-dimensional target case. -/
theorem IsSubmersionAt.comp {G' : Type*} [NormedAddCommGroup G']
    [NormedSpace ℝ G'] [CompleteSpace E] [FiniteDimensional ℝ G']
    {f : E → F} {g : F → G'} {a : E}
    (hg : IsSubmersionAt g (f a)) (hf : IsSubmersionAt f a) :
    IsSubmersionAt (g ∘ f) a := by
  obtain ⟨g', hgd, hgs, -⟩ := hg
  obtain ⟨f', hfd, hfs, -⟩ := hf
  apply isSubmersionAt_of_finiteDimensional (hgd.comp a hfd)
  rw [LinearMap.range_eq_top] at hgs hfs ⊢
  rw [ContinuousLinearMap.coe_comp]
  exact hgs.comp hfs

/-- A submersion maps neighborhoods onto neighborhoods: the section
    is continuous through the point, so the image filter fills the
    target filter, and the strict derivative gives the other
    inclusion. -/
theorem IsSubmersionAt.map_nhds_eq [CompleteSpace E]
    [CompleteSpace F] {f : E → F} {a : E} (h : IsSubmersionAt f a) :
    Filter.map f (𝓝 a) = 𝓝 (f a) := by
  obtain ⟨g, hga, hgc, hev⟩ := h.exists_local_section
  apply le_antisymm
  · obtain ⟨f', hfd, -, -⟩ := h
    exact hfd.continuousAt
  · intro s hs
    rw [Filter.mem_map] at hs
    have h1 : g ⁻¹' (f ⁻¹' s) ∈ 𝓝 (f a) :=
      hgc.preimage_mem_nhds (by rwa [hga])
    filter_upwards [h1, hev] with z hz1 hz2
    rw [← hz2]
    exact hz1

/-! ### The motivating instance

The matrix product map on layer tuples is a submersion at every
point of the invertible stratum. The ordered product is a continuous
multilinear map (mkPiAlgebraFin), so its strict derivative is the
linearDeriv, whose value is the sum of single-slot substitutions:
the tuple form of the chain derivative. Surjectivity is A3's
single-slot construction: aim the head slot through the inverse
tail product and every other substitution carries a zero factor. -/

section ProductSubmersion

attribute [local instance] Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {h L : ℕ}

/-- The end-to-end product on layer tuples is a submersion at every
    invertible tuple. -/
theorem isSubmersionAt_prodTuple
    (Wu : Fin (L+1) → (Matrix (Fin (h+1)) (Fin (h+1)) ℝ)ˣ) :
    IsSubmersionAt
      (fun W : Fin (L+1) → Matrix (Fin (h+1)) (Fin (h+1)) ℝ =>
        (List.ofFn W).prod)
      (fun i => ↑(Wu i)) := by
  set A := Matrix (Fin (h+1)) (Fin (h+1)) ℝ
  set Fm := ContinuousMultilinearMap.mkPiAlgebraFin ℝ (L+1) A
    with hFm
  set x : Fin (L+1) → A := fun i => ↑(Wu i) with hx
  have hfun : (fun W : Fin (L+1) → A => (List.ofFn W).prod) = ⇑Fm :=
    funext fun W =>
      (ContinuousMultilinearMap.mkPiAlgebraFin_apply W).symm
  rw [hfun]
  have hfd : HasStrictFDerivAt (⇑Fm) (Fm.linearDeriv x) x :=
    Fm.hasStrictFDerivAt x
  apply isSubmersionAt_of_finiteDimensional hfd
  rw [LinearMap.range_eq_top]
  intro U
  set tailU := (List.ofFn (fun i : Fin L => Wu i.succ)).prod with htU
  set w : A := U * ↑tailU⁻¹ with hw
  refine ⟨Pi.single 0 w, ?_⟩
  simp only [ContinuousLinearMap.coe_coe,
    ContinuousMultilinearMap.linearDeriv_apply]
  have htail : (List.ofFn (fun i : Fin L => x i.succ)).prod
      = (↑tailU : A) := by
    rw [htU, ← units_val_prod]
    congr 1
    rw [List.map_ofFn]
    rfl
  have hzero : ∀ i : Fin (L+1), i ≠ 0
      → Fm (Function.update x i ((Pi.single 0 w : Fin (L+1) → A) i))
        = 0 := by
    intro i hi
    rw [Pi.single_eq_of_ne hi]
    rw [ContinuousMultilinearMap.mkPiAlgebraFin_apply]
    apply List.prod_eq_zero
    rw [List.mem_ofFn]
    exact ⟨i, Function.update_self i 0 x⟩
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0)
    (fun i _ hi => hzero i hi)]
  rw [Pi.single_eq_same, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    List.ofFn_succ]
  have hhead : Function.update x 0 w 0 = w := Function.update_self 0 w x
  have htailf : ∀ i : Fin L, Function.update x 0 w i.succ = x i.succ :=
    fun i => Function.update_of_ne (Fin.succ_ne_zero i) w x
  rw [hhead, List.prod_cons,
    show (List.ofFn fun i : Fin L => Function.update x 0 w i.succ)
      = List.ofFn (fun i : Fin L => x i.succ) from
      congrArg List.ofFn (funext htailf), htail, hw, mul_assoc,
    show ((↑tailU⁻¹ : A) * ↑tailU) = 1 from Units.inv_mul _, mul_one]

/-- The quotient-topology seed: the product map carries
    neighborhoods of an invertible tuple onto neighborhoods of the
    end-to-end product. -/
theorem matProd_map_nhds
    (Wu : Fin (L+1) → (Matrix (Fin (h+1)) (Fin (h+1)) ℝ)ˣ) :
    Filter.map
      (fun W : Fin (L+1) → Matrix (Fin (h+1)) (Fin (h+1)) ℝ =>
        (List.ofFn W).prod)
      (𝓝 (fun i => ↑(Wu i)))
    = 𝓝 (List.ofFn fun i =>
        ((Wu i : Matrix (Fin (h+1)) (Fin (h+1)) ℝ))).prod :=
  (isSubmersionAt_prodTuple Wu).map_nhds_eq

end ProductSubmersion

end DeadDirections
