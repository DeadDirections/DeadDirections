/-
  DDCAdam gauge equivariance (theory paper, prop:ddcadam_equivariance).

  Formal model of Algorithm alg:ddcadam, one step on one gauge block.
  The optimizer-state maps (Adam moments, bias correction, the vertical
  mode choice) enter only through their arguments, so they are modelled
  as ARBITRARY functions of the gauge-decomposed inputs and an opaque
  state. The proposition's content is exactly that these inputs are
  G-invariant, hence any deterministic state map is invariant
  (transport_h = identity), and that the multiplicative radial
  application turns invariant steps into an equivariant update.

  Covered here:
  * Type (ii) single multiplicative rescale (ReLURescaleGauge):
    h_c : (W₁, W₂) ↦ (c·W₁, c⁻¹·W₂), gradients (c⁻¹·g₁, c·g₂).
    Main theorems `ddcadamMult_fst_equivariant` / `_snd_equivariant`,
    with decoupled weight decay included as the shrink factor δ
    (algorithm step 1; the global rescale commutes with the gauge).
  * Type (i) translation gauge: the step map reads W only in the final
    additive application, so equivariance is `ddcadamTransl_equivariant`
    (stated at λ = 0, per the algorithm's scoping).

  * Chained (ℝ⁺)^{L-1} gauge (section 5): the update map commutes
    with EVERY positive per-block scaling family; the gauge group is
    the product-one subfamily.
  * Per-channel (ℝ⁺)^d LNScaleGauge (section 6): the pair theorem
    applied pointwise over disjoint channels.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace DeadDirections

open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## 1. Per-block quantities of Algorithm alg:ddcadam, step 2 -/

/-- Log-norm gradient ĝ = ⟨g, W⟩ (the gradient of the loss in the
    log-norm coordinate, up to the ρ² factor collapsed by q_V). -/
def hatg (g W : E) : ℝ := ⟪g, W⟫

/-- Tangential gradient g − (ĝ/ρ²) W, the component orthogonal to W. -/
def gtan (g W : E) : E := g - (hatg g W / ‖W‖ ^ 2) • W

/-- Adam input on the tangential channel: ρ · g^tan. -/
def tangIn (g W : E) : E := ‖W‖ • gtan g W

/-- Re-projection of a per-coordinate update against the current W
    (algorithm step 6, multiplicative case). -/
def reproj (u W : E) : E := u - (⟪u, W⟫ / ‖W‖ ^ 2) • W

/-- Block application (algorithm step 7, multiplicative case): a
    multiplicative radial step and an additive tangential step,
    W ↦ exp(Δlogρ)·W − η·ρ·u. -/
def applyBlock (η r : ℝ) (u W : E) : E :=
  Real.exp r • W - (η * ‖W‖) • u

/-! ## 2. Transformation laws under a block scaling k > 0

The gauge moves a block by W ↦ k·W and its gradient by g ↦ k⁻¹·g
(k = c on the first block, k = c⁻¹ on the second; primed variants
below phrase the second block's instance directly). -/

lemma norm_smul_of_pos {k : ℝ} (hk : 0 < k) (W : E) :
    ‖k • W‖ = k * ‖W‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk]

/-- ĝ is G-invariant. -/
lemma hatg_gauge {k : ℝ} (hk : k ≠ 0) (g W : E) :
    hatg (k⁻¹ • g) (k • W) = hatg g W := by
  simp only [hatg, real_inner_smul_left, real_inner_smul_right]
  rw [mul_inv_cancel_left₀ hk]

/-- ĝ invariance, phrased for the inverse-scaled block. -/
lemma hatg_gauge' {k : ℝ} (hk : k ≠ 0) (g W : E) :
    hatg (k • g) (k⁻¹ • W) = hatg g W := by
  have h := hatg_gauge (inv_ne_zero hk) g W
  rwa [inv_inv] at h

/-- g^tan transforms like the gradient: g^tan ↦ k⁻¹ · g^tan. -/
lemma gtan_gauge {k : ℝ} (hk : 0 < k) (g W : E) :
    gtan (k⁻¹ • g) (k • W) = k⁻¹ • gtan g W := by
  have hk' : k ≠ 0 := ne_of_gt hk
  have hcoef : hatg g W / ‖k • W‖ ^ 2 * k = k⁻¹ * (hatg g W / ‖W‖ ^ 2) := by
    rw [norm_smul_of_pos hk, mul_pow]
    rcases eq_or_ne ‖W‖ 0 with h0 | h0
    · simp [h0]
    · field_simp
  unfold gtan
  rw [hatg_gauge hk', smul_sub, smul_smul, smul_smul, hcoef]

/-- The tangential Adam input ρ·g^tan is G-invariant. -/
lemma tangIn_gauge {k : ℝ} (hk : 0 < k) (g W : E) :
    tangIn (k⁻¹ • g) (k • W) = tangIn g W := by
  have hk' : k ≠ 0 := ne_of_gt hk
  rw [tangIn, gtan_gauge hk, norm_smul_of_pos hk, tangIn, smul_smul]
  congr 1
  rw [mul_comm k ‖W‖, mul_assoc, mul_inv_cancel₀ hk', mul_one]

/-- Tangential-input invariance, phrased for the inverse-scaled block. -/
lemma tangIn_gauge' {k : ℝ} (hk : 0 < k) (g W : E) :
    tangIn (k • g) (k⁻¹ • W) = tangIn g W := by
  have h := tangIn_gauge (inv_pos.mpr hk) g W
  rwa [inv_inv] at h

/-- Re-projection against k·W equals re-projection against W: the
    projected update is G-invariant when its input is. -/
lemma reproj_gauge {k : ℝ} (hk : 0 < k) (u W : E) :
    reproj u (k • W) = reproj u W := by
  have hk' : k ≠ 0 := ne_of_gt hk
  have hcoef : k * ⟪u, W⟫ / ‖k • W‖ ^ 2 * k = ⟪u, W⟫ / ‖W‖ ^ 2 := by
    rw [norm_smul_of_pos hk, mul_pow]
    rcases eq_or_ne ‖W‖ 0 with h0 | h0
    · simp [h0]
    · field_simp
  unfold reproj
  rw [real_inner_smul_right, smul_smul, hcoef]

/-- The block application is G-equivariant: an invariant radial step r
    and an invariant update u applied at k·W give k times the update
    applied at W. -/
lemma applyBlock_gauge {k : ℝ} (hk : 0 < k) (η r : ℝ) (u W : E) :
    applyBlock η r u (k • W) = k • applyBlock η r u W := by
  unfold applyBlock
  rw [norm_smul_of_pos hk]
  simp only [smul_sub, smul_smul]
  congr 1
  · congr 1
    ring
  · congr 1
    ring

/-! ## 3. The two-block multiplicative step (ReLURescaleGauge)

State maps are arbitrary functions of the invariant inputs: `FU`, `FV`
consume the radial and gauge-mode scalars (algorithm steps 4 and 5),
`F₁`, `F₂` the tangential inputs (per-coordinate Adam), and `a₁`, `a₂`
assemble the per-block log-norm steps from (Δ_U, u_V). δ is the
decoupled weight-decay shrink 1 − ηλ (algorithm step 1). -/

section MultPair

variable {E₁ E₂ S : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]

/-- Radial scalar g_U = (ĝ₁ + ĝ₂)/√2 on the shrunk parameters. -/
def gU (δ : ℝ) (W₁ g₁ : E₁) (W₂ g₂ : E₂) : ℝ :=
  (hatg g₁ (δ • W₁) + hatg g₂ (δ • W₂)) / Real.sqrt 2

/-- Gauge-mode scalar g_V = (ĝ₁ − ĝ₂)/√2 on the shrunk parameters. -/
def gV (δ : ℝ) (W₁ g₁ : E₁) (W₂ g₂ : E₂) : ℝ :=
  (hatg g₁ (δ • W₁) - hatg g₂ (δ • W₂)) / Real.sqrt 2

/-- One DDCAdam step on the first block of a multiplicative pair. -/
def ddcadamMultFst (FU FV : ℝ → S → ℝ) (F₁ : E₁ → S → E₁)
    (a₁ : ℝ → ℝ → ℝ) (η δ : ℝ) (s : S)
    (W₁ g₁ : E₁) (W₂ g₂ : E₂) : E₁ :=
  applyBlock η
    (a₁ (FU (gU δ W₁ g₁ W₂ g₂) s) (FV (gV δ W₁ g₁ W₂ g₂) s))
    (reproj (F₁ (tangIn g₁ (δ • W₁)) s) (δ • W₁))
    (δ • W₁)

/-- One DDCAdam step on the second block of a multiplicative pair. -/
def ddcadamMultSnd (FU FV : ℝ → S → ℝ) (F₂ : E₂ → S → E₂)
    (a₂ : ℝ → ℝ → ℝ) (η δ : ℝ) (s : S)
    (W₁ g₁ : E₁) (W₂ g₂ : E₂) : E₂ :=
  applyBlock η
    (a₂ (FU (gU δ W₁ g₁ W₂ g₂) s) (FV (gV δ W₁ g₁ W₂ g₂) s))
    (reproj (F₂ (tangIn g₂ (δ • W₂)) s) (δ • W₂))
    (δ • W₂)

/-- The radial scalar is invariant under the pair gauge action
    (c·W₁, c⁻¹·W₂), (c⁻¹·g₁, c·g₂). Weight decay commutes with the
    action, so the shrink factor δ passes through. -/
lemma gU_gauge {c : ℝ} (hc : 0 < c) (δ : ℝ)
    (W₁ g₁ : E₁) (W₂ g₂ : E₂) :
    gU δ (c • W₁) (c⁻¹ • g₁) (c⁻¹ • W₂) (c • g₂) = gU δ W₁ g₁ W₂ g₂ := by
  have hc' : c ≠ 0 := ne_of_gt hc
  unfold gU
  rw [smul_comm δ c W₁, smul_comm δ c⁻¹ W₂, hatg_gauge hc',
    hatg_gauge' hc']

/-- The gauge-mode scalar is likewise invariant. -/
lemma gV_gauge {c : ℝ} (hc : 0 < c) (δ : ℝ)
    (W₁ g₁ : E₁) (W₂ g₂ : E₂) :
    gV δ (c • W₁) (c⁻¹ • g₁) (c⁻¹ • W₂) (c • g₂) = gV δ W₁ g₁ W₂ g₂ := by
  have hc' : c ≠ 0 := ne_of_gt hc
  unfold gV
  rw [smul_comm δ c W₁, smul_comm δ c⁻¹ W₂, hatg_gauge hc',
    hatg_gauge' hc']

/-- prop:ddcadam_equivariance, type (ii), first block: the DDCAdam step
    commutes with the gauge, W₁' ↦ c·W₁'. Every state map is evaluated
    at the same (invariant) arguments on both sides, which is the
    transport_h = identity clause. -/
theorem ddcadamMult_fst_equivariant
    (FU FV : ℝ → S → ℝ) (F₁ : E₁ → S → E₁) (a₁ : ℝ → ℝ → ℝ)
    (η δ : ℝ) (s : S) (W₁ g₁ : E₁) (W₂ g₂ : E₂)
    {c : ℝ} (hc : 0 < c) :
    ddcadamMultFst FU FV F₁ a₁ η δ s
        (c • W₁) (c⁻¹ • g₁) (c⁻¹ • W₂) (c • g₂)
      = c • ddcadamMultFst FU FV F₁ a₁ η δ s W₁ g₁ W₂ g₂ := by
  unfold ddcadamMultFst
  rw [gU_gauge hc δ W₁ g₁ W₂ g₂, gV_gauge hc δ W₁ g₁ W₂ g₂,
    smul_comm δ c W₁, tangIn_gauge hc, reproj_gauge hc,
    applyBlock_gauge hc]

/-- prop:ddcadam_equivariance, type (ii), second block: W₂' ↦ c⁻¹·W₂'. -/
theorem ddcadamMult_snd_equivariant
    (FU FV : ℝ → S → ℝ) (F₂ : E₂ → S → E₂) (a₂ : ℝ → ℝ → ℝ)
    (η δ : ℝ) (s : S) (W₁ g₁ : E₁) (W₂ g₂ : E₂)
    {c : ℝ} (hc : 0 < c) :
    ddcadamMultSnd FU FV F₂ a₂ η δ s
        (c • W₁) (c⁻¹ • g₁) (c⁻¹ • W₂) (c • g₂)
      = c⁻¹ • ddcadamMultSnd FU FV F₂ a₂ η δ s W₁ g₁ W₂ g₂ := by
  have hc' : 0 < c⁻¹ := inv_pos.mpr hc
  unfold ddcadamMultSnd
  rw [gU_gauge hc δ W₁ g₁ W₂ g₂, gV_gauge hc δ W₁ g₁ W₂ g₂,
    smul_comm δ c⁻¹ W₂, tangIn_gauge' hc, reproj_gauge hc',
    applyBlock_gauge hc']

end MultPair

/-! ## 4. Translation gauges (type (i))

The action is W ↦ W + t along the gauge direction; tangent vectors are
unchanged (dh = Id), so the gradient is invariant and the projectors
are W-independent. The whole step map therefore reads W only in the
final additive application, and equivariance is immediate. Stated at
λ = 0 per algorithm step 1. -/

section Translation

variable {E S : Type*} [AddCommGroup E]

/-- One DDCAdam step for a translation gauge: W ↦ W − step(g, state),
    with `step` the assembled vertical-plus-horizontal update
    (algorithm steps 2 to 7; its internals never read W because the
    projectors are constant). -/
def ddcadamTransl (step : E → S → E) (s : S) (W g : E) : E :=
  W - step g s

/-- prop:ddcadam_equivariance, type (i): the step commutes with the
    shift action W ↦ W + t, for every shift t (in particular along the
    gauge directions of the CE specs). -/
theorem ddcadamTransl_equivariant (step : E → S → E) (s : S)
    (W g t : E) :
    ddcadamTransl step s (W + t) g = ddcadamTransl step s W g + t := by
  simp only [ddcadamTransl]
  abel

end Translation

/-! ## 5. The chained multiplicative gauge

The chained (ℝ⁺)^{L−1} gauge acts on a chain (W₁, …, W_L) by
W_ℓ ↦ a_ℓ·W_ℓ with a_ℓ = c_{ℓ−1}⁻¹·c_ℓ, so the scaling family has
∏ a_ℓ = 1. The formal statement below is stronger: the update map
commutes with EVERY positive per-block scaling family, product-one or
not. Each state-map input is a per-block invariant (the log-norm
gradients ⟨g_ℓ, W_ℓ⟩ and the tangential inputs ρ_ℓ·g_ℓ^tan), so
invariance never uses the constraint; the product-one condition is
what makes the constrained subgroup a symmetry of the LOSS, not a
hypothesis the update map needs. The paper's global zero-mean/total-sum
split appears here as the `assemble` maps, which build each block's
log-norm step from the full invariant vector (covering the radial
coordinate, the DCT gauge-mode basis, and any other W-independent
assembly at once). -/

section Chained

variable {L : ℕ} {S : Type*} {E : Fin L → Type*}
  [∀ ℓ, NormedAddCommGroup (E ℓ)] [∀ ℓ, InnerProductSpace ℝ (E ℓ)]

/-- Invariant scalar inputs of the chained step: the log-norm gradients
    of every block, on the shrunk parameters. -/
def chainInvariants (δ : ℝ) (W g : ∀ ℓ, E ℓ) : Fin L → ℝ :=
  fun ℓ => hatg (g ℓ) (δ • W ℓ)

/-- One DDCAdam step on block ℓ of a chained multiplicative gauge.
    `assemble ℓ` builds block ℓ's log-norm step from the full vector
    of invariant scalars and the state; `F ℓ` is the per-coordinate
    state map on the tangential input. -/
def ddcadamChain (assemble : Fin L → (Fin L → ℝ) → S → ℝ)
    (F : ∀ ℓ, E ℓ → S → E ℓ) (η δ : ℝ) (s : S)
    (W g : ∀ ℓ, E ℓ) (ℓ : Fin L) : E ℓ :=
  applyBlock η (assemble ℓ (chainInvariants δ W g) s)
    (reproj (F ℓ (tangIn (g ℓ) (δ • W ℓ)) s) (δ • W ℓ))
    (δ • W ℓ)

lemma chainInvariants_gauge {a : Fin L → ℝ} (ha : ∀ ℓ, 0 < a ℓ)
    (δ : ℝ) (W g : ∀ ℓ, E ℓ) :
    chainInvariants δ (fun ℓ => a ℓ • W ℓ) (fun ℓ => (a ℓ)⁻¹ • g ℓ)
      = chainInvariants δ W g := by
  funext ℓ
  unfold chainInvariants
  rw [smul_comm δ (a ℓ) (W ℓ), hatg_gauge (ne_of_gt (ha ℓ))]

/-- prop:ddcadam_equivariance, chained multiplicative gauge: the step
    on every block commutes with any positive per-block scaling
    family. The chained gauge group is the product-one subfamily.
    Transport is the identity: both sides evaluate every state map at
    the same invariant arguments. -/
theorem ddcadamChain_equivariant
    (assemble : Fin L → (Fin L → ℝ) → S → ℝ)
    (F : ∀ ℓ, E ℓ → S → E ℓ) (η δ : ℝ) (s : S) (W g : ∀ ℓ, E ℓ)
    {a : Fin L → ℝ} (ha : ∀ ℓ, 0 < a ℓ) (ℓ : Fin L) :
    ddcadamChain assemble F η δ s (fun j => a j • W j)
        (fun j => (a j)⁻¹ • g j) ℓ
      = a ℓ • ddcadamChain assemble F η δ s W g ℓ := by
  unfold ddcadamChain
  rw [chainInvariants_gauge ha δ W g, smul_comm δ (a ℓ) (W ℓ),
    tangIn_gauge (ha ℓ), reproj_gauge (ha ℓ), applyBlock_gauge (ha ℓ)]

end Chained

/-! ## 6. The per-channel LN-scale gauge

The LNScaleGauge acts channel-wise on (γ, W_next): channel i is one
copy of the single multiplicative rescale on the pair
(γ_i, col_i W_next), and the channels are disjoint parameter blocks.
Equivariance is therefore the pair theorem applied pointwise in the
channel index, which is the composition claim of
prop:ddcadam_equivariance's per-channel clause. -/

section PerChannel

variable {d : ℕ} {S : Type*} {E : Fin d → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

/-- Per-channel LN-scale equivariance, γ side: channel i's scale
    coordinate transforms as γ_i ↦ c_i·γ_i. -/
theorem ddcadamLNScale_fst_equivariant
    (FU FV : ℝ → S → ℝ) (F₁ : Fin d → ℝ → S → ℝ) (a₁ : ℝ → ℝ → ℝ)
    (η δ : ℝ) (s : S) (γ gγ : Fin d → ℝ) (Wc gc : ∀ i, E i)
    {c : Fin d → ℝ} (hc : ∀ i, 0 < c i) (i : Fin d) :
    ddcadamMultFst FU FV (F₁ i) a₁ η δ s
        (c i • γ i) ((c i)⁻¹ • gγ i) ((c i)⁻¹ • Wc i) (c i • gc i)
      = c i • ddcadamMultFst FU FV (F₁ i) a₁ η δ s
          (γ i) (gγ i) (Wc i) (gc i) :=
  ddcadamMult_fst_equivariant FU FV (F₁ i) a₁ η δ s
    (γ i) (gγ i) (Wc i) (gc i) (hc i)

/-- Per-channel LN-scale equivariance, W_next side: channel i's column
    transforms as col_i ↦ c_i⁻¹·col_i. -/
theorem ddcadamLNScale_snd_equivariant
    (FU FV : ℝ → S → ℝ) (F₂ : ∀ i, E i → S → E i) (a₂ : ℝ → ℝ → ℝ)
    (η δ : ℝ) (s : S) (γ gγ : Fin d → ℝ) (Wc gc : ∀ i, E i)
    {c : Fin d → ℝ} (hc : ∀ i, 0 < c i) (i : Fin d) :
    ddcadamMultSnd FU FV (F₂ i) a₂ η δ s
        (c i • γ i) ((c i)⁻¹ • gγ i) ((c i)⁻¹ • Wc i) (c i • gc i)
      = (c i)⁻¹ • ddcadamMultSnd FU FV (F₂ i) a₂ η δ s
          (γ i) (gγ i) (Wc i) (gc i) :=
  ddcadamMult_snd_equivariant FU FV (F₂ i) a₂ η δ s
    (γ i) (gγ i) (Wc i) (gc i) (hc i)

end PerChannel

end

end DeadDirections
