# Blueprint of the DeadDirections formalization

A reader's map of the Lean 4 package that accompanies *Dead Directions:
Geometric Singular Learning*. One entry per row of the coverage ledger
(`proofs/COVERAGE.md`), grouped by theme, each giving what the Lean proves at
the scope the ledger states, the declarations that carry it, the hypotheses the
Lean consumes as inputs instead of deriving, and the other ledger rows whose
Lean results it uses.

Two companion graphs sit in `proofs/blueprint/`: `modules.mmd` draws the
package's own import edges, and `results.mmd` draws the row-level dependency
structure with nodes coloured by ledger status. Graphviz is not installed on
this machine, so `modules.dot`, `results.dot`, and their SVG renderings were
not produced; the Mermaid sources render in any Markdown viewer that carries
Mermaid, and in the GitHub web view.

## How to read a row

The ledger assigns each numbered paper result one of six statuses. This
document covers the three that carry Lean content.

- **full**: every clause of the paper statement is machine-checked at or
  beyond the paper's own scope. Fourteen of the fifty-six numbered results
  sit here, along with all three worked-example anchors.
- **partial**: one or more clauses are machine-checked, and the row names what
  the proof takes as a hypothesis. Forty numbered results sit here. On most of
  them the Lean runs at a *model scope*: a scalar chain, a diagonal
  configuration, a two-block Fisher matrix, a two-position attention layer. The
  model-scope proof certifies the mechanism the paper's argument uses; carrying
  it to a trained network is the paper's own bridge argument, not something the
  Lean establishes.
- **out**: no formalization planned. Two results sit here, one because its
  content is a numerical value and one because it needs resolution of
  singularities.

Every claim below inherits its row's status. When an entry says a statement is
machine-checked, the scope in the same paragraph is part of the claim: either
the row is fully certified, or the transfer from the model to a network rests
on the hypotheses listed under **Inputs**.

The package builds under Lean toolchain `v4.29.0` against the pinned Mathlib
revision in `lake-manifest.json`, and no declaration in it invokes `sorry`.

---

## Rate calculus and worked anchors

The rate calculus is the package's shared vocabulary. `HasLeadingRate F p c`
says that `F t / t ^ p` converges to `c` as `t` approaches zero from above, and
`HasLeadingRateR` is the same predicate with a real exponent through
`Real.rpow`. Almost every other row states its conclusion in one of these two
forms, which is why the results graph has so many edges into
`thm:fisher_decay`.

### thm:fisher_decay (full)

**Proved.** The Fisher rate theorem is machine-checked in both of its layers,
at or beyond the paper's scope. The abstract layer takes a score expansion
`s(t) = k·t^(k−1)·a + r(t)` and returns the Fisher expansion with leading rate
`2(k−1)` and coefficient `k²·E[a²]`; the two asymptotic readings follow, the
log-log slope of the directional Fisher tending to `2(k−1)` and the estimator
`k̂ = 1 + slope/2` tending to `k`. The concrete layer instantiates the abstract
one on the two-component mixture curve `(w, m) = (t, t)` and discharges every
hypothesis there, so the mixture reading needs no analytic input from the
reader. The moving-measure convention of the paper is handled by
`HasLeadingRate.of_relatively_close`: leading rates survive a perturbation of
the density that is `1 + O(t)`.

**Lean.** `HasLeadingRate`, `hasLeadingRate_of_expansion`,
`HasLeadingRate.log_slope`, `HasLeadingRate.khat_recovers`,
`fisher_expansion_of_score_expansion`, `fisher_decay_slope`,
`HasLeadingRate.of_relatively_close`, `mixture_fisher_expansion`,
`mixture_fisher_slope`.

**Inputs.** The abstract statement consumes the score expansion with `E[a²]`
finite and positive and the `L²` remainder bound `∫ r(t)² ≤ M·t^(2k)`, under
the fixed measure `p*`. Those two package the paper's hypotheses (ii) and
(iii). On the mixture curve nothing is left assumed: the closed-form score is
certified as the logarithmic `t`-derivative of the curve density and the
remainder bound is proved with an explicit dominator.

**Depends on.** Nothing. This row is the base of the graph.

### cor:fisher_structure (partial)

**Proved.** The cross entry of the Fisher matrix is machine-checked at the
expansion level: with the transversal score `k·t^(k−1)·a + r₁` and the
tangential score `b + r₂`, both with `L²` remainders, the cross moment is
`k·t^(k−1)·E[a·b]` with an explicit remainder bound at `t^k`. The tangential
block carries `F_αβ = g_αβ + O(t)` with the constant written out. The assembled
statement converts entrywise perturbation bounds to a bound on the quadratic
form and lower-bounds the perturbed block form by the Schur complement minus
the perturbation cost.

**Lean.** `cross_moment_expansion`, `tangential_moment_expansion`,
`abs_integral_mul_le_weighted`, `quadform_entrywise_bound`,
`assembled_schur_slice`.

**Inputs.** The per-model score expansions, which instantiate the hypotheses.
All cross bounds run through a weighted AM-GM integral bound. The ledger row
records nothing missing at model scope.

**Depends on.** Nothing among the ledger rows; the declarations live in
`FisherDecay` and `SigmaMin` alongside the rate calculus.

### Gaussian location anchor (full)

**Proved.** The worked Gaussian example is machine-checked as a chain of exact
identities. The Fisher information of `N(μ, σ²)` in `μ` is `1/σ²`; along
`μ(t) = t^k` the directional Fisher is `k²·t^(2(k−1))` and the KL is `t^(2k)/2`,
so the ratio `F(t)·t² = 2k²·K(t)` is an identity at every `t`;
the curve has leading rate `2(k−1)` with coefficient `k²` and KL order `k`, and
`gaussian_curve_readings` bundles both readings on the one family.

**Lean.** `fisherMu_gaussian`, `curveFisher_eq`, `curveKL_eq`,
`curve_fisher_kl_ratio`, `curveFisher_hasLeadingRate`, `HasKLOrder`,
`curveKL_hasKLOrder`, `gaussian_curve_readings`.

**Inputs.** Nothing beyond the family's definition. Each statement is an exact
identity or an exact limit.

**Depends on.** `thm:fisher_decay`, for the rate predicate the readings are
stated in.

### Mixture weight boundary (full)

**Proved.** The two-component mixture Fisher determinant tends to zero as the
weight goes to zero from above and stays strictly positive at nonzero mean
separation with weight in the open unit interval, which is the rank loss at the
degeneration boundary as an exact limit and an exact positivity.

**Lean.** `mixture_rank_loss`, `mixture_det_pos`.

**Inputs.** Nothing beyond the family's definition.

**Depends on.** Nothing.

### Bridge invariant on the mixture curve (full)

**Proved.** The KL divergence of the base model from the curve `(w, m) = (t, t)`
is `t⁴/2 + O(t⁵)`, so the curve has KL order 2. Paired with the Fisher
instantiation of `thm:fisher_decay` on the same curve, one family carries both
readings of the bridge invariant, the KL order on the Watanabe side and the
leading rate `2(k−1)` with coefficient `k²·E[a²]` on the Amari side.

**Lean.** `mixKL`, `mixKL_hasKLOrder`, `mixture_readings`.

**Inputs.** Nothing; every hypothesis in both chains is proved.

**Depends on.** `thm:fisher_decay` (through `mixture_fisher_expansion`, which
`mixture_readings` pairs with the KL side) and the Gaussian location anchor
(through `HasKLOrder`).

---

## Bridge channels

These rows carry the paper's central mechanism: a dead direction's backward
signal decays as a power of the approach parameter, and the exponent counts
layers. The Lean covers the three activation classes (P1) linear, (P2) smooth
with a quadratic Taylor bound, and (P3) positively homogeneous, plus the
biased, rectangular, multi-direction, rotated, and cross-entropy variants.

### thm:bridge (partial)

**Proved.** The channel core of all three classes is machine-checked, forward
and backward. At the canonical configuration the linear layer is
`diag(1, …, 1, t)`, so the backward composition over `L − ℓ` layers is
`diag(1, …, 1, t^(L−ℓ))` exactly and the dead diagonal of the backward second
moment carries `t^(2(L−ℓ))`. Positive homogeneity collapses the ReLU chain
exactly to `t^L·ReLU(x)`, and the second moment under the standard Gaussian is
`t^(2L)/2`, with the shared-gate survival probability `1/2` as an exact
constant. For the smooth class a polynomial envelope, proved by induction on
depth, keeps the compounded activation remainders one order below the leading
term, so the `L`-layer chain has leading rate `2L` with coefficient `c^(2L)`.
The two-channel base is exact for ReLU (the dead moment sits strictly below the
live moment at every `t < s`) and eventual for the smooth class. Mixing
configurations are covered at the `σ_min` level: `sigmaMinSq_mul_le` with
`le_sigmaMinSq_mul` squeezes a product two-sided, so a live mixing layer moves
the constant and never the exponent. The ordered spectrum enters through the
spectral theorem. `eigenvalue_count_of_block_bounds` counts exactly `m`
eigenvalues at most `a` and `h − m` at least `c` by dimension counting on
eigenvector spans, so the proof calls on no minimax theorem, and
`singular_value_count_of_block_bounds` is its singular-value reading. The MSE
base case is derived, not assumed: `mse_base_case` computes the squared
residual of the dead output against an independent Gaussian noise target as
`c² + v`, and `mse_bridge_composed` reads the dead `G`-entry at depth `ℓ` as
`t^(2(L−ℓ))·(c² + v)` exactly.

**Lean.** `mse_bridge_composed`, `eigenvalue_count_of_block_bounds`,
`quadform_eigen`, `eigSpan`, `gram_quadform`,
`singular_value_count_of_block_bounds`, `relu_chain_eq`, `relu_channel_moment`,
`relu_channel_hasLeadingRate`, `smooth_channel_hasLeadingRate`,
`smoothChain_abs_le`, `smoothChain_sub_le`, `smooth_chain_hasLeadingRate`,
`smooth_chain_slope`, `canonicalLayer_pow`, `deep_linear_backward_rate`,
`canonicalLayer_pow_mulVec_ne`, `deep_linear_hasLeadingRate`,
`deep_linear_dead_entry_eventually_le`, `relu_two_channel_dead_lt_live`,
`smooth_two_channel_dead_eventually_lt`.

**Inputs.** The canonical-aligned configuration; the (P2) class is defined by
the global quadratic Taylor bound `|φ(u) − c·u| ≤ K·u²`; the two-channel model
keeps the channels decoupled. The ledger records nothing missing at model
scope.

**Depends on.** `thm:fisher_decay` (rate calculus and the score-to-Fisher
expansion), `cor:bridge_g2` (the spectrum-count machinery in `SpectrumCount`).

### cor:a_g_duality (full)

**Proved.** The forward and backward rates multiply to the paper's product in
all three classes. For (P1) and (P3) the product is exact: the deep-linear
forward rate times the backward rate gives `deep_linear_ag_product`, and the
ReLU chain's certified derivative gives `relu_channel_ag_product`. For (P2) the
class is defined by a Taylor bound, so the product holds at leading order,
which is the strongest form available for that class.

**Lean.** `deep_linear_forward_rate`, `deep_linear_ag_product`,
`relu_chain_hasDerivAt`, `relu_backward_hasDerivAt`,
`relu_channel_backward_moment`, `relu_channel_ag_product`,
`hasDerivAt_smoothChain`, `backDeriv_sub_le`,
`smooth_chain_backward_hasLeadingRate`, `smooth_chain_ag_product`,
`HasLeadingRate.mul`.

**Inputs.** The backpropagation gate convention `ReLU'(0) = 0` enters at the
single point `x = 0`; off it the gate reading is the derivative in the
`HasDerivAt` sense. For (P2) the Taylor bound defines the class, so no exact
product form exists there.

**Depends on.** `thm:bridge` (the channel chains it multiplies),
`thm:fisher_decay` (the rate calculus and `HasLeadingRate.mul`).

### prop:swiglu_rate (full)

**Proved.** At the stated canonical diagonal initialization the dead-dimension
output of a SwiGLU block is exactly the scalar channel `t³·x²·σ(t·x)`. The
pointwise expansion is `(1/2)·t³·x²` with an explicit global `O(t⁴)`
remainder that holds at every `t` and every input. The
moment rate is 6 with coefficient `E[x⁴]/4`, and the composition remark's
`3(2ⁿ − 1)` recursion is machine-checked.

**Lean.** `sigmoid`, `abs_sigmoid_sub_half`, `swigluDead_eq`,
`swigluDead_sub_le`, `swiglu_channel_hasLeadingRate`, `quadBlock_iterate`.

**Inputs.** The scalar dead channel at the stated diagonal initialization,
which carries the proposition's content there. Mathlib has no Gaussian moment
formulas, so the coefficient is written as the fourth-moment integral rather
than as the number 3.

**Depends on.** `thm:fisher_decay`.

### thm:bridge_bias (partial)

**Proved.** For (P1) the biased chain's linear part is exactly the weight
product, so the backward ladder never sees the biases, which is clauses (a) and
(c). The dead coordinate has a closed form, and the forward moment at `q ≡ 1`
is capped at rate 2 with coefficient exactly 1 at every depth `m ≥ 2`. For (P3)
a positive dead bias opens every deep gate: the derivative is exactly `t^m` for
any non-negative activation, the full-chain derivative carries the single
layer-1 gate `1_{x > −1}`, and its mass strictly exceeds the bias-free `1/2`.
The (P2) correction is the Lipschitz gate bound `bias_taylor_correction`: a
`K`-Lipschitz gate derivative moves by at most `K·|t|·|x|` at the biased
pre-activation.

**Lean.** `bias_taylor_correction`, `affChain_sub`, `affChain_dead_eq`,
`affChain_dead_uniform`, `aff_forward_cap`, `biasedChain_deriv_of_nonneg`,
`biasedChain_deriv`, `biased_backward_moment`, `biased_gate_mass_gt_half`.

**Inputs.** The scalar dead-channel models at the symmetric joint case
`q ≡ 1`. The cross-entropy base case is `ce_dead_lower`, read at the biased
chain's dead coordinate. Nothing missing at model scope.

**Depends on.** `thm:fisher_decay`, `thm:bridge_ce` (for `ce_dead_lower`).

### thm:bridge_rect (partial)

**Proved.** The narrow chain is self-contained against arbitrary complement
maps, linear or not, of depth-varying width, which is stronger than the paper's
linear complements: the ladder `t^m`, the `Θ(1)` base, and the width-independent
backward moment `t^(2m)`. The complement-leak clause (c) is closed at the leak
model: a first-order leak `γ·c` drops the squared-output rate to 2 with
coefficient `(γc)²` (`leak_kl_rate`), the invariant complement keeps rate 4
(`invariant_kl_rate`), and `leak_not_dead` records that `2 ≠ 2k` for every
`k ≥ 2`, so the leaked direction is not dead at any depth.

**Lean.** `bias_taylor_correction`, `rectLayer`, `rectChain_fst`,
`rect_dead_ladder`, `rect_nondead_invariant`, `rect_backward_rate`.

**Inputs.** The coordinate-aligned model. The general composed-complement case
is the distance-to-image bound on the `cor:rect_product_sigma_min` row. The
activation-class corrections at rectangular widths are the same Lipschitz gate
bound, which carries no width dependence. Nothing missing at model scope.

**Depends on.** `thm:bridge` (the canonical chain), `thm:bridge_bias` (the
Lipschitz gate correction).

### thm:bridge_multi (partial)

**Proved.** Clauses (a), (b), and (d) are exact on the diagonal
multi-direction model, with the joint dead-block congruence carried through the
cross moments (`multi_backward_cross`). The layer product reduces to the
canonical form (`multiProd_eq_diagonal`, `multiLayer_eq_canonical`), and the
dead entry eventually falls below every live entry.

**Lean.** `spectrum_count_form`, `multiLayer`, `multiProd_eq_diagonal`,
`multi_backward_rate`, `multi_backward_cross`, `multi_backward_hasLeadingRate`,
`multi_dead_entry_eventually_le`, `multiLayer_eq_canonical`.

**Inputs.** The diagonal multi-direction model. The spectrum clause (c) is
`spectrum_count_form`, carried on the `cor:bridge_g2` row, and the
cross-entropy logit-shift zero mode is `ce_gauge_kernel` on the
`thm:bridge_ce` row, which removes one dead eigenvalue from the count. Nothing
missing at model scope.

**Depends on.** `thm:fisher_decay`, `cor:bridge_g2`, `cor:bridge_g3`.

### cor:bridge_g2 (partial)

**Proved.** At the uniform symmetric approach every dead direction reads the
shared rate `2(L − ℓ)`. The spectrum-count form is machine-checked: with a dead
subspace of dimension `m` carrying the quadratic form at most `a·‖v‖²` and a
live complement of dimension `h − m` carrying at least `c·‖v‖²` with `a < c`,
every subspace carrying at most `a·‖v‖²` has dimension at most `m`, and the
dead subspace attains `m`.

**Lean.** `small_subspace_dim_le`, `spectrum_count_form`, `cumExp_uniform`,
`multi_backward_hasLeadingRate`.

**Inputs.** The uniform symmetric approach and the diagonal model. Nothing
missing at model scope.

**Depends on.** `thm:bridge_multi` (the backward rates the count is applied
to), `cor:bridge_g3` (the cumulative exponent), `thm:fisher_decay`.

### cor:bridge_g3 (full)

**Proved.** The layer-varying single-direction rate is `2·Σ_{ℓ′>ℓ} p_{ℓ′}`,
with the exponent a sum over the layers above `ℓ` only. The restriction is
visible in the definition of the cumulative exponent `cumExp` itself.

**Lean.** `cumExp`, `multi_backward_hasLeadingRate`.

**Inputs.** The diagonal model of the layer stack.

**Depends on.** `thm:bridge_multi`, `thm:fisher_decay`.

### cor:bridge_g7 (partial)

**Proved.** Per-direction distinct rates hold as entries, together with the
joint block scaling through the cross moments.

**Lean.** `spectrum_count_form`, `multi_backward_rate`, `multi_backward_cross`,
`multi_dead_entry_eventually_le`.

**Inputs.** The diagonal model. The spectrum reading under non-dead-block
control is `spectrum_count_form` on the `cor:bridge_g2` row. Nothing missing at
model scope.

**Depends on.** `cor:bridge_g2`, `cor:bridge_g3`, `thm:bridge_multi`.

### prop:bridge_linear_rot (full)

**Proved.** The proposition closes without the singular value decomposition
milestone the attack queue had reserved for it. Its statement is the
`U`-conjugated configuration, and orthogonality `UᵀU = 1` telescopes the
rotated pairing back to the canonical dead coordinate of the rotated gradient.
The backward moment carries `t^(2m)` exactly at every orthogonal `U`, so
rotation is without loss of generality for class (P1) at model level.

**Lean.** `rotated_pairing`, `rotated_backward_rate`, `rotated_hasLeadingRate`.

**Inputs.** The conjugated model. General non-conjugated configurations wait on
the singular value decomposition.

**Depends on.** `thm:fisher_decay`.

### prop:bridge_nonlinear_rot_negative (partial)

**Proved.** The paper presents this as an empirical demonstration with a
mechanism sketch; the mechanism is now proved exactly at a planar witness. At
the 3-4-5 rotation the pre-activation at the dead-probe input is `t·u` with
opposite-sign coordinates, so the ReLU mask is exactly `(0, 1)` for every
`t > 0`, the masked dead direction carries live overlap `12/25`, and the dead
reading of a live backward flow has leading rate 0 with coefficient `12c/25`.
Masks scale canonical directions in place, so a canonical reading keeps its
rate `K` and the two exponents differ at every `K ≥ 1`. The window question the
paper left open is closed at the model level: the leak amplitude is `γ·s·c`,
linear in the rotation sine, the two-sided slope bounds hold at margin `δ`, the
half-maximum crossover sits at `b·t^(2K) = (γsc)²`, so the crossover scale is
`Θ(s^(1/K))`, and `crossover_scale_closed_form` solves the crossover equation
exactly at `t_× = (c₀/b)^(1/m)`. The constants are derived at a two-chain
model: `γ` is the live route's chain coefficient and `b` the square of the dead
route's.

**Lean.** `rotU`, `reluDeriv`, `witness_mask`, `masked_dead_live_overlap`,
`canonical_mask_in_line`, `deadRead`, `rotated_rate_collapse`,
`canonical_reading_rate`, `rotated_canonical_rates_differ`.

**Inputs.** The planar witness architecture and the two-chain model for the
constants. Missing at network scope: the derivation beyond the chain model,
where the mask couples the routes of a general architecture.

**Depends on.** `thm:fisher_decay` (rate calculus, and the real-exponent
calculus in `RpowRate`).

### cor:bridge_near_canonical (partial)

**Proved.** The paper states this as an open problem and constrains the shape
of the answer; the model carries that shape exactly. The perturbed observable
`t^(2k) + ε²t²` has leading rate 2 with coefficient `ε²` at fixed `ε`, leading
rate `2k` at `ε = 0`, and the two iterated limits disagree for every `k ≥ 2`.

**Lean.** `near_canonical_rate_perturbed`, `near_canonical_rate_zero`,
`near_canonical_rates_differ`.

**Inputs.** The scalar perturbed observable. Missing: the network-level
constants. The quantitative window that governs which of the two limits a
finite measurement sees is the rotation row's window bound.

**Depends on.** `thm:fisher_decay`,
`prop:bridge_nonlinear_rot_negative` (the window and crossover calculus).

### thm:bridge_ce (partial)

**Proved.** The output-head lemma is complete. The softmax Hessian
`H = diag(p) − p pᵀ` has quadratic form equal to the variance of `v` under `p`,
vanishing exactly on the constant directions and positive definite on their
orthogonal complement. The base case (b) reads `c₀(1 − 1/C)`. Clause (c) closes
in the diagonal model: the pulled-back covariance `Jᵀ H̄ J` kills the explicit
gauge vector `(t^p, …, t^p, 1)` at every `t`, and that vector converges to the
dead basis vector at the boundary. The linear-class composition is one
statement, `ce_bridge_composed`: the dead `G`-entry at depth `ℓ` is at least
`c₀(1 − 1/C)·t^(2(L−ℓ))`. The nonlinear-channel composition runs the gated
chain on the head base case, giving at least `(∏c)²·q·c₀(1 − 1/C)·t^(2Σk)`.

**Lean.** `head_dead_axis_eq_moment`, `ce_gated_chain_lower`,
`ce_gated_chain_lower_of_indep`, `ceHess_expect`, `ceHess_mulVec_one`,
`ceHess_one_vecMul`, `ceHess_quadform`, `ceHess_quadform_eq_var`,
`ceHess_quadform_eq_zero_iff`, `ceHess_posdef_on_perp`, `ce_dead_lower`,
`ce_gauge_kernel`, `ce_gauge_eigen_limit`, `ce_bridge_composed`.

**Inputs.** The gated chain runs under one joint gate-and-gradient hypothesis,
`q·E[δ_h²] ≤ E[g·δ_h²]`, which `ce_gated_chain_lower_of_indep` discharges under
independence of gate and gradient with `q` the survival probability. The
backward recursion of clauses (a) and (d) is loss-independent and lives in the
channel modules. Nothing missing at model scope.

**Depends on.** `thm:bridge` (the backward chain it composes with),
`thm:bridge_composition` (the composed-signal integral).

### thm:bridge_composition (partial)

**Proved.** Clauses (a) and (b) hold in the gated-scalar model: the composed
second moment is exactly `(∏ cᵢ)²·t^(2Σkᵢ)·E[g·X²]`, so a chain's rate is the
sum of its per-block rates, and concatenating two chains adds the rates and
multiplies the coefficients. Every exclusion clause is sharp as a model
theorem. Disjoint gates kill the composed moment identically. A quadratic dead
map compounds the arriving order to `k + 2e`, which differs from the additive
`k + e` at every `e ≥ 1`. A fixed-order injection below the arriving order caps
the composed rate at `2·cap` with the injection coefficient, the LayerNorm
reset.

**Lean.** `composedSignal_eq`, `composedSignal_sq_integral`,
`composedSignal_hasLeadingRate`, `composedSignal_forward_hasLeadingRate`,
`chainRate_append`, `chainCoeff_append`, `disjoint_gates_moment_zero`,
`quad_block_compounds`, `quad_rate_ne_additive`, `leak_caps_rate`,
`leak_cap_ne_additive`.

**Inputs.** The scalar, linear, jointly gated transfer model with one shared
indicator gate for the chain. Nothing missing at model scope; deriving
per-block rates from an architecture is the other bridge theorems' subject.

**Depends on.** `thm:fisher_decay`.

### cor:composition_heterogeneous (full)

**Proved.** Uniform rate-2 blocks compose at moment rate `4n` on the model,
which is the `α = 4(L − ℓ)` profile the corollary predicts.

**Lean.** `chainRate_replicate`, `composition_rate_two_hasLeadingRate`.

**Inputs.** The gated-scalar model. The corollary's remaining content is
empirical validation, which the Lean does not address.

**Depends on.** `thm:bridge_composition`, `thm:fisher_decay`.

### cor:composition_reduces (full)

**Proved.** All three clauses hold at model level: unit matmuls read the ladder
`2n`, rate-0 residual blocks leave the moment free of `t` at every `t`, and a
block chain carries the same rate and coefficient as its flattened weight
chain.

**Lean.** `composition_matmul_hasLeadingRate`, `composition_residual_const`,
`chainRate_flatMap`, `chainCoeff_flatMap`.

**Inputs.** The gated-scalar model.

**Depends on.** `thm:bridge_composition`, `cor:composition_heterogeneous`,
`thm:fisher_decay`.

### cor:composition_reduces_sub (full)

**Proved.** The same model evaluations as `cor:composition_reduces`, restated
under the sub-chain index convention.

**Lean.** `composition_matmul_hasLeadingRate`, `composition_residual_const`.

**Inputs.** The gated-scalar model and the sub-chain indexing.

**Depends on.** `thm:bridge_composition`, `cor:composition_heterogeneous`,
`thm:fisher_decay`.

---

## Attention

Attention enters the package as a genuine softmax, first as a logistic on the
score gap at two positions and then as the `N`-position row with a certified
directional Jacobian. The route inventory (the value-output route against the
score route) is built from the network graph conditional on the attention
pattern, and the paper's generic non-cancellation hypothesis is upgraded to an
almost-everywhere theorem.

### thm:bridge_attn (partial)

**Proved.** In the two-position model the softmax is present as a logistic on
the score gap: the bilinear QK dead entry carries two `t`-factors, the
attention weight moves continuously in `t²`, and the dead output is `t²` times
the `A₀`-weighted average, the forward block rate 2 with the theorem's
coefficient. The `N`-position upgrade is in: `softmaxN` with positivity,
sum-one, and continuity, and `bridge_attn_forward_N` gives the forward rate 2
with the `A₀`-weighted coefficient through the true softmax row. The
almost-sure non-degeneracy of the weighted average is `hyperplane_null`: the
zero set of a nonzero reading is Haar-null. The quantitative operating-point
bound is exact and derivative-free: a perturbation bounded by `ε` moves every
softmax entry by a factor in `[e^(−2ε), e^(2ε)]`.

**Lean.** `logistic`, `score_bilinear`, `attnA`, `attnDeadOut`,
`bridge_attn_forward`.

**Inputs.** The two-position model for the headline statement, with the
`N`-position statement carried by `bridge_attn_forward_N`. The ledger records
nothing remaining at model scope.

**Depends on.** `thm:fisher_decay`, `prop:attn_chain_softmax` (the softmax
Jacobian and the route inventory).

### thm:bridge_attn_backward (partial)

**Proved.** The two-route composite is machine-checked at model level: each
route carries two `t`-factors with a factor continuous at zero, and the
composite has rate 2 with coefficient the sum of the two route coefficients.
The statement is informative exactly under the theorem's generic
non-cancellation condition, and the measure-zero argument for cancellation sits
on the `prop:attn_chain_softmax` row.

**Lean.** `attnBackDead`, `bridge_attn_backward`, `hasLeadingRate_pow_factor`.

**Inputs.** The two-route model, with the routes derived from the network graph
conditional on the attention pattern. Nothing missing at model scope.

**Depends on.** `thm:fisher_decay`, `prop:attn_chain_softmax`.

### prop:attn_chain_softmax (partial)

**Proved.** The two-route minimum mechanism holds at rate level: when two
routes reach one component, the smaller rate carries the sum, and tied rates
add coefficients. The softmax Jacobian analysis is certified:
`softmaxN_hasDerivAt_dir` derives the `diag(a) − a aᵀ` action as a directional
derivative, `softmaxN_jacobian_const` is the shift gauge zero, and
`softmaxN_uniform_jacobian` is the sequence-space projector at uniform scores.
The route inventory is composed from per-block products, and
`route_moment_vo_wins`, `route_moment_tie`, `route_moment_floor_wins` give the
full `min(4k, 4p+8)` trichotomy with coefficients `a²`, `(a+b)²`, `b²`, the tie
sitting at the paper's profile peak. The amplitudes are derived conditional on
the attention pattern: `chainA` composes the stack as a list product with
continuity, row-stochasticity, and non-negative entries, and `voAmp_floor`
makes value-output non-degeneracy unconditional on the positive cone. The
paper's non-cancellation hypothesis is now mostly theorem:
`route_noncancellation_witness` is unconditional at constant score directions,
`analytic_zero_set_null` with `route_noncancellation_ae` confines cancellation
to a Lebesgue-null parameter set along any analytic one-parameter family
through a witness, and `route_noncancellation_ae_concrete` states the
almost-everywhere reading with no analyticity hypothesis left. The
several-parameter version runs through `analytic_zero_set_null_pi`, a Fubini
induction over the first coordinate.

**Lean.** `HasLeadingRate.add_of_lt`, `HasLeadingRate.add_of_eq`,
`hasLeadingRate_pow`.

**Inputs.** The route model, with the amplitudes conditional on the attention
pattern. Nothing remains at model scope.

**Depends on.** `thm:fisher_decay`, `thm:bridge_attn` (the module `AttnRoutes`
builds on `AttnBridge`).

### prop:attn_VO_invariant (partial)

**Proved.** The operational invariant is exact: one extra Linear shifts the
moment rate by exactly 2 and leaves the coefficient untouched. The `A₀`
comparison is closed deterministically, hence under every expectation:
`mixing_theta_comparison` sandwiches the squared reading between `σ_min²` and
`σ_max²` of `A₀ᵀ` times the squared input, and `sigmaMinSq_pos_of_unit` makes
the lower constant positive at every invertible `A₀`.

**Lean.** `HasLeadingRate.extra_linear`.

**Inputs.** The gated-scalar model, and invertibility of `A₀` for the positive
lower constant.

**Depends on.** `thm:fisher_decay`.

### cor:g10_composition (full)

**Proved.** The additive reading holds at model level, and the scope caveat is
arithmetic on the two routes: the additive `4k` is the smaller route exactly
where `k ≤ p + 2`, and the score-path floor `4p + 8` takes over beyond it.

**Lean.** `composition_rate_two_hasLeadingRate`, `g10_anomaly_scope`.

**Inputs.** The gated-scalar model, with the route trichotomy carried on the
`prop:attn_chain_softmax` row.

**Depends on.** `thm:bridge_composition`, `cor:composition_heterogeneous`,
`prop:attn_chain_softmax`, `thm:fisher_decay`.

### cor:g10_via_composition (partial)

**Proved.** The residual reading: rate-0 blocks keep the stream free of `t`.

**Lean.** `composition_residual_const`.

**Inputs.** The gated-scalar model. The attention non-transfer clause is the
model's own exclusion, stated on the `thm:bridge_composition` row.

**Depends on.** `thm:bridge_composition`, `cor:composition_reduces`.

---

## Residual and DAG

The residual rows replace layer counting with a shortest-path distance. A
weight edge costs one unit, a skip edge is free, and the backward delta at a
node carries leading rate equal to the Bellman distance to that node.

### thm:bridge_res (partial)

**Proved.** The segment model is exact: weight edges transfer `c·t` at cost
one, residual blocks transfer `1 + c·t^k` at cost zero, and the composed
squared transfer carries leading rate `2·K` with `K` the total weighted path
cost. The DAG framework generalizes it. With `K` the Bellman shortest-weighted-path
distance and `T` the backward delta obeying the matching recursion,
`dag_backward_rate` gives `T(m)` leading rate exactly `K(m)` with a positive
coefficient, and `dag_backward_moment_rate` the dead moment at rate `2K(m)`.
Multi-path interference is explicit: a sum of rates carries the minimum, ties
add coefficients, and positivity forbids cancellation. The nonlinear gating
clause holds with a shared survival gate on every weight edge, since every path
to a node of positive distance crosses a weight edge, so the gated delta is `g`
times the ungated one and the moment scales by the survival probability. The
explicit Schur constant is in: `dag_backward_coeff` gives the coefficient as
the shortest-path recursion itself, and `dag_coeff_pos` makes it positive by
uniqueness of leading coefficients.

**Lean.** `HasLeadingRate.add_min`, `hasLeadingRate_finset_sum_pos`,
`dag_backward_rate`, `dag_backward_moment_rate`, `dag_no_skip_K`,
`dag_full_skip_K`, `dag_skiponly_zero_iff`, `dag_gated_eq`,
`gated_moment_factor`, `HasLeadingRate.add_min_coeff`,
`hasLeadingRate_finset_sum`, `dag_backward_coeff`, `dag_coeff_pos`,
`ResSeg.transfer`, `seg_sq_hasLeadingRate`, `chainTransfer_sq_hasLeadingRate`.

**Inputs.** The scalar segment model on a chain, and the DAG in Bellman form
with the backward delta obeying the matching recursion with positive weight
coefficients. Nothing missing at model scope.

**Depends on.** `thm:fisher_decay`.

### cor:res_all (full)

**Proved.** With every layer wrapped in a residual connection the cost is zero
at every depth, so the composed moment is `Θ(1)` with rate 0 and coefficient 1.

**Lean.** `res_all_hasLeadingRate`.

**Inputs.** The segment model.

**Depends on.** `thm:bridge_res`, `thm:fisher_decay`.

### cor:res_ff (full)

**Proved.** With no residual edges the cost equals the depth and the ladder
rate `2(L − ℓ)` returns.

**Lean.** `res_ff_kdist`, `chainTransfer_sq_hasLeadingRate`.

**Inputs.** The segment model.

**Depends on.** `thm:bridge_res`, `thm:fisher_decay`.

### cor:res_block (partial)

**Proved.** The skip-saves-`k` accounting is exact: a residual block
contributes nothing to the cost, so `K = a + b` whatever `k` it spans, and all
three cut positions reduce to computed segment lists. The finite-`t` skip
correction is in on the DAG: below `t = 1` the backward delta sits within
`R·t^(K+1)` of its leading term, with `R` explicit from the parents, since
longer paths through unused skips and non-shortest parent chains enter one
order higher.

**Lean.** `res_block_kdist`, `dag_K_succ_le`, `dag_K_le_skip`,
`dag_backward_remainder`.

**Inputs.** The segment model and the DAG distance facts. Nothing missing at
model scope.

**Depends on.** `thm:bridge_res`.

### cor:res_lambda_min (partial)

**Proved.** In the diagonal model, with positive path cost the dead entry of
the residual `G`-model tends to zero, the live entries hold a positive floor,
and eventually the dead entry is the variational minimum of the form. Beyond
diagonality the Schur argument closes it: the cross moments cost at most
`‖b‖²/c` and the rate survives by `HasLeadingRate.sub_of_lt`. The
complement-zero caveat is machine-checked as its own statement: a null
direction of the live complement, whether a gauge zero or tied shortest paths
with linearly dependent products, zeroes the whole block form, so the
variational minimum reads zero whatever the dead entry does.

**Lean.** `diag_lambda_min_slice_general`, `resGModel`, `res_lambda_min_slice`,
`complement_zero_caveat`.

**Inputs.** The diagonal residual `G`-model for the slice, and a positive live
floor for the Schur step. Nothing missing at model scope.

**Depends on.** `thm:bridge_res`, `cor:rect_lambda_min` (the shared
`schur_dead_lower`).

### cor:sigma-min-res (partial)

**Proved.** Depth invariance is exact at both levels. Per sample, a residual
step with non-negative stream-branch pairing does not shrink the sum of squares,
and the floor telescopes along the trajectory. At the operator level `σ_min²`
is supermultiplicative, a block `1 + B` with positive-semidefinite pairing has
`σ_min² ≥ 1`, and the chain keeps `σ_min² ≥ 1` at every depth.

**Lean.** `residual_sq_sum_ge`, `residual_chain_sq_sum_ge`,
`one_le_sigmaMinSq_one_add`, `le_sigmaMinSq_mul`, `one_le_sigmaMinSq_resChain`.

**Inputs.** Linear residual blocks with the positive-semidefinite pairing as
the no-cancellation hypothesis. Nothing missing at model scope.

**Depends on.** `thm:bridge_res`.

### cor:sigma-min-res-all (partial)

**Proved.** The forward cost is zero everywhere at model level: the
all-residual chain's moment is `Θ(1)` with rate 0 and coefficient 1, and the
operator chain keeps `σ_min² ≥ 1` at every depth.

**Lean.** `res_all_hasLeadingRate`, `one_le_sigmaMinSq_resChain`.

**Inputs.** The segment and operator models. The sample-matrix form follows
from the `cor:sigma-min` sample clauses, which carry a population floor to the
sample matrix with the factor `N`.

**Depends on.** `cor:res_all`, `cor:sigma-min-res`, `cor:sigma-min`,
`thm:fisher_decay`.

### cor:sigma_min_res_g5 (partial)

**Proved.** The forward cost rate holds at model level (the segment model reads
forward identically), together with the diagonal-Gram `λ_min` slice. The
sharpness of `φ′(0) > 0` is exact: two tied routes compose to coefficient
`(c₁ + c₂)²`, which vanishes exactly at `c₂ = −c₁`, so a negative slope cancels
a tie and the rate jumps. The post-LayerNorm exclusion is machine-checked as
`post_ln_sample_kernel`: on any sample the centred LayerNorm outputs pair to
zero with `γ⁻¹` row by row, so the centred sample Gram form vanishes at `γ⁻¹`
and `σ_min(LN(X)) = 0` identically at post-LayerNorm nodes.

**Lean.** `chainTransfer_sq_hasLeadingRate`, `tied_routes_coeff`,
`multi_lambda_min_slice`, `post_ln_sample_kernel`.

**Inputs.** The segment and diagonal models; the sample matrix is covered by
the `cor:sigma-min` sample clauses and the nonlinear gating by `dag_gated_eq`
on the `thm:bridge_res` row. Nothing missing at model scope.

**Depends on.** `thm:bridge_res`, `thm:bridge_multi`, `prop:ln_kernel`,
`cor:sigma-min`, `thm:fisher_decay`.

---

## LayerNorm

Four rows read LayerNorm from three sides: the exact kernel direction of the
output covariance, the negative result that RMSNorm has no such direction, the
bracket on the backward rate, and the finite-`t` regime structure of the MLP
block.

### prop:ln_kernel (full)

**Proved.** Part (a) is complete and generalized beyond the paper's statement
to any scalar normaliser: a coefficient vector whose pairing with the output is
almost surely constant lies in the kernel of the covariance, the `γ⁻¹` pairing
of the LayerNorm output takes the same value at every input, and both clauses
(i) and (ii) follow, including at the exact normaliser `s(x) = √d/‖Px‖`. Part
(b) is in witness form, which is the proposition's content: on the admissible
input with uniform mass on the `2d` points `±eᵢ`, whose input covariance is
`I/d` and certified positive definite, every candidate direction `v ≠ 0` reads
RMSNorm with variance exactly `Σᵢ (vᵢγᵢ)² > 0` for any `γ` without zero
coordinates, so no direction built from `γ` is a universal kernel vector.

**Lean.** `covMatrix_vecMul_eq_zero_of_sum_const`, `sum_ginv_mul_lnLike`,
`covMatrix_lnLike_ginv_eq_zero`, `covMatrix_lnLike_zero_coord`,
`covMatrix_layerNorm_ginv_eq_zero`, `rmsNorm`, `rmsnorm_no_kernel`,
`rmsnorm_witness_input_posdef`.

**Inputs.** Each output coordinate and each centred product is integrable, so
the covariance exists. The Lean identity is pointwise and total, so the paper's
hypothesis that `X` puts no mass on `span(𝟙_d)` drops.

**Depends on.** `prop:rmsnorm_no_kernel` (part (b) is the RMSNorm witness).

### prop:rmsnorm_no_kernel (full)

**Proved.** One admissible witness defeats every candidate at once. Uniform
mass on the `2d` points `±eᵢ` has input covariance `I/d`, certified positive
definite, and every reading `v ≠ 0` of RMSNorm on it carries variance exactly
`Σᵢ (vᵢγᵢ)²`. This is stronger than the paper's per-direction Gaussian argument
and elementary: the distribution enters as explicit finite-support weights, so
every expectation is a finite sum.

**Lean.** `rmsNorm`, `rmsNorm_reading_single`, `rmsnorm_no_kernel`,
`rmsnorm_witness_input_posdef`.

**Inputs.** The finite-support witness distribution, and `γ` without zero
coordinates. The proof consumes no measure theory.

**Depends on.** Nothing.

### thm:bridge_ln (partial)

**Proved.** Both ends of the bracket are realised on the scalar model. The
normalizer's scale invariance erases upstream decay, so a decayed channel
returns to unit moment and the composed moment is `t^(2·k_post)` exactly, the
end that every measured configuration saturates. The no-crossing channel reads
the full `2(k_pre + k_post)`.

**Lean.** `normalizeS_scale`, `ln_reset_moment`, `ln_bracket_plateau`,
`ln_bracket_no_crossing`.

**Inputs.** The scalar normalizer model. Missing per the ledger: the bracket
inequality on the full LayerNorm backward Jacobian.

**Depends on.** Nothing.

*Note.* `LnJacobian.lean` (2026-08-22) carries the LayerNorm backward
Jacobian as a certified directional derivative together with the split of its
dead component into a passing term and a leak term; the ledger row cites
`znorm_hasDerivAt_dir`, `lnJac_mulVec`, `ln_jacobian_dead_component`,
`ln_jacobian_dead_passes`, and `ln_jacobian_leak`, and the row stays `partial`
because the bracket inequality itself is the paper's own open item.

### thm:ln_finite_t_mlp (partial)

**Proved.** The regime structure sits on the three-term expansion
`G(t) = c₀ + c₂t² + c₄t⁴`, with the derivative certified and the log-slope's
rational form derived: `α` tends to 0 at a positive noise floor, to 2 on the
`t²` plateau, and equals 4 exactly on the direct rate. The almost-sure bound on
the `t²` prefactor is exact (`σ₀²` dominates its own mean-square term
pointwise, so the ratio caps at `d²/(d−1)`), as is the rate-shift contrast:
rate 2 with the leak against rate 4 without. The leak mechanism is pointwise
exact, with the `O(1)` amplitude `−x̄_d/σ₀` at `t = 0` and the dead output
`t·z_h(t)` having derivative `z_h(0)` at the singularity. Cochran's theorem is
derived through the route behind its proof: `rotBasis` is the orthonormal basis
whose first vector is `𝟙/√m`, the statistic reads `y₀²/d² + d⁻¹Σ_{j≥1} y_j²` in
those coordinates, the isotropic Gaussian is the product Gaussian in any
orthonormal coordinates, and `ln_sigma0_inv_moment_lt_top_iff` states
`E[1/σ₀²] < ∞ ⟺ d ≥ 4` with no hypothesis left. The Laplace side supplies the
analytic half: the Gamma density tilts to a shifted rate, the reciprocal moment
of `Gamma(a, r)` is `r/(a−1)` for `a > 1`, the reciprocal moment of any positive
variable is the Lebesgue integral of its Laplace transform over `(0, ∞)`, and
the product integrand of two Gamma pieces is integrable exactly when the shapes
sum above one, which with the Cochran shapes `(d−2)/2` and `1/2` reads `d ≥ 4`.
The `t⁴` coefficient is pointwise exact through the exact quadratic form of the
LayerNorm variance, and `ln_moment_assembled` reads the residual moment as
`v + t²E[p₀] + t³E[p₁] + t⁴E[p₂]` up to `R·|t|⁵`, with `E[p₁] = 0` by sign
symmetry.

**Lean.** `gammaPDFReal_mul_exp`, `integral_exp_neg_mul_gammaMeasure`,
`integral_inv_gammaMeasure`, `lintegral_inv_eq_lintegral_laplace`,
`laplace_product_integrableOn_iff`, `ln_sigma0_shape_criterion`,
`laplace_indep_gamma_pair`, `gamma_laplace_factor_eq`,
`inv_moment_gamma_pair_lt_top_iff`, `lnZ_zero`, `leak_amplitude_normalised`,
`ln_leak_derivative`, `integral_exp_neg_mul_sq_gaussianReal`,
`laplace_weighted_sq_pi`, `rotSigma`, `inv_moment_rotSigma_lt_top_iff`,
`sigma0`, `sigma0_eq_paper_form`, `rotBasis_zero`, `sigma0_eq_rotSigma`,
`ln_sigma0_inv_moment_lt_top_iff`, `lnVar_eq_quadratic`, `lnP2`,
`lnZ_sq_expansion`, `lnP1_odd`, `lnZ_sq_remainder_bounded`,
`residual_moment_product`, `ln_moment_assembled`, `lnG`, `lnG_hasDerivAt`,
`alphaSlope`, `alphaSlope_eq`, `noise_floor_regime`, `t2_plateau_regime`,
`direct_rate_regime`, `leak_prefactor_bounded`, `ln_leak_rate`,
`noln_direct_rate`.

**Inputs.** The scalar dead-channel model of the MLP block, integrable
coefficients, and an integrable remainder bound for the assembled moment
identity. Nothing missing at model scope.

**Depends on.** `thm:fisher_decay`,
`prop:bridge_nonlinear_rot_negative` (the crossover-scale closed form in
`RotNegative`), and the Gaussian layer in `GaussianLayer`.

---

## Volume and RLCT

These rows carry the Watanabe side of the bridge: sublevel-set volumes of
normal forms, the slope that reads the real log canonical threshold, and the
multi-component crossing laws where the multiplicity shows up as powers of
`log(1/ε)`.

### thm:selection_rule (partial)

**Proved.** Clause (c) is machine-checked on the slice normal form at
`m_perp = 0` and in general: the diagonal scaling carries the unit sublevel set
onto the `ε`-sublevel set, the volume is a power of `ε`, and the log-volume
slope reads the slice RLCT. Clauses (a) and (b) hold in a two-block model of
the Fisher matrix. `block_form_lower_weighted` absorbs the cross term by AM-GM
at weight `g` and Cauchy-Schwarz, and `block_lambda_min_sandwich` runs it on
the rate calculus, so an entry of rate `q` against a block of rate `p < q` with
cross entries at rate `p + q` and the Schur-type margin `2β/d < a` eventually
dominates `(g/2)‖v‖²`. The variational minimum then sits between `g/2` and the
axis value `g`, which is the entry's own rate. Clause (a) is the instance
`p = 0` against the `Θ(1)` live block, giving rate `2(k−1)`; clause (b) is the
instance `2j₁ < 2j₂` with the tangential entry keeping its own rate. The
eigenvector clause of (b) holds at the two-block model:
`two_by_two_eigvec_tilt` bounds the tilt of the eigenvector toward the first
axis by `|B|/(A − D)`, so as the cross entry vanishes the eigenvector converges
to the tangential axis. `selection_rule_assembled` assembles the rule from the
score side, consuming the three entry expansions in their proved forms.

**Lean.** `volume_sublevel_pow`, `tendsto_log_div_log_of_rpow`,
`slice_rlct_slope`, `normalForm_diagScale`, `sublevel_normalForm_eq_image`,
`volume_sublevel_normalForm`, `slice_rlct_product_slope`,
`block_form_lower_weighted`, `block_lambda_min_sandwich`,
`selection_rule_transversal_lower`, `selection_rule_tangential_lower`,
`block_form_dead_axis`, `two_by_two_eigvec_tilt`,
`hasLeadingRate_sq_of_expansion`, `hasLeadingRate_sum_same`,
`block_lambda_min_sandwich_ev`, `tangential_floor_eventually`,
`selection_rule_assembled`.

**Inputs.** Clause (c) runs on the slice normal form with no resolution of
singularities; tangential-normal coupling and the full local RLCT are not
formalized, which matches the theorem's own scope note. The assembly consumes
the graded margin `2k²Σ_α E[ab_α]²/(k²E[a²]) < λ/2`, which is hypothesis (ii*)
in the form the Schur argument uses. Nothing missing at model scope.

**Depends on.** `thm:fisher_decay`, `cor:fisher_structure`.

### thm:multi_component_rates (partial)

**Proved.** The exact volume laws and slopes hold at `r ≤ 3`, and the tied law
now holds at every multiplicity: the sublevel volume of the product on the open
unit cube is `δ·Σ_{j<r} (−log δ)^j / j!`, by a Fubini induction over the first
coordinate through the `piFinSuccAbove` equivalence with the one-dimensional
recursion. `volume_crossing_tied_general` carries it to the `(∏xᵢ)^(2k) < ε`
crossing form, and `crossing_tied_general_slope` squeezes the log-polynomial
factor between 1 and `r(1+x)^(r−1)`, so the estimator reads `λ = 1/(2k)` at
every `r`. The Jacobian exponent enters as a prior weight exactly as Watanabe's
formula says: the `x^h`-weighted slice volume is `ε^((h+1)/(2k))/(h+1)` with
slope `(h+1)/(2k)`, and the weighted law holds at every tied multiplicity as
`(h+1)^(−r)·P_r(δ^(h+1))`, carried onto the unweighted recursion by the
substitution `s = t^(h+1)`.

**Lean.** `volume_crossing_tied`, `crossing_tied_slope`,
`volume_power_hyperbola`, `volume_crossing_distinct`,
`crossing_distinct_slope`, `volume_crossing_tied3`, `logPoly_recursion`,
`volume_cubeHyper`, `volume_crossing_tied_general`,
`crossing_tied_general_slope`, `weighted_volume_sublevel_pow`,
`weighted_slice_rlct_slope`, `weighted_slice_recursion`, `weighted_unitCube`,
`weighted_volume_cubeHyper`.

**Inputs.** The normal-crossing form on the open unit cube. Nothing missing at
model scope.

**Depends on.** `thm:selection_rule` (the slice-RLCT slope machinery),
`prop:volume_multi` (the one-direction power integral).

### prop:volume_multi (partial)

**Proved.** The normal-form content is exact:
`V(ε) = ε^(Σᵢ 1/(2kᵢ) + m/2)·V(1)` with `0 < V(1) < ∞`, and the slope reads the
summed slice RLCT. The graded-Gram refinement is machine-checked at the model.
`polydisc_volume_factorised` integrates the factorised density
`u₁^(k₁−1)u₂^(k₂−1)` over the positive polydisc to the product of the
one-direction laws, `polydisc_volume_factorised_pi` does the same at every `r`,
and `polydisc_radius_pow` carries the radii to the exponents. The negative
control is exact and symbolic: the twisted map has `K = u₁⁴ + u₂⁴` exactly,
four certified partial derivatives, Jacobian determinant `4(u₁³ − u₂³)` through
the orthonormal polar frame, and pullback volume density `4|u₁³ − u₂³|`, whose
zero set `twisted_density_zero_iff` locates on the diagonal.
`twisted_vs_factorised` reads `M^(−5/2)` against
the factorised `M^(−2)` at `k = (2, 2)`.

**Lean.** `twisted_kl`, `twRho_hasDerivAt_fst`, `twMu0_hasDerivAt_fst`,
`twMu1_hasDerivAt_snd`, `twisted_jacobian_det`, `twisted_sqrt_det_fisher`,
`twisted_density_zero_iff`, `polydisc_volume_factorised_pi`,
`integral_pow_Ioo`, `polydisc_volume_factorised`, `polydisc_radius_pow`,
`twisted_polydisc_scaling`, `twisted_unit_constant_pos`,
`twisted_vs_factorised`, `normalFormMulti_diagScale`,
`sublevel_normalFormMulti_eq_image`, `volume_sublevel_normalFormMulti`,
`volume_multi_slope`.

**Inputs.** The additive normal form itself. Nothing missing at model scope.

**Depends on.** `thm:selection_rule` (the slice normal form and its slope
lemma).

### thm:nu_universality (partial)

**Proved.** The frozen-`Z` skeleton, in `NuFrozen` (2026-08-22). Under the
frozen posterior `exp(-η^{2k})` the statistic `T = η^{2k}` has the Gamma law
with shape `1/(2k)`, by the half-line substitution (`frozen_half_line`); its
mean is `1/(2k)` and the mean of `√T` is `Γ(λ+½)/Γ(λ)` (`frozen_mean_T`,
`frozen_mean_sqrtT`); the variance of `η^k` is `ν^{√T}(k)` for even `k`
(`frozen_var_even`) and `λ` for odd `k` (`frozen_var_odd`, the odd mean
vanishing by symmetry). The model-scale posterior `exp(A s^k − B s^{2k})` read
in `η = B^{1/(2k)} s` is the renormalised posterior at `Z = A/√B`, so every
expectation ratio depends on the model only through `Z`
(`scaled_ratio_invariant`, `nu_scale_invariance`). At `k = 1` the renormalised
posterior is the Gaussian `N(Z/2, 1/2)`, so the fluctuation is `1/2` for every
`Z` and `ν_LO(1) = 1/2` exactly, equal to the frozen-`Z` variance
(`renormExp_one`, `renormVar_one`, `nuLO_one`, `nuLO_one_eq_frozen`). The
strict inequality, in `NuInequality`: the Gamma-Stein identity
`c₂ = λc + (Z/2)c₁` (`tilt_stein`) gives the exact relation
`V(Z) = λ + m(Z)(Z/2 − m(Z))` at every order (`renormVar_riccati`); at odd `k`
the bounds `0 ≤ m(Z) ≤ Z/2` (`tiltC1_nonneg`, `tilt_gap_eq`,
`tilt_gap_integral_nonneg`, strict versions for `k ≥ 3`) make `V(Z) > λ` for
`Z ≠ 0` (`renormVar_odd_gt`), and with continuity and the bound
`V ≤ λ + Z²/16` the `N(0, 2)` average exceeds the frozen value
(`nuLO_odd_gt`, `nuLO_gt_frozenVar_odd`).

**Inputs.** Mathlib's Gamma integral, the Gaussian-tail integrability of
polynomial moments, and the change of variables on the line.

**Missing.** The leading-order replacement of the posterior along the dead
line, the central-limit step `Z → N(0, 2)`, the `Z`-averaged value `ν_LO(k)`
for `k ≥ 2`, which has no closed form, and the strict inequality at even `k`,
where `Z/2 − m(Z)` changes sign; at even `k` it is proved outside Lean by a
computer-assisted argument at every order (`experiments/nu_even_certify/`:
per-order certificates to 1000, a uniform proof for `k ≥ 20`).

**Depends on.** Nothing in the package.

### prop:determinantal_resolution (partial)

**Proved.** The proposition's output at width one, in `DeterminantalInstances`
(2026-08-22): at rank zero the depth-`L` chain `K = (∏ wᵢ)²` has `λ = 1/2`
with multiplicity `L`, its volume law the degree-`(L−1)` log polynomial exactly
(`width_one_chain_volume`, `width_one_chain_slope`); at rank one the regular
direction `K = (w − p)²` has `λ = 1/2` with multiplicity one, volume `2√ε`
(`morse_block_volume`, `morse_block_slope`).

**Inputs.** The tied normal-crossing law of `MultiCrossingGeneral` at `k = 1`.

**Missing.** The SVD change of variables, the Vandermonde monomialisation, and
the Newton-polyhedron formula at general widths and ranks, which is the
resolution content proper.

**Depends on.** `thm:multi_component_rates` (the tied crossing law).

---

## Curvature

### prop:curvature_rate (partial)

**Proved.** Item (ii)'s closed forms are exact. The mean-map families at
`k = 2` and `k = 3` have Gauss curvature `−1/(4t²(1+t²)²)` and
`−1/(9t⁴(1+t²)²)` on the trajectory, with `K·t^(2(k−1))` converging to `−1/4`
and `−1/9`. The determinant form of the Gauss curvature keeps every ingredient
polynomial in the jet, and the jets themselves are certified as derivatives of
the parametrization. Item (i)'s order bounds are machine-checked:
`christoffel_numerator_identity` cancels the mixed score partials to
`E[s₁(2∂_α s_α + s_α²)]`, `cross_score_order` is Cauchy-Schwarz at rate level
with constant `√(2cM)`, `christoffel_order_bound` gives
`Γ¹_{αα} = O(t^(−(k−1)))` over a Gram determinant of order `t^(2(k−1))`, and
`gamma_gamma_bounded` keeps both `ΓΓ` products of `R_{1α1α}` bounded for
`k ≥ 2`.

**Lean.** `christoffel_numerator_identity`, `abs_integral_mul_le_sqrt`,
`cross_score_order`, `christoffel_order_bound`, `gamma_gamma_bounded`,
`surfCurvAt`, `fam2_curvature`, `fam2_curvature_rate`, `fam3_curvature`,
`fam3_curvature_rate`.

**Inputs.** Score-integration regularity, in the form that the entry
derivatives are the inserted-score integrals. Missing: the identification of
the embedded Gauss curvature with the intrinsic Fisher sectional curvature,
which is the Gauss equation and enters here as the definition.

**Depends on.** `thm:fisher_decay`, `cor:fisher_structure` (the weighted
integral bound).

### cor:volume (partial)

**Proved.** The `k = 2` instance is exact. The curvature magnitude is strictly
antitone in `t`, so the high-curvature set is precisely the transverse tube;
the tube volume at density `t^m` is `δ^(m+1)/(m+1)`; Fisher volume times the
threshold converges to `1/8` and Lebesgue volume times the square root of the
threshold converges to `1/2`, both with explicit coefficients. The
real-exponent side runs on the `rpow` calculus: the `k = 3` law is exact, with
Fisher tube volume times the `3/4`-power of the threshold converging to
`1/(3·9^(3/4))`, the first non-integer instance of the scaling. Both remainders
are closed: `famKmagK` puts the instances in one family,
`fisher_volume_scaling_general` gives the exact `M^(−k/(2(k−1)))` law at every
`k ≥ 2`, and sheet uniformity is formal in `highcurv_tube_sandwich` and
`tube_weight_sandwich`, with constants uniform in the profile.

**Lean.** `famKmag`, `highcurv_iff_tube`, `tube_volume_pow`,
`fisher_volume_scaling`, `lebesgue_volume_scaling`.

**Inputs.** The mean-map families and their closed-form curvature. Nothing
remains at model scope.

**Depends on.** `prop:curvature_rate` (`famKmag_eq_neg_curv` rewrites through
`fam2_curvature`).

---

## Quotient and gauge

The gauge rows treat rescaling symmetry as a group action and ask what a
Fisher reading, an optimizer update, and a noise process do on the orbit space.
Track A works at matrix level on the invertible stratum; Track B builds the
topology and the submersion API.

### prop:ddcadam_equivariance (full)

**Proved.** The DDCAdam update map is gauge-equivariant in every gauge type the
algorithm covers: the multiplicative rescale pair in both slots, the
translation gauge, the chained gauge, and the per-channel LayerNorm scale in
both slots. The chained identity is stronger than the paper's statement: it
holds for every positive per-block family, of which the product-one chain is
the subfamily that also preserves the loss.

**Lean.** `ddcadamMult_fst_equivariant`, `ddcadamMult_snd_equivariant`,
`ddcadamTransl_equivariant`, `ddcadamChain_equivariant`,
`ddcadamLNScale_fst_equivariant`, `ddcadamLNScale_snd_equivariant`.

**Inputs.** The Adam moments and the vertical-mode choice enter as arbitrary
functions of the gauge-decomposed inputs, which is the `transport_h = Id`
clause. For the chained gauge those functions read the full vector of per-block
invariants, so the radial and gauge-mode assembly is covered at once.

**Depends on.** Nothing.

### cor:quotient_rate (partial)

**Proved.** The scalar `L`-layer model carries the whole chain: the product-one
gauge fixes the quotient coordinate, the score annihilates every vertical
direction at every point because the layer-weighted score is the product
itself, the KL factors through the quotient coordinate, and the horizontal
reading at the symmetric point has leading rate `2(L−1)` with coefficient `L`.
At matrix level Track A has landed the same chain: `matProdMap` with gauge
invariance, the fiber characterization (equal-length lists with equal products
in any group connect by the interpolating gauge), the chain derivative
certified entrywise, the telescoping vertical annihilation, the concrete
submersion through the single-slot inverse-tail direction, the closed-form
pairing `chainDeriv = x₀·P − P·x_L` whose kernel is exactly the vertical space,
and `quotient_rate_matrix`, the normalised dead-slot reading with leading rate
`2(L−1)` and coefficient `L`.

**Lean.** `prodMap`, `prodMap_gauge_invariant`, `prodGrad`,
`prodMap_hasDerivAt`, `mul_prodGrad`, `quotient_F_vertical`,
`quotient_F_vertical_quadform`, `quotient_K_invariant`, `quotient_rate_model`.

**Inputs.** The scalar model for the headline row, the invertible stratum for
the matrix level. Missing: the abstract Lie quotient of Track B; the balanced
flow itself landed in general position on the `thm:bridge` module cluster
(`balance_transport`, `balance_defect_hasDerivAt`, `balanced_flow_closed_L2`).

**Depends on.** `thm:fisher_decay`.

### cor:sgd_quotient (partial)

**Proved.** Both halves of the metric condition are exact. Euclidean SGD fails
to project, witnessed by the squared score norm taking different values at
`(1,1)` and `(2,1/2)` on one orbit, and the log-coordinate invariant metric
projects exactly, with flow factor `L·p²`, a function of the quotient
coordinate alone. The balanced flow holds in general position: the transport
identity needs no balance and no invertibility, and the balance defect
`W′W′ᵀ − WᵀW` has derivative zero along Euclidean gradient flow, certified
entrywise. The stochastic side is in at the model: pairwise independent
log-weight increments of common variance `σ²` give quotient coordinate variance
`L·σ²`, the quotient coordinate is uncorrelated with every vertical direction,
and the orbit lines have zero acceleration, so the projected drift carries no
Itô correction.

**Lean.** `euclidean_projection_obstruction`, `invariant_metric_projects`,
`covariance_table`, `quotient_noise_variance`,
`quotient_noise_vertical_uncorrelated`, `orbitLine`, `orbitLine_hasDerivAt`,
`orbitLine_accel_zero`, `orbitLine_sum`.

**Inputs.** The scalar and log-coordinate models, and pairwise independence of
the increments. Missing: the Riemannian-submersion formalism, whose first arc
is the `IsSubmersionAt` API with local sections, composition, the open-mapping
property, and `isSubmersionAt_prodTuple`.

**Depends on.** `cor:quotient_rate`.

### cor:ddcadam_quotient_rate (partial)

**Proved.** Any gauge-equivariant update has a gauge-independent projected
readout, so the quotient trajectory and its rate reading are well defined
regardless of the lift. `equivariant_update_prod` lifts the readout to chain
level in any group, and `equivariant_iterate` with `equivariant_iterate_prod`
carries it along the whole trajectory. `HasLeadingRate.comp_reparam` and
`khat_reparam_invariant` prove the rate and its `k̂` reading invariant under
any approach reparameterisation of leading rate one, of which arc length is the
inverse-speed instance.

**Lean.** `equivariant_update_projects`.

**Inputs.** The rate itself is `quotient_rate_model` and the equivariance of
the DDCAdam model update is `ddcadamChain_equivariant`, both on other rows.
Nothing remains at model scope.

**Depends on.** `cor:quotient_rate`, `prop:ddcadam_equivariance`.

### cor:global-rate (partial)

**Proved.** In the scalar gauge model at `L = 2` the raw two-layer Fisher
quadratic form `t²(v₁+v₂)²` is null on the gauge direction `(1, −1)` at every
`t`, so the raw parameter Fisher never attains the rate, and the symmetric
horizontal direction reads the quotient eigenvalue `2t²` with leading rate
`2(L−1) = 2`. The per-block minimum over same-rate blocks keeps the rate. The
orbit-space layer is machine-checked end to end at the family: the interface
gauges act through a genuine `MulAction`, the action is free on the invertible
stratum, partial products move by right multiplication under a gauge and the
total product is the complete orbit invariant, the trivialization is a global
bundle equivalence with both inverse laws, continuity holds through the
units-topology workhorses, the action-pair map is a closed embedding so the
action is proper and the orbit space is Hausdorff, `orbitSpaceHomeo` identifies
the orbit space with the units through the descended total with the
constant-tuple slice meeting every orbit once, and `slice_isometric` realizes
the quotient form as the flat Frobenius form on the base.

**Lean.** `HasLeadingRate.min_of_eq`, `gaugeQuad`, `gauge_null`,
`gauge_null_witness`, `horizontal_rate`.

**Inputs.** The scalar gauge model at `L = 2` for the rate reading; the
invertible stratum for the orbit-space statements. Missing: the abstract slice
theorem and the O'Neill machinery in full generality, held as upstream
material.

**Depends on.** `thm:fisher_decay`, `cor:kfac_lift` (the block bottoms are the
Kronecker products), `cor:quotient_rate` (the matrix quotient the orbit-space
layer runs on).

---

## Estimator slices

These rows check what a practitioner actually computes: the smallest singular
value of an activation matrix, the smallest eigenvalue of a K-FAC block, the
Kronecker lift, and the empirical-versus-expected gradient reading.

### cor:sigma-min (partial)

**Proved.** The feedforward activation `σ_min` holds at model level: the
forward dead entry carries `t^(2ℓ)`, the diagonal Gram's variational minimum is
eventually the dead entry, and the canonical chain's `σ_min²` is `t^(2ℓ)`
exactly. The sample-matrix clauses are in. The `√N` scaling is an identity: the
sample Gram form is `N` times the normalised Gram form, so a floor on the
empirical form lifts with the factor `N`. The strong law identifies the
empirical covariance with the population second moment almost surely,
entrywise, and then along every reading direction at once.

**Lean.** `deep_linear_forward_rate`, `multi_lambda_min_slice`,
`sigmaMinSq_canonical`, `sample_form_eq_N_mul_gram`, `sample_form_ge_of_gram_ge`,
`empirical_gram_strong_law`, `empirical_form_strong_law`.

**Inputs.** The scalar and diagonal models, and pairwise independent
identically distributed rows for the strong law. Nothing missing at model
scope; the population rate of the chain rows is the sample rate up to `√N`.

**Depends on.** `cor:a_g_duality` (the forward rate),
`cor:rect_product_sigma_min` (the canonical `σ_min`), `thm:bridge_multi` (the
diagonal `λ_min` slice).

### thm:multilayer-A (partial)

**Proved.** The ladder holds at the diagonal model: the layer-`ℓ` factor array
carries exactly `t^(2(ℓ−1))` at the dead unit and that entry is the bottom for
`0 < t ≤ 1`. The mixing bounds extend the exponent beyond diagonal
configurations: `σ_min²` of a product is squeezed between
`σ_min²(A)·σ_min²(B)` and `σ_max²(A)·σ_min²(B)`, so a live mixing layer changes
the constant and never the exponent.

**Lean.** `canonicalFactor`, `canonical_factor_bottom`, `sigmaMaxSq`,
`sq_sum_le_sigmaMaxSq`, `sigmaMinSq_mul_le`.

**Inputs.** The diagonal model. The strong-law identification of the empirical
covariance with the factor and the `Θ(√N)` constant are the `cor:sigma-min`
sample clauses. Nothing missing at model scope.

**Depends on.** `cor:sigma-min`.

### cor:rect_lambda_min (partial)

**Proved.** On the diagonal-spectrum slice the dead entry eventually bounds the
diagonal quadratic form from below at every vector, and the dead basis vector
attains it, so the variational `λ_min` is the dead entry. The Schur argument at
non-diagonal moments is closed: `schur_dead_lower` bounds the full block
quadratic form below by `(g − ‖b‖²/c)·v₀²` by a per-coordinate AM-GM with no
diagonality assumption, and `HasLeadingRate.sub_of_lt` propagates the rate
through the correction. The width-condition failure mode is exact: a backward
operator that factors through a narrower layer above has a nontrivial kernel by
rank-nullity, so the Gram form has an exact zero direction at every `t` and the
smallest eigenvalue is zero whatever the dead entry does.

**Lean.** `width_condition_failure`, `multi_lambda_min_slice`,
`multi_lambda_min_attained`.

**Inputs.** Diagonal second moments for the slice; a positive live floor `c`
for the Schur step. Nothing missing at model scope.

**Depends on.** `thm:bridge_multi`, `cor:bridge_g3`,
`prop:task_expansion_gfactor` (the diagonal quadratic-form lemmas).

### cor:rect_product_sigma_min (partial)

**Proved.** The canonical instance is a genuine `σ_min`: the variational
minimum of the canonical chain is `t^(2p)` exactly on `t ∈ [0,1]`, and the same
value holds at every orthogonal conjugation. The general composed-complement
case is the distance-to-image bound: when the complement's image keeps a
positive angle from the dead output direction
(`|⟨e, Bw⟩| ≤ (1 − ρ)‖Bw‖`) and the complement map has a floor, the composed
map's squared norm is at least `ρ·min(a², c²)` times the squared input, so the
narrow chain's `t^(2L)` survives exactly when the complement cannot occupy the
vacated direction.

**Lean.** `distance_to_image_lower`, `canonical_sigma_min_lower`,
`canonical_sigma_min_attained`, `sigmaMinSq_canonical`,
`sigmaMinSq_rotated_canonical`.

**Inputs.** The canonical chain for the exact value; a positive angle and a
floor on the complement for the general case. Nothing missing at model scope.

**Depends on.** `thm:bridge`.

### cor:kfac_lift (partial)

**Proved.** In the diagonal model the Kronecker factor is the product array on
the product index, the bottom of the product array is the product of the factor
bottoms with attainment at the pair index, and at the canonical configuration
the dead-unit pair carries exactly `t^(2(a+b))`, the A-G duality product, and
is the bottom for `0 < t ≤ 1`. The cross-layer remark's gauge-ray flatness is
`gauge_ray_flat`. The matrix side is closed: `kron_mulVec_vecKron` proves the
mixed-product property in vector form on true Kronecker matrices, `kron_eigen`
lifts factor eigenpairs to product eigenpairs, `vecKron_rankOne` is the
vectorisation identification, and `kron_spectral` gives the complete spectral
decomposition with the lifted eigenvector matrix, the product eigenvalues on
the product index, and orthogonality, so the lifted eigenpairs exhaust the
spectrum with multiplicity.

**Lean.** `kron`, `kron_min`, `kron_min_attained`, `kron_quadform`,
`canonical_kron_dead`, `canonical_kron_bottom`, `gauge_ray_flat`.

**Inputs.** The diagonal model for the headline reading. The vectorisation
identification of `a ⊗ g` with `g aᵀ` stays with the paper. Nothing remains at
model scope.

**Depends on.** `thm:multilayer-A` (the canonical factor array).

### prop:task_expansion_gfactor (partial)

**Proved.** The exact block slice: the head form is sandwiched between
`σ²_old·‖v‖²` and `σ²_new·‖v‖²` with both ends attained on basis vectors, so
the condition ratio is exactly `σ²_new/σ²_old`. Through a diagonal Jacobian the
entries are `jᵢ²dᵢ`, so the spread is multiplied by at most the Jacobian's
squared conditioning, the `κ(J)²κ(G)` bound in entry form. The perturbation
term is exact: an entrywise perturbation of size `ε` moves the sandwich by at
most `ε(n+1)‖v‖²`.

**Lean.** `task_expansion_perturbed`, `diag_quadform_ge`, `diag_quadform_le`,
`diag_quadform_single`, `task_expansion_head_bounds`,
`task_expansion_inherit_bounds`.

**Inputs.** The exact block slice at zero perturbation, and a diagonal Jacobian
for the inheritance bound. Nothing missing at model scope.

**Depends on.** `cor:fisher_structure` (the entrywise-to-quadratic-form
conversion).

### cor:emp_vs_exp_ce (partial)

**Proved.** Per sample, at observed-label mass `1 − ε` the empirical gradient
norm lies in `[ε², 2ε²]`, the Hessian trace in `[ε(1−ε), 2ε]`, and the sandwich
`(tr H)²/4 ≤ ‖p − e_y‖² ≤ 2(tr H)²/(1−ε)²` gives the quadratic separation with
explicit constants. The `x`-averaged form integrates the per-sample bounds over
the data: the empirical gradient norm averages between `E[ε²]` and `2E[ε²]` and
the expected trace between `E[ε(1−ε)]` and `2E[ε]`, which is the `Θ(ε²)`
against `Θ(ε)` reading along a memorising trajectory.

**Lean.** `ceHess_trace`, `emp_grad_sq_bounds`, `exp_trace_bounds`,
`emp_exp_quadratic_separation`, `emp_exp_averaged`.

**Inputs.** The finite-probability-vector model of the softmax head. Nothing
missing at model scope.

**Depends on.** `thm:bridge_ce` (the head Hessian).

---

## Module import graph

`proofs/blueprint/modules.mmd` draws all 50 files under
`proofs/DeadDirections/` with 53 intra-package import edges, grouped into the
same themes as the rows above. Nine modules import nothing else from the
package and act as the package's bases: `FisherDecay` (the rate calculus),
`LnKernel`, `DdcAdamEquivariance`, `SliceRlct`, `SpectrumCount`, `SampleGram`,
`LaplaceGamma`, `TwistedMap`, and `AnalyticNull`.

`FisherDecay` is the single hub. Sixteen modules import it directly, and almost
every rate statement in the package is phrased in its `HasLeadingRate`
predicate; `RpowRate` extends the same calculus to real exponents for the
curvature-volume and rotation-window rows. The second cluster centres on
`DeepLinearBridge`, which the bias, cross-entropy, `σ_min`, K-FAC, and Gaussian-layer
modules build on. `MixtureScore` is the third fan-out point, feeding the three
nonlinear channels (`ReluChannel`, `SmoothChain`, `SwigluChannel`) and the
LayerNorm reset. `MatrixQuotient` carries the quotient program, with
`OrbitSpace`, `Submersion`, and `MatrixSqrt` above it.

One fact about the package layout is worth recording, because it bit this
program. The lake library compiles only the transitive imports of
`DeadDirections.lean`. Until 2026-08-22 the root imported 33 of the 47
modules, so fourteen (`AnalyticNullPi`, `CeGated`, `Cochran`,
`CurvatureOrders`, `DagPathRates`, `LaplaceGamma`, `LnJacobian`,
`MultiCrossingGeneral`, `QuotientNoise`, `SampleGram`, `SelectionAssembly`,
`SpectrumCount`, `TwistedMap`, `VolumeMultiG`) were never compiled by a plain
`lake build`, and twelve of them failed on first real compilation. They were
repaired that day with every statement unchanged (three cosmetic spelling and
binder edits), the root now imports every module (50 as of 2026-08-22), and
`verification/checks/check_lean_proofs.py` fails on a module missing from the
root or lacking a compiled `.olean`. The ledger's integrity paragraph records
the details.

## Upstreaming bundles

The ledger's Mathlib tracker holds fifteen candidate bundles, each with its
declarations, a target home in Mathlib, and a note on what to check before
opening a pull request. None has advanced past `candidate`. Grouped by what
they are:

**Analysis and asymptotics.** The leading-rate mini-theory in both the natural
and real exponent forms (`HasLeadingRate` with its calculus, `HasLeadingRateR`,
`hasLeadingRateR_rpow`), aimed at the `Asymptotics` neighborhood after checking
overlap with `IsTheta` and `IsEquivalent` and generalizing the base filter away
from `𝓝[>] 0`. Alongside it, the analytic zero-set bundle
(`analytic_zero_set_null`, `analytic_zero_set_null_pi`, `consCLM`), complete in
both the one-variable and several-variable forms.

**Probability.** The Gaussian tilt and moment workhorse
(`gaussDensity_tilt`, the integrability and integral lemmas), to be restated
over `gaussianReal`; and the Gamma Laplace transform with the reciprocal moment
plus the Gaussian square transform (`integral_exp_neg_mul_gammaMeasure`,
`integral_inv_gammaMeasure`, `lintegral_inv_eq_lintegral_laplace`,
`integral_exp_neg_mul_sq_gaussianReal`, `laplace_weighted_sq_pi`), which fills a
gap the pinned Mathlib has today.

**Measure theory and volume.** The monomial sublevel volume laws
(`volume_sublevel_pow` through `volume_crossing_tied_general`), ready now that
the general-`r` tied law is in; the hyperplane Haar-nullity convenience lemma
`hyperplane_null`; and the instance gap where typeclass search misses the
product-of-Haar instance on `(Fin r → ℝ) × (Fin m → ℝ)`, which the package
applies by hand in `SliceRlctProduct`. The ledger names the instance gap as the
first pull request to open, as a Zulip report followed by a small fix.

**Linear algebra.** The variational `σ_min` for real matrices with attainment
(`sigmaMinSq`, `hermitian_quadform_*`), to be checked against the existing
Rayleigh theory; the eigenvalue count from block bounds
(`eigenvalue_count_of_block_bounds` and the eigenvector-span lemmas under it),
which needs no Courant-Fischer; the Kronecker vector lemmas
(`kron_mulVec_vecKron`, `kron_eigen`), bundled with the Haar-nullity item; and
the real positive-semidefinite square root with uniqueness (`matSqrt`,
`matSqrt_unique`, `balanced_gram_eq_sqrt`), built through the spectral
decomposition and the self-hosted trace trick.

**Topology, calculus, and special functions.** The submersion API at
normed-space level (`IsSubmersionAt` with local sections, composition, the
open-mapping property, `isSubmersionAt_prodTuple`), where Mathlib has
immersions and no submersions; the two units-topology continuity workhorses
(`continuous_units_mul`, `continuous_units_inv`), which are the content of the
missing `ContinuousMul` instance for `Mˣ`; the finite softmax with its
certified Jacobian (`softmaxN`, `softmaxN_hasDerivAt_dir`,
`softmaxN_uniform_jacobian`), where no softmax API exists today; the sigmoid
half-point bound; and the interpolating gauge for equal list products
(`gaugeActFrom`, `exists_gauge_of_prod_eq`), group-general and provable by one
induction in each direction.

The tracker's process note fixes the sequence: the Haar-instance item first,
the leading-rate and Gaussian items after the current attack wave, the volume
laws after the general-`r` log law. Every pull request opens with a Zulip
thread, and the code has to be generalized out of project context, named to
convention, and docstringed.

## Declaration verification

Every declaration name cited above appears in the table below with the file and
line where the package declares it. The table was produced by scanning
`proofs/DeadDirections/*.lean` for declaration keywords with the enclosing
namespace tracked, then matching against the names used in this document; the
scan is `proofs/blueprint/gen_blueprint.py`, which also regenerates
`modules.mmd`, so the table is checkable by re-running it.

| Declaration | File | Line |
|---|---|---|
| `HasKLOrder` | `DeadDirections/KlOrder.lean` | 23 |
| `HasLeadingRate` | `DeadDirections/FisherDecay.lean` | 27 |
| `HasLeadingRate.add_min` | `DeadDirections/DagPathRates.lean` | 28 |
| `HasLeadingRate.add_min_coeff` | `DeadDirections/DagPathRates.lean` | 305 |
| `HasLeadingRate.add_of_eq` | `DeadDirections/FisherDecay.lean` | 754 |
| `HasLeadingRate.add_of_lt` | `DeadDirections/FisherDecay.lean` | 726 |
| `HasLeadingRate.comp_reparam` | `DeadDirections/FisherDecay.lean` | 817 |
| `HasLeadingRate.extra_linear` | `DeadDirections/BridgeComposition.lean` | 245 |
| `HasLeadingRate.khat_recovers` | `DeadDirections/FisherDecay.lean` | 111 |
| `HasLeadingRate.log_slope` | `DeadDirections/FisherDecay.lean` | 68 |
| `HasLeadingRate.min_of_eq` | `DeadDirections/FisherDecay.lean` | 779 |
| `HasLeadingRate.mul` | `DeadDirections/FisherDecay.lean` | 331 |
| `HasLeadingRate.of_relatively_close` | `DeadDirections/FisherDecay.lean` | 287 |
| `HasLeadingRate.sub_of_lt` | `DeadDirections/FisherDecay.lean` | 764 |
| `HasLeadingRateR` | `DeadDirections/RpowRate.lean` | 19 |
| `IsSubmersionAt` | `DeadDirections/Submersion.lean` | 33 |
| `ResSeg.transfer` | `DeadDirections/BridgeComposition.lean` | 459 |
| `abs_integral_mul_le_sqrt` | `DeadDirections/CurvatureOrders.lean` | 65 |
| `abs_integral_mul_le_weighted` | `DeadDirections/FisherDecay.lean` | 573 |
| `abs_sigmoid_sub_half` | `DeadDirections/SwigluChannel.lean` | 53 |
| `affChain_dead_eq` | `DeadDirections/BiasChannel.lean` | 73 |
| `affChain_dead_uniform` | `DeadDirections/BiasChannel.lean` | 109 |
| `affChain_sub` | `DeadDirections/BiasChannel.lean` | 46 |
| `aff_forward_cap` | `DeadDirections/BiasChannel.lean` | 153 |
| `alphaSlope` | `DeadDirections/LnFiniteT.lean` | 51 |
| `alphaSlope_eq` | `DeadDirections/LnFiniteT.lean` | 55 |
| `analytic_zero_set_null` | `DeadDirections/AnalyticNull.lean` | 34 |
| `analytic_zero_set_null_pi` | `DeadDirections/AnalyticNullPi.lean` | 39 |
| `assembled_schur_slice` | `DeadDirections/SigmaMin.lean` | 501 |
| `attnA` | `DeadDirections/AttnBridge.lean` | 42 |
| `attnBackDead` | `DeadDirections/AttnBridge.lean` | 75 |
| `attnDeadOut` | `DeadDirections/AttnBridge.lean` | 48 |
| `backDeriv_sub_le` | `DeadDirections/SmoothChain.lean` | 570 |
| `balance_defect_hasDerivAt` | `DeadDirections/MatrixQuotient.lean` | 834 |
| `balance_transport` | `DeadDirections/MatrixQuotient.lean` | 809 |
| `balanced_flow_closed_L2` | `DeadDirections/MatrixQuotient.lean` | 926 |
| `balanced_gram_eq_sqrt` | `DeadDirections/MatrixSqrt.lean` | 232 |
| `bias_taylor_correction` | `DeadDirections/SpectrumCount.lean` | 86 |
| `biasedChain_deriv` | `DeadDirections/BiasChannel.lean` | 303 |
| `biasedChain_deriv_of_nonneg` | `DeadDirections/BiasChannel.lean` | 275 |
| `biased_backward_moment` | `DeadDirections/BiasChannel.lean` | 343 |
| `biased_gate_mass_gt_half` | `DeadDirections/BiasChannel.lean` | 358 |
| `block_form_dead_axis` | `DeadDirections/SigmaMin.lean` | 635 |
| `block_form_lower_weighted` | `DeadDirections/SigmaMin.lean` | 517 |
| `block_lambda_min_sandwich` | `DeadDirections/SigmaMin.lean` | 551 |
| `block_lambda_min_sandwich_ev` | `DeadDirections/SelectionAssembly.lean` | 89 |
| `bridge_attn_backward` | `DeadDirections/AttnBridge.lean` | 82 |
| `bridge_attn_forward` | `DeadDirections/AttnBridge.lean` | 54 |
| `bridge_attn_forward_N` | `DeadDirections/SoftmaxN.lean` | 226 |
| `canonicalFactor` | `DeadDirections/KfacLift.lean` | 72 |
| `canonicalLayer_pow` | `DeadDirections/DeepLinearBridge.lean` | 46 |
| `canonicalLayer_pow_mulVec_ne` | `DeadDirections/DeepLinearBridge.lean` | 65 |
| `canonical_factor_bottom` | `DeadDirections/KfacLift.lean` | 123 |
| `canonical_kron_bottom` | `DeadDirections/KfacLift.lean` | 89 |
| `canonical_kron_dead` | `DeadDirections/KfacLift.lean` | 78 |
| `canonical_mask_in_line` | `DeadDirections/RotNegative.lean` | 70 |
| `canonical_reading_rate` | `DeadDirections/RotNegative.lean` | 122 |
| `canonical_sigma_min_attained` | `DeadDirections/DeepLinearBridge.lean` | 526 |
| `canonical_sigma_min_lower` | `DeadDirections/DeepLinearBridge.lean` | 504 |
| `ceHess_expect` | `DeadDirections/CeHead.lean` | 47 |
| `ceHess_mulVec_one` | `DeadDirections/CeHead.lean` | 140 |
| `ceHess_one_vecMul` | `DeadDirections/CeHead.lean` | 275 |
| `ceHess_posdef_on_perp` | `DeadDirections/CeHead.lean` | 177 |
| `ceHess_quadform` | `DeadDirections/CeHead.lean` | 107 |
| `ceHess_quadform_eq_var` | `DeadDirections/CeHead.lean` | 124 |
| `ceHess_quadform_eq_zero_iff` | `DeadDirections/CeHead.lean` | 157 |
| `ceHess_trace` | `DeadDirections/CeHead.lean` | 405 |
| `ce_bridge_composed` | `DeadDirections/CeHead.lean` | 352 |
| `ce_dead_lower` | `DeadDirections/CeHead.lean` | 212 |
| `ce_gated_chain_lower` | `DeadDirections/CeGated.lean` | 56 |
| `ce_gated_chain_lower_of_indep` | `DeadDirections/CeGated.lean` | 88 |
| `ce_gauge_eigen_limit` | `DeadDirections/CeHead.lean` | 324 |
| `ce_gauge_kernel` | `DeadDirections/CeHead.lean` | 313 |
| `chainA` | `DeadDirections/AttnRoutes.lean` | 66 |
| `chainCoeff_append` | `DeadDirections/BridgeComposition.lean` | 52 |
| `chainCoeff_flatMap` | `DeadDirections/BridgeComposition.lean` | 216 |
| `chainRate_append` | `DeadDirections/BridgeComposition.lean` | 47 |
| `chainRate_flatMap` | `DeadDirections/BridgeComposition.lean` | 204 |
| `chainRate_replicate` | `DeadDirections/BridgeComposition.lean` | 143 |
| `chainTransfer_sq_hasLeadingRate` | `DeadDirections/BridgeComposition.lean` | 526 |
| `christoffel_numerator_identity` | `DeadDirections/CurvatureOrders.lean` | 30 |
| `christoffel_order_bound` | `DeadDirections/CurvatureOrders.lean` | 152 |
| `complement_zero_caveat` | `DeadDirections/SigmaMin.lean` | 646 |
| `composedSignal_eq` | `DeadDirections/BridgeComposition.lean` | 59 |
| `composedSignal_forward_hasLeadingRate` | `DeadDirections/BridgeComposition.lean` | 277 |
| `composedSignal_hasLeadingRate` | `DeadDirections/BridgeComposition.lean` | 112 |
| `composedSignal_sq_integral` | `DeadDirections/BridgeComposition.lean` | 87 |
| `composition_matmul_hasLeadingRate` | `DeadDirections/BridgeComposition.lean` | 161 |
| `composition_rate_two_hasLeadingRate` | `DeadDirections/BridgeComposition.lean` | 228 |
| `composition_residual_const` | `DeadDirections/BridgeComposition.lean` | 177 |
| `consCLM` | `DeadDirections/AnalyticNullPi.lean` | 24 |
| `continuous_units_inv` | `DeadDirections/OrbitSpace.lean` | 472 |
| `continuous_units_mul` | `DeadDirections/OrbitSpace.lean` | 453 |
| `covMatrix_layerNorm_ginv_eq_zero` | `DeadDirections/LnKernel.lean` | 185 |
| `covMatrix_lnLike_ginv_eq_zero` | `DeadDirections/LnKernel.lean` | 148 |
| `covMatrix_lnLike_zero_coord` | `DeadDirections/LnKernel.lean` | 165 |
| `covMatrix_vecMul_eq_zero_of_sum_const` | `DeadDirections/LnKernel.lean` | 104 |
| `covariance_table` | `DeadDirections/QuotientNoise.lean` | 36 |
| `cross_moment_expansion` | `DeadDirections/FisherDecay.lean` | 366 |
| `cross_score_order` | `DeadDirections/CurvatureOrders.lean` | 118 |
| `crossing_distinct_slope` | `DeadDirections/MultiCrossing.lean` | 473 |
| `crossing_tied_general_slope` | `DeadDirections/MultiCrossingGeneral.lean` | 401 |
| `crossing_tied_slope` | `DeadDirections/MultiCrossing.lean` | 193 |
| `crossover_scale_closed_form` | `DeadDirections/RotNegative.lean` | 254 |
| `cumExp` | `DeadDirections/DeepLinearBridge.lean` | 203 |
| `cumExp_uniform` | `DeadDirections/DeepLinearBridge.lean` | 291 |
| `curveFisher_eq` | `DeadDirections/GaussianFisher.lean` | 808 |
| `curveFisher_hasLeadingRate` | `DeadDirections/GaussianFisher.lean` | 847 |
| `curveKL_eq` | `DeadDirections/GaussianFisher.lean` | 817 |
| `curveKL_hasKLOrder` | `DeadDirections/KlOrder.lean` | 28 |
| `curve_fisher_kl_ratio` | `DeadDirections/GaussianFisher.lean` | 838 |
| `dag_K_le_skip` | `DeadDirections/DagPathRates.lean` | 479 |
| `dag_K_succ_le` | `DeadDirections/DagPathRates.lean` | 468 |
| `dag_backward_coeff` | `DeadDirections/DagPathRates.lean` | 369 |
| `dag_backward_moment_rate` | `DeadDirections/DagPathRates.lean` | 132 |
| `dag_backward_rate` | `DeadDirections/DagPathRates.lean` | 81 |
| `dag_backward_remainder` | `DeadDirections/DagPathRates.lean` | 489 |
| `dag_coeff_pos` | `DeadDirections/DagPathRates.lean` | 438 |
| `dag_full_skip_K` | `DeadDirections/DagPathRates.lean` | 164 |
| `dag_gated_eq` | `DeadDirections/DagPathRates.lean` | 233 |
| `dag_no_skip_K` | `DeadDirections/DagPathRates.lean` | 152 |
| `dag_skiponly_zero_iff` | `DeadDirections/DagPathRates.lean` | 189 |
| `ddcadamChain_equivariant` | `DeadDirections/DdcAdamEquivariance.lean` | 309 |
| `ddcadamLNScale_fst_equivariant` | `DeadDirections/DdcAdamEquivariance.lean` | 338 |
| `ddcadamLNScale_snd_equivariant` | `DeadDirections/DdcAdamEquivariance.lean` | 351 |
| `ddcadamMult_fst_equivariant` | `DeadDirections/DdcAdamEquivariance.lean` | 201 |
| `ddcadamMult_snd_equivariant` | `DeadDirections/DdcAdamEquivariance.lean` | 214 |
| `ddcadamTransl_equivariant` | `DeadDirections/DdcAdamEquivariance.lean` | 251 |
| `deadRead` | `DeadDirections/RotNegative.lean` | 80 |
| `deep_linear_ag_product` | `DeadDirections/DeepLinearBridge.lean` | 123 |
| `deep_linear_backward_rate` | `DeadDirections/DeepLinearBridge.lean` | 76 |
| `deep_linear_dead_entry_eventually_le` | `DeadDirections/DeepLinearBridge.lean` | 146 |
| `deep_linear_forward_rate` | `DeadDirections/DeepLinearBridge.lean` | 109 |
| `deep_linear_hasLeadingRate` | `DeadDirections/DeepLinearBridge.lean` | 92 |
| `diag_lambda_min_slice_general` | `DeadDirections/DeepLinearBridge.lean` | 393 |
| `diag_quadform_ge` | `DeadDirections/DeepLinearBridge.lean` | 560 |
| `diag_quadform_le` | `DeadDirections/DeepLinearBridge.lean` | 567 |
| `diag_quadform_single` | `DeadDirections/DeepLinearBridge.lean` | 575 |
| `direct_rate_regime` | `DeadDirections/LnFiniteT.lean` | 119 |
| `disjoint_gates_moment_zero` | `DeadDirections/BridgeComposition.lean` | 287 |
| `distance_to_image_lower` | `DeadDirections/SigmaMin.lean` | 703 |
| `eigSpan` | `DeadDirections/SpectrumCount.lean` | 210 |
| `eigenvalue_count_of_block_bounds` | `DeadDirections/SpectrumCount.lean` | 257 |
| `emp_exp_averaged` | `DeadDirections/CeHead.lean` | 523 |
| `emp_exp_quadratic_separation` | `DeadDirections/CeHead.lean` | 486 |
| `emp_grad_sq_bounds` | `DeadDirections/CeHead.lean` | 414 |
| `empirical_form_strong_law` | `DeadDirections/SampleGram.lean` | 86 |
| `empirical_gram_strong_law` | `DeadDirections/SampleGram.lean` | 62 |
| `equivariant_iterate` | `DeadDirections/MatrixQuotient.lean` | 188 |
| `equivariant_iterate_prod` | `DeadDirections/MatrixQuotient.lean` | 205 |
| `equivariant_update_prod` | `DeadDirections/MatrixQuotient.lean` | 165 |
| `equivariant_update_projects` | `DeadDirections/Quotient.lean` | 182 |
| `euclidean_projection_obstruction` | `DeadDirections/Quotient.lean` | 137 |
| `exists_gauge_of_prod_eq` | `DeadDirections/MatrixQuotient.lean` | 144 |
| `exp_trace_bounds` | `DeadDirections/CeHead.lean` | 449 |
| `fam2_curvature` | `DeadDirections/CurvatureInstance.lean` | 121 |
| `fam2_curvature_rate` | `DeadDirections/CurvatureInstance.lean` | 133 |
| `fam3_curvature` | `DeadDirections/CurvatureInstance.lean` | 191 |
| `fam3_curvature_rate` | `DeadDirections/CurvatureInstance.lean` | 203 |
| `famKmag` | `DeadDirections/CurvatureInstance.lean` | 237 |
| `famKmagK` | `DeadDirections/CurvatureInstance.lean` | 429 |
| `famKmag_eq_neg_curv` | `DeadDirections/CurvatureInstance.lean` | 239 |
| `fisherMu_gaussian` | `DeadDirections/GaussianFisher.lean` | 102 |
| `fisher_decay_slope` | `DeadDirections/FisherDecay.lean` | 268 |
| `fisher_expansion_of_score_expansion` | `DeadDirections/FisherDecay.lean` | 144 |
| `fisher_volume_scaling` | `DeadDirections/CurvatureInstance.lean` | 285 |
| `fisher_volume_scaling_general` | `DeadDirections/CurvatureInstance.lean` | 477 |
| `frozen_half_line` | `DeadDirections/NuFrozen.lean` | 61 |
| `frozen_mean_T` | `DeadDirections/NuFrozen.lean` | 241 |
| `frozen_mean_sqrtT` | `DeadDirections/NuFrozen.lean` | 251 |
| `frozen_var_even` | `DeadDirections/NuFrozen.lean` | 271 |
| `frozen_var_odd` | `DeadDirections/NuFrozen.lean` | 292 |
| `g10_anomaly_scope` | `DeadDirections/AttnRoutes.lean` | 488 |
| `gammaPDFReal_mul_exp` | `DeadDirections/LaplaceGamma.lean` | 32 |
| `gamma_gamma_bounded` | `DeadDirections/CurvatureOrders.lean` | 174 |
| `gamma_laplace_factor_eq` | `DeadDirections/LaplaceGamma.lean` | 392 |
| `gated_moment_factor` | `DeadDirections/DagPathRates.lean` | 284 |
| `gaugeActFrom` | `DeadDirections/MatrixQuotient.lean` | 36 |
| `gaugeQuad` | `DeadDirections/KfacLift.lean` | 229 |
| `gauge_null` | `DeadDirections/KfacLift.lean` | 233 |
| `gauge_null_witness` | `DeadDirections/KfacLift.lean` | 240 |
| `gauge_ray_flat` | `DeadDirections/KfacLift.lean` | 264 |
| `gaussDensity_tilt` | `DeadDirections/MixtureScore.lean` | 103 |
| `gaussian_curve_readings` | `DeadDirections/KlOrder.lean` | 41 |
| `gram_quadform` | `DeadDirections/SpectrumCount.lean` | 341 |
| `hasDerivAt_smoothChain` | `DeadDirections/SmoothChain.lean` | 522 |
| `hasLeadingRateR_rpow` | `DeadDirections/RpowRate.lean` | 32 |
| `hasLeadingRate_finset_sum` | `DeadDirections/DagPathRates.lean` | 322 |
| `hasLeadingRate_finset_sum_pos` | `DeadDirections/DagPathRates.lean` | 48 |
| `hasLeadingRate_of_expansion` | `DeadDirections/FisherDecay.lean` | 32 |
| `hasLeadingRate_pow` | `DeadDirections/FisherDecay.lean` | 716 |
| `hasLeadingRate_pow_factor` | `DeadDirections/FisherDecay.lean` | 792 |
| `hasLeadingRate_sq_of_expansion` | `DeadDirections/SelectionAssembly.lean` | 29 |
| `hasLeadingRate_sum_same` | `DeadDirections/SelectionAssembly.lean` | 65 |
| `head_dead_axis_eq_moment` | `DeadDirections/CeGated.lean` | 29 |
| `highcurv_iff_tube` | `DeadDirections/CurvatureInstance.lean` | 264 |
| `highcurv_tube_sandwich` | `DeadDirections/CurvatureInstance.lean` | 539 |
| `horizontal_rate` | `DeadDirections/KfacLift.lean` | 249 |
| `hyperplane_null` | `DeadDirections/GaussianLayer.lean` | 120 |
| `integral_exp_neg_mul_gammaMeasure` | `DeadDirections/LaplaceGamma.lean` | 122 |
| `integral_exp_neg_mul_sq_gaussianReal` | `DeadDirections/Cochran.lean` | 46 |
| `integral_inv_gammaMeasure` | `DeadDirections/LaplaceGamma.lean` | 132 |
| `integral_pow_Ioo` | `DeadDirections/VolumeMultiG.lean` | 29 |
| `inv_moment_gamma_pair_lt_top_iff` | `DeadDirections/LaplaceGamma.lean` | 403 |
| `inv_moment_rotSigma_lt_top_iff` | `DeadDirections/Cochran.lean` | 174 |
| `invariant_kl_rate` | `DeadDirections/DeepLinearBridge.lean` | 751 |
| `invariant_metric_projects` | `DeadDirections/Quotient.lean` | 165 |
| `isSubmersionAt_prodTuple` | `DeadDirections/Submersion.lean` | 141 |
| `khat_reparam_invariant` | `DeadDirections/FisherDecay.lean` | 854 |
| `kron` | `DeadDirections/KfacLift.lean` | 29 |
| `kron_eigen` | `DeadDirections/KfacLift.lean` | 174 |
| `kron_min` | `DeadDirections/KfacLift.lean` | 36 |
| `kron_min_attained` | `DeadDirections/KfacLift.lean` | 50 |
| `kron_mulVec_vecKron` | `DeadDirections/KfacLift.lean` | 158 |
| `kron_quadform` | `DeadDirections/KfacLift.lean` | 56 |
| `kron_spectral` | `DeadDirections/KfacLift.lean` | 195 |
| `laplace_indep_gamma_pair` | `DeadDirections/LaplaceGamma.lean` | 362 |
| `laplace_product_integrableOn_iff` | `DeadDirections/LaplaceGamma.lean` | 209 |
| `laplace_weighted_sq_pi` | `DeadDirections/Cochran.lean` | 72 |
| `le_sigmaMinSq_mul` | `DeadDirections/SigmaMin.lean` | 795 |
| `leak_amplitude_normalised` | `DeadDirections/LnFiniteT.lean` | 199 |
| `leak_cap_ne_additive` | `DeadDirections/BridgeComposition.lean` | 346 |
| `leak_caps_rate` | `DeadDirections/BridgeComposition.lean` | 323 |
| `leak_kl_rate` | `DeadDirections/DeepLinearBridge.lean` | 732 |
| `leak_not_dead` | `DeadDirections/DeepLinearBridge.lean` | 761 |
| `leak_prefactor_bounded` | `DeadDirections/LnFiniteT.lean` | 132 |
| `lebesgue_volume_scaling` | `DeadDirections/CurvatureInstance.lean` | 320 |
| `lintegral_inv_eq_lintegral_laplace` | `DeadDirections/LaplaceGamma.lean` | 171 |
| `lnG` | `DeadDirections/LnFiniteT.lean` | 31 |
| `lnG_hasDerivAt` | `DeadDirections/LnFiniteT.lean` | 34 |
| `lnJac_mulVec` | `DeadDirections/LnJacobian.lean` | 123 |
| `lnP1_odd` | `DeadDirections/LnFiniteT.lean` | 321 |
| `lnP2` | `DeadDirections/LnFiniteT.lean` | 281 |
| `lnVar_eq_quadratic` | `DeadDirections/LnFiniteT.lean` | 239 |
| `lnZ_sq_expansion` | `DeadDirections/LnFiniteT.lean` | 296 |
| `lnZ_sq_remainder_bounded` | `DeadDirections/LnFiniteT.lean` | 333 |
| `lnZ_zero` | `DeadDirections/LnFiniteT.lean` | 192 |
| `ln_bracket_no_crossing` | `DeadDirections/LnResetChannel.lean` | 80 |
| `ln_bracket_plateau` | `DeadDirections/LnResetChannel.lean` | 63 |
| `ln_jacobian_dead_component` | `DeadDirections/LnJacobian.lean` | 147 |
| `ln_jacobian_dead_passes` | `DeadDirections/LnJacobian.lean` | 175 |
| `ln_jacobian_leak` | `DeadDirections/LnJacobian.lean` | 192 |
| `ln_leak_derivative` | `DeadDirections/LnFiniteT.lean` | 205 |
| `ln_leak_rate` | `DeadDirections/LnFiniteT.lean` | 147 |
| `ln_moment_assembled` | `DeadDirections/LnFiniteT.lean` | 444 |
| `ln_reset_moment` | `DeadDirections/LnResetChannel.lean` | 45 |
| `ln_sigma0_inv_moment_lt_top_iff` | `DeadDirections/Cochran.lean` | 358 |
| `ln_sigma0_shape_criterion` | `DeadDirections/LaplaceGamma.lean` | 343 |
| `logPoly_recursion` | `DeadDirections/MultiCrossingGeneral.lean` | 97 |
| `logistic` | `DeadDirections/AttnBridge.lean` | 26 |
| `masked_dead_live_overlap` | `DeadDirections/RotNegative.lean` | 63 |
| `matProdMap` | `DeadDirections/MatrixQuotient.lean` | 223 |
| `matSqrt` | `DeadDirections/MatrixSqrt.lean` | 65 |
| `matSqrt_unique` | `DeadDirections/MatrixSqrt.lean` | 128 |
| `mixKL` | `DeadDirections/MixtureScore.lean` | 837 |
| `mixKL_hasKLOrder` | `DeadDirections/MixtureScore.lean` | 1063 |
| `mixing_theta_comparison` | `DeadDirections/SigmaMin.lean` | 291 |
| `mixture_det_pos` | `DeadDirections/GaussianFisher.lean` | 622 |
| `mixture_fisher_expansion` | `DeadDirections/MixtureScore.lean` | 555 |
| `mixture_fisher_slope` | `DeadDirections/MixtureScore.lean` | 620 |
| `mixture_rank_loss` | `DeadDirections/GaussianFisher.lean` | 422 |
| `mixture_readings` | `DeadDirections/MixtureScore.lean` | 1193 |
| `morse_block_slope` | `DeadDirections/DeterminantalInstances.lean` | 71 |
| `morse_block_volume` | `DeadDirections/DeterminantalInstances.lean` | 64 |
| `mse_base_case` | `DeadDirections/GaussianLayer.lean` | 52 |
| `mse_bridge_composed` | `DeadDirections/GaussianLayer.lean` | 191 |
| `mul_prodGrad` | `DeadDirections/Quotient.lean` | 64 |
| `multiLayer` | `DeadDirections/DeepLinearBridge.lean` | 190 |
| `multiLayer_eq_canonical` | `DeadDirections/DeepLinearBridge.lean` | 321 |
| `multiProd_eq_diagonal` | `DeadDirections/DeepLinearBridge.lean` | 207 |
| `multi_backward_cross` | `DeadDirections/DeepLinearBridge.lean` | 258 |
| `multi_backward_hasLeadingRate` | `DeadDirections/DeepLinearBridge.lean` | 275 |
| `multi_backward_rate` | `DeadDirections/DeepLinearBridge.lean` | 243 |
| `multi_dead_entry_eventually_le` | `DeadDirections/DeepLinearBridge.lean` | 302 |
| `multi_lambda_min_attained` | `DeadDirections/DeepLinearBridge.lean` | 369 |
| `multi_lambda_min_slice` | `DeadDirections/DeepLinearBridge.lean` | 337 |
| `near_canonical_rate_perturbed` | `DeadDirections/BridgeComposition.lean` | 691 |
| `near_canonical_rate_zero` | `DeadDirections/BridgeComposition.lean` | 703 |
| `near_canonical_rates_differ` | `DeadDirections/BridgeComposition.lean` | 712 |
| `noise_floor_regime` | `DeadDirections/LnFiniteT.lean` | 68 |
| `noln_direct_rate` | `DeadDirections/LnFiniteT.lean` | 159 |
| `normalFormMulti_diagScale` | `DeadDirections/SliceRlctProduct.lean` | 285 |
| `normalForm_diagScale` | `DeadDirections/SliceRlctProduct.lean` | 35 |
| `normalizeS_scale` | `DeadDirections/LnResetChannel.lean` | 29 |
| `nuLO_gt_frozenVar_odd` | `DeadDirections/NuInequality.lean` | 749 |
| `nuLO_odd_gt` | `DeadDirections/NuInequality.lean` | 723 |
| `nuLO_one` | `DeadDirections/NuFrozen.lean` | 477 |
| `nuLO_one_eq_frozen` | `DeadDirections/NuFrozen.lean` | 484 |
| `nu_scale_invariance` | `DeadDirections/NuFrozen.lean` | 390 |
| `one_le_sigmaMinSq_one_add` | `DeadDirections/SigmaMin.lean` | 818 |
| `one_le_sigmaMinSq_resChain` | `DeadDirections/SigmaMin.lean` | 844 |
| `orbitLine` | `DeadDirections/QuotientNoise.lean` | 93 |
| `orbitLine_accel_zero` | `DeadDirections/QuotientNoise.lean` | 104 |
| `orbitLine_hasDerivAt` | `DeadDirections/QuotientNoise.lean` | 95 |
| `orbitLine_sum` | `DeadDirections/QuotientNoise.lean` | 111 |
| `orbitSpaceHomeo` | `DeadDirections/OrbitSpace.lean` | 835 |
| `polydisc_radius_pow` | `DeadDirections/VolumeMultiG.lean` | 58 |
| `polydisc_volume_factorised` | `DeadDirections/VolumeMultiG.lean` | 42 |
| `polydisc_volume_factorised_pi` | `DeadDirections/VolumeMultiG.lean` | 195 |
| `post_ln_sample_kernel` | `DeadDirections/LnKernel.lean` | 371 |
| `prodGrad` | `DeadDirections/Quotient.lean` | 43 |
| `prodMap` | `DeadDirections/Quotient.lean` | 32 |
| `prodMap_gauge_invariant` | `DeadDirections/Quotient.lean` | 36 |
| `prodMap_hasDerivAt` | `DeadDirections/Quotient.lean` | 48 |
| `quadBlock_iterate` | `DeadDirections/SwigluChannel.lean` | 337 |
| `quad_block_compounds` | `DeadDirections/BridgeComposition.lean` | 304 |
| `quad_rate_ne_additive` | `DeadDirections/BridgeComposition.lean` | 316 |
| `quadform_eigen` | `DeadDirections/SpectrumCount.lean` | 167 |
| `quadform_entrywise_bound` | `DeadDirections/SigmaMin.lean` | 455 |
| `quotient_F_vertical` | `DeadDirections/Quotient.lean` | 71 |
| `quotient_F_vertical_quadform` | `DeadDirections/Quotient.lean` | 83 |
| `quotient_K_invariant` | `DeadDirections/Quotient.lean` | 91 |
| `quotient_noise_variance` | `DeadDirections/QuotientNoise.lean` | 53 |
| `quotient_noise_vertical_uncorrelated` | `DeadDirections/QuotientNoise.lean` | 69 |
| `quotient_rate_matrix` | `DeadDirections/MatrixQuotient.lean` | 717 |
| `quotient_rate_model` | `DeadDirections/Quotient.lean` | 108 |
| `rectChain_fst` | `DeadDirections/DeepLinearBridge.lean` | 455 |
| `rectLayer` | `DeadDirections/DeepLinearBridge.lean` | 441 |
| `rect_backward_rate` | `DeadDirections/DeepLinearBridge.lean` | 489 |
| `rect_dead_ladder` | `DeadDirections/DeepLinearBridge.lean` | 471 |
| `rect_nondead_invariant` | `DeadDirections/DeepLinearBridge.lean` | 480 |
| `reluDeriv` | `DeadDirections/RotNegative.lean` | 41 |
| `relu_backward_hasDerivAt` | `DeadDirections/ReluChannel.lean` | 192 |
| `relu_chain_eq` | `DeadDirections/ReluChannel.lean` | 45 |
| `relu_chain_hasDerivAt` | `DeadDirections/ReluChannel.lean` | 160 |
| `relu_channel_ag_product` | `DeadDirections/ReluChannel.lean` | 265 |
| `relu_channel_backward_moment` | `DeadDirections/ReluChannel.lean` | 248 |
| `relu_channel_hasLeadingRate` | `DeadDirections/ReluChannel.lean` | 132 |
| `relu_channel_moment` | `DeadDirections/ReluChannel.lean` | 116 |
| `relu_two_channel_dead_lt_live` | `DeadDirections/ReluChannel.lean` | 301 |
| `renormExp_one` | `DeadDirections/NuFrozen.lean` | 440 |
| `renormVar_odd_gt` | `DeadDirections/NuInequality.lean` | 584 |
| `renormVar_one` | `DeadDirections/NuFrozen.lean` | 462 |
| `renormVar_riccati` | `DeadDirections/NuInequality.lean` | 208 |
| `resGModel` | `DeadDirections/BridgeComposition.lean` | 637 |
| `res_all_hasLeadingRate` | `DeadDirections/BridgeComposition.lean` | 579 |
| `res_block_kdist` | `DeadDirections/BridgeComposition.lean` | 603 |
| `res_ff_kdist` | `DeadDirections/BridgeComposition.lean` | 570 |
| `res_lambda_min_slice` | `DeadDirections/BridgeComposition.lean` | 647 |
| `residual_chain_sq_sum_ge` | `DeadDirections/SigmaMin.lean` | 769 |
| `residual_moment_product` | `DeadDirections/LnFiniteT.lean` | 388 |
| `residual_sq_sum_ge` | `DeadDirections/SigmaMin.lean` | 751 |
| `rmsNorm` | `DeadDirections/LnKernel.lean` | 216 |
| `rmsNorm_reading_single` | `DeadDirections/LnKernel.lean` | 247 |
| `rmsnorm_no_kernel` | `DeadDirections/LnKernel.lean` | 277 |
| `rmsnorm_witness_input_posdef` | `DeadDirections/LnKernel.lean` | 320 |
| `rotBasis` | `DeadDirections/Cochran.lean` | 319 |
| `rotBasis_zero` | `DeadDirections/Cochran.lean` | 323 |
| `rotSigma` | `DeadDirections/Cochran.lean` | 124 |
| `rotU` | `DeadDirections/RotNegative.lean` | 32 |
| `rotated_backward_rate` | `DeadDirections/DeepLinearBridge.lean` | 677 |
| `rotated_canonical_rates_differ` | `DeadDirections/RotNegative.lean` | 129 |
| `rotated_hasLeadingRate` | `DeadDirections/DeepLinearBridge.lean` | 693 |
| `rotated_pairing` | `DeadDirections/DeepLinearBridge.lean` | 655 |
| `rotated_rate_collapse` | `DeadDirections/RotNegative.lean` | 87 |
| `route_moment_floor_wins` | `DeadDirections/AttnBridge.lean` | 184 |
| `route_moment_tie` | `DeadDirections/AttnBridge.lean` | 159 |
| `route_moment_vo_wins` | `DeadDirections/AttnBridge.lean` | 138 |
| `route_noncancellation_ae` | `DeadDirections/AttnRoutes.lean` | 312 |
| `route_noncancellation_ae_concrete` | `DeadDirections/AttnRoutes.lean` | 464 |
| `route_noncancellation_witness` | `DeadDirections/AttnRoutes.lean` | 301 |
| `sample_form_eq_N_mul_gram` | `DeadDirections/SampleGram.lean` | 30 |
| `sample_form_ge_of_gram_ge` | `DeadDirections/SampleGram.lean` | 40 |
| `scaled_ratio_invariant` | `DeadDirections/NuFrozen.lean` | 359 |
| `schur_dead_lower` | `DeadDirections/SigmaMin.lean` | 308 |
| `score_bilinear` | `DeadDirections/AttnBridge.lean` | 37 |
| `seg_sq_hasLeadingRate` | `DeadDirections/BridgeComposition.lean` | 494 |
| `selection_rule_assembled` | `DeadDirections/SelectionAssembly.lean` | 185 |
| `selection_rule_tangential_lower` | `DeadDirections/SigmaMin.lean` | 617 |
| `selection_rule_transversal_lower` | `DeadDirections/SigmaMin.lean` | 598 |
| `sigma0` | `DeadDirections/Cochran.lean` | 267 |
| `sigma0_eq_paper_form` | `DeadDirections/Cochran.lean` | 273 |
| `sigma0_eq_rotSigma` | `DeadDirections/Cochran.lean` | 332 |
| `sigmaMaxSq` | `DeadDirections/SigmaMin.lean` | 226 |
| `sigmaMinSq` | `DeadDirections/SigmaMin.lean` | 175 |
| `sigmaMinSq_canonical` | `DeadDirections/SigmaMin.lean` | 385 |
| `sigmaMinSq_mul_le` | `DeadDirections/SigmaMin.lean` | 245 |
| `sigmaMinSq_pos_of_unit` | `DeadDirections/SigmaMin.lean` | 260 |
| `sigmaMinSq_rotated_canonical` | `DeadDirections/SigmaMin.lean` | 434 |
| `sigmoid` | `DeadDirections/SwigluChannel.lean` | 29 |
| `singular_value_count_of_block_bounds` | `DeadDirections/SpectrumCount.lean` | 349 |
| `slice_isometric` | `DeadDirections/MatrixQuotient.lean` | 1043 |
| `slice_rlct_product_slope` | `DeadDirections/SliceRlctProduct.lean` | 236 |
| `slice_rlct_slope` | `DeadDirections/SliceRlct.lean` | 96 |
| `small_subspace_dim_le` | `DeadDirections/SpectrumCount.lean` | 31 |
| `smoothChain_abs_le` | `DeadDirections/SmoothChain.lean` | 108 |
| `smoothChain_sub_le` | `DeadDirections/SmoothChain.lean` | 175 |
| `smooth_chain_ag_product` | `DeadDirections/SmoothChain.lean` | 990 |
| `smooth_chain_backward_hasLeadingRate` | `DeadDirections/SmoothChain.lean` | 755 |
| `smooth_chain_hasLeadingRate` | `DeadDirections/SmoothChain.lean` | 291 |
| `smooth_chain_slope` | `DeadDirections/SmoothChain.lean` | 468 |
| `smooth_channel_hasLeadingRate` | `DeadDirections/ReluChannel.lean` | 340 |
| `smooth_two_channel_dead_eventually_lt` | `DeadDirections/SmoothChain.lean` | 1023 |
| `softmaxN` | `DeadDirections/SoftmaxN.lean` | 30 |
| `softmaxN_hasDerivAt_dir` | `DeadDirections/SoftmaxN.lean` | 141 |
| `softmaxN_jacobian_const` | `DeadDirections/SoftmaxN.lean` | 190 |
| `softmaxN_uniform_jacobian` | `DeadDirections/SoftmaxN.lean` | 208 |
| `spectrum_count_form` | `DeadDirections/SpectrumCount.lean` | 65 |
| `sq_sum_le_sigmaMaxSq` | `DeadDirections/SigmaMin.lean` | 236 |
| `sublevel_normalFormMulti_eq_image` | `DeadDirections/SliceRlctProduct.lean` | 306 |
| `sublevel_normalForm_eq_image` | `DeadDirections/SliceRlctProduct.lean` | 58 |
| `sum_ginv_mul_lnLike` | `DeadDirections/LnKernel.lean` | 74 |
| `surfCurvAt` | `DeadDirections/CurvatureInstance.lean` | 42 |
| `swigluDead_eq` | `DeadDirections/SwigluChannel.lean` | 99 |
| `swigluDead_sub_le` | `DeadDirections/SwigluChannel.lean` | 107 |
| `swiglu_channel_hasLeadingRate` | `DeadDirections/SwigluChannel.lean` | 168 |
| `t2_plateau_regime` | `DeadDirections/LnFiniteT.lean` | 91 |
| `tangential_floor_eventually` | `DeadDirections/SelectionAssembly.lean` | 135 |
| `tangential_moment_expansion` | `DeadDirections/FisherDecay.lean` | 604 |
| `task_expansion_head_bounds` | `DeadDirections/DeepLinearBridge.lean` | 592 |
| `task_expansion_inherit_bounds` | `DeadDirections/DeepLinearBridge.lean` | 615 |
| `task_expansion_perturbed` | `DeadDirections/SigmaMin.lean` | 657 |
| `tendsto_log_div_log_of_rpow` | `DeadDirections/SliceRlct.lean` | 69 |
| `tied_routes_coeff` | `DeadDirections/BridgeComposition.lean` | 620 |
| `tiltC1_nonneg` | `DeadDirections/NuInequality.lean` | 505 |
| `tilt_gap_eq` | `DeadDirections/NuInequality.lean` | 305 |
| `tilt_gap_integral_nonneg` | `DeadDirections/NuInequality.lean` | 428 |
| `tilt_stein` | `DeadDirections/NuInequality.lean` | 143 |
| `tube_volume_pow` | `DeadDirections/CurvatureInstance.lean` | 277 |
| `tube_weight_sandwich` | `DeadDirections/CurvatureInstance.lean` | 591 |
| `twMu0_hasDerivAt_fst` | `DeadDirections/TwistedMap.lean` | 91 |
| `twMu1_hasDerivAt_snd` | `DeadDirections/TwistedMap.lean` | 135 |
| `twRho_hasDerivAt_fst` | `DeadDirections/TwistedMap.lean` | 55 |
| `twisted_density_zero_iff` | `DeadDirections/TwistedMap.lean` | 188 |
| `twisted_jacobian_det` | `DeadDirections/TwistedMap.lean` | 161 |
| `twisted_kl` | `DeadDirections/TwistedMap.lean` | 46 |
| `twisted_polydisc_scaling` | `DeadDirections/VolumeMultiG.lean` | 76 |
| `twisted_sqrt_det_fisher` | `DeadDirections/TwistedMap.lean` | 181 |
| `twisted_unit_constant_pos` | `DeadDirections/VolumeMultiG.lean` | 116 |
| `twisted_vs_factorised` | `DeadDirections/VolumeMultiG.lean` | 164 |
| `two_by_two_eigvec_tilt` | `DeadDirections/SigmaMin.lean` | 683 |
| `vecKron_rankOne` | `DeadDirections/KfacLift.lean` | 152 |
| `voAmp_floor` | `DeadDirections/AttnRoutes.lean` | 146 |
| `volume_crossing_distinct` | `DeadDirections/MultiCrossing.lean` | 365 |
| `volume_crossing_tied` | `DeadDirections/MultiCrossing.lean` | 137 |
| `volume_crossing_tied3` | `DeadDirections/MultiCrossing.lean` | 715 |
| `volume_crossing_tied_general` | `DeadDirections/MultiCrossingGeneral.lean` | 339 |
| `volume_cubeHyper` | `DeadDirections/MultiCrossingGeneral.lean` | 170 |
| `volume_multi_slope` | `DeadDirections/SliceRlctProduct.lean` | 542 |
| `volume_power_hyperbola` | `DeadDirections/MultiCrossing.lean` | 343 |
| `volume_sublevel_normalForm` | `DeadDirections/SliceRlctProduct.lean` | 126 |
| `volume_sublevel_normalFormMulti` | `DeadDirections/SliceRlctProduct.lean` | 391 |
| `volume_sublevel_pow` | `DeadDirections/SliceRlct.lean` | 60 |
| `weighted_slice_recursion` | `DeadDirections/MultiCrossingGeneral.lean` | 607 |
| `weighted_slice_rlct_slope` | `DeadDirections/MultiCrossingGeneral.lean` | 566 |
| `weighted_unitCube` | `DeadDirections/MultiCrossingGeneral.lean` | 661 |
| `weighted_volume_cubeHyper` | `DeadDirections/MultiCrossingGeneral.lean` | 678 |
| `weighted_volume_sublevel_pow` | `DeadDirections/MultiCrossingGeneral.lean` | 547 |
| `width_condition_failure` | `DeadDirections/SpectrumCount.lean` | 102 |
| `width_one_chain_slope` | `DeadDirections/DeterminantalInstances.lean` | 35 |
| `width_one_chain_volume` | `DeadDirections/DeterminantalInstances.lean` | 28 |
| `witness_mask` | `DeadDirections/RotNegative.lean` | 46 |
| `znorm_hasDerivAt_dir` | `DeadDirections/LnJacobian.lean` | 69 |
