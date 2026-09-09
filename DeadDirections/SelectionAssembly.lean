/-
  The assembled Fisher matrix: the selection rule from the score
  expansions.

  The three entry theorems give the transversal entry F₁₁ its leading
  rate 2(k−1) (fisher_expansion_of_score_expansion), each cross entry
  F₁α its expansion k·t^{k−1}·E[ab_α] + O(t^k)
  (cross_moment_expansion), and each tangential entry
  F_αβ = g_αβ + O(t) (tangential_moment_expansion). This module takes
  those conclusions as inputs and assembles the selection rule: the
  squared cross entries sum to a leading rate 2(k−1), the tangential
  block keeps a floor λ/2 once the O(t) perturbation is small, and
  the two-block sandwich puts the variational minimum of the whole
  Fisher form between F₁₁/2 and F₁₁, the transversal rate. The margin
  2k²Σ_α E[ab_α]²/(k²E[a²]) < λ/2 is the graded non-degeneracy
  hypothesis of the theorem in the form the Schur argument consumes.
-/
import DeadDirections.SigmaMin
import DeadDirections.DagPathRates

namespace DeadDirections

open Filter Topology

section RateLemmas

/-- An expansion F = c·t^p + O(t^{p+1}) squares to leading rate 2p
    with coefficient c². -/
theorem hasLeadingRate_sq_of_expansion {F : ℝ → ℝ} {p : ℕ} {c M : ℝ}
    (hM : 0 ≤ M)
    (hF : ∀ᶠ t in 𝓝[>] (0:ℝ), |F t - c * t ^ p| ≤ M * t ^ (p + 1)) :
    HasLeadingRate (fun t => F t ^ 2) (2 * p) (c ^ 2) := by
  have hwin : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ t ≤ 1 := by
    filter_upwards [eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds
        (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with t ht0 ht1
    exact ⟨ht0, ht1.le⟩
  apply hasLeadingRate_of_expansion
    (R := fun t => (F t - c * t ^ p) * (F t + c * t ^ p))
    (M := M * (2 * |c| + M))
  · filter_upwards [] with t
    ring
  · filter_upwards [hF, hwin] with t hFt ⟨ht0, ht1⟩
    have htp : 0 < t ^ p := pow_pos ht0 p
    have hbound : |F t + c * t ^ p| ≤ 2 * |c| * t ^ p + M * t ^ (p + 1) := by
      have h1 : |F t| ≤ |c| * t ^ p + M * t ^ (p + 1) := by
        have := abs_sub_abs_le_abs_sub (F t) (c * t ^ p)
        rw [abs_mul, abs_of_pos htp] at this
        linarith
      calc |F t + c * t ^ p| ≤ |F t| + |c * t ^ p| := abs_add_le _ _
        _ = |F t| + |c| * t ^ p := by rw [abs_mul, abs_of_pos htp]
        _ ≤ 2 * |c| * t ^ p + M * t ^ (p + 1) := by linarith
    have htp1 : t ^ (p + 1) ≤ t ^ p := pow_le_pow_of_le_one ht0.le ht1 (by omega)
    rw [abs_mul]
    calc |F t - c * t ^ p| * |F t + c * t ^ p|
        ≤ (M * t ^ (p + 1)) * (2 * |c| * t ^ p + M * t ^ (p + 1)) :=
          mul_le_mul hFt hbound (abs_nonneg _) (by positivity)
      _ ≤ (M * t ^ (p + 1)) * (2 * |c| * t ^ p + M * t ^ p) := by
          gcongr
      _ = M * (2 * |c| + M) * (t ^ (p + 1) * t ^ p) := by ring
      _ = M * (2 * |c| + M) * t ^ (2 * p + 1) := by ring

/-- A finite sum of leading rates at one common rate carries that rate
    with the summed coefficient. -/
theorem hasLeadingRate_sum_same {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ)
    (p : ℕ) (a : ι → ℝ) (hF : ∀ i ∈ s, HasLeadingRate (F i) p (a i)) :
    HasLeadingRate (fun t => ∑ i ∈ s, F i t) p (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (tendsto_const_nhds (X := ℝ) (x := (0:ℝ))
      (f := 𝓝[>] (0:ℝ))).congr fun t => by simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have h1 := hF i (Finset.mem_insert_self i s)
    have h2 := ih fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have := h1.add_of_eq h2
    refine this.congr fun t => ?_
    simp only [Finset.sum_insert hi]

end RateLemmas

section Assembly

variable {n : ℕ}

/-- The two-block sandwich with an eventual live floor. -/
theorem block_lambda_min_sandwich_ev {p q : ℕ} (hpq : p < q)
    {g B c : ℝ → ℝ} {d a β : ℝ}
    (hg : HasLeadingRate g q d) (hd : 0 < d)
    (hc : HasLeadingRate c p a)
    (hB : HasLeadingRate B (p + q) β) (hcond : 2 * β / d < a)
    (b : ℝ → Fin (n+1) → ℝ) (hb : ∀ t, ∑ i, b t i ^ 2 = B t)
    (Qlive : ℝ → (Fin (n+1) → ℝ) → ℝ)
    (hlive : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ w, c t * ∑ i, w i ^ 2 ≤ Qlive t w) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ (v₀ : ℝ) (w : Fin (n+1) → ℝ),
      (g t / 2) * (v₀ ^ 2 + ∑ i, w i ^ 2)
        ≤ g t * v₀ ^ 2 + 2 * v₀ * (∑ i, b t i * w i) + Qlive t w := by
  have hBg : HasLeadingRate (fun t => B t / g t) p (β / d) := by
    have h := hB.div hg hd (by omega)
    rwa [show p + q - q = p from by omega] at h
  have h2 : HasLeadingRate (fun t => -2 * (B t / g t)) p (-2 * (β / d)) :=
    HasLeadingRate.const_mul hBg (-2)
  have hsum : HasLeadingRate (fun t => c t + -2 * (B t / g t)) p
      (a + -2 * (β / d)) :=
    hc.add_of_eq h2
  have hhalf : HasLeadingRate (fun t => g t / 2) q (1 / 2 * d) := by
    have h := HasLeadingRate.const_mul hg (1 / 2)
    refine h.congr fun t => ?_
    ring
  have hmargin : HasLeadingRate
      (fun t => c t + -2 * (B t / g t) - g t / 2) p (a + -2 * (β / d)) :=
    hsum.sub_of_lt hhalf hpq
  have hpos : 0 < a + -2 * (β / d) := by
    have : 2 * β / d = 2 * (β / d) := by ring
    linarith
  filter_upwards [hmargin.eventually_pos hpos, hg.eventually_pos hd, hlive]
    with t hm hgt hlivet
  intro v₀ w
  have hlow := block_form_lower_weighted (n := n) hgt (b t) (Qlive t)
    hlivet v₀ w
  rw [hb t] at hlow
  have hW0 : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcoef : g t / 2 ≤ c t - 2 * B t / g t := by
    have e : 2 * B t / g t = 2 * (B t / g t) := by ring
    linarith
  have hmono : (g t / 2) * ∑ i, w i ^ 2
      ≤ (c t - 2 * B t / g t) * ∑ i, w i ^ 2 :=
    mul_le_mul_of_nonneg_right hcoef hW0
  linarith

/-- The tangential block keeps half its Gram floor once the O(t)
    perturbation of its entries is small. -/
theorem tangential_floor_eventually (F : ℝ → Fin (n+1) → Fin (n+1) → ℝ)
    (g : Fin (n+1) → Fin (n+1) → ℝ) {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 < lam)
    (htan : ∀ α β, ∀ᶠ t in 𝓝[>] (0:ℝ), |F t α β - g α β| ≤ C * t)
    (hg : ∀ w : Fin (n+1) → ℝ, lam * ∑ i, w i ^ 2 ≤ ∑ α, ∑ β, g α β * w α * w β) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ w : Fin (n+1) → ℝ,
      (lam / 2) * ∑ i, w i ^ 2 ≤ ∑ α, ∑ β, F t α β * w α * w β := by
  have hall : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ α β, |F t α β - g α β| ≤ C * t := by
    rw [Filter.eventually_all]
    intro α
    rw [Filter.eventually_all]
    exact htan α
  have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), C * t * ((n:ℝ) + 1) ≤ lam / 2 := by
    have hδ : (0:ℝ) < lam / 2 / (C * ((n:ℝ) + 1) + 1) := by positivity
    filter_upwards [eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hδ)] with t ht0 htδ
    have ht0' : (0:ℝ) < t := ht0
    have h1 : C * ((n:ℝ) + 1) ≤ C * ((n:ℝ) + 1) + 1 := by linarith
    calc C * t * ((n:ℝ) + 1) = t * (C * ((n:ℝ) + 1)) := by ring
      _ ≤ t * (C * ((n:ℝ) + 1) + 1) := mul_le_mul_of_nonneg_left h1 ht0'.le
      _ ≤ lam / 2 / (C * ((n:ℝ) + 1) + 1) * (C * ((n:ℝ) + 1) + 1) :=
          mul_le_mul_of_nonneg_right htδ.le (by positivity)
      _ = lam / 2 := by field_simp
  filter_upwards [hall, hsmall, eventually_mem_nhdsWithin] with t hallt hsmallt ht0
  intro w
  have ht0' : (0:ℝ) < t := ht0
  have hE := quadform_entrywise_bound (fun α β => F t α β - g α β)
    (ε := C * t) (fun α β => hallt α β) w
  have hsplit : ∑ α, ∑ β, F t α β * w α * w β
      = ∑ α, ∑ β, g α β * w α * w β
        + ∑ α, ∑ β, (F t α β - g α β) * w α * w β := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  rw [hsplit]
  have hW0 : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hE1 := (abs_le.mp hE).1
  have hpert : C * t * ((n:ℝ) + 1) * ∑ i, w i ^ 2 ≤ lam / 2 * ∑ i, w i ^ 2 :=
    mul_le_mul_of_nonneg_right hsmallt hW0
  have hgw := hg w
  nlinarith [hE1, hpert, hgw]

/-- thm:selection_rule (a) from the score expansions: with the
    transversal entry at leading rate 2(k−1) and coefficient d > 0,
    the cross entries k·t^{k−1}·e_α + O(t^k), the tangential entries
    g_αβ + O(t) with Gram floor λ, and the graded non-degeneracy
    margin 2k²Σe_α²/d < λ/2, the Fisher form is eventually at least
    (F₁₁/2)·‖v‖² at every (v₀, w): the variational minimum sits
    between F₁₁/2 and F₁₁, the transversal rate. -/
theorem selection_rule_assembled {k : ℕ} (hk : 2 ≤ k)
    (F11 : ℝ → ℝ) {d : ℝ} (hF11 : HasLeadingRate F11 (2 * (k - 1)) d) (hd : 0 < d)
    (F1 : ℝ → Fin (n+1) → ℝ) (e : Fin (n+1) → ℝ) {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hcross : ∀ α, ∀ᶠ t in 𝓝[>] (0:ℝ),
      |F1 t α - (k:ℝ) * e α * t ^ (k - 1)| ≤ C₁ * t ^ (k - 1 + 1))
    (F : ℝ → Fin (n+1) → Fin (n+1) → ℝ) (g : Fin (n+1) → Fin (n+1) → ℝ)
    {C₂ lam : ℝ} (hC₂ : 0 ≤ C₂) (hlam : 0 < lam)
    (htan : ∀ α β, ∀ᶠ t in 𝓝[>] (0:ℝ), |F t α β - g α β| ≤ C₂ * t)
    (hg : ∀ w : Fin (n+1) → ℝ, lam * ∑ i, w i ^ 2 ≤ ∑ α, ∑ β, g α β * w α * w β)
    (hmargin : 2 * ((k:ℝ) ^ 2 * ∑ α, e α ^ 2) / d < lam / 2) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ (v₀ : ℝ) (w : Fin (n+1) → ℝ),
      (F11 t / 2) * (v₀ ^ 2 + ∑ i, w i ^ 2)
        ≤ F11 t * v₀ ^ 2 + 2 * v₀ * (∑ α, F1 t α * w α)
          + ∑ α, ∑ β, F t α β * w α * w β := by
  -- the squared cross entries
  have hB : HasLeadingRate (fun t => ∑ α, F1 t α ^ 2) (0 + 2 * (k - 1))
      ((k:ℝ) ^ 2 * ∑ α, e α ^ 2) := by
    have h := hasLeadingRate_sum_same Finset.univ (fun α t => F1 t α ^ 2)
      (2 * (k - 1)) (fun α => ((k:ℝ) * e α) ^ 2)
      (fun α _ => hasLeadingRate_sq_of_expansion hC₁ (hcross α))
    rw [zero_add]
    have hcoef : ∑ α, ((k:ℝ) * e α) ^ 2 = (k:ℝ) ^ 2 * ∑ α, e α ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by ring
    rw [hcoef] at h
    exact h
  have hlive := tangential_floor_eventually F g hC₂ hlam htan hg
  exact block_lambda_min_sandwich_ev (by omega) hF11 hd
    (hasLeadingRate_const (lam / 2)) hB hmargin F1 (fun t => rfl)
    (fun t w => ∑ α, ∑ β, F t α β * w α * w β) hlive

end Assembly

end DeadDirections
