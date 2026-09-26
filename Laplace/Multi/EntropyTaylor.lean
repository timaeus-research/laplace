/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.MixturePathEnergy

/-!
# The entropy of a density `1 + tg + O(t²)` is quadratic

The scalar Taylor bound `|klFun (1 + u) − u²/2| ≤ 4|u|³` for `|u| ≤ 1/2`
(`abs_klFun_one_add_sub_le`) integrates: if a family of densities satisfies
`q_t = 1 + t g + e_t` with `|e_t| ≤ K t²` (a.e., for `|t| ≤ δ`) and `g` bounded, then

  `(∫ klFun (q_t) dν) / t² → (∫ g²) / 2`  as `t → 0`      (`tendsto_integral_klFun_div_sq`).

Since `KL(q_t ν ‖ ν) = ∫ klFun(q_t) dν` for a probability density, this is the reusable engine
behind the separate quadratic expansions of the fibre and marginal residuals: the information of
any smooth one-parameter family of densities is, to leading order, half the squared `L²`-norm of
its score.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Scalar

/-- **Taylor bound for `klFun` at `1`**: `|klFun (1 + u) − u²/2| ≤ 4|u|³` for `|u| ≤ 1/2`. -/
theorem abs_klFun_one_add_sub_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |klFun (1 + u) - u ^ 2 / 2| ≤ 4 * |u| ^ 3 := by
  have hu1 : |-u| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hu1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_one, Nat.cast_zero,
    div_one, Nat.cast_one, sub_neg_eq_add, abs_neg] at h
  have hden : 1 / 2 ≤ 1 - |u| := by linarith
  have hε : |Real.log (1 + u) - u + u ^ 2 / 2| ≤ 2 * |u| ^ 3 := by
    have e : Real.log (1 + u) - u + u ^ 2 / 2 = -u + (-u) ^ (1 + 1) / (1 + 1) + Real.log (1 +
      u) := by
      ring
    rw [e]
    refine h.trans ?_
    have h3 : |u| ^ (2 + 1) = |u| ^ 3 := by norm_num
    rw [h3, div_le_iff₀ (by linarith)]
    have hp := pow_nonneg (abs_nonneg u) 3
    nlinarith [mul_nonneg hp (by linarith : (0 : ℝ) ≤ 1 - 2 * |u|)]
  have hkl : klFun (1 + u) - u ^ 2 / 2 =
      (1 + u) * (Real.log (1 + u) - u + u ^ 2 / 2) - u ^ 3 / 2 := by
    unfold klFun
    ring
  rw [hkl]
  have h1u : |1 + u| ≤ 3 / 2 := by
    rw [abs_le] at hu ⊢
    constructor <;> linarith [hu.1, hu.2]
  calc |(1 + u) * (Real.log (1 + u) - u + u ^ 2 / 2) - u ^ 3 / 2|
      ≤ |1 + u| * |Real.log (1 + u) - u + u ^ 2 / 2| + |u ^ 3 / 2| := by
        rw [← abs_mul]
        exact abs_sub _ _
    _ ≤ 3 / 2 * (2 * |u| ^ 3) + |u| ^ 3 / 2 := by
        gcongr
        rw [abs_div, abs_pow]
        norm_num
    _ ≤ 4 * |u| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg u) 3]

end Scalar

section Density

variable {X : Type*} [MeasurableSpace X] [Nonempty X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- **The entropy of `1 + tg + O(t²)` is quadratic**: `(∫ klFun (q_t) dν)/t² → (∫ g²)/2`. -/
theorem tendsto_integral_klFun_div_sq {q : ℝ → X → ℝ} {g : X → ℝ} {e : ℝ → X → ℝ}
    (hg : Bdd g) (hq : ∀ t, ∀ᵐ x ∂ν, q t x = 1 + t * g x + e t x) {δ K : ℝ} (hδ : 0 < δ)
    (hK : 0 ≤ K) (he : ∀ t, |t| ≤ δ → ∀ᵐ x ∂ν, |e t x| ≤ K * t ^ 2)
    (hqm : ∀ t, AEStronglyMeasurable (q t) ν) :
    Tendsto (fun t ↦ (∫ x, klFun (q t x) ∂ν) / t ^ 2) (𝓝[≠] 0) (𝓝 ((∫ x, g x ^ 2 ∂ν) / 2)) := by
  obtain ⟨hgm, B, hB⟩ := hg
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary X))
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = B * K + K ^ 2 / 2 + 4 * (B + K) ^ 3 := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  obtain ⟨η, hη0, hηδ, hη1, hηBK⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ η ≤ 1 ∧ η * (B + K) ≤ 1 / 2 := by
    refine ⟨min δ (min 1 (1 / (2 * (B + K + 1)))), by positivity, min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), ?_⟩
    have h1 : min δ (min 1 (1 / (2 * (B + K + 1)))) ≤ 1 / (2 * (B + K + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have h2 : 0 ≤ min δ (min 1 (1 / (2 * (B + K + 1)))) := by positivity
    calc min δ (min 1 (1 / (2 * (B + K + 1)))) * (B + K)
        ≤ 1 / (2 * (B + K + 1)) * (B + K) := by gcongr
      _ ≤ 1 / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
          nlinarith
  have hpt : ∀ t, |t| ≤ η → ∀ᵐ x ∂ν, |klFun (q t x) - t ^ 2 / 2 * g x ^ 2| ≤ C * |t| ^ 3 := by
    intro t ht
    filter_upwards [hq t, he t (ht.trans hηδ)] with x hx hex
    have hgx := hB x
    have ht1 : |t| ≤ 1 := ht.trans hη1
    have ht0 : 0 ≤ |t| := abs_nonneg t
    have ht2 : t ^ 2 ≤ |t| := by
      rw [← sq_abs]
      nlinarith
    have hu : |t * g x + e t x| ≤ |t| * (B + K) := by
      calc |t * g x + e t x| ≤ |t| * |g x| + |e t x| := by
            rw [← abs_mul]
            exact abs_add_le _ _
        _ ≤ |t| * B + K * t ^ 2 := by gcongr
        _ ≤ |t| * B + K * |t| := by gcongr
        _ = |t| * (B + K) := by ring
    have hu2 : |t * g x + e t x| ≤ 1 / 2 := by
      refine hu.trans ?_
      calc |t| * (B + K) ≤ η * (B + K) := by gcongr
        _ ≤ 1 / 2 := hηBK
    have hkl := abs_klFun_one_add_sub_le hu2
    rw [hx, add_assoc]
    have e2 : klFun (1 + (t * g x + e t x)) - t ^ 2 / 2 * g x ^ 2 =
        (klFun (1 + (t * g x + e t x)) - (t * g x + e t x) ^ 2 / 2) +
          (t * g x * e t x + e t x ^ 2 / 2) := by ring
    rw [e2]
    have h3 : |t * g x * e t x + e t x ^ 2 / 2| ≤ B * K * |t| ^ 3 + K ^ 2 / 2 * |t| ^ 3 := by
      have hte : |t * g x * e t x| ≤ B * K * |t| ^ 3 := by
        rw [abs_mul, abs_mul]
        calc |t| * |g x| * |e t x| ≤ |t| * B * (K * t ^ 2) := by gcongr
          _ = B * K * (|t| * t ^ 2) := by ring
          _ = B * K * |t| ^ 3 := by rw [← sq_abs]; ring
      have hee : |e t x ^ 2 / 2| ≤ K ^ 2 / 2 * |t| ^ 3 := by
        rw [abs_div, abs_pow, abs_two]
        have h4 : |e t x| ^ 2 ≤ (K * t ^ 2) ^ 2 := by
          exact pow_le_pow_left₀ (abs_nonneg _) hex 2
        have h5 : (K * t ^ 2) ^ 2 ≤ K ^ 2 * |t| ^ 3 := by
          rw [mul_pow, ← sq_abs t, ← pow_mul]
          have : |t| ^ (2 * 2) ≤ |t| ^ 3 := pow_le_pow_of_le_one ht0 ht1 (by norm_num)
          nlinarith [sq_nonneg K]
        calc |e t x| ^ 2 / 2 ≤ (K * t ^ 2) ^ 2 / 2 := by gcongr
          _ ≤ K ^ 2 * |t| ^ 3 / 2 := by gcongr
          _ = K ^ 2 / 2 * |t| ^ 3 := by ring
      exact (abs_add_le _ _).trans (add_le_add hte hee)
    have h4 : 4 * |t * g x + e t x| ^ 3 ≤ 4 * (B + K) ^ 3 * |t| ^ 3 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hu 3
      rw [mul_pow] at this
      nlinarith
    calc |(klFun (1 + (t * g x + e t x)) - (t * g x + e t x) ^ 2 / 2) +
          (t * g x * e t x + e t x ^ 2 / 2)|
        ≤ 4 * |t * g x + e t x| ^ 3 + (B * K * |t| ^ 3 + K ^ 2 / 2 * |t| ^ 3) :=
          (abs_add_le _ _).trans (add_le_add hkl h3)
      _ ≤ 4 * (B + K) ^ 3 * |t| ^ 3 + (B * K * |t| ^ 3 + K ^ 2 / 2 * |t| ^ 3) := by gcongr
      _ = C * |t| ^ 3 := by rw [hC]; ring
  have hg2 : Integrable (fun x ↦ g x ^ 2) ν :=
    integrable_of_bdd_prob ν (Bdd.mul ⟨hgm, B, hB⟩ ⟨hgm, B, hB⟩) |>.congr
      (Eventually.of_forall fun x ↦ by simp [sq])
  have hint : ∀ t, |t| ≤ η → Integrable (fun x ↦ klFun (q t x)) ν := by
    intro t ht
    refine Integrable.of_bound (measurable_klFun.comp_aemeasurable (hqm t).aemeasurable
      |>.aestronglyMeasurable) (B ^ 2 / 2 + C) ?_
    filter_upwards [hpt t ht] with x hx
    have ht1 : |t| ≤ 1 := ht.trans hη1
    have hgx := hB x
    rw [Real.norm_eq_abs]
    have h1 : |t ^ 2 / 2 * g x ^ 2| ≤ B ^ 2 / 2 := by
      rw [abs_mul, abs_div, abs_two, abs_pow, abs_pow, sq_abs t]
      have : t ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
      have : |g x| ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hgx 2
      nlinarith [sq_nonneg t, sq_nonneg (|g x|)]
    have h2 : C * |t| ^ 3 ≤ C := by
      have : |t| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg t) ht1
      nlinarith
    calc |klFun (q t x)| = |(klFun (q t x) - t ^ 2 / 2 * g x ^ 2) + t ^ 2 / 2 * g x ^ 2| := by
          ring_nf
      _ ≤ |klFun (q t x) - t ^ 2 / 2 * g x ^ 2| + |t ^ 2 / 2 * g x ^ 2| := abs_add_le _ _
      _ ≤ C + B ^ 2 / 2 := add_le_add (hx.trans h2) h1
      _ = B ^ 2 / 2 + C := by ring
  have hkey : ∀ t, |t| ≤ η → t ≠ 0 →
      |(∫ x, klFun (q t x) ∂ν) / t ^ 2 - (∫ x, g x ^ 2 ∂ν) / 2| ≤ C * |t| := by
    intro t ht ht0
    have hdiff : |(∫ x, klFun (q t x) ∂ν) - t ^ 2 / 2 * ∫ x, g x ^ 2 ∂ν| ≤ C * |t| ^ 3 := by
      rw [← integral_const_mul, ← integral_sub (hint t ht) (hg2.const_mul _), ← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le (integrable_const (C * |t| ^ 3)) ?_).trans ?_
      · filter_upwards [hpt t ht] with x hx
        rw [Real.norm_eq_abs]
        exact hx
      · rw [integral_const, probReal_univ, one_smul]
    have ht2 : 0 < t ^ 2 := by positivity
    rw [div_sub_div _ _ ht2.ne' two_ne_zero, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t
      ^ 2 * 2),
      div_le_iff₀ (by positivity)]
    calc |(∫ x, klFun (q t x) ∂ν) * 2 - t ^ 2 * ∫ x, g x ^ 2 ∂ν|
        = 2 * |(∫ x, klFun (q t x) ∂ν) - t ^ 2 / 2 * ∫ x, g x ^ 2 ∂ν| := by
          rw [← abs_two, ← abs_mul]
          congr 1
          ring
      _ ≤ 2 * (C * |t| ^ 3) := by gcongr
      _ = C * |t| * (t ^ 2 * 2) := by rw [← sq_abs t]; ring
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min η (ε / (C + 1)), lt_min hη0 (by positivity), fun t ht hdist ↦ ?_⟩
  rw [Real.dist_eq, sub_zero] at hdist
  rw [Real.dist_eq]
  have ht1 : |t| ≤ η := (lt_min_iff.1 hdist).1.le
  have ht2 : |t| < ε / (C + 1) := (lt_min_iff.1 hdist).2
  refine lt_of_le_of_lt (hkey t ht1 ht) ?_
  calc C * |t| ≤ (C + 1) * |t| := by gcongr; linarith
    _ < (C + 1) * (ε / (C + 1)) := by gcongr
    _ = ε := by field_simp

end Density

end Laplace.Multi
