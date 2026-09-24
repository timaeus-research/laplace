/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PowerLogDominance

/-!
# Finite power–log assembly with lexicographic dominance and negligible terms

Astra's recommendation (`gpt_responses/review_endtoend_v1.md`, §5): normalise each term by
`t^{λ_p}/(log t)^{k_p}`; the dominant pair is the smallest `λ`, then the largest `k`; terms with a
certified limit at their own pair are negligible at a lexicographically smaller pair
(`tendsto_negligible_of_certified`), and the ratio of two finite sums converges to the ratio of
the summed dominant coefficients as soon as the dominant terms have limits and every other term
is `o(1)` at the dominant normalisation (`tendsto_sum_ratio_powLog`). No term outside the dominant
set needs a nonzero asymptotic description, and `tendsto_general` terms enter directly.
-/

open Filter Topology Real

namespace Laplace.Multi

/-- A kernel certified at `(λ, k)` is negligible at a lexicographically smaller `(λ₀, k₀)`. -/
theorem tendsto_negligible_of_certified {K : ℝ → ℝ} {lam lam₀ C : ℝ} {k k₀ : ℕ}
    (hlex : lam₀ < lam ∨ (lam₀ = lam ∧ k < k₀))
    (hK : Tendsto (fun t ↦ t ^ lam / log t ^ k * K t) atTop (𝓝 C)) :
    Tendsto (fun t ↦ t ^ lam₀ / log t ^ k₀ * K t) atTop (𝓝 0) := by
  have hq : Tendsto (fun t ↦ powLog lam (k : ℝ) t / powLog lam₀ (k₀ : ℝ) t) atTop (𝓝 0) := by
    refine tendsto_powLog_div_powLog ?_
    rcases hlex with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, by exact_mod_cast h2⟩
  have h2 := hK.mul hq
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  have ht0 : 0 < t := one_pos.trans ht
  have hlt : 0 < log t := Real.log_pos ht
  unfold powLog
  rw [Real.rpow_natCast, Real.rpow_natCast, Real.rpow_neg ht0.le, Real.rpow_neg ht0.le]
  have h1 : t ^ lam ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
  have h3 : t ^ lam₀ ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
  have h4 : log t ^ k ≠ 0 := pow_ne_zero _ hlt.ne'
  have h5 : log t ^ k₀ ≠ 0 := pow_ne_zero _ hlt.ne'
  field_simp

variable {ι : Type*} [Fintype ι]

/-- **Finite power–log assembly with negligible terms.** The dominant terms `S` have limits at the
normalisation `t^{λ₀}/(log t)^{k₀}`, every other term is `o(1)` there, and the dominant
denominator coefficient is nonzero. -/
theorem tendsto_sum_ratio_powLog {K Kφ : ι → ℝ → ℝ} {C J : ι → ℝ} {lam₀ : ℝ} {k₀ : ℕ}
    (S : Finset ι)
    (hK : ∀ i ∈ S, Tendsto (fun t ↦ t ^ lam₀ / log t ^ k₀ * K i t) atTop (𝓝 (C i)))
    (hKφ : ∀ i ∈ S, Tendsto (fun t ↦ t ^ lam₀ / log t ^ k₀ * Kφ i t) atTop (𝓝 (J i)))
    (hnK : ∀ i ∉ S, Tendsto (fun t ↦ t ^ lam₀ / log t ^ k₀ * K i t) atTop (𝓝 0))
    (hnKφ : ∀ i ∉ S, Tendsto (fun t ↦ t ^ lam₀ / log t ^ k₀ * Kφ i t) atTop (𝓝 0))
    (hpos : ∑ i ∈ S, C i ≠ 0) :
    Tendsto (fun t ↦ (∑ i, Kφ i t) / ∑ i, K i t) atTop (𝓝 ((∑ i ∈ S, J i) / ∑ i ∈ S, C i)) := by
  classical
  have hlimK : ∀ i, Tendsto (fun t ↦ t ^ lam₀ / log t ^ k₀ * K i t) atTop
      (𝓝 (if i ∈ S then C i else 0)) := fun i ↦ by
    by_cases hi : i ∈ S
    · rw [if_pos hi]; exact hK i hi
    · rw [if_neg hi]; exact hnK i hi
  have hlimKφ : ∀ i, Tendsto (fun t ↦ t ^ lam₀ / log t ^ k₀ * Kφ i t) atTop
      (𝓝 (if i ∈ S then J i else 0)) := fun i ↦ by
    by_cases hi : i ∈ S
    · rw [if_pos hi]; exact hKφ i hi
    · rw [if_neg hi]; exact hnKφ i hi
  have hden := tendsto_finsetSum Finset.univ fun i _ ↦ hlimK i
  have hnum := tendsto_finsetSum Finset.univ fun i _ ↦ hlimKφ i
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter] at hden hnum
  refine (hnum.div hden hpos).congr' ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  have hne : t ^ lam₀ / log t ^ k₀ ≠ 0 :=
    (div_pos (Real.rpow_pos_of_pos (one_pos.trans ht) _)
      (pow_pos (Real.log_pos ht) _)).ne'
  simp only [Pi.div_apply]
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_div_mul_left _ _ hne]

/-- The lexicographic minimum: every term certified at its own pair `(λ_i, k_i)`, the dominant set
being the terms attaining the minimal `λ` with the maximal `k` among them. -/
theorem tendsto_sum_ratio_lex {K Kφ : ι → ℝ → ℝ} {lam C J : ι → ℝ} {kk : ι → ℕ} {lam₀ : ℝ}
    {k₀ : ℕ} (hmin : ∀ i, lam₀ ≤ lam i ∧ (lam i = lam₀ → kk i ≤ k₀))
    (hK : ∀ i, Tendsto (fun t ↦ t ^ lam i / log t ^ kk i * K i t) atTop (𝓝 (C i)))
    (hKφ : ∀ i, Tendsto (fun t ↦ t ^ lam i / log t ^ kk i * Kφ i t) atTop (𝓝 (J i)))
    (hpos : (∑ i ∈ Finset.univ.filter (fun i ↦ lam i = lam₀ ∧ kk i = k₀), C i) ≠ 0) :
    Tendsto (fun t ↦ (∑ i, Kφ i t) / ∑ i, K i t) atTop
      (𝓝 ((∑ i ∈ Finset.univ.filter (fun i ↦ lam i = lam₀ ∧ kk i = k₀), J i) /
        ∑ i ∈ Finset.univ.filter (fun i ↦ lam i = lam₀ ∧ kk i = k₀), C i)) := by
  classical
  have hlex : ∀ i, ¬ (lam i = lam₀ ∧ kk i = k₀) → lam₀ < lam i ∨ (lam₀ = lam i ∧ kk i < k₀) := by
    intro i hi
    obtain ⟨h1, h2⟩ := hmin i
    by_cases h : lam i = lam₀
    · exact Or.inr ⟨h.symm, lt_of_le_of_ne (h2 h) fun hk ↦ hi ⟨h, hk⟩⟩
    · exact Or.inl (lt_of_le_of_ne h1 (Ne.symm h))
  refine tendsto_sum_ratio_powLog (lam₀ := lam₀) (k₀ := k₀)
    (Finset.univ.filter fun i ↦ lam i = lam₀ ∧ kk i = k₀)
    (fun i hi ↦ ?_) (fun i hi ↦ ?_) (fun i hi ↦ ?_) (fun i hi ↦ ?_) hpos
  · obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hi).2
    rw [← h1, ← h2]; exact hK i
  · obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hi).2
    rw [← h1, ← h2]; exact hKφ i
  · exact tendsto_negligible_of_certified
      (hlex i fun h ↦ hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)) (hK i)
  · exact tendsto_negligible_of_certified
      (hlex i fun h ↦ hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)) (hKφ i)

end Laplace.Multi
