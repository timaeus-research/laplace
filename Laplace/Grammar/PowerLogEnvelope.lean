/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.GammaLogAsymptotic

/-!
# Power–log envelopes from a ratio limit

First step of the mixed-ratio general-`d` monomial programme (Astra #15, route A). If a bounded
function `f` on `(0,∞)` satisfies `f(M) / (M^{-λ} (log M)^r) → C`, then it obeys the **global
envelope**

  `|f(M)| ≤ K · M^{-λ} · (1 + max 0 (log M))^r`   for all `M > 0`

(`envelope_of_tendsto_ratio`): beyond a threshold by the ratio limit, below it by the global bound
and `λ > 0`. Two consequences feed the dominated-coordinate transfer of the next unit:

* the **scaled pointwise limit** `f(Nt) / (N^{-λ} (log N)^r) → C t^{-λ}` for fixed `t > 0`
  (`tendsto_scaled_ratio`), since `log(Nt)/log N → 1`;
* the **scaled domination** `|t^{q-1} f(Nt) / (N^{-λ} (log N)^r)| ≤ K 2^r t^{q-λ-1}` for
  `N ≥ e` and `0 < t ≤ 1` (`scaled_envelope_bound`), which never divides by `log(Nt)`.
-/

open Filter Topology

namespace Laplace.Grammar

/-- **Global power–log envelope** from a ratio limit and a global bound. -/
theorem envelope_of_tendsto_ratio (f : ℝ → ℝ) (l : ℝ) (r : ℕ) (C B : ℝ) (hl : 0 < l)
    (hB : ∀ M, 0 < M → |f M| ≤ B)
    (hlim : Tendsto (fun M => f M / (M ^ (-l) * Real.log M ^ r)) atTop (𝓝 C)) :
    ∃ K, 0 ≤ K ∧ ∀ M, 0 < M → |f M| ≤ K * M ^ (-l) * (1 + max 0 (Real.log M)) ^ r := by
  have hev : ∀ᶠ M in atTop, |f M / (M ^ (-l) * Real.log M ^ r)| < |C| + 1 :=
    hlim.abs.eventually (gt_mem_nhds (by linarith))
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hev
  set M₁ : ℝ := max M₀ 2 with hM₁
  have hM₁pos : 0 < M₁ := lt_of_lt_of_le two_pos (le_max_right _ _)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 1 one_pos)
  refine ⟨max (|C| + 1) (B * M₁ ^ l), le_max_of_le_left (by positivity), fun M hM => ?_⟩
  have hpow : 0 < M ^ (-l) := Real.rpow_pos_of_pos hM _
  have hfac : 1 ≤ (1 + max 0 (Real.log M)) ^ r :=
    one_le_pow₀ (by linarith [le_max_left 0 (Real.log M)])
  rcases le_or_gt M₁ M with h | h
  · -- large `M`: use the ratio bound
    have hM0 : M₀ ≤ M := (le_max_left _ _).trans h
    have hM1 : 1 < M := by linarith [(le_max_right M₀ 2).trans h]
    have hlog : 0 < Real.log M := Real.log_pos hM1
    have hD : 0 < M ^ (-l) * Real.log M ^ r := by positivity
    have h1 := (hM₀ M hM0).le
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD] at h1
    calc |f M| ≤ (|C| + 1) * (M ^ (-l) * Real.log M ^ r) := h1
      _ ≤ (|C| + 1) * (M ^ (-l) * (1 + max 0 (Real.log M)) ^ r) := by
          gcongr
          linarith [le_max_right 0 (Real.log M)]
      _ ≤ max (|C| + 1) (B * M₁ ^ l) * M ^ (-l) * (1 + max 0 (Real.log M)) ^ r := by
          rw [← mul_assoc]
          gcongr
          exact le_max_left _ _
  · -- small `M`: use the global bound and `M^{-λ} ≥ M₁^{-λ}`
    have hM1inv : M₁ ^ (-l) ≤ M ^ (-l) :=
      Real.rpow_le_rpow_of_nonpos hM h.le (by linarith)
    have hone : 1 ≤ M₁ ^ l * M ^ (-l) := by
      have : M₁ ^ l * M₁ ^ (-l) = 1 := by
        rw [← Real.rpow_add hM₁pos, add_neg_cancel, Real.rpow_zero]
      rw [← this]
      exact mul_le_mul_of_nonneg_left hM1inv (Real.rpow_pos_of_pos hM₁pos _).le
    calc |f M| ≤ B := hB M hM
      _ ≤ B * (M₁ ^ l * M ^ (-l)) := le_mul_of_one_le_right hB0 hone
      _ = B * M₁ ^ l * M ^ (-l) * 1 := by ring
      _ ≤ max (|C| + 1) (B * M₁ ^ l) * M ^ (-l) * (1 + max 0 (Real.log M)) ^ r := by
          gcongr
          exact le_max_right _ _

/-- **Scaled pointwise limit**: for fixed `t > 0`, `f(Nt) / (N^{-λ} (log N)^r) → C t^{-λ}`. -/
theorem tendsto_scaled_ratio (f : ℝ → ℝ) (l : ℝ) (r : ℕ) (C : ℝ)
    (hlim : Tendsto (fun M => f M / (M ^ (-l) * Real.log M ^ r)) atTop (𝓝 C)) (t : ℝ)
    (ht : 0 < t) :
    Tendsto (fun N => f (N * t) / (N ^ (-l) * Real.log N ^ r)) atTop (𝓝 (C * t ^ (-l))) := by
  have h1 : Tendsto (fun N => f (N * t) / ((N * t) ^ (-l) * Real.log (N * t) ^ r)) atTop
      (𝓝 C) := hlim.comp (tendsto_id.atTop_mul_const ht)
  have h2 : Tendsto (fun N => (1 + Real.log t * (Real.log N)⁻¹) ^ r) atTop (𝓝 1) := by
    have := (Real.tendsto_log_atTop.inv_tendsto_atTop).const_mul (Real.log t)
    rw [mul_zero] at this
    have h3 := (tendsto_const_nhds (x := (1 : ℝ))).add this
    rw [add_zero] at h3
    simpa using h3.pow r
  have h := (h1.mul_const (t ^ (-l))).mul h2
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (max 1 (1 / t))] with N hN
  have hN1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN0 : 0 < N := by linarith
  have hNt : 1 < N * t := by
    have : 1 / t < N := lt_of_le_of_lt (le_max_right _ _) hN
    rwa [div_lt_iff₀ ht] at this
  have hlogN : Real.log N ≠ 0 := (Real.log_pos hN1).ne'
  have hlogNt : Real.log (N * t) ≠ 0 := (Real.log_pos hNt).ne'
  have hpN : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hpt : t ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  rw [Real.log_mul hN0.ne' ht.ne'] at hlogNt
  rw [Real.mul_rpow hN0.le ht.le, Real.log_mul hN0.ne' ht.ne',
    show (1 + Real.log t * (Real.log N)⁻¹) = (Real.log N + Real.log t) / Real.log N by
      field_simp, div_pow]
  field_simp

/-- **Scaled domination**: for `N ≥ e` and `0 < t ≤ 1`, the envelope gives the `N`-independent
bound `|t^{q-1} f(Nt) / (N^{-λ} (log N)^r)| ≤ K 2^r t^{q-λ-1}`. -/
theorem scaled_envelope_bound (f : ℝ → ℝ) (l q : ℝ) (r : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (henv : ∀ M, 0 < M → |f M| ≤ K * M ^ (-l) * (1 + max 0 (Real.log M)) ^ r) (N t : ℝ)
    (hN : Real.exp 1 ≤ N) (ht : 0 < t) (ht1 : t ≤ 1) :
    |t ^ (q - 1) * f (N * t) / (N ^ (-l) * Real.log N ^ r)| ≤ K * 2 ^ r * t ^ (q - l - 1) := by
  have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hN
  have hlogN : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    exact hN
  have hNt : 0 < N * t := mul_pos hN0 ht
  have hlogt : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
  have hmax : max 0 (Real.log (N * t)) ≤ Real.log N := by
    rw [Real.log_mul hN0.ne' ht.ne']
    exact max_le (by linarith) (by linarith)
  have hfac : (1 + max 0 (Real.log (N * t))) ^ r ≤ 2 ^ r * Real.log N ^ r := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) r
  have hD : 0 < N ^ (-l) * Real.log N ^ r := by positivity
  have hpt : 0 < t ^ (q - 1) := Real.rpow_pos_of_pos ht _
  have hpN : 0 < N ^ (-l) := Real.rpow_pos_of_pos hN0 _
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD, abs_mul, abs_of_pos hpt]
  calc t ^ (q - 1) * |f (N * t)|
      ≤ t ^ (q - 1) * (K * (N * t) ^ (-l) * (1 + max 0 (Real.log (N * t))) ^ r) :=
        mul_le_mul_of_nonneg_left (henv _ hNt) hpt.le
    _ ≤ t ^ (q - 1) * (K * (N * t) ^ (-l) * (2 ^ r * Real.log N ^ r)) := by gcongr
    _ = K * 2 ^ r * t ^ (q - l - 1) * (N ^ (-l) * Real.log N ^ r) := by
        rw [Real.mul_rpow hN0.le ht.le, show q - l - 1 = (q - 1) + (-l) by ring,
          Real.rpow_add ht]
        ring

end Laplace.Grammar
