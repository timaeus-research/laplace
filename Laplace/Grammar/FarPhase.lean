/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.ProbNormalisedRemainder

/-!
# Exponential negligibility of the far-phase region (grammar §4.3, Astra #11 rank 5)

The proof of thm:strataempiricalexpansion splits the partition function into the region `K < ε`
(treated by the resolution and the Taylor tree) and the far region `K ≥ ε`, where the AM–GM bound
`β√(nK)ψ ≤ β(nK + ψ²)/2` shows that the integrand is dominated by `|η| e^{-βnε/2 + βM²/2}` whenever
`|ψ| ≤ M`. We formalise this on an arbitrary measurable set `E` of a measure space:

`|∫_E η e^{-βnK + β√(nK)ψ}| ≤ (∫_E |η|) e^{-βnε/2 + βM²/2}` (`farPhase_bound`),

and the resulting exponential decay in `n` for a fixed bound `M` (`farPhase_tendsto_zero`). Note
that the region must be `{K ≥ ε}` itself; the complement of a small box is not such a region for
the monomial phase `u₁^{2k₁}u₂^{2k₂}`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Grammar

/-- The AM–GM exponent bound: `-βnK + β√(nK)ψ ≤ -βnε/2 + βM²/2` when `K ≥ ε ≥ 0`, `|ψ| ≤ M`. -/
theorem farPhase_exponent_le (β n ε M K ψ : ℝ) (hβ : 0 < β) (hn : 0 ≤ n) (hε : 0 ≤ ε)
    (hK : ε ≤ K) (hψ : |ψ| ≤ M) :
    -β * n * K + β * Real.sqrt (n * K) * ψ ≤ -β * n * ε / 2 + β * M ^ 2 / 2 := by
  have hnK : 0 ≤ n * K := mul_nonneg hn (hε.trans hK)
  have hsq : Real.sqrt (n * K) ^ 2 = n * K := Real.sq_sqrt hnK
  have hamgm : 2 * Real.sqrt (n * K) * |ψ| ≤ Real.sqrt (n * K) ^ 2 + |ψ| ^ 2 :=
    two_mul_le_add_sq _ _
  have hψ2 : |ψ| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hψ 2
  have hψle : Real.sqrt (n * K) * ψ ≤ Real.sqrt (n * K) * |ψ| :=
    mul_le_mul_of_nonneg_left (le_abs_self ψ) (Real.sqrt_nonneg _)
  have hnε : n * ε ≤ n * K := mul_le_mul_of_nonneg_left hK hn
  rw [sq_abs] at hψ2 hamgm
  nlinarith [mul_le_mul_of_nonneg_left hψle hβ.le, hsq, hamgm, hψ2, hnε]

/-- **Far-phase bound**: on a set where the phase is at least `ε` and the fluctuation is bounded by
`M`, the standard-integral integrand is exponentially small. -/
theorem farPhase_bound {W : Type*} [MeasurableSpace W] (μ : Measure W) (E : Set W)
    (hE : MeasurableSet E) (β n ε M : ℝ) (hβ : 0 < β) (hn : 0 ≤ n) (hε : 0 ≤ ε)
    (η K ψ : W → ℝ) (hK : ∀ w ∈ E, ε ≤ K w) (hψ : ∀ w ∈ E, |ψ w| ≤ M)
    (hη : IntegrableOn η E μ) :
    |∫ w in E, η w * Real.exp (-β * n * K w + β * Real.sqrt (n * K w) * ψ w) ∂μ|
      ≤ (∫ w in E, |η w| ∂μ) * Real.exp (-β * n * ε / 2 + β * M ^ 2 / 2) := by
  set C := Real.exp (-β * n * ε / 2 + β * M ^ 2 / 2) with hC
  have hg : Integrable (fun w => |η w| * C) (μ.restrict E) := hη.norm.mul_const C
  have hbound : ∀ᵐ w ∂(μ.restrict E),
      ‖η w * Real.exp (-β * n * K w + β * Real.sqrt (n * K w) * ψ w)‖ ≤ |η w| * C := by
    refine ae_restrict_of_forall_mem hE fun w hw => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (farPhase_exponent_le β n ε M (K w) (ψ w) hβ hn hε (hK w hw) (hψ w hw)))
      (abs_nonneg _)
  have h := norm_integral_le_of_norm_le hg hbound
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  exact integral_mul_const C _

/-- The far-phase contribution decays exponentially as `n → ∞` for a fixed fluctuation bound. -/
theorem farPhase_tendsto_zero (β ε M I : ℝ) (hβ : 0 < β) (hε : 0 < ε) :
    Tendsto (fun n : ℝ => I * Real.exp (-β * n * ε / 2 + β * M ^ 2 / 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℝ => -β * n * ε / 2 + β * M ^ 2 / 2) atTop atBot := by
    have hc : (-β * ε / 2) < 0 := by
      have : 0 < β * ε := mul_pos hβ hε
      linarith
    have := tendsto_atBot_add_const_right atTop (β * M ^ 2 / 2)
      (tendsto_id.const_mul_atTop_of_neg hc)
    refine this.congr fun n => ?_
    simp only [id]; ring
  have h2 := Real.tendsto_exp_atBot.comp h1
  simpa using h2.const_mul I

end Laplace.Grammar
