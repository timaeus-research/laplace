/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.Fluctuation

/-!
# Differentiation of the fluctuation function in the order parameter

The grammar paper §4 encodes SLT log terms as derivatives of the fluctuation function with respect to
its order `λ` (`eq:log_lambda_derivative`): since `∂_λ t^{λ-1} = (log t) t^{λ-1}`,

  `∂_λ S_λ(a) = ∫₀^∞ (log t) t^{λ-1} e^{-βt+βa√t} dt`.

This is the `k = 1` case and the analytic foundation of the log-insertion machinery
(`lem:log_shift`, `prop:LogODE`, `lem:log_generating`). We prove it by differentiation under the
integral sign in `λ`, dominating the derivative integrand by the `|log t|`-weighted fluctuation
integrand, whose integrability we establish first.
-/

open Real MeasureTheory

namespace Laplace.Grammar

/-- `|log t| ≤ (t^ε + t^{-ε})/ε` for `t, ε > 0`: the logarithm is dominated by an arbitrarily small
power near both `0` and `∞`. -/
theorem abs_log_le_rpow_add (t ε : ℝ) (ht : 0 < t) (hε : 0 < ε) :
    |Real.log t| ≤ (t ^ ε + t ^ (-ε)) / ε := by
  have hpε : (0 : ℝ) ≤ t ^ ε := (Real.rpow_pos_of_pos ht _).le
  have hnε : (0 : ℝ) ≤ t ^ (-ε) := (Real.rpow_pos_of_pos ht _).le
  rcases le_or_gt 1 t with h1 | h1
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    calc Real.log t ≤ t ^ ε / ε := Real.log_le_rpow_div ht.le hε
      _ ≤ (t ^ ε + t ^ (-ε)) / ε := by gcongr; linarith
  · rw [abs_of_neg (Real.log_neg ht h1), ← Real.log_inv]
    have h := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ t⁻¹) hε
    rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at h
    calc Real.log t⁻¹ ≤ t ^ (-ε) / ε := h
      _ ≤ (t ^ ε + t ^ (-ε)) / ε := by gcongr; linarith

/-- The `|log t|`-weighted fluctuation integrand is integrable on `(0,∞)` (`β, c > 0`, any `a`):
`|log t|` is absorbed into an arbitrarily small power split, and the AM–GM Gaussian bound handles the
phase. This is the dominating function for order-differentiation. -/
theorem log_fluctuation_integrableOn (β c a : ℝ) (hβ : 0 < β) (hc : 0 < c) :
    IntegrableOn (fun t => |Real.log t| * t ^ (c - 1) * Real.exp (-β * t + β * a * Real.sqrt t))
      (Set.Ioi 0) := by
  have hε : (0 : ℝ) < c / 2 := by positivity
  have hmaj : IntegrableOn (fun t => Real.exp (β * a ^ 2 / 2) / (c / 2) *
      (t ^ (c - 1 + c / 2) * Real.exp (-(β / 2) * t ^ (1 : ℝ))
        + t ^ (c - 1 - c / 2) * Real.exp (-(β / 2) * t ^ (1 : ℝ)))) (Set.Ioi 0) := by
    apply Integrable.const_mul
    apply Integrable.add
    · exact integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) (by norm_num) (by positivity)
    · exact integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) (by norm_num) (by positivity)
  refine hmaj.mono' ?_ ?_
  · exact (by fun_prop : Measurable (fun t => |Real.log t| * t ^ (c - 1)
      * Real.exp (-β * t + β * a * Real.sqrt t))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hlog := abs_log_le_rpow_add t (c / 2) ht0 hε
    have hamgm : β * a * Real.sqrt t ≤ β / 2 * t + β / 2 * a ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt t - a), Real.sq_sqrt ht0.le, Real.sqrt_nonneg t, hβ.le]
    have hexp : Real.exp (-β * t + β * a * Real.sqrt t)
        ≤ Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 2) * t) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [hamgm]
    have ht1 : t ^ (1 : ℝ) = t := Real.rpow_one t
    have hrw1 : t ^ (c - 1) * t ^ (c / 2) = t ^ (c - 1 + c / 2) := by rw [← Real.rpow_add ht0]
    have hrw2 : t ^ (c - 1) * t ^ (-(c / 2)) = t ^ (c - 1 - c / 2) := by
      rw [show c - 1 - c / 2 = (c - 1) + (-(c / 2)) by ring, ← Real.rpow_add ht0]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ht1]
    calc |Real.log t| * t ^ (c - 1) * Real.exp (-β * t + β * a * Real.sqrt t)
        ≤ (t ^ (c / 2) + t ^ (-(c / 2))) / (c / 2) * t ^ (c - 1)
            * (Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 2) * t)) := by gcongr
      _ = Real.exp (β * a ^ 2 / 2) / (c / 2) *
            (t ^ (c - 1 + c / 2) * Real.exp (-(β / 2) * t)
              + t ^ (c - 1 - c / 2) * Real.exp (-(β / 2) * t)) := by rw [← hrw1, ← hrw2]; ring

/-- **Order-derivative of the fluctuation function** (grammar §4 `eq:log_lambda_derivative`, `k=1`):
`∂_λ S_λ(a) = ∫₀^∞ (log t) t^{λ-1} e^{-βt+βa√t} dt`. Differentiation under the integral sign in the
order `λ`, dominated by the `|log t|`-weighted integrand. -/
theorem hasDerivAt_fluctuation_order (β lam a : ℝ) (hβ : 0 < β) (hlam : 0 < lam) :
    HasDerivAt (fun l => fluctuation β l a)
      (∫ t in Set.Ioi 0, Real.log t * t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t))
      lam := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  let F : ℝ → ℝ → ℝ := fun l t => t ^ (l - 1) * Real.exp (-β * t + β * a * Real.sqrt t)
  let D : ℝ → ℝ → ℝ := fun l t => Real.log t * t ^ (l - 1) * Real.exp (-β * t + β * a * Real.sqrt t)
  let bound : ℝ → ℝ := fun t =>
    |Real.log t| * t ^ (lam / 2 - 1) * Real.exp (-β * t + β * a * Real.sqrt t)
      + |Real.log t| * t ^ (3 * lam / 2 - 1) * Real.exp (-β * t + β * a * Real.sqrt t)
  have hFi : ∀ l, 0 < l → Integrable (F l) μ := fun l hl => fluctuation_integrableOn β l hβ hl a
  have hbdi : Integrable bound μ :=
    (log_fluctuation_integrableOn β (lam / 2) a hβ (by positivity)).add
      (log_fluctuation_integrableOn β (3 * lam / 2) a hβ (by positivity))
  -- Pointwise derivative in the order `l`.
  have hpoint : ∀ t, 0 < t → ∀ l, HasDerivAt (fun l => F l t) (D l t) l := by
    intro t ht l
    have hbase : HasDerivAt (fun l : ℝ => t ^ (l - 1)) (t ^ (l - 1) * Real.log t) l := by
      have h := (Real.hasStrictDerivAt_const_rpow ht (l - 1)).hasDerivAt.comp l
        ((hasDerivAt_id l).sub_const 1)
      simp only [Function.comp, mul_one] at h
      exact h
    have hraw := hbase.mul_const (Real.exp (-β * t + β * a * Real.sqrt t))
    have hval : t ^ (l - 1) * Real.log t * Real.exp (-β * t + β * a * Real.sqrt t) = D l t := by
      change _ = Real.log t * t ^ (l - 1) * Real.exp (-β * t + β * a * Real.sqrt t); ring
    rwa [hval] at hraw
  have hpos : ∀ᵐ t ∂μ, 0 < t := ae_restrict_mem measurableSet_Ioi
  have hFmeas : ∀ᶠ l in nhds lam, AEStronglyMeasurable (F l) μ :=
    Filter.Eventually.of_forall fun l =>
      (by fun_prop : Measurable (fun t => t ^ (l - 1)
        * Real.exp (-β * t + β * a * Real.sqrt t))).aestronglyMeasurable
  -- Domination on `ball lam (lam/2)` (so every `l` there is positive).
  have hbound : ∀ᵐ t ∂μ, ∀ l ∈ Metric.ball lam (lam / 2), ‖D l t‖ ≤ bound t := by
    filter_upwards [hpos] with t ht l hl
    have ht0 : (0 : ℝ) < t := ht
    have hlt : lam / 2 < l ∧ l < 3 * lam / 2 := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hl; constructor <;> linarith [hl.1, hl.2]
    have hC : (0 : ℝ) ≤ Real.exp (-β * t + β * a * Real.sqrt t) := (Real.exp_pos _).le
    have htb : t ^ (l - 1) ≤ t ^ (lam / 2 - 1) + t ^ (3 * lam / 2 - 1) := by
      rcases le_or_gt 1 t with h1 | h1
      · exact le_add_of_nonneg_of_le (Real.rpow_pos_of_pos ht0 _).le
          (Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hlt.2]))
      · exact le_add_of_le_of_nonneg
          (Real.rpow_le_rpow_of_exponent_ge ht0 h1.le (by linarith [hlt.1]))
          (Real.rpow_pos_of_pos ht0 _).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _),
      abs_of_pos (Real.exp_pos _)]
    calc |Real.log t| * t ^ (l - 1) * Real.exp (-β * t + β * a * Real.sqrt t)
        ≤ |Real.log t| * (t ^ (lam / 2 - 1) + t ^ (3 * lam / 2 - 1))
            * Real.exp (-β * t + β * a * Real.sqrt t) := by gcongr
      _ = bound t := by simp only [bound]; ring
  have hdiff : ∀ᵐ t ∂μ, ∀ l ∈ Metric.ball lam (lam / 2), HasDerivAt (fun l => F l t) (D l t) l := by
    filter_upwards [hpos] with t ht l _
    exact hpoint t ht l
  have hDmeas : AEStronglyMeasurable (D lam) μ :=
    (by fun_prop : Measurable (fun t => Real.log t * t ^ (lam - 1)
      * Real.exp (-β * t + β * a * Real.sqrt t))).aestronglyMeasurable
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := D)
    (x₀ := lam) (bound := bound) (s := Metric.ball lam (lam / 2))
    (Metric.ball_mem_nhds lam (by positivity)) hFmeas (hFi lam hlam) hDmeas hbound hbdi hdiff
  exact h.2

/-- Property `eq:log_lambda_derivative` (`k=1`) in `deriv` form. -/
theorem deriv_fluctuation_order (β lam a : ℝ) (hβ : 0 < β) (hlam : 0 < lam) :
    deriv (fun l => fluctuation β l a) lam
      = ∫ t in Set.Ioi 0, Real.log t * t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t) :=
  (hasDerivAt_fluctuation_order β lam a hβ hlam).deriv

end Laplace.Grammar
