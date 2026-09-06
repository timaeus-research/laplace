/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.OrderDerivative

/-!
# Higher order-derivatives: log insertions of all degrees

The grammar paper §4 (`eq:log_lambda_derivative`) records that inserting `(log t)^k` under the
fluctuation integral corresponds to the `k`-th derivative in the order parameter:

  `∂_λ^k S_λ(a) = ∫₀^∞ (log t)^k t^{λ-1} e^{-βt+βa√t} dt`.

The `OrderDerivative` module handled `k = 1`. Here we prove the general `k` by induction, which needs
the `|log t|^k`-weighted integrand to be integrable (`log_pow_fluctuation_integrableOn`, via a
`|log t|^k ≤ (m/δ)^m(t^δ+t^{-δ})` power bound) and a generic parametric-differentiation step
(`hasDerivAt_logpow_integral`). This is the analytic backbone of `lem:log_shift`, `prop:LogODE`, and
`lem:log_generating`.
-/

open Real MeasureTheory

namespace Laplace.Grammar

/-- `|log t|^m ≤ (m/δ)^m (t^δ + t^{-δ})` for `t, δ > 0`: raising the two-sided log bound to the `m`-th
power, handled per regime `t ≷ 1` to keep the exponent at `±δ`. -/
theorem abs_log_pow_le (t δ : ℝ) (m : ℕ) (ht : 0 < t) (hδ : 0 < δ) :
    |Real.log t| ^ m ≤ (m / δ) ^ m * (t ^ δ + t ^ (-δ)) := by
  have hpos1 : (0 : ℝ) ≤ t ^ δ := (Real.rpow_pos_of_pos ht _).le
  have hpos2 : (0 : ℝ) ≤ t ^ (-δ) := (Real.rpow_pos_of_pos ht _).le
  have hprod : t ^ δ * t ^ (-δ) = 1 := by rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero]
  have hsum1 : (1 : ℝ) ≤ t ^ δ + t ^ (-δ) := by
    nlinarith [sq_nonneg (t ^ δ - 1), hprod, Real.rpow_pos_of_pos ht δ, hpos2]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp only [pow_zero, one_mul]; linarith
  have hεpos : (0 : ℝ) < δ / m := by positivity
  have hmδ : (m : ℝ) / δ = (δ / m)⁻¹ := by rw [inv_div]
  rcases le_or_gt 1 t with h1 | h1
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    have hb : Real.log t ≤ (m / δ) * t ^ (δ / m) := by
      rw [hmδ]; have := Real.log_le_rpow_div ht.le hεpos; rwa [div_eq_inv_mul] at this
    calc Real.log t ^ m ≤ ((m / δ) * t ^ (δ / m)) ^ m :=
          pow_le_pow_left₀ (Real.log_nonneg h1) hb m
      _ = (m / δ) ^ m * t ^ δ := by
          rw [mul_pow, ← Real.rpow_natCast (t ^ (δ / m)) m, ← Real.rpow_mul ht.le]
          congr 2; field_simp
      _ ≤ (m / δ) ^ m * (t ^ δ + t ^ (-δ)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hpos2) (by positivity)
  · rw [abs_of_neg (Real.log_neg ht h1), ← Real.log_inv]
    have hlognn : 0 ≤ Real.log t⁻¹ := by rw [Real.log_inv]; linarith [Real.log_neg ht h1]
    have hb : Real.log t⁻¹ ≤ (m / δ) * t ^ (-(δ / m)) := by
      rw [hmδ]; have := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ t⁻¹) hεpos
      rw [div_eq_inv_mul, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at this; exact this
    calc Real.log t⁻¹ ^ m ≤ ((m / δ) * t ^ (-(δ / m))) ^ m := pow_le_pow_left₀ hlognn hb m
      _ = (m / δ) ^ m * t ^ (-δ) := by
          rw [mul_pow, ← Real.rpow_natCast (t ^ (-(δ / m))) m, ← Real.rpow_mul ht.le]
          congr 2; field_simp
      _ ≤ (m / δ) ^ m * (t ^ δ + t ^ (-δ)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hpos1) (by positivity)

/-- The `|log t|^m`-weighted fluctuation integrand is integrable on `(0,∞)` (`β, c > 0`, any `a`):
the dominating function for the `k`-th order-derivative. -/
theorem log_pow_fluctuation_integrableOn (β c a : ℝ) (m : ℕ) (hβ : 0 < β) (hc : 0 < c) :
    IntegrableOn
      (fun t => |Real.log t| ^ m * t ^ (c - 1) * Real.exp (-β * t + β * a * Real.sqrt t))
      (Set.Ioi 0) := by
  have hδ : (0 : ℝ) < c / 2 := by positivity
  have hmaj : IntegrableOn (fun t => ((m : ℝ) / (c / 2)) ^ m * Real.exp (β * a ^ 2 / 2) *
      (t ^ (c / 2 + (c - 1)) * Real.exp (-(β / 2) * t ^ (1 : ℝ))
        + t ^ (-(c / 2) + (c - 1)) * Real.exp (-(β / 2) * t ^ (1 : ℝ)))) (Set.Ioi 0) := by
    apply Integrable.const_mul
    apply Integrable.add
    · exact integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) (by norm_num) (by positivity)
    · exact integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) (by norm_num) (by positivity)
  refine hmaj.mono' ?_ ?_
  · exact (by fun_prop : Measurable (fun t => |Real.log t| ^ m * t ^ (c - 1)
      * Real.exp (-β * t + β * a * Real.sqrt t))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hlog := abs_log_pow_le t (c / 2) m ht0 hδ
    have hamgm : β * a * Real.sqrt t ≤ β / 2 * t + β / 2 * a ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt t - a), Real.sq_sqrt ht0.le, Real.sqrt_nonneg t, hβ.le]
    have hexp : Real.exp (-β * t + β * a * Real.sqrt t)
        ≤ Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 2) * t) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [hamgm]
    have ht1 : t ^ (1 : ℝ) = t := Real.rpow_one t
    have hrw1 : t ^ (c / 2) * t ^ (c - 1) = t ^ (c / 2 + (c - 1)) := by rw [← Real.rpow_add ht0]
    have hrw2 : t ^ (-(c / 2)) * t ^ (c - 1) = t ^ (-(c / 2) + (c - 1)) := by
      rw [← Real.rpow_add ht0]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ht1]
    calc |Real.log t| ^ m * t ^ (c - 1) * Real.exp (-β * t + β * a * Real.sqrt t)
        ≤ (m / (c / 2)) ^ m * (t ^ (c / 2) + t ^ (-(c / 2))) * t ^ (c - 1)
            * (Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 2) * t)) := by gcongr
      _ = ((m : ℝ) / (c / 2)) ^ m * Real.exp (β * a ^ 2 / 2) *
            (t ^ (c / 2 + (c - 1)) * Real.exp (-(β / 2) * t)
              + t ^ (-(c / 2) + (c - 1)) * Real.exp (-(β / 2) * t)) := by
          rw [← hrw1, ← hrw2]; ring

/-- Generic order-differentiation step: differentiating the `(log t)^k`-weighted integral in `λ` adds
one more `log t`. -/
theorem hasDerivAt_logpow_integral (β lam a : ℝ) (k : ℕ) (hβ : 0 < β) (hlam : 0 < lam) :
    HasDerivAt
      (fun l => ∫ t in Set.Ioi 0,
        (Real.log t) ^ k * t ^ (l - 1) * Real.exp (-β * t + β * a * Real.sqrt t))
      (∫ t in Set.Ioi 0,
        (Real.log t) ^ (k + 1) * t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t))
      lam := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  let F : ℝ → ℝ → ℝ := fun l t =>
    (Real.log t) ^ k * t ^ (l - 1) * Real.exp (-β * t + β * a * Real.sqrt t)
  let D : ℝ → ℝ → ℝ := fun l t =>
    (Real.log t) ^ (k + 1) * t ^ (l - 1) * Real.exp (-β * t + β * a * Real.sqrt t)
  let bound : ℝ → ℝ := fun t =>
    |Real.log t| ^ (k + 1) * t ^ (lam / 2 - 1) * Real.exp (-β * t + β * a * Real.sqrt t)
      + |Real.log t| ^ (k + 1) * t ^ (3 * lam / 2 - 1) * Real.exp (-β * t + β * a * Real.sqrt t)
  have hFmeas : ∀ l : ℝ, AEStronglyMeasurable (F l) μ := fun l =>
    (by fun_prop : Measurable (fun t => (Real.log t) ^ k * t ^ (l - 1)
      * Real.exp (-β * t + β * a * Real.sqrt t))).aestronglyMeasurable
  have hnorm : ∀ l t : ℝ, 0 < t → ‖F l t‖ = |Real.log t| ^ k * t ^ (l - 1)
      * Real.exp (-β * t + β * a * Real.sqrt t) := by
    intro l t ht
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.rpow_pos_of_pos ht _),
      abs_of_pos (Real.exp_pos _)]
  have hFi : ∀ l, 0 < l → Integrable (F l) μ := by
    intro l hl
    refine (log_pow_fluctuation_integrableOn β l a k hβ hl).mono' (hFmeas l) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hnorm l t ht]
  have hbdi : Integrable bound μ :=
    (log_pow_fluctuation_integrableOn β (lam / 2) a (k + 1) hβ (by positivity)).add
      (log_pow_fluctuation_integrableOn β (3 * lam / 2) a (k + 1) hβ (by positivity))
  have hpoint : ∀ t, 0 < t → ∀ l, HasDerivAt (fun l => F l t) (D l t) l := by
    intro t ht l
    have hbase : HasDerivAt (fun l : ℝ => t ^ (l - 1)) (t ^ (l - 1) * Real.log t) l := by
      have h := (Real.hasStrictDerivAt_const_rpow ht (l - 1)).hasDerivAt.comp l
        ((hasDerivAt_id l).sub_const 1)
      simp only [Function.comp, mul_one] at h
      exact h
    have hraw := (hbase.const_mul ((Real.log t) ^ k)).mul_const
      (Real.exp (-β * t + β * a * Real.sqrt t))
    have hval : (Real.log t) ^ k * (t ^ (l - 1) * Real.log t)
        * Real.exp (-β * t + β * a * Real.sqrt t) = D l t := by
      change _ = (Real.log t) ^ (k + 1) * t ^ (l - 1) * Real.exp (-β * t + β * a * Real.sqrt t)
      rw [pow_succ]; ring
    rwa [hval] at hraw
  have hpos : ∀ᵐ t ∂μ, 0 < t := ae_restrict_mem measurableSet_Ioi
  have hbound : ∀ᵐ t ∂μ, ∀ l ∈ Metric.ball lam (lam / 2), ‖D l t‖ ≤ bound t := by
    filter_upwards [hpos] with t ht l hl
    have ht0 : (0 : ℝ) < t := ht
    have hlt : lam / 2 < l ∧ l < 3 * lam / 2 := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hl; constructor <;> linarith [hl.1, hl.2]
    have htb : t ^ (l - 1) ≤ t ^ (lam / 2 - 1) + t ^ (3 * lam / 2 - 1) := by
      rcases le_or_gt 1 t with h1 | h1
      · exact le_add_of_nonneg_of_le (Real.rpow_pos_of_pos ht0 _).le
          (Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hlt.2]))
      · exact le_add_of_le_of_nonneg
          (Real.rpow_le_rpow_of_exponent_ge ht0 h1.le (by linarith [hlt.1]))
          (Real.rpow_pos_of_pos ht0 _).le
    have hnn : (0 : ℝ) ≤ |Real.log t| ^ (k + 1) := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.rpow_pos_of_pos ht0 _),
      abs_of_pos (Real.exp_pos _)]
    calc |Real.log t| ^ (k + 1) * t ^ (l - 1) * Real.exp (-β * t + β * a * Real.sqrt t)
        ≤ |Real.log t| ^ (k + 1) * (t ^ (lam / 2 - 1) + t ^ (3 * lam / 2 - 1))
            * Real.exp (-β * t + β * a * Real.sqrt t) := by gcongr
      _ = bound t := by simp only [bound]; ring
  have hdiff : ∀ᵐ t ∂μ, ∀ l ∈ Metric.ball lam (lam / 2), HasDerivAt (fun l => F l t) (D l t) l := by
    filter_upwards [hpos] with t ht l _
    exact hpoint t ht l
  have hDmeas : AEStronglyMeasurable (D lam) μ :=
    (by fun_prop : Measurable (fun t => (Real.log t) ^ (k + 1) * t ^ (lam - 1)
      * Real.exp (-β * t + β * a * Real.sqrt t))).aestronglyMeasurable
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := D)
    (x₀ := lam) (bound := bound) (s := Metric.ball lam (lam / 2))
    (Metric.ball_mem_nhds lam (by positivity))
    (Filter.Eventually.of_forall hFmeas) (hFi lam hlam) hDmeas hbound hbdi hdiff
  exact h.2

/-- **Order-derivatives as log insertions** (grammar §4 `eq:log_lambda_derivative`):
`∂_λ^k S_λ(a) = ∫₀^∞ (log t)^k t^{λ-1} e^{-βt+βa√t} dt` for all `k` and `λ > 0`. -/
theorem iteratedDeriv_fluctuation_order (β a : ℝ) (hβ : 0 < β) (k : ℕ) :
    ∀ lam, 0 < lam → iteratedDeriv k (fun l => fluctuation β l a) lam
      = ∫ t in Set.Ioi 0,
          (Real.log t) ^ k * t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t) := by
  induction k with
  | zero =>
    intro lam hlam
    rw [iteratedDeriv_zero]
    show fluctuation β lam a = _
    rw [fluctuation]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp
  | succ k ih =>
    intro lam hlam
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv k (fun l => fluctuation β l a)
        =ᶠ[nhds lam] (fun l => ∫ t in Set.Ioi 0,
          (Real.log t) ^ k * t ^ (l - 1) * Real.exp (-β * t + β * a * Real.sqrt t)) :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds hlam) (fun l hl => ih l hl)
    rw [Filter.EventuallyEq.deriv_eq heq]
    exact (hasDerivAt_logpow_integral β lam a k hβ hlam).deriv

end Laplace.Grammar
