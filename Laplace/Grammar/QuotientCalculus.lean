/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.ProductDensityCore

/-!
# Quotient calculus for power–log leading terms (cor:empirical_expectation, deterministic)

If `Z_φ(N) ~ C_φ N^{−α_φ} (log N)^{r_φ}` and `Z_1(N) ~ C_1 N^{−α_1} (log N)^{r_1}`, then
`Z_φ/Z_1 ~ (C_φ/C_1) N^{−(α_φ − α_1)} (log N)^{r_φ}/(log N)^{r_1}` (`quotient_isEquivalent`;
totalised division, so `C_1 ≠ 0` is only needed to make the limit meaningful), with the
three consequences used for posterior expectations: the same leading term gives the constant limit
`C_φ/C_1` (`tendsto_quotient_of_eq`); one fewer logarithm in the numerator gives decay like
`1/log N`, i.e. `(Z_φ/Z_1) log N → C_φ/C_1` (`tendsto_quotient_mul_log_of_eq`); a strictly larger
power in the numerator gives decay to `0` (`tendsto_quotient_zero_of_lt`). Astra #14 rank 1: the
calculus is independent of the chart indexing. Zero `sorry`/`axiom`.
-/

open Asymptotics Filter Real Topology

namespace Laplace.Grammar

/-- The power–log model term `C N^{−α} (log N)^r`. -/
noncomputable def powLog (C α : ℝ) (r : ℕ) (N : ℝ) : ℝ := C * N ^ (-α) * Real.log N ^ r

theorem powLog_pos (C α : ℝ) (r : ℕ) (hC : 0 < C) (N : ℝ) (hN : 1 < N) : 0 < powLog C α r N := by
  unfold powLog
  have h1 : 0 < N ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
  have h2 : 0 < Real.log N := Real.log_pos hN
  positivity

/-- **Quotient of power–log leading terms.** -/
theorem quotient_isEquivalent (Zφ Z₁ : ℝ → ℝ) (Cφ C₁ αφ α₁ : ℝ) (rφ r₁ : ℕ)
    (hφ : Zφ ~[atTop] powLog Cφ αφ rφ) (h₁ : Z₁ ~[atTop] powLog C₁ α₁ r₁) :
    (fun N => Zφ N / Z₁ N) ~[atTop]
      fun N => (Cφ / C₁) * N ^ (-(αφ - α₁)) * (Real.log N ^ rφ / Real.log N ^ r₁) := by
  have h := hφ.div h₁
  refine (h.congr_left (Eventually.of_forall fun N => rfl)).congr_right ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hpow : N ^ (-(αφ - α₁)) = N ^ (-αφ) / N ^ (-α₁) := by
    rw [← Real.rpow_sub hN0]; congr 1; ring
  show powLog Cφ αφ rφ N / powLog C₁ α₁ r₁ N = _
  unfold powLog
  rw [hpow]
  have h1 : N ^ (-αφ) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have h2 : N ^ (-α₁) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have h3 : Real.log N ^ r₁ ≠ 0 := pow_ne_zero _ hlog.ne'
  field_simp

/-- Same leading term: the quotient converges to the ratio of the coefficients. -/
theorem tendsto_quotient_of_eq (Zφ Z₁ : ℝ → ℝ) (Cφ C₁ α : ℝ) (r : ℕ)
    (hφ : Zφ ~[atTop] powLog Cφ α r) (h₁ : Z₁ ~[atTop] powLog C₁ α r) :
    Tendsto (fun N => Zφ N / Z₁ N) atTop (𝓝 (Cφ / C₁)) := by
  have h := quotient_isEquivalent Zφ Z₁ Cφ C₁ α α r r hφ h₁
  refine (h.congr_right ?_).tendsto_const
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hlog : 0 < Real.log N := Real.log_pos hN
  simp only [Function.const_apply, sub_self, neg_zero, Real.rpow_zero, mul_one,
    div_self (pow_ne_zero r hlog.ne')]

/-- One fewer logarithm in the numerator: the quotient decays like `1 / log N`. -/
theorem tendsto_quotient_mul_log_of_eq (Zφ Z₁ : ℝ → ℝ) (Cφ C₁ α : ℝ) (r : ℕ)
    (hφ : Zφ ~[atTop] powLog Cφ α r) (h₁ : Z₁ ~[atTop] powLog C₁ α (r + 1)) :
    Tendsto (fun N => Zφ N / Z₁ N * Real.log N) atTop (𝓝 (Cφ / C₁)) := by
  have h := quotient_isEquivalent Zφ Z₁ Cφ C₁ α α r (r + 1) hφ h₁
  have h' := h.mul (IsEquivalent.refl (u := fun N : ℝ => Real.log N))
  refine (h'.congr_right ?_).tendsto_const
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hlog : 0 < Real.log N := Real.log_pos hN
  show (Cφ / C₁) * N ^ (-(α - α)) * (Real.log N ^ r / Real.log N ^ (r + 1)) * Real.log N = Cφ / C₁
  rw [sub_self, neg_zero, Real.rpow_zero, mul_one]
  field_simp
  ring

/-- A strictly larger power in the numerator: the quotient tends to `0`. -/
theorem tendsto_quotient_zero_of_lt (Zφ Z₁ : ℝ → ℝ) (Cφ C₁ αφ α₁ : ℝ) (rφ r₁ : ℕ)
    (hα : α₁ < αφ) (hφ : Zφ ~[atTop] powLog Cφ αφ rφ) (h₁ : Z₁ ~[atTop] powLog C₁ α₁ r₁) :
    Tendsto (fun N => Zφ N / Z₁ N) atTop (𝓝 0) := by
  have h := quotient_isEquivalent Zφ Z₁ Cφ C₁ αφ α₁ rφ r₁ hφ h₁
  refine h.tendsto_nhds_iff.2 ?_
  have hδ : 0 < αφ - α₁ := sub_pos.2 hα
  have hlittle : (fun N : ℝ => Real.log N ^ (rφ : ℝ)) =o[atTop] fun N => N ^ (αφ - α₁) :=
    isLittleO_log_rpow_rpow_atTop (rφ : ℝ) hδ
  have hdiv := hlittle.tendsto_div_nhds_zero
  have hbound : ∀ᶠ N in atTop,
      ‖(Cφ / C₁) * N ^ (-(αφ - α₁)) * (Real.log N ^ rφ / Real.log N ^ r₁)‖
        ≤ |Cφ / C₁| * (N ^ (-(αφ - α₁)) * Real.log N ^ rφ) := by
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
    have hN1 : 1 ≤ N := le_trans (Real.one_le_exp zero_le_one) hN
    have hN0 : 0 < N := by linarith
    have hlog1 : 1 ≤ Real.log N := (Real.le_log_iff_exp_le hN0).2 hN
    have hlogpos : 0 < Real.log N := by linarith
    have hpow : 0 < N ^ (-(αφ - α₁)) := Real.rpow_pos_of_pos hN0 _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hpow,
      abs_of_pos (show (0 : ℝ) < Real.log N ^ rφ / Real.log N ^ r₁ by positivity)]
    have h1 : Real.log N ^ rφ / Real.log N ^ r₁ ≤ Real.log N ^ rφ :=
      div_le_self (by positivity) (one_le_pow₀ hlog1)
    calc |Cφ / C₁| * N ^ (-(αφ - α₁)) * (Real.log N ^ rφ / Real.log N ^ r₁)
        ≤ |Cφ / C₁| * N ^ (-(αφ - α₁)) * Real.log N ^ rφ :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = |Cφ / C₁| * (N ^ (-(αφ - α₁)) * Real.log N ^ rφ) := by ring
  have hlim : Tendsto (fun N : ℝ => |Cφ / C₁| * (N ^ (-(αφ - α₁)) * Real.log N ^ rφ)) atTop
      (𝓝 0) := by
    have := hdiv.const_mul |Cφ / C₁|
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    rw [Real.rpow_neg hN.le, Real.rpow_natCast]
    ring
  exact squeeze_zero_norm' hbound hlim

end Laplace.Grammar
