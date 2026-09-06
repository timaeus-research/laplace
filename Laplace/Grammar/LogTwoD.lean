/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.QuadraticKernel

/-!
# The first `log n`: the two-dimensional standard integral (grammar §4.2, `d = 2`)

For the chart integral with `d = 2`, `k = (1,1)`, `h = (0,0)`, `ξ ≡ a`, `η ≡ 1`,

  `Z₂(n) = ∫₀^b ∫₀^b e^{-βn u²v² + β√n uv a} dv du`,

the state density of `τ = u²v²` is `-(log τ)/(4√τ)`: the candidate exponent `μ = 1/2` has
multiplicity `m = 2`, and the paper's expansion acquires its first `log n`. We prove

  `Z₂(n) ~ (S_{1/2}(a)/4) · n^{-1/2} · log n`   as `n → ∞`,

with the explicit bound `|Z₂(n) - (A/2) n^{-1/2} log n| ≤ (2A|log b| + E + M) n^{-1/2}` for
`√n b² ≥ 1` (`A = S_{1/2}(a)/2`). The route needs **no two-dimensional Fubini**: the inner integral
is the primitive `F(√n u b)/(√n u)` by a one-dimensional substitution, the outer integral is then
`n^{-1/2} H(b²√n)` by a second substitution, and the logarithmic primitive `H` is squeezed in
`QuadraticKernel.lean`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter

namespace Laplace.Grammar

/-- The two-dimensional chart standard integral (`d = 2`, `k = (1,1)`, `h = (0,0)`, `ξ ≡ a`,
`η ≡ 1`) on `(0,b]²`, as an iterated integral. -/
noncomputable def twoDIntegral (β a b n : ℝ) : ℝ :=
  ∫ u in Ioc (0 : ℝ) b, ∫ v in Ioc (0 : ℝ) b,
    Real.exp (-β * n * (u * v) ^ 2 + β * Real.sqrt n * (u * v) * a)

/-- **Inner substitution** `s = √n u v`: the inner integral is `F(√n u b)/(√n u)`. -/
theorem twoD_inner (β a b n u : ℝ) (hn : 0 < n) (hu : 0 < u) (hb : 0 < b) :
    (∫ v in Ioc (0 : ℝ) b, Real.exp (-β * n * (u * v) ^ 2 + β * Real.sqrt n * (u * v) * a))
      = (Real.sqrt n * u)⁻¹ * quadPrimitive β a (Real.sqrt n * u * b) := by
  have hc : Real.sqrt n * u ≠ 0 := by positivity
  have hfun : ∀ v, Real.exp (-β * n * (u * v) ^ 2 + β * Real.sqrt n * (u * v) * a)
      = quadKernel β a (Real.sqrt n * u * v) := by
    intro v
    unfold quadKernel
    congr 1
    rw [show (Real.sqrt n * u * v) ^ 2 = Real.sqrt n ^ 2 * (u * v) ^ 2 by ring, Real.sq_sqrt hn.le]
    ring
  simp_rw [hfun]
  rw [← intervalIntegral.integral_of_le hb.le,
    intervalIntegral.integral_comp_mul_left (quadKernel β a) hc, mul_zero, smul_eq_mul]
  rfl

/-- **Outer substitution** `x = √n b u`: `Z₂(n) = n^{-1/2} H(√n b²)`. -/
theorem twoDIntegral_eq (β a b n : ℝ) (hn : 0 < n) (hb : 0 < b) :
    twoDIntegral β a b n = (Real.sqrt n)⁻¹ * logPrimitive β a (Real.sqrt n * b ^ 2) := by
  unfold twoDIntegral
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hc' : Real.sqrt n * b ≠ 0 := by positivity
  have hin : ∀ u ∈ Ioc (0 : ℝ) b,
      (∫ v in Ioc (0 : ℝ) b, Real.exp (-β * n * (u * v) ^ 2 + β * Real.sqrt n * (u * v) * a))
        = (Real.sqrt n)⁻¹ * (quadPrimitive β a (Real.sqrt n * b * u) / u) := by
    intro u hu
    rw [twoD_inner β a b n u hn hu.1 hb, show Real.sqrt n * u * b = Real.sqrt n * b * u by ring]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioc hin, MeasureTheory.integral_const_mul]
  congr 1
  have hpt : ∀ u, quadPrimitive β a (Real.sqrt n * b * u) / u
      = (Real.sqrt n * b) * (quadPrimitive β a (Real.sqrt n * b * u) / (Real.sqrt n * b * u)) := by
    intro u
    rcases eq_or_ne u 0 with h0 | h0
    · simp [h0, quadPrimitive]
    · field_simp
  simp_rw [hpt]
  have hsub : (∫ u in (0 : ℝ)..b,
      quadPrimitive β a (Real.sqrt n * b * u) / (Real.sqrt n * b * u))
      = (Real.sqrt n * b)⁻¹ • ∫ x in (Real.sqrt n * b * 0)..(Real.sqrt n * b * b),
          quadPrimitive β a x / x :=
    intervalIntegral.integral_comp_mul_left (fun x => quadPrimitive β a x / x) hc'
  rw [← intervalIntegral.integral_of_le hb.le, intervalIntegral.integral_const_mul, hsub, mul_zero,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc', one_mul,
    intervalIntegral.integral_of_le (by positivity), logPrimitive]
  congr 2; ring

/-- **Explicit two-sided bound**: for `√n b² ≥ 1`,
`|Z₂(n) - (A/2) n^{-1/2} log n| ≤ (2A|log b| + E + M) n^{-1/2}`. -/
theorem twoDIntegral_sub_le (β a b n : ℝ) (hβ : 0 < β) (hb : 0 < b) (hn : 0 < n)
    (hL : 1 ≤ Real.sqrt n * b ^ 2) :
    |twoDIntegral β a b n - quadMass β a / 2 * (Real.log n / Real.sqrt n)|
      ≤ (2 * quadMass β a * |Real.log b| + Real.exp (β * a ^ 2 / 2) + quadMoment β a)
        / Real.sqrt n := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hH := logPrimitive_bounds β a (Real.sqrt n * b ^ 2) hβ hL
  have hlogL : Real.log (Real.sqrt n * b ^ 2) = Real.log n / 2 + 2 * Real.log b := by
    rw [Real.log_mul hsn.ne' (by positivity), Real.log_sqrt hn.le, Real.log_pow]; push_cast; ring
  rw [hlogL] at hH
  rw [twoDIntegral_eq β a b n hn hb]
  rw [show (Real.sqrt n)⁻¹ * logPrimitive β a (Real.sqrt n * b ^ 2)
      - quadMass β a / 2 * (Real.log n / Real.sqrt n)
      = (logPrimitive β a (Real.sqrt n * b ^ 2)
          - quadMass β a * (Real.log n / 2 + 2 * Real.log b) + 2 * quadMass β a * Real.log b)
        / Real.sqrt n by field_simp; ring,
    abs_div, abs_of_pos hsn]
  gcongr
  have hA0 : 0 ≤ quadMass β a := (quadMass_pos β a hβ).le
  have hE0 : 0 < Real.exp (β * a ^ 2 / 2) := Real.exp_pos _
  have hM0 := quadMoment_nonneg β a
  have hlb : |2 * quadMass β a * Real.log b| = 2 * quadMass β a * |Real.log b| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * quadMass β a)]
  calc |logPrimitive β a (Real.sqrt n * b ^ 2)
        - quadMass β a * (Real.log n / 2 + 2 * Real.log b) + 2 * quadMass β a * Real.log b|
      ≤ |logPrimitive β a (Real.sqrt n * b ^ 2)
          - quadMass β a * (Real.log n / 2 + 2 * Real.log b)| + |2 * quadMass β a * Real.log b| :=
        abs_add_le _ _
    _ ≤ (Real.exp (β * a ^ 2 / 2) + quadMoment β a) + 2 * quadMass β a * |Real.log b| := by
        rw [hlb]
        gcongr
        rw [abs_le]; constructor <;> linarith [hH.1, hH.2]
    _ = _ := by ring

/-- `n^{-1/2} = o(n^{-1/2} log n)` (in the form `1/√n = o(log n/√n)`). -/
theorem isLittleO_inv_sqrt_log :
    (fun n : ℝ => 1 / Real.sqrt n) =o[atTop] fun n : ℝ => Real.log n / Real.sqrt n := by
  refine isLittleO_of_tendsto' ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn h
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (zero_lt_one.trans hn)
    have hlog : 0 < Real.log n := Real.log_pos hn
    exact absurd h (div_ne_zero hlog.ne' hsn.ne')
  · refine (Real.tendsto_log_atTop.inv_tendsto_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (zero_lt_one.trans hn)
    have hlog : 0 < Real.log n := Real.log_pos hn
    simp only [Pi.inv_apply]
    field_simp

/-- **The first `log n`** (grammar §4.2, `d = 2`, `k = (1,1)`, `h = (0,0)`):
`Z₂(n) ~ (S_{1/2}(a)/4) · n^{-1/2} · log n` as `n → ∞`. The candidate exponent `μ = 1/2` appears
with multiplicity `2`, exactly as predicted by the state density `-(log τ)/(4√τ)` of `τ = u²v²`. -/
theorem twoDIntegral_isEquivalent (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) :
    (fun n : ℝ => twoDIntegral β a b n) ~[atTop]
      fun n : ℝ => fluctuation β (1 / 2) a / 4 * (n ^ (-(1 / 2 : ℝ)) * Real.log n) := by
  set A := quadMass β a with hA
  have hA0 : 0 < A := quadMass_pos β a hβ
  -- first, the equivalence with `A/2 · log n / √n`
  have hmain : (fun n : ℝ => twoDIntegral β a b n) ~[atTop]
      fun n : ℝ => A / 2 * (Real.log n / Real.sqrt n) := by
    apply IsLittleO.isEquivalent
    have hbig : (fun n : ℝ => twoDIntegral β a b n - A / 2 * (Real.log n / Real.sqrt n))
        =O[atTop] fun n : ℝ => 1 / Real.sqrt n := by
      apply IsBigO.of_bound (2 * A * |Real.log b| + Real.exp (β * a ^ 2 / 2) + quadMoment β a)
      filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / b ^ 4)] with n hn hnb
      have hn0 : (0 : ℝ) < n := by linarith
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
      have hL : 1 ≤ Real.sqrt n * b ^ 2 := by
        have h1 : (1 / b ^ 2) ^ 2 ≤ n := by rw [div_pow, one_pow, ← pow_mul]; exact hnb
        have h2 : 1 / b ^ 2 ≤ Real.sqrt n := by
          rw [Real.le_sqrt (by positivity) hn0.le]; exact h1
        calc (1 : ℝ) = 1 / b ^ 2 * b ^ 2 := by field_simp
          _ ≤ Real.sqrt n * b ^ 2 := by gcongr
      have := twoDIntegral_sub_le β a b n hβ hb hn0 hL
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.sqrt n)]
      calc _ ≤ _ := this
        _ = _ := by rw [hA]; ring
    exact (hbig.trans_isLittleO isLittleO_inv_sqrt_log).const_mul_right (by positivity)
  -- then rewrite the comparison function
  refine hmain.congr_right ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
  rw [hA, quadMass_eq β a, Real.sqrt_eq_rpow, Real.rpow_neg hn.le]
  ring

end Laplace.Grammar
