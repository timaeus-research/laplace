/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.IteratedLogSqueeze

/-!
# The general multiplicity theorem in the all-equal case (grammar §4.2, any `d`)

For the `d`-dimensional chart standard integral with `k = (1,…,1)`, `h = (0,…,0)` (all candidate
exponents equal to `1/2`, multiplicity `d`),

  `Z_d(n) = ∫_{(0,b]^d} e^{-βn (u₁⋯u_d)² + β√n u₁⋯u_d a} du`,

written recursively as `iterChart d (√n)` with `iterChart (d+1) c = ∫₀^b iterChart d (c u) du`, the
"divide and substitute" identity gives `Z_{d}(n) = n^{-1/2} H_{d-1}(√n b^d)` with `H_m` the iterated
logarithmic primitive, and the squeeze of `IteratedLogSqueeze.lean` yields

  `Z_d(n) ~ S_{1/2}(a) / (2^d (d-1)!) · n^{-1/2} · (log n)^{d-1}`   (`d ≥ 2`),

the `(log n)^{m-1}` of `thm:TaylorTree` with `m = d`, and consistent with the `d = 2, 3` instances
(`S/4`, `S/16`). The asymptotic is assembled with the `IsEquivalent` calculus (composition with
`L(n) = √n b^d → ∞`, `log L(n) ~ ½ log n`, products and powers) rather than explicit polynomial
bounds. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter

namespace Laplace.Grammar

/-- The `d`-fold iterated chart integral at scale `c`: `iterChart 0 c = f(c)`,
`iterChart (d+1) c = ∫₀^b iterChart d (c u) du`; `iterChart d (√n)` is the `d`-dimensional standard
integral for `k = 1`, `h = 0`, `ξ ≡ a`, `η ≡ 1`. -/
noncomputable def iterChart (β a b : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun c => quadKernel β a c
  | d + 1 => fun c => ∫ u in Ioc (0 : ℝ) b, iterChart β a b d (c * u)

theorem iterChart_zero (β a b c : ℝ) : iterChart β a b 0 c = quadKernel β a c := rfl

theorem iterChart_succ (β a b : ℝ) (d : ℕ) (c : ℝ) :
    iterChart β a b (d + 1) c = ∫ u in Ioc (0 : ℝ) b, iterChart β a b d (c * u) := rfl

/-- **Reduction**: `iterChart (d+1) c = c⁻¹ H_d(c b^{d+1})` for `c > 0`. -/
theorem iterChart_succ_eq (β a b : ℝ) (d : ℕ) (c : ℝ) (hc : 0 < c) (hb : 0 < b) :
    iterChart β a b (d + 1) c = c⁻¹ * iterLogPrim β a d (c * b ^ (d + 1)) := by
  induction d generalizing c with
  | zero =>
    rw [iterChart_succ]
    simp only [iterChart_zero, zero_add, pow_one, iterLogPrim_zero]
    rw [← intervalIntegral.integral_of_le hb.le,
      intervalIntegral.integral_comp_mul_left (quadKernel β a) hc.ne', mul_zero, smul_eq_mul]
    rfl
  | succ d ih =>
    rw [iterChart_succ]
    have hpt : ∀ u ∈ Ioc (0 : ℝ) b, iterChart β a b (d + 1) (c * u)
        = c⁻¹ * (iterLogPrim β a d (c * b ^ (d + 1) * u) / u) := by
      intro u hu
      rw [ih (c * u) (mul_pos hc hu.1), show c * u * b ^ (d + 1) = c * b ^ (d + 1) * u by ring]
      have hu0 : u ≠ 0 := hu.1.ne'
      field_simp
    rw [setIntegral_congr_fun measurableSet_Ioc hpt, MeasureTheory.integral_const_mul,
      integral_iterLogPrim_div_eq β a d (c * b ^ (d + 1)) b (by positivity) hb]
    congr 2; ring

/-- `(1 + log L)^k = o((log L)^{k+1})` as `L → ∞`. -/
theorem isLittleO_one_add_log_pow (k : ℕ) :
    (fun L : ℝ => (1 + Real.log L) ^ k) =o[atTop] fun L : ℝ => Real.log L ^ (k + 1) := by
  refine isLittleO_of_tendsto' ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL h
    exact absurd h (pow_ne_zero _ (Real.log_pos hL).ne')
  · have h1 : Tendsto (fun L : ℝ => (Real.log L)⁻¹) atTop (nhds 0) :=
      Real.tendsto_log_atTop.inv_tendsto_atTop
    have h2 := h1.mul ((tendsto_const_nhds (x := (1 : ℝ))).add h1 |>.pow k)
    simp only [zero_mul] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
    have hlog : 0 < Real.log L := Real.log_pos hL
    rw [show (1 : ℝ) + (Real.log L)⁻¹ = (1 + Real.log L) / Real.log L by field_simp; ring, div_pow,
      pow_succ]
    field_simp

/-- **Asymptotic of the iterated logarithmic primitive**:
`H_{k+1}(L) ~ A (log L)^{k+1}/(k+1)!` as `L → ∞`. -/
theorem iterLogPrim_isEquivalent (β a : ℝ) (hβ : 0 < β) (k : ℕ) :
    (fun L : ℝ => iterLogPrim β a (k + 1) L) ~[atTop]
      fun L : ℝ => quadMass β a / ((k + 1).factorial : ℝ) * Real.log L ^ (k + 1) := by
  apply IsLittleO.isEquivalent
  have hbig : (fun L : ℝ => iterLogPrim β a (k + 1) L
      - quadMass β a / ((k + 1).factorial : ℝ) * Real.log L ^ (k + 1))
      =O[atTop] fun L : ℝ => (1 + Real.log L) ^ k := by
    apply IsBigO.of_bound (iterConst β a (k + 1))
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have := iterLogPrim_sub_le β a hβ k L hL
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by linarith [Real.log_nonneg hL] : (0 : ℝ) ≤ 1 + Real.log L) k)]
    calc _ = |iterLogPrim β a (k + 1) L
          - quadMass β a * Real.log L ^ (k + 1) / ((k + 1).factorial : ℝ)| := by congr 1; ring
      _ ≤ _ := this
  have hA0 : quadMass β a / ((k + 1).factorial : ℝ) ≠ 0 :=
    (div_pos (quadMass_pos β a hβ) (by positivity)).ne'
  exact (hbig.trans_isLittleO (isLittleO_one_add_log_pow k)).const_mul_right hA0

/-- `log(√n b^m) ~ ½ log n` as `n → ∞`. -/
theorem log_sqrt_mul_pow_isEquivalent (b : ℝ) (hb : 0 < b) (m : ℕ) :
    (fun n : ℝ => Real.log (Real.sqrt n * b ^ m)) ~[atTop]
      fun n : ℝ => (1 / 2 : ℝ) * Real.log n := by
  apply IsLittleO.isEquivalent
  have hc : (fun _ : ℝ => (m : ℝ) * Real.log b) =o[atTop]
      fun n : ℝ => (1 / 2 : ℝ) * Real.log n := by
    rw [isLittleO_const_left]
    right
    have h : Tendsto (fun n : ℝ => (1 / 2 : ℝ) * Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.const_mul_atTop (by norm_num)
    simpa [Function.comp_def, Real.norm_eq_abs] using tendsto_abs_atTop_atTop.comp h
  refine hc.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
  simp only [Pi.sub_apply]
  rw [Real.log_mul (Real.sqrt_pos.2 hn).ne' (by positivity), Real.log_sqrt hn.le, Real.log_pow]
  ring

/-- **The general multiplicity theorem, all-equal case** (grammar §4.2 `thm:TaylorTree`, `d = k+2`
dimensions, `k = (1,…,1)`, `h = (0,…,0)`): 
`Z_d(n) ~ S_{1/2}(a)/(2^d (d-1)!) · n^{-1/2} · (log n)^{d-1}`. -/
theorem iterChart_isEquivalent (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) (k : ℕ) :
    (fun n : ℝ => iterChart β a b (k + 2) (Real.sqrt n)) ~[atTop]
      fun n : ℝ => fluctuation β (1 / 2) a / (2 ^ (k + 2) * ((k + 1).factorial : ℝ))
        * (n ^ (-(1 / 2 : ℝ)) * Real.log n ^ (k + 1)) := by
  set A := quadMass β a with hA
  have hZ : ∀ n : ℝ, 0 < n → iterChart β a b (k + 2) (Real.sqrt n)
      = (Real.sqrt n)⁻¹ * iterLogPrim β a (k + 1) (Real.sqrt n * b ^ (k + 2)) := fun n hn =>
    iterChart_succ_eq β a b (k + 1) (Real.sqrt n) (Real.sqrt_pos.2 hn) hb
  have hLtend : Tendsto (fun n : ℝ => Real.sqrt n * b ^ (k + 2)) atTop atTop :=
    tendsto_sqrt_atTop.atTop_mul_const (pow_pos hb _)
  have h2 := (iterLogPrim_isEquivalent β a hβ k).comp_tendsto hLtend
  have h3 := (log_sqrt_mul_pow_isEquivalent b hb (k + 2)).pow (k + 1)
  have h4 : (fun n : ℝ => iterLogPrim β a (k + 1) (Real.sqrt n * b ^ (k + 2))) ~[atTop]
      fun n : ℝ => A / ((k + 1).factorial : ℝ) * ((1 / 2 : ℝ) * Real.log n) ^ (k + 1) := by
    refine h2.trans ?_
    have := (IsEquivalent.refl (u := fun _ : ℝ => A / ((k + 1).factorial : ℝ)) (l := atTop)).mul h3
    exact this
  have h5 := (IsEquivalent.refl (u := fun n : ℝ => (Real.sqrt n)⁻¹) (l := atTop)).mul h4
  refine (h5.congr_left ?_).congr_right ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    simp only [Pi.mul_apply]
    rw [hZ n hn]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    simp only [Pi.mul_apply]
    rw [hA, quadMass_eq β a, Real.sqrt_eq_rpow, Real.rpow_neg hn.le, mul_pow, div_pow, one_pow,
      show (2 : ℝ) ^ (k + 2) = 2 ^ (k + 1) * 2 by ring]
    field_simp

end Laplace.Grammar
