/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LogPowerGeneralD

/-!
# Partially coinciding exponents: `d = 3`, `h = (0,0,1)` (grammar §4.2)

The multiplicity in `thm:TaylorTree` counts how many coordinates attain the *minimal* candidate
exponent. For `k = (1,1,1)`, `h = (0,0,1)` the exponents are `(1/2, 1/2, 1)`: two coincide at the
minimum, the third is larger, so the prediction is `n^{-1/2} log n` (multiplicity `2`), not
`(log n)²`. We prove the **exact chart formula**

  `Z(n) = ∫∫∫ w e^{-βn(uvw)² + β√n uvw a} = (b/√n) (H(L) - K(L))`,   `L = √n b³`,

with `H` the logarithmic primitive and `K(L) = ∫₀^L x⁻² F₁ = F₀(L) - F₁(L)/L` the noncritical power
primitive (bounded by `A`), hence

  `Z(n) ~ (b S_{1/2}(a)/4) · n^{-1/2} · log n`.

The third coordinate contributes only the bounded `K` and the factor `b`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter

namespace Laplace.Grammar

theorem quadMomentPrimitive_zero (β a : ℝ) : quadMomentPrimitive β a 0 = 0 := by
  simp [quadMomentPrimitive]

theorem quadPowerPrimitive_zero (β a : ℝ) : quadPowerPrimitive β a 0 = 0 := by
  simp [quadPowerPrimitive]

/-- `|F₁(t)| ≤ E t²` for every real `t`. -/
theorem abs_quadMomentPrimitive_le (β a t : ℝ) (hβ : 0 < β) :
    |quadMomentPrimitive β a t| ≤ Real.exp (β * a ^ 2 / 2) * t ^ 2 := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
    (C := Real.exp (β * a ^ 2 / 2) * |t|) (f := fun s => s * quadKernel β a s) fun s hs => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (quadKernel_pos β a s)]
      have hs' : |s| ≤ |t| := by
        rcases le_total 0 t with ht | ht
        · rw [Set.uIoc_of_le ht] at hs; rw [abs_of_pos hs.1, abs_of_nonneg ht]; exact hs.2
        · rw [Set.uIoc_of_ge ht] at hs
          rw [abs_of_nonpos (hs.2), abs_of_nonpos ht]; linarith [hs.1]
      calc |s| * quadKernel β a s ≤ |t| * Real.exp (β * a ^ 2 / 2) :=
            mul_le_mul hs' (quadKernel_le_const β a s hβ) (quadKernel_pos β a s).le (abs_nonneg _)
        _ = _ := by ring
  rw [Real.norm_eq_abs, sub_zero] at this
  calc |quadMomentPrimitive β a t| ≤ Real.exp (β * a ^ 2 / 2) * |t| * |t| := this
    _ = _ := by rw [mul_assoc, ← sq, sq_abs]

/-- The integrand of `K` is bounded by `E` on all of `ℝ`. -/
theorem quadPowerPrimitive_integrand_abs_le (β a t : ℝ) (hβ : 0 < β) :
    |(t ^ 2)⁻¹ * quadMomentPrimitive β a t| ≤ Real.exp (β * a ^ 2 / 2) := by
  rcases eq_or_ne t 0 with h0 | h0
  · simp [h0, (Real.exp_pos _).le]
  · rw [abs_mul, abs_of_pos (inv_pos.2 (by positivity)), inv_mul_le_iff₀ (by positivity),
      mul_comm]
    exact abs_quadMomentPrimitive_le β a t hβ

theorem quadPowerPrimitive_continuous (β a : ℝ) (hβ : 0 < β) :
    Continuous (quadPowerPrimitive β a) := by
  unfold quadPowerPrimitive
  refine intervalIntegral.continuous_primitive (fun c d => ?_) 0
  refine (intervalIntegrable_const (c := Real.exp (β * a ^ 2 / 2))).mono_fun
    (((measurable_id.pow_const 2).inv.mul
      (quadMomentPrimitive_continuous β a).measurable).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun t => ?_
  beta_reduce
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact quadPowerPrimitive_integrand_abs_le β a t hβ

theorem quadPowerPrimitive_nonneg (β a L : ℝ) (hL : 0 ≤ L) : 0 ≤ quadPowerPrimitive β a L :=
  intervalIntegral.integral_nonneg hL fun x hx =>
    mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (quadMomentPrimitive_nonneg β a x hx.1)

/-- `K(L) ≤ A`. -/
theorem quadPowerPrimitive_le_mass (β a L : ℝ) (hβ : 0 < β) (hL : 0 ≤ L) :
    quadPowerPrimitive β a L ≤ quadMass β a := by
  rcases eq_or_lt_of_le hL with h0 | h0
  · rw [← h0, quadPowerPrimitive_zero]; exact (quadMass_pos β a hβ).le
  · rw [quadPowerPrimitive_eq β a L hβ h0]
    have h1 := quadMass_sub_primitive_nonneg β a L hβ hL
    have h2 : 0 ≤ quadMomentPrimitive β a L / L :=
      div_nonneg (quadMomentPrimitive_nonneg β a L hL) hL
    linarith

/-- `K(x)/x ≤ E/2` on `x > 0`, hence `K(x)/x` is integrable on `(0, L]`. -/
theorem quadPowerPrimitive_div_integrableOn (β a L : ℝ) (hβ : 0 < β) :
    IntegrableOn (fun x => quadPowerPrimitive β a x / x) (Ioc 0 L) := by
  refine Integrable.mono' (g := fun _ => Real.exp (β * a ^ 2 / 2) / 2)
    (integrableOn_const measure_Ioc_lt_top.ne)
    ((quadPowerPrimitive_continuous β a hβ).measurable.div measurable_id).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx.1
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (quadPowerPrimitive_nonneg β a x hx0.le) hx0.le),
    div_le_iff₀ hx0]
  exact abs_quadPowerPrimitive_le β a x hβ hx0.le |>.trans' (le_abs_self _)

/-- `∫₀^b x⁻² F₁(cx) dx = c K(cb)`. -/
theorem integral_quadMomentPrimitive_div_sq_eq (β a c b : ℝ) (hc : 0 < c) (hb : 0 < b) :
    (∫ v in Ioc (0 : ℝ) b, (v ^ 2)⁻¹ * quadMomentPrimitive β a (c * v))
      = c * quadPowerPrimitive β a (c * b) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hpt : ∀ v, (v ^ 2)⁻¹ * quadMomentPrimitive β a (c * v)
      = c ^ 2 * (((c * v) ^ 2)⁻¹ * quadMomentPrimitive β a (c * v)) := by
    intro v
    rcases eq_or_ne v 0 with h0 | h0
    · simp [h0]
    · field_simp
  simp_rw [hpt]
  have hsub : (∫ v in (0 : ℝ)..b, ((c * v) ^ 2)⁻¹ * quadMomentPrimitive β a (c * v))
      = c⁻¹ • ∫ x in (c * 0)..(c * b), (x ^ 2)⁻¹ * quadMomentPrimitive β a x :=
    intervalIntegral.integral_comp_mul_left (fun x => (x ^ 2)⁻¹ * quadMomentPrimitive β a x) hc0
  rw [← intervalIntegral.integral_of_le hb.le, intervalIntegral.integral_const_mul, hsub, mul_zero,
    smul_eq_mul, quadPowerPrimitive]
  field_simp

/-- `∫₀^b K(cu)/u du = ∫₀^{cb} K(x)/x dx`. -/
theorem integral_quadPowerPrimitive_div_eq (β a c b : ℝ) (hc : 0 < c) (hb : 0 < b) :
    (∫ u in Ioc (0 : ℝ) b, quadPowerPrimitive β a (c * u) / u)
      = ∫ x in Ioc (0 : ℝ) (c * b), quadPowerPrimitive β a x / x := by
  have hc0 : c ≠ 0 := hc.ne'
  have hpt : ∀ u, quadPowerPrimitive β a (c * u) / u
      = c * (quadPowerPrimitive β a (c * u) / (c * u)) := by
    intro u
    rcases eq_or_ne u 0 with h0 | h0
    · simp [h0, quadPowerPrimitive_zero]
    · field_simp
  simp_rw [hpt]
  have hsub : (∫ u in (0 : ℝ)..b, quadPowerPrimitive β a (c * u) / (c * u))
      = c⁻¹ • ∫ x in (c * 0)..(c * b), quadPowerPrimitive β a x / x :=
    intervalIntegral.integral_comp_mul_left (fun x => quadPowerPrimitive β a x / x) hc0
  rw [← intervalIntegral.integral_of_le hb.le, intervalIntegral.integral_const_mul, hsub, mul_zero,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul,
    intervalIntegral.integral_of_le (by positivity)]

/-- `∫₀^L K(x)/x dx = H(L) - K(L)`. -/
theorem integral_quadPowerPrimitive_div (β a L : ℝ) (hβ : 0 < β) (hL : 0 ≤ L) :
    (∫ x in Ioc (0 : ℝ) L, quadPowerPrimitive β a x / x)
      = logPrimitive β a L - quadPowerPrimitive β a L := by
  have hH := quadPrimitive_div_integrableOn β a L hβ
  have hK : IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹ * quadMomentPrimitive β a x) (Ioc 0 L) :=
    (quadPowerPrimitive_integrand_intervalIntegrable β a L hβ hL).1
  have hpt : ∀ x ∈ Ioc (0 : ℝ) L, quadPowerPrimitive β a x / x
      = quadPrimitive β a x / x - (x ^ 2)⁻¹ * quadMomentPrimitive β a x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx.1
    rw [quadPowerPrimitive_eq β a x hβ hx0]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, MeasureTheory.integral_sub hH hK, logPrimitive,
    quadPowerPrimitive, intervalIntegral.integral_of_le hL]

/-- The `d = 3`, `k = (1,1,1)`, `h = (0,0,1)` chart standard integral (iterated form). -/
noncomputable def threeDIntegralH001 (β a b n : ℝ) : ℝ :=
  ∫ u in Ioc (0 : ℝ) b, ∫ v in Ioc (0 : ℝ) b, ∫ w in Ioc (0 : ℝ) b,
    w * Real.exp (-β * n * (u * v * w) ^ 2 + β * Real.sqrt n * (u * v * w) * a)

/-- **Exact reduction**: `Z(n) = (b/√n)(H(L) - K(L))`, `L = √n b³`. -/
theorem threeDIntegralH001_eq (β a b n : ℝ) (hβ : 0 < β) (hn : 0 < n) (hb : 0 < b) :
    threeDIntegralH001 β a b n
      = b / Real.sqrt n * (logPrimitive β a (Real.sqrt n * b ^ 3)
        - quadPowerPrimitive β a (Real.sqrt n * b ^ 3)) := by
  unfold threeDIntegralH001
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hmid : ∀ u ∈ Ioc (0 : ℝ) b,
      (∫ v in Ioc (0 : ℝ) b, ∫ w in Ioc (0 : ℝ) b,
        w * Real.exp (-β * n * (u * v * w) ^ 2 + β * Real.sqrt n * (u * v * w) * a))
        = b / Real.sqrt n * (quadPowerPrimitive β a (Real.sqrt n * b ^ 2 * u) / u) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hin : ∀ v ∈ Ioc (0 : ℝ) b,
        (∫ w in Ioc (0 : ℝ) b,
          w * Real.exp (-β * n * (u * v * w) ^ 2 + β * Real.sqrt n * (u * v * w) * a))
          = ((Real.sqrt n * u) ^ 2)⁻¹
            * ((v ^ 2)⁻¹ * quadMomentPrimitive β a (Real.sqrt n * u * b * v)) := by
      intro v hv
      rw [twoDH01_inner β a b n (u * v) hn (mul_pos hu0 hv.1) hb,
        show Real.sqrt n * (u * v) * b = Real.sqrt n * u * b * v by ring]
      have hv0 : v ≠ 0 := hv.1.ne'
      field_simp
    rw [setIntegral_congr_fun measurableSet_Ioc hin, MeasureTheory.integral_const_mul,
      integral_quadMomentPrimitive_div_sq_eq β a (Real.sqrt n * u * b) b (by positivity) hb,
      show Real.sqrt n * u * b * b = Real.sqrt n * b ^ 2 * u by ring]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioc hmid, MeasureTheory.integral_const_mul,
    integral_quadPowerPrimitive_div_eq β a (Real.sqrt n * b ^ 2) b (by positivity) hb,
    show Real.sqrt n * b ^ 2 * b = Real.sqrt n * b ^ 3 by ring,
    integral_quadPowerPrimitive_div β a _ hβ (by positivity)]

/-- **Multiplicity two for exponents `(1/2, 1/2, 1)`**:
`Z(n) ~ (b S_{1/2}(a)/4) · n^{-1/2} · log n`. -/
theorem threeDIntegralH001_isEquivalent (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) :
    (fun n : ℝ => threeDIntegralH001 β a b n) ~[atTop]
      fun n : ℝ => b * fluctuation β (1 / 2) a / 4 * (n ^ (-(1 / 2 : ℝ)) * Real.log n) := by
  set A := quadMass β a with hA
  have hA0 : 0 < A := quadMass_pos β a hβ
  set E := Real.exp (β * a ^ 2 / 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set M := quadMoment β a with hM
  have hM0 : 0 ≤ M := quadMoment_nonneg β a
  have hmain : (fun n : ℝ => threeDIntegralH001 β a b n) ~[atTop]
      fun n : ℝ => b * A / 2 * (Real.log n / Real.sqrt n) := by
    apply IsLittleO.isEquivalent
    have hbig : (fun n : ℝ => threeDIntegralH001 β a b n - b * A / 2 * (Real.log n / Real.sqrt n))
        =O[atTop] fun n : ℝ => 1 / Real.sqrt n := by
      apply IsBigO.of_bound (b * (E + M + 3 * A * |Real.log b| + A))
      filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / b ^ 6)] with n hn hnb
      have hn0 : (0 : ℝ) < n := by linarith
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
      have hL : 1 ≤ Real.sqrt n * b ^ 3 := by
        have h1 : (1 / b ^ 3) ^ 2 ≤ n := by rw [div_pow, one_pow, ← pow_mul]; exact hnb
        have h2 : 1 / b ^ 3 ≤ Real.sqrt n := by
          rw [Real.le_sqrt (by positivity) hn0.le]; exact h1
        calc (1 : ℝ) = 1 / b ^ 3 * b ^ 3 := by field_simp
          _ ≤ Real.sqrt n * b ^ 3 := by gcongr
      have hH := logPrimitive_bounds β a (Real.sqrt n * b ^ 3) hβ hL
      have hlogL : Real.log (Real.sqrt n * b ^ 3) = Real.log n / 2 + 3 * Real.log b := by
        rw [Real.log_mul hsn.ne' (by positivity), Real.log_sqrt hn0.le, Real.log_pow]
        push_cast; ring
      rw [hlogL] at hH
      have hK0 := quadPowerPrimitive_nonneg β a (Real.sqrt n * b ^ 3) (by positivity)
      have hKA := quadPowerPrimitive_le_mass β a (Real.sqrt n * b ^ 3) hβ (by positivity)
      rw [threeDIntegralH001_eq β a b n hβ hn0 hb, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.sqrt n)]
      set H := logPrimitive β a (Real.sqrt n * b ^ 3)
      set K := quadPowerPrimitive β a (Real.sqrt n * b ^ 3)
      have hlb := le_abs_self (Real.log b)
      have hlb' := neg_abs_le (Real.log b)
      have hD : |H - K - A * (Real.log n / 2)| ≤ E + M + 3 * A * |Real.log b| + A := by
        rw [abs_le]; constructor <;> nlinarith [hH.1, hH.2, mul_le_mul_of_nonneg_left hlb hA0.le,
          mul_le_mul_of_nonneg_left hlb' hA0.le]
      calc |b / Real.sqrt n * (H - K) - b * A / 2 * (Real.log n / Real.sqrt n)|
          = b / Real.sqrt n * |H - K - A * (Real.log n / 2)| := by
            rw [show b / Real.sqrt n * (H - K) - b * A / 2 * (Real.log n / Real.sqrt n)
              = b / Real.sqrt n * (H - K - A * (Real.log n / 2)) by ring, abs_mul,
              abs_of_pos (by positivity)]
        _ ≤ b / Real.sqrt n * (E + M + 3 * A * |Real.log b| + A) := by gcongr
        _ = b * (E + M + 3 * A * |Real.log b| + A) * (1 / Real.sqrt n) := by ring
    exact (hbig.trans_isLittleO isLittleO_inv_sqrt_log).const_mul_right (by positivity)
  refine hmain.congr_right ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
  rw [hA, quadMass_eq β a, Real.sqrt_eq_rpow, Real.rpow_neg hn.le]
  ring

end Laplace.Grammar
