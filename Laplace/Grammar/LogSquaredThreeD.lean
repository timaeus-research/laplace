/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TwoDNoLog

/-!
# The first `(log n)²`: the three-dimensional standard integral (grammar §4.2, `d = 3`)

For `d = 3`, `k = (1,1,1)`, `h = (0,0,0)` all three candidate exponents equal `1/2`, so the
multiplicity is `3` and the paper's expansion carries `(log n)^{m-1} = (log n)²`. Iterating the
`d = 2` reduction once more,

  `Z₃(n) = ∫₀^b∫₀^b∫₀^b e^{-βn(uvw)² + β√n uvw a} = n^{-1/2} H₂(√n b³)`,   `H₂(L) = ∫₀^L H(x)/x dx`,

with `H` the logarithmic primitive of `LogTwoD.lean`; and since `H(x) = A log x + O(1)`,
`H₂(L) = (A/2) log² L + O(log L)`. Hence

  `Z₃(n) ~ (S_{1/2}(a)/16) · n^{-1/2} · (log n)²`.

Every step is again one-dimensional; the squeeze for `H₂` is the one for `H` integrated once against
`dx/x` (`∫₁^L log x/x = log² L/2`). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter

namespace Laplace.Grammar

/-- `|F(t)| ≤ E |t|` for every real `t`. -/
theorem abs_quadPrimitive_le (β a t : ℝ) (hβ : 0 < β) :
    |quadPrimitive β a t| ≤ Real.exp (β * a ^ 2 / 2) * |t| := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
    (C := Real.exp (β * a ^ 2 / 2)) (f := quadKernel β a) fun x _ => by
      rw [Real.norm_eq_abs, abs_of_pos (quadKernel_pos β a x)]; exact quadKernel_le_const β a x hβ
  rw [Real.norm_eq_abs, sub_zero] at this
  exact this

/-- `|F(t)/t| ≤ E` for every real `t`. -/
theorem abs_quadPrimitive_div_le (β a t : ℝ) (hβ : 0 < β) :
    |quadPrimitive β a t / t| ≤ Real.exp (β * a ^ 2 / 2) := by
  rcases eq_or_ne t 0 with h0 | h0
  · simp [h0, (Real.exp_pos _).le]
  · rw [abs_div, div_le_iff₀ (abs_pos.2 h0)]; exact abs_quadPrimitive_le β a t hβ

theorem quadPrimitive_div_intervalIntegrable (β a c d : ℝ) (hβ : 0 < β) :
    IntervalIntegrable (fun t => quadPrimitive β a t / t) volume c d := by
  refine (intervalIntegrable_const (c := Real.exp (β * a ^ 2 / 2))).mono_fun
    ((quadPrimitive_continuous β a).measurable.div measurable_id).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  beta_reduce
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact abs_quadPrimitive_div_le β a t hβ

theorem logPrimitive_eq_intervalIntegral (β a x : ℝ) (hx : 0 ≤ x) :
    logPrimitive β a x = ∫ t in (0 : ℝ)..x, quadPrimitive β a t / t :=
  (intervalIntegral.integral_of_le hx).symm

theorem logPrimitive_primitive_continuous (β a : ℝ) (hβ : 0 < β) :
    Continuous (fun x : ℝ => ∫ t in (0 : ℝ)..x, quadPrimitive β a t / t) :=
  intervalIntegral.continuous_primitive
    (fun c d => quadPrimitive_div_intervalIntegrable β a c d hβ) 0

theorem logPrimitive_nonneg (β a x : ℝ) : 0 ≤ logPrimitive β a x :=
  setIntegral_nonneg measurableSet_Ioc fun t ht =>
    div_nonneg (quadPrimitive_nonneg β a t ht.1.le) ht.1.le

/-- `H(x) ≤ E x` for `x ≥ 0`. -/
theorem logPrimitive_le_linear (β a x : ℝ) (hβ : 0 < β) (hx : 0 ≤ x) :
    logPrimitive β a x ≤ Real.exp (β * a ^ 2 / 2) * x := by
  rw [logPrimitive_eq_intervalIntegral β a x hx]
  calc (∫ t in (0 : ℝ)..x, quadPrimitive β a t / t)
      ≤ ∫ _ in (0 : ℝ)..x, Real.exp (β * a ^ 2 / 2) :=
        intervalIntegral.integral_mono_on hx (quadPrimitive_div_intervalIntegrable β a 0 x hβ)
          (continuous_const.intervalIntegrable _ _) fun t _ =>
          (le_abs_self _).trans (abs_quadPrimitive_div_le β a t hβ)
    _ = _ := by rw [intervalIntegral.integral_const]; simp [mul_comm]

theorem logPrimitive_div_le (β a x : ℝ) (hβ : 0 < β) (hx : 0 < x) :
    logPrimitive β a x / x ≤ Real.exp (β * a ^ 2 / 2) := by
  rw [div_le_iff₀ hx]; exact logPrimitive_le_linear β a x hβ hx.le

theorem logPrimitive_div_integrableOn (β a L : ℝ) (hβ : 0 < β) :
    IntegrableOn (fun x => logPrimitive β a x / x) (Ioc 0 L) := by
  have hcont := logPrimitive_primitive_continuous β a hβ
  have h1 : IntegrableOn (fun x => (∫ t in (0 : ℝ)..x, quadPrimitive β a t / t) / x) (Ioc 0 L) := by
    refine Integrable.mono' (g := fun _ => Real.exp (β * a ^ 2 / 2))
      (integrableOn_const measure_Ioc_lt_top.ne)
      (hcont.measurable.div measurable_id).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx.1
    rw [← logPrimitive_eq_intervalIntegral β a x hx0.le, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (logPrimitive_nonneg β a x) hx0.le)]
    exact logPrimitive_div_le β a x hβ hx0
  refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioc
  beta_reduce; rw [logPrimitive_eq_intervalIntegral β a x hx.1.le]

/-- The iterated logarithmic primitive `H₂(L) = ∫₀^L H(x)/x dx`. -/
noncomputable def logLogPrimitive (β a L : ℝ) : ℝ := ∫ x in Ioc (0 : ℝ) L, logPrimitive β a x / x

/-- `∫₁^L log x / x dx = log² L / 2`. -/
theorem integral_Ioc_log_div (L : ℝ) (hL : 1 ≤ L) :
    (∫ x in Ioc (1 : ℝ) L, Real.log x / x) = Real.log L ^ 2 / 2 := by
  rw [← intervalIntegral.integral_of_le hL]
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) L,
      HasDerivAt (fun x => Real.log x ^ 2 / 2) (Real.log x / x) x := by
    intro x hx
    rw [Set.uIcc_of_le hL] at hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx.1
    have h := ((Real.hasDerivAt_log hx0.ne').pow 2).div_const 2
    exact h.congr_deriv (by field_simp; ring)
  have hint : IntervalIntegrable (fun x : ℝ => Real.log x / x) volume 1 L := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hL]
    exact (Real.continuousOn_log.mono fun x hx => (lt_of_lt_of_le one_pos hx.1).ne').div
      continuousOn_id fun x hx => (lt_of_lt_of_le one_pos hx.1).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- `∫₁^L dx/x = log L`. -/
theorem integral_Ioc_inv (L : ℝ) (hL : 1 ≤ L) : (∫ x in Ioc (1 : ℝ) L, x⁻¹) = Real.log L := by
  rw [← intervalIntegral.integral_of_le hL, integral_inv_of_pos one_pos (lt_of_lt_of_le one_pos hL),
    div_one]

/-- **The `(log L)²` squeeze**: for `L ≥ 1`,
`A log² L/2 - M log L ≤ H₂(L) ≤ A log² L/2 + E log L + E`. -/
theorem logLogPrimitive_bounds (β a L : ℝ) (hβ : 0 < β) (hL : 1 ≤ L) :
    quadMass β a * Real.log L ^ 2 / 2 - quadMoment β a * Real.log L ≤ logLogPrimitive β a L ∧
      logLogPrimitive β a L ≤ quadMass β a * Real.log L ^ 2 / 2
        + Real.exp (β * a ^ 2 / 2) * Real.log L + Real.exp (β * a ^ 2 / 2) := by
  set E := Real.exp (β * a ^ 2 / 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hint := logPrimitive_div_integrableOn β a L hβ
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioc 1 L) :=
    Set.disjoint_left.2 fun x h1 h2 => (not_lt.2 h1.2) h2.1
  have hsplit := setIntegral_union hdisj measurableSet_Ioc (hint.mono_set (Ioc_subset_Ioc_right hL))
    (hint.mono_set (Ioc_subset_Ioc_left zero_le_one))
  rw [Ioc_union_Ioc_eq_Ioc zero_le_one hL] at hsplit
  -- the piece on (0, 1]
  have h1_nonneg : 0 ≤ ∫ x in Ioc (0 : ℝ) 1, logPrimitive β a x / x :=
    setIntegral_nonneg measurableSet_Ioc fun x hx =>
      div_nonneg (logPrimitive_nonneg β a x) hx.1.le
  have h1_le : (∫ x in Ioc (0 : ℝ) 1, logPrimitive β a x / x) ≤ E := by
    calc (∫ x in Ioc (0 : ℝ) 1, logPrimitive β a x / x) ≤ ∫ _ in Ioc (0 : ℝ) 1, E :=
          setIntegral_mono_on (hint.mono_set (Ioc_subset_Ioc_right hL))
            (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc fun x hx =>
            logPrimitive_div_le β a x hβ hx.1
      _ = E := by rw [setIntegral_const]; simp [Measure.real, Real.volume_Ioc]
  -- integrability of the comparison functions on (1, L]
  have hlogint : IntegrableOn (fun x : ℝ => Real.log x / x) (Ioc 1 L) := by
    have : ContinuousOn (fun x : ℝ => Real.log x / x) (Icc 1 L) :=
      (Real.continuousOn_log.mono fun x hx => (lt_of_lt_of_le one_pos hx.1).ne').div
        continuousOn_id fun x hx => (lt_of_lt_of_le one_pos hx.1).ne'
    exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hinvint : IntegrableOn (fun x : ℝ => x⁻¹) (Ioc 1 L) := by
    have : ContinuousOn (fun x : ℝ => x⁻¹) (Icc 1 L) :=
      continuousOn_inv₀.mono fun x hx => (lt_of_lt_of_le one_pos hx.1).ne'
    exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hHint := hint.mono_set (Ioc_subset_Ioc_left zero_le_one)
  -- comparison integrals
  have hlow_val : (∫ x in Ioc (1 : ℝ) L, (quadMass β a * (Real.log x / x) - quadMoment β a * x⁻¹))
      = quadMass β a * Real.log L ^ 2 / 2 - quadMoment β a * Real.log L := by
    rw [MeasureTheory.integral_sub (hlogint.const_mul _) (hinvint.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      integral_Ioc_log_div L hL, integral_Ioc_inv L hL]
    ring
  have hhigh_val : (∫ x in Ioc (1 : ℝ) L, (quadMass β a * (Real.log x / x) + E * x⁻¹))
      = quadMass β a * Real.log L ^ 2 / 2 + E * Real.log L := by
    rw [MeasureTheory.integral_add (hlogint.const_mul _) (hinvint.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      integral_Ioc_log_div L hL, integral_Ioc_inv L hL]
    ring
  have h2_lo : quadMass β a * Real.log L ^ 2 / 2 - quadMoment β a * Real.log L
      ≤ ∫ x in Ioc (1 : ℝ) L, logPrimitive β a x / x := by
    rw [← hlow_val]
    refine setIntegral_mono_on ((hlogint.const_mul _).sub (hinvint.const_mul _)) hHint
      measurableSet_Ioc fun x hx => ?_
    have hx0 : (0 : ℝ) < x := one_pos.trans hx.1
    have hH := (logPrimitive_bounds β a x hβ hx.1.le).1
    rw [show quadMass β a * (Real.log x / x) - quadMoment β a * x⁻¹
        = (quadMass β a * Real.log x - quadMoment β a) / x by field_simp,
      div_le_div_iff_of_pos_right hx0]
    exact hH
  have h2_hi : (∫ x in Ioc (1 : ℝ) L, logPrimitive β a x / x)
      ≤ quadMass β a * Real.log L ^ 2 / 2 + E * Real.log L := by
    rw [← hhigh_val]
    refine setIntegral_mono_on hHint ((hlogint.const_mul _).add (hinvint.const_mul _))
      measurableSet_Ioc fun x hx => ?_
    have hx0 : (0 : ℝ) < x := one_pos.trans hx.1
    have hH := (logPrimitive_bounds β a x hβ hx.1.le).2
    rw [show quadMass β a * (Real.log x / x) + E * x⁻¹
        = (quadMass β a * Real.log x + E) / x by field_simp,
      div_le_div_iff_of_pos_right hx0]
    exact hH
  rw [logLogPrimitive, hsplit]
  constructor <;> linarith

/-- `∫₀^b F(cu)/u du = H(cb)`. -/
theorem integral_quadPrimitive_div_eq (β a c b : ℝ) (hc : 0 < c) (hb : 0 < b) :
    (∫ u in Ioc (0 : ℝ) b, quadPrimitive β a (c * u) / u) = logPrimitive β a (c * b) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hpt : ∀ u, quadPrimitive β a (c * u) / u = c * (quadPrimitive β a (c * u) / (c * u)) := by
    intro u
    rcases eq_or_ne u 0 with h0 | h0
    · simp [h0, quadPrimitive]
    · field_simp
  simp_rw [hpt]
  have hsub : (∫ u in (0 : ℝ)..b, quadPrimitive β a (c * u) / (c * u))
      = c⁻¹ • ∫ x in (c * 0)..(c * b), quadPrimitive β a x / x :=
    intervalIntegral.integral_comp_mul_left (fun x => quadPrimitive β a x / x) hc0
  rw [← intervalIntegral.integral_of_le hb.le, intervalIntegral.integral_const_mul, hsub, mul_zero,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul,
    intervalIntegral.integral_of_le (by positivity), logPrimitive]

/-- `∫₀^b H(cu)/u du = H₂(cb)`. -/
theorem integral_logPrimitive_div_eq (β a c b : ℝ) (hc : 0 < c) (hb : 0 < b) :
    (∫ u in Ioc (0 : ℝ) b, logPrimitive β a (c * u) / u) = logLogPrimitive β a (c * b) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hpt : ∀ u, logPrimitive β a (c * u) / u = c * (logPrimitive β a (c * u) / (c * u)) := by
    intro u
    rcases eq_or_ne u 0 with h0 | h0
    · simp [h0, logPrimitive]
    · field_simp
  simp_rw [hpt]
  have hsub : (∫ u in (0 : ℝ)..b, logPrimitive β a (c * u) / (c * u))
      = c⁻¹ • ∫ x in (c * 0)..(c * b), logPrimitive β a x / x :=
    intervalIntegral.integral_comp_mul_left (fun x => logPrimitive β a x / x) hc0
  rw [← intervalIntegral.integral_of_le hb.le, intervalIntegral.integral_const_mul, hsub, mul_zero,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul,
    intervalIntegral.integral_of_le (by positivity), logLogPrimitive]

/-- The `d = 3`, `k = (1,1,1)`, `h = (0,0,0)` chart standard integral (iterated form). -/
noncomputable def threeDIntegral (β a b n : ℝ) : ℝ :=
  ∫ u in Ioc (0 : ℝ) b, ∫ v in Ioc (0 : ℝ) b, ∫ w in Ioc (0 : ℝ) b,
    Real.exp (-β * n * (u * v * w) ^ 2 + β * Real.sqrt n * (u * v * w) * a)

/-- **Reduction**: `Z₃(n) = n^{-1/2} H₂(√n b³)`. -/
theorem threeDIntegral_eq (β a b n : ℝ) (hn : 0 < n) (hb : 0 < b) :
    threeDIntegral β a b n = (Real.sqrt n)⁻¹ * logLogPrimitive β a (Real.sqrt n * b ^ 3) := by
  unfold threeDIntegral
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hmid : ∀ u ∈ Ioc (0 : ℝ) b,
      (∫ v in Ioc (0 : ℝ) b, ∫ w in Ioc (0 : ℝ) b,
        Real.exp (-β * n * (u * v * w) ^ 2 + β * Real.sqrt n * (u * v * w) * a))
        = (Real.sqrt n)⁻¹ * (logPrimitive β a (Real.sqrt n * b ^ 2 * u) / u) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hin : ∀ v ∈ Ioc (0 : ℝ) b,
        (∫ w in Ioc (0 : ℝ) b,
          Real.exp (-β * n * (u * v * w) ^ 2 + β * Real.sqrt n * (u * v * w) * a))
          = (Real.sqrt n * u)⁻¹ * (quadPrimitive β a (Real.sqrt n * u * b * v) / v) := by
      intro v hv
      rw [twoD_inner β a b n (u * v) hn (mul_pos hu0 hv.1) hb,
        show Real.sqrt n * (u * v) * b = Real.sqrt n * u * b * v by ring]
      field_simp
    rw [setIntegral_congr_fun measurableSet_Ioc hin, MeasureTheory.integral_const_mul,
      integral_quadPrimitive_div_eq β a (Real.sqrt n * u * b) b (by positivity) hb,
      show Real.sqrt n * u * b * b = Real.sqrt n * b ^ 2 * u by ring]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioc hmid, MeasureTheory.integral_const_mul,
    integral_logPrimitive_div_eq β a (Real.sqrt n * b ^ 2) b (by positivity) hb,
    show Real.sqrt n * b ^ 2 * b = Real.sqrt n * b ^ 3 by ring]

/-- `(log n + 1)/√n = o(log² n/√n)`. -/
theorem isLittleO_log_add_one_div_sqrt :
    (fun n : ℝ => (Real.log n + 1) / Real.sqrt n) =o[atTop]
      fun n : ℝ => Real.log n ^ 2 / Real.sqrt n := by
  refine isLittleO_of_tendsto' ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn h
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (zero_lt_one.trans hn)
    have hlog : 0 < Real.log n := Real.log_pos hn
    exact absurd h (div_ne_zero (by positivity) hsn.ne')
  · have h1 : Tendsto (fun n : ℝ => (Real.log n)⁻¹) atTop (nhds 0) :=
      Real.tendsto_log_atTop.inv_tendsto_atTop
    have h2 := h1.add (h1.mul h1)
    simp only [zero_add, zero_mul] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (zero_lt_one.trans hn)
    have hlog : 0 < Real.log n := Real.log_pos hn
    field_simp

/-- Algebraic core of the `(log n)²` bound: from the `H₂` squeeze at `log L = ℓ/2 + 3 b'`
(`|b'| ≤ lb`) to `|H₂ - A ℓ²/8| ≤ K (ℓ + 1)`. -/
theorem logsq_bound_helper (A E M ℓ b' lb H₂ : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hℓ : 0 ≤ ℓ) (hlb0 : 0 ≤ lb) (hb1 : b' ≤ lb) (hb2 : -lb ≤ b')
    (hlo : A * (ℓ / 2 + 3 * b') ^ 2 / 2 - M * (ℓ / 2 + 3 * b') ≤ H₂)
    (hhi : H₂ ≤ A * (ℓ / 2 + 3 * b') ^ 2 / 2 + E * (ℓ / 2 + 3 * b') + E) :
    |H₂ - A * ℓ ^ 2 / 8|
      ≤ ((E + M) / 2 + 3 * (E + M) * lb + E + 3 * A / 2 * lb + 9 * A / 2 * b' ^ 2) * (ℓ + 1) := by
  have h1 : A * (b' * ℓ) ≤ A * (lb * ℓ) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb1 hℓ) hA
  have h2 : A * (-(lb * ℓ)) ≤ A * (b' * ℓ) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hA
  have h3 : E * b' ≤ E * lb := mul_le_mul_of_nonneg_left hb1 hE
  have h4 : M * (-lb) ≤ M * b' := mul_le_mul_of_nonneg_left hb2 hM
  have n1 : 0 ≤ M * ℓ := mul_nonneg hM hℓ
  have n2 : 0 ≤ E * ℓ := mul_nonneg hE hℓ
  have n3 : 0 ≤ E * (lb * ℓ) := mul_nonneg hE (mul_nonneg hlb0 hℓ)
  have n4 : 0 ≤ M * (lb * ℓ) := mul_nonneg hM (mul_nonneg hlb0 hℓ)
  have n5 : 0 ≤ A * (lb * ℓ) := mul_nonneg hA (mul_nonneg hlb0 hℓ)
  have n6 : 0 ≤ A * (b' ^ 2 * ℓ) := mul_nonneg hA (mul_nonneg (sq_nonneg _) hℓ)
  have n7 : 0 ≤ A * b' ^ 2 := mul_nonneg hA (sq_nonneg _)
  have n8 : 0 ≤ E * lb := mul_nonneg hE hlb0
  have n9 : 0 ≤ M * lb := mul_nonneg hM hlb0
  have n10 : 0 ≤ A * lb := mul_nonneg hA hlb0
  rw [abs_le]
  constructor <;> nlinarith

/-- **The first `(log n)²`** (grammar §4.2, `d = 3`, `k = (1,1,1)`, `h = (0,0,0)`):
`Z₃(n) ~ (S_{1/2}(a)/16) · n^{-1/2} · (log n)²` — the candidate exponent `1/2` with
multiplicity `3`. -/
theorem threeDIntegral_isEquivalent (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) :
    (fun n : ℝ => threeDIntegral β a b n) ~[atTop]
      fun n : ℝ => fluctuation β (1 / 2) a / 16 * (n ^ (-(1 / 2 : ℝ)) * Real.log n ^ 2) := by
  set A := quadMass β a with hA
  have hA0 : 0 < A := quadMass_pos β a hβ
  set E := Real.exp (β * a ^ 2 / 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set M := quadMoment β a with hM
  have hM0 : 0 ≤ M := quadMoment_nonneg β a
  set K : ℝ := (E + M) / 2 + 3 * (E + M) * |Real.log b| + E + 3 * A / 2 * |Real.log b|
    + 9 * A / 2 * Real.log b ^ 2 with hK
  have hmain : (fun n : ℝ => threeDIntegral β a b n) ~[atTop]
      fun n : ℝ => A / 8 * (Real.log n ^ 2 / Real.sqrt n) := by
    apply IsLittleO.isEquivalent
    have hbig : (fun n : ℝ => threeDIntegral β a b n - A / 8 * (Real.log n ^ 2 / Real.sqrt n))
        =O[atTop] fun n : ℝ => (Real.log n + 1) / Real.sqrt n := by
      apply IsBigO.of_bound K
      filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / b ^ 6)] with n hn hnb
      have hn0 : (0 : ℝ) < n := by linarith
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
      have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn
      have hL : 1 ≤ Real.sqrt n * b ^ 3 := by
        have h1 : (1 / b ^ 3) ^ 2 ≤ n := by rw [div_pow, one_pow, ← pow_mul]; exact hnb
        have h2 : 1 / b ^ 3 ≤ Real.sqrt n := by
          rw [Real.le_sqrt (by positivity) hn0.le]; exact h1
        calc (1 : ℝ) = 1 / b ^ 3 * b ^ 3 := by field_simp
          _ ≤ Real.sqrt n * b ^ 3 := by gcongr
      have hH := logLogPrimitive_bounds β a (Real.sqrt n * b ^ 3) hβ hL
      have hlogL : Real.log (Real.sqrt n * b ^ 3) = Real.log n / 2 + 3 * Real.log b := by
        rw [Real.log_mul hsn.ne' (by positivity), Real.log_sqrt hn0.le, Real.log_pow]
        push_cast; ring
      have hlogL0 : 0 ≤ Real.log (Real.sqrt n * b ^ 3) := Real.log_nonneg hL
      rw [hlogL] at hH hlogL0
      rw [threeDIntegral_eq β a b n hn0 hb, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < (Real.log n + 1) / Real.sqrt n)]
      set H2 := logLogPrimitive β a (Real.sqrt n * b ^ 3) with hH2
      have hD : |H2 - A / 8 * Real.log n ^ 2| ≤ K * (Real.log n + 1) := by
        have := logsq_bound_helper A E M (Real.log n) (Real.log b) |Real.log b| H2 hA0.le hE0.le hM0
          hlogn (abs_nonneg _) (le_abs_self _) (neg_abs_le _) hH.1 hH.2
        rw [hK]
        convert this using 2
        ring
      calc |(Real.sqrt n)⁻¹ * H2 - A / 8 * (Real.log n ^ 2 / Real.sqrt n)|
          = (Real.sqrt n)⁻¹ * |H2 - A / 8 * Real.log n ^ 2| := by
            rw [show (Real.sqrt n)⁻¹ * H2 - A / 8 * (Real.log n ^ 2 / Real.sqrt n)
              = (Real.sqrt n)⁻¹ * (H2 - A / 8 * Real.log n ^ 2) by field_simp, abs_mul,
              abs_of_pos (inv_pos.2 hsn)]
        _ ≤ (Real.sqrt n)⁻¹ * (K * (Real.log n + 1)) := by gcongr
        _ = K * ((Real.log n + 1) / Real.sqrt n) := by ring
    have hlit := hbig.trans_isLittleO isLittleO_log_add_one_div_sqrt
    exact hlit.const_mul_right (by positivity)
  refine hmain.congr_right ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
  rw [hA, quadMass_eq β a, Real.sqrt_eq_rpow, Real.rpow_neg hn.le]
  ring

end Laplace.Grammar
