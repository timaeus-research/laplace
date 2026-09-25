/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ValuationLP

/-!
# Non-uniformity at a wall of the valuation fan: the logarithmic multiplicity interpolates

Astra's warning example (round 19): for the two-dimensional chart integral

  `Z(t, s) = ∫₀¹ ∫₀¹ e^{-t x (y + s)} dy dx`

the exact identity

  `t Z(t, s) = log ((1 + s)/s) − ∫_{ts}^{t(1+s)} e^{-u}/u du`   (`wallZ_eq`)

with the remainder in `[0, e^{-ts}/(ts)]` (`wallRem_nonneg`, `wallRem_le`) shows that along the
coupled path `s = t^{-σ}`:

* for fixed `0 < σ < 1` the leading order is `σ t^{-1} log t` (exponent `1`, logarithmic
  multiplicity `1`, constant `σ`: `tendsto_wallZ_fixed`);
* at the wall `σ = 0` (`s = 1`) it is `t^{-1} log 2` (multiplicity `0`: `tendsto_wallZ_wall`);
* along the moving path `s(t) = e^{-√(log t)}`, i.e. `σ(t) = (log t)^{-1/2}`, which stays inside
  the open cell `σ > 0` for all `t`, the leading order is `t^{-1} √(log t)`
  (`tendsto_wallZ_moving`): neither the fixed-`σ` law `t^{-1} log t` nor the wall law `t^{-1}`.

So fixed-`σ` asymptotics are not uniform on the open cells of the valuation fan: approaching a
wall, the logarithmic multiplicity interpolates, and the correct wall variable is
`τ = σ log t`, in which `t Z = log (1 + e^{τ}) + o(1)`. This is the mechanism the uniform
stratified response theorem must resolve, and it is invisible to the LP value, which is `1` on
the whole cell.
-/

open MeasureTheory Filter Topology Set intervalIntegral
open scoped Interval

namespace Laplace.Multi

/-- The two-dimensional wall integral `Z(t, s) = ∫₀¹ ∫₀¹ e^{-t x (y + s)} dy dx`. -/
noncomputable def wallZ (t s : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, Real.exp (-(t * x * (y + s)))

/-- The remainder `∫_{ts}^{t(1+s)} e^{-u}/u du`. -/
noncomputable def wallRem (t s : ℝ) : ℝ := ∫ u in (t * s)..(t * (1 + s)), Real.exp (-u) / u

/-- The exponential integral `G(a) = ∫₀^a (1 − e^{-u})/u du`. -/
noncomputable def expInt (a : ℝ) : ℝ := ∫ u in (0 : ℝ)..a, (1 - Real.exp (-u)) / u

/-! ### The one-dimensional profile `(1 − e^{-u})/u` -/

theorem one_sub_exp_neg_div_le {u : ℝ} (hu : 0 ≤ u) : (1 - Real.exp (-u)) / u ≤ 1 := by
  rcases hu.lt_or_eq with hu | hu
  · rw [div_le_one hu]
    linarith [Real.add_one_le_exp (-u)]
  · subst hu
    simp

theorem one_sub_exp_neg_div_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ (1 - Real.exp (-u)) / u := by
  refine div_nonneg ?_ hu
  linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)]

theorem intervalIntegrable_one_sub_exp_div {a : ℝ} (ha : 0 ≤ a) :
    IntervalIntegrable (fun u ↦ (1 - Real.exp (-u)) / u) volume 0 a := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  rw [uIoc_of_le ha]
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu ↦ ?_)
  beta_reduce
  rw [Real.norm_eq_abs, norm_one, abs_of_nonneg (one_sub_exp_neg_div_nonneg hu.1.le)]
  exact one_sub_exp_neg_div_le hu.1.le

/-- `∫₀¹ (1 − e^{-a x})/x dx = G(a)`. -/
theorem integral_one_sub_exp_div_eq_expInt {a : ℝ} (ha : 0 ≤ a) :
    ∫ x in (0 : ℝ)..1, (1 - Real.exp (-(a * x))) / x = expInt a := by
  rcases ha.lt_or_eq with ha | ha
  · have e : ∀ x : ℝ, (1 - Real.exp (-(a * x))) / x =
        a * ((1 - Real.exp (-(a * x))) / (a * x)) := by
      intro x
      rcases eq_or_ne x 0 with hx | hx
      · simp [hx]
      · field_simp
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul,
      integral_comp_mul_left (fun u ↦ (1 - Real.exp (-u)) / u) ha.ne', mul_zero, mul_one,
      smul_eq_mul, mul_inv_cancel_left₀ ha.ne']
    rfl
  · subst ha
    simp [expInt]

theorem intervalIntegrable_one_sub_exp_mul_div {a : ℝ} (ha : 0 ≤ a) :
    IntervalIntegrable (fun x ↦ (1 - Real.exp (-(a * x))) / x) volume 0 1 := by
  rcases ha.lt_or_eq with ha | ha
  · have h := ((intervalIntegrable_one_sub_exp_div ha.le).comp_mul_left (c := a)).const_mul a
    rw [zero_div, div_self ha.ne'] at h
    refine h.congr fun x _ ↦ ?_
    rcases eq_or_ne x 0 with hx | hx
    · simp [hx]
    · field_simp
  · subst ha
    have : (fun x : ℝ ↦ (1 - Real.exp (-(0 * x))) / x) = fun _ ↦ 0 := by funext x; simp
    rw [this]
    exact intervalIntegrable_const

/-- `G(b) − G(a) = ∫_a^b (1 − e^{-u})/u du`. -/
theorem expInt_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    expInt b - expInt a = ∫ u in a..b, (1 - Real.exp (-u)) / u :=
  integral_interval_sub_left (intervalIntegrable_one_sub_exp_div hb)
    (intervalIntegrable_one_sub_exp_div ha)

/-- `∫_a^b (1 − e^{-u})/u du = log (b/a) − ∫_a^b e^{-u}/u du` for `0 < a ≤ b`. -/
theorem integral_one_sub_exp_div_eq_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ u in a..b, (1 - Real.exp (-u)) / u = Real.log (b / a) - ∫ u in a..b, Real.exp (-u) / u := by
  have hpos : ∀ u ∈ uIcc a b, 0 < u := fun u hu ↦ by
    rw [uIcc_of_le hab] at hu
    exact ha.trans_le hu.1
  have h1 : IntervalIntegrable (fun u : ℝ ↦ 1 / u) volume a b :=
    (continuousOn_const.div continuousOn_id fun u hu ↦ (hpos u hu).ne').intervalIntegrable
  have h2 : IntervalIntegrable (fun u : ℝ ↦ Real.exp (-u) / u) volume a b :=
    ((Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
      fun u hu ↦ (hpos u hu).ne').intervalIntegrable
  rw [← integral_one_div (fun h ↦ (hpos 0 h).false), ← integral_sub h1 h2]
  refine integral_congr fun u hu ↦ ?_
  have := (hpos u hu).ne'
  field_simp

/-! ### The exact identity -/

/-- The inner integral: `∫₀¹ e^{-c (y + s)} dy = (e^{-cs} − e^{-c(1+s)})/c`. -/
theorem integral_exp_inner {c : ℝ} (hc : c ≠ 0) (s : ℝ) :
    ∫ y in (0 : ℝ)..1, Real.exp (-(c * (y + s))) =
      (Real.exp (-(c * s)) - Real.exp (-(c * (1 + s)))) / c := by
  have e : ∀ y : ℝ, Real.exp (-(c * (y + s))) = Real.exp (-(c * s)) * Real.exp (-c * y) := by
    intro y
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul,
    integral_comp_mul_left (fun u ↦ Real.exp u) (neg_ne_zero.mpr hc), integral_exp, mul_zero,
    mul_one, Real.exp_zero, smul_eq_mul]
  field_simp
  ring

/-- `t Z(t, s) = G(t(1 + s)) − G(ts)`. -/
theorem mul_wallZ_eq_expInt {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) :
    t * wallZ t s = expInt (t * (1 + s)) - expInt (t * s) := by
  have hts : 0 ≤ t * s := mul_nonneg ht.le hs
  have hts1 : 0 < t * (1 + s) := mul_pos ht (by linarith)
  unfold wallZ
  have hinner : ∀ᵐ x ∂volume, x ∈ Ι (0 : ℝ) 1 →
      (∫ y in (0 : ℝ)..1, Real.exp (-(t * x * (y + s)))) =
        ((1 - Real.exp (-(t * (1 + s) * x))) / x - (1 - Real.exp (-(t * s * x))) / x) / t := by
    refine Filter.Eventually.of_forall fun x hx ↦ ?_
    rw [uIoc_of_le zero_le_one] at hx
    have hx0 : x ≠ 0 := hx.1.ne'
    rw [integral_exp_inner (mul_ne_zero ht.ne' hx0)]
    rw [show t * (1 + s) * x = t * x * (1 + s) by ring, show t * s * x = t * x * s by ring]
    field_simp
    ring
  rw [intervalIntegral.integral_congr_ae hinner, intervalIntegral.integral_div,
    mul_div_cancel₀ _ ht.ne', integral_sub (intervalIntegrable_one_sub_exp_mul_div hts1.le)
      (intervalIntegrable_one_sub_exp_mul_div hts),
    integral_one_sub_exp_div_eq_expInt hts1.le, integral_one_sub_exp_div_eq_expInt hts]

/-- **The exact wall identity**: `t Z(t, s) = log ((1 + s)/s) − ∫_{ts}^{t(1+s)} e^{-u}/u du`. -/
theorem wallZ_eq {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    t * wallZ t s = Real.log ((1 + s) / s) - wallRem t s := by
  have hts : 0 < t * s := mul_pos ht hs
  rw [mul_wallZ_eq_expInt ht hs.le, expInt_sub hts.le (by positivity),
    integral_one_sub_exp_div_eq_log hts (by nlinarith), wallRem]
  congr 2
  field_simp

theorem wallRem_nonneg {t s : ℝ} (ht : 0 < t) (hs : 0 < s) : 0 ≤ wallRem t s := by
  unfold wallRem
  refine integral_nonneg (by nlinarith) fun u hu ↦ ?_
  exact div_nonneg (Real.exp_pos _).le (by linarith [hu.1, mul_pos ht hs])

/-- `∫_a^b e^{-u}/u du ≤ e^{-a}/a` for `0 < a ≤ b`. -/
theorem integral_exp_neg_div_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ u in a..b, Real.exp (-u) / u ≤ Real.exp (-a) / a := by
  have hpos : ∀ u ∈ uIcc a b, 0 < u := fun u hu ↦ by
    rw [uIcc_of_le hab] at hu
    exact ha.trans_le hu.1
  have h2 : IntervalIntegrable (fun u : ℝ ↦ Real.exp (-u) / u) volume a b :=
    ((Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
      fun u hu ↦ (hpos u hu).ne').intervalIntegrable
  have h3 : IntervalIntegrable (fun u : ℝ ↦ Real.exp (-u) / a) volume a b :=
    (Real.continuous_exp.comp continuous_neg).continuousOn.intervalIntegrable.div_const _
  calc ∫ u in a..b, Real.exp (-u) / u ≤ ∫ u in a..b, Real.exp (-u) / a := by
        refine integral_mono_on hab h2 h3 fun u hu ↦ ?_
        exact div_le_div_of_nonneg_left (Real.exp_pos _).le ha hu.1
    _ = (Real.exp (-a) - Real.exp (-b)) / a := by
        rw [intervalIntegral.integral_div, integral_comp_neg (f := fun u ↦ Real.exp u),
          integral_exp]
    _ ≤ Real.exp (-a) / a := by
        refine div_le_div_of_nonneg_right ?_ ha.le
        linarith [Real.exp_pos (-b)]

theorem wallRem_le {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    wallRem t s ≤ Real.exp (-(t * s)) / (t * s) :=
  integral_exp_neg_div_le (mul_pos ht hs) (by nlinarith)

/-! ### The three regimes -/

/-- `e^{-x}/x → 0` as `x → ∞`. -/
theorem tendsto_exp_neg_div_atTop : Tendsto (fun x : ℝ ↦ Real.exp (-x) / x) atTop (𝓝 0) := by
  have := Real.tendsto_exp_neg_atTop_nhds_zero.mul tendsto_inv_atTop_zero
  simpa [div_eq_mul_inv] using this

/-- The remainder vanishes along any path with `t s(t) → ∞`. -/
theorem tendsto_wallRem {s : ℝ → ℝ} (hs : ∀ᶠ t in atTop, 0 < s t)
    (hts : Tendsto (fun t ↦ t * s t) atTop atTop) :
    Tendsto (fun t ↦ wallRem t (s t)) atTop (𝓝 0) := by
  have hup := tendsto_exp_neg_div_atTop.comp hts
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hs, eventually_gt_atTop (0 : ℝ)] with t hst ht
    exact wallRem_nonneg ht hst
  · filter_upwards [hs, eventually_gt_atTop (0 : ℝ)] with t hst ht
    exact wallRem_le ht hst

/-- **The wall** `σ = 0` (`s = 1`): `t Z(t, 1) → log 2`, logarithmic multiplicity `0`. -/
theorem tendsto_wallZ_wall : Tendsto (fun t ↦ t * wallZ t 1) atTop (𝓝 (Real.log 2)) := by
  have hR := tendsto_wallRem (s := fun _ ↦ 1) (Filter.Eventually.of_forall fun _ ↦ one_pos)
    (by simp only [mul_one]; exact tendsto_id)
  have h2 : Tendsto (fun t ↦ Real.log ((1 + 1) / 1) - wallRem t 1) atTop
      (𝓝 (Real.log ((1 + 1) / 1) - 0)) := tendsto_const_nhds.sub hR
  norm_num at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [wallZ_eq ht one_pos]
  norm_num

/-- **Inside the cell** `0 < σ < 1`: `t Z(t, t^{-σ}) / log t → σ`, logarithmic multiplicity `1`
with constant `σ`. -/
theorem tendsto_wallZ_fixed {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    Tendsto (fun t ↦ t * wallZ t (t ^ (-σ)) / Real.log t) atTop (𝓝 σ) := by
  have hts : Tendsto (fun t : ℝ ↦ t * t ^ (-σ)) atTop atTop := by
    have := tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - σ)
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [show (1 - σ) = 1 + -σ by ring, Real.rpow_add ht, Real.rpow_one]
  have hR := tendsto_wallRem (s := fun t ↦ t ^ (-σ))
    (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht; exact Real.rpow_pos_of_pos ht _)
    hts
  have hlog1 : Tendsto (fun t : ℝ ↦ Real.log (1 + t ^ (-σ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ ↦ 1 + t ^ (-σ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_rpow_neg_atTop hσ)
    rw [add_zero] at h1
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    rw [Real.log_one] at this
    exact this
  have hnum : Tendsto (fun t ↦ Real.log (1 + t ^ (-σ)) - wallRem t (t ^ (-σ))) atTop (𝓝 0) := by
    simpa using hlog1.sub hR
  have hdiv := hnum.div_atTop Real.tendsto_log_atTop
  have : Tendsto (fun t ↦ σ + (Real.log (1 + t ^ (-σ)) - wallRem t (t ^ (-σ))) / Real.log t)
      atTop (𝓝 (σ + 0)) := tendsto_const_nhds.add hdiv
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos ht
  have hsp : 0 < t ^ (-σ) := Real.rpow_pos_of_pos ht0 _
  rw [wallZ_eq ht0 hsp]
  have hlog : Real.log ((1 + t ^ (-σ)) / t ^ (-σ)) = σ * Real.log t + Real.log (1 + t ^ (-σ)) := by
    rw [Real.log_div (by positivity) hsp.ne', Real.log_rpow ht0]
    ring
  rw [hlog]
  field_simp
  ring

/-- **The moving path** `s(t) = e^{-√(log t)}` (`σ(t) = (log t)^{-1/2} → 0` inside the cell):
`t Z / √(log t) → 1` — the logarithmic multiplicity interpolates between `1` and `0`. -/
theorem tendsto_wallZ_moving :
    Tendsto (fun t ↦ t * wallZ t (Real.exp (-Real.sqrt (Real.log t))) / Real.sqrt (Real.log t))
      atTop (𝓝 1) := by
  have hsqrt : Tendsto (fun t : ℝ ↦ Real.sqrt (Real.log t)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hts : Tendsto (fun t : ℝ ↦ t * Real.exp (-Real.sqrt (Real.log t))) atTop atTop := by
    have h1 : Tendsto (fun t : ℝ ↦ Real.log t - Real.sqrt (Real.log t)) atTop atTop := by
      have : Tendsto (fun x : ℝ ↦ x - Real.sqrt x) atTop atTop := by
        refine tendsto_atTop_mono' atTop ?_ (tendsto_id.atTop_div_const two_pos)
        filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
        have hx0 : 0 ≤ x := by linarith
        have : Real.sqrt x ≤ x / 2 := by
          rw [Real.sqrt_le_left (by linarith)]
          nlinarith
        simp only [id]
        linarith
      exact this.comp Real.tendsto_log_atTop
    have := Real.tendsto_exp_atTop.comp h1
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [Function.comp, Real.exp_sub, Real.exp_log ht, Real.exp_neg, div_eq_mul_inv]
  have hR := tendsto_wallRem (s := fun t ↦ Real.exp (-Real.sqrt (Real.log t)))
    (Filter.Eventually.of_forall fun _ ↦ Real.exp_pos _) hts
  have hlog1 : Tendsto (fun t : ℝ ↦ Real.log (1 + Real.exp (-Real.sqrt (Real.log t)))) atTop
      (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ ↦ Real.exp (-Real.sqrt (Real.log t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hsqrt
    have h1 : Tendsto (fun t : ℝ ↦ 1 + Real.exp (-Real.sqrt (Real.log t))) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add h0
    rw [add_zero] at h1
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    rw [Real.log_one] at this
    exact this
  have hnum : Tendsto (fun t ↦ Real.log (1 + Real.exp (-Real.sqrt (Real.log t))) -
      wallRem t (Real.exp (-Real.sqrt (Real.log t)))) atTop (𝓝 0) := by
    simpa using hlog1.sub hR
  have hdiv := hnum.div_atTop hsqrt
  have : Tendsto (fun t ↦ 1 + (Real.log (1 + Real.exp (-Real.sqrt (Real.log t))) -
      wallRem t (Real.exp (-Real.sqrt (Real.log t)))) / Real.sqrt (Real.log t)) atTop
      (𝓝 (1 + 0)) := tendsto_const_nhds.add hdiv
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos ht
  have hsq : 0 < Real.sqrt (Real.log t) := Real.sqrt_pos.mpr hlogt
  have hsp : 0 < Real.exp (-Real.sqrt (Real.log t)) := Real.exp_pos _
  rw [wallZ_eq ht0 hsp]
  have hlog : Real.log ((1 + Real.exp (-Real.sqrt (Real.log t))) /
      Real.exp (-Real.sqrt (Real.log t))) =
      Real.sqrt (Real.log t) + Real.log (1 + Real.exp (-Real.sqrt (Real.log t))) := by
    rw [Real.log_div (by positivity) hsp.ne', Real.log_exp]
    ring
  rw [hlog]
  field_simp
  ring

end Laplace.Multi
