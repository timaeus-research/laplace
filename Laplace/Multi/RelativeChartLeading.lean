/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.SingularPowerNormalForm
import Laplace.Multi.MorseBottLeading

/-!
# A resolved chart with one active variable: the leading order of its Laplace integral

The local object a relative modification delivers on each chart (see
`docs/hironaka_relative_resolution_spec.md`): coordinates `(x, y) ∈ ℝ × ℝⁿ` with `x` the active
variable, the phase `a(x, y) x^{2k}` with an analytic positive unit `a`, the Jacobian
`b(x, y) |x|^h`, and a cutoff `χ(x, y)` from a partition of unity; the exponent data `(k, h)` are
the frozen part, `a, b, χ` the moving part. Here the unit depends on `x` as well as `y`, so
nothing is exact in `t` any more: this file proves the leading order
`t^{(h+1)/2k} ∫ g(y) χ b |x|^h e^{-t a x^{2k}} → c_{k,h} ∫ g(y) χ(0,y) b(0,y) a(0,y)^{-(h+1)/2k} dy`
(`ChartData.tendsto_rpow_mul_chartIntegral`), `c_{k,h} = ∫ |u|^h e^{-u^{2k}} du`, by the
substitution `x = t^{-1/2k} u` and two dominated convergences (as in `MorseBottLeading`, with the
unit `a(t^{-1/2k}u, y) → a(0, y)`).
The chart's leading exponent is `λ = (h+1)/2k`, read off the frozen data; the coefficient is the
integral over the chart's piece of the exceptional divisor `{x = 0}` of the density
`χ b a^{-λ}` — the object whose response to a variation of the truth `RelativeChartFamily` computes.
-/

open Real MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {n : ℕ}

/-! ### Generalised Gaussian moments with an absolute-value weight -/

/-- `c_{k,h} = ∫ |u|^h e^{-u^{2k}} du`. -/
noncomputable def agmom (k h : ℕ) : ℝ := ∫ u : ℝ, |u| ^ h * Real.exp (-u ^ (2 * k))

theorem integrable_abs_pow_mul_exp_neg_mul_pow {b : ℝ} (hb : 0 < b) (k : ℕ) (hk : 1 ≤ k) (h : ℕ) :
    Integrable fun u : ℝ ↦ |u| ^ h * Real.exp (-(b * u ^ (2 * k))) := by
  have := (integrable_pow_mul_exp_neg_mul_pow hb k hk h).norm
  refine this.congr (Filter.Eventually.of_forall fun u ↦ ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, Real.abs_exp]

theorem agmom_pos (k : ℕ) (hk : 1 ≤ k) (h : ℕ) : 0 < agmom k h := by
  unfold agmom
  have hi : Integrable fun u : ℝ ↦ |u| ^ h * Real.exp (-u ^ (2 * k)) := by
    have := integrable_abs_pow_mul_exp_neg_mul_pow one_pos k hk h
    simpa using this
  refine (integral_pos_iff_support_of_nonneg (fun u ↦ by positivity) hi).mpr ?_
  have hsub : Ioi (0 : ℝ) ⊆ Function.support fun u : ℝ ↦ |u| ^ h * Real.exp (-u ^ (2 * k)) := by
    intro u hu
    have hu' : (0 : ℝ) < u := hu
    simp only [Function.mem_support]
    positivity
  exact lt_of_lt_of_le (by simp) (measure_mono hsub)

/-- Scaling: `∫ |u|^h e^{-b u^{2k}} du = b^{-(h+1)/2k} c_{k,h}` for `b > 0`. -/
theorem integral_abs_pow_mul_exp_neg_mul_pow {b : ℝ} (hb : 0 < b) (k : ℕ) (hk : 1 ≤ k) (h : ℕ) :
    ∫ u : ℝ, |u| ^ h * Real.exp (-(b * u ^ (2 * k))) =
      b ^ (-((h : ℝ) + 1) / (2 * k)) * agmom k h := by
  set s : ℝ := b ^ (1 / (2 * k : ℝ)) with hs
  have hspos : 0 < s := Real.rpow_pos_of_pos hb _
  have hk' : (2 * k : ℝ) ≠ 0 := by positivity
  have hs2k : s ^ (2 * k) = b := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    push_cast
    rw [one_div_mul_cancel hk', Real.rpow_one]
  have hcomp := Measure.integral_comp_mul_left (fun u : ℝ ↦ |u| ^ h * Real.exp (-u ^ (2 * k))) s
  have hpt : (fun x : ℝ ↦ |s * x| ^ h * Real.exp (-(s * x) ^ (2 * k))) =
      fun x ↦ s ^ h * (|x| ^ h * Real.exp (-(b * x ^ (2 * k)))) := by
    funext x
    rw [abs_mul, abs_of_pos hspos, mul_pow, mul_pow, hs2k]
    ring
  rw [hpt, integral_const_mul, abs_inv, abs_of_pos hspos, smul_eq_mul] at hcomp
  have hsm : s ^ h ≠ 0 := pow_ne_zero _ hspos.ne'
  have hI : (∫ x : ℝ, |x| ^ h * Real.exp (-(b * x ^ (2 * k)))) = (s ^ h)⁻¹ * s⁻¹ * agmom k h := by
    unfold agmom
    calc (∫ x : ℝ, |x| ^ h * Real.exp (-(b * x ^ (2 * k))))
        = (s ^ h)⁻¹ * (s ^ h * ∫ x : ℝ, |x| ^ h * Real.exp (-(b * x ^ (2 * k)))) := by
          field_simp
      _ = (s ^ h)⁻¹ * (s⁻¹ * ∫ u : ℝ, |u| ^ h * Real.exp (-u ^ (2 * k))) := by rw [hcomp]
      _ = (s ^ h)⁻¹ * s⁻¹ * ∫ u : ℝ, |u| ^ h * Real.exp (-u ^ (2 * k)) := by ring
  rw [hI]
  congr 1
  rw [← mul_inv, ← pow_succ, hs, ← Real.rpow_natCast, ← Real.rpow_mul hb.le,
    ← Real.rpow_neg hb.le]
  congr 1
  push_cast
  ring

/-! ### The chart -/

/-- One resolved chart with one active variable: frozen exponents `k ≥ 1` (phase `x^{2k}`) and
`h` (Jacobian `|x|^h`), a continuous unit `a ≥ a₀ > 0`, a continuous Jacobian unit `b`, and a
continuous compactly supported cutoff `χ` on the chart. -/
structure ChartData (k h : ℕ) (a b χ : ℝ × EuclidD n → ℝ) (a₀ : ℝ) : Prop where
  k_pos : 1 ≤ k
  a_cont : Continuous a
  a₀_pos : 0 < a₀
  a_lower : ∀ z, a₀ ≤ a z
  b_cont : Continuous b
  χ_cont : Continuous χ
  χ_supp : HasCompactSupport χ

/-- The chart integral `∫ g(y) χ b |x|^h e^{-t a x^{2k}} dx dy`. -/
noncomputable def chartIntegral (k h : ℕ) (a b χ : ℝ × EuclidD n → ℝ) (g : EuclidD n → ℝ) (t : ℝ) :
    ℝ :=
  ∫ z : ℝ × EuclidD n, g z.2 * χ z * b z * |z.1| ^ h * Real.exp (-(t * (a z * z.1 ^ (2 * k))))

/-- The chart's leading coefficient `c_{k,h} ∫ g(y) χ(0,y) b(0,y) a(0,y)^{-(h+1)/2k} dy`. -/
noncomputable def chartCoeff (k h : ℕ) (a b χ : ℝ × EuclidD n → ℝ) (g : EuclidD n → ℝ) : ℝ :=
  agmom k h * ∫ y, g y * χ (0, y) * b (0, y) * a (0, y) ^ (-((h : ℝ) + 1) / (2 * k))

/-- The scaled inner integral at `y`: `∫ χ(qu,y) b(qu,y) |u|^h e^{-a(qu,y) u^{2k}} du`,
`q = t^{-1/2k}`. -/
noncomputable def chartInner (k h : ℕ) (a b χ : ℝ × EuclidD n → ℝ) (t : ℝ) (y : EuclidD n) : ℝ :=
  ∫ u : ℝ, χ (t ^ (-(1 / (2 * k : ℝ))) * u, y) * b (t ^ (-(1 / (2 * k : ℝ))) * u, y) * |u| ^ h *
    Real.exp (-(a (t ^ (-(1 / (2 * k : ℝ))) * u, y) * u ^ (2 * k)))

theorem ChartData.exists_bound {k h : ℕ} {a b χ : ℝ × EuclidD n → ℝ} {a₀ : ℝ}
    (hc : ChartData k h a b χ a₀) : ∃ M, 0 ≤ M ∧ ∀ z, |χ z * b z| ≤ M := by
  obtain ⟨M, hM⟩ := hc.χ_supp.exists_bound_of_continuousOn (hc.χ_cont.mul hc.b_cont).continuousOn
  refine ⟨|M|, abs_nonneg _, fun z ↦ ?_⟩
  by_cases hz : z ∈ tsupport χ
  · exact ((hM z hz).trans (le_abs_self M))
  · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, abs_zero]
    exact abs_nonneg _

/-- Pointwise domination of the scaled integrand, uniform in `t` and `y`. -/
theorem ChartData.abs_scaled_le {k h : ℕ} {a b χ : ℝ × EuclidD n → ℝ} {a₀ : ℝ}
    (hc : ChartData k h a b χ a₀) {M : ℝ} (hM : ∀ z, |χ z * b z| ≤ M) (q u : ℝ) (y : EuclidD n) :
    |χ (q * u, y) * b (q * u, y) * |u| ^ h * Real.exp (-(a (q * u, y) * u ^ (2 * k)))| ≤
      M * (|u| ^ h * Real.exp (-(a₀ * u ^ (2 * k)))) := by
  have hu : 0 ≤ u ^ (2 * k) := by rw [pow_mul]; positivity
  have hexp : Real.exp (-(a (q * u, y) * u ^ (2 * k))) ≤ Real.exp (-(a₀ * u ^ (2 * k))) := by
    apply Real.exp_le_exp.mpr
    have := hc.a_lower (q * u, y)
    nlinarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (q * u, y))
  rw [abs_mul, abs_mul, Real.abs_exp, abs_pow, abs_abs]
  calc |χ (q * u, y) * b (q * u, y)| * |u| ^ h * Real.exp (-(a (q * u, y) * u ^ (2 * k)))
      ≤ M * |u| ^ h * Real.exp (-(a₀ * u ^ (2 * k))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hM _) (by positivity)) hexp
          (Real.exp_pos _).le (by positivity)
    _ = M * (|u| ^ h * Real.exp (-(a₀ * u ^ (2 * k)))) := by ring

/-- The substitution `x = q u`, `q = t^{-1/2k}`: `t^{(h+1)/2k} ∫ (…) dx = chartInner t y`. -/
theorem ChartData.rpow_mul_inner_eq {k h : ℕ} {a b χ : ℝ × EuclidD n → ℝ} {a₀ : ℝ}
    (hc : ChartData k h a b χ a₀) {t : ℝ} (ht : 0 < t) (y : EuclidD n) :
    t ^ (((h : ℝ) + 1) / (2 * k)) *
      ∫ x : ℝ, χ (x, y) * b (x, y) * |x| ^ h * Real.exp (-(t * (a (x, y) * x ^ (2 * k)))) =
      chartInner k h a b χ t y := by
  have hk : (0 : ℝ) < k := by exact_mod_cast hc.k_pos
  set q : ℝ := t ^ (-(1 / (2 * k : ℝ))) with hq
  have hqpos : 0 < q := Real.rpow_pos_of_pos ht _
  have hq2k : t * q ^ (2 * k) = 1 := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    push_cast
    rw [show -(1 / (2 * (k : ℝ))) * (2 * k) = -1 by field_simp, Real.rpow_neg_one,
      mul_inv_cancel₀ ht.ne']
  have hqh : t ^ (((h : ℝ) + 1) / (2 * k)) * q ^ (h + 1) = 1 := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
    push_cast
    rw [show ((h : ℝ) + 1) / (2 * k) + -(1 / (2 * k)) * ((h : ℝ) + 1) = 0 by ring, Real.rpow_zero]
  have hcomp := Measure.integral_comp_mul_left
    (fun x : ℝ ↦ χ (x, y) * b (x, y) * |x| ^ h * Real.exp (-(t * (a (x, y) * x ^ (2 * k))))) q
  rw [abs_inv, abs_of_pos hqpos, smul_eq_mul] at hcomp
  have hpt : ∀ u : ℝ,
      χ (q * u, y) * b (q * u, y) * |q * u| ^ h *
        Real.exp (-(t * (a (q * u, y) * (q * u) ^ (2 * k)))) =
        q ^ h * (χ (q * u, y) * b (q * u, y) * |u| ^ h *
          Real.exp (-(a (q * u, y) * u ^ (2 * k)))) := by
    intro u
    rw [abs_mul, abs_of_pos hqpos, mul_pow, mul_pow,
      show t * (a (q * u, y) * (q ^ (2 * k) * u ^ (2 * k))) =
        (t * q ^ (2 * k)) * (a (q * u, y) * u ^ (2 * k)) by ring, hq2k, one_mul]
    ring
  simp only [hpt, integral_const_mul] at hcomp
  -- `∫ F = q · ∫ F(qu) = q^{h+1} · chartInner`
  have hI : (∫ x : ℝ, χ (x, y) * b (x, y) * |x| ^ h * Real.exp (-(t * (a (x, y) * x ^ (2 * k))))) =
      q ^ (h + 1) * chartInner k h a b χ t y := by
    unfold chartInner
    rw [← hq]
    have hF : (∫ x : ℝ, χ (x, y) * b (x, y) * |x| ^ h *
        Real.exp (-(t * (a (x, y) * x ^ (2 * k))))) =
        q * (q⁻¹ * ∫ x : ℝ, χ (x, y) * b (x, y) * |x| ^ h *
          Real.exp (-(t * (a (x, y) * x ^ (2 * k))))) := by
      rw [← mul_assoc, mul_inv_cancel₀ hqpos.ne', one_mul]
    rw [hF, ← hcomp, pow_succ]
    ring
  rw [hI, ← mul_assoc, hqh, one_mul]

/-- Pointwise convergence of the scaled integrand as `t → ∞`. -/
theorem ChartData.tendsto_scaled {k h : ℕ} {a b χ : ℝ × EuclidD n → ℝ} {a₀ : ℝ}
    (hc : ChartData k h a b χ a₀) (u : ℝ) (y : EuclidD n) :
    Tendsto (fun t : ℝ ↦ χ (t ^ (-(1 / (2 * k : ℝ))) * u, y) * b (t ^ (-(1 / (2 * k : ℝ))) * u, y) *
        |u| ^ h * Real.exp (-(a (t ^ (-(1 / (2 * k : ℝ))) * u, y) * u ^ (2 * k)))) atTop
      (𝓝 (χ (0, y) * b (0, y) * |u| ^ h * Real.exp (-(a (0, y) * u ^ (2 * k))))) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast hc.k_pos
  have hq : Tendsto (fun t : ℝ ↦ t ^ (-(1 / (2 * k : ℝ))) * u) atTop (𝓝 (0 * u)) :=
    (tendsto_rpow_neg_atTop (by positivity)).mul_const u
  rw [zero_mul] at hq
  have hz : Tendsto (fun t : ℝ ↦ (t ^ (-(1 / (2 * k : ℝ))) * u, y)) atTop (𝓝 ((0 : ℝ), y)) :=
    hq.prodMk_nhds tendsto_const_nhds
  have h1 := ((hc.χ_cont.tendsto _).comp hz).mul ((hc.b_cont.tendsto _).comp hz)
  have h2 := (Real.continuous_exp.tendsto _).comp
    ((((hc.a_cont.tendsto _).comp hz).mul_const (u ^ (2 * k))).neg)
  exact (h1.mul_const (|u| ^ h)).mul h2

theorem ChartData.continuous_scaled_u {k h : ℕ} {a b χ : ℝ × EuclidD n → ℝ} {a₀ : ℝ}
    (hc : ChartData k h a b χ a₀) (q : ℝ) (y : EuclidD n) :
    Continuous fun u : ℝ ↦ χ (q * u, y) * b (q * u, y) * |u| ^ h *
      Real.exp (-(a (q * u, y) * u ^ (2 * k))) := by
  have hz : Continuous fun u : ℝ ↦ (q * u, y) := by fun_prop
  exact (((hc.χ_cont.comp hz).mul (hc.b_cont.comp hz)).mul (by fun_prop)).mul
    (Real.continuous_exp.comp (((hc.a_cont.comp hz).mul (by fun_prop)).neg))

theorem ChartData.continuous_scaled_joint {k h : ℕ} {a b χ : ℝ × EuclidD n → ℝ} {a₀ : ℝ}
    (hc : ChartData k h a b χ a₀) (q : ℝ) :
    Continuous fun p : EuclidD n × ℝ ↦ χ (q * p.2, p.1) * b (q * p.2, p.1) * |p.2| ^ h *
      Real.exp (-(a (q * p.2, p.1) * p.2 ^ (2 * k))) := by
  have hz : Continuous fun p : EuclidD n × ℝ ↦ (q * p.2, p.1) := by fun_prop
  exact (((hc.χ_cont.comp hz).mul (hc.b_cont.comp hz)).mul (by fun_prop)).mul
    (Real.continuous_exp.comp (((hc.a_cont.comp hz).mul (by fun_prop)).neg))

/-- Inner dominated convergence: `chartInner t y → χ(0,y) b(0,y) a(0,y)^{-(h+1)/2k} c_{k,h}`. -/
theorem ChartData.tendsto_chartInner {k h : ℕ} {a b χ : ℝ × EuclidD n → ℝ} {a₀ : ℝ}
    (hc : ChartData k h a b χ a₀) (y : EuclidD n) :
    Tendsto (fun t ↦ chartInner k h a b χ t y) atTop
      (𝓝 (χ (0, y) * b (0, y) * (a (0, y) ^ (-((h : ℝ) + 1) / (2 * k)) * agmom k h))) := by
  obtain ⟨M, _hM0, hM⟩ := hc.exists_bound
  have hlim : (∫ u : ℝ, χ (0, y) * b (0, y) * |u| ^ h * Real.exp (-(a (0, y) * u ^ (2 * k)))) =
      χ (0, y) * b (0, y) * (a (0, y) ^ (-((h : ℝ) + 1) / (2 * k)) * agmom k h) := by
    have : (fun u : ℝ ↦ χ (0, y) * b (0, y) * |u| ^ h * Real.exp (-(a (0, y) * u ^ (2 * k)))) =
        fun u ↦ (χ (0, y) * b (0, y)) * (|u| ^ h * Real.exp (-(a (0, y) * u ^ (2 * k)))) := by
      funext u
      ring
    rw [this, integral_const_mul, integral_abs_pow_mul_exp_neg_mul_pow
      (hc.a₀_pos.trans_le (hc.a_lower _)) k hc.k_pos h]
  rw [← hlim]
  unfold chartInner
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u ↦ M * (|u| ^ h * Real.exp (-(a₀ * u ^ (2 * k)))))
    (Filter.Eventually.of_forall fun t ↦ (hc.continuous_scaled_u _ y).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ↦ Filter.Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs]
      exact hc.abs_scaled_le hM _ u y)
    ((integrable_abs_pow_mul_exp_neg_mul_pow hc.a₀_pos k hc.k_pos h).const_mul M)
    (Filter.Eventually.of_forall fun u ↦ hc.tendsto_scaled u y)

/-- Off the `y`-shadow of the support the inner integral vanishes. -/
theorem ChartData.chartInner_eq_zero {k h : ℕ} {a b χ : ℝ × EuclidD n → ℝ} {a₀ : ℝ}
    (_hc : ChartData k h a b χ a₀) (t : ℝ) {y : EuclidD n}
    (hy : y ∉ Prod.snd '' tsupport χ) : chartInner k h a b χ t y = 0 := by
  unfold chartInner
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u ↦ ?_)
  have : χ (t ^ (-(1 / (2 * k : ℝ))) * u, y) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact hy ⟨_, hmem, rfl⟩
  change χ (t ^ (-(1 / (2 * k : ℝ))) * u, y) * b (t ^ (-(1 / (2 * k : ℝ))) * u, y) * |u| ^ h *
    Real.exp (-(a (t ^ (-(1 / (2 * k : ℝ))) * u, y) * u ^ (2 * k))) = 0
  rw [this]
  simp only [zero_mul]

theorem ChartData.abs_chartInner_le {k h : ℕ} {a b χ : ℝ × EuclidD n → ℝ} {a₀ : ℝ}
    (hc : ChartData k h a b χ a₀) {M : ℝ} (hM : ∀ z, |χ z * b z| ≤ M) (t : ℝ) (y : EuclidD n) :
    |chartInner k h a b χ t y| ≤ M * ∫ u : ℝ, |u| ^ h * Real.exp (-(a₀ * u ^ (2 * k))) := by
  unfold chartInner
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  exact norm_integral_le_of_norm_le
    ((integrable_abs_pow_mul_exp_neg_mul_pow hc.a₀_pos k hc.k_pos h).const_mul M)
    (Filter.Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs]
      exact hc.abs_scaled_le hM _ u y)

/-- Fubini for the chart integral. -/
theorem ChartData.chartIntegral_eq {k h : ℕ} {a b χ : ℝ × EuclidD n → ℝ} {a₀ : ℝ}
    (hc : ChartData k h a b χ a₀) {g : EuclidD n → ℝ} (hg : Continuous g) (t : ℝ) :
    chartIntegral k h a b χ g t =
      ∫ y, g y * ∫ x : ℝ, χ (x, y) * b (x, y) * |x| ^ h *
        Real.exp (-(t * (a (x, y) * x ^ (2 * k)))) := by
  have hcont : Continuous fun z : ℝ × EuclidD n ↦
      g z.2 * χ z * b z * |z.1| ^ h * Real.exp (-(t * (a z * z.1 ^ (2 * k)))) := by
    have := hc.a_cont
    have := hc.b_cont
    have := hc.χ_cont
    fun_prop
  have hsupp : HasCompactSupport fun z : ℝ × EuclidD n ↦
      g z.2 * χ z * b z * |z.1| ^ h * Real.exp (-(t * (a z * z.1 ^ (2 * k)))) := by
    have : (fun z : ℝ × EuclidD n ↦
        g z.2 * χ z * b z * |z.1| ^ h * Real.exp (-(t * (a z * z.1 ^ (2 * k))))) =
        fun z ↦ χ z * (g z.2 * b z * |z.1| ^ h * Real.exp (-(t * (a z * z.1 ^ (2 * k))))) := by
      funext z
      ring
    rw [this]
    exact hc.χ_supp.mul_right
  have hi := hcont.integrable_of_hasCompactSupport (μ := (volume : Measure (ℝ × EuclidD n))) hsupp
  unfold chartIntegral
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod_symm _ hi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  ring

/-- **Leading order of a resolved chart with one active variable**:
`t^{(h+1)/2k} ∫ g χ b |x|^h e^{-t a x^{2k}} → c_{k,h} ∫ g(y) χ(0,y) b(0,y) a(0,y)^{-(h+1)/2k} dy`.
-/
theorem ChartData.tendsto_rpow_mul_chartIntegral {k h : ℕ} {a b χ : ℝ × EuclidD n → ℝ} {a₀ : ℝ}
    (hc : ChartData k h a b χ a₀) {g : EuclidD n → ℝ} (hg : Continuous g) :
    Tendsto (fun t ↦ t ^ (((h : ℝ) + 1) / (2 * k)) * chartIntegral k h a b χ g t) atTop
      (𝓝 (chartCoeff k h a b χ g)) := by
  obtain ⟨M, hM0, hM⟩ := hc.exists_bound
  set Ky : Set (EuclidD n) := Prod.snd '' tsupport χ with hKy
  have hKyc : IsCompact Ky := hc.χ_supp.image continuous_snd
  obtain ⟨G, hG⟩ := hKyc.exists_bound_of_continuousOn hg.continuousOn
  set I₀ : ℝ := ∫ u : ℝ, |u| ^ h * Real.exp (-(a₀ * u ^ (2 * k))) with hI₀
  -- rewrite as the outer integral of the scaled inner integral
  have hrew : ∀ᶠ t : ℝ in atTop, t ^ (((h : ℝ) + 1) / (2 * k)) * chartIntegral k h a b χ g t =
      ∫ y, g y * chartInner k h a b χ t y := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [hc.chartIntegral_eq hg t, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only
    rw [← hc.rpow_mul_inner_eq ht y]
    ring
  refine Tendsto.congr' (hrew.mono fun t ht ↦ ht.symm) ?_
  -- the limit value
  have hval : chartCoeff k h a b χ g =
      ∫ y, g y * (χ (0, y) * b (0, y) * (a (0, y) ^ (-((h : ℝ) + 1) / (2 * k)) * agmom k h)) := by
    unfold chartCoeff
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    ring
  rw [hval]
  have hKyfin : (volume : Measure (EuclidD n)) Ky ≠ ⊤ :=
    (IsCompact.measure_lt_top (μ := (volume : Measure (EuclidD n))) hKyc).ne
  have hbi : Integrable (Ky.indicator fun _ : EuclidD n ↦ |G| * (M * I₀)) :=
    (integrableOn_const (μ := (volume : Measure (EuclidD n))) (s := Ky)
      (C := |G| * (M * I₀)) hKyfin).integrable_indicator hKyc.isClosed.measurableSet
  refine tendsto_integral_filter_of_dominated_convergence
    (Ky.indicator fun _ ↦ |G| * (M * I₀)) ?_ ?_ hbi
    (Filter.Eventually.of_forall fun y ↦ tendsto_const_nhds.mul (hc.tendsto_chartInner y))
  · refine Filter.Eventually.of_forall fun t ↦ ?_
    have hmeas : StronglyMeasurable (chartInner k h a b χ t) := by
      unfold chartInner
      exact (hc.continuous_scaled_joint _).stronglyMeasurable.integral_prod_right'
    exact (hg.stronglyMeasurable.mul hmeas).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t ↦ Filter.Eventually.of_forall fun y ↦ ?_
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hy : y ∈ Ky
    · rw [Set.indicator_of_mem hy]
      exact mul_le_mul ((hG y hy).trans (le_abs_self G)) (hc.abs_chartInner_le hM t y)
        (abs_nonneg _) (abs_nonneg _)
    · rw [Set.indicator_of_notMem hy, hc.chartInner_eq_zero t hy, abs_zero, mul_zero]

end Laplace.Multi
