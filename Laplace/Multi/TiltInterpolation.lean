/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.EmpiricalRelative

/-!
# The interpolation identity: `d/du ⟨f⟩_{L + uR} = −t Cov_{L+uR}(f, R)`

Interpolating between the population loss `L` and the empirical loss `K = L + R` along
`L_u = L + uR`, the normalized Gibbs expectation `P_u(f) = ∫ f e^{-tuR} ν / ∫ e^{-tuR} ν`
(`ν = χ e^{-tL}` the population weight with window `χ`) is differentiable in `u` with

  `P_u'(f) = −t · Cov_{P_u}(f, R)`

(`hasDerivAt_tiltExp`), so `|P_1(f) − P_0(f)| ≤ t · sup_{u ∈ [0,1]} |Cov_{P_u}(f, R)|`
(`abs_tiltExp_one_sub_zero_le`). This is the sharp form of the empirical perturbation bound:
where the sup-norm bound of `EmpiricalRelative` has `tδ`, this has `t` times a covariance, and
the covariance of `f` with a residual `R` of small variance under the tilted Gibbs laws is the
quantity the fluctuation theory of the empirical loss controls (Cauchy–Schwarz and the
variance-rate corollary are in `TiltCauchySchwarz`).
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- The tilted numerator `∫ f e^{-tuR} ν`. -/
noncomputable def tiltNum (ν f R : X → ℝ) (t u : ℝ) : ℝ :=
  ∫ x, f x * Real.exp (-(t * R x * u)) * ν x ∂μ

/-- The tilted normalized expectation `P_u(f)`. -/
noncomputable def tiltExp (ν f R : X → ℝ) (t u : ℝ) : ℝ :=
  tiltNum μ ν f R t u / tiltNum μ ν (fun _ ↦ 1) R t u

/-- The tilted covariance `Cov_{P_u}(f, g)`. -/
noncomputable def tiltCov (ν f g R : X → ℝ) (t u : ℝ) : ℝ :=
  tiltExp μ ν (fun x ↦ f x * g x) R t u - tiltExp μ ν f R t u * tiltExp μ ν g R t u

variable {μ}

/-- Standing hypotheses: a nonnegative measurable integrable weight with positive mass and a
bounded measurable residual. -/
structure TiltData (μ : Measure X) (ν R : X → ℝ) (M : ℝ) : Prop where
  ν_meas : Measurable ν
  ν_int : Integrable ν μ
  ν_nonneg : ∀ x, 0 ≤ ν x
  ν_pos : 0 < ∫ x, ν x ∂μ
  R_meas : Measurable R
  R_bound : ∀ x, |R x| ≤ M

theorem TiltData.M_nonneg [Nonempty X] {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) : 0 ≤ M :=
  le_trans (abs_nonneg _) (h.R_bound (Classical.arbitrary X))

/-- The exponential tilt is bounded above and below on `|u| ≤ U`. -/
theorem TiltData.exp_bounds [Nonempty X] {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) (t : ℝ)
    {u U : ℝ} (hu : |u| ≤ U) (x : X) :
    Real.exp (-(|t| * U * M)) ≤ Real.exp (-(t * R x * u)) ∧
      Real.exp (-(t * R x * u)) ≤ Real.exp (|t| * U * M) := by
  have hR := h.R_bound x
  have hM := h.M_nonneg
  have hU : 0 ≤ U := le_trans (abs_nonneg _) hu
  have habs : |t * R x * u| ≤ |t| * U * M := by
    rw [abs_mul, abs_mul]
    calc |t| * |R x| * |u| ≤ |t| * M * U := by gcongr
      _ = |t| * U * M := by ring
  constructor
  · rw [Real.exp_le_exp]
    linarith [le_abs_self (t * R x * u)]
  · rw [Real.exp_le_exp]
    linarith [neg_le_abs (t * R x * u)]

theorem TiltData.measurable_tilt {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) {f : X → ℝ}
    (hfm : Measurable f) (t u : ℝ) :
    Measurable fun x ↦ f x * Real.exp (-(t * R x * u)) * ν x :=
  (hfm.mul (Real.measurable_exp.comp ((h.R_meas.const_mul t).mul_const u).neg)).mul h.ν_meas

/-- Bounded measurable observables are integrable against the tilted weight. -/
theorem TiltData.integrable_tilt [Nonempty X] {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M)
    {f : X → ℝ} (hfm : Measurable f) {Mf : ℝ} (hf : ∀ x, |f x| ≤ Mf) (t u : ℝ) :
    Integrable (fun x ↦ f x * Real.exp (-(t * R x * u)) * ν x) μ := by
  refine h.ν_int.bdd_mul (c := Mf * Real.exp (|t| * |u| * M)) ?_ (Filter.Eventually.of_forall
    fun x ↦ ?_)
  · exact (hfm.mul (Real.measurable_exp.comp ((h.R_meas.const_mul t).mul_const u).neg))
      |>.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    exact mul_le_mul (hf x) (h.exp_bounds t le_rfl x).2 (Real.exp_pos _).le
      (le_trans (abs_nonneg _) (hf x))

/-- The tilted partition value is positive. -/
theorem TiltData.tiltNum_one_pos [Nonempty X] {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M)
    (t u : ℝ) : 0 < tiltNum μ ν (fun _ ↦ 1) R t u := by
  unfold tiltNum
  have hc : 0 < Real.exp (-(|t| * |u| * M)) := Real.exp_pos _
  have hlow : Real.exp (-(|t| * |u| * M)) * ∫ x, ν x ∂μ ≤
      ∫ x, (fun _ ↦ (1 : ℝ)) x * Real.exp (-(t * R x * u)) * ν x ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono (h.ν_int.const_mul _)
      (h.integrable_tilt measurable_const (Mf := 1) (fun _ ↦ by simp) t u) fun x ↦ ?_
    beta_reduce
    rw [one_mul]
    exact mul_le_mul_of_nonneg_right (h.exp_bounds t le_rfl x).1 (h.ν_nonneg x)
  exact lt_of_lt_of_le (mul_pos hc h.ν_pos) hlow

/-! ### The derivative in the interpolation parameter -/

/-- `d/du ∫ f e^{-tuR} ν = −t ∫ f R e^{-tuR} ν`. -/
theorem TiltData.hasDerivAt_tiltNum [Nonempty X] {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M)
    {f : X → ℝ} (hfm : Measurable f) {Mf : ℝ} (hf : ∀ x, |f x| ≤ Mf) (t u₀ : ℝ) :
    HasDerivAt (fun u ↦ tiltNum μ ν f R t u)
      (-t * tiltNum μ ν (fun x ↦ f x * R x) R t u₀) u₀ := by
  have hMf : 0 ≤ Mf := le_trans (abs_nonneg _) (hf (Classical.arbitrary X))
  have hM := h.M_nonneg
  have hs : Metric.ball u₀ 1 ∈ 𝓝 u₀ := Metric.ball_mem_nhds u₀ one_pos
  have hmeasF : ∀ᶠ u in 𝓝 u₀,
      AEStronglyMeasurable (fun x ↦ f x * Real.exp (-(t * R x * u)) * ν x) μ :=
    Filter.Eventually.of_forall fun u ↦ (h.measurable_tilt hfm t u).aestronglyMeasurable
  have hint := h.integrable_tilt hfm hf t u₀
  have hmeasF' : AEStronglyMeasurable
      (fun x ↦ f x * (Real.exp (-(t * R x * u₀)) * (-(t * R x))) * ν x) μ :=
    ((hfm.mul ((Real.measurable_exp.comp ((h.R_meas.const_mul t).mul_const u₀).neg).mul
      (h.R_meas.const_mul t).neg)).mul h.ν_meas).aestronglyMeasurable
  have hbound_int : Integrable
      (fun x ↦ (Mf * (Real.exp (|t| * (|u₀| + 1) * M) * (|t| * M))) * ν x) μ :=
    h.ν_int.const_mul _
  have hbound : ∀ᵐ x ∂μ, ∀ u ∈ Metric.ball u₀ 1,
      ‖f x * (Real.exp (-(t * R x * u)) * (-(t * R x))) * ν x‖ ≤
        (Mf * (Real.exp (|t| * (|u₀| + 1) * M) * (|t| * M))) * ν x := by
    refine Filter.Eventually.of_forall fun x u hu ↦ ?_
    have hu' : |u| ≤ |u₀| + 1 := by
      have := Metric.mem_ball.mp hu
      rw [Real.dist_eq] at this
      calc |u| = |u₀ + (u - u₀)| := by ring_nf
        _ ≤ |u₀| + |u - u₀| := abs_add_le _ _
        _ ≤ |u₀| + 1 := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, Real.abs_exp, abs_neg, abs_mul,
      abs_of_nonneg (h.ν_nonneg x)]
    have he := (h.exp_bounds t hu' x).2
    have hR := h.R_bound x
    have hfx := hf x
    have h1 : |f x| * (Real.exp (-(t * R x * u)) * (|t| * |R x|)) ≤
        Mf * (Real.exp (|t| * (|u₀| + 1) * M) * (|t| * M)) := by
      gcongr
    exact mul_le_mul_of_nonneg_right h1 (h.ν_nonneg x)
  have hdiff : ∀ᵐ x ∂μ, ∀ u ∈ Metric.ball u₀ 1,
      HasDerivAt (fun u ↦ f x * Real.exp (-(t * R x * u)) * ν x)
        (f x * (Real.exp (-(t * R x * u)) * (-(t * R x))) * ν x) u := by
    refine Filter.Eventually.of_forall fun x u _ ↦ ?_
    have h1 : HasDerivAt (fun u : ℝ ↦ -(t * R x * u)) (-(t * R x)) u := by
      have h0 : HasDerivAt (fun y : ℝ ↦ t * R x * y) (t * R x) u := by
        simpa using (hasDerivAt_id u).const_mul (t * R x)
      exact h0.neg
    exact (h1.exp.const_mul (f x)).mul_const (ν x)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u x ↦ f x * Real.exp (-(t * R x * u)) * ν x)
    (F' := fun u x ↦ f x * (Real.exp (-(t * R x * u)) * (-(t * R x))) * ν x)
    hs hmeasF hint hmeasF' hbound hbound_int hdiff
  have hderiv := key.2
  have hrw : (∫ x, f x * (Real.exp (-(t * R x * u₀)) * (-(t * R x))) * ν x ∂μ) =
      -t * tiltNum μ ν (fun x ↦ f x * R x) R t u₀ := by
    unfold tiltNum
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    ring
  rw [hrw] at hderiv
  exact hderiv

/-- **The interpolation identity**: `d/du P_u(f) = −t Cov_{P_u}(f, R)`. -/
theorem TiltData.hasDerivAt_tiltExp [Nonempty X] {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M)
    {f : X → ℝ} (hfm : Measurable f) {Mf : ℝ} (hf : ∀ x, |f x| ≤ Mf) (t u₀ : ℝ) :
    HasDerivAt (fun u ↦ tiltExp μ ν f R t u) (-t * tiltCov μ ν f R R t u₀) u₀ := by
  have hN := h.hasDerivAt_tiltNum hfm hf t u₀
  have hZ := h.hasDerivAt_tiltNum (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1)
    (fun _ ↦ by simp) t u₀
  simp only [one_mul] at hZ
  have hZpos := h.tiltNum_one_pos t u₀
  have hdiv := hN.div hZ hZpos.ne'
  have hval : (-t * tiltNum μ ν (fun x ↦ f x * R x) R t u₀ * tiltNum μ ν (fun _ ↦ 1) R t u₀ -
      tiltNum μ ν f R t u₀ * (-t * tiltNum μ ν (fun x ↦ R x) R t u₀)) /
        tiltNum μ ν (fun _ ↦ 1) R t u₀ ^ 2 = -t * tiltCov μ ν f R R t u₀ := by
    unfold tiltCov tiltExp
    field_simp
    ring
  exact hdiv.congr_deriv hval

/-- **Mean value bound**: `|P_1(f) − P_0(f)| ≤ t · sup_{u ∈ [0,1]} |Cov_{P_u}(f, R)|`. -/
theorem TiltData.abs_tiltExp_one_sub_zero_le [Nonempty X] {ν R : X → ℝ} {M : ℝ}
    (h : TiltData μ ν R M) {f : X → ℝ} (hfm : Measurable f) {Mf : ℝ} (hf : ∀ x, |f x| ≤ Mf)
    {t : ℝ} (ht : 0 ≤ t) {B : ℝ} (hB : ∀ u ∈ Set.Icc (0 : ℝ) 1, |tiltCov μ ν f R R t u| ≤ B) :
    |tiltExp μ ν f R t 1 - tiltExp μ ν f R t 0| ≤ t * B := by
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun u ↦ tiltExp μ ν f R t u) (f' := fun u ↦ -t * tiltCov μ ν f R R t u)
    (a := 0) (b := 1) (C := t * B)
    (fun u _ ↦ (h.hasDerivAt_tiltExp hfm hf t u).hasDerivWithinAt)
    (fun u hu ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg ht]
      exact mul_le_mul_of_nonneg_left (hB u (Set.Ico_subset_Icc_self hu)) ht)
    1 (Set.right_mem_Icc.mpr zero_le_one)
  simpa using hmv

/-! ### The endpoints are the population and empirical expectations -/

/-- At `u = 0` the tilted expectation is the population one. -/
theorem tiltExp_zero (ν f R : X → ℝ) (t : ℝ) :
    tiltExp μ ν f R t 0 = (∫ x, f x * ν x ∂μ) / ∫ x, ν x ∂μ := by
  unfold tiltExp tiltNum
  simp

/-- With the population weight `ν = χ e^{-tL}` and the truncated residual
`R = 1_{supp χ} (K − L)`, the tilted expectation at `u = 1` is the empirical normalized
expectation of a test `φ` supported where `χ = 1`, and at `u = 0` the population one. -/
theorem tiltExp_window_endpoints {ι : Type*} [Fintype ι] {K L φ χ : (ι → ℝ) → ℝ}
    (hφχ : ∀ w, φ w * χ w = φ w) (t : ℝ) :
    tiltExp (volume : Measure (ι → ℝ)) (fun w ↦ χ w * Real.exp (-(t * L w))) φ
        ((tsupport χ).indicator fun w ↦ K w - L w) t 1 = nmoment K φ χ t ∧
    tiltExp (volume : Measure (ι → ℝ)) (fun w ↦ χ w * Real.exp (-(t * L w))) φ
        ((tsupport χ).indicator fun w ↦ K w - L w) t 0 = nmoment L φ χ t := by
  have hpt : ∀ (g : (ι → ℝ) → ℝ), (∀ w, g w * χ w = g w) → ∀ w,
      g w * Real.exp (-(t * (tsupport χ).indicator (fun w ↦ K w - L w) w * 1)) *
        (χ w * Real.exp (-(t * L w))) = g w * Real.exp (-(t * K w)) := by
    intro g hg w
    by_cases hw : w ∈ tsupport χ
    · rw [Set.indicator_of_mem hw]
      have : g w * Real.exp (-(t * (K w - L w) * 1)) * (χ w * Real.exp (-(t * L w))) =
          (g w * χ w) * (Real.exp (-(t * (K w - L w) * 1)) * Real.exp (-(t * L w))) := by ring
      rw [this, hg w, ← Real.exp_add]
      congr 2
      ring
    · rw [image_eq_zero_of_notMem_tsupport hw]
      have : g w = 0 := by
        have := hg w
        rw [image_eq_zero_of_notMem_tsupport hw, mul_zero] at this
        exact this.symm
      simp [this]
  have hden : ∀ w, (fun _ ↦ (1 : ℝ)) w *
      Real.exp (-(t * (tsupport χ).indicator (fun w ↦ K w - L w) w * 1)) *
        (χ w * Real.exp (-(t * L w))) = χ w * Real.exp (-(t * K w)) := by
    intro w
    by_cases hw : w ∈ tsupport χ
    · rw [Set.indicator_of_mem hw]
      have : (fun _ ↦ (1 : ℝ)) w * Real.exp (-(t * (K w - L w) * 1)) *
          (χ w * Real.exp (-(t * L w))) =
          χ w * (Real.exp (-(t * (K w - L w) * 1)) * Real.exp (-(t * L w))) := by ring
      rw [this, ← Real.exp_add]
      congr 2
      ring
    · rw [image_eq_zero_of_notMem_tsupport hw]
      simp
  constructor
  · unfold tiltExp tiltNum nmoment
    congr 1
    · exact integral_congr_ae (Filter.Eventually.of_forall fun w ↦ hpt φ hφχ w)
    · exact integral_congr_ae (Filter.Eventually.of_forall fun w ↦ hden w)
  · rw [tiltExp_zero]
    unfold nmoment
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
    beta_reduce
    rw [← mul_assoc, hφχ w]

end Laplace.Multi
