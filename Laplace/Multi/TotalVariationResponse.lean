/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.TruthVariation

/-!
# The total-variation form of the fixed-temperature derivative

`TruthVariation` proved the quadratic remainder bound uniformly over bounded tests. By duality
(testing against the sign of the remainder density) this is the total-variation statement:
with the normalised tilted densities `p_u = e^{-tuR} ν / Z_u` and the derivative density
`D = -t (R - E₀R) p₀`,
`∫ |p₁ - p₀ - D| dμ ≤ 6 t² ‖R‖∞²`   (`TiltData.tv_taylor_le`),   `∫ |D| dμ ≤ 2 t ‖R‖∞`.
Read with `L ↦ μ_{L,t} = p_L μ`: the map from losses (sup norm on the window) to probability
measures (total variation) is Fréchet differentiable with derivative `-t (R - μ(R)) μ` and a
quadratic remainder — Astra's Level 1 statement (`research_truth_variation_v1`), here for the
densities in `L¹(μ)` rather than for a Banach space of signed measures.
-/

open MeasureTheory

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [Nonempty X]

/-- The normalised tilted density `p_u = e^{-tuR} ν / Z_u`. -/
noncomputable def tiltDensity (ν R : X → ℝ) (t u : ℝ) (x : X) : ℝ :=
  Real.exp (-(t * R x * u)) * ν x / tiltNum μ ν (fun _ ↦ (1 : ℝ)) R t u

/-- The derivative density `D = -t (R - E₀R) p₀`. -/
noncomputable def tiltDerivDensity (ν R : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  -t * (R x - tiltExp μ ν R R t 0) * tiltDensity (μ := μ) ν R t 0 x

omit [Nonempty X] in
theorem TiltData.measurable_tiltDensity {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) (t u : ℝ) :
    Measurable (tiltDensity (μ := μ) ν R t u) := by
  unfold tiltDensity
  exact ((Real.measurable_exp.comp ((measurable_const.mul h.R_meas).mul measurable_const).neg).mul
    h.ν_meas).div_const _

theorem TiltData.integrable_mul_tiltDensity {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M)
    {f : X → ℝ} (hfm : Measurable f) {Mf : ℝ} (hf : ∀ x, |f x| ≤ Mf) (t u : ℝ) :
    Integrable (fun x ↦ f x * tiltDensity (μ := μ) ν R t u x) μ := by
  have := (h.integrable_tilt hfm hf t u).div_const (tiltNum μ ν (fun _ ↦ (1 : ℝ)) R t u)
  refine this.congr (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [tiltDensity]
  ring

omit [Nonempty X] in
/-- Testing the density: `∫ f p_u = ⟨f⟩_u`. -/
theorem TiltData.integral_mul_tiltDensity {ν R : X → ℝ} {M : ℝ} (_h : TiltData μ ν R M)
    {f : X → ℝ} (t u : ℝ) :
    ∫ x, f x * tiltDensity (μ := μ) ν R t u x ∂μ = tiltExp μ ν f R t u := by
  unfold tiltExp tiltDensity tiltNum
  rw [← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  ring

theorem TiltData.integrable_mul_tiltDerivDensity {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M)
    {f : X → ℝ} (hfm : Measurable f) {Mf : ℝ} (hf : ∀ x, |f x| ≤ Mf) (t : ℝ) :
    Integrable (fun x ↦ f x * tiltDerivDensity (μ := μ) ν R t x) μ := by
  have hMf : 0 ≤ Mf := le_trans (abs_nonneg _) (hf (Classical.arbitrary X))
  have hM := h.M_nonneg
  have hg : Measurable fun x ↦ f x * (-t * (R x - tiltExp μ ν R R t 0)) :=
    hfm.mul (measurable_const.mul (h.R_meas.sub measurable_const))
  have hgb : ∀ x, |f x * (-t * (R x - tiltExp μ ν R R t 0))| ≤ Mf * (|t| * (M + M)) := by
    intro x
    rw [abs_mul, abs_mul, abs_neg]
    refine mul_le_mul (hf x) (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) (by positivity) hMf
    have h1 := h.R_bound x
    have h2 := h.abs_tiltExp_le h.R_meas h.R_bound t 0
    calc |R x - tiltExp μ ν R R t 0| ≤ |R x| + |tiltExp μ ν R R t 0| := abs_sub _ _
      _ ≤ M + M := add_le_add h1 h2
  have := h.integrable_mul_tiltDensity hg hgb t 0
  refine this.congr (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [tiltDerivDensity]
  ring

/-- Testing the derivative density: `∫ f D = -t Cov₀(f, R)`. -/
theorem TiltData.integral_mul_tiltDerivDensity {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M)
    {f : X → ℝ} (hfm : Measurable f) {Mf : ℝ} (hf : ∀ x, |f x| ≤ Mf) (t : ℝ) :
    ∫ x, f x * tiltDerivDensity (μ := μ) ν R t x ∂μ = -t * tiltCov μ ν f R R t 0 := by
  have hMf : 0 ≤ Mf := le_trans (abs_nonneg _) (hf (Classical.arbitrary X))
  have hfR : Integrable (fun x ↦ (f x * R x) * tiltDensity (μ := μ) ν R t 0 x) μ :=
    h.integrable_mul_tiltDensity (hfm.mul h.R_meas) (Mf := Mf * M) (fun x ↦ by
      simp only [Pi.mul_apply, abs_mul]
      exact mul_le_mul (hf x) (h.R_bound x) (abs_nonneg _) hMf) t 0
  have hff : Integrable (fun x ↦ f x * tiltDensity (μ := μ) ν R t 0 x) μ :=
    h.integrable_mul_tiltDensity hfm hf t 0
  have hpt : ∀ x, f x * tiltDerivDensity (μ := μ) ν R t x =
      -t * ((f x * R x) * tiltDensity (μ := μ) ν R t 0 x -
        tiltExp μ ν R R t 0 * (f x * tiltDensity (μ := μ) ν R t 0 x)) := by
    intro x
    simp only [tiltDerivDensity]
    ring
  simp only [hpt]
  rw [integral_const_mul, integral_sub hfR (hff.const_mul _), integral_const_mul,
    h.integral_mul_tiltDensity, h.integral_mul_tiltDensity]
  unfold tiltCov
  ring

/-- **The total-variation remainder**: `∫ |p₁ - p₀ - D| ≤ 6 t² ‖R‖∞²`. -/
theorem TiltData.tv_taylor_le {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) (t : ℝ) :
    ∫ x, |tiltDensity (μ := μ) ν R t 1 x - tiltDensity (μ := μ) ν R t 0 x -
      tiltDerivDensity (μ := μ) ν R t x| ∂μ ≤ 6 * t ^ 2 * M ^ 2 := by
  classical
  set g : X → ℝ := fun x ↦ tiltDensity (μ := μ) ν R t 1 x - tiltDensity (μ := μ) ν R t 0 x -
    tiltDerivDensity (μ := μ) ν R t x with hg
  have hgm : Measurable g := by
    have hD : Measurable (tiltDerivDensity (μ := μ) ν R t) := by
      unfold tiltDerivDensity
      exact (measurable_const.mul (h.R_meas.sub measurable_const)).mul
        (h.measurable_tiltDensity t 0)
    exact ((h.measurable_tiltDensity t 1).sub (h.measurable_tiltDensity t 0)).sub hD
  -- the sign test
  let f : X → ℝ := fun x ↦ if 0 ≤ g x then 1 else -1
  have hfm : Measurable f :=
    Measurable.ite (measurableSet_le measurable_const hgm) measurable_const measurable_const
  have hf : ∀ x, |f x| ≤ 1 := fun x ↦ by
    simp only [f]
    split_ifs <;> simp
  have hfg : ∀ x, f x * g x = |g x| := fun x ↦ by
    simp only [f]
    split_ifs with hx
    · rw [one_mul, abs_of_nonneg hx]
    · push Not at hx
      rw [abs_of_neg hx]
      ring
  have h1 : Integrable (fun x ↦ f x * tiltDensity (μ := μ) ν R t 1 x) μ :=
    h.integrable_mul_tiltDensity hfm hf t 1
  have h0 : Integrable (fun x ↦ f x * tiltDensity (μ := μ) ν R t 0 x) μ :=
    h.integrable_mul_tiltDensity hfm hf t 0
  have hD : Integrable (fun x ↦ f x * tiltDerivDensity (μ := μ) ν R t x) μ :=
    h.integrable_mul_tiltDerivDensity hfm hf t
  have hsplit : (∫ x, |g x| ∂μ) = tiltExp μ ν f R t 1 - tiltExp μ ν f R t 0 -
      (-t * tiltCov μ ν f R R t 0) := by
    have h10 : Integrable (fun x ↦ f x * tiltDensity (μ := μ) ν R t 1 x -
        f x * tiltDensity (μ := μ) ν R t 0 x) μ := h1.sub h0
    rw [← h.integral_mul_tiltDensity (f := f) t 1, ← h.integral_mul_tiltDensity (f := f) t 0,
      ← h.integral_mul_tiltDerivDensity hfm hf, ← integral_sub h1 h0, ← integral_sub h10 hD]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    change |g x| = f x * tiltDensity (μ := μ) ν R t 1 x - f x * tiltDensity (μ := μ) ν R t 0 x -
      f x * tiltDerivDensity (μ := μ) ν R t x
    rw [← hfg x]
    simp only [g]
    ring
  rw [hsplit]
  have := h.abs_tiltExp_taylor_le hfm hf t
  calc tiltExp μ ν f R t 1 - tiltExp μ ν f R t 0 - (-t * tiltCov μ ν f R R t 0)
      ≤ |tiltExp μ ν f R t 1 - tiltExp μ ν f R t 0 - (-t * tiltCov μ ν f R R t 0)| :=
        le_abs_self _
    _ ≤ 6 * t ^ 2 * 1 * M ^ 2 := this
    _ = 6 * t ^ 2 * M ^ 2 := by ring

/-- The derivative has total variation at most `2 t ‖R‖∞`. -/
theorem TiltData.tv_deriv_le {ν R : X → ℝ} {M : ℝ} (h : TiltData μ ν R M) (t : ℝ) :
    ∫ x, |tiltDerivDensity (μ := μ) ν R t x| ∂μ ≤ 2 * |t| * M := by
  have hM := h.M_nonneg
  have hp : ∀ x, 0 ≤ tiltDensity (μ := μ) ν R t 0 x := fun x ↦ by
    unfold tiltDensity
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (h.ν_nonneg x)) (h.tiltNum_one_pos t 0).le
  have hbound : ∀ x, |tiltDerivDensity (μ := μ) ν R t x| ≤
      (2 * |t| * M) * tiltDensity (μ := μ) ν R t 0 x := by
    intro x
    unfold tiltDerivDensity
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (hp x)]
    refine mul_le_mul_of_nonneg_right ?_ (hp x)
    have h1 := h.R_bound x
    have h2 := h.abs_tiltExp_le h.R_meas h.R_bound t 0
    have : |R x - tiltExp μ ν R R t 0| ≤ 2 * M := by
      calc |R x - tiltExp μ ν R R t 0| ≤ |R x| + |tiltExp μ ν R R t 0| := abs_sub _ _
        _ ≤ M + M := add_le_add h1 h2
        _ = 2 * M := by ring
    calc |t| * |R x - tiltExp μ ν R R t 0| ≤ |t| * (2 * M) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = 2 * |t| * M := by ring
  have hint : Integrable (fun x ↦ (2 * |t| * M) * tiltDensity (μ := μ) ν R t 0 x) μ := by
    have := h.integrable_mul_tiltDensity (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1)
      (fun _ ↦ by simp) t 0
    simp only [one_mul] at this
    exact this.const_mul _
  calc ∫ x, |tiltDerivDensity (μ := μ) ν R t x| ∂μ
      ≤ ∫ x, (2 * |t| * M) * tiltDensity (μ := μ) ν R t 0 x ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x ↦ abs_nonneg _) hint
          (Filter.Eventually.of_forall hbound)
    _ = (2 * |t| * M) * ∫ x, (fun _ ↦ (1 : ℝ)) x * tiltDensity (μ := μ) ν R t 0 x ∂μ := by
        rw [integral_const_mul]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        simp
    _ = 2 * |t| * M := by
        rw [h.integral_mul_tiltDensity, h.tiltExp_const, mul_one]

end Laplace.Multi
