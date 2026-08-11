/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.QuadGaussian

/-!
# Gaussian covariance rigidity

Opening tide of the degree-`k` tensor-recovery programme (stage J2 of
the scoping consult, with the needed slices of J0/J1 inline): a
continuous homogeneous function of positive degree and polynomial
growth whose self-covariance against the quadratic Gaussian vanishes
is identically zero. This is the no-Isserlis injectivity input for
every recovery rung: no moment matrices, no monomial enumeration —
only full support (via a direct ball argument on the positive
continuous kernel) and the variance identity.
-/

open Real Matrix MeasureTheory

namespace Laplace.Multi

variable {d : ℕ}

/-- Polynomial growth certificate for observables. -/
def HasPolynomialGrowth (f : EuclidD d → ℝ) : Prop :=
  ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧ ∀ x : EuclidD d, |f x| ≤ C * (1 + ‖x‖ ^ n)

/-- Homogeneity of degree `k` under real dilations. -/
def IsHomogeneousOfDegree (k : ℕ) (Q : EuclidD d → ℝ) : Prop :=
  ∀ (a : ℝ) (x : EuclidD d), Q (a • x) = a ^ k * Q x

theorem HasPolynomialGrowth.mul {f g : EuclidD d → ℝ}
    (hf : HasPolynomialGrowth f) (hg : HasPolynomialGrowth g) :
    HasPolynomialGrowth (fun x ↦ f x * g x) := by
  obtain ⟨C₁, n₁, hC₁, h₁⟩ := hf
  obtain ⟨C₂, n₂, hC₂, h₂⟩ := hg
  refine ⟨3 * (C₁ * C₂), n₁ + n₂, by positivity, fun x ↦ ?_⟩
  have hxn : (0 : ℝ) ≤ ‖x‖ ^ (n₁ + n₂) := by positivity
  have h1 : ‖x‖ ^ n₁ ≤ 1 + ‖x‖ ^ (n₁ + n₂) := by
    rcases le_total ‖x‖ 1 with h | h
    · have := pow_le_one₀ (norm_nonneg x) h (n := n₁)
      linarith
    · have := pow_le_pow_right₀ h (Nat.le_add_right n₁ n₂)
      linarith
  have h2 : ‖x‖ ^ n₂ ≤ 1 + ‖x‖ ^ (n₁ + n₂) := by
    rcases le_total ‖x‖ 1 with h | h
    · have := pow_le_one₀ (norm_nonneg x) h (n := n₂)
      linarith
    · have := pow_le_pow_right₀ h (Nat.le_add_left n₂ n₁)
      linarith
  have h3 : ‖x‖ ^ n₁ * ‖x‖ ^ n₂ = ‖x‖ ^ (n₁ + n₂) := (pow_add _ _ _).symm
  have hb : (1 + ‖x‖ ^ n₁) * (1 + ‖x‖ ^ n₂) ≤
      3 * (1 + ‖x‖ ^ (n₁ + n₂)) := by
    nlinarith
  calc |f x * g x| = |f x| * |g x| := abs_mul _ _
    _ ≤ C₁ * (1 + ‖x‖ ^ n₁) * (C₂ * (1 + ‖x‖ ^ n₂)) :=
        mul_le_mul (h₁ x) (h₂ x) (abs_nonneg _) (by positivity)
    _ = C₁ * C₂ * ((1 + ‖x‖ ^ n₁) * (1 + ‖x‖ ^ n₂)) := by ring
    _ ≤ C₁ * C₂ * (3 * (1 + ‖x‖ ^ (n₁ + n₂))) := by
        apply mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 3 * (C₁ * C₂) * (1 + ‖x‖ ^ (n₁ + n₂)) := by ring

theorem HasPolynomialGrowth.sub_const {f : EuclidD d → ℝ}
    (hf : HasPolynomialGrowth f) (c : ℝ) :
    HasPolynomialGrowth (fun x ↦ f x - c) := by
  obtain ⟨C, n, hC, h⟩ := hf
  refine ⟨C + |c|, n, by positivity, fun x ↦ ?_⟩
  have hxn : (0 : ℝ) ≤ ‖x‖ ^ n := by positivity
  calc |f x - c| ≤ |f x| + |c| := abs_sub _ _
    _ ≤ C * (1 + ‖x‖ ^ n) + |c| := by linarith [h x]
    _ ≤ (C + |c|) * (1 + ‖x‖ ^ n) := by nlinarith [abs_nonneg c]

/-- **J0 slice**: polynomial-growth observables are integrable
against the quadratic Gaussian kernel. -/
theorem integrable_mul_quadKernel_of_polynomialGrowth
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {f : EuclidD d → ℝ}
    (hf_meas : AEStronglyMeasurable f (volume : Measure (EuclidD d)))
    (hf : HasPolynomialGrowth f) :
    Integrable (fun x : EuclidD d ↦ f x * quadKernel H x) := by
  obtain ⟨C, n, hC, h⟩ := hf
  have hdom : Integrable (fun x : EuclidD d ↦
      C * (quadKernel H x + ‖x‖ ^ n * quadKernel H x)) :=
    ((quadKernel_integrable hH).add
      (quadKernel_integrable_pow hH n)).const_mul C
  refine hdom.mono'
    (hf_meas.mul (quadKernel_continuous H).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (quadKernel_pos H x)]
  calc |f x| * quadKernel H x
      ≤ C * (1 + ‖x‖ ^ n) * quadKernel H x :=
        mul_le_mul_of_nonneg_right (h x) (quadKernel_pos H x).le
    _ = C * (quadKernel H x + ‖x‖ ^ n * quadKernel H x) := by ring

/-- **J1 slice**: a continuous nonnegative observable with vanishing
weighted integral vanishes everywhere (full support of the quadratic
Gaussian, by the direct ball argument). -/
theorem continuous_eq_zero_of_integral_mul_quadKernel_eq_zero
    {H : Matrix (Fin d) (Fin d) ℝ}
    {f : EuclidD d → ℝ} (hf_cont : Continuous f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_int : Integrable (fun x : EuclidD d ↦ f x * quadKernel H x))
    (hzero : ∫ x : EuclidD d, f x * quadKernel H x = 0) :
    ∀ x, f x = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀⟩ := hcon
  set g : EuclidD d → ℝ := fun x ↦ f x * quadKernel H x with hg_def
  have hg_cont : Continuous g := hf_cont.mul (quadKernel_continuous H)
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x ↦
    mul_nonneg (hf_nonneg x) (quadKernel_pos H x).le
  have hgx₀ : 0 < g x₀ :=
    mul_pos ((hf_nonneg x₀).lt_of_ne (Ne.symm hx₀)) (quadKernel_pos H x₀)
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ x ∈ Metric.ball x₀ r,
      g x₀ / 2 ≤ g x := by
    have hc := hg_cont.continuousAt (x := x₀)
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ, hδ, hd⟩ := hc (g x₀ / 2) (by positivity)
    refine ⟨δ, hδ, fun x hx ↦ ?_⟩
    have := hd (Metric.mem_ball.mp hx)
    rw [Real.dist_eq] at this
    have := abs_lt.mp this
    linarith [this.1]
  have hlower : (volume (Metric.ball x₀ r)).toReal * (g x₀ / 2) ≤
      ∫ x in Metric.ball x₀ r, g x := by
    have := MeasureTheory.setIntegral_ge_of_const_le
      (measurableSet_ball) (measure_ball_lt_top.ne)
      hball (hf_int.integrableOn)
    simpa [measureReal_def] using this
  have hvol : 0 < (volume (Metric.ball x₀ r)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume x₀ hr).ne'
      measure_ball_lt_top.ne
  have hup : ∫ x in Metric.ball x₀ r, g x ≤ ∫ x : EuclidD d, g x :=
    setIntegral_le_integral hf_int
      (Filter.Eventually.of_forall hg_nonneg)
  have : (0 : ℝ) < ∫ x in Metric.ball x₀ r, g x := by
    calc (0 : ℝ) < (volume (Metric.ball x₀ r)).toReal * (g x₀ / 2) := by
          positivity
      _ ≤ _ := hlower
  linarith [hup, this]

/-- The normalized quadratic-Gaussian expectation of an observable. -/
noncomputable def gaussianExpectation (H : Matrix (Fin d) (Fin d) ℝ)
    (f : EuclidD d → ℝ) : ℝ :=
  (∫ x : EuclidD d, f x * quadKernel H x) /
    ∫ x : EuclidD d, quadKernel H x

/-- The quadratic-Gaussian covariance of two observables. -/
noncomputable def gaussianCovariance (H : Matrix (Fin d) (Fin d) ℝ)
    (f g : EuclidD d → ℝ) : ℝ :=
  gaussianExpectation H (fun x ↦ f x * g x) -
    gaussianExpectation H f * gaussianExpectation H g

/-- **The variance identity**: self-covariance is the weighted
integral of the squared deviation, over the partition value. -/
theorem gaussianCovariance_self_eq {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {Q : EuclidD d → ℝ}
    (hQ_meas : AEStronglyMeasurable Q (volume : Measure (EuclidD d)))
    (hQ_growth : HasPolynomialGrowth Q) :
    (∫ x : EuclidD d, (Q x - gaussianExpectation H Q) ^ 2 *
        quadKernel H x) =
      (∫ x : EuclidD d, quadKernel H x) * gaussianCovariance H Q Q := by
  have hZpos := integral_quadKernel_pos hH
  have hA : Integrable
      (fun x : EuclidD d ↦ (Q x * Q x) * quadKernel H x) :=
    integrable_mul_quadKernel_of_polynomialGrowth hH
      (hQ_meas.mul hQ_meas) (hQ_growth.mul hQ_growth)
  have hB : Integrable (fun x : EuclidD d ↦
      2 * gaussianExpectation H Q * (Q x * quadKernel H x)) :=
    (integrable_mul_quadKernel_of_polynomialGrowth hH
      hQ_meas hQ_growth).const_mul _
  have hC : Integrable (fun x : EuclidD d ↦
      gaussianExpectation H Q ^ 2 * quadKernel H x) :=
    (quadKernel_integrable hH).const_mul _
  have hexp : (fun x : EuclidD d ↦
      (Q x - gaussianExpectation H Q) ^ 2 * quadKernel H x) =
      fun x : EuclidD d ↦
        ((Q x * Q x) * quadKernel H x -
          2 * gaussianExpectation H Q * (Q x * quadKernel H x)) +
          gaussianExpectation H Q ^ 2 * quadKernel H x := by
    funext x
    ring
  have hAB : Integrable (fun x : EuclidD d ↦
      (Q x * Q x) * quadKernel H x -
        2 * gaussianExpectation H Q * (Q x * quadKernel H x)) :=
    hA.sub hB
  rw [hexp, integral_add hAB hC, integral_sub hA hB,
    integral_const_mul, integral_const_mul]
  unfold gaussianCovariance gaussianExpectation
  field_simp
  ring

/-- **Gaussian covariance rigidity** (tensor programme J2): a
continuous homogeneous observable of positive degree and polynomial
growth with vanishing self-covariance is identically zero. -/
theorem homogeneous_eq_zero_of_gaussianCovariance_self_eq_zero
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {k : ℕ} (hk : 0 < k) {Q : EuclidD d → ℝ}
    (hQ_cont : Continuous Q) (hQ_growth : HasPolynomialGrowth Q)
    (hQ_hom : IsHomogeneousOfDegree k Q)
    (hvar : gaussianCovariance H Q Q = 0) :
    Q = 0 := by
  have hzero : ∫ x : EuclidD d,
      (Q x - gaussianExpectation H Q) ^ 2 * quadKernel H x = 0 := by
    rw [gaussianCovariance_self_eq hH
      hQ_cont.aestronglyMeasurable hQ_growth, hvar, mul_zero]
  have hdev_growth : HasPolynomialGrowth
      (fun x ↦ (Q x - gaussianExpectation H Q) ^ 2) := by
    have h1 := hQ_growth.sub_const (gaussianExpectation H Q)
    have h2 := h1.mul h1
    refine h2.imp ?_
    intro C hC
    refine hC.imp fun n hn ↦ ⟨hn.1, fun x ↦ ?_⟩
    have := hn.2 x
    calc |(Q x - gaussianExpectation H Q) ^ 2| =
        |(Q x - gaussianExpectation H Q) *
          (Q x - gaussianExpectation H Q)| := by rw [sq]
      _ ≤ C * (1 + ‖x‖ ^ n) := this
  have hdev_cont : Continuous
      (fun x : EuclidD d ↦ (Q x - gaussianExpectation H Q) ^ 2) :=
    (hQ_cont.sub continuous_const).pow 2
  have hdev_int : Integrable (fun x : EuclidD d ↦
      (Q x - gaussianExpectation H Q) ^ 2 * quadKernel H x) :=
    integrable_mul_quadKernel_of_polynomialGrowth hH
      hdev_cont.aestronglyMeasurable hdev_growth
  have hpt := continuous_eq_zero_of_integral_mul_quadKernel_eq_zero
    hdev_cont (fun x ↦ sq_nonneg _) hdev_int hzero
  have hQc : ∀ x, Q x = gaussianExpectation H Q := by
    intro x
    have := hpt x
    have hsub : Q x - gaussianExpectation H Q = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith [hsub]
  have h0 : Q 0 = 0 := by
    have := hQ_hom 0 0
    rw [smul_zero, zero_pow hk.ne', zero_mul] at this
    exact this
  funext x
  rw [Pi.zero_apply, hQc x, ← h0, hQc 0]

end Laplace.Multi
