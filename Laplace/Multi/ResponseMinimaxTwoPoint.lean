/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseDataInfluence

/-!
# The two-point minimax scale of a posterior expectation

The variance that governs the empirical fluctuations of a posterior expectation
(`ResponseObservableJointCovariance`) also supplies an unavoidable minimax resolution scale.

* **Le Cam's two-point bound** (`lecam_two_point`): for laws `μ ≪ η` with finite information and
  a functional taking the values `ψ₀ < ψ₁` at them, every integrable estimator `T` of `n` i.i.d.
  samples has
  `max(E_{μⁿ}|T − ψ₀|, E_{ηⁿ}|T − ψ₁|) ≥ ((ψ₁ − ψ₀)/2)(1 − √(n KL(μ‖η)))`,
  from the clipped randomised test `φ = clamp((T − ψ₀)/(ψ₁ − ψ₀), 0, 1)` and the data-law testing
  obstruction of `ResponseTestingData`;
* **the minimax scale of a posterior expectation** (`minimax_two_point_tilted`): with alternatives
  `D_t ∝ e^{t IF_{F,D}} D` along the influence function at scale `t_n = a/√n`, the two-point lower
  bound `L_n` for estimating `Ψ_F` satisfies
  `√n · L_n → (a σ_F²/2)(1 − √(a² σ_F²/2))`, `σ_F² = Σ_D(u_F, u_F)`,
  so no estimator of the posterior expectation of `F` has risk below a constant multiple of
  `σ_F/√n` uniformly over these alternatives — the same `Σ_D(u_F,u_F)` that is its sampling
  variance.
-/

open MeasureTheory InformationTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section LeCam

variable {Ω : Type*} [MeasurableSpace Ω] {μ η : Measure Ω} [IsProbabilityMeasure μ]
  [IsProbabilityMeasure η]

/-- The clipped test built from an estimator: `clamp((T − ψ₀)/(ψ₁ − ψ₀), 0, 1)`. -/
noncomputable def clipTest (T : Ω → ℝ) (ψ₀ ψ₁ : ℝ) (z : Ω) : ℝ :=
  max 0 (min 1 ((T z - ψ₀) / (ψ₁ - ψ₀)))

omit [MeasurableSpace Ω] in
theorem clipTest_nonneg (T : Ω → ℝ) (ψ₀ ψ₁ : ℝ) (z : Ω) : 0 ≤ clipTest T ψ₀ ψ₁ z :=
  le_max_left _ _

omit [MeasurableSpace Ω] in
theorem clipTest_le_one (T : Ω → ℝ) (ψ₀ ψ₁ : ℝ) (z : Ω) : clipTest T ψ₀ ψ₁ z ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem measurable_clipTest {T : Ω → ℝ} (hT : Measurable T) (ψ₀ ψ₁ : ℝ) :
    Measurable (clipTest T ψ₀ ψ₁) :=
  measurable_const.max (measurable_const.min ((hT.sub_const _).div_const _))

omit [MeasurableSpace Ω] in
/-- The clipped test is dominated by the normalised loss at `ψ₀`. -/
theorem mul_clipTest_le (T : Ω → ℝ) {ψ₀ ψ₁ : ℝ} (h : ψ₀ < ψ₁) (z : Ω) :
    (ψ₁ - ψ₀) * clipTest T ψ₀ ψ₁ z ≤ |T z - ψ₀| := by
  have hΔ : 0 < ψ₁ - ψ₀ := sub_pos.2 h
  have h1 : clipTest T ψ₀ ψ₁ z ≤ |(T z - ψ₀) / (ψ₁ - ψ₀)| :=
    max_le (abs_nonneg _) ((min_le_right _ _).trans (le_abs_self _))
  calc (ψ₁ - ψ₀) * clipTest T ψ₀ ψ₁ z ≤ (ψ₁ - ψ₀) * |(T z - ψ₀) / (ψ₁ - ψ₀)| :=
        mul_le_mul_of_nonneg_left h1 hΔ.le
    _ = |T z - ψ₀| := by
        rw [abs_div, abs_of_pos hΔ, mul_div_cancel₀ _ hΔ.ne']

omit [MeasurableSpace Ω] in
/-- The complementary clipped test is dominated by the normalised loss at `ψ₁`. -/
theorem mul_one_sub_clipTest_le (T : Ω → ℝ) {ψ₀ ψ₁ : ℝ} (h : ψ₀ < ψ₁) (z : Ω) :
    (ψ₁ - ψ₀) * (1 - clipTest T ψ₀ ψ₁ z) ≤ |T z - ψ₁| := by
  have hΔ : 0 < ψ₁ - ψ₀ := sub_pos.2 h
  set s := (T z - ψ₀) / (ψ₁ - ψ₀) with hs
  have h1 : 1 - clipTest T ψ₀ ψ₁ z ≤ |1 - s| := by
    have : min 1 s ≤ clipTest T ψ₀ ψ₁ z := le_max_right _ _
    have h2 : 1 - min 1 s ≤ |1 - s| := by
      rcases le_total 1 s with hs1 | hs1
      · rw [min_eq_left hs1, sub_self]
        exact abs_nonneg _
      · rw [min_eq_right hs1]
        exact le_abs_self _
    linarith
  calc (ψ₁ - ψ₀) * (1 - clipTest T ψ₀ ψ₁ z) ≤ (ψ₁ - ψ₀) * |1 - s| :=
        mul_le_mul_of_nonneg_left h1 hΔ.le
    _ = |T z - ψ₁| := by
        have e : (ψ₁ - ψ₀) * (1 - s) = -(T z - ψ₁) := by
          rw [hs, mul_sub, mul_one, mul_div_cancel₀ _ hΔ.ne']
          ring
        rw [← abs_of_pos hΔ, ← abs_mul, e, abs_neg]

/-- **Le Cam's two-point bound**: for `μ ≪ η` with finite information and a functional taking the
values `ψ₀ < ψ₁` at `μ` and `η`, every integrable estimator of `n` i.i.d. samples satisfies
`max(E_{μⁿ}|T − ψ₀|, E_{ηⁿ}|T − ψ₁|) ≥ ((ψ₁ − ψ₀)/2)(1 − √(n KL(μ‖η)))`. -/
theorem lecam_two_point (hμη : μ ≪ η) (hkl : klDiv μ η ≠ ⊤) {ψ₀ ψ₁ : ℝ} (h : ψ₀ < ψ₁) (n : ℕ)
    {T : (Fin n → Ω) → ℝ} (hTm : Measurable T)
    (hT₀ : Integrable T (Measure.pi fun _ : Fin n ↦ μ))
    (hT₁ : Integrable T (Measure.pi fun _ : Fin n ↦ η)) :
    (ψ₁ - ψ₀) / 2 * (1 - √(n * (klDiv μ η).toReal)) ≤
      max (∫ z, |T z - ψ₀| ∂(Measure.pi fun _ : Fin n ↦ μ))
        (∫ z, |T z - ψ₁| ∂(Measure.pi fun _ : Fin n ↦ η)) := by
  have hΔ : 0 < ψ₁ - ψ₀ := sub_pos.2 h
  have htest := testing_error_data_ge_of_klDiv hμη hkl n (measurable_clipTest hTm ψ₀ ψ₁)
    (clipTest_nonneg T ψ₀ ψ₁) (clipTest_le_one T ψ₀ ψ₁)
  have hφi : ∀ (ρ : Measure (Fin n → Ω)) [IsProbabilityMeasure ρ],
      Integrable (clipTest T ψ₀ ψ₁) ρ := fun ρ _ ↦
    Integrable.of_bound (measurable_clipTest hTm ψ₀ ψ₁).aestronglyMeasurable 1
      (ae_of_all _ fun z ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (clipTest_nonneg T ψ₀ ψ₁ z)]
        exact clipTest_le_one T ψ₀ ψ₁ z)
  have h0 : (ψ₁ - ψ₀) * ∫ z, clipTest T ψ₀ ψ₁ z ∂(Measure.pi fun _ : Fin n ↦ μ) ≤
      ∫ z, |T z - ψ₀| ∂(Measure.pi fun _ : Fin n ↦ μ) := by
    rw [← integral_const_mul]
    exact integral_mono ((hφi _).const_mul _) (hT₀.sub (integrable_const _)).abs
      fun z ↦ mul_clipTest_le T h z
  have h1 : (ψ₁ - ψ₀) * ∫ z, (1 - clipTest T ψ₀ ψ₁ z) ∂(Measure.pi fun _ : Fin n ↦ η) ≤
      ∫ z, |T z - ψ₁| ∂(Measure.pi fun _ : Fin n ↦ η) := by
    rw [← integral_const_mul]
    exact integral_mono (((integrable_const _).sub (hφi _)).const_mul _)
      (hT₁.sub (integrable_const _)).abs fun z ↦ mul_one_sub_clipTest_le T h z
  have hmax := le_max_left (∫ z, |T z - ψ₀| ∂(Measure.pi fun _ : Fin n ↦ μ))
    (∫ z, |T z - ψ₁| ∂(Measure.pi fun _ : Fin n ↦ η))
  have hmax' := le_max_right (∫ z, |T z - ψ₀| ∂(Measure.pi fun _ : Fin n ↦ μ))
    (∫ z, |T z - ψ₁| ∂(Measure.pi fun _ : Fin n ↦ η))
  nlinarith [htest, h0, h1, hmax, hmax']

/-- **Le Cam's two-point bound, reversed order** (`ψ₁ < ψ₀`): the same bound with the roles of the
two values exchanged, from the test `1 − clamp((T − ψ₁)/(ψ₀ − ψ₁), 0, 1)`. -/
theorem lecam_two_point_rev (hμη : μ ≪ η) (hkl : klDiv μ η ≠ ⊤) {ψ₀ ψ₁ : ℝ} (h : ψ₁ < ψ₀)
    (n : ℕ) {T : (Fin n → Ω) → ℝ} (hTm : Measurable T)
    (hT₀ : Integrable T (Measure.pi fun _ : Fin n ↦ μ))
    (hT₁ : Integrable T (Measure.pi fun _ : Fin n ↦ η)) :
    (ψ₀ - ψ₁) / 2 * (1 - √(n * (klDiv μ η).toReal)) ≤
      max (∫ z, |T z - ψ₀| ∂(Measure.pi fun _ : Fin n ↦ μ))
        (∫ z, |T z - ψ₁| ∂(Measure.pi fun _ : Fin n ↦ η)) := by
  have hΔ : 0 < ψ₀ - ψ₁ := sub_pos.2 h
  have hφm : Measurable fun z ↦ 1 - clipTest T ψ₁ ψ₀ z :=
    measurable_const.sub (measurable_clipTest hTm ψ₁ ψ₀)
  have htest := testing_error_data_ge_of_klDiv hμη hkl n hφm
    (fun z ↦ by linarith [clipTest_le_one T ψ₁ ψ₀ z])
    (fun z ↦ by linarith [clipTest_nonneg T ψ₁ ψ₀ z])
  have hφi : ∀ (ρ : Measure (Fin n → Ω)) [IsProbabilityMeasure ρ],
      Integrable (clipTest T ψ₁ ψ₀) ρ := fun ρ _ ↦
    Integrable.of_bound (measurable_clipTest hTm ψ₁ ψ₀).aestronglyMeasurable 1
      (ae_of_all _ fun z ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (clipTest_nonneg T ψ₁ ψ₀ z)]
        exact clipTest_le_one T ψ₁ ψ₀ z)
  have h0 : (ψ₀ - ψ₁) * ∫ z, (1 - clipTest T ψ₁ ψ₀ z) ∂(Measure.pi fun _ : Fin n ↦ μ) ≤
      ∫ z, |T z - ψ₀| ∂(Measure.pi fun _ : Fin n ↦ μ) := by
    rw [← integral_const_mul]
    exact integral_mono (((integrable_const _).sub (hφi _)).const_mul _)
      (hT₀.sub (integrable_const _)).abs fun z ↦ mul_one_sub_clipTest_le T h z
  have h1 : (ψ₀ - ψ₁) * ∫ z, clipTest T ψ₁ ψ₀ z ∂(Measure.pi fun _ : Fin n ↦ η) ≤
      ∫ z, |T z - ψ₁| ∂(Measure.pi fun _ : Fin n ↦ η) := by
    rw [← integral_const_mul]
    exact integral_mono ((hφi _).const_mul _) (hT₁.sub (integrable_const _)).abs
      fun z ↦ mul_clipTest_le T h z
  have e : ∫ z, (1 - (1 - clipTest T ψ₁ ψ₀ z)) ∂(Measure.pi fun _ : Fin n ↦ η) =
      ∫ z, clipTest T ψ₁ ψ₀ z ∂(Measure.pi fun _ : Fin n ↦ η) := by
    simp only [sub_sub_cancel]
  rw [e] at htest
  have hmax := le_max_left (∫ z, |T z - ψ₀| ∂(Measure.pi fun _ : Fin n ↦ μ))
    (∫ z, |T z - ψ₁| ∂(Measure.pi fun _ : Fin n ↦ η))
  have hmax' := le_max_right (∫ z, |T z - ψ₀| ∂(Measure.pi fun _ : Fin n ↦ μ))
    (∫ z, |T z - ψ₁| ∂(Measure.pi fun _ : Fin n ↦ η))
  nlinarith [htest, h0, h1, hmax, hmax']

end LeCam

section Scale

/-- The scale `t_n = a/√n` tends to `0` through nonzero values. -/
theorem tendsto_scale {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ a / Real.sqrt n) atTop (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).const_mul a
    simpa [div_eq_mul_inv, Function.comp_def] using this
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    exact (div_pos ha (Real.sqrt_pos.2 this)).ne'

end Scale

section Minimax

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (D : Measure X) [IsProbabilityMeasure D] (hDν : D ≪ ν) (hνD : ν ≪ D)
include hS hDν hνD

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The feature mean of the data law. -/
local notation "mD" => (fun j : J ↦ ∫ x, S j x ∂D)

/-- The regression direction of `F` at the response of `D`. -/
local notation "uF" F => regressionDir hS ν F (θr mD)

omit [IsProbabilityMeasure D] hDν hνD in
/-- The influence function is bounded. -/
theorem bdd_dataInfluence (F : X → ℝ) : Bdd (dataInfluence hS ν D F) :=
  (bdd_dirLoss hS _).sub (Bdd.const _)

omit hDν hνD in
/-- The variance of the influence function is the data variance of the regression feature. -/
theorem lawCov_dataInfluence_self (F : X → ℝ) :
    lawCov D (dataInfluence hS ν D F) (dataInfluence hS ν D F) =
      dataBilin hS ν D (uF F) (uF F) := by
  rw [lawCov_dataInfluence hS ν D F (bdd_dataInfluence hS ν D F), lawCov_comm,
    lawCov_dataInfluence hS ν D F (bdd_dirLoss hS _), lawCov_comm]
  rfl

/-- The response derivative along the influence direction is the sampling variance. -/
theorem hasDerivAt_dataObs_tilted_dataInfluence {F : X → ℝ} (hF : Bdd F) :
    HasDerivAt (fun t ↦ dataObs hS ν F (D.tilted fun x ↦ t * dataInfluence hS ν D F x))
      (dataBilin hS ν D (uF F) (uF F)) 0 := by
  have h := hasDerivAt_dataObs_tilted hS ν D hDν hνD hF (bdd_dataInfluence hS ν D F)
  rw [lawCov_comm, lawCov_dataInfluence hS ν D F (bdd_dirLoss hS _), lawCov_comm] at h
  exact h

/-- **The minimax scale of a posterior expectation**: along the alternatives
`D_t ∝ e^{t IF_{F,D}} D` at scale `t_n = a/√n`, the Le Cam two-point lower bound `L_n` for
estimating `Ψ_F` satisfies `√n · L_n → (a σ_F²/2)(1 − √(a² σ_F²/2))` with `σ_F² = Σ_D(u_F,u_F)`,
and for `n` large every integrable estimator has
`max(E_{Dⁿ}|T − Ψ_F(D)|, E_{D_{t_n}ⁿ}|T − Ψ_F(D_{t_n})|) ≥ L_n`. -/
theorem minimax_two_point_tilted {F : X → ℝ} (hF : Bdd F)
    (hpos : 0 < dataBilin hS ν D (uF F) (uF F)) {a : ℝ} (ha : 0 < a) :
    ∃ L : ℕ → ℝ,
      Tendsto (fun n : ℕ ↦ Real.sqrt n * L n) atTop
        (𝓝 (a * dataBilin hS ν D (uF F) (uF F) / 2 *
          (1 - √(a ^ 2 * dataBilin hS ν D (uF F) (uF F) / 2)))) ∧
      ∀ᶠ n : ℕ in atTop, ∀ T : (Fin n → X) → ℝ, Measurable T →
        Integrable T (Measure.pi fun _ : Fin n ↦ D) →
        Integrable T (Measure.pi fun _ : Fin n ↦
          D.tilted fun x ↦ (a / Real.sqrt n) * dataInfluence hS ν D F x) →
        L n ≤ max (∫ z, |T z - dataObs hS ν F D| ∂(Measure.pi fun _ : Fin n ↦ D))
          (∫ z, |T z - dataObs hS ν F (D.tilted fun x ↦ (a / Real.sqrt n) *
            dataInfluence hS ν D F x)| ∂(Measure.pi fun _ : Fin n ↦
              D.tilted fun x ↦ (a / Real.sqrt n) * dataInfluence hS ν D F x)) := by
  set σ2 := dataBilin hS ν D (uF F) (uF F) with hσ2
  set h := dataInfluence hS ν D F with hh
  have hhb : Bdd h := bdd_dataInfluence hS ν D F
  set t : ℕ → ℝ := fun n ↦ a / Real.sqrt n with ht
  -- the increment of the functional and the information along the alternatives
  set Δ : ℕ → ℝ := fun n ↦ dataObs hS ν F (D.tilted fun x ↦ t n * h x) - dataObs hS ν F D
    with hΔ
  set KL : ℕ → ℝ := fun n ↦ (klDiv (D.tilted fun x ↦ t n * h x) D).toReal with hKL
  have hslope := (hasDerivAt_iff_tendsto_slope_zero.1
    (hasDerivAt_dataObs_tilted_dataInfluence hS ν D hDν hνD hF)).comp (tendsto_scale ha)
  -- `√n Δ_n = a · (Δ_n / t_n)`
  have e1 : ∀ n : ℕ, 0 < n → Real.sqrt n * Δ n = a * ((t n)⁻¹ • (dataObs hS ν F
      (D.tilted fun x ↦ (0 + t n) * h x) - dataObs hS ν F (D.tilted fun x ↦ 0 * h x))) := by
    intro n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
    simp only [zero_add, hΔ, smul_eq_mul, tilted_zero_mul_eq]
    rw [ht]
    field_simp
  have hA : Tendsto (fun n : ℕ ↦ Real.sqrt n * Δ n) atTop (𝓝 (a * σ2)) := by
    refine (hslope.const_mul a).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [e1 n hn]
    rfl
  refine ⟨fun n ↦ Δ n / 2 * (1 - √(n * KL n)), ?_, ?_⟩
  · -- the limit
    have hkl := (tendsto_klDiv_tilted_div_sq D hhb).comp (tendsto_scale ha)
    rw [lawCov_dataInfluence_self hS ν D F] at hkl
    -- `n KL_n = a² · (KL_n / t_n²)`
    have e2 : ∀ n : ℕ, 0 < n → (n : ℝ) * KL n = a ^ 2 * (KL n / (t n) ^ 2) := by
      intro n hn
      have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
      rw [ht]
      simp only
      rw [div_pow, Real.sq_sqrt hn'.le]
      field_simp
    have hB : Tendsto (fun n : ℕ ↦ (n : ℝ) * KL n) atTop (𝓝 (a ^ 2 * (σ2 / 2))) := by
      refine (hkl.const_mul (a ^ 2)).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [e2 n hn]
      rfl
    have hlim := ((hA.div_const 2).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub ((Real.continuous_sqrt.tendsto _).comp hB)))
    rw [show a ^ 2 * σ2 / 2 = a ^ 2 * (σ2 / 2) by ring]
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [Function.comp_def]
    ring
  · -- eventually the increment is positive and Le Cam applies
    have hev := hA.eventually (lt_mem_nhds (by positivity : 0 < a * σ2))
    filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
    intro T hTm hT₀ hT₁
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
    have hΔpos : 0 < Δ n := by
      by_contra hcon
      push Not at hcon
      have : Real.sqrt n * Δ n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.le hcon
      linarith
    have := isProbabilityMeasure_tilted (integrable_exp_of_bdd D (hhb.const_mul (t n)))
    have hle := lecam_two_point_rev (μ := D.tilted fun x ↦ t n * h x) (η := D)
      (tilted_absolutelyContinuous D _) (klDiv_tilted_data_ne_top D hhb (t n))
      (show dataObs hS ν F D < dataObs hS ν F (D.tilted fun x ↦ t n * h x) by
        simp only [hΔ] at hΔpos
        linarith) n hTm hT₁ hT₀
    rw [max_comm] at hle
    exact hle

end Minimax

end Laplace.Multi
