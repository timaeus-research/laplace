/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.GradeComparison
import Laplace.Multi.RateCalculus

/-!
# Kernel-level normalized comparison and masked one-grade limits

Two layers of the weighted-jet induction (germbij §7.4(b)):

* `tendsto_normalizedKernel_difference_div_pow` — the quotient algebra of the one-grade
  comparison for arbitrary kernels `K₁ K₂ : ℝ → X → ℝ` with common limit `K₀`: from
  the rate limits of the numerator and partition differences and the plain limits of
  the base family, the normalized moments separate at the rate with the `K₀`-covariance
  as coefficient. The exponential structure plays no role here.
* `maskedKernel E P V h = 1_{E h} · e^{-(P + V h)}` — the localized (cutoff) rescaled
  density; `tendsto_integral_maskedKernel` (limit of the base family) and
  `tendsto_integral_maskedKernel_difference_div_pow` (rate limit of the difference)
  discharge the kernel-level hypotheses by dominated convergence, with domination from
  a common lower bound `c P ≤ P + V h` on the mask and a polynomial bound on the divided
  correction difference. `tendsto_masked_normalized_difference_div_pow` assembles the
  localized one-grade limit `→ −Cov_P(A, Q)` under a common mask.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-! ### The quotient algebra for arbitrary kernels -/

/-- **Kernel-level normalized comparison.** -/
theorem tendsto_normalizedKernel_difference_div_pow (K₁ K₂ : ℝ → X → ℝ) (K₀ A Q : X → ℝ)
    (ρ : ℕ)
    (hΔN : Tendsto (fun h : ℝ ↦ ((∫ x, A x * K₂ h x ∂μ) - ∫ x, A x * K₁ h x ∂μ) / h ^ ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 (-∫ x, A x * Q x * K₀ x ∂μ)))
    (hΔZ : Tendsto (fun h : ℝ ↦ ((∫ x, K₂ h x ∂μ) - ∫ x, K₁ h x ∂μ) / h ^ ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 (-∫ x, Q x * K₀ x ∂μ)))
    (hN₁ : Tendsto (fun h : ℝ ↦ ∫ x, A x * K₁ h x ∂μ) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, A x * K₀ x ∂μ)))
    (hZ₁ : Tendsto (fun h : ℝ ↦ ∫ x, K₁ h x ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, K₀ x ∂μ)))
    (hZ₂ : Tendsto (fun h : ℝ ↦ ∫ x, K₂ h x ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, K₀ x ∂μ)))
    (hZpos : 0 < ∫ x, K₀ x ∂μ) :
    Tendsto (fun h : ℝ ↦ ((∫ x, A x * K₂ h x ∂μ) / (∫ x, K₂ h x ∂μ) -
        (∫ x, A x * K₁ h x ∂μ) / ∫ x, K₁ h x ∂μ) / h ^ ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-((∫ x, A x * Q x * K₀ x ∂μ) / (∫ x, K₀ x ∂μ) -
        (∫ x, A x * K₀ x ∂μ) / (∫ x, K₀ x ∂μ) * ((∫ x, Q x * K₀ x ∂μ) / ∫ x, K₀ x ∂μ)))) := by
  set Z0 : ℝ := ∫ x, K₀ x ∂μ with hZ0_def
  have hZ₁low : ∀ᶠ h in 𝓝[>] (0 : ℝ), Z0 / 2 ≤ ∫ x, K₁ h x ∂μ :=
    hZ₁.eventually_const_le (half_lt_self hZpos)
  have hZ₂low : ∀ᶠ h in 𝓝[>] (0 : ℝ), Z0 / 2 ≤ ∫ x, K₂ h x ∂μ :=
    hZ₂.eventually_const_le (half_lt_self hZpos)
  have hQ1 := hΔN.div hZ₂ hZpos.ne'
  have hQ2 := hN₁.div hZ₁ hZpos.ne'
  have hQ3 := hΔZ.div hZ₂ hZpos.ne'
  have hRHS := hQ1.sub (hQ2.mul hQ3)
  have hval : (-∫ x, A x * Q x * K₀ x ∂μ) / Z0 -
      ((∫ x, A x * K₀ x ∂μ) / Z0) * ((-∫ x, Q x * K₀ x ∂μ) / Z0) =
      -((∫ x, A x * Q x * K₀ x ∂μ) / Z0 -
        (∫ x, A x * K₀ x ∂μ) / Z0 * ((∫ x, Q x * K₀ x ∂μ) / Z0)) := by
    ring
  rw [hval] at hRHS
  refine hRHS.congr' ?_
  filter_upwards [hZ₁low, hZ₂low, self_mem_nhdsWithin] with h h1 h2 hh0'
  have hh0 : (0 : ℝ) < h := hh0'
  have hZ0half : (0 : ℝ) < Z0 / 2 := half_pos hZpos
  have hZ₁ne : (∫ x, K₁ h x ∂μ) ≠ 0 := (lt_of_lt_of_le hZ0half h1).ne'
  have hZ₂ne : (∫ x, K₂ h x ∂μ) ≠ 0 := (lt_of_lt_of_le hZ0half h2).ne'
  have hhρ : (h : ℝ) ^ ρ ≠ 0 := (pow_pos hh0 ρ).ne'
  simp only [Pi.div_apply]
  field_simp
  ring

/-- The `K₀ = e^{-P}` specialisation of the limit value is `−Cov_P(A, Q)`. -/
theorem neg_cov_eq (P A Q : X → ℝ) :
    -((∫ x, A x * Q x * Real.exp (-P x) ∂μ) / (∫ x, Real.exp (-P x) ∂μ) -
        (∫ x, A x * Real.exp (-P x) ∂μ) / (∫ x, Real.exp (-P x) ∂μ) *
          ((∫ x, Q x * Real.exp (-P x) ∂μ) / ∫ x, Real.exp (-P x) ∂μ)) =
      -covarianceUnder μ P A Q := by
  unfold covarianceUnder expectationUnder
  rfl

/-! ### Masked (cutoff) kernels -/

/-- The masked rescaled density `1_{E h} · e^{-(P + V h)}`. -/
noncomputable def maskedKernel (E : ℝ → Set X) (P : X → ℝ) (V : ℝ → X → ℝ) (h : ℝ) (x : X) :
    ℝ :=
  (E h).indicator (fun x ↦ Real.exp (-(P x + V h x))) x

omit [MeasurableSpace X] in
theorem maskedKernel_of_mem {E : ℝ → Set X} {P : X → ℝ} {V : ℝ → X → ℝ} {h : ℝ} {x : X}
    (hx : x ∈ E h) : maskedKernel E P V h x = Real.exp (-(P x + V h x)) :=
  Set.indicator_of_mem hx _

omit [MeasurableSpace X] in
theorem maskedKernel_of_notMem {E : ℝ → Set X} {P : X → ℝ} {V : ℝ → X → ℝ} {h : ℝ} {x : X}
    (hx : x ∉ E h) : maskedKernel E P V h x = 0 :=
  Set.indicator_of_notMem hx _

omit [MeasurableSpace X] in
theorem maskedKernel_nonneg (E : ℝ → Set X) (P : X → ℝ) (V : ℝ → X → ℝ) (h : ℝ) (x : X) :
    0 ≤ maskedKernel E P V h x :=
  Set.indicator_nonneg (fun _ _ ↦ (Real.exp_pos _).le) _

theorem measurable_maskedKernel {E : ℝ → Set X} {P : X → ℝ} {V : ℝ → X → ℝ}
    (hE : ∀ h, MeasurableSet (E h)) (hP : Measurable P) (hV : ∀ h, Measurable (V h)) (h : ℝ) :
    Measurable (maskedKernel E P V h) :=
  Measurable.indicator (Real.measurable_exp.comp ((hP.add (hV h)).neg)) (hE h)

omit [MeasurableSpace X] in
/-- On the mask, a common lower bound `c P ≤ P + V h` gives the Gaussian-type domination
`maskedKernel ≤ e^{-cP}`. -/
theorem maskedKernel_le {E : ℝ → Set X} {P : X → ℝ} {V : ℝ → X → ℝ} {c : ℝ} {h : ℝ}
    (hlow : ∀ x ∈ E h, c * P x ≤ P x + V h x) (x : X) :
    maskedKernel E P V h x ≤ Real.exp (-(c * P x)) := by
  by_cases hx : x ∈ E h
  · rw [maskedKernel_of_mem hx]
    exact Real.exp_le_exp.mpr (neg_le_neg (hlow x hx))
  · rw [maskedKernel_of_notMem hx]
    positivity

/-- **Limit of a masked base family**: with the mask eventually containing every point
and the correction vanishing pointwise, `∫ A · maskedKernel → ∫ A e^{-P}`. -/
theorem tendsto_integral_maskedKernel {E : ℝ → Set X} {P : X → ℝ} {V : ℝ → X → ℝ}
    {A : X → ℝ} {c : ℝ}
    (hE : ∀ h, MeasurableSet (E h)) (hEmem : ∀ x, ∀ᶠ h in 𝓝[>] (0 : ℝ), x ∈ E h)
    (hP : Measurable P) (hV : ∀ h, Measurable (V h)) (hA : Measurable A)
    (hVlim : ∀ x, Tendsto (fun h : ℝ ↦ V h x) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hlow : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ x ∈ E h, c * P x ≤ P x + V h x)
    (hG : Integrable (fun x ↦ |A x| * Real.exp (-(c * P x))) μ) :
    Tendsto (fun h : ℝ ↦ ∫ x, A x * maskedKernel E P V h x ∂μ) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, A x * Real.exp (-P x) ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ |A x| * Real.exp (-(c * P x))) ?_ ?_ hG ?_
  · filter_upwards with h
    exact (hA.mul (measurable_maskedKernel hE hP hV h)).aestronglyMeasurable
  · filter_upwards [hlow] with h hl
    refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (maskedKernel_nonneg E P V h x)]
    exact mul_le_mul_of_nonneg_left (maskedKernel_le hl x) (abs_nonneg _)
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    have hexp : Tendsto (fun h : ℝ ↦ Real.exp (-(P x + V h x))) (𝓝[>] (0 : ℝ))
        (𝓝 (Real.exp (-P x))) := by
      have := ((Real.continuous_exp.tendsto _).comp
        (((hVlim x).const_add (P x)).neg))
      simpa [Function.comp_def] using this
    refine (hexp.const_mul (A x)).congr' ?_
    filter_upwards [hEmem x] with h hx
    rw [maskedKernel_of_mem hx]

/-- **Rate limit of the masked difference**: `(∫ A K₂ − ∫ A K₁)/h^ρ → −∫ A Q e^{-P}`. -/
theorem tendsto_integral_maskedKernel_difference_div_pow {E : ℝ → Set X} {P : X → ℝ}
    {V₁ V₂ : ℝ → X → ℝ} {A Q B : X → ℝ} {c : ℝ} {ρ : ℕ}
    (hE : ∀ h, MeasurableSet (E h)) (hEmem : ∀ x, ∀ᶠ h in 𝓝[>] (0 : ℝ), x ∈ E h)
    (hP : Measurable P) (hV₁ : ∀ h, Measurable (V₁ h)) (hV₂ : ∀ h, Measurable (V₂ h))
    (hA : Measurable A)
    (hV₁lim : ∀ x, Tendsto (fun h : ℝ ↦ V₁ h x) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hV₂lim : ∀ x, Tendsto (fun h : ℝ ↦ V₂ h x) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hdiff : ∀ x, Tendsto (fun h : ℝ ↦ (V₂ h x - V₁ h x) / h ^ ρ) (𝓝[>] (0 : ℝ)) (𝓝 (Q x)))
    (hlow₁ : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ x ∈ E h, c * P x ≤ P x + V₁ h x)
    (hlow₂ : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ x ∈ E h, c * P x ≤ P x + V₂ h x)
    (hB0 : ∀ x, 0 ≤ B x)
    (hbound : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ x ∈ E h, |V₂ h x - V₁ h x| / h ^ ρ ≤ B x)
    (hG : Integrable (fun x ↦ |A x| * B x * Real.exp (-(c * P x))) μ)
    (hint₁ : ∀ᶠ h in 𝓝[>] (0 : ℝ), Integrable (fun x ↦ A x * maskedKernel E P V₁ h x) μ)
    (hint₂ : ∀ᶠ h in 𝓝[>] (0 : ℝ), Integrable (fun x ↦ A x * maskedKernel E P V₂ h x) μ) :
    Tendsto (fun h : ℝ ↦ ((∫ x, A x * maskedKernel E P V₂ h x ∂μ) -
        ∫ x, A x * maskedKernel E P V₁ h x ∂μ) / h ^ ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 (-∫ x, A x * Q x * Real.exp (-P x) ∂μ)) := by
  have hDCT := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
    (fun x ↦ |A x| * B x * Real.exp (-(c * P x)))
    (F := fun h x ↦ A x * (maskedKernel E P V₂ h x - maskedKernel E P V₁ h x) / h ^ ρ)
    (f := fun x ↦ -(A x * Q x * Real.exp (-P x))) ?_ ?_ hG ?_
  · rw [integral_neg] at hDCT
    refine hDCT.congr' ?_
    filter_upwards [hint₁, hint₂] with h h1 h2
    rw [integral_div, ← integral_sub h2 h1]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    ring
  · filter_upwards with h
    exact ((hA.mul ((measurable_maskedKernel hE hP hV₂ h).sub
      (measurable_maskedKernel hE hP hV₁ h))).div_const _).aestronglyMeasurable
  · filter_upwards [hlow₁, hlow₂, hbound, self_mem_nhdsWithin] with h hl₁ hl₂ hb hh
    have hh0 : (0 : ℝ) < h := hh
    have hp : (0 : ℝ) < h ^ ρ := pow_pos hh0 ρ
    refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hp, abs_mul]
    by_cases hx : x ∈ E h
    · rw [maskedKernel_of_mem hx, maskedKernel_of_mem hx]
      have hexp := abs_exp_neg_sub_exp_neg_le (P x + V₂ h x) (P x + V₁ h x)
      have hmax : max (Real.exp (-(P x + V₂ h x))) (Real.exp (-(P x + V₁ h x))) ≤
          Real.exp (-(c * P x)) := by
        rw [max_le_iff]
        exact ⟨Real.exp_le_exp.mpr (neg_le_neg (hl₂ x hx)),
          Real.exp_le_exp.mpr (neg_le_neg (hl₁ x hx))⟩
      have hsub : |P x + V₂ h x - (P x + V₁ h x)| = |V₂ h x - V₁ h x| := by
        congr 1
        ring
      rw [hsub] at hexp
      have hB : 0 ≤ B x := le_trans (by positivity) (hb x hx)
      calc |A x| * |Real.exp (-(P x + V₂ h x)) - Real.exp (-(P x + V₁ h x))| / h ^ ρ
          ≤ |A x| * (|V₂ h x - V₁ h x| * Real.exp (-(c * P x))) / h ^ ρ := by
            apply div_le_div_of_nonneg_right _ hp.le
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact hexp.trans (mul_le_mul_of_nonneg_left hmax (abs_nonneg _))
        _ = |A x| * (|V₂ h x - V₁ h x| / h ^ ρ) * Real.exp (-(c * P x)) := by ring
        _ ≤ |A x| * B x * Real.exp (-(c * P x)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_left (hb x hx) (abs_nonneg _)
    · rw [maskedKernel_of_notMem hx, maskedKernel_of_notMem hx, sub_zero, abs_zero, mul_zero,
        zero_div]
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (hB0 x)) (Real.exp_pos _).le
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    have hpt := tendsto_pointwise_difference_div_pow A P (V₁ := V₁) (V₂ := V₂) (ρ := ρ) (Q := Q)
      x (hV₁lim x) (hV₂lim x) (hdiff x)
    refine hpt.congr' ?_
    filter_upwards [hEmem x] with h hx
    rw [maskedKernel_of_mem hx, maskedKernel_of_mem hx]

/-- Integrability of a masked family from the lower bound. -/
theorem integrable_mul_maskedKernel {E : ℝ → Set X} {P : X → ℝ} {V : ℝ → X → ℝ}
    {A : X → ℝ} {c : ℝ} {h : ℝ}
    (hE : ∀ h, MeasurableSet (E h)) (hP : Measurable P) (hV : ∀ h, Measurable (V h))
    (hA : Measurable A) (hlow : ∀ x ∈ E h, c * P x ≤ P x + V h x)
    (hG : Integrable (fun x ↦ |A x| * Real.exp (-(c * P x))) μ) :
    Integrable (fun x ↦ A x * maskedKernel E P V h x) μ := by
  refine hG.mono' (hA.mul (measurable_maskedKernel hE hP hV h)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (maskedKernel_nonneg E P V h x)]
  exact mul_le_mul_of_nonneg_left (maskedKernel_le hlow x) (abs_nonneg _)

/-- **The localized one-grade limit under a common mask**:
`(M₂(A) − M₁(A))/h^ρ → −Cov_P(A, Q)` for the masked normalized moments. -/
theorem tendsto_masked_normalized_difference_div_pow {E : ℝ → Set X} {P : X → ℝ}
    {V₁ V₂ : ℝ → X → ℝ} {A Q B : X → ℝ} {c : ℝ} {ρ : ℕ}
    (hE : ∀ h, MeasurableSet (E h)) (hEmem : ∀ x, ∀ᶠ h in 𝓝[>] (0 : ℝ), x ∈ E h)
    (hP : Measurable P) (hV₁ : ∀ h, Measurable (V₁ h)) (hV₂ : ∀ h, Measurable (V₂ h))
    (hA : Measurable A)
    (hV₁lim : ∀ x, Tendsto (fun h : ℝ ↦ V₁ h x) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hV₂lim : ∀ x, Tendsto (fun h : ℝ ↦ V₂ h x) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hdiff : ∀ x, Tendsto (fun h : ℝ ↦ (V₂ h x - V₁ h x) / h ^ ρ) (𝓝[>] (0 : ℝ)) (𝓝 (Q x)))
    (hlow₁ : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ x ∈ E h, c * P x ≤ P x + V₁ h x)
    (hlow₂ : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ x ∈ E h, c * P x ≤ P x + V₂ h x)
    (hB0 : ∀ x, 0 ≤ B x)
    (hbound : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ x ∈ E h, |V₂ h x - V₁ h x| / h ^ ρ ≤ B x)
    (hGA : Integrable (fun x ↦ |A x| * Real.exp (-(c * P x))) μ)
    (hGAB : Integrable (fun x ↦ |A x| * B x * Real.exp (-(c * P x))) μ)
    (hG1 : Integrable (fun x ↦ Real.exp (-(c * P x))) μ)
    (hGB : Integrable (fun x ↦ B x * Real.exp (-(c * P x))) μ)
    (hZpos : 0 < ∫ x, Real.exp (-P x) ∂μ) :
    Tendsto (fun h : ℝ ↦
        ((∫ x, A x * maskedKernel E P V₂ h x ∂μ) / (∫ x, maskedKernel E P V₂ h x ∂μ) -
          (∫ x, A x * maskedKernel E P V₁ h x ∂μ) / ∫ x, maskedKernel E P V₁ h x ∂μ) / h ^ ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 (-covarianceUnder μ P A Q)) := by
  have hone : Measurable fun _ : X ↦ (1 : ℝ) := measurable_const
  have hG1' : Integrable (fun x ↦ |(fun _ : X ↦ (1 : ℝ)) x| * Real.exp (-(c * P x))) μ := by
    simpa using hG1
  have hGB' : Integrable (fun x ↦ |(fun _ : X ↦ (1 : ℝ)) x| * B x * Real.exp (-(c * P x))) μ := by
    simpa using hGB
  have hintA₁ : ∀ᶠ h in 𝓝[>] (0 : ℝ), Integrable (fun x ↦ A x * maskedKernel E P V₁ h x) μ := by
    filter_upwards [hlow₁] with h hl
    exact integrable_mul_maskedKernel hE hP hV₁ hA hl hGA
  have hintA₂ : ∀ᶠ h in 𝓝[>] (0 : ℝ), Integrable (fun x ↦ A x * maskedKernel E P V₂ h x) μ := by
    filter_upwards [hlow₂] with h hl
    exact integrable_mul_maskedKernel hE hP hV₂ hA hl hGA
  have hint1₁ : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      Integrable (fun x ↦ (fun _ : X ↦ (1 : ℝ)) x * maskedKernel E P V₁ h x) μ := by
    filter_upwards [hlow₁] with h hl
    exact integrable_mul_maskedKernel hE hP hV₁ hone hl hG1'
  have hint1₂ : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      Integrable (fun x ↦ (fun _ : X ↦ (1 : ℝ)) x * maskedKernel E P V₂ h x) μ := by
    filter_upwards [hlow₂] with h hl
    exact integrable_mul_maskedKernel hE hP hV₂ hone hl hG1'
  have hΔN := tendsto_integral_maskedKernel_difference_div_pow hE hEmem hP hV₁ hV₂ hA hV₁lim
    hV₂lim hdiff hlow₁ hlow₂ hB0 hbound hGAB hintA₁ hintA₂
  have hΔZ := tendsto_integral_maskedKernel_difference_div_pow hE hEmem hP hV₁ hV₂ hone hV₁lim
    hV₂lim hdiff hlow₁ hlow₂ hB0 hbound hGB' hint1₁ hint1₂
  have hN₁ := tendsto_integral_maskedKernel hE hEmem hP hV₁ hA hV₁lim hlow₁ hGA
  have hZ₁ := tendsto_integral_maskedKernel hE hEmem hP hV₁ hone hV₁lim hlow₁ hG1'
  have hZ₂ := tendsto_integral_maskedKernel hE hEmem hP hV₂ hone hV₂lim hlow₂ hG1'
  simp only [one_mul] at hΔZ hZ₁ hZ₂
  have key := tendsto_normalizedKernel_difference_div_pow (μ := μ) (maskedKernel E P V₁)
    (maskedKernel E P V₂) (fun x ↦ Real.exp (-P x)) A Q ρ hΔN hΔZ hN₁ hZ₁ hZ₂ hZpos
  rw [neg_cov_eq] at key
  exact key

end Laplace.Multi
