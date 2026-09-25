/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.IntegratedSusceptibility

/-!
# Square-root integral convergence from an `L¹` mass bound, and the `√t` law

If nonnegative functions `F_n` converge almost everywhere to `f` on a finite measure space and
their integrals are uniformly bounded, then `∫ √F_n → ∫ √f` (`tendsto_integral_sqrt_of_mass_bound`).
No domination is needed: truncate at a level `M`, use dominated convergence for the truncated
part, and bound the excess by `√y − min(√y, M) ≤ y/M`, so the excess integrals are at most `C/M`.

Applied to a mixture line this turns the pointwise convergence `t Var_{t,s}(Δ) → κ(s)` into the
**`√t` law for the thermodynamic length**,

  `ℓ(t)/√t → ∫₀¹ √κ(s) ds`   (`thermoLength_div_sqrt_tendsto`),

because the integrated-susceptibility identity supplies the uniform mass bound
`∫₀¹ t Var_{t,s}(Δ) ds = ⟨Δ⟩_{t,0} − ⟨Δ⟩_{t,1} ≤ 2M` for free (Astra, round 22). In the regular
case `κ(s) = ⟨∇Δ, H_s⁻¹ ∇Δ⟩` at the moving minimiser, so two data distributions with different
truths are at response distance `√t · Length_G(γ) + o(√t)` in the limiting Hessian metric `G`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- `√y − min(√y, M) ≤ y/M` for `y ≥ 0`, `M > 0`. -/
theorem sqrt_sub_min_le {y M : ℝ} (hy : 0 ≤ y) (hM : 0 < M) :
    Real.sqrt y - min (Real.sqrt y) M ≤ y / M := by
  rcases le_total (Real.sqrt y) M with h | h
  · rw [min_eq_left h, sub_self]
    positivity
  · rw [min_eq_right h, le_div_iff₀ hM]
    nlinarith [sq_nonneg (Real.sqrt y - M / 2), Real.sq_sqrt hy]

/-- `√y ≤ 1 + y` for `y ≥ 0`. -/
theorem sqrt_le_one_add {y : ℝ} (hy : 0 ≤ y) : Real.sqrt y ≤ 1 + y :=
  Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- `√F` is integrable when `F ≥ 0` is integrable on a finite measure space. -/
theorem integrable_sqrt_of_integrable [IsFiniteMeasure μ] {F : α → ℝ} (hF : Integrable F μ)
    (hnn : ∀ x, 0 ≤ F x) : Integrable (fun x ↦ Real.sqrt (F x)) μ := by
  refine ((integrable_const (1 : ℝ)).add hF).mono'
    (Real.continuous_sqrt.comp_aestronglyMeasurable hF.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact sqrt_le_one_add (hnn x)

/-- **Square-root convergence from a mass bound.** If `0 ≤ F_n → f` almost everywhere on a finite
measure space, `∫ F_n ≤ C` eventually and `∫ f ≤ C`, then `∫ √F_n → ∫ √f`. -/
theorem tendsto_integral_sqrt_of_mass_bound [IsFiniteMeasure μ] {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι → α → ℝ} {f : α → ℝ} {C : ℝ}
    (hFint : ∀ᶠ n in l, Integrable (F n) μ) (hFnn : ∀ᶠ n in l, ∀ x, 0 ≤ F n x)
    (hFC : ∀ᶠ n in l, ∫ x, F n x ∂μ ≤ C) (hfint : Integrable f μ) (hfnn : ∀ x, 0 ≤ f x)
    (hfC : ∫ x, f x ∂μ ≤ C) (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ F n x) l (𝓝 (f x))) :
    Tendsto (fun n ↦ ∫ x, Real.sqrt (F n x) ∂μ) l (𝓝 (∫ x, Real.sqrt (f x) ∂μ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set M : ℝ := 4 * (|C| + 1) / ε with hM
  have hMpos : 0 < M := by positivity
  have hCM : 2 * (C / M) < ε / 2 := by
    have h1 : C / M ≤ |C| / M := div_le_div_of_nonneg_right (le_abs_self C) hMpos.le
    have h2 : |C| / M < ε / 4 := by
      rw [hM, div_div_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hε, abs_nonneg C]
    linarith
  -- the truncated integrands converge by dominated convergence
  have hTf : Tendsto (fun n ↦ ∫ x, min (Real.sqrt (F n x)) M ∂μ) l
      (𝓝 (∫ x, min (Real.sqrt (f x)) M ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ M) ?_ ?_
      (integrable_const M) ?_
    · filter_upwards [hFint] with n hn
      exact (Real.continuous_sqrt.min continuous_const).comp_aestronglyMeasurable
        hn.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun n ↦ Filter.Eventually.of_forall fun x ↦ ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.sqrt_nonneg _) hMpos.le)]
      exact min_le_right _ _
    · filter_upwards [hlim] with x hx
      exact ((Real.continuous_sqrt.min continuous_const).tendsto _).comp hx
  have hev := Metric.tendsto_nhds.mp hTf (ε / 2) (by positivity)
  filter_upwards [hev, hFint, hFnn, hFC] with n hn hint hnn hC
  -- the excess of the limit
  have hfs := integrable_sqrt_of_integrable hfint hfnn
  have hfT : Integrable (fun x ↦ min (Real.sqrt (f x)) M) μ :=
    hfs.mono' ((Real.continuous_sqrt.min continuous_const).comp_aestronglyMeasurable
      hfint.aestronglyMeasurable) (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.sqrt_nonneg _) hMpos.le)]
        exact min_le_left _ _)
  have hf1 : ∫ x, min (Real.sqrt (f x)) M ∂μ ≤ ∫ x, Real.sqrt (f x) ∂μ :=
    integral_mono hfT hfs fun x ↦ min_le_left _ _
  have hf2 : (∫ x, Real.sqrt (f x) ∂μ) - ∫ x, min (Real.sqrt (f x)) M ∂μ ≤ C / M := by
    rw [← integral_sub hfs hfT]
    calc ∫ x, (Real.sqrt (f x) - min (Real.sqrt (f x)) M) ∂μ ≤ ∫ x, f x / M ∂μ :=
          integral_mono (hfs.sub hfT) (hfint.div_const M) fun x ↦ sqrt_sub_min_le (hfnn x) hMpos
      _ = (∫ x, f x ∂μ) / M := integral_div _ _
      _ ≤ C / M := div_le_div_of_nonneg_right hfC hMpos.le
  -- the excess of the approximants
  have hns := integrable_sqrt_of_integrable hint hnn
  have hnT : Integrable (fun x ↦ min (Real.sqrt (F n x)) M) μ :=
    hns.mono' ((Real.continuous_sqrt.min continuous_const).comp_aestronglyMeasurable
      hint.aestronglyMeasurable) (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.sqrt_nonneg _) hMpos.le)]
        exact min_le_left _ _)
  have hn1 : ∫ x, min (Real.sqrt (F n x)) M ∂μ ≤ ∫ x, Real.sqrt (F n x) ∂μ :=
    integral_mono hnT hns fun x ↦ min_le_left _ _
  have hn2 : (∫ x, Real.sqrt (F n x) ∂μ) - ∫ x, min (Real.sqrt (F n x)) M ∂μ ≤ C / M := by
    rw [← integral_sub hns hnT]
    calc ∫ x, (Real.sqrt (F n x) - min (Real.sqrt (F n x)) M) ∂μ ≤ ∫ x, F n x / M ∂μ :=
          integral_mono (hns.sub hnT) (hint.div_const M) fun x ↦ sqrt_sub_min_le (hnn x) hMpos
      _ = (∫ x, F n x ∂μ) / M := integral_div _ _
      _ ≤ C / M := div_le_div_of_nonneg_right hC hMpos.le
  rw [Real.dist_eq] at hn ⊢
  rw [abs_lt] at hn ⊢
  constructor <;> linarith

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [Nonempty X]

/-- **The `√t` law**: if `t Var_{t,s}(Δ) → κ(s)` for almost every `s ∈ (0,1]` along a mixture line
with bounded contrast, then `ℓ(t)/√t → ∫₀¹ √κ`. The uniform mass bound is the integrated
susceptibility. -/
theorem thermoLength_div_sqrt_tendsto {π L₀ Δ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
    (hL₀ : ∀ x, |L₀ x| ≤ M₀) (hΔm : Measurable Δ) {MΔ : ℝ} (hΔ : ∀ x, |Δ x| ≤ MΔ) {κ : ℝ → ℝ}
    (hκi : Integrable κ (volume.restrict (Ioc 0 1))) (hκnn : ∀ s, 0 ≤ κ s)
    (hκC : ∫ s in Ioc (0 : ℝ) 1, κ s ≤ 2 * MΔ)
    (hlim : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      Tendsto (fun t ↦ t * mixCov μ π L₀ Δ Δ Δ t s) atTop (𝓝 (κ s))) :
    Tendsto (fun t ↦ thermoLength μ π (pathLoss L₀ Δ) (fun _ ↦ Δ) t / Real.sqrt t) atTop
      (𝓝 (∫ s in Ioc (0 : ℝ) 1, Real.sqrt (κ s))) := by
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hT : ∀ t : ℝ, TiltData μ (baseWeight π L₀ t) Δ MΔ := fun t ↦
    tiltData_baseWeight_of_bounded μ hπm hπi hπ hπpos hL₀m hL₀ hΔm hΔ t
  have hΔb : Bdd Δ := ⟨hΔm, MΔ, hΔ⟩
  have key := tendsto_integral_sqrt_of_mass_bound (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (l := atTop) (F := fun t s ↦ t * mixCov μ π L₀ Δ Δ Δ t s) (f := κ) (C := 2 * MΔ) ?_ ?_ ?_
    hκi hκnn hκC hlim
  · refine key.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have e : ∀ s, Real.sqrt (fisherSpeed μ π (pathLoss L₀ Δ) (fun _ ↦ Δ) t s) =
        Real.sqrt (t * mixCov μ π L₀ Δ Δ Δ t s) * Real.sqrt t := fun s ↦ by
      rw [fisherSpeed_mixture, show t ^ 2 * mixCov μ π L₀ Δ Δ Δ t s =
        (t * mixCov μ π L₀ Δ Δ Δ t s) * t by ring,
        Real.sqrt_mul (mul_nonneg ht.le ((hT t).mixCov_self_nonneg hΔb s))]
    rw [eq_div_iff hst.ne']
    unfold thermoLength
    rw [intervalIntegral.integral_of_le zero_le_one]
    simp_rw [e]
    rw [MeasureTheory.integral_mul_const]
  · filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    exact (continuous_const.mul ((hT t).continuous_mixCov ht hΔb)).integrableOn_Ioc
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht s
    exact mul_nonneg ht ((hT t).mixCov_self_nonneg hΔb s)
  · refine Filter.Eventually.of_forall fun t ↦ ?_
    rw [← intervalIntegral.integral_of_le zero_le_one, (hT t).integrated_susceptibility]
    have hb : ∀ s, |mixExp μ π L₀ Δ Δ t s| ≤ MΔ := fun s ↦ by
      rw [mixExp_eq_tiltExp]
      exact (hT t).abs_tiltExp_le_of_bound hΔm hΔ t s
    have h0 := hb 0
    have h1 := hb 1
    rw [abs_le] at h0 h1
    linarith

end Laplace.Multi
