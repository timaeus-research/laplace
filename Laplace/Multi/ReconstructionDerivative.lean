/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DensityDerivative
import Laplace.Multi.ObservableCurvature
import Laplace.Multi.EmpiricalProjection

/-!
# The `L¹` derivative of the reconstruction density in response coordinates

The reconstruction `Π(M) = P_{θ(M)}` has density `q_M = p_{θ(M)}` with respect to `ν`, where
`θ = chartVInv ∘ toV` is the inverse chart. For a response `M` in the relative interior of the
moment body and a direction `z` in the direction subspace `𝕍`,

`∫ |q_{M+z} − q_M − q_M ℓ_{M,z}| dν = o(‖z‖)`, `ℓ_{M,z} = ⟨Dθ(M) z, M⟩ − ⟨Dθ(M) z, S⟩`,

with `Dθ(M) = (chartDerivEquiv θ(M))⁻¹` the inverse covariance operator on `𝕍`. This is the
Fréchet derivative of the reconstruction density in `L¹(ν)`, read through the chart: the
natural-chart remainder is `O(‖η‖²)`, the chart increment `η(z) = θ(M+z) − θ(M)` is Lipschitz in
`z` and `η(z) − Dθ(M) z = o(‖z‖)` by strict differentiability of the inverse chart.
-/

open MeasureTheory Filter Topology Set Asymptotics
open scoped ENNReal

namespace Laplace.Multi

section Recon

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The family measure is the density law of `famDens`. -/
theorem familyMeasure_eq_withDensity_famDens (θ : J → ℝ) :
    familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ =
      ν.withDensity fun x ↦ ENNReal.ofReal (famDens S ν θ x) := by
  unfold familyMeasure famDens famZ famWeight priorZ affLoss dirLoss
  congr 1
  funext x
  simp

omit [Nonempty X] [Nonempty J] in
include hS in
/-- The response of `famDens` is the mean map. -/
theorem famMean_eq_meanMap (θ : J → ℝ) :
    famMean S ν θ = meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ := by
  funext i
  have h := congrFun (mean_familyMeasure_one_zero hS ν θ) i
  simp only at h
  rw [← h, integral_familyMeasure_one_zero hS ν θ (S i)]
  unfold famMean famDens famZ famWeight priorExp priorZ affLoss dirLoss
  simp only [zero_add, one_mul, mul_one]
  rw [← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  ring

include hS in
/-- The reconstruction of an interior response is the density law of `famDens` at its natural
coordinates. -/
theorem responseProjection_eq_withDensity_famDens {M : J → ℝ}
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    responseProjection hS ν M = ν.withDensity fun x ↦ ENNReal.ofReal (famDens S ν
      (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
        hS M) x) := by
  rw [responseProjection_eq_familyMeasure_responseTheta hS ν hrel,
    familyMeasure_eq_withDensity_famDens]

include hS in
/-- The natural coordinates of a translated interior response. -/
theorem responseTheta_add {M : J → ℝ} (hM : M ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S)
    (z : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
        (M + z) =
      chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
        (toV ν (fun _ ↦ (1 : ℝ)) S M + z) := by
  unfold responseTheta
  congr 1
  have hM' := sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS hM
  have hMz : M + z - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 ∈
      dirSpan ν (fun _ ↦ (1 : ℝ)) S := by
    rw [add_sub_right_comm]
    exact Submodule.add_mem _ hM' z.2
  refine Subtype.ext ?_
  rw [toV_apply hMz, Submodule.coe_add, toV_apply hM']
  abel

include hS in
/-- **The `L¹` derivative of the reconstruction density in response coordinates**: for an
interior response `M` and directions `z` in the direction subspace,
`∫ |q_{M+z} − q_M − q_M (⟨Dθ z, M⟩ − ⟨Dθ z, S⟩)| dν = o(‖z‖)`. -/
theorem isLittleO_reconstruction_density_remainder {M : J → ℝ}
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    (fun z : dirSpan ν (fun _ ↦ (1 : ℝ)) S ↦ ∫ x, |famDens S ν (responseTheta measurable_const
        (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS (M + z)) x -
      famDens S ν (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS M) x -
      famDens S ν (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS M) x *
        (dotJ (((chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos ν) hS (responseTheta measurable_const (integrable_const 1)
            (fun _ ↦ one_pos) (one_integral_pos ν) hS M)).symm : dirSpan ν (fun _ ↦ (1 : ℝ)) S
              →L[ℝ] dirSpan ν (fun _ ↦ (1 : ℝ)) S) z : J → ℝ) M -
        dirLoss S (((chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos ν) hS (responseTheta measurable_const (integrable_const 1)
            (fun _ ↦ one_pos) (one_integral_pos ν) hS M)).symm : dirSpan ν (fun _ ↦ (1 : ℝ)) S
              →L[ℝ] dirSpan ν (fun _ ↦ (1 : ℝ)) S) z : J → ℝ) x)| ∂ν)
      =o[𝓝 0] fun z ↦ ‖z‖ := by
  -- abbreviations
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀, θ₀ = responseTheta measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS M := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : dirSpan ν (fun _ ↦ (1 : ℝ)) S →L[ℝ] dirSpan ν (fun _ ↦ (1 : ℝ)) S,
    L = ((chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS θ₀).symm : _ →L[ℝ] _) := ⟨_, rfl⟩
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : dirSpan ν (fun _ ↦ (1 : ℝ)) S → dirSpan ν (fun _ ↦ (1 : ℝ)) S,
    Θ = fun z ↦ chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (toV ν (fun _ ↦ (1 : ℝ)) S M + z) := ⟨_, rfl⟩
  have hM : M ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := intrinsicInterior_subset hrel
  have hΘz : ∀ z : dirSpan ν (fun _ ↦ (1 : ℝ)) S, responseTheta measurable_const
      (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS (M + z) = Θ z := fun z ↦ by
    rw [hΘ, responseTheta_add hS ν hM z]
  have hΘ0 : Θ 0 = θ₀ := by
    rw [hΘ, hθ₀]
    simp only [add_zero]
    rfl
  have hmean : famMean S ν θ₀ = M := by
    rw [famMean_eq_meanMap hS ν, hθ₀]
    exact meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS hrel
  -- strict differentiability of the chart increment
  have hstrict : HasStrictFDerivAt Θ L 0 := by
    have h1 := hasStrictFDerivAt_chartVInv measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS θ₀
    rw [hθ₀, chartV_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS hrel, ← hθ₀] at h1
    have h2 : HasStrictFDerivAt (fun z : dirSpan ν (fun _ ↦ (1 : ℝ)) S ↦
        toV ν (fun _ ↦ (1 : ℝ)) S M + z) (ContinuousLinearMap.id ℝ _) 0 :=
      (hasStrictFDerivAt_id (0 : dirSpan ν (fun _ ↦ (1 : ℝ)) S)).const_add _
    rw [show toV ν (fun _ ↦ (1 : ℝ)) S M = toV ν (fun _ ↦ (1 : ℝ)) S M + 0 from
      (add_zero _).symm] at h1
    have h3 := h1.comp (0 : dirSpan ν (fun _ ↦ (1 : ℝ)) S) h2
    rw [hΘ, hL]
    simpa [Function.comp_def] using h3
  -- Lipschitz bound on the increment
  obtain ⟨K, s, hs, hK⟩ := hstrict.exists_lipschitzOnWith
  have hlip : (fun z ↦ ‖((Θ z : J → ℝ) - (θ₀ : J → ℝ))‖) =O[𝓝 0] fun z ↦ ‖z‖ := by
    refine IsBigO.of_bound K ?_
    filter_upwards [hs] with z hz
    have h0s : (0 : dirSpan ν (fun _ ↦ (1 : ℝ)) S) ∈ s := mem_of_mem_nhds hs
    have hd := hK.dist_le_mul _ hz 0 h0s
    rw [hΘ0, dist_eq_norm, dist_eq_norm, sub_zero] at hd
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), ← Submodule.coe_sub, Submodule.norm_coe]
    exact hd
  -- little-o of the linearisation error
  have hlin : (fun z ↦ (Θ z : J → ℝ) - (θ₀ : J → ℝ) - (L z : J → ℝ)) =o[𝓝 0] fun z ↦ z := by
    have h := hasFDerivAt_iff_isLittleO_nhds_zero.1 hstrict.hasFDerivAt
    simp only [zero_add, hΘ0] at h
    have h' := h.norm_left
    refine (IsLittleO.of_norm_left ?_)
    refine h'.congr_left fun z ↦ ?_
    rw [← Submodule.coe_sub, ← Submodule.coe_sub, Submodule.norm_coe]
  -- constants
  choose Mj hMj using fun j ↦ (hS j).2
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, |S j x| ≤ B :=
    ⟨∑ j, |Mj j|, Finset.sum_nonneg fun j _ ↦ abs_nonneg _, fun j x ↦
      (hMj j x).trans ((le_abs_self _).trans (Finset.single_le_sum
        (f := fun j ↦ |Mj j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ j)))⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = (Fintype.card J : ℝ) * B := ⟨_, rfl⟩
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  -- the two remainders
  have hη : ∀ z, (Θ z : J → ℝ) = θ₀ + ((Θ z : J → ℝ) - (θ₀ : J → ℝ)) := fun z ↦ by abel
  have hf1 : (fun z ↦ ∫ x, |famDens S ν (Θ z) x - famDens S ν θ₀ x - famDens S ν θ₀ x *
      (dotJ ((Θ z : J → ℝ) - (θ₀ : J → ℝ)) M -
        dirLoss S ((Θ z : J → ℝ) - (θ₀ : J → ℝ)) x)| ∂ν) =O[𝓝 0] fun z ↦ ‖z‖ ^ 2 := by
    have hbig := isBigO_famDens_remainder hS ν hB0 hB (θ₀ : J → ℝ)
    have hcont : Tendsto (fun z ↦ (Θ z : J → ℝ) - (θ₀ : J → ℝ)) (𝓝 0) (𝓝 0) := by
      have := hstrict.continuousAt.tendsto
      rw [hΘ0] at this
      have h := (continuous_subtype_val.tendsto _).comp this
      simpa [Function.comp_def] using h.sub_const (θ₀ : J → ℝ)
    have h1 := hbig.comp_tendsto hcont
    rw [← hmean]
    refine (IsBigO.congr_left h1 fun z ↦ ?_).trans (hlip.pow 2)
    simp only [Function.comp_def]
    rw [← hη]
  have hf2 : (fun z ↦ 2 * K₀ * ‖(Θ z : J → ℝ) - (θ₀ : J → ℝ) - (L z : J → ℝ)‖) =o[𝓝 0]
      fun z ↦ ‖z‖ := by
    have := (hlin.norm_left.const_mul_left (2 * K₀)).norm_right
    exact this
  -- assemble
  refine IsBigO.trans_isLittleO (g := fun z ↦ (∫ x, |famDens S ν (Θ z) x - famDens S ν θ₀ x -
      famDens S ν θ₀ x * (dotJ ((Θ z : J → ℝ) - (θ₀ : J → ℝ)) M -
        dirLoss S ((Θ z : J → ℝ) - (θ₀ : J → ℝ)) x)| ∂ν) +
      2 * K₀ * ‖(Θ z : J → ℝ) - (θ₀ : J → ℝ) - (L z : J → ℝ)‖) ?_
    ((hf1.trans_isLittleO ?_).add hf2)
  · refine IsBigO.of_bound 1 (Eventually.of_forall fun z ↦ ?_)
    rw [one_mul, hΘz, ← hθ₀, ← hL]
    have hI0 := integrable_famDens hS ν θ₀
    have hI1 := integrable_famDens hS ν (Θ z)
    set η : J → ℝ := (Θ z : J → ℝ) - (θ₀ : J → ℝ) with hηdef
    set u : J → ℝ := (L z : J → ℝ) with hudef
    have hlin_int : ∀ v : J → ℝ, Integrable (fun x ↦ famDens S ν θ₀ x *
        (dotJ v M - dirLoss S v x)) ν := fun v ↦ by
      have hm : Measurable (fun x ↦ dotJ v M - dirLoss S v x) :=
        measurable_const.sub (bdd_dirLoss hS v).1
      have h := hI0.bdd_mul (c := K₀ * ‖v‖ + K₀ * ‖v‖) hm.aestronglyMeasurable
        (Eventually.of_forall fun x ↦ by
          rw [Real.norm_eq_abs]
          refine (abs_sub _ _).trans (add_le_add ?_ ?_)
          · rw [← hmean, hK₀]; exact abs_dotJ_famMean_le hS ν hB0 hB θ₀ v
          · rw [hK₀]; exact abs_dirLoss_le_card_mul hB0 hB v x)
      exact h.congr (Eventually.of_forall fun x ↦ mul_comm _ _)
    have hpt : ∀ x, |famDens S ν (Θ z) x - famDens S ν θ₀ x - famDens S ν θ₀ x *
        (dotJ u M - dirLoss S u x)| ≤
        |famDens S ν (Θ z) x - famDens S ν θ₀ x - famDens S ν θ₀ x *
          (dotJ η M - dirLoss S η x)| +
        famDens S ν θ₀ x * (2 * K₀ * ‖η - u‖) := fun x ↦ by
      have e : famDens S ν (Θ z) x - famDens S ν θ₀ x - famDens S ν θ₀ x *
          (dotJ u M - dirLoss S u x) =
          (famDens S ν (Θ z) x - famDens S ν θ₀ x - famDens S ν θ₀ x *
            (dotJ η M - dirLoss S η x)) +
          famDens S ν θ₀ x * (dotJ (η - u) M - dirLoss S (η - u) x) := by
        have hds2 : dotJ (η - u) M = dotJ η M - dotJ u M := by
          simp only [dotJ, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
        have hds : dirLoss S (η - u) x = dirLoss S η x - dirLoss S u x := by
          simp only [dirLoss, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
        rw [hds2, hds]
        ring
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul, abs_of_nonneg (famDens_nonneg hS ν θ₀ x)]
      refine mul_le_mul_of_nonneg_left ?_ (famDens_nonneg hS ν θ₀ x)
      refine (abs_sub _ _).trans ?_
      have h1 : |dotJ (η - u) M| ≤ K₀ * ‖η - u‖ := by
        rw [← hmean, hK₀]; exact abs_dotJ_famMean_le hS ν hB0 hB θ₀ (η - u)
      have h2 : |dirLoss S (η - u) x| ≤ K₀ * ‖η - u‖ := by
        rw [hK₀]; exact abs_dirLoss_le_card_mul hB0 hB (η - u) x
      linarith
    have hg1 : Integrable (fun x ↦ |famDens S ν (Θ z) x - famDens S ν θ₀ x - famDens S ν θ₀ x *
        (dotJ η M - dirLoss S η x)|) ν := by
      have h := (hI1.sub hI0).sub (hlin_int η)
      exact h.abs
    have hg2 : Integrable (fun x ↦ famDens S ν θ₀ x * (2 * K₀ * ‖η - u‖)) ν := hI0.mul_const _
    have hK0' : 0 ≤ 2 * K₀ * ‖η - u‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x ↦ abs_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (integral_nonneg fun x ↦ abs_nonneg _) hK0')]
    calc ∫ x, |famDens S ν (Θ z) x - famDens S ν θ₀ x - famDens S ν θ₀ x *
          (dotJ u M - dirLoss S u x)| ∂ν
        ≤ ∫ x, (|famDens S ν (Θ z) x - famDens S ν θ₀ x - famDens S ν θ₀ x *
            (dotJ η M - dirLoss S η x)| + famDens S ν θ₀ x * (2 * K₀ * ‖η - u‖)) ∂ν :=
          integral_mono_of_nonneg (Eventually.of_forall fun x ↦ abs_nonneg _) (hg1.add hg2)
            (Eventually.of_forall hpt)
      _ = (∫ x, |famDens S ν (Θ z) x - famDens S ν θ₀ x - famDens S ν θ₀ x *
            (dotJ η M - dirLoss S η x)| ∂ν) + 2 * K₀ * ‖η - u‖ := by
          rw [integral_add hg1 hg2, integral_mul_const, integral_famDens hS ν, one_mul]
  · exact (isLittleO_norm_pow_id one_lt_two).norm_right

end Recon

end Laplace.Multi
