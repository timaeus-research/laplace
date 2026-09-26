/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.NormalGeometry

/-!
# Fréchet derivatives of the family in natural coordinates

For the affine family `P_θ ∝ e^{−⟨θ,S⟩}ν` with bounded features, the expectation
`θ ↦ E_{P_θ} φ` of a bounded observable, the covariance `θ ↦ Cov_{P_θ}(f, g)` and the pointwise
density `θ ↦ p_θ(x)` are Fréchet differentiable in `θ ∈ ℝ^J`:

* `D_θ E_{P_θ} φ [v] = −Cov_{P_θ}(φ, ⟨v,S⟩)` (`hasFDerivAt_integral_family`);
* `D_θ Cov_{P_θ}(f,g) [v] = −T_{P_θ}(f, g, ⟨v,S⟩)` (`hasFDerivAt_lawCov_family`);
* `D_θ p_θ(x) [v] = p_θ(x)(⟨v, m(θ)⟩ − ⟨v, S(x)⟩)` (`hasFDerivAt_famDens`).

Two general helpers lift Fréchet derivatives through a finite-dimensional submodule: the derivative
of a submodule-valued map takes values in the submodule (`mem_of_hasFDerivAt_val`) and a map is
differentiable once its coercion is (`hasFDerivAt_of_subtypeL_comp`).
-/

open MeasureTheory Filter Topology Set Asymptotics
open scoped ENNReal

namespace Laplace.Multi

section Subtype

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A map into a submodule is differentiable once its coercion is. -/
theorem hasFDerivAt_of_subtypeL_comp {W : Submodule ℝ F} {f : E → W} {f' : E →L[ℝ] W} {x : E}
    (h : HasFDerivAt (fun v ↦ (f v : F)) (W.subtypeL.comp f') x) : HasFDerivAt f f' x := by
  rw [hasFDerivAt_iff_isLittleO] at h ⊢
  rw [← isLittleO_norm_left] at h ⊢
  refine h.congr_left fun p ↦ ?_
  rw [Submodule.coe_norm, Submodule.coe_sub, Submodule.coe_sub]
  rfl

/-- The derivative of a map into a finite-dimensional submodule takes values in the submodule. -/
theorem mem_of_hasFDerivAt_val {W : Submodule ℝ F} [FiniteDimensional ℝ W] {f : E → W}
    {f' : E →L[ℝ] F} {x : E} (h : HasFDerivAt (fun v ↦ (f v : F)) f' x) (η : E) : f' η ∈ W := by
  have hl : HasDerivAt (fun t : ℝ ↦ (f (x + t • η) : F)) (f' η) 0 := by
    rw [show x = x + (0 : ℝ) • η by simp] at h
    have := h.comp_hasDerivAt (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).smul_const η).const_add x)
    simpa [Function.comp_def] using this
  rw [hasDerivAt_iff_tendsto_slope] at hl
  refine (Submodule.closed_of_finiteDimensional W).mem_of_tendsto hl
    (Eventually.of_forall fun t ↦ ?_)
  rw [slope_def_module]
  exact W.smul_mem _ (W.sub_mem (f _).2 (f _).2)

end Subtype

section Natural

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]

/-- The covariance functional `v ↦ −Cov_ρ(φ, ⟨v,S⟩)`. -/
noncomputable def covCLM (S : J → X → ℝ) (ρ : Measure X) (φ : X → ℝ) : (J → ℝ) →L[ℝ] ℝ :=
  -dotCLM (fun j ↦ lawCov ρ φ (S j))

/-- The third-cumulant functional `v ↦ −T_ρ(f, g, ⟨v,S⟩)`. -/
noncomputable def cumCLM (S : J → X → ℝ) (ρ : Measure X) (f g : X → ℝ) : (J → ℝ) →L[ℝ] ℝ :=
  covCLM S ρ (fun x ↦ f x * g x) - (∫ x, f x ∂ρ) • covCLM S ρ g - (∫ x, g x ∂ρ) • covCLM S ρ f

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

include hS

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem covCLM_apply (ρ : Measure X) [IsProbabilityMeasure ρ] {φ : X → ℝ} (hφ : Bdd φ)
    (v : J → ℝ) : covCLM S ρ φ v = -lawCov ρ φ (dirLoss S v) := by
  simp only [covCLM, neg_apply, dotCLM_apply, dotJ]
  rw [lawCov_comm, lawCov_dirLoss_left hS ρ v φ hφ]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by rw [lawCov_comm]

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem cumCLM_apply (ρ : Measure X) [IsProbabilityMeasure ρ] {f g : X → ℝ} (hf : Bdd f)
    (hg : Bdd g) (v : J → ℝ) : cumCLM S ρ f g v = -thirdCentral ρ f g (dirLoss S v) := by
  simp only [cumCLM, sub_apply, smul_apply, smul_eq_mul, covCLM_apply hS ρ (hf.mul hg),
    covCLM_apply hS ρ hg, covCLM_apply hS ρ hf]
  rw [thirdCentral_eq ρ hf hg (bdd_dirLoss hS v)]
  unfold lawCov
  ring

omit [Nonempty J] in
theorem isProbabilityMeasure_family (θ : J → ℝ) : IsProbabilityMeasure (Pfam θ) :=
  isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS (t := 1) θ

omit [Nonempty J] in
/-- **The expectation of a bounded observable is Fréchet differentiable in the natural
coordinates**, with derivative `v ↦ −Cov_{P_θ}(φ, ⟨v,S⟩)`. -/
theorem hasFDerivAt_integral_family {φ : X → ℝ} (hφ : Bdd φ) (θ₀ : J → ℝ) :
    HasFDerivAt (fun θ ↦ ∫ x, φ x ∂(Pfam θ)) (covCLM S (Pfam θ₀) φ) θ₀ := by
  have hP := isProbabilityMeasure_family hS ν θ₀
  obtain ⟨hφm, Mφ, hφb⟩ := hφ
  have h := hasFDerivAt_obsMap (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ)) measurable_const
    (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const (M₀ := 0)
    (fun _ ↦ by simp) hS hφm hφb one_pos θ₀
  have e : (fun θ ↦ ∫ x, φ x ∂(Pfam θ)) =
      fun θ ↦ priorExp ν (fun _ ↦ (1 : ℝ)) (affLoss (fun _ ↦ (0 : ℝ)) S θ) φ 1 :=
    funext fun θ ↦ integral_familyMeasure_one_zero hS ν θ φ
  rw [e]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  rw [obsMapDeriv_apply (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ)) measurable_const
    (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const (M₀ := 0)
    (fun _ ↦ by simp) hS hφm hφb one_pos, priorCov_eq_lawCov_familyMeasure hS ν,
    covCLM_apply hS _ ⟨hφm, Mφ, hφb⟩]
  ring

omit [Nonempty J] in
/-- **The covariance is Fréchet differentiable in the natural coordinates**, with derivative
`v ↦ −T_{P_θ}(f, g, ⟨v,S⟩)`. -/
theorem hasFDerivAt_lawCov_family {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) (θ₀ : J → ℝ) :
    HasFDerivAt (fun θ ↦ lawCov (Pfam θ) f g) (cumCLM S (Pfam θ₀) f g) θ₀ := by
  have hfg := hasFDerivAt_integral_family hS ν (hf.mul hg) θ₀
  have hf' := hasFDerivAt_integral_family hS ν hf θ₀
  have hg' := hasFDerivAt_integral_family hS ν hg θ₀
  have h : HasFDerivAt (fun θ ↦ (∫ x, f x * g x ∂(Pfam θ)) -
      (∫ x, f x ∂(Pfam θ)) * ∫ x, g x ∂(Pfam θ))
      (covCLM S (Pfam θ₀) (fun x ↦ f x * g x) - ((∫ x, f x ∂(Pfam θ₀)) • covCLM S (Pfam θ₀) g +
        (∫ x, g x ∂(Pfam θ₀)) • covCLM S (Pfam θ₀) f)) θ₀ := hfg.sub (hf'.mul hg')
  unfold lawCov
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  simp only [cumCLM, sub_apply, add_apply, smul_apply, smul_eq_mul]
  ring

omit [Nonempty X] in
/-- **The density is pointwise Fréchet differentiable in the natural coordinates**:
`D_θ p_θ(x)[v] = p_θ(x)(⟨v, m(θ)⟩ − ⟨v, S(x)⟩)`. -/
theorem hasFDerivAt_famDens (θ₀ : J → ℝ) (x : X) :
    HasFDerivAt (fun θ ↦ famDens S ν θ x)
      (famDens S ν θ₀ x • (dotCLM (famMean S ν θ₀) - dirCLM S x)) θ₀ := by
  choose Mj hMj using fun j ↦ (hS j).2
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, |S j x| ≤ B :=
    ⟨∑ j, |Mj j|, Finset.sum_nonneg fun j _ ↦ abs_nonneg _, fun j x ↦
      (hMj j x).trans ((le_abs_self _).trans (Finset.single_le_sum
        (f := fun j ↦ |Mj j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ j)))⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hK : 0 ≤ (Fintype.card J : ℝ) * B := by positivity
  have hδ : (0 : ℝ) < 1 / (4 * ((Fintype.card J : ℝ) * B + 1)) := by
    apply div_pos one_pos
    linarith
  have hbig : (fun η : J → ℝ ↦ famDens S ν (θ₀ + η) x - famDens S ν θ₀ x -
      (famDens S ν θ₀ x • (dotCLM (famMean S ν θ₀) - dirCLM S x)) η) =O[𝓝 0]
      fun η ↦ ‖η‖ ^ 2 := by
    refine IsBigO.of_bound (10 * ((Fintype.card J : ℝ) * B) ^ 2 * famDens S ν θ₀ x) ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : J → ℝ) hδ] with η hη
    rw [Metric.mem_closedBall, dist_zero_right] at hη
    have h1 : (Fintype.card J : ℝ) * B * ‖η‖ ≤ 1 / 4 := by
      calc (Fintype.card J : ℝ) * B * ‖η‖ ≤ (Fintype.card J : ℝ) * B *
            (1 / (4 * ((Fintype.card J : ℝ) * B + 1))) := mul_le_mul_of_nonneg_left hη hK
        _ ≤ 1 / 4 := by
            rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    have h := abs_famDens_remainder_le hS ν hB0 hB θ₀ η h1 x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖η‖),
      smul_apply, sub_apply, dotCLM_apply, dirCLM_apply, smul_eq_mul]
    calc |famDens S ν (θ₀ + η) x - famDens S ν θ₀ x -
          famDens S ν θ₀ x * (dotJ η (famMean S ν θ₀) - dirLoss S η x)|
        ≤ 10 * ((Fintype.card J : ℝ) * B * ‖η‖) ^ 2 * famDens S ν θ₀ x := h
      _ = 10 * ((Fintype.card J : ℝ) * B) ^ 2 * famDens S ν θ₀ x * ‖η‖ ^ 2 := by ring
  exact hbig.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)

end Natural

section Operator

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]

/-- The third-cumulant vector `(T_θ(η, v))_j = T_{P_θ}(S_j, ⟨v,S⟩, ⟨η,S⟩)`. -/
noncomputable def thirdVec (S : J → X → ℝ) (ν : Measure X) (θ η v : J → ℝ) : J → ℝ :=
  fun j ↦ thirdCentral (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) (S j)
    (dirLoss S v) (dirLoss S η)

/-- The coordinate derivative of the restricted covariance operator as a continuous linear map. -/
noncomputable def thirdCoordCLM (S : J → X → ℝ) (ν : Measure X)
    (θ v : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : dirSpan ν (fun _ ↦ (1 : ℝ)) S →L[ℝ] (J → ℝ) :=
  ContinuousLinearMap.pi fun j ↦
    -((cumCLM S (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) (S j)
      (dirLoss S v)).comp (dirSpan ν (fun _ ↦ (1 : ℝ)) S).subtypeL)

variable {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

include hS

omit [Nonempty J] in
theorem thirdCoordCLM_apply (θ v η : 𝕍) :
    thirdCoordCLM S ν θ v η = thirdVec S ν θ η v := by
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  funext j
  simp only [thirdCoordCLM, ContinuousLinearMap.pi_apply, neg_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, cumCLM_apply hS _ (hS j) (bdd_dirLoss hS _), neg_neg, thirdVec]

/-- **The restricted covariance operator applied to a fixed direction is Fréchet differentiable
in the natural coordinates**, with derivative the third-cumulant vector. -/
theorem hasFDerivAt_chartDeriv_coe (θ₀ v : 𝕍) :
    HasFDerivAt (fun θ : 𝕍 ↦ (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS θ v : J → ℝ)) (thirdCoordCLM S ν θ₀ v) θ₀ := by
  refine hasFDerivAt_pi'' fun j ↦ ?_
  rw [thirdCoordCLM, ContinuousLinearMap.proj_pi]
  have h := ((hasFDerivAt_lawCov_family hS ν (hS j) (bdd_dirLoss hS v) (θ₀ : J → ℝ)).comp θ₀
    (𝕍).subtypeL.hasFDerivAt).neg
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun θ ↦ ?_)
  simp only [Function.comp_def]
  exact chartDeriv_coe_apply hS ν θ v j

theorem thirdVec_mem_dirSpan (θ₀ v η : 𝕍) : thirdVec S ν θ₀ η v ∈ 𝕍 := by
  rw [← thirdCoordCLM_apply hS ν]
  exact mem_of_hasFDerivAt_val (hasFDerivAt_chartDeriv_coe hS ν θ₀ v) η

/-- The third-cumulant vector as a map `𝕍 → 𝕍` (in the differentiation direction). -/
noncomputable def thirdDir (θ v : 𝕍) : 𝕍 →L[ℝ] 𝕍 :=
  (thirdCoordCLM S ν θ v).codRestrict (𝕍) fun η ↦ by
    rw [thirdCoordCLM_apply hS ν]
    exact thirdVec_mem_dirSpan hS ν θ v η

theorem thirdDir_coe_apply (θ v η : 𝕍) : (thirdDir hS ν θ v η : J → ℝ) = thirdVec S ν θ η v := by
  rw [thirdDir, ContinuousLinearMap.coe_codRestrict_apply, thirdCoordCLM_apply hS ν]

theorem hasFDerivAt_chartDeriv_apply (θ₀ v : 𝕍) :
    HasFDerivAt (fun θ : 𝕍 ↦ chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS θ v) (thirdDir hS ν θ₀ v) θ₀ := by
  refine hasFDerivAt_of_subtypeL_comp ?_
  rw [thirdDir, ContinuousLinearMap.subtypeL_comp_codRestrict]
  exact hasFDerivAt_chartDeriv_coe hS ν θ₀ v

/-- **The third-cumulant operator** `T_θ : 𝕍 → (𝕍 → 𝕍)`,
`T_θ(η) v = ⟨T_{P_θ}(S_j, ⟨v,S⟩, ⟨η,S⟩)⟩_j`: the Fréchet derivative of the restricted covariance
operator. -/
noncomputable def thirdOp (θ : 𝕍) : 𝕍 →L[ℝ] (𝕍 →L[ℝ] 𝕍) :=
  ∑ i, (ContinuousLinearMap.smulRightL ℝ (𝕍) (𝕍)
    (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ (𝕍)).coord i))).comp
      (thirdDir hS ν θ (Module.finBasis ℝ (𝕍) i))

/-- **The restricted covariance operator is Fréchet differentiable in the natural
coordinates**, with derivative the third-cumulant operator. -/
theorem hasFDerivAt_chartDeriv (θ₀ : 𝕍) :
    HasFDerivAt (fun θ : 𝕍 ↦ chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS θ) (thirdOp hS ν θ₀) θ₀ := by
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin (Module.finrank ℝ (𝕍))) ℝ (𝕍),
    b = Module.finBasis ℝ _ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℝ (𝕍)) → StrongDual ℝ (𝕍),
    c = fun i ↦ LinearMap.toContinuousLinearMap (b.coord i) := ⟨_, rfl⟩
  have hdecomp : ∀ L : 𝕍 →L[ℝ] 𝕍,
      L = ∑ i, ContinuousLinearMap.smulRightL ℝ _ _ (c i) (L (b i)) := fun L ↦ by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    rw [sum_apply]
    simp only [ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply, hc,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    simp only [map_smul]
  have hbi : ∀ i, HasFDerivAt (fun θ : 𝕍 ↦ chartDeriv measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS θ (b i)) (thirdDir hS ν θ₀ (b i)) θ₀ := fun i ↦
    hasFDerivAt_chartDeriv_apply hS ν θ₀ (b i)
  have hsum := HasFDerivAt.sum (u := Finset.univ) fun i _ ↦
    (ContinuousLinearMap.smulRightL ℝ (𝕍) (𝕍) (c i)).hasFDerivAt.comp θ₀ (hbi i)
  have e : thirdOp hS ν θ₀ = ∑ i, (ContinuousLinearMap.smulRightL ℝ (𝕍) (𝕍) (c i)).comp
      (thirdDir hS ν θ₀ (b i)) := by
    subst hc hb
    rfl
  rw [e]
  refine hsum.congr_of_eventuallyEq (Eventually.of_forall fun θ ↦ ?_)
  simp only [Finset.sum_apply, Function.comp_def]
  exact hdecomp _

/-- The third-cumulant operator evaluated: `(T_θ(η) v)_j = T_{P_θ}(S_j, ⟨v,S⟩, ⟨η,S⟩)`. -/
theorem thirdOp_coe_apply (θ η v : 𝕍) : (thirdOp hS ν θ η v : J → ℝ) = thirdVec S ν θ η v := by
  have h1 := (hasFDerivAt_chartDeriv hS ν θ).clm_apply (hasFDerivAt_const v θ)
  have h2 := hasFDerivAt_chartDeriv_apply hS ν θ v
  have h := h1.unique h2
  rw [← thirdDir_coe_apply hS ν θ v η, ← h]
  simp

end Operator

section Response

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]

/-- The pairing `y ↦ ⟨·, y⟩` as a continuous linear map into functionals. -/
noncomputable def dotCLMlin : (J → ℝ) →L[ℝ] ((J → ℝ) →L[ℝ] ℝ) :=
  ∑ j, ContinuousLinearMap.smulRightL ℝ (J → ℝ) ((J → ℝ) →L[ℝ] ℝ) (ContinuousLinearMap.proj j)
    (ContinuousLinearMap.proj j)

omit [Nonempty J] in
theorem dotCLMlin_apply (y : J → ℝ) : dotCLMlin y = dotCLM y := by
  simp only [dotCLMlin, dotCLM, sum_apply, ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]

omit [Nonempty J] in
theorem dotCLM_add (a b : J → ℝ) : dotCLM (a + b) = dotCLM a + dotCLM b := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [dotCLM_apply, add_apply, (isLinearMap_dotJ v).map_add]

variable {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {M : J → ℝ}

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative as a linear equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The inverse chart derivative at `M`, as a continuous linear map. -/
local notation "RinvL" => (ContinuousLinearEquiv.symm (CDE (θr M)) : 𝕍 →L[ℝ] 𝕍)

include hS

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- **The natural coordinate is strictly differentiable in response coordinates**, with derivative
the inverse chart derivative `R = (Dm(θ(M))|_𝕍)⁻¹`. -/
theorem hasStrictFDerivAt_responseTheta_add :
    HasStrictFDerivAt (fun z : 𝕍 ↦ θr (M + z)) RinvL 0 := by
  have hM : M ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := intrinsicInterior_subset hrel
  have h1 := hasStrictFDerivAt_chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (θr M)
  rw [chartV_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS hrel] at h1
  have h2 : HasStrictFDerivAt (fun z : 𝕍 ↦ toV ν (fun _ ↦ (1 : ℝ)) S M + z)
      (ContinuousLinearMap.id ℝ _) 0 := (hasStrictFDerivAt_id (0 : 𝕍)).const_add _
  rw [show toV ν (fun _ ↦ (1 : ℝ)) S M = toV ν (fun _ ↦ (1 : ℝ)) S M + 0 from
    (add_zero _).symm] at h1
  have h3 := h1.comp (0 : 𝕍) h2
  rw [ContinuousLinearMap.comp_id] at h3
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)
  exact (responseTheta_add hS ν hM z).symm

theorem hasFDerivAt_responseTheta_add_coe :
    HasFDerivAt (fun z : 𝕍 ↦ (θr (M + z) : J → ℝ)) ((𝕍).subtypeL.comp RinvL) 0 :=
  (𝕍).subtypeL.hasFDerivAt.comp 0 (hasStrictFDerivAt_responseTheta_add hS ν hrel).hasFDerivAt

/-- **The reconstruction density is pointwise differentiable in response coordinates.** -/
theorem hasFDerivAt_famDens_response (x : X) :
    HasFDerivAt (fun z : 𝕍 ↦ famDens S ν (θr (M + z)) x)
      ((famDens S ν (θr M) x • (dotCLM M - dirCLM S x)).comp ((𝕍).subtypeL.comp RinvL)) 0 := by
  have hΘ := hasFDerivAt_responseTheta_add_coe hS ν hrel
  have hq := hasFDerivAt_famDens hS ν (θr (M + (0 : 𝕍)) : J → ℝ) x
  have h0 : ((θr (M + (0 : 𝕍)) : J → ℝ)) = (θr M : J → ℝ) := by simp
  have hmean : famMean S ν (θr M) = M := by
    rw [famMean_eq_meanMap hS ν]
    exact meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS hrel
  have h := hq.comp (0 : 𝕍) hΘ
  rw [h0, hmean] at h
  exact h

omit hrel in
theorem responseScore_apply (v : 𝕍) (x : X) :
    responseScore hS ν M v x = dotJ (ContinuousLinearEquiv.symm (CDE (θr M)) v : J → ℝ) M -
      dirLoss S (ContinuousLinearEquiv.symm (CDE (θr M)) v : J → ℝ) x := rfl

omit hrel in
/-- The first derivative of the reconstruction density is `q_M ℓ_{M,u}`. -/
theorem famDens_response_deriv_apply (x : X) (u : 𝕍) :
    ((famDens S ν (θr M) x • (dotCLM M - dirCLM S x)).comp ((𝕍).subtypeL.comp RinvL)) u =
      famDens S ν (θr M) x * responseScore hS ν M u x := by
  simp only [ContinuousLinearMap.comp_apply, smul_apply, sub_apply, dotCLM_apply, dirCLM_apply,
    Submodule.subtypeL_apply, smul_eq_mul, responseScore, ContinuousLinearEquiv.coe_coe]

/-- **The restricted covariance operator is differentiable in response coordinates.** -/
theorem hasFDerivAt_chartDeriv_response :
    HasFDerivAt (fun z : 𝕍 ↦ chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (θr (M + z))) ((thirdOp hS ν (θr M)).comp RinvL) 0 := by
  have hΘ := (hasStrictFDerivAt_responseTheta_add hS ν hrel).hasFDerivAt
  have h0 : θr (M + (0 : 𝕍)) = θr M := by simp
  have h := (hasFDerivAt_chartDeriv hS ν (θr (M + (0 : 𝕍)))).comp (0 : 𝕍) hΘ
  rw [h0] at h
  exact h

/-- **The inverse chart derivative is differentiable in response coordinates**, with derivative
`u ↦ −R T_{θ(M)}(R u) R`. -/
theorem hasFDerivAt_inverse_response :
    HasFDerivAt (fun z : 𝕍 ↦ (ContinuousLinearEquiv.symm (CDE (θr (M + z))) : 𝕍 →L[ℝ] 𝕍))
      ((-ContinuousLinearMap.mulLeftRight ℝ _ RinvL RinvL).comp
        ((thirdOp hS ν (θr M)).comp RinvL)) 0 := by
  have hG := hasFDerivAt_chartDeriv_response hS ν hrel
  have hu : IsUnit (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (θr M)) := by
    rw [← coe_chartDerivEquiv]
    exact ((ContinuousLinearEquiv.unitsEquiv ℝ (𝕍)).symm (CDE (θr M))).isUnit
  obtain ⟨u, hu⟩ := hu
  have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have h0 : θr (M + (0 : 𝕍)) = θr M := by simp
  rw [hu, ← h0] at h
  have h2 := h.comp (0 : 𝕍) hG
  have hinv : ((u⁻¹ : (𝕍 →L[ℝ] 𝕍)ˣ) : 𝕍 →L[ℝ] 𝕍) = RinvL := by
    rw [coe_chartDerivEquiv_symm, ← hu, Ring.inverse_unit]
  rw [hinv] at h2
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)
  simp only [Function.comp_def]
  exact coe_chartDerivEquiv_symm measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (θr (M + z))

theorem hasFDerivAt_inverse_response_apply (w : 𝕍) :
    HasFDerivAt (fun z : 𝕍 ↦ ContinuousLinearEquiv.symm (CDE (θr (M + z))) w)
      (((-ContinuousLinearMap.mulLeftRight ℝ _ RinvL RinvL).comp
        ((thirdOp hS ν (θr M)).comp RinvL)).flip w) 0 := by
  have h := (hasFDerivAt_inverse_response hS ν hrel).clm_apply (hasFDerivAt_const w (0 : 𝕍))
  simpa using h

omit hrel in
theorem neg_mulLeftRight_apply (G : 𝕍 →L[ℝ] 𝕍) (w : 𝕍) :
    ((-ContinuousLinearMap.mulLeftRight ℝ _ RinvL RinvL) G) w =
      -(ContinuousLinearEquiv.symm (CDE (θr M)) (G (ContinuousLinearEquiv.symm (CDE (θr M)) w))) :=
  rfl

omit hrel in
theorem inverse_response_deriv_apply (w u : 𝕍) :
    (((-ContinuousLinearMap.mulLeftRight ℝ _ RinvL RinvL).comp
        ((thirdOp hS ν (θr M)).comp RinvL)).flip w) u =
      -(ContinuousLinearEquiv.symm (CDE (θr M))
        (thirdOp hS ν (θr M) (ContinuousLinearEquiv.symm (CDE (θr M)) u)
          (ContinuousLinearEquiv.symm (CDE (θr M)) w))) := rfl

/-- The third-cumulant vector in response directions is the covariance vector of the product of
the response scores: `T_{θ(M)}(Ru, Rw) = Cov_Q(S, ℓ_{M,u} ℓ_{M,w})`. -/
theorem thirdVec_eq_respCov (u w : 𝕍) :
    thirdVec S ν (θr M) (ContinuousLinearEquiv.symm (CDE (θr M)) u)
        (ContinuousLinearEquiv.symm (CDE (θr M)) w) =
      respCov hS ν M (fun x ↦ responseScore hS ν M u x * responseScore hS ν M w x) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have hM : ∀ j, ∫ y, S j y ∂(Pfam (θr M)) = M j := fun j ↦
    congrFun (integral_stat_responseTheta hS ν hrel) j
  have hu' := integral_dirLoss_responseTheta hS ν hrel
    (ContinuousLinearEquiv.symm (CDE (θr M)) u : J → ℝ)
  have hw' := integral_dirLoss_responseTheta hS ν hrel
    (ContinuousLinearEquiv.symm (CDE (θr M)) w : J → ℝ)
  funext j
  have h1 : Integrable (fun x ↦ S j x * (responseScore hS ν M u x * responseScore hS ν M w x))
      (Pfam (θr M)) := integrable_of_bdd_prob _ ((hS j).mul
        ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M w)))
  have h2 : Integrable (fun x ↦ M j * (responseScore hS ν M u x * responseScore hS ν M w x))
      (Pfam (θr M)) := (integrable_of_bdd_prob _
        ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M w))).const_mul _
  simp only [thirdVec, respCov, lawCov, thirdCentral]
  rw [hM, hu', hw', ← integral_const_mul, ← integral_sub h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [responseScore]
  ring

/-- **The response score is differentiable in response coordinates**:
`D_M ℓ_{M,w}(x)[u] = −E_Q[ℓ_{M,u} ℓ_{M,w}] − (B_M(ℓ_{M,u} ℓ_{M,w}))(x)`. -/
theorem hasFDerivAt_responseScore_response (w : 𝕍) (x : X) :
    ∃ L : 𝕍 →L[ℝ] ℝ, HasFDerivAt (fun z : 𝕍 ↦ responseScore hS ν (M + z) w x) L 0 ∧
      ∀ u, L u = -(∫ y, responseScore hS ν M u y * responseScore hS ν M w y ∂(Pfam (θr M))) -
        regProj hS ν M ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M w)) x := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have hR := hasFDerivAt_inverse_response_apply hS ν hrel w
  have hRc := (𝕍).subtypeL.hasFDerivAt.comp 0 hR
  have hc : HasFDerivAt (fun z : 𝕍 ↦ dotCLM (M + (z : J → ℝ))) (dotCLMlin.comp (𝕍).subtypeL)
      0 := by
    have := (dotCLMlin.comp (𝕍).subtypeL).hasFDerivAt (x := (0 : 𝕍)) |>.const_add (dotCLM M)
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, dotCLMlin_apply,
      dotCLM_add]
  have h1 := hc.clm_apply hRc
  have h2 := (dirCLM S x).hasFDerivAt.comp 0 hRc
  refine ⟨_, (h1.sub h2).congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_), fun u ↦ ?_⟩
  · simp only [responseScore, dotCLM_apply, dirCLM_apply, Function.comp_def,
      Submodule.subtypeL_apply, Pi.sub_apply]
  · have hsym : dotJ (ContinuousLinearEquiv.symm (CDE (θr M)) w : J → ℝ) u =
        dotJ (ContinuousLinearEquiv.symm (CDE (θr M)) u : J → ℝ) w := by
      have a := integral_responseScore_mul hS ν hrel w u
      have b := integral_responseScore_mul hS ν hrel u w
      have e : ∫ y, responseScore hS ν M w y * responseScore hS ν M u y ∂(Pfam (θr M)) =
          ∫ y, responseScore hS ν M u y * responseScore hS ν M w y ∂(Pfam (θr M)) :=
        integral_congr_ae (Eventually.of_forall fun y ↦ mul_comm _ _)
      linarith
    have hT : thirdOp hS ν (θr M) (ContinuousLinearEquiv.symm (CDE (θr M)) u)
        (ContinuousLinearEquiv.symm (CDE (θr M)) w) =
        ⟨respCov hS ν M (fun x ↦ responseScore hS ν M u x * responseScore hS ν M w x),
          respCov_mem_dirSpan hS ν
            ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M w))⟩ :=
      Subtype.ext (by rw [thirdOp_coe_apply, thirdVec_eq_respCov hS ν hrel])
    simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      ContinuousLinearMap.flip_apply, Function.comp_def, dotCLM_apply, dirCLM_apply,
      dotCLMlin_apply, Submodule.coe_zero, add_zero, neg_mulLeftRight_apply,
      ContinuousLinearEquiv.coe_coe, hT, Submodule.coe_neg, dotJ_neg_left, dirLoss_neg,
      integral_responseScore_mul hS ν hrel u w]
    unfold regProj
    rw [responseScore_apply, hsym]
    ring

/-- **The polarised response Hessian of the reconstruction density**: the derivative field
`z ↦ q_{M+z} ℓ_{M+z,w}` (the first derivative of `z ↦ q_{M+z}` in direction `w`) is differentiable
at `z = 0`, with derivative `u ↦ q_M · N_M(ℓ_{M,u} ℓ_{M,w})(x)`: the second derivative of the
reconstruction density in response coordinates is the normal projection of the product of the two
response scores. -/
theorem hasFDerivAt_famDens_responseScore (w : 𝕍) (x : X) :
    ∃ L : 𝕍 →L[ℝ] ℝ,
      HasFDerivAt (fun z : 𝕍 ↦ famDens S ν (θr (M + z)) x * responseScore hS ν (M + z) w x) L 0 ∧
      ∀ u, L u = famDens S ν (θr M) x *
        normalProj hS ν M ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M w)) x := by
  obtain ⟨L₂, hL₂, hL₂v⟩ := hasFDerivAt_responseScore_response hS ν hrel w x
  have hq := hasFDerivAt_famDens_response hS ν hrel x
  refine ⟨_, hq.mul hL₂, fun u ↦ ?_⟩
  simp only [add_apply, smul_apply, smul_eq_mul, famDens_response_deriv_apply, hL₂v,
    Submodule.coe_zero, add_zero]
  unfold normalProj
  ring

end Response

end Laplace.Multi
