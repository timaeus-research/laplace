/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseDualConnections
import Laplace.Multi.ResponseFisherCurvature
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# The first variation of the Fisher energy and the Levi-Civita equation

For a path `θ` in the natural coordinates the **Fisher energy** is `E(θ) = ½ ∫₀¹ G_θ(θ', θ') dt`. A
two-parameter `C²` family `Θ(s,t)` with velocity `V = ∂_tΘ`, acceleration `A = ∂_t²Θ`, variation
field `U = ∂_sΘ` and mixed derivative `W = ∂_s∂_tΘ = ∂_t∂_sΘ` (`FisherVariation`, an explicit
regularity package) has energy derivative

  `E'(0) = G(U,V)|₀¹ − ∫₀¹ G_θ(U, θ'' + ½ C_θ(θ',θ')) dt`   (`fisherEnergy_variation`),

obtained by differentiating under the integral (`hasDerivAt_fisherEnergy`), using the metric
derivative `∂_u G(v,w) = G(C(u,v),w)` of `ResponseFisherJets` for the `s`-derivative of the
integrand (`hasDerivAt_energyIntegrand`), and integrating by parts through the `t`-derivative of
`G(U,V)` (`hasDerivAt_energyPairing`). Hence the **Levi-Civita equation** `θ'' + ½ C_θ(θ',θ') = 0`
(`alphaChristoffel` at `α = 0`) is exactly the Euler–Lagrange equation of the Fisher
energy: along a
Levi-Civita geodesic the energy is stationary under every variation with fixed endpoints
(`hasDerivAt_fisherEnergy_of_lcGeodesic`). No division by the speed and no regular-curve hypothesis
are needed, which is why the energy, not the length, is the right first variational target.
-/

open MeasureTheory Filter Topology Set intervalIntegral

namespace Laplace.Multi

section Energy

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative. -/
local notation "CD" => chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

omit [Nonempty J] in
theorem fisherInner_add_right (θ u v w : 𝕍) : G θ u (v + w) = G θ u v + G θ u w := by
  rw [fisherInner_comm hS ν, fisherInner_add_left hS ν, fisherInner_comm hS ν θ v,
    fisherInner_comm hS ν θ w]

omit [Nonempty J] in
theorem fisherInner_smul_right (θ : 𝕍) (r : ℝ) (u v : 𝕍) : G θ u (r • v) = r * G θ u v := by
  rw [fisherInner_comm hS ν, fisherInner_smul_left, fisherInner_comm hS ν]

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem fisherInner_zero_left (θ v : 𝕍) : G θ 0 v = 0 := by
  have := fisherInner_smul_left ν θ (0 : ℝ) 0 v
  rwa [zero_smul, zero_mul] at this

/-- The Fisher form is jointly continuous in the base point and the two directions. -/
theorem continuous_fisherInner : Continuous fun p : 𝕍 × 𝕍 × 𝕍 ↦ G p.1 p.2.1 p.2.2 := by
  have e : (fun p : 𝕍 × 𝕍 × 𝕍 ↦ G p.1 p.2.1 p.2.2) =
      fun p ↦ -(dotCLMlin (CD p.1 p.2.2 : J → ℝ)) (p.2.1 : J → ℝ) := by
    funext p
    rw [fisherInner_eq_neg_dotJ hS ν, dotCLMlin_apply, dotCLM_apply]
  rw [e]
  refine Continuous.neg ?_
  refine Continuous.clm_apply ?_ (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  refine dotCLMlin.continuous.comp (continuous_subtype_val.comp ?_)
  exact ((contDiff_chartDeriv hS ν).continuous.comp continuous_fst).clm_apply
    (continuous_snd.comp continuous_snd)

/-- The mixture Christoffel operator is jointly continuous. -/
theorem continuous_mChristoffel :
    Continuous fun p : 𝕍 × 𝕍 × 𝕍 ↦ mChristoffel hS ν p.1 p.2.1 p.2.2 := by
  have e : (fun p : 𝕍 × 𝕍 × 𝕍 ↦ mChristoffel hS ν p.1 p.2.1 p.2.2) =
      fun p ↦ ((CDE p.1).symm : 𝕍 →L[ℝ] 𝕍) (thirdOp hS ν p.1 p.2.1 p.2.2) := rfl
  rw [e]
  refine Continuous.clm_apply ((contDiff_chartDerivEquiv_symm hS ν).continuous.comp continuous_fst)
    ?_
  exact (((contDiff_thirdOp hS ν).continuous.comp continuous_fst).clm_apply
    (continuous_fst.comp continuous_snd)).clm_apply (continuous_snd.comp continuous_snd)

variable (S) in
/-- **A two-parameter variation** `Θ(s,t)` of a path in the natural coordinates, with velocity
`V = ∂_tΘ`, acceleration `A = ∂_t²Θ`, variation field `U = ∂_sΘ` and mixed derivative
`W = ∂_s∂_tΘ = ∂_t∂_sΘ`: an explicit `C²` regularity package. -/
structure FisherVariation where
  /-- The family of paths. -/
  Θ : ℝ → ℝ → 𝕍
  /-- The velocity `∂_tΘ`. -/
  V : ℝ → ℝ → 𝕍
  /-- The acceleration `∂_t²Θ`. -/
  A : ℝ → ℝ → 𝕍
  /-- The variation field `∂_sΘ`. -/
  U : ℝ → ℝ → 𝕍
  /-- The mixed derivative `∂_s∂_tΘ = ∂_t∂_sΘ`. -/
  W : ℝ → ℝ → 𝕍
  hasDerivAt_t : ∀ s t, HasDerivAt (Θ s) (V s t) t
  hasDerivAt_tt : ∀ s t, HasDerivAt (V s) (A s t) t
  hasDerivAt_s : ∀ s t, HasDerivAt (fun s ↦ Θ s t) (U s t) s
  hasDerivAt_st : ∀ s t, HasDerivAt (fun s ↦ V s t) (W s t) s
  hasDerivAt_ts : ∀ s t, HasDerivAt (U s) (W s t) t
  continuous_Θ : Continuous fun p : ℝ × ℝ ↦ Θ p.1 p.2
  continuous_V : Continuous fun p : ℝ × ℝ ↦ V p.1 p.2
  continuous_A : Continuous fun p : ℝ × ℝ ↦ A p.1 p.2
  continuous_U : Continuous fun p : ℝ × ℝ ↦ U p.1 p.2
  continuous_W : Continuous fun p : ℝ × ℝ ↦ W p.1 p.2

/-- **The Fisher energy** of the path `Θ(s, ·)`: `E(s) = ½ ∫₀¹ G(V,V) dt`. -/
noncomputable def fisherEnergy (Λ : FisherVariation S ν) (s : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, G (Λ.Θ s t) (Λ.V s t) (Λ.V s t)

/-- The `s`-derivative of the energy integrand: `∂_s G(V,V) = 2G(W,V) + G(C(U,V),V)`. -/
theorem hasDerivAt_energyIntegrand (Λ : FisherVariation S ν) (s t : ℝ) :
    HasDerivAt (fun s ↦ G (Λ.Θ s t) (Λ.V s t) (Λ.V s t))
      (2 * G (Λ.Θ s t) (Λ.W s t) (Λ.V s t) +
        G (Λ.Θ s t) (mChristoffel hS ν (Λ.Θ s t) (Λ.U s t) (Λ.V s t)) (Λ.V s t)) s := by
  have e : (fun s ↦ G (Λ.Θ s t) (Λ.V s t) (Λ.V s t)) = fun s ↦
      -((dotCLMlin.comp (𝕍).subtypeL) (Λ.V s t)) ((𝕍).subtypeL (CD (Λ.Θ s t) (Λ.V s t))) := by
    funext s
    rw [fisherInner_eq_neg_dotJ hS ν, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      Submodule.subtypeL_apply, dotCLMlin_apply, dotCLM_apply, dotJ_comm']
  rw [e]
  have hc : HasDerivAt (fun s ↦ (dotCLMlin.comp (𝕍).subtypeL) (Λ.V s t))
      ((dotCLMlin.comp (𝕍).subtypeL) (Λ.W s t)) s :=
    (dotCLMlin.comp (𝕍).subtypeL).hasFDerivAt.comp_hasDerivAt s (Λ.hasDerivAt_st s t)
  have h0 := (hasFDerivAt_chartDeriv hS ν (Λ.Θ s t)).comp_hasDerivAt s (Λ.hasDerivAt_s s t)
  have h1 : HasDerivAt (fun s ↦ CD (Λ.Θ s t)) (thirdOp hS ν (Λ.Θ s t) (Λ.U s t)) s := h0
  have hCD := h1.clm_apply (Λ.hasDerivAt_st s t)
  have hu : HasDerivAt (fun s ↦ (𝕍).subtypeL (CD (Λ.Θ s t) (Λ.V s t)))
      ((𝕍).subtypeL (thirdOp hS ν (Λ.Θ s t) (Λ.U s t) (Λ.V s t) + CD (Λ.Θ s t) (Λ.W s t))) s :=
    (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt s hCD
  refine (hc.clm_apply hu).neg.congr_deriv ?_
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, dotCLMlin_apply,
    dotCLM_apply, map_add]
  rw [fisherInner_eq_neg_dotJ hS ν, fisherInner_mChristoffel hS ν,
    dotJ_comm' (CD (Λ.Θ s t) (Λ.V s t) : J → ℝ),
    dotJ_comm' (thirdOp hS ν (Λ.Θ s t) (Λ.U s t) (Λ.V s t) : J → ℝ),
    ← dotJ_chartDeriv_symm hS ν (Λ.Θ s t) (Λ.W s t) (Λ.V s t)]
  ring

/-- The `t`-derivative of the pairing `G(U,V)` along the path:
`∂_t G(U,V) = G(W,V) + G(U,A) + G(C(U,V),V)`. -/
theorem hasDerivAt_energyPairing (Λ : FisherVariation S ν) (s t : ℝ) :
    HasDerivAt (fun t ↦ G (Λ.Θ s t) (Λ.U s t) (Λ.V s t))
      (G (Λ.Θ s t) (Λ.W s t) (Λ.V s t) + G (Λ.Θ s t) (Λ.U s t) (Λ.A s t) +
        G (Λ.Θ s t) (mChristoffel hS ν (Λ.Θ s t) (Λ.U s t) (Λ.V s t)) (Λ.V s t)) t := by
  have e : (fun t ↦ G (Λ.Θ s t) (Λ.U s t) (Λ.V s t)) = fun t ↦
      -((dotCLMlin.comp (𝕍).subtypeL) (Λ.U s t)) ((𝕍).subtypeL (CD (Λ.Θ s t) (Λ.V s t))) := by
    funext t
    rw [fisherInner_eq_neg_dotJ hS ν, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      Submodule.subtypeL_apply, dotCLMlin_apply, dotCLM_apply, dotJ_comm']
  rw [e]
  have hc : HasDerivAt (fun t ↦ (dotCLMlin.comp (𝕍).subtypeL) (Λ.U s t))
      ((dotCLMlin.comp (𝕍).subtypeL) (Λ.W s t)) t :=
    (dotCLMlin.comp (𝕍).subtypeL).hasFDerivAt.comp_hasDerivAt t (Λ.hasDerivAt_ts s t)
  have hCD := hasDerivAt_chartDeriv_path hS ν (Λ.hasDerivAt_t s t) (Λ.hasDerivAt_tt s t)
  have hu : HasDerivAt (fun t ↦ (𝕍).subtypeL (CD (Λ.Θ s t) (Λ.V s t)))
      ((𝕍).subtypeL (thirdOp hS ν (Λ.Θ s t) (Λ.V s t) (Λ.V s t) + CD (Λ.Θ s t) (Λ.A s t))) t :=
    (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt t hCD
  refine (hc.clm_apply hu).neg.congr_deriv ?_
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, dotCLMlin_apply,
    dotCLM_apply, map_add]
  rw [fisherInner_eq_neg_dotJ hS ν (Λ.Θ s t) (Λ.W s t),
    fisherInner_eq_neg_dotJ hS ν (Λ.Θ s t) (Λ.U s t), fisherInner_mChristoffel hS ν,
    dotJ_comm' (CD (Λ.Θ s t) (Λ.V s t) : J → ℝ), dotJ_comm' (CD (Λ.Θ s t) (Λ.A s t) : J → ℝ),
    dotJ_comm' (thirdOp hS ν (Λ.Θ s t) (Λ.V s t) (Λ.V s t) : J → ℝ),
    dotJ_thirdOp_symm₁₂ hS ν (Λ.Θ s t) (Λ.U s t) (Λ.V s t) (Λ.V s t)]
  ring

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem fisherInner_zero_right (θ u : 𝕍) : G θ u 0 = 0 := by
  have := fisherInner_smul_left ν θ (0 : ℝ) 0 u
  rw [zero_smul, zero_mul] at this
  unfold fisherInner at this ⊢
  have hprob : lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ : J → ℝ))
      (dirLoss S (u : J → ℝ)) (dirLoss S ((0 : 𝕍) : J → ℝ)) =
      lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ : J → ℝ))
      (dirLoss S ((0 : 𝕍) : J → ℝ)) (dirLoss S (u : J → ℝ)) := by
    simp [lawCov, mul_comm]
  rw [hprob]
  exact this

/-- The energy integrand is jointly continuous in `(s, t)`. -/
theorem continuous_energyIntegrand (Λ : FisherVariation S ν) :
    Continuous fun p : ℝ × ℝ ↦ G (Λ.Θ p.1 p.2) (Λ.V p.1 p.2) (Λ.V p.1 p.2) := by
  have hmap : Continuous fun p : ℝ × ℝ ↦ (Λ.Θ p.1 p.2, (Λ.V p.1 p.2, Λ.V p.1 p.2)) :=
    Λ.continuous_Θ.prodMk (Λ.continuous_V.prodMk Λ.continuous_V)
  have h := (continuous_fisherInner hS ν).comp hmap
  simpa only [Function.comp_def] using h

/-- The `s`-derivative of the energy integrand is jointly continuous. -/
theorem continuous_energyIntegrandDeriv (Λ : FisherVariation S ν) :
    Continuous fun p : ℝ × ℝ ↦ 2 * G (Λ.Θ p.1 p.2) (Λ.W p.1 p.2) (Λ.V p.1 p.2) +
      G (Λ.Θ p.1 p.2) (mChristoffel hS ν (Λ.Θ p.1 p.2) (Λ.U p.1 p.2) (Λ.V p.1 p.2))
        (Λ.V p.1 p.2) := by
  have hmap1 : Continuous fun p : ℝ × ℝ ↦ (Λ.Θ p.1 p.2, (Λ.W p.1 p.2, Λ.V p.1 p.2)) :=
    Λ.continuous_Θ.prodMk (Λ.continuous_W.prodMk Λ.continuous_V)
  have h1 : Continuous fun p : ℝ × ℝ ↦ G (Λ.Θ p.1 p.2) (Λ.W p.1 p.2) (Λ.V p.1 p.2) := by
    simpa only [Function.comp_def] using (continuous_fisherInner hS ν).comp hmap1
  have hmapC : Continuous fun p : ℝ × ℝ ↦ (Λ.Θ p.1 p.2, (Λ.U p.1 p.2, Λ.V p.1 p.2)) :=
    Λ.continuous_Θ.prodMk (Λ.continuous_U.prodMk Λ.continuous_V)
  have hC : Continuous fun p : ℝ × ℝ ↦
      mChristoffel hS ν (Λ.Θ p.1 p.2) (Λ.U p.1 p.2) (Λ.V p.1 p.2) := by
    simpa only [Function.comp_def] using (continuous_mChristoffel hS ν).comp hmapC
  have hmap2 : Continuous fun p : ℝ × ℝ ↦ (Λ.Θ p.1 p.2,
      (mChristoffel hS ν (Λ.Θ p.1 p.2) (Λ.U p.1 p.2) (Λ.V p.1 p.2), Λ.V p.1 p.2)) :=
    Λ.continuous_Θ.prodMk (hC.prodMk Λ.continuous_V)
  have h2 : Continuous fun p : ℝ × ℝ ↦
      G (Λ.Θ p.1 p.2) (mChristoffel hS ν (Λ.Θ p.1 p.2) (Λ.U p.1 p.2) (Λ.V p.1 p.2))
        (Λ.V p.1 p.2) := by
    simpa only [Function.comp_def] using (continuous_fisherInner hS ν).comp hmap2
  exact (continuous_const.mul h1).add h2

/-- **Differentiation under the integral**: the energy is differentiable in the variation
parameter, with derivative `½ ∫₀¹ (2G(W,V) + G(C(U,V),V)) dt`. -/
theorem hasDerivAt_fisherEnergy (Λ : FisherVariation S ν) :
    HasDerivAt (fisherEnergy ν Λ)
      ((1 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, (2 * G (Λ.Θ 0 t) (Λ.W 0 t) (Λ.V 0 t) +
        G (Λ.Θ 0 t) (mChristoffel hS ν (Λ.Θ 0 t) (Λ.U 0 t) (Λ.V 0 t)) (Λ.V 0 t))) 0 := by
  have hFc := continuous_energyIntegrand hS ν Λ
  have hF'c := continuous_energyIntegrandDeriv hS ν Λ
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hF'c.continuousOn
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := (0 : ℝ))
    (b := 1) (F := fun s t ↦ G (Λ.Θ s t) (Λ.V s t) (Λ.V s t))
    (F' := fun s t ↦ 2 * G (Λ.Θ s t) (Λ.W s t) (Λ.V s t) +
      G (Λ.Θ s t) (mChristoffel hS ν (Λ.Θ s t) (Λ.U s t) (Λ.V s t)) (Λ.V s t))
    (x₀ := 0) (s := Icc (-1) 1) (bound := fun _ ↦ C) (Icc_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun x ↦
      (hFc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    ((hFc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1)
    (hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun t ht x hx ↦ ?_) (continuous_const.intervalIntegrable 0 1)
    (ae_of_all _ fun t _ x _ ↦ hasDerivAt_energyIntegrand hS ν Λ x t)
  · unfold fisherEnergy
    exact h.2.const_mul _
  · have ht' : t ∈ Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact Ioc_subset_Icc_self ht
    exact hC (x, t) ⟨hx, ht'⟩

/-- **The first variation of the Fisher energy**:
`E'(0) = G(U,V)|₀¹ − ∫₀¹ G(U, θ'' + ½ C(θ',θ')) dt`. -/
theorem fisherEnergy_variation (Λ : FisherVariation S ν) :
    HasDerivAt (fisherEnergy ν Λ)
      (G (Λ.Θ 0 1) (Λ.U 0 1) (Λ.V 0 1) - G (Λ.Θ 0 0) (Λ.U 0 0) (Λ.V 0 0) -
        ∫ t in (0 : ℝ)..1, G (Λ.Θ 0 t) (Λ.U 0 t)
          (Λ.A 0 t + (1 / 2 : ℝ) • mChristoffel hS ν (Λ.Θ 0 t) (Λ.V 0 t) (Λ.V 0 t))) 0 := by
  refine (hasDerivAt_fisherEnergy hS ν Λ).congr_deriv ?_
  have hc : ∀ f : ℝ × ℝ → ℝ, Continuous f → Continuous fun t ↦ f (0, t) := fun f hf ↦
    hf.comp (continuous_const.prodMk continuous_id)
  have m1 : Continuous fun p : ℝ × ℝ ↦ (Λ.Θ p.1 p.2, (Λ.W p.1 p.2, Λ.V p.1 p.2)) :=
    Λ.continuous_Θ.prodMk (Λ.continuous_W.prodMk Λ.continuous_V)
  have g1 : Continuous fun p : ℝ × ℝ ↦ G (Λ.Θ p.1 p.2) (Λ.W p.1 p.2) (Λ.V p.1 p.2) := by
    simpa only [Function.comp_def] using (continuous_fisherInner hS ν).comp m1
  have c1 : Continuous fun t ↦ G (Λ.Θ 0 t) (Λ.W 0 t) (Λ.V 0 t) := hc _ g1
  have m2 : Continuous fun p : ℝ × ℝ ↦ (Λ.Θ p.1 p.2, (Λ.U p.1 p.2, Λ.A p.1 p.2)) :=
    Λ.continuous_Θ.prodMk (Λ.continuous_U.prodMk Λ.continuous_A)
  have g2 : Continuous fun p : ℝ × ℝ ↦ G (Λ.Θ p.1 p.2) (Λ.U p.1 p.2) (Λ.A p.1 p.2) := by
    simpa only [Function.comp_def] using (continuous_fisherInner hS ν).comp m2
  have c2 : Continuous fun t ↦ G (Λ.Θ 0 t) (Λ.U 0 t) (Λ.A 0 t) := hc _ g2
  have mC : Continuous fun p : ℝ × ℝ ↦ (Λ.Θ p.1 p.2, (Λ.U p.1 p.2, Λ.V p.1 p.2)) :=
    Λ.continuous_Θ.prodMk (Λ.continuous_U.prodMk Λ.continuous_V)
  have gC : Continuous fun p : ℝ × ℝ ↦
      mChristoffel hS ν (Λ.Θ p.1 p.2) (Λ.U p.1 p.2) (Λ.V p.1 p.2) := by
    simpa only [Function.comp_def] using (continuous_mChristoffel hS ν).comp mC
  have m3 : Continuous fun p : ℝ × ℝ ↦ (Λ.Θ p.1 p.2,
      (mChristoffel hS ν (Λ.Θ p.1 p.2) (Λ.U p.1 p.2) (Λ.V p.1 p.2), Λ.V p.1 p.2)) :=
    Λ.continuous_Θ.prodMk (gC.prodMk Λ.continuous_V)
  have g3 : Continuous fun p : ℝ × ℝ ↦
      G (Λ.Θ p.1 p.2) (mChristoffel hS ν (Λ.Θ p.1 p.2) (Λ.U p.1 p.2) (Λ.V p.1 p.2))
        (Λ.V p.1 p.2) := by
    simpa only [Function.comp_def] using (continuous_fisherInner hS ν).comp m3
  have c3 : Continuous fun t ↦
      G (Λ.Θ 0 t) (mChristoffel hS ν (Λ.Θ 0 t) (Λ.U 0 t) (Λ.V 0 t)) (Λ.V 0 t) := hc _ g3
  have i1 : IntervalIntegrable (fun t ↦ G (Λ.Θ 0 t) (Λ.W 0 t) (Λ.V 0 t)) volume 0 1 :=
    c1.intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun t ↦ G (Λ.Θ 0 t) (Λ.U 0 t) (Λ.A 0 t)) volume 0 1 :=
    c2.intervalIntegrable 0 1
  have i3 : IntervalIntegrable (fun t ↦
      G (Λ.Θ 0 t) (mChristoffel hS ν (Λ.Θ 0 t) (Λ.U 0 t) (Λ.V 0 t)) (Λ.V 0 t)) volume 0 1 :=
    c3.intervalIntegrable 0 1
  have i12 : IntervalIntegrable (fun t ↦ G (Λ.Θ 0 t) (Λ.W 0 t) (Λ.V 0 t) +
      G (Λ.Θ 0 t) (Λ.U 0 t) (Λ.A 0 t)) volume 0 1 := (c1.add c2).intervalIntegrable 0 1
  have i123 : IntervalIntegrable (fun t ↦ G (Λ.Θ 0 t) (Λ.W 0 t) (Λ.V 0 t) +
      G (Λ.Θ 0 t) (Λ.U 0 t) (Λ.A 0 t) +
      G (Λ.Θ 0 t) (mChristoffel hS ν (Λ.Θ 0 t) (Λ.U 0 t) (Λ.V 0 t)) (Λ.V 0 t)) volume 0 1 :=
    ((c1.add c2).add c3).intervalIntegrable 0 1
  have hftc := integral_eq_sub_of_hasDerivAt (fun t _ ↦ hasDerivAt_energyPairing hS ν Λ 0 t) i123
  rw [integral_add i12 i3, integral_add i1 i2] at hftc
  have e : ∀ t, G (Λ.Θ 0 t) (Λ.U 0 t)
      (Λ.A 0 t + (1 / 2 : ℝ) • mChristoffel hS ν (Λ.Θ 0 t) (Λ.V 0 t) (Λ.V 0 t)) =
      G (Λ.Θ 0 t) (Λ.U 0 t) (Λ.A 0 t) + (1 / 2 : ℝ) *
        G (Λ.Θ 0 t) (mChristoffel hS ν (Λ.Θ 0 t) (Λ.U 0 t) (Λ.V 0 t)) (Λ.V 0 t) := fun t ↦ by
    rw [fisherInner_add_right hS ν, fisherInner_smul_right hS ν,
      fisherInner_comm hS ν (Λ.Θ 0 t) (Λ.U 0 t)
        (mChristoffel hS ν (Λ.Θ 0 t) (Λ.V 0 t) (Λ.V 0 t)),
      fisherInner_mChristoffel_swap hS ν, mChristoffel_symm hS ν]
  have i3h : IntervalIntegrable (fun t ↦ (1 / 2 : ℝ) *
      G (Λ.Θ 0 t) (mChristoffel hS ν (Λ.Θ 0 t) (Λ.U 0 t) (Λ.V 0 t)) (Λ.V 0 t)) volume 0 1 :=
    (c3.const_mul _).intervalIntegrable 0 1
  have i1' : IntervalIntegrable (fun t ↦ 2 * G (Λ.Θ 0 t) (Λ.W 0 t) (Λ.V 0 t)) volume 0 1 :=
    (c1.const_mul _).intervalIntegrable 0 1
  simp_rw [e]
  rw [integral_add i2 i3h, intervalIntegral.integral_const_mul, integral_add i1' i3,
    intervalIntegral.integral_const_mul]
  linarith

/-- **Levi-Civita geodesics are stationary for the Fisher energy**: along a path with
`θ'' + Γ⁰(θ',θ') = 0` the energy variation reduces to the boundary term `G(U,V)|₀¹`. -/
theorem hasDerivAt_fisherEnergy_of_lcGeodesic (Λ : FisherVariation S ν)
    (hgeo : ∀ t, Λ.A 0 t + alphaChristoffel hS ν 0 (Λ.Θ 0 t) (Λ.V 0 t) (Λ.V 0 t) = 0) :
    HasDerivAt (fisherEnergy ν Λ)
      (G (Λ.Θ 0 1) (Λ.U 0 1) (Λ.V 0 1) - G (Λ.Θ 0 0) (Λ.U 0 0) (Λ.V 0 0)) 0 := by
  have h := fisherEnergy_variation hS ν Λ
  simp only [alphaChristoffel_zero hS ν] at hgeo
  simp only [hgeo, fisherInner_zero_right, intervalIntegral.integral_zero, sub_zero] at h
  exact h

/-- With fixed endpoints, the Fisher energy is stationary along Levi-Civita geodesics: the
Levi-Civita equation is the Euler–Lagrange equation of the Fisher energy. -/
theorem hasDerivAt_fisherEnergy_of_lcGeodesic_fixed (Λ : FisherVariation S ν)
    (hgeo : ∀ t, Λ.A 0 t + alphaChristoffel hS ν 0 (Λ.Θ 0 t) (Λ.V 0 t) (Λ.V 0 t) = 0)
    (h0 : Λ.U 0 0 = 0) (h1 : Λ.U 0 1 = 0) : HasDerivAt (fisherEnergy ν Λ) 0 0 := by
  have h := hasDerivAt_fisherEnergy_of_lcGeodesic hS ν Λ hgeo
  rwa [h0, h1, fisherInner_zero_left, fisherInner_zero_left, sub_zero] at h

end Energy

end Laplace.Multi
