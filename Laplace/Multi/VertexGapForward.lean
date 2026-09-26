/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.VertexGapExtinction
import Laplace.Multi.PolytopeFaceOrder
import Laplace.Multi.AtlasRefinement

/-!
# Vertex gaps from the convergence of means

On a charged polytope, if the means `m(η_n)` of the family laws `P_{η_n}` converge to `M`, then the
family densities converge in `L¹` to the projection density of `M`
(`tendsto_integral_abs_famDens_sub`, from the `L¹` continuity of the atlas), hence the masses of
the charged vertex fibres converge (`tendsto_measureReal_family_statFibre`).  The projection `q_M`
gives no mass to the fibre of a vertex off the minimal face and positive mass to the fibre of a
charged vertex, while

  `P_η(S = v)/P_η(S = v₀) = e^{−⟨η, v − v₀⟩} ν(S = v)/ν(S = v₀)`

(`measureReal_family_statFibre`), so every off-face vertex gap diverges:
`⟨η_n, v − v₀⟩ → +∞` (`tendsto_vertexGap_of_tendsto_meanMap`).  This is the forward half of the
vertex-gap criterion.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Forward

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family density is the projection density of its own mean. -/
theorem projDens_meanMap_ae_eq (η : J → ℝ) :
    projDens hS ν (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η) =ᵐ[ν] famDens S ν η := by
  refine projDens_ae_eq hS ν (measurable_famDens hS ν η) (famDens_nonneg hS ν η) ?_
  rw [← mean_familyMeasure_one_zero hS ν η, responseProjection_mean_familyMeasure hS ν η,
    familyMeasure_eq_withDensity_famDens]

omit [Nonempty X] [Nonempty J] in
/-- The mass of a vertex fibre under the family law. -/
theorem measureReal_family_statFibre (η : J → ℝ) (v : J → ℝ) :
    (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η).real (statFibre S v) =
      Real.exp (-dotJ η v) * ν.real (statFibre S v) / famZ S ν η := by
  rw [familyMeasure_eq_withDensity_famDens, measureReal_withDensity_ofReal ν (famDens_nonneg hS ν η)
    (integrable_famDens hS ν η) (measurableSet_statFibre hS v),
    setIntegral_congr_fun (measurableSet_statFibre hS v) (fun x hx ↦ ?_) (g := fun _ ↦
      Real.exp (-dotJ η v) / famZ S ν η), setIntegral_const, smul_eq_mul]
  · ring
  · change famDens S ν η x = Real.exp (-dotJ η v) / famZ S ν η
    rw [famDens, famWeight_eq_of_mem_statFibre η hx]

variable (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hpoly hcharged

omit [Nonempty V] hcharged in
/-- The means of the family laws lie in the polytope. -/
theorem meanMap_mem_polytope (η : J → ℝ) :
    meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η ∈ convexHull ℝ (V : Set (J → ℝ)) := by
  rw [← hpoly]
  exact meanMap_mem_momentBody measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS η

/-- **`L¹` convergence of the family densities** when the means converge. -/
theorem tendsto_integral_abs_famDens_sub {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ)))
    {η : ℕ → J → ℝ}
    (hlim : Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η n)) atTop
      (𝓝 M)) :
    Tendsto (fun n ↦ ∫ x, |famDens S ν (η n) x - projDens hS ν M x| ∂ν) atTop (𝓝 0) := by
  have h := tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_projL1_of_tendsto hS ν V hcharged hM
    (fun n ↦ meanMap_mem_polytope hS ν V hpoly (η n)) hlim)
  simp only [norm_projL1_sub] at h
  refine h.congr fun n ↦ integral_congr_ae ((projDens_meanMap_ae_eq hS ν (η n)).mono
    fun x hx ↦ ?_)
  beta_reduce
  rw [hx]

/-- The masses of the vertex fibres converge to their masses under the projection. -/
theorem tendsto_measureReal_family_statFibre {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) {η : ℕ → J → ℝ}
    (hlim : Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η n)) atTop
      (𝓝 M)) (v : J → ℝ) :
    Tendsto (fun n ↦ (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η n)).real
      (statFibre S v)) atTop (𝓝 ((responseProjection hS ν M).real (statFibre S v))) := by
  have hfin := genRate_ne_top_of_mem_convexHull_vertices hS ν V hcharged hM
  have hA := measurableSet_statFibre hS v
  have e1 : ∀ n, (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η n)).real
      (statFibre S v) = ∫ x in statFibre S v, famDens S ν (η n) x ∂ν := fun n ↦ by
    rw [familyMeasure_eq_withDensity_famDens,
      measureReal_withDensity_ofReal ν (famDens_nonneg hS ν _) (integrable_famDens hS ν _) hA]
  have e2 : (responseProjection hS ν M).real (statFibre S v) =
      ∫ x in statFibre S v, projDens hS ν M x ∂ν := by
    rw [responseProjection_eq_withDensity_projDens hS ν hfin,
      measureReal_withDensity_ofReal ν (projDens_nonneg hS ν M) (integrable_projDens hS ν M) hA]
  simp only [e1, e2]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _)
    (Eventually.of_forall fun n ↦ ?_)
    (tendsto_integral_abs_famDens_sub hS ν V hpoly hcharged hM hlim)
  have hint : Integrable (fun x ↦ |famDens S ν (η n) x - projDens hS ν M x|) ν :=
    ((integrable_famDens hS ν _).sub (integrable_projDens hS ν M)).abs
  rw [Real.norm_eq_abs, ← integral_sub (integrable_famDens hS ν _).integrableOn
    (integrable_projDens hS ν M).integrableOn]
  exact abs_integral_le_integral_abs.trans
    (setIntegral_le_integral hint (Eventually.of_forall fun x ↦ abs_nonneg _))

omit [Nonempty V] in
/-- The projection gives no mass to the fibre of a vertex off the exposing face. -/
theorem responseProjection_statFibre_eq_zero {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
    {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (hMβ : dotJ u M = β) {v : J → ℝ}
    (hvβ : dotJ u v < β) : responseProjection hS ν M (statFibre S v) = 0 := by
  refine measure_mono_null (fun x hx ↦ ?_)
    (responseProjection_compl_faceFibre_eq_zero hS ν V hpoly hcharged hV hM hMβ)
  have hx' : statPoint S x = v := hx
  intro hxF
  have hxF' : dirLoss S u x = β := hxF
  rw [dirLoss_eq_dotJ_statPoint, hx'] at hxF'
  exact hvβ.ne hxF'

/-- The projection charges the fibre of every vertex on the minimal face. -/
theorem responseProjection_statFibre_pos {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ)))
    {v : J → ℝ} (hvV : v ∈ V) (hvF : v ∈ minimalFacePoly V M) :
    0 < (responseProjection hS ν M).real (statFibre S v) := by
  have hac := restrict_minimalFaceFibre_absolutelyContinuous hS ν V hpoly hcharged hM
  refine ENNReal.toReal_pos (fun h0 ↦ ?_) (measure_ne_top _ _)
  have h := hac h0
  rw [Measure.restrict_apply (measurableSet_statFibre hS v),
    Set.inter_eq_left.2 (statFibre_subset_minimalFaceFibre hvF)] at h
  have hpos := hcharged v hvV
  rw [measureReal_def, h, ENNReal.toReal_zero] at hpos
  exact lt_irrefl _ hpos

/-- **The forward vertex-gap criterion**: if the means converge to `M`, every gap between a vertex
off the exposing face and a vertex charged by `M` diverges. -/
theorem tendsto_vertexGap_of_tendsto_meanMap {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
    {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (hMβ : dotJ u M = β) {v₀ : J → ℝ}
    (hv₀V : v₀ ∈ V) (hv₀F : v₀ ∈ minimalFacePoly V M) {v : J → ℝ} (hvV : v ∈ V)
    (hvβ : dotJ u v < β) {η : ℕ → J → ℝ}
    (hlim : Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η n)) atTop
      (𝓝 M)) :
    Tendsto (fun n ↦ dotJ (η n) (v - v₀)) atTop atTop := by
  have h1 := tendsto_measureReal_family_statFibre hS ν V hpoly hcharged hM hlim v
  have h2 := tendsto_measureReal_family_statFibre hS ν V hpoly hcharged hM hlim v₀
  have hzero : (responseProjection hS ν M).real (statFibre S v) = 0 := by
    rw [measureReal_def, responseProjection_statFibre_eq_zero hS ν V hpoly hcharged hV hM hMβ hvβ,
      ENNReal.toReal_zero]
  rw [hzero] at h1
  have hpos := responseProjection_statFibre_pos hS ν V hpoly hcharged hM hv₀V hv₀F
  have hratio := h1.div h2 hpos.ne'
  rw [zero_div] at hratio
  have hcv := hcharged v hvV
  have hcv₀ := hcharged v₀ hv₀V
  have e : ∀ n, (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η n)).real
        (statFibre S v) /
      (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η n)).real (statFibre S v₀) =
      Real.exp (-dotJ (η n) (v - v₀)) * (ν.real (statFibre S v) / ν.real (statFibre S v₀)) :=
    fun n ↦ by
      have hZ := (famZ_pos hS ν (η n)).ne'
      have h1 := hcv.ne'
      have h2 := hcv₀.ne'
      rw [measureReal_family_statFibre hS ν, measureReal_family_statFibre hS ν,
        (isLinearMap_dotJ (η n)).map_sub, neg_sub, Real.exp_sub, Real.exp_neg, Real.exp_neg]
      field_simp
  have hratio' : Tendsto (fun n ↦ Real.exp (-dotJ (η n) (v - v₀)) *
      (ν.real (statFibre S v) / ν.real (statFibre S v₀))) atTop (𝓝 0) :=
    hratio.congr fun n ↦ by
      rw [Pi.div_apply]
      exact e n
  have hC : 0 < ν.real (statFibre S v) / ν.real (statFibre S v₀) := div_pos hcv hcv₀
  have hexp : Tendsto (fun n ↦ Real.exp (-dotJ (η n) (v - v₀))) atTop (𝓝 0) := by
    have := hratio'.div_const (ν.real (statFibre S v) / ν.real (statFibre S v₀))
    rw [zero_div] at this
    refine this.congr fun n ↦ ?_
    rw [mul_div_cancel_right₀ _ hC.ne']
  exact tendsto_neg_atBot_iff.1 (Real.tendsto_exp_comp_nhds_zero.1 hexp)

end Forward

end Laplace.Multi
