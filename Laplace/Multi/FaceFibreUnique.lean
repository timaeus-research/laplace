/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.VertexFibreUnique
import Laplace.Multi.VertexGapConditioning
import Laplace.Multi.FaceGauge

/-!
# The completion fibre over every charged face interior is a single point

On a charged polytope let `A = {⟨u,S⟩ = β}` be an exposed face event containing a charged
vertex `z₀` of the minimal face of `M`, and let `M` lie in the relative interior of the face
body. The **face normal form** of a sequence whose means converge to `M`: its tangential
coordinates `τ_n = faceTheta θ_n` converge to `v_M` (the face means converge and the face mean
map is a chart), the normal parts `a_n = θ_n − τ_n` are invisible on the face (`⟨a_n,S⟩` is
a.e. constant on `A`, equal to `⟨a_n, z₀⟩`), and every outside-vertex gap `⟨a_n, w − z₀⟩`
diverges (the forward vertex-gap criterion minus a convergent tangential term), so `a_n`
eventually lies in the normal cone of the face; the face mass tends to one. Replacing `τ_n` by
`v_M` costs a Euclidean segment of vanishing length, so two Fisher-Cauchy sequences over `M`
are of the shape `v_M + a_n`, `v_M + b_n` required by normal-cone coalescence: **the completion
fibre over `M` is at most one point** (`meanExt_eq_face_unique`), in every codimension and
without a preferred normal ray.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Perturb

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family of tilts. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

omit [Nonempty J] in
/-- The mass of a set is stable under Euclidean perturbations of the parameter that vanish. -/
theorem tendsto_real_of_norm_sub_tendsto {A : Set X} (hA : MeasurableSet A)
    {θ η : ℕ → dirSpan ν (fun _ ↦ (1 : ℝ)) S}
    (h : Tendsto (fun n ↦ (Pfam (θ n : J → ℝ)).real A) atTop (𝓝 1))
    (hd : Tendsto (fun n ↦ ‖(η n : J → ℝ) - (θ n : J → ℝ)‖) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (Pfam (η n : J → ℝ)).real A) atTop (𝓝 1) := by
  obtain ⟨K, hK0, hK⟩ := exists_fisherNorm_bound hS ν
  have hsq : ∀ n, |√((Pfam (η n : J → ℝ)).real A) - √((Pfam (θ n : J → ℝ)).real A)| ≤
      K / 2 * ‖(η n : J → ℝ) - (θ n : J → ℝ)‖ := fun n ↦ by
    refine (abs_sqrt_real_sub_le_hellingerDist hS ν _ _ hA).trans
      ((hellingerDist_le_half_fisherDist hS ν (θ n) (η n)).trans ?_)
    have := fisherDist_le_mul_norm hS ν hK (θ n) (η n)
    rw [Submodule.coe_norm, Submodule.coe_sub] at this
    linarith
  have hθs : Tendsto (fun n ↦ √((Pfam (θ n : J → ℝ)).real A)) atTop (𝓝 1) := by
    simpa using h.sqrt
  have hs : Tendsto (fun n ↦ √((Pfam (η n : J → ℝ)).real A)) atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero] at hθs ⊢
    have hlim : Tendsto (fun n ↦ K / 2 * ‖(η n : J → ℝ) - (θ n : J → ℝ)‖ +
        ‖√((Pfam (θ n : J → ℝ)).real A) - 1‖) atTop (𝓝 0) := by
      simpa using (hd.const_mul (K / 2)).add hθs
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hlim
    calc ‖√((Pfam (η n : J → ℝ)).real A) - 1‖ =
          |(√((Pfam (η n : J → ℝ)).real A) - √((Pfam (θ n : J → ℝ)).real A)) +
            (√((Pfam (θ n : J → ℝ)).real A) - 1)| := by
          rw [Real.norm_eq_abs]
          congr 1
          ring
      _ ≤ K / 2 * ‖(η n : J → ℝ) - (θ n : J → ℝ)‖ + ‖√((Pfam (θ n : J → ℝ)).real A) - 1‖ := by
          rw [Real.norm_eq_abs]
          exact (abs_add_le _ _).trans (add_le_add (hsq n) le_rfl)
  have := hs.pow 2
  simp only [one_pow] at this
  exact this.congr fun n ↦ Real.sq_sqrt measureReal_nonneg

/-- Convergence in the completion is stable under Euclidean perturbations that vanish. -/
theorem tendsto_completion_of_norm_sub_tendsto {θ η : ℕ → FisherPoint hS ν}
    {x : FisherCompletion hS ν} (hθ : Tendsto (fun n ↦ (θ n : FisherCompletion hS ν)) atTop (𝓝 x))
    (hd : Tendsto (fun n ↦ ‖((η n).param : J → ℝ) - ((θ n).param : J → ℝ)‖) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (η n : FisherCompletion hS ν)) atTop (𝓝 x) := by
  obtain ⟨K, hK0, hK⟩ := exists_fisherNorm_bound hS ν
  rw [tendsto_iff_dist_tendsto_zero] at hθ ⊢
  refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_)
    (by simpa using (hd.const_mul K).add hθ)
  calc dist (η n : FisherCompletion hS ν) x ≤
        dist (η n : FisherCompletion hS ν) (θ n) + dist (θ n : FisherCompletion hS ν) x :=
        dist_triangle _ _ _
    _ ≤ K * ‖((η n).param : J → ℝ) - ((θ n).param : J → ℝ)‖ +
        dist (θ n : FisherCompletion hS ν) x := by
        refine add_le_add ?_ le_rfl
        rw [UniformSpace.Completion.dist_eq, FisherPoint.dist_eq]
        have := fisherDist_le_mul_norm hS ν hK (η n).param (θ n).param
        rwa [Submodule.coe_norm, Submodule.coe_sub, norm_sub_rev] at this

end Perturb

section Face

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family of tilts. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

variable (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hpoly hcharged

/-- `L¹` convergence of the family densities gives convergence of the mass of every measurable
set to its projection mass. -/
theorem tendsto_measureReal_family_set {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ)))
    {η : ℕ → J → ℝ}
    (hlim : Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η n)) atTop
      (𝓝 M)) {B : Set X} (hB : MeasurableSet B) :
    Tendsto (fun n ↦ (Pfam (η n)).real B) atTop (𝓝 ((responseProjection hS ν M).real B)) := by
  have hfin := genRate_ne_top_of_mem_convexHull_vertices hS ν V hcharged hM
  have e1 : ∀ n, (Pfam (η n)).real B = ∫ x in B, famDens S ν (η n) x ∂ν := fun n ↦ by
    rw [familyMeasure_eq_withDensity_famDens,
      measureReal_withDensity_ofReal ν (famDens_nonneg hS ν _) (integrable_famDens hS ν _) hB]
  have e2 : (responseProjection hS ν M).real B = ∫ x in B, projDens hS ν M x ∂ν := by
    rw [responseProjection_eq_withDensity_projDens hS ν hfin,
      measureReal_withDensity_ofReal ν (projDens_nonneg hS ν M) (integrable_projDens hS ν M) hB]
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

variable {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β) {z₀ : J → ℝ} (hz₀V : z₀ ∈ V)
  (hz₀β : dotJ u z₀ = β)
include hz₀V hz₀β

omit [Nonempty X] [Nonempty J] [Nonempty V] hpoly hz₀V hz₀β in
/-- A charged face vertex has positive face mass. -/
theorem faceMeasure_statFibre_ne_zero {v : J → ℝ} (hvV : v ∈ V) (hvβ : dotJ u v = β) :
    faceMeasure ν {x | dirLoss S u x = β} (statFibre S v) ≠ 0 := by
  have hsub : statFibre S v ⊆ {x | dirLoss S u x = β} := statFibre_subset_faceFibre hvβ
  unfold faceMeasure
  rw [Measure.smul_apply, Measure.restrict_apply (measurableSet_statFibre hS v),
    Set.inter_eq_left.2 hsub, smul_eq_mul]
  exact mul_ne_zero (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
    (ENNReal.toReal_pos_iff.1 (hcharged v hvV)).1.ne'

omit [Nonempty X] [Nonempty J] [Nonempty V] hpoly hz₀V hz₀β in
/-- A direction whose contrast is a.e. constant on the face pairs with every charged face vertex
to that constant. -/
theorem dotJ_eq_of_ae_const {a : J → ℝ} {c : ℝ}
    (hc : ∀ᵐ x ∂faceMeasure ν {x | dirLoss S u x = β}, dirLoss S a x = c) {v : J → ℝ}
    (hvV : v ∈ V) (hvβ : dotJ u v = β) : dotJ a v = c := by
  by_contra hne
  have hsub : statFibre S v ⊆ {x | ¬ dirLoss S a x = c} := fun x hx ↦ by
    have hx' : statPoint S x = v := hx
    change ¬ dirLoss S a x = c
    rw [dirLoss_eq_dotJ_statPoint, hx']
    exact hne
  exact faceMeasure_statFibre_ne_zero hS ν V hcharged hvV hvβ
    (measure_mono_null hsub (ae_iff.1 hc))

omit [Nonempty X] [Nonempty J] [Nonempty V] hpoly in
/-- The a.e. face constancy of an invisible direction, with the constant `⟨a, z₀⟩`. -/
theorem ae_dirLoss_eq_of_mem_invisible {a : J → ℝ}
    (ha : a ∈ invisibleSet (faceMeasure ν {x | dirLoss S u x = β}) S) :
    ∀ᵐ x ∂ν, x ∈ {x | dirLoss S u x = β} → dirLoss S a x = dotJ a z₀ := by
  obtain ⟨c, hc⟩ := ha
  rw [dotJ_eq_of_ae_const hS ν V hcharged hc hz₀V hz₀β]
  have hA := measurableSet_faceFibre hS u β
  have hc' : ((ν {x | dirLoss S u x = β})⁻¹ • ν.restrict {x | dirLoss S u x = β})
      {x | ¬ dirLoss S a x = c} = 0 := ae_iff.1 hc
  rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hc'
  rcases hc' with h0 | h0
  · exact absurd h0 (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
  · exact (ae_restrict_iff' hA).1 (ae_iff.2 h0)

omit [Nonempty X] [Nonempty J] [Nonempty V] hpoly in
theorem dotJ_eq_dotJ_of_mem_invisible {a : J → ℝ}
    (ha : a ∈ invisibleSet (faceMeasure ν {x | dirLoss S u x = β}) S) {w : J → ℝ} (hwV : w ∈ V)
    (hwβ : dotJ u w = β) : dotJ a w = dotJ a z₀ := by
  obtain ⟨c, hc⟩ := ha
  rw [dotJ_eq_of_ae_const hS ν V hcharged hc hwV hwβ,
    dotJ_eq_of_ae_const hS ν V hcharged hc hz₀V hz₀β]

include hV

/-- **Eventual normal-cone membership of the normal part**: if the means converge to `M` and
the tangential parts converge, the normal parts `θ_n − τ_n` eventually pair with `z₀` at most as
with any vertex. -/
theorem eventually_face_cone {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ)))
    (hMβ : dotJ u M = β) (hz₀F : z₀ ∈ minimalFacePoly V M) {θ : ℕ → J → ℝ}
    (hlim : Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ n)) atTop
      (𝓝 M)) {τ : ℕ → J → ℝ}
    (hinv : ∀ n, θ n - τ n ∈ invisibleSet (faceMeasure ν {x | dirLoss S u x = β}) S)
    {v : J → ℝ} (hτ : Tendsto τ atTop (𝓝 v)) :
    ∀ᶠ n in atTop, ∀ w ∈ V, dotJ (θ n - τ n) z₀ ≤ dotJ (θ n - τ n) w := by
  rw [eventually_all_finset]
  intro w hw
  by_cases hwβ : dotJ u w = β
  · exact Eventually.of_forall fun n ↦
      (dotJ_eq_dotJ_of_mem_invisible hS ν V hcharged hz₀V hz₀β (hinv n) hw hwβ).ge
  · have hwβ' : dotJ u w < β := lt_of_le_of_ne (hV w hw) hwβ
    have hgap := tendsto_vertexGap_of_tendsto_meanMap hS ν V hpoly hcharged hV hM hMβ hz₀V hz₀F
      hw hwβ' hlim
    have hconv : Tendsto (fun n ↦ dotJ (τ n) (w - z₀)) atTop (𝓝 (dotJ v (w - z₀))) :=
      ((continuous_dotJ_left (w - z₀)).tendsto v).comp hτ
    filter_upwards [hgap.eventually_ge_atTop (dotJ v (w - z₀) + 1),
      hconv.eventually (Iio_mem_nhds (lt_add_one _))] with n h1 h2
    have e1 := (isLinearMap_dotJ (θ n)).map_sub w z₀
    have e2 := (isLinearMap_dotJ (τ n)).map_sub w z₀
    rw [dotJ_sub_left, dotJ_sub_left]
    have h2' : dotJ (τ n) (w - z₀) < dotJ v (w - z₀) + 1 := h2
    linarith

omit hz₀V hz₀β in
/-- **Face mass tends to one** along a sequence whose means converge to a point of the exposing
face. -/
theorem tendsto_real_faceFibre_one {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ)))
    (hMβ : dotJ u M = β) {θ : ℕ → J → ℝ}
    (hlim : Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ n)) atTop
      (𝓝 M)) :
    Tendsto (fun n ↦ (Pfam (θ n)).real {x | dirLoss S u x = β}) atTop (𝓝 1) := by
  have hA := measurableSet_faceFibre hS u β
  have hfin := genRate_ne_top_of_mem_convexHull_vertices hS ν V hcharged hM
  have hq := (responseProjection_spec hS ν hfin).1
  have h := tendsto_measureReal_family_set hS ν V hpoly hcharged hM hlim hA
  have h1 : (responseProjection hS ν M).real {x | dirLoss S u x = β} = 1 := by
    rw [measureReal_def, (prob_compl_eq_zero_iff hA).1
      (responseProjection_compl_faceFibre_eq_zero hS ν V hpoly hcharged hV hM hMβ),
      ENNReal.toReal_one]
  rwa [h1] at h

/-- **The completion fibre over a charged face interior is a single point.** -/
theorem meanExt_eq_face_unique {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ)))
    (hMβ : dotJ u M = β) (hz₀F : z₀ ∈ minimalFacePoly V M)
    [IsProbabilityMeasure (faceMeasure ν {x | dirLoss S u x = β})]
    (hMint : M ∈ intrinsicInterior ℝ
      (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S))
    {x x' : FisherCompletion hS ν} (hx : meanExt hS ν x = M) (hx' : meanExt hS ν x' = M) :
    x = x' := by
  have hAm := measurableSet_faceFibre hS u β
  have hp : 0 < ν.real {x | dirLoss S u x = β} := faceFibre_pos_of_charged ν V hcharged hz₀V hz₀β
  have hWA := dirSpan_faceMeasure_le hS ν {x | dirLoss S u x = β} hAm hp
  obtain ⟨θ, hθ⟩ := exists_seq_tendsto_completion hS ν x
  obtain ⟨η, hη⟩ := exists_seq_tendsto_completion hS ν x'
  have hmθ := tendsto_meanMap_of_tendsto_completion hS ν hθ
  have hmη := tendsto_meanMap_of_tendsto_completion hS ν hη
  rw [hx] at hmθ
  rw [hx'] at hmη
  -- tangential convergence
  have hfθ := tendsto_meanMap_faceMeasure_of_tendsto_meanMap hS ν (u := u) (β := β) V hpoly
    hcharged hV hp hM hMβ hmθ
  have hfη := tendsto_meanMap_faceMeasure_of_tendsto_meanMap hS ν (u := u) (β := β) V hpoly
    hcharged hV hp hM hMβ hmη
  obtain ⟨v, hvdef⟩ : ∃ v : J → ℝ,
      v = (faceThetaOf hS ν {x | dirLoss S u x = β} hMint : J → ℝ) := ⟨_, rfl⟩
  have hvW : v ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := hvdef ▸ hWA (faceThetaOf _ _ _ hMint).2
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℕ → J → ℝ, τ = fun n ↦
      (faceTheta hS ν {x | dirLoss S u x = β} ((θ n).param : J → ℝ) : J → ℝ) := ⟨_, rfl⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℕ → J → ℝ, σ = fun n ↦
      (faceTheta hS ν {x | dirLoss S u x = β} ((η n).param : J → ℝ) : J → ℝ) := ⟨_, rfl⟩
  have hτ : Tendsto τ atTop (𝓝 v) := by
    rw [hτdef, hvdef]
    exact tendsto_subtype_rng.1 (tendsto_faceTheta hS ν _ hMint
      (η := fun n ↦ ((θ n).param : J → ℝ)) hfθ)
  have hσ : Tendsto σ atTop (𝓝 v) := by
    rw [hσdef, hvdef]
    exact tendsto_subtype_rng.1 (tendsto_faceTheta hS ν _ hMint
      (η := fun n ↦ ((η n).param : J → ℝ)) hfη)
  have hinvθ : ∀ n, ((θ n).param : J → ℝ) - τ n ∈
      invisibleSet (faceMeasure ν {x | dirLoss S u x = β}) S := fun n ↦ by
    rw [hτdef]
    exact sub_faceTheta_mem_invisible hS ν _ _
  have hinvη : ∀ n, ((η n).param : J → ℝ) - σ n ∈
      invisibleSet (faceMeasure ν {x | dirLoss S u x = β}) S := fun n ↦ by
    rw [hσdef]
    exact sub_faceTheta_mem_invisible hS ν _ _
  -- eventual cone membership
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (eventually_face_cone hS ν V hpoly hcharged hV hz₀V hz₀β
    hM hMβ hz₀F (θ := fun n ↦ ((θ n).param : J → ℝ)) hmθ hinvθ hτ)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (eventually_face_cone hS ν V hpoly hcharged hV hz₀V hz₀β
    hM hMβ hz₀F (θ := fun n ↦ ((η n).param : J → ℝ)) hmη hinvη hσ)
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = max N₁ N₂ := ⟨_, rfl⟩
  have hN₁N : N₁ ≤ N := hNdef ▸ le_max_left _ _
  have hN₂N : N₂ ≤ N := hNdef ▸ le_max_right _ _
  -- the shifted normal parts
  obtain ⟨a, hadef⟩ : ∃ a : ℕ → J → ℝ, a = fun n ↦ ((θ (n + N)).param : J → ℝ) - τ (n + N) :=
    ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℕ → J → ℝ, b = fun n ↦ ((η (n + N)).param : J → ℝ) - σ (n + N) :=
    ⟨_, rfl⟩
  have hτW : ∀ n, τ n ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun n ↦ by
    rw [hτdef]
    exact hWA (faceTheta _ _ _ _).2
  have hσW : ∀ n, σ n ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun n ↦ by
    rw [hσdef]
    exact hWA (faceTheta _ _ _ _).2
  have ha : ∀ n, a n ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun n ↦ by
    rw [hadef]
    exact Submodule.sub_mem _ (θ (n + N)).param.2 (hτW _)
  have hb : ∀ n, b n ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun n ↦ by
    rw [hbdef]
    exact Submodule.sub_mem _ (η (n + N)).param.2 (hσW _)
  have hconea : ∀ n, ∀ w ∈ V, dotJ (a n) z₀ ≤ dotJ (a n) w := fun n w hw ↦ by
    rw [hadef]
    exact hN₁ (n + N) (by omega) w hw
  have hconeb : ∀ n, ∀ w ∈ V, dotJ (b n) z₀ ≤ dotJ (b n) w := fun n w hw ↦ by
    rw [hbdef]
    exact hN₂ (n + N) (by omega) w hw
  have hca : ∀ n, ∀ᵐ y ∂ν, y ∈ {x | dirLoss S u x = β} → dirLoss S (a n) y = dotJ (a n) z₀ :=
    fun n ↦ ae_dirLoss_eq_of_mem_invisible hS ν V hcharged hz₀V hz₀β (hadef ▸ hinvθ (n + N))
  have hcb : ∀ n, ∀ᵐ y ∂ν, y ∈ {x | dirLoss S u x = β} → dirLoss S (b n) y = dotJ (b n) z₀ :=
    fun n ↦ ae_dirLoss_eq_of_mem_invisible hS ν V hcharged hz₀V hz₀β (hbdef ▸ hinvη (n + N))
  have hgea : ∀ n, ∀ᵐ y ∂ν, dotJ (a n) z₀ ≤ dirLoss S (a n) y := fun n ↦ by
    filter_upwards [ae_statPoint_mem_polytope hS ν V hpoly] with y hy
    rw [dirLoss_eq_dotJ_statPoint]
    exact le_dotJ_of_mem_convexHull V (hconea n) hy
  have hgeb : ∀ n, ∀ᵐ y ∂ν, dotJ (b n) z₀ ≤ dirLoss S (b n) y := fun n ↦ by
    filter_upwards [ae_statPoint_mem_polytope hS ν V hpoly] with y hy
    rw [dirLoss_eq_dotJ_statPoint]
    exact le_dotJ_of_mem_convexHull V (hconeb n) hy
  have hBa' : ∀ n, ∃ B : ℝ, ∀ y, |dirLoss S (a n) y - dotJ (a n) z₀| ≤ B := fun n ↦ by
    obtain ⟨K, hK⟩ := (bdd_dirLoss hS (a n)).2
    exact ⟨K + |dotJ (a n) z₀|, fun y ↦ (abs_sub _ _).trans (add_le_add (hK y) le_rfl)⟩
  have hBb' : ∀ n, ∃ B : ℝ, ∀ y, |dirLoss S (b n) y - dotJ (b n) z₀| ≤ B := fun n ↦ by
    obtain ⟨K, hK⟩ := (bdd_dirLoss hS (b n)).2
    exact ⟨K + |dotJ (b n) z₀|, fun y ↦ (abs_sub _ _).trans (add_le_add (hK y) le_rfl)⟩
  choose Ba hBa using hBa'
  choose Bb hBb using hBb'
  -- the perturbed sequences `v + a n` and `v + b n`
  have hdθ : Tendsto (fun n ↦ ‖(v + a n) - ((θ (n + N)).param : J → ℝ)‖) atTop (𝓝 0) := by
    have := tendsto_iff_norm_sub_tendsto_zero.1 (hτ.comp (tendsto_add_atTop_nat N))
    have e : ∀ n, (v + a n) - ((θ (n + N)).param : J → ℝ) = -(τ (n + N) - v) := fun n ↦ by
      simp only [hadef]
      abel
    refine this.congr fun n ↦ ?_
    rw [Function.comp_apply, e n, norm_neg]
  have hdη : Tendsto (fun n ↦ ‖(v + b n) - ((η (n + N)).param : J → ℝ)‖) atTop (𝓝 0) := by
    have := tendsto_iff_norm_sub_tendsto_zero.1 (hσ.comp (tendsto_add_atTop_nat N))
    have e : ∀ n, (v + b n) - ((η (n + N)).param : J → ℝ) = -(σ (n + N) - v) := fun n ↦ by
      simp only [hbdef]
      abel
    refine this.congr fun n ↦ ?_
    rw [Function.comp_apply, e n, norm_neg]
  have hθA : Tendsto (fun n ↦ (Pfam (v + a n)).real {x | dirLoss S u x = β}) atTop (𝓝 1) := by
    have hmass := (tendsto_real_faceFibre_one hS ν V hpoly hcharged hV hM hMβ
      (θ := fun n ↦ ((θ n).param : J → ℝ)) hmθ).comp (tendsto_add_atTop_nat N)
    exact tendsto_real_of_norm_sub_tendsto hS ν hAm (θ := fun n ↦ (θ (n + N)).param)
      (η := fun n ↦ ⟨v + a n, Submodule.add_mem _ hvW (ha n)⟩) hmass hdθ
  have hηA : Tendsto (fun n ↦ (Pfam (v + b n)).real {x | dirLoss S u x = β}) atTop (𝓝 1) := by
    have hmass := (tendsto_real_faceFibre_one hS ν V hpoly hcharged hV hM hMβ
      (θ := fun n ↦ ((η n).param : J → ℝ)) hmη).comp (tendsto_add_atTop_nat N)
    exact tendsto_real_of_norm_sub_tendsto hS ν hAm (θ := fun n ↦ (η (n + N)).param)
      (η := fun n ↦ ⟨v + b n, Submodule.add_mem _ hvW (hb n)⟩) hmass hdη
  have hxa : Tendsto (fun n ↦ ((⟨⟨v + a n, Submodule.add_mem _ hvW (ha n)⟩⟩ :
      FisherPoint hS ν) : FisherCompletion hS ν)) atTop (𝓝 x) :=
    tendsto_completion_of_norm_sub_tendsto hS ν (θ := fun n ↦ θ (n + N))
      (hθ.comp (tendsto_add_atTop_nat N)) hdθ
  have hxb : Tendsto (fun n ↦ ((⟨⟨v + b n, Submodule.add_mem _ hvW (hb n)⟩⟩ :
      FisherPoint hS ν) : FisherCompletion hS ν)) atTop (𝓝 x') :=
    tendsto_completion_of_norm_sub_tendsto hS ν (θ := fun n ↦ η (n + N))
      (hη.comp (tendsto_add_atTop_nat N)) hdη
  exact completion_limit_eq_of_normalCone hS ν v hvW ha hb hAm hca hgea hBa hcb hgeb hBb hθA hηA
    hxa hxb

end Face

end Laplace.Multi
