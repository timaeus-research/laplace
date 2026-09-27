/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.VertexGapCriterion
import Laplace.Multi.IntrinsicChart

/-!
# The tangential coordinate on a face, and the normal depth on a facet

For a face fibre `A` of positive mass, the face family `P^A_η = (ν(·|A)).tilted(−⟨η, S⟩)` only
sees the parameter `η` modulo the directions invisible on `A`. The **tangential coordinate**
`faceTheta η ∈ W_A = dirSpan(ν(·|A))` is the face natural coordinate of the face mean of `η`: it
has the same face mean as `η` (`meanMap_faceTheta`), the difference `η − faceTheta η` is invisible
on the face (`sub_faceTheta_mem_invisible`), hence `P^A_η = P^A_{faceTheta η}`
(`familyMeasure_faceMeasure_faceTheta`), and it depends continuously on the face mean
(`tendsto_faceTheta`). On a **facet** — when the only directions of `W = dirSpan ν` invisible on
the face are the multiples of the normal `u` — every `η ∈ W` decomposes as
`η = faceTheta η − (normalDepth η) u` (`eq_faceTheta_sub_smul`), and convergence of the means to
a point of the relative interior of the face forces the tangential coordinate to converge and the
normal depth to diverge (`tendsto_faceTheta_normalDepth_of_tendsto_meanMap`), through the
vertex-gap criterion.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Gauge

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty J] in
/-- The family law is invariant under invisible shifts of the parameter. -/
theorem familyMeasure_add_of_invisible (μ : Measure X) [IsProbabilityMeasure μ] (a : J → ℝ)
    {k : J → ℝ} (hk : k ∈ invisibleSet μ S) :
    familyMeasure μ (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (a + k) =
      familyMeasure μ (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 a := by
  obtain ⟨c, hc⟩ := hk
  rw [familyMeasure_one_zero_eq_tilted hS μ, familyMeasure_one_zero_eq_tilted hS μ]
  have hae : (fun x ↦ -1 * dirLoss S (a + k) x) =ᵐ[μ] fun x ↦ -1 * dirLoss S a x + -c := by
    filter_upwards [hc] with x hx
    simp only [dirLoss_add]
    rw [hx]
    ring
  rw [tilted_congr hae, tilted_add_const]

omit [MeasurableSpace X] [Nonempty X] [Nonempty J] hS in
theorem dotJ_sub_left (a b y : J → ℝ) : dotJ (a - b) y = dotJ a y - dotJ b y := by
  simp [dotJ, sub_mul, Finset.sum_sub_distrib]

variable (A : Set X) [IsProbabilityMeasure (faceMeasure ν A)]

/-- The face law `ν(·|A)`. -/
local notation "νA" => faceMeasure ν A

/-- The face mean map. -/
local notation "meanA" => meanMap νA (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- **The tangential coordinate**: the face natural coordinate of the face mean of `η`. -/
noncomputable def faceTheta (η : J → ℝ) : dirSpan νA (fun _ ↦ (1 : ℝ)) S :=
  chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos _) hS
    ⟨meanA η - meanA 0,
      meanMap_sub_mem_dirSpan measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos _) hS η 0⟩

omit [IsProbabilityMeasure ν] in
theorem chartV_faceTheta (η : J → ℝ) :
    chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos _) hS
      (faceTheta hS ν A η) =
      ⟨meanA η - meanA 0, meanMap_sub_mem_dirSpan measurable_const (integrable_const 1)
        (fun _ ↦ one_pos) (one_integral_pos _) hS η 0⟩ := by
  apply chartV_chartVInv
  simp only [add_sub_cancel]
  rw [← range_meanMap_eq_intrinsicInterior_momentBody measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos _) hS]
  exact ⟨η, rfl⟩

omit [IsProbabilityMeasure ν] in
/-- The tangential coordinate has the same face mean as `η`. -/
theorem meanMap_faceTheta (η : J → ℝ) : meanA (faceTheta hS ν A η : J → ℝ) = meanA η := by
  have h := congrArg Subtype.val (chartV_faceTheta hS ν A η)
  rw [chartV_apply] at h
  exact sub_left_inj.1 h

omit [IsProbabilityMeasure ν] in
/-- `η − faceTheta η` is invisible on the face. -/
theorem sub_faceTheta_mem_invisible (η : J → ℝ) :
    η - (faceTheta hS ν A η : J → ℝ) ∈ invisibleSet νA S := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  exact (meanMap_eq_iff_invisible measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos _) measurable_const h0 hS one_pos _ _).1 (meanMap_faceTheta hS ν A η)

omit [IsProbabilityMeasure ν] in
/-- **Face gauge invariance**: the face family law of `η` is that of its tangential coordinate. -/
theorem familyMeasure_faceMeasure_faceTheta (η : J → ℝ) :
    familyMeasure νA (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η =
      familyMeasure νA (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (faceTheta hS ν A η) := by
  have := familyMeasure_add_of_invisible hS νA (faceTheta hS ν A η : J → ℝ)
    (sub_faceTheta_mem_invisible hS ν A η)
  rwa [add_sub_cancel] at this

omit [IsProbabilityMeasure ν] in
theorem sub_meanMap_zero_mem_dirSpan {M : J → ℝ}
    (hM : M ∈ intrinsicInterior ℝ (momentBody νA (fun _ ↦ (1 : ℝ)) S)) :
    M - meanA 0 ∈ dirSpan νA (fun _ ↦ (1 : ℝ)) S := by
  have h := AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ (intrinsicInterior_subset hM))
    (mem_affineSpan ℝ (meanMap_mem_momentBody measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos _) hS 0))
  rwa [vsub_eq_sub] at h

/-- The tangential coordinate of a point of the relative interior of the face body. -/
noncomputable def faceThetaOf {M : J → ℝ}
    (hM : M ∈ intrinsicInterior ℝ (momentBody νA (fun _ ↦ (1 : ℝ)) S)) :
    dirSpan νA (fun _ ↦ (1 : ℝ)) S :=
  chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos _) hS
    ⟨M - meanA 0, sub_meanMap_zero_mem_dirSpan hS ν A hM⟩

omit [IsProbabilityMeasure ν] in
theorem chartV_faceThetaOf {M : J → ℝ}
    (hM : M ∈ intrinsicInterior ℝ (momentBody νA (fun _ ↦ (1 : ℝ)) S)) :
    chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos _) hS
      (faceThetaOf hS ν A hM) = ⟨M - meanA 0, sub_meanMap_zero_mem_dirSpan hS ν A hM⟩ := by
  apply chartV_chartVInv
  simpa only [add_sub_cancel] using hM

omit [IsProbabilityMeasure ν] in
/-- The face mean of the tangential coordinate of `M` is `M`. -/
theorem meanMap_faceThetaOf {M : J → ℝ}
    (hM : M ∈ intrinsicInterior ℝ (momentBody νA (fun _ ↦ (1 : ℝ)) S)) :
    meanA (faceThetaOf hS ν A hM : J → ℝ) = M := by
  have h := congrArg Subtype.val (chartV_faceThetaOf hS ν A hM)
  rw [chartV_apply] at h
  exact sub_left_inj.1 h

omit [IsProbabilityMeasure ν] in
/-- **Tangential convergence**: convergent face means give convergent tangential coordinates. -/
theorem tendsto_faceTheta {ι : Type*} {l : Filter ι} {η : ι → J → ℝ} {M : J → ℝ}
    (hM : M ∈ intrinsicInterior ℝ (momentBody νA (fun _ ↦ (1 : ℝ)) S))
    (hlim : Tendsto (fun i ↦ meanA (η i)) l (𝓝 M)) :
    Tendsto (fun i ↦ faceTheta hS ν A (η i)) l (𝓝 (faceThetaOf hS ν A hM)) := by
  have hc := (hasStrictFDerivAt_chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos _) hS (faceThetaOf hS ν A hM)).continuousAt
  rw [chartV_faceThetaOf] at hc
  have hsub : Tendsto (fun i ↦ (⟨meanA (η i) - meanA 0, meanMap_sub_mem_dirSpan measurable_const
      (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos _) hS (η i) 0⟩ :
        dirSpan νA (fun _ ↦ (1 : ℝ)) S)) l
      (𝓝 ⟨M - meanA 0, sub_meanMap_zero_mem_dirSpan hS ν A hM⟩) :=
    tendsto_subtype_rng.2 (hlim.sub_const _)
  exact hc.tendsto.comp hsub

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure νA] in
set_option linter.unusedFintypeInType false in
/-- The face direction space lies in the direction space. -/
theorem dirSpan_faceMeasure_le (hA : MeasurableSet A) (hp : 0 < ν.real A) :
    dirSpan νA (fun _ ↦ (1 : ℝ)) S ≤ dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
  AffineSubspace.direction_le (affineSpan_mono ℝ (momentBody_faceMeasure_subset ν hA hS hp))

variable (u : J → ℝ)

/-- **The normal depth** of a parameter: the coefficient of `−u` in `η − faceTheta η`. -/
noncomputable def normalDepth (η : J → ℝ) : ℝ :=
  -dotJ (η - (faceTheta hS ν A η : J → ℝ)) u / dotJ u u

/-- **The facet decomposition** `η = faceTheta η − (normalDepth η) u` for `η ∈ W`, when the only
directions of `W` invisible on the face are the normals. -/
theorem eq_faceTheta_sub_smul (hA : MeasurableSet A) (hp : 0 < ν.real A)
    (hfacet : ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, w ∈ invisibleSet νA S → ∃ c : ℝ, w = c • u)
    (hu : dotJ u u ≠ 0) {η : J → ℝ} (hη : η ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    η = (faceTheta hS ν A η : J → ℝ) - normalDepth hS ν A u η • u := by
  obtain ⟨c, hc⟩ := hfacet (η - faceTheta hS ν A η)
    (Submodule.sub_mem _ hη (dirSpan_faceMeasure_le hS ν A hA hp (faceTheta hS ν A η).2))
    (sub_faceTheta_mem_invisible hS ν A η)
  have hd : normalDepth hS ν A u η = -c := by
    rw [normalDepth, hc, dotJ_smul_left, neg_div, mul_div_assoc, div_self hu, mul_one]
  rw [hd, neg_smul, sub_neg_eq_add, ← hc]
  abel

/-- **Normal divergence**: an off-face vertex gap forces the normal depth to `+∞`. -/
theorem tendsto_normalDepth_atTop (hA : MeasurableSet A) (hp : 0 < ν.real A)
    (hfacet : ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, w ∈ invisibleSet νA S → ∃ c : ℝ, w = c • u)
    (hu : dotJ u u ≠ 0) {η : ℕ → J → ℝ} (hη : ∀ n, η n ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
    {β : ℝ} {z z₀ : J → ℝ} (hz : dotJ u z < β) (hz₀ : dotJ u z₀ = β)
    (hgap : Tendsto (fun n ↦ dotJ (η n) (z - z₀)) atTop atTop) {vM : J → ℝ}
    (hv : Tendsto (fun n ↦ (faceTheta hS ν A (η n) : J → ℝ)) atTop (𝓝 vM)) :
    Tendsto (fun n ↦ normalDepth hS ν A u (η n)) atTop atTop := by
  have hd : 0 < β - dotJ u z := sub_pos.2 hz
  have e : ∀ n, normalDepth hS ν A u (η n) =
      (dotJ (η n) (z - z₀) - dotJ (faceTheta hS ν A (η n) : J → ℝ) (z - z₀)) /
        (β - dotJ u z) := by
    intro n
    have h2 : dotJ (η n) (z - z₀) = dotJ (faceTheta hS ν A (η n) : J → ℝ) (z - z₀) -
        normalDepth hS ν A u (η n) * dotJ u (z - z₀) := by
      conv_lhs => rw [eq_faceTheta_sub_smul hS ν A u hA hp hfacet hu (hη n)]
      rw [dotJ_sub_left, dotJ_smul_left]
    have h3 : dotJ u (z - z₀) = dotJ u z - β := by rw [(isLinearMap_dotJ u).map_sub, hz₀]
    rw [eq_div_iff hd.ne', h2, h3]
    ring
  simp_rw [e]
  refine Tendsto.atTop_div_const hd ?_
  have hcont : Tendsto (fun n ↦ dotJ (faceTheta hS ν A (η n) : J → ℝ) (z - z₀)) atTop
      (𝓝 (dotJ vM (z - z₀))) :=
    ((continuous_dotJ_left (z - z₀)).tendsto _).comp hv
  simpa [sub_eq_add_neg] using hgap.atTop_add hcont.neg

end Gauge

section Components

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hpoly hcharged

/-- **Facet components of a convergent parameter sequence**: if the means converge to a point `M`
of the relative interior of a facet then the tangential coordinates converge to the tangential
coordinate of `M` and the normal depths diverge. -/
theorem tendsto_faceTheta_normalDepth_of_tendsto_meanMap {u : J → ℝ} {β : ℝ}
    [IsProbabilityMeasure (faceMeasure ν {x | dirLoss S u x = β})]
    (hV : ∀ v ∈ V, dotJ u v ≤ β) {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ)))
    (hMβ : dotJ u M = β)
    (hF : minimalFacePoly V M =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)))
    (hM' : M ∈ intrinsicInterior ℝ
      (momentBody (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S))
    {v₀ : J → ℝ} (hv₀V : v₀ ∈ V) (hv₀β : dotJ u v₀ = β) {z : J → ℝ} (hzV : z ∈ V)
    (hz : dotJ u z < β)
    (hfacet : ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S,
      w ∈ invisibleSet (faceMeasure ν {x | dirLoss S u x = β}) S → ∃ c : ℝ, w = c • u)
    (hu : dotJ u u ≠ 0) {η : ℕ → J → ℝ} (hη : ∀ n, η n ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
    (hlim : Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η n)) atTop
      (𝓝 M)) :
    Tendsto (fun n ↦ faceTheta hS ν {x | dirLoss S u x = β} (η n)) atTop
        (𝓝 (faceThetaOf hS ν {x | dirLoss S u x = β} hM')) ∧
      Tendsto (fun n ↦ normalDepth hS ν {x | dirLoss S u x = β} u (η n)) atTop atTop := by
  have hp : 0 < ν.real {x | dirLoss S u x = β} := faceFibre_pos_of_charged ν V hcharged hv₀V hv₀β
  obtain ⟨hface, hgap⟩ := (tendsto_meanMap_iff_faceMean_and_vertexGaps hS ν V hpoly hcharged hV hM
    hMβ hF hv₀V hv₀β η).1 hlim
  have ht := tendsto_faceTheta hS ν _ hM' hface
  have hv : Tendsto (fun n ↦ (faceTheta hS ν {x | dirLoss S u x = β} (η n) : J → ℝ)) atTop
      (𝓝 (faceThetaOf hS ν {x | dirLoss S u x = β} hM' : J → ℝ)) :=
    (continuous_subtype_val.tendsto _).comp ht
  exact ⟨ht, tendsto_normalDepth_atTop hS ν _ u (measurableSet_faceFibre hS u β) hp hfacet hu hη
    hz hv₀β (hgap z hzV hz) hv⟩

end Components

end Laplace.Multi
