/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.VertexGapForward
import Laplace.Multi.NormalConeCauchyCoalescence
import Laplace.Multi.FacetCompletionUnique
import Laplace.Multi.EmpiricalProjection

/-!
# The completion fibre over a charged vertex is a single point

On a charged polytope (`momentBody = conv V`, every vertex fibre charged) let `M ∈ V` be the
unique vertex on the exposing face `{⟨u,·⟩ = β}`. The **vertex normal form** of a sequence of
parameters whose means converge to `M` is: eventually every gap `⟨θ_n, w − M⟩`, `w ∈ V`, is
nonnegative (the forward vertex-gap criterion makes them diverge for `w ≠ M`), so `θ_n` lies in
the closed normal cone of the vertex, and the mass of the vertex fibre `{S = M}` tends to one (the
family laws converge in `L¹` to the projection law of `M`, which is carried by the fibre). Any
two Fisher-Cauchy sequences over `M` are therefore of the shape required by normal-cone
coalescence with base `v = 0`: **the completion fibre over a charged vertex is at most one point**
(`meanExt_eq_vertex_unique`), in every codimension.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Geometry

variable {J : Type*} [Fintype J] (V : Finset (J → ℝ))

/-- A linear functional on the polytope is bounded below by its bound on the vertices. -/
theorem le_dotJ_of_mem_convexHull {a : J → ℝ} {c : ℝ} (hcone : ∀ w ∈ V, c ≤ dotJ a w)
    {x : J → ℝ} (hx : x ∈ convexHull ℝ (V : Set (J → ℝ))) : c ≤ dotJ a x := by
  obtain ⟨wts, ⟨hw0, hw1⟩, rfl⟩ := (mem_convexHull_iff_exists_vertexWeights V x).1 hx
  rw [dotJ_sum_smul_vertices]
  calc c = ∑ v : V, wts v * c := by rw [← Finset.sum_mul, hw1, one_mul]
    _ ≤ ∑ v : V, wts v * dotJ a v :=
        Finset.sum_le_sum fun v _ ↦ mul_le_mul_of_nonneg_left (hcone v v.2) (hw0 v)

/-- **An exposed vertex is the only point of the polytope on its exposing face.** -/
theorem eq_of_dotJ_eq_of_mem_convexHull {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β)
    {M : J → ℝ} (hMV : M ∈ V) (huniq : ∀ v ∈ V, dotJ u v = β → v = M) {x : J → ℝ}
    (hx : x ∈ convexHull ℝ (V : Set (J → ℝ))) (hxβ : dotJ u x = β) : x = M := by
  classical
  obtain ⟨wts, ⟨hw0, hw1⟩, rfl⟩ := (mem_convexHull_iff_exists_vertexWeights V x).1 hx
  rw [dotJ_sum_smul_vertices] at hxβ
  have hsum : ∑ v : V, wts v * (β - dotJ u v) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul, hxβ, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun v _ ↦
    mul_nonneg (hw0 v) (sub_nonneg.2 (hV v v.2))).1 hsum
  have hoff : ∀ v : V, v ≠ ⟨M, hMV⟩ → wts v = 0 := fun v hv ↦ by
    have h := hzero v (Finset.mem_univ v)
    rcases mul_eq_zero.1 h with h0 | h0
    · exact h0
    · exfalso
      exact hv (Subtype.ext (huniq v v.2 (by linarith)))
  have hM1 : wts ⟨M, hMV⟩ = 1 := by
    rw [← hw1, Finset.sum_eq_single ⟨M, hMV⟩ (fun v _ hv ↦ hoff v hv)
      (fun h ↦ absurd (Finset.mem_univ _) h)]
  rw [Finset.sum_eq_single ⟨M, hMV⟩ (fun v _ hv ↦ by rw [hoff v hv, zero_smul])
    (fun h ↦ absurd (Finset.mem_univ _) h), hM1, one_smul]

end Geometry

section Vertex

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family of tilts. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

variable (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hpoly hcharged

omit [Nonempty X] [Nonempty J] [Nonempty V] [IsProbabilityMeasure ν] hcharged in
set_option linter.unusedFintypeInType false in
/-- The statistics take values in the polytope almost everywhere. -/
theorem ae_statPoint_mem_polytope : ∀ᵐ x ∂ν, statPoint S x ∈ convexHull ℝ (V : Set (J → ℝ)) := by
  filter_upwards [ae_statPoint_mem_essRange measurable_const (fun _ ↦ one_pos) hS] with x hx
  exact hpoly ▸ essRange_subset_momentBody S hx

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] [Nonempty V] hcharged in
/-- A parameter in the closed normal cone of the vertex `M` has `⟨a, S⟩ ≥ ⟨a, M⟩` a.e. -/
theorem ae_dotJ_le_dirLoss_of_cone {M a : J → ℝ} (hcone : ∀ w ∈ V, 0 ≤ dotJ a (w - M)) :
    ∀ᵐ x ∂ν, dotJ a M ≤ dirLoss S a x := by
  filter_upwards [ae_statPoint_mem_polytope hS ν V hpoly] with x hx
  rw [dirLoss_eq_dotJ_statPoint]
  refine le_dotJ_of_mem_convexHull V (fun w hw ↦ ?_) hx
  have := hcone w hw
  rw [(isLinearMap_dotJ a).map_sub] at this
  linarith

variable {u : J → ℝ} {β : ℝ} (hV : ∀ v ∈ V, dotJ u v ≤ β) {M : J → ℝ} (hMV : M ∈ V)
  (hMβ : dotJ u M = β) (huniq : ∀ v ∈ V, dotJ u v = β → v = M)
include hV hMV hMβ huniq

/-- **Eventual cone membership**: if the means converge to the exposed vertex `M`, the parameters
eventually lie in the closed normal cone `{θ | ⟨θ, w − M⟩ ≥ 0 ∀ w ∈ V}`. -/
theorem eventually_cone_of_tendsto_meanMap {θ : ℕ → J → ℝ}
    (hlim : Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ n)) atTop
      (𝓝 M)) :
    ∀ᶠ n in atTop, ∀ w ∈ V, 0 ≤ dotJ (θ n) (w - M) := by
  have hM : M ∈ convexHull ℝ (V : Set (J → ℝ)) := subset_convexHull ℝ _ hMV
  rw [eventually_all_finset]
  intro w hw
  by_cases hwM : w = M
  · subst hwM
    exact Eventually.of_forall fun n ↦ by
      rw [sub_self, (isLinearMap_dotJ (θ n)).map_zero]
  · have hwβ : dotJ u w < β := lt_of_le_of_ne (hV w hw) fun h ↦ hwM (huniq w hw h)
    have := tendsto_vertexGap_of_tendsto_meanMap hS ν V hpoly hcharged hV hM hMβ hMV
      (mem_minimalFacePoly (V := V) hM) hw hwβ hlim
    exact this.eventually_ge_atTop 0

omit [Nonempty V] in
/-- The projection law of the exposed vertex is carried by the vertex fibre. -/
theorem responseProjection_statFibre_eq_one :
    (responseProjection hS ν M).real (statFibre S M) = 1 := by
  have hM : M ∈ convexHull ℝ (V : Set (J → ℝ)) := subset_convexHull ℝ _ hMV
  have hfin := genRate_ne_top_of_mem_convexHull_vertices hS ν V hcharged hM
  have hq := (responseProjection_spec hS ν hfin).1
  have hac := responseProjection_absolutelyContinuous_of_mem_polytope hS ν V hpoly hcharged hM
  have hface := responseProjection_compl_faceFibre_eq_zero hS ν V hpoly hcharged hV hM hMβ
  have hnull : ν ({x | dirLoss S u x = β} \ statFibre S M) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 (ae_statPoint_mem_polytope hS ν V hpoly))
    intro x hx' hx
    obtain ⟨hxβ, hxM⟩ := hx'
    exact hxM (eq_of_dotJ_eq_of_mem_convexHull V hV hMV huniq hx hxβ)
  have hcompl : responseProjection hS ν M (statFibre S M)ᶜ = 0 := by
    refine measure_mono_null (fun x hx ↦ ?_) (measure_union_null hface (hac hnull))
    by_cases hxβ : dirLoss S u x = β
    · exact Or.inr ⟨hxβ, hx⟩
    · exact Or.inl hxβ
  rw [measureReal_def, (prob_compl_eq_zero_iff (measurableSet_statFibre hS M)).1 hcompl,
    ENNReal.toReal_one]

/-- **Face mass tends to one**: along a sequence whose means converge to the exposed vertex, the
mass of the vertex fibre tends to one. -/
theorem tendsto_real_statFibre_one {θ : ℕ → J → ℝ}
    (hlim : Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (θ n)) atTop
      (𝓝 M)) :
    Tendsto (fun n ↦ (Pfam (θ n)).real (statFibre S M)) atTop (𝓝 1) := by
  have hM : M ∈ convexHull ℝ (V : Set (J → ℝ)) := subset_convexHull ℝ _ hMV
  have h := tendsto_measureReal_family_statFibre hS ν V hpoly hcharged hM hlim M
  rwa [responseProjection_statFibre_eq_one hS ν V hpoly hcharged hV hMV hMβ huniq] at h

/-- **The completion fibre over a charged vertex is a single point**: two points of the Fisher
completion with extended mean the exposed vertex `M` coincide. -/
theorem meanExt_eq_vertex_unique {x x' : FisherCompletion hS ν} (hx : meanExt hS ν x = M)
    (hx' : meanExt hS ν x' = M) : x = x' := by
  obtain ⟨θ, hθ⟩ := exists_seq_tendsto_completion hS ν x
  obtain ⟨η, hη⟩ := exists_seq_tendsto_completion hS ν x'
  have hmθ := tendsto_meanMap_of_tendsto_completion hS ν hθ
  have hmη := tendsto_meanMap_of_tendsto_completion hS ν hη
  rw [hx] at hmθ
  rw [hx'] at hmη
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    (eventually_cone_of_tendsto_meanMap hS ν V hpoly hcharged hV hMV hMβ huniq hmθ)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1
    (eventually_cone_of_tendsto_meanMap hS ν V hpoly hcharged hV hMV hMβ huniq hmη)
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = max N₁ N₂ := ⟨_, rfl⟩
  have hN₁N : N₁ ≤ N := hNdef ▸ le_max_left _ _
  have hN₂N : N₂ ≤ N := hNdef ▸ le_max_right _ _
  obtain ⟨a, hadef⟩ : ∃ a : ℕ → J → ℝ, a = fun n ↦ ((θ (n + N)).param : J → ℝ) := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℕ → J → ℝ, b = fun n ↦ ((η (n + N)).param : J → ℝ) := ⟨_, rfl⟩
  have ha : ∀ n, a n ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun n ↦ by
    rw [hadef]
    exact (θ (n + N)).param.2
  have hb : ∀ n, b n ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun n ↦ by
    rw [hbdef]
    exact (η (n + N)).param.2
  have hconea : ∀ n, ∀ w ∈ V, 0 ≤ dotJ (a n) (w - M) := fun n w hw ↦ by
    rw [hadef]
    exact hN₁ (n + N) (by omega) w hw
  have hconeb : ∀ n, ∀ w ∈ V, 0 ≤ dotJ (b n) (w - M) := fun n w hw ↦ by
    rw [hbdef]
    exact hN₂ (n + N) (by omega) w hw
  have hA := measurableSet_statFibre hS M
  have hca : ∀ n, ∀ y ∈ statFibre S M, dirLoss S (a n) y = dotJ (a n) M := fun n y hy ↦ by
    rw [dirLoss_eq_dotJ_statPoint]
    exact congrArg (dotJ (a n)) hy
  have hcb : ∀ n, ∀ y ∈ statFibre S M, dirLoss S (b n) y = dotJ (b n) M := fun n y hy ↦ by
    rw [dirLoss_eq_dotJ_statPoint]
    exact congrArg (dotJ (b n)) hy
  have hgea : ∀ n, ∀ᵐ y ∂ν, dotJ (a n) M ≤ dirLoss S (a n) y := fun n ↦
    ae_dotJ_le_dirLoss_of_cone hS ν V hpoly (hconea n)
  have hgeb : ∀ n, ∀ᵐ y ∂ν, dotJ (b n) M ≤ dirLoss S (b n) y := fun n ↦
    ae_dotJ_le_dirLoss_of_cone hS ν V hpoly (hconeb n)
  have hBa' : ∀ n, ∃ B : ℝ, ∀ y, |dirLoss S (a n) y - dotJ (a n) M| ≤ B := fun n ↦ by
    obtain ⟨K, hK⟩ := (bdd_dirLoss hS (a n)).2
    exact ⟨K + |dotJ (a n) M|, fun y ↦ (abs_sub _ _).trans (add_le_add (hK y) le_rfl)⟩
  have hBb' : ∀ n, ∃ B : ℝ, ∀ y, |dirLoss S (b n) y - dotJ (b n) M| ≤ B := fun n ↦ by
    obtain ⟨K, hK⟩ := (bdd_dirLoss hS (b n)).2
    exact ⟨K + |dotJ (b n) M|, fun y ↦ (abs_sub _ _).trans (add_le_add (hK y) le_rfl)⟩
  choose Ba hBa using hBa'
  choose Bb hBb using hBb'
  have hθA : Tendsto (fun n ↦ (Pfam (0 + a n)).real (statFibre S M)) atTop (𝓝 1) := by
    have := (tendsto_real_statFibre_one hS ν V hpoly hcharged hV hMV hMβ huniq
      (θ := fun n ↦ ((θ n).param : J → ℝ)) hmθ).comp (tendsto_add_atTop_nat N)
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_def, hadef, zero_add]
  have hηA : Tendsto (fun n ↦ (Pfam (0 + b n)).real (statFibre S M)) atTop (𝓝 1) := by
    have := (tendsto_real_statFibre_one hS ν V hpoly hcharged hV hMV hMβ huniq
      (θ := fun n ↦ ((η n).param : J → ℝ)) hmη).comp (tendsto_add_atTop_nat N)
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_def, hbdef, zero_add]
  have hxa : Tendsto (fun n ↦ ((⟨⟨0 + a n, Submodule.add_mem _ (Submodule.zero_mem _) (ha n)⟩⟩ :
      FisherPoint hS ν) : FisherCompletion hS ν)) atTop (𝓝 x) := by
    refine (hθ.comp (tendsto_add_atTop_nat N)).congr fun n ↦ ?_
    simp only [Function.comp_def]
    congr 1
    exact FisherPoint.ext (Subtype.ext (by simp [hadef]))
  have hxb : Tendsto (fun n ↦ ((⟨⟨0 + b n, Submodule.add_mem _ (Submodule.zero_mem _) (hb n)⟩⟩ :
      FisherPoint hS ν) : FisherCompletion hS ν)) atTop (𝓝 x') := by
    refine (hη.comp (tendsto_add_atTop_nat N)).congr fun n ↦ ?_
    simp only [Function.comp_def]
    congr 1
    exact FisherPoint.ext (Subtype.ext (by simp [hbdef]))
  exact completion_limit_eq_of_normalCone hS ν 0 (Submodule.zero_mem _) ha hb hA hca hgea hBa
    hcb hgeb hBb hθA hηA hxa hxb

end Vertex

end Laplace.Multi
