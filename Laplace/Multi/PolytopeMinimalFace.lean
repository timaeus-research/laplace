/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PolyhedralVertexSection
import Laplace.Multi.FiniteMinimalFace
import Laplace.Multi.RelativeInterior
import Laplace.Multi.PolytopeFaceCut

/-!
# The minimal face of a polytope through the vertex section

For a polytope `P = conv V` and a point `M ∈ P`, the vertex section `vertexSection V M` is the
entropy-maximal weighting of the vertices with barycentre `M`.  We show that the set of
*charged* vertices (positive weight) spans the **minimal face** of `P` containing `M`:

* `minimalFacePoly V M = conv (charged vertices)` is an extreme subset of `P`
  (`isExtreme_minimalFacePoly`) contained in every face containing `M`
  (`minimalFacePoly_subset_of_isExtreme`);
* a vertex is charged exactly when it lies on this face
  (`vertexSection_pos_iff_mem_minimalFacePoly`, Csiszár's support theorem for polytopes);
* `M` lies in the relative interior of the face (`mem_intrinsicInterior_minimalFacePoly`);
* the face is **exposed**: there is a linear functional `dotJ u` maximised over `V` exactly at the
  charged vertices, and the face is the hull of the tight generators
  (`exists_exposing_minimalFacePoly`).

The exposure uses the strong separation of the affine span of the face from the hull of the
uncharged vertices; disjointness comes from the relative interior of `M` together with the
absorption property of the vertex section.
-/

open MeasureTheory Set

namespace Laplace.Multi

variable {J : Type*} [Fintype J]

section Carried

variable (V : Finset (J → ℝ))

omit [Fintype J] in
/-- The responses carried by a set of vertices form the hull of those vertices. -/
theorem carriedResponses_vertexStat (A : Set V) :
    carriedResponses (vertexStat V) A = convexHull ℝ (Subtype.val '' A) := by
  classical
  apply subset_antisymm
  · rintro _ ⟨b, hb, hbA, rfl⟩
    rw [vecMoment_eq_sum_smul]
    have hsum : ∑ x : V, b x • statPoint (vertexStat V) x =
        ∑ x ∈ Finset.univ.filter (fun x : V ↦ x ∈ A), b x • (x : J → ℝ) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ hx
      have hxA : x ∉ A := by simpa using hx
      rw [hbA x hxA, zero_smul]
    rw [hsum]
    refine (convex_convexHull ℝ _).sum_mem (fun x _ ↦ hb.1 x) ?_
      (fun x hx ↦ subset_convexHull ℝ _ ⟨x, by simpa using hx, rfl⟩)
    rw [Finset.sum_subset (Finset.subset_univ _) (fun x _ hx ↦ hbA x (by simpa using hx))]
    exact hb.2
  · refine convexHull_min ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      refine ⟨deltaVec v, deltaVec_mem_stdSimplex v, fun x hx ↦ ?_, vecMoment_deltaVec _ v⟩
      have hxv : x ≠ v := fun h ↦ hx (h ▸ hv)
      simp [deltaVec, hxv]
    · intro y hy z hz a c ha hc hac
      obtain ⟨b, hb, hbA, rfl⟩ := hy
      obtain ⟨b', hb', hbA', rfl⟩ := hz
      refine ⟨a • b + c • b', convex_stdSimplex ℝ V hb hb' ha hc hac, fun x hx ↦ ?_, ?_⟩
      · simp [hbA x hx, hbA' x hx]
      · rw [vecMoment_add, vecMoment_smul, vecMoment_smul]

end Carried

section MinimalFace

variable [Nonempty J] (V : Finset (J → ℝ)) [Nonempty V]

/-- The vertices charged by the vertex section. -/
def chargedVertices (M : J → ℝ) : Set (J → ℝ) :=
  Subtype.val '' {v : V | 0 < vertexSection V M v}

/-- The face of the polytope spanned by the charged vertices. -/
def minimalFacePoly (M : J → ℝ) : Set (J → ℝ) := convexHull ℝ (chargedVertices V M)

theorem chargedVertices_subset (M : J → ℝ) : chargedVertices V M ⊆ (V : Set (J → ℝ)) := by
  rintro _ ⟨v, -, rfl⟩
  exact v.2

theorem minimalFacePoly_subset (M : J → ℝ) :
    minimalFacePoly V M ⊆ convexHull ℝ (V : Set (J → ℝ)) :=
  convexHull_mono (chargedVertices_subset V M)

theorem mem_minimalFacePoly_of_pos {M : J → ℝ} {v : V} (hv : 0 < vertexSection V M v) :
    (v : J → ℝ) ∈ minimalFacePoly V M :=
  subset_convexHull ℝ _ ⟨v, hv, rfl⟩

variable {V}

omit [Fintype J] [Nonempty J] [Nonempty V] in
theorem mem_hull_range_iff {M : J → ℝ} :
    M ∈ convexHull ℝ (range (statPoint (vertexStat V))) ↔ M ∈ convexHull ℝ (V : Set (J → ℝ)) := by
  rw [range_statPoint_vertexStat]

/-- **The minimal face is the hull of the charged vertices.** -/
theorem minimalFace_vertexStat_eq {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    minimalFace (vertexStat V) M = minimalFacePoly V M := by
  rw [minimalFace_eq (bdd_vertexStat V) (vertexUniform V) (vertexUniform_singleton_pos V)
    (mem_hull_range_iff.2 hM), carriedResponses_vertexStat]
  rfl

theorem isExtreme_minimalFacePoly {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    IsExtreme ℝ (convexHull ℝ (V : Set (J → ℝ))) (minimalFacePoly V M) := by
  have := isExtreme_minimalFace (bdd_vertexStat V) (vertexUniform V)
    (vertexUniform_singleton_pos V) (mem_hull_range_iff.2 hM)
  rwa [range_statPoint_vertexStat, minimalFace_vertexStat_eq hM] at this

theorem mem_minimalFacePoly {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    M ∈ minimalFacePoly V M := by
  have := mem_minimalFace (bdd_vertexStat V) (vertexUniform V)
    (vertexUniform_singleton_pos V) (mem_hull_range_iff.2 hM)
  rwa [minimalFace_vertexStat_eq hM] at this

/-- The face of the charged vertices lies in every face containing `M`. -/
theorem minimalFacePoly_subset_of_isExtreme {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ)))
    {G : Set (J → ℝ)} (hG : IsExtreme ℝ (convexHull ℝ (V : Set (J → ℝ))) G) (hMG : M ∈ G) :
    minimalFacePoly V M ⊆ G := by
  rw [← minimalFace_vertexStat_eq hM]
  exact sInter_subset_of_mem ⟨by rwa [range_statPoint_vertexStat], hMG⟩

/-- **Csiszár's support theorem for polytopes**: a vertex is charged iff it lies on the minimal
face. -/
theorem vertexSection_pos_iff_mem_minimalFacePoly {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (v : V) :
    0 < vertexSection V M v ↔ (v : J → ℝ) ∈ minimalFacePoly V M := by
  have := qStarVec_pos_iff_mem_minimalFace (bdd_vertexStat V) (vertexUniform V)
    (vertexUniform_singleton_pos V) (mem_hull_range_iff.2 hM) v
  rwa [minimalFace_vertexStat_eq hM] at this

theorem vertexSection_eq_zero_iff {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (v : V) :
    vertexSection V M v = 0 ↔ (v : J → ℝ) ∉ minimalFacePoly V M := by
  rw [← vertexSection_pos_iff_mem_minimalFacePoly hM, not_lt]
  exact ⟨fun h ↦ h.le, fun h ↦ le_antisymm h (vertexSection_nonneg V hM v)⟩

omit [Nonempty J] [Nonempty V] in
/-- `dotJ` of a vertex combination. -/
theorem dotJ_sum_smul_vertices (e : J → ℝ) (a : V → ℝ) :
    dotJ e (∑ v : V, a v • (v : J → ℝ)) = ∑ v : V, a v * dotJ e v := by
  change (IsLinearMap.mk' (dotJ e) (isLinearMap_dotJ e)) (∑ v : V, a v • (v : J → ℝ)) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun v _ ↦ by rw [map_smul, smul_eq_mul]; rfl

/-- **The point lies in the relative interior of its minimal face.** -/
theorem mem_intrinsicInterior_minimalFacePoly {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    M ∈ intrinsicInterior ℝ (minimalFacePoly V M) := by
  unfold minimalFacePoly
  rw [mem_intrinsicInterior_iff_forall_supporting (convex_convexHull ℝ _)]
  refine ⟨mem_minimalFacePoly hM, fun e he ↦ ?_⟩
  have hsum := sum_vertexSection_smul V hM
  have hvert : ∀ v : V, 0 < vertexSection V M v → dotJ e v = dotJ e M := by
    intro v₀ hv₀
    by_contra hne
    have hlt : dotJ e v₀ < dotJ e M :=
      lt_of_le_of_ne (he _ (mem_minimalFacePoly_of_pos V hv₀)) hne
    have hle : ∀ v : V, vertexSection V M v * dotJ e v ≤ vertexSection V M v * dotJ e M := by
      intro v
      rcases (vertexSection_nonneg V hM v).lt_or_eq with hv | hv
      · exact mul_le_mul_of_nonneg_left (he _ (mem_minimalFacePoly_of_pos V hv)) hv.le
      · rw [← hv, zero_mul, zero_mul]
    have hstrict : ∑ v : V, vertexSection V M v * dotJ e v <
        ∑ v : V, vertexSection V M v * dotJ e M :=
      Finset.sum_lt_sum (fun v _ ↦ hle v)
        ⟨v₀, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt hv₀⟩
    rw [← Finset.sum_mul, (vertexSection_mem_stdSimplex V hM).2, one_mul, ← dotJ_sum_smul_vertices,
      hsum] at hstrict
    exact lt_irrefl _ hstrict
  intro y hy
  refine convexHull_min ?_ (convex_hyperplane_dotJ e (dotJ e M)) hy
  rintro _ ⟨v, hv, rfl⟩
  exact hvert v hv

/-- The uncharged vertices. -/
def unchargedVertices (V : Finset (J → ℝ)) [Nonempty V] (M : J → ℝ) : Set (J → ℝ) :=
  Subtype.val '' {v : V | vertexSection V M v = 0}

theorem unchargedVertices_subset (M : J → ℝ) :
    unchargedVertices V M ⊆ (V : Set (J → ℝ)) := by
  rintro _ ⟨v, -, rfl⟩
  exact v.2

/-- No point of the hull of the uncharged vertices lies on the minimal face. -/
theorem notMem_minimalFacePoly_of_mem_uncharged {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) {x : J → ℝ}
    (hx : x ∈ convexHull ℝ (unchargedVertices V M)) : x ∉ minimalFacePoly V M := by
  intro hxF
  have hM' := mem_hull_range_iff.2 hM
  have hxF' : x ∈ carriedResponses (vertexStat V) (supportSet (bdd_vertexStat V)
      (vertexUniform V) M) := by
    rw [carriedResponses_vertexStat]
    exact hxF
  have hxU : x ∈ carriedResponses (vertexStat V) {v : V | vertexSection V M v = 0} := by
    rw [carriedResponses_vertexStat]
    exact hx
  obtain ⟨b, hb, hbs, rfl⟩ := hxF'
  obtain ⟨c, hc, hcs, hcb⟩ := hxU
  have hpos : ∑ v : V, (0 : ℝ) < ∑ v : V, c v := by
    rw [hc.2]
    simp
  obtain ⟨v, -, hv⟩ := Finset.exists_lt_of_sum_lt hpos
  have hq := support_absorb (bdd_vertexStat V) (vertexUniform V) (vertexUniform_singleton_pos V)
    hM' hb hbs hc hcb hv
  have hzero : c v = 0 := hcs v (by
    intro h
    exact hq.ne' h)
  exact hv.ne' hzero

/-- The hull of the uncharged vertices misses the affine span of the minimal face. -/
theorem disjoint_uncharged_affineSpan {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    Disjoint (convexHull ℝ (unchargedVertices V M))
      (affineSpan ℝ (minimalFacePoly V M) : Set (J → ℝ)) := by
  rw [Set.disjoint_left]
  intro x hx hxA
  refine notMem_minimalFacePoly_of_mem_uncharged hM hx ?_
  have hMF := mem_minimalFacePoly hM
  obtain ⟨-, δ, hδ, hball⟩ :=
    mem_intrinsicInterior_iff_exists_ball.1 (mem_intrinsicInterior_minimalFacePoly hM)
  have hv : M - x ∈ (affineSpan ℝ (minimalFacePoly V M)).direction := by
    have := AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hMF) hxA
    simpa [vsub_eq_sub] using this
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = δ / (2 * (‖M - x‖ + 1)) := ⟨_, rfl⟩
  have hε : 0 < ε := by
    rw [hεdef]
    positivity
  have hεv : ‖ε • (M - x)‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    calc ε * ‖M - x‖ ≤ ε * (‖M - x‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ = δ / 2 := by
        rw [hεdef, div_mul_eq_mul_div, mul_div_mul_right _ _ (by positivity)]
      _ < δ := by linarith
  have hy : M + ε • (M - x) ∈ minimalFacePoly V M := hball _ (Submodule.smul_mem _ ε hv) hεv
  have hxP : x ∈ convexHull ℝ (V : Set (J → ℝ)) :=
    convexHull_mono (unchargedVertices_subset M) hx
  have hyP : M + ε • (M - x) ∈ convexHull ℝ (V : Set (J → ℝ)) := minimalFacePoly_subset V M hy
  refine (isExtreme_minimalFacePoly hM).left_mem_of_mem_openSegment hxP hyP hMF ?_
  refine ⟨ε / (1 + ε), 1 / (1 + ε), by positivity, by positivity, ?_, ?_⟩
  · field_simp
    ring
  · have hab : ε / (1 + ε) + 1 / (1 + ε) = 1 := by
      field_simp
      ring
    have h2 : 1 / (1 + ε) * ε = ε / (1 + ε) := by ring
    rw [smul_add, smul_smul, smul_sub, h2]
    calc (ε / (1 + ε)) • x + ((1 / (1 + ε)) • M + ((ε / (1 + ε)) • M - (ε / (1 + ε)) • x))
        = (ε / (1 + ε) + 1 / (1 + ε)) • M := by module
      _ = M := by rw [hab, one_smul]

omit [Nonempty J] in
/-- Every continuous linear functional is a `dotJ`. -/
theorem exists_dotJ_eq (f : StrongDual ℝ (J → ℝ)) : ∃ u : J → ℝ, ∀ x, f x = dotJ u x := by
  classical
  refine ⟨fun j ↦ f (fun i ↦ if j = i then 1 else 0), fun x ↦ ?_⟩
  rw [show f x = f.toLinearMap x from rfl, LinearMap.pi_apply_eq_sum_univ]
  simp only [dotJ, smul_eq_mul, ContinuousLinearMap.coe_coe]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

omit [Nonempty J] in
/-- A linear functional bounded below on an affine subspace is constant on it. -/
theorem dotJ_eq_of_forall_lt_on_affineSpan {K : Set (J → ℝ)} {u : J → ℝ} {c : ℝ}
    (hlt : ∀ b ∈ (affineSpan ℝ K : Set (J → ℝ)), c < dotJ u b) {x y : J → ℝ}
    (hx : x ∈ affineSpan ℝ K) (hy : y ∈ affineSpan ℝ K) : dotJ u y = dotJ u x := by
  by_contra hne
  have hw : y - x ∈ (affineSpan ℝ K).direction := by
    have := AffineSubspace.vsub_mem_direction hy hx
    simpa [vsub_eq_sub] using this
  have hne' : dotJ u y - dotJ u x ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (c - dotJ u x - 1) / (dotJ u y - dotJ u x) := ⟨_, rfl⟩
  have hmem : s • (y - x) +ᵥ x ∈ affineSpan ℝ K :=
    (AffineSubspace.vadd_mem_iff_mem_direction _ hx).2 (Submodule.smul_mem _ s hw)
  have h := hlt _ hmem
  rw [vadd_eq_add, (isLinearMap_dotJ u).map_add, (isLinearMap_dotJ u).map_smul, smul_eq_mul,
    (isLinearMap_dotJ u).map_sub, hsdef, div_mul_cancel₀ _ hne'] at h
  linarith

/-- **The minimal face is exposed**: a linear functional maximised over the vertices exactly at
the charged vertices, whose tight hull is the minimal face. -/
theorem exists_exposing_minimalFacePoly {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    ∃ u : J → ℝ, ∃ β : ℝ, (∀ v ∈ V, dotJ u v ≤ β) ∧ dotJ u M = β ∧
      (∀ v : V, dotJ u v = β ↔ 0 < vertexSection V M v) ∧
      minimalFacePoly V M =
        convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)) := by
  have hfin : (unchargedVertices V M).Finite := (Set.toFinite _).image _
  obtain ⟨f, s, t, hs, hst, ht⟩ := geometric_hahn_banach_compact_closed (convex_convexHull ℝ _)
    (hfin.isCompact_convexHull ℝ) (affineSpan ℝ (minimalFacePoly V M)).convex
    (AffineSubspace.closed_of_finiteDimensional _) (disjoint_uncharged_affineSpan hM)
  obtain ⟨u, hu⟩ := exists_dotJ_eq f
  simp only [hu] at hs ht
  have hMF := mem_minimalFacePoly hM
  have hconst : ∀ y ∈ minimalFacePoly V M, dotJ u y = dotJ u M := fun y hy ↦
    dotJ_eq_of_forall_lt_on_affineSpan ht (mem_affineSpan ℝ hMF) (mem_affineSpan ℝ hy)
  have hvertex : ∀ v : V, dotJ u v = dotJ u M ↔ 0 < vertexSection V M v := by
    intro v
    constructor
    · intro hv
      by_contra hv0
      have h0 : vertexSection V M v = 0 :=
        le_antisymm (not_lt.1 hv0) (vertexSection_nonneg V hM v)
      have hlt := hs _ (subset_convexHull ℝ _ ⟨v, h0, rfl⟩)
      have hgt := ht _ (mem_affineSpan ℝ hMF)
      linarith
    · intro hv
      exact hconst _ (mem_minimalFacePoly_of_pos V hv)
  have hle : ∀ v ∈ V, dotJ u v ≤ dotJ u M := by
    intro v hv
    rcases (vertexSection_nonneg V hM ⟨v, hv⟩).lt_or_eq with hpos | hzero
    · exact ((hvertex ⟨v, hv⟩).2 hpos).le
    · have hlt := hs _ (subset_convexHull ℝ _ ⟨⟨v, hv⟩, hzero.symm, rfl⟩)
      have hgt := ht _ (mem_affineSpan ℝ hMF)
      exact (hlt.trans (hst.trans hgt)).le
  refine ⟨u, dotJ u M, hle, rfl, hvertex, ?_⟩
  apply subset_antisymm
  · refine convexHull_mono ?_
    rintro _ ⟨v, hv, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨v.2, (hvertex v).2 hv⟩)
  · refine convexHull_mono ?_
    intro v hv
    obtain ⟨hvV, hvβ⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hv)
    exact ⟨⟨v, hvV⟩, (hvertex ⟨v, hvV⟩).1 hvβ, rfl⟩

/-- The exposed form of the minimal face as a hyperplane section of the polytope. -/
theorem exists_minimalFacePoly_eq_inter_hyperplane {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    ∃ u : J → ℝ, ∃ β : ℝ, (∀ v ∈ V, dotJ u v ≤ β) ∧ dotJ u M = β ∧
      minimalFacePoly V M = convexHull ℝ (V : Set (J → ℝ)) ∩ {y | dotJ u y = β} := by
  obtain ⟨u, β, hV, hMβ, -, hF⟩ := exists_exposing_minimalFacePoly hM
  exact ⟨u, β, hV, hMβ, by rw [hF, convexHull_inter_hyperplane V u β hV]⟩

end MinimalFace

end Laplace.Multi
