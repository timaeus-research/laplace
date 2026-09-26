/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PolyhedralVertexWitness

/-!
# Polyhedral completion II: the continuous vertex section

The finite completion of round 68, applied to the finite **vertex set** `V` with the tautological
features `v ↦ v j` and the uniform reference law, yields a continuous simplex-valued section
`a : conv V → Δ_V` of the barycentre map, `Σ_v a_v(M) v = M` (`vertexSection`,
`sum_vertexSection_smul`, `continuousOn_vertexSection`). No triangulation and no polyhedral
lifting theorem are needed: the entropy projection on the vertex simplex is the canonical
continuous choice of barycentric weights.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section VertexSection

variable {J : Type*} [Fintype J] [Nonempty J] (V : Finset (J → ℝ))

omit [Nonempty J] in
/-- The tautological features on the vertex set: `v ↦ v j`. -/
def vertexStat : J → V → ℝ := fun j v ↦ (v : J → ℝ) j

omit [Fintype J] [Nonempty J] in
theorem statPoint_vertexStat (v : V) : statPoint (vertexStat V) v = (v : J → ℝ) := rfl

omit [Fintype J] [Nonempty J] in
theorem range_statPoint_vertexStat : range (statPoint (vertexStat V)) = (V : Set (J → ℝ)) := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    exact v.2
  · intro hy
    exact ⟨⟨y, hy⟩, rfl⟩

omit [Fintype J] [Nonempty J] in
theorem bdd_vertexStat [Finite J] [Nonempty V] (j : J) : Bdd (vertexStat V j) := by
  cases nonempty_fintype J
  exact bdd_finite _ j

omit [Fintype J] [Nonempty J] in
/-- The uniform reference law on the vertex set. -/
noncomputable def vertexUniform : Measure V := vecMeasure fun _ ↦ (Fintype.card V : ℝ)⁻¹

omit [Fintype J] [Nonempty J] in
theorem uniform_mem_stdSimplex [Nonempty V] :
    (fun _ : V ↦ (Fintype.card V : ℝ)⁻¹) ∈ stdSimplex ℝ V := by
  refine ⟨fun _ ↦ by positivity, ?_⟩
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀]
  exact_mod_cast Fintype.card_ne_zero

omit [Fintype J] [Nonempty J] in
instance isProbabilityMeasure_vertexUniform [Finite J] [Nonempty V] :
    IsProbabilityMeasure (vertexUniform V) := by
  cases nonempty_fintype J
  exact isProbabilityMeasure_vecMeasure (uniform_mem_stdSimplex V)

omit [Fintype J] [Nonempty J] in
theorem vertexUniform_singleton_pos [Finite J] [Nonempty V] (v : V) :
    0 < vertexUniform V {v} := by
  cases nonempty_fintype J
  unfold vertexUniform
  rw [vecMeasure_apply_singleton]
  exact ENNReal.ofReal_pos.2 (by positivity)

variable [Nonempty V]

/-- **The vertex section**: the entropy projection on the vertex simplex, a continuous choice of
barycentric coordinates on the polytope `conv V`. -/
noncomputable def vertexSection (M : J → ℝ) : V → ℝ :=
  qStarVec (bdd_vertexStat V) (vertexUniform V) M

theorem genRate_vertexStat_ne_top {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    genRate (vertexUniform V) (vertexStat V) M ≠ ⊤ :=
  genRate_ne_top_of_mem_convexHull (bdd_vertexStat V) (vertexUniform V)
    (vertexUniform_singleton_pos V) (by rwa [range_statPoint_vertexStat])

theorem vertexSection_mem_stdSimplex {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    vertexSection V M ∈ stdSimplex ℝ V :=
  qStarVec_mem_stdSimplex _ _ (genRate_vertexStat_ne_top V hM)

/-- The vertex section is a section of the barycentre map. -/
theorem sum_vertexSection_smul {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    ∑ v : V, vertexSection V M v • (v : J → ℝ) = M := by
  refine Eq.trans ?_ (vecMoment_qStarVec (bdd_vertexStat V) (vertexUniform V)
    (genRate_vertexStat_ne_top V hM))
  rw [vecMoment_eq_sum_smul]
  rfl

/-- **The vertex section is continuous on the polytope.** -/
theorem continuousOn_vertexSection :
    ContinuousOn (vertexSection V) (convexHull ℝ (V : Set (J → ℝ))) := by
  have := continuousOn_qStarVec (bdd_vertexStat V) (vertexUniform V)
    (vertexUniform_singleton_pos V)
  rwa [range_statPoint_vertexStat] at this

theorem vertexSection_nonneg {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (v : V) :
    0 ≤ vertexSection V M v :=
  (vertexSection_mem_stdSimplex V hM).1 v

theorem vertexSection_le_one {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (v : V) :
    vertexSection V M v ≤ 1 := by
  rw [← (vertexSection_mem_stdSimplex V hM).2]
  exact Finset.single_le_sum (fun w _ ↦ vertexSection_nonneg V hM w) (Finset.mem_univ v)

end VertexSection

end Laplace.Multi
