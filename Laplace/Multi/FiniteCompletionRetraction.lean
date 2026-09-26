/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FiniteCompletionContinuity

/-!
# The completed family as a retract of the simplex

On a finite alphabet with a full-support reference law:

* `completedFamily = q*(conv S(X))` is the completed family of probability vectors, a compact set
  (`isCompact_completedFamily`) homeomorphic to the moment polytope through the response map
  (`completedHomeomorph`: `q*` and `p ↦ E_p S` are mutually inverse and continuous);
* `retract p = q*(E_p S)` is a continuous, moment-preserving, idempotent retraction of the simplex
  onto the completed family (`continuousOn_retract`, `vecMoment_retract`, `retract_idempotent`,
  `retract_eq_self_iff`);
* `deformation t p = (1 − t) p + t · retract p` is a **strong deformation retraction** of the
  simplex onto the completed family, fibrewise moment-preserving: it is continuous, `H_0 = id`,
  `H_1 = retract`, it fixes the completed family pointwise, keeps the response of `p`, and
  `retract ∘ H_t = retract` (`retract_deformation`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Linear

variable {X : Type*} [Fintype X] {J : Type*} (S : J → X → ℝ)

theorem vecMoment_add (p q : X → ℝ) : vecMoment S (p + q) = vecMoment S p + vecMoment S q := by
  funext j
  simp only [vecMoment, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem vecMoment_smul (c : ℝ) (p : X → ℝ) : vecMoment S (c • p) = c • vecMoment S p := by
  funext j
  simp only [vecMoment, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

end Linear

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν]
include hS

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

/-- The completed family of probability vectors, `q*(conv S(X))`. -/
def completedFamily : Set (X → ℝ) := qStarVec hS ν '' hull

/-- The retraction `p ↦ q*(E_p S)` of the simplex onto the completed family. -/
noncomputable def retract (p : X → ℝ) : X → ℝ := qStarVec hS ν (vecMoment S p)

variable (hν : ∀ x, 0 < ν {x})
include hν

theorem retract_mem_stdSimplex {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X) :
    retract hS ν p ∈ stdSimplex ℝ X :=
  qStarVec_mem_stdSimplex hS ν
    (genRate_ne_top_of_mem_convexHull hS ν hν (vecMoment_mem_convexHull hp))

/-- The retraction preserves the response. -/
theorem vecMoment_retract {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X) :
    vecMoment S (retract hS ν p) = vecMoment S p :=
  vecMoment_qStarVec hS ν (genRate_ne_top_of_mem_convexHull hS ν hν (vecMoment_mem_convexHull hp))

theorem retract_qStarVec {M : J → ℝ} (hM : M ∈ hull) :
    retract hS ν (qStarVec hS ν M) = qStarVec hS ν M := by
  unfold retract
  rw [vecMoment_qStarVec hS ν (genRate_ne_top_of_mem_convexHull hS ν hν hM)]

omit [MeasurableSingletonClass X] [IsProbabilityMeasure ν] hν in
theorem retract_mem_completedFamily {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X) :
    retract hS ν p ∈ completedFamily hS ν :=
  ⟨vecMoment S p, vecMoment_mem_convexHull hp, rfl⟩

theorem completedFamily_subset_stdSimplex : completedFamily hS ν ⊆ stdSimplex ℝ X := by
  rintro _ ⟨M, hM, rfl⟩
  exact qStarVec_mem_stdSimplex hS ν (genRate_ne_top_of_mem_convexHull hS ν hν hM)

theorem retract_of_mem_completedFamily {p : X → ℝ} (hp : p ∈ completedFamily hS ν) :
    retract hS ν p = p := by
  obtain ⟨M, hM, rfl⟩ := hp
  exact retract_qStarVec hS ν hν hM

theorem retract_idempotent {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X) :
    retract hS ν (retract hS ν p) = retract hS ν p :=
  retract_of_mem_completedFamily hS ν hν (retract_mem_completedFamily hS ν hp)

/-- The completed family is exactly the fixed-point set of the retraction. -/
theorem retract_eq_self_iff {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X) :
    retract hS ν p = p ↔ p ∈ completedFamily hS ν :=
  ⟨fun h ↦ h ▸ retract_mem_completedFamily hS ν hp, retract_of_mem_completedFamily hS ν hν⟩

/-- **The retraction is continuous on the simplex.** -/
theorem continuousOn_retract : ContinuousOn (retract hS ν) (stdSimplex ℝ X) :=
  (continuousOn_qStarVec hS ν hν).comp (continuous_vecMoment S).continuousOn
    fun _ hp ↦ vecMoment_mem_convexHull hp

omit [Fintype X] in
/-- The completed family is compact. -/
theorem isCompact_completedFamily [Finite X] : IsCompact (completedFamily hS ν) := by
  cases nonempty_fintype X
  exact ((finite_range (statPoint S)).isCompact_convexHull (𝕜 := ℝ)).image_of_continuousOn
    (continuousOn_qStarVec hS ν hν)

theorem vecMoment_mem_hull_of_mem_completedFamily {p : X → ℝ} (hp : p ∈ completedFamily hS ν) :
    vecMoment S p ∈ hull := by
  obtain ⟨M, hM, rfl⟩ := hp
  rwa [vecMoment_qStarVec hS ν (genRate_ne_top_of_mem_convexHull hS ν hν hM)]

/-- **The completed family is homeomorphic to the moment polytope** through the response map, with
inverse `q*`. -/
noncomputable def completedHomeomorph : hull ≃ₜ completedFamily hS ν where
  toFun M := ⟨qStarVec hS ν M, M, M.2, rfl⟩
  invFun p := ⟨vecMoment S p, vecMoment_mem_hull_of_mem_completedFamily hS ν hν p.2⟩
  left_inv M := Subtype.ext
    (vecMoment_qStarVec hS ν (genRate_ne_top_of_mem_convexHull hS ν hν M.2))
  right_inv p := Subtype.ext (retract_of_mem_completedFamily hS ν hν p.2)
  continuous_toFun :=
    ((continuousOn_qStarVec hS ν hν).comp_continuous continuous_subtype_val
      fun M ↦ M.2).subtype_mk _
  continuous_invFun := ((continuous_vecMoment S).comp continuous_subtype_val).subtype_mk _

/-- The straight-line deformation `H_t(p) = (1 − t) p + t · retract p`. -/
noncomputable def deformation (t : ℝ) (p : X → ℝ) : X → ℝ := (1 - t) • p + t • retract hS ν p

omit [MeasurableSingletonClass X] [IsProbabilityMeasure ν] hν in
theorem deformation_zero (p : X → ℝ) : deformation hS ν 0 p = p := by
  simp [deformation]

omit [MeasurableSingletonClass X] [IsProbabilityMeasure ν] hν in
theorem deformation_one (p : X → ℝ) : deformation hS ν 1 p = retract hS ν p := by
  simp [deformation]

theorem deformation_mem_stdSimplex {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {p : X → ℝ}
    (hp : p ∈ stdSimplex ℝ X) : deformation hS ν t p ∈ stdSimplex ℝ X :=
  convex_stdSimplex ℝ X hp (retract_mem_stdSimplex hS ν hν hp) (by linarith) ht0 (by ring)

/-- The deformation preserves the response at every time. -/
theorem vecMoment_deformation (t : ℝ) {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X) :
    vecMoment S (deformation hS ν t p) = vecMoment S p := by
  unfold deformation
  rw [vecMoment_add, vecMoment_smul, vecMoment_smul, vecMoment_retract hS ν hν hp, ← add_smul]
  simp

/-- **The retraction is constant along the deformation**: `retract ∘ H_t = retract`. -/
theorem retract_deformation (t : ℝ) {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X) :
    retract hS ν (deformation hS ν t p) = retract hS ν p := by
  unfold retract
  rw [vecMoment_deformation hS ν hν t hp]

/-- The deformation fixes the completed family pointwise. -/
theorem deformation_of_mem_completedFamily (t : ℝ) {p : X → ℝ} (hp : p ∈ completedFamily hS ν) :
    deformation hS ν t p = p := by
  unfold deformation
  rw [retract_of_mem_completedFamily hS ν hν hp, ← add_smul]
  simp

/-- **The deformation is jointly continuous** in time and in the probability vector. -/
theorem continuousOn_deformation :
    ContinuousOn (fun z : ℝ × (X → ℝ) ↦ deformation hS ν z.1 z.2) (univ ×ˢ stdSimplex ℝ X) := by
  have hr : ContinuousOn (fun z : ℝ × (X → ℝ) ↦ retract hS ν z.2) (univ ×ˢ stdSimplex ℝ X) :=
    (continuousOn_retract hS ν hν).comp continuousOn_snd fun z hz ↦ hz.2
  exact ((continuousOn_const.sub continuousOn_fst).smul continuousOn_snd).add
    (continuousOn_fst.smul hr)

end Laplace.Multi
