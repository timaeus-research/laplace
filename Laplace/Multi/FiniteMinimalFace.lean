/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FiniteCompletionRetraction

/-!
# The support of the completed family is the minimal face

On a finite alphabet with a full-support reference law, the completed family `q*(M)` charges
exactly the points `x` whose feature vector `S(x)` lies on the minimal face of the moment polytope
containing `M` (Csiszár's support theorem), proved from maximal support alone:

* `exists_absorb`: the completed vector absorbs every vector `b` carried by its support,
  `q*(M) = ε b + (1 − ε) z` with `z` a probability vector and `0 < ε < 1`;
* **`support_absorb`**: a probability vector with the same response as a vector carried by
  `supp q*(M)` is itself carried by `supp q*(M)`;
* `carriedResponses A` is the set of responses of probability vectors carried by `A ⊆ X`;
  `carriedResponses (supp q*(M))` contains `M`, is an extreme subset (a face) of the polytope
  (`isExtreme_carriedResponses_supportSet`), and is contained in every face containing `M`
  (`carriedResponses_supportSet_subset_of_isExtreme`); hence it is **the minimal face**
  `minimalFace M = ⋂ {F face, M ∈ F}` (`minimalFace_eq`);
* **`qStarVec_pos_iff_mem_minimalFace`**: `q*(M) x > 0 ↔ S(x) ∈ minimalFace M`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Delta

variable {X : Type*} [Fintype X] [DecidableEq X] {J : Type*} (S : J → X → ℝ)

/-- The point mass at `x` as a probability vector. -/
def deltaVec (x : X) : X → ℝ := fun y ↦ if y = x then 1 else 0

theorem deltaVec_mem_stdSimplex (x : X) : deltaVec x ∈ stdSimplex ℝ X :=
  ⟨fun y ↦ by unfold deltaVec; split_ifs <;> norm_num, by simp [deltaVec]⟩

theorem vecMoment_deltaVec (x : X) : vecMoment S (deltaVec x) = statPoint S x := by
  funext j
  simp [vecMoment, deltaVec, statPoint, ite_mul]

end Delta

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν]
include hS

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

/-- The support of the completed family at `M`. -/
def supportSet (M : J → ℝ) : Set X := {x | 0 < qStarVec hS ν M x}

omit hS in
variable (S) in
/-- The responses of the probability vectors carried by `A`. -/
def carriedResponses (A : Set X) : Set (J → ℝ) :=
  {m | ∃ b ∈ stdSimplex ℝ X, (∀ x, x ∉ A → b x = 0) ∧ vecMoment S b = m}

omit [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Fintype J] [Nonempty J] hS in
theorem carriedResponses_subset_hull [Finite J] (A : Set X) : carriedResponses S A ⊆ hull := by
  rintro _ ⟨b, hb, -, rfl⟩
  exact vecMoment_mem_convexHull hb

variable (hν : ∀ x, 0 < ν {x})
include hν

omit [Fintype X] in
theorem qStarVec_eq_zero_of_notMem [Finite X] {M : J → ℝ} (hM : M ∈ hull) {x : X}
    (hx : x ∉ supportSet hS ν M) : qStarVec hS ν M x = 0 := by
  cases nonempty_fintype X
  exact le_antisymm (not_lt.1 hx) ((qStarVec_mem_stdSimplex hS ν
    (genRate_ne_top_of_mem_convexHull hS ν hν hM)).1 x)

/-- The completed vector lies in the face polytope of its own support. -/
theorem mem_carriedResponses_supportSet {M : J → ℝ} (hM : M ∈ hull) :
    M ∈ carriedResponses S (supportSet hS ν M) :=
  ⟨qStarVec hS ν M, qStarVec_mem_stdSimplex hS ν (genRate_ne_top_of_mem_convexHull hS ν hν hM),
    fun _ hx ↦ qStarVec_eq_zero_of_notMem hS ν hν hM hx,
    vecMoment_qStarVec hS ν (genRate_ne_top_of_mem_convexHull hS ν hν hM)⟩

/-- **Absorption**: the completed vector absorbs every probability vector carried by its support. -/
theorem exists_absorb {M : J → ℝ} (hM : M ∈ hull) {b : X → ℝ} (hb : b ∈ stdSimplex ℝ X)
    (hbs : ∀ x, x ∉ supportSet hS ν M → b x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ z ∈ stdSimplex ℝ X, qStarVec hS ν M = ε • b + (1 - ε) • z := by
  classical
  have hq := qStarVec_mem_stdSimplex hS ν (genRate_ne_top_of_mem_convexHull hS ν hν hM)
  obtain ⟨q, hqdef⟩ : ∃ q : X → ℝ, q = qStarVec hS ν M := ⟨_, rfl⟩
  rw [← hqdef] at hq ⊢
  have hsupp : ∀ x, x ∉ supportSet hS ν M ↔ ¬ 0 < q x := fun x ↦ by
    rw [hqdef]
    exact Iff.rfl
  -- the positive coordinates
  set T := Finset.univ.filter fun x ↦ 0 < q x with hT
  have hTne : T.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : ∑ x, q x = 0 := Finset.sum_eq_zero fun x _ ↦ by
      have hx : x ∉ T := by rw [hne]; exact Finset.notMem_empty x
      rw [hT, Finset.mem_filter] at hx
      exact le_antisymm (not_lt.1 fun h ↦ hx ⟨Finset.mem_univ x, h⟩) (hq.1 x)
    linarith [hq.2]
  obtain ⟨x₀, hx₀T, hmin⟩ := T.exists_min_image q hTne
  have hx₀ : 0 < q x₀ := (Finset.mem_filter.1 hx₀T).2
  have hqle : ∀ x, q x ≤ 1 := fun x ↦ by
    have := Finset.single_le_sum (f := q) (fun y _ ↦ hq.1 y) (Finset.mem_univ x)
    linarith [hq.2]
  have hble : ∀ x, b x ≤ 1 := fun x ↦ by
    have := Finset.single_le_sum (f := b) (fun y _ ↦ hb.1 y) (Finset.mem_univ x)
    linarith [hb.2]
  refine ⟨q x₀ / 2, by positivity, by linarith [hqle x₀], (1 - q x₀ / 2)⁻¹ • (q - (q x₀ / 2) • b),
    ⟨fun x ↦ ?_, ?_⟩, ?_⟩
  · -- nonnegativity of the complementary vector
    have h1 : 0 < 1 - q x₀ / 2 := by linarith [hqle x₀]
    refine mul_nonneg (inv_nonneg.2 h1.le) ?_
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx : 0 < q x
    · have hxT : x ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩
      have := hmin x hxT
      nlinarith [hble x, hb.1 x]
    · have h0 : q x = 0 := le_antisymm (not_lt.1 hx) (hq.1 x)
      rw [h0, hbs x ((hsupp x).2 hx)]
      simp
  · -- the complementary vector has unit mass
    have h1 : (1 - q x₀ / 2) ≠ 0 := by linarith [hqle x₀]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib,
      hq.2, hb.2]
    field_simp
    exact div_self (by linarith [hqle x₀])
  · -- the absorption identity
    have h1 : (1 - q x₀ / 2) ≠ 0 := by linarith [hqle x₀]
    rw [smul_smul, mul_inv_cancel₀ h1, one_smul]
    abel

/-- **Support absorption**: a probability vector with the same response as a vector carried by
`supp q*(M)` is itself carried by `supp q*(M)`. -/
theorem support_absorb {M : J → ℝ} (hM : M ∈ hull) {b : X → ℝ} (hb : b ∈ stdSimplex ℝ X)
    (hbs : ∀ x, x ∉ supportSet hS ν M → b x = 0) {w : X → ℝ} (hw : w ∈ stdSimplex ℝ X)
    (hwb : vecMoment S w = vecMoment S b) {x : X} (hx : 0 < w x) : 0 < qStarVec hS ν M x := by
  have hfin := genRate_ne_top_of_mem_convexHull hS ν hν hM
  obtain ⟨ε, hε0, hε1, z, hz, hqz⟩ := exists_absorb hS ν hν hM hb hbs
  have hr : ε • w + (1 - ε) • z ∈ stdSimplex ℝ X :=
    convex_stdSimplex ℝ X hw hz hε0.le (by linarith) (by ring)
  have hrM : vecMoment S (ε • w + (1 - ε) • z) = M := by
    rw [vecMoment_add, vecMoment_smul, vecMoment_smul, hwb, ← vecMoment_smul, ← vecMoment_smul,
      ← vecMoment_add, ← hqz, vecMoment_qStarVec hS ν hfin]
  have hrx : 0 < (ε • w + (1 - ε) • z) x := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hz.1 x
    nlinarith
  have hP := (responseProjection_spec hS ν hfin).1
  exact ENNReal.toReal_pos (responseProjection_singleton_pos_of_vec hS ν hν hfin hr hrM hrx).ne'
    (measure_ne_top _ _)

/-- **The face polytope of the support is a face** (an extreme subset) of the moment polytope. -/
theorem isExtreme_carriedResponses_supportSet {M : J → ℝ} (hM : M ∈ hull) :
    IsExtreme ℝ hull (carriedResponses S (supportSet hS ν M)) := by
  refine ⟨carriedResponses_subset_hull (S := S) _, fun u hu v hv y hy hseg ↦ ?_⟩
  obtain ⟨b, hb, hbs, rfl⟩ := hy
  obtain ⟨a, c, ha, hc, hac, hacy⟩ := hseg
  obtain ⟨u', hu', rfl⟩ := exists_stdSimplex_vecMoment_eq hu
  obtain ⟨v', hv', rfl⟩ := exists_stdSimplex_vecMoment_eq hv
  have hw : a • u' + c • v' ∈ stdSimplex ℝ X := convex_stdSimplex ℝ X hu' hv' ha.le hc.le hac
  have hwb : vecMoment S (a • u' + c • v') = vecMoment S b := by
    rw [vecMoment_add, vecMoment_smul, vecMoment_smul, hacy]
  refine ⟨u', hu', fun x hx ↦ ?_, rfl⟩
  by_contra hux
  have hux' : 0 < u' x := lt_of_le_of_ne (hu'.1 x) (Ne.symm hux)
  have hwx : 0 < (a • u' + c • v') x := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hv'.1 x
    nlinarith
  exact hx (support_absorb hS ν hν hM hb hbs hw hwb hwx)

/-- The face polytope of the support is contained in every face containing `M`. -/
theorem carriedResponses_supportSet_subset_of_isExtreme {M : J → ℝ} (hM : M ∈ hull)
    {F : Set (J → ℝ)} (hF : IsExtreme ℝ hull F) (hMF : M ∈ F) :
    carriedResponses S (supportSet hS ν M) ⊆ F := by
  rintro _ ⟨b, hb, hbs, rfl⟩
  obtain ⟨ε, hε0, hε1, z, hz, hqz⟩ := exists_absorb hS ν hν hM hb hbs
  have hfin := genRate_ne_top_of_mem_convexHull hS ν hν hM
  have hMseg : M ∈ openSegment ℝ (vecMoment S b) (vecMoment S z) := by
    refine ⟨ε, 1 - ε, hε0, by linarith, by ring, ?_⟩
    rw [← vecMoment_smul, ← vecMoment_smul, ← vecMoment_add, ← hqz, vecMoment_qStarVec hS ν hfin]
  exact hF.left_mem_of_mem_openSegment (vecMoment_mem_convexHull hb) (vecMoment_mem_convexHull hz)
    hMF hMseg

omit hν in
variable (S) in
/-- The minimal face of the moment polytope containing `M`: the intersection of all faces
containing `M`. -/
def minimalFace (M : J → ℝ) : Set (J → ℝ) := ⋂₀ {F | IsExtreme ℝ hull F ∧ M ∈ F}

/-- **The minimal face is the face polytope of the support of the completed family.** -/
theorem minimalFace_eq {M : J → ℝ} (hM : M ∈ hull) :
    minimalFace S M = carriedResponses S (supportSet hS ν M) := by
  refine subset_antisymm (sInter_subset_of_mem ⟨isExtreme_carriedResponses_supportSet hS ν hν hM,
    mem_carriedResponses_supportSet hS ν hν hM⟩) (subset_sInter fun F ⟨hF, hMF⟩ ↦
    carriedResponses_supportSet_subset_of_isExtreme hS ν hν hM hF hMF)

omit [Fintype X] [Fintype J] in
theorem isExtreme_minimalFace [Finite X] [Finite J] {M : J → ℝ} (hM : M ∈ hull) :
    IsExtreme ℝ hull (minimalFace S M) := by
  cases nonempty_fintype X
  cases nonempty_fintype J
  rw [minimalFace_eq hS ν hν hM]
  exact isExtreme_carriedResponses_supportSet hS ν hν hM

omit [Fintype X] [Fintype J] in
theorem mem_minimalFace [Finite X] [Finite J] {M : J → ℝ} (hM : M ∈ hull) :
    M ∈ minimalFace S M := by
  cases nonempty_fintype X
  cases nonempty_fintype J
  rw [minimalFace_eq hS ν hν hM]
  exact mem_carriedResponses_supportSet hS ν hν hM

omit [Fintype X] in
/-- **Csiszár's support theorem**: the completed family charges `x` exactly when `S(x)` lies on the
minimal face of the polytope containing `M`. -/
theorem qStarVec_pos_iff_mem_minimalFace [Finite X] {M : J → ℝ} (hM : M ∈ hull) (x : X) :
    0 < qStarVec hS ν M x ↔ statPoint S x ∈ minimalFace S M := by
  classical
  cases nonempty_fintype X
  rw [minimalFace_eq hS ν hν hM]
  constructor
  · intro hx
    refine ⟨deltaVec x, deltaVec_mem_stdSimplex x, fun y hy ↦ ?_, vecMoment_deltaVec S x⟩
    have hyx : y ≠ x := fun h ↦ hy (h ▸ hx)
    simp [deltaVec, hyx]
  · rintro ⟨b, hb, hbs, hbx⟩
    refine support_absorb hS ν hν hM hb hbs (deltaVec_mem_stdSimplex x)
      (by rw [vecMoment_deltaVec S x, hbx]) (w := deltaVec x) ?_
    simp [deltaVec]

end Laplace.Multi
