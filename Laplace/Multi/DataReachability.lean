/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.DataMixture
import Laplace.Multi.MeanMapEmbedding
import Laplace.Multi.TemperatureSlice

/-!
# Reachability by actual data distributions

Which responses does the data manifold actually visit? Let a finite family of data distributions
`ν j` have population losses affine in the features, `L_{ν j} = L₀ + a_j·R + k_j`. Mixing them with
weights `w` in the standard simplex gives the loss `L₀ + (∑ w_j a_j)·R + ∑ w_j k_j`
(`dataLoss_mixFin`), whose posterior is the family point `a_w = ∑ w_j a_j`
(`priorExp_mixFin`). Hence at temperature `t` the reachable responses are exactly

  `reachableResponse = m_t '' conv{a_j}`   (`reachableResponse_eq_image_convexHull`),

a compact subset of the interior of the moment body (`isCompact_reachableResponse`,
`reachableResponse_subset_interior`), and a response `M` is reachable iff its unique preimage
lies
in the coefficient polytope (`mem_reachableResponse_iff`). The faces of the coefficient polytope
`conv{a_j}` map to the boundary strata of the reachable set: the "walls" of the actual data
manifold.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]
  {Z : Type*} [MeasurableSpace Z] {J : Type*} [Fintype J]

/-- The finite mixture `∑ⱼ wⱼ νⱼ` of data distributions. -/
noncomputable def mixFin (ν : J → Measure Z) (w : J → ℝ) : Measure Z :=
  ∑ j, ENNReal.ofReal (w j) • ν j

/-- The coefficient polytope `{∑ⱼ wⱼ aⱼ : w ∈ Δ}`. -/
def reachableCoeff (a : J → ι → ℝ) : Set (ι → ℝ) :=
  (fun w : J → ℝ ↦ ∑ j, w j • a j) '' stdSimplex ℝ J

/-- The responses reachable by mixtures of the given data distributions at temperature `t`. -/
noncomputable def reachableResponse (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (a : J → ι → ℝ) : Set (ι → ℝ) :=
  meanMap μ π L₀ R t '' reachableCoeff a

omit [MeasurableSpace X] [Fintype ι] [MeasurableSpace Z] in
/-- The coefficient polytope is the convex hull of the coefficients. -/
theorem reachableCoeff_eq_convexHull (a : J → ι → ℝ) :
    reachableCoeff a = convexHull ℝ (Set.range a) := by
  classical
  let f : (J → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun w ↦ ∑ j, w j • a j
      map_add' := fun w₁ w₂ ↦ by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c w ↦ by simp [Finset.smul_sum, smul_smul] }
  have hbasis : (fun j : J ↦ (Pi.single j (1 : ℝ) : J → ℝ)) = fun j i ↦ if j = i then 1 else 0 := by
    funext j i
    simp [Pi.single_apply, eq_comm]
  have h1 : reachableCoeff a = f '' stdSimplex ℝ J := rfl
  rw [h1, ← convexHull_basis_eq_stdSimplex, LinearMap.image_convexHull, ← Set.range_comp]
  congr 2
  funext j
  simp only [Function.comp, f, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk; simp [Ne.symm hk]
  · intro h; exact absurd (Finset.mem_univ j) h

omit [MeasurableSpace X] [Fintype ι] [MeasurableSpace Z] in
theorem isCompact_reachableCoeff (a : J → ι → ℝ) : IsCompact (reachableCoeff a) :=
  (isCompact_stdSimplex ℝ J).image (by fun_prop)

omit [MeasurableSpace X] [Fintype ι] [MeasurableSpace Z] in
theorem mem_reachableCoeff_of_mem_stdSimplex (a : J → ι → ℝ) {w : J → ℝ}
    (hw : w ∈ stdSimplex ℝ J) : (∑ j, w j • a j) ∈ reachableCoeff a :=
  ⟨w, hw, rfl⟩

section Mixture

variable {ν : J → Measure Z} [∀ j, IsProbabilityMeasure (ν j)] {ℓ : X → Z → ℝ}
  (hℓ : Measurable (Function.uncurry ℓ)) {M : ℝ} (hM : ∀ x z, |ℓ x z| ≤ M)
include hℓ hM

omit [Fintype J] in
theorem integrable_mixFin_partial {w : J → ℝ} (x : X) (s : Finset J) :
    Integrable (ℓ x) (∑ j ∈ s, ENNReal.ofReal (w j) • ν j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact ((integrable_ℓ_right hℓ hM (ν j) x).smul_measure ENNReal.ofReal_ne_top).add_measure ih

/-- The population loss of a finite mixture is the mixture of the population losses. -/
theorem dataLoss_mixFin {w : J → ℝ} (hw : ∀ j, 0 ≤ w j) (x : X) :
    dataLoss ℓ (mixFin ν w) x = ∑ j, w j * dataLoss ℓ (ν j) x := by
  classical
  unfold dataLoss mixFin
  have key : ∀ (s : Finset J), (∫ z, ℓ x z ∂(∑ j ∈ s, ENNReal.ofReal (w j) • ν j)) =
      ∑ j ∈ s, w j * ∫ z, ℓ x z ∂(ν j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, integral_add_measure
        ((integrable_ℓ_right hℓ hM (ν j) x).smul_measure ENNReal.ofReal_ne_top)
        (integrable_mixFin_partial hℓ hM x s), integral_smul_measure,
        ENNReal.toReal_ofReal (hw j), smul_eq_mul, ih]
  exact key Finset.univ

/-- A mixture of data distributions with affine losses `L₀ + aⱼ·R + kⱼ` has loss
`L₀ + (∑ wⱼ aⱼ)·R + ∑ wⱼ kⱼ`. -/
theorem dataLoss_mixFin_eq_affLoss {L₀ : X → ℝ} {R : ι → X → ℝ} {a : J → ι → ℝ} {k : J → ℝ}
    (hrep : ∀ j, dataLoss ℓ (ν j) = fun x ↦ affLoss L₀ R (a j) x + k j) {w : J → ℝ}
    (hw : w ∈ stdSimplex ℝ J) :
    dataLoss ℓ (mixFin ν w) = fun x ↦ (∑ j, w j * k j) + affLoss L₀ R (∑ j, w j • a j) x := by
  funext x
  rw [dataLoss_mixFin hℓ hM hw.1 x]
  simp only [hrep]
  have hsum : ∑ j, w j = 1 := hw.2
  simp only [affLoss, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_mul, hsum, one_mul, Finset.sum_comm]
  have e : ∀ y, ∑ j, w j * (a j y * R y x) = ∑ j, w j * a j y * R y x := fun y ↦
    Finset.sum_congr rfl fun j _ ↦ by ring
  simp only [e]
  ring

/-- **The posterior of a mixture of data distributions is the family point `∑ wⱼ aⱼ`.** -/
theorem priorExp_mixFin {π L₀ : X → ℝ} {R : ι → X → ℝ} {a : J → ι → ℝ} {k : J → ℝ}
    (hrep : ∀ j, dataLoss ℓ (ν j) = fun x ↦ affLoss L₀ R (a j) x + k j) {w : J → ℝ}
    (hw : w ∈ stdSimplex ℝ J) (φ : X → ℝ) (t : ℝ) :
    priorExp μ π (dataLoss ℓ (mixFin ν w)) φ t =
      priorExp μ π (affLoss L₀ R (∑ j, w j • a j)) φ t := by
  rw [dataLoss_mixFin_eq_affLoss hℓ hM hrep hw, priorExp_const_add']

end Mixture

section Response

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR ht in
theorem reachableResponse_eq_image_convexHull (a : J → ι → ℝ) :
    reachableResponse μ π L₀ R t a = meanMap μ π L₀ R t '' convexHull ℝ (Set.range a) := by
  rw [reachableResponse, reachableCoeff_eq_convexHull]

/-- **The reachable responses form a compact set.** -/
theorem isCompact_reachableResponse (a : J → ι → ℝ) : IsCompact (reachableResponse μ π L₀ R t a) :=
  (isCompact_reachableCoeff a).image
    (continuous_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht)

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR ht in
theorem reachableResponse_subset_range (a : J → ι → ℝ) :
    reachableResponse μ π L₀ R t a ⊆ Set.range (meanMap μ π L₀ R t) :=
  Set.image_subset_range _ _

variable (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
include hnd

/-- The reachable responses lie in the interior of the moment body. -/
theorem reachableResponse_subset_interior [Nonempty ι] (a : J → ι → ℝ) :
    reachableResponse μ π L₀ R t a ⊆ interior (momentBody μ π R) := by
  rw [← range_meanMap_slice hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd]
  exact Set.image_subset_range _ _

/-- **Reachability criterion**: `M` is reachable iff it is a response whose data point lies in the
coefficient polytope. -/
theorem mem_reachableResponse_iff (a : J → ι → ℝ) (M : ι → ℝ) :
    M ∈ reachableResponse μ π L₀ R t a ↔
      M ∈ Set.range (meanMap μ π L₀ R t) ∧
        Function.invFun (meanMap μ π L₀ R t) M ∈ reachableCoeff a := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨⟨b, rfl⟩, ?_⟩
    rw [invFun_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd]
    exact hb
  · rintro ⟨hM, hb⟩
    exact ⟨_, hb, meanMap_invFun hM⟩

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd in
/-- The response of a mixture of actual data distributions is reachable. -/
theorem response_mixFin_mem {ν : J → Measure Z} [∀ j, IsProbabilityMeasure (ν j)]
    {ℓ : X → Z → ℝ} (hℓ : Measurable (Function.uncurry ℓ)) {M : ℝ} (hM : ∀ x z, |ℓ x z| ≤ M)
    {a : J → ι → ℝ} {k : J → ℝ}
    (hrep : ∀ j, dataLoss ℓ (ν j) = fun x ↦ affLoss L₀ R (a j) x + k j) {w : J → ℝ}
    (hw : w ∈ stdSimplex ℝ J) :
    (fun i ↦ priorExp μ π (dataLoss ℓ (mixFin ν w)) (R i) t) ∈ reachableResponse μ π L₀ R t a := by
  refine ⟨∑ j, w j • a j, mem_reachableCoeff_of_mem_stdSimplex a hw, ?_⟩
  funext i
  unfold meanMap
  exact (priorExp_mixFin hℓ hM hrep hw (R i) t).symm

/-- **Reachable responses are a proper subset of the response space**: a compact set cannot
exhaust the open range of the mean map (`ι` nonempty). -/
theorem reachableResponse_ne_range [Nonempty ι] (a : J → ι → ℝ) :
    reachableResponse μ π L₀ R t a ≠ Set.range (meanMap μ π L₀ R t) := by
  intro h
  have hcpt := isCompact_reachableResponse hπm hπi hπ hπpos hL₀m hL₀ hR ht a
  rw [h] at hcpt
  have hopen := isOpen_range_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd
  have hclopen : IsClopen (Set.range (meanMap μ π L₀ R t)) := ⟨hcpt.isClosed, hopen⟩
  exact hcpt.ne_univ (hclopen.eq_univ (Set.range_nonempty _))

end Response

end Laplace.Multi
