/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseFibreDeformation
import Mathlib.Topology.Homotopy.Equiv

/-!
# The response map as a topological quotient and a homotopy equivalence

The response map `Φ : DataLaw → W` is a continuous surjection with the continuous section
`θ ↦ p_θ`, hence a **quotient map** (`isQuotientMap_lawResponse`): the direction space `W` carries
exactly the quotient topology of the space of data laws by the response fibres, and the quotient
`DataLaw / ker Φ` is homeomorphic to `W` (`responseQuotientHomeomorph`).

The mixture deformation is a homotopy from the identity to the retraction `p ↦ p_{Φ(p)}` onto the
family (`deformHomotopy`), through response-preserving maps (`deformHomotopyWith`) and relative to
the family (`deformHomotopyRel`). Consequently the response map is a **homotopy equivalence**
`DataLaw ≃ₕ W` with homotopy inverse the family (`responseHomotopyEquiv`): the space of data laws
retracts onto the family along the mixture segments, the response is the projection, and every
fibre is contractible (`contractibleSpace_responseFibre`). This is the topological content of the
response map: the data manifold is, up to homotopy, the family of laws it is compared against.
-/

open MeasureTheory Filter Topology Set unitInterval
open scoped ContinuousMap

namespace Laplace.Multi

section Quotient

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The response map is onto the direction space. -/
theorem surjective_lawResponse : Function.Surjective (lawResponse hS ν) :=
  fun θ ↦ ⟨modelLaw hS ν θ, lawResponse_modelLaw hS ν θ⟩

/-- The family is a right inverse of the response map. -/
theorem rightInverse_modelLaw : Function.RightInverse (modelLaw hS ν) (lawResponse hS ν) :=
  lawResponse_modelLaw hS ν

/-- **The response map is a quotient map**: `W` carries the quotient topology of the space of data
laws by the response fibres. -/
theorem isQuotientMap_lawResponse : Topology.IsQuotientMap (lawResponse hS ν) :=
  Topology.IsQuotientMap.of_inverse (continuous_modelLaw hS ν) (continuous_lawResponse hS ν)
    (lawResponse_modelLaw hS ν)

/-- A map out of `W` is continuous iff its composite with the response is. -/
theorem continuous_iff_comp_lawResponse {Z : Type*} [TopologicalSpace Z] {f : 𝕍 → Z} :
    Continuous f ↔ Continuous (f ∘ lawResponse hS ν) :=
  (isQuotientMap_lawResponse hS ν).continuous_iff

/-- **The quotient of the space of data laws by the response fibres is homeomorphic to the
direction space.** -/
noncomputable def responseQuotientHomeomorph :
    Quotient (Setoid.ker (lawResponse hS ν)) ≃ₜ 𝕍 where
  toEquiv := Setoid.quotientKerEquivOfRightInverse (lawResponse hS ν) (modelLaw hS ν)
    (lawResponse_modelLaw hS ν)
  continuous_toFun := by
    exact (continuous_lawResponse hS ν).quotient_lift fun _ _ h ↦ h
  continuous_invFun := by
    exact continuous_quotient_mk'.comp (continuous_modelLaw hS ν)

theorem responseQuotientHomeomorph_mk (p : DataLaw ν) :
    responseQuotientHomeomorph hS ν (Quotient.mk'' p) = lawResponse hS ν p := by
  rfl

/-- The response map as a continuous map. -/
noncomputable def lawResponseCM : C(DataLaw ν, 𝕍) := ⟨lawResponse hS ν, continuous_lawResponse hS ν⟩

/-- The family as a continuous map. -/
noncomputable def modelLawCM : C(𝕍, DataLaw ν) := ⟨modelLaw hS ν, continuous_modelLaw hS ν⟩

/-- **The mixture deformation as a homotopy** from the identity to the retraction `p ↦ p_{Φ(p)}`
onto the family. -/
noncomputable def deformHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id (DataLaw ν))
      ((modelLawCM hS ν).comp (lawResponseCM hS ν)) where
  toFun q := deform hS ν q.1 q.2
  continuous_toFun := continuous_deform hS ν
  map_zero_left := deform_zero hS ν
  map_one_left := deform_one hS ν

/-- The deformation is a homotopy **through response-preserving maps**. -/
noncomputable def deformHomotopyWith :
    ContinuousMap.HomotopyWith (ContinuousMap.id (DataLaw ν))
      ((modelLawCM hS ν).comp (lawResponseCM hS ν))
      (fun f ↦ ∀ p, lawResponse hS ν (f p) = lawResponse hS ν p) where
  toHomotopy := deformHomotopy hS ν
  prop' t p := lawResponse_deform hS ν t p

/-- The deformation is a homotopy **relative to the family**: a strong deformation retraction. -/
noncomputable def deformHomotopyRel :
    ContinuousMap.HomotopyRel (ContinuousMap.id (DataLaw ν))
      ((modelLawCM hS ν).comp (lawResponseCM hS ν)) (Set.range (modelLaw hS ν)) where
  toHomotopy := deformHomotopy hS ν
  prop' t := by
    rintro _ ⟨θ, rfl⟩
    exact deform_modelLaw hS ν t θ

/-- **The response map is a homotopy equivalence** between the space of data laws and the direction
space, with homotopy inverse the family. -/
noncomputable def responseHomotopyEquiv : DataLaw ν ≃ₕ 𝕍 where
  toFun := lawResponseCM hS ν
  invFun := modelLawCM hS ν
  left_inv := ⟨(deformHomotopy hS ν).symm⟩
  right_inv := by
    have e : (lawResponseCM hS ν).comp (modelLawCM hS ν) = ContinuousMap.id 𝕍 :=
      ContinuousMap.ext (lawResponse_modelLaw hS ν)
    rw [e]

/-- The quotient by the response fibres is contractible (it is the direction space). -/
theorem contractibleSpace_responseQuotient :
    ContractibleSpace (Quotient (Setoid.ker (lawResponse hS ν))) :=
  (responseQuotientHomeomorph hS ν).contractibleSpace_iff.2 inferInstance

end Quotient

end Laplace.Multi
