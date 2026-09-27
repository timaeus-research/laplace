/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseFisherCurvatureSign

/-!
# Saturated families have constant Fisher curvature `¼`

A family is **saturated at `θ`** when the centred scores `f_u = ⟨u, S⟩ − E_θ⟨u,S⟩`, `u ∈ W`, are
closed under products up to constants: for all `u, v` there is `c ∈ W` with
`f_u f_v − G_θ(u,v) = f_c` (`P_θ`-a.e.). This is the case of the full simplex of laws on a finite
set with the features an affine basis (every function on the set is an affine function of the
features), and more generally of any family whose scores exhaust the centred functions.

* `mChristoffel_eq_neg_of_saturated`: the m-Christoffel vector `C_θ(u,v)` is `−c`: its score is
  `−(f_u f_v − G(u,v))`, the negative centred product.
* `fisherInner_mChristoffel_mChristoffel_of_saturated`:
  `G(C(u,v), C(x,y)) = E_θ[f_u f_v f_x f_y] − G(u,v) G(x,y)`.
* `fisherInner_alphaCurvature_of_saturated`: **the constant-curvature tensor**
  `G(R^α(u,v)w, x) = ((1 − α²)/4) (G(u,x) G(v,w) − G(v,x) G(u,w))` — the fourth moments cancel.
* `fisherSectional_of_saturated`: every nondegenerate plane has Fisher sectional curvature `1/4`:
  the Fisher geometry of a saturated family is the round sphere of radius `2` (the Hellinger sphere
  `√p`), as it should be.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Simplex

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

omit hS in
variable (S) in
/-- The centred score of the direction `u` at `θ`: `f_u = ⟨u,S⟩ − E_θ⟨u,S⟩`. -/
noncomputable def modelScore (θ u : 𝕍) : X → ℝ :=
  fun x ↦ dirLoss S (u : J → ℝ) x - ∫ y, dirLoss S (u : J → ℝ) y ∂Pfam (θ : J → ℝ)

omit hS in
variable (S) in
/-- **Saturation at `θ`**: centred scores are closed under products up to constants. -/
def SaturatedAt (θ : 𝕍) : Prop :=
  ∀ u v : 𝕍, ∃ c : 𝕍, ∀ᵐ x ∂Pfam (θ : J → ℝ),
    modelScore S ν θ u x * modelScore S ν θ v x - G θ u v = modelScore S ν θ c x

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem bdd_modelScore (θ u : 𝕍) : Bdd (modelScore S ν θ u) :=
  (bdd_dirLoss hS (u : J → ℝ)).sub (Bdd.const _)

omit [Nonempty J] in
/-- Centred scores integrate to zero. -/
theorem integral_modelScore (θ u : 𝕍) : ∫ x, modelScore S ν θ u x ∂Pfam (θ : J → ℝ) = 0 := by
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  unfold modelScore
  rw [integral_sub (integrable_of_bdd_prob _ (bdd_dirLoss hS _)) (integrable_const _),
    integral_const, probReal_univ, one_smul, sub_self]

omit [Nonempty J] in
/-- The Fisher form is the second moment of the centred scores. -/
theorem fisherInner_eq_integral_modelScore (θ u v : 𝕍) :
    G θ u v = ∫ x, modelScore S ν θ u x * modelScore S ν θ v x ∂Pfam (θ : J → ℝ) := by
  have := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  unfold fisherInner
  rw [lawCov_eq_integral_centred _ (bdd_dirLoss hS _) (bdd_dirLoss hS _)]
  rfl

/-- The lowered m-Christoffel symbol is minus the third moment of the centred scores. -/
theorem fisherInner_mChristoffel_eq_integral (θ u v w : 𝕍) :
    G θ (mChristoffel hS ν θ u v) w =
      -∫ x, modelScore S ν θ u x * modelScore S ν θ v x * modelScore S ν θ w x
        ∂Pfam (θ : J → ℝ) := by
  rw [fisherInner_mChristoffel_eq_thirdCentral hS ν, thirdCentral]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by unfold modelScore; ring)

/-- Under saturation, the m-Christoffel vector of `u, v` is `−c` where `f_c = f_u f_v − G(u,v)`. -/
theorem mChristoffel_eq_neg_of_saturated (θ u v c : 𝕍)
    (hc : ∀ᵐ x ∂Pfam (θ : J → ℝ),
      modelScore S ν θ u x * modelScore S ν θ v x - G θ u v = modelScore S ν θ c x) :
    mChristoffel hS ν θ u v = -c := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  symm
  refine mChristoffel_unique hS ν θ u v fun w ↦ ?_
  rw [← fisherInner_mChristoffel hS ν, fisherInner_mChristoffel_eq_integral hS ν,
    ← neg_one_smul ℝ c, fisherInner_smul_left, neg_one_mul,
    fisherInner_eq_integral_modelScore hS ν]
  congr 1
  have h1 : Integrable (fun x ↦ modelScore S ν θ u x * modelScore S ν θ v x *
      modelScore S ν θ w x) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (((bdd_modelScore hS ν θ u).mul (bdd_modelScore hS ν θ v)).mul
      (bdd_modelScore hS ν θ w))
  have h2 : Integrable (fun x ↦ G θ u v * modelScore S ν θ w x) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (Bdd.const_mul _ (bdd_modelScore hS ν θ w))
  calc ∫ x, modelScore S ν θ c x * modelScore S ν θ w x ∂Pfam (θ : J → ℝ)
      = ∫ x, (modelScore S ν θ u x * modelScore S ν θ v x * modelScore S ν θ w x -
          G θ u v * modelScore S ν θ w x) ∂Pfam (θ : J → ℝ) := by
        refine integral_congr_ae (hc.mono fun x hx ↦ ?_)
        beta_reduce
        rw [← hx]; ring
    _ = ∫ x, modelScore S ν θ u x * modelScore S ν θ v x * modelScore S ν θ w x
          ∂Pfam (θ : J → ℝ) := by
        rw [integral_sub h1 h2, integral_const_mul, integral_modelScore hS ν, mul_zero, sub_zero]

/-- **The Christoffel Gram matrix of a saturated family**:
`G(C(u,v), C(x,y)) = E_θ[f_u f_v f_x f_y] − G(u,v) G(x,y)`. -/
theorem fisherInner_mChristoffel_mChristoffel_of_saturated (θ : 𝕍) (hsat : SaturatedAt S ν θ)
    (u v x y : 𝕍) :
    G θ (mChristoffel hS ν θ u v) (mChristoffel hS ν θ x y) =
      (∫ z, modelScore S ν θ u z * modelScore S ν θ v z *
        (modelScore S ν θ x z * modelScore S ν θ y z) ∂Pfam (θ : J → ℝ)) -
        G θ u v * G θ x y := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  obtain ⟨c, hc⟩ := hsat u v
  obtain ⟨c', hc'⟩ := hsat x y
  rw [mChristoffel_eq_neg_of_saturated hS ν θ u v c hc,
    mChristoffel_eq_neg_of_saturated hS ν θ x y c' hc', ← neg_one_smul ℝ c,
    fisherInner_smul_left, fisherInner_comm hS ν, ← neg_one_smul ℝ c', fisherInner_smul_left,
    fisherInner_comm hS ν, fisherInner_eq_integral_modelScore hS ν]
  set a := G θ u v with ha
  set b := G θ x y with hb
  have hE : Integrable (fun z ↦ modelScore S ν θ u z * modelScore S ν θ v z *
      (modelScore S ν θ x z * modelScore S ν θ y z)) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (((bdd_modelScore hS ν θ u).mul (bdd_modelScore hS ν θ v)).mul
      ((bdd_modelScore hS ν θ x).mul (bdd_modelScore hS ν θ y)))
  have h2 : Integrable (fun z ↦ b * (modelScore S ν θ u z * modelScore S ν θ v z))
      (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (Bdd.const_mul _ ((bdd_modelScore hS ν θ u).mul
      (bdd_modelScore hS ν θ v)))
  have h3 : Integrable (fun z ↦ a * (modelScore S ν θ x z * modelScore S ν θ y z))
      (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (Bdd.const_mul _ ((bdd_modelScore hS ν θ x).mul
      (bdd_modelScore hS ν θ y)))
  have h12 : Integrable (fun z ↦ modelScore S ν θ u z * modelScore S ν θ v z *
      (modelScore S ν θ x z * modelScore S ν θ y z) -
      b * (modelScore S ν θ u z * modelScore S ν θ v z)) (Pfam (θ : J → ℝ)) := hE.sub h2
  have h123 : Integrable (fun z ↦ modelScore S ν θ u z * modelScore S ν θ v z *
      (modelScore S ν θ x z * modelScore S ν θ y z) -
      b * (modelScore S ν θ u z * modelScore S ν θ v z) -
      a * (modelScore S ν θ x z * modelScore S ν θ y z)) (Pfam (θ : J → ℝ)) := h12.sub h3
  calc (-1) * ((-1) * ∫ z, modelScore S ν θ c z * modelScore S ν θ c' z ∂Pfam (θ : J → ℝ))
      = ∫ z, (modelScore S ν θ u z * modelScore S ν θ v z - a) *
          (modelScore S ν θ x z * modelScore S ν θ y z - b) ∂Pfam (θ : J → ℝ) := by
        rw [← mul_assoc, show (-1 : ℝ) * (-1) = 1 by norm_num, one_mul]
        refine integral_congr_ae ((hc.and hc').mono fun z ⟨hz, hz'⟩ ↦ ?_)
        beta_reduce
        rw [← hz, ← hz']
    _ = ∫ z, (modelScore S ν θ u z * modelScore S ν θ v z *
          (modelScore S ν θ x z * modelScore S ν θ y z) -
          b * (modelScore S ν θ u z * modelScore S ν θ v z) -
          a * (modelScore S ν θ x z * modelScore S ν θ y z) + a * b) ∂Pfam (θ : J → ℝ) :=
        integral_congr_ae (Eventually.of_forall fun z ↦ by ring)
    _ = (∫ z, modelScore S ν θ u z * modelScore S ν θ v z *
          (modelScore S ν θ x z * modelScore S ν θ y z) ∂Pfam (θ : J → ℝ)) - b * a - a * b +
          a * b := by
        rw [integral_add h123 (integrable_const _), integral_sub h12 h3, integral_sub hE h2,
          integral_const_mul, integral_const_mul, integral_const, probReal_univ, one_smul,
          ← fisherInner_eq_integral_modelScore hS ν, ← fisherInner_eq_integral_modelScore hS ν]
    _ = _ := by ring

/-- **The constant-curvature tensor of a saturated family**:
`G(R^α(u,v)w, x) = ((1 − α²)/4) (G(u,x) G(v,w) − G(v,x) G(u,w))`: the fourth moments cancel and
only the metric survives. -/
theorem fisherInner_alphaCurvature_of_saturated (θ : 𝕍) (hsat : SaturatedAt S ν θ) (α : ℝ)
    (u v w x : 𝕍) :
    G θ (alphaCurvature hS ν α θ u v w) x =
      ((1 - α ^ 2) / 4) * (G θ u x * G θ v w - G θ v x * G θ u w) := by
  rw [fisherInner_alphaCurvature hS ν, ← fisherInner_mChristoffel_mChristoffel hS ν,
    ← fisherInner_mChristoffel_mChristoffel hS ν,
    fisherInner_mChristoffel_mChristoffel_of_saturated hS ν θ hsat,
    fisherInner_mChristoffel_mChristoffel_of_saturated hS ν θ hsat]
  have e : ∫ z, modelScore S ν θ u z * modelScore S ν θ x z *
      (modelScore S ν θ v z * modelScore S ν θ w z) ∂Pfam (θ : J → ℝ) =
      ∫ z, modelScore S ν θ v z * modelScore S ν θ x z *
        (modelScore S ν θ u z * modelScore S ν θ w z) ∂Pfam (θ : J → ℝ) :=
    integral_congr_ae (Eventually.of_forall fun z ↦ by ring)
  rw [e]
  ring

/-- **Saturated families are round**: every nondegenerate plane has Fisher sectional curvature
`1/4`. -/
theorem fisherSectional_of_saturated (θ : 𝕍) (hsat : SaturatedAt S ν θ) (u v : 𝕍)
    (hden : 0 < G θ u u * G θ v v - G θ u v ^ 2) :
    fisherSectional hS ν θ u v = 1 / 4 := by
  rw [fisherSectional, fisherInner_alphaCurvature_of_saturated hS ν θ hsat,
    fisherInner_comm hS ν θ v u]
  have e : (1 - (0 : ℝ) ^ 2) / 4 * (G θ u u * G θ v v - G θ u v * G θ u v) =
      1 / 4 * (G θ u u * G θ v v - G θ u v ^ 2) := by ring
  rw [e, mul_div_assoc, div_self hden.ne', mul_one]

end Simplex

end Laplace.Multi
