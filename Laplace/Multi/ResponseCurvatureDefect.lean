/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseSimplexCurvature

/-!
# The curvature defect: how far a response geometry is from the round sphere

For a general family the product of two centred scores `f_u f_v` need not be a centred score. Its
**score residual** is
`r_{uv} = f_u f_v − G_θ(u,v) + f_{C_θ(u,v)}`
(the sign is the seabed's: the score projection of `f_u f_v − G(u,v)` is `−f_{C(u,v)}`). The
residual is centred and orthogonal to every score (`integral_scoreResidual`,
`integral_scoreResidual_mul_modelScore`), and the Christoffel Gram matrix is the fourth moment
corrected by the residual Gram matrix:

`G(C(u,v), C(x,y)) = E[f_u f_v f_x f_y] − G(u,v) G(x,y) − E[r_{uv} r_{xy}]`
(`fisherInner_mChristoffel_mChristoffel_eq_sub_residual`).

Inserted into the curvature formula this gives the **Gauss-type identity**

`G(R^α(u,v)w, x) = ((1 − α²)/4) [ (G(u,x)G(v,w) − G(v,x)G(u,w))
  + (E[r_{ux} r_{vw}] − E[r_{vx} r_{uw}]) ]`
(`fisherInner_alphaCurvature_eq_round_add_residual`) and

`K_θ(u,v) = 1/4 + (E[r_{uu} r_{vv}] − E[r_{uv}²]) / (4 D)`, `D = G(u,u)G(v,v) − G(u,v)²`
(`fisherSectional_eq_quarter_add_residual`):

the response model inherits the sphere's curvature `¼`, corrected exactly by the component of the
score products that the response coordinates cannot represent. Saturation is `r ≡ 0`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Defect

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

/-- The centred score. -/
local notation "f" => modelScore S ν

/-- **The score residual** `r_{uv} = f_u f_v − G(u,v) + f_{C(u,v)}`: the part of the product of two
centred scores not represented by any score. -/
noncomputable def scoreResidual (θ u v : 𝕍) : X → ℝ :=
  fun x ↦ f θ u x * f θ v x - G θ u v + f θ (mChristoffel hS ν θ u v) x

theorem bdd_scoreResidual (θ u v : 𝕍) : Bdd (scoreResidual hS ν θ u v) :=
  (((bdd_modelScore hS ν θ u).mul (bdd_modelScore hS ν θ v)).sub (Bdd.const _)).add
    (bdd_modelScore hS ν θ _)

theorem scoreResidual_symm (θ u v : 𝕍) :
    scoreResidual hS ν θ u v = scoreResidual hS ν θ v u := by
  funext x
  simp only [scoreResidual, mChristoffel_symm hS ν θ u v, fisherInner_comm hS ν θ u v, mul_comm]

/-- The residual is centred. -/
theorem integral_scoreResidual (θ u v : 𝕍) :
    ∫ x, scoreResidual hS ν θ u v x ∂Pfam (θ : J → ℝ) = 0 := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  have h1 : Integrable (fun x ↦ f θ u x * f θ v x - G θ u v) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (((bdd_modelScore hS ν θ u).mul (bdd_modelScore hS ν θ v)).sub
      (Bdd.const _))
  have h2 : Integrable (fun x ↦ f θ u x * f θ v x) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ ((bdd_modelScore hS ν θ u).mul (bdd_modelScore hS ν θ v))
  unfold scoreResidual
  rw [integral_add h1 (integrable_of_bdd_prob _ (bdd_modelScore hS ν θ _)),
    integral_modelScore hS ν, integral_sub h2 (integrable_const _), integral_const, probReal_univ,
    one_smul, ← fisherInner_eq_integral_modelScore hS ν]
  ring

/-- **The residual is orthogonal to every score.** -/
theorem integral_scoreResidual_mul_modelScore (θ u v w : 𝕍) :
    ∫ x, scoreResidual hS ν θ u v x * f θ w x ∂Pfam (θ : J → ℝ) = 0 := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  have h1 : Integrable (fun x ↦ f θ u x * f θ v x * f θ w x) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (((bdd_modelScore hS ν θ u).mul (bdd_modelScore hS ν θ v)).mul
      (bdd_modelScore hS ν θ w))
  have h2 : Integrable (fun x ↦ G θ u v * f θ w x) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (Bdd.const_mul _ (bdd_modelScore hS ν θ w))
  have h3 : Integrable (fun x ↦ f θ (mChristoffel hS ν θ u v) x * f θ w x) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ ((bdd_modelScore hS ν θ _).mul (bdd_modelScore hS ν θ w))
  have h12 : Integrable (fun x ↦ f θ u x * f θ v x * f θ w x - G θ u v * f θ w x)
      (Pfam (θ : J → ℝ)) := h1.sub h2
  have e : (fun x ↦ scoreResidual hS ν θ u v x * f θ w x) = fun x ↦
      (f θ u x * f θ v x * f θ w x - G θ u v * f θ w x) +
        f θ (mChristoffel hS ν θ u v) x * f θ w x := by
    funext x; simp only [scoreResidual]; ring
  rw [e, integral_add h12 h3, integral_sub h1 h2, integral_const_mul, integral_modelScore hS ν,
    mul_zero, sub_zero, ← fisherInner_eq_integral_modelScore hS ν,
    fisherInner_mChristoffel_eq_integral hS ν]
  ring

omit [Nonempty J] in
/-- The fourth-moment expansion of the product of two centred products. -/
theorem integral_centredProd_mul_centredProd (θ u v x y : 𝕍) :
    ∫ z, (f θ u z * f θ v z - G θ u v) * (f θ x z * f θ y z - G θ x y) ∂Pfam (θ : J → ℝ) =
      (∫ z, f θ u z * f θ v z * (f θ x z * f θ y z) ∂Pfam (θ : J → ℝ)) - G θ u v * G θ x y := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  set a := G θ u v with ha
  set b := G θ x y with hb
  have hE : Integrable (fun z ↦ f θ u z * f θ v z * (f θ x z * f θ y z)) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (((bdd_modelScore hS ν θ u).mul (bdd_modelScore hS ν θ v)).mul
      ((bdd_modelScore hS ν θ x).mul (bdd_modelScore hS ν θ y)))
  have h2 : Integrable (fun z ↦ b * (f θ u z * f θ v z)) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (Bdd.const_mul _ ((bdd_modelScore hS ν θ u).mul
      (bdd_modelScore hS ν θ v)))
  have h3 : Integrable (fun z ↦ a * (f θ x z * f θ y z)) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (Bdd.const_mul _ ((bdd_modelScore hS ν θ x).mul
      (bdd_modelScore hS ν θ y)))
  have h12 : Integrable (fun z ↦ f θ u z * f θ v z * (f θ x z * f θ y z) -
      b * (f θ u z * f θ v z)) (Pfam (θ : J → ℝ)) := hE.sub h2
  have h123 : Integrable (fun z ↦ f θ u z * f θ v z * (f θ x z * f θ y z) -
      b * (f θ u z * f θ v z) - a * (f θ x z * f θ y z)) (Pfam (θ : J → ℝ)) := h12.sub h3
  calc ∫ z, (f θ u z * f θ v z - a) * (f θ x z * f θ y z - b) ∂Pfam (θ : J → ℝ)
      = ∫ z, (f θ u z * f θ v z * (f θ x z * f θ y z) - b * (f θ u z * f θ v z) -
          a * (f θ x z * f θ y z) + a * b) ∂Pfam (θ : J → ℝ) :=
        integral_congr_ae (Eventually.of_forall fun z ↦ by ring)
    _ = (∫ z, f θ u z * f θ v z * (f θ x z * f θ y z) ∂Pfam (θ : J → ℝ)) - b * a - a * b +
          a * b := by
        rw [integral_add h123 (integrable_const _), integral_sub h12 h3, integral_sub hE h2,
          integral_const_mul, integral_const_mul, integral_const, probReal_univ, one_smul,
          ← fisherInner_eq_integral_modelScore hS ν, ← fisherInner_eq_integral_modelScore hS ν]
    _ = _ := by ring

/-- **The Christoffel Gram matrix is the fourth moment corrected by the residual Gram matrix**:
`G(C(u,v), C(x,y)) = E[f_u f_v f_x f_y] − G(u,v) G(x,y) − E[r_{uv} r_{xy}]`. -/
theorem fisherInner_mChristoffel_mChristoffel_eq_sub_residual (θ u v x y : 𝕍) :
    G θ (mChristoffel hS ν θ u v) (mChristoffel hS ν θ x y) =
      (∫ z, f θ u z * f θ v z * (f θ x z * f θ y z) ∂Pfam (θ : J → ℝ)) - G θ u v * G θ x y -
        ∫ z, scoreResidual hS ν θ u v z * scoreResidual hS ν θ x y z ∂Pfam (θ : J → ℝ) := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  -- abbreviations
  set c := mChristoffel hS ν θ u v with hc
  set c' := mChristoffel hS ν θ x y with hc'
  set r := scoreResidual hS ν θ u v with hr
  set r' := scoreResidual hS ν θ x y with hr'
  -- `f_c = r − p`, `f_c' = r' − p'` pointwise
  have hp : ∀ z, f θ c z = r z - (f θ u z * f θ v z - G θ u v) := fun z ↦ by
    simp only [hr, scoreResidual]; ring
  have hp' : ∀ z, f θ c' z = r' z - (f θ x z * f θ y z - G θ x y) := fun z ↦ by
    simp only [hr', scoreResidual]; ring
  -- integrability
  have hbr : Bdd r := bdd_scoreResidual hS ν θ u v
  have hbr' : Bdd r' := bdd_scoreResidual hS ν θ x y
  have hbp : Bdd fun z ↦ f θ u z * f θ v z - G θ u v :=
    ((bdd_modelScore hS ν θ u).mul (bdd_modelScore hS ν θ v)).sub (Bdd.const _)
  have hbp' : Bdd fun z ↦ f θ x z * f θ y z - G θ x y :=
    ((bdd_modelScore hS ν θ x).mul (bdd_modelScore hS ν θ y)).sub (Bdd.const _)
  have i_rr : Integrable (fun z ↦ r z * r' z) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (hbr.mul hbr')
  have i_rp : Integrable (fun z ↦ r z * (f θ x z * f θ y z - G θ x y)) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (hbr.mul hbp')
  have i_pr : Integrable (fun z ↦ (f θ u z * f θ v z - G θ u v) * r' z) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (hbp.mul hbr')
  have i_pp : Integrable (fun z ↦ (f θ u z * f θ v z - G θ u v) *
      (f θ x z * f θ y z - G θ x y)) (Pfam (θ : J → ℝ)) := integrable_of_bdd_prob _ (hbp.mul hbp')
  have i_rc' : Integrable (fun z ↦ r z * f θ c' z) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (hbr.mul (bdd_modelScore hS ν θ c'))
  have i_cr' : Integrable (fun z ↦ f θ c z * r' z) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ ((bdd_modelScore hS ν θ c).mul hbr')
  -- orthogonality of the residuals to the scores `f_c'`, `f_c`
  have ho1 : ∫ z, r z * f θ c' z ∂Pfam (θ : J → ℝ) = 0 :=
    integral_scoreResidual_mul_modelScore hS ν θ u v c'
  have ho2 : ∫ z, f θ c z * r' z ∂Pfam (θ : J → ℝ) = 0 := by
    have h0 := integral_scoreResidual_mul_modelScore hS ν θ x y c
    calc ∫ z, f θ c z * r' z ∂Pfam (θ : J → ℝ)
        = ∫ z, r' z * f θ c z ∂Pfam (θ : J → ℝ) :=
          integral_congr_ae (Eventually.of_forall fun z ↦ mul_comm (f θ c z) (r' z))
      _ = 0 := h0
  -- `E[r p'] = E[r r']` and `E[p r'] = E[r r']`
  have hrp : ∫ z, r z * (f θ x z * f θ y z - G θ x y) ∂Pfam (θ : J → ℝ) =
      ∫ z, r z * r' z ∂Pfam (θ : J → ℝ) := by
    have e : (fun z ↦ r z * (f θ x z * f θ y z - G θ x y)) =
        fun z ↦ r z * r' z - r z * f θ c' z := by
      funext z; rw [hp' z]; ring
    rw [e, integral_sub i_rr i_rc', ho1, sub_zero]
  have hpr : ∫ z, (f θ u z * f θ v z - G θ u v) * r' z ∂Pfam (θ : J → ℝ) =
      ∫ z, r z * r' z ∂Pfam (θ : J → ℝ) := by
    have e : (fun z ↦ (f θ u z * f θ v z - G θ u v) * r' z) =
        fun z ↦ r z * r' z - f θ c z * r' z := by
      funext z; rw [hp z]; ring
    rw [e, integral_sub i_rr i_cr', ho2, sub_zero]
  -- assemble
  have hmain : ∫ z, f θ c z * f θ c' z ∂Pfam (θ : J → ℝ) =
      (∫ z, (f θ u z * f θ v z - G θ u v) * (f θ x z * f θ y z - G θ x y) ∂Pfam (θ : J → ℝ)) -
        ∫ z, r z * r' z ∂Pfam (θ : J → ℝ) := by
    have e : (fun z ↦ f θ c z * f θ c' z) = fun z ↦
        (r z * r' z - r z * (f θ x z * f θ y z - G θ x y)) -
          ((f θ u z * f θ v z - G θ u v) * r' z -
            (f θ u z * f θ v z - G θ u v) * (f θ x z * f θ y z - G θ x y)) := by
      funext z; rw [hp z, hp' z]; ring
    have i1 : Integrable (fun z ↦ r z * r' z - r z * (f θ x z * f θ y z - G θ x y))
        (Pfam (θ : J → ℝ)) := i_rr.sub i_rp
    have i2 : Integrable (fun z ↦ (f θ u z * f θ v z - G θ u v) * r' z -
        (f θ u z * f θ v z - G θ u v) * (f θ x z * f θ y z - G θ x y)) (Pfam (θ : J → ℝ)) :=
      i_pr.sub i_pp
    rw [e, integral_sub i1 i2, integral_sub i_rr i_rp, integral_sub i_pr i_pp, hrp, hpr]
    ring
  rw [fisherInner_eq_integral_modelScore hS ν, hmain,
    integral_centredProd_mul_centredProd hS ν]

/-- **The Gauss-type curvature identity**: the lowered `α`-curvature is the round tensor plus the
residual Gram defect,
`G(R^α(u,v)w, x) = ((1 − α²)/4) [ (G(u,x)G(v,w) − G(v,x)G(u,w))
  + (E[r_{ux} r_{vw}] − E[r_{vx} r_{uw}]) ]`. -/
theorem fisherInner_alphaCurvature_eq_round_add_residual (α : ℝ) (θ u v w x : 𝕍) :
    G θ (alphaCurvature hS ν α θ u v w) x =
      ((1 - α ^ 2) / 4) * ((G θ u x * G θ v w - G θ v x * G θ u w) +
        ((∫ z, scoreResidual hS ν θ u x z * scoreResidual hS ν θ v w z ∂Pfam (θ : J → ℝ)) -
          ∫ z, scoreResidual hS ν θ v x z * scoreResidual hS ν θ u w z ∂Pfam (θ : J → ℝ))) := by
  rw [fisherInner_alphaCurvature hS ν, ← fisherInner_mChristoffel_mChristoffel hS ν,
    ← fisherInner_mChristoffel_mChristoffel hS ν,
    fisherInner_mChristoffel_mChristoffel_eq_sub_residual hS ν,
    fisherInner_mChristoffel_mChristoffel_eq_sub_residual hS ν]
  have e : ∫ z, f θ u z * f θ x z * (f θ v z * f θ w z) ∂Pfam (θ : J → ℝ) =
      ∫ z, f θ v z * f θ x z * (f θ u z * f θ w z) ∂Pfam (θ : J → ℝ) :=
    integral_congr_ae (Eventually.of_forall fun z ↦ by ring)
  rw [e]
  ring

/-- **The sectional curvature is `¼` plus the residual defect**:
`K_θ(u,v) = 1/4 + (E[r_{uu} r_{vv}] − E[r_{uv}²]) / (4 D)` on a nondegenerate plane. -/
theorem fisherSectional_eq_quarter_add_residual (θ u v : 𝕍)
    (hden : 0 < G θ u u * G θ v v - G θ u v ^ 2) :
    fisherSectional hS ν θ u v = 1 / 4 +
      ((∫ z, scoreResidual hS ν θ u u z * scoreResidual hS ν θ v v z ∂Pfam (θ : J → ℝ)) -
        ∫ z, scoreResidual hS ν θ u v z ^ 2 ∂Pfam (θ : J → ℝ)) /
        (4 * (G θ u u * G θ v v - G θ u v ^ 2)) := by
  rw [fisherSectional, fisherInner_alphaCurvature_eq_round_add_residual hS ν,
    fisherInner_comm hS ν θ v u, scoreResidual_symm hS ν θ v u]
  have e : ∫ z, scoreResidual hS ν θ u v z * scoreResidual hS ν θ u v z ∂Pfam (θ : J → ℝ) =
      ∫ z, scoreResidual hS ν θ u v z ^ 2 ∂Pfam (θ : J → ℝ) :=
    integral_congr_ae (Eventually.of_forall fun z ↦ by ring)
  rw [e]
  field_simp
  ring

/-- Saturation is exactly the vanishing of all residuals. -/
theorem scoreResidual_eq_zero_ae_of_saturated (θ : 𝕍) (hsat : SaturatedAt S ν θ) (u v : 𝕍) :
    scoreResidual hS ν θ u v =ᵐ[Pfam (θ : J → ℝ)] fun _ ↦ 0 := by
  obtain ⟨c, hc⟩ := hsat u v
  filter_upwards [hc] with z hz
  simp only [scoreResidual, mChristoffel_eq_neg_of_saturated hS ν θ u v c hc, modelScore,
    Submodule.coe_neg, dirLoss_neg, integral_neg]
  simp only [modelScore] at hz
  linarith

end Defect

end Laplace.Multi
