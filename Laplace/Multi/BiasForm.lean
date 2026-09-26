/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.RegressionOrthogonality
import Laplace.Multi.ObservableTaylorUniform
import Laplace.Multi.DifferentialRetraction

/-!
# The bias form of an observable

The normal projection `N_M` is self-adjoint in `L²(Q_M)` (`integral_mul_normalProj_comm`), so the
quadratic term of the observable Taylor expansion, `∫ F · N_M(ℓ_z²) dQ`, is `∫ N_M F · ℓ_z² dQ`. We
extend it to a bilinear form `b_F` on the ambient coordinate space `J → ℝ` through a linear
projection `π` onto the direction subspace (`dirProj`), obtaining the **bias form**
`biasForm M F u v = ∫ N_M F · ℓ_{πu} ℓ_{πv} dQ_M`, its coordinate expansion (`biasForm_eq_sum`),
and the uniform Peano expansion restated with it (`integral_response_peano_biasForm`). These are
the analytic inputs of the reconstruction-bias theorem.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Proj

variable {X : Type*} [MeasurableSpace X] {J : Type*} (S : J → X → ℝ) (ν : Measure X)

/-- A linear projection of the coordinate space onto the direction subspace. -/
noncomputable def dirProj : (J → ℝ) →ₗ[ℝ] dirSpan ν (fun _ ↦ (1 : ℝ)) S :=
  Submodule.projectionOnto (dirSpan ν (fun _ ↦ (1 : ℝ)) S)
    (Classical.choose (Submodule.exists_isCompl (dirSpan ν (fun _ ↦ (1 : ℝ)) S)))
    (Classical.choose_spec (Submodule.exists_isCompl (dirSpan ν (fun _ ↦ (1 : ℝ)) S)))

/-- The projection fixes the direction subspace. -/
theorem dirProj_coe (v : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : dirProj S ν (v : J → ℝ) = v :=
  Submodule.projectionOnto_apply_left _ v

end Proj

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

variable {M : J → ℝ}

/-- The linear part of the observable response, extended to the coordinate space. -/
noncomputable def linForm (M : J → ℝ) {F : X → ℝ} (hF : Bdd F) : (J → ℝ) →ₗ[ℝ] ℝ where
  toFun u := ∫ x, F x * responseScore hS ν M (dirProj S ν u) x ∂(Pfam (θr M))
  map_add' u v := by
    have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
    simp only [map_add, responseScore_add, mul_add]
    exact integral_add (integrable_of_bdd_prob _ (hF.mul (bdd_responseScore hS ν M _)))
      (integrable_of_bdd_prob _ (hF.mul (bdd_responseScore hS ν M _)))
  map_smul' c u := by
    simp only [map_smul, responseScore_smul, RingHom.id_apply, smul_eq_mul, mul_left_comm _ c,
      integral_const_mul]

theorem linForm_apply {F : X → ℝ} (hF : Bdd F) (u : J → ℝ) :
    linForm hS ν M hF u = ∫ x, F x * responseScore hS ν M (dirProj S ν u) x ∂(Pfam (θr M)) := rfl

/-- The coordinate basis vector `e_a`. -/
def coordUnit [DecidableEq J] (a : J) : J → ℝ := fun j ↦ if a = j then 1 else 0

omit hS [Nonempty J] in
/-- Coordinate expansion of a linear functional on `J → ℝ`. -/
theorem linearMap_eq_sum_coordUnit [DecidableEq J] (L : (J → ℝ) →ₗ[ℝ] ℝ) (u : J → ℝ) :
    L u = ∑ a, u a * L (coordUnit a) := by
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp only [smul_eq_mul]
  rfl

/-- The bias-form integrand is bilinear: the raw function. -/
noncomputable def biasFormFun (M : J → ℝ) {F : X → ℝ} (hF : Bdd F) (u v : J → ℝ) : ℝ :=
  ∫ x, normalProj hS ν M hF x * (responseScore hS ν M (dirProj S ν u) x *
    responseScore hS ν M (dirProj S ν v) x) ∂(Pfam (θr M))

theorem bdd_biasForm_integrand {F : X → ℝ} (hF : Bdd F) (u v : J → ℝ) :
    Bdd fun x ↦ normalProj hS ν M hF x * (responseScore hS ν M (dirProj S ν u) x *
      responseScore hS ν M (dirProj S ν v) x) :=
  (bdd_normalProj hS ν hF).mul ((bdd_responseScore hS ν M _).mul (bdd_responseScore hS ν M _))

/-- **The bias form** `b_F(u, v) = ∫ N_M F · ℓ_{πu} ℓ_{πv} dQ_M`, bilinear on `J → ℝ`. -/
noncomputable def biasForm (M : J → ℝ) {F : X → ℝ} (hF : Bdd F) :
    (J → ℝ) →ₗ[ℝ] (J → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (biasFormFun hS ν M hF)
    (fun u u' v ↦ by
      have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
      unfold biasFormFun
      simp only [map_add, responseScore_add, add_mul, mul_add]
      exact integral_add (integrable_of_bdd_prob _ (bdd_biasForm_integrand hS ν hF u v))
        (integrable_of_bdd_prob _ (bdd_biasForm_integrand hS ν hF u' v)))
    (fun c u v ↦ by
      unfold biasFormFun
      simp only [map_smul, responseScore_smul, smul_eq_mul, mul_assoc, mul_left_comm _ c,
        integral_const_mul])
    (fun u v v' ↦ by
      have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
      unfold biasFormFun
      simp only [map_add, responseScore_add, mul_add]
      exact integral_add (integrable_of_bdd_prob _ (bdd_biasForm_integrand hS ν hF u v))
        (integrable_of_bdd_prob _ (bdd_biasForm_integrand hS ν hF u v')))
    (fun c u v ↦ by
      unfold biasFormFun
      simp only [map_smul, responseScore_smul, smul_eq_mul, mul_left_comm _ c,
        integral_const_mul])

theorem biasForm_apply {F : X → ℝ} (hF : Bdd F) (u v : J → ℝ) :
    biasForm hS ν M hF u v = ∫ x, normalProj hS ν M hF x *
      (responseScore hS ν M (dirProj S ν u) x * responseScore hS ν M (dirProj S ν v) x)
      ∂(Pfam (θr M)) := rfl

/-- Coordinate expansion of the bias form. -/
theorem biasForm_eq_sum [DecidableEq J] {F : X → ℝ} (hF : Bdd F) (u v : J → ℝ) :
    biasForm hS ν M hF u v =
      ∑ a, ∑ b, u a * v b * biasForm hS ν M hF (coordUnit a) (coordUnit b) := by
  rw [linearMap_eq_sum_coordUnit (biasForm hS ν M hF u) v]
  rw [LinearMap.pi_apply_eq_sum_univ (biasForm hS ν M hF) u]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  change v b * (u a * biasForm hS ν M hF (coordUnit a) (coordUnit b)) = _
  ring

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- `∫ f N_M g = ∫ N_M f N_M g`: pairing with a normal part only sees the normal part. -/
theorem integral_mul_normalProj_eq {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) :
    ∫ x, f x * normalProj hS ν M hg x ∂(Pfam (θr M)) =
      ∫ x, normalProj hS ν M hf x * normalProj hS ν M hg x ∂(Pfam (θr M)) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have hNg := bdd_normalProj hS ν hg (M := M)
  have hNf := bdd_normalProj hS ν hf (M := M)
  have e : ∀ x, f x * normalProj hS ν M hg x =
      ((∫ y, f y ∂(Pfam (θr M))) * normalProj hS ν M hg x +
        regProj hS ν M hf x * normalProj hS ν M hg x) +
        normalProj hS ν M hf x * normalProj hS ν M hg x := by
    intro x
    have := sub_integral_eq_regProj_add_normalProj hS ν (M := M) hf x
    linear_combination (normalProj hS ν M hg x) * this
  have h1 : Integrable (fun x ↦ (∫ y, f y ∂(Pfam (θr M))) * normalProj hS ν M hg x)
      (Pfam (θr M)) := (integrable_of_bdd_prob _ hNg).const_mul _
  have h2 : Integrable (fun x ↦ regProj hS ν M hf x * normalProj hS ν M hg x) (Pfam (θr M)) :=
    integrable_of_bdd_prob _ ((bdd_responseScore hS ν M _).mul hNg)
  have h3 : Integrable (fun x ↦ normalProj hS ν M hf x * normalProj hS ν M hg x)
      (Pfam (θr M)) := integrable_of_bdd_prob _ (hNf.mul hNg)
  have h12 : Integrable (fun x ↦ (∫ y, f y ∂(Pfam (θr M))) * normalProj hS ν M hg x +
      regProj hS ν M hf x * normalProj hS ν M hg x) (Pfam (θr M)) := h1.add h2
  simp_rw [e]
  rw [integral_add h12 h3, integral_add h1 h2, integral_const_mul, integral_normalProj hS ν hrel hg,
    mul_zero, zero_add]
  have h0 : ∫ x, regProj hS ν M hf x * normalProj hS ν M hg x ∂(Pfam (θr M)) = 0 := by
    have h := integral_normalProj_mul_responseScore hS ν hrel hg
      ⟨respCov hS ν M f, respCov_mem_dirSpan hS ν hf⟩
    unfold regProj
    refine (integral_congr_ae (Eventually.of_forall fun x ↦ ?_)).trans h
    ring
  rw [h0, zero_add]

/-- **The normal projection is self-adjoint in `L²(Q_M)`**: `∫ f N_M g = ∫ N_M f · g`. -/
theorem integral_mul_normalProj_comm {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) :
    ∫ x, f x * normalProj hS ν M hg x ∂(Pfam (θr M)) =
      ∫ x, normalProj hS ν M hf x * g x ∂(Pfam (θr M)) := by
  rw [integral_mul_normalProj_eq hS ν hrel hf hg]
  have := integral_mul_normalProj_eq hS ν hrel hg hf
  simp only [mul_comm] at this ⊢
  exact this.symm

/-- The quadratic Peano term is the bias form on the diagonal. -/
theorem integral_mul_normalProj_sq_eq_biasForm {F : X → ℝ} (hF : Bdd F) (z : 𝕍) :
    ∫ x, F x * normalProj hS ν M
      ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x ∂(Pfam (θr M)) =
      biasForm hS ν M hF (z : J → ℝ) (z : J → ℝ) := by
  rw [integral_mul_normalProj_comm hS ν hrel hF, biasForm_apply, dirProj_coe]

omit hrel in
/-- The linear Peano term is the linear form. -/
theorem integral_mul_responseScore_eq_linForm {F : X → ℝ} (hF : Bdd F) (z : 𝕍) :
    ∫ x, F x * responseScore hS ν M z x ∂(Pfam (θr M)) = linForm hS ν M hF (z : J → ℝ) := by
  rw [linForm_apply, dirProj_coe]

omit hrel in
/-- **The compact-uniform observable Taylor expansion in bias-form notation**:
`G(M + z) = G(M) + linForm_M(z) + ½ b_F(z, z) + O(ε ‖z‖²)` uniformly on compact convex interior
sets. -/
theorem integral_response_peano_biasForm {C : Set (J → ℝ)} (hC : IsCompact C) (hCc : Convex ℝ C)
    (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {F : X → ℝ} (hF : Bdd F)
    {BF : ℝ} (hBF : ∀ x, |F x| ≤ BF) :
    ∀ ε > 0, ∃ δ > 0, ∀ M ∈ C, ∀ z : 𝕍, M + (z : J → ℝ) ∈ C → ‖z‖ ≤ δ →
      |(∫ x, F x ∂(Pfam (θr (M + z)))) - (∫ x, F x ∂(Pfam (θr M))) -
        linForm hS ν M hF (z : J → ℝ) -
        (1 / 2) * biasForm hS ν M hF (z : J → ℝ) (z : J → ℝ)| ≤ BF * (ε * ‖z‖ ^ 2) := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := integral_response_peano_uniform hS ν hC hCc hCK hF hBF ε hε
  refine ⟨δ, hδ, fun M hM z hMz hz ↦ ?_⟩
  rw [← integral_mul_responseScore_eq_linForm hS ν hF z,
    ← integral_mul_normalProj_sq_eq_biasForm hS ν (hCK hM) hF z]
  exact h M hM z hMz hz

end Laplace.Multi
