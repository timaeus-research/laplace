/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseModelBaseDefect
import Laplace.Multi.ResponseFeatureRefinement
import Laplace.Multi.FacetFisherAccess
import Laplace.Multi.SusceptibilityDefect
import Laplace.Multi.ResponseBilinearForm
import Laplace.Multi.ResponseInformationPythagoras

/-!
# The infinitesimal refinement ladder

Let `T` refine `S` and let `D` be a model law of the coarse family, hence of the fine one
(`exists_familyMeasure_eq_of_refines`). Along the data path `D_t ∝ e^{t h} D` the refinement ladder
`KL(D_t ‖ R^S_t) = KL(D_t ‖ R^T_t) + KL(R^T_t ‖ R^S_t)` of `ResponseFeatureRefinement` holds at
every `t`, and the defect theorem of `ResponseModelBaseDefect` expands both defects to second
order. The
information newly resolved by the finer features is therefore quadratic with curvature the
**variance gained by the finer regression**:

`KL(R^T_t ‖ R^S_t) / t² → ½ (Var_D(g_T) − Var_D(g_S)) = ½ Var_D(g_T − g_S)`

(`tendsto_klDiv_responseProjection_refine_div_sq`,
`tendsto_klDiv_responseProjection_refine_div_sq'`), where `g_S`, `g_T` are the regressions of
the score `h` on the coarse and on the fine features under `D`. The second form is the
Pythagorean identity of nested regressions (`lawCov_regressor_sub_regressor`): the coarse
regression is a fine affine function, so it is
orthogonal to the fine residual. This says exactly which tangent information each refinement
adds; the common model base point is essential, since away from it the two response laws at `t = 0`
already differ.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Ladder

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {K : Type*} [Fintype K] [Nonempty K] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
  {T : K → X → ℝ} (hT : ∀ k, Bdd (T k)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS hT

/-- The coarse family. -/
local notation "PS" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The fine family. -/
local notation "PT" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) T 1

omit [Nonempty X] [Nonempty J] [Nonempty K] hS hT [IsProbabilityMeasure ν] in
/-- Every coarse contrast is `ν`-a.e. an affine fine contrast. -/
theorem exists_dirLoss_ae_eq_of_refines (hST : Refines S T ν) (e : J → ℝ) :
    ∃ (b : K → ℝ) (c : ℝ), dirLoss S e =ᵐ[ν] fun x ↦ dirLoss T b x + c := by
  choose b c hbc using hST
  refine ⟨∑ j, e j • b j, ∑ j, e j * c j, ?_⟩
  filter_upwards [Filter.eventually_all.2 hbc] with x hx
  simp only [dirLoss, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hx j]
  simp only [dirLoss]
  rw [mul_add, Finset.mul_sum]
  refine congrArg₂ _ (Finset.sum_congr rfl fun k _ ↦ ?_) rfl
  ring

omit [Nonempty J] [Nonempty K] in
/-- **A model law of the coarse family is a model law of the fine family.** -/
theorem exists_familyMeasure_eq_of_refines (hST : Refines S T ν) (θ₀ : J → ℝ) :
    ∃ η₀ : K → ℝ, PT η₀ = PS θ₀ := by
  obtain ⟨b, c, hbc⟩ := exists_dirLoss_ae_eq_of_refines ν hST θ₀
  refine ⟨b, ?_⟩
  rw [familyMeasure_one_zero_eq_tilted hS ν, familyMeasure_one_zero_eq_tilted hT ν,
    ← tilted_add_const ν (fun x ↦ -1 * dirLoss T b x) (-c)]
  refine tilted_congr ?_
  filter_upwards [hbc] with x hx
  rw [hx]
  ring

variable {h : X → ℝ} (hh : Bdd h)
include hh

omit [Nonempty J] [Fintype K] [Nonempty K] hT hh in
/-- The data path through a model law is a bounded tilt of the base point. -/
theorem tilted_familyMeasure_eq_tilted (θ₀ : J → ℝ) (t : ℝ) :
    (PS θ₀).tilted (fun x ↦ t * h x) = ν.tilted fun x ↦ -1 * dirLoss S θ₀ x + t * h x := by
  rw [familyMeasure_one_zero_eq_tilted hS ν, tilted_tilted
    (integrable_exp_of_bdd ν ((bdd_dirLoss hS θ₀).const_mul (-1)))]
  rfl

/-- The refinement ladder in real form along the data path. -/
theorem toReal_klDiv_responseProjection_refine_eq (hST : Refines S T ν) {θ₀ : J → ℝ}
    {η₀ : K → ℝ} (hbase : PT η₀ = PS θ₀) [IsProbabilityMeasure (PS θ₀)] (t : ℝ) :
    (klDiv (responseProjection hT ν fun k ↦ ∫ x, T k x ∂(PS θ₀).tilted fun x ↦ t * h x)
        (responseProjection hS ν fun j ↦ ∫ x, S j x ∂(PS θ₀).tilted fun x ↦ t * h x)).toReal =
      (klDiv ((PS θ₀).tilted fun x ↦ t * h x)
          (responseProjection hS ν fun j ↦ ∫ x, S j x ∂(PS θ₀).tilted fun x ↦ t * h x)).toReal -
        (klDiv ((PS θ₀).tilted fun x ↦ t * h x)
          (responseProjection hT ν fun k ↦ ∫ x, T k x ∂(PS θ₀).tilted fun x ↦ t * h x)).toReal := by
  have hg : Bdd fun x ↦ -1 * dirLoss S θ₀ x + t * h x :=
    ((bdd_dirLoss hS θ₀).const_mul (-1)).add (hh.const_mul t)
  have hDt : IsProbabilityMeasure ((PS θ₀).tilted fun x ↦ t * h x) := by
    rw [tilted_familyMeasure_eq_tilted hS ν θ₀ t]
    exact isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  have hDν : ((PS θ₀).tilted fun x ↦ t * h x) ≪ ν := by
    rw [tilted_familyMeasure_eq_tilted hS ν θ₀ t]
    exact tilted_absolutelyContinuous ν _
  have hkl : klDiv ((PS θ₀).tilted fun x ↦ t * h x) ν ≠ ⊤ := by
    rw [tilted_familyMeasure_eq_tilted hS ν θ₀ t]
    exact klDiv_tilted_ne_top ν hg
  have hfinT : genRate ν T (fun k ↦ ∫ x, T k x ∂(PS θ₀).tilted fun x ↦ t * h x) ≠ ⊤ := by
    rw [← hbase]
    have : IsProbabilityMeasure (PT η₀) := by rw [hbase]; infer_instance
    exact genRate_tilted_familyMeasure_ne_top hT ν hh η₀ t
  have hfinS : genRate ν S (fun j ↦ ∫ x, S j x ∂(PS θ₀).tilted fun x ↦ t * h x) ≠ ⊤ :=
    genRate_tilted_familyMeasure_ne_top hS ν hh θ₀ t
  have hlad := klDiv_data_responseProjection_refine hS hT ν _ hDν hfinT hST
  have hSfin : klDiv ((PS θ₀).tilted fun x ↦ t * h x)
      (responseProjection hS ν fun j ↦ ∫ x, S j x ∂(PS θ₀).tilted fun x ↦ t * h x) ≠ ⊤ := by
    have hp := (responseProjection_spec hS ν hfinS).2.2.2 _ hDt rfl
    refine ne_top_of_le_ne_top hkl ?_
    rw [hp]
    exact le_self_add
  have hTfin : klDiv ((PS θ₀).tilted fun x ↦ t * h x)
      (responseProjection hT ν fun k ↦ ∫ x, T k x ∂(PS θ₀).tilted fun x ↦ t * h x) ≠ ⊤ := by
    have hp := (responseProjection_spec hT ν hfinT).2.2.2 _ hDt rfl
    refine ne_top_of_le_ne_top hkl ?_
    rw [hp]
    exact le_self_add
  rw [hlad, ENNReal.toReal_add hTfin (by rw [hlad] at hSfin; exact (ENNReal.add_ne_top.1 hSfin).2)]
  ring

/-- **THE INFINITESIMAL REFINEMENT LADDER**: along `D_t ∝ e^{t h} D` through a common model law
`D = P^S_{θ₀} = P^T_{η₀}`, the information newly resolved by the finer features is, to second order,
half the variance gained by the finer regression of the score:
`KL(R^T_t ‖ R^S_t) / t² → ½ (Var_D(g_T) − Var_D(g_S))`. -/
theorem tendsto_klDiv_responseProjection_refine_div_sq (hST : Refines S T ν) {θ₀ : J → ℝ}
    {η₀ : K → ℝ} (hbase : PT η₀ = PS θ₀) [IsProbabilityMeasure (PS θ₀)] :
    Tendsto (fun t ↦ (klDiv
        (responseProjection hT ν fun k ↦ ∫ x, T k x ∂(PS θ₀).tilted fun x ↦ t * h x)
        (responseProjection hS ν fun j ↦ ∫ x, S j x ∂(PS θ₀).tilted fun x ↦ t * h x)).toReal /
      t ^ 2) (𝓝[≠] 0)
      (𝓝 ((lawCov (PS θ₀) (regressor hT (PS θ₀) hh) (regressor hT (PS θ₀) hh) -
        lawCov (PS θ₀) (regressor hS (PS θ₀) hh) (regressor hS (PS θ₀) hh)) / 2)) := by
  have hSdef := tendsto_klDiv_tilted_familyMeasure_responseProjection_div_sq hS ν hh θ₀ (PS θ₀) rfl
  have hTdef := tendsto_klDiv_tilted_familyMeasure_responseProjection_div_sq hT ν hh η₀ (PS θ₀)
    hbase.symm
  rw [← residual_variance hS (PS θ₀) hh] at hSdef
  rw [← residual_variance hT (PS θ₀) hh] at hTdef
  have e : (lawCov (PS θ₀) (regressor hT (PS θ₀) hh) (regressor hT (PS θ₀) hh) -
      lawCov (PS θ₀) (regressor hS (PS θ₀) hh) (regressor hS (PS θ₀) hh)) / 2 =
      (lawCov (PS θ₀) h h -
        lawCov (PS θ₀) (regressor hS (PS θ₀) hh) (regressor hS (PS θ₀) hh)) / 2 -
      (lawCov (PS θ₀) h h -
        lawCov (PS θ₀) (regressor hT (PS θ₀) hh) (regressor hT (PS θ₀) hh)) / 2 := by
    ring
  rw [e]
  refine (hSdef.sub hTdef).congr' (Eventually.of_forall fun t ↦ ?_)
  beta_reduce
  rw [toReal_klDiv_responseProjection_refine_eq hS hT ν hh hST hbase t, sub_div]

omit [IsProbabilityMeasure ν] in
/-- **Nested Pythagoras**: the coarse regression is a fine affine function, so
`Var_D(g_T − g_S) = Var_D(g_T) − Var_D(g_S)` at a law `D ≪ ν`. -/
theorem lawCov_regressor_sub_regressor (hST : Refines S T ν) (D : Measure X)
    [IsProbabilityMeasure D] (hDν : D ≪ ν) :
    lawCov D (fun x ↦ regressor hT D hh x - regressor hS D hh x)
        (fun x ↦ regressor hT D hh x - regressor hS D hh x) =
      lawCov D (regressor hT D hh) (regressor hT D hh) -
        lawCov D (regressor hS D hh) (regressor hS D hh) := by
  have hbS := bdd_regressor hS D hh
  have hbT := bdd_regressor hT D hh
  -- the cross covariance is the coarse variance
  have hcross : lawCov D (regressor hS D hh) (regressor hT D hh) =
      lawCov D (regressor hS D hh) (regressor hS D hh) := by
    obtain ⟨b, c, hbc⟩ := exists_dirLoss_ae_eq_of_refines ν hST
      (-(basepointVelocity hS D hh : J → ℝ))
    have hbc' : regressor hS D hh =ᵐ[D] fun x ↦ dirLoss T b x + c := hDν.ae_eq hbc
    have hconst : ∀ g : X → ℝ, Bdd g →
        lawCov D (fun x ↦ dirLoss T b x + c) g = lawCov D (dirLoss T b) g := fun g hg ↦ by
      rw [lawCov_add_left_eq D (bdd_dirLoss hT b) (Bdd.const c) hg, lawCov_const_left_eq_zero,
        add_zero]
    calc lawCov D (regressor hS D hh) (regressor hT D hh)
        = lawCov D (fun x ↦ dirLoss T b x + c) (regressor hT D hh) :=
          lawCov_congr_ae D hbc' (ae_eq_refl _)
      _ = lawCov D (dirLoss T b) h := by
          rw [hconst _ hbT, lawCov_dirLoss_regressor hT D hh b]
      _ = lawCov D (regressor hS D hh) h := by
          rw [← hconst _ hh]
          exact (lawCov_congr_ae D hbc' (ae_eq_refl _)).symm
      _ = lawCov D (regressor hS D hh) (regressor hS D hh) :=
          (lawCov_dirLoss_regressor hS D hh _).symm
  rw [lawCov_sub_left_eq D hbT hbS (hbT.sub hbS),
    lawCov_comm D (regressor hT D hh) (fun x ↦ regressor hT D hh x - regressor hS D hh x),
    lawCov_sub_left_eq D hbT hbS hbT,
    lawCov_comm D (regressor hS D hh) (fun x ↦ regressor hT D hh x - regressor hS D hh x),
    lawCov_sub_left_eq D hbT hbS hbS, hcross,
    lawCov_comm D (regressor hT D hh) (regressor hS D hh), hcross]
  ring

/-- The infinitesimal ladder in Pythagorean form:
`KL(R^T_t ‖ R^S_t) / t² → ½ Var_D(g_T − g_S)`. -/
theorem tendsto_klDiv_responseProjection_refine_div_sq' (hST : Refines S T ν) {θ₀ : J → ℝ}
    {η₀ : K → ℝ} (hbase : PT η₀ = PS θ₀) [IsProbabilityMeasure (PS θ₀)] :
    Tendsto (fun t ↦ (klDiv
        (responseProjection hT ν fun k ↦ ∫ x, T k x ∂(PS θ₀).tilted fun x ↦ t * h x)
        (responseProjection hS ν fun j ↦ ∫ x, S j x ∂(PS θ₀).tilted fun x ↦ t * h x)).toReal /
      t ^ 2) (𝓝[≠] 0)
      (𝓝 (lawCov (PS θ₀) (fun x ↦ regressor hT (PS θ₀) hh x - regressor hS (PS θ₀) hh x)
        (fun x ↦ regressor hT (PS θ₀) hh x - regressor hS (PS θ₀) hh x) / 2)) := by
  have hDν : PS θ₀ ≪ ν := by
    rw [familyMeasure_one_zero_eq_tilted hS ν]
    exact tilted_absolutelyContinuous ν _
  rw [lawCov_regressor_sub_regressor hS hT ν hh hST (PS θ₀) hDν]
  exact tendsto_klDiv_responseProjection_refine_div_sq hS hT ν hh hST hbase

end Ladder

end Laplace.Multi
