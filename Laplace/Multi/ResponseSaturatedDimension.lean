/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseSaturatedIdentification
import Laplace.Multi.ResponseObservableHessian
import Laplace.Multi.IntrinsicChart

/-!
# The dimension of the response space of a saturated finite family

Under `SpansAffine` every bounded observable is, after centring, a centred score of a unique
direction (`exists_modelScore_eq_of_spansAffine`, the regression representation of
`ResponseFiniteSaturation` for an arbitrary observable). On a **finite** set with every atom
charged, the evaluation of centred scores `w ↦ f_w` is therefore a linear isomorphism of `W` onto
the space of `P_θ`-centred functions, a hyperplane of `X → ℝ`, and

`dim W = |X| − 1`   (`finrank_dirSpan_eq_card_sub_one`).

This is the promised dimension count: the response space of the full simplex on `|X|` points has
the dimension of the simplex.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Representation

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

/-- The centred score. -/
local notation "f" => modelScore S ν

/-- **Every bounded observable is a centred score after centring** (affinely spanning family):
`h − E_θ h = f_w` for some `w ∈ W`. -/
theorem exists_modelScore_eq_of_spansAffine (hspan : SpansAffine S ν) (θ : 𝕍) {h : X → ℝ}
    (hb : Bdd h) :
    ∃ w : 𝕍, ∀ᵐ x ∂Pfam (θ : J → ℝ), h x - ∫ y, h y ∂Pfam (θ : J → ℝ) = f θ w x := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  have hPν : Pfam (θ : J → ℝ) ≪ ν := withDensity_absolutelyContinuous _ _
  have hcv : (fun i ↦ lawCov (Pfam (θ : J → ℝ)) (S i) h) ∈ 𝕍 :=
    covVec_mem_dirSpan hS ν (Pfam (θ : J → ℝ)) hPν hb
  have hcvn : -(fun i ↦ lawCov (Pfam (θ : J → ℝ)) (S i) h) ∈ 𝕍 := Submodule.neg_mem _ hcv
  set c : 𝕍 := (CDE θ).symm ⟨-(fun i ↦ lawCov (Pfam (θ : J → ℝ)) (S i) h), hcvn⟩ with hc
  refine ⟨c, ?_⟩
  have hGc : ∀ w : 𝕍, G θ w c = lawCov (Pfam (θ : J → ℝ)) (dirLoss S (w : J → ℝ)) h := by
    intro w
    rw [hc, fisherInner_chartDerivEquiv_symm hS ν θ w hcvn,
      lawCov_dirLoss_left hS (Pfam (θ : J → ℝ)) _ _ hb]
    simp only [dotJ, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_neg]
  obtain ⟨b, k, hbk⟩ := hspan h hb
  have hbkP : h =ᵐ[Pfam (θ : J → ℝ)] fun x ↦ dirLoss S b x + k := hPν.ae_eq hbk
  set d : J → ℝ := b - (c : J → ℝ) with hd
  set m := ∫ y, dirLoss S (c : J → ℝ) y ∂Pfam (θ : J → ℝ) with hm
  have hrep : (fun x ↦ h x - f θ c x) =ᵐ[Pfam (θ : J → ℝ)] fun x ↦ dirLoss S d x + (k + m) := by
    filter_upwards [hbkP] with x hx
    simp only [hx, modelScore, hd, dirLoss_sub', ← hm]
    ring
  have hcov0 : ∀ w : 𝕍, lawCov (Pfam (θ : J → ℝ)) (dirLoss S (w : J → ℝ)) (dirLoss S d) = 0 := by
    intro w
    have e1 := lawCov_congr_ae (Pfam (θ : J → ℝ)) (ae_eq_refl (dirLoss S (w : J → ℝ))) hrep
    rw [lawCov_add_right_eq _ (bdd_dirLoss hS d) (Bdd.const _) (bdd_dirLoss hS _),
      lawCov_comm _ _ (fun _ ↦ k + m), lawCov_const_left_eq_zero, add_zero] at e1
    rw [← e1, lawCov_comm, lawCov_sub_left_eq _ hb (bdd_modelScore hS ν θ c) (bdd_dirLoss hS _),
      lawCov_comm _ h, ← hGc w]
    have e2 : lawCov (Pfam (θ : J → ℝ)) (f θ c) (dirLoss S (w : J → ℝ)) = G θ w c := by
      rw [fisherInner_comm hS ν]
      unfold fisherInner modelScore
      rw [lawCov_sub_left_eq _ (bdd_dirLoss hS _) (Bdd.const _) (bdd_dirLoss hS _),
        lawCov_const_left_eq_zero, sub_zero]
    rw [e2, sub_self]
  have hcv' : (fun i ↦ lawCov (Pfam (θ : J → ℝ)) (S i) (dirLoss S d)) ∈ 𝕍 :=
    covVec_mem_dirSpan hS ν (Pfam (θ : J → ℝ)) hPν (bdd_dirLoss hS d)
  have hdot : ∀ w : 𝕍,
      dotJ (w : J → ℝ) (fun i ↦ lawCov (Pfam (θ : J → ℝ)) (S i) (dirLoss S d)) = 0 := by
    intro w
    have := hcov0 w
    rw [lawCov_dirLoss_left hS (Pfam (θ : J → ℝ)) _ _ (bdd_dirLoss hS d)] at this
    exact this
  have hcv0 : (fun i ↦ lawCov (Pfam (θ : J → ℝ)) (S i) (dirLoss S d)) = 0 :=
    eq_zero_of_dotJ_self_eq_zero (hdot ⟨_, hcv'⟩)
  have hcv0' : ∀ i, lawCov (Pfam (θ : J → ℝ)) (S i) (dirLoss S d) = 0 := fun i ↦ by
    have := congrFun hcv0 i
    simpa using this
  have hvar : lawCov (Pfam (θ : J → ℝ)) (dirLoss S d) (dirLoss S d) = 0 := by
    rw [lawCov_dirLoss_left hS (Pfam (θ : J → ℝ)) _ _ (bdd_dirLoss hS d)]
    simp [hcv0']
  have hconst := ae_eq_integral_of_lawCov_self_eq_zero (Pfam (θ : J → ℝ)) (bdd_dirLoss hS d) hvar
  have hE1 : ∫ x, (h x - f θ c x) ∂Pfam (θ : J → ℝ) = ∫ x, h x ∂Pfam (θ : J → ℝ) := by
    rw [integral_sub (integrable_of_bdd_prob _ hb)
      (integrable_of_bdd_prob _ (bdd_modelScore hS ν θ c)), integral_modelScore hS ν, sub_zero]
  have hE2 : ∫ x, (h x - f θ c x) ∂Pfam (θ : J → ℝ) =
      (∫ x, dirLoss S d x ∂Pfam (θ : J → ℝ)) + (k + m) := by
    rw [integral_congr_ae hrep, integral_add (integrable_of_bdd_prob _ (bdd_dirLoss hS d))
      (integrable_const _), integral_const, probReal_univ, one_smul]
  filter_upwards [hrep, hconst] with x hx hx'
  rw [← hE1, hE2]
  linarith

end Representation

section Finite

variable {X : Type*} [MeasurableSpace X] [Nonempty X] [Fintype X] [MeasurableSingletonClass X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, ν {x} ≠ 0)
include hS hν

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The centred score. -/
local notation "f" => modelScore S ν

omit [Nonempty X] [Nonempty J] hS hν [IsProbabilityMeasure ν] in
set_option linter.unusedFintypeInType false in
/-- Every function on a finite measurable space is bounded. -/
theorem bdd_of_fintype (h : X → ℝ) : Bdd h :=
  ⟨measurable_of_countable h, ∑ x, |h x|, fun x ↦
    Finset.single_le_sum (fun y _ ↦ abs_nonneg (h y)) (Finset.mem_univ x)⟩

omit [Nonempty J] [Fintype X] [MeasurableSingletonClass X] in
/-- Every atom is charged by every family member. -/
theorem familyMeasure_singleton_ne_zero (θ : J → ℝ) (x : X) : Pfam θ {x} ≠ 0 := by
  intro h0
  have hac : ν ≪ Pfam θ := by
    rw [← tilted_modelTilt hS ν θ]
    exact absolutelyContinuous_tilted (integrable_exp_of_bdd ν (bdd_modelTilt hS θ))
  exact hν x (hac h0)

omit [Nonempty J] [MeasurableSingletonClass X] in
set_option linter.unusedFintypeInType false in
/-- On a finite space with charged atoms, `P_θ`-a.e. statements hold everywhere. -/
theorem forall_of_ae_familyMeasure (θ : J → ℝ) {p : X → Prop} (h : ∀ᵐ x ∂Pfam θ, p x) :
    ∀ x, p x := fun x ↦
  (ae_iff_of_countable.mp h) x (familyMeasure_singleton_ne_zero hS ν hν θ x)

omit hν in
/-- **The centred-score evaluation** `W → (X → ℝ)`, `w ↦ f_w`. -/
noncomputable def scoreEval (θ : 𝕍) : 𝕍 →ₗ[ℝ] (X → ℝ) where
  toFun w := fun x ↦ f θ w x
  map_add' u v := by
    funext x
    have := congrFun (modelScore_add hS ν θ u v) x
    simpa using this
  map_smul' c u := by
    funext x
    have := congrFun (modelScore_smul ν θ c u) x
    simpa using this

omit [Fintype X] [MeasurableSingletonClass X] [Nonempty J] hν in
/-- The centred-score evaluation is injective: a direction with constant loss is invisible. -/
theorem scoreEval_injective (θ : 𝕍) : Function.Injective (scoreEval hS ν θ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  have hconst : ∀ x, dirLoss S (w : J → ℝ) x = ∫ y, dirLoss S (w : J → ℝ) y ∂Pfam (θ : J → ℝ) := by
    intro x
    have := congrFun hw x
    simp only [scoreEval, LinearMap.coe_mk, AddHom.coe_mk, modelScore, Pi.zero_apply] at this
    linarith
  have hinv : (w : J → ℝ) ∈ invisibleSet ν S :=
    ⟨∫ y, dirLoss S (w : J → ℝ) y ∂Pfam (θ : J → ℝ), ae_of_all _ hconst⟩
  exact Subtype.ext (eq_zero_of_invisible_of_mem_dirSpan (μ := ν) measurable_const
    (fun _ ↦ one_pos) hS hinv w.2)

omit hS hν in
/-- The `P_θ`-mean functional on functions. -/
noncomputable def meanFunctional (θ : 𝕍) : (X → ℝ) →ₗ[ℝ] ℝ where
  toFun a := ∑ x, (Pfam (θ : J → ℝ)).real {x} * a x
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.mul_sum, mul_left_comm]

omit [Nonempty J] hν in
/-- The mean functional is the integral. -/
theorem meanFunctional_apply (θ : 𝕍) (a : X → ℝ) :
    meanFunctional ν θ a = ∫ x, a x ∂Pfam (θ : J → ℝ) := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  rw [integral_fintype (integrable_of_bdd_prob _ (bdd_of_fintype a))]
  rfl

omit [Nonempty J] hν in
/-- The mean functional is onto. -/
theorem meanFunctional_range_eq_top (θ : 𝕍) : LinearMap.range (meanFunctional ν θ) = ⊤ := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  rw [LinearMap.range_eq_top]
  intro r
  refine ⟨fun _ ↦ r, ?_⟩
  rw [meanFunctional_apply hS ν, integral_const, probReal_univ, one_smul]

/-- **The centred scores are exactly the `P_θ`-centred functions** (affinely spanning family). -/
theorem range_scoreEval (hspan : SpansAffine S ν) (θ : 𝕍) :
    LinearMap.range (scoreEval hS ν θ) = LinearMap.ker (meanFunctional ν θ) := by
  ext a
  rw [LinearMap.mem_range, LinearMap.mem_ker, meanFunctional_apply hS ν]
  constructor
  · rintro ⟨w, rfl⟩
    exact integral_modelScore hS ν θ w
  · intro ha
    obtain ⟨w, hw⟩ := exists_modelScore_eq_of_spansAffine hS ν hspan θ (bdd_of_fintype a)
    refine ⟨w, ?_⟩
    funext x
    have := forall_of_ae_familyMeasure hS ν hν (θ : J → ℝ) hw x
    rw [ha, sub_zero] at this
    exact this.symm

/-- **The dimension of the response space of a saturated finite family**: `dim W = |X| − 1`. -/
theorem finrank_dirSpan_eq_card_sub_one (hspan : SpansAffine S ν) :
    Module.finrank ℝ 𝕍 = Fintype.card X - 1 := by
  classical
  obtain ⟨θ⟩ : Nonempty 𝕍 := ⟨0⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker (meanFunctional ν θ)
  rw [meanFunctional_range_eq_top hS ν θ, finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at h1
  have h2 : Module.finrank ℝ 𝕍 = Module.finrank ℝ (LinearMap.range (scoreEval hS ν θ)) :=
    (LinearEquiv.ofInjective _ (scoreEval_injective hS ν θ)).finrank_eq
  rw [h2, range_scoreEval hS ν hν hspan θ]
  omega

end Finite

end Laplace.Multi
