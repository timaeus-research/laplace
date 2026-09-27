/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseSaturatedDimension
import Laplace.Multi.ResponseEndpointInformationAction

/-!
# The simplex identification of a saturated finite family

For a finite space `X` with charged atoms and an affinely spanning feature family, the response
space `W` is identified with the **open probability simplex** `Δ° = {p : X → ℝ | p > 0, ∑ p = 1}`
through the **atom-mass map** `B(θ)_x = P_θ{x}`:

* `atomMass_eq`: `B(θ)_x = p_θ(x) ν{x}`; `atomMass_pos`, `sum_atomMass`: `B(θ) ∈ Δ°`;
* `meanMap_eq_sum_atomMass`: the mean map is the barycentre `m(θ) = ∑_x B(θ)_x S(x)`;
* `atomMass_injective`: `B` is injective on `W` (the mean map is);
* the **log-lift** `L : W → (X → ℝ)/ℝ𝟙`, `L(θ) = [x ↦ ⟨θ, S(x)⟩]`, is a linear isomorphism
  (`logEquiv`: injective by invisibility, bijective by the dimension count `dim W = |X| − 1`), and
  the inverse of `B` is `p ↦ L⁻¹[−log(p/ν)]` (`simplexInv`, `atomMass_simplexInv`,
  `simplexInv_atomMass`);
* `simplexEquiv : W ≃ Δ°`, `simplexHomeomorph : W ≃ₜ Δ°`, with `B` smooth (`contDiff_atomMass`)
  and `B⁻¹` smooth on the positive orthant (`contDiffOn_simplexInv`) — a nonlinear
  diffeomorphism; the *linear* identification is with log-probabilities modulo constants.

**The featureless journey is the mixture segment**: for the model journey from `ν` (`θ = 0`) to
`θ₁`, `B(θ_t) = (1 − t) ν{·} + t B(θ₁)` (`atomMass_modelJourney_zero`), so every observable has
affine expectation along it (`integral_familyMeasure_modelJourney_zero`) and the posterior
variance obeys the exact mixture identity
`Var_t F = (1−t) Var_ν F + t Var_{θ₁} F + t(1−t)(E_{θ₁}F − E_ν F)²` (`lawCov_modelJourney_zero`).
The journey "from the featureless distribution to the data" is literally the straight line in
the simplex.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Laplace.Multi

/-- The open probability simplex on a finite set. -/
def posSimplex (X : Type*) [Fintype X] : Set (X → ℝ) := {p | (∀ x, 0 < p x) ∧ ∑ x, p x = 1}

section Simplex

variable {X : Type*} [MeasurableSpace X] [Nonempty X] [Fintype X] [MeasurableSingletonClass X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, ν {x} ≠ 0)
include hS hν

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

variable (S) in
omit [Nonempty X] [Nonempty J] [Fintype X] [MeasurableSingletonClass X] hS hν
  [IsProbabilityMeasure ν] in
/-- **The atom-mass map** `B(θ)_x = P_θ{x}`. -/
noncomputable def atomMass (θ : J → ℝ) (x : X) : ℝ := (Pfam θ).real {x}

omit [Nonempty X] [Nonempty J] [Fintype X] hν in
/-- `B(θ)_x = p_θ(x) ν{x}`. -/
theorem atomMass_eq (θ : J → ℝ) (x : X) : atomMass S ν θ x = famDens S ν θ x * ν.real {x} := by
  unfold atomMass
  rw [measureReal_def, familyMeasure_eq_withDensity_famDens ν θ,
    withDensity_apply _ (measurableSet_singleton x), lintegral_singleton, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (famDens_nonneg hS ν θ x)]
  rfl

omit [Nonempty J] [Fintype X] [MeasurableSingletonClass X] in
/-- Every atom mass is positive. -/
theorem atomMass_pos (θ : J → ℝ) (x : X) : 0 < atomMass S ν θ x := by
  have := isProbabilityMeasure_family hS ν θ
  unfold atomMass
  rw [measureReal_def]
  exact ENNReal.toReal_pos (familyMeasure_singleton_ne_zero hS ν hν θ x) (measure_ne_top _ _)

omit [Nonempty J] hν in
/-- The atom masses sum to one. -/
theorem sum_atomMass (θ : J → ℝ) : ∑ x, atomMass S ν θ x = 1 := by
  have := isProbabilityMeasure_family hS ν θ
  unfold atomMass
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

omit [Nonempty J] hν in
/-- Integrals against `P_θ` are barycentric sums. -/
theorem integral_familyMeasure_eq_sum (θ : J → ℝ) (f : X → ℝ) :
    ∫ x, f x ∂Pfam θ = ∑ x, atomMass S ν θ x * f x := by
  have := isProbabilityMeasure_family hS ν θ
  rw [integral_fintype (integrable_of_bdd_prob _ (bdd_of_fintype f))]
  rfl

omit [Nonempty J] hν in
/-- **The mean map is the barycentre**: `m(θ) = ∑_x B(θ)_x S(x)`. -/
theorem meanMap_eq_sum_atomMass (θ : J → ℝ) :
    mean θ = fun j ↦ ∑ x, atomMass S ν θ x * S j x := by
  rw [← mean_familyMeasure_one_zero hS ν θ]
  funext j
  exact integral_familyMeasure_eq_sum hS ν θ (S j)

omit [Fintype X] [MeasurableSingletonClass X] hν in
/-- The mean map is injective on the direction space. -/
theorem meanMap_injective_dirSpan {θ η : 𝕍} (h : mean (θ : J → ℝ) = mean (η : J → ℝ)) : θ = η := by
  rw [← responseTheta_meanMap hS ν θ, ← responseTheta_meanMap hS ν η, h]

omit hν in
set_option linter.unusedFintypeInType false in
/-- **The atom-mass map is injective on the direction space.** -/
theorem atomMass_injective {θ η : 𝕍} (h : atomMass S ν (θ : J → ℝ) = atomMass S ν (η : J → ℝ)) :
    θ = η := by
  refine meanMap_injective_dirSpan hS ν ?_
  rw [meanMap_eq_sum_atomMass hS ν, meanMap_eq_sum_atomMass hS ν, h]

omit [Nonempty J] [Fintype X] [MeasurableSingletonClass X] hν in
/-- The atom masses at `θ = 0` are the reference masses. -/
theorem atomMass_zero : atomMass S ν (0 : J → ℝ) = fun x ↦ ν.real {x} := by
  funext x
  unfold atomMass
  rw [familyMeasure_zero_eq hS ν]

omit [Nonempty X] [Nonempty J] [Fintype X] [MeasurableSingletonClass X] hν
  [IsProbabilityMeasure ν] in
variable (S) in
/-- The direction loss as a linear map `W → (X → ℝ)`. -/
noncomputable def dirLossLin : 𝕍 →ₗ[ℝ] (X → ℝ) where
  toFun θ := dirLoss S (θ : J → ℝ)
  map_add' θ η := by
    rw [Submodule.coe_add, dirLoss_add]
    rfl
  map_smul' c θ := by
    rw [Submodule.coe_smul, dirLoss_smul]
    rfl

omit [Nonempty X] [Nonempty J] [Fintype X] [MeasurableSingletonClass X] hν
  [IsProbabilityMeasure ν] in
variable (S) in
/-- **The log-lift** `L : W → (X → ℝ)/ℝ𝟙`, `L(θ) = [x ↦ ⟨θ, S(x)⟩]`. -/
noncomputable def logLift : 𝕍 →ₗ[ℝ] ((X → ℝ) ⧸ (ℝ ∙ (1 : X → ℝ))) :=
  (Submodule.mkQ _).comp (dirLossLin S ν)

omit [Nonempty X] [Nonempty J] [Fintype X] [MeasurableSingletonClass X] hS hν
  [IsProbabilityMeasure ν] in
theorem logLift_apply (θ : 𝕍) :
    logLift S ν θ = Submodule.Quotient.mk (dirLoss S (θ : J → ℝ)) := rfl

omit [Nonempty X] [Nonempty J] [Fintype X] [MeasurableSingletonClass X] hν
  [IsProbabilityMeasure ν] in
/-- The log-lift is injective: a direction with constant loss contrast is invisible. -/
theorem logLift_injective : Function.Injective (logLift S ν) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro θ hθ
  rw [logLift_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton] at hθ
  obtain ⟨c, hc⟩ := hθ
  have he : (θ : J → ℝ) ∈ invisibleSet ν S := by
    refine ⟨c, ae_of_all _ fun x ↦ ?_⟩
    have := congrFun hc x
    simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at this
    exact this.symm
  exact Subtype.ext (eq_zero_of_invisible_of_mem_dirSpan (μ := ν) measurable_const
    (fun _ ↦ one_pos) hS he θ.2)

omit [MeasurableSpace X] [Nonempty J] [MeasurableSingletonClass X] hν [IsProbabilityMeasure ν]
  hS in
/-- The quotient by the constants has dimension `|X| − 1`. -/
theorem finrank_quotient_constants :
    Module.finrank ℝ ((X → ℝ) ⧸ (ℝ ∙ (1 : X → ℝ))) = Fintype.card X - 1 := by
  have h := Submodule.finrank_quotient_add_finrank (ℝ ∙ (1 : X → ℝ))
  have h1 : (1 : X → ℝ) ≠ 0 := fun h0 ↦ by
    have := congrFun h0 (Classical.arbitrary X)
    simp at this
  rw [finrank_span_singleton h1, Module.finrank_fintype_fun_eq_card] at h
  omega

set_option linter.unusedFintypeInType false in
/-- The log-lift is bijective for an affinely spanning family (dimension count). -/
theorem logLift_bijective (hspan : SpansAffine S ν) : Function.Bijective (logLift S ν) := by
  refine ⟨logLift_injective hS ν, ?_⟩
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  · exact logLift_injective hS ν
  · rw [finrank_dirSpan_eq_card_sub_one hS ν hν hspan, finrank_quotient_constants (X := X)]

/-- **The log-lift isomorphism** `W ≃ (X → ℝ)/ℝ𝟙`. -/
noncomputable def logEquiv (hspan : SpansAffine S ν) : 𝕍 ≃ₗ[ℝ] ((X → ℝ) ⧸ (ℝ ∙ (1 : X → ℝ))) :=
  LinearEquiv.ofBijective (logLift S ν) (logLift_bijective hS ν hν hspan)

/-- The linear inverse of the log-lift, precomposed with the quotient map. -/
noncomputable def logInv (hspan : SpansAffine S ν) : (X → ℝ) →ₗ[ℝ] 𝕍 :=
  (logEquiv hS ν hν hspan).symm.toLinearMap.comp (Submodule.mkQ _)

/-- **The inverse of the atom-mass map**: `p ↦ L⁻¹[−log(p/ν)]`. -/
noncomputable def simplexInv (hspan : SpansAffine S ν) (p : X → ℝ) : 𝕍 :=
  logInv hS ν hν hspan fun x ↦ -Real.log (p x / ν.real {x})

/-- The loss contrast of `B⁻¹(p)` is `−log(p/ν)` up to a constant. -/
theorem dirLoss_simplexInv (hspan : SpansAffine S ν) (p : X → ℝ) :
    ∃ c : ℝ, ∀ x, dirLoss S (simplexInv hS ν hν hspan p : J → ℝ) x =
      -Real.log (p x / ν.real {x}) + c := by
  have h : logLift S ν (simplexInv hS ν hν hspan p) =
      Submodule.Quotient.mk fun x ↦ -Real.log (p x / ν.real {x}) := by
    change (logEquiv hS ν hν hspan) ((logEquiv hS ν hν hspan).symm
      (Submodule.mkQ _ fun x ↦ -Real.log (p x / ν.real {x}))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [logLift_apply, Submodule.Quotient.eq, Submodule.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun x ↦ ?_⟩
  have := congrFun hc x
  simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, Pi.sub_apply] at this
  linarith

omit [Nonempty X] [Nonempty J] [Fintype X] [MeasurableSingletonClass X] hS in
/-- The reference masses are positive. -/
theorem measureReal_singleton_pos_of_ne_zero (x : X) : 0 < ν.real {x} := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (hν x) (measure_ne_top _ _)

omit [Nonempty X] [Nonempty J] hS hν in
/-- The normaliser as a finite sum. -/
theorem famZ_eq_sum (θ : J → ℝ) : famZ S ν θ = ∑ x, ν.real {x} * famWeight S θ x := by
  unfold famZ
  rw [integral_fintype (integrable_of_bdd_prob _ (bdd_of_fintype _))]
  rfl

/-- **`B ∘ B⁻¹ = id` on the open simplex.** -/
theorem atomMass_simplexInv (hspan : SpansAffine S ν) {p : X → ℝ} (hp : p ∈ posSimplex X) :
    atomMass S ν (simplexInv hS ν hν hspan p : J → ℝ) = p := by
  obtain ⟨c, hc⟩ := dirLoss_simplexInv hS ν hν hspan p
  set θ : J → ℝ := (simplexInv hS ν hν hspan p : J → ℝ) with hθ
  have hw : ∀ x, famWeight S θ x = p x / ν.real {x} * Real.exp (-c) := by
    intro x
    unfold famWeight
    rw [hc x, neg_add, neg_neg, Real.exp_add,
      Real.exp_log (div_pos (hp.1 x) (measureReal_singleton_pos_of_ne_zero ν hν x))]
  have hZ : famZ S ν θ = Real.exp (-c) := by
    rw [famZ_eq_sum ν θ]
    have : ∀ x, ν.real {x} * famWeight S θ x = p x * Real.exp (-c) := by
      intro x
      rw [hw x]
      field_simp [(measureReal_singleton_pos_of_ne_zero ν hν x).ne']
    simp only [this, ← Finset.sum_mul, hp.2, one_mul]
  funext x
  rw [atomMass_eq hS ν θ x]
  unfold famDens
  rw [hw x, hZ]
  field_simp [(measureReal_singleton_pos_of_ne_zero ν hν x).ne', (Real.exp_pos (-c)).ne']

omit [Nonempty J] in
/-- The atom masses lie in the open simplex. -/
theorem atomMass_mem_posSimplex (θ : J → ℝ) : atomMass S ν θ ∈ posSimplex X :=
  ⟨atomMass_pos hS ν hν θ, sum_atomMass hS ν θ⟩

/-- **`B⁻¹ ∘ B = id` on the direction space.** -/
theorem simplexInv_atomMass (hspan : SpansAffine S ν) (θ : 𝕍) :
    simplexInv hS ν hν hspan (atomMass S ν (θ : J → ℝ)) = θ :=
  atomMass_injective hS ν
    (atomMass_simplexInv hS ν hν hspan (atomMass_mem_posSimplex hS ν hν (θ : J → ℝ)))

/-- **The simplex identification** `W ≃ Δ°`. -/
noncomputable def simplexEquiv (hspan : SpansAffine S ν) : 𝕍 ≃ posSimplex X where
  toFun θ := ⟨atomMass S ν (θ : J → ℝ), atomMass_mem_posSimplex hS ν hν (θ : J → ℝ)⟩
  invFun p := simplexInv hS ν hν hspan p
  left_inv θ := simplexInv_atomMass hS ν hν hspan θ
  right_inv p := Subtype.ext (atomMass_simplexInv hS ν hν hspan p.2)

theorem simplexEquiv_apply (hspan : SpansAffine S ν) (θ : 𝕍) :
    (simplexEquiv hS ν hν hspan θ : X → ℝ) = atomMass S ν (θ : J → ℝ) := rfl

omit [Nonempty X] [Nonempty J] [Fintype X] [MeasurableSingletonClass X] hS hν
  [IsProbabilityMeasure ν] in
/-- The loss contrast is smooth in the direction. -/
theorem contDiff_dirLoss_coe (x : X) : ContDiff ℝ ∞ fun θ : 𝕍 ↦ dirLoss S (θ : J → ℝ) x := by
  unfold dirLoss
  exact ContDiff.sum fun j _ ↦
    ((contDiff_apply ℝ ℝ j).comp (Submodule.subtypeL _).contDiff).mul contDiff_const

omit [Nonempty X] [Nonempty J] hν in
/-- **The atom-mass map is smooth** on the direction space. -/
theorem contDiff_atomMass : ContDiff ℝ ∞ fun θ : 𝕍 ↦ atomMass S ν (θ : J → ℝ) := by
  have hw : ∀ x, ContDiff ℝ ∞ fun θ : 𝕍 ↦ famWeight S (θ : J → ℝ) x := fun x ↦
    Real.contDiff_exp.comp (contDiff_dirLoss_coe ν x).neg
  have hZ : ContDiff ℝ ∞ fun θ : 𝕍 ↦ famZ S ν (θ : J → ℝ) := by
    have : (fun θ : 𝕍 ↦ famZ S ν (θ : J → ℝ)) =
        fun θ : 𝕍 ↦ ∑ x, ν.real {x} * famWeight S (θ : J → ℝ) x := by
      funext θ; exact famZ_eq_sum ν _
    rw [this]
    exact ContDiff.sum fun x _ ↦ contDiff_const.mul (hw x)
  rw [contDiff_pi]
  intro x
  have : (fun θ : 𝕍 ↦ atomMass S ν (θ : J → ℝ) x) =
      fun θ : 𝕍 ↦ famWeight S (θ : J → ℝ) x / famZ S ν (θ : J → ℝ) * ν.real {x} := by
    funext θ; rw [atomMass_eq hS ν]; rfl
  rw [this]
  exact ((hw x).div hZ fun θ ↦ (famZ_pos hS ν _).ne').mul contDiff_const

/-- **The inverse of the atom-mass map is smooth on the positive orthant.** -/
theorem contDiffOn_simplexInv (hspan : SpansAffine S ν) :
    ContDiffOn ℝ ∞ (simplexInv hS ν hν hspan) {p : X → ℝ | ∀ x, 0 < p x} := by
  have hlin : ContDiff ℝ ∞ (logInv hS ν hν hspan) :=
    (LinearMap.toContinuousLinearMap (logInv hS ν hν hspan)).contDiff
  refine hlin.comp_contDiffOn ?_
  refine contDiffOn_pi.2 fun x ↦ ?_
  refine ContDiffOn.neg ?_
  refine ContDiffOn.log ((contDiff_apply ℝ ℝ x).contDiffOn.div_const _) fun p hp ↦ ?_
  exact (div_pos (hp x) (measureReal_singleton_pos_of_ne_zero ν hν x)).ne'

/-- **The simplex homeomorphism** `W ≃ₜ Δ°`. -/
noncomputable def simplexHomeomorph (hspan : SpansAffine S ν) : 𝕍 ≃ₜ posSimplex X where
  toEquiv := simplexEquiv hS ν hν hspan
  continuous_toFun := (contDiff_atomMass hS ν).continuous.subtype_mk _
  continuous_invFun :=
    (contDiffOn_simplexInv hS ν hν hspan).continuousOn.comp_continuous continuous_subtype_val
      fun p ↦ p.2.1

set_option linter.unusedFintypeInType false in
/-- **The featureless journey is the mixture segment in the simplex**: for `t ∈ [0,1]`,
`B(θ_t) = (1 − t) ν{·} + t B(θ₁)` along the model journey from `θ = 0` to `θ₁`. -/
theorem atomMass_modelJourney_zero (hspan : SpansAffine S ν) (θ₁ : 𝕍) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    atomMass S ν (modelJourney hS ν 0 θ₁ t : J → ℝ) =
      fun x ↦ (1 - t) * ν.real {x} + t * atomMass S ν (θ₁ : J → ℝ) x := by
  set p : X → ℝ := fun x ↦ (1 - t) * ν.real {x} + t * atomMass S ν (θ₁ : J → ℝ) x with hp
  have hpos : ∀ x, 0 < p x := by
    intro x
    have h1 := measureReal_singleton_pos_of_ne_zero ν hν x
    have h2 := atomMass_pos hS ν hν (θ₁ : J → ℝ) x
    rcases lt_or_eq_of_le ht1 with h | h
    · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) h1) (mul_nonneg ht0 h2.le)
    · rw [hp]; simp only [h, sub_self, zero_mul, one_mul, zero_add]; exact h2
  have hsum : ∑ x, p x = 1 := by
    simp only [hp, Finset.sum_add_distrib, ← Finset.mul_sum, sum_measureReal_singleton,
      Finset.coe_univ, probReal_univ, sum_atomMass hS ν]
    ring
  have hpΔ : p ∈ posSimplex X := ⟨hpos, hsum⟩
  have hB := atomMass_simplexInv hS ν hν hspan hpΔ
  -- the inverse image of `p` has the mean of the model journey
  have hmean : mean (simplexInv hS ν hν hspan p : J → ℝ) =
      mean (modelJourney hS ν 0 θ₁ t : J → ℝ) := by
    rw [meanMap_modelJourney hS ν (Icc_subset_modelJourneyDomain hS ν 0 θ₁ ⟨ht0, ht1⟩),
      meanMap_eq_sum_atomMass hS ν, hB, meanMap_eq_sum_atomMass hS ν (θ₁ : J → ℝ),
      meanMap_eq_sum_atomMass hS ν ((0 : 𝕍) : J → ℝ), Submodule.coe_zero, atomMass_zero hS ν]
    funext j
    simp only [hp, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, mul_sub, ← Finset.mul_sum, mul_assoc]
    ring
  rw [← meanMap_injective_dirSpan hS ν hmean, hB]

set_option linter.unusedFintypeInType false in
/-- **Affine expectations along the featureless journey**:
`E_{θ_t} F = (1 − t) E_ν F + t E_{θ₁} F`. -/
theorem integral_familyMeasure_modelJourney_zero (hspan : SpansAffine S ν) (θ₁ : 𝕍) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (F : X → ℝ) :
    ∫ x, F x ∂Pfam (modelJourney hS ν 0 θ₁ t : J → ℝ) =
      (1 - t) * ∫ x, F x ∂ν + t * ∫ x, F x ∂Pfam (θ₁ : J → ℝ) := by
  rw [integral_familyMeasure_eq_sum hS ν, atomMass_modelJourney_zero hS ν hν hspan θ₁ ht0 ht1,
    integral_familyMeasure_eq_sum hS ν,
    integral_fintype (integrable_of_bdd_prob _ (bdd_of_fintype F))]
  simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ ↦ by ring

set_option linter.unusedFintypeInType false in
/-- **The exact mixture identity for the posterior variance along the featureless journey**:
`Var_{θ_t} F = (1−t) Var_ν F + t Var_{θ₁} F + t(1−t)(E_{θ₁}F − E_ν F)²`. -/
theorem lawCov_modelJourney_zero (hspan : SpansAffine S ν) (θ₁ : 𝕍) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (F : X → ℝ) :
    lawCov (Pfam (modelJourney hS ν 0 θ₁ t : J → ℝ)) F F =
      (1 - t) * lawCov ν F F + t * lawCov (Pfam (θ₁ : J → ℝ)) F F +
        t * (1 - t) * ((∫ x, F x ∂Pfam (θ₁ : J → ℝ)) - ∫ x, F x ∂ν) ^ 2 := by
  unfold lawCov
  rw [integral_familyMeasure_modelJourney_zero hS ν hν hspan θ₁ ht0 ht1 F,
    integral_familyMeasure_modelJourney_zero hS ν hν hspan θ₁ ht0 ht1 (fun x ↦ F x * F x)]
  ring

end Simplex

end Laplace.Multi
