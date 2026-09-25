/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.EntropyProjection
import Laplace.Multi.AnnealingRay
import Laplace.Multi.RelativeEntropyGeometry
import Laplace.Multi.ReducedPotential
import Laplace.Multi.TemperatureSlice

/-!
# The transport law: expectations move by covariance

**The master transport identity.** For a probability law `ν`, bounded `f`, `g` and the exponential
tilts `ν_s = ν.tilted (s f)` (Mathlib's `Measure.tilted`),
  `d/ds E_{ν_s} g = Cov_{ν_s}(g, f)`       (`hasDerivAt_integral_tilted`)
and the information accumulated relative to `ν` grows by the fluctuation energy,
  `d/ds KL(ν_s ‖ ν) = s Var_{ν_s}(f)`      (`hasDerivAt_klDiv_tilted_toReal`).
This is the change of posterior expectation values with the change of the data law, for every
bounded perturbation `f` of the log-density and every bounded observable `g`.

**The thermal journey.** The affine family is the tilt of the prior `π̄ = P_{0,0}` by `−t H_a`,
`H_a = L₀ + a·R` (`familyMeasure_eq_tilted_prior`, through the joint family:
`familyMeasure_natCoord`),
so along the temperature path at fixed `a`, from the featureless prior at `t = 0`:
* `KL(P_{t,a} ‖ π̄) = −𝒮(t, a)` in Mathlib's divergence (`klDiv_familyMeasure_prior`);
* `d/dt 𝒮(t, a) = −t Var_{t,a}(H_a)` (`hasDerivAt_relEntropy_temp_fixed`), hence
  `KL(P_{t,a} ‖ π̄) = ∫₀ᵗ s Var_{s,a}(H_a) ds` (`klDiv_familyMeasure_prior_eq_integral`) and
  `d/dt KL(P_{t,a} ‖ π̄) = t Var_{t,a}(H_a)` (`hasDerivAt_klDiv_familyMeasure_prior_toReal`);
* the response moves by covariance, `d/dt ⟨φ⟩_{t,a} = −Cov_{t,a}(φ, H_a)`
  (`hasDerivAt_priorExp_temp` of `AnnealingRay`; for `φ = R i` this is the trajectory of the
  response).

**The rate along the temperature.** At a fixed interior response `M`,
  `∂_t 𝓘_t(M) = E_{P_{t,θ_t(M)}} L₀ − E_{Q_t} L₀`      (`hasDerivAt_rateFun_temp_toReal`),
the difference of the loss expectations at the response `M` and at the featureless member; the same
holds for the constrained relative entropy (`hasDerivAt_entropyProj_temp_toReal`). The already
proved `∂_t I_t(M) = obsMean` is not by itself the derivative of the rate: the normaliser `A_t(0)`
contributes `−E_{Q_t} L₀`.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section General

variable (ν : Measure X) [IsProbabilityMeasure ν]

omit [Fintype ι] [IsProbabilityMeasure ν] in
/-- The seabed's tilted expectation with unit weight is the expectation under Mathlib's tilt. -/
theorem tiltExp_one_eq_integral_tilted (f g : X → ℝ) (s : ℝ) :
    tiltExp ν (fun _ ↦ (1 : ℝ)) g f (-1) s = ∫ x, g x ∂ν.tilted (fun x ↦ s * f x) := by
  rw [integral_tilted]
  unfold tiltExp tiltNum
  simp only [mul_one, smul_eq_mul, div_mul_eq_mul_div]
  rw [integral_div]
  congr 1
  · exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      beta_reduce
      rw [mul_comm, show -(-1 * f x * s) = s * f x by ring])
  · exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      beta_reduce
      rw [one_mul, show -(-1 * f x * s) = s * f x by ring])

omit [Fintype ι] in
/-- **The master transport identity**: `d/ds E_{ν_s} g = Cov_{ν_s}(g, f)` along the tilts
`ν_s = ν.tilted (s f)`. -/
theorem hasDerivAt_integral_tilted [Nonempty X] {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g)
    (s₀ : ℝ) :
    HasDerivAt (fun s ↦ ∫ x, g x ∂ν.tilted (fun x ↦ s * f x))
      (∫ x, g x * f x ∂ν.tilted (fun x ↦ s₀ * f x) -
        (∫ x, g x ∂ν.tilted (fun x ↦ s₀ * f x)) * ∫ x, f x ∂ν.tilted (fun x ↦ s₀ * f x)) s₀ := by
  obtain ⟨hfm, Mf, hfb⟩ := hf
  obtain ⟨hgm, Mg, hgb⟩ := hg
  have hT : TiltData ν (fun _ ↦ (1 : ℝ)) f Mf :=
    ⟨measurable_const, integrable_const _, fun _ ↦ zero_le_one, by simp, hfm, hfb⟩
  have h := hT.hasDerivAt_tiltExp hgm hgb (-1) s₀
  simp only [neg_neg, one_mul, tiltCov] at h
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun s ↦
    (tiltExp_one_eq_integral_tilted ν f g s).symm)).congr_deriv ?_
  rw [tiltExp_one_eq_integral_tilted, tiltExp_one_eq_integral_tilted,
    tiltExp_one_eq_integral_tilted]

omit [Fintype ι] in
/-- `d/ds ∫ e^{s f} dν = ∫ f e^{s f} dν` for bounded `f`. -/
theorem hasDerivAt_integral_exp_mul [Nonempty X] {f : X → ℝ} (hf : Bdd f) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ ∫ x, Real.exp (s * f x) ∂ν) (∫ x, f x * Real.exp (s₀ * f x) ∂ν) s₀ := by
  obtain ⟨hfm, Mf, hfb⟩ := hf
  have hT : TiltData ν (fun _ ↦ (1 : ℝ)) f Mf :=
    ⟨measurable_const, integrable_const _, fun _ ↦ zero_le_one, by simp, hfm, hfb⟩
  have h := hT.hasDerivAt_tiltNum (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1)
    (fun _ ↦ by simp) (-1) s₀
  simp only [neg_neg, one_mul, tiltNum, mul_one] at h
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)).congr_deriv ?_
  · exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      beta_reduce
      rw [show -(-1 * f x * s) = s * f x by ring])
  · exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      beta_reduce
      rw [show -(-1 * f x * s₀) = s₀ * f x by ring])

omit [Fintype ι] [IsProbabilityMeasure ν] in
/-- `E_{ν_s} f = (∫ f e^{s f} dν) / ∫ e^{s f} dν`. -/
theorem integral_tilted_eq_div (f : X → ℝ) (s : ℝ) :
    ∫ x, f x ∂ν.tilted (fun x ↦ s * f x) =
      (∫ x, f x * Real.exp (s * f x) ∂ν) / ∫ x, Real.exp (s * f x) ∂ν := by
  rw [integral_tilted]
  simp only [smul_eq_mul, div_mul_eq_mul_div]
  rw [integral_div]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)

omit [Fintype ι] in
/-- **Information grows by the fluctuation energy**: `d/ds KL(ν_s ‖ ν) = s Var_{ν_s}(f)`. -/
theorem hasDerivAt_klDiv_tilted_toReal [Nonempty X] {f : X → ℝ} (hf : Bdd f) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ (klDiv (ν.tilted (fun x ↦ s * f x)) ν).toReal)
      (s₀ * (∫ x, f x * f x ∂ν.tilted (fun x ↦ s₀ * f x) -
        (∫ x, f x ∂ν.tilted (fun x ↦ s₀ * f x)) * ∫ x, f x ∂ν.tilted (fun x ↦ s₀ * f x))) s₀ := by
  have hrep : ∀ s, (klDiv (ν.tilted (fun x ↦ s * f x)) ν).toReal =
      s * ∫ x, f x ∂ν.tilted (fun x ↦ s * f x) - Real.log (∫ x, Real.exp (s * f x) ∂ν) := fun s ↦ by
    rw [klDiv_tilted_eq ν (Bdd.const_mul s hf),
      ENNReal.toReal_ofReal (integral_sub_log_nonneg ν (Bdd.const_mul s hf)), integral_const_mul]
  have h1 := hasDerivAt_integral_tilted ν hf hf s₀
  have h2 := hasDerivAt_integral_exp_mul ν hf s₀
  have hZpos : 0 < ∫ x, Real.exp (s₀ * f x) ∂ν :=
    integral_exp_pos (integrable_exp_of_bdd ν (Bdd.const_mul s₀ hf))
  have h3 := h2.log hZpos.ne'
  have h := ((hasDerivAt_id s₀).mul h1).sub h3
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ hrep s)).congr_deriv ?_
  rw [← integral_tilted_eq_div ν f s₀]
  simp only [id_eq]
  ring

end General

section Family

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hπm hπi hπ hπpos hL₀m hL₀ hR

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
/-- The joint family at the natural coordinates is the affine family. -/
theorem familyMeasure_natCoord (t : ℝ) (a : ι → ℝ) :
    familyMeasure μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (natCoord t a) =
      familyMeasure μ π L₀ R t a := by
  unfold familyMeasure
  rw [priorZ_natCoord]
  congr 1
  funext x
  rw [affLoss_zero_jointStat_natCoord]
  simp only [add_zero, one_mul]

omit [Fintype ι] [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
theorem natCoord_zero_eq (a : ι → ℝ) : natCoord (0 : ℝ) a = 0 := by
  funext j
  cases j <;> simp [natCoord, Option.elim]

/-- **The information distance to the prior is minus the relative entropy**, in Mathlib's
divergence: `KL(P_{t,a} ‖ π̄) = −𝒮(t, a)`, with `π̄ = P_{0,0}` the prior. -/
theorem klDiv_familyMeasure_prior (t : ℝ) (a : ι → ℝ) :
    klDiv (familyMeasure μ π L₀ R t a) (familyMeasure μ π L₀ R 0 0) =
      ENNReal.ofReal (-relEntropy μ π L₀ R (natCoord t a)) := by
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  rw [← familyMeasure_natCoord t a, ← familyMeasure_natCoord 0 0, natCoord_zero_eq,
    klDiv_familyMeasure_zero hπm hπi hπ hπpos measurable_const h0 hS' one_pos (natCoord t a)]
  unfold relEntropy famKL
  rw [neg_neg]

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
/-- The prior is the family member at zero temperature (any `a`). -/
theorem familyMeasure_zero_temp (a : ι → ℝ) :
    familyMeasure μ π L₀ R 0 a = familyMeasure μ π L₀ R 0 0 := by
  rw [← familyMeasure_natCoord 0 a, natCoord_zero_eq, ← natCoord_zero_eq (0 : ι → ℝ),
    familyMeasure_natCoord]

/-- **The family is the tilt of the prior by `−t H_a`.** -/
theorem familyMeasure_eq_tilted_prior (t : ℝ) (a : ι → ℝ) :
    familyMeasure μ π L₀ R t a =
      (familyMeasure μ π L₀ R 0 0).tilted (fun x ↦ -t * affLoss L₀ R a x) := by
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  rw [← familyMeasure_natCoord t a, ← familyMeasure_natCoord 0 0, natCoord_zero_eq,
    familyMeasure_eq_tilted hπm hπi hπ hπpos measurable_const h0 hS' one_pos (natCoord t a)]
  congr 1
  funext x
  rw [dirLoss_jointStat_natCoord]
  ring

/-- **Along the thermal path the relative entropy decreases at the rate `t Var_{t,a}(H_a)`.** -/
theorem hasDerivAt_relEntropy_temp_fixed (a : ι → ℝ) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ relEntropy μ π L₀ R (natCoord t a))
      (-(t₀ * priorCov μ π (affLoss L₀ R a) (affLoss L₀ R a) (affLoss L₀ R a) t₀)) t₀ := by
  have hline : HasDerivAt (fun t : ℝ ↦ natCoord t a) (natCoord 1 a) t₀ := by
    have e : (fun t : ℝ ↦ natCoord t a) = fun t : ℝ ↦ t • natCoord 1 a :=
      funext fun t ↦ natCoord_eq_smul t a
    rw [e]
    simpa using (hasDerivAt_id t₀).smul_const (natCoord 1 a)
  have h := hasDerivAt_relEntropy_path hπm hπi hπ hπpos hL₀m hL₀ hR hline
  refine h.congr_deriv ?_
  unfold natForm
  rw [priorCov_natCoord]
  have e1 : dirLoss (jointStat L₀ R) (natCoord t₀ a) = fun x ↦ t₀ * affLoss L₀ R a x :=
    funext (dirLoss_jointStat_natCoord L₀ R t₀ a)
  have e2 : dirLoss (jointStat L₀ R) (natCoord 1 a) = affLoss L₀ R a :=
    funext fun x ↦ by rw [dirLoss_jointStat_natCoord, one_mul]
  rw [e1, e2, priorCov_const_mul_left]

/-- **The relative entropy along the thermal path is the integrated fluctuation energy**:
`𝒮(T, a) = −∫₀ᵀ s Var_{s,a}(H_a) ds`. -/
theorem relEntropy_natCoord_eq_neg_integral (a : ι → ℝ) (T : ℝ) :
    relEntropy μ π L₀ R (natCoord T a) =
      -∫ u in (0 : ℝ)..T,
        u * priorCov μ π (affLoss L₀ R a) (affLoss L₀ R a) (affLoss L₀ R a) u := by
  have hH : Bdd (affLoss L₀ R a) := bdd_affLoss hL₀m hL₀ hR a
  have hcont := continuous_priorCov_temp hπm hπi hπ hπpos hL₀m hL₀ hR a hH hH
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u ↦ -relEntropy μ π L₀ R (natCoord u a))
    (f' := fun u ↦ u * priorCov μ π (affLoss L₀ R a) (affLoss L₀ R a) (affLoss L₀ R a) u)
    (fun u _ ↦ ((hasDerivAt_relEntropy_temp_fixed hπm hπi hπ hπpos hL₀m hL₀ hR a
      u).neg).congr_deriv (neg_neg _)) ((continuous_id.mul hcont).intervalIntegrable 0 T)
  rw [h, natCoord_zero_eq, relEntropy_zero hπm hπi hπ hπpos hL₀m hL₀ hR]
  ring

/-- **Information acquired along the thermal journey**:
`KL(P_{T,a} ‖ π̄) = ∫₀ᵀ s Var_{s,a}(H_a) ds`. -/
theorem klDiv_familyMeasure_prior_eq_integral (a : ι → ℝ) (T : ℝ) :
    klDiv (familyMeasure μ π L₀ R T a) (familyMeasure μ π L₀ R 0 0) =
      ENNReal.ofReal (∫ u in (0 : ℝ)..T,
        u * priorCov μ π (affLoss L₀ R a) (affLoss L₀ R a) (affLoss L₀ R a) u) := by
  rw [klDiv_familyMeasure_prior hπm hπi hπ hπpos hL₀m hL₀ hR,
    relEntropy_natCoord_eq_neg_integral hπm hπi hπ hπpos hL₀m hL₀ hR, neg_neg]

/-- **The information distance to the prior grows at the rate `t Var_{t,a}(H_a)`.** -/
theorem hasDerivAt_klDiv_familyMeasure_prior_toReal (a : ι → ℝ) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ (klDiv (familyMeasure μ π L₀ R t a) (familyMeasure μ π L₀ R 0 0)).toReal)
      (t₀ * priorCov μ π (affLoss L₀ R a) (affLoss L₀ R a) (affLoss L₀ R a) t₀) t₀ := by
  have hrep : ∀ t, (klDiv (familyMeasure μ π L₀ R t a) (familyMeasure μ π L₀ R 0 0)).toReal =
      -relEntropy μ π L₀ R (natCoord t a) := fun t ↦ by
    rw [klDiv_familyMeasure_prior hπm hπi hπ hπpos hL₀m hL₀ hR,
      ENNReal.toReal_ofReal (neg_nonneg.2 (relEntropy_nonpos hπm hπi hπ hπpos hL₀m hL₀ hR _))]
  refine ((hasDerivAt_relEntropy_temp_fixed hπm hπi hπ hπpos hL₀m hL₀ hR a
    t₀).neg.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ hrep t)).congr_deriv ?_
  ring

section Rate

variable (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c) [Nonempty ι]
include hnd

/-- `𝓘_t(M) = I_t(M) + A_t(0)` at every positive temperature, for `M` in the response space. -/
theorem rateFun_toReal_eq {t : ℝ} (ht : 0 < t) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    (rateFun μ π L₀ R t M).toReal = dualPotential μ π L₀ R t M + affLogZ μ π L₀ R t 0 := by
  obtain ⟨a, ha⟩ : M ∈ Set.range (meanMap μ π L₀ R t) := by
    rw [range_meanMap_slice hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd]
    exact hM
  rw [← ha]
  exact rateFun_meanMap_toReal hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a

/-- **The temperature derivative of the rate at a fixed response**:
`∂_t 𝓘_t(M) = E_{P_{t,θ_t(M)}} L₀ − E_{Q_t} L₀`. -/
theorem hasDerivAt_rateFun_temp_toReal {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    HasDerivAt (fun t ↦ (rateFun μ π L₀ R t M).toReal)
      (obsMean μ π L₀ L₀ R t₀ M - priorExp μ π (affLoss L₀ R 0) L₀ t₀) t₀ := by
  have h1 := hasDerivAt_dualPotential_temp hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀ hM
  have h2 := hasDerivAt_affLogZ_temp hπm hπi hπ hπpos hL₀m hL₀ hR 0 t₀
  refine ((h1.add h2).congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Ioi_mem_nhds ht₀] with t ht
    exact rateFun_toReal_eq hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht hM
  · rw [dotJ_zero_left, add_zero]
    ring

/-- The same temperature derivative for the constrained relative entropy. -/
theorem hasDerivAt_entropyProj_temp_toReal {t₀ : ℝ} (ht₀ : 0 < t₀) {M : ι → ℝ}
    (hM : M ∈ interior (momentBody μ π R)) :
    HasDerivAt (fun t ↦ (entropyProj (familyMeasure μ π L₀ R t 0) R M).toReal)
      (obsMean μ π L₀ L₀ R t₀ M - priorExp μ π (affLoss L₀ R 0) L₀ t₀) t₀ := by
  refine (hasDerivAt_rateFun_temp_toReal hπm hπi hπ hπpos hL₀m hL₀ hR hnd ht₀
    hM).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht₀] with t ht
  obtain ⟨a, ha⟩ : M ∈ Set.range (meanMap μ π L₀ R t) := by
    rw [range_meanMap_slice hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd]
    exact hM
  rw [← ha, entropyProj_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht a]

end Rate

end Family

end Laplace.Multi
