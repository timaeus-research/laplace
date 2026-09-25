/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.MeanJourney
import Laplace.Multi.NaturalJourney

/-!
# The full mean chart: the relative entropy is concave in the full mean coordinates

The joint family `P_θ ∝ e^{−θ·S} π`, `S = (L₀, R)`, `θ ∈ ℝ^{Option ι}`, is itself an affine family
(base loss `0`, features `S`, temperature `1`), so the response geometry of `DualPotential` and
`MeanJourney` applies to it verbatim under the joint nondegeneracy hypothesis (no nontrivial
combination of `L₀` and the `Rᵢ` is a.s. constant). The **full mean** `μ(θ) = ⟨S⟩_θ` (`fullMean`) is
the mean map of this family, and the relative entropy to the prior is its entropy in mean
coordinates: `𝒮(θ) = −KL(P_θ ‖ π̄) = 𝒮^{full}(μ(θ))` (`relEntropy_eq_meanEntropy`). Consequently

* **`𝒮` is concave in the full mean coordinates** (`relEntropy_concaveOn_fullMean`), with
  gradient `θ` — `d/ds 𝒮(μ₀ + sΔ) = ⟨Δ, θ(s)⟩` (`hasDerivAt_relEntropy_fullMean_line`) — and
  second derivative `−Δ ⬝ G_{θ(s)}⁻¹ Δ` along full mean segments
  (`hasDerivAt_relEntropy_fullMean_line_deriv`), where `G_θ = Cov_θ(S, S)` is the full Fisher form;
* **the two journeys from the featureless point** spend the same information: with
  `Δ = μ(θ) − μ(0)`,

  `∫₀¹ s G_{sθ}(θ, θ) ds = KL(P_θ ‖ π̄) = ∫₀¹ (1 − s) Δ ⬝ G_{θ(μ(0) + sΔ)}⁻¹ Δ ds`

  (`natRay_cost_eq_fullMean_cost`, `relEntropy_eq_neg_integral_fullMean`): the covariance along
  the natural ray, weighted by `s`, and the inverse covariance along the straight full mean
  journey, weighted by `1 − s`;
* the entropy decreases along the full mean journey from the featureless point
  (`relEntropy_fullMean_line_antitoneOn`).

This is the capstone of the round-38 consult in the full (not sliced) geometry: the map of
responses from the featureless distribution of maximal relative entropy to the data is the
straight segment of full means, along which the entropy falls concavely at the rate of the inverse
Fisher form.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The full mean `μ(θ) = ⟨S⟩_θ = (⟨L₀⟩_θ, ⟨R⟩_θ)` of the joint family. -/
noncomputable def fullMean (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (θ : Option ι → ℝ) :
    Option ι → ℝ :=
  meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 θ

omit [MeasurableSpace X] [Fintype ι] in
/-- The base loss of the joint family is bounded by `0`. -/
theorem abs_zero_fun_le (x : X) : |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := by simp

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
  (hjnd : ∀ v : Option ι → ℝ, v ≠ 0 →
    ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss (jointStat L₀ R) v x = c)
include hπm hπi hπ hπpos hL₀m hL₀ hR hjnd

/-- The relative entropy to the prior is the mean-coordinate entropy of the joint family. -/
theorem relEntropy_eq_meanEntropy (θ : Option ι → ℝ) :
    relEntropy μ π L₀ R θ =
      meanEntropy μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (fullMean μ π L₀ R θ) := by
  unfold fullMean
  rw [meanEntropy_meanMap hπm hπi hπ hπpos measurable_const abs_zero_fun_le
    (bdd_jointStat hL₀m hL₀ hR) one_pos hjnd θ]
  rfl

/-- The full mean lies in the interior of the joint moment body. -/
theorem fullMean_mem_interior (θ : Option ι → ℝ) :
    fullMean μ π L₀ R θ ∈ interior (momentBody μ π (jointStat L₀ R)) :=
  meanMap_mem_interior hπm hπi hπ hπpos measurable_const abs_zero_fun_le
    (bdd_jointStat hL₀m hL₀ hR) one_pos hjnd θ

/-- **The relative entropy is concave in the full mean coordinates.** -/
theorem relEntropy_concaveOn_fullMean :
    ConcaveOn ℝ (Set.range (fullMean μ π L₀ R))
      (fun M ↦ relEntropy μ π L₀ R (Function.invFun (fullMean μ π L₀ R) M)) :=
  meanEntropy_concaveOn hπm hπi hπ hπpos measurable_const abs_zero_fun_le
    (bdd_jointStat hL₀m hL₀ hR) one_pos hjnd

/-- **The gradient of the relative entropy in full mean coordinates is the natural coordinate**:
`d/ds 𝒮(μ₀ + sΔ) = ⟨Δ, θ(s)⟩`. -/
theorem hasDerivAt_relEntropy_fullMean_line {y₀ d : Option ι → ℝ} {s : ℝ}
    (hM : y₀ + s • d ∈ interior (momentBody μ π (jointStat L₀ R))) :
    HasDerivAt (fun s ↦ relEntropy μ π L₀ R (Function.invFun (fullMean μ π L₀ R) (y₀ + s • d)))
      (dotJ d (meanLine μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 y₀ d s)) s := by
  have h := hasDerivAt_meanEntropy_line hπm hπi hπ hπpos measurable_const abs_zero_fun_le
    (bdd_jointStat hL₀m hL₀ hR) one_pos hjnd hM
  exact h.congr_deriv (one_mul _)

/-- **The Hessian of the relative entropy in full mean coordinates is minus the inverse Fisher
form**: `d/ds ⟨Δ, θ(s)⟩ = −Δ ⬝ G_{θ(s)}⁻¹ Δ`. -/
theorem hasDerivAt_relEntropy_fullMean_line_deriv [DecidableEq ι] {y₀ d : Option ι → ℝ} {s : ℝ}
    (hM : y₀ + s • d ∈ interior (momentBody μ π (jointStat L₀ R))) :
    HasDerivAt (fun s ↦ dotJ d (meanLine μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 y₀ d s))
      (-meanSpeed μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 y₀ d s) s := by
  have h := hasDerivAt_meanEntropy_line_deriv hπm hπi hπ hπpos measurable_const abs_zero_fun_le
    (bdd_jointStat hL₀m hL₀ hR) one_pos hjnd hM
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun u ↦ (one_mul _).symm)

/-- **The two journeys from the featureless point spend the same information**: the Fisher form
along the natural ray, weighted by `s`, equals the inverse Fisher form along the straight full mean
journey, weighted by `1 − s`. -/
theorem natRay_cost_eq_fullMean_cost [DecidableEq ι] (θ : Option ι → ℝ) :
    ∫ s in (0 : ℝ)..1, s * natForm μ π L₀ R (s • θ) θ θ =
      ∫ s in (0 : ℝ)..1, (1 - s) * meanSpeed μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1
        (fullMean μ π L₀ R 0) (fullMean μ π L₀ R θ - fullMean μ π L₀ R 0) s := by
  have h := famKL_e_journey_eq_m_journey hπm hπi hπ hπpos measurable_const abs_zero_fun_le
    (bdd_jointStat hL₀m hL₀ hR) one_pos hjnd 0 θ
  rw [one_pow, one_mul] at h
  unfold fullMean
  rw [← h]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  simp [segVar, natForm]

/-- The information from the featureless point through the full mean journey:
`KL(P_θ ‖ π̄) = ∫₀¹ (1 − s) Δ ⬝ G⁻¹ Δ ds`. -/
theorem relEntropy_eq_neg_integral_fullMean [DecidableEq ι] (θ : Option ι → ℝ) :
    relEntropy μ π L₀ R θ =
      -∫ s in (0 : ℝ)..1, (1 - s) * meanSpeed μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1
        (fullMean μ π L₀ R 0) (fullMean μ π L₀ R θ - fullMean μ π L₀ R 0) s := by
  rw [relEntropy_eq_meanEntropy hπm hπi hπ hπpos hL₀m hL₀ hR hjnd θ]
  exact meanEntropy_eq_neg_integral hπm hπi hπ hπpos measurable_const abs_zero_fun_le
    (bdd_jointStat hL₀m hL₀ hR) one_pos hjnd θ

/-- **Entropy decreases along the full mean journey from the featureless point.** -/
theorem relEntropy_fullMean_line_antitoneOn {y₁ : Option ι → ℝ}
    (h₁ : y₁ ∈ interior (momentBody μ π (jointStat L₀ R))) :
    AntitoneOn (fun s : ℝ ↦ relEntropy μ π L₀ R (Function.invFun (fullMean μ π L₀ R)
      (fullMean μ π L₀ R 0 + s • (y₁ - fullMean μ π L₀ R 0)))) (Icc 0 1) :=
  meanEntropy_line_antitoneOn hπm hπi hπ hπpos measurable_const abs_zero_fun_le
    (bdd_jointStat hL₀m hL₀ hR) one_pos hjnd h₁

end

end Laplace.Multi
