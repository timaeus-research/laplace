/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.LegendreMaximum
import Laplace.Multi.TemperatureSlice

/-!
# Convexity of the dual potential and the variational principle of the temperature slices

* **Tangent inequality and convexity of `I`.** From the Legendre identity, `I(m(b)) ≥ I(m(a)) −
  t⟨a, m(b) − m(a)⟩` (`dualPotential_ge_tangent`) and `I` is convex on the response space
  (`dualPotential_convexOn`), as a maximum of affine functions.
* **The temperature slice is a constrained minimum.** In the joint family of `NaturalCoordinates`
  the dual potential `I(e, M)` has `∂_e I = −t` at the slice point `η(Θ(t,a))`
  (`partial_base_dualPotential`), and among all joint responses with the same contrast part `M`
  the slice point minimises `e ↦ I(e, M) + t e` (`slice_variational`): the temperature slice is the
  graph of the minimiser of the reduced potential `J_t(M) = inf_e (I(e, M) + t e)`, the constrained
  thermodynamics of the joint family.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section Tangent

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd

/-- **The tangent inequality of the dual potential**: `I(m(b)) ≥ I(m(a)) − t⟨a, m(b) − m(a)⟩`. -/
theorem dualPotential_ge_tangent (a b : ι → ℝ) :
    dualPotential μ π L₀ R t (meanMap μ π L₀ R t a) -
        t * dotJ a (meanMap μ π L₀ R t b - meanMap μ π L₀ R t a) ≤
      dualPotential μ π L₀ R t (meanMap μ π L₀ R t b) := by
  rw [dualPotential_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd,
    dualPotential_meanMap hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd]
  have h := dual_objective_le_at_mean hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) b a
  rw [(isLinearMap_dotJ a).map_sub]
  linarith

end Tangent

section Convex

variable [Nonempty ι] [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd

/-- **Convexity of the dual potential** on the response space (a maximum of affine functions). -/
theorem dualPotential_convexOn :
    ConvexOn ℝ (Set.range (meanMap μ π L₀ R t)) (dualPotential μ π L₀ R t) := by
  have hπ' : ∀ x, 0 ≤ π x := fun x ↦ (hπ x).le
  have hrange := range_meanMap_slice hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd
  have hconv : Convex ℝ (Set.range (meanMap μ π L₀ R t)) := by
    rw [hrange]; exact (convex_momentBody R).interior
  refine ⟨hconv, ?_⟩
  rintro _ ⟨a₁, rfl⟩ _ ⟨a₂, rfl⟩ l₁ l₂ hl₁ hl₂ hl
  obtain ⟨c, hc⟩ := hconv ⟨a₁, rfl⟩ ⟨a₂, rfl⟩ hl₁ hl₂ hl
  rw [← hc, dualPotential_meanMap hπm hπi hπ' hπpos hL₀m hL₀ hR ht hnd,
    dualPotential_meanMap hπm hπi hπ' hπpos hL₀m hL₀ hR ht hnd,
    dualPotential_meanMap hπm hπi hπ' hπpos hL₀m hL₀ hR ht hnd, hc,
    (isLinearMap_dotJ c).map_add, (isLinearMap_dotJ c).map_smul, (isLinearMap_dotJ c).map_smul]
  simp only [smul_eq_mul]
  have h1 := dual_objective_le_at_mean hπm hπi hπ' hπpos hL₀m hL₀ hR (t := t) a₁ c
  have h2 := dual_objective_le_at_mean hπm hπi hπ' hπpos hL₀m hL₀ hR (t := t) a₂ c
  have e : affLogZ μ π L₀ R t c = l₁ * affLogZ μ π L₀ R t c + l₂ * affLogZ μ π L₀ R t c := by
    rw [← add_mul, hl, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 hl₁, mul_le_mul_of_nonneg_left h2 hl₂]

end Convex

section Slice

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
  (hndJ : ∀ w : Option ι → ℝ, w ≠ 0 →
    ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss (jointStat L₀ R) w x = c)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht hndJ

omit ht in
set_option linter.unusedFintypeInType false in
/-- **`∂_e I = −t` at the slice point**: the base-direction derivative of the joint dual potential
at `η(Θ(t,a))` is minus the temperature. -/
theorem partial_base_dualPotential [DecidableEq ι] (a : ι → ℝ) :
    HasDerivAt (fun e : ℝ ↦ dualPotential μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1
      (meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (natCoord t a) + e • Pi.single none 1))
      (-t) 0 := by
  have hI := hasFDerivAt_dualPotential hπm hπi hπ hπpos measurable_const (zero_bdd (X := X))
    (bdd_jointStat hL₀m hL₀ hR) one_pos hndJ (natCoord t a)
  have hline := hasDerivAt_affineLine (meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1
    (natCoord t a)) (Pi.single none 1 : Option ι → ℝ) 0
  have hI' : HasFDerivAt (dualPotential μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1)
      ((-1 : ℝ) • dotCLM (natCoord t a))
      ((fun s : ℝ ↦ meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (natCoord t a) +
        s • (Pi.single none 1 : Option ι → ℝ)) 0) := by
    simpa using hI
  have h := hI'.comp_hasDerivAt (0 : ℝ) hline
  refine h.congr_deriv ?_
  rw [_root_.smul_apply, dotCLM_apply, dotJ_single_left, smul_eq_mul]
  simp [natCoord]

omit ht in
/-- **The temperature slice is a constrained minimum**: among all joint responses `η(b)` with the
same contrast part as `η(Θ(t,a))`, the slice point minimises `e ↦ I(e, M) + t e`. -/
theorem slice_variational (a : ι → ℝ) {b : Option ι → ℝ}
    (hb : ∀ i, meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 b (some i) =
      meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (natCoord t a) (some i)) :
    dualPotential μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1
        (meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (natCoord t a)) +
      t * meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (natCoord t a) none ≤
    dualPotential μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1
        (meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 b) +
      t * meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 b none := by
  have h := dualPotential_ge_tangent hπm hπi hπ hπpos measurable_const (zero_bdd (X := X))
    (bdd_jointStat hL₀m hL₀ hR) one_pos hndJ (natCoord t a) b
  have e : dotJ (natCoord t a) (meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 b -
      meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (natCoord t a)) =
      t * (meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 b none -
        meanMap μ π (fun _ ↦ (0 : ℝ)) (jointStat L₀ R) 1 (natCoord t a) none) := by
    simp only [dotJ, Fintype.sum_option, Pi.sub_apply, hb, sub_self, mul_zero,
      Finset.sum_const_zero, add_zero]
    rfl
  rw [e] at h
  linarith

end Slice

end Laplace.Multi
