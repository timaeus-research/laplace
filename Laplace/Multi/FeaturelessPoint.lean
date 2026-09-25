/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.SegmentDivergence
import Laplace.Multi.DualPotential

/-!
# The featureless point of the response space

The prior `P_0 = e^{−tL₀}π` is the origin of the map from featureless to data. Its response
`y₀ = m(0) = ⟨R⟩_{P_0}` is the unique minimiser of the dual potential on the response space, and the
excess `I(y) − I(y₀)` is exactly the information `KL(P_{θ(y)} ‖ P_0)` acquired relative to the prior
(`dualPotential_sub_prior_eq_mixKL`). Strict positivity of the divergence between distinct members
of the family (`mixKL_pos`, `mixKL_eq_zero_iff`) makes the minimiser unique
(`dualPotential_prior_lt`, `eq_zero_of_dualPotential_eq_prior`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd

/-- Along a segment in a nonzero direction the response variance is positive. -/
theorem segVar_pos (a v : ι → ℝ) (hv : v ≠ 0) (s : ℝ) : 0 < segVar μ π L₀ R t a v s := by
  refine lt_of_le_of_ne (segVar_nonneg hπm hπi hπ hπpos hL₀m hL₀ hR a v s) fun h0 ↦ ?_
  have hform : responseForm μ π L₀ R (a + s • v) t v v = 0 := by
    unfold responseForm segVar at *
    rw [← h0]; ring
  obtain ⟨c, hc⟩ := (responseForm_self_eq_zero_iff hπm hπi hπ hπpos hL₀m hL₀ hR ht _ v).1 hform
  exact hnd v hv ⟨c, hc.mono fun x hx _ ↦ hx⟩

/-- **Distinct members of the family are at positive divergence**: `0 < KL(P_b ‖ P_a)` for
`a ≠ b`. -/
theorem mixKL_pos (a b : ι → ℝ) (hab : a ≠ b) :
    0 < mixKL μ π (affLoss L₀ R b) (dirLoss R (a - b)) t 0 1 := by
  rw [mixKL_eq_integral_mul_var hπm hπi hπ hπpos hL₀m hL₀ hR ht a b]
  refine mul_pos (by positivity) ?_
  have hv : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun s hs ↦ ?_) zero_lt_one
  · exact (continuous_id.mul (continuous_segVar hπm hπi hπ hπpos hL₀m hL₀ hR ht a (b - a)))
      |>.intervalIntegrable 0 1
  · exact mul_pos hs.1 (segVar_pos hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a (b - a) hv s)

/-- `KL(P_b ‖ P_a) = 0` iff `a = b`. -/
theorem mixKL_eq_zero_iff (a b : ι → ℝ) :
    mixKL μ π (affLoss L₀ R b) (dirLoss R (a - b)) t 0 1 = 0 ↔ a = b := by
  constructor
  · intro h
    by_contra hab
    exact (mixKL_pos hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd a b hab).ne' h
  · rintro rfl
    have h := mixKL_eq_bregman_dual hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a a
    rw [h]; simp [dotJ]

/-- The dual potential at the prior's response is `−A(0)`. -/
theorem dualPotential_meanMap_zero :
    dualPotential μ π L₀ R t (meanMap μ π L₀ R t 0) = -affLogZ μ π L₀ R t 0 := by
  rw [dualPotential_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd]
  simp [dotJ]

/-- **The excess of the dual potential over its value at the featureless point is the information
relative to the prior**: `I(m(b)) − I(m(0)) = KL(P_b ‖ P_0)`. -/
theorem dualPotential_sub_prior_eq_mixKL (b : ι → ℝ) :
    dualPotential μ π L₀ R t (meanMap μ π L₀ R t b) -
        dualPotential μ π L₀ R t (meanMap μ π L₀ R t 0) =
      mixKL μ π (affLoss L₀ R b) (dirLoss R (0 - b)) t 0 1 := by
  rw [mixKL_eq_bregman_dual hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd 0 b]
  simp [dotJ]

/-- In response coordinates: for every attainable `y`, `I(y) − I(y₀) = KL(P_{θ(y)} ‖ P_0)`. -/
theorem dualPotential_sub_prior_eq_mixKL' {y : ι → ℝ} (hy : y ∈ Set.range (meanMap μ π L₀ R t)) :
    dualPotential μ π L₀ R t y - dualPotential μ π L₀ R t (meanMap μ π L₀ R t 0) =
      mixKL μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t) y))
        (dirLoss R (0 - Function.invFun (meanMap μ π L₀ R t) y)) t 0 1 := by
  have h := dualPotential_sub_prior_eq_mixKL hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd
    (Function.invFun (meanMap μ π L₀ R t) y)
  rwa [meanMap_invFun hy] at h

/-- The featureless point minimises the dual potential over the realised responses. -/
theorem dualPotential_prior_le (b : ι → ℝ) :
    dualPotential μ π L₀ R t (meanMap μ π L₀ R t 0) ≤
      dualPotential μ π L₀ R t (meanMap μ π L₀ R t b) := by
  have h := dualPotential_sub_prior_eq_mixKL hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd b
  have h0 : 0 ≤ mixKL μ π (affLoss L₀ R b) (dirLoss R (0 - b)) t 0 1 := by
    rw [mixKL_eq_integral_mul_var hπm hπi hπ hπpos hL₀m hL₀ hR ht 0 b]
    refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg zero_le_one fun s hs ↦
      mul_nonneg hs.1 (segVar_nonneg hπm hπi hπ hπpos hL₀m hL₀ hR 0 (b - 0) s))
  linarith

/-- ... and strictly so away from the prior. -/
theorem dualPotential_prior_lt (b : ι → ℝ) (hb : b ≠ 0) :
    dualPotential μ π L₀ R t (meanMap μ π L₀ R t 0) <
      dualPotential μ π L₀ R t (meanMap μ π L₀ R t b) := by
  have h := dualPotential_sub_prior_eq_mixKL hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd b
  have h0 := mixKL_pos hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd 0 b (Ne.symm hb)
  linarith

/-- **The featureless point is the unique minimiser of the dual potential on the response
space.** -/
theorem dualPotential_isMinOn_prior :
    IsMinOn (dualPotential μ π L₀ R t) (Set.range (meanMap μ π L₀ R t))
      (meanMap μ π L₀ R t 0) := by
  rintro y ⟨b, rfl⟩
  exact dualPotential_prior_le hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd b

theorem eq_zero_of_dualPotential_eq_prior (b : ι → ℝ)
    (h : dualPotential μ π L₀ R t (meanMap μ π L₀ R t b) =
      dualPotential μ π L₀ R t (meanMap μ π L₀ R t 0)) : b = 0 := by
  by_contra hb
  exact (dualPotential_prior_lt hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd b hb).ne h.symm

/-- The information relative to the prior, as a function on the response space, is nonnegative,
vanishes exactly at the featureless point, and equals `I(y) + A(0)`. -/
theorem dualPotential_add_affLogZ_zero_nonneg {y : ι → ℝ}
    (hy : y ∈ Set.range (meanMap μ π L₀ R t)) :
    0 ≤ dualPotential μ π L₀ R t y + affLogZ μ π L₀ R t 0 := by
  obtain ⟨b, rfl⟩ := hy
  have h := dualPotential_prior_le hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd b
  rw [dualPotential_meanMap_zero hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd] at h
  linarith

end

end Laplace.Multi
