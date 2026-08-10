/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.DiagonalVolume

/-!
# Quasi-homogeneous moment-ratio recovery

Piece (i) of the germbij semi-quasi-homogeneous debt, in the
distribution-free form of the scoping consult: testing with the
monomial observable itself, anisotropic scaling recovers every moment
ratio `M_α/M_0` of a quasi-homogeneous model exactly — exponent
collisions between different multi-indices never enter a single
observable's coefficient, so no partial-derivatives-of-delta
linear-independence argument (and no distribution theory) is needed.
All multi-indices, including odd ones, extending the even-coordinate
recovery perimeter. The statements are exact identities, not
asymptotics: for the global model
`t^{⟨q,α⟩}·⟨x^α⟩_t = M_α/M_0` for every `t > 0`, and two models with
the same weights whose normalized monomial moments agree at a single
temperature have equal moment ratios. Two boundary notes: the
identities are junk-value-consistent and take no integrability or
positivity hypotheses — "recovery" is substantive only when the
reference moments are finite with `M_0 > 0` (the note's `q_i > 0` and
`P > 0` away from the origin supply this, but are not assumed here);
and the note's LOCALIZED law with cutoff and `O(e^{-ct})` error is
not formalised — these are the global-model exact forms.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-- The multi-index monomial on the pi space. -/
def mvMonomial (α : ι → ℕ) : (ι → ℝ) → ℝ :=
  fun w ↦ ∏ i : ι, w i ^ α i

theorem mvMonomial_measurable (α : ι → ℕ) :
    Measurable (mvMonomial (ι := ι) α) :=
  Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _

/-- Powers of an rpow collapse along a finite sum of exponents. -/
theorem rpow_sum_of_pos {s : ℝ} (hs : 0 < s) (c : ι → ℝ) :
    s ^ (∑ i : ι, c i) = ∏ i : ι, s ^ (c i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      Real.rpow_add hs, ih]

/-- Monomials are homogeneous along the quasi-homogeneous dilation,
with weight the pairing `⟨q, α⟩ = ∑ q_i α_i`. -/
theorem mvMonomial_qhDilation (q : ι → ℝ) (α : ι → ℕ) {s : ℝ}
    (hs : 0 < s) (w : ι → ℝ) :
    mvMonomial α (qhDilation q s w) =
      s ^ (∑ i : ι, q i * α i) * mvMonomial α w := by
  unfold mvMonomial qhDilation
  rw [rpow_sum_of_pos hs, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [mul_pow, ← Real.rpow_natCast (s ^ q i) (α i),
    ← Real.rpow_mul hs.le]

/-- **The exact unnormalized monomial moment law** for a
quasi-homogeneous potential on Lebesgue measure. -/
theorem qh_monomial_moment_law (q : ι → ℝ) {P : (ι → ℝ) → ℝ}
    (hP : Measurable P)
    (hPqh : ∀ s : ℝ, 0 < s → ∀ w, P (qhDilation q s w) = s * P w)
    (α : ι → ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ w : ι → ℝ, mvMonomial α w * Real.exp (-(t * P w)) =
      t ^ (-((∑ i : ι, q i) + ∑ i : ι, q i * α i)) *
        ∫ w : ι → ℝ, mvMonomial α w * Real.exp (-(P w)) :=
  scalesMeasure_moment_law (scalesMeasure_qhDilation_volume q)
    (fun s _ ↦ qhDilation_measurable q s) hP
    (mvMonomial_measurable α) hPqh
    (fun _ hs w ↦ mvMonomial_qhDilation q α hs w) ht

/-- **The exact normalized monomial moment law**: the temperature
enters only through the pairing exponent. -/
theorem qh_monomial_normalized_law (q : ι → ℝ) {P : (ι → ℝ) → ℝ}
    (hP : Measurable P)
    (hPqh : ∀ s : ℝ, 0 < s → ∀ w, P (qhDilation q s w) = s * P w)
    (α : ι → ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ w : ι → ℝ, mvMonomial α w * Real.exp (-(t * P w))) /
        (∫ w : ι → ℝ, Real.exp (-(t * P w))) =
      t ^ (-(∑ i : ι, q i * α i)) *
        ((∫ w : ι → ℝ, mvMonomial α w * Real.exp (-(P w))) /
          ∫ w : ι → ℝ, Real.exp (-(P w))) :=
  scalesMeasure_normalized_law (scalesMeasure_qhDilation_volume q)
    (fun s _ ↦ qhDilation_measurable q s) hP
    (mvMonomial_measurable α) hPqh
    (fun _ hs w ↦ mvMonomial_qhDilation q α hs w) ht

/-- **Moment-ratio recovery**: rescaling the normalized monomial
moment by the pairing power recovers the moment ratio `M_α/M_0`
exactly, at every temperature — every multi-index, including odd
ones. -/
theorem qh_momentRatio_recovery (q : ι → ℝ) {P : (ι → ℝ) → ℝ}
    (hP : Measurable P)
    (hPqh : ∀ s : ℝ, 0 < s → ∀ w, P (qhDilation q s w) = s * P w)
    (α : ι → ℕ) {t : ℝ} (ht : 0 < t) :
    t ^ (∑ i : ι, q i * α i) *
        ((∫ w : ι → ℝ, mvMonomial α w * Real.exp (-(t * P w))) /
          ∫ w : ι → ℝ, Real.exp (-(t * P w))) =
      (∫ w : ι → ℝ, mvMonomial α w * Real.exp (-(P w))) /
        ∫ w : ι → ℝ, Real.exp (-(P w)) := by
  rw [qh_monomial_normalized_law q hP hPqh α ht, ← mul_assoc,
    ← Real.rpow_add ht]
  rw [show (∑ i : ι, q i * α i) + -(∑ i : ι, q i * α i) = 0 from by
    ring, Real.rpow_zero, one_mul]

/-- **Comparison form**: two quasi-homogeneous models with the same
weights whose normalized monomial moments agree at a single
temperature have equal moment ratios. -/
theorem momentRatios_eq_of_normalized_moments_eq (q : ι → ℝ)
    {P₁ P₂ : (ι → ℝ) → ℝ} (hP₁ : Measurable P₁) (hP₂ : Measurable P₂)
    (hP₁qh : ∀ s : ℝ, 0 < s → ∀ w, P₁ (qhDilation q s w) = s * P₁ w)
    (hP₂qh : ∀ s : ℝ, 0 < s → ∀ w, P₂ (qhDilation q s w) = s * P₂ w)
    (α : ι → ℕ) {t : ℝ} (ht : 0 < t)
    (hmom : (∫ w : ι → ℝ, mvMonomial α w * Real.exp (-(t * P₁ w))) /
        (∫ w : ι → ℝ, Real.exp (-(t * P₁ w))) =
      (∫ w : ι → ℝ, mvMonomial α w * Real.exp (-(t * P₂ w))) /
        ∫ w : ι → ℝ, Real.exp (-(t * P₂ w))) :
    (∫ w : ι → ℝ, mvMonomial α w * Real.exp (-(P₁ w))) /
        (∫ w : ι → ℝ, Real.exp (-(P₁ w))) =
      (∫ w : ι → ℝ, mvMonomial α w * Real.exp (-(P₂ w))) /
        ∫ w : ι → ℝ, Real.exp (-(P₂ w)) := by
  rw [← qh_momentRatio_recovery q hP₁ hP₁qh α ht,
    ← qh_momentRatio_recovery q hP₂ hP₂qh α ht, hmom]

end Laplace.Multi
