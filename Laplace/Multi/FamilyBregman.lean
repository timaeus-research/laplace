/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.EndpointConvergence
import Laplace.Multi.JourneyEnergy

/-!
# The Kullback–Leibler divergence between two family members is the Bregman divergence

`klDiv_familyMeasure` identifies Mathlib's `klDiv (P_{t,a}) (P_{t,b})` with the seabed's real-valued
`famKL a b`, hence (`famKL_eq`) with the Bregman divergence of the log-partition function
`A_t(b) − A_t(a) + t ⟨b − a, m_t(a)⟩`. Together with `mixKL_eq_bregman_dual` this is the operative
content of dual flatness: the divergence between two members is the Bregman divergence of the
log-partition function in the natural coordinates, and of its Legendre dual in the responses.
`klDiv_familyMeasure_add_symm` is the Jeffreys form, `KL(P_a‖P_b) + KL(P_b‖P_a) =
−t ⟨a − b, m(a) − m(b)⟩`.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section Family

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

/-- **The divergence between two family members is the Bregman divergence**:
`KL(P_{t,a} ‖ P_{t,b}) = famKL a b`. -/
theorem klDiv_familyMeasure (a b : ι → ℝ) :
    klDiv (familyMeasure μ π L₀ R t a) (familyMeasure μ π L₀ R t b) =
      ENNReal.ofReal (famKL μ π L₀ R t a b) := by
  have hQ := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) 0
  have hP := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  have hbdd : Bdd fun x ↦ -t * dirLoss R b x := Bdd.const_mul (-t) (bdd_dirLoss hR b)
  have hac : familyMeasure μ π L₀ R t a ≪ familyMeasure μ π L₀ R t 0 := by
    rw [familyMeasure_eq_tilted hπm hπi hπ hπpos hL₀m hL₀ hR ht a]
    exact tilted_absolutelyContinuous _ _
  have hfin : klDiv (familyMeasure μ π L₀ R t a) (familyMeasure μ π L₀ R t 0) ≠ ⊤ := by
    rw [klDiv_familyMeasure_zero hπm hπi hπ hπpos hL₀m hL₀ hR ht a]
    exact ENNReal.ofReal_ne_top
  have hm : (fun i ↦ ∫ x, R i x ∂familyMeasure μ π L₀ R t a) = meanMap μ π L₀ R t a :=
    funext fun i ↦ integral_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR a (R i)
  rw [familyMeasure_eq_tilted hπm hπi hπ hπpos hL₀m hL₀ hR ht b,
    klDiv_tilted_right_eq _ _ hac hfin hbdd,
    klDiv_familyMeasure_zero hπm hπi hπ hπpos hL₀m hL₀ hR ht a,
    integral_exp_neg_mul_dirLoss_familyMeasure_zero hπm hπi hπ hπpos hL₀m hL₀ hR ht b,
    Real.log_exp, integral_const_mul, ← dotJ_integral_eq _ hR b, hm,
    ENNReal.toReal_ofReal (famKL_nonneg hπm hπi hπ hπpos hL₀m hL₀ hR ht a 0),
    famKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR, famKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR]
  congr 1
  have e : ∑ i, (b i - a i) * meanMap μ π L₀ R t a i =
      ∑ i, b i * meanMap μ π L₀ R t a i - ∑ i, a i * meanMap μ π L₀ R t a i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have e0 : ∑ i, ((0 : ι → ℝ) i - a i) * meanMap μ π L₀ R t a i =
      -∑ i, a i * meanMap μ π L₀ R t a i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by simp
  simp only [dotJ]
  rw [e, e0]
  ring

/-- **The Bregman form of the divergence between two family members**:
`KL(P_{t,a} ‖ P_{t,b}) = A_t(b) − A_t(a) + t ⟨b − a, m_t(a)⟩`. -/
theorem klDiv_familyMeasure_eq_bregman (a b : ι → ℝ) :
    klDiv (familyMeasure μ π L₀ R t a) (familyMeasure μ π L₀ R t b) =
      ENNReal.ofReal (affLogZ μ π L₀ R t b - affLogZ μ π L₀ R t a +
        t * ∑ i, (b i - a i) * meanMap μ π L₀ R t a i) := by
  rw [klDiv_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR ht,
    famKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR]

/-- **The Jeffreys form**: `KL(P_a ‖ P_b) + KL(P_b ‖ P_a) = −t ⟨a − b, m(a) − m(b)⟩`. -/
theorem klDiv_familyMeasure_add_symm (a b : ι → ℝ) :
    klDiv (familyMeasure μ π L₀ R t a) (familyMeasure μ π L₀ R t b) +
        klDiv (familyMeasure μ π L₀ R t b) (familyMeasure μ π L₀ R t a) =
      ENNReal.ofReal (-t * dotJ (a - b) (meanMap μ π L₀ R t a - meanMap μ π L₀ R t b)) := by
  rw [klDiv_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR ht,
    klDiv_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR ht,
    ← ENNReal.ofReal_add (famKL_nonneg hπm hπi hπ hπpos hL₀m hL₀ hR ht a b)
      (famKL_nonneg hπm hπi hπ hπpos hL₀m hL₀ hR ht b a),
    famKL_add_famKL_eq_neg_mul_dot hπm hπi hπ hπpos hL₀m hL₀ hR b a]

end Family

end Laplace.Multi
