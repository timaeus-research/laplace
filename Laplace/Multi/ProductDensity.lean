/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# Products of density-defined probability measures

If `Q = P.withDensity (ofReal ∘ r)` for a bounded nonnegative measurable density `r` of mass one,
then the `n`-fold product of `Q` is the product of `P` with the product density
(`Measure.pi_withDensity_ofReal`), and on a set where the product density is at least `c` the
product of `Q` dominates `c` times the product of `P` (`measureReal_pi_ge_of_density_ge`). These
are the change-of-measure tools for the tilt-based lower bounds on the empirical feature mean.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- The indicator of a box is the product of the coordinate indicators. -/
theorem indicator_pi_prod {n : ℕ} (s : Fin n → Set X) (r : X → ℝ) (x : Fin n → X) :
    (Set.pi univ s).indicator (fun x : Fin n → X ↦ ∏ k, r (x k)) x =
      ∏ k, (s k).indicator r (x k) := by
  by_cases hx : x ∈ Set.pi univ s
  · rw [Set.indicator_of_mem hx]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [Set.indicator_of_mem (Set.mem_univ_pi.1 hx k)]
  · rw [Set.indicator_of_notMem hx]
    obtain ⟨k, hk⟩ : ∃ k, x k ∉ s k := by
      by_contra h
      push Not at h
      exact hx (Set.mem_univ_pi.2 h)
    exact (Finset.prod_eq_zero (Finset.mem_univ k) (Set.indicator_of_notMem hk r)).symm

/-- **The product of density-defined probability measures is a density of the product**:
`(P.withDensity r)^{⊗n} = P^{⊗n}.withDensity (∏ₖ r(xₖ))`. -/
theorem Measure.pi_withDensity_ofReal (P : Measure X) [IsProbabilityMeasure P] {r : X → ℝ}
    (hrm : Measurable r) (hr0 : ∀ x, 0 ≤ r x) {C : ℝ} (hrC : ∀ x, r x ≤ C)
    [IsProbabilityMeasure (P.withDensity fun x ↦ ENNReal.ofReal (r x))] (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ P.withDensity fun x ↦ ENNReal.ofReal (r x)) =
      (Measure.pi fun _ : Fin n ↦ P).withDensity
        (fun x ↦ ENNReal.ofReal (∏ k, r (x k))) := by
  refine Measure.pi_eq fun s hs ↦ ?_
  have hbox : MeasurableSet (Set.pi univ s) := MeasurableSet.pi countable_univ fun k _ ↦ hs k
  have hprodm : Measurable (fun x : Fin n → X ↦ ∏ k, r (x k)) :=
    Finset.measurable_prod _ fun k _ ↦ hrm.comp (measurable_pi_apply k)
  have hprod0 : ∀ x : Fin n → X, 0 ≤ ∏ k, r (x k) := fun x ↦
    Finset.prod_nonneg fun k _ ↦ hr0 (x k)
  have hprodint : Integrable (fun x : Fin n → X ↦ ∏ k, r (x k)) (Measure.pi fun _ ↦ P) :=
    Integrable.of_bound hprodm.aestronglyMeasurable (C ^ n) (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hprod0 x)]
      calc ∏ k, r (x k) ≤ ∏ _k : Fin n, C :=
            Finset.prod_le_prod (fun k _ ↦ hr0 (x k)) fun k _ ↦ hrC (x k)
        _ = C ^ n := by simp)
  rw [withDensity_apply _ hbox, ← ofReal_integral_eq_lintegral_ofReal hprodint.integrableOn
    (ae_of_all _ fun x ↦ hprod0 x), ← integral_indicator hbox]
  have e : (fun x : Fin n → X ↦ (Set.pi univ s).indicator (fun x ↦ ∏ k, r (x k)) x) =
      fun x ↦ ∏ k, (fun y ↦ (s k).indicator r y) (x k) :=
    funext fun x ↦ indicator_pi_prod s r x
  rw [e, integral_fintype_prod_eq_prod (fun k y ↦ (s k).indicator r y)]
  have hcoord : ∀ k, ∫ y, (s k).indicator r y ∂P =
      ((P.withDensity fun x ↦ ENNReal.ofReal (r x)) (s k)).toReal := by
    intro k
    rw [integral_indicator (hs k), withDensity_apply _ (hs k),
      ← ofReal_integral_eq_lintegral_ofReal (Integrable.of_bound hrm.aestronglyMeasurable C
        (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hr0 x)]; exact hrC x)
        |>.integrableOn) (ae_of_all _ fun x ↦ hr0 x),
      ENNReal.toReal_ofReal (setIntegral_nonneg (hs k) fun x _ ↦ hr0 x)]
  simp only [hcoord]
  rw [ENNReal.ofReal_prod_of_nonneg fun k _ ↦ ENNReal.toReal_nonneg]
  exact Finset.prod_congr rfl fun k _ ↦ ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- **Change of measure from below**: on a measurable set where the product density is at least
`c ≥ 0`, `Q^{⊗n}(A) ≥ c · P^{⊗n}(A)`. -/
theorem measureReal_pi_ge_of_density_ge (P : Measure X) [IsProbabilityMeasure P] {r : X → ℝ}
    (hrm : Measurable r) (hr0 : ∀ x, 0 ≤ r x) {C : ℝ} (hrC : ∀ x, r x ≤ C)
    [IsProbabilityMeasure (P.withDensity fun x ↦ ENNReal.ofReal (r x))] {n : ℕ}
    {A : Set (Fin n → X)} (hA : MeasurableSet A) {c : ℝ} (hc : 0 ≤ c)
    (hge : ∀ x ∈ A, c ≤ ∏ k, r (x k)) :
    c * (Measure.pi fun _ : Fin n ↦ P).real A ≤
      (Measure.pi (fun _ : Fin n ↦ P.withDensity fun x ↦ ENNReal.ofReal (r x))).real A := by
  have h : ENNReal.ofReal c * (Measure.pi fun _ : Fin n ↦ P) A ≤
      (Measure.pi (fun _ : Fin n ↦ P.withDensity fun x ↦ ENNReal.ofReal (r x))) A := by
    rw [Measure.pi_withDensity_ofReal P hrm hr0 hrC n, withDensity_apply _ hA,
      ← setLIntegral_const]
    exact setLIntegral_mono (by fun_prop) fun x hx ↦ ENNReal.ofReal_le_ofReal (hge x hx)
  have h' := ENNReal.toReal_mono (measure_ne_top _ _) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at h'
  exact h'

end Laplace.Multi
