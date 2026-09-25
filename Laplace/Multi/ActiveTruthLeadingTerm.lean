/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthDistinguish
import Laplace.Multi.TermData

/-!
# The leading measure of a certificate with a strictly dominant term

Astra round 13, item 5 (the certificate-level assembly example). For the certificate assembled
from term data of any shapes (vertex, tied, partial, active-truth, degenerate active-truth), the
term whose power is strictly smaller than every other term's carries the whole leading measure
(`ofTermData_leadingMeasure_eq_of_lt`); when the minimal power is shared, the leading measure is
the sum over the terms of minimal power and maximal logarithmic order
(`leadingMeasure_eq_sum_filter`, the definition made explicit). This is the "which shape leads"
bookkeeping: it tests nothing analytic beyond `ofTermData` and `lexMeasure`, and is recorded as the
assembly statement rather than as an end-to-end example.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

namespace TruthChartsData.Phase.TermMeasureCertificate

variable {m : ℕ} {L' : Set (Fin (m + 1) → ℝ)} {T : (Fin (m + 1) → ℝ) → ℝ}
  {D : TruthChartsData m T L'}
  {F : (Fin (m + 1) → ℝ) → ℝ} {P : D.Phase F} {σ γ : ℝ}

open scoped Classical in
/-- The leading measure is the sum of the measures of the terms of leading order. -/
theorem leadingMeasure_eq_sum_filter (C : P.TermMeasureCertificate σ γ) :
    C.leadingMeasure = ∑ p ∈ Finset.univ.filter (fun p ↦ C.lam p = C.lam₀ ∧ C.kk p = C.k₀), C.μ p :=
  rfl

/-- A unique term of leading order carries the leading measure. -/
theorem leadingMeasure_eq_of_unique (C : P.TermMeasureCertificate σ γ) {p : TermIdx D}
    (hp : C.lam p = C.lam₀ ∧ C.kk p = C.k₀)
    (huniq : ∀ q, C.lam q = C.lam₀ → C.kk q = C.k₀ → q = p) : C.leadingMeasure = C.μ p := by
  classical
  rw [leadingMeasure_eq_sum_filter]
  rw [Finset.sum_eq_single p]
  · intro q hq hqp
    exact absurd (huniq q (Finset.mem_filter.mp hq).2.1 (Finset.mem_filter.mp hq).2.2) hqp
  · intro hp'
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩) hp'

/-- **The strictly dominant term.** In the certificate assembled from term data, a term whose power
is strictly smaller than every other term's power carries the whole leading measure. -/
theorem ofTermData_leadingMeasure_eq_of_lt [Nonempty D.ι] (T : ∀ p, P.TermData σ γ p)
    {p : TermIdx D} (hlt : ∀ q, q ≠ p → (T p).lam < (T q).lam) :
    (ofTermData P T).leadingMeasure = (T p).μ := by
  classical
  have hle : ∀ q, (T p).lam ≤ (T q).lam := fun q ↦ by
    by_cases hq : q = p
    · rw [hq]
    · exact (hlt q hq).le
  have hlam₀ : (ofTermData P T).lam₀ = (T p).lam := by
    refine le_antisymm ((ofTermData P T).hmin p).1 ?_
    exact Finset.le_inf' Finset.univ_nonempty _ fun q _ ↦ hle q
  have hk₀ : (ofTermData P T).k₀ = (T p).kk := by
    refine le_antisymm ?_ (((ofTermData P T).hmin p).2 hlam₀.symm)
    refine Finset.sup_le fun q hq ↦ ?_
    have hq2 : (T q).lam = (ofTermData P T).lam₀ := (Finset.mem_filter.mp hq).2
    by_cases hqp : q = p
    · rw [hqp]
    · rw [hlam₀] at hq2
      exact absurd hq2 (ne_of_gt (hlt q hqp))
  refine leadingMeasure_eq_of_unique (ofTermData P T) ⟨hlam₀.symm, hk₀.symm⟩ fun q hq _ ↦ ?_
  by_contra hqp
  have hq2 : (T q).lam = (T p).lam := by
    rw [← hlam₀]
    exact hq
  exact (ne_of_gt (hlt q hqp)) hq2

end TruthChartsData.Phase.TermMeasureCertificate

end Laplace.Multi
