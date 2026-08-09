/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.TaylorCompare

/-!
# The smooth-loss recovery: Taylor adapter

Stages C4-C5 of the smooth-germ programme, first installment: the
bridge from smoothness to the comparison machinery. Mathlib's
`taylor_isLittleO` is the Peano remainder; here it is converted to
the epsilon-radius jet form the local Taylor comparison consumes
(`taylor_jet_epsilon`), and the admissibility package is shown to
force the first-order facts at the minimum: the derivative vanishes
(`AdmissiblePotential.deriv_zero`) and the second Taylor coefficient
dominates the envelope constant
(`AdmissiblePotential.taylorBase_ge`), so nondegeneracy `λ > 0` is
derived rather than assumed.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.OneD

open Laplace

/-- The quadratic Taylor coefficient (the `λ/2` of the note). -/
noncomputable def taylorBase (L : ℝ → ℝ) : ℝ :=
  iteratedDeriv 2 L 0 / 2

/-- The higher Taylor coefficients in jet indexing: index `i` carries
degree `2 + (i+1)`. -/
noncomputable def taylorCoeff (L : ℝ → ℝ) (D : ℕ) :
    Fin (D - 2) → ℝ :=
  fun i ↦ iteratedDeriv (2 + (i.1 + 1)) L 0 /
    (Nat.factorial (2 + (i.1 + 1)) : ℝ)

/-- **Peano remainder in epsilon-radius form** (from Mathlib's
`taylor_isLittleO`): the jet hypothesis of the local Taylor
comparison, verbatim. -/
theorem taylor_jet_epsilon
    {L : ℝ → ℝ} {D : ℕ} (hL : ContDiff ℝ D L) :
    ∀ ε : ℝ, 0 < ε → ∃ δ' : ℝ, 0 < δ' ∧ ∀ x : ℝ, |x| ≤ δ' →
      |L x - taylorWithinEval L D Set.univ 0 x| ≤ ε * |x| ^ D := by
  intro ε hε
  have h := taylor_isLittleO (convex_univ) (Set.mem_univ (0 : ℝ))
    hL.contDiffOn
  rw [nhdsWithin_univ] at h
  have h2 := (Asymptotics.isLittleO_iff.mp h) hε
  rw [Metric.eventually_nhds_iff] at h2
  obtain ⟨δ₀, hδ₀, hh⟩ := h2
  refine ⟨δ₀ / 2, by positivity, fun x hx ↦ ?_⟩
  have hd : dist x 0 < δ₀ := by
    rw [Real.dist_eq, sub_zero]
    linarith [abs_nonneg x]
  have := hh hd
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_pow] at this
  exact this

/-- The derivative of an admissible potential vanishes at the
minimum. -/
theorem AdmissiblePotential.deriv_zero
    {L : ℝ → ℝ} {ρ κ δ : ℝ} (h : AdmissiblePotential L ρ κ δ) :
    deriv L 0 = 0 := by
  have hmin : IsLocalMin L 0 := by
    apply Filter.Eventually.of_forall
    intro x
    have h1 := h.lower x
    rw [h.zero]
    nlinarith [sq_nonneg x, h.rho_pos]
  exact hmin.deriv_eq_zero

/-- The quadratic Taylor coefficient of an admissible potential
dominates the envelope constant; in particular it is positive
(`λ > 0` is derived, not assumed). Uses the degree-2 Peano remainder
against the global lower envelope. -/
theorem AdmissiblePotential.taylorBase_ge
    {L : ℝ → ℝ} {ρ κ δ : ℝ} (h : AdmissiblePotential L ρ κ δ)
    (hL : ContDiff ℝ 2 L) : ρ ≤ taylorBase L := by
  by_contra hlt
  rw [not_le] at hlt
  set ε : ℝ := (ρ - taylorBase L) / 2 with hε_def
  have hε : 0 < ε := by
    rw [hε_def]
    linarith
  obtain ⟨δ', hδ', hjet⟩ := taylor_jet_epsilon hL ε hε
  -- Evaluate at a small positive point.
  set x : ℝ := min δ' (δ / 2) with hx_def
  have hx0 : 0 < x := lt_min hδ' (by linarith [h.delta_pos])
  have hxδ' : |x| ≤ δ' := by
    rw [abs_of_pos hx0]
    exact min_le_left _ _
  have hT : taylorWithinEval L 2 Set.univ 0 x =
      taylorBase L * x ^ 2 := by
    rw [taylor_within_apply]
    have h0 : iteratedDerivWithin 0 L Set.univ 0 = 0 := by
      rw [iteratedDerivWithin_zero]
      exact h.zero
    have h1 : iteratedDerivWithin 1 L Set.univ 0 = 0 := by
      rw [iteratedDerivWithin_one, derivWithin_univ]
      exact h.deriv_zero
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, h0, h1]
    rw [iteratedDerivWithin_univ]
    simp only [smul_eq_mul, sub_zero]
    rw [taylorBase]
    norm_num [Nat.factorial]
    ring
  have hjx := hjet x hxδ'
  rw [hT] at hjx
  have hlow := h.lower x
  rw [abs_of_pos hx0] at hjx
  -- ρ x² ≤ L x ≤ taylorBase·x² + ε·x², contradicting ε = (ρ−base)/2.
  have habs := abs_le.mp hjx
  have hup : L x ≤ taylorBase L * x ^ 2 + ε * x ^ 2 := by
    nlinarith [habs.2]
  have hx2 : 0 < x ^ 2 := by positivity
  nlinarith [hlow, hup]

end Laplace.OneD
