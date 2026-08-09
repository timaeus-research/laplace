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

/-- **The Taylor polynomial in jet shape**: for an admissible `C^D`
potential, the degree-`D` Taylor polynomial at the minimum is exactly
the jet potential with base `taylorBase` and coefficients
`taylorCoeff` (the `k = 0, 1` terms vanish at an admissible
minimum). -/
theorem taylorWithinEval_eq_jet
    {L : ℝ → ℝ} {ρ κ δ : ℝ} {D : ℕ} (hD : 2 ≤ D)
    (h : AdmissiblePotential L ρ κ δ) (x : ℝ) :
    taylorWithinEval L D Set.univ 0 x =
      jetPotential 1 (D - 2) (taylorBase L) 1 (taylorCoeff L D) x := by
  rw [taylor_within_apply]
  simp only [sub_zero, smul_eq_mul, iteratedDerivWithin_univ]
  -- Split off the first three terms.
  have hsplit : (∑ k ∈ Finset.range (D + 1),
      ((Nat.factorial k : ℝ))⁻¹ * x ^ k * iteratedDeriv k L 0) =
      (∑ k ∈ Finset.Ico 0 3,
        ((Nat.factorial k : ℝ))⁻¹ * x ^ k * iteratedDeriv k L 0) +
      ∑ k ∈ Finset.Ico 3 (D + 1),
        ((Nat.factorial k : ℝ))⁻¹ * x ^ k * iteratedDeriv k L 0 := by
    rw [Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive _ (by omega : 0 ≤ 3)
        (by omega : 3 ≤ D + 1)]
  rw [hsplit]
  -- The head: k = 0, 1 vanish; k = 2 is the base term.
  have hhead : (∑ k ∈ Finset.Ico 0 3,
      ((Nat.factorial k : ℝ))⁻¹ * x ^ k * iteratedDeriv k L 0) =
      taylorBase L * x ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [Finset.sum_range_succ, iteratedDeriv_zero, h.zero,
      iteratedDeriv_one, h.deriv_zero, taylorBase, Nat.factorial]
    ring
  rw [hhead]
  -- The tail: reindex to Fin (D - 2).
  have htail : (∑ k ∈ Finset.Ico 3 (D + 1),
      ((Nat.factorial k : ℝ))⁻¹ * x ^ k * iteratedDeriv k L 0) =
      ∑ i : Fin (D - 2), taylorCoeff L D i * 1 ^ (i.1 + 1) *
        x ^ (2 * 1 + (i.1 + 1)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    rw [show D + 1 - 3 = D - 2 by omega]
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦
      ((Nat.factorial (3 + i) : ℝ))⁻¹ * x ^ (3 + i) *
        iteratedDeriv (3 + i) L 0) (D - 2)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [taylorCoeff]
    rw [show 2 + (i.1 + 1) = 3 + i.1 by omega]
    rw [one_pow]
    ring
  rw [htail, jetPotential]

/-- Extension of a jet coefficient vector by zeros, with the
stabilizer `d` at the top slot (index `M - 3`, carrying degree
`M`). -/
noncomputable def stabilizedCoeff (R' M : ℕ) (c : Fin R' → ℝ)
    (d : ℝ) : Fin (M - 2) → ℝ :=
  fun i ↦ if h : i.1 < R' then c ⟨i.1, h⟩
    else if i.1 = M - 3 then d else 0

/-- The stabilized jet potential is the original jet plus the top
monomial. -/
theorem stabilized_jet_eq {R' M : ℕ} (hM : R' + 2 < M)
    (a : ℝ) (c : Fin R' → ℝ) (d : ℝ) (x : ℝ) :
    jetPotential 1 (M - 2) a 1 (stabilizedCoeff R' M c d) x =
      jetPotential 1 R' a 1 c x + d * x ^ M := by
  unfold jetPotential
  set g : ℕ → ℝ := fun k ↦
    (if h : k < R' then c ⟨k, h⟩ else if k = M - 3 then d else 0) *
      x ^ (2 * 1 + (k + 1)) with hg_def
  set f : ℕ → ℝ := fun k ↦
    (if h : k < R' then c ⟨k, h⟩ else 0) * x ^ (2 * 1 + (k + 1))
    with hf_def
  have hL : (∑ i : Fin (M - 2), stabilizedCoeff R' M c d i *
      1 ^ (i.1 + 1) * x ^ (2 * 1 + (i.1 + 1))) =
      ∑ k ∈ Finset.range (M - 2), g k := by
    rw [← Fin.sum_univ_eq_sum_range g (M - 2)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hg_def, stabilizedCoeff, one_pow, mul_one]
  have hR : (∑ i : Fin R', c i * 1 ^ (i.1 + 1) *
      x ^ (2 * 1 + (i.1 + 1))) = ∑ k ∈ Finset.range R', f k := by
    rw [← Fin.sum_univ_eq_sum_range f R']
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hf_def, one_pow, mul_one]
    rw [dif_pos i.isLt]
  have hsplit : (∑ k ∈ Finset.range (M - 2), g k) =
      (∑ k ∈ Finset.Ico 0 R', g k) +
        ∑ k ∈ Finset.Ico R' (M - 2), g k := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _
      (by omega : 0 ≤ R') (by omega : R' ≤ M - 2)]
  have hlow : (∑ k ∈ Finset.Ico 0 R', g k) =
      ∑ k ∈ Finset.range R', f k := by
    rw [Finset.range_eq_Ico]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkR : k < R' := (Finset.mem_Ico.mp hk).2
    rw [hg_def, hf_def]
    simp only [dif_pos hkR]
  have hhigh : (∑ k ∈ Finset.Ico R' (M - 2), g k) = d * x ^ M := by
    have hstep : ∀ k ∈ Finset.Ico R' (M - 2),
        g k = if k = M - 3 then d * x ^ (2 * 1 + (k + 1)) else 0 := by
      intro k hk
      have hkR : ¬ k < R' := by
        have := (Finset.mem_Ico.mp hk).1
        omega
      rw [hg_def]
      simp only [dif_neg hkR]
      by_cases hk3 : k = M - 3
      · simp [hk3]
      · simp [hk3]
    rw [Finset.sum_congr rfl hstep, Finset.sum_ite_eq' _ _ _]
    rw [if_pos (Finset.mem_Ico.mpr ⟨by omega, by omega⟩),
      show 2 * 1 + (M - 3 + 1) = M by omega]
  rw [hL, hR, hsplit, hlow, hhigh]
  ring

end Laplace.OneD
