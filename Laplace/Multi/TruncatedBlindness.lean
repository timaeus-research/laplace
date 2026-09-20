/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.KernelInstance
import Laplace.Multi.ForwardTheorems

/-!
# Finite-order non-identifiability from a finite observable family

The leading-rate blindness of finite families (`finite_family_leading_rate_blind`) is
upgraded to the level of expansion coefficients: in `d ≥ 2`, for every family of `n`
observables and every `N ≥ max (n − 2) 1`, there are two certified polynomial losses
`½ qform + Q` and `½ qform` (`Q` a nonzero homogeneous polynomial of degree `N + 2` in the
kernel of the observation operator) with different degree-`(N+2)` tensors whose forward
moment expansions (`momentCoeff`) agree at every order `≤ N` for every observable of the
family. The polynomial losses carry `ForwardExpansionDomain N` packages because their
Taylor remainder beyond degree `N + 2` vanishes identically
(`forwardExpansionDomain_halfQform_add`), and coefficient agreement is the uniqueness of
asymptotic expansions (`momentCoeff_eq_of_isLittleO`) applied to the blindness rate.

This is the finite-order form of the full-expansion question: for every truncation order
the truncated data map on jets is not injective. Whether a single pair of germs can share
the FULL expansions of a finite family (the first discrepancy escaping to higher degree as
the order grows is the gap) remains open; see the slop note.
-/

open Real MeasureTheory Filter Topology Asymptotics
open scoped ContDiff

namespace Laplace.Multi

variable {d : ℕ}

/-- **The forward expansion package for `½ qform + Q`**, `Q` smooth and homogeneous of
degree `N + 2`: the Taylor remainder beyond degree `N + 2` is identically zero. -/
noncomputable def forwardExpansionDomain_halfQform_add {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {Q : EuclidD d → ℝ} (hQ : ContDiff ℝ ∞ Q) {N : ℕ} (hN : 0 < N)
    (hhom : IsHomogeneousOfDegree (N + 2) Q) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y : EuclidD d, |Q y| ≤ M * ‖y‖ ^ (N + 2)) :
    ForwardExpansionDomain N (fun x ↦ halfQform H x + Q x) H where
  toHigherLaplaceDomain := higherLaplaceDomain_halfQform_add hH hQ (by omega) hhom hM0 hM
  taylorPeano := by
    have hsum : ∀ y : EuclidD d, ∑ m ∈ Finset.range (N + 3),
        taylorHomogeneousTerm m (fun x ↦ halfQform H x + Q x) y = halfQform H y + Q y := by
      intro y
      rw [Finset.sum_range_succ, sum_taylor_halfQform_add hQ (by omega) hhom,
        taylorHomogeneousTerm_add (contDiff_halfQform H) hQ,
        taylorHomogeneousTerm_of_isHomogeneous (contDiff_halfQform H)
          (isHomogeneousOfDegree_halfQform H),
        taylorHomogeneousTerm_of_isHomogeneous hQ hhom, if_pos rfl, if_neg (by omega)]
      simp
    have hzero : (fun y : EuclidD d ↦ (fun x ↦ halfQform H x + Q x) y -
        ∑ m ∈ Finset.range (N + 3), taylorHomogeneousTerm m (fun x ↦ halfQform H x + Q x) y) =
        fun _ ↦ (0 : ℝ) := by
      funext y
      rw [hsum y]
      simp
    rw [hzero]
    exact isLittleO_zero _ _

/-- **Finite-order non-identifiability of finite families** (`d ≥ 2`): for every family of
`n` observables and every `N > 0` with `n ≤ N + 2`, there are two polynomial losses with
forward expansion packages of order `N`, equal jets below degree `N + 2`, different
degree-`(N+2)` tensors, and identical moment expansion coefficients at every order `≤ N`
for every observable of the family. -/
theorem exists_pair_finite_family_truncated_blind (hd : 2 ≤ d) {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {n : ℕ} (φ : Fin n → EuclidD d → ℝ)
    (hφc : ∀ i, Continuous (φ i)) (hφg : ∀ i, HasPolynomialGrowth (φ i))
    {N : ℕ} (hN : 0 < N) (hnk : n ≤ N + 2) :
    ∃ (L₁ L₂ : EuclidD d → ℝ) (D₁ : ForwardExpansionDomain N L₁ H)
      (D₂ : ForwardExpansionDomain N L₂ H),
      (∀ j < N + 2, iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0) ∧
      iteratedFDeriv ℝ (N + 2) L₁ 0 ≠ iteratedFDeriv ℝ (N + 2) L₂ 0 ∧
      ∀ i, ∀ j ≤ N, D₁.momentCoeff (φ i) j = D₂.momentCoeff (φ i) j := by
  have hk : 2 < N + 2 := by omega
  obtain ⟨Q, hQ, hQne, hblind⟩ := finite_family_leading_rate_blind hd hH φ hφc hφg hk hnk
  have hQs : ContDiff ℝ ∞ Q := contDiff_of_mem_homogPolySpan hQ
  have hhom : IsHomogeneousOfDegree (N + 2) Q := homogPolySpan_isHomogeneous hQ
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_isHomogeneous hQs.continuous (by omega) hhom
  have hzero_hom : IsHomogeneousOfDegree (N + 2) (fun _ : EuclidD d ↦ (0 : ℝ)) := by
    intro a x
    simp
  have hzero_bound : ∀ y : EuclidD d, |(fun _ : EuclidD d ↦ (0 : ℝ)) y| ≤ 0 * ‖y‖ ^ (N + 2) := by
    intro y
    simp
  let D₁ := forwardExpansionDomain_halfQform_add hH hQs hN hhom hM0 hM
  let D₂ := forwardExpansionDomain_halfQform_add hH contDiff_const hN hzero_hom le_rfl hzero_bound
  have hadd : ∀ j, iteratedFDeriv ℝ j (fun x ↦ halfQform H x + Q x) 0 =
      iteratedFDeriv ℝ j (halfQform H) 0 + iteratedFDeriv ℝ j Q 0 := by
    intro j
    have hsum : (fun x ↦ halfQform H x + Q x) = halfQform H + Q := by
      funext x
      simp
    rw [hsum, iteratedFDeriv_add_apply
      ((contDiff_halfQform H).contDiffAt.of_le (natCast_le_infty j))
      (hQs.contDiffAt.of_le (natCast_le_infty j))]
  have hL₂ : (fun x ↦ halfQform H x + (fun _ : EuclidD d ↦ (0 : ℝ)) x) = halfQform H := by
    funext x
    simp
  have hlower : ∀ j < N + 2, iteratedFDeriv ℝ j (fun x ↦ halfQform H x + Q x) 0 =
      iteratedFDeriv ℝ j (fun x ↦ halfQform H x + (fun _ : EuclidD d ↦ (0 : ℝ)) x) 0 := by
    intro j hj
    rw [hL₂, hadd, iteratedFDeriv_zero_of_isHomogeneous hQs hhom hj.ne, add_zero]
  have hdiff : (fun x ↦ taylorHomogeneousTerm (N + 2) (fun x ↦ halfQform H x + Q x) x -
      taylorHomogeneousTerm (N + 2) (fun x ↦ halfQform H x + (fun _ : EuclidD d ↦ (0 : ℝ)) x) x)
      = Q := by
    funext x
    rw [hL₂, taylorHomogeneousTerm_add (contDiff_halfQform H) hQs,
      taylorHomogeneousTerm_of_isHomogeneous hQs hhom, if_pos rfl]
    simp
  refine ⟨_, _, D₁, D₂, hlower, ?_, ?_⟩
  · rw [hL₂, hadd]
    intro heq
    have hk0 : iteratedFDeriv ℝ (N + 2) Q 0 = 0 := by
      have := congrArg (fun T ↦ T - iteratedFDeriv ℝ (N + 2) (halfQform H) 0) heq
      simpa using this
    apply hQne
    funext x
    have hdg := iteratedFDeriv_diag_of_isHomogeneous hQs hhom x
    rw [hk0, zero_apply] at hdg
    have hfac : ((N + 2).factorial : ℝ) ≠ 0 := by exact_mod_cast (N + 2).factorial_ne_zero
    simpa [hfac] using hdg.symm
  · intro i
    have h := hblind D₁.toHigherLaplaceDomain D₂.toHigherLaplaceDomain hlower hdiff i
    rw [show N + 2 - 2 = N by omega] at h
    exact momentCoeff_eq_of_isLittleO D₁ D₂ (hφc i) (hφg i) h

end Laplace.Multi
