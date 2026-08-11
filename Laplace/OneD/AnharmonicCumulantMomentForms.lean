/-
Copyright (c) 2026 Timaeus AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.OneD.AnharmonicFourthCumulant

/-!
# Connected cumulants in unperturbed-Gibbs moment form

The third and fourth connected cumulants of `u = -(t x)` were proved as
rational closed forms in the partition values `G_n(0) = weightedPartition … n 0`.
This file re-expresses them in the physically transparent moment form, with
`⟨u^k⟩₀ = gibbsExp … 0 (fun x => (-(t x))^k)` the unperturbed Gibbs expectation:
\[
  \kappa_3 = \langle u^3\rangle_0 - 3\langle u^2\rangle_0\langle u\rangle_0
    + 2\langle u\rangle_0^3,
\]
\[
  \kappa_4 = \langle u^4\rangle_0 - 4\langle u^3\rangle_0\langle u\rangle_0
    - 3\langle u^2\rangle_0^2 + 12\langle u^2\rangle_0\langle u\rangle_0^2
    - 6\langle u\rangle_0^4 .
\]
(The `κ_2` moment form is `anharmonic_susceptibility_eq_connected_variance`.)
Each `⟨u^k⟩₀` rewrites to `G_k(0)/G_0(0)` by moment-normalisation, and the
identities then close by `field_simp` (clearing the `G_0(0)` denominators).
-/

open MeasureTheory

namespace Laplace.OneD

/-- **Third cumulant in moment form.**
`κ₃ = ⟨u³⟩₀ − 3⟨u²⟩₀⟨u⟩₀ + 2⟨u⟩₀³`. -/
theorem anharmonic_third_cumulant_moment_form
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    iteratedDeriv 2
        (fun h : ℝ => weightedPartition lam alpha gamma t 1 h
          / weightedPartition lam alpha gamma t 0 h) 0
      = Threepoint.gibbsExp (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0
            (fun x : ℝ => (-(t * x)) ^ 3)
        - 3 * Threepoint.gibbsExp (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0
            (fun x : ℝ => (-(t * x)) ^ 2)
          * Threepoint.gibbsExp (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0
            (fun x : ℝ => (-(t * x)) ^ 1)
        + 2 * (Threepoint.gibbsExp (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0
            (fun x : ℝ => (-(t * x)) ^ 1)) ^ 3 := by
  have hne : weightedPartition lam alpha gamma t 0 0 ≠ 0 :=
    (weightedPartition_zero_zero_pos hlam hgamma hdisc ht).ne'
  have hmom : ∀ k : ℕ, Threepoint.gibbsExp (volume : Measure ℝ)
      (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0
      (fun x : ℝ => (-(t * x)) ^ k)
      = weightedPartition lam alpha gamma t k 0
        / weightedPartition lam alpha gamma t 0 0 := by
    intro k
    rw [← iteratedDeriv_partition_div_eq_gibbsExp k hlam hgamma hdisc ht,
      iteratedDeriv_weightedPartition_zero hlam hgamma hdisc ht k (h := 0) (by norm_num)]
  rw [anharmonic_third_cumulant hlam hgamma hdisc ht, hmom 3, hmom 2, hmom 1]
  field_simp

/-- **Fourth cumulant in moment form.**
`κ₄ = ⟨u⁴⟩₀ − 4⟨u³⟩₀⟨u⟩₀ − 3⟨u²⟩₀² + 12⟨u²⟩₀⟨u⟩₀² − 6⟨u⟩₀⁴`. -/
theorem anharmonic_fourth_cumulant_moment_form
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    iteratedDeriv 3
        (fun h : ℝ => weightedPartition lam alpha gamma t 1 h
          / weightedPartition lam alpha gamma t 0 h) 0
      = Threepoint.gibbsExp (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0
            (fun x : ℝ => (-(t * x)) ^ 4)
        - 4 * Threepoint.gibbsExp (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0
            (fun x : ℝ => (-(t * x)) ^ 3)
          * Threepoint.gibbsExp (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0
            (fun x : ℝ => (-(t * x)) ^ 1)
        - 3 * (Threepoint.gibbsExp (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0
            (fun x : ℝ => (-(t * x)) ^ 2)) ^ 2
        + 12 * Threepoint.gibbsExp (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0
            (fun x : ℝ => (-(t * x)) ^ 2)
          * (Threepoint.gibbsExp (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0
            (fun x : ℝ => (-(t * x)) ^ 1)) ^ 2
        - 6 * (Threepoint.gibbsExp (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0
            (fun x : ℝ => (-(t * x)) ^ 1)) ^ 4 := by
  have hne : weightedPartition lam alpha gamma t 0 0 ≠ 0 :=
    (weightedPartition_zero_zero_pos hlam hgamma hdisc ht).ne'
  have hmom : ∀ k : ℕ, Threepoint.gibbsExp (volume : Measure ℝ)
      (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0
      (fun x : ℝ => (-(t * x)) ^ k)
      = weightedPartition lam alpha gamma t k 0
        / weightedPartition lam alpha gamma t 0 0 := by
    intro k
    rw [← iteratedDeriv_partition_div_eq_gibbsExp k hlam hgamma hdisc ht,
      iteratedDeriv_weightedPartition_zero hlam hgamma hdisc ht k (h := 0) (by norm_num)]
  rw [anharmonic_fourth_cumulant hlam hgamma hdisc ht, hmom 4, hmom 3, hmom 2, hmom 1]
  field_simp

end Laplace.OneD
