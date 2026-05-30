/-
Copyright (c) 2026 Timaeus AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.OneD.AnharmonicSecondCumulant

/-!
# Susceptibility of the anharmonic Gibbs measure at a general perturbation

The previous tide established the susceptibility (derivative of the perturbed
mean `⟨u⟩_h = G_1(h)/G_0(h)` of `u = -(t x)`) at the single point `h = 0`.
This file lifts it to an arbitrary base point `|h₀| < 1`:
\[
  \frac{\partial}{\partial h}\Big|_{h_0}\!\langle u \rangle_h
    = \frac{G_2(h_0)G_0(h_0) - G_1(h_0)^2}{G_0(h_0)^2},
\]
the fluctuation–dissipation (linear-response) identity at any perturbation
strength. It is the foundation for the third cumulant `κ₃`, which is the
second derivative of the mean and therefore needs the mean's derivative as a
function of `h`. Two ingredients: positivity of the perturbed partition at a
general `h₀` (mirroring `anharmonic_partition_pos`), and a pointwise
`HasDerivAt.div` on the arc's general-`h` partition derivatives.
-/

open MeasureTheory

namespace Laplace.OneD

/-- The perturbed partition `∫ exp(-(t(L + h x)))` is strictly positive for
`|h| < 1`. General-`h` analogue of `anharmonic_partition_pos`. -/
theorem partition_perturbed_pos
    {lam alpha gamma t : ℝ} {h : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) (hh : |h| < 1) :
    0 < ∫ x : ℝ,
        Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x))) := by
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · have h_support : Function.support
        (fun x : ℝ =>
          Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x))))
          = Set.univ := by
      ext x
      simp [Function.mem_support, Real.exp_ne_zero]
    rw [h_support, Real.volume_univ]
    exact ENNReal.zero_lt_top
  · exact Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)
  · have hint := integrable_weightedPartition_integrand 0 hlam hgamma hdisc ht hh
    simpa only [pow_zero, one_mul] using hint

/-- `Z(h) = weightedPartition … 0 h > 0` for `|h| < 1`. -/
theorem weightedPartition_zero_pos
    {lam alpha gamma t : ℝ} {h : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) (hh : |h| < 1) :
    0 < weightedPartition lam alpha gamma t 0 h := by
  have heq : weightedPartition lam alpha gamma t 0 h
      = ∫ x : ℝ,
          Real.exp (-(t * (anharmonicPotential lam alpha gamma x + h * x))) := by
    unfold weightedPartition
    congr 1
    funext x
    rw [pow_zero, one_mul]
  rw [heq]
  exact partition_perturbed_pos hlam hgamma hdisc ht hh

/-- **General-`h` susceptibility.** For `|h₀| < 1`, the derivative of the
perturbed mean `⟨u⟩_h = G_1(h)/G_0(h)` at `h₀` is
`(G_2(h₀)·G_0(h₀) − G_1(h₀)²)/G_0(h₀)²`. The `h₀ = 0` instance is the
`κ₂` susceptibility. -/
theorem anharmonic_mean_hasDerivAt_general
    {lam alpha gamma t : ℝ} {h₀ : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) (hh₀ : |h₀| < 1) :
    HasDerivAt
      (fun h : ℝ => weightedPartition lam alpha gamma t 1 h
        / weightedPartition lam alpha gamma t 0 h)
      ((weightedPartition lam alpha gamma t 2 h₀
            * weightedPartition lam alpha gamma t 0 h₀
          - weightedPartition lam alpha gamma t 1 h₀
            * weightedPartition lam alpha gamma t 1 h₀)
        / weightedPartition lam alpha gamma t 0 h₀ ^ 2) h₀ := by
  have hc := weightedPartition_hasDerivAt 1 hlam hgamma hdisc ht (h₀ := h₀) hh₀
  have hd := weightedPartition_hasDerivAt 0 hlam hgamma hdisc ht (h₀ := h₀) hh₀
  have hne : weightedPartition lam alpha gamma t 0 h₀ ≠ 0 :=
    (weightedPartition_zero_pos hlam hgamma hdisc ht hh₀).ne'
  exact hc.div hd hne

end Laplace.OneD
