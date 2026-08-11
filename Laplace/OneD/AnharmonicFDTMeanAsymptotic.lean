/-
Copyright (c) 2026 Timaeus AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.OneD.AnharmonicFDT
import Laplace.OneD.IntegralRemainder

/-!
# Large-`t` asymptote of the anharmonic first-cumulant FDT

Companion to the cross-susceptibility asymptote. The FDT-capstone tide proved
`∂_h ⟨x⟩_h|_{h=0} = -t · Cov_0(x,x)`; here we take `t → ∞`:
\[
  \frac{\partial}{\partial h}\Big|_0 \langle x\rangle_h
    = -t\,\mathrm{Var}_0(x) \;\xrightarrow[t\to\infty]{}\; -\frac{1}{\lambda}.
\]
The FDT identity is stated with the abstract `Threepoint.gibbsCov` while the
asymptotic `cov_self_anharmonic_asymptotic` is stated with the concrete
`Laplace.gibbsCov`; a small definitional bridge (`Threepoint`-expectation at
`h = 0` equals the `Laplace` expectation) connects them.
-/

open MeasureTheory Filter Topology

namespace Laplace.OneD

/-- **Bridge.** At `h = 0`, `A = id`, against Lebesgue, the abstract
`Threepoint` Gibbs expectation is the concrete `Laplace` one. -/
theorem threepoint_gibbsExp_zero_eq_laplace
    (lam alpha gamma t : ℝ) (φ : ℝ → ℝ) :
    Threepoint.gibbsExp (volume : Measure ℝ)
        (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0 φ
      = Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) t φ := by
  unfold Threepoint.gibbsExp Laplace.gibbsExpectation Laplace.partitionFunction
  simp only [zero_mul, add_zero]

/-- **Bridge (covariance).** The `Threepoint` covariance at `h = 0` is the
`Laplace` covariance. -/
theorem threepoint_gibbsCov_zero_eq_laplace
    (lam alpha gamma t : ℝ) (φ ψ : ℝ → ℝ) :
    Threepoint.gibbsCov (volume : Measure ℝ)
        (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0 φ ψ
      = Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t φ ψ := by
  unfold Threepoint.gibbsCov Laplace.gibbsCov
  rw [threepoint_gibbsExp_zero_eq_laplace, threepoint_gibbsExp_zero_eq_laplace,
    threepoint_gibbsExp_zero_eq_laplace]

/-- **Large-`t` asymptote of the first-cumulant FDT.**
`∂_h ⟨x⟩_h|_{h=0} → -1/λ` as `t → ∞`. -/
theorem gibbsExp_deriv_anharmonic_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto
      (fun t : ℝ => deriv
        (fun h : ℝ => Threepoint.gibbsExp (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t h
            (fun x : ℝ => x)) 0)
      Filter.atTop (nhds (-1 / lam)) := by
  have hlim :
      Filter.Tendsto
        (fun t : ℝ => -(t * Laplace.gibbsCov (anharmonicPotential lam alpha gamma)
          t (fun x : ℝ => x) (fun x : ℝ => x)))
        Filter.atTop (nhds (-1 / lam)) := by
    have h := (cov_self_anharmonic_asymptotic hlam hgamma hdisc).neg
    have heq : -(1 / lam) = -1 / lam := by ring
    rwa [heq] at h
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [(gibbsExp_deriv_anharmonic_id_id_eq hlam hgamma hdisc ht).deriv,
    threepoint_gibbsCov_zero_eq_laplace]
  ring

end Laplace.OneD
