/-
Copyright (c) 2026 Timaeus AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.OneD.AnharmonicFDT
import Laplace.OneD.AnharmonicKappa3

/-!
# Large-`t` asymptote of the anharmonic cross-susceptibility

The FDT-capstone tide proved the unconditional three-point identity
`∂_h Cov_h(x,x)|_{h=0} = -t · κ₃(x,x,x)` for the anharmonic Gibbs measure, and
deferred its `t → ∞` asymptote. This file lands it: composing that identity
with the third-cumulant asymptotic `t² κ₃ → -α/λ³` gives
\[
  t \cdot \frac{\partial}{\partial h}\Big|_{0}\mathrm{Cov}_h(x,x)
    = -t^2\,\kappa_3 \;\xrightarrow[t\to\infty]{}\; \frac{\alpha}{\lambda^3}.
\]
This is the closed-form value validated empirically (HMC) in the 1D
FDT-identity experiment: `∂_h Cov ∼ α/(λ³ t)`, i.e. the rescaled limit
`t · ∂_h Cov → α/λ³`.
-/

open MeasureTheory Filter Topology

namespace Laplace.OneD

/-- **Large-`t` asymptote of the cross-susceptibility.**
`t · ∂_h Cov_h(x,x)|_{h=0} → α/λ³` as `t → ∞`. -/
theorem gibbsCov_deriv_anharmonic_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto
      (fun t : ℝ => t * deriv
        (fun h : ℝ => Threepoint.gibbsCov (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t h
            (fun x : ℝ => x) (fun x : ℝ => x)) 0)
      Filter.atTop (nhds (alpha / lam ^ 3)) := by
  -- `-(t² κ₃) → -(-α/λ³) = α/λ³`.
  have hlim :
      Filter.Tendsto
        (fun t : ℝ => -(t ^ 2 * Threepoint.kappa3 (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma)
            (fun x : ℝ => x) t (fun x : ℝ => x) (fun x : ℝ => x)))
        Filter.atTop (nhds (alpha / lam ^ 3)) := by
    have h := (kappa3_anharmonic_id_id_id_asymptotic hlam hgamma hdisc).neg
    have heq : -(-alpha / lam ^ 3) = alpha / lam ^ 3 := by ring
    rwa [heq] at h
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [(gibbsCov_deriv_anharmonic_id_id_id_eq hlam hgamma hdisc ht).deriv]
  ring

end Laplace.OneD
