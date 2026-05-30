/-
Copyright (c) 2026 Timaeus AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.OneD.AnharmonicThirdCumulant

/-!
# Fourth connected cumulant of the anharmonic Gibbs measure

The fourth connected cumulant of `u = -(t x)` is the third derivative of the
perturbed mean `M(h) = ⟨u⟩_h = G_1(h)/G_0(h)` at `h = 0`:
\[
  \kappa_4 = \frac{\partial^3}{\partial h^3}\Big|_0\langle u\rangle_h
    = \langle u^4\rangle_0 - 4\langle u^3\rangle_0\langle u\rangle_0
      - 3\langle u^2\rangle_0^2 + 12\langle u^2\rangle_0\langle u\rangle_0^2
      - 6\langle u\rangle_0^4,
\]
the flow-equation / fourth-cumulant identity. The first derivative of `M` is
the susceptibility `S = (G_2 G_0 - G_1^2)/G_0^2`; the second is
`S_2 = (G_3 G_0^2 - 3 G_1 G_2 G_0 + 2 G_1^3)/G_0^3` (so `deriv S = S_2` near 0,
the general-`h` third cumulant proved below); differentiating `S_2` once more
gives `κ_4`. The three layers are stitched together with
`Filter.EventuallyEq.deriv`.
-/

open MeasureTheory Topology

namespace Laplace.OneD

/-- **General-`h` third cumulant.** For `|h₀| < 1`, the derivative of the
susceptibility `S = (G_2 G_0 - G_1^2)/G_0^2` at `h₀` is
`(G_3 G_0^2 - 3 G_1 G_2 G_0 + 2 G_1^3)/G_0^3` evaluated at `h₀`. (The `h₀ = 0`
instance is `anharmonic_third_cumulant`.) -/
theorem anharmonic_susceptibility_deriv_general
    {lam alpha gamma t : ℝ} {h₀ : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) (hh₀ : |h₀| < 1) :
    HasDerivAt
      (fun h : ℝ => (weightedPartition lam alpha gamma t 2 h
            * weightedPartition lam alpha gamma t 0 h
          - weightedPartition lam alpha gamma t 1 h
            * weightedPartition lam alpha gamma t 1 h)
        / weightedPartition lam alpha gamma t 0 h ^ 2)
      ((weightedPartition lam alpha gamma t 3 h₀
            * weightedPartition lam alpha gamma t 0 h₀ ^ 2
          - 3 * weightedPartition lam alpha gamma t 1 h₀
            * weightedPartition lam alpha gamma t 2 h₀
            * weightedPartition lam alpha gamma t 0 h₀
          + 2 * weightedPartition lam alpha gamma t 1 h₀ ^ 3)
        / weightedPartition lam alpha gamma t 0 h₀ ^ 3) h₀ := by
  have hne : weightedPartition lam alpha gamma t 0 h₀ ≠ 0 :=
    (weightedPartition_zero_pos hlam hgamma hdisc ht hh₀).ne'
  have hG0 := weightedPartition_hasDerivAt 0 hlam hgamma hdisc ht (h₀ := h₀) hh₀
  have hG1 := weightedPartition_hasDerivAt 1 hlam hgamma hdisc ht (h₀ := h₀) hh₀
  have hG2 := weightedPartition_hasDerivAt 2 hlam hgamma hdisc ht (h₀ := h₀) hh₀
  have hnum : HasDerivAt
      (fun h : ℝ => weightedPartition lam alpha gamma t 2 h
          * weightedPartition lam alpha gamma t 0 h
        - weightedPartition lam alpha gamma t 1 h
          * weightedPartition lam alpha gamma t 1 h) _ h₀ :=
    (hG2.mul hG0).sub (hG1.mul hG1)
  have hden : HasDerivAt
      (fun h : ℝ => weightedPartition lam alpha gamma t 0 h ^ 2) _ h₀ :=
    hG0.pow 2
  convert hnum.div hden (pow_ne_zero 2 hne) using 1
  field_simp
  ring

/-- **Fourth connected cumulant** of `u = -(t x)`: the third `h`-derivative of
the perturbed mean `G_1(h)/G_0(h)` at `0`. -/
theorem anharmonic_fourth_cumulant
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    iteratedDeriv 3
        (fun h : ℝ => weightedPartition lam alpha gamma t 1 h
          / weightedPartition lam alpha gamma t 0 h) 0
      = (weightedPartition lam alpha gamma t 4 0
            * weightedPartition lam alpha gamma t 0 0 ^ 3
          - 4 * weightedPartition lam alpha gamma t 3 0
            * weightedPartition lam alpha gamma t 1 0
            * weightedPartition lam alpha gamma t 0 0 ^ 2
          - 3 * weightedPartition lam alpha gamma t 2 0 ^ 2
            * weightedPartition lam alpha gamma t 0 0 ^ 2
          + 12 * weightedPartition lam alpha gamma t 2 0
            * weightedPartition lam alpha gamma t 1 0 ^ 2
            * weightedPartition lam alpha gamma t 0 0
          - 6 * weightedPartition lam alpha gamma t 1 0 ^ 4)
        / weightedPartition lam alpha gamma t 0 0 ^ 4 := by
  have hne : weightedPartition lam alpha gamma t 0 0 ≠ 0 :=
    (weightedPartition_zero_zero_pos hlam hgamma hdisc ht).ne'
  -- (B) Differentiate the third-cumulant function `S₂` at 0.
  have hG0 := weightedPartition_hasDerivAt 0 hlam hgamma hdisc ht (h₀ := 0) (by norm_num)
  have hG1 := weightedPartition_hasDerivAt 1 hlam hgamma hdisc ht (h₀ := 0) (by norm_num)
  have hG2 := weightedPartition_hasDerivAt 2 hlam hgamma hdisc ht (h₀ := 0) (by norm_num)
  have hG3 := weightedPartition_hasDerivAt 3 hlam hgamma hdisc ht (h₀ := 0) (by norm_num)
  have hG4 := weightedPartition_hasDerivAt 4 hlam hgamma hdisc ht (h₀ := 0) (by norm_num)
  have hnum2 : HasDerivAt
      (fun h : ℝ => weightedPartition lam alpha gamma t 3 h
          * weightedPartition lam alpha gamma t 0 h ^ 2
        - 3 * weightedPartition lam alpha gamma t 1 h
          * weightedPartition lam alpha gamma t 2 h
          * weightedPartition lam alpha gamma t 0 h
        + 2 * weightedPartition lam alpha gamma t 1 h ^ 3) _ 0 :=
    ((hG3.mul (hG0.pow 2)).sub (((hG1.const_mul 3).mul hG2).mul hG0)).add
      ((hG1.pow 3).const_mul 2)
  have hden2 : HasDerivAt
      (fun h : ℝ => weightedPartition lam alpha gamma t 0 h ^ 3) _ 0 :=
    hG0.pow 3
  have hS2 :
      HasDerivAt
        (fun h : ℝ => (weightedPartition lam alpha gamma t 3 h
              * weightedPartition lam alpha gamma t 0 h ^ 2
            - 3 * weightedPartition lam alpha gamma t 1 h
              * weightedPartition lam alpha gamma t 2 h
              * weightedPartition lam alpha gamma t 0 h
            + 2 * weightedPartition lam alpha gamma t 1 h ^ 3)
          / weightedPartition lam alpha gamma t 0 h ^ 3)
        ((weightedPartition lam alpha gamma t 4 0
              * weightedPartition lam alpha gamma t 0 0 ^ 3
            - 4 * weightedPartition lam alpha gamma t 3 0
              * weightedPartition lam alpha gamma t 1 0
              * weightedPartition lam alpha gamma t 0 0 ^ 2
            - 3 * weightedPartition lam alpha gamma t 2 0 ^ 2
              * weightedPartition lam alpha gamma t 0 0 ^ 2
            + 12 * weightedPartition lam alpha gamma t 2 0
              * weightedPartition lam alpha gamma t 1 0 ^ 2
              * weightedPartition lam alpha gamma t 0 0
            - 6 * weightedPartition lam alpha gamma t 1 0 ^ 4)
          / weightedPartition lam alpha gamma t 0 0 ^ 4) 0 := by
    convert hnum2.div hden2 (pow_ne_zero 3 hne) using 1
    simp only [Pi.pow_apply, Pi.mul_apply]
    field_simp
    ring
  -- Chaining: deriv M = S, deriv S = S₂, on a neighbourhood of 0.
  have hball : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_self]; exact one_pos)
  have hMS : deriv (fun h : ℝ => weightedPartition lam alpha gamma t 1 h
        / weightedPartition lam alpha gamma t 0 h)
      =ᶠ[𝓝 0]
      (fun h : ℝ => (weightedPartition lam alpha gamma t 2 h
            * weightedPartition lam alpha gamma t 0 h
          - weightedPartition lam alpha gamma t 1 h
            * weightedPartition lam alpha gamma t 1 h)
        / weightedPartition lam alpha gamma t 0 h ^ 2) := by
    filter_upwards [hball] with h₀ hmem
    have hh : |h₀| < 1 := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem; exact hmem
    exact (anharmonic_mean_hasDerivAt_general hlam hgamma hdisc ht hh).deriv
  have hSS2 : deriv (fun h : ℝ => (weightedPartition lam alpha gamma t 2 h
            * weightedPartition lam alpha gamma t 0 h
          - weightedPartition lam alpha gamma t 1 h
            * weightedPartition lam alpha gamma t 1 h)
        / weightedPartition lam alpha gamma t 0 h ^ 2)
      =ᶠ[𝓝 0]
      (fun h : ℝ => (weightedPartition lam alpha gamma t 3 h
            * weightedPartition lam alpha gamma t 0 h ^ 2
          - 3 * weightedPartition lam alpha gamma t 1 h
            * weightedPartition lam alpha gamma t 2 h
            * weightedPartition lam alpha gamma t 0 h
          + 2 * weightedPartition lam alpha gamma t 1 h ^ 3)
        / weightedPartition lam alpha gamma t 0 h ^ 3) := by
    filter_upwards [hball] with h₀ hmem
    have hh : |h₀| < 1 := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem; exact hmem
    exact (anharmonic_susceptibility_deriv_general hlam hgamma hdisc ht hh).deriv
  -- iteratedDeriv 3 M 0 = deriv (deriv (deriv M)) 0 = deriv S₂ 0 = κ₄.
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
    (hMS.deriv.trans hSS2).deriv_eq, hS2.deriv]

end Laplace.OneD
