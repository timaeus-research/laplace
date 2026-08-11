/-
Copyright (c) 2026 Timaeus AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.OneD.AnharmonicLogPartitionDeriv

/-!
# Second connected cumulant / susceptibility of the anharmonic Gibbs measure

The perturbed mean of the observable `u(x) = -(t x)` is
`⟨u⟩_h = G_1(h)/G_0(h)`, where `G_n(h) = ∫ (-(t x))^n e^{-t(L+hx)}`. Its
derivative at `h = 0` — the **susceptibility** — is the connected second
cumulant of `u` under the unperturbed Gibbs measure:
\[
  \frac{\partial}{\partial h}\Big|_{h=0}\!\langle u \rangle_h
    = \langle u^2 \rangle_0 - \langle u \rangle_0^2 .
\]
This is the fluctuation–dissipation identity at the level of the mean, and the
$\kappa_2$ rung of the cumulant ladder opened by
`logPartition_hasDerivAt`. The proof is a pointwise `HasDerivAt.div` on the
arc's partition derivatives, plus a `field_simp`/`ring` identity tying the
quotient form to the variance form via moment-normalisation.
-/

open MeasureTheory

namespace Laplace.OneD

/-- **Susceptibility.** The derivative at `h = 0` of the perturbed mean
`⟨u⟩_h = G_1(h)/G_0(h)` of `u = -(t x)` is
`(G_2(0)·G_0(0) − G_1(0)²)/G_0(0)²`. -/
theorem anharmonic_mean_hasDerivAt
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    HasDerivAt
      (fun h : ℝ => weightedPartition lam alpha gamma t 1 h
        / weightedPartition lam alpha gamma t 0 h)
      ((weightedPartition lam alpha gamma t 2 0
            * weightedPartition lam alpha gamma t 0 0
          - weightedPartition lam alpha gamma t 1 0
            * weightedPartition lam alpha gamma t 1 0)
        / weightedPartition lam alpha gamma t 0 0 ^ 2) 0 := by
  have hc := weightedPartition_hasDerivAt 1 hlam hgamma hdisc ht (h₀ := 0) (by norm_num)
  have hd := weightedPartition_hasDerivAt 0 hlam hgamma hdisc ht (h₀ := 0) (by norm_num)
  have hne : weightedPartition lam alpha gamma t 0 0 ≠ 0 :=
    (weightedPartition_zero_zero_pos hlam hgamma hdisc ht).ne'
  exact hc.div hd hne

/-- **Second connected cumulant.** The susceptibility equals the connected
variance `⟨u²⟩₀ − ⟨u⟩₀²` of `u = -(t x)` under the unperturbed Gibbs
measure. -/
theorem anharmonic_susceptibility_eq_connected_variance
    {lam alpha gamma t : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    deriv
      (fun h : ℝ => weightedPartition lam alpha gamma t 1 h
        / weightedPartition lam alpha gamma t 0 h) 0
      = Threepoint.gibbsExp (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0
            (fun x : ℝ => (-(t * x)) ^ 2)
        - (Threepoint.gibbsExp (volume : Measure ℝ)
            (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0
            (fun x : ℝ => (-(t * x)) ^ 1)) ^ 2 := by
  rw [(anharmonic_mean_hasDerivAt hlam hgamma hdisc ht).deriv]
  -- Replace each `gibbsExp` moment by `G_n(0)/G_0(0)`.
  have h2 := iteratedDeriv_partition_div_eq_gibbsExp 2 hlam hgamma hdisc ht
  have h1 := iteratedDeriv_partition_div_eq_gibbsExp 1 hlam hgamma hdisc ht
  have hid2 := iteratedDeriv_weightedPartition_zero hlam hgamma hdisc ht 2 (h := 0) (by norm_num)
  have hid1 := iteratedDeriv_weightedPartition_zero hlam hgamma hdisc ht 1 (h := 0) (by norm_num)
  rw [← h2, ← h1, hid2, hid1]
  have hne : weightedPartition lam alpha gamma t 0 0 ≠ 0 :=
    (weightedPartition_zero_zero_pos hlam hgamma hdisc ht).ne'
  -- `(a c − b²)/c² = a/c − (b/c)²` with `c = G_0(0) ≠ 0`. Clear `c` explicitly
  -- so `ring` always finishes (robust to `field_simp` version drift).
  rw [div_pow, div_sub_div _ _ hne (pow_ne_zero 2 hne), div_eq_div_iff
    (pow_ne_zero 2 hne) (mul_ne_zero hne (pow_ne_zero 2 hne))]
  ring

end Laplace.OneD
