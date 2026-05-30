/-
Copyright (c) 2026 Timaeus AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.OneD.AnharmonicPartitionDerivGeneralH

/-!
# Moment-normalisation: partition derivatives are unperturbed Gibbs moments

The partition-derivative arc produced, for the anharmonic potential, the
iterated `h`-derivatives of the perturbed partition `Z = weightedPartition … 0`
at `h = 0`: `iteratedDeriv n Z 0 = ∫ (-(t x))^n e^{-tL}`. Dividing by
`Z(0) = ∫ e^{-tL} > 0` turns these into the **unperturbed Gibbs expectation**
of the observable `(-(t x))^n`,
\[
  \frac{Z^{(n)}(0)}{Z(0)} = \big\langle (-(t x))^n \big\rangle_0
    = \texttt{gibbsExp}\ \mu\ L\ \mathrm{id}\ t\ 0\ \big(x \mapsto (-(t x))^n\big).
\]
This ties the arc to the `Threepoint.gibbsExp` machinery used by the FDT
capstone, and is the natural reading of the derivatives: the `n`-th derivative
of the log-partition's first integral is the `n`-th raw moment of the
perturbation observable.
-/

open MeasureTheory

namespace Laplace.OneD

/-- **Moment-normalisation.** For the anharmonic potential and `t > 0`, the
`n`-th `h`-derivative of the perturbed partition at `h = 0`, divided by the
partition value `Z(0)`, equals the unperturbed Gibbs expectation of the
observable `(-(t x))^n`. -/
theorem iteratedDeriv_partition_div_eq_gibbsExp
    {lam alpha gamma t : ℝ} (n : ℕ)
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (ht : 0 < t) :
    iteratedDeriv n (weightedPartition lam alpha gamma t 0) 0
        / weightedPartition lam alpha gamma t 0 0
      = Threepoint.gibbsExp (volume : Measure ℝ)
          (anharmonicPotential lam alpha gamma) (fun x : ℝ => x) t 0
          (fun x : ℝ => (-(t * x)) ^ n) := by
  rw [iteratedDeriv_weightedPartition_zero hlam hgamma hdisc ht n (by norm_num)]
  unfold weightedPartition Threepoint.gibbsExp
  -- Numerators are identical (after beta); the denominators differ only by
  -- `(-(t x))^0 = 1`. `simp` reduces both and closes by reflexivity.
  simp only [pow_zero, one_mul]

end Laplace.OneD
