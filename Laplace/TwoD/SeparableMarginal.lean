/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.TwoD.AddSeparable

/-!
# Marginal expectation and free-energy additivity for separable 2D Gibbs measures

Companions to `Laplace/TwoD/AddSeparable.lean` at the marginal and CGF (free-energy) levels, for a
separable potential `L(x, y) = U(x) + V(y)`.

* `gibbsExpectation_addSeparable_fst` / `gibbsExpectation_addSeparable_snd`: a single-coordinate
  observable marginalises to its 1D Gibbs expectation, `⟨f∘fst⟩_{2D,t} = ⟨f⟩_{U,t}` (the other
  coordinate integrates out). This is the mean-level companion of the covariance-level
  `SeparableSameCoordCov`; the same step was previously only available inlined inside
  `gibbsCov_addSeparable_fst_snd_eq_zero`.
* `logPartition_addSeparable`: the free energy is additive, `log Z_2D = log Z_U + log Z_V`, the
  CGF-level reading of the partition-function factorisation `Z_2D = Z_U · Z_V`.

These are clean corollaries of the `AddSeparable` factorisation lemmas
(`gibbsExpectation_separable_addSeparable`, `gibbsExpectation_const`,
`partitionFunction_addSeparable_factor`).
-/

open MeasureTheory

namespace Laplace.TwoD

/-- **Marginal expectation, first coordinate.** For a separable potential `L(x, y) = U(x) + V(y)`,
the Gibbs expectation of a first-coordinate observable `f ∘ fst` equals the 1D marginal expectation
`⟨f⟩_{U,t}`: the second coordinate integrates out. Mean-level companion of
`gibbsCov_addSeparable_fst_fst_eq`. -/
theorem gibbsExpectation_addSeparable_fst
    {U V : ℝ → ℝ} {t : ℝ} (f : ℝ → ℝ)
    (hZU_ne : Laplace.partitionFunction U t ≠ 0)
    (hZV_ne : Laplace.partitionFunction V t ≠ 0)
    (hU : Integrable (fun x : ℝ => Real.exp (-(t * U x))))
    (hV : Integrable (fun y : ℝ => Real.exp (-(t * V y))))
    (hf : Integrable (fun x : ℝ => f x * Real.exp (-(t * U x)))) :
    gibbsExpectation (addSeparable U V) t (fun z => f z.1) =
      Laplace.gibbsExpectation U t f := by
  have h := gibbsExpectation_separable_addSeparable f (fun _ => (1 : ℝ))
    hZU_ne hZV_ne hU hV hf (Integrable.const_mul hV 1)
  have hg1 : Laplace.gibbsExpectation V t (fun _ => (1 : ℝ)) = 1 :=
    Laplace.gibbsExpectation_const V t 1 hZV_ne
  rw [show (fun z : ℝ × ℝ => f z.1 * (1 : ℝ)) = (fun z : ℝ × ℝ => f z.1) from by
        funext z; exact MulOneClass.mul_one (f z.1)] at h
  rw [h, hg1, mul_one]

/-- **Marginal expectation, second coordinate.** Symmetric to `gibbsExpectation_addSeparable_fst`:
`⟨g∘snd⟩_{2D,t} = ⟨g⟩_{V,t}`. -/
theorem gibbsExpectation_addSeparable_snd
    {U V : ℝ → ℝ} {t : ℝ} (g : ℝ → ℝ)
    (hZU_ne : Laplace.partitionFunction U t ≠ 0)
    (hZV_ne : Laplace.partitionFunction V t ≠ 0)
    (hU : Integrable (fun x : ℝ => Real.exp (-(t * U x))))
    (hV : Integrable (fun y : ℝ => Real.exp (-(t * V y))))
    (hg : Integrable (fun y : ℝ => g y * Real.exp (-(t * V y)))) :
    gibbsExpectation (addSeparable U V) t (fun z => g z.2) =
      Laplace.gibbsExpectation V t g := by
  have h := gibbsExpectation_separable_addSeparable (fun _ => (1 : ℝ)) g
    hZU_ne hZV_ne hU hV (Integrable.const_mul hU 1) hg
  have hf1 : Laplace.gibbsExpectation U t (fun _ => (1 : ℝ)) = 1 :=
    Laplace.gibbsExpectation_const U t 1 hZU_ne
  rw [show (fun z : ℝ × ℝ => (1 : ℝ) * g z.2) = (fun z : ℝ × ℝ => g z.2) from by
        funext z; exact one_mul (g z.2)] at h
  rw [h, hf1, one_mul]

/-- **Free-energy additivity for a separable potential.** The log-partition function (free energy)
of `L(x, y) = U(x) + V(y)` is the sum of the 1D free energies:
`log Z_2D(t) = log Z_U(t) + log Z_V(t)`. The CGF-level reading of the partition-function
factorisation `partitionFunction_addSeparable_factor`. -/
theorem logPartition_addSeparable
    {U V : ℝ → ℝ} {t : ℝ}
    (hU : Integrable (fun x : ℝ => Real.exp (-(t * U x))))
    (hV : Integrable (fun y : ℝ => Real.exp (-(t * V y))))
    (hZU_pos : 0 < Laplace.partitionFunction U t)
    (hZV_pos : 0 < Laplace.partitionFunction V t) :
    Real.log (partitionFunction (addSeparable U V) t) =
      Real.log (Laplace.partitionFunction U t) + Real.log (Laplace.partitionFunction V t) := by
  rw [partitionFunction_addSeparable_factor hU hV, Real.log_mul hZU_pos.ne' hZV_pos.ne']

end Laplace.TwoD
