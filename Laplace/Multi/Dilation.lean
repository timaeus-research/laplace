/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.Basic

/-!
# The ambient space and the dilation wrapper

Stages H0-H1 of the multivariate Theorem 3.1 programme (germbij; also
the Susceptibility Primer's Stage 3). The ambient representation is
`EuclideanSpace ℝ (Fin d)` — coordinate-accessible while composing
with inner products and the Hilbert-space APIs — and the single
project-local change-of-variables wrapper is
`∫ f = q^d · ∫ f(q•x)` for `q > 0` (`integral_dilation`), with the
indicator form for expanding domains (`setIntegral_dilation`). The
orientation (substitution carries `q^d`; the Mathlib pushforward
carries `|q^{-d}|`) is fixed here once, so downstream proofs never
touch it.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

/-- The ambient space of the multivariate programme. -/
abbrev EuclidD (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- **The dilation wrapper** (stage H1): the substitution `w = q·x`
carries the Jacobian `q^d`. All downstream change-of-variables goes
through this single lemma. -/
theorem integral_dilation {d : ℕ} (f : EuclidD d → ℝ) {q : ℝ}
    (hq : 0 < q) :
    ∫ x : EuclidD d, f x = q ^ d * ∫ x : EuclidD d, f (q • x) := by
  have h := MeasureTheory.Measure.integral_comp_smul (μ := volume) f q
  rw [finrank_euclideanSpace_fin, smul_eq_mul,
    abs_of_pos (inv_pos.mpr (by positivity : (0:ℝ) < q ^ d))] at h
  rw [h]
  field_simp

/-- The indicator form for expanding domains (the stage-H4 shape):
a set integral becomes a fixed-space integral of the dilated
indicator. -/
theorem setIntegral_dilation {d : ℕ} (f : EuclidD d → ℝ)
    {U : Set (EuclidD d)} (hU : MeasurableSet U) {q : ℝ}
    (hq : 0 < q) :
    ∫ x in U, f x = q ^ d *
      ∫ x : EuclidD d, Set.indicator U f (q • x) := by
  rw [← integral_indicator hU, integral_dilation _ hq]

end Laplace.Multi
