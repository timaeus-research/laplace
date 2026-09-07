/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.HeadlineGaussian

/-!
# Core identity for the product-density lemma (general-`d` monomial model, step 0)

The pushforward of `∏ tᵢ^{λ−1} dt` on `(0,1]^d` under `t ↦ ∏ tᵢ` has density
`z^{λ−1} (−log z)^{d−1}/(d−1)!`; the induction on `d` reduces to the one-dimensional identity

`∫_z^1 (log t − log z)^d / t dt = (−log z)^{d+1}/(d+1)`  (`integral_log_sub_pow_div`),

proved by the fundamental theorem of calculus with antiderivative `(log t − log z)^{d+1}/(d+1)`.
Zero `sorry`/`axiom`.
-/

open Real Set MeasureTheory intervalIntegral

namespace Laplace.Grammar

/-- The antiderivative `(log t − log z)^{d+1}/(d+1)` of `(log t − log z)^d / t` for `t > 0`. -/
theorem hasDerivAt_log_sub_pow_div (z t : ℝ) (ht : 0 < t) (d : ℕ) :
    HasDerivAt (fun t => (Real.log t - Real.log z) ^ (d + 1) / ((d : ℝ) + 1))
      ((Real.log t - Real.log z) ^ d / t) t := by
  have h1 : HasDerivAt (fun t => Real.log t - Real.log z) (1 / t) t := by
    have := (Real.hasDerivAt_log ht.ne').sub_const (Real.log z)
    simpa [one_div] using this
  have h2 := (h1.pow (d + 1)).div_const ((d : ℝ) + 1)
  refine h2.congr_deriv ?_
  have hd : ((d : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-- **Core identity**: `∫_z^1 (log t − log z)^d / t dt = (−log z)^{d+1}/(d+1)` for `0 < z ≤ 1`. -/
theorem integral_log_sub_pow_div (z : ℝ) (hz : 0 < z) (hz1 : z ≤ 1) (d : ℕ) :
    ∫ t in z..1, (Real.log t - Real.log z) ^ d / t = (-Real.log z) ^ (d + 1) / ((d : ℝ) + 1) := by
  have hderiv : ∀ t ∈ uIcc z 1, HasDerivAt
      (fun t => (Real.log t - Real.log z) ^ (d + 1) / ((d : ℝ) + 1))
      ((Real.log t - Real.log z) ^ d / t) t := by
    intro t ht
    rw [uIcc_of_le hz1] at ht
    exact hasDerivAt_log_sub_pow_div z t (lt_of_lt_of_le hz ht.1) d
  have hint : IntervalIntegrable (fun t => (Real.log t - Real.log z) ^ d / t) volume z 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hz1]
    refine ContinuousOn.div (ContinuousOn.pow (ContinuousOn.sub ?_ continuousOn_const) d)
      continuousOn_id fun t ht => (lt_of_lt_of_le hz ht.1).ne'
    exact Real.continuousOn_log.mono fun t ht => (lt_of_lt_of_le hz ht.1).ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [Real.log_one]

end Laplace.Grammar
