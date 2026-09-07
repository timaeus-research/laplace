/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.GaussianThreshold

/-!
# Headline statements, part III: the constant-Gaussian fluctuation model (rem:pop_vs_emp)

Paper-facing wrappers for units 161 and 163. Scope: the leading coefficient of the `d = 2` chart
expansion with equal starting exponents is `A_p = y₀₀/(k₁k₂) · J_p(x₀₀)` with
`J_p(x) = ∫₀^∞ s^{p−1} e^{−βs²} e^{βsx} ds` (unit 124); the model takes the constant fluctuation
`x₀₀ = X ~ N(0, v)` and computes the expectation of the positive factor `J_p(X)` in the extended
nonnegative reals. NOT claimed: anything about the empirical process itself (whose finite-`n`
exponential moments need not exist), or about the fixed-`n` compact-chart integral (whose
expectation is finite in all regimes). Zero `sorry`/`axiom`.
-/

open MeasureTheory ProbabilityTheory

namespace Laplace.Grammar

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The Gaussian dichotomy** (rem:pop_vs_emp): for `X ~ N(0, v)` the expected leading moment
`E₊[J_p(X)]` is finite iff `βv < 2`, in which case it equals `J_p(0)(1 − βv/2)^{−p/2}`; above the
threshold it is `+∞`. -/
theorem headline_gaussian_dichotomy (β p : ℝ) (hβ : 0 < β) (hp : 0 < p) (X : Ω → ℝ)
    (hX : Measurable X) (v : NNReal) (hXg : μ.map X = gaussianReal 0 v) :
    ((∫⁻ ω, ENNReal.ofReal (gaussMomentJ β p (X ω)) ∂μ) < ⊤ ↔ β * v < 2)
      ∧ (β * v < 2 → ∫⁻ ω, ENNReal.ofReal (gaussMomentJ β p (X ω)) ∂μ
          = ENNReal.ofReal (gaussMomentJ β p 0 * (1 - β * v / 2) ^ (-p / 2)))
      ∧ (2 ≤ β * v → ∫⁻ ω, ENNReal.ofReal (gaussMomentJ β p (X ω)) ∂μ = ⊤) :=
  ⟨lintegral_gaussMomentJ_lt_top_iff β p hβ hp X hX v hXg,
    lintegral_gaussMomentJ_eq_of_lt β p hβ hp X hX v hXg,
    lintegral_gaussMomentJ_eq_top_of_ge β p hβ hp X hX v hXg⟩

/-- **Jensen gap**: for a nondegenerate subcritical Gaussian fluctuation the expected leading
moment strictly exceeds the fluctuation-free value, so `E[C(ξ)] ≠ C(0)` (rem:pop_vs_emp (ii)). -/
theorem headline_gaussian_jensen_gap (β p : ℝ) (hβ : 0 < β) (hp : 0 < p) (X : Ω → ℝ)
    (hX : Measurable X) (v : NNReal) (hv : 0 < (v : ℝ)) (hXg : μ.map X = gaussianReal 0 v)
    (h : β * v < 2) :
    ENNReal.ofReal (gaussMomentJ β p 0) < ∫⁻ ω, ENNReal.ofReal (gaussMomentJ β p (X ω)) ∂μ :=
  lt_lintegral_gaussMomentJ β p hβ hp X hX v hv hXg h

end Laplace.Grammar
