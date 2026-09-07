/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.ChartPosteriorDeterministic

/-!
# Headline statements, part IV: leading rates of the chart posterior ratio

Paper-facing wrappers for units 166–168 (deterministic, one chart, `d = 2`, equal starting exponents
`p`, fixed phase data `x` and amplitudes `y_φ, y_1` with `y_{1,00} > 0`):

* the generic quotient calculus for power–log leading terms (`headline_quotient_calculus`);
* the two-term expansion with power-saving remainder (`headline_leading_two_terms`);
* the constant limit `Z[φ]/Z[1] → y_{φ,00}/y_{1,00}` when the observable does not vanish at the
  corner (`headline_posterior_const_limit`);
* the `1/log N` decay `(Z[φ]/Z[1]) log N → B^φ_p/A^1_p` when it does **and** the constant
  coefficient `B^φ_p` is nonzero (`headline_posterior_log_decay`); corner vanishing alone does
  not force a nonzero `1/log N` term.

NOT claimed: a power improvement from corner vanishing (it does not hold in general), the
identification of the next exponent under coordinatewise divisibility, unequal starting
exponents, or the stochastic version of the `1/log N` regime. Zero `sorry`/`axiom`.
-/

open Asymptotics Filter Real Topology

namespace Laplace.Grammar

/-- **Quotient calculus**: quotients of power–log leading terms. -/
theorem headline_quotient_calculus (Zφ Z₁ : ℝ → ℝ) (Cφ C₁ αφ α₁ : ℝ) (rφ r₁ : ℕ)
    (hφ : Zφ ~[atTop] powLog Cφ αφ rφ) (h₁ : Z₁ ~[atTop] powLog C₁ α₁ r₁) :
    (fun N => Zφ N / Z₁ N) ~[atTop]
      fun N => (Cφ / C₁) * N ^ (-(αφ - α₁)) * (Real.log N ^ rφ / Real.log N ^ r₁) :=
  quotient_isEquivalent Zφ Z₁ Cφ C₁ αφ α₁ rφ r₁ hφ h₁

/-- **Two-term expansion** at the leading exponent with a power-saving remainder. -/
theorem headline_leading_two_terms (β b p ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hy : WSummable ρ y) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b)
        - N ^ (-p) * (canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) p * Real.log N
          + canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x y) b) (anaFaceV (ampCoeff β x y) b)
              (fun i j s => ampCoeff β x y (i, j) s) p))
      =O[atTop] fun N : ℝ => N ^ (-(p + leadingGap k₁ k₂)) * (1 + Real.log N) :=
  chart_leading_isBigO β b p ρ h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ x y hx hy

/-- **Constant posterior limit** for an observable not vanishing at the corner. -/
theorem headline_posterior_const_limit (β b p ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (x yφ y₁ : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hyφ : WSummable ρ yφ) (hy₁ : WSummable ρ y₁) (hy₁0 : 0 < y₁ (0, 0))
    (hyφ0 : yφ (0, 0) ≠ 0) :
    Tendsto (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x yφ) b)
        / twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y₁) b)) atTop
      (𝓝 (yφ (0, 0) / y₁ (0, 0))) :=
  chart_posterior_tendsto_const β b p ρ h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ x yφ y₁ hx hyφ hy₁
    hy₁0 hyφ0

/-- **`1/log N` decay** of the posterior expectation of an observable vanishing at the corner
(with nonzero constant coefficient `B^φ_p`). -/
theorem headline_posterior_log_decay (β b p ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (x yφ y₁ : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hyφ : WSummable ρ yφ) (hy₁ : WSummable ρ y₁) (hy₁0 : 0 < y₁ (0, 0))
    (hyφ0 : yφ (0, 0) = 0)
    (hB : canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x yφ) b) (anaFaceV (ampCoeff β x yφ) b)
      (fun i j s => ampCoeff β x yφ (i, j) s) p ≠ 0) :
    Tendsto (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x yφ) b)
        / twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y₁) b) * Real.log N) atTop
      (𝓝 (canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x yφ) b) (anaFaceV (ampCoeff β x yφ) b)
          (fun i j s => ampCoeff β x yφ (i, j) s) p
        / canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y₁ (i, j) s) p)) :=
  chart_posterior_tendsto_log β b p ρ h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ x yφ y₁ hx hyφ hy₁
    hy₁0 hyφ0 hB

end Laplace.Grammar
