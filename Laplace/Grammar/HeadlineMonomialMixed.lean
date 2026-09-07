/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MonomialMixedAsymptotic

/-!
# Headline statements, part VII: the normal moment integral with arbitrary exponent ratios

Paper-facing wrappers for units 177–181 (the mixed-ratio general-`d` monomial milestone), stated
directly on the Bochner box integral

  `M(N) = ∫_{(0,1]^{m+1}} ∏ xᵢ^{hᵢ} e^{-βN ∏ xᵢ^{2kᵢ}} dx`

with Mellin ratios `ℓᵢ = (hᵢ+1)/(2kᵢ)`, minimum `λ` and `J = {i : ℓᵢ = λ}`:

* the exact reduction to the weighted integral with exponents `ℓᵢ`
  (`headline_normal_moment_weighted`);
* the dominated-coordinate transfer principle behind the residue factors
  (`headline_dominated_coordinate`);
* the mixed-ratio asymptotic
  `M(N) ~ Γ(λ) β^{-λ}/(|J|-1)! · ∏_{i∈J} 1/(2kᵢ) · ∏_{i∉J} 1/(hᵢ+1-2kᵢλ) · N^{-λ} (log N)^{|J|-1}`
  (`headline_normal_moment_mixed`), and its form at the computed minimum
  (`headline_normal_moment_min`).

Scope: nonempty block of boundary-type coordinates, unit cutoff `b = 1`, `kᵢ > 0`, `β > 0`. This is
the paper's zeta-pole prediction for the bare normal moment integral (exponent = minimal ratio,
logarithmic degree = multiplicity − 1, Laurent coefficient `a_{-|J|}` at `b = 1` times
`Γ(λ)/(|J|-1)!`). NOT claimed: cutoffs `b ≠ 1`, interior coordinates with parity factors, variable
amplitudes, or the full expectation expansion. Zero `sorry`/`axiom`.
-/

open Asymptotics Filter MeasureTheory Set Topology

namespace Laplace.Grammar

/-- **Exact weighted reduction**: `M(N) = ∏ 1/(2kᵢ) · ∫_{(0,1]^d} ∏ tᵢ^{ℓᵢ-1} e^{-βN ∏ tᵢ} dt`. -/
theorem headline_normal_moment_weighted (d : ℕ) (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (β N : ℝ) :
    ∫ x in unitBox d, (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))) =
      (∏ i, 1 / (2 * (k i : ℝ))) *
        (weightedBoxIntegral d (fun i => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1)
          (expKernel β N)).toReal :=
  monomialBoxReal_eq_mixed d h k hk β N

/-- **Dominated-coordinate transfer**: a coordinate with ratio `q > λ` multiplies a power–log
asymptotic by `1/(q-λ)` without changing exponent or logarithmic degree. -/
theorem headline_dominated_coordinate (f : ℝ → ℝ) (l q : ℝ) (r : ℕ) (C B : ℝ) (hl : 0 < l)
    (hq : l < q) (hf : Measurable f) (hB : ∀ M, 0 < M → |f M| ≤ B)
    (hlim : Tendsto (fun M => f M / (M ^ (-l) * Real.log M ^ r)) atTop (𝓝 C)) :
    Tendsto (fun N => (∫ t in Ioc (0 : ℝ) 1, t ^ (q - 1) * f (N * t)) /
        (N ^ (-l) * Real.log N ^ r)) atTop (𝓝 (C / (q - l))) :=
  tendsto_weighted_scale_div f l q r C B hl hq hf hB hlim

/-- **Mixed-ratio normal moment asymptotic**: with `ℓᵢ = (hᵢ+1)/(2kᵢ)`, `λ ≤ ℓᵢ` for all `i` and
`λ = ℓᵢ` for some `i`,
`M(N) ~ Γ(λ) β^{-λ}/(|J|-1)! · ∏_{i∈J} 1/(2kᵢ) · ∏_{i∉J} 1/(hᵢ+1-2kᵢλ) · N^{-λ} (log N)^{|J|-1}`,
where `|J| = ∑ᵢ [ℓᵢ = λ]`. -/
theorem headline_normal_moment_mixed (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β)
    (hmin : ∀ i, l ≤ ((h i : ℝ) + 1) / (2 * (k i : ℝ)))
    (hatt : ∃ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l) :
    (fun N => ∫ x in unitBox (m + 1),
        (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i)))) ~[atTop]
      fun N => (Real.Gamma l * β ^ (-l) /
          (((∑ i, if ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l then 1 else 0) - 1).factorial : ℝ) *
        ∏ i, if ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l then 1 / (2 * (k i : ℝ))
          else 1 / ((h i : ℝ) + 1 - 2 * (k i : ℝ) * l)) *
        N ^ (-l) * Real.log N ^ ((∑ i, if ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l then 1 else 0) - 1) :=
  monomialBoxReal_mixed_isEquivalent m h k hk l β hl hβ hmin hatt

/-- **Normal moment asymptotic at the minimal ratio** `λ = minᵢ (hᵢ+1)/(2kᵢ)`. -/
theorem headline_normal_moment_min (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) :
    (fun N => ∫ x in unitBox (m + 1),
        (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i)))) ~[atTop]
      fun N => monomialMixedConst h k (minRatio h k) β * N ^ (-(minRatio h k)) *
        Real.log N ^ (multCount (ratioExp h k) (minRatio h k) - 1) :=
  monomialBoxReal_minRatio_isEquivalent m h k hk β hβ

end Laplace.Grammar
