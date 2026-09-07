/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MonomialAsymptotic

/-!
# Headline statements, part VI: the equal-ratio normal moment integral in general dimension

Paper-facing wrappers for units 165, 170–175 (the general-`d` equal-ratio monomial milestone).
The paper's *bare normal moment integral* on a stratum with numerical data `(k_i, h_i)_{i ∈ I}` is

  `M(n) = ∫_{[0,b]^{|I|}} ∏ u_i^{h_i} e^{-n ∏ u_i^{2k_i}} du`,

and its asymptotic is governed by the poles of the factored zeta function: the leading exponent is
`λ = min_i (h_i+1)/(2k_i)` with multiplicity the number of coordinates realising it. The wrappers
below cover the **equal-ratio** case (every coordinate realises the minimum), with cutoff `b = 1`,
inverse temperature `β` and `d = m + 1 ≥ 1` coordinates, all of boundary type:

* the exact reduction to the one-dimensional weighted integral with the log density
  `z^{λ-1} (-log z)^m / m!` (`headline_normal_moment_reduction`);
* the asymptotic `M(N) ~ Γ(λ) β^{-λ} / (m! ∏ᵢ 2kᵢ) · N^{-λ} (log N)^m`
  (`headline_normal_moment_asymptotic`, `headline_normal_moment_ratio`);
* the general-`λ` Gamma/log asymptotic itself (`headline_gamma_log_asymptotic`);
* the recursive product density (`headline_product_density`).

NOT claimed: unequal ratios (a proper subset of coordinates realising the minimum), cutoffs
`b ≠ 1`, interior coordinates with parity factors, or the Taylor-expanded smooth factor. Zero
`sorry`/`axiom`.
-/

open Asymptotics Filter MeasureTheory Set Topology

namespace Laplace.Grammar

/-- **Product density**: the pushforward of `∏ tᵢ^{λ-1} dt` on `(0,1]^{m+1}` under the product map
has density `z^{λ-1} (-log z)^m / m!` on `(0,1]`. -/
theorem headline_product_density (l : ℝ) (m : ℕ) (g : ℝ → ENNReal) (hg : Measurable g) :
    weightedBoxIntegral (m + 1) (fun _ => l - 1) g =
      ENNReal.ofReal (1 / (m.factorial : ℝ)) *
        ∫⁻ z in Ioc (0 : ℝ) 1, ENNReal.ofReal (logDensity l m z) * g z := by
  rw [weightedBoxIntegral_const_eq_productIntegral l (m + 1) g hg, productIntegral_succ_eq l m g hg]

/-- **Gamma/log asymptotic**: `∫₀¹ z^{λ-1} (-log z)^m e^{-βNz} dz ~ Γ(λ) β^{-λ} N^{-λ} (log N)^m`. -/
theorem headline_gamma_log_asymptotic (l : ℝ) (m : ℕ) (β : ℝ) (hl : 0 < l) (hβ : 0 < β) :
    (fun N => ∫ z in Ioc (0 : ℝ) 1, z ^ (l - 1) * (-Real.log z) ^ m * Real.exp (-(β * N * z)))
      ~[atTop] fun N => Real.Gamma l * β ^ (-l) * N ^ (-l) * Real.log N ^ m :=
  gammaLogIntegral_isEquivalent l m β hl hβ

/-- **Exact reduction of the equal-ratio normal moment integral** to the one-dimensional weighted
integral: `M(N) = (∏ᵢ 1/(2kᵢ)) (1/m!) ∫₀¹ z^{λ-1} (-log z)^m e^{-βNz} dz`. -/
theorem headline_normal_moment_reduction (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β N : ℝ) (hl : 0 < l) (hratio : ∀ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l)
    (hβN : 0 < β * N) :
    ∫ x in unitBox (m + 1), (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))) =
      (∏ i, 1 / (2 * (k i : ℝ))) * (1 / (m.factorial : ℝ)) *
        ∫ z in Ioc (0 : ℝ) 1, z ^ (l - 1) * (-Real.log z) ^ m * Real.exp (-(β * N * z)) :=
  monomialBoxReal_eq m h k hk l β N hl hratio hβN

/-- **Equal-ratio normal moment asymptotic (ratio form)**. -/
theorem headline_normal_moment_ratio (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β)
    (hratio : ∀ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l) :
    Tendsto (fun N => (∫ x in unitBox (m + 1),
        (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i)))) /
        (N ^ (-l) * Real.log N ^ m)) atTop
      (𝓝 ((∏ i, 1 / (2 * (k i : ℝ))) * (1 / (m.factorial : ℝ)) * (Real.Gamma l * β ^ (-l)))) :=
  monomialBoxReal_tendsto m h k hk l β hl hβ hratio

/-- **Equal-ratio normal moment asymptotic (paper form)**: with `d = m + 1` coordinates all
realising `λ = (hᵢ+1)/(2kᵢ)`,
`M(N) ~ Γ(λ) β^{-λ} / ((d-1)! ∏ᵢ 2kᵢ) · N^{-λ} (log N)^{d-1}`. -/
theorem headline_normal_moment_asymptotic (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β)
    (hratio : ∀ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l) :
    (fun N => ∫ x in unitBox (m + 1),
        (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i)))) ~[atTop]
      fun N => Real.Gamma l * β ^ (-l) / ((m.factorial : ℝ) * ∏ i, 2 * (k i : ℝ)) *
        N ^ (-l) * Real.log N ^ m :=
  monomialBoxReal_isEquivalent' m h k hk l β hl hβ hratio

end Laplace.Grammar
