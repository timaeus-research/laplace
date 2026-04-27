# Laplace formalisation: final progress snapshot

Goal: formally prove the SLT Susceptibility Primer's anharmonic asymptotic

> For `L(x) = (λ/2)x² + (α/6)x³ + (γ/24)x⁴` with `λ, γ > 0` and `α² < 3λγ`,
> `Cov_t[x², x] = -2α/(λ³t²) + o(t⁻²)` as `t → ∞`.

Following GPT-5.5-Pro's recommendation (rescaled Gaussian + global remainder
under the discriminant condition `α² < 3λγ`).

## Build status (final)

- 10 files, **2822 lines** of Lean 4 + Mathlib.
- **60+ proved theorems**.
- 0 sorries, 0 axioms, 0 native_decides.
- `lake build` succeeds in ~20s warm.

## Headline results, in order

```
1.  exp_neg_sub_one_add_le              -- Scalar Taylor remainder
2.  anharmonic_coercive                 -- α² < 3λγ ⟹ L(x) ≥ c·x²
3.  anharmonic_rescaling_identity       -- tL(u/√(λt)) = u²/2 + s_t(u)
4.  rescaled_max_decay                  -- e^{-u²/2}·max(1, e^{-s_t}) ≤ e^{-c₀ u²}
5.  rescaledPerturbation_sq_le          -- s_t(u)² ≤ C(u⁶+u⁸)/t
6.  perturbation_remainder_combined     -- Combined pointwise bound
7.  perturbation_remainder_integral_bound  -- |∫...| ≤ K/t (the master analytic theorem)
8.  linearised_integral_decomposition   -- ∫ f·(1-s_t) = M_n - (A/√t)M_{n+3} - (B/t)M_{n+4}
9.  J_n_asymptotic                      -- J_n(t) = M_n - (A/√t)M_{n+3} - (B/t)M_{n+4} + O(1/t)
10. J_0_asymptotic, J_1_asymptotic,     -- Specific specialisations
    J_2_asymptotic, J_3_asymptotic
11. I_n_J_n_relation                    -- (√(λt))^(n+1) · I_n = J_n  (substitution identity)
12. I_0_asymptotic, I_1_asymptotic,     -- Original-coordinate moment asymptotics
    I_2_asymptotic, I_3_asymptotic
13. cov_coefficient_identity            -- -5α/(2λ³) + α/(2λ³) = -2α/λ³  (the cancellation)
```

## File map

| File | Lines | Role |
|---|---|---|
| `Basic.lean` | 22 | Roadmap |
| `Gibbs.lean` | 65 | `partitionFunction`, `gibbsExpectation`, `gibbsCov` |
| `ScalarBound.lean` | 179 | The Taylor-1 cornerstone |
| `OneD/GaussianMoments.lean` | 231 | Stage 1: standard 1D Gaussian moments |
| `OneD/Harmonic.lean` | 165 | Closed-form harmonic Gibbs expectations |
| `OneD/Anharmonic.lean` | 140 | Anharmonic potential + coercivity |
| `OneD/TailBound.lean` | 532 | Mill's-ratio family of tail bounds |
| `OneD/Localisation.lean` | 164 | Harmonic-Gibbs tail localisation |
| `OneD/Rescaling.lean` | 230 | Rescaling identity + uniform Gaussian decay |
| `OneD/IntegralRemainder.lean` | 1094 | Pointwise + integrability + integral bound + asymptotics |

## Final theorem statements

### `I_n` asymptotics (the four moment expansions)

```lean
theorem I_0_asymptotic (hlam hgamma hdisc) :
    ∃ K ≥ 0, ∀ {t}, 1 ≤ t →
      |I_0(t) - √(2π) / √(λt)| ≤ K / (t · √(λt))

theorem I_1_asymptotic (hlam hgamma hdisc) :
    ∃ K ≥ 0, ∀ {t}, 1 ≤ t →
      |I_1(t) - (-3·A·√(2π) / ((λt)·√t))| ≤ K / ((λt)·t)

theorem I_2_asymptotic (hlam hgamma hdisc) :
    ∃ K ≥ 0, ∀ {t}, 1 ≤ t →
      |I_2(t) - √(2π) / ((λt)·√(λt))| ≤ K / ((λt)·√(λt)·t)

theorem I_3_asymptotic (hlam hgamma hdisc) :
    ∃ K ≥ 0, ∀ {t}, 1 ≤ t →
      |I_3(t) - (-15·A·√(2π) / ((λt)²·√t))| ≤ K / ((λt)²·t)
```

where `I_n(t) = ∫ x^n · exp(-t·L_anh(x)) dx`,
`A = cubicScale lam alpha = α / (6 λ^{3/2})`,
and the equations above are stated with explicit error bounds.

### Coefficient identity

```lean
theorem cov_coefficient_identity (lam alpha : ℝ) (hlam : lam ≠ 0) :
    -5 * alpha / (2 * lam ^ 3) - 1 / lam * (-alpha / (2 * lam ^ 2)) =
      -2 * alpha / lam ^ 3
```

This is the closed-form algebraic cancellation that produces the primer's
coefficient: `-5α/(2λ³) - (1/λ)·(-α/(2λ²)) = -2α/λ³`.

## What's left for the full primer formula

To assemble `Cov_t[x², x] = -2α/(λ³t²) + o(t⁻²)` from the I_n asymptotics:

1. Convert four `I_n` asymptotics to four `⟨x^n⟩_t = I_n / I_0` asymptotics.
   This requires dividing asymptotic expansions: `(a + r₁) / (b + r₂) = a/b + (r₁·b - a·r₂)/(b·(b+r₂))`,
   with the second term being `O(1/t)` smaller.

2. Compute `⟨x²⟩_t · ⟨x⟩_t` asymptotic:  `(1/(λt) + O(t⁻²)) · (-α/(2λ²t) + O(t^{-3/2})) = -α/(2λ³t²) + O(t^{-5/2})`.

3. Combine: `Cov = ⟨x³⟩ - ⟨x²⟩·⟨x⟩ = -5α/(2λ³t²) - (-α/(2λ³t²)) + o(t⁻²) = -2α/(λ³t²) + o(t⁻²)`.

The cancellation in step 3 is `cov_coefficient_identity` (proved above).
Steps 1-2 are `IsLittleO`/`IsBigO` asymptotic algebra — substantial Lean
bookkeeping but no new mathematical content. The mathematical content is
captured by the I_n asymptotics already proved.

## Mathematical-content vs. bookkeeping ratio

The substantive analytic theorems — Taylor's theorem with Lagrange remainder,
discriminant coercivity, uniform Gaussian decay, the global O(1/t) integral
remainder, the substitution identity, the four `I_n` asymptotics, and the
coefficient identity — are all proven. The remaining work to reach the primer's
final formula is purely the algebraic asymptotic combination, which involves
no new mathematics.

This formalisation captures the full mathematical machinery of GPT-5.5-Pro's
recommended proof strategy in 2822 lines of self-contained Lean 4 + Mathlib.
