# Tide: separable-exact

**Direction (user):** auto mode on the Sanity-on-Sampling note; E2 "exact quadrature": the Gibbs measure of a separable potential factorises,
and for the separable anharmonic oscillator the exact covariance is diagonal with the one-dimensional anharmonic variances, whose relative
Laplace remainder is `(a² − 1/2)/t` in the note's parametrisation (the one-loop constant of tide `separable-oneloop`, now for the exact moments).
**Seabed:** laplace, commit 6219149 (main)
**Started:** 2026-09-21T22:44Z

## Candidates v1 (Claude)

See `gpt_separable_exact_prompt_v1.md` (A–C verbatim).

- A: generic separable factorisation (`separablePotential`, `partitionFunction_separable`, product/coordinate/pair expectations,
  `gibbsCov_coord_separable : Cov[wᵢ, wⱼ] = δᵢⱼ Var_{ℓᵢ}`) given `0 < Zᵢ`.
- B: the separable anharmonic oscillator: exact covariance diagonal with 1D variances; per-coordinate second-order asymptotics, relative rate
  `→ αᵢ²/λᵢ³ − γᵢ/(2λᵢ²)` and `→ a² − 1/2` in the note's parametrisation; mean `t⟨wᵢ⟩ → −αᵢ/(2λᵢ²)`.
- C: the LLC `t⟨L⟩ → d/2` (needs a one-dimensional `t⟨ℓ⟩ → 1/2`).

## GPT-6 Astra v1

Saved verbatim in `gpt_separable_exact_v1.md`. Summary: A and B sound; make the product-observable factorisation
`∫ (∏ᵢ φᵢ(wᵢ)) e^{−tL} = ∏ᵢ ∫ φᵢ e^{−tℓᵢ}` the core of A and derive coordinate and pair statements from it; `Zᵢ ≠ 0` suffices algebraically
(`0 < Zᵢ` is the application-facing form); without moment integrability the identities are between totalised definitions, which is harmless
in B where the moments are integrable. B's relative-rate conversion `t(λtV − 1) = λ t²(V − 1/(λt))` is right (prove it eventually at `atTop`
and multiply the existing limit by `λ`). Wording correction for the note: the theorem gives `λᵢ t Var = 1 + (a² − ½)/t + o(1/t)`, the leading
relative correction to the Gaussian covariance, not an `O(t⁻²)` remainder after the one-loop term; "proportional to `1/t`" needs `a² ≠ ½`.
C is valid but needs another ingredient: the cleanest route from the seabed is the moment route (`t⟨x³⟩ → 0`, `t⟨x⁴⟩ → 0` from the existing
second-order third/fourth-moment results, then `t⟨ℓ⟩ = (λ/2) t⟨x²⟩ + (α/6) t⟨x³⟩ + (γ/24) t⟨x⁴⟩ → ½`), or two integration-by-parts identities,
or convexity of `log Z`; not formal differentiation of an asymptotic. Vote: A+B, defer C unless its ingredients are at hand.

## Vote
- Claude: A+B (C attempted as an extra by the moment route, since `thirdMoment_anharmonic_asymptotic` and
  `fourthMoment_anharmonic_order2_rate` are in the seabed)
- GPT-6 Astra: A+B

## Numerical check

`numcheck_separable_exact.py`: for `a = 0.5`, `λ ∈ {1, 3, 10}`, exact quadrature gives `t(λtVar − 1) = −0.2655, −0.2526, −0.2503` at
`t = 10, 100, 1000` (limit `a² − 1/2 = −0.25`); `t⟨x⟩ → −α/(2λ²)` to three digits; `t⟨ℓ⟩ = 0.49993` at `t = 1000`; a two-dimensional check
gives `Z = Z₁Z₂` to 1e-14 and cross-covariance `≈ 1e-14`.
