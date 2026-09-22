# Tide: localised-derivative

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about
retrospectives"); the exact identities on the localised measure: `d/dt⟨ψ⟩_loc = −Cov_loc[L, ψ]` (E2) and the localised Stein identity (1D).
**Seabed:** laplace, commit bfac237 (worktree `laplace-tide-localised-derivative`, branch `tide/localised-derivative` off `main`)
**Started:** 2026-09-22T17:44Z

## Candidates v1 (Claude)

Setting as in tides 65–76: the 1D anharmonic oscillator `ℓ` with E3's isotropic localiser (`g ≥ 0`, anchor `x₀`, `a = g x₀`,
`φ = e^{ax − (g/2)x²}`, localised measure `∝ e^{−tℓ}φ`, `⟨·⟩_loc`), and E2's rotated separable oscillator with the isotropic localiser
(`Φ(w) = e^{−(g/2)|w − w₀|²}`, localised potential `L∘A + (g/(2t))|w − w₀|²`, so `e^{−t·(localised potential)} = e^{−t L∘A}·Φ` with `Φ`
`t`-independent). Two *exact* identities on the localised measure, the localised analogues of tides 61–64 (the derivative reading of
eq:covK) and 70 (the Stein identity):

### A. `d/dt ⟨ψ⟩_loc = −Cov_loc[L∘A, ψ]` on E2 (exact)

For the centred quadratic probe `ψ(w) = ½(w − c)ᵀB(w − c) + bᵀ(w − c)`:
`HasDerivAt (fun s => ⟨ψ⟩_loc(s)) (−Cov_loc,t[L∘A, ψ]) t` for `t > 0`, where `⟨ψ⟩_loc(s) = gibbsExpectation (localisedRotatedAnharmonic … s) s ψ`
and `Cov_loc,t[L∘A, ψ] = gibbsCov (localisedRotatedAnharmonic … t) t (rotatedAnharmonic …) ψ` (tide 76's object). Hence
`Cov_loc[L∘A, ψ] = −deriv ⟨ψ⟩_loc` (`localisedCovK_eq_neg_deriv`), and likewise for the coordinates `uᵢ`, `uᵢuⱼ`.
Route: `⟨ψ⟩_loc(s) = ⟨ψΦ⟩_s/⟨Φ⟩_s` (a ratio of *fixed-potential* Gibbs expectations, `Φ` `t`-independent — the multi-d analogue of
`gibbsExpectation_locPotential1`), the seabed's `hasDerivAt_gibbsExpectation_of_integrable` (continuous `L ≥ 0`, observables `ψΦ`, `Φ`;
integrability from the unlocalised one by `|Φ| ≤ 1`), the quotient rule, and the algebra
`(−Cov[L, ψΦ]⟨Φ⟩ + ⟨ψΦ⟩Cov[L, Φ])/⟨Φ⟩² = −(⟨LψΦ⟩/⟨Φ⟩ − (⟨LΦ⟩/⟨Φ⟩)(⟨ψΦ⟩/⟨Φ⟩)) = −Cov_loc[L, ψ]`; done in the separable frame and
transported by `gibbsExpectation/gibbsCov_rotated_of_continuous` (as `hasDerivAt_gibbsExpectation_rotatedAnharmonic_probe` does).
Reading: the exact localised eq:covK *is* `−∂ₜ` of the exact localised eq:mean/eq:cov, including the anchor term — the exact-measure
counterpart of tide 63 (§68), and the structural reason behind tide 76's leading constant (`−∂ₜ(a/(tλ + g)) → a/λ`).

### B. The localised Stein identity and its moment recursion (1D, exact)

`⟨f'⟩_loc = ⟨f·(tℓ' + gx − a)⟩_loc` for `f = x^k` (`stein_loc_pow`), from tide 70's `stein_anharmonic` applied to `g := x^kφ`
(`(x^kφ)' = (kx^{k−1} + x^k(a − gx))φ`) and division by `⟨φ⟩`; hence the recursion (`stein_loc_recursion`, GPT's form)
`(tλ + g)m_{k+1} + (tα/2)m_{k+2} + (tγ/6)m_{k+3} = k m_{k−1} + a m_k`, `m_j = ⟨x^j⟩_loc`, and at `k = 0`:
`(tλ + g)m₁ + (tα/2)m₂ + (tγ/6)m₃ = a` (`stein_loc_zero`) — the exact localised mean equation (consistent with `t m₁ → a/λ − α/(2λ²)`).
Infrastructure for the deferred second-order localised eq:covK (tide 76's D).

### C. Consistency corollaries (cheap)

`stein_loc_zero` rearranged: `m₁ = (a − (tα/2)m₂ − (tγ/6)m₃)/(tλ + g)` — the exact localised mean as a function of the higher localised
moments, whose leading order reproduces tide 67's `c` and whose displayed truncation is `P_t`'s anchor term `a/(tλ + g)`. (Remark only.)

Proposed bundle: A + B (C as remark). Line estimate ~550 (A ~350 incl. the multi-d ratio identity and the rotation transport; B ~200).

Numerical check (`numcheck_localised_derivative.py`, 1D quadrature, `λ = 1.3, α = 0.7, γ = 1.1, g = 0.8, x₀ = 0.6`): central differences of
`⟨ψ⟩_loc(t)` vs `−Cov_loc[ℓ, ψ]` for `ψ = x, x², 0.35x² − 0.3x` at `t = 5, 20, 80` agree to `10⁻⁸`–`10⁻¹¹` (finite-difference error); the
recursion at `k = 0` checked to quadrature precision.

## Numerical check

`numcheck_localised_derivative.py`: `d/dt⟨ψ⟩_loc` (central differences) vs `−Cov_loc[ℓ, ψ]` — differences `6·10⁻⁹` … `3·10⁻¹¹` for
`ψ = x, x², 0.35x² − 0.3x` at `t = 5, 20, 80`; the identity is exact, the residual is the finite-difference error.

## GPT-6 Astra v1

Verbatim in `gpt_localised_derivative_v1.md` (prompt: `gpt_localised_derivative_prompt_v1.md`). Summary: A and B correct (quotient-rule
signs and cancellation checked; the covariance is with the *unlocalised* `V = L∘A`, not the `t`-dependent potential; the ratio need only
hold eventually near `t > 0`; `D(t) > 0` from `Φ > 0`; `0 < Φ ≤ 1` needs `g ≥ 0`; fixed probe — a varying one adds `⟨∂ₜψₜ⟩_loc`).
Corrections: (i) `−∂ₜ(a/(tλ + g)) = aλ/(tλ + g)² → 0`; it is `t²·(−∂ₜ…) → a/λ` — the *anchor contribution*, not the full mean coefficient;
(ii) `φ = e^{ax − gx²/2} ≤ e^{gx₀²/2}`, not `≤ 1` (only the centred `Φ` is); (iii) a separate `k = 0` statement rather than `m₋₁`
(done: `stein_loc_zero`); (iv) if eq:cov means the *central* covariance, `−∂ₜCov_loc(uᵢ, uⱼ) = Cov_loc[V, (uᵢ − μᵢ)(uⱼ − μⱼ)]`, not
`Cov_loc[V, uᵢuⱼ]` — our statements are for the raw quadratic probe. Route: the fixed-potential ratio route is right; the general
`d/dt⟨ψ⟩_{U_t} = −Cov[ψ, U_t + t∂ₜU_t]` explains it conceptually but is unnecessary infrastructure; discharge integrability in the
separable frame and rotate the anchor too. **Add the exact localised Stein–covariance reduction** (`C_{r,n} = Cov_loc[x^r, xⁿ]`):
Stein on `x^{n+1}` minus `m_n` times Stein on `x` gives `n m_n = t Cov_loc[xℓ', xⁿ] + gC_{2,n} − aC_{1,n}`, and `xℓ' = 2ℓ + (α/6)x³ + (γ/12)x⁴`,
hence `t²Cov_loc[ℓ, xⁿ] = (n/2)t m_n − (α/12)t²C_{3,n} − (γ/24)t²C_{4,n} − (g/2)tC_{2,n} + (a/2)tC_{1,n}` (new terms `−g/2`, `+a/2`; both sides
vanish at `n = 0`); general form with `⟨xf'⟩_loc`. Moment inputs for the `1/t` coefficients at `n = 1, 2`: `m₁, m₂` to `t⁻²`, `m₃` to `t⁻²`
leading, `m₄` to `t⁻³` (the easy-to-miss one), `m₅, m₆` leading at `t⁻³`; then `t²Cov_loc[ℓ, xⁿ] = Aₙ + 2Bₙ/t + o(1/t)` by algebra and
remainder estimates — "B plus the reduction supplies the remainder-safe asymptotic proof" (D stays deferred: `m₄`'s `t⁻³` term is not
in the seabed).

## Vote
- Claude: A + B + the localised Stein–covariance reduction (`stein_loc_cov_reduction`), C as remark
- GPT-6 Astra: "A + B + the exact localised Stein–covariance reduction; C as a remark, with no general `t`-dependent-potential
  derivative theorem this tide"
