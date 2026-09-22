You are GPT-6 Astra consulting on a Lean 4 + Mathlib formalisation tide ("laplace" seabed: Laplace asymptotics of Gibbs expectations for
the quartic anharmonic oscillator with the isotropic Gaussian localiser of a research note's E3). The seabed has: the exact derivative
identity `d/ds⟨ψ⟩_s = −Cov_t[L, ψ]` for fixed continuous `L ≥ 0` (`hasDerivAt_gibbsExpectation_of_integrable`, with integrability of
`Lψe^{−(t/2)L}`, `ψe^{−(t/2)L}`, `Le^{−(t/2)L}`, `e^{−(t/2)L}` and `Z ≠ 0`); the 1D Stein identity `⟨g'⟩ = t⟨gℓ'⟩` for differentiable `g` with
`ge^{−tℓ}`, `g'e^{−tℓ}`, `gℓ'e^{−tℓ}` integrable (`stein_anharmonic`); the localised measures as ratios `⟨f⟩_loc = ⟨fφ⟩/⟨φ⟩` (1D) and the
identity `e^{−t·(L + (g/(2t))|w − w₀|²)} = e^{−tL}·e^{−(g/2)|w − w₀|²}`. Below are the candidates. Please answer:

1. Are A and B correct as stated (the quotient-rule algebra, the sign conventions, the Stein form `⟨f'⟩_loc = ⟨f(tℓ' + gx − a)⟩_loc` and
   the recursion `(tλ + g)m_{k+1} + (tα/2)m_{k+2} + (tγ/6)m_{k+3} = k m_{k−1} + a m_k`, the `k = 0` case)? Any hidden hypothesis (the
   `HasDerivAt` of `s ↦ ⟨ψ⟩_loc(s)` uses the ratio representation only for `s > 0`; `Φ` bounded by `1` needs `g ≥ 0`)?
2. Is the route (ratio of fixed-potential expectations + the seabed's derivative lemma + quotient rule, in the separable frame then
   rotated) the cleanest, or should the derivative lemma be generalised to `t`-dependent potentials `U_t` with `d/dt⟨ψ⟩ = −Cov[ψ, U + t∂ₜU]`?
   Pitfalls in Lean (eventual equality near `t`, the division by `⟨Φ⟩_s`)?
3. What do A and B buy for the note's E3? Is the reading "the exact localised eq:covK is exactly `−∂ₜ` of the exact localised
   eq:mean/eq:cov, anchor term included — so §68's displayed identity holds on the exact measure too" fair? With A in hand, does the
   second-order localised eq:covK (tide 76's deferred D: `1/t` coefficients `2c'`, `2c₂'`) become reachable without differentiating
   remainders — e.g. via B's recursion plus the known second-order localised moments, as tide 71's Stein–covariance reduction did
   unlocalised (`t²Cov[ℓ, xⁿ] = (n/2)t⟨xⁿ⟩ − (α/12)t²Cov[x³, xⁿ] − (γ/24)t²Cov[x⁴, xⁿ]`)? Please write the localised analogue of that
   reduction if it exists, and say what moment inputs it would need.
4. Vote: which bundle do you back, and should the localised Stein–covariance reduction be added to this tide?

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
