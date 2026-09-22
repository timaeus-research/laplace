You are consulted (one round) on tide 86 of an automated Lean 4 + Mathlib formalisation loop extending the `laplace` seabed
(Laplace asymptotics for Gibbs expectations, susceptibility-primer / "Sanity on Sampling" note). Zero sorry/axiom discipline. Fixed
parameters, eventual remainders. Your tide-85 consult named the second-order energy variance (a stretch) and the correctly normalised
derivative discrepancy as next targets; both need second-order fifth/sixth localised moments, which are not landed. Instead this tide
goes one derivative further at *leading* order: the third cumulant of the localised energy, which needs only the *signed* seventh moment
at leading order — reachable from the landed localised Stein recursion.

## Candidates v1 (Claude)

Setting (E2, as in tides 68–85): the exact localised measure, frame coordinates `uᵢ`, `ℓᵢ = anharmonicPotential (λᵢ, αᵢ, γᵢ)`,
`aᵢ = g u₀ᵢ`. Landed (tide 85): `∂ₜ⟨L∘A⟩_loc = −Var_loc(L∘A)` exactly, `Var_loc(L∘A) = ∑ᵢ Var_loc,ᵢ(ℓᵢ)`, `t²Var_loc(ℓ) → ½`,
`t²⟨ℓ²⟩_loc → 3/4`; the localised Stein recursion `(tλ + g)m_{k+1} + (tα/2)m_{k+2} + (tγ/6)m_{k+3} = k m_{k−1} + a m_k` (tide 77);
the leading localised moments `t²m₃ → c₃ = −5α/(2λ³) + 3a/λ²` (`locThirdCoeff`), `t²m₄ → 3/λ²`, `t³m₅ → c₅ = −35α/(2λ⁴) + 15a/λ³`
(`locFifthCoeff`), `t³m₆ → 15/λ³`, all with `O(1/t)` remainders; even envelopes through degree 8 (tide 85's template).

**A. The signed localised seventh moment is `O(t⁻⁴)`.** From the Stein recursion at `k = 4`,
`t⁴m₇ = (6/γ)[4t(t²m₃ − c₃) + a t(t²m₄ − 3/λ²) − λt(t³m₅ − c₅) − g(t³m₅) − (α/2)t(t³m₆ − 15/λ³)]` because the `O(t)` terms cancel exactly:
`4c₃ + 3a/λ² − λc₅ − (α/2)(15/λ³) = 0` (Stein consistency of the leading coefficients), hence `|t⁴⟨x⁷⟩_loc| ≤ K` eventually. Plus the
localised even envelopes of degrees 10 and 12 (`|t⁵⟨x¹⁰⟩_loc|`, `|t⁶⟨x¹²⟩_loc|` bounded, or the weaker `t⁴`-scaled versions) and the odd
envelopes 9, 11 via `|x|⁹ ≤ (x⁸ + x¹⁰)/2`, `|x|¹¹ ≤ (x¹⁰ + x¹²)/2`. (The unlocalised `seventhMoment_bound : |t⁴m₇| ≤ K` is landed;
this is its localised analogue, obtained from the recursion rather than an expansion.)

**B. The localised energy's third moment and third cumulant at leading order.**
`ℓ³ = (λ/2)³x⁶ + (λ²α/8)x⁷ + (λ²γ/32 + λα²/24)x⁸ + (λαγ/48 + α³/216)x⁹ + (λγ²/384 + α²γ/288)x¹⁰ + (αγ²/1152)x¹¹ + (γ/24)³x¹²`, so
`|t³⟨ℓ³⟩_loc − 15/8| ≤ K/t` (the `x⁶` term gives `(λ³/8)(15/λ³)`; `x⁷` needs A's signed bound; `x⁸…x¹²` the envelopes), and with tide 85's
`⟨ℓ²⟩`, `⟨ℓ⟩` rates: **`|t³ κ₃,loc(ℓ) − 1| ≤ K/t`**, `κ₃ = ⟨ℓ³⟩ − 3⟨ℓ²⟩⟨ℓ⟩ + 2⟨ℓ⟩³` (`15/8 − 3·(3/4)(1/2) + 2/8 = 1`): the third cumulant of a
`Gamma(½, t)` energy, unchanged at leading order by the localiser and the anchor.

**C. The second temperature derivative of the localised energy on E2 (the headline).** Exactly, on the frame family,
`∂ₜ⟨ℓᵢ(uᵢ)²⟩_loc = −Cov_loc[L∘A, ℓᵢ²] = −Cov_1D,ᵢ[ℓᵢ, ℓᵢ²]` and `∂ₜ⟨ℓᵢ⟩_loc = −Cov_1D,ᵢ[ℓᵢ, ℓᵢ]` (tide 77's derivative identity with
two-coordinate integrability, coordinate independence), so `∂ₜ Var_loc,ᵢ(ℓᵢ) = −κ₃,loc,ᵢ(ℓᵢ)` and, with tide 85's exact splitting,
**`∂ₜ² ⟨L∘A⟩_loc = −∂ₜ Var_loc(L∘A) = ∑ᵢ κ₃,loc,ᵢ(ℓᵢ)`** exactly; therefore **`|t³ ∂ₜ²⟨L∘A⟩_loc − d| ≤ K/t`**: the LLC `d/2` governs the
second temperature derivative too (`∂ₜ²⟨L⟩ = 2·(d/2)/t³`, the `Gamma(d/2, t)` law's third cumulant `2k/t³`). Together with tide 85:
`t⟨L⟩ → d/2`, `−t²∂ₜ⟨L⟩ → d/2`, `t³∂ₜ²⟨L⟩ → d` — the first three temperature derivatives of the localised free-energy-like quantity
are governed by the one number `d/2`.

**D (optional).** The direct multi-d third cumulant `⟨(L∘A)³⟩ − 3⟨(L∘A)²⟩⟨L∘A⟩ + 2⟨L∘A⟩³ = ∑ᵢ κ₃,ᵢ` (cumulant additivity over the product
measure) — needs triple-coordinate integrability; defer unless cheap.

Sizing: A ~150 lines (recursion algebra + consistency identity + envelopes), B ~200 (`⟨ℓ³⟩` expansion: 7 monomials, assembly, cumulant
algebra), C ~250 (two derivative identities per coordinate with integrability, independence reductions, the second derivative via
`deriv` of `deriv`, the sum). Target A + B + C.

## Numerical check (done; two frame coordinates, λ = (1.3, .9), α = (.7, −.4), γ = (1.1, .8), g = .8, u₀ = (.55, −.35); 2D quadrature for
the direct cumulant at t = 40)
coord 0: t^2 m3 -> -0.012378, -0.013918   t^3 m5 -> -1.254915, -1.269858   t^4 m7 = -12.31960, -12.90398, -13.20706, -13.36140
   Stein leading consistency 4c3 + 3a/lam^2 - lam c5 - (alpha/2)(15/lam^3) = -0.01342 (-> 0)
coord 1: t^2 m3 -> 0.323834, 0.329230   t^3 m5 -> 4.768851, 4.837733   t^4 m7 = 54.33769, 57.96248, 59.88340, 60.87234
   Stein leading consistency 4c3 + 3a/lam^2 - lam c5 - (alpha/2)(15/lam^3) = 0.04115 (-> 0)
t=   80: t^3<ell^3>_loc = 1.82573, 1.80071 (->1.875)   t^3 kappa3 = 0.97376, 0.96045 (->1)   sum t^3 kappa3 = 1.93422 (->2)
t=  160: t^3<ell^3>_loc = 1.85006, 1.83718 (->1.875)   t^3 kappa3 = 0.98671, 0.97985 (->1)   sum t^3 kappa3 = 1.96655 (->2)
t=  320: t^3<ell^3>_loc = 1.86245, 1.85592 (->1.875)   t^3 kappa3 = 0.99331, 0.98983 (->1)   sum t^3 kappa3 = 1.98314 (->2)
t=  640: t^3<ell^3>_loc = 1.86870, 1.86542 (->1.875)   t^3 kappa3 = 0.99664, 0.99489 (->1)   sum t^3 kappa3 = 1.99153 (->2)
(c) t=40.0: -dVar/dt = 2.926074153e-05   sum kappa3_i = 2.926068545e-05   direct kappa3(L) (2D) = 2.926068545e-05   d2<L>/dt2 = 2.926071349e-05
(d) t=   80: t^3 d2<L>/dt2 = 1.93422 (-> 2)
(d) t=  160: t^3 d2<L>/dt2 = 1.96656 (-> 2)
(d) t=  320: t^3 d2<L>/dt2 = 1.98314 (-> 2)
(d) t=  640: t^3 d2<L>/dt2 = 1.99154 (-> 2)
(A: `t⁴m₇` converges to a constant per coordinate and the leading Stein consistency tends to 0 (its finite-`t` value is the `O(1/t)` error of
the finite-`t` moment estimates); B: `t³κ₃ → 1` per coordinate; C: `−∂ₜVar = ∑κ₃ᵢ = κ₃(L) = ∂ₜ²⟨L⟩` to 6 digits and `t³∂ₜ²⟨L⟩ → 2 = d`.)

## Questions
1. Are A, B, C correct? Check the Stein consistency identity `4c₃ + 3a/λ² − λc₅ − (α/2)(15/λ³) = 0` with `c₃ = −5α/(2λ³) + 3a/λ²`,
   `c₅ = −35α/(2λ⁴) + 15a/λ³` (we get `−10α/λ³ + 12a/λ² + 35α/(2λ³) − 15a/λ² − 15α/(2λ³) = −3a/λ²`?? — please recompute carefully: is the
   anchor term of the recursion `a·m_k` with `k = 4` contributing `a·(3/λ²)` at leading order, and does the identity then close, or is a
   coefficient in `locFifthCoeff` (`15a/λ³`) inconsistent with it?). Check the `ℓ³` expansion coefficients and the leading value
   `15/8 − 9/8 + 2/8 = 1`.
2. Is the exact chain in C right: `∂ₜVar_loc,ᵢ(ℓᵢ) = −Cov_1D[ℓ, ℓ²] + 2⟨ℓ⟩Cov_1D[ℓ, ℓ] = −κ₃`? Any hidden hypothesis (differentiability of
   the variance as a function of `t`; the second derivative `deriv (deriv f) t` needs `deriv f = −Var` on a neighbourhood — we have it on
   `(0, ∞)`)?
3. Wording against the note (E3; the LLC `λ = d/2`): "the same LLC governs the first three temperature derivatives of the localised
   energy: `t⟨L⟩ → d/2`, `−t²∂ₜ⟨L⟩ = t²Var(L) → d/2`, `t³∂ₜ²⟨L⟩ = t³κ₃(L) → d`, the moments of a `Gamma(d/2, t)` law" — right, and worth
   stating as the Gamma-law reading of the LLC?
4. Lean route: for A, algebra on the recursion (`stein_loc_recursion hg ht 4`) with the landed rates; for B, the `locSixth_bound` template
   for degrees 10 and 12 and neighbour envelopes for 9 and 11; for C, the frame-family derivative identity `hasDerivAt_localised_separable`
   with probes `ℓᵢ(uᵢ)` and `ℓᵢ(uᵢ)²` (two-coordinate integrability via `integrable_coord_pow_mul_separableAnharmonic`) and the
   coordinate-independence lemma `gibbsCov_coord_fun_separable`. Pitfalls? Better or additional candidates, and the best next target?
Vote: which bundle (A, A+B, A+B+C, A+B+C+D) should this tide commit to? Be concrete and terse; flag any error explicitly.
