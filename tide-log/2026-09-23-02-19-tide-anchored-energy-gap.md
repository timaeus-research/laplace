# Tide: anchored-energy-gap

**Direction (user):** auto mode — "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." / "Continue with what you think best, don't stop". Claude's choice for tide 95: the anchored Gaussian *energy* gap — GPT's suggested corollary of tide 94, done from the landed E2 energy theorem and an independent expansion of the exact anchored Gaussian energy (never by differentiating the fixed-s transform remainder).
**Seabed:** laplace, commit a077f30 (tide 94 landed)
**Started:** 2026-09-23T02:22Z

## Seabed
`tiltedExpectation_quadForm : tiltedExpectation P v (uᵀHu) = ∑ᵢⱼ Hᵢⱼ(P⁻¹)ᵢⱼ + mᵀHm` (`m = P⁻¹v`); E3's `localised_llc` (tilt `γ•w₀`);
`localised_llc_matrix_eq_eigen : ½∑ᵢⱼ(tH)ᵢⱼ((tH+γI)⁻¹)ᵢⱼ = localisedLLC = ½∑ᵢ tλᵢ/(tλᵢ+γ)`; tide 94's `inv_localisedPrecision_eq_conj`
(`(tH+gI)⁻¹ = U diag(1/(tλᵢ+g)) Uᵀ`), `tiltMean_dot_localised`, `inv_shift_rate` (`|1/(u+g) − 1/u| ≤ g/u²`), `energyLocCoeff1_anchored`
(`e₁ + g/(2λ) − a²/(2λ) = e₀ − aα/(2λ²)`); the E2 energy expansion `localisedRotatedAnharmonic_llc_order2_rate`:
`|t⟨L∘A⟩_loc − d/2 − (∑ᵢe₁ᵢ)/t| ≤ K/t²` (tide 73); tide 85/87's `C₁ = ∑(e₁ᵢ + g/(2λᵢ))` energy gap against the *centred* prediction
`P = ½tr(H(tH+gI)⁻¹)`.

## Candidates v1 (Claude)

**A (Sampler, exact eigen form of the anchored Gaussian energy).** `tiltMean_quadForm_localised`: `mᵀHm = ∑ᵢ λᵢ(Uᵀv)ᵢ²/(tλᵢ+g)²` for
`m = (tH+gI)⁻¹v` (from `inv_localisedPrecision_eq_conj`, `UᵀHU = diag λ`, and `vᵀMv = (Uᵀv)ᵀ(UᵀMU)(Uᵀv)`); hence
**`𝓔^{anch}_t := t·tiltedExpectation (tH+gI) v (½uᵀHu) = ½∑ᵢ tλᵢ/(tλᵢ+g) + (t/2)∑ᵢ λᵢaᵢ²/(tλᵢ+g)²`** (`anchoredGaussianEnergy_eq`) — E3's
localised LLC prediction plus the anchor's mean-energy term.

**B (Multi, expansion in the E2 frame).** **`|𝓔^{anch}_t − d/2 − (A − G)/t| ≤ K/t²`**: per direction `tλ/(tλ+g) = 1 − g/(tλ+g)` with
`|g/(tλ+g) − g/(tλ)| ≤ g²/(λ²t²)` (`inv_shift_rate`), and `tλa²/(tλ+g)² − a²/(λt) = −a²g(2tλ+g)/(λt(tλ+g)²)`, `|·| ≤ a²g(2/λ² + g/λ³)/t²` for
`t ≥ 1`; summed with `Finset.abs_sum_le_sum_abs`.

**C (Multi, the gap).** With `localisedRotatedAnharmonic_llc_order2_rate`: **`|t⟨L∘A⟩_loc − 𝓔^{anch}_t − C₁′/t| ≤ K/t²`**,
`C₁′ = ∑ᵢ(e₁ᵢ + g/(2λᵢ) − aᵢ²/(2λᵢ)) = ∑ᵢ(e₀ᵢ − aᵢαᵢ/(2λᵢ²))` (`energyLocCoeff1_anchored`) — the same coefficient as the transform gap
(tide 94): "two gaps, one anharmonic coefficient"; against the centred prediction the energy gap is `C₁/t` (tides 85/87), so the anchor's
mean-energy term accounts for exactly `∑aᵢ²/(2λᵢ)` of it. Note `−∂ₛ|₀` of tide 94's transform gap `−sC₁′/((1+s)^{d/2+1}t)` is `C₁′/t` — a
consistency check with C, not a derivation.

**D (optional).** The variance gap: the anchored Gaussian variance of `t·½uᵀHu` is `½∑ᵢ(tλᵢ/(tλᵢ+g))² + t²∑ᵢλᵢ²aᵢ²/(tλᵢ+g)³` (Gaussian
quadratic-form variance with mean) — requires a fourth-moment/Wick identity for the tilted Gaussian which is *not* landed; we would
*not* attempt it this tide (mention only).

## Numerical check (scipy quad, λ = (1.3, 0.9), α = (0.7, −0.4), γ = (1.1, 0.8), g = 0.8, u₀ = (0.55, −0.35); `C₁′ = −0.27289`,
`A − G = −0.63412`)
`t(𝓔^{anch} − d/2)` → −0.62391, −0.62897, −0.63153, −0.63282, −0.63347 (t = 40 … 640) vs −0.63412; `t(t⟨L⟩ − 𝓔^{anch})` → −0.25337, −0.26294,
−0.26787, −0.27037, −0.27162 vs `C₁′ = −0.27289`; the `t²`-remainder converges (0.78 → 0.81).

## Questions put to GPT-6 Astra
1. Are A–C correct (the eigen form of `mᵀHm`, the expansion `𝓔^{anch} = d/2 + (A − G)/t + O(t⁻²)`, the gap coefficient `C₁′`, the per-term
   bound `|tλa²/(tλ+g)² − a²/(λt)| ≤ a²g(2/λ² + g/λ³)/t²` for `t ≥ 1`)?
2. Bundle/route: is there a slicker route to B than the two per-term rational bounds (e.g. `tλ/(tλ+g)·(1 − g/(tλ+g))` structure, or
   reuse of tide 94's `inv_shift_rate` for both terms)? Should the Sampler statement be for general `v` with the E2 specialisation
   `(Uᵀv)ᵢ = g u₀ᵢ` as prose, as in tide 94?
3. Anything missed close to this seabed: is the "two gaps, one coefficient" statement worth a packaging theorem (a conjunction), or a
   named definition `anchoredGapCoeff := ∑(e₀ᵢ − aᵢαᵢ/(2λᵢ²))` used in both tide 94 and this tide (we avoid competing definitions per your
   earlier advice)? Is the variance gap `2C₁′/t³` (D) reachable from landed material (tide 87's `localisedVar_energy_order2` gives the exact
   side; the Gaussian side needs Wick)?
4. Wording against E3 ("the LLC shrinks as ½ t tr(H(tH+γI)⁻¹)"): "the anchored Gaussian LLC prediction `½∑tλᵢ/(tλᵢ+g) + (t/2)mᵀHm`
   misses the exact localised LLC by `C₁′/t`, a purely anharmonic coefficient; the centred prediction misses by `C₁/t = (C₁′ + ∑aᵢ²/(2λᵢ))/t`"
   — fair? Qualifications (fixed `g, u₀`; the anchored prediction is E3's `tiltedExpectation (tH+γI) (γw₀)` object; `d = 0`)?
Vote for one bundle at the end.

(The numerical check script is `numcheck_anchored_energy_gap.py` in this directory; full output in the tide's SRI note.)

## GPT-6 Astra v1 (summary; verbatim in `gpt_anchored_energy_gap_v1.md`)

- A–C correct under `H ≻ 0`, `U` orthogonal, `g ≥ 0`, `t > 0`, `v` fixed, `a = Uᵀv`. Recommends proving the coordinate identity `Uᵀm = (aᵢ/(tλᵢ+g))ᵢ` first rather than a general quadratic-form conjugation lemma.
- B: a sharper bound valid for all `t > 0`, via reciprocal factorisation `x a² q² − a² r = x a² (q−r)(q+r)` with `q = 1/(x+g)`, `r = 1/x`: `|tλa²/(tλ+g)² − a²/(λt)| ≤ 2a²g/(λ²t²)`, so `K_anch = ∑(g²/2 + aᵢ²g)/λᵢ²` and no `g/λ³` term. (We keep the `t ≥ 1` route with `inv_sq_shift_rate` since the E2 theorem already has `T ≥ 1`; the sharper constant is noted as a follow-up.)
- C: `C₁′ = ∑(e₁ᵢ + g/(2λᵢ) − aᵢ²/(2λᵢ)) = ∑(e₀ᵢ − aᵢαᵢ/(2λᵢ²))`, sign agrees with tide 94; remainder constant = sum of the two constants.
- Packaging: one canonical coefficient (reuse tide 94's inline sum, no parallel "transform"/"energy" definitions), two separately usable rate theorems; a conjunction theorem is optional and adds little.
- Variance gap `2C₁′/t³` is correct but not an immediate consequence of landed material (needs a Gaussian fourth-moment identity or justified parameter differentiation) — defer.
- Wording: keep the discrepancy signed with remainder; "purely anharmonic" = vanishes for a purely quadratic loss, but it does couple anchor and anharmonicity via `−aᵢαᵢ/(2λᵢ²)`; do not transfer the centred prediction's shrinkage claim to the anchored one (its mean-energy term can put it above `d/2`); `A` is the first-order coefficient, not the finite-`t` mean-energy term.

## Vote
- Claude: A–C (`anchoredGaussianEnergy_eq`, `anchoredGaussianEnergy_rate2`, `localisedEnergy_anchoredGap`), D deferred
- GPT-6 Astra: A–C, with the sharper reciprocal-factorisation proof of B, one shared coefficient identity, D deferred
