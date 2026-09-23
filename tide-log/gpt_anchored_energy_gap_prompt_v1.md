You are consulted (one round) on tide 95 of an automated Lean 4 + Mathlib formalisation loop extending the `laplace` seabed
(Laplace asymptotics for Gibbs expectations, susceptibility-primer / "Sanity on Sampling" note). Zero sorry/axiom discipline. Fixed
parameters, eventual remainders. Tide 94 (your consult) is landing: E3's anchored (tilted) Gaussian prediction has the scaled-energy
transform `Λ^{anch} = exp(∑ᵢ(aᵢ²/2)(1/((1+s)tλᵢ+g) − 1/(tλᵢ+g)))·∏ᵢ√((tλᵢ+g)/((1+s)tλᵢ+g))` (exact, `aᵢ = (Uᵀv)ᵢ`), expands as
`(1+s)^{−d/2}(1 + s(G − A)/((1+s)t)) + O(t⁻²)` (`G = g∑1/(2λᵢ)`, `A = ∑aᵢ²/(2λᵢ)`), and the exact anharmonic localised transform differs from it by
`−sC₁′/((1+s)^{d/2+1}t) + O(t⁻²)`, `C₁′ = ∑ᵢ(e₀ᵢ − aᵢαᵢ/(2λᵢ²))`. You suggested the anchored *energy* corollary "if the existing E2 energy rate
theorem makes it short", with the warning not to differentiate the fixed-`s` transform remainder. This tide is that corollary, done from
the landed energy theorem and an independent expansion of the exact Gaussian energy.

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

## Questions
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
