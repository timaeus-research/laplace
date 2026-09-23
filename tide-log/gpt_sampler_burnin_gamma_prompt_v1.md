You are consulted (one round) on tide 92 of an automated Lean 4 + Mathlib formalisation loop extending the `laplace` seabed
(Laplace asymptotics for Gibbs expectations, susceptibility-primer / "Sanity on Sampling" note). Zero sorry/axiom discipline.
Tide 91 (your consult, A1+A2+A3) is landing: in the seabed's tilted-Gaussian formalism `tiltedExpectation Q 0`, the Laplace transform
of the LLC statistic `X = t·½uᵀHu` is `√(det Q)/√(det(Q + stH))` exactly, giving `(1+s)^{−d/2}` under the Gibbs law, `∏(1 + s tλᵢ/(tλᵢ+γ))^{−1/2}`
under the localised law and `∏(1 + s/(1 − hpᵢ/2))^{−1/2}` under the ULA stationary law (`pᵢ = tλᵢ`). You flagged the finite-time
(burn-in) transform as "valuable, especially for quantifying burn-in, but not necessary for the current bundle". This tide is it.

## Seabed (sampler side)
`ulaStep P h = 1 − h•P = U diag(1 − hpᵢ) Uᵀ` (`ulaStep_eq_conj`), `ulaCov P h = (P − (h/2)P²)⁻¹ = U diag(1/(pᵢ(1 − hpᵢ/2))) Uᵀ`
(`ulaCov_eq_conj_diagonal`, `U = orthoOf hP.1`), `covStep A N X = A X Aᵀ + N`, the fixed point `covStep A N S = S` for `S = ulaCov`
(`ulaCov_fixed`), `covStep_iterate_zero_of_comm : (covStep A N)^[k] 0 = S (1 − A^{2k})` (from the mode), the Mathlib-side
`gaussStep_iterate_zero : law after k steps = multivariateGaussian 0 (S − A^k S Aᵀ^k)`, `llc_ula_trajectory` (the mean along the
trajectory as a trace); tide 91's `tiltedExpectation_exp_quadForm`, `det_conj_orthoOf`, `posDef_of_orthoOf_conj`; Mathlib
`Matrix.inv_eq_left_inv`, `diagonal_mul_diagonal`, `diagonal_pow`, `diagonal_sub`, `Matrix.PosDef.diagonal`.

## Candidates v1 (Claude)

**A. The burn-in covariance in the eigenbasis.** For `P ≻ 0`, `0 < h`, `hpᵢ < 2` (so `ρᵢ := 1 − hpᵢ ∈ (−1, 1)`) and `k ≥ 1`:
`Σ_k := ulaCov P h * (1 − (ulaStep P h)^(2k)) = U diag(σᵢ²(1 − ρᵢ^{2k})) Uᵀ`, `σᵢ² = 1/(pᵢ(1 − hpᵢ/2))`; its inverse (the precision of the
k-step law from the mode) is `Q_k = U diag(qᵢ(k)) Uᵀ`, `qᵢ(k) = pᵢ(1 − hpᵢ/2)/(1 − ρᵢ^{2k}) > 0` (`inv_eq_left_inv`), so `Q_k ≻ 0`.
(Lemmas: `(U D Uᵀ)^n = U Dⁿ Uᵀ`, `U D₁ Uᵀ · U D₂ Uᵀ = U D₁D₂ Uᵀ`, `1 − U D Uᵀ = U (1 − D) Uᵀ`.)

**B. The burn-in Gamma law.** For `s ≥ 0`: **`tiltedExpectation Q_k 0 (exp(−s·t·½uᵀHu)) = √(∏ᵢ qᵢ(k)/(qᵢ(k) + s pᵢ))
= ∏ᵢ (1 + s(1 − ρᵢ^{2k})/(1 − hpᵢ/2))^{−1/2}`** — after `k` ULA steps from the mode the LLC statistic is a sum of independent
`Gamma(½, rate (1 − hpᵢ/2)/(1 − ρᵢ^{2k}))`: the burn-in *raises* every rate by `1/(1 − ρᵢ^{2k})` (the statistic starts at `0` and grows
to its stationary law), monotonically in `k` toward the stationary rates `1 − hpᵢ/2` (tide 91); the mean
`½∑ᵢ(1 − ρᵢ^{2k})/(1 − hpᵢ/2)` is `llc_ula_trajectory`'s trace `½ tr(P(S − A^kSAᵀ^k))` in eigen form (we would state the mean formula
only as the value of the trace, not via differentiation). Also the localised version (`P_γ = tH + γI`) if cheap.

**C. Monotonicity/limit remarks (Lean-cheap):** `1 − ρᵢ^{2k}` is increasing in `k` and `→ 1`, so the transform decreases in `k` to the
stationary transform pointwise in `s ≥ 0`; `k = 0` gives the transform `1` (`δ₀`; excluded from B since `Σ_0 = 0` is not invertible).

## Numerical check (d = 3, t = 2, h = 0.05, `hp_max = 1.20`, `ρ = (0.947, 0.922, −0.197)`, 10⁶ chains from the mode)
`k = 1`: MC `0.48036 ± 0.00032` (s = 1) vs product `0.48031`; `k = 5`: `0.35639 ± 0.00028` vs `0.35644`; `k = 40`: `0.26422 ± 0.00025`
vs `0.26418` (stationary tide-91 value `0.26279`); the MC mean of `X` tracks `½∑(1 − ρ^{2k})/(1 − hp/2)` (`1.328 → 2.272`, stationary
`2.279`). (With `h = 0.15`, `hp_max = 2.4 > 2`, the chain is unstable — the transform formula still matched MC at each `k`, but the
"stationary" quantities are meaningless; stability `hpᵢ < 2` is a hypothesis of B.)

## Questions
1. Are A–C correct (the eigen form of `Σ_k`, the precision `Q_k`, positivity for `k ≥ 1` under `|ρᵢ| < 1`, the rate
   `(1 − hpᵢ/2)/(1 − ρᵢ^{2k})`, the sign of `s`)? Does `|ρᵢ| < 1` need `hpᵢ < 2` *and* `hpᵢ > 0` — is the case `ρᵢ ≤ 0` (overshooting,
   `1 < hpᵢ < 2`) fine (`ρᵢ^{2k} < 1` still)? 
2. Route/pitfalls: is stating the law via the precision `Q_k = Σ_k⁻¹` (tilted formalism) the right interface, or should the theorem be
   phrased for the covariance `Σ_k` with an explicit inverse lemma? Is there a slicker way to get `Uᵀ Σ_k⁻¹ U = diag(1/…)` than
   `inv_eq_left_inv` on `U diag(1/d) Uᵀ · U diag(d) Uᵀ = 1`?
3. Anything missed close to this seabed: e.g. a *non-zero* start `w₀ ≠ 0` (mean `A^k w₀`, non-central Gamma: transform picks up
   `exp(−s·½ mᵀ(…)m)`-type factors — worth it?), or the burn-in of the *localised* chain, or an explicit bound "after `k ≥ log(ε)/(2 log ρ_max)`
   steps the transform is within `ε` of stationary"?
4. Wording against E4 (burn-in / zero-start factor `ρ^{2(b+1)}`) and E3: is "from the mode, the LLC statistic is at every step a sum of
   independent Gamma(½) variables whose rates decay geometrically to the stationary ULA rates; the burn-in bias of the LLC is the sum
   `½∑ρᵢ^{2k}/(1 − hpᵢ/2)`" a fair gloss; qualifications (Gaussian target, exact chain law not the pooled estimator, the
   `multivariateGaussian` bridge not machine-checked)?
Vote for one bundle at the end.
