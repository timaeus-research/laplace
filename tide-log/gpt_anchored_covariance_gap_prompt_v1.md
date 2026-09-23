# Tide 97 consult: the anchored Gaussian covariance (susceptibility) gap for quadratic probes (laplace seabed, Lean 4 + Mathlib)

Context (landed): E2's exact localised law `exp(−t∑ᵢℓᵢ(uᵢ) − (g/2)|u − u₀|²)` in the eigenframe, `ℓᵢ = λᵢx²/2 + αᵢx³/6 + γᵢx⁴/24`, `αᵢ² < 3λᵢγᵢ`, `aᵢ = g u₀ᵢ`.
- `localisedRotatedAnharmonic_covK_order2_rate` (ambient probe `ψ(w) = ½(w−c)ᵀB(w−c) + b·(w−c)`, `B̃ = QᵀBQ`, `b̃ = Qᵀb`):
  `|t²Cov_loc(L∘A, ψ) − ∑ᵢ(B̃ᵢᵢ/(2λᵢ) + b̃ᵢcᵢ) − C′_loc/t| ≤ K/t²`, `cᵢ = −αᵢ/(2λᵢ²) + aᵢ/λᵢ` (`locLeadMean`),
  `C′_loc = ∑ᵢ(B̃ᵢᵢc₂′ᵢ + 2b̃ᵢm₂ᵢ) + ∑_{i≠j}B̃ᵢⱼcᵢcⱼ` (`locCovKCoeff2Sep`), with the landed closed forms
  `c₂′ = locSecondCoeff2 = 5α²/(4λ⁴) − 2aα/λ³ − γ/(2λ³) + (a² − g)/λ²` (via `varLocCoeff2_eq`: `varLocCoeff2 = c₂′ − c² = α²/λ⁴ − aα/λ³ − g/λ² − γ/(2λ³)`),
  `m₂ = meanLocCoeff2 = meanCoeff2 + aα²/λ⁴ − aγ/(2λ³) + αg/λ³ − αa²/(2λ³) − ag/λ²`, `meanCoeff2 = −5α³/(8λ⁵) + 2αγ/(3λ⁴)`.
- Tide 96 (`tiltedVar_quadForm`): `Var_{P,v}(uᵀHu) = 2tr(HΣHΣ) + 4(Hm)ᵀΣ(Hm)` from the Wick fourth moment `∫u_a u_b u_c u_d gw = Z(Σ_ad Σ_bc + Σ_bd Σ_ac + Σ_cd Σ_ab)`, the shift `u ↦ u + m`, odd moments by reflection; `∫(uᵀHu)² gw = Z(tr(HΣ)² + 2tr(HΣHΣ))`; eigen forms `H(tH+gI)⁻¹ = U diag(λᵢ/(tλᵢ+g)) Uᵀ`, `Uᵀm = (aᵢ/(tλᵢ+g))ᵢ`.
- Tides 94–96: transform, mean and variance gaps all governed by `C₁′ = ∑(e₀ᵢ − aᵢαᵢ/(2λᵢ²))`.

Candidates v1 (Claude), `Σ = P⁻¹`, `m = P⁻¹v`, `H, B` symmetric, `pᵢ = tλᵢ + g`:

A (Sampler, general). `tiltedCov_quadForm`: `Cov_{P,v}(uᵀHu, uᵀBu) = 2tr(HΣBΣ) + 4(Hm)ᵀΣ(Bm)` — the mixed Wick integral `∫(uᵀHu)(uᵀBu) gw = Z(tr(HΣ)tr(BΣ) + 2tr(HΣBΣ))` (same three-contraction proof as tide 96 with `B` in place of the second `H`), plus `∫(uᵀHu)(uᵀw) gw = 0`, `∫(uᵀw₁)(uᵀw₂) gw = Z w₁ᵀΣw₂`.
   `tiltedCov_quadForm_linear`: `Cov_{P,v}(uᵀHu, b·u) = 2bᵀΣ(Hm)`.
B (Sampler, eigen). For `P = tH + gI`, `B̃ = UᵀBU`, `b̃ = Uᵀb`, `aᵢ = (Uᵀv)ᵢ`:
   `t²Cov_{tH+gI,v}(½uᵀHu, ½uᵀBu + b·u) = ½∑ᵢB̃ᵢᵢ(tλᵢ/pᵢ)²/λᵢ + t²∑ᵢⱼλᵢaᵢB̃ᵢⱼaⱼ/(pᵢ²pⱼ) + t²∑ᵢb̃ᵢλᵢaᵢ/pᵢ²`.
C (Multi, expansion). `B = ∑ᵢ(B̃ᵢᵢ/(2λᵢ) + b̃ᵢaᵢ/λᵢ) + [−g∑ᵢB̃ᵢᵢ/λᵢ² + ∑ᵢⱼB̃ᵢⱼaᵢaⱼ/(λᵢλⱼ) − 2g∑ᵢb̃ᵢaᵢ/λᵢ²]/t + O(t⁻²)` with an explicit constant (per-term reciprocal bounds as in tide 96).
D (Multi, the gap). In the E2 frame:
   `t²Cov_loc(L∘A, ψ) − t²Cov_anch = −∑ᵢb̃ᵢαᵢ/(2λᵢ²) + Γ_B/t + O(t⁻²)`,
   `Γ_B = ∑ᵢB̃ᵢᵢΓᵢᵢ + ∑_{i≠j}B̃ᵢⱼ(cᵢcⱼ − aᵢaⱼ/(λᵢλⱼ)) + 2∑ᵢb̃ᵢ(m₂ᵢ + gaᵢ/λᵢ²)`, `Γᵢᵢ = c₂′ᵢ + g/λᵢ² − aᵢ²/λᵢ² = 5αᵢ²/(4λᵢ⁴) − 2aᵢαᵢ/λᵢ³ − γᵢ/(2λᵢ³)`,
   `cᵢcⱼ − aᵢaⱼ/(λᵢλⱼ) = αᵢαⱼ/(4λᵢ²λⱼ²) − αᵢaⱼ/(2λᵢ²λⱼ) − αⱼaᵢ/(2λⱼ²λᵢ)`, `m₂ + ga/λ² = meanCoeff2 + aα²/λ⁴ − aγ/(2λ³) + αg/λ³ − αa²/(2λ³)`.
   Reading: for a purely quadratic probe (`b = 0`) the anchored prediction of the susceptibility is correct to leading order and off by `tr(B̃Γ)/t` with a purely anharmonic "susceptibility gap matrix" `Γ` (diagonal `Γᵢᵢ`, off-diagonal `cᵢcⱼ − aᵢaⱼ/(λᵢλⱼ)`); a linear probe part sees a *leading-order* gap `−b̃ᵢαᵢ/(2λᵢ²)`: the cubic term's mean shift, invisible to any Gaussian.

Numerical check (λ = (1.3, 0.9), α = (0.7, −0.4), γ = (1.1, 0.8), g = 0.8, u₀ = (0.55, −0.35), B̃ = [[0.9, 0.4],[0.4, 1.6]], b̃ = (0.3, −0.5)): formula B equals direct Gaussian integration to 1e-10; leading gap −0.185587 = predicted; `t·(gap − leading)` → −0.31099 (t = 640) vs `Γ_B = −0.31263`; `t²`-remainder ≈ 1.05 converging; the 1D closed forms `m₂`, `c₂′` reproduced numerically to 3–4 digits at t = 640.

Questions:
1. Are A–D correct as stated? In particular the mixed Wick identity, the cross term `4(Hm)ᵀΣ(Bm)` (not symmetrised — is it automatically symmetric in `H ↔ B`?), the linear covariance `2bᵀΣ(Hm)`, the eigen form B with a non-diagonal `B̃`, and the gap coefficients (leading `−∑b̃ᵢαᵢ/(2λᵢ²)`, `Γᵢᵢ`, off-diagonal, linear `2(m₂ + ga/λ²)`).
2. Sanity: with `B = H`, `b = 0` the probe is the quadratic part of the energy; `Γ_H = ∑λᵢΓᵢᵢ = ∑(5αᵢ²/(4λᵢ³) − 2aᵢαᵢ/λᵢ² − γᵢ/(2λᵢ²))` differs from the variance gap `2C₁′ = ∑(5αᵢ²/(12λᵢ³) − aᵢαᵢ/λᵢ² − γᵢ/(4λᵢ²))` — consistent, since `Cov(L, ½uᵀHu) ≠ Var(L)` (the cubic and quartic parts of `L` contribute)? Is there a clean identity relating `Γ_H`, `2C₁′` and the cubic/quartic probe covariances worth recording?
3. Lean route: prove the mixed Wick integral directly (copy of tide 96's proof with `B`) or by polarisation from the landed `H = B` case (`(H+B)`, `H`, `B`)? For `B̃` non-diagonal, the eigen form of `tr(HΣBΣ)` is `∑ᵢ dᵢ B̃ᵢᵢ d′ᵢ` with `d = λ/(tλ+g)`, `d′ = 1/(tλ+g)`; any pitfalls in stating B with `UᵀBU` and `Uᵀb` (Lean: `(orthoOf hH.1)ᵀ * B * orthoOf hH.1`)?
4. For the Multi gap we compare against the landed E2 theorem stated with `Q`, while the Sampler formula is in the `orthoOf` frame; as in tides 95–96 we state the Multi theorem with the explicit frame formula in `lam`, `QᵀBQ`, `Qᵀb`, `aᵢ = g·affineFrame Q c w₀ i`, and leave the identification of the two spectral frames to prose. Acceptable, or should we also prove basis-independence of the formula this tide?
5. Wording for E3: "E3's anchored Gaussian predicts the susceptibility of every quadratic observable correctly at leading order, with a first-order error `tr(B̃Γ)/t` governed by a purely anharmonic matrix `Γ`; for observables with a linear part the error is already at leading order and equals the cubic mean shift `−∑b̃ᵢαᵢ/(2λᵢ²)`, which no Gaussian model reproduces." Fair? Qualifications?
6. Vote.
