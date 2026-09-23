# Tide 96 consult: the anchored Gaussian variance gap (laplace seabed, Lean 4 + Mathlib)

Context. In the `laplace` seabed (formalising the "Sanity on Sampling" note's E2/E3 comparisons) we have landed:
- tide 87 `localisedVar_energy_order2`: `|t² Var_loc(L∘A) − d/2 − 2∑ᵢe₁ᵢ/t| ≤ K/t²` for `t ≥ T ≥ 1`, where `Var_loc` is the variance under the localised anharmonic Gibbs law `exp(−t∑ℓᵢ(uᵢ) − (g/2)|u − u₀|²)` in the E2 frame (`ℓᵢ = λᵢx²/2 + αᵢx³/6 + γᵢx⁴/24`, `αᵢ² < 3λᵢγᵢ`), and `e₁ = (a² − g)/(2λ) − aα/(2λ²) − γ/(8λ²) + 5α²/(24λ³)`, `a = g u₀`.
- tide 94 `localisedLaplace_anchoredGap`: transform gap `⟨e^{−st·L∘A}⟩_loc − Λ^{anch} = −(1+s)^{−d/2} sC₁′/((1+s)t) + O(t⁻²)`, `C₁′ = ∑(e₁ᵢ + g/(2λᵢ) − aᵢ²/(2λᵢ)) = ∑(e₀ᵢ − aᵢαᵢ/(2λᵢ²))`, with the identity `energyLocCoeff1_anchored : e₁ + g/(2λ) − a²/(2λ) = e₀ − aα/(2λ²)`.
- tide 95 `localisedEnergy_anchoredGap`: energy gap `t⟨L∘A⟩_loc − 𝓔^{anch}_t = C₁′/t + O(t⁻²)`, `𝓔^{anch}_t = t·⟨½uᵀHu⟩_{tH+gI,v} = ½∑tλᵢ/(tλᵢ+g) + (t/2)∑λᵢ(aᵢ/(tλᵢ+g))²`.
- Gaussian infrastructure (analytic, `gaussianWeight (matCLM P) u = exp(−½uᵀPu)`, `gaussianZ`): `gaussian_fourth_moment_matCLM (hP) (a b c d) : ∫ u_a u_b u_c u_d gw = Z (Σ_ad Σ_bc + Σ_bd Σ_ac + Σ_cd Σ_ab)`, `Σ = P⁻¹`; `integral_coord_mul_gaussianWeight_matCLM : ∫ u_i u_j gw = Z Σ_ij`; `integral_coord_mul_gaussianWeight_matCLM_eq_zero : ∫ u_i gw = 0`; `gaussian_stein_prod_coord_matCLM (A : Fin n → ι) (j) : ∫ u_j (∏ u_{A s}) gw = ∑_r Σ_{j,A r} ∫ (∏_{s≠r} u_{A s}) gw`; `integrable_prod_coord_mul_gaussianWeight_matCLM`; tilted Gaussian `tiltedExpectation P v φ = ∫ φ e^{−½uᵀPu + v·u} / Z_v`, `tiltedExpectation_eq : = ∫ φ(u + m) gw / Z`, `m = P⁻¹v`; `tiltedExpectation_quadForm : ⟨uᵀHu⟩_{P,v} = ∑∑ H_ij Σ_ij + mᵀHm`; `tiltedCov`; `inv_localisedPrecision_eq_conj : (tH+gI)⁻¹ = U diag(1/(tλᵢ+g)) Uᵀ`; `mul_orthoOf_eq : H U = U diag(λ)`; `tiltMean_quadForm_localised : mᵀHm = ∑λᵢ(aᵢ/(tλᵢ+g))²`, `aᵢ = (Uᵀv)ᵢ`.

Candidates v1 (Claude):

A (Sampler, general). `tiltedVar_quadForm`: for `P ≻ 0` and `H` symmetric,
  `⟨(uᵀHu)²⟩_{P,v} − ⟨uᵀHu⟩²_{P,v} = 2·tr((HΣ)²) + 4·(Hm)ᵀΣ(Hm)`, `Σ = P⁻¹`, `m = P⁻¹v`.
  Route: shift `u ↦ u + m` (`tiltedExpectation_eq`), expand `((u+m)ᵀH(u+m))² = (uᵀHu)² + 4(mᵀHu)² + (mᵀHm)² + 4(uᵀHu)(mᵀHu) + 2(uᵀHu)(mᵀHm) + 4(mᵀHu)(mᵀHm)`; the odd terms vanish; `∫(uᵀHu)² gw = Z(tr(HΣ)² + 2tr((HΣ)²))` from the Wick fourth moment via `(uᵀHu)² = ∑_{ab}∑_{cd} H_ab H_cd u_a u_b u_c u_d`; `∫(mᵀHu)² gw = Z (Hm)ᵀΣ(Hm)`. Then subtract `(tr(HΣ) + mᵀHm)²`.
  Hence for `Q = ½uᵀHu`: `Var_{P,v}(Q) = ½tr((HΣ)²) + mᵀHΣHm`.

B (Sampler, eigen form). For `P = tH + gI`, `aᵢ = (Uᵀv)ᵢ`:
  `t²·Var_{tH+gI,v}(½uᵀHu) = ½∑ᵢ(tλᵢ/(tλᵢ+g))² + t²∑ᵢ λᵢ²aᵢ²/(tλᵢ+g)³`
  (`HΣ = U diag(λᵢ/(tλᵢ+g)) Uᵀ`, `tr((HΣ)²) = ∑(λᵢ/(tλᵢ+g))²`; `Uᵀ(Hm) = (λᵢaᵢ/(tλᵢ+g))ᵢ`).

C (Multi, expansion). For `t ≥ 1`: `|B − d/2 − (∑ᵢaᵢ²/λᵢ − g∑ᵢ1/λᵢ)/t| ≤ K/t²` with explicit `K`, via `½(tλ/(tλ+g))² − ½ + g/(λt) = g(1/(tλ) − 1/(tλ+g)) + g²/(2(tλ+g)²)` (≤ (3/2)g²/(λ²t²)) and `t²λ²a²/(tλ+g)³ − a²/(λt) = a²λ²t²(1/(tλ+g)³ − 1/(tλ)³)`, `|1/(u+g)³ − 1/u³| ≤ g(3u² + 3ug + g²)/u⁶`.

D (Multi, the gap). `t²Var_loc(L∘A) − t²Var_{tH+gI, g u₀}(½uᵀHu) = 2C₁′/t + O(t⁻²)` in the E2 frame (`aᵢ = g u₀ᵢ`), from tide 87 and C with `2(e₁ + g/(2λ) − a²/(2λ)) = 2e₁ − (a²/λ − g/λ)`: **three gaps (transform, energy, variance), one coefficient `C₁′`**.

Numerical check (λ = (1.3, 0.9), α = (0.7, −0.4), γ = (1.1, 0.8), g = 0.8, u₀ = (0.55, −0.35); `C₁′ = −0.272888`): formula B agrees with direct Gaussian integration to 1e-10; `t(t²Var_anch − d/2) → −1.26824` (the coefficient `∑a²/λ − g∑1/λ`); `t(t²Var_loc − t²Var_anch)` → `2C₁′ = −0.545776` (−0.48 at t = 40 → −0.535 at t = 640, t²-remainder ≈ 3.4 converging).

Questions:
1. Are A–D correct as stated (in particular the Wick expansion `∫(uᵀHu)² gw = Z(tr(HΣ)² + 2tr((HΣ)²))`, the cross-term `4(Hm)ᵀΣ(Hm)`, and the variance-gap coefficient `2C₁′`)? Is the cumulant bookkeeping consistent across the three landed gaps: mean `d/2 + E₁/t`, variance `d/2 + 2E₁/t`, transform `(1+s)^{−d/2}(1 − sE₁/((1+s)t))` for the same `E₁` — i.e. does `log Λ` to order `1/t` reproduce mean and variance corrections `E₁/t` and `2E₁/t`?
2. For the vanishing odd moments `∫(uᵀHu)(mᵀHu) gw = 0` and `∫ (mᵀHu) gw = 0`: is the cleanest Lean route the Stein identity `gaussian_stein_prod_coord_matCLM` with `n = 2` (giving `∫ u_j u_a u_b gw = Σ_ja ∫u_b + Σ_jb ∫u_a = 0`), or a reflection `u ↦ −u` argument (we have `integral_comp_mulVec (M) (hM : det M ≠ 0) g : ∫ g = |det M| ∫ g(Mv)`)? Any pitfalls with the quadruple-sum → trace bookkeeping (we plan `tr((HΣ)²) = ∑_a∑_c (HΣ)_ac (HΣ)_ca`, expanding via `Matrix.mul_apply` to the order a, c, b, d and matching the Wick terms termwise using the symmetry of `H` and `Σ`)?
3. Is there a stronger or cleaner target nearby (e.g. the full second cumulant identity for general tilt, or the covariance `Cov_{P,v}(uᵀHu, uᵀKu) = 2tr(HΣKΣ) + 4(Hm)ᵀΣ(Km)`, which costs little extra and would give the anchored covariance of two quadratic probes)? Would you fold it in?
4. Wording against E3 for the note: "the anchored Gaussian prediction's mean, variance and Laplace transform of the scaled energy each differ from the exact localised law at order `1/t` by the single anharmonic coefficient `C₁′` (`C₁′/t`, `2C₁′/t`, `−sC₁′/((1+s)^{d/2+1}t)`)" — fair, and what qualifications?
5. Vote: which candidates to formalise this tide?
