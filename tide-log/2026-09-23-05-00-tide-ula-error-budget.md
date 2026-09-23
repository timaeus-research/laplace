# Tide: ula-error-budget

**Direction (user):** auto mode — "Continue with what you think best, don't stop"; chosen: the E2–E4 error budget — tide 92's ULA burn-in algebra in an arbitrary orthogonal frame, ULA on the anchored Gaussian from any start with the energy of a second matrix in the same frame, and the exact decomposition of `t⟨L∘A⟩_loc − t⟨½uᵀHu⟩_k` (exact localised LLC minus the k-step ULA anchored estimate) into the anharmonic gap `C₁′/t` (tide 95), the step-size bias `−(th/4)∑λᵢ/κᵢ` and the burn-in transient.
**Seabed:** laplace, commit 3105f47 (tide 98 `burnin-nonzero-start` landed)
**Started:** 2026-09-23T05:00Z

## Candidates v1 (Claude)

`pᵢ = tλᵢ + g`, `ρᵢ = 1 − hpᵢ`, `κᵢ = 1 − hpᵢ/2`, `fᵢ = 1 − ρᵢ^{2k}`, `aᵢ = g u₀ᵢ`.
- **A** (Sampler, frame-general): `ulaStep_eq_conj_frame`, `ulaCov_eq_conj_frame`, `burnInCov_eq_conj_frame`, `burnInCov_inv_posDef_frame` for any `U` with `UᵀU = 1`, `UᵀPU = diag p`.
- **B** (Sampler): ULA on `N(m, P⁻¹)` from `x₀`: k-step law `N(m_k, Σ_k)`, `m_k = m + (1 − hP)^k(x₀ − m)` (`burnInMeanAnch`, `burnInTiltAnch`), and for `UᵀHU = diag λ`:
  `⟨½uᵀHu⟩_k = ½∑λᵢfᵢ/(pᵢκᵢ) + ½∑λᵢ((Uᵀm_k)ᵢ)²`, `(Uᵀm_k)ᵢ = (Uᵀm)ᵢ + ρᵢ^k((Uᵀx₀)ᵢ − (Uᵀm)ᵢ)` (`burnInAnch_energy_frame`).
- **C** (Multi): `|t⟨L∘A⟩_loc − t⟨½uᵀHu⟩_k − C₁′/t + (th/4)∑λᵢ/κᵢ − Burn_k| ≤ K/t²` for `t ≥ T`, any `h` with `hpᵢ < 2`, `k ≥ 1`, `x₀`;
  `Burn_k = (t/2)∑λᵢρᵢ^{2k}/(pᵢκᵢ) − (t/2)∑λᵢ[((Qᵀm_k)ᵢ)² − (aᵢ/pᵢ)²]` (`ulaAnchored_llc_budget`), via the exact identity `𝓔^{anch} − t⟨½uᵀHu⟩_k = −(th/4)∑λᵢ/κᵢ + Burn_k`.

## Numerical check

`numcheck_ula_error_budget.py` (E2 frame 2D as in tides 94–97, `x₀ = (0.9, −0.6)`, `k = 3`, `h = η/t`, `η = 0.3`): the exact identity holds to 1e-6; Monte Carlo of the ULA chain gives `t⟨½uᵀHu⟩_k = 3.130` vs the formula 3.133 (t = 40); `t·(t⟨L⟩ − t⟨½uᵀHu⟩_k − disc − burn)`: −0.2534 (t = 40) → −0.2716 (t = 640) vs `C₁′ = −0.2729`. With `h = η/t` the step-size bias tends to `(η/4)∑λᵢ/(1 − ηλᵢ/2) = 0.199` (O(1) in t), and the burn-in transient from a fixed ambient start grows like `t·ρ^{2k}` (−1.95 at t = 40, −32.9 at t = 640).

## Questions for GPT-6 Astra (prompt in `gpt_ula_error_budget_prompt_v1.md`)

Correctness of A–C and sign conventions; E4/E5 reading (β-scaled step ⇒ O(1) discretisation bias vs `C₁′/t` anharmonic error; burn-in steps must grow like `log t`); Lean route and pitfalls; cheap additions (`h = η/t` corollary, stationary budget, variance budget); vote.

## GPT-6 Astra v1 (summary; verbatim in `gpt_ula_error_budget_v1.md`)

- A–C correct with `pᵢ > 0`, `h > 0`, `hpᵢ < 2` (`|ρᵢ| < 1`, `κᵢ > 0`, `fᵢ > 0` for `k ≥ 1`); `Σ_k` is the covariance from a *deterministic* start; the per-mode
  identity is exactly `1 − κᵢ = hpᵢ/2`; under "truth minus estimate" the stationary discretisation term is negative (the sampler's stationary
  quadratic estimate lies above the anchored Gaussian value), the burn-in term has no fixed sign. A frame diagonalising `H` diagonalises
  `P = tH + gI` automatically — use the E2 frame `Q`. Inherit tide 95's hypotheses; the remainder constant and threshold are unchanged
  (the sampler corrections are exact), so the budget is uniform over admissible `h`, `k`, `x₀`, including `t`-dependent ones.
- Scaled step `h = η/t` with `ηλ_max < 2`: stability for large `t`; bias `D_t → D_∞ = (η/4)∑λᵢ/(1 − ηλᵢ/2) = (η/4)tr H + O(η²)`: an `O(1)` LLC bias
  vs the `O(1/t)` anharmonic correction; to make the discretisation bias `O(1/t)` take `h = O(t⁻²)`. Contraction rate: use `r = max|ρᵢ|`
  (not the smallest precision's mode). Burn-in expansion `Burn_k = (t/2)∑λρ^{2k}/(pκ) − t∑λbρ^k(z − b) − (t/2)∑λρ^{2k}(z − b)²` gives
  `|Burn_k| ≤ C(t r^{2k} + r^k + r^{2k})`: bounded transient needs `k ≳ log t/(2|log r|)`, `O(1/t)` transient needs `k ≳ log t/|log r|`
  (sufficient, worst case). Exact stationary Gaussian ULA bias `(h/4)tr(H(I − hP/2)⁻¹) = (h/4)tr(PHΣ_∞)`; first-order `(h/4)tr H` is not
  adequate when `hP` is not small.
- Note wording: "The anharmonic correction compares two equilibrium models. The ULA discretisation bias compares their Gaussian target with
  the sampler's invariant law, while burn-in measures nonstationarity. At fixed `ht = η` the discretisation bias persists as `t → ∞` and
  generally masks the `t⁻¹` anharmonic correction." Label C an *expectation-bias* budget (Monte Carlo fluctuation is separate).
- Lean route endorsed; pitfalls: both `UᵀU = 1` and `UUᵀ = 1`, positivity facts before inversion, `k ≥ 1`, `ρ^{2k} = (ρ^k)²`, symmetry of `Σ_k`
  when passing to the trace, `field_simp; ring` per mode with only `p ≠ 0`, `κ ≠ 0`.
- Cheap additions (taken: cold-start specialisation, expanded burn-in formula, scaled-step limit; deferred: stationary `k → ∞` budget as a
  separate statement, the single-time variance `(t²/2)∑λᵢ²vᵢ² + t²∑λᵢ²μᵢ²vᵢ`).

## Vote
- Claude: A–C plus `burnInAnch_energy_frame_modeStart`, `burnIn_meanTerm_expand`, `ulaScaledStep_bias_tendsto`
- GPT-6 Astra: land A → B → C plus the stationary identity and expanded burn-in formula; state the rate via `max|ρᵢ|`; distinguish bounded from `t⁻¹`-accurate burn-in
