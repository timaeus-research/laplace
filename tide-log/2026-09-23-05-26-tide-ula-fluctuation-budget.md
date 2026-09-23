# Tide: ula-fluctuation-budget

**Direction (user):** auto mode — "Continue with what you think best, don't stop"; chosen: the fluctuation side of tide 99 — the variance of the k-step ULA-sampled anchored statistic in an arbitrary frame (tide 96's tilted variance on the frame-general burn-in law), its E2 instantiation, the stationary (`k → ∞`) limits of the burn-in energy, transient and variance, and the stationary form of the error budget.
**Seabed:** laplace, commit a1852a9 (tide 99 `ula-error-budget` landed)
**Started:** 2026-09-23T05:26Z

## Candidates v1 (Claude)

`vᵢ = fᵢ/(pᵢκᵢ)`, `μᵢ = (Uᵀm)ᵢ + ρᵢ^k(Uᵀ(x₀ − m))ᵢ`; E2 frame: `bᵢ = aᵢ/pᵢ`, `zᵢ = (Qᵀx₀)ᵢ`.
- **A** (Sampler, frame) `burnInAnch_var_frame`: `Var_k(½uᵀHu) = ½∑ᵢ(λᵢvᵢ)² + ∑ᵢvᵢ(λᵢμᵢ)²`.
- **B** (Multi) `ulaAnchored_llc_var`: `Var_k(t·½uᵀHu) = (t²/2)∑(λᵢvᵢ)² + t²∑vᵢ(λᵢ(bᵢ + ρᵢ^k(zᵢ − bᵢ)))²`.
- **C** (Multi, fixed `t`, `h`) `ulaAnchored_energy_tendsto`, `ulaAnchored_burn_tendsto`, `ulaAnchored_var_tendsto`: `k → ∞` limits `(t/2)∑λᵢ/(pᵢκᵢ) + (t/2)∑λᵢbᵢ²`, `0`, `(t²/2)∑(λᵢ/(pᵢκᵢ))² + t²∑λᵢ²bᵢ²/(pᵢκᵢ)`.
- **D** (Multi) `ulaAnchored_llc_budget_stationary`: `|t⟨L∘A⟩_loc − ((t/2)∑λᵢ/(pᵢκᵢ) + (t/2)∑λᵢbᵢ²) − C₁′/t + (th/4)∑λᵢ/κᵢ| ≤ K/t²` (tide 95's constants).

## Numerical check

`numcheck_ula_fluctuation_budget.py` (E2 frame 2D, `t = 40`, `h = 0.3/t`, `x₀ = (0.9, −0.6)`, 4·10⁵ chains): at `k = 3` MC variance 5.604 vs formula 5.592 (mean 3.133 vs 3.133); along `k` the energy 11.87 (k = 1) → 1.1843 (k ≥ 30 = stationary `t/2∑λ/(pκ) + t/2∑λb²`), the transient −10.68 → 0, the variance 16.29 → 1.4048 (= stationary formula); step-size bias 0.19988.

## Questions for GPT-6 Astra (prompt in `gpt_ula_fluctuation_budget_prompt_v1.md`)

Correctness of A–D; E5 reading (`t → ∞` limits at fixed `η`, what a single sample resolves, steps/samples to see `C₁′/t`); Lean route; cheap additions; vote.

## GPT-6 Astra v1 (summary; verbatim in `gpt_ula_fluctuation_budget_v1.md`)

- A–D correct (`H = U diag λ Uᵀ`, `pᵢ > 0`, `h > 0`, `hpᵢ < 2`): `Var(½uᵀHu) = ½tr(HΣ_kHΣ_k) + (Hm_k)ᵀΣ_k(Hm_k) = ½∑(λᵢvᵢ)² + ∑vᵢλᵢ²μᵢ²`;
  stationary `S = (t/2)∑λᵢ/(pᵢκᵢ) + (t/2)∑λᵢbᵢ²`, `V = (t²/2)∑λᵢ²/(pᵢκᵢ)² + t²∑λᵢ²bᵢ²/(pᵢκᵢ)`; D has the right signs ("exceeds" is a signed expansion,
  not a finite-`t` inequality). Corrections to the prose: the stationary variance is independent of `x₀` (its second piece is an
  anchor/noncentrality term), and `Var_k` need not increase monotonically in `k` (a distant start can overshoot).
- Fixed `η` (`h = η/t`, `0 < η < 2/λ_max`, `cᵢ = 1 − ηλᵢ/2`): `(t²/2)∑λᵢ²/(pᵢ²κᵢ²) → ½∑cᵢ⁻²` and `t²∑λᵢ²bᵢ²/(pᵢκᵢ) = (1/t)∑aᵢ²/(λᵢcᵢ) + O(t⁻²) → 0`
  (my prompt's nonzero limit for the second piece lost a factor `1/t`); so `V_{t,η/t} = ½∑cᵢ⁻² + O(1/t)`, one stationary sample has `O(1)`
  fluctuation (`Y_∞ → ½∑Zᵢ²/cᵢ` in law), `D_{t,η/t} → ½∑(cᵢ⁻¹ − 1)`. Ledger: sampling fluctuation `O(1)`, fixed-`η` ULA bias `O(1)`, anharmonic
  `C₁′/t`, analytic remainder `O(t⁻²)`. Resolving `C₁′/t` by averaging needs `M_eff ≳ V t²/(α²C₁′²)` effectively independent observations (order
  `t²`), after subtracting the exact `D_{t,h}` or making it small (`h = o(t⁻²)`, at the cost of correlation times `∼ t` and order-`t³` steps);
  "Gaussian ULA samples alone do not identify an unknown anharmonic coefficient".
- Lean route endorsed (frame algebra first, `tiltedVar_quadForm` with precision `Σ_k⁻¹` and tilt `Σ_k⁻¹m_k`, `k ≥ 1`, scalar limits via
  `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`, D by direct algebra with tide 95's constants).
- Cheap additions: fixed-`η` variance limits (taken for the main piece: `ulaScaledStep_factor_tendsto`, `ulaScaledStep_var_main_tendsto`),
  an explicit geometric burn bound, independent-replicate MSE `E(Ȳ_M − EY)² = V/M` + Chebyshev (deferred), stationary autocovariance
  `Cov(Y₀,Y_ℓ) = (t²/2)∑λᵢ²sᵢ²ρᵢ^{2ℓ} + t²∑λᵢ²bᵢ²sᵢρᵢ^ℓ` and the long-run variance for time averaging (recorded, deferred).

## Vote
- Claude: A–D plus the fixed-`η` main-variance limit; MSE/Chebyshev, autocovariance and the explicit burn bound deferred
- GPT-6 Astra: YES on A–D; prioritise the fixed-`η` limit and explicit burn bound, MSE optional, autocorrelation deferred
