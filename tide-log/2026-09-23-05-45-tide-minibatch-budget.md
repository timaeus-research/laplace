# Tide: minibatch-budget

**Direction (user):** auto mode — "Continue with what you think best, don't stop"; chosen: E8 into the E2–E4 budget — the stationary covariance of SGLD with a constant minibatch gradient-noise covariance `C` in an arbitrary orthogonal frame (the seabed's Lyapunov solution), the energy trace `(t/2)tr(HΣ^{mb}) = (t/2)∑λᵢ(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ)` (only the frame diagonal of `C` enters), and the extended stationary budget with the minibatch bias `(ht³/4)∑λᵢĈᵢᵢ/(pᵢκᵢ)`.
**Seabed:** laplace, commit 8b385c1 (tide 100 `ula-fluctuation-budget` landed)
**Started:** 2026-09-23T05:45Z

## Candidates v1 (Claude)

`pᵢ = tλᵢ + g`, `ρᵢ = 1 − hpᵢ`, `κᵢ = 1 − hpᵢ/2`, `Ĉ = UᵀCU`, `Σ^{mb} = lyapunovVia U ρ (minibatchNoise h t C)`, `minibatchNoise h t C = 2h·1 + h²t²C`.
- **A** (Sampler, frame): `minibatchCov_frame_apply`: `(UᵀΣ^{mb}U)ᵢⱼ = (2h[i=j] + h²t²Ĉᵢⱼ)/(h(pᵢ+pⱼ) − h²pᵢpⱼ)`; `minibatchCov_frame_diag`: `(UᵀΣ^{mb}U)ᵢᵢ = (1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ)`; `minibatch_fixed_iff_frame`: `Σ^{mb}` is the unique fixed point of `X ↦ AXAᵀ + N`.
- **B** (Sampler): `trace_mul_eq_sum_conj_diag`: `tr(HX) = ∑λᵢ(UᵀXU)ᵢᵢ`; `minibatch_llc_frame`: `(t/2)tr(HΣ^{mb}) = (t/2)∑ᵢλᵢ(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ)`.
- **C** (Multi): `ulaAnchored_llc_budget_minibatch`: `|t⟨L∘A⟩_loc − [(t/2)∑λᵢ(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ) + (t/2)∑λᵢbᵢ²] − C₁′/t + (th/4)∑λᵢ/κᵢ + (ht³/4)∑λᵢĈᵢᵢ/(pᵢκᵢ)| ≤ K/t²` (tide 95's constants).

## Numerical check

`numcheck_minibatch_budget.py` (E2 frame 2D, random PSD `C` of size 0.02, `h = 0.3/t`): the iterated Lyapunov fixed point equals the entry and diagonal formulas to 1e-17; `t(t⟨L⟩ − stationary + disc + mb)` → `C₁′` (−0.2534 at t = 40 → −0.2716 at t = 640 vs −0.2729); the minibatch bias grows linearly, 0.066 (t = 40) → 1.069 (t = 640), against the constant discretisation bias 0.199. (The GPT prompt quoted preliminary figures 0.33 → 5.3 typed before the run finished.)

## Questions for GPT-6 Astra (prompt in `gpt_minibatch_budget_prompt_v1.md`)

Correctness of A–C (only the frame diagonal of `C` enters the mean); E8 reading and the phrasing of the three sampler biases against `C₁′/t`; whether the full law's state-dependent term matters for the mean; Lean route; cheap additions; vote.

## GPT-6 Astra v1 (summary; verbatim in `gpt_minibatch_budget_v1.md`)

- A–C correct (`t, h > 0`, `C ⪰ 0`, `0 < hpᵢ < 2`, `U` diagonalising `H` — automatic for `P = tH + gI`); `1 − ρᵢ² = 2hpᵢκᵢ`; only the frame diagonal of
  `C` enters the quadratic mean (a second-moment statement, no Gaussianity); the full `Ĉ` affects the variance only under a distributional
  assumption. `M_mb = (ht³/4)∑λᵢĈᵢᵢ/(pᵢκᵢ) ≥ 0` for PSD `H`, `C`: minibatching inflates the sampler statistic. Scope: the target-side `O(t⁻²)`
  remainder is unchanged, but nothing is said about the minibatch sampler's expectation of the actual non-quadratic loss.
- E8: `C_g = (1/m)(1 − m/n)S²` (denominator `n − 1`) is the covariance of the estimator of `∇L`, so an Euler step injects `h²t²C_g`. At
  `h = η/t`: `M_mb = (ηt/4)∑(tλᵢ/pᵢ)(Ĉᵢᵢ/κᵢ) = (ηt/4)∑Ĉᵢᵢ/(1 − ηλᵢ/2) + O(1)` (keep modewise `κᵢ`; `tr C` only with comparable factors and no
  kernel); bounded inflation needs the weighted covariance `O(1/t)`, comparable to `C₁′/t` needs `O(1/t²)`; for `m ≪ n` this is `m ∝ t`.
  **Constant `C` is the frozen-noise approximation** (`C = C_g(m)`): the exact minibatch covariance recursion is
  `Σ_{k+1} = AΣ_kAᵀ + 2hI + h²t²E[C_g(X_k)]` with `E[C_g(X)] = C_g(m) + E_B[ΔH_BΣΔH_Bᵀ]` at stationarity (the full law's Hessian-fluctuation
  term changes the covariance, hence the energy mean; near interpolation `C_g(m)` can vanish so that term dominates); conditional
  unbiasedness keeps the anchored mean.
- Note wording: "Under the additive constant-covariance approximation the quadratic LLC statistic has stationary upward biases from
  discretisation, `D = (η/4)∑λᵢ/κᵢ`, and minibatching, `M_mb = (ηt/4)∑(tλᵢ/pᵢ)(Ĉᵢᵢ/κᵢ)`; the target-minus-sampler budget is
  `C₁′/t − D − M_mb + Burn_k + O(t⁻²)`. The anharmonic term decays like `1/t`, fixed-`η` discretisation persists, fixed-`C` minibatch inflation
  grows like `t`."
- Lean route endorsed (frame-general conjugation, generic trace lemma, exact energy split before the budget; `(1+x)/y = 1/y + x/y` needs no
  `field_simp`). Cheap additions taken: `M_mb ≥ 0`, the exact `h = η/t` identity, the bound `0 ≤ M_mb ≤ (ht²/(4δ))tr C` for `κᵢ ≥ δ`;
  deferred: the Gaussian-surrogate variance `t²[½∑ᵢⱼλᵢλⱼSᵢⱼ² + ∑ᵢⱼλᵢλⱼbᵢbⱼSᵢⱼ]` (off-diagonal `Ĉ`), `Σ^{mb} − Σ^{ULA} = h²t²∑ᵣAʳC(Aᵀ)ʳ ⪰ 0`.

## Vote
- Claude: A–C plus `minibatch_bias_nonneg`, `minibatch_bias_scaled`, `minibatch_bias_le`
- GPT-6 Astra: land A–C plus exact scaling and nonnegative inflation; label constant `C` a frozen-noise approximation; defer the variance

## Result

Commit `5a3334e` on `tide/minibatch-budget`; `lake build` clean, `scripts/sorries` 0/0/0/0. `Laplace/Multi/MinibatchBudget.lean` (     226 lines).
A–C as voted.
Sampler: `minibatchCov_frame_apply`, `minibatchCov_frame_diag`, `minibatch_fixed_iff_frame`, `trace_mul_eq_sum_conj_diag`, `minibatch_llc_frame`.
Multi: `posSemidef_conj_frame`, `minibatch_bias_nonneg`, `minibatch_bias_scaled`, `minibatch_bias_le`, `ulaAnchored_llc_budget_minibatch`.

Surprises: compiled first time — the seabed's Lyapunov API was already frame-general, so the whole tide is a transcription plus one
exact rearrangement of sums; only the frame diagonal of the gradient-noise covariance enters the mean of the LLC statistic, and at the
β-scaled step the minibatch bias grows linearly in t (0.066 → 1.07 over t = 40 → 640 in the check) while the discretisation bias stays
at 0.199.
