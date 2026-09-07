# Grammar §4 formalisation — headline index (general-dimensional normal block)

## Taylor-tree programme (opened 2026-09-07, after the freeze; Astra #26)
**Stage 1 — exact multivariate state density — COMPLETE (units 223–226).**
| Headline | Statement | File:line |
|---|---|---|
| XXII | exact state density: `∫_{(0,1]^{n+1}} ∏aᵢ^{wᵢ} g(∏aᵢ) = ∫₀¹ v g`, `v = eval (stateDensityRep n w)` a finite sum of `z^{μ-1}(-log z)^j`, `μ ∈ {wᵢ+1}`, `j < multiplicity` | StateDensity.lean (`weightedBoxIntegral_eq_stateDensity`, `stateDensityRep_exponent_mem`, `stateDensityRep_degree_lt`) |
| XXII′ | Mellin transform `∫₀¹ z^s v = ∏ 1/(wᵢ+s+1)`; basis `∫₀¹ τ^{c-1}(-log τ)^j = j!/c^{j+1}`; real identity for `f ≥ 0`; integrability | StateDensityAPI.lean (`mellin_stateDensity`, `integral_Ioc_rpow_mul_neg_log_pow`, `integral_unitBox_eq_stateDensity`) |
| XXII″ | top coefficient `c_{l,m-1} = (1/(m-1)!) ∏_{wᵢ+1≠l} 1/(wᵢ+1-l)`; monomial form `= a_{-m}/(m-1)!` (Headline XXI's `mellinCoeff h k l 1`) | StateDensityLeadCoeff.lean (`stateDensityRep_leadCoeff`, `monomial_leadCoeff`) |
Convolution calculus in `PowLogCalculus.lean` (`PowLogRep.eval_conv`, `conv_exponent_mem`, `conv_degree_lt`).
**Stage 2 — exact monomial moments with a constant phase — COMPLETE (units 227–229).**
| Headline | Statement | File:line |
|---|---|---|
| XXIII | exact identity: `∫_{(0,1]^{n+1}} u^h (√N u^k)^p e^{-βNu^{2k}+β√N u^k a} = ∏1/(2kᵢ) ∑_{(μ,j,c)∈v} c N^{-μ} ∑_{i≤j} C(j,i)(log N)^{j-i} ∫₀^N t^{μ-1}(-log t)^i g(t)`, `g(t) = (√t)^p e^{-βt+β√t a}`, every `N > 0` | MonomialPhaseExpansion.lean (`monomialPhase_eq`) |
| XXIII′ | asymptotic form: `T(N) − monomialMainSum(N) = O(e^{-βN/8})` with the full moments `fluctMoment β a p μ i = ∫₀^∞ t^{μ-1}(-log t)^i g` | MonomialPhaseTail.lean (`monomialPhase_isBigO`, `tail_le`) |
Tools: `phaseKernel`, `truncMoment`, `basis_scaling`, `integral_unitBox_monomial_eq_stateDensity` (MonomialPhaseIdentity.lean).
**Stage 3 — polynomial Taylor tree with spectral truncation — COMPLETE (units 230–239; Astra #27, Gates A–D passed).**
Scope: polynomial phase `ξ` and amplitude `η` (finite monomial lists `MonoRep`), box `(0,1]^{n+1}` (`d = n+1`), `β > 0`, `kᵢ > 0`, `N` = paper's `n`; `Z(N) = polyPhaseIntegral = ∫ η u^h e^{-βN u^{2k} + β√N u^k ξ(u)}`; `Λ_L = latticeBelow (2∏kᵢ) L` (the lattice `Q⁻¹ℕ` below the cutoff; coefficients vanish at exponents not carried by any density).
| Headline | Statement | File:line |
|---|---|---|
| XXIV | exact polynomial Taylor tree, every `N > 0`: `Z(N) = ∑_p β^p/p! ∑_{(γ,c)∈ηJ^p} c · monomialTruncSum(h+γ)` with `J = ξ − ξ(0)` (absolutely convergent; `HasSum` form at L159 / L286) | PhaseTaylorIdentity.lean:270 (`polyPhaseIntegral_eq_tsum_truncSum`) |
| XXV | quantitative cutoff: `|Z(N) − ∑_{μ∈Λ_L} N^{-μ} ∑_{j≤n} A_{μ,j}(log N)^j| ≤ C · N^{-L}(1+log N)^n` for all `N ≥ 1`, `L > 0`, `C` explicit and `N`-free; exact form `= R_high − tail` at L444 | LowSpectrumTail.lean:457 (`taylorTree_cutoff_bound`) |
| XXVI | asymptotic expansion: `Z − spectralSum_L = O(N^{-L}(1+log N)^n)` (L41), `= O(N^{-L}(log N)^n)` (L64), `= o(N^{-L'})` for `L' < L` (L81) | TaylorTreeAsymptotic.lean:41 (`taylorTree_isBigO`) |
| — | spectral coefficient `A_{μ,j} = ∑_p β^p/p! K_k ∑_{(γ,c)} c ∑_{q=j}^{n} coeffAt(ρ_{h+γ},μ,q) C(q,j) fluctMoment_p(μ,q−j)`: cutoff-free, absolutely convergent (Gate D) | SpectralCoefficients.lean:371 (`spectralCoeff`), :343 (`summable_coeffTerm_series`), :384 (`mainSeries_eq_sum`) |
| — | Gate C: `|R_high(N)| ≤ K_k‖η‖₁(n+1)!Q^n M_{L,n}(ξ(0)+‖J‖₁) · N^{-L}(1+log N)^n` (τ-side estimate, constants independent of the monomial) | HighSpectrumBound.lean:376 (`abs_highRemainder_le`), :118 (`basis_integral_le`) |
| — | Gate B: log majorant `M_{ν,r,p}(b) = ∫₀^∞ t^{ν-1}(1+|log t|)^r(√t)^p e^{-βt+βb√t}` finite for all real `b`; Tonelli `∑_p (βB)^p/p! M_{ν,r,p}(b) = M_{ν,r,0}(b+B)` (no smallness on `B`) | PhaseMajorant.lean:146 (`integrableOn_logMajorant`), :246 (`tsum_phaseLogMoment_series`) |
| — | Gate A: uniform weighted budget `∑|c| j! Q^j ≤ (n+1)! Q^n` for every lattice-supported state density | DensityBudget.lean:204 (`budget_stateDensityRep_le`) |
| — | lattice `Q = 2∏kᵢ`, `(e+1)/(2kᵢ) ∈ Q⁻¹ℕ_{>0}`, spacing `1/Q`, finite `latticeBelow` | SpectralLattice.lean:37 (`ratio_mem_lattice`) |
| — | polynomial ℓ¹ algebra: `|P(u)| ≤ ‖P‖₁` on the cube, `‖PQ‖₁ = ‖P‖₁‖Q‖₁`, `‖P^p‖₁ ≤ ‖P‖₁^p`, `fluct` | MonomialRep.lean:85 (`abs_eval_le_l1`), :149 (`l1_pow_le`) |
Low-spectrum tail replacement: `LowSpectrumTail.lean` (`tsum_logTailMoment_series` L48, `exp_le_rpow_const` L137, `abs_tailSeries_le` L396). Numerical checks: XXIV in d=1 to 2e-15; XXV in d=1 (L = 5/2): error × N^{5/2} ≈ 0.15 stable over N = 10…640.
Not formalised (Stage 4 — not authorised): analytic (non-polynomial) `ξ, η` (coefficient space with weighted ℓ¹ norm, monomial summability), `b ≠ 1`, identification of the coarse lattice with the paper's `Λ(h,k)`, the derivative dictionary `β^p fluctMoment = (−∂_μ)^i ∂_a^p S_μ(a)`.


## Completion statement (2026-09-07)
The scoped **§4 normal-block programme is complete** at the reviewed baseline `d65d48b` (Astra #24–#25; reviews
v1–v17): general machinery (Headlines VI–XIX), the assembled statistical example (XX–XX'' with the genuine-prior
lemmas), and the Abelian coefficient dictionary (XXI). Explicit non-claims: XX–XX'' are fixed-`θ` moment-generating-
function limits, not a formalised weak-convergence theorem for posterior laws; XXI is a real-axis Abelian coefficient
limit, not meromorphic continuation or an exact-pole-order theorem; the signed-weight statements are analytic, the
posterior interpretation needs `ρ ≥ 0`. The remaining paper material (full Taylor-tree expansion, complex Mellin
continuation, the boundary tail, `eq:flucttreeterms`, the resolution-based §4.3 application) is **outside the
completed work package**. Preferred separately authorised successor (Astra #25): posterior weak convergence of the
law of `√n x₀x₁` to `N(z,1)` for deterministic phases (reconnaissance first: Lévy/Curtiss route vs direct
test-function route); a cheap robustness variant is available via Mathlib's CLT (i.i.d. mean-0 variance-1 data).

Pinned commit for the mirror `grammar_lean.tex`: see `\laplaceLeanCommit` there. All statements
zero `sorry`/`axiom`; independent statement-level reviews v1–v15 in `tide-log/gpt6_fidelity_review_v*.md`.
Conventions: boxes `(0,1]^d` (`unitBox`), `(-1,1]^d` (`symBox`); `ratioExp h k i = (hᵢ+1)/(2kᵢ)`,
`λ = min`, `J` the minimisers, `m = multCount`; chart variable `N` (paper's `√n`), `p = 2λ`;
`phaseMoment β p a = ∫₀^∞ s^{p-1} e^{-βs²+βas} ds` is the paper's `J_p(a) = S_{p/2}(a)/2`.

| Headline | Statement | File:line |
|---|---|---|
| VI  | bare equal-ratio normal moment asymptotic | HeadlineMonomial.lean:73 |
| VII | bare mixed-ratio (face) asymptotic, `minRatio` wrapper | HeadlineMonomialMixed.lean:58 |
| VIII | continuous amplitude: face-supported functional | HeadlineAmplitude.lean:85 |
| IX  | tangential integration against a compact set | HeadlineTangential.lean:38 |
| X   | stochastic `1/log N` regime (d = 2) | HeadlineStochasticLog.lean:37 |
| XI  | signed reflections, zero phase (parity) | SymmetricAmplitudeAsymptotic.lean:89 |
| XII | zero-phase unequal-exponent dictionary, `noLogConst` closed form | QuadraticMixedBridge.lean:115 |
| XIII | phase-dressed leading term, general d (face integral of `η(πu) J_p(ξ(πu))`) | HeadlinePhase.lean:117 |
| XIII' | equal ratios: corner value `η(0) J_p(ξ(0)) / ((d-1)! ∏ kᵢ)` (= paper's `A_p` at d = 2) | HeadlinePhase.lean:138 |
| XIII'' | uniform cutoff `(0,b]^d` | PhaseCutoff.lean:117 |
| XIV | per-stratum posterior quotient (deterministic) | PhasePosterior.lean:148 |
| XV  | conditional finite chart assembly (deterministic) | HeadlineAssembly.lean:51 |
| XVI | random phases and amplitudes: `F_{N_n}(X_n) ⇒ F(Z)` | PhaseRandomTransfer.lean:222 |
| XVII | random per-stratum posterior quotient | PhaseRandomPosterior.lean:99 |
| XVIII | assembled stochastic posterior quotient over charts | HeadlineStochasticAssembly.lean:102 |
| XIX | symmetric box with phase (signed `x^h` / absolute `|x|^h`) | HeadlineSymmetricPhase.lean:102 / 127 |
| XX  | end-to-end example: model `N(x₀x₁,1)` on `(-1,1]²`, posterior MGF of `√n x₀x₁` → `e^{zθ+θ²/2}` (exact likelihood identity at L152) | NormalCrossingModel.lean:278 |
| XX' | Gaussian data `Yᵢ` iid `N(0,1)`: `E_post[e^{θ√n x₀x₁}] − e^{Zₙθ+θ²/2} → 0` in probability (uniform-in-phase MGF at L255, Chebyshev at L350) | NormalCrossingData.lean:361 |
| XX'' | Gaussian data: `E_post[e^{θ√n x₀x₁}] ⇒ e^{Zθ+θ²/2}`, `Z ~ N(0,1)` (exact law `Zₙ ~ N(0,1)` at L123) | NormalCrossingLaw.lean:178 |
| XXI | real-axis Abelian limit for the leading Mellin (zeta) coefficient: `s^m ∫ η u^{2k(-λ+s)+h} → ∏_J 1/(2kᵢ) ∫ η(πu) ∏_{∉J} u^{h-2kλ}` as `s → 0⁺` (`η` continuous on the closed cube; no continuation/pole-order claim); `η = 1` gives the paper's `a_{-m}` (L303); Γ-dictionary with Headline VIII (L338) | MellinCoefficient.lean:285 |
| — | genuine prior (`ρ ≥ 0`, `ρ(0) > 0`): evidence positive at every sample size; posterior mean of `1` is `1` | NormalCrossingPrior.lean:87 / 102 |
| — | formal face-vs-corner counterexample (`5√π/12 ≠ √π/4`) | MixedRatioCounterexample.lean:126 |
| — | abstract assembly (min exponent, max log multiplicity) | ChartAssembly.lean:142 |

Earlier headlines (I–V, d = 2 Taylor tree, coefficient CLT, chart posterior limit, `1/log N` regime)
are in `Headline.lean`, `HeadlinePosterior.lean` and their neighbours.

## What the theorems assume (hand-off)
See `projects/grammar/staging/normal-block-report-v3.pdf` §Assumptions: the chart decomposition is an
external input ("conditional" = assuming); densities are deterministic and strictly positive; no
remainders; joint convergence of the empirical phases is a hypothesis; the stochastic results are weak
limits, not expansions with rates; selection is at the normalised scale and signed numerators may cancel.
Headlines XX/XX'/XX'' concern one concrete statistical model with no chart-decomposition or likelihood-remainder
hypothesis (XX assumes `Zₙ → z`; XX'/XX'' assume i.i.d. `N(0,1)` data). They are fixed-`θ` moment-generating-function
limits, not weak convergence of the posterior law, with no rate; the weight `ρ` may be signed (`ρ(0) > 0` only), and for a
genuine prior (`ρ ≥ 0` on the box) the evidence is positive at every sample size (`NormalCrossingPrior.lean`). Reviews v16–v17.
