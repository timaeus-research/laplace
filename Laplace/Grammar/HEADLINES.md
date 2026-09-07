# Grammar §4 formalisation — headline index (general-dimensional normal block)

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
| XX  | end-to-end example: model `N(x₀x₁,1)` on `(-1,1]²`, posterior MGF of `√n x₀x₁` → `e^{zθ+θ²/2}` (exact likelihood identity at L149) | NormalCrossingModel.lean:275 |
| XX' | Gaussian data `Yᵢ` iid `N(0,1)`: `E_post[e^{θ√n x₀x₁}] − e^{Zₙθ+θ²/2} → 0` in probability (uniform-in-phase MGF at L255, Chebyshev at L350) | NormalCrossingData.lean:361 |
| XX'' | Gaussian data: `E_post[e^{θ√n x₀x₁}] ⇒ e^{Zθ+θ²/2}`, `Z ~ N(0,1)` (exact law `Zₙ ~ N(0,1)` at L123) | NormalCrossingLaw.lean:178 |
| — | genuine prior (`ρ ≥ 0`, `ρ(0) > 0`): evidence positive at every sample size; posterior mean of `1` is `1` | NormalCrossingPrior.lean:86 / 101 |
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
genuine prior (`ρ ≥ 0` on the box) the evidence is positive at every sample size (`NormalCrossingPrior.lean`). Review v16.
