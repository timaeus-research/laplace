# laplace

A Lean 4 + Mathlib formalisation of the Laplace asymptotics of Gibbs
expectations, covariances and susceptibilities from the SLT Susceptibility
Primer (Elliott & Murfet, 2026).

## Main theorems

[![Solutions.lean](https://github.com/timaeus-research/laplace/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/timaeus-research/laplace/actions/workflows/comparator.yml)

Theorems are stated in [Statements.lean](Statements.lean) and fulfilled in
[Solutions.lean](Solutions.lean), checked with
[leanprover/comparator](https://github.com/leanprover/comparator)
([config](comparator.json)).

| Citation | Statement | Solution |
|---|---|---|
| Primer, `eq:cov_anharmonic_1d` (eq. (4.10) compiled); limit only — the primer's `O(t⁻³)` rate is not pinned | `t²·Cov_t[x², x] → -2α/λ³` for the 1D anharmonic potential `(λ/2)x² + (α/6)x³ + (γ/24)x⁴` ([statement](Statements.lean#L179)) | [solution](Solutions.lean#L172) |
| new; the `κ₃` of *Clusters to Circuits*, Cor. `prop:cross_susc` | `t²·κ₃(x, x, x) → -α/λ³` — the anharmonic three-point function ([statement](Statements.lean#L201)) | [solution](Solutions.lean#L194) |
| new; identity from *Clusters to Circuits*, Cor. `prop:cross_susc` | `t·∂ₕCov_h(x,x)\|₀ → α/λ³` — the anharmonic cross-susceptibility (FDT) asymptote ([statement](Statements.lean#L227)) | [solution](Solutions.lean#L220) |
| Primer, Lemma `lem:laplace_cov` | `Cov_t[φ, ψ] = (1/t)·⟨∇φ, Σ∇ψ⟩ + O(t⁻²)`, multivariate, sharp rate ([statement](Statements.lean#L259)) | [solution](Solutions.lean#L252) |
| Primer, Lemma `lem:laplace_exp` | `⟨φ⟩_t = (1/2t)·[tr(AΣ) - (Σ∇φ)·(T:Σ)] + O(t⁻²)`, explicit coefficient ([statement](Statements.lean#L293)) | [solution](Solutions.lean#L286) |
| Primer, Lemma `lem:laplace_cov2` | `t²·Cov_t[φ, ψ]` → the explicit four-term tensor coefficient `½tr(AΣBΣ) + ½(Σb)·(Φ:Σ) - ½b^⊤ΣAΣ(T:Σ) - ½(Σb)·(T:(ΣAΣ))`, at rate `O(1/t)` ([statement](Statements.lean#L327)) | [solution](Solutions.lean#L320) |
| new (degenerate/singular regime) | `⟨x^(2j₁) y^(2j₂)⟩_t ~ C·t^(-j₁/k₁ - j₂/k₂)` for the separable potential `x^(2k₁)/(2k₁)! + y^(2k₂)/(2k₂)!` ([statement](Statements.lean#L358)) | [solution](Solutions.lean#L351) |

To verify that `Solutions.lean` fulfills `Statements.lean` in a sandboxed
build, ensure `go` and `elan` are installed (Linux, Landlock ≥ 5.13), then
from the repo root:

```bash
git clone --depth 1 https://github.com/Zouuup/landrun && (cd landrun && go build -o landrun ./cmd/landrun)
git clone --depth 1 --branch "$(sed 's|leanprover/lean4:||' lean-toolchain)" https://github.com/leanprover/lean4export && (cd lean4export && lake build)
git clone --depth 1 https://github.com/leanprover/comparator
sed -i 's/args ++ #\[spawnArgs.cmd\] ++ spawnArgs.args/args ++ #["--", spawnArgs.cmd] ++ spawnArgs.args/' comparator/Main.lean  # missing flag terminator, pending upstream fix
(cd comparator && lake build comparator)

export PATH="$PWD/landrun:$PWD/lean4export/.lake/build/bin:$PATH"
lake exe cache get
lake env comparator/.lake/build/bin/comparator comparator.json  # expect: Your solution is okay!
```

## Status

- ~46k lines of Lean 4 + Mathlib across the 1D, 2D and multi-D tracks.
- **0 sorries, 0 axioms, 0 `native_decide`** (the deliberate `sorry` bodies
  of `Statements.lean` are exempt by design; each is proved in
  `Solutions.lean`).
- `lake build` succeeds (warm cache).

Audit with `scripts/sorries`.

## Build

Requires [`elan`](https://github.com/leanprover/elan) (to manage the Lean
toolchain) and `git`. The toolchain is pinned to `leanprover/lean4:v4.29.0`
in `lean-toolchain`; Mathlib is pinned to the matching `v4.29.0` tag in
`lakefile.toml`.

```bash
lake exe cache get   # download prebuilt Mathlib oleans (~1 min)
lake build           # build the Laplace library (~20s warm)
```

Pulling the Mathlib cache is essential. Building Mathlib from source takes
30+ minutes.

## File map

### 1D track (anharmonic potential)

| File | Role |
|---|---|
| [`Laplace/Basic.lean`](Laplace/Basic.lean) | Roadmap |
| [`Laplace/Gibbs.lean`](Laplace/Gibbs.lean) | `partitionFunction`, `gibbsExpectation`, `gibbsCov` |
| [`Laplace/ScalarBound.lean`](Laplace/ScalarBound.lean) | The Taylor-1 cornerstone |
| [`Laplace/OneD/GaussianMoments.lean`](Laplace/OneD/GaussianMoments.lean) | Standard 1D Gaussian moments |
| [`Laplace/OneD/Harmonic.lean`](Laplace/OneD/Harmonic.lean) | Closed-form harmonic Gibbs expectations |
| [`Laplace/OneD/Anharmonic.lean`](Laplace/OneD/Anharmonic.lean) | Anharmonic potential + coercivity |
| [`Laplace/OneD/TailBound.lean`](Laplace/OneD/TailBound.lean) | Mill's-ratio family of tail bounds |
| [`Laplace/OneD/Localisation.lean`](Laplace/OneD/Localisation.lean) | Harmonic-Gibbs tail localisation |
| [`Laplace/OneD/Rescaling.lean`](Laplace/OneD/Rescaling.lean) | Rescaling identity + uniform Gaussian decay |
| [`Laplace/OneD/IntegralRemainder.lean`](Laplace/OneD/IntegralRemainder.lean) | Pointwise + integrability + integral bound + asymptotics |

### Multi-D track (sharp covariance asymptotic)

| File | Role |
|---|---|
| [`Laplace/Multi/Basic.lean`](Laplace/Multi/Basic.lean) | `dot`, `gaussianWeight`, `quadForm`, abstract Gaussian hypotheses |
| [`Laplace/Multi/QuadraticApprox.lean`](Laplace/Multi/QuadraticApprox.lean) | `PotentialApprox`, `ObservableApprox` (local cubic remainder packages) |
| [`Laplace/Multi/GaussianDomination.lean`](Laplace/Multi/GaussianDomination.lean) | Coercivity ⟹ Gaussian-dominated rescaled weight |
| [`Laplace/Multi/RescaledIntegrals.lean`](Laplace/Multi/RescaledIntegrals.lean) | Polynomial-Gaussian moment integrability + uniform tail bounds |
| [`Laplace/Multi/GaussianIBP.lean`](Laplace/Multi/GaussianIBP.lean) | Multivariate IBP / parity for Gaussian against odd integrands |
| [`Laplace/Multi/Covariance.lean`](Laplace/Multi/Covariance.lean) | Weak-track `gibbsCov_first_order_rate_weak` (`O(t^{-3/2})`) |
| [`Laplace/Multi/CovarianceSharp.lean`](Laplace/Multi/CovarianceSharp.lean) | Sharp-track `gibbsCov_first_order_rate_sharp` (`O(t^{-2})`) |
| [`Laplace/Multi/CovarianceExplicit.lean`](Laplace/Multi/CovarianceExplicit.lean) | Explicit-coefficient `gibbsExpectation_first_order_rate_explicit` (`lem:laplace_exp`) and `gibbsCov_first_order_rate_explicit` (`lem:laplace_cov2`) |
| [`Laplace/Multi/Defs.lean`](Laplace/Multi/Defs.lean) | Statement vocabulary of the multi-D track (Mathlib-only import closure; shared with [Statements.lean](Statements.lean)) |

## Proof strategy

Following the rescaled-Gaussian-plus-global-remainder route under the
discriminant condition `α² < 3λγ`:

1. Scalar Taylor remainder: `|exp(-z) - (1-z)| ≤ (z²/2) · max(1, exp(-z))`.
2. Coercivity: `α² < 3λγ ⟹ L(x) ≥ c · x²`.
3. Rescaling identity: `t · L(u/√(λt)) = u²/2 + s_t(u)` with
   `s_t(u) = A u³/√t + B u⁴/t`.
4. Uniform Gaussian decay: `exp(-u²/2) · max(1, exp(-s_t(u))) ≤ exp(-c₀ u²)`.
5. Pointwise perturbation bound: `s_t(u)² ≤ C · (u⁶ + u⁸) / t`.
6. Master analytic theorem: `|∫ f(u) · (exp(-s_t(u)) - (1 - s_t(u))) du| ≤ K/t`.
7. Linearised decomposition:
   `∫ f · (1 - s_t) = M_n − (A/√t) M_{n+3} − (B/t) M_{n+4}`.
8. `J_n` and `I_n` asymptotics for `n = 0, 1, 2, 3` via the substitution
   `(√(λt))^{n+1} · I_n = J_n`.
9. Coefficient cancellation: `−5α/(2λ³) − (1/λ)·(−α/(2λ²)) = −2α/λ³`.

Steps 1–9 then assemble the headline theorem.

A more detailed walkthrough is in [`PROGRESS.md`](PROGRESS.md).

## Project guidance

[`CLAUDE.md`](CLAUDE.md) is the working playbook for AI-assisted
development on this repo. It covers the proof strategy, Mathlib API
references discovered along the way, and recurrent tactic gotchas.

## Tooling

- `scripts/lean-search` — Python wrapper around
  [leansearch.net](https://leansearch.net/) for semantic Mathlib search.
- `scripts/sorries` — audits `sorry`, `#exit`, `native_decide`, and `axiom`
  occurrences across the codebase.

## Acknowledgements

- The repo structure and AI-assisted formalisation discipline are modelled
  on Geoffrey Irving's [aks](https://github.com/girving/aks) Lean
  formalisation of the AKS primality theorem.
- Strategic guidance for the proof structure and several key tactical
  unblocks were provided by GPT-5.5 Pro consultations, recorded in
  [`gpt_responses/`](gpt_responses/).
- The mathematical content tracks the SLT Susceptibility Primer (Elliott &
  Murfet, 2026) and depends throughout on
  [Mathlib](https://github.com/leanprover-community/mathlib4).
