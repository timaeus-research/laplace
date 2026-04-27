# laplace

A Lean 4 + Mathlib formalisation of the anharmonic Laplace asymptotic from
the SLT Susceptibility Primer (Baker et al., 2025).

## Headline theorem

For the anharmonic potential
`L(x) = (λ/2)x² + (α/6)x³ + (γ/24)x⁴` with `λ > 0`, `γ > 0`,
and the discriminant condition `α² < 3λγ`,

```lean
theorem cov_anharmonic_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto
      (fun t : ℝ =>
        t ^ 2 *
          Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
            (fun x => x ^ 2) (fun x => x))
      Filter.atTop
      (nhds (-2 * alpha / lam ^ 3))
```

i.e. `Cov_t[x², x] = -2α/(λ³ t²) + o(t⁻²)` as `t → ∞`. This is equation
(4.10) in the primer.

The full theorem lives at the end of
[`Laplace/OneD/IntegralRemainder.lean`](Laplace/OneD/IntegralRemainder.lean).

## Status

- 3279 lines of Lean 4 + Mathlib.
- 60+ proved theorems.
- **0 sorries, 0 axioms, 0 `native_decide`.**
- `lake build` succeeds in ~20s (warm cache).

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

| File | Lines | Role |
|---|---|---|
| [`Laplace/Basic.lean`](Laplace/Basic.lean) | 22 | Roadmap |
| [`Laplace/Gibbs.lean`](Laplace/Gibbs.lean) | 65 | `partitionFunction`, `gibbsExpectation`, `gibbsCov` |
| [`Laplace/ScalarBound.lean`](Laplace/ScalarBound.lean) | 179 | The Taylor-1 cornerstone |
| [`Laplace/OneD/GaussianMoments.lean`](Laplace/OneD/GaussianMoments.lean) | 231 | Standard 1D Gaussian moments |
| [`Laplace/OneD/Harmonic.lean`](Laplace/OneD/Harmonic.lean) | 165 | Closed-form harmonic Gibbs expectations |
| [`Laplace/OneD/Anharmonic.lean`](Laplace/OneD/Anharmonic.lean) | 140 | Anharmonic potential + coercivity |
| [`Laplace/OneD/TailBound.lean`](Laplace/OneD/TailBound.lean) | 532 | Mill's-ratio family of tail bounds |
| [`Laplace/OneD/Localisation.lean`](Laplace/OneD/Localisation.lean) | 164 | Harmonic-Gibbs tail localisation |
| [`Laplace/OneD/Rescaling.lean`](Laplace/OneD/Rescaling.lean) | 230 | Rescaling identity + uniform Gaussian decay |
| [`Laplace/OneD/IntegralRemainder.lean`](Laplace/OneD/IntegralRemainder.lean) | 1541 | Pointwise + integrability + integral bound + asymptotics |

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
- The mathematical content tracks the SLT Susceptibility Primer (Baker et
  al., 2025) and depends throughout on
  [Mathlib](https://github.com/leanprover-community/mathlib4).
