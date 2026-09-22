> **Archived.** This repository was merged into the resolution monorepo on 2026-09-22:
> it now lives at [https://github.com/resolutionorg/resolution/tree/main/lean/laplace](https://github.com/resolutionorg/resolution/tree/main/lean/laplace)
> (`lean/laplace/`), history included.  An old commit SHA maps to its new one via
> `lean/.monorepo/commit-map/laplace.txt` there.  Nothing here is maintained.

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

- ~68k lines of Lean 4 + Mathlib across the 1D, 2D and multi-D tracks
  (`Laplace/OneD/`, `Laplace/TwoD/`, `Laplace/Multi/` plus the top-level
  identifiability modules).
- **0 sorries, 0 axioms, 0 `native_decide`** (the deliberate `sorry` bodies
  of `Statements.lean` are exempt by design; each is proved in
  `Solutions.lean`).
- `lake build` succeeds (warm cache).

Audit with `scripts/sorries`.

## Build

Requires [`elan`](https://github.com/leanprover/elan) (to manage the Lean
toolchain) and `git`. The toolchain is pinned to `leanprover/lean4:v4.33.0`
in `lean-toolchain`; Mathlib is pinned to the matching `v4.33.0` tag in
`lakefile.toml`, alongside `resolution-common` and
`threepoint`.

```bash
lake exe cache get   # download prebuilt Mathlib oleans (~1 min)
lake build           # build the Laplace library (~20s warm)
```

Pulling the Mathlib cache is essential. Building Mathlib from source takes
30+ minutes.

## File map

The two tables below cover the primer core (the modules behind
`Statements.lean`). The bulk of the library is the germbij identifiability
programme built on top of it — singular identifiability (`Laplace/Pencil.lean`,
`Sector.lean`, `Identifiability.lean`, `Turnkey.lean`, `Analytic.lean`,
`Decay.lean`, `Anchoring.lean`, `OnePointAnchoring.lean` and their
`Laplace/Multi/` counterparts), 1D jet/germ recovery (`Laplace/OneD/*Recovery*.lean`,
`FlatInvisible.lean`), multivariate Hessian/tensor recovery and jet induction
(`Laplace/Multi/HessianRecovery.lean`, `JetInduction.lean`, `MonomialTests.lean`),
the forward all-orders expansion (`Laplace/Multi/ForwardTheorems.lean`), and
the degenerate/separable tracks (`Laplace/Multi/Separable*.lean`,
`Laplace/TwoD/`). Per-tide entries are in [`tide-log/`](tide-log/) and
[`retrospectives/`](retrospectives/).

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
| [`Laplace/Multi/GaussianLLC.lean`](Laplace/Multi/GaussianLLC.lean) | Gaussian LLC identity: `⟨½ uᵀHu⟩ = ½ Σ H_ij (P⁻¹)_ij` under `exp(-½ uᵀ(tH + γ)u)`, `t⟨K⟩ = d/2` at `γ = 0` |

### Sampler track (SGLD on a Gaussian target)

| File | Role |
|---|---|
| [`Laplace/Sampler/Lyapunov.lean`](Laplace/Sampler/Lyapunov.lean) | Discrete Lyapunov equation `X = A X Aᵀ + N`: diagonal solver, transport by orthogonal diagonalisation (`orthoOf`, `spectral_real`), finite-time identity `X_k - S = A^k (X_0 - S) (Aᵀ)^k`, AR(1) variance |
| [`Laplace/Sampler/ULA.lean`](Laplace/Sampler/ULA.lean) | ULA law `(P - (h/2)P²)⁻¹` (unique fixed point, positive definite, eigenbasis entries) and the minibatch entry formula `(2hδ_ij + h²t²C̃_ij)/(h(p_i+p_j) - h²p_ip_j)` for arbitrary `C` |

### Patterning track (the *Patterning flow* working note)

Algebraic cores of the propositions of `learning-theory/local/directsgld/main.tex`; the
asymptotic and probabilistic reductions leading to these identities (Laplace expansions,
stationarity of SDEs, RLCT asymptotics) are stated in the note and not formalised. Each file
header says which parts are covered.

| File | Role |
|---|---|
| [`Laplace/Patterning/Horizon.lean`](Laplace/Patterning/Horizon.lean) | Finite-horizon response of linearised gradient descent to a constant force: `δ_T = -ε F_T(H) b`, `F_T = η ∑_{k<T} (1 - ηH)^k`, eigen-form `(1 - (1 - ηλ)^T)/λ`, null-space form `ηT`; the gradient-flow filter `(1 - e^{-λt})/λ` as an ODE solution; the 26% saturation mismatch of Cor. 3.3 (Prop. 3.1) |
| [`Laplace/Patterning/Profile.lean`](Laplace/Patterning/Profile.lean) | Short-chain ULA profile of a Gaussian target: per-mode variance, first step `½ nβ tr(H) ε`, plateau, small-step limit `½ ∑ λ_i/(λ_i + ρ)` (Prop. 12.1), finite-chain matrix identity (Prop. 3.2), spectral trace identities for `tr(H (H+ρ)⁻¹)` and `tr(H S_ε)` |
| [`Laplace/Patterning/Direct.lean`](Laplace/Patterning/Direct.lean) | Regime-1 direct force: `χχᵀ = S/n`, minimal-norm solution `ω_P` of the fundamental equation, mean zero, force `-C R A S⁻¹ dμ`, the `C = H` corollary (Prop. 4.1, Cor. 4.2) |
| [`Laplace/Patterning/SGDLyapunov.lean`](Laplace/Patterning/SGDLyapunov.lean) | OU model of SGD: `tr(HΣ) = (η/2B) tr C`, isotropic solution for `C = cH`, discrete diagonal fixed point `ηc/(B(2 - ηλ_i))` and its exact `O(η³)` remainder, and the invariance of the centred Gaussian with that covariance under the linearised SGD step with Gaussian minibatch noise (Prop. 12.2) |
| [`Laplace/Patterning/Virial.lean`](Laplace/Patterning/Virial.lean) | Virial balance `tr(PX) = d + (h/2) tr(P²X)` for the ULA law, 1D Gibbs virial `⟨x U'⟩ = 1` by the whole-line FTC, degree decomposition (Prop. 12.4) |
| [`Laplace/Patterning/FourGon.lean`](Laplace/Patterning/FourGon.lean) | Population TMS at the 4-gon: exact frozen loss with the dead unit at `(x, y)`, `r⁴/15` at uniform `h`, ray form `a(θ;h) r² + (h₄/3) r⁴`, sublevel volume `π √(15ε)` (Prop. 11.1 (ii)–(iv)) |
| [`Laplace/Patterning/FourGonGibbs.lean`](Laplace/Patterning/FourGonGibbs.lean) | Gibbs moments of the dead component `K = r⁴/15` on `ℝ²` by polar coordinates and Gamma integrals: `Z(t)`, the exact `t ⟨K⟩_t = ½` for every `t`, and `⟨r⟩_t = Γ(3/4) π^{-1/2} (15/t)^{1/4}` (Prop. 11.1 (iii)) |
| [`Laplace/Patterning/Jacobi.lean`](Laplace/Patterning/Jacobi.lean) | Jacobi's formula from the Leibniz expansion: `d/ds det H(s) = tr(adj H · H')`, `d/ds log det H = tr(H⁻¹ H')`, the column-replacement sum `∑ᵢ det(H[i ← B·ᵢ]) = tr(adj H · B)`, and the Prop. 5.2 identification `tr(Σ(B - H + T·v)) = tr(BΣ) - d + (T:Σ)·v` (Lemma 5.1) |
| [`Laplace/Patterning/RadialVirial.lean`](Laplace/Patterning/RadialVirial.lean) | Virial identity for radial potentials in the plane, `∫₀^∞ r² U' e^{-U} = 2 ∫₀^∞ r e^{-U}` by the FTC on `(0,∞)`, with quartic-dominated integrability and decay; the localised 4-gon law `t⟨K⟩_{t,γ} = ½ - (γ/4)⟨r²⟩_{t,γ}` (Prop. 11.1 (iii), Prop. 12.4 in the plane) |
| [`Laplace/Patterning/GaussianFourth.lean`](Laplace/Patterning/GaussianFourth.lean) | Gaussian moments by Stein's identity in the direction `Σ e_a` (`stein_invDir`): second moments, the Isserlis fourth moment `E[x_a x_b x_c x_e] = Σ_ab Σ_ce + Σ_ac Σ_be + Σ_ae Σ_bc` (general `Σ = H⁻¹` and the standard Gaussian), the covariance of two quadratic forms `Cov(⟪x,Ax⟫,⟪x,Bx⟫) = tr(AΣBΣ) + tr(AΣBᵀΣ)` with the symmetric wrapper `Cov(½⟪x,Ax⟫, ½⟪x,Bx⟫) = ½ tr(AΣBΣ)`, the cubic–linear term `E[(gᵀx) ⅙ T(x,x,x)] = ½ (Σg)ᵀ(T:Σ)` for symmetric `T`, odd moments vanish, `Cov(aᵀx, gᵀx) = aᵀΣg` and `E[⟪x,Ax⟫ gᵀx] = 0` (Prop. 8.1) |
| [`Laplace/Patterning/FourGonStationary.lean`](Laplace/Patterning/FourGonStationary.lean) | `[z]_+²` is `C¹` with derivative `2[z]_+`; the Gateaux derivative of `ℓ_i` along `W + sV`; every per-feature gradient vanishes at the 4-gon, so `L_h` is stationary for every `h` and the checkpoint-frozen force is zero (Prop. 11.1 (i)) |
| [`Laplace/Patterning/FourGonModel.lean`](Laplace/Patterning/FourGonModel.lean) | Eq. *(featureloss)* from the model: `ℓ_i(W) = ∫₀¹ ‖x e_i − ReLU(WᵀW x e_i)‖² dx` (the bias-free single-feature case of tms-lean's closed-form TMS potential) |
| [`Laplace/Patterning/FourGonSaddle.lean`](Laplace/Patterning/FourGonSaddle.lean) | The descending path of Prop. 11.1 (v) as an exact polynomial, `L_h(W(r)) − L_h(4-gon) = −r⁴/15 + r⁶/15 + 103r⁸/1920` for `0 < r < 1`, negative for `r < 1/2`: the 4-gon is a degenerate saddle of the full loss |
| [`Laplace/Patterning/VirialMulti.lean`](Laplace/Patterning/VirialMulti.lean) | The virial identity in `d` dimensions for a `C¹` potential, `∫ (δ·∇U) e^{-U} = d ∫ e^{-U}`, by Mathlib's multivariate integration by parts coordinatewise; normalised form `E[δ·∇U] = d`; the localised form `nβ E[δ·∇K] + γ E‖δ‖² = d` (Prop. 12.4) |
| [`Laplace/Patterning/HorizonNonlinear.lean`](Laplace/Patterning/HorizonNonlinear.lean) | The nonlinear GD recursion `w_{k+1} = w_k − η(G(w_k) + ε b(w_k))` is differentiable in `ε` at `0` with derivative the linearised iterate, so `w_T − w* = −ε F_T(H) b(w*) + o(ε)` (the first-order content of Prop. 3.1) |
| [`Laplace/Patterning/MovingMinimizer.lean`](Laplace/Patterning/MovingMinimizer.lean) | The moving critical point of Prop. 5.2 by the inverse function theorem: existence of `w*(s)` with `w*'(0) = −H⁻¹g`, the chain rule for the moving Hessian, and `d/ds log det H(s)|₀ = tr(BΣ) − d − (Σg)ᵀ(T:Σ)` |
| [`Laplace/Patterning/PosteriorSusceptibility.lean`](Laplace/Patterning/PosteriorSusceptibility.lean) | Eq. (chi_laplace) from the primer's formalised Lemma 4.4: the quadratic localiser preserves the jet-approximation package with Hessian `H + ρ·id`, so `Cov_t[φ, ℓ] = aᵀ(H+ρ)⁻¹g/t + O(t⁻²)` and `χ = −(1/n) aᵀ(H+ρ)⁻¹g + O((nβ)⁻²)` at fixed `ρ` |
| [`Laplace/Patterning/VolumeExponent.lean`](Laplace/Patterning/VolumeExponent.lean) | Uniqueness of the exponents `(λ, m)` of a volume asymptotic `c ε^λ (−log ε)^{m−1}` under a two-sided sandwich `V(ε/c₂) ≤ W(ε) ≤ V(ε/c₁)`, and its application to the sublevel volumes of `K` and the reweighted `K_w` (the learning-coefficient conclusion of Prop. 6.1, given the asymptotics) |
| [`Laplace/Patterning/IsotropicExpansion.lean`](Laplace/Patterning/IsotropicExpansion.lean) | The scaling expansion of Prop. 8.1 for cubic polynomial observables under `N(0, σ²Σ)`: dilation `E_{σ⁻²H}[f] = E_H[f(σ·)]`, parity (odd cross terms vanish), bilinearity of the Gaussian covariance on polynomials, and `Cov = σ² aᵀΣg + σ⁴ C₄ + σ⁶ C₆` exactly, with `C₄ = ½tr(AΣBΣ) + ½(Σa)ᵀ(R:Σ) + ½(Σg)ᵀ(Q:Σ)` for symmetric tensors; hence the `O(‖Σ‖²)` and `O(‖Σ‖³)` remainders for such observables |
| [`Laplace/Patterning/OrnsteinUhlenbeck.lean`](Laplace/Patterning/OrnsteinUhlenbeck.lean) | The Ornstein–Uhlenbeck model of SGD as its Gaussian transition semigroup `N(e^{-sH} m, Σ_s)`, `Σ_s = Σ − e^{-sH} Σ e^{-sH}`: the Lyapunov ODE `Σ_s' = D − HΣ_s − Σ_s H`, the semigroup identity, `Σ_s ⪰ 0`, invariance of `N(0, Σ)` for `HΣ + ΣH = D`, the law from the minimiser, relaxation `e^{-sH} → 0`, `Σ_s → Σ` and `Σ ⪰ 0` for positive definite `H` (Prop. 12.2) |
| [`Laplace/Patterning/OUPathwise.lean`](Laplace/Patterning/OUPathwise.lean) | The OU equation `dX = −HX ds + σ dw` driven by an arbitrary continuous path, in integral form `X_s = x₀ − ∫₀ˢ H X_u du + σ w_s`: the variation-of-constants solution `ouSol` (stochastic integral written by integration by parts), existence, uniqueness among continuous solutions, and the covariance integral `∫₀ˢ e^{-uH} D e^{-uH} du = Σ − e^{-sH} Σ e^{-sH}` under the Lyapunov identity |
| [`Laplace/Patterning/OUIncrement.lean`](Laplace/Patterning/OUIncrement.lean) | Itô-type increment sums `∑ₖ F(uₖ)(w(uₖ₊₁) − w(uₖ))` along a continuous path converge to the integration-by-parts expression (Abel summation plus a mesh estimate); left Riemann sums of a continuous function converge to the integral; the OU increment sums converge to `X_s − e^{-sH} x₀` |
| [`Laplace/Patterning/OUBrownian.lean`](Laplace/Patterning/OUBrownian.lean) | Brownian motion as a hypothesis package `IsBrownianVec` (centred Gaussian process, covariance `δᵢⱼ min(s,t)`, continuous paths); the increment sums are Gaussian with variance `mesh · ∑ₖ tᵀ E_{s−uₖ} σσᵀ E_{s−uₖ} t`; almost sure convergence to the pathwise solution; **the marginal law** `X_s ∼ N(e^{-sH} x₀, ∫₀ˢ e^{-uH} σσᵀ e^{-uH} du)` via characteristic functions and dominated convergence, and its identification with the transition kernel `ouStep` under `HΣ + ΣH = σσᵀ` (Prop. 12.2, the SDE side) |
| [`Laplace/Patterning/BrownianVecInstances.lean`](Laplace/Patterning/BrownianVecInstances.lean) | `IsBrownianVec` is the standard notion: `d` independent copies of Mathlib's real Brownian motion `IsBrownianReal`, assembled coordinatewise, satisfy it (`isBrownianVec_of_iIndepFun`, via `iIndepFun.hasGaussianLaw`); the one-dimensional bridge `isBrownianVec_of_isBrownianReal` |
| [`Laplace/Patterning/PrimerNLO.lean`](Laplace/Patterning/PrimerNLO.lean) | The primer's next-to-leading covariance formula, eq. (primer_nlo) of the note: `t² Cov_t(K, ℓᵢ − Lₙ) → ½[tr(BᵢΣ) − d] − ½(Σgᵢ)ᵀ(T:Σ)` at rate `O(1/t)`, as an instance of the seabed's `covV_first_order_rate_posDef` (Multi/CovKClosedForm.lean) for the centred perturbation with Hessian `Bᵢ − H` |
| [`Laplace/Patterning/OUMarkov.lean`](Laplace/Patterning/OUMarkov.lean) | **The Markov property of the OU process.** Restart identity `X_{s+r} = e^{-rH} X_s + X⁰_r(w^{(s)})` for every continuous path (by uniqueness); the restarted Brownian motion is a Brownian motion; the restart noise has law `N(0, C_r)` and is independent of `X_s` (past and future Brownian increments are uncorrelated, hence independent, and independence passes to a.s. limits through dual characteristic functions); the two-time law `Law(X_s, X_{s+r}) = Law(X_s) ⊗ₘ κ_r` with the Gaussian transition kernel `κ_r x = N(e^{-rH} x, C_r)`, and `condDistrib X_{s+r} X_s = κ_r` |
| [`Laplace/Patterning/FourGonSusceptibility.lean`](Laplace/Patterning/FourGonSusceptibility.lean) | **Susceptibility without gradient.** The exact susceptibility matrix of the dead unit at the degenerate 4-gon under the restricted Gibbs law `e^{−t r⁴/15}`: direction rows `Cov(d_α, ℓ_β) = (2/9π) cos(α−β) E[r³]` for *every* rotationally symmetric law (polar separation, angular integrals), hence `χ(dⱼ; hⱼ) = −c`, `χ(dⱼ; hⱼ₊₂) = +c`, zero for the orthogonal and dead features (`c > 0`): upweighting a feature pushes the dead unit away from it, at a point where every checkpoint-frozen force is zero (Prop. 11.1, Section 12 results) |
| [`Laplace/Patterning/FourGonSusceptibilityRadial.lean`](Laplace/Patterning/FourGonSusceptibilityRadial.lean) | The norm and excess-loss rows in closed form via the Gamma moments `E_t[rᵏ] = (t/15)^{-k/4} Γ((k+2)/4)/Γ(1/2)`: `χ(‖W₄‖; hⱼ) = −(t/60) Cov(r, r²) < 0` (log-convexity of Γ and Legendre duplication), `χ(‖W₄‖; h₄)`, `χ(K; hⱼ)`, `χ(K; h₄)`, the exact sum rule `∑ᵢ χ(K; hᵢ) = −t Var_t(K) = −1/(2t)`, and `t² Var_t(K) = ½`: `tK` is `Gamma(½, 1)`, the learning coefficient is both the mean and the variance of the tempered excess loss |
| [`Laplace/Patterning/FourGonPatterning.lean`](Laplace/Patterning/FourGonPatterning.lean) | **Which gap.** The pipeline's reweighting `ω* = (−1, −1, +1, +1, 0)/(2c)` solves `χ ω* = dμ` for the target gap, is mean-zero and minimal-norm; under `h₀ + ε ω*` the stability coefficient is `−(ε/6c)(cos θ|cos θ| + sin θ|sin θ|)`, negative exactly on the target half-plane `cos θ + sin θ > 0`, where the reweighted loss drops below the plateau along every ray |
| [`Laplace/Patterning/HorizonSecondOrder.lean`](Laplace/Patterning/HorizonSecondOrder.lean) | **Prop. 3.1 to second order.** With a quadratic Taylor bound `‖G(w) − H(w − w*)‖ ≤ L‖w − w*‖²` for the gradient field and a local Lipschitz bound for the force, `w_T(ε) − w* + ε F_T(H) b(w*) = O(ε²)` (`gdIter_isBigO_sq`): the error against the linearised iterate satisfies `e_{k+1} = (1 − ηH)e_k − η[G(w_k) − H(w_k − w*)] − ηε[b(w_k) − b(w*)]` and both brackets are `O(ε²)` once `w_k − w* = O(ε)`. This is the remainder behind "the pipeline is the split Euler step of the flow" |
| [`Laplace/Patterning/Positivity.lean`](Laplace/Patterning/Positivity.lean) | Bounded positive reweighting: sandwich `c₁K ≤ K_w ≤ c₂K`, equal zero sets, sublevel and measure sandwich (Prop. 6.1, sublevel core) |

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
