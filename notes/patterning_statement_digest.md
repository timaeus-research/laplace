# Patterning flow: statement digest for review

Branch `patterning-flow` (merged to `main`), `Laplace/Patterning/` (31 files). Every claim of the working note
*Patterning flow* (`learning-theory/local/directsgld/main.tex`, Overleaf `6aada9b9684134925b8ee562`)
that carries a blue margin marker is listed here with the Lean statement it links to, the
hypotheses that statement carries, and what is *not* covered. The purpose is a 20-minute read:
check that the Lean signature says what the note claims. Proof bodies are irrelevant to that check.
`lake build` clean, `scripts/sorries` reports 0 sorry / 0 axiom / 0 native_decide.

Conventions. `ι` is the parameter index (finite, decidable equality); `H` is a real matrix; the
Gaussian machinery lives on `EuclideanSpace ℝ ι` with `euclid A` the matrix `A` as a continuous
linear map; `gibbsCov L t φ ψ` is the covariance under `e^{-tL}`; `multivariateGaussian m S` is
Mathlib's Gaussian, a Dirac mass off the positive semidefinite cone.

## Section 3: finite horizon

| Note | Lean | Hypotheses | Not covered |
|---|---|---|---|
| Prop 3.1, linearised recursion `w_T − w* = −ε F_T(H) B ω` | `horizon_iterate_zero_filter` (Horizon.lean) | none: an identity for the affine recursion `δ ↦ (I − ηH)δ − εη b` from `0` | the reduction from the nonlinear recursion (see next row) |
| Prop 3.1, nonlinear recursion is tangent to the linear one | `gdIter_isLittleO`, `hasDerivAt_gdIter` (HorizonNonlinear.lean) | gradient field `G` with `G w* = 0` and Fréchet derivative `H` at `w*`; `b` differentiable at `w*` | |
| Prop 3.1, the `O(ε²)` remainder (the pipeline step is the linear response to second order) | `gdIter_isBigO_sq` (HorizonSecondOrder.lean) | quadratic Taylor bound `‖G(w) − H(w − w*)‖ ≤ L‖w − w*‖²` and Lipschitz bound `‖b(w) − b(w*)‖ ≤ K‖w − w*‖` on a ball around `w*` (a `C²` loss with Lipschitz Hessian) | the retrain-to-minimiser variant (moving minimiser) is still `o(s)`, not `O(s²)` |
| eq (horizon), eigen and null forms of `F_T` | `horizonFilter_mulVec_eigen`, `horizonFilter_mulVec_null` | eigenvector `Hv = λv`, `λ ≠ 0` (resp. `Hv = 0`) | |
| eq (horizon), gradient flow filter `(1 − e^{−λt})/λ` | `gradientFlow_filter`, `gradientFlow_filter_null` | `λ ≠ 0` | |
| eq (matching), `1.26 < 2(1 − e^{−1}) < 1.27` | `mismatch_ratio_bounds` | none | |

## Section 4: direct force

| Note | Lean | Hypotheses | Not covered |
|---|---|---|---|
| Prop 4.1, `χ ω_P = dμ` | `suscept_mulVec_omegaP` (Direct.lean) | `Rᵀ = R`; the Gram matrix `Aᵀ R C R A` (here `gram n A R G`) is invertible | |
| Prop 4.1, minimality of `ω_P` | `omegaP_minimal` | as above and `n ≠ 0`; minimality is in the sum-of-squares norm among all `ω'` with `χ ω' = dμ` | |
| eq (omega_P), mean zero | `omegaP_mean_zero` | the gradient matrix annihilates constants, `G 1 = 0` | |
| eq (omega_P), force `−C R A S⁻¹ dμ` | `force_omegaP` | none | |
| Cor 4.2, natural-gradient form | `natgrad_gram`, `natgrad_force`, `natgrad_target` | `C = H`, `R (H + ρ) = I`, Gram invertible; the target is hit up to `ρ Aᵀ R² A S⁻¹ dμ` | |

## Section 5: log-volume derivative and the primer's NLO formula

| Note | Lean | Hypotheses | Not covered |
|---|---|---|---|
| Lemma 5.1, Jacobi `d/ds log det H = tr(H⁻¹ H')` | `hasDerivAt_log_det`, `hasDerivAt_half_log_det` (Jacobi.lean) | entrywise differentiable matrix path, `det H(s₀) ≠ 0` | |
| eq (primer_nlo), `Cov_t[K, ℓᵢ − Lₙ] = (1/2t²)[tr(BᵢΣ) − d − (Σgᵢ)ᵀ(T:Σ)] + O(t⁻³)` | `primer_nlo_centered` (PrimerNLO.lean), instantiating `covV_first_order_rate_posDef` (Multi/CovKClosedForm.lean) | `V` regular with Hessian `P ≻ 0` and the quintic jet package `PotentialQuinticApprox`; `ψ` with gradient `g` and exact Hessian `B − P` (`ObservableTensorApprox`); rate `K/t` for `t ≥ T₀` | the `O(t⁻³)` is stated as `O(t⁻¹)` after multiplying by `t²`, i.e. the same thing; the expectation-level NLO is `gibbsExpectation_first_order_rate_explicit` |
| the uncentred form `Cov_t[K, ℓᵢ]` and `Var_t[K] = d/2t² + O(t⁻³)` | `covV_first_order_rate_posDef`, `varV_first_order_rate_posDef` | same packages | |
| Prop 5.2, moving critical point `w*'(0) = −H⁻¹g` and `d/ds log det H(s)` | `movingMinimizer_exists`, `logdet_response_deriv_at_minimizer` (MovingMinimizer.lean) | gradient field strictly differentiable at `(0, w*)` with derivative `(σ,u) ↦ σg + Hu`, `H` invertible; Hessian path differentiable with the displayed derivative | **criticality, not minimality**, of `w*(s)`; the identification `d/ds E_s[K] = −t Cov_t[K,h]` is the primer's formula (previous row) |

## Section 6: positivity and the RLCT

| Note | Lean | Hypotheses | Not covered |
|---|---|---|---|
| Prop 6.1, `c₁K ≤ K_ω ≤ c₂K`, equal zero sets, sublevel and volume sandwiches | `reweighted_sandwich`, `reweighted_eq_zero_iff`, `reweighted_volume_sandwich` (Positivity.lean) | weights in `[c₁, c₂]`, `0 < c₁`; losses `≥ 0` | |
| Prop 6.1, the RLCT and multiplicity are preserved | `reweighted_volume_exponent_unique`, `volume_exponent_unique` (VolumeExponent.lean) | *given* volume asymptotics `c ε^λ (−log ε)^{m−1}` for both losses, the pairs `(λ, m)` agree | the existence of such asymptotics for analytic `K` (Watanabe) is cited, not proved |
| Prop 6.2 (Girsanov) | none | | not formalised |

## Section 8: isotropic and Laplace-Gaussian estimators

| Note | Lean | Hypotheses | Not covered |
|---|---|---|---|
| Prop 8.1, Gaussian moments (Isserlis, quadratic-form covariances, cubic–linear term) | `integral_coord4_quadKernel`, `gaussianCovariance_qform_qform`, `gaussianExpectation_linForm_mul_cubicForm_div_six`, odd moments, `gaussianCovariance_linForm_linForm`, `integral_qform_mul_linForm_mul_quadKernel` (GaussianFourth.lean) | `N(0, H⁻¹)` with `H ≻ 0`; symmetric `B`, `Q` where stated | |
| Prop 8.1, `Cov_δ = σ² aᵀΣg + O(σ⁴)` with explicit constant | `gaussianCovariance_obs_scaled_bound` (IsotropicExpansion.lean) | `0 < σ ≤ 1`; observables are **cubic polynomials** `c + aᵀx + ½xᵀAx + ⅙Q(x,x,x)` | general smooth observables: Taylor remainders not formalised |
| Prop 8.1, zero-gradient case `Cov = σ⁴C₄ + σ⁶C₆` exactly, `C₄` as displayed | `gaussianCovariance_obs_scaled_zero_grad`, `gaussianCovariance_obs_scaled_symm` | cubic polynomial observables, symmetric tensors for the displayed `C₄` | |

## Section 11: the 4-gon

| Note | Lean | Hypotheses | Not covered |
|---|---|---|---|
| eq (featureloss) from the model | `featureLoss_eq_integral` (FourGonModel.lean) | bias-free `ReLU(WᵀW x eᵢ)`, `x ∈ [0,1]` | |
| Prop 11.1 (i), stationarity | `fourGon_featureLoss_stationary`, `fourGon_weightedLoss_stationary` (FourGonStationary.lean) | Gateaux derivative along every direction `V` | the loss is not `C¹` on the whole space; only directional derivatives at the 4-gon are claimed |
| Prop 11.1 (ii), frozen loss `r⁴/15` | `weightedLoss_fourGon_uniform` (FourGon.lean) | uniform weights | |
| Prop 11.1 (ii), ray form `a(θ;h)r² + (h₄/3)r⁴` | `weightedLoss_fourGon_ray` | `r ≥ 0` | |
| Prop 11.1 (iii), sublevel volume `π√(15ε)`, hence `λ = ½` | `volume_sublevel_quartic` | `ε > 0` | the RLCT is read off the volume; no Watanabe theory invoked |
| Prop 11.1 (iii), Gibbs moments `t⟨K⟩_t = ½`, `E_t[r]` | `deadQuartic_gibbs_excess`, `deadQuartic_gibbs_radius`, `partitionFunction_deadQuartic` (FourGonGibbs.lean) | `t > 0`; unlocalised | |
| Prop 11.1 (iii), localised law `t⟨K⟩ = ½ − (γ/4)E[r²]` | `deadQuartic_localized_virial` (RadialVirial.lean) | `t > 0`, `γ ≥ 0` | |
| Section 12 results, susceptibilities at the degenerate point: `χ(dⱼ; hⱼ) = −0.31`, `χ(dⱼ; hⱼ₊₂) = +0.32`, orthogonal and dead ≈ 0 | `deadChi_dir_same`, `deadChi_dir_opposite`, `deadChi_dir_orth`, `deadChi_dirObs_dead` (FourGonSusceptibility.lean), from `radialCov_dirObs_plusLoss` | restricted Gibbs law `e^{−t r⁴/15}`, `t > 0`; `χ(φ; hᵢ) := −(t/5) Cov_t(φ, ℓᵢ)`; exact value `c = (t/5)(2/9π)E_t[r³]` (= 0.310 at t = 1000) | the full-parameter-space chain (only the restricted one is computed) |
| the direction rows are the same for every rotationally symmetric ensemble up to `E[r³]` | `radialCov_dirObs_plusLoss` | any weight `G(‖z‖²)` | |
| `χ(‖W₄‖; hⱼ) = −0.08`, `χ(‖W₄‖; h₄) = +0.29`, `χ(K; hⱼ) = −0.0005`, `χ(K; h₄) = +0.0018` | `deadChi_normObs_alive(_neg)`, `deadChi_normObs_dead`, `deadChi_deadQuartic_alive`, `deadChi_deadQuartic_dead` (FourGonSusceptibilityRadial.lean) | closed forms in the Gamma moments; the sign of the norm row is proved, the sign of `χ(‖W₄‖; h₄)` depends on `t` and is not | |
| "summing to zero within noise" | `deadChi_deadQuartic_sum`: the row sums to `−1/(2t)` exactly (= −0.0005 at t = 1000), i.e. `−t Var_t(K)` with `t² Var_t(K) = ½` | | the note's text has been corrected |
| Which gap: `ω = (−0.48, −0.48, +0.49, +0.50, −0.03)`, every grown seed in the target half-plane | `omegaStar_solves`, `omegaStar_sum`, `omegaStar_minimal`, `stabilityCoeff_omegaStar`, `stabilityCoeff_omegaStar_neg_iff`, `weightedLoss_omegaStar_lt` (FourGonPatterning.lean) | exact `ω*`; destabilisation means `a(θ) < 0` on the frozen-component ray, and the loss drops below the plateau for small `r` | the SGD dynamics itself (growth in 32/40 seeds) is not modelled |
| Prop 11.1 (v), descending path `−r⁴/15 + r⁶/15 + 103r⁸/1920`, negative for `r < ½` | `weightedLoss_saddlePath`, `saddlePath_descends` (FourGonSaddle.lean) | `0 < r < 1` | |

## Section 12: effective dimension, SGD, OU, virial

| Note | Lean | Hypotheses | Not covered |
|---|---|---|---|
| Prop 12.1, `tr H(H+ρ)⁻¹ = ∑ λᵢ/(λᵢ+ρ)` and the plateau limit | `trace_mul_inv_spectral`, `plateau_tendsto_effdim` (Profile.lean) | orthogonal eigenbasis given explicitly; `λᵢ + ρ ≠ 0` | |
| eq (profile), finite-chain profile, first step, plateau | `profile_eq`, `profile_one`, `profile_tendsto`, `plateau_eq_trace` | stability `0 < ε(tλᵢ+γ) < 4` | |
| eq (chi_laplace), ULA covariance after `k` steps; invariance of `N(0, S)` | `ula_iterate_zero`; `ulaCov_invariant`, `gaussStep_iterate_zero` (Sampler/GaussianInvariance.lean) | `Pᵀ = P`, ULA denominator invertible; stability `hλᵢ < 2` | non-Gaussian targets |
| eq (sigma_rho), `χ = −β Cov` at leading order | `susceptibility_leading`, `posterior_susceptibility_leading` (PosteriorSusceptibility.lean) | the primer's jet packages for `L`, `φ`, `ℓ`; `ρ ≥ 0`; localiser scaled with `nβ` so `ρ` is fixed; explicit `O((nβ)⁻²)` | the note's fixed-`γ` limit is a different regime |
| Prop 12.2, `tr(HΣ) = (η/2B) tr C` and `E[K] = (η/4B) tr C` | `trace_mul_of_lyapunov`, `excessLoss_of_lyapunov` (SGDLyapunov.lean) | `HΣ + ΣH = (η/B)C` | |
| Prop 12.2, isotropic case `C = cH` | `lyapunov_isotropic`, `excessLoss_isotropic` | none | |
| Prop 12.2, discrete recursion, mode expansion | `sgd_discrete_diag`, `sgd_discrete_excessLoss`, `sgd_discrete_mode_expansion` | `B > 0`, `|1 − ηλᵢ| < 1` | state-dependent noise |
| Prop 12.2, invariance of the discrete Gaussian | `sgd_gaussian_invariant` | as above, `η > 0`, `c ≥ 0` | |
| Prop 12.2, the OU semigroup `N(e^{−sH}m, Σ_s)`: Lyapunov ODE, stationarity, relaxation | `ou_sgd_stationary`, `ouStep_invariant`, `hasDerivAt_ouCov'`, `ouCov_tendsto` (OrnsteinUhlenbeck.lean) | `Hᵀ = H`, `Σᵀ = Σ ⪰ 0`, `(η/B)C ⪰ 0`, Lyapunov identity; relaxation needs `H ≻ 0` | |
| Prop 12.2, the OU **equation** `dw = −Hw ds + σ dW` has marginal law `N(e^{−sH}w₀, ∫₀ˢ e^{−uH}σσᵀe^{−uH}du)` | `ou_marginal_law`, `ou_marginal_law_lyapunov` (OUBrownian.lean); `ouSol_integral_equation`, `ouSol_unique` (OUPathwise.lean); `tendsto_ouIncrementSum` (OUIncrement.lean) | `W` an `IsBrownianVec` (centred Gaussian process, `Cov = δᵢⱼ min(s,t)`, continuous paths); `Hᵀ = H`; `s ≥ 0`; the process is the pathwise variation-of-constants solution | existence of Brownian motion (not on this Mathlib pin); `IsBrownianVec` is satisfied by `d` independent real Brownian motions, `isBrownianVec_of_iIndepFun` |
| Prop 12.2, the OU process is Markov with transition kernel `N(e^{−rH}x, C_r)` | `ou_two_time_law_compProd`, `condDistrib_ouProcess`, `ouKernel_eq` (OUMarkov.lean); `ouSol_restart`, `indepFun_ouProcess_restartNoise` | `IsBrownianVec`, `Hᵀ = H`, `s, r ≥ 0` | conditioning is on the present state `X_s` only, not on the whole past σ-algebra; finite-dimensional distributions for three or more times not assembled |
| Prop 12.4, virial identity `E[δ·∇U] = d` | `virial_multi`, `virial_localized` (VirialMulti.lean); `radial_virial`, `gibbs_virial_one_dim`, `ulaCov_virial` | `U` differentiable (`C¹`), `e^{−U}`, `xᵢe^{−U}`, `xᵢ∂ᵢU e^{−U}` integrable | the note's locally Lipschitz hypothesis |
| eq (virial), degree decomposition | `degree_decomposition` | algebra only: `ta + γb = d`, `K ≠ 0`, `p = a/K ≠ 0` | |
| eq (degree_decomp), Gaussian and ULA balances | `gaussian_virial`, `ulaCov_virial` | `P` invertible; ULA denominator invertible | |

## What the reader should look at first

1. `ou_marginal_law` (OUBrownian.lean) and the structure `IsBrownianVec`: the hypothesis package is
   new; check that its four fields are what you mean by Brownian motion, and that
   `isBrownianVec_of_iIndepFun` (BrownianVecInstances.lean) is the construction you expect.
2. `primer_nlo_centered` (PrimerNLO.lean): check the sign convention of the bracket against the
   note and the primer, and that `ObservableTensorApprox ψ g` with `hψ.A = B − matCLM P` is the
   centred perturbation.
3. `gdIter_isBigO_sq`: the `O(ε²)` remainder of Prop 3.1 now has a Lean statement; check that
   the two local bounds are the hypotheses you want (they hold for a `C²` loss with Lipschitz
   Hessian).
4. `movingMinimizer_exists`: criticality, not minimality.
5. `gaussianCovariance_obs_scaled_bound`: cubic polynomial observables only.
