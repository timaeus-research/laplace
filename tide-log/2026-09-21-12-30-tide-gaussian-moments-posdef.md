# Tide: gaussian-moments-posdef

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." Continuing the Sanity on Sampling programme: discharge the integrability and Fubini-IBP hypotheses of the seabed's multivariate Gaussian theorems (and of the Gaussian LLC identity behind `eq:llc`) for a positive definite precision matrix, by computing the Gaussian moments on `ℝ^d` via a linear change of variables: `Z = (2π)^{d/2}/√det P`, `∫ uᵢuⱼ gW = Z (P⁻¹)ᵢⱼ`.
**Seabed:** laplace, commit ca5f5b8 (origin/main at tide start; `gaussian-quadratic` and `ula-eigendirection` landing in parallel)
**Started:** 2026-09-21T06:17Z
**Worktree / branch:** learning-theory/lean/laplace-tide-gaussian-moments-posdef, tide/gaussian-moments-posdef
**Retrospective:** skipped by user instruction for this auto run.

## Seabed snapshot

- `Laplace/Multi/Defs.lean` (`quadForm`, `gaussianWeight`, `gaussianZ`, `FubiniIBPHypothesis`), `GaussianIBP.lean` (IBP theorem *given* the hypotheses), `GaussianDomination.lean` (`integrable_exp_neg_const_mul_sum_sq` and coordinate variants), `GaussianLLC.lean`; `Laplace/Sampler/Lyapunov.lean` (`orthoOf`, `spectral_real`), `GaussianQuadratic.lean` (measure-form second moments).
- The Fubini-IBP hypothesis has never been discharged in the seabed.

## Candidates v1 (Claude)

Verbatim in `tide-log/gpt_gaussian_moments_prompt_v1.md`: **D** Gaussian moments for PD `P` (D1 integrability, D2 `Z`, D3 second moments and hence the IBP hypothesis, D4 corollaries), by linear change of variables (R1) or identification with `multivariateGaussian` (R2).

## Numerical check

Standard identities (`Z = (2π)^{d/2}/√det P`, second moments `Z P⁻¹`); checked implicitly by every Laplace-route number in the note.

## GPT-6 Astra v1

Verbatim in `tide-log/gpt_gaussian_moments_v1.md`. Summary: the reduction "second moments ⟹ FubiniIBPHypothesis" is right (`∫ u_j (Hu)_i g = Σ_k P_ik ∫ u_j u_k g = Z (P P⁻¹)_ij`, needing D1 for `integral_sub`/finite sums; apply the moment theorem with indices `k j` to avoid a symmetry rewrite; `P.PosDef` supplies the symmetry the weight needs); prefer R1 with one change-of-variables wrapper `∫ f = |det M| ∫ f ∘ M` (the Haar lemma gives `map M volume = |det M|⁻¹ • volume`, so the substitution factor is `|det M|`, not its inverse), whitening `M = U diag(p^{-1/2})` with `MᵀPM = 1`, `MMᵀ = P⁻¹`, `det M ≠ 0`; the standard-coordinate package `Z₀`, `∫ v_a v_b e^{-|v|²/2} = δ_ab Z₀` by product factorisation with the `a = b`/`a ≠ b` split; D3 needs neither `Z₀` nor `|det M|` in closed form (`|det M| Z₀ = Z`); D2's `(det P)^{-1/2}` from `det (MᵀPM) = 1`, with real exponent `d/2`; D1 by coercivity `a Σ u_i² ≤ uᵀPu` (spectral; handle empty `ι`) and domination with the seabed's `integrable_coord_mul_coord_mul_exp_neg_const_mul_sum_sq`; package as a `Prop` structure of facts plus thin adapters; the `LaplaceCov6MomentHypotheses` sixth moments are *not* covered by second moments. Size: medium-to-large (rough ranges 500–1250 lines); cut D2 first if it balloons. Vote: D1 + D3 + a thin IBP adapter via R1, D2 deferred.

## Integration (Claude)

Accepted: R1; whitening algebra block; standard-coordinate package; D3 and the IBP discharge with D1; D2 kept only as `Z > 0` plus the closed form if it falls out of `det(MᵀPM) = 1` cheaply; adapters for the seabed's scalar second-moment theorem and `localised_gaussian_K_expectation`.

## Vote
- Claude: D1 + D3 + IBP adapter (+ D2 if cheap).
- GPT-6 Astra: D1 + D3 + adapter, D2 deferred.

Agreed after one round.

## Result

Committed as `Laplace/Multi/GaussianMomentsPosDef.lean` (3e6a701, renamed `whitening` → `whiteningOf` in f33c278 after the umbrella build exposed a clash with `QuadForm.whitening`), 0 sorries, full `lake build` green after merging `origin/main` (germbij tides `435b651`, `24cb50b`).

Theorems: `matCLM`, `quadForm_matCLM`, `whiteningOf` (`Mᵀ P M = 1`, `M Mᵀ = P⁻¹`, `|det M| = (√det P)⁻¹`), `map_mulVec_volume`, `integral_comp_mulVec`, `integrable_comp_mulVec_iff`, the standard-Gaussian product integrals on `ι → ℝ` (`integral_std_gaussian_pi`, `integral_coord_mul_std_gaussian_pi`, integrability), `gaussianZ_matCLM` (`√(2π)^d (√det P)⁻¹`), `integral_coord_mul_gaussianWeight_matCLM` (`Z (P⁻¹)ᵢⱼ`), `fubiniIBPHypothesis_matCLM`, `gaussian_quadForm_integral_posDef`, `gaussian_llc_posDef` (`t E[½⟨u,Hu⟩] = d/2` with only `H.PosDef`).

Surprises: `Real.map_linearMap_volume_pi_eq_smul_volume_pi` makes the change of variables a two-line affair once the map is packaged as `Matrix.toLin'`; `lean-state check` on a single module cannot see cross-module name clashes, only the umbrella `lake build` can (hence the rename).
