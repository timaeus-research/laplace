# Tide: ula-eigendirection

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." Continuing the Sanity on Sampling programme (E1/E2/E4): the ULA chain started at the mode, projected on an eigendirection of the precision, is an AR(1) chain with `ρ = 1 - h p` and innovation variance `2h`; hence the note's finite-chain prediction applies to the actual ULA chain with i.i.d. standard Gaussian noise.
**Seabed:** laplace, commit c340173 (origin/main at tide start)
**Started:** 2026-09-21T05:58Z
**Worktree / branch:** learning-theory/lean/laplace-tide-ula-eigendirection, tide/ula-eigendirection
**Retrospective:** skipped by user instruction for this auto run.

## Seabed snapshot

- `Laplace/Sampler/AR1.lean`, `AR1Real.lean` (realised chains, `expected_pooled_sample_variance`, `white_of_indep`), `RandomMap.lean`, `ULA.lean` (`orthoOf`, `ulaStep_eq_conj`, `ulaCov_conj_apply`), `GaussianInvariance.lean`.
- Mathlib: `stdGaussian`, `variance_dual_stdGaussian`, `iIndepFun`, `IndepFun.comp`, `IndepFun.integral_mul_eq_mul_integral`.

## Candidates v1 (Claude)

Verbatim in `tide-log/gpt_ula_eigendirection_prompt_v1.md`: **G** the ULA chain along an eigendirection is the realised AR(1) chain with `ρ = 1 - hp`, `v = 2h` (G1 white-noise table of the projected innovations from independence and the standard-Gaussian variance; G2 the finite-chain prediction for the actual chain; G3 several chains; G4 eigenvectors from the spectral packaging).

## Numerical check

E1/E2/E4 of the note are exactly this comparison (sampled per-eigendirection variances vs `ar1_expected_sample_variance` with `ρ_i = 1 - h p_i`, `σ_i² = 1/(p_i(1 - h p_i/2))`), agreeing to the finite-chain precision reported there.

## GPT-6 Astra v1

Verbatim in `tide-log/gpt_ula_eigendirection_v1.md`. Summary: G is the right bridge with three qualifications: the projection identity `⟨u, (I - hQ) z⟩ = (1 - hp)⟨u, z⟩` needs a *left* eigenvector or symmetric `Q` (a right eigenvector of a non-symmetric matrix is not enough); the innovation variance `2h` needs `0 ≤ h`; the stationary parametrisation `σ² = 2h/(1-(1-hp)²) = 1/(p(1-hp/2))` needs `p > 0`, `h > 0`, `hp < 2` (fails at `h = 0` under Lean's total division). Organisation: a deterministic projection lemma (`hproj : ∀ z, ⟨u, B z⟩ = ρ ⟨u, z⟩`, induction with `inner_add_right`, `inner_smul_right`), Gaussian scalar lemmas under `stdGaussian E` for arbitrary `u` (`∫ ⟨u,z⟩ = 0`, `∫ ⟨u,z⟩² = ‖u‖²` via `variance_dual_stdGaussian` + `innerSL_apply_norm`, or via `covarianceBilin_stdGaussian`), transfer through the law with `integral_map`/`memLp_map_measure_iff` (assume `Measurable (ξ k)`), off-diagonal moments via `IndepFun.comp` + `IndepFun.integral_mul_eq_mul_integral`, reuse `white_of_indep` on the flattened index `Fin C × ℕ`; spectral column as a unit eigenvector by entrywise algebra from `Q U = U D` and `Uᵀ U = 1`, packaged as an element of `EuclideanSpace` (not a raw function). Vote: G1–G4 as one cluster.

## Integration (Claude)

Accepted in full: symmetric `Q`, `0 ≤ h`, deterministic projection lemma first, Gaussian lemmas for arbitrary `u` with the unit case as a corollary, `Measurable (ξ k)`, stationary-variance identity as a separate algebraic lemma with the nondegeneracy hypotheses.

## Vote
- Claude: G1–G4.
- GPT-6 Astra: G1–G4.

Agreed after one round.

## Result

- Commit `dec52b1` on `tide/ula-eigendirection`. Full `lake build` green; `scripts/sorries`: 0 sorry, 0 axiom, 0 native_decide.
- `Laplace/Sampler/ULAEigen.lean` (     259 lines): `vecChain`, `inner_vecChain_eq_realChain` (deterministic projection lemma), `ulaChain`, `projNoise`, `inner_euclid_ulaStep`, `inner_ulaChain_eq_realChain`, `memLp_inner_stdGaussian`, `integral_innerSL_stdGaussian`, `integral_inner_stdGaussian`, `integral_inner_sq_stdGaussian`, `memLp_projNoise`, `integral_projNoise`, `integral_projNoise_sq`, `integral_projNoise_mul` (white noise with variance `2h‖u‖²`), `expected_pooled_sample_variance_ula`, `ula_variance_eq`, `orthoCol`, `mul_orthoOf_eq`, `mulVec_orthoCol`, `norm_orthoCol`.
- Surprises: none mathematical after GPT-6 Astra's symmetry correction. Lean friction: rewrite patterns carrying `⇑(innerSL ℝ u)` vs `inner ℝ u z` (pass the lambdas explicitly), a stuck `IsGaussian ?μ` instance until the measure was pinned, and an implicit variance parameter assigned by a stray `rfl`.
