# Tide: gaussian-table

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"; "Continue with what you think best, don't stop"). Chosen: discharge the four-moment hypothesis of the `frobenius-law` tide for the ULA chain with independent standard Gaussian noise: the projected innovations `√(2h) <u_i, ξ_{c,k}>` along the orthonormal eigenvectors `u_i = orthoCol i` form a `FourthMomentTable` across chains, times and directions, so the E4 whole-covariance law holds unconditionally for the sampler of the note.
**Seabed:** laplace, commit e82e49f (branch tide/frobenius-law, chained)
**Started:** 2026-09-21-17-38 UTC

## Context

`estimator-variance` built `FourthMomentTable g P v` (independent, `L^4`, moments `(0, v, 0, 3v^2)`) and discharged it for a *single*
direction: `fourthMomentTable_projNoise : FourthMomentTable (fun a : Fin C × ℕ => projNoise h u (ξ a.1) a.2) P (2h)` for a unit vector `u`, using
`map_innerSL_eq_gaussianReal` (`<u, ξ> ~ gaussianReal 0 1`), the seabed's 1-D moments, and `hind.comp` for independence across `(c, k)`.
`frobenius-law` needs the table for the family `(c, k, i) ↦ √(2h) <u_i, ξ_{c,k}>` on `Fin C × ℕ × ι` (with `u_i = orthoCol hP i` orthonormal,
`norm_orthoCol`, `orthoOf_transpose_mul : Uᵀ U = 1`). Everything except the *joint independence across directions* is already available
per element (`L^4`, means, moments are per-element facts). Mathlib (Sep 2026): `iIndepFun.hasGaussianLaw_pi` (independent Gaussian vectors are
jointly Gaussian), `HasGaussianLaw.map_fun` (CLM image), `HasGaussianLaw.iIndepFun_of_covariance_inner` (jointly Gaussian + `cov[⟪x, X i⟫, ⟪y, X j⟫] = 0`
for `i ≠ j` ⇒ `iIndepFun`), `covarianceBilin_stdGaussian`/`variance_dual_stdGaussian`, `IndepFun.covariance_eq_zero`(?).

## Candidates v1 (Claude)

**A. Independence of the Gaussian projections across chains, times and directions.** For `ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι` with
`P.map (ξ c k) = stdGaussian`, `iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P`, and an orthonormal family `u : ι → EuclideanSpace ℝ ι`:
`iIndepFun (fun a : Fin C × ℕ × ι => fun ω => <u a.2.2, ξ a.1 a.2.1 ω>) P`. Route: restrict to a finite time window `Fin T` (independence of the
whole ℕ-family follows from independence of every finite sub-family, or state the table on `Fin C × Fin T × ι` and adapt the chain
lemmas); the vector `(ξ_a)_{a ∈ Fin C × Fin T}` has a Gaussian law by `iIndepFun.hasGaussianLaw_pi`; the CLM
`L : (Fin C × Fin T → E) → (Fin C × Fin T × ι → ℝ)`, `L f (a, i) = <u i, f a>`, gives `HasGaussianLaw (fun ω (a,i) => <u i, ξ a ω>) P` by
`HasGaussianLaw.map_fun`; the covariances vanish off the diagonal: for `a ≠ a'` by independence of `ξ a`, `ξ a'` (`IndepFun.covariance_eq_zero`
or `integral_mul_eq_mul_integral` + zero means), for `a = a'`, `i ≠ j` by `cov[<u_i, ·>, <u_j, ·>] = <u_i, u_j> = 0` under `stdGaussian`
(`covarianceBilin_stdGaussian`); conclude with `HasGaussianLaw.iIndepFun_of_covariance_inner` (with `E i = ℝ`, where the inner product `⟪x, X i⟫`
is `x * X i`).

**B. The `FourthMomentTable` for the projected innovations across directions**: `FourthMomentTable (fun a : Fin C × Fin T × ι => projNoise h (u a.2.2)
(ξ a.1) a.2.1) P (2h)` for `0 ≤ h`, from A plus the per-element facts of `estimator-variance` (`memLp_four_inner_of_stdGaussian`,
`integral_projNoise`, `integral_projNoise_sq`, `integral_inner_pow_of_stdGaussian`, `integral_pow_three/four_gaussianReal`).

**C. The unconditional E4 law for ULA.** Instantiate `frobenius_realChain_le` (or its finite-window variant) with `η c k i := projNoise h (orthoCol
hP i) (ξ c) k`, `ρ_i = 1 - h p_i`, `v = 2h`: for the ULA chain in the eigenbasis of `P` (`<u_i, ulaChain Q h (ξ c) k> = realChain (1 - h p_i)
(projNoise …) k` by `inner_ulaChain_eq_realChain`), with `0 < h p_i ≤ 1`,
`E|Σ̂ - E Σ̂|_F^2 ≤ (1/(CN)) ∑_ij (1 + δ_ij) s2_i s2_j (1 + ρ_i ρ_j)/(1 - ρ_i ρ_j)`, `s2_i = 2h/(1 - ρ_i^2)`: the note's E4 finding for the actual sampler.

Proposed: A + B + C, one module `Laplace/Sampler/GaussianTable.lean` (~400 lines; A is the risky part).

## Numerical check

Structural (independence and moment identities); the substance is checked by the E4 Monte Carlo of `numcheck25.py` (per-entry variances of the
pooled second-moment matrix of the ULA chain in the eigenbasis within 2.6% of the prediction that assumes exactly this four-moment table).

## GPT-6 Astra v1

Saved verbatim in `gpt_gaussian_table_v1.md`. Summary: A correct; the finite-block Gaussian route (independent Gaussian vectors ⇒ joint law,
CLM of projections, vanishing covariances, `iIndepFun_of_covariance_inner`) works, but prefer "one block, then flatten": prove independence
of the orthonormal projections within one `stdGaussian` block (a `Fintype ι` statement), then assemble across `(c, k)` with an
independent-block flattening lemma if Mathlib has one (group independence is essential; pairwise cross-block independence would not
flatten); otherwise recover the ℕ-indexed family's independence from finite restrictions via the finite-subfamily formulation of
`iIndepFun` (choose `T` above every time in the finset; assemble the Gaussian vector on the *distinct* block indices, then project; mind
the `Fin C × ℕ × ι` vs `(Fin C × ℕ) × ι` associativity). Do not pad with zeros (kills the moments) or add independent copies. Same-block
covariance via `covariance_map` + `covarianceBilin_stdGaussian` (or polarisation as fallback with a norm-squared lemma for arbitrary
vectors); cross-block via independence + `L^2`. State A for an `Orthonormal ℝ u` family; prove `Orthonormal ℝ (orthoCol hP)` from
`orthoOf_transpose_mul` separately (unit norms alone are not enough). B is routine from the per-element facts with `0 ≤ h`; C is
bookkeeping; "unconditional" means the table hypothesis is discharged (Gaussian noise, step size, sample size, initialisation remain).
~400 lines plausible only if the combination API exists. **Vote: A+B+C**, A for orthonormal families, final table on `Fin C × ℕ × ι`.

## Vote
- Claude: A+B+C (one-block independence + flattening if available, finite-subfamily fallback)
- GPT-6 Astra: A+B+C

Agreed.

## Result

Committed as `b09e163` on `tide/gaussian-table` (`Laplace/Sampler/GaussianTable.lean`, 260 lines; full `lake build` and `scripts/sorries` clean:
0 sorry, 0 axiom, 0 native_decide).

Theorems: `orthonormal_orthoCol`, `hasGaussianLaw_of_map_stdGaussian`, `memLp_two_inner_of_stdGaussian`,
`covariance_inner_inner_of_stdGaussian`, `iIndepFun_inner_window`, `iIndepFun_of_windows`, `fourthMomentTable_projNoise_dir`,
`frobenius_ula_le`.

Surprises: Mathlib's `HasGaussianLaw` API did all the heavy lifting (`iIndepFun.hasGaussianLaw`, `iIndepFun_of_covariance_inner`,
`covarianceBilin_stdGaussian`); the only real friction was the Pi-type instance mismatch that rules out `map_fun` in favour of
`map_of_measurable`, and the finite-window → ℕ passage, which is ~40 lines of Finset gymnastics through the finite-subfamily
characterisation of independence.
