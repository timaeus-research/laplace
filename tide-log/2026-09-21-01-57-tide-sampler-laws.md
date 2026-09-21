# Tide: sampler-laws

**Direction (user):** Formalise the mathematics used in the Sanity on Sampling note (learning-theory/papers/sanity/main.tex, project sanity) in the laplace seabed: the ULA stationary covariance law for the Euler-discretised Langevin chain on a Gaussian target, the minibatch Lyapunov law, the finite-chain AR(1) variance, the Gaussian identities behind the localised LLC and mean shift, the one-loop covariance correction, and the Rosenbrock d=2 closed forms.
**Seabed:** laplace, commit b7e20dd (origin/main at tide start)
**Started:** 2026-09-21T01:57Z
**Worktree / branch:** learning-theory/lean/laplace-tide-sampler-laws, tide/sampler-laws
**Scope of this tide:** the direction is a programme (six items). This tide takes the first coherent chunk, the sampler-side laws for the Gaussian linear recursion (ULA stationary covariance, Lyapunov law with minibatch noise, finite-chain formula), and leaves the Gaussian LLC identity, the one-loop covariance term and the Rosenbrock closed forms as follow-up tides.

## Seabed snapshot

- Gibbs objects live in `Laplace/Multi/Defs.lean`: `partitionFunction`, `gibbsExpectation`, `gibbsCov` as integrals of `exp(-t L)` over `ι → ℝ`; `gaussianWeight H`, `quadForm`, `dot`.
- Gaussian integration by parts on ℝ^d in `Laplace/Multi/GaussianIBP.lean`: `gaussian_second_moment_eq_inverse_entry` (second moment of `exp(-½ uᵀHu)` is `(H⁻¹)_ij`), `gaussian_dot_mul_dot`, odd moments vanish. `H` is a continuous linear map `(ι → ℝ) →L[ℝ] (ι → ℝ)`.
- Multivariate Laplace rates: `gibbsCov_first_order_rate_sharp`, `gibbsExpectation_first_order_rate_explicit`, `gibbsCov_first_order_rate_explicit` (Statements.lean surface).
- One-dimensional: harmonic moments (`Laplace/OneD/Harmonic.lean`), anharmonic rates, localisation tail bounds (`Laplace/OneD/Localisation.lean` is about tails of the harmonic measure, not the γ-localised Gibbs posterior), near-degenerate scaling (`NearDegenerate.lean`).
- Nothing on discrete-time samplers, Markov chains, Lyapunov equations, or covariance recursions. New arc; proposed home `Laplace/Sampler/`.
- Mathlib (pinned rev 8a178386ffc0, Lean v4.33.0): `Matrix.PosDef`/`PosSemidef`, Hermitian spectral theorem, `multivariateGaussian` on `EuclideanSpace ℝ ι` with `covarianceBilin_multivariateGaussian` and `charFun_multivariateGaussian`, `IsGaussian` with `isGaussian_map` (continuous linear maps) and `isGaussian_conv`, matrix operator norms, summable matrix families.

## Candidates v1 (Claude)

See `tide-log/gpt_sampler_laws_prompt_v1.md` for the verbatim text sent to GPT-6 Astra. In brief:

- **A. Lyapunov laws (linear algebra).** (A1) For positive-definite P and 0 < lr with lr·P < 2I, Σ_ULA := P⁻¹(I − (lr/2)P)⁻¹ satisfies Σ = AΣA + 2lr·I with A = I − lr·P. (A2) For ‖A‖ < 1 and symmetric N, Σ = AΣAᵀ + N has the unique solution Σ_{k≥0} A^k N (Aᵀ)^k; the recursion from Σ_0 = 0 gives partial sums, converges, and when N commutes with A gives Σ_k = Σ_∞(I − A^{2k}), Σ_∞ = (I − A²)⁻¹N. (A3) Minibatch corollary for C commuting with P: per-direction variance (1 + lr t² c_i/2)/(p_i(1 − lr p_i/2)); 1D finite-chain Var x_k = σ²(1 − ρ^{2k}).
- **B. Gaussian invariance (probabilistic).** A X + √(2lr) ξ ~ N(0, AΣAᵀ + 2lr I) for independent Gaussians; hence N(0, Σ_ULA) is invariant under one ULA step.
- **C. Localised Gaussian LLC identity (seabed language).** For L = ½ wᵀHw and weight exp(−tL − γ|w|²/2), ⟨K⟩ = ½ tr(H(tH + γI)⁻¹), from `gaussian_second_moment_eq_inverse_entry`.

Claude's prior: back A (A1 + A2 + A3) as the core, C as a cheap add-on, B only if Mathlib's Gaussian identification is clean.

## GPT-6 Astra v1

Verbatim response saved as `tide-log/gpt_sampler_laws_v1.md` (13 kB). Summary of the corrections and
additions it made:

- A1 correct; the clean identity is `I - A² = 2h·P·B` with `B = I - (h/2)P`, so `Σ_ULA - AΣ_ULA A = (I - A²)Σ_ULA = 2hI`
  because Σ_ULA commutes with A. No probability, no series needed.
- A2: `‖A‖ < 1` in the *Euclidean* operator norm suffices for existence and uniqueness among all real matrices;
  the commuting closed forms `Σ_k = Σ_∞(I - A^{2k})`, `Σ_∞ = (I - A²)⁻¹N` additionally need `A = Aᵀ`. Stronger
  finite-time identity without any commutation: `Σ_k - Σ_∞ = A^k (Σ_0 - Σ_∞) (Aᵀ)^k`, proved by induction once a
  fixed point is known; convergence follows. The finite-time covariance is not yet the note's expected *sample*
  variance (that needs temporal cross-covariances `Cov(x_{r+l}, x_r) = A^l Σ_r`; a follow-up).
- A3 strengthened: commutation of C with P is unnecessary. In an orthonormal eigenbasis of P, with `C̃ = QᵀCQ`,
  `Σ̃_ij = (2h δ_ij + h²t² C̃_ij) / (h(p_i + p_j) - h² p_i p_j)`; the diagonal `Σ̃_ii = (1 + h t² C̃_ii/2)/(p_i(1 - h p_i/2))`
  holds for any C. Noncommutation only adds off-diagonal covariance in the precision eigenbasis.
- Stability: `‖I - hP‖₂ = max_i |1 - h p_i|`, so `‖A‖₂ < 1 ⇔ 0 < h p_i < 2 ∀i ⇔ hλ_max < 2`; the sup-norm on `ι → ℝ`
  does not give this, so state the Lean theorems eigenvalue-wise (`|a_i| < 1`) and add an operator-norm wrapper later.
- B correct (invariance, not uniqueness of the invariant law); defer: measure-theoretic plumbing.
- C correct with hypotheses `H` symmetric, `P = tH + γI ≻ 0`; a displaced mean μ adds `½ μᵀHμ`.
- Route: spectral, not Neumann. Diagonal Lyapunov solver `X_ij = N_ij/(1 - a_i a_j)` for `|a_i| < 1`, transported
  through an orthogonal diagonalisation; existence/uniqueness become scalar algebra.
- Extra cheap theorem: monotonicity `N₁ ≼ N₂ ⇒ Σ(N₁) ≼ Σ(N₂)`, hence `Σ_mb ≽ Σ_ULA`.
- Full state-dependent law and one-loop covariance: separate tides; the full law needs a contraction hypothesis on
  the whole operator `T(X) = AXAᵀ + h²t²c Σ_i D_i X D_iᵀ`, not just on A.
- Lean representation: `Matrix ι ι ℝ` with `[Fintype ι] [DecidableEq ι]` for statements; `EuclideanSpace ℝ ι`
  only where operator norms or Gaussian pushforwards enter; connect to the seabed's `(ι → ℝ) →L[ℝ] (ι → ℝ)`
  Gaussian IBP through a boundary conversion lemma.

## Integration (Claude)

Accepted in full. The tide's candidate is the cluster GPT-6 Astra named, with the symmetric-A hypothesis made
explicit and the arbitrary-C entry formula as the headline minibatch statement:

1. **Diagonal Lyapunov solver.** `D = diagonal a`, `∀ i, |a i| < 1`: `X = D X D + N ↔ X = fun i j => N i j / (1 - a i * a j)`.
2. **Symmetric Lyapunov theorem.** For `A` real symmetric with all eigenvalues in `(-1, 1)` and any `N`, the equation
   `X = A X A + N` has the unique solution `Σ_∞(A, N)`; in the eigenbasis of A its entries are `Ñ_ij/(1 - a_i a_j)`.
3. **ULA law.** `P` positive definite, `h > 0`, `h·P < 2I` (eigenvalue-wise): `Σ_ULA := (P - (h/2)P²)⁻¹` is positive
   definite, commutes with P, satisfies `Σ_ULA = AΣ_ULA A + 2hI`, and is the unique solution.
4. **Minibatch entries.** With `N = 2hI + h²t²C`, in the eigenbasis of P: `Σ̃_ij = (2hδ_ij + h²t²C̃_ij)/(h(p_i+p_j) - h²p_ip_j)`
   and `Σ̃_ii = (1 + ht²C̃_ii/2)/(p_i(1 - hp_i/2))`; the commuting/diagonal C case as a corollary.
5. **Finite-time identity.** `Σ_{k+1} = AΣ_kAᵀ + N`, any `Σ_0`: `Σ_k - Σ_∞ = A^k(Σ_0 - Σ_∞)(Aᵀ)^k`; for `Σ_0 = 0` and
   symmetric A commuting with N, `Σ_k = Σ_∞(I - A^{2k})`; 1D: `Var x_k = σ²(1 - ρ^{2k})`.
6. **Gaussian LLC bridge.** In the seabed's language: for `L = ½ wᵀHw` and weight `exp(-tL - γ|w|²/2)`,
   `gibbsExpectation` of `K = L` equals `½ tr(H (tH + γI)⁻¹)` (from `gaussian_second_moment_eq_inverse_entry`), with
   the `γ = 0` specialisation `t⟨K⟩ = d/2` and the eigenvalue sum `½ Σ_i tλ_i/(tλ_i + γ)`.

Deferred to follow-up tides (recorded in `## Follow-ups` of the retrospective): Gaussian invariance (B), temporal
cross-covariances and the expected sample variance, the full state-dependent law, the one-loop covariance
coefficient, Rosenbrock d = 2 closed forms.

## Vote
- Claude: the six-item "spectral Lyapunov laws + ULA closed form + minibatch entries + finite-time identity + Gaussian LLC bridge" cluster.
- GPT-6 Astra: the same cluster ("Back a tight 'spectral Lyapunov laws + quadratic LLC' cluster").

Agreed after one round.

## Numerical check

numpy/scipy, d = 5, random SPD P with eigenvalues (0.3, 0.8, 1.5, 2.5, 4.0), h = 1.9/λ_max, t = 7, random PSD C
(script in the sanity-sampling repo session; results):
- ULA fixed point: `|Σ_ULA - (AΣ_ULA A + 2hI)|_max = 2.4e-15`, Σ_ULA positive definite, eigenvalues equal `1/(p_i(1 - h p_i/2))`.
- Arbitrary-C entry formula vs `scipy.linalg.solve_discrete_lyapunov`: max entry error `3.3e-13`; diagonal formula error `3.8e-13`.
- Finite-time identity `Σ_k = S - A^k S (Aᵀ)^k` from `Σ_0 = 0`: error `≤ 1.4e-14` for k = 1..7; iteration from a perturbed start returns to S (`1.4e-14`).
- Gaussian LLC bridge: Monte Carlo `E[½uᵀHu]` with 4·10⁵ draws of `N(0, (tH + γI)⁻¹)` = 0.6766 vs `½ tr(H(tH+γI)⁻¹)` = 0.6769 = `½ Σ_i tλ_i/(tλ_i+γ)`.

## Step 3 hand-off

- Seabed worktree: `learning-theory/lean/laplace-tide-sampler-laws`, branch `tide/sampler-laws`, base b7e20dd.
- New modules: `Laplace/Sampler/Lyapunov.lean` (diagonal solver, symmetric Lyapunov theorem via the real spectral
  theorem, finite-time identity), `Laplace/Sampler/ULA.lean` (ULA closed form and positivity, minibatch entry formula,
  diagonal/commuting corollary, 1D chain), `Laplace/Multi/GaussianLLC.lean` (quadratic Gaussian expectation bridge to
  `gaussian_second_moment_eq_inverse_entry`). Imports added to `Laplace.lean`.
- Skeleton first (statements with `sorry`, typechecked), then fill; `scripts/sorries` clean before each commit.

## Result

- Commit `eab4a82` on `tide/sampler-laws` (base b7e20dd). Full `lake build` green (8944 jobs); `scripts/sorries`: 0 sorry, 0 axiom, 0 native_decide.
- `Laplace/Sampler/Lyapunov.lean` (251 lines): `diagLyapunov_fixed`, `diagLyapunov_unique`, `covStep_diagonal_fixed_iff`, `covStep_conj`, `lyapunovVia_fixed_iff`, `lyapunovVia_conj_apply`, `orthoOf`, `spectral_real`, `symmLyapunov_fixed_iff`, `covStep_iterate_sub_fixed`, `covStep_iterate_zero`, `covStep_iterate_zero_of_comm`, `ar1_var_iterate`.
- `Laplace/Sampler/ULA.lean` (269 lines): `one_sub_ulaStep_sq`, `ulaCov_commute`, `ulaCov_fixed`, `ulaStep_eq_conj`, `ula_fixed_iff`, `isUnit_det_ulaDenom`, `ulaCov_eq_lyapunov`, `ulaCov_conj_apply`, `ulaCov_posDef`, `minibatchCov_conj_apply`, `minibatchCov_conj_diag`, `minibatch_fixed_iff`.
- `Laplace/Multi/GaussianLLC.lean` (195 lines): `hessInvPairing`, `quadForm_eq_double_sum`, `gaussian_quadForm_integral`, `localised_gaussian_K_expectation`, `hessInvPairing_self_inv`, `gaussian_K_expectation_eq_half_dim`.
- Scope note: the Gaussian LLC bridge (item 6 of the Integration section) was included after all, contrary to the "Scope of this tide" line at the top; the one-loop term, the Rosenbrock closed forms, Gaussian invariance and the expected sample variance remain deferred.
- Surprises: none mathematical. All friction was Lean idiom in the spectral packaging (`Unitary.conjStarAlgAut_apply`, `congr 1` closing the `RCLike.ofReal ∘ eigenvalues` goal outright) and one looping `simp` in the quadratic-form expansion. The only statement change during filling was dropping an unused `0 < h` hypothesis from `isUnit_det_ulaDenom`.

## Retrospective

`retrospectives/2026-09-21-01-57-tide-sampler-laws.tex` (PDF alongside).
