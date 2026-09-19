# Tide: germbij sufficient sub-families of observables

**Direction (user):** "Ok let's continue with the formalisation and exploration of this. Examine the current state of the paper and the Lean … Things I'm particularly interested in: … what it looks like on the geometry side if you 'subsample' i.e. just take some non-complete family of observables (i.e. what is a 'sufficient set' of observables to fully recover the germ? Is there a clear condition for this? And if we take less, what kind of 'approximation' do we get in function space?)" — continued on auto after the normalized-singular tide.
**Seabed:** laplace, commit 207b415 (main; includes NormalizedSingular at 258a8fb)
**Started:** 2026-09-19T14:40Z
**Ledger direction:** germbij: sufficient sub-families of observables — covariance-pairing injectivity characterises which finite test families recover the degree-k tensor (iff, with counterexample direction), corollary: no finite family recovers the full jet for d >= 2.

## Seabed snapshot (what the sufficient-set question can stand on)

- `HigherLaplaceDomain k L H` (LocalRateDCT): H4 domain data + `C^k` + order-`k` Taylor
  remainder bound on a ball; `rescaledMoment A P q` (NormalizedRate) = localized posterior
  moment of test `P` at rescaling `q` (the `t = q^{-2}` variable).
- **Pairing limit** `tendsto_pairwise_normalized_moment_difference hk A₁ A₂ hlower hP_cont hP_growth`:
  for ANY continuous polynomially-growing test `P`,
  `(A₁.rescaledMoment P q − A₂.rescaledMoment P q)/q^{k−2} → −gaussianCovariance H P Q`
  where `Q = taylorHomogeneousTerm k L₁ − taylorHomogeneousTerm k L₂`. This is exactly the
  Gaussian covariance pairing `Cov_γ[P, Q]`, `γ = N(0, H^{-1})`.
- **Rigidity** `homogeneous_eq_zero_of_gaussianCovariance_self_eq_zero`: `Q` homogeneous of
  degree `k > 0`, `Cov_γ[Q,Q] = 0` ⇒ `Q = 0`. `iteratedFDeriv_eq_of_diag_eq`: symmetric
  tensors with equal diagonals are equal.
- Existing sufficiency results: `iteratedFDeriv_recovery_of_moment_rates` (ALL homogeneous
  tests), `iteratedFDeriv_recovery_of_monomial_rates` (the `d^k` monomial words),
  `finite_jet_recovery_of_monomial_rates` (degrees ≤ N ⇒ N-jet), `smooth_jet_recovery_of_monomial_rates`.
  So "degree-≤D observables give the D-jet" is ALREADY formalised; slop S4 must say so.
- Missing: any statement about a *general* family `S` of tests, the iff condition, the
  converse (data blind to a kernel direction), and the finite-family impossibility.
