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

## Candidates v1 (Claude)

Notation: `γ = N(0, H⁻¹)`, `Cov_γ = gaussianCovariance H`, `Q_k(L₁,L₂) = taylorHomogeneousTerm k L₁ − taylorHomogeneousTerm k L₂`
(the degree-k Taylor difference; a homogeneous degree-k polynomial when the tensors are symmetric).
"S-data at degree k" for a family `φ : ι → EuclidD d → ℝ` of tests: `∀ i, (A₁.rescaledMoment (φ i) q − A₂.rescaledMoment (φ i) q) = o(q^{k−2})` as `q → 0⁺`.

### A. Sufficient family at one degree (the "if" of the iff), general test family
```
theorem iteratedFDeriv_recovery_of_family_rates {ι : Type*} (hk : 2 < k)
    (A₁ : HigherLaplaceDomain k L₁ H) (A₂ : HigherLaplaceDomain k L₂ H)
    (hlower : ∀ j < k, iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    (hsymm₁ hsymm₂ : IsSymm …)
    (φ : ι → EuclidD d → ℝ) (hφc : ∀ i, Continuous (φ i)) (hφg : ∀ i, HasPolynomialGrowth (φ i))
    (hinj : ∀ Q : EuclidD d → ℝ, Continuous Q → HasPolynomialGrowth Q → IsHomogeneousOfDegree k Q →
       (∀ i, gaussianCovariance H (φ i) Q = 0) → Q = 0)
    (hdata : ∀ i, (fun q ↦ A₁.rescaledMoment (φ i) q − A₂.rescaledMoment (φ i) q) =o[𝓝[>] 0] fun q ↦ q^(k−2)) :
    iteratedFDeriv ℝ k L₁ 0 = iteratedFDeriv ℝ k L₂ 0
```
Proof: pairing limit for each `φ i` + uniqueness of limits ⇒ `Cov_γ[φ i, Q_k] = 0 ∀ i` ⇒ `Q_k = 0` by `hinj` ⇒ diagonals equal ⇒ tensors equal. ~40 lines. Recovers the monomial theorem (monomials are a spanning family; `hinj` from the self-covariance rigidity). Rationale: this IS the "clean condition" — injectivity of the covariance pairing on `H_k`, and it is `H`-dependent in general.

### B. The converse: kernel directions are invisible at the rate (the "only if", pair form)
```
theorem family_rates_of_kernel (hk : 2 < k) (A₁ A₂) (hlower) (φ …)
    (hker : ∀ i, gaussianCovariance H (φ i) (Q_k L₁ L₂) = 0) :
    ∀ i, (fun q ↦ A₁.rescaledMoment (φ i) q − A₂.rescaledMoment (φ i) q) =o[𝓝[>] 0] fun q ↦ q^(k−2)
```
Immediate from the pairing limit (limit is 0 ⇒ little-o). ~15 lines. Together with A this is the iff, stated
relative to a given pair of losses. The *absolute* form ("if the pairing is not injective there EXIST two
losses with different k-jets and matching S-data") needs an instance:

### B′. Instance: perturb a certified loss by a kernel polynomial
Given `A₁ : HigherLaplaceDomain k L₁ H` (package family for all degrees) and `Q ≠ 0` homogeneous of degree k
(diagonal of a symmetric k-tensor `T`, so `Q x = T (fun _ ↦ x)`), build `HigherLaplaceDomain k (L₁ + Q) H`
with the same lower jets and `iteratedFDeriv k (L₁+Q) 0 = iteratedFDeriv k L₁ 0 + k! • T ≠ iteratedFDeriv k L₁ 0`.
Needs: `iteratedFDeriv j (T ∘ diag) 0` for all `j` (Mathlib `ContinuousMultilinearMap.iteratedFDeriv` /
`cpolynomial` API + `ContinuousLinearMap.iteratedFDeriv_comp_right` for the diagonal), Taylor remainder bound
of `L₁ + Q` from that of `L₁` (Q's own Taylor remainder at order k is 0), the `rescaled_lower` bound on a
shrunken ball (`c/2` after `|Q(x)| ≤ M‖x‖^k`), measurability/contDiff. Estimated 200–300 lines; the most
Lean-friction-prone part. Could be deferred: A+B already give the relative iff.

### C. No finite family suffices for the full jet when d ≥ 2 (pairing-level)
```
theorem exists_kernel_homogeneous_of_finite_family (hd : 2 ≤ d) (hH : H.PosDef)
    {n : ℕ} (φ : Fin n → EuclidD d → ℝ) (hφc hφg) (k : ℕ) (hk : n < k + 1) :
    ∃ Q : EuclidD d → ℝ, Continuous Q ∧ HasPolynomialGrowth Q ∧ IsHomogeneousOfDegree k Q ∧ Q ≠ 0 ∧
      ∀ i, gaussianCovariance H (φ i) Q = 0
```
Proof: the `k+1` functions `x ↦ x₀^{k−j} x₁^{j}` are linearly independent (restrict to `x = (s, 1, 0, …)`:
a real polynomial in `s` vanishing everywhere is zero, `Polynomial.funext`); `Cov_γ[φ i, ·]` is linear on
their span (needs `gaussianCovariance` additivity/smul in the second slot under polynomial growth — NOT yet
in the seabed, ~40 lines from `integrable_mul_quadKernel_of_polynomialGrowth`); a linear map from an
`(k+1)`-dimensional space to `ℝ^n` with `n < k+1` has nontrivial kernel (`LinearMap.ker_ne_bot_of_finrank_lt`).
~150 lines. With B: for ANY finite family and any pair of losses whose degree-`(n+3)` Taylor difference is
that `Q`, the family's data are blind at the rate; with B′: such pairs exist, so no finite family is
sufficient for the jet in `d ≥ 2`. (In `d = 1` two observables suffice — `{x², x³}`, already implicit in
the 1D recovery theorems; worth a remark, not a theorem.)

### D. (Already formalised, for the record) Degree-≤N observables give exactly the N-jet
`finite_jet_recovery_of_monomial_rates` (MonomialTests). The "and nothing more" half is B/B′ at degree N+1.
Slop S4 wrongly implied this was new; correct it.

**Proposed tide:** A + B + C (+ B′ if the Mathlib cpolynomial API makes the instance cheap). Vote: A+B+C as
one file `Laplace/Multi/SufficientFamilies.lean`.

## GPT-6 Astra v1 (summary; verbatim in `gpt_germbij_sufficient_v1.md`)

- A, B correct. **Quantify `hinj` over homogeneous POLYNOMIAL diagonals** (the finite-dimensional
  `H_k`), not over all continuous homogeneous functions (infinite-dimensional in d ≥ 2, so finite
  families could never satisfy it). B is best stated as an iff: S-data o(q^{k−2}) ⇔ Cov_γ[φ_i, Q_k] = 0 ∀i.
- **Correction to my S4 claim**: the pairing does NOT depend only on the k-jet of φ. 1D counterexample:
  φ = x^k − c x^{k+2}, c = Var(X^k)/Cov(X^{k+2},X^k), has the k-jet of x^k but Cov(φ, X^k) = 0. The
  H-uniform sufficient condition is `H_k ⊆ span{φ_i} + ℝ·1` as FUNCTIONS.
- C's count is right (k+1 > n via the two-coordinate slice; sharp for d = 2; in d > 2 the full
  binomial count fails earlier). **Major correction**: C+B(+B′) prove only LEADING-RATE blindness, not
  that no finite family recovers the jet from entire expansions. Example H = I, L_ε = ½|x|² + εx₁³,
  φ = x₁²: cubic pairing vanishes by parity, but ΔM = (ε²q²/2)·Cov(X₁², X₁⁶) + o(q²) = 45ε²q² + o(q²)
  (hand check: E X⁸ − E X² E X⁶ = 105 − 15 = 90, 90/2 = 45 ✓). So the justified statement: no fixed
  finite family is injective on homogeneous perturbations at their first rate in every degree, d ≥ 2.
- B′ (instance): defer; cheapest route is L₀ = ½H(x,x), L₁ = L₀ + Q (polynomial, order-k remainder 0,
  shrink ball). Paper: one-line remark.
- Nearby addition: "recovery modulo the invisible subspace" — the data determine [Q_k] ∈ H_k / ker T,
  i.e. the Cov_γ-orthogonal projection onto (ker T)^⊥; cheap kernel statement in Lean if free.
- Also: distinguish full Taylor jet from smooth germ (flat perturbations; already in seabed).

## Vote
- Claude: A+B+C (polynomial-diagonal form, leading-rate framing), one file `Laplace/Multi/SufficientFamilies.lean`
- GPT-6 Astra: A+B+C, restricted to polynomial/tensor diagonals, framed as leading-rate recovery

## Numerical check
Structural statements (existence/iff); the one number in play is Astra's cubic example coefficient,
checked by hand above (Gaussian moments 105, 15, 3). No further numerical check feasible.

## Step 3 plan
`Laplace/Multi/SufficientFamilies.lean`: (1) `homogPolySpan k : Submodule ℝ (EuclidD d → ℝ) := span (range monomialTest)`,
certificates for span members (continuous, polynomial growth, homogeneous) by span induction;
(2) `taylorDifference_mem_homogPolySpan` via `diag_eq_sum_monomialTest`; (3) `gaussianCovariance`
add/smul/zero in the second slot; (4) `pairingMap H φ : homogPolySpan k →ₗ[ℝ] (ι → ℝ)`;
(5) B iff `family_rates_iff_pairing_eq_zero`; (6) A `iteratedFDeriv_recovery_of_family_rates`
(kernel-zero hypothesis) + monomial family as instance sanity check; (7) C: linear independence of
`x₀^{k−j}x₁^{j}` (slice x = (s,1,0,…), `Polynomial.funext`), `ker_ne_bot_of_finrank_lt`,
`exists_kernel_of_finite_family`; (8) corollary `finite_family_leading_rate_blind` (B ∘ C).

## Result

Commit `dc7626d` on `tide/germbij-sufficient`: `Laplace/Multi/SufficientFamilies.lean` (~560 lines), imported
from `Laplace.lean`; `lake build` clean (8889 jobs), `scripts/sorries` 0/0/0/0. Two LSP rounds.

Theorems: `homogPolySpan` + certificates (`homogPolySpan_continuous/_hasPolynomialGrowth/_isHomogeneous`),
`taylorDifference_mem_homogPolySpan`, `gaussianExpectation_add/_const_mul`,
`gaussianCovariance_add_right/_const_smul_right/_comm`, `pairingMap` (the observation operator, a
`LinearMap` on the span), **B** `HigherLaplaceDomain.family_rates_iff_pairing_eq_zero`, **A**
`HigherLaplaceDomain.iteratedFDeriv_recovery_of_family_rates` (+ `_of_pairingMap_ker_eq_bot`),
`monomialTest_family_injective` (consistency with the seabed's monomial theorem), **C**
`linearIndependent_sliceMonomials`, `le_finrank_homogPolySpan`, `exists_kernel_of_finite_family`,
`finite_family_leading_rate_blind`.

Surprises: (1) my slop note S4 had claimed the pairing depends only on the k-jet of the test — false
(Astra's `x^k − c x^{k+2}` example); the H-uniform condition is spanning as functions modulo constants.
(2) The finite-family obstruction is a leading-rate statement only; the cubic example shows a
perturbation invisible at first order that reappears at `ε² q²`. Both go to the slop file.
(3) The whole file needed no new analysis: the pairing limit already carried the general test.

## Retrospective

`retrospectives/2026-09-19-14-40-tide-germbij-sufficient.tex` (compiled PDF alongside).
