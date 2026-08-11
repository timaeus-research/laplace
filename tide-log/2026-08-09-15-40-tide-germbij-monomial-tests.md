# Tide: germbij monomial test families

**Direction (user):** standing auto-mode commission; first
consult-flagged follow-on after the tensor programme closed (J0-J7,
PRs #74-#82).
**Seabed:** laplace, main at 270eed2.
**Started:** 2026-08-09T15:40 local

## Candidates v1 (Claude)

The J6/J7 data hypotheses quantify over EVERY continuous
polynomial-growth homogeneous test P of degree k. An experimentalist
measures finitely many observables. The gap: the diagonal difference
Q(x) = (1/k!)(D^k L1 - D^k L2)(x,...,x) instantiated in J6's proof is
itself a homogeneous POLYNOMIAL, hence a finite linear combination of
the monomials x^alpha, |alpha| = k.

1. **`rescaledMoment` linearity + monomial expansion + J6'
   (`iteratedFDeriv_recovery_of_monomial_rates`)**: if for every
   multi-index alpha with |alpha| = k the pairwise rescaledMoment
   difference at x^alpha is o(q^(k-2)), the k-th derivative tensors
   agree. Proof plan: (a) expand the CMM diagonal
   (iteratedFDeriv applied to (fun _ => x)) into the finite monomial
   sum via multilinearity over the basis (ContinuousMultilinearMap
   applied to sums, Finset expansion over functions Fin k -> Fin d);
   (b) rescaledMoment is linear in the test (integral linearity;
   integrability from the polynomial-growth adapter, already in
   GaussianCovariance); (c) IsLittleO is closed under finite linear
   combinations; (d) feed J6. No new analysis; the only real Lean
   work is (a) with continuity/growth certificates per monomial.
2. **J7' wrapper (`finite_jet_recovery_of_monomial_rates`)**: same
   weakening propagated through the jet induction: data = monomial
   moments at each degree 2 < k <= N only ((d+k-1 choose k) tests
   per degree). Trivial once 1 lands.
3. **Full MvPolynomial bridge**: an API identifying homogeneous
   MvPolynomial evaluations with our test class, then restating J6/J7
   over MvPolynomial. Heavier, more general, probably over-engineered
   for the note's claim.

Claude's view: 1 + 2 in one tide; 3 is over-engineering (specialise
early). The measured statement matches the note's "the moments
m_alpha(t)" phrasing (data indexed by multi-indices alpha), so 1+2 is
also the faithful formalisation of what Theorem 3.1's proof actually
consumes.

## GPT-5.6 Sol v1

Archived verbatim in `tide-log/gpt56_monomial_shape_v1.md`. Summary:
candidates 1+2 correct; ordered-tuple indexing (m : Fin k -> Fin d)
is the right Lean representation (multi-indices would add orbit/
multinomial bookkeeping for no gain); d = 0 is vacuously fine. Key
staging correction: monomial rates canNOT discharge J6's universal
quantifier by linearity (monomials span homogeneous POLYNOMIALS, not
all homogeneous functions) — extract the one-test core first:

1. J6-point: recovery from the rate at Delta_k alone (the proof
   already only uses hdata there).
2. Existing J6 becomes a trivial wrapper.
3. Algebraic coordinate expansion (diagonal = finite monomial sum).
4. Finite-sum moment-rate closure (linearity + IsLittleO closure).
5. J6-prime (monomial rates). 6. J7-prime.

Consult also flags J6-point as itself the best minimal candidate: it
isolates that the analytic Laplace argument needs ONE test, with
determining families a mechanism for deriving that test's rate.

## Vote

- Claude: candidates 1+2 with the consult's staging (J6-point core,
  then monomial closure, then the induction wrapper).
- GPT-5.6 Sol: same (sequence 1-6 above; MvPolynomial rejected as
  conversion infrastructure). Agreed.

## Numerical check

Not feasible in the closed-form sense: the statements are structural
(a hypothesis-weakening refactor plus an algebraic expansion over
verified components). The expansion identity itself is
kernel-checked at the point of use (diag_eq_sum_monomialTest).

## Progress

- `Laplace/Multi/MonomialTests.lean` (consult-independent prep,
  compiled clean before the consult returned): monomialTest,
  certificates (continuity via PiLp.continuous_apply, growth via
  coordinate-norm bound, homogeneity), euclid_eq_sum_single (via
  OrthonormalBasis.sum_repr on EuclideanSpace.basisFun — the direct
  Finset.sum_apply route hits .ofLp coercion friction), and
  diag_eq_sum_monomialTest (MultilinearMap.map_sum with explicit g +
  map_smul_univ; the consult's predicted coercion friction was real
  and resolved by calc through toMultilinearMap with rfl bridges).

## Result

Committed on tide/germbij-monomial-tests (PR #84):
`Laplace/Multi/MonomialTests.lean` (~250 lines) plus the J6-point
refactor of `DegreeRecovery.lean`. Theorems:
`iteratedFDeriv_recovery_of_taylorDifference_rate` (one-test core),
`HasPolynomialGrowth.sub`, `monomialTest` + certificates,
`euclid_eq_sum_single`, `diag_eq_sum_monomialTest`,
`rescaledMoment_finset_sum`,
`iteratedFDeriv_recovery_of_monomial_rates`,
`finite_jet_recovery_of_monomial_rates`,
`smooth_jet_recovery_of_monomial_rates`. Zero sorries, zero warnings.

Surprises: (1) every stage after the prep file compiled on the FIRST
build — the consult's staging held exactly; (2) the direct
`Finset.sum_apply` route to sum-of-singles hits `.ofLp` coercion
friction in this Mathlib pin; `OrthonormalBasis.sum_repr` on
`EuclideanSpace.basisFun` avoids it entirely (consult predicted
this); (3) one beta-unreduced-goal trap in the J6 wrapper's
homogeneity leg (catalogued class, `simp only []` fix).
