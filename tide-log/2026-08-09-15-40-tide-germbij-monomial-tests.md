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
