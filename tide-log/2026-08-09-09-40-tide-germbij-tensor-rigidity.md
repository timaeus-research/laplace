# Tide: germbij tensor programme J2 (Gaussian covariance rigidity)

**Direction (user):** standing auto-mode commission on the germbij
note; opening tide of the degree-k tensor-recovery programme, staged
J0-J7 by the scoping consult archived verbatim in this directory
(`tide-log/gpt56_tensor_scoping_v1.md`).
**Seabed:** laplace main at d22cdcf (H-recovery milestone complete,
PRs #66-#73).
**Started:** 2026-08-09T09:40 local

## Candidates

The consult's ruling (section 3): the minimal good first tide is J2
with the needed slices of J0/J1 inline, one file
`Laplace/Multi/GaussianCovariance.lean`. Target theorem:

    homogeneous_eq_zero_of_gaussianCovariance_self_eq_zero :
      H.PosDef → 0 < k → Continuous Q → HasPolynomialGrowth Q →
      IsHomogeneousOfDegree k Q → gaussianCovariance H Q Q = 0 →
      Q = 0

Components (all consult-specified):
1. J0 slice: `HasPolynomialGrowth` + closure (add/mul/const) +
   `integrable_mul_quadKernel_of_polynomialGrowth` (splits into
   quadKernel_integrable + quadKernel_integrable_pow, which IS the
   norm-moment form the consult asked to verify — confirmed).
2. J1 slice: `continuous_eq_zero_of_integral_mul_quadKernel_eq_zero`
   (continuous nonneg, zero weighted integral ⇒ ≡ 0), by the direct
   ball argument: continuity gives f ≥ ε/2 and K ≥ K(x₀)/2 on a
   ball, setIntegral_ge_of_const_le + measure_ball_pos, against
   setIntegral_le_integral.
3. J2: `gaussianExpectation`/`gaussianCovariance` defs (weighted
   integrals, NOT the probability-measure variance API — the consult
   warns MemLp friction), the variance identity
   Cov(Q,Q) = E[(Q - EQ)²], and the target: variance zero ⇒
   (Q-EQ)²·K integrates to zero ⇒ Q ≡ EQ ⇒ (homogeneity, k > 0,
   Q(0) = 0) Q = 0.

Rulings adopted: no Isserlis, no MvPolynomial, no monomial moments —
abstract continuous polynomial-growth tests suffice (only P, Q, PQ,
Q² integrals ever occur).

## Numerical check

Not feasible beyond structure: the statement is a rigidity
implication (zero variance ⇒ zero function), no closed form. The
variance identity itself is exact algebra verified in the proof.

## Vote

- Claude: J2 as the opening tide (the consult's own ruling, section 3).
- GPT-5.6 Sol: same (archived).

Agreed.
