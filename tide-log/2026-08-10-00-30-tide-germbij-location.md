# Tide: germbij location recovery (nondegenerate core, item D)

**Direction (user):** the nondegenerate core; audit consult (archived
in the expansion-bridge tide log) item D.
**Seabed:** laplace, stacked on tide/germbij-expansion-bridge
(PR #93, unmerged at start).
**Started:** 2026-08-10T00:30 local

## Candidates

Per the audit consult section 4 (deliberation of record):

1. Anchored coordinate-moment limit: posteriorMoment (w i) q -> 0
   (from the merged q^-1 E[w_i] -> 0 by multiplying back the q).
2. Located moments: for a loss anchored at 0 and a location c, the
   located moment is the anchored moment of the translated
   observable; the honest translated-integral form recorded via
   measure translation invariance. Located coordinate moments tend
   to c_i (observable splits as c_i + y_i; integrand additivity;
   spectator normalization).
3. Two-loss location equality: superpolynomially matched located
   first-moment families force c1 = c2 (limits along t -> infinity
   through the q = (sqrt t)^-1 substitution; uniqueness of limits).
   "The observable family must contain the uncentered coordinate
   functions" — hence located moments at uncentered coordinates.

## Vote

- Claude: as staged. - GPT-5.6 Sol: section 4 of the audit consult
  is exactly this staging. Agreed on record.

## Numerical check

Not feasible: structural limit plumbing over merged components.

## Result

Committed on tide/germbij-location:
`Laplace/Multi/LocationRecovery.lean` (~230 lines). Theorems:
`integrable_integrand` (Local-level mirror of slice integrability,
via measurable_L + coercivity), `integrand_add`,
`tendsto_posteriorMoment_coord` (anchored coordinate moments vanish),
`locatedMoment`/`locatedMomentT` (located moments as anchored moments
of translated observables), `tendsto_locatedMoment_coord` (located
coordinate moments recover the location; the split c_i + q-rescaled
coordinate with spectator normalization),
`tendsto_inv_sqrt_nhdsGT_zero`, and
`location_eq_of_superPoly_first_moments`: superpolynomially matched
located first-moment families force equal minima — the w* clause of
Theorem 3.1. Zero sorries, zero warnings.

Iterations: the honest translated-integral form via
integral_add_left_eq_self hit an AddGroup (Fin d) instance-synthesis
confusion on PiLp and was dropped as non-load-bearing (the located
definition is itself the faithful object); the integral_add step
needed the CATALOGUED type-ascribed single-lambda witnesses; the
final quotient algebra used the catalogued fold-atoms discipline
(deterministic mul_div_mul_left chain instead of field_simp).
