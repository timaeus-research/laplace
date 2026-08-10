# Tide: grand composition coda (the package-derivation wrapper)

**Direction (user):** "Go ahead with those queued items" (2026-08-10)
— the wrapper was queued as the remaining distance between the
located headlines and the note's prose hypotheses, and was named in
the original approved tide direction ("derive the package family from
a smooth nondegenerate-minimum setup").

**Seabed:** laplace main at 9171d40 (grand composition merged).

**Started:** 2026-08-10T19:30Z

## Corpus reconnaissance (before the consult)

Much more exists than the plan assumed:

- `LocalQuadraticApprox.ofContDiff` (QuadLowerBound.lean): C² +
  gradient zero + posdef Hessian → the quadratic package, with
  quadratic_peano PROVEN (corpus theorem `quadratic_peano`) and the
  eigenvalue bound from `qform_coercive`.
- `LocalQuadraticApprox.exists_local_lower_bound`: the small-ball
  coercivity ∃ δ c, ∀ q x, 0 < q → ‖q•x‖ ≤ δ → c‖x‖² ≤ rescaled
  quotient — exactly rescaled_lower's shape for U := ball 0 δ.
- `ray_iteratedDeriv` (RadialTaylor.lean): the ray-derivative
  identity AT 0. For the Lagrange route it needs the interior-point
  generalization (the proof's composition identity is global; only
  the final map_zero step specializes).
- Mathlib `taylor_mean_remainder_lagrange` (1D) exists.

## Candidates v1 (Claude)

`Laplace/Multi/PackageConstructor.lean`:

1. `LocalLaplaceDomain.ofContDiff`: from ContDiff ℝ 2 L + fderiv 0 =
   0 + (hessianMatrix L).PosDef, with U := ball 0 δ from
   exists_local_lower_bound (measurable: open), c := the same, delta
   := δ, measurable_L from continuity. ~25 lines, unambiguous.
2. `ray_iteratedDeriv_at`: the interior-point generalization. ~20
   lines.
3. `taylorRemainder_bound_of_contDiff`: for C^k L (k ≥ 1) and R > 0,
   ∃ C ≥ 0, ∀ y ∈ ball 0 R, |L y - Σ_{j<k} taylorHomogeneousTerm j
   L y| ≤ C‖y‖^k — via 1D Lagrange along rays with the sup of
   ‖iteratedFDeriv k L‖ on closedBall 0 R (compactness bound). The
   tide's real work (~150-200 lines: taylorWithinEval vs
   iteratedDeriv bridging on Icc, ray endpoints).
4. `HigherLaplaceDomain.ofContDiff` (k): assembly, contDiff_k from
   ContDiff ℝ ⊤ by of_le, taylorRadius := δ. ~40 lines.
5. The headline family: `higherLaplaceDomain_family_ofContDiff`
   producing ∀ k, 2 < k → HigherLaplaceDomain k L (hessianMatrix L)
   — which is exactly what located_positive_jet_recovery_of_ccData
   and the analytic capstone consume.

## GPT-5.6 Sol v1

Verbatim at `tide-log/gpt56_package_derivation_v1.md`. Headline
recommendation: for ONE tide, the wrapper should ASSUME the per-k
fixed-ball Taylor bounds as a single hypothesis (htaylor) and derive
everything else — 60-120 lines, low risk — with the general
C^k ⇒ Taylor-bound theorem (the radial route: interior-point ray
derivatives, 1D Lagrange, compact-ball sup, coefficient
identification) as its own follow-up tide (70-160 additional lines,
API-sensitive). Two load-bearing observations: (i) the structures
store GLOBAL ContDiff and Measurable, so ContDiffAt-only input
cannot fill them — take hcont : ∀ k, ContDiff ℝ k L; (ii) reuse the
existing corpus quadratic_peano (which produces hessianMatrix L) and
transfer to H by a diagonal-equality hypothesis
hdiag : ∀ y, qform (hessianMatrix L) y = qform H y, rather than
planning around a Mathlib multivariate Peano theorem. Same ρ for U,
delta, and taylorRadius makes both inclusion fields reflexive.

## Vote

- Claude: Option 1 (the wrapper with htaylor assumed), candidates
  1/4/5 of v1 merged into the single family constructor; candidates
  2/3 (the radial Taylor theorem) deferred to the follow-up tide.
- GPT-5.6 Sol: the same ("Rank: 1 — recommended").

## Numerical check

Not feasible: structure assembly (radius shrinking and field
wiring); no closed forms.

## Result

`Laplace/Multi/PackageConstructor.lean` (~120 lines), all gates
green after ONE fix (the catalogued beta_reduce-before-rw in the
congr' per-point goal of the Peano transfer):

- `LocalQuadraticApprox.ofBareSetup`: C² + gradient zero +
  diagonal-matched posdef H → the quadratic package (corpus
  quadratic_peano transferred via hdiag; qform_coercive for lambda).
- `higherLaplaceDomainFamily_ofTaylorBounds`: the consult's Option 1
  verbatim — hcont (global per-k smoothness), hgrad, hdiag, hH, and
  the per-order Taylor-bound hypothesis htaylor produce
  ∀ k, 2 < k → HigherLaplaceDomain k L H, with ρ := min δ r serving
  as region, delta, and Taylor radius (both inclusions reflexive),
  coercivity from exists_local_lower_bound restricted to the shrunk
  ball, measurable_L from continuity.

The located headlines' package hypotheses are now dischargeable from
a bare setup modulo htaylor.

### Suggested follow-ups

- The radial C^k Taylor-bound tide (consult Rank 2): interior-point
  ray_iteratedDeriv generalization (the corpus lemma is at 0 only;
  its composition proof generalizes), 1D taylor_mean_remainder_lagrange,
  compact-ball sup of ‖iteratedFDeriv k L‖, coefficient
  identification — discharging htaylor from hcont alone (70-160
  lines, API-sensitive per the consult).
- LocationRecovery module docstring update (the "not formalised
  here" sentence now discharged by TranslationBridge) — fold into
  the next PR touching that file.
