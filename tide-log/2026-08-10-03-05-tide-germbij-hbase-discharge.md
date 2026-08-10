# Tide: germbij hbase discharge (inverse perimeter 2/3)

**Direction (user):** "Fix the docstring overclaim and proceed with the tides
to fix the gaps" — gap 2 of the 2026-08-10 fidelity review: the shift-
normalization wrapper discharging the j = 0 constant assumption, plus the
recomposed hbase-free headline (findings F1 remainder + F2).
**Seabed:** laplace, branch tide/germbij-hessian-bridge (stacked; base
commit 5812972, PR #109 in flight).
**Started:** 2026-08-10T03:05Z

## Seabed snapshot

- Tide 1 (this stack's parent): `hessian_recovery_of_superPoly_moments` —
  superPoly second-moment data ⟹ H₁ = H₂.
- `smooth_jet_recovery_of_superPoly_moments` (ExpansionBridge.lean:192) —
  the headline to be freed of `hbase : ∀ j < 3, iteratedFDeriv j L₁ 0 =
  iteratedFDeriv j L₂ 0` and of the shared `H`.
- `posteriorIntegral` (HessianMoments.lean:33) uses `exp (-(L w / q²))`
  with the RAW loss — shift invariance of the normalized moment is a
  one-step cancellation (`exp (-(c/q²))` factors out of numerator and
  denominator), not definitional.
- `taylorHomogeneousTerm` (RadialTaylor.lean:30); GaussAbsorb has the ray
  uniqueness argument (`rayExpansion_taylor`/`rayExpansion_quad`,
  `taylorHomogeneousTerm_one_eq_zero`, `taylorHomogeneousTerm_two_eq_qform`)
  but at `ForwardExpansionDomain` (Peano field); here we need the
  `HigherLaplaceDomain k` (k ≥ 3) mirror using the `O(‖y‖^k)` remainder.
- `iteratedFDeriv_eq_of_diag_eq` (MultilinearDiagonal.lean:304) — symmetric
  tensors with equal diagonals are equal; needs `IsSymm` at the order used.
- Mathlib: `iteratedFDeriv_add_apply` (ContDiff/Operations.lean:223),
  `iteratedFDeriv_const_of_ne` (ContDiff/Basic.lean:140) — shift
  invariance of derivatives of positive order.
- Stage-1 `isAsymptoticExpansionTo_coeff_eq` (AsymptoticPolynomial.lean) —
  the coefficient uniqueness the ray argument consumes.

## Candidates v1 (Claude)

**A (backed): the full hbase discharge in one tide.** New file
`Laplace/Multi/ShiftNormalization.lean` (or split naming below):

1. *Shift transport.* `LocalLaplaceDomain.shift (A) (c : ℝ) :
   LocalLaplaceDomain (fun w ↦ L w + c) H` (all fields invariant: the
   quadratic Peano and coercivity see only `L · − L 0`; measurability by
   `Measurable.add_const`) and `HigherLaplaceDomain.shift` (ContDiff of
   `+const`; Taylor remainder invariant since only the degree-0 diagonal
   term absorbs `c`).
2. *Moment invariance.* `(A.shift c).posteriorMoment = A.posteriorMoment`
   and likewise `posteriorMomentT`: `posteriorIntegral_{L+c} f q =
   exp (-(c/q²)) · posteriorIntegral_L f q` (pull the constant out of the
   integral), then `mul_div_mul` cancellation in the normalized quotient
   (unconditional: junk-consistent even where the denominator vanishes).
3. *Ray uniqueness at HigherLaplaceDomain level* (k ≥ 3):
   `taylorHomogeneousTerm 1 L = 0` and
   `taylorHomogeneousTerm 2 L z = qform H z / 2` — mirror of the
   GaussAbsorb pair with the `O(‖y‖^k)` remainder along rays in place of
   the Peano field (`O(t^k) ⊆ o(t²)` for k ≥ 3).
4. *Tensor extraction.* j = 1: `iteratedFDeriv ℝ 1 L 0 = 0` (a 1-linear
   map vanishing on diagonals vanishes: `Fin 1` inputs are constant
   functions). j = 2: equal diagonals from `T₂ = qform H/2` + `H₁ = H₂`
   (tide 1), then `iteratedFDeriv_eq_of_diag_eq` with `IsSymm` at order 2
   taken as a hypothesis (same documented debt as the existing k > 2
   `hsymm`; Mathlib's C² symmetry is `second_derivative_symmetric`-shaped
   and connecting it to `iteratedFDeriv 2` `IsSymm` is a separate
   excursion).
5. *Recomposed headline* `smooth_jet_recovery_of_superPoly_moments'`
   (final name TBD): hypotheses — packages `A : ∀ k, 2 < k →
   HigherLaplaceDomain k L₁ H₁`, `B : … L₂ H₂` (SEPARATE H's), `hsymm₁/₂ :
   ∀ k, 1 < k → (iteratedFDeriv ℝ k L· 0).IsSymm`, `hdata₂` (superPoly
   second-moment families), `hdatak` (superPoly monomial families, k > 2);
   conclusion — `∀ j, 0 < j → iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j
   L₂ 0`. Proof: H₁ = H₂ by tide 1; subst; shift L₂ by c := L₁ 0 − L₂ 0;
   hbase j=0 by construction, j=1 by (4), j=2 by (4); data transports by
   (2); apply the existing headline; un-shift the conclusion at j ≥ 1 by
   Mathlib shift invariance.
6. *Analytic corollary rewrap* `analytic_germ_recovery_of_superPoly_moments'`:
   same data + `AnalyticAt` both ⟹ germ equality mod constant, now without
   hbase (compose 5 with the merged `analytic_germ_eq_of_jet_eq`, whose
   hypotheses are exactly positive-order jet equality).

**B (split).** Same content over two tides (shift machinery, then
recomposition). Rationale against: the shift machinery has no standalone
value and the recomposition is its only consumer; the parent deliberation
already assigned the tensor tie here.

**C (defer j=2 symmetry debt).** As A but attempt to DERIVE IsSymm at
order 2 from `ContDiff ℝ k L` via Mathlib's second-derivative symmetry.
Riskier (API archaeology; the seabed CLAUDE.md records that C^k symmetry
API at general order is ω-only, order-2 exists in some form); the payoff
is two fewer hypotheses on the composed statement.

Claude's inclination: A, with C's derivation attempted opportunistically
during formalisation and abandoned without ceremony if the API fights back
(the hypotheses are honest documented debt either way).

## GPT-5.6 Sol v1

Verbatim in `tide-log/gpt_tide_hbase_discharge_v1.md`. Candidate A sound;
(a) shift invariance exact for EVERY q (the nonzero exponential factor
cancels field-theoretically even where the denominator vanishes; keep U
unchanged); (b) fixed-ball remainder suffices for the ray argument
(eventual membership); (c) j=1 valid with no symmetry; (d) recomposition
transports trivially, but PIN the local packages carrying hdata₂ (use the
k=3 projections) since the family's U fields may differ across k. Keep
order-2 IsSymm a hypothesis (∀ k, 1 < k → IsSymm); deriving from ContDiff
is avoidable API work, attempt opportunistically only. Shifting L₂ has
the correct sign.

## Vote

- Claude: A (with hdata₂ pinned to the k=3 projections, IsSymm at 1 < k).
- GPT-5.6 Sol: A.

Agreed: **A — shift transport + ray uniqueness + hbase-free recomposed
headline `smooth_positive_jet_recovery_of_superPoly_moments` and the
analytic corollary rewrap.**

## Numerical check

Not feasible: structural (package transport + composition of
numerically-verified components).

## Step 3 hand-off

New file `Laplace/Multi/ShiftNormalization.lean`: `iteratedFDeriv_shift`,
`LocalQuadraticApprox.shift`, `LocalLaplaceDomain.shift` +
`posteriorIntegral_shift`/`posteriorMoment_shift`/`posteriorMomentT_shift`,
`HigherLaplaceDomain.shift` (k ≠ 0), the HigherLaplaceDomain-level ray pair
(`rayExpansion_taylor'` at 2 < k; quad side stated at LocalQuadraticApprox),
`taylorHomogeneousTerm_one_eq_zero'`/`_two_eq_qform'`,
`iteratedFDeriv_one_eq_zero`, `iteratedFDeriv_two_diag`, headline
`smooth_positive_jet_recovery_of_superPoly_moments`, and
`analytic_germ_recovery_of_superPoly_moments_free`.

## Result

Committed on tide/germbij-hbase-discharge (206286d):
`Laplace/Multi/ShiftNormalization.lean` — `iteratedFDeriv_shift`, the three
package `shift` transports, `posteriorIntegral_shift`/`posteriorMoment_shift`/
`posteriorMomentT_shift` (exact, every scale), `LocalQuadraticApprox.rayExpansion_quad`,
`HigherLaplaceDomain.rayExpansion_taylor` (fixed-ball remainder),
`taylorHomogeneousTerm_one_eq_zero`/`_two_eq_qform` (higher-domain level),
`iteratedFDeriv_one_eq_zero`, `iteratedFDeriv_two_diag`, headline
`smooth_positive_jet_recovery_of_superPoly_moments`, and
`analytic_germ_recovery_of_superPoly_moments_free`. Zero sorries, three
mechanical iterations (un-beta-reduced integrand after integral_const_mul →
`show`; ContDiff grades are WithTop ℕ∞ not ℕ∞; per-index ContDiffAt needed
range membership). Surprise: the j = 0 discharge has literally zero analytic
content once moment shift-invariance is an identity.

## Retrospective

Retrospective: laplace/retrospectives/2026-08-10-03-05-tide-germbij-hbase-discharge.tex
