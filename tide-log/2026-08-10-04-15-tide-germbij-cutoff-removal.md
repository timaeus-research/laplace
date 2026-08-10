# Tide: germbij cutoff removal (inverse perimeter 3/3)

**Direction (user):** "Fix the docstring overclaim and proceed with the tides
to fix the gaps" — gap 3 of the 2026-08-10 fidelity review (finding F3): the
note's premise quantifies over φ ∈ C_c^∞(U) while the Lean data is bare
monomials; the cutoff-removal implication was unformalised.
**Seabed:** laplace, branch tide/germbij-hbase-discharge (stacked; base
7b1e769, PRs #109/#112 in flight).
**Started:** 2026-08-10T04:15Z

## Seabed snapshot

- Tides 1–2 (this stack): `hessian_recovery_of_superPoly_moments`,
  `smooth_positive_jet_recovery_of_superPoly_moments`,
  `analytic_germ_recovery_of_superPoly_moments_free` — recovery from
  superPoly-matched BARE monomial/second-moment families, no base case.
- `LocalLaplaceDomain.rescaled_lower` at q = 1: `c‖x‖² ≤ L x − L 0` on U —
  the loss gap the tail estimate needs.
- `tendsto_integral_rescaled` (RescaledDCT): ∫ integrand(h) q →
  ∫ h·quadKernel; at h ≡ 1 gives the denominator's positive limit;
  `eventually_integrand_one_pos` (used in LocationRecovery).
- `posteriorIntegral_eq` (dilation identity), `integrable_integrand`
  (LocationRecovery: continuous polynomial-growth integrands integrable at
  each q > 0).
- Mathlib `ContDiffBump`: `one_of_mem_closedBall`, `support_eq`,
  `tsupport_eq` (= closedBall c rOut), `hasCompactSupport`, `contDiff`;
  instances exist on finite-dimensional real normed spaces (EuclidD ✓).
- Mathlib `tendsto_pow_mul_exp_neg_atTop_nhds_zero`. No exponential→
  SuperPoly packaging exists in the seabed (FlatInvisible proved its
  superpolynomial bound bespoke).

## Candidates v1 (Claude)

**A (backed): tail lemma + CC-data bridge + composed note-literal
corollaries.** New file `Laplace/Multi/CutoffRemoval.lean`:

1. `superPoly_of_eventually_abs_le_exp` — if |f t| ≤ K e^{−δt} eventually
   (δ > 0), then `SuperPoly f`. (t^N e^{−δt} → 0 by Mathlib, rate-composed.)
2. `posteriorMoment_cutoff_tail` (per domain): for continuous
   polynomial-growth P and continuous χ with 0 ≤ χ ≤ 1 and χ ≡ 1 on
   ball(0,r), r > 0:
   `SuperPoly (fun t ↦ A.posteriorMomentT P t − A.posteriorMomentT (P·χ) t)`.
   Proof: at scale q, the moment difference is
   ∫ integrand((P(1−χ))(q•·)) / ∫ integrand(1) (prefactors cancel; pI
   linearity via dilation-transported integrability). On the numerator's
   support ‖q•x‖ ≥ r, so the exponent obeys BOTH (L(q•x)−L0)/q² ≥ c‖x‖²
   and ≥ cr²/q²; halving the rate, e^{−G} ≤ e^{−cr²/(2q²)}·e^{−(c/2)‖x‖²},
   and |P(q•x)| ≤ C(1+‖x‖^n) for q ≤ 1, so |numerator| ≤ M e^{−cr²/(2q²)}.
   Denominator eventually ≥ Z_H/2 > 0 by the merged limit. Compose with
   t = q⁻² (e^{−cr²/(2q²)} = e^{−(cr²/2)t}) and (1).
3. `superPoly_moments_of_ccData` (per domain pair): if for every smooth
   compactly-supported φ with tsupport φ ⊆ A.U and ⊆ B.U the moment
   families agree beyond all orders, then they agree for every smooth
   polynomial-growth P (no support restriction). Pick a `ContDiffBump`
   with rIn < rOut < min(A.delta, B.delta); split
   m_A(P) − m_B(P) = [m_A(P) − m_A(Pχ)] + [m_A(Pχ) − m_B(Pχ)] +
   [m_B(Pχ) − m_B(P)]: tails by (2), middle is data at φ = Pχ (smooth by
   `ContDiff.mul`, compactly supported by `HasCompactSupport.mul_left`,
   tsupport ⊆ closedBall rOut ⊆ ball delta ⊆ U). SuperPoly closed under
   add/neg (inline or small helpers).
4. Composed corollaries `smooth_positive_jet_recovery_of_ccData` and
   `analytic_germ_recovery_of_ccData`: the tide-2 headlines with the
   superPoly data hypotheses replaced by the C_c^∞-data premise, scoped
   per package pair (∀ k h2, ∀ φ …(A k h2).U…), instantiated at
   P = w_i·w_j and P = monomialTest m (smooth: finite products of
   coordinate CLMs; polynomial growth: merged certificates).

**B (smaller).** (1)–(3) only, composition deferred. Against: the
composition is a few dozen lines and is the point of the perimeter arc.

**C (bigger).** A + the located first-moment CC form (composing location
recovery too). Against: location recovery's data is located moments of a
different shape; a natural follow-up, not this tide.

Claude's inclination: A.

## GPT-5.6 Sol v1

Verbatim in `tide-log/gpt_tide_cutoff_removal_v1.md`. Tail estimate correct
in substance: on the support both G ≥ c‖x‖² and G ≥ cr²/q² hold, so
G ≥ ½c‖x‖² + ½cr²/q² — split as an average, not by rate-halving one bound;
growth and 0 ≤ χ ≤ 1 give the C(1+‖x‖^n) factor for q ≤ 1; denominator
eventually ≥ Z_H/2 excludes junk quotients; do linearity at the RESCALED
level after posteriorIntegral_eq (integrable_integrand covers both
observables) — cleaner than transporting unrescaled integrability. CC
premise: pairwise-U shape adequate ("tests supported in the common
localization region" — do not gloss as a literal single C_c^∞(U) unless
domains are identified; a V-interface would be cleaner but the intersection
form suffices). Smoothness: coordinate CLMs + finite products, plumbing
only. A is the minimal complete target.

## Vote

- Claude: A.
- GPT-5.6 Sol: A.

Agreed: **A — exponential→SuperPoly helper, per-domain cutoff tail,
CC-data bridge, and the composed note-literal corollaries.**

## Numerical check

Not feasible: inequality/structural content (exponential tail domination
over merged components; no closed form to evaluate).

## Step 3 hand-off

New file `Laplace/Multi/CutoffRemoval.lean`:
`superPoly_of_eventually_abs_le_exp`, `Laplace.SuperPoly.add`/`.neg`
helpers, `HasPolynomialGrowth.comp_smul`, `posteriorMoment_eq_integrand_div`,
`posteriorMoment_cutoff_tail`, `superPoly_moment_of_ccData` (ContDiffBump),
`contDiff_monomialTest` + coordinate-pair observables, and the composed
`smooth_positive_jet_recovery_of_ccData` /
`analytic_germ_recovery_of_ccData`.
