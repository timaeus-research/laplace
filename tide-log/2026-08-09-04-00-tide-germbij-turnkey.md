# Tide: germbij-turnkey

**Direction (user):** continue the germbij arc (auto mode): turnkey
integrability, deriving the composite's per-t integrability premises from
global continuity of L1, L2 and continuity + compact support of psi, and the
final 1D corollary whose hypotheses are purely mathematical.

**Seabed:** laplace, main at 36e0025 (germbij arc + analytic instantiation +
analytic corollary).
**Started:** 2026-08-09T04:00Z
**Worktree/branch:** laplace-tide-germbij-turnkey / tide/germbij-turnkey
(chained off tide/germbij-analytic-corollary, rebased onto merged main;
base verified)

## Deliberation

Third follow-up of the analytic tide's list, twice re-confirmed in
subsequent retrospectives. Structure: three integrability lemmas (minorant;
uncurried pencil integrand on the restricted product; per-slice) from
continuity + compact support, plus the composed corollary
`analytic_pencil_difference_lower_bound'`. The minorant and slice lemmas are
Continuous.integrable_of_hasCompactSupport with the support transported from
psi (HasCompactSupport.intro on K = tsupport psi). The product lemma is the
only nontrivial one: bound the continuous uncurried integrand by
C * indicator(tsupport psi) via compactness of Icc 0 1 x tsupport psi, and
conclude by Integrable.mono' against the indicator majorant (finite product
measure of Ioc x tsupport). Consult launched on the exact Mathlib idiom.

## Numerical check

Not feasible: the statement asserts integrability (no closed form). The
downstream inequality is unchanged from prior tides.

## GPT-5.6 Sol v1 (returned)

Saved verbatim: `gpt55_germbij-turnkey_v1.md`. Endorsed the majorant plan
and supplied the exact idiom set: joint continuity via fun_prop (never
separate continuity), `IsCompact.exists_bound_of_continuousOn`,
`Measure.prod_restrict` (+ restrict_univ) for the restricted-product
rewrite, `ae_restrict_mem` for the a.e. membership, `Measure.prod_prod` +
`IsCompact.measure_lt_top` for finiteness of the cylinder, indicator
majorant via `integrable_indicator_iff` + `integrableOn_const`, and
`Integrable.mono'` to close. The implementation followed it directly.

## Vote

Carried over (third follow-up of the analytic tide, re-confirmed twice);
the consult was tactical (idiom-level) rather than a candidate vote.

## Result

`Laplace/Turnkey.lean`, registered in `Laplace.lean`. Declarations, all
sorry-free, zero warnings:
- `Laplace.integrable_minorant`, `Laplace.integrable_slice` (continuity +
  compact support via `HasCompactSupport.intro` on tsupport psi)
- `Laplace.integrable_pencil_product` (the restricted-product integrability,
  by the cylinder-indicator majorant)
- `Laplace.analytic_pencil_difference_lower_bound'`: the turnkey 1D
  germbij Theorem 7.3 bound. Hypotheses: L1, L2 analytic at 0 with
  differing germs, globally continuous, nonnegative, L1 + L2 <= C0 w^2 on
  [0, R]; psi continuous, compactly supported, nonnegative, = 1 on [0, R].
  Conclusion: exists m, c > 0, r0 in (0, R] with
  c * t * t^(-(m:R) - 1/2) <= Delta_t((L2 - L1) psi) for all t >= 4/r0^2.
  No integrability premises remain.

Two compile iterations: `isCompact_Icc`'s implicit endpoints unified with a
stray `t` (fixed by explicit (a := 0) (b := 1)); an anonymous-constructor
membership inside a rw argument needed a named `have`. Full `lake build`
passes; `scripts/sorries` 0/0/0/0.

## Retrospective

Retrospective: laplace/retrospectives/2026-08-09-04-00-tide-germbij-turnkey.tex
