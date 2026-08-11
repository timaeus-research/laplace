# Tide: grand composition convenience capstone (bare recovery)

**Direction (user):** the optional end-to-end statement recorded in
the radial-taylor tide's follow-ups, folded into the standing
"continue with what you think best".

**Seabed:** laplace, branch `tide/germbij-radial-taylor` (stacked;
parent PR #129 in flight).

**Started:** 2026-08-10T21:20Z

## Candidate

`Laplace/Multi/BareRecovery.lean`:

`located_analytic_germ_recovery_of_bare_setup` — one theorem whose
hypotheses are only the prose-level facts:

- global smoothness of the two actual losses (∀ k, ContDiff ℝ k Λᵢ);
- centred first/second-order data: vanishing gradient of the
  recentred loss and the diagonal-matched positive-definite matrix
  (stated for y ↦ Λᵢ (pᵢ + y) at 0 — the spatial
  iteratedFDeriv-translation bridge is deliberately NOT built, per
  the grand-composition consult's scope note);
- analyticity at the minima;
- ONE physical data premise, quantified over localization radii: for
  every pair ρ₁, ρ₂ > 0 and every smooth compactly supported test in
  the common region V (⊇ balls around both minima), the physical
  moment families over translatedRegion pᵢ (ball 0 ρᵢ) agree beyond
  all orders.

Conclusion: p₁ = p₂ ∧ germ equality at 𝓝 p₁ modulo the constant.

Proof: build the package families with
higherLaplaceDomainFamily_ofContDiff (centred losses; ContDiff
transported by composition with the shift); the constructed packages'
regions are balls by construction, so the radius-quantified premise
instantiates at the (choice-extracted) radii — the one risk item is
whether `(family k h2).toLocalLaplaceDomain.U = Metric.ball 0 ρ★`
closes by rfl through the tactic-built definition; fall back to a
consult if defeq fights. Then the located analytic capstone.

## GPT-5.6 Sol

Covered by the grand-composition and package-derivation consults (no
new mathematical content; the radius-quantified premise is the
"common actual open region" option 2 of the former, specialized to
ball localizations).

## Vote

- Claude: the single convenience theorem.
- GPT-5.6 Sol (via the two prior consults): in scope as composed.

## Numerical check

Not feasible: pure composition.

## Result

`Laplace/Multi/BareRecovery.lean` (~120 lines), all gates green
after one fix round with a reusable lesson:

- `located_analytic_germ_recovery_of_bare_setup`: the one-theorem
  form. Hypotheses: global smoothness of the two actual losses,
  centred gradient/Hessian data, analyticity at the minima, the
  common region with balls around both minima, and the
  radius-quantified physical data premise. Conclusion: p₁ = p₂ and
  germ equality modulo the constant.
- The fix-round lesson: `have A := <constructor> ...` ERASES the
  definition (the binder is opaque), so a later
  `(A k h2).U = ball 0 ρ := rfl` cannot reduce — pass the
  constructor application INLINE (or use `let`). And rather than
  matching the constructor's internal `choose` chains (which are
  Classical-opaque even under delta), instantiate the premise at the
  package's own `delta` field: the constructor sets U and delta to
  the same ρ, so `U = ball 0 delta` is rfl and positivity is the
  `delta_pos` field. Constructor postconditions that matter to
  callers are best consumed through fields, not reconstructed.

### Suggested follow-ups

- germbij.tex markers for the three constructor/end-to-end theorems
  (exists_taylorRemainder_bound, higherLaplaceDomainFamily_ofContDiff,
  located_analytic_germ_recovery_of_bare_setup) at thm:recovery +
  pin bump — GATED on user approval.
- The 27 recorded proof refactors (simplification tide).
- Promote the have-vs-let constructor lesson to the repo CLAUDE.md
  in the next hygiene PR.
