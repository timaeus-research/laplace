# Tide: grand composition part 4 (the located analytic capstone)

**Direction (user):** continuation of the approved grand-composition
arc; the consult's Tide 4 (deliberation archived on main).

**Seabed:** laplace, branch `tide/germbij-located-headline` (stacked;
parent PR #126 in flight).

**Started:** 2026-08-10T18:20Z

## Candidate

`Laplace/Multi/LocatedAnalytic.lean`:

`located_analytic_germ_recovery_of_ccData` — the arc capstone,
stated for the ACTUAL losses Λ₁, Λ₂ (minima at unknown p₁, p₂):
package families for the centred versions y ↦ Λᵢ (pᵢ + y),
analyticity of Λᵢ at pᵢ (NO IsSymm hypotheses — discharged by
AnalyticAt.iteratedFDeriv_isSymm), the common-region physical data
premise now literally about regionMomentT Λᵢ (the identity
Λᵢ (pᵢ + (w - pᵢ)) = Λᵢ w makes tide 3's translated-loss form
collapse to the raw loss), conclusion:

    p₁ = p₂ ∧ ∀ᶠ w in 𝓝 p₁, Λ₁ w - Λ₁ p₁ = Λ₂ w - Λ₂ p₁.

Proof plan: centred analyticity by composition with the affine shift
(the SingularSmooth idiom); hsymm from analyticity; convert hdata to
tide 3's shape by the pointwise identity above; apply
located_positive_jet_recovery_of_ccData; centred germ by
analytic_germ_eq_of_jet_eq; transport to 𝓝 p₁ along
w ↦ w - p₁ (Tendsto.eventually) with add_sub_cancel / add_zero
cleanup.

## GPT-5.6 Sol

The grand-composition consult's Tide 4 verbatim (hsymm from
analyticity; germ transported to 𝓝 p; "state the fully located
analytic germ theorem without explicit symmetry hypotheses").

## Vote

- Claude: the capstone as above.
- GPT-5.6 Sol (via the consult): the same.

## Numerical check

Not feasible: structural transport of verified conclusions.

## Result

`Laplace/Multi/LocatedAnalytic.lean` (~110 lines), all gates green
after one structural fix (the `have ... ?_` + `case _ =>` pattern
does not defer a trailing explicit argument — pass the converted
data premise as an inline lambda with a `by beta_reduce; rw` block
instead):

- `located_analytic_germ_recovery_of_ccData`: the arc capstone. The
  hypotheses are about the ACTUAL losses (analytic at their unknown
  minima; the physical data premise literally about
  regionMomentT Λᵢ, since Λᵢ(pᵢ + (w - pᵢ)) = Λᵢ w collapses the
  translated-loss form); no IsSymm hypotheses (discharged by
  AnalyticAt.iteratedFDeriv_isSymm from tide 1); conclusion p₁ = p₂
  and germ equality modulo the constant on 𝓝 p₁.

THE GRAND COMPOSITION ARC IS CLOSED: with this, the note's inverse
Theorem 3.1 + Corollary 3.2 are machine-checked in fully located
form — unknown minima, one C_c^∞(V) physical data premise, location
+ jet + germ recovered — modulo the remaining package-derivation
wrapper (constructing the HigherLaplaceDomain family from a bare
smooth-nondegenerate-minimum setup), which the perimeter review
already records as the one outstanding distance to the note's prose
hypotheses.

### Suggested follow-ups

- The package-derivation wrapper (a real construction: fixed-ball
  Taylor remainder bounds from ContDiff on a compact ball; the last
  item on the perimeter review's literal-fidelity list).
- germbij.tex: markers for the located theorems at answer-(i) and
  thm:recovery + pin bump — GATED, surface for user approval.
- LocationRecovery module docstring update citing the bridge.
