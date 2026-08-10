# Tide: grand composition part 3 (the located grand headline)

**Direction (user):** continuation of the approved grand-composition
arc; the consult's Tide 3 (deliberation archived on main at
`tide-log/gpt56_grand_composition_v1.md`).

**Seabed:** laplace, branch `tide/germbij-located-cutoff` (stacked;
parent PR #125 in flight). Tide 2 supplies
superPoly_locatedMoment_of_ccData.

**Started:** 2026-08-10T17:20Z

## Candidate

`Laplace/Multi/LocatedHeadline.lean`:

`located_positive_jet_recovery_of_ccData`: package families A, B for
the centred losses L₁, L₂ (IsSymm hypotheses as in the centred
headline), centres p₁ p₂, common actual region V ⊇ balls around both
centres, and ONE physical data premise per package order k (smooth
compactly supported φ with tsupport φ ⊆ V, superPoly agreement of
the regionMomentT families of the actual translated losses).
Conclusion: p₁ = p₂ AND equality of all positive-order centred
derivative tensors.

Proof plan:
1. Location: tide-2's theorem at the k = 3 package pair with
   P := coordinate observables (smooth via EuclideanSpace.proj,
   growth ⟨1,1⟩), then location_eq_of_superPoly_first_moments.
2. subst p := p₁ = p₂. Key reparametrization: for ANY centred smooth
   polynomial-growth Q, the actual observable P := Q(· - p) is smooth
   (comp with id - const) with polynomial growth
   (comp_const_add (-p) + sub_eq_neg_add), and
   locatedMomentT p P = posteriorMomentT Q (add_sub_cancel_left
   under the binder). So tide-2's conclusion at P is exactly centred
   superPoly data at Q.
3. Instantiate Q := coordinate products (k = 3) and monomialTests
   (each k) and feed the base-case-free
   smooth_positive_jet_recovery_of_superPoly_moments.

The actual-point forms (iteratedFDeriv of the actual losses at p,
germ at 𝓝 p, hsymm from analyticity) are tide 4.

## GPT-5.6 Sol

The grand-composition consult is the deliberation; its Tide 3 items
(recover p₁ = p₂; transport the premise to centred form; invoke the
centred headline) are followed, with one deviation that SIMPLIFIES:
the consult routed the centred step through
smooth_positive_jet_recovery_of_ccData, but the common-region premise
V need not contain the centred headline's own cutoff supports; the
tide-2 theorem already yields data for ALL polynomial-growth
observables, so feeding the superPoly-form headline
(smooth_positive_jet_recovery_of_superPoly_moments) through the
Q ↦ Q(· - p) reparametrization avoids any second support condition.

## Vote

- Claude: the located headline as above.
- GPT-5.6 Sol (via the consult's Tide 3, with the noted
  simplification): the same target.

## Numerical check

Not feasible: structural composition of verified headlines.

## Result

`Laplace/Multi/LocatedHeadline.lean` (~150 lines), all gates green,
ZERO fix rounds (second time in the arc):

- contDiff_coord / hasPolynomialGrowth_coord (single-coordinate
  observable instances).
- locatedMomentT_sub_observable: the reparametrization identity
  locatedMomentT p (Q(· - p)) = posteriorMomentT Q.
- located_positive_jet_recovery_of_ccData exactly as planned:
  location via tide-2 at the coordinates + subst, centred data via
  the reparametrization (comp_const_add (-p₁) + sub_eq_neg_add for
  growth, beta_reduce before the rewrite in the SuperPoly.congr
  per-point goal), then the base-case-free superPoly headline.

### Suggested follow-ups (tide 4, the arc capstone)

- The actual-loss forms: iteratedFDeriv transport under translation
  (centred jets at 0 → actual jets at p for Λᵢ := Lᵢ(· - p)), the
  analytic located germ corollary with hsymm discharged by
  AnalyticAt.iteratedFDeriv_isSymm and the germ transported to 𝓝 p.
- After the arc: germbij.tex markers for the located theorems at
  answer-(i)/thm:recovery + pin bump (TeX actions: surface for
  approval per the standing gate).
- LocationRecovery module docstring update (its "not formalised
  here" sentence) alongside tide 4's PR.
