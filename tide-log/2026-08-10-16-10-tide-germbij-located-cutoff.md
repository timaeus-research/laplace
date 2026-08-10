# Tide: grand composition part 2 (located cutoff removal)

**Direction (user):** continuation of the approved grand-composition
arc ("OK go ahead with the composition tide", 2026-08-10); this is
the consult's Tide 2 (deliberation archived on the parent branch at
`tide-log/gpt56_grand_composition_v1.md`).

**Seabed:** laplace, branch `tide/germbij-grand-composition` (stacked;
parent PR #124 in flight). TranslationBridge supplies regionMomentT /
translatedRegion and the located identities.

**Started:** 2026-08-10T16:10Z

## Candidate

`Laplace/Multi/LocatedCutoff.lean`:

`superPoly_locatedMoment_of_ccData`: packages A (for L₁) and B (for
L₂), centres p₁ p₂, a common actual test region V with
V ⊆ translatedRegion pᵢ (their U's) and balls ball pᵢ rᵢ ⊆ V around
BOTH centres (the consult's load-bearing common-region hypothesis:
support-in-intersection alone is vacuous when the regions are
disjoint), and data: for every smooth compactly supported φ with
tsupport φ ⊆ V,

    SuperPoly (t ↦ regionMomentT (w ↦ L₁ (w - p₁)) (transRegion p₁ A.U) φ t
                 - regionMomentT (w ↦ L₂ (w - p₂)) (transRegion p₂ B.U) φ t)

(the PHYSICAL premise, in actual coordinates). Conclusion: for every
smooth polynomial-growth P,

    SuperPoly (t ↦ A.locatedMomentT p₁ P t - B.locatedMomentT p₂ P t).

Proof plan (mirror of superPoly_moment_of_ccData, translated):
1. `SuperPoly.congr`: eventual-equality transport (tiny; needed to
   convert the physical premise to locatedMomentT via the
   TranslationBridge identities, which hold for 0 < t).
2. Translation preservation: ContDiff of y ↦ P (p + y) (comp with
   the affine shift); HasPolynomialGrowth of the translate (constant
   inflation via (‖p‖ + ‖y‖)^n ≤ 2^n (‖p‖^n + ‖y‖^n)).
3. The double bump: two ContDiffBumps f₁ (centre p₁, rIn r₁/2,
   rOut 3r₁/4) and f₂ (centre p₂ likewise);
   χ := 1 - (1 - f₁)(1 - f₂). Smooth, [0,1]-valued, ≡ 1 where either
   bump is 1 (in particular on balls around both centres), support ⊆
   supp f₁ ∪ supp f₂ ⊆ V, compact support.
4. Apply hdata at φ := P·χ; convert both sides to locatedMomentT
   (TranslationBridge, eventually in t).
5. Per package: posteriorMoment_cutoff_tail with observable
   P(pᵢ + ·) and cutoff χ(pᵢ + ·) (≡ 1 on ball 0 (rᵢ/2)).
6. Telescope (A_P - A_Pχ) + (A_Pχ - B_Pχ) - (B_P - B_Pχ).

## GPT-5.6 Sol

The grand-composition consult (parent branch) IS the deliberation for
this tide: its section on candidate 2 specifies exactly this
decomposition (located cutoff removal as its own layer, common-region
hypothesis option 2 "closest to a note-literal premise"). No new
consult needed for the statement; consults fire on tactical walls.

## Vote

- Claude: the located cutoff-removal theorem as specified.
- GPT-5.6 Sol (via the grand-composition consult): the same (its
  "Tide 2" recommendation verbatim).

## Numerical check

Not feasible: structural (cutoff bookkeeping and telescoping); the
quantitative content is posteriorMoment_cutoff_tail, already
verified and reviewed.

## Result

`Laplace/Multi/LocatedCutoff.lean` (~230 lines), all gates green
after two small fix rounds:

- `SuperPoly.congr` (eventual-equality transport at atTop).
- `HasPolynomialGrowth.comp_const_add` (translation preserves
  polynomial growth; constant inflation via
  (a+b)^n ≤ 2^n max^n ≤ 2^n(a^n + b^n), closed by nlinarith with
  explicit product-nonnegativity hints).
- `superPoly_locatedMoment_of_ccData` exactly as planned: double
  bump χ = 1 - (1-f₁)(1-f₂) from two ContDiffBumps (rIn rᵢ/2,
  rOut 3rᵢ/4, supports inside ball pᵢ rᵢ ⊆ V), per-package cutoff
  tails in centred coordinates, physical middle term transported by
  the TranslationBridge identities eventually in t, telescope closed
  by beta_reduce + unfold locatedMomentT + beta_reduce + ring.

Surprises: `posteriorMoment_cutoff_tail` was NOT in the import chain
(LocationRecovery does not import CutoffRemoval — the "unknown
identifier from a sibling file" class; the import line is part of the
statement); `push Not` refuses ¬(a ∈ s ∪ t) until Set.mem_union is
unfolded (use simp only [Set.mem_union, not_or]);
`isCompact_closedBall` is top-level with explicit args, not
Metric-namespaced; the style linter rejects the goal-restating
`show` before the telescope — beta_reduce twice (once after
unfolding, for the redex inside the observable argument) then ring.

### Suggested follow-ups (consult's tides 3-4)

- Tide 3: the located grand headline — apply this theorem to the
  coordinate observables (smooth, polynomial growth) to get located
  first-moment data, conclude p₁ = p₂ via
  location_eq_of_superPoly_first_moments, transport the ccData
  premise to centred form at the common point, invoke
  smooth_positive_jet_recovery_of_ccData, and transport
  derivatives/germ back to the actual point.
- Tide 4: the analytic wrapper (hsymm via
  AnalyticAt.iteratedFDeriv_isSymm, germ at 𝓝 p).
