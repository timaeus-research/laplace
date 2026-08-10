# Tide: germbij Theorem 3.1 inverse, grand composition (part 1)

**Direction (user):** "OK go ahead with the composition tide" —
compose location recovery with the ccData jet/germ theorems into a
single literal statement; derive the package family from a smooth
nondegenerate-minimum setup; IsSymm from analyticity where possible.
(2026-08-10, following the perimeter review's "remaining distance"
list.)

**Seabed:** laplace main at e2ce7ee (+ #123 docs). Relevant corpus:
LocationRecovery (locatedMoment is a DEFINITION-LEVEL model — the
docstring says the identification with the posterior integral of the
translated loss "is the usual change of variables but is not
formalised here"), ShiftNormalization (constant-shift transport),
CutoffRemoval (ccData headlines, centred package-level form),
SingularPoint/SingularSmooth (the Lebesgue-substitution idiom
integral_add_left_eq_self, AnalyticAt translation via comp with the
affine shift).

**Started:** 2026-08-10T14:40Z

## Candidates v1 (Claude)

Part 1 (this tide), `Laplace/Multi/TranslationBridge.lean`:

1. **Translation transport of the localized moment** (discharges
   LocationRecovery's definition-level caveat). For a package
   `A : LocalLaplaceDomain L H` for the CENTRED loss `L` and a point
   `p`, define the actual located moment of the loss `w ↦ L (w - p)`
   on the translated region `p +ᵥ` (rescaled appropriately) and prove
   it equals `A.posteriorMoment (fun y ↦ f (p + y)) q`
   (= `A.locatedMoment p f q`) via `integral_add_left_eq_self` in
   numerator and denominator. Suggested statement shape: define

       regionMomentT (Λ : EuclidD d → ℝ) (V : Set (EuclidD d))
           (φ : EuclidD d → ℝ) (t : ℝ) : ℝ :=
         (∫ w in V, φ w * Real.exp (-(t * (Λ w - infimum shift?))))
           / (∫ w in V, Real.exp (-(t * ...)))

   — exact normalization to be settled in deliberation; the point is
   that the constant factors and Jacobians cancel in the quotient, so
   the theorem is `regionMomentT (fun w ↦ L (w - p)) (p +ᵥ V) φ t =
   A.posteriorMomentT (fun y ↦ φ (p + y)) t` under the package's
   region/rescaling conventions.

2. **The located ccData headline** (part 2, possibly same tide if
   part 1 is light): two losses Λ₁, Λ₂ with minima p₁, p₂, package
   families for the centred versions `y ↦ Λᵢ (pᵢ + y)`, ONE data
   premise over φ ∈ C_c^∞ (supports in the common actual localization
   region), concluding `p₁ = p₂` (via cutoff removal applied to the
   translated coordinate observables `y ↦ (pᵢ + y) i`, which are
   smooth with polynomial growth, then
   `location_eq_of_superPoly_first_moments`) and then positive-jet /
   germ equality at the common point (translated ccData premise fed
   to `smooth_positive_jet_recovery_of_ccData`).

3. **IsSymm from analyticity** (bonus, for the analytic corollary):
   `AnalyticAt ℝ L 0 → ∀ k, 1 < k → (iteratedFDeriv ℝ k L 0).IsSymm`
   via ω-regularity (`ContDiffAt.iteratedFDeriv_comp_perm` exists
   only at ω per the repo gotcha catalogue) — lets the analytic
   located corollary drop both hsymm hypotheses.

Deferred to a later tide: deriving the package family
`∀ k, 2 < k → HigherLaplaceDomain k L H` from a bare
smooth-nondegenerate-minimum setup (fixed-ball Taylor remainder
bounds from ContDiff on a compact ball; a real construction).

## GPT-5.6 Sol v1

Verbatim at `tide-log/gpt56_grand_composition_v1.md`. Headline: the
plan's candidate 1 is sound AFTER sharpening (posteriorIntegral is
already unrescaled, so translation never touches the dilation; build
a generic layer regionIntegralQ / regionMomentQ / regionMomentT with
translatedRegion p U := {w | w - p ∈ U}, all identities junk-safe
with no denominator-nonvanishing needed; raw loss in the definition,
constant-shift invariance as a separate lemma; direct-temperature
form bridged at 0 < t only, since posteriorMomentT's (sqrt t)⁻¹ has
junk semantics for t ≤ 0). Candidate 2 is NOT mere gluing: it needs
an actual-coordinate (located) cutoff-removal theorem (the centred
superPoly_moment_of_ccData takes ONE observable P on both sides,
but the translated coordinate observables differ per side), and a
common-region hypothesis strong enough to contain neighborhoods of
BOTH minima (support-in-intersection alone is vacuous when the
regions are disjoint). Candidate 3 confirmed
(AnalyticAt.contDiffAt at ω + ContDiffAt.iteratedFDeriv_comp_perm),
no 1 < k needed. Recommended sequence: Tide 1 TranslationBridge
(seven-item list), Tide 2 located cutoff removal, Tide 3 located
grand headline, Tide 4 analytic wrapper.

## Vote

- Claude: candidate 1 as sharpened (TranslationBridge layer), with
  candidate 3 as the independent bonus in the same file.
- GPT-5.6 Sol: the same ("candidate 1 alone is the right minimal
  scope ... candidate 3 is tiny and independent enough that it could
  be included as a bonus").

## Numerical check

Not feasible: structural composition/transport (change of variables
and quotient cancellations); the quantitative content is in the
already-verified headlines.

## Result

`Laplace/Multi/TranslationBridge.lean` (~220 lines), all gates green
on the FIRST full check — zero fix rounds (the gotcha catalogue paid
for itself: beta_reduce before indicator rewrites, function-first
argument order for integral_add_left_eq_self, open scoped ContDiff
for ω, exp-factor cancellation via mul_div_mul_left):

- regionIntegralQ / regionMomentQ / regionMomentT: the generic
  unrescaled region layer (GPT's sharpened design); the package
  moments are these verbatim (rfl lemmas
  posteriorIntegral_eq_regionIntegralQ,
  posteriorMoment_eq_regionMomentQ).
- translatedRegion p U := {w | w - p ∈ U} with a simp membership
  lemma.
- regionIntegralQ_translate / regionMomentQ_translate: the Lebesgue
  substitution, junk-safe for every q.
- regionMomentQ_translate_eq_locatedMoment and (0 < t)
  regionMomentT_translate_eq_locatedMomentT: LocationRecovery's
  definition-level caveat is DISCHARGED — the located moment IS the
  physical Gibbs moment of the translated loss on the translated
  region.
- regionIntegralQ_sub_const / regionMomentQ_sub_const: raw-vs-shifted
  loss invariance (the constant factors out and cancels identically).
- AnalyticAt.iteratedFDeriv_isSymm (bonus): every iterated derivative
  at an analytic point is IsSymm, via ContDiffAt.iteratedFDeriv_comp_perm
  at ω.

### Suggested follow-ups (the consult's tides 2-4)

- Tide 2: located cutoff removal — superPoly_locatedMoment_of_ccData
  with a common actual test region containing neighborhoods of BOTH
  candidate minima (support-in-intersection alone is vacuous when
  regions are disjoint); translation-preservation lemmas for
  ContDiff / tsupport / polynomial growth.
- Tide 3: the located grand headline (recover p₁ = p₂ via the
  translated coordinate observables; transport the ccData premise to
  centred form; invoke smooth_positive_jet_recovery_of_ccData;
  transport derivatives/germ back to the common actual point).
- Tide 4: the analytic wrapper with hsymm discharged via
  AnalyticAt.iteratedFDeriv_isSymm and the germ transported to 𝓝 p.
- LocationRecovery module docstring: the "not formalised here"
  sentence can now cite the bridge (do together with tide 3's PR to
  avoid churn).
