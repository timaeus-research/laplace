# Tide: germbij thm:singular composition, part 2 (the point theorem)

**Direction (user):** Continuation of the user-approved (2026-08-10)
closing of the composition gap surfaced by the adversarial GPT-5.6 Sol
critique of the unnormalized degenerate theorem (archived at
`tide-log/gpt56_singular_critique_v1.md` on the parent branch). Part 1
(PR #120, branch `tide/germbij-singular-compose`) delivered the prep
lemmas; this part composes them with the endpoint into the point-form
theorem.

**Seabed:** laplace, branch `tide/germbij-singular-compose` at f8600c2
(stacked; parent PR #120 in flight).

**Started:** 2026-08-10T10:05Z

## Candidate (part 2 of ~3: the composed point theorem)

`Laplace/Multi/SingularPoint.lean`:

`pencil_families_force_germ_eq_at`: for L₁ L₂ : (ι → ℝ) → ℝ
continuous, nonnegative, analytic at p, with L₁ p = 0 and L₂ p = 0,
if for EVERY continuous compactly supported observable φ and every N
the family difference

    t ↦ ∫ w, φ w * (exp (-(t * L₁ w)) - exp (-(t * L₂ w)))

is o(t^(-N)) at ∞, then L₁ = L₂ eventually in 𝓝 p (germ equality).

This is critique steps 2-3 and 8-11 in one statement:

- **Translation to the origin (steps 2-3):** G w := L₂ (p+w) - L₁ (p+w)
  is analytic at 0 (composition with the affine shift), G 0 = 0 from
  the two point-vanishing hypotheses; extract HasFPowerSeriesOnBall.
- **Contrapositive setup:** ¬(germ eq) gives frequently-nonzero at p,
  hence a witness of G ≠ 0 inside any shrunk finite power-series ball
  (HasFPowerSeriesOnBall.mono to min r 1).
- **Steps 4-5:** `exists_least_nonzero_diagonal` (part 1) on G.
- **Step 6:** `quadratic_upper_bound_of_nonneg` (part 1) on
  K w := L₁ (p+w) + L₂ (p+w): C² at 0 via AnalyticAt.contDiffAt, zero
  value, nonneg near 0.
- **Step 7:** `exists_bump_one_on_ball` (part 1) at the R from step 6.
- **Endpoint:** `analytic_pencil_difference_not_superpolynomial`
  applied to the SHIFTED pencil L₁(p+·), L₂(p+·), ψ.
- **Steps 10-11 (bridge + rewriting):** the endpoint's integral is the
  hfam integral for φ u := (L₂ u - L₁ u) * ψ (u - p) after the Lebesgue
  substitution u = p + w (`integral_add_left_eq_self`; volume on ι → ℝ
  is additive Haar, no integrability needed). φ is continuous with
  compact support (translated bump times continuous). Contradiction.

Part 3 (next tide): the locus theorem — compactness point selection
(step 1) and neighborhood assembly (step 12).

## GPT-5.6 Sol

The adversarial critique remains the deliberation for this arc; its B4
list steps 2-3 and 8-11 are followed as above. No new consult needed
for the statement (the composition has no new mathematical content);
consults will fire on tactical walls per the lean-formalisation
triggers.

## Vote

- Claude: the composed point theorem as stated.
- GPT-5.6 Sol (via the critique's B4): the same decomposition.

## Numerical check

Not feasible: structural composition of already-verified pieces (the
quantitative content lives in the endpoint theorem, verified in the
identifiability arc and re-audited by the critique).

## Result

`Laplace/Multi/SingularPoint.lean` (~120 lines), all gates green
(import in Laplace.lean, fresh .olean, zero errors/warnings,
scripts/sorries clean):

- `pencil_families_force_germ_eq_at` exactly as planned. The proof
  went through in essentially one pass; only three small walls:
  - `AnalyticAt.comp` needs the outer analyticity restated at
    `(fun w ↦ p + w) 0` (a `simpa`-typed `have`, not `▸` — the motive
    goes wrong and produces a doubly-shifted point).
  - `integral_add_left_eq_self` takes the FUNCTION first and the
    translation second (`(f) (p)`, mirroring
    `integral_mul_left_eq_self f g`); passing `p` first silently
    elaborates with `G := ι` and dies asking `MeasurableSpace ι`.
  - the endpoint's integral appears behind `(fun t ↦ ...) t` redexes
    inside `IsLittleO.congr'` per-point goals: `beta_reduce` before
    the `rw` (catalogued gotcha, fired again).
- Prep lemmas from part 1 are consumed under the `Multi.` prefix
  (SingularPrep lives in namespace `Laplace.Multi`, this file in
  `Laplace` to sit beside the endpoint).

### Plan compression: the locus assembly landed here too

While writing the part-3 follow-up it became clear the locus assembly
needs NO compactness: the per-point neighborhoods from
`pencil_families_force_germ_eq_at` union to an open set containing
W₀, which is the note-level conclusion shape. Critique step 1
(compactness point selection) belongs to the note's contrapositive
phrasing, not to the direct assembly. So
`pencil_families_force_eq_near` (~30 lines: eventually_nhds_iff +
choose + biUnion) is included in this tide.

### Observable-class gap (checked against the note, NOT closed here)

germbij.tex thm:singular quantifies the decay premise over
φ ∈ C_c^∞ (smooth). The Lean `hfam` quantifies over ALL continuous
compactly supported φ — a strictly STRONGER premise, because the
constructed observable (L₂ - L₁)·ψ(· - p) with the hand-rolled
min/max bump is continuous but not smooth. So these theorems do not
yet literally subsume the note's statement. The upgrade (real part 3):

- extract an analyticity radius ρ at p (AnalyticAt gives a ball on
  which L₂ - L₁ is analytic, hence C^∞);
- replace the bump by a Mathlib `ContDiffBump` with
  rIn := min R (ρ/4), rOut := 2·rIn ≤ ρ/2 < ρ, so
  tsupport(ψ(· - p)) ⊆ closedBall p rOut ⊆ ball p ρ;
- glue: φ := (L₂ - L₁)·ψ(· - p) is smooth pointwise — at u in
  ball p ρ as a product of C^∞ functions on an open set, and at
  u outside tsupport as locally zero (ContDiffAt.congr with 0);
- restate hfam over smooth φ and rerun the composition (the endpoint
  itself needs only continuity, so only the observable-membership
  step changes).

The tide-level theorems here remain correct and are the engine; the
footnote must NOT claim full coverage until the smooth-class version
lands.

### Suggested follow-ups

- Part 3 (stacked): the C_c^∞ observable-class upgrade above, giving
  `pencil_families_force_germ_eq_at_smooth` / `..._eq_near_smooth`
  whose premise matches the note verbatim.
- After part 3: germbij.tex footnote tightening + markers at
  thm:singular + pin bump.
