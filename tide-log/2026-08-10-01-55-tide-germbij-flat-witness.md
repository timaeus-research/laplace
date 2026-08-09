# Tide: germbij-flat-witness

**Direction (user):** concrete witness for germbij Proposition 4.1
(auto mode, standing delegation): the classic flat function
f = e^{-1/x²} (extended by 0 at x = 0) satisfies every hypothesis of
`flat_perturbation_invisible`, so the invisibility theorem is
witnessed rather than conditionally quantified. Deferred from the
flat-invisible tide by joint vote; GPT-5.6 Sol supplied the flatness
route in that tide's consult.

**Seabed:** laplace, stacked on tide/germbij-flat-invisible at c90d1d0
(PR #51, in CI at tide start). Linear-chain worktree per protocol.
**Worktree/branch:** laplace-tide-germbij-flat-witness /
tide/germbij-flat-witness
**Started:** 2026-08-10T01:55Z

## Candidate v1 (Claude)

1. `def flatWitness (x : ℝ) : ℝ := if x = 0 then 0 else exp (-(1/x²))`
2. `flatWitness_nonneg`, `flatWitness_le_one` — trivial if-splits.
3. `flatWitness_flat : ∀ n, ∀ x, flatWitness x ≤ n.factorial * x^(2n)`
   — GLOBAL bound (stronger than the local hypothesis needs): for
   x ≠ 0 set s = 1/x²; from s^n/n! ≤ e^s (single term of the
   exponential series, `Real.sum_le_exp_of_nonneg`) get
   e^{-s} ≤ n!/s^n = n! x^{2n}. At x = 0 both sides are 0 ≤ 0 (n ≥ 1)
   or 0 ≤ n! (n = 0).
4. `flatWitness_continuous` — away from 0 by composition; at 0 by
   squeeze against x² (the n = 1 case of the global bound).
5. `flat_witness_invisible` / `flat_witness_superpolynomial` —
   instantiation corollaries of the parent tide's theorems with
   M = 1, C = n!, δ = 1.

Rationale: minimal step (pure instantiation, no new analysis), closes
the "fully witnessed" gap the parent retrospective names as the
natural follow-up. Architecture already deliberated in the parent
consult (gpt56_germbij_flat_invisible_v1.md §5).

## Numerical check

Executed before formalisation. Grid n ∈ {1,2,3,5},
x ∈ {0.05, 0.1, 0.3, 0.5, 1, 2, 10}: e^{-1/x²} ≤ n!·x^{2n} holds at
every point; max ratio f/bound = 0.3679 (n = 1), matching the
analytic sup e^{-n}n^n/n! at s = n (0.3679, 0.2707, 0.2240, 0.1755
for n = 1, 2, 3, 5). Bound confirmed with comfortable margin.

## Deliberation

No fresh consult: this candidate and its full proof route were
deliberated in the parent tide's consult
(tide-log/gpt56_germbij_flat_invisible_v1.md, §5), which recommended
exactly this follow-up declaration and supplied the flatness route
(s^n/n! ≤ e^s gives e^{-1/x²} ≤ n!·x^{2n} globally, C = n!, any δ),
plus the lemma names to verify. Both names verified before writing:
`Real.sum_le_exp_of_nonneg` exists (Complex/Exponential.lean:244);
single term extracted via `Finset.single_le_sum`. This is the
documented proceed-without-new-consult path (prior deliberation +
executed numerical check).

## Vote

- Claude: flatWitness + global factorial bound + continuity +
  instantiation corollaries, per parent consult §5.
- GPT-5.6 Sol (from parent consult, verbatim recommendation): "It is
  a useful second theorem/example ... one can in fact obtain the flat
  bound globally: e^{-1/x²} ≤ n! x^{2n}."

Agreed (carried over from the parent deliberation).

## Result

- Declarations: `flatWitness` (e^{-1/x²} extended by 0),
  `flatWitness_nonneg`, `flatWitness_le_one`,
  `flatWitness_le_factorial_mul_pow` (the GLOBAL flatness bound),
  `flatWitness_continuous` (squeeze against x² at 0, composition
  elsewhere), `flatWitness_flat` (hypothesis packaging, C = n!,
  δ = 1), and the instantiations `flat_witness_invisible`,
  `flat_witness_superpolynomial`. Zero sorries, zero warnings.
- File: Laplace/OneD/FlatWitness.lean (~140 lines).
- Surprises: (1) the known cascading-rewrite gotcha struck again in
  flatWitness_le_one — rewriting 1 = exp 0 also stomped the 1 inside
  1/x²; fixed with a calc through exp 0 instead. (2)
  `continuousAt_pow` takes (x, n), not (n, x). (3) One dead tactic
  after field_simp (known class). Everything else first-try.
- Infrastructure: seed_worktree failed on this host (macOS system
  bash 3.2 lacks `local -A`); worktree was seeded manually via rsync
  --link-dest from the parent worktree. Fixed portably in SRI
  (.agents/skills/tide/seed_worktree, awk lookup) and smoke-tested.
