# Tide: cumulants as log-partition derivatives (synthesis)

**Direction (user):** Close the cumulant-arc loop: the κ₂,κ₃,κ₄ proved as
derivatives of the *mean* `M = G_1/G_0` are the genuine connected cumulants
`κ_n = ∂ⁿ_h log Z|_0` of the cumulant generating function `K = log Z`. Relate
`iteratedDeriv n (log Z)` to `iteratedDeriv (n-1) M`, and re-derive κ₂,κ₃,κ₄ as
`∂²,∂³,∂⁴ log Z`.

**Seabed:** lean/laplace, commit a084445 (main, post κ₄).
**Started:** 2026-05-30

## Seabed snapshot

- `weightedPartition_hasDerivAt 0 {|h₀|<1}`: HasDerivAt G_0 (G_1 h₀) h₀.
- `weightedPartition_zero_pos {|h₀|<1}`: G_0(h₀) > 0.
- κ-ladder values: `anharmonic_mean_hasDerivAt` (κ₂ = deriv M 0),
  `anharmonic_third_cumulant` (κ₃ = iteratedDeriv 2 M 0),
  `anharmonic_fourth_cumulant` (κ₄ = iteratedDeriv 3 M 0).
- Mathlib `HasDerivAt.log`, `iteratedDeriv_succ'`, `iteratedDeriv_one`,
  `Filter.EventuallyEq.iteratedDeriv_eq`.

## Candidate (agreed) — proceed-without-GPT

**A. General-h log-partition derivative.** `HasDerivAt (log ∘ G_0) (G_1 h₀/G_0 h₀) h₀`
for `|h₀|<1` (HasDerivAt.log on the partition derivative + positivity), hence
`deriv (log Z) =ᶠ[𝓝 0] M`.
**B. Succ lemma.** `iteratedDeriv (n+1) (log Z) 0 = iteratedDeriv n M 0`
(`iteratedDeriv_succ'` + `EventuallyEq.iteratedDeriv_eq`).
**C. Corollaries.** `∂² log Z|_0 = κ₂`, `∂³ log Z|_0 = κ₃`, `∂⁴ log Z|_0 = κ₄`
by `rw [B]` then citing the existing cumulant theorems (Lean checks the values).

**Proceed-without-GPT:** pure chaining of established lemmas; the analytic
content (the κ_n values) is already proved and validated. Lean verifies the
corollary values match the cited theorems, so no silent restatement risk.

## Numerical check

Not needed: relabelling already-proved derivatives via the CGF; no new value.

## Result

New file `Laplace/OneD/AnharmonicCumulantsLogPartition.lean`:
`logPartition_hasDerivAt_general`, `deriv_logPartition_eventuallyEq`,
`iteratedDeriv_logPartition_succ` (iteratedDeriv (n+1) logZ 0 = iteratedDeriv n M 0),
and corollaries `logPartition_{second,third,fourth}Deriv_eq_kappa{2,3,4}` giving
κ₂,κ₃,κ₄ = ∂²,∂³,∂⁴ log Z at 0. ~130 lines, first-try build, no sorries.

## Retrospective

Retrospective: `retrospectives/2026-05-30-tide-anharmonic-cumulants-logpartition.tex`
