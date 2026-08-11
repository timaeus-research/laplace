# Tide: anharmonic cumulant moment-forms (κ₃, κ₄)

**Direction (user):** Express the connected cumulants κ₃, κ₄ (proved in
`(G₀,…,G₄)` closed form) in the physically-meaningful unperturbed-Gibbs moment
form `⟨uᵏ⟩₀` (`u = -(t x)`), completing the trio (κ₂'s moment form already
exists). Survey 2026-05-31 #1.

**Seabed:** lean/laplace, commit ee9d6be (main, post CGF synthesis).
**Started:** 2026-05-31

## Seabed snapshot

- `anharmonic_third_cumulant` / `anharmonic_fourth_cumulant`: κ₃, κ₄ in
  `(G_n(0))`-rational form.
- `iteratedDeriv_partition_div_eq_gibbsExp k`: `iteratedDeriv k (wP 0) 0 / wP 0 0
  = gibbsExp … 0 (·^k)` (moment-normalisation).
- `iteratedDeriv_weightedPartition_zero`: `iteratedDeriv k (wP 0) 0 = wP k 0`.
- `weightedPartition_zero_zero_pos`: `G_0(0) > 0`.

## Candidate (agreed) — proceed-without-GPT

`κ₃ = ⟨u³⟩₀ − 3⟨u²⟩₀⟨u⟩₀ + 2⟨u⟩₀³` and
`κ₄ = ⟨u⁴⟩₀ − 4⟨u³⟩₀⟨u⟩₀ − 3⟨u²⟩₀² + 12⟨u²⟩₀⟨u⟩₀² − 6⟨u⟩₀⁴`,
with `⟨uᵏ⟩₀ = gibbsExp … 0 (fun x => (-(t x))^k)`. Proof: rewrite each `⟨uᵏ⟩₀`
to `G_k(0)/G_0(0)` (moment-normalisation helper), then `field_simp`/`ring`
against the proved `(G_n)`-forms.

**Proceed-without-GPT:** definitional rewrite of already-proved values into the
moment basis; the moments-to-cumulants combinations are standard and checked by
`ring`. No fresh consult adds value.

## Numerical check

Not needed: algebraic re-expression of proved cumulant values; the `G_n(0)`
integrals were numerically validated in the higher-deriv tide.

## Result

New file `Laplace/OneD/AnharmonicCumulantMomentForms.lean`:
`anharmonic_third_cumulant_moment_form` and `anharmonic_fourth_cumulant_moment_form`
— κ₃, κ₄ as ⟨uᵏ⟩₀ moment combinations via a moment-normalisation helper +
`field_simp`. ~90 lines, no sorries.

## Retrospective

Retrospective: `retrospectives/2026-05-31-tide-anharmonic-cumulant-moment-forms.tex`
