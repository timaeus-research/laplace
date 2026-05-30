# Tide: anharmonic moment-normalisation

**Direction (user):** Bridge this session's partition-derivative arc to the
unperturbed Gibbs moments: `iteratedDeriv n Z 0 / Z(0) = ⟨(-(t x))^n⟩₀`, the
unperturbed Gibbs expectation (`Threepoint.gibbsExp ... 0`) of the observable
`(-(t x))^n`. Survey v4 #1.

**Seabed:** lean/laplace, commit ddc21fe (main, post general-h merge).
**Started:** 2026-05-30

## Seabed snapshot

- `weightedPartition lam alpha gamma t n h = ∫ (-(t·x))^n · exp(-(t·(L + h·x)))`;
  `Z = weightedPartition ... 0`.
- `iteratedDeriv_weightedPartition_zero`: for `|h|<1`,
  `iteratedDeriv n (weightedPartition ... 0) h = weightedPartition ... n h`.
- `anharmonic_partition_pos`: `0 < ∫ exp(-(t·L))` (i.e. `Z(0) > 0`).
- `Threepoint.gibbsExp μ L A t h φ = (∫ φ·exp(-(t(L+h·A)))) / (∫ exp(-(t(L+h·A))))`.

## Candidate (agreed) — proceed-without-GPT

**Statement.** For the anharmonic potential, `t>0`, every `n:ℕ`:
`iteratedDeriv n (weightedPartition lam alpha gamma t 0) 0 / weightedPartition lam alpha gamma t 0 0
  = Threepoint.gibbsExp volume (anharmonicPotential lam alpha gamma) (fun x => x) t 0 (fun x => (-(t*x))^n)`.

This is a near-definitional identity:
- `iteratedDeriv n (wP 0) 0 = wP n 0 = ∫ (-(t·x))^n · exp(-(t(L+0·x)))` — the
  gibbsExp numerator at `φ = (-(t·x))^n`, `h=0`.
- `wP 0 0 = ∫ (-(t·x))^0 · exp(-(t(L+0·x))) = ∫ exp(-(t(L+0·x)))` (`pow_zero`),
  the gibbsExp denominator.

**Proceed-without-GPT:** the statement is an identity by the definition of
`gibbsExp` (no analytic content beyond the already-formalised
`iteratedDeriv_weightedPartition_zero`); a fresh consult would add nothing.
The signs/derivative forms were already GPT-confirmed in the higher-deriv tide.

## Numerical check

Not feasible / not needed: structural identity by definition of `gibbsExp`,
not a new closed-form number. (The underlying `G_n(0)` integrals were
numerically validated in the higher-deriv tide-log.)

## Result

New file `Laplace/OneD/AnharmonicMomentNormalisation.lean`: theorem
`iteratedDeriv_partition_div_eq_gibbsExp (n)`. 6-line definitional proof
(rw the iteratedDeriv identity, unfold weightedPartition + gibbsExp,
`simp only [pow_zero, one_mul]`). Builds clean, no sorries.

## Retrospective

Retrospective: `retrospectives/2026-05-30-tide-anharmonic-moment-normalisation.tex`
