# Tide: anharmonic FDT mean asymptote (t→∞) + Threepoint↔Laplace bridge

**Direction (user):** The companion to the cross-susceptibility asymptote: the
`t→∞` limit of the first-cumulant FDT, `∂_h⟨x⟩_h|_0 = -t·Var_0(x) → -1/λ`.
Needs a definitional bridge from the `Threepoint` covariance at `h=0` to the
`Laplace` covariance (to consume `cov_self_anharmonic_asymptotic`), then the
same Tendsto composition as the cross-susceptibility tide.

**Seabed:** lean/laplace, commit 372aa1f (main).
**Started:** 2026-05-31

## Seabed snapshot

- `gibbsExp_deriv_anharmonic_id_id_eq` (FDT, unconditional): `deriv (⟨x⟩_h) 0
  = -t · Threepoint.gibbsCov vol L id t 0 x x`.
- `cov_self_anharmonic_asymptotic`: `Tendsto (fun t => t · Laplace.gibbsCov L t x x)
  atTop (nhds (1/λ))` — note **Laplace** covariance.
- `Threepoint.gibbsExp vol L id t 0 φ` and `Laplace.gibbsExpectation L t φ` are
  both `(∫ φ·e^{-tL})/(∫ e^{-tL})` after the `0·x` reduction; `partitionFunction
  L t = ∫ e^{-tL}`.

## Candidate (agreed) — proceed-without-GPT

**A. Bridge.** `Threepoint.gibbsExp vol L id t 0 φ = Laplace.gibbsExpectation L t φ`
(`simp [zero_mul, add_zero]` after unfolding), hence
`Threepoint.gibbsCov vol L id t 0 φ ψ = Laplace.gibbsCov L t φ ψ`.
**B. Mean asymptote.** `Tendsto (fun t => deriv (⟨x⟩_h) 0) atTop (nhds (-1/λ))`:
`deriv(⟨x⟩_h)0 = -t·Threepoint.gibbsCov…0 = -t·Laplace.gibbsCov` (bridge), and
`t·Laplace.gibbsCov → 1/λ`, so `-(t·Cov) → -1/λ` (`.neg` + `Tendsto.congr'`).

**Proceed-without-GPT:** a definitional namespace bridge + a Tendsto
composition mirroring the just-landed cross-susceptibility asymptote. No fresh
consult adds value.

## Numerical check

Not needed: `-1/λ` is the standard linear-response asymptote
(`t·Var → 1/λ ⇒ ∂_h⟨x⟩ = -t·Var → -1/λ`); composition of validated pieces.

## Result

New file `Laplace/OneD/AnharmonicFDTMeanAsymptotic.lean`:
`threepoint_gibbsExp_zero_eq_laplace` / `threepoint_gibbsCov_zero_eq_laplace`
(reusable Threepoint↔Laplace bridge at h=0) and
`gibbsExp_deriv_anharmonic_asymptotic` — `∂_h⟨x⟩_h|_0 → -1/λ` as t→∞. ~50 lines,
first-try build, no sorries. Completes both FDT t→∞ asymptotes.

## Retrospective

Retrospective: `retrospectives/2026-05-31-tide-anharmonic-fdt-mean-asymptotic.tex`
