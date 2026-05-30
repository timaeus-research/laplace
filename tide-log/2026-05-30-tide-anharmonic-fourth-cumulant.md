
## Result

New file `Laplace/OneD/AnharmonicFourthCumulant.lean`:
`anharmonic_susceptibility_deriv_general` (general-h κ₃) and
`anharmonic_fourth_cumulant` — iteratedDeriv 3 (G_1/G_0) 0 =
(G_4 G_0³ - 4 G_3 G_1 G_0² - 3 G_2² G_0² + 12 G_2 G_1² G_0 - 6 G_1⁴)/G_0⁴.
Triple HasDerivAt-layer chaining via Filter.EventuallyEq.deriv. ~160 lines.
Builds within default heartbeats, no sorries. Key fix: simp only [Pi.pow_apply,
Pi.mul_apply] before ring to reduce Pi-application atoms in the compound
derivative value.

## Retrospective

Retrospective: `retrospectives/2026-05-30-tide-anharmonic-fourth-cumulant.tex`
