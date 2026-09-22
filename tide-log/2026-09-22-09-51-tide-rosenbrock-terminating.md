# Tide: rosenbrock-terminating

**Direction (user):** Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives.
(Auto-mode continuation: E5/E7's "the series terminates" for Rosenbrock, checked against the two-loop energy, eq:mean and eq:covK.)
**Seabed:** laplace, main 94c6d10
**Started:** 2026-09-22T09:53Z

## Candidates v1 (Claude)

See `gpt_rosenbrock_terminating_prompt_v1.md` (A–C verbatim).

- A: `twoLoopEnergy t rosenHess rosenT rosenQ = 1/t = ⟨L⟩` at every `t` (`θ = 12a/t³`, `δ = 4a/t³`, `q = 12a/t²` cancel;
  `θ = 3δ` is a non-separable check of the two-loop weights).
- B: `meanShift t rosenHess rosenT = (0, 1/t) = (⟨x⟩ − 1, ⟨y⟩ − 1)` exactly.
- C: `Cov[L, ½vᵀBv + b⬝v] = covKFormula + 3B₁₁/t³`; exact for linear probes.

## Numerical check

`numcheck_rosenbrock_terminating.py` (sympy, exact): `theta = 12a/t³`, `dumbbell = 4a/t³`, `q = 12a/t²`, `twoLoopEnergy = 1/t`;
`meanShift = (0, 1/t)`; `covKFormula = (a B₀₀ + 2a(B₀₁ + B₁₀) + (4a + 1)B₁₁ + 2a b₁)/(2a t²)`, `exact − covKFormula = 3B₁₁/t³`;
`L·ψ` has `z`-degree 6 and `u`-degree 4. Earlier floating-point runs (`rosen2loop.py`, `rosenmean.py`) agree to `1e-11`.

## GPT-6 Astra v1

Verbatim in `gpt_rosenbrock_terminating_v1.md`. Summary: A, B, C correct (`a > 0`, `t > 0`, probes independent of `t`; symmetry of
`B` not needed). Recomputed the contractions in the tangent coordinates `v = (r, 2r + s)`, where `L = ½r² + (a/2)(s − r²)²`, the
Hessian is `diag(1, a)`, `T'₀₀₁ = −2a` (three permutations), `Q'₀₀₀₀ = 12a`: `θ = 3(−2a)²/(a t³) = 12a/t³`, `δ = 4a/t³`,
`q = 12a/t²`, `θ = 3δ`; `meanShift = −(t/2) S d = (0, 1/t)`. Confirms the sign reduction `covKFormula = ½ tr(HSBS) − ½ (Sb)⬝(T:S)`
and the closed form. Neat reading of C: `⟨ψ⟩ = (A_B/2 + b₁)/t + 3B₁₁/(2t²)` exactly, and `Cov(L, ψ) = −d⟨ψ⟩/dt` for a
`t`-independent probe, so `Cov = (A_B/2 + b₁)/t² + 3B₁₁/t³`; a complete second-order covariance formula would be exact for these
probes ("the exact inverse-temperature expansion terminates at this next order"). Wording: say "the two-loop energy and the
leading mean-shift formulas are exact for Rosenbrock; all subsequent coefficients of these observables' `1/t` expansions vanish",
not that individual higher diagrams vanish; keep a general second-order `covKFormula` as future work. Lean: no obstruction to
`Fin 7 → Fin 5`; check `Fin.sum_univ_seven` exists (it does), keep positivity hypotheses explicit.

## Vote
- Claude: A+B+C
- GPT-6 Astra: A+B+C ("Keep the tide focused on the exact Rosenbrock identity and explicit remainder")

Adopted: GPT's wording for the staging note; the `−d⟨ψ⟩/dt` reading recorded as a remark (not formalised).

## Result

Commit `de63117` on `tide/rosenbrock-terminating`; `lake build` clean, `scripts/sorries` 0/0/0/0. A, B and C landed.
`Laplace/Multi/RosenbrockTerminating.lean` (     274 lines): `gibbsExpectation_valley_poly'`, `harmonicMoment_five`,
`harmonicMoment_six`, `harmonicMoment_vec7`, `gibbsExpectation_rosenbrock_of_poly7`, `thetaDiagram_rosenbrock`,
`dumbbell_rosenbrock`, `figureEight_rosenbrock`, `trace_HS_rosenbrock`, `twoLoopEnergy_rosenbrock`,
`twoLoopEnergy_rosenbrock_exact`, `meanShift_rosenbrock`, `meanShift_rosenbrock_exact`, `rosenProbe`,
`contractT_rosenbrock_SHS`, `covKFormula_rosenbrock`, `gibbsCov_rosenbrock_probe`, `gibbsCov_rosenbrock_linear_probe`,
`covKFormula_rosenbrock_linear`.

Surprises: the degree-six computation (35 symbolic coefficients from sympy, `simp; ring`) compiled first time; the only friction was
the trace of `H S B S` with symbolic `B`, where plain `simp` stops at `vecMul` forms. Mathematically, the first-order eq:covK is
*not* exact for Rosenbrock although the one-loop covariance and the two-loop energy are: the `3B₁₁/t³` remainder is the flat
direction's `z²` pushed through `y − 1 = u + 2z + z²` into `Cov[z²/2, z⁴]`.
