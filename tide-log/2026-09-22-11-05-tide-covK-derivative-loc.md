# Tide: covK-derivative-loc

**Direction (user):** Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives.
(Auto-mode continuation: the note's displayed eq:covK, with `S = (tH + γI)⁻¹`, as `−∂ₜ` of eq:cov/eq:mean's cubic prediction.)
**Seabed:** laplace, main 6f2b20a (local; the GitHub repository was archived into `resolutionorg/resolution` at 10:48 UTC, so this
tide is built locally and exported as a patch)
**Started:** 2026-09-22 (UTC)

## Candidates v1 (Claude)

See `gpt_covK_loc_prompt_v1.md` (A–C verbatim).

- A: `covKFormulaLoc`, `meanShiftLoc` with `S = (t • H + γ • 1)⁻¹`; `covKFormulaLoc_zero` (the `γ = 0` case is `covKFormula`).
- B: the resolvent derivative without a matrix norm: `resolvent_identity`, `continuousAt_locS` (via `Matrix.inv_def`,
  `Continuous.matrix_det/adjugate`), `hasDerivAt_locS_apply` (entrywise, by `hasDerivAt_iff_tendsto_slope`).
- C: the scalar `HasDerivAt (fun s => ½ tr(B S(s)) + b⬝meanShiftLoc s) (−covKFormulaLoc t) t` for symmetric `H`, and
  `covKFormulaLoc_eq_neg_deriv`.

## Numerical check

Formula level, `d = 4`, random `H` (symmetric positive), `T`, `B`, `b`, `γ = 0.7`, `t = 3`: central differences of `F(s) = ½ tr(B S(s))
− ½ bᵀS(s)(s T:S(s))` against the four displayed terms (`numcheck_covK_loc.py`, below).

## GPT-6 Astra v1

Verbatim in `gpt_covK_loc_v1.md`. Summary: both routes viable; recommends trying `Ring.inverse` first (with
`attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra`; completeness supplies `HasSummableGeomSeries`;
extract entries by composing with the CLM `M ↦ Mᵢⱼ`, *not* `hasDerivAt_pi`) and keeping the elementary resolvent/slope argument as
the fallback; do not formalise both. For C prefer entrywise assembly with finite-sum derivative lemmas (`mulVec` is bilinear, so a
product rule is needed either way); warns not to mix the entrywise sup-norm and operator-norm instances. Algebra confirmed:
`−F' = ½ tr(HSBS) + ½ bᵀSC − (t/2) bᵀSHSC − (t/2) bᵀSD` with `C = T:S`, `D = T:(SHS)`, cyclicity (not symmetry) for the trace, and
symmetry of `S(t)` only for the final `bᵀS = (Sb)ᵀ` rewriting; hypotheses: `IsUnit (tH + γ1).det` and `Hᵀ = H` (no sign
assumptions on `t, γ`, no invertibility of `H`, no symmetry of `B`, `T`). Suggests proving the derivative first in `bᵀS` form without
symmetry, then `covKFormulaLoc` under symmetry. Vote A+B+C.

## Vote
- Claude: A+B+C (B via the elementary slope route, which was already clean when the consult returned)
- GPT-6 Astra: A+B+C ("prefer the ring-inverse/entrywise hybrid; do not spend the tide formalising both inverse-derivative routes")

Adopted: keep the elementary B (done); C as `bᵀS`-form derivative (`hasDerivAt_firstOrderLoc`, no symmetry) plus the symmetric
rewrite to the displayed formula.

## Result

Built locally (`lake build` clean, `scripts/sorries` 0/0/0/0); **not landed** (the GitHub seabed was archived into the resolution
monorepo during this run; the commit is exported as a patch in the SRI, `staging/pending-patches/tide-63-covK-derivative-loc/`).
A, B and C landed in the file.
`Laplace/Multi/CovKDerivativeLoc.lean` (     238 lines): `locPrec`, `locS`, `locPrec_sub`, `resolvent_identity`, `continuous_locPrec`, `continuousAt_locS`,
`eventually_isUnit_det`, `hasDerivAt_locS_apply`, `meanShiftLoc`, `covKFormulaLoc`, `locS_zero`, `meanShiftLoc_zero`,
`covKFormulaLoc_zero`, `covKFormulaLoc'`, `hasDerivAt_contractT_locS`, `meanShift_deriv_sum`, `hasDerivAt_firstOrderLoc`,
`locS_transpose`, `covKFormulaLoc_eq_of_symm`, `covKFormulaLoc_eq_neg_deriv`.

Surprises: the elementary resolvent/slope route needed no matrix norm and compiled on the second pass; the assembly of the scalar
derivative was the friction (`HasDerivAt.sum` Pi-sums, `const_mul` before `congr_of_eventuallyEq`, and keeping the matrix
products as atoms until the final `ring`).
