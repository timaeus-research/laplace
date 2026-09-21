# Tide: separable-oneloop

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"); this tide chosen by the agent: the one-loop covariance of a separable anharmonic potential (E2/E7).
**Seabed:** laplace, main after `llc-mse` (183b092) / `localised-llc-bounds`
**Started:** 2026-09-21 (UTC, see filename)

## Context

The sanity note's E2 and E7 use the separable anharmonic potential
`L(w) = ∑ᵢ (λᵢ/2 uᵢ² + αᵢ/6 uᵢ³ + gᵢ/24 uᵢ⁴)`, `u = Qᵀ(w − w*)`, `αᵢ = a λᵢ^{3/2} sᵢ`, `gᵢ = λᵢ²`, `sᵢ = ±1`, and E7 compares the
second-order (one-loop) prediction per eigendirection with exact quadrature "one dimension at a time". The seabed has the one-loop functional
`oneLoopCov t H T Q = S + SΠS` (`Laplace/Multi/OneLoop.lean`, tide `oneloop-rosenbrock`) with its one-dimensional value `oneLoopCov_oneDim`
(`1/(λt) + (α²/λ⁴ − γ/(2λ³))/t²`) and its Rosenbrock instance; and, on the analysis side, `var_anharmonic_second_order` (the 1D formula is the
true second-order variance). Nothing connects the `d`-dimensional functional to the separable potential.

## Candidates v1 (Claude)

Let `λ α g : Fin d → ℝ`, `sepT α` the cubic tensor with `Tᵢᵢᵢ = αᵢ` and all other entries `0`, `sepQ g` the quartic tensor with `Qᵢᵢᵢᵢ = gᵢ`,
`t ≠ 0`, `λᵢ ≠ 0`.

**A. The pieces of the functional on a diagonal `S`** (`S = diagonal s`):
```
contractQ (sepQ g) (diagonal s) = diagonal (gᵢ sᵢ)
contractT (sepT α) (diagonal s) = fun l => αₗ sₗ
bubble (sepT α) (diagonal s)     = diagonal (αᵢ² sᵢ²)
tadpoleLine (sepT α) (diagonal s) = diagonal (αᵢ² sᵢ²)
oneLoopPi t (sepT α) (sepQ g) (diagonal s) = diagonal (−(t/2) gᵢ sᵢ + t² αᵢ² sᵢ²)
```
and `(t • diagonal λ)⁻¹ = diagonal (1/(tλᵢ))`.

**B. The one-loop covariance of the separable potential is diagonal with the 1D second-order variances**:
```
oneLoopCov_separable :
  oneLoopCov t (diagonal λ) (sepT α) (sepQ g) = diagonal (fun i => 1/(λᵢ t) + (αᵢ²/λᵢ⁴ − gᵢ/(2λᵢ³))/t²)
```
(each entry is `oneLoopCov_oneDim`'s value: the functional respects separability, so E7's "one dimension at a time" comparison is the
`d`-dimensional prediction).

**C. The note's parametrisation.** With `αᵢ² = a² λᵢ³` and `gᵢ = λᵢ²`:
```
oneLoopCov_separable_note : entry i = 1/(λᵢ t) + (a² − 1/2)/(λᵢ t²)
oneLoopCov_separable_note_ratio : (second-order term)/(first-order term) = (a² − 1/2)/t
```
so the relative second-order correction is the same in every direction and independent of `κ`: E2's "relative error ∝ 1/t" with the
coefficient `|a² − 1/2|` (`0.25` at `a = 0.5`, `0.5` at `a = 1`; E2 measured `2.7 × 10⁻²` at `t = 10`, `a = 0.5`, against `0.25/10 = 0.025`).

**D. (Optional) The rotated frame.** For `H = Q diag(λ) Qᵀ` with `Q` orthogonal and the tensors rotated accordingly, `oneLoopCov` is
`Q diag(…) Qᵀ`. Tensor rotation is bookkeeping-heavy; propose to state B and C in the eigenframe and record D as a follow-up.

Vote intention: A+B+C.

## Numerical check

`numcheck32.py` (`d = 4`, random `λ ∈ [0.5, 2]`, `α ∈ [−1, 1]`, `g ∈ [0.5, 2]`, `t = 30`): the functional evaluated from its tensor definition
against the diagonal formula gives `max |cov − pred| = 0.0`, off-diagonal entries `0.0`; with the note's parametrisation the second-order
coefficient `α²/λ⁴ − g/(2λ³)` equals `(a² − 1/2)/λ` to machine precision in every direction.

## GPT-6 Astra v1

Saved verbatim in `tide-log/gpt_separable_oneloop_v1.md`. Summary: A–C correct (bubble and line tadpole both force all indices equal on a diagonal `S`); the sign of `(a² − 1/2)/t` means Laplace *over*predicts the one-loop variance for `a² < 1/2` — a statement about the expansion, not an unconditional finite-`t` inequality; B/C are the note's eigenframe (`u`-coordinate) prediction, and the rotation law `R C Rᵀ` (D) is not proven — say so. Lean: entrywise proofs with early `by_cases hij`, `Finset.sum_eq_single`, watch the orientation of off-index hypotheses; inversion via the right-inverse characterisation with `diagonal_mul_diagonal`. Cheap additions taken up: the unique *global* minimum `L(u) = u²(g u² + 4αu + 12λ)/24 > 0` for `u ≠ 0` under `α² < 3λg`, which is `a² < 3` in the note's parametrisation (global, not local: excluding other stationary points needs `α² < (8/3)λg`); an absolute-value form of the ratio. Not claimed: a relative `O(t⁻²)` remainder for the second-order prediction.

## Vote
- Claude: A+B+C (+ the unique-global-minimum and absolute-ratio corollaries; D a follow-up)
- GPT-6 Astra: A+B+C

Agreed. Proceeding to Step 3.
