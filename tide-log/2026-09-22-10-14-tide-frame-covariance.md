# Tide: frame-covariance

**Direction (user):** Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives.
(Auto-mode continuation: the Hessian route is coordinate-free; tide 51's diagonal rotation law for arbitrary tensors.)
**Seabed:** laplace, main 344cff4
**Started:** 2026-09-22T10:17Z

## Candidates v1 (Claude)

See `gpt_frame_covariance_prompt_v1.md` (A–C verbatim).

- A: `rotateT`, `rotateQ`; `contractT`, `contractQ`, `bubble`, `tadpoleLine`, `oneLoopPi`, `oneLoopCov` covariant under
  `H ↦ QHQᵀ`, `T ↦ rotateT Q T`, `Q₄ ↦ rotateQ Q Q₄` (with `(t • QHQᵀ)⁻¹ = Q (t•H)⁻¹ Qᵀ` unconditionally).
- B: `meanShift` covariant; `covKFormula` (with `B ↦ QBQᵀ`, `b ↦ Qb`) and `twoLoopEnergy` invariant.
- C: `rotT Q α = rotateT Q (diagT α)`, `rotQ Q γ = rotateQ Q (diagQ γ)`.

## Numerical check

`numcheck_frame_covariance.py` (`d = 4`, `t = 7`, random orthogonal `Q`, random symmetric tensors): `S' − QSQᵀ`, the four
contractions, `oneLoopCov`, `meanShift`, `covKFormula`, `twoLoopEnergy` all covariant to `≤ 7e-17`; the same with *non-symmetric*
`T`, `Q₄` (`≤ 2e-17`), so no symmetry hypothesis is needed.

## GPT-6 Astra v1

Verbatim in `gpt_frame_covariance_v1.md`. Summary: A and B hold without symmetry of `T`, `Q₄` (equivariance of contractions; the
workhorse is `∑ₖₗ Qₖ_c (QSQᵀ)ₖₗ Qₗ_e = S_{ce}`, which needs neither symmetry nor invertibility); keep the slot order in every
auxiliary representation (`S (slice T j) Sᵀ`, not `S (slice T j) S`). The inverse identity `(t • QHQᵀ)⁻¹ = Q (t•H)⁻¹ Qᵀ` is
unconditional (`Matrix.mul_inv_rev` is unconditional; both sides vanish for singular `H`; includes `t = 0`). Correction to the
motivation: covariance does *not* detect every misplaced index (permuting slots or changing coefficients preserves covariance); it
tests the tensorial structure, while the diagonal evaluations test the rest. Strategy: hybrid, matrix/Frobenius route for the bubble,
`frob X Y = tr(Xᵀ Y)` with bilinearity, orthogonal invariance, slice transport and the bridge to the definition; never globally
normalise nested sums with `mul_sum`/`sum_mul`. Cheap additions: `rotateT 1 T = T`, composition `rotateT Q₁ (rotateT Q₂ T) =
rotateT (Q₁Q₂) T` (no orthogonality), linearity, symmetry preservation if a predicate exists; C definitely. Vote A+B+C.

## Vote
- Claude: A+B+C
- GPT-6 Astra: A+B+C ("A is the core deliverable; B is the payoff; C connects it to the existing seabed")

Adopted: matrix route throughout (the prototype already used it); `rotateT_one`, `rotateQ_one` added; composition law attempted
if cheap; the "covariance is not a complete index test" correction goes into the note and staging text.
