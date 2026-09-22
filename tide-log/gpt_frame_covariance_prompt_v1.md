# Tide `frame-covariance` (laplace seabed, main 344cff4): candidates for GPT-6 Astra

## Context

The note's Hessian-route formulas are tensor expressions in `H = D²L(w*)`, `T = D³L(w*)`, `Q₄ = D⁴L(w*)` and `S = (tH)⁻¹`:
eq:oneloop `Cov = S + SΠS`, `Π = −(t/2)(Q₄:S) + (t²/2) TSST + (t²/2) T·S·(T:S)` (`oneLoopCov`), eq:mean `−½ S (tT:S)` (`meanShift`),
eq:covK (`covKFormula t H T B b`), and the two-loop energy `½ tr(HS) + (t/12)θ + (t/8)δ − (1/8)q` (`twoLoopEnergy`). The seabed
evaluates them on E2's *diagonal-in-a-rotated-frame* tensors `rotT Q α i j k = ∑ₗ αₗ Qᵢₗ Qⱼₗ Qₖₗ`, `rotQ`, `H = Q diag λ Qᵀ`
(`OneLoopRotated`, `E2Matrix`, `TwoLoopEnergy`), with the eigenframe contraction `∑ₖₘ Qₖₚ (Q diag s Qᵀ)ₖₘ Qₘq = δₚq sₚ` as the
workhorse, and `Laplace.Multi.GibbsRotation` shows the *exact* Gibbs quantities transport under `w = Qu + c`.

Missing: the statement that the *formulas themselves* are frame-covariant for arbitrary tensors, i.e. that the Hessian route is
coordinate-free. This is also the natural regression test of every index placement in the four formulas: a misplaced index breaks
covariance.

## Candidates (numerically verified, `numcheck_frame_covariance.py`, `d = 4`, random `Q`, random symmetric *and* non-symmetric
tensors, all identities to `1e-17`)

**A. Rotated tensors and the covariant contractions.** `rotateT Q T i j k := ∑ₐ_b_c Qᵢₐ Qⱼ_b Qₖ_c T_{abc}`,
`rotateQ Q Q₄ i j k l := ∑ Qᵢₐ Qⱼ_b Qₖ_c Qₗ_e Q₄_{abce}`. For `Qᵀ Q = 1` and *any* `S`, `T`, `Q₄`:
`contractT (rotateT Q T) (Q S Qᵀ) = Q *ᵥ contractT T S`, `contractQ (rotateQ Q Q₄) (Q S Qᵀ) = Q (contractQ Q₄ S) Qᵀ`,
`bubble (rotateT Q T) (Q S Qᵀ) = Q (bubble T S) Qᵀ`, `tadpoleLine (rotateT Q T) (Q S Qᵀ) = Q (tadpoleLine T S) Qᵀ`, hence
`oneLoopPi` covariant. Also `(t • (Q H Qᵀ))⁻¹ = Q (t • H)⁻¹ Qᵀ` for *all* `H` (both sides `0` when singular; via
`Matrix.mul_inv_rev` and `Qᵀ⁻¹ = Q`), so `oneLoopCov t (Q H Qᵀ) (rotateT Q T) (rotateQ Q Q₄) = Q (oneLoopCov t H T Q₄) Qᵀ`.

**B. The scalars and the vector.** `meanShift t (QHQᵀ) (rotateT Q T) = Q *ᵥ meanShift t H T`;
`covKFormula t (QHQᵀ) (rotateT Q T) (Q B Qᵀ) (Q *ᵥ b) = covKFormula t H T B b`;
`twoLoopEnergy t (QHQᵀ) (rotateT Q T) (rotateQ Q Q₄) = twoLoopEnergy t H T Q₄`.

**C. The diagonal case is the special case.** `rotT Q α = rotateT Q (diagT α)` with `diagT α a b c := if a = b ∧ b = c then α a
else 0`, `rotQ Q γ = rotateQ Q (diagQ γ)`, and `Q diag λ Qᵀ` is `rotate` of `diag λ`; so `OneLoopRotated`'s closed forms are A+B
applied to the separable tensors.

## Questions

1. Are the covariance statements right *without* symmetry of `T`, `Q₄` (the identities are pure index gymnastics)? Is
   `(t • (QHQᵀ))⁻¹ = Q (t•H)⁻¹ Qᵀ` really unconditional in Mathlib (`Matrix.nonsing_inv` is `0` on singular matrices;
   `Matrix.mul_inv_rev` unconditional?), or should I assume `IsUnit H.det`?
2. Lean strategy for the six-index sums (the bubble): (i) index gymnastics with the two-index contraction
   `∑ₖₗ Qₖ_c (QSQᵀ)ₖₗ Qₗ_e = S_{ce}` after distributing (tide 51 did the diagonal case this way, with a recorded gotcha that
   `simp only [Finset.mul_sum, Finset.sum_mul]` on products of two sums is dangerous), or (ii) a matrix route: `slice T i := of fun
   k l => T i k l`, `bubble T S i j = frob (slice T i) (S (slice T j) Sᵀ)` with `frob X Y := (Xᵀ Y).trace`, `slice (rotateT Q T) i =
   ∑ₐ Qᵢₐ • (Q (slice T a) Qᵀ)`, and Frobenius invariance `frob (QXQᵀ) (QYQᵀ) = frob X Y` plus `Matrix.sum_mul`/`mul_sum`/
   `trace_sum` bilinearity? Which is less error-prone?
3. Anything else worth including at low cost (e.g. `rotateT` preserves symmetry, or `rotateT` of `rotateT` is `rotateT` of the
   product `Q₁Q₂`, or covariance of the exact Taylor identity `rotatedAnharmonic_taylor`)?
4. Scope and vote (A+B+C)?
