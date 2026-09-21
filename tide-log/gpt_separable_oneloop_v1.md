## 1. Mathematics

**A–C are correct**, under the stated nonzero assumptions and the seabed’s normalization of `oneLoopPi`.

- **Bubble:** the two cubic tensors force `k = l = i` and `m = n = j`; the diagonal propagators then force `i = j`, giving `αᵢ² sᵢ² δᵢⱼ`.
- **Line tadpole:** `Tᵢⱼₖ` forces `i = j = k`, and `Sₖₗ` forces `l = i`; since `(T:S)ᵢ = αᵢsᵢ`, the result is again `αᵢ²sᵢ² δᵢⱼ`.
- Thus
  \[
  \Pi_{ii}=-\frac t2g_i s_i+t^2\alpha_i^2s_i^2,
  \qquad
  (S+S\Pi S)_{ii}
  =\frac1{\lambda_i t}
   +\frac{\alpha_i^2/\lambda_i^4-g_i/(2\lambda_i^3)}{t^2}.
  \]
- Under C’s parametrisation, the **signed correction divided by the leading term** is `(a² − 1/2)/t`. For `t > 0`, `λᵢ > 0`, it is negative when `a² < 1/2`: Laplace overpredicts the one-loop variance, and asymptotically the true variance where the expansion applies. This is not an unconditional finite-temperature inequality.

**Eigenframe scope:** B/C faithfully formalise the note’s eigenframe prediction. With an orthogonal rotation `R`, the covariance transforms as `R C Rᵀ` when all tensors are transformed consistently. Without D, however, you have not formally proved that transformation law for the implemented functional. Say explicitly that the result is in `u` coordinates.

## 2. Lean

Prefer **entrywise proofs with `by_cases hij : i = j` early**, then collapse the sums:

- Try `simp` using tensor definitions, `Matrix.diagonal_apply`, and equality orientations such as `eq_comm`.
- Where simplification stalls, use `Finset.sum_eq_single i` explicitly and discharge the surviving/off-index cases by `simp`.
- Package the contraction identities as helper lemmas; avoid manually combining every product of conditionals into one large conjunction unless necessary.

An off-index hypothesis may need reversing (`i ≠ k` versus `k ≠ i`), so plain `simp [hk]` is not always sufficient.

For inversion, first look for a diagonal-inverse theorem in the actual checkout. **I cannot certify `Matrix.inv_diagonal` or `Matrix.smul_inv` in the pinned version.** A robust fallback is to rewrite
` t • diagonal λ = diagonal (fun i => t * λ i)`,
prove its product with the proposed inverse is `1` using `diagonal_mul_diagonal`, and apply the available right-inverse characterization. Check that characterization’s precise hypotheses and orientation. Finish scalar equalities with `field_simp` using `t ≠ 0` and `λ i ≠ 0`.

## 3. Scope

**A+B+C is a coherent tide; ~250 lines is plausible**, depending on inversion and simplifier friction. Keep D separate: without existing tensor-equivariance infrastructure, expanding rank-3/rank-4 rotations brings substantial sum rearrangement and orthogonality bookkeeping.

Cheap additions:

- **Unique global minimum:** with `λ,g > 0`,
  \[
  L(u)=\frac{u^2}{24}(gu^2+4\alpha u+12\lambda),
  \]
  so `α² < 3λg` ensures `L(u)>0` for `u ≠ 0`. Under the parametrisation this becomes `a² < 3`.
  **Distinguish global from local:** this condition does not exclude other local minima. Excluding nonzero stationary points requires the stronger `α² < (8/3)λg`.
- An absolute-value version of C’s ratio is cheap and directly useful for E2.
- Do **not** claim the second-order approximation has relative error `O(t⁻²)` without a suitable remainder bound. A second-order asymptotic expansion alone generally gives only relative remainder `o(t⁻¹)`.

A+B+C closes the separable-functional gap cleanly, while rotation and stronger remainder estimates are independent follow-ups.

Vote: A+B+C