### 1. Mathematics

**A–D are correct**, subject to the existing covariance, initialization, and integrability hypotheses.

- **(i)** For finite square real matrices, either `UᵀU = 1` or `UUᵀ = 1` implies the other. Thus one assumption suffices mathematically; having both identities available simplifies the trace proof. No symmetry of `A` is needed.
- **B:** Correct provided `Σ_ULA = U diag(s₂) Uᵀ` and `P⁻¹ = U diag(1/p) Uᵀ` have been established under the existing positivity/stability hypotheses.
- **(ii)** Your column convention gives exactly `Σ̂_eig = Uᵀ Σ̂_raw U`. Entrywise expectation commutes with this deterministic linear transformation **when the entries are integrable**, giving the stated centred identity and Frobenius equality.
- **(iii)** The proposed integrability route is sound and noncircular: first prove the inverse bridge pointwise; obtain integrability of eigen-estimator entries from the known projection moments; transfer it through finite linear combinations to raw entries; only then commute expectation. On a probability space, `L⁴` projections give `L²` products and hence integrability. They also give `L²` raw estimator entries, sufficient for integrability of the squared centred error.

**Important terminology:** D transfers the **centred variance**, normalized by the target norm. It is not automatically the MSE against `Σ_ULA`; that additionally includes squared bias.

### 2. Lean

Your proposed expansions are reasonable. A cleaner reusable abstraction is the outer-product identity
\[
 (U^\top x)(U^\top x)^\top = U^\top(xx^\top)U.
\]
Prove its coordinate form once, then commute conjugation through the finite pool. `Matrix.vecMulVec`, `mulVec`, and their multiplication lemmas may help; otherwise `ext`, `Matrix.mul_apply`, finite-sum distribution, and `ring` are robust.

- The real inner-product conversion via `inner_eq_star_dotProduct` and simplification of conjugation is appropriate. Check factor order in the library lemma; real commutativity resolves it.
- Two `mul_apply` expansions can produce a different summation order from the desired normal form: one `sum_comm` plus reassociation resolves this. No need to depend on a particular primed lemma.
- Entrywise `integral_finsetSum` and constant-multiplication lemmas are fine. Supply integrability of each summand explicitly; Lean’s totalized integral does **not** make finite-sum linearity unconditional.
- Keep the core API in `∑ᵢⱼ Aᵢⱼ²`. A Frobenius-norm wrapper improves presentation but adds scoped-instance/coercion work. Ordinary matrix norm notation must not silently select a different norm.

### 3. Scope

**A+B+C+D is coherent**, though ~250 lines is optimistic unless the spectral decompositions and moment APIs are already convenient.

Both extras are valuable follow-ups:
- the closed-form mean is cheap once the diagonal eigenbasis mean—including vanishing off-diagonal entries—is available, with the existing initialization assumptions;
- the raw target-MSE theorem is especially useful because it addresses the bias distinction above. Reuse the existing target theorem rather than redoing variance–bias algebra.

The core bridge closes the coordinate gap cleanly; keep extras optional rather than expanding the acceptance scope.

Vote: A+B+C+D