### 1. Correctness

**(a) Both closed forms are correct.** Write \(c=T:\Sigma\) and \(q=\langle\Sigma b,c\rangle\). The four terms reduce to
\[
\tfrac12\operatorname{tr}(B\Sigma)
+\begin{cases}0&\text{quadratic},\\ \tfrac12q&\phi=V,\end{cases}
-\tfrac12q-\tfrac12q.
\]
Here \(\Sigma A\Sigma=\Sigma\), and symmetry moves \(\Sigma\) across the dot product.

**(b) Yes: \(d/2\).** Taking \(\psi=V\) gives \(b=0\), \(B=P\), hence
\[
\left|t^2\operatorname{Var}_t(V)-d/2\right|\le C/t.
\]
The numerical value \(0.9935\) is consistent with the limit \(1\) in dimension two.

**Qualification on Watanabe:** this coefficient agrees numerically with the singular fluctuation \(\nu=d/2\) of a **regular, well-specified statistical model**, but the theorem alone does not identify the two notions. Watanabe’s functional variance is a sum of posterior variances of individual log likelihoods, not the posterior variance of their sum/average; its asymptotic expectation is \(2\nu=d\) in that setting. Avoid presenting “functional variance \(=d\)” as an exact identity or as following from this deterministic Laplace theorem. Regular misspecified models need not have \(\nu=d/2\).

**(c) Yes—the cubic correction has twice the coefficient.** Suggested footnote:

> Although the loss and its quadratic approximation have the same Hessian at the minimiser, their second-order covariances with a general observable differ. The cubic term of the loss contributes \(+\frac12\langle\Sigma\nabla\psi,T:\Sigma\rangle\), cancelling half the correction induced by the Gibbs weight; the quadratic observable has no such contribution.

### 2. Lean route

Your route is sound. Main implementation cautions:

- **Keep unfolding local.** Use `change` or projection lemmas to expose `.A` and `.Φ`; both advertised projections are definitional. Avoid unfolding the entire observable structure.
- **Composition direction:** for `A.comp (Σ.comp X)`, reassociate to `(A.comp Σ).comp X`, then cancel. Your proposed `← ContinuousLinearMap.comp_assoc` is the intended direction under the usual statement; confirm the actual declaration with `#check`.
- **Prove both inverse identities once.** Use the same determinant-unit argument as `trASig_matCLM_inv`; then derive pointwise cancellation lemmas with `congrArg (fun f => f v)`. These are often more robust than rewriting nested applications through `.comp`.
- **Trace:** package `trASig (B.comp Σ) 1 = trASig B Σ` as a helper. If `simp` does not reduce the CLM `1`, explicitly expose its identity action.
- **Zero contraction:** try `ext i; simp [tensorContractMatrix]`. A `Fin 3` match generally becomes harmless once the zero multilinear map is evaluated; if needed, isolate a zero-contraction lemma rather than expanding contractions throughout the main proof.
- **Symmetry:** reuse `quadForm_symm_matCLM` with positive definiteness of \(P^{-1}\), rather than reproving symmetry entrywise. Check the precise arguments of `Matrix.posDef_inv_iff`; do not assume its rewrite orientation.
- Finish the scalar cancellation with `ring`.
- For `potentialObservableQuintic`, reuse the potential’s odd-part bound, restricting the observable’s `min` jet radius to the potential’s jet radius.

### 3. Vote

**A, with the Watanabe interpretation qualified; add explicit `Tendsto` corollaries if cheap, and defer B.**