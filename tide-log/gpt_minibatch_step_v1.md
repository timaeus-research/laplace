### 1. Correctness

**A.1–A.4 are correct**, assuming \(n\ge2\), \(1\le m\le n\), \(h\ge0\), \(H=\operatorname{popMean}(Hs)\), and \(\sum_i g_i=0\). Batches must be fresh uniform subsets, and the Gaussian noise independent of the batch and current state.

Write
\[
D_i=H_i-H,\qquad c=\frac{1-m/n}{m(n-1)},\qquad A=I-htH.
\]
For \(a_i=H_iw-g_i\),
\[
\bar a=Hw,\qquad
\operatorname{batchMean}(a)-\bar a=(H_B-H)w-g_B.
\]
Thus the **single-family application of `fpc_bilinear` is exactly right**.

Putting \(r_i=D_iw-g_i\), the conditional second moment is
\[
Aww^\top A^\top+2hI+h^2t^2c\sum_i r_ir_i^\top.
\]
The expansion is
\[
r_ir_i^\top
=D_iww^\top D_i^\top
-\underbrace{D_iwg_i^\top}_{\text{negative}}
-\underbrace{g_iw^\top D_i^\top}_{\text{negative}}
+g_ig_i^\top.
\]
Both cross terms disappear under a centred law. Consequently,
\[
\Sigma'
=A\Sigma A^\top+2hI+h^2t^2C_g
+\operatorname{minibatchCoeff}(h,t,m,n)\,\operatorname{stateTerm}(D,\Sigma),
\quad C_g=c\sum_i g_ig_i^\top.
\]

* The attached `fullLinear` **explicitly uses `A * X * Aᵀ`**, not `A * X * A`.
* `fullStep` adds `N` after the state term; only additive reassociation is needed.
* **`ulaStep` and `minibatchNoise` are imported, not defined in the supplied excerpts.** The identification with `e8FullStep (t • H) ...` requires checking that they unfold to \(I-hP\) and \(2hI+h^2t^2C\), respectively. With those definitions, the match is exact.
* Yes: under centring, \(S^2=(n-1)^{-1}\sum_i g_ig_i^\top\), so \((1/m)(1-m/n)S^2=C_g\).

Minor convention correction: if \(\nabla l_i(w)=H_iw-g_i\) in coordinates centred at \(w^*\), then \(\nabla l_i(w^*)=-g_i\). Calling \(g_i\) the gradient itself reverses that sign, though its covariance is unchanged.

Uniqueness/PSD of the fixed-point solution requires the **contraction and positivity hypotheses** from `FullStep.lean`; it is not unconditional.

### 2. Lean route

**Entrywise scalar integrals are likely less painful here.** They align with the existing Gaussian lemmas and avoid matrix-norm/continuous-linear-map infrastructure.

Important details:

* Prove weighted integrability of constants, coordinates, and coordinate products **before** distributing integrals. Moment-value identities alone do not justify `integral_add`.
* Record `gaussianZ (matCLM 1) ≠ 0` and the zeroth-moment normalization.
* For \(s=\sqrt{2h}\), use `Real.sq_sqrt` with \(0\le2h\).
* Your coordinate and coordinate-product integrability hypotheses suffice for every law-form polynomial. Probability normalization handles constants.
* Define the mean expectation separately; the proposed matrix expectation only handles matrix-valued functions.
* `Matrix.of` adds little here: a matrix already is a function of two indices. `ext i j` is the natural proof entry point.

Rather than repeatedly invoking broad `simp`, prove one reusable entry lemma:
\[
(A X A^\top)_{ij}=\sum_k\sum_l A_{ik}X_{kl}A_{jl}.
\]
`Matrix.mul_apply`, `Matrix.transpose_apply`, finite-sum distributivity, and `Finset.sum_comm` establish it; associativity may need explicit normalization. Likewise isolate the outer-product sandwich identity.

Use the matrix-valued Bochner route only if suitable integral/CLM helpers already exist.

### 3. Nearby strengthening / vote

For a noncentred law, let \(q=\mathbb E[w]\), \(M=\mathbb E[ww^\top]\). Then
\[
q'=Aq,\qquad
M'=\operatorname{e8FullStep}(M)
-h^2t^2c\sum_i\bigl(D_iqg_i^\top+g_iq^\top D_i^\top\bigr).
\]
This is an **affine joint recursion on \((q,M)\)**; the centred subspace is invariant. It cleanly explains why second moments alone close in A.4.

**Vote: A, with the joint mean/raw-second-moment recursion if inexpensive, then centred stationary equation and conditional `fullFixed` uniqueness as corollaries—not uniqueness of the stationary distribution.**