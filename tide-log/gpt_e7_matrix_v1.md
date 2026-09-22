## 1. Tensor algebra: A is correct; C has a coefficient typo

Write
\[
s_i=\frac1{\lambda_i t},\qquad
S=Q\operatorname{diag}(s)Q^\top,\qquad D=Q^\top S Q=\operatorname{diag}(s).
\]
Assume \(t>0\) and \(\lambda_i>0\), as in the intended application.

Expanding the rotated tensors and collecting eigen-indices gives the following identities before using that \(D\) is diagonal:
\[
\begin{aligned}
(\operatorname{contractQ}(\mathrm{rotQ},S))_{ij}
 &=\sum_p\gamma_p Q_{ip}Q_{jp}D_{pp},\\
(\operatorname{contractT}(\mathrm{rotT},S))_l
 &=\sum_p\alpha_p Q_{lp}D_{pp},\\
\operatorname{bubble}_{ij}
 &=\sum_{p,q}\alpha_p\alpha_q Q_{ip}Q_{jq}D_{pq}^{\,2},\\
\operatorname{tadpoleLine}_{ij}
 &=\sum_p\alpha_pQ_{ip}Q_{jp}
      \sum_q\alpha_qD_{pq}D_{qq}.
\end{aligned}
\]
Thus, for this \(S\),
\[
\begin{aligned}
\operatorname{contractQ}&=Q\operatorname{diag}(\gamma_i s_i)Q^\top,\\
\operatorname{contractT}_l&=\sum_p\alpha_pQ_{lp}s_p,\\
\operatorname{bubble}
 &=\operatorname{tadpoleLine}
 =Q\operatorname{diag}(\alpha_i^2s_i^2)Q^\top.
\end{aligned}
\]
In particular, **bubble equals tadpoleLine here, not for general tensors and covariances**.

The signs and factors in \(\Pi\) are correct:
\[
-\frac t2\gamma_i s_i
+\frac{t^2}{2}\alpha_i^2s_i^2
+\frac{t^2}{2}\alpha_i^2s_i^2
=\frac{\alpha_i^2}{\lambda_i^2}-\frac{\gamma_i}{2\lambda_i}.
\]
Multiplication by \(S\) on both sides consequently gives
\[
\boxed{
\operatorname{oneLoopCov}
=Q\operatorname{diag}\left(
\frac1{\lambda_i t}
+\frac{\alpha_i^2/\lambda_i^4-\gamma_i/(2\lambda_i^3)}{t^2}
\right)Q^\top.}
\]

Keep a nonzero-\(t\) hypothesis on the closed form for \(\Pi\): at \(t=0\), Lean’s totalized inverses do not justify the cancellation used above.

### Derivative identification

It is correct. Since
\[
A_p(w)=\sum_iQ_{ip}(w_i-c_i),
\qquad \partial_i A_p=Q_{ip},
\]
and \(A(c)=0\), the second, third, and fourth derivatives at \(c\) are
\[
H_{ij}=\sum_p\lambda_pQ_{ip}Q_{jp},\quad
T_{ijk}=\sum_p\alpha_pQ_{ip}Q_{jp}Q_{kp},\quad
R_{ijkm}=\sum_p\gamma_pQ_{ip}Q_{jp}Q_{kp}Q_{mp}.
\]
There are no missing factorials: the \(1/6\) and \(1/24\) in the potential cancel upon differentiation. Under the scalar minimum hypotheses, \(c\) is the minimum in question. Thus the proposed tensors are indeed the E2 tensors, even if that identification remains explanatory rather than formally proved in this tide.

### Correction to C

Under the note’s parametrization,
\[
\boxed{
C_i=\frac{\alpha_i^2}{\lambda_i^4}
-\frac{\gamma_i}{2\lambda_i^3}
=\frac{a^2-\tfrac12}{\lambda_i},
}
\]
**not** \((a^2-\tfrac12)/\lambda_i^2\).

This correction is essential and agrees with the supplied limit and numerical check. Setting \(b=a^2-\tfrac12\), the note-specialized matrix formula becomes particularly simple:
\[
\operatorname{oneLoopCov}(t)=\left(1+\frac bt\right)S(t).
\]

## 2. Lean strategy: factor through \(D=Q^\top S Q\), with staged lemmas

Your factorization is the right abstraction. I would not rely on a single large `simp` to normalize all six-index expressions. `simp` distributes finite sums effectively, but it does not reliably choose the desired permutation and factorization of nested sums.

A robust organization is:

1. **Prove a matrix-entry bridge**
   \[
   \sum_k\sum_m Q_{kp}S_{km}Q_{mq}=(Q^\top S Q)_{pq}.
   \]
   This is a short `Matrix.mul_apply`/sum-distribution calculation.

2. **Prove the four contraction identities in terms of \(D\)** displayed above. These are reusable algebraic lemmas; they do not require orthogonality.

3. **Specialize to diagonal \(D\)**. At this point, `diagonal_apply`, `simp`, and the finite-sum delta lemmas should collapse the eigen-index sums cleanly.

4. **Assemble \(\Pi\) and covariance using matrix algebra**, rather than reopening entrywise sums. In particular,
   \[
   (Q\operatorname{diag}(x)Q^\top)
   (Q\operatorname{diag}(y)Q^\top)
   =Q\operatorname{diag}(xy)Q^\top.
   \]
   Then the remaining coefficient identities are scalar `field_simp`/`ring` goals with the nonzero hypotheses supplied.

For the orthogonality sum, extracting an entry of `hQ` is already the appropriate idiom:
```lean
have hentry := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M p q) hQ
```
Simplifying `hentry` with `Matrix.mul_apply` and the transpose/identity entry rules gives
\[
\sum_k Q_{kp}Q_{kq}=\text{if }p=q\text{ then }1\text{ else }0.
\]
I would package this as a local helper, rather than search for a specialized theorem about this exact sum.

One further simplification: prove the contraction formulas for **arbitrary diagonal entries \(s_i\)** first. Introduce \(s_i=1/(\lambda_i t)\) only afterward. This keeps inverses and denominator side conditions out of the tensor algebra.

## 3. B: squared error is the right core statement; retain the Laplace denominator

Use
\[
\frac{\sum_{j,k}(\operatorname{Cov}_w(t)-\operatorname{oneLoopCov}(t))_{jk}^2}
     {\sum_{j,k}S(t)_{jk}^2}
\le \frac K{t^4}
\]
as the main formal theorem. It avoids unnecessary square-root bookkeeping and directly uses the available Frobenius bridge.

The bound follows with explicit constants. Suppose the scalar rate theorem supplies
\[
\left|tV_i(t)-\lambda_i^{-1}-C_i/t\right|\le K_i/t^2
\quad(t\ge T_i).
\]
For a common \(T\ge1,T_i\), division by positive \(t\) gives
\[
|V_i(t)-(\lambda_i t)^{-1}-C_i/t^2|\le K_i/t^3.
\]
Orthogonal invariance then yields
\[
\sum_{j,k}(\operatorname{Cov}_w-\operatorname{oneLoopCov})_{jk}^2
\le \frac{\sum_iK_i^2}{t^6},
\qquad
\sum_{j,k}S_{jk}^2=\frac{\sum_i\lambda_i^{-2}}{t^2}.
\]
For a nonempty index type, take
\[
K=\frac{\sum_iK_i^2}{\sum_i\lambda_i^{-2}}.
\]

To use the supplied `sum_sq_conj`, instantiate its conjugating matrix with \(U=Q^\top\). Its hypothesis then reduces exactly to \(Q^\top Q=1\).

A useful public-facing corollary is
\[
\frac{\sqrt{\sum_{j,k}(\operatorname{Cov}_w-\operatorname{oneLoopCov})_{jk}^2}}
     {\sqrt{\sum_{j,k}S_{jk}^2}}
\le\frac{\sqrt K}{t^2}.
\]
This is relative Frobenius error; “relative RMS” gives the same ratio if numerator and denominator use the same normalization.

**Keep \(\|S\|_F\) as denominator**, matching the proposed note statement. Normalization by \(\|\operatorname{Cov}_w\|_F\) is asymptotically equivalent because
\[
\frac{\|\operatorname{Cov}_w-S\|_F}{\|S\|_F}\to0,
\]
but proving and using that equivalence is unnecessary scope here.

### Dimension-zero caveat

Require `Nonempty ι` or \(0<d\) for meaningful relative errors and for C’s positive lower bound. With an empty index type, Lean evaluates these ratios as \(0/0=0\). B is then trivially true, but the stated nonzero Laplace limit and lower bound are false. The supplied limit theorem must have a nonemptiness hypothesis, possibly omitted in the summary.

## 4. Scope, sharpening, and vote

**A+B+C is a coherent single tide**, with A the substantial algebraic component, B the main E7 result, and C a short contrast corollary.

I would structure the deliverables as follows:

- **A:** General diagonal-frame contraction lemmas and the closed form for `oneLoopCov`.
- **B:** General-parameter squared relative Frobenius \(O(t^{-4})\) bound, under the existing scalar sharp-rate hypotheses.
- **C:** Note-specialized contrast, using the corrected \(C_i=b/\lambda_i\):
  \[
  \operatorname{oneLoopCov}=(1+b/t)S,
  \qquad
  t^2\,\mathrm{rel}^2(\mathrm{Laplace})\to b^2.
  \]

When \(b\ne0\), the limit gives an eventual lower bound with, for example,
\[
c=\frac{b^2}{2}>0:
\qquad
\mathrm{rel}^2(\mathrm{Laplace})\ge\frac c{t^2}.
\]
The limit also supplies the corresponding upper bound, so the full contrast is **Laplace relative error \(\Theta(t^{-1})\)** versus **one-loop relative error \(O(t^{-2})\)**. Do not claim a sharp \(\Theta(t^{-2})\) one-loop rate without an additional nonvanishing next-order coefficient.

At \(a^2=1/2\), the correction vanishes, `oneLoopCov = S`, and B actually upgrades Laplace itself to relative \(O(t^{-2})\). This is a useful explicit exceptional-case remark.

Writing `oneLoopCov` as \(S+S\Pi S\) should be a presentation corollary obtained by unfolding its definition, not a separate proof target.

**Vote: A+B+C, with B as the headline and A as its reusable algebraic foundation. Correct the coefficient in C and make positive dimension explicit.**