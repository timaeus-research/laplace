## 1. A–C are correct, but the term in B is not generally the leading correction

Write
\[
T(X)=AXA^\top,\qquad B(X)=\sum_iD_iXD_i^\top,\qquad
L=T+cB,
\]
and let \(S=\Sigma^{mb}\), \(F=\Sigma_{\rm full}\). Thus
\[
S=T(S)+N,\qquad F=L(F)+N.
\]
Assume \(c\ge0\), \(N\succeq0\), and the stated contraction condition.

**A is correct.** For \(H=U\operatorname{diag}(\lambda)U^\top\), with \(U\) orthogonal and \(\lambda_j\ge0\),
\[
\operatorname{tr}(HX)=\sum_j\lambda_j(U^\top XU)_{jj}\ge0
\]
whenever \(X\succeq0\). Apply this to \(Y-X\) for trace monotonicity.

**B is correct as a lower-bound chain**, provided \(t\ge0\), \(\widehat C\succeq0\), and the denominators \(p_i\kappa_i\) are positive. In particular,
\[
\operatorname{tr}(HS)+c\operatorname{tr}(HB(S))
\le \operatorname{tr}(HF).
\]

However, **\(cB(S)\) is a one-step lower correction, not generally the exact first-order correction in \(c\)**. The distinction is that the new covariance is subsequently propagated by the additive dynamics.

Indeed, with
\[
R=(I-T)^{-1}=\sum_{r\ge0}T^r,\qquad K=RB,
\]
one obtains
\[
F=S+cK(F)
\quad\Longrightarrow\quad
F=\sum_{k\ge0}c^kK^k(S).
\]
Consequently, holding \(A,N,D\) fixed,
\[
F=S+cRB(S)+O(c^2),
\]
and the genuine leading LLC correction is
\[
\boxed{\frac t2\,c\,\operatorname{tr}\!\left(HRB(S)\right).}
\]
Since \(R\) is positive and contains the identity term, this dominates the proposed correction. You can strengthen B to
\[
\operatorname{tr}(HS)+c\operatorname{tr}(HB(S))
\le
\operatorname{tr}(HS)+c\operatorname{tr}(HRB(S))
\le
\operatorname{tr}(HF).
\]

A scalar example makes the distinction transparent:
\[
F=\frac{N}{1-a^2-cd^2},\qquad S=\frac{N}{1-a^2}.
\]
The actual first-order increment is \(cd^2S/(1-a^2)\), not \(cd^2S\).

### Clean upper bounds

Put
\[
a=\|A\|\|A^\top\|,\quad
b=\sum_i\|D_i\|\|D_i^\top\|,\quad q=a+cb<1.
\]
The difference equation
\[
F-S=L(F-S)+cB(S)
\]
gives the inexpensive bound
\[
\boxed{\|F-S\|\le \frac{c\|B(S)\|}{1-q}
\le\frac{cb}{1-q}\|S\|.}
\]
For the induced \(\ell^\infty\) matrix norm in dimension \(d\),
\[
0\le\operatorname{tr}(HF)-\operatorname{tr}(HS)
\le d\|H\|\frac{c\|B(S)\|}{1-q}.
\]
Multiply by \(t/2\) for the LLC bound.

For a controlled leading-order expansion, set \(r=cb/(1-a)<1\). Then
\[
\left\|F-S-cRB(S)\right\|
\le \frac{r^2}{1-r}\|S\|.
\]

A **relative trace bound** needs additional order/comparability information; it does not follow simply by replacing matrix norms with traces. One clean sufficient condition is
\[
K(S)\preceq\beta S,\qquad c\beta<1.
\]
Positivity of \(K\) then gives
\[
F\preceq\frac{S}{1-c\beta},
\qquad
\operatorname{tr}(HF)\le
\frac{\operatorname{tr}(HS)}{1-c\beta}.
\]
When \(S\succ0\), such a \(\beta\) can be obtained from the largest eigenvalue of
\(S^{-1/2}K(S)S^{-1/2}\).

**C is also correct.** With \(\widehat D_i=U^\top D_iU\) and \(\widehat S=U^\top SU\),
\[
\operatorname{tr}(HB(S))
=\sum_{i,j}\lambda_j
\sum_{k,\ell}(\widehat D_i)_{jk}\widehat S_{k\ell}
(\widehat D_i)_{j\ell}.
\]
No simultaneous diagonalisation of the \(D_i\) and \(H\) is needed.

## 2. Scaling and the comparison with the constant-\(C\) bias

Define
\[
f=\frac{1-m/n}{m(n-1)},\qquad c=h^2t^2f.
\]
Your displayed one-step correction is algebraically right:
\[
J_{\rm one}
=\frac{h^2t^3f}{2}\operatorname{tr}(HB(S)).
\]
If \(h=\eta/t\), \(S=\bar S/t+o(t^{-1})\), and \(H,D_i\) remain fixed, then
\[
J_{\rm one}
=\frac{\eta^2f}{2}\operatorname{tr}(HB(\bar S))+o(1).
\]
Thus it is **\(O(1)\) in \(t\)** under those assumptions.

There are three important qualifications.

1. **The true leading correction includes the resolvent.**
   \[
   J_{\rm leading}
   =\frac t2\,c\,\operatorname{tr}(HRB(S)).
   \]
   If \(A\) has a uniformly stable limit at fixed \(\eta\), this is also \(O(1)\) in \(t\). But when additionally taking small \(\eta\), typically \(I-T=O(\eta)\), so \(R=O(\eta^{-1})\). The true correction is then typically **\(O(\eta)\)**, whereas the one-step bound is **\(O(\eta^2)\)**. This is another reason not to label the latter “the leading correction.”

2. **The sum over samples usually cancels the apparent extra \(1/n\).** For an averaged Hessian-fluctuation statistic,
   \[
   f\sum_i(\cdots)
   =\frac{n-m}{m(n-1)}\,\frac1n\sum_i(\cdots).
   \]
   Thus, for fixed per-sample fluctuation size and \(m\ll n\), the scaling is typically fluctuation size divided by **\(m\)**, not by \(mn\). A \(1/(mn)\) prefactor is appropriate only when the fluctuation size is defined using the *unnormalised sum*.

3. **The constant-\(C\) comparison requires the denominator scaling.** Substituting \(h=\eta/t\) gives
   \[
   \frac{\eta t^2}{4}\sum_i
   \frac{\lambda_i\widehat C_{ii}}{p_i\kappa_i}.
   \]
   This is \(O(\eta t\,\operatorname{tr}\widehat C)\) if \(p_i\kappa_i=\Theta(t)\), with suitable uniform bounds. If \(\widehat C\) already denotes the minibatch covariance, its batch factor is already included: do not divide by batch size again.

Suggested prose:

> The additive-law formula captures the constant-covariance minibatch bias. The full covariance law adds a nonnegative Hessian-fluctuation correction. Its one-step contribution gives an explicit lower bound; its leading perturbative contribution includes propagation through the additive Lyapunov resolvent. At fixed \(h t=\eta\), with additive covariance \(O(t^{-1})\), this additional contribution is \(O(1)\) in temperature, whereas the constant-covariance bias can grow linearly in temperature.

For the **LLC mean** itself, explicitly state the second-moment bridge:
\[
\mathbb E\!\left[\frac t2u^\top Hu\right]
=\frac t2\operatorname{tr}(H\Sigma)+\frac t2\mu^\top H\mu.
\]
No Gaussian assumption is needed. Identification with \((t/2)\operatorname{tr}(HF)\) requires a **centred stationary law with finite second moments**. The covariance fixed-point theorem alone should not be described as proving existence of that stationary law.

## 3. Lean route and pitfalls

Your proposed route is sound. I would organise it as follows.

- **Prove A once as two reusable lemmas:** nonnegativity of `trace (H * X)` for PSD \(X\), then monotonicity from PSD \(Y-X\). The trace product need not itself be symmetric; the frame identity is the certificate of nonnegativity.
- For \(U^\top XU\), check the orientation of the available PSD congruence lemma. Some formulations produce \(MXM^\top\); instantiate with \(M=U^\top\). Over `ℝ`, also watch `transpose` versus `conjTranspose`.
- **Keep B abstract in \(S\)** initially: assume its additive fixed-point equation and PSD. Instantiate with `lyapunovVia` only in the final LLC theorem. This avoids repeatedly unfolding frame constructions.
- Apply trace monotonicity directly to
  \[
  F-(S+cB(S))\succeq0,
  \]
  or normalize the existing `F - S - c • B S` statement to that form first. Then use trace linearity. This is generally cleaner than expanding the whole LLC chain at once.
- Separate the three scalar inequalities in B. Besides PSD, the chain needs the nonnegativity of \(c\), \(t/2\), and the constant-\(C\) summands.
- For C, first prove the matrix identity
  \[
  U^\top B(S)U
  =\sum_i\widehat D_i\,\widehat S\,\widehat D_i^\top.
  \]
  Only then expand the diagonal entries. This keeps the \(UU^\top=1\) insertions out of the four-index sum.
- Expect explicit associativity rewrites and `Finset.sum_comm`/`sum_congr`; avoid a single large `simp` proof.
- For the finite-population coefficient, handle the parameter assumptions explicitly: \(m>0\), \(n>1\), \(m\le n\). In particular, avoid accidental natural-number subtraction before casting.

For this tide, the finite-iterate result below is likely much cheaper than formalising the resolvent and its perturbation theory.

## 4. Cheap additions: priorities

**First priority: monotone finite-iterate lower bounds.** Let \(X_0=S\), \(X_{k+1}=\operatorname{fullStep}(X_k)\). Positivity gives
\[
S=X_0\preceq X_1\preceq\cdots\preceq F,
\]
hence monotone LLC lower bounds. More explicitly,
\[
\boxed{X_k=S+c\sum_{j=0}^{k-1}L^jB(S).}
\]
They converge to \(F\) under contraction. This extends the existing one-step theorem naturally and makes the missing propagation visible.

**Second priority: \(D=0\), and preferably \(c=0\), recover equality.** Both are immediate uniqueness corollaries. The latter directly covers full-batch sampling when the coefficient vanishes.

**Third priority: strictness, with the weighted-row qualification.** If \(S\succ0\), then
\[
\operatorname{tr}(HB(S))>0
\]
whenever some row \(j\) of some \(\widehat D_i\) is nonzero **and \(\lambda_j>0\)**. A nonzero row in a zero-eigenvalue direction of \(H\) is insufficient. If \(H\succ0\), this simplifies to “some \(D_i\ne0\).” With \(c>0\) and \(t>0\), this proves strict LLC inflation.

**Vote:** ship A–C, call B a one-step lower bound rather than the exact first-order correction, add monotone iterates and zero-noise equality, and explain the resolvent-leading correction and scaling in prose.