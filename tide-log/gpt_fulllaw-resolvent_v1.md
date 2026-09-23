**Vote: adopt A–D and the exact/inequality parts of E.** These are a meaningful improvement over the one-step bound. Qualify the scaling claim, reject the proposed general PSD upper bound, and replace “integrated autocorrelation time” by “geometric accumulation factor.”

Throughout, assume \(c\ge0\), \(N\succeq0\), and \(L=a+cb<1\). For the LLC lower bounds, also assume \(t\ge0\) and \(H\succeq0\).

## 1. Candidates A–E

### A. Exact resolvent identity: correct

Subtracting the two fixed-point equations gives
\[
\Delta=T(\Delta)+cB(\Sigma_{\rm full}),
\]
so Lyapunov uniqueness yields
\[
\boxed{\Delta=cR(B(\Sigma_{\rm full})).}
\]

### B. Resolvent-enhanced PSD lower bound: correct

The convergent representation
\[
R(Y)=\sum_{k=0}^{\infty}A^kY(A^\top)^k
\]
shows that \(R\) is positivity-preserving and, for \(Y\succeq0\),
\[
R(Y)-Y=\sum_{k=1}^{\infty}A^kY(A^\top)^k\succeq0.
\]
Thus your interpretation is exactly right.

By linearity,
\[
\Delta-cR(B(\Sigma^{mb}))=cR(B(\Delta))\succeq0,
\]
hence
\[
\boxed{\Delta\succeq cR(B(\Sigma^{mb}))\succeq cB(\Sigma^{mb})\succeq0.}
\]

### C–D. Norm and remainder bounds: correct

Since \(\|T\|\le a<1\),
\[
\|R(Y)\|\le\frac{\|Y\|}{1-a}.
\]
Consequently,
\[
\boxed{
\|\Delta-cR(B(\Sigma^{mb}))\|
\le
\frac{c^2b\,\|B(\Sigma^{mb})\|}
{(1-a)(1-L)}.
}
\]
All intermediate inequalities in D are valid.

### E. Frame formula: correct with a simultaneous-frame assumption

Suppose an **orthonormal** frame diagonalizes both \(P\) and \(H\):
\[
\widehat P=\operatorname{diag}(p_i),\qquad
\widehat H=\operatorname{diag}(\lambda_i).
\]
Then, whether or not \(Y\) is diagonal,
\[
\operatorname{tr}(HR(Y))
=\sum_i\lambda_i\widehat{R(Y)}_{ii}
=\boxed{\sum_i\frac{\lambda_i\widehat Y_{ii}}{1-\rho_i^2}}.
\]
The off-diagonal entries of \(\widehat Y\) do not contribute to this trace.

Therefore both the exact LLC correction and your lower bound follow. Merely diagonalizing \(P\), without \(H\) being diagonal in that same frame, would not suffice.

## 2. Cheap additions

### (i) A scalar-multiple PSD upper bound: not in general

An operator norm bounds magnitude, not direction in the PSD cone. In particular,
\[
\Delta\preceq\frac{cR(B(\Sigma^{mb}))}{1-c\|RB\|}
\]
can fail even in dimension two.

Take
\[
A=0,\quad R=I,\quad
B(X)=SXS^\top,\quad
S=\begin{pmatrix}0&1\\1&0\end{pmatrix},
\quad
\Sigma^{mb}=N=\begin{pmatrix}1&0\\0&0\end{pmatrix},
\]
with \(0<c<1\). Here \(a=0,b=1,L=c\), and
\[
Q_1:=cR(B(\Sigma^{mb}))
=\begin{pmatrix}0&0\\0&c\end{pmatrix},
\]
whereas
\[
\Delta=\begin{pmatrix}
c^2/(1-c^2)&0\\
0&c/(1-c^2)
\end{pmatrix}.
\]
No finite scalar multiple of \(Q_1\) dominates \(\Delta\).

A valid version needs an additional **order-domination assumption**, such as
\[
K(Q_1)\preceq\kappa Q_1,\qquad K:=RB,\qquad c\kappa<1.
\]
Then positivity and iteration give
\[
\Delta\preceq\frac{Q_1}{1-c\kappa}.
\]

**Vote: skip this addition unless such an assumption is natural.**

### (ii) Second order and a positive remainder: yes—cheap and useful

Set
\[
K:=RB,\qquad \theta:=c\|K\|
\le\frac{cb}{1-a}<1.
\]
Then
\[
\Delta=cK(\Sigma^{mb})+cK(\Delta),
\]
so
\[
\boxed{\Delta=\sum_{j=1}^{\infty}c^jK^j(\Sigma^{mb}).}
\]
Every summand is PSD. In particular, with
\[
Q_1=cK(\Sigma^{mb}),\qquad
Q_2=c^2K^2(\Sigma^{mb}),
\]
we have
\[
\boxed{\Delta-Q_1-Q_2=c^2K^2(\Delta)\succeq0}
\]
and
\[
\boxed{
\|\Delta-Q_1-Q_2\|
\le\frac{\theta^2}{1-\theta}\|Q_1\|.
}
\]
This is \(O(c^3)\) when \(K\) and \(\Sigma^{mb}\) are held fixed as \(c\to0\).

**Vote: include, especially the monotone hierarchy of PSD lower bounds.**

### (iii) Anchored scaling: substitute first; do not infer the extra \(1/\lambda_i\)

Write
\[
\alpha:=\frac{1-m/n}{m(n-1)},\qquad
c=h^2t^2\alpha=\eta^2\alpha.
\]
The first-order LLC correction is exactly
\[
\boxed{
\mathcal C_1
=\frac{\eta t^2\alpha}{2}
\sum_i
\frac{\lambda_i\,\widehat{B(\Sigma^{mb})}_{ii}}
{p_i(2-\eta p_i/t)}.
}
\]

**If the anchored relation is \(p_i=t\lambda_i\)**, this simplifies to
\[
\boxed{
\mathcal C_1
=\frac{\eta t\alpha}{2}
\sum_i
\frac{\widehat{B(\Sigma^{mb})}_{ii}}
{2-\eta\lambda_i}.
}
\]
There is **no remaining \(1/\lambda_i\)** from the resolvent substitution alone. Such a factor would have to arise from an additional formula for \(B(\Sigma^{mb})\). Likewise, relating \(\alpha\) to \(m'\) requires the definition of \(m'\).

If, at fixed \(t\),
\[
\widehat{B(\Sigma^{mb}(\eta,t))}_{ii}\longrightarrow \beta_i(t),
\]
then
\[
\mathcal C_1
=\frac{\eta t\alpha}{4}\sum_i\beta_i(t)+o(\eta).
\]
Thus the correction is \(O(\eta)\) under boundedness assumptions. Its prefactor is explicitly linear in \(t\), but the **whole correction** is linear in \(t\) only if the remaining covariance/fluctuation factor is \(t\)-independent.

Also distinguish the expansions:

- At fixed \(A,B,N\): first order in \(c\), with \(O(c^2)\) remainder.
- Along anchored scaling: \(R\) typically grows like \(1/\eta\), so the corresponding hierarchy is \(O(\eta),O(\eta^2),\ldots\), under suitable uniform assumptions.

## 3. Suggested E8 wording

> At fixed Lyapunov dynamics and additive-noise covariance, the first-order Hessian-fluctuation correction to the LLC is
> \[
> \frac t2\,c\sum_i
> \frac{\lambda_i\,\widehat{B(\Sigma^{mb})}_{ii}}
> {hp_i(2-hp_i)}.
> \]
> It is a lower bound on the full correction, with a positive-semidefinite covariance remainder of order \(c^2\). Mode by mode, the one-step contribution is amplified by the geometric accumulation factor
> \[
> \frac1{1-\rho_i^2}=\sum_{k\ge0}\rho_i^{2k}.
> \]

I would **not** call this simply “the integrated autocorrelation time.” The usual two-sided IACT for a correlation sequence \(r^k\) is \((1+r)/(1-r)\), not \(1/(1-r)\). “Integrated variance-response factor” or “geometric accumulation factor” is precise here.

**Final vote:** prioritize **A → B → E**, retain **C–D** for quantitative control, add **(ii)** if cheap, reject unqualified **(i)**, and state the anchored \(O(\eta)\) conclusion with the covariance-scaling assumptions explicit.