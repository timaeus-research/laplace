**Vote: accept A–C, conditional on \(c\ge0\) and \(L<1\); revise D.** The main issue is that the contraction gap \(1-L\) generally shrinks like \(h\), so an \(O(h^2t^2/m)\) forcing does **not** generally give an \(O(h^2t^2/m)\) stationary-covariance correction.

Write
\[
T(X)=AXA^\top,\qquad B(X)=\sum_iD_iXD_i^\top,
\]
\[
a=\|A\|\|A^\top\|,\qquad
b=\sum_i\|D_i\|\|D_i^\top\|,\qquad L=a+cb,
\]
and put \(S=\Sigma^{mb}\), \(\Delta=\Sigma_{\rm full}-S\).

## 1. Candidates A–D

### A: correct

For the induced \(\ell^\infty\) matrix norm,
\[
|M_{ij}|\le\|M\|,\qquad
|\operatorname{tr}M|\le d\|M\|,
\]
and hence
\[
|\operatorname{tr}(HX)|\le d\|H\|\|X\|.
\]
Here “\(\ell^\infty\) operator norm” means maximum absolute row sum, not maximum absolute entry.

### B: correct

Subtracting the fixed-point equations gives
\[
\Delta=(T+cB)\Delta+cB(S).
\]
Consequently,
\[
\boxed{\quad
\|\Delta\|
\le \frac{c\|B(S)\|}{1-L}
\le \frac{cb\|S\|}{1-L}.
\quad}
\]
This also bounds every \(|\Delta_{ij}|\). It is precisely the Banach residual estimate.

PSD order does **not** imply entrywise nonnegativity, so the entrywise conclusion should retain absolute values.

### C: correct

Assuming the established lower bound applies—in particular, \(H\succeq0\)—one obtains
\[
c\,\operatorname{tr}(HB(S))
\le \operatorname{tr}(H\Delta)
\le \frac{d\|H\|c\|B(S)\|}{1-L}.
\]
Multiplication by \(t/2\) gives the stated LLC sandwich for \(t\ge0\).

### D: not as an unconditional scaling claim

The actual estimate is
\[
\|\Delta\|\le
h^2t^2\frac{1-m/n}{m(n-1)}
\frac{b\|S\|}{1-L}.
\]
An \(O(h^2t^2/m)\) conclusion needs uniform control of the remaining factors, especially \(1/(1-L)\). For fixed positive-definite \(P\), the usual small-\(h\) regime instead has
\[
1-L=\Theta(h).
\]
With bounded \(S\) and bounded normalized Hessian fluctuations, the resulting upper bound is typically
\[
\boxed{\|\Delta\|=O(ht^2/m),}
\]
with the finite-population factor retained as appropriate.

This loss of one power of \(h\) is real. In a scalar example with \(A=1-hp\), \(N=2h\), and \(cB(x)=h^2q\,x\),
\[
S=\frac{2}{2p-hp^2},\qquad
\Sigma_{\rm full}=\frac{2}{2p-h(p^2+q)},
\]
so
\[
\Delta=\frac{hq}{2p^2}+O(h^2).
\]

Thus D is defensible as a **fixed-gap perturbation statement**, or with \(h,t\) fixed and the asymptotic dependence only on minibatch size, but not generally as \(h\to0\).

## 2. Norm choice and change of frame

The \(\ell^\infty\) operator norm is entirely legitimate. State the theorem **conditionally on its specified \(L<1\)**.

For symmetric \(P\), an orthogonal eigenbasis makes
\[
A' = U^\top AU=\operatorname{diag}(1-hp_i),
\]
and hence
\[
\|A'\|_\infty\|(A')^\top\|_\infty
=\max_i|1-hp_i|^2<1
\]
when \(P\succ0\) and \(0<h<2/\lambda_{\max}(P)\).

Two caveats:

* This removes the **deterministic** norm obstruction, not necessarily the full-law obstruction: one still needs \(a'+cb'<1\).
* All coefficients must be conjugated, and the resulting bound is in the transformed-frame norm. Trace quantities are invariant under this orthogonal change; the \(\ell^\infty\) norm is not.

For exposition, the spectral/operator \(2\)-norm is cleaner and orthogonally invariant. For the existing formalization, conditional \(\ell^\infty\)-norm statements plus the frame-change remark are sound.

## 3. Cheaper or stronger alternatives

### (i) Trace-only bounds: valid, but they need trace control

For \(\Delta\succeq0\) and symmetric \(H\),
\[
\operatorname{tr}(H\Delta)
\le \lambda_{\max}(H)\operatorname{tr}\Delta
\le \|H\|_\infty\operatorname{tr}\Delta.
\]
So your proposed inequality is valid in the Hessian setting. Merely replacing \(\operatorname{tr}\Delta\) by \(d\|\Delta\|_\infty\), however, recovers the same dimensional factor.

A genuinely useful trace version follows if
\[
A^\top A+c\sum_iD_i^\top D_i\preceq \ell I,\qquad \ell<1.
\]
Taking traces of the equation for \(\Delta\) gives
\[
\operatorname{tr}\Delta
\le \frac{c\,\operatorname{tr}B(S)}{1-\ell},
\]
and therefore
\[
\operatorname{tr}(H\Delta)
\le
\frac{\lambda_{\max}(H)c\,\operatorname{tr}B(S)}{1-\ell}.
\]
This avoids an explicit \(d\), though it requires a different contraction certificate.

### (ii) First-order expansion: yes, and worth recording

Since \(a<1\), let \(R=(I-T)^{-1}\), with
\[
\|R\|\le\frac1{1-a}.
\]
Then exactly
\[
\boxed{\Delta=cR B(\Sigma_{\rm full}).}
\]
Subtracting the first-order term yields
\[
\Delta-cRB(S)=cRB(\Delta),
\]
so
\[
\boxed{
\|\Delta-cRB(S)\|
\le
\frac{c^2b\,\|B(S)\|}{(1-a)(1-L)}
\le
\frac{c^2b^2\|S\|}{(1-a)(1-L)}.
}
\]
This is \(O(c^2)\) **when the other parameters and contraction gaps are controlled**; it is not automatically a uniform joint small-\(h\) assertion.

Moreover, positivity gives the stronger lower bound
\[
\Delta\succeq cRB(S)\succeq cB(S).
\]
Thus the exact first-order term improves the one-step LLC lower bound as well.

### (iii) Relative estimate: yes, with the transpose caveat

For \(S\ne0\),
\[
\frac{\|\Delta\|}{\|S\|}
\le\frac{cb}{1-L}.
\]
In general retain \(\|D_i\|\|D_i^\top\|\). Here the \(D_i\) are symmetric Hessian deviations, so
\[
b=\sum_i\|D_i\|^2
\]
even for the \(\ell^\infty\) operator norm. Your relative statement is therefore correct in this setting.

## 4. Suggested E8 wording

> Under the sufficient contraction condition
> \[
> L=\|A\|\|A^\top\|+
> c\sum_i\|H_i-H\|\|(H_i-H)^\top\|<1,
> \]
> the Hessian-fluctuation correction to the stationary covariance is positive semidefinite and satisfies
> \[
> \|\Sigma_{\rm full}-\Sigma^{mb}\|
> \le
> \frac{c\|B(\Sigma^{mb})\|}{1-L}
> \le
> \frac{c\sum_i\|H_i-H\|^2\|\Sigma^{mb}\|}{1-L}.
> \]
> Its contribution to the quadratic LLC observable lies between the one-step lower bound and the corresponding trace-norm upper bound. The correction is first order in \(c\) at fixed contraction gap; because that gap typically scales as \(h\), the \(h^2t^2/m\)-scale covariance forcing typically produces an \(ht^2/m\)-scale stationary correction.

Keep the exact finite-population coefficient visible: in particular, \(m=n\) gives \(c=0\) and no correction.

Finally, **a covariance fixed point does not establish a Gaussian stationary law**. The quantity \((t/2)\operatorname{tr}(H\Sigma)\) is the quadratic expectation for any centered distribution with covariance \(\Sigma\); identifying an invariant law as Gaussian, or identifying this proxy with a broader LLC notion, requires separate justification.

**Priority vote:** formalize **A → B → C**, add the relative estimate cheaply, and pursue **(ii)** as the strongest natural refinement. Reject D’s current unqualified small-\(h\) wording.