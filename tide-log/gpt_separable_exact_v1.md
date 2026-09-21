**A and B are sound.** I would make general product-observable factorisation the core of A, derive B from it, and defer C unless the relevant integration-by-parts infrastructure is already available.

## 1. Correctness of A and B

### A: factorisation and covariance

Under the stated hypothesis-free theorem `integral_fintype_prod_volume_eq_prod`, the proposed integral identities are correct for Mathlib’s **total Bochner integrals**. The key identity is
\[
e^{-tL(w)}=\prod_i e^{-t\ell_i(w_i)}.
\]
For a coordinate observable, absorb the observable into the corresponding factor before applying the product-integral theorem.

The assumption
\[
\forall i,\quad 0<Z_i
\]
is sufficient for cancellation, hence for
\[
\langle\varphi(w_i)\rangle_L=\langle\varphi\rangle_{\ell_i}.
\]
It is also sufficient for the covariance identity:
\[
\operatorname{Cov}_L(w_i,w_j)=
\begin{cases}
\operatorname{Var}_{\ell_i}(x),&i=j,\\
0,&i\ne j.
\end{cases}
\]
For distinct indices, the product-moment numerator factorises, giving
\[
\langle w_iw_j\rangle_L
=\langle x\rangle_{\ell_i}\langle x\rangle_{\ell_j}.
\]
For equal indices, use coordinate factorisation for both \(x\) and \(x^2\).

Two qualifications:

* Algebraically, **\(Z_i\ne0\)** suffices; positivity is a convenient application-facing hypothesis.
* Without moment integrability, this is an identity between the **totalised definitions**, not necessarily a statement about a classically defined covariance. This distinction disappears in B, where polynomial moments are integrable.

No integrability hypothesis is needed for these particular factorisation identities. That does **not** extend to arbitrary uses of integral linearity, such as splitting the energy observable in C.

### B: the relative-rate conversion is correct

For \(\lambda>0\) and \(t\ne0\),
\[
t(\lambda tV(t)-1)
=\lambda\,t^2\left(V(t)-\frac1{\lambda t}\right).
\]
Thus the claimed limit is indeed
\[
\frac{\alpha^2}{\lambda^3}-\frac{\gamma}{2\lambda^2}.
\]
In Lean, establish the equality eventually at `atTop`, using eventual positivity of \(t\), and then multiply the existing limit by \(\lambda\).

With \(\alpha_i^2=a^2\lambda_i^3\) and \(\gamma_i=\lambda_i^2\), this becomes
\[
t\bigl(\lambda_i t\,\operatorname{Var}_L(w_i)-1\bigr)
\longrightarrow a^2-\frac12.
\]
The mean limit transfers directly by coordinate factorisation.

For \(Z_i>0\), the existing integrability theorem plus positivity of the exponential is enough. Continuity and positivity on a neighbourhood of zero provide a fallback if the support-based positivity theorem is inconvenient.

**One wording correction:** the theorem proves
\[
\lambda_i t\,\operatorname{Var}_L(w_i)
=1+\frac{a^2-\frac12}{t}+o(t^{-1}).
\]
This identifies the leading relative correction to the **Gaussian covariance**. It does not prove an \(O(t^{-2})\) relative remainder after including the one-loop correction. Also, “proportional to \(1/t\)” requires \(a^2\ne1/2\); at that exceptional value the relative correction is \(o(1/t)\).

## 2. C: valid, but it needs another ingredient

The LLC statement is correct. However, **one cannot simply differentiate a partition-function asymptotic**, even a second-order one, without additional control on the derivative.

There are three reasonable routes.

### Most direct analytically: rescaling and dominated convergence

Your discriminant condition gives the useful global bound
\[
\ell(x)
=x^2\left(\frac{\lambda}{2}+\frac{\alpha x}{6}
+\frac{\gamma x^2}{24}\right)
\ge c x^2,\qquad
c=\frac{\lambda}{2}-\frac{\alpha^2}{6\gamma}>0.
\]
After \(x=y/\sqrt t\),
\[
t\ell(y/\sqrt t)\longrightarrow \frac{\lambda y^2}{2}.
\]
Gaussian domination then proves the denominator and energy-numerator limits, yielding
\[
t\langle\ell\rangle_t\longrightarrow\frac12.
\]
Equivalently, establish the higher-moment bounds
\[
\langle |x|^p\rangle_t=O(t^{-p/2}),\qquad p=3,4,
\]
and combine them with the existing second-moment limit.

### Particularly close to the listed results: two integration-by-parts identities

If boundary/integration-by-parts lemmas are accessible, prove
\[
\langle\ell'(x)\rangle_t=0,\qquad
t\langle x\ell'(x)\rangle_t=1.
\]
Writing \(M_k=\langle x^k\rangle_t\), these say
\[
\lambda M_1+\frac{\alpha}{2}M_2+\frac{\gamma}{6}M_3=0,
\]
\[
t\left(\lambda M_2+\frac{\alpha}{2}M_3+\frac{\gamma}{6}M_4\right)=1.
\]
The existing limits for \(tM_1\) and \(tM_2\) first give \(tM_3\to0\), then \(tM_4\to0\). Consequently,
\[
t\langle\ell\rangle_t
=\frac{\lambda}{2}tM_2+\frac{\alpha}{6}tM_3
+\frac{\gamma}{24}tM_4\longrightarrow\frac12.
\]
This route uses exactly the existing mean and second-moment asymptotics, but adds two genuine analytic lemmas.

### Via log partition: possible with convexity

If \(Z(t)\sim C t^{-1/2}\), differentiability and convexity of \(\log Z\) allow a secant-slope argument at \(t/r,t,rt\), followed by \(r\downarrow1\). Together with
\[
-(\log Z)'(t)=\langle\ell\rangle_t,
\]
this yields the desired limit. The justification is **convexity**, not formal differentiation of an asymptotic expansion.

Once the one-dimensional result is proved, integrability and finite-sum linearity give
\[
\langle L\rangle_L=\sum_i\langle\ell_i\rangle_{\ell_i},
\qquad
t\langle L\rangle_L\longrightarrow \frac{\#\iota}{2}.
\]

So C is a good subsequent target, but it is less immediate than A–B.

## 3. Recommended scope and organisation of A

Yes: make the general product-observable theorem foundational:
\[
\int\left(\prod_i\varphi_i(w_i)\right)e^{-tL(w)}\,dw
=
\prod_i\int\varphi_i(x)e^{-t\ell_i(x)}\,dx,
\]
and, assuming nonzero coordinate partition functions,
\[
\left\langle\prod_i\varphi_i(w_i)\right\rangle_L
=
\prod_i\langle\varphi_i\rangle_{\ell_i}.
\]

Then derive:

1. partition-function factorisation;
2. coordinate expectations by setting spectator observables to \(1\);
3. distinct-coordinate product expectations;
4. covariance, by splitting on equality of indices.

Keep named coordinate and pair lemmas as convenient application-facing corollaries. For Lean, separate diagonal and off-diagonal covariance lemmas may also be easier to use than the combined `if` statement.

A useful, nearly free strengthening is
\[
\operatorname{Cov}_L(\varphi(w_i),\psi(w_j))
=
\begin{cases}
\operatorname{Cov}_{\ell_i}(\varphi,\psi),&i=j,\\
0,&i\ne j.
\end{cases}
\]
There is no need to introduce a full product-probability-measure construction for this tide.

**Vote: formalise A + B, with product-observable factorisation as A’s core. Defer C to a follow-up unless the required integration-by-parts lemmas are already close at hand.**