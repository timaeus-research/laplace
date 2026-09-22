## 1. Correctness of A and B, and necessary corrections

**A and B are correct under the existing oscillator integrability/coercivity hypotheses, with parameters and probes fixed as \(t\) varies.** There are a few important qualifications.

### A: derivative and quotient-rule algebra

Put \(V=L\circ A\), and write
\[
N(s)=\langle\psi\Phi\rangle_s,\qquad D(s)=\langle\Phi\rangle_s,
\]
where these expectations use the **fixed** potential \(V\). Then
\[
N'(t)=-\operatorname{Cov}_t[V,\psi\Phi],
\qquad
D'(t)=-\operatorname{Cov}_t[V,\Phi].
\]
Consequently,
\[
\begin{aligned}
\left(\frac ND\right)'(t)
&=\frac{-\operatorname{Cov}[V,\psi\Phi]D
             +N\operatorname{Cov}[V,\Phi]}{D^2}\\
&=-\left(
 \frac{\langle V\psi\Phi\rangle}{D}
 -\frac{\langle V\Phi\rangle}{D}
  \frac{\langle\psi\Phi\rangle}{D}
 \right)\\
&=-\operatorname{Cov}_{\mathrm{loc},t}[V,\psi].
\end{aligned}
\]
The signs and cancellation are right. In particular, the covariance is with \(V\), **not with the \(t\)-dependent localised potential**.

Required details:

* The ratio representation need only hold **eventually near \(t>0\)**. No identity at \(s=0\) is required.
* Prove \(D(t)>0\), using positivity of \(\Phi\), finiteness of the weighted integral, positivity of the base partition function, and a nonzero underlying measure.
* The bound \(0<\Phi\le1\) uses \(g\ge0\).
* All parameters, including \(g,w_0,c,B,b\), must be fixed. A varying probe contributes \(\langle\partial_t\psi_t\rangle_{\rm loc}\).
* The fixed potential must satisfy the seabed derivative lemma’s hypotheses. Do not silently infer \(L\ge0\) from quartic coercivity alone.

**One displayed asymptotic claim needs correction:**
\[
-\partial_t\frac{a}{t\lambda+g}
=\frac{a\lambda}{(t\lambda+g)^2}\longrightarrow0,
\]
whereas
\[
t^2\left(-\partial_t\frac{a}{t\lambda+g}\right)
\longrightarrow\frac a\lambda.
\]
This is the **anchor contribution**, not the full anharmonic mean coefficient.

### B: Stein identity and recursion

For
\[
\ell(x)=\frac{\lambda}{2}x^2+\frac{\alpha}{6}x^3+\frac{\gamma}{24}x^4,
\qquad
\phi(x)=e^{ax-gx^2/2},
\]
the proposed identity is exactly
\[
\boxed{\quad
\langle f'\rangle_{\rm loc}
=\langle f(t\ell'+gx-a)\rangle_{\rm loc}.
\quad}
\]
Applying the base Stein identity to \(f\phi\) proves it, provided its differentiability and three required integrability hypotheses are discharged.

Thus, for \(k\ge1\),
\[
\boxed{\quad
(t\lambda+g)m_{k+1}
+\frac{t\alpha}{2}m_{k+2}
+\frac{t\gamma}{6}m_{k+3}
=k\,m_{k-1}+a\,m_k.
\quad}
\]
At \(k=0\), use a separate statement:
\[
\boxed{\quad
(t\lambda+g)m_1+\frac{t\alpha}{2}m_2
+\frac{t\gamma}{6}m_3=a.
\quad}
\]
There is no need to introduce \(m_{-1}\). With natural-number indexing, Lean’s truncated subtraction can support a uniform formula, but a separate zero lemma is clearer.

**Distinguish \(\phi\) from \(\Phi\):** generally \(\phi\not\le1\). With \(a=gx_0\),
\[
\phi(x)=e^{gx_0^2/2}e^{-g(x-x_0)^2/2}
\le e^{gx_0^2/2}.
\]
This constant bound suffices; alternatively use the centred localiser throughout. Polynomial factors in \((f\phi)'\) and \(f\phi\ell'\) still require the corresponding polynomial-weight integrability.

C is a valid rearrangement when \(t\lambda+g\ne0\), in particular when \(t,\lambda>0\) and \(g\ge0\). Its asymptotic interpretation additionally needs the known moment limits.

## 2. Recommended proof route and Lean pitfalls

**Use the fixed-potential ratio route for this tide.** It matches the available API and avoids a substantially more general dominated-differentiation theorem.

The general formula is indeed
\[
\frac d{dt}\langle\psi\rangle_{U_t,t}
=-\operatorname{Cov}_{U_t,t}
 \bigl[\psi,U_t+t\,\partial_tU_t\bigr]
\]
for a fixed probe, under suitable differentiation-under-the-integral hypotheses. Here
\[
U_t=V+\frac{g}{2t}|w-w_0|^2
\quad\Longrightarrow\quad
U_t+t\partial_tU_t=V.
\]
This explains A conceptually, but it is unnecessary infrastructure for proving A.

I would structure the Lean proof as follows:

1. Establish a reusable weighted-expectation derivative lemma for
   \[
   s\longmapsto
   \frac{\operatorname{gibbsExpectation}(V,s,\psi\Phi)}
        {\operatorname{gibbsExpectation}(V,s,\Phi)}.
   \]
2. Prove denominator positivity and the relevant ratio identities.
3. Apply `HasDerivAt.div`.
4. Rewrite the result as the localised covariance, explicitly supplying nonzero denominators before `field_simp`/`ring`.
5. Transfer the derivative using eventual equality on a neighbourhood contained in \(s>0\).

The quotient rule requires the denominator to be nonzero **at \(t\)**; its continuity then handles nearby behaviour. A global nonvanishing theorem is useful but not required by that step.

The separable frame is a sensible place to discharge integrability. The algebraic ratio-derivative lemma itself need not be frame-specific. For rotation transport, remember to rotate the anchor as well:
\[
|w-w_0|^2=|Aw-Aw_0|^2
\]
for orthogonal \(A\).

## 3. What this buys for E3, and the localised covariance reduction

### Exact derivative interpretation

The reading is fair **when stated for exact-measure quantities and the matching fixed probes**:
\[
-\partial_t\langle u_i\rangle_{\rm loc}
=\operatorname{Cov}_{\rm loc}[V,u_i],
\]
and
\[
-\partial_t\langle u_i u_j\rangle_{\rm loc}
=\operatorname{Cov}_{\rm loc}[V,u_i u_j].
\]
The anchor contribution is automatically included.

There are two distinctions worth preserving:

* This does **not** identify derivatives of finite asymptotic truncations with exact covariances, nor justify differentiating uncontrolled remainders.
* If “eq:cov” means the **central covariance**, rather than the raw second moment, then
  \[
  -\partial_t\operatorname{Cov}_{\rm loc}(u_i,u_j)
  =
  \operatorname{Cov}_{\rm loc}
  \!\left[V,(u_i-\mu_i)(u_j-\mu_j)\right],
  \qquad \mu_i=\langle u_i\rangle_{\rm loc}.
  \]
  It is not simply \(\operatorname{Cov}_{\rm loc}[V,u_i u_j]\).

Thus the asserted §68 interpretation is justified for its corresponding exact expectation identity, with this raw-versus-central distinction respected.

### Exact localised Stein–covariance reduction

**Yes: add this identity.** Write
\[
C_{r,n}=\operatorname{Cov}_{\rm loc}[x^r,x^n].
\]
Stein applied to \(x^{n+1}\), minus \(m_n\) times Stein applied to \(x\), gives
\[
n m_n
=t\,\operatorname{Cov}_{\rm loc}[x\ell',x^n]
 +gC_{2,n}-aC_{1,n}.
\]
Since
\[
x\ell'=2\ell+\frac{\alpha}{6}x^3+\frac{\gamma}{12}x^4,
\]
we obtain
\[
\boxed{
\begin{aligned}
t^2\operatorname{Cov}_{\rm loc}[\ell,x^n]
={}&\frac n2\,t\,m_n
-\frac{\alpha}{12}t^2C_{3,n}
-\frac{\gamma}{24}t^2C_{4,n}\\
&-\frac g2\,t\,C_{2,n}
+\frac a2\,t\,C_{1,n}.
\end{aligned}}
\]
The two new terms have signs **\(-g/2\)** and **\(+a/2\)**. At \(n=0\), both sides vanish.

More generally, whenever the required Stein and integrability hypotheses hold,
\[
\boxed{
\begin{aligned}
t^2\operatorname{Cov}_{\rm loc}[\ell,f]
={}&\frac t2\langle xf'\rangle_{\rm loc}
-\frac{\alpha}{12}t^2\operatorname{Cov}_{\rm loc}[x^3,f]
-\frac{\gamma}{24}t^2\operatorname{Cov}_{\rm loc}[x^4,f]\\
&-\frac g2t\operatorname{Cov}_{\rm loc}[x^2,f]
+\frac a2t\operatorname{Cov}_{\rm loc}[x,f].
\end{aligned}}
\]

### Moment inputs for the \(1/t\) covariance coefficients

For \(n=1,2\), a sufficient, fairly economical input package is
\[
\begin{aligned}
m_1&=A_1t^{-1}+B_1t^{-2}+o(t^{-2}),\\
m_2&=A_2t^{-1}+B_2t^{-2}+o(t^{-2}),\\
m_3&=A_3t^{-2}+o(t^{-2}),\\
m_4&=A_4t^{-2}+B_4t^{-3}+o(t^{-3}),\\
m_5&=A_5t^{-3}+o(t^{-3}),\\
m_6&=A_6t^{-3}+o(t^{-3}).
\end{aligned}
\]
Indeed:

* the \(t^2C_{3,n}\) and \(t^2C_{4,n}\) terms require the relevant covariance expansions through \(t^{-3}\);
* the \(tC_{2,n}\) and \(tC_{1,n}\) terms require them through \(t^{-2}\);
* \(tm_n\) requires \(m_n\) through \(t^{-2}\).

The especially easy-to-miss input is **the \(t^{-3}\) correction to \(m_4\)** for \(n=1\). Knowing only \(m_1,m_2\) to second order is not sufficient.

With these moment coefficients identified, the reduction gives
\[
t^2\operatorname{Cov}_{\rm loc}[\ell,x^n]
=A_n+\frac{2B_n}{t}+o(t^{-1}),
\qquad n=1,2,
\]
by finite algebra and remainder estimates—not by differentiating the moment remainders. Thus it is a concrete route to the proposed \(2c'\), \(2c_2'\), provided those symbols denote the corresponding second-order moment coefficients. If \(c_2'\) instead denotes a central-variance coefficient, include the mean-product correction.

For the separable multidimensional measure, independence and product identities handle cross-coordinate probes; rotation then transports the result. A supplies the exact derivative interpretation, while **B plus the reduction supplies the remainder-safe asymptotic proof**.

## 4. Bundle recommendation

Back **A + B**, keep C as a remark or cheap rearrangement, and add the power-form Stein–covariance reduction now. It is a short algebraic consequence of B and makes the connection to deferred D explicit. The full second-order asymptotic theorem can remain deferred if the higher-moment inputs are not yet available.

**Vote: A + B + the exact localised Stein–covariance reduction; C as a remark, with no general \(t\)-dependent-potential derivative theorem this tide.**