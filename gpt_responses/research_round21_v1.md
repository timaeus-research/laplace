## Overall assessment

The new results give you the **exact finite-parameter response calculus** and the **candidate limiting response calculus**. The main remaining mathematical gap is now sharply identifiable:

> Prove convergence of the score-weighted asymptotic integrals, not merely convergence of the unweighted measures.

That is the bridge I would prioritize. The `Phase` family work should be organized to supply its hypotheses.

My audit below is of the stated mathematical interfaces, rather than the unseen Lean implementations.

## 1. Audit of the new statements

### `TermScoreResponse`

The envelope
\[
|\phi|H(1+P)e^{-B(c/2)P}\in L^1(m)
\]
is a natural, robust sufficient hypothesis.

Indeed, writing
\[
U_{a+sv}=U_a+sR_v,
\]
boundedness of the \(h_i\), hence of \(R_v\), gives a neighborhood of \(s=0\) in which \(U_{a+sv}\ge c/2\). The original integrand and its derivative are then dominated by constant multiples of
\[
|\phi|He^{-B(c/2)P},
\qquad
|\phi|HPe^{-B(c/2)P}.
\]
So the \(1+P\) envelope packages exactly what differentiation under the integral needs.

Two qualifications:

* For the normalized theorem, you also need the corresponding hypothesis for \(\phi=1\), and a positive denominator.
* This is sufficient, not minimal: separate integrability hypotheses for the value and derivative would be weaker.

**Everywhere positivity is stronger than necessary.** The natural condition is
\[
U_a(\operatorname{face}(x))\ge c
\quad\text{for }m\text{-a.e. }x\text{ with }H(x)>0.
\]
The same applies to the bounds on the score direction. Positivity at irrelevant face points should not become an atlas obstruction.

I would retain the current easy-to-use theorem and add an **a.e.-on-the-active-support wrapper**. There is no need to redesign everything around topological support.

One additional scope condition matters: this score is complete only when \(H,P,B\), the domain, and the face map are parameter-independent. If any of those vary, their derivatives contribute additional score terms or boundary terms.

### `GammaFaceMarginal`

The gamma calculation is exactly right for \(\beta>0\), \(B>0\), \(U>0\). It is also the correct radial model whenever the limiting atlas term genuinely has the form
\[
w(u)z^{\beta-1}e^{-BU(u)z}\,d\nu(u)\,dz.
\]

But the important word is **whenever**: the gamma theorem does not itself establish that every atlas term has this form.

For example, a radial substitution \(z=r^\kappa\) gives
\[
r^{\gamma-1}\,dr=\frac1\kappa z^{\gamma/\kappa-1}\,dz.
\]
Thus \(\beta=\gamma/\kappa\), with the Jacobian constant absorbed into \(w\). More complicated monomial coordinates can leave angular variables, logarithmic factors, or residual cuts.

The bookkeeping rule is:

* A limiting cut or truth constraint depending only on \(u\) belongs in \(w(u)\), usually as an indicator.
* A constraint that disappears under scaling contributes nothing to the limiting domain, but that disappearance needs proof.
* A surviving constraint depending on \(z\) remains in the radial integral.

For instance,
\[
0<z<L(u)
\]
produces an incomplete gamma function, not \(\Gamma(\beta)\). A coupled indicator \(1_{\{Q(u,z)<1\}}\) cannot silently be absorbed into an angular weight.

So the next atlas audit should explicitly classify the **\(Q\)-monomial cut and truth constraint after scaling**. Pure gamma marginalization applies when the surviving domain is radially unrestricted, up to angular restrictions.

A useful interpretation already follows from your theorem:
\[
\mathbb E[S_v\mid u]=\beta\,\frac{R_v(u)}{U(u)}.
\]
Consequently, for observables depending only on \(u\), the full gamma-space covariance reduces to a face-space covariance with this conditional score. For observables depending on \(z\), that reduction is generally invalid.

### `AssembledResponse`

Yes: the scalar formula recovers the disjoint-union covariance, including the relative-mass response.

Set
\[
Z_k=\mu_k(X),\quad p_k=\frac{Z_k}{\sum_jZ_j},\quad
m_k=\mathbb E_k[\phi],\quad q_k=\mathbb E_k[S_k].
\]
Then
\[
\operatorname{Cov}_{\mathrm{union}}(\phi,S)
=
\sum_kp_k\operatorname{Cov}_k(\phi,S_k)
+
\operatorname{Cov}_{p}(m_k,q_k).
\]
The second term is exactly the relative-mass term, since
\[
D_vp_k=p_k\left(-q_k+\sum_jp_jq_j\right).
\]

The common base does not lose this information: the indexed sum retains the term label implicitly. What you should not do is identify the score on the unlabelled base with an arbitrary one of the \(S_k\).

The common-unit-family assumption is a convenience, not a mathematical necessity. The same quotient theorem works for term-specific unit families and scores.

### `MixtureSeries`

Fine, subject to the exponential-moment hypotheses actually proved in the file.

* Bounded \(\Delta\), together with integrability of the base weight, gives the clean global result.
* For unbounded \(\Delta\), all polynomial moments alone do **not** suffice; appropriate exponential integrability is needed.

A power-series identity with infinite radius gives an entire complex extension of the **unnormalized** coefficient. It does not make the normalized posterior entire: complex zeros of \(Z\) can create poles. Along the real line, positivity of \(Z\) gives real analyticity wherever the numerator and denominator are analytic.

---

## 2. The uniform asymptotic bridge

### The cleanest theorem is a four-integral theorem

Let
\[
d\rho_{t,a}=e^{-tL_a}\,d\pi,\qquad
Q_{t,v}=tD_vL_a.
\]
Allow \(\phi_t\) to be a pulled-back or scaled observable, provided it is parameter-independent for the differentiation under discussion.

Suppose there is a positive normalization \(A_t\) such that
\[
\begin{aligned}
A_t\int 1\,d\rho_{t,a}&\longrightarrow M_0>0,\\
A_t\int \phi_t\,d\rho_{t,a}&\longrightarrow M_\phi,\\
A_t\int Q_{t,v}\,d\rho_{t,a}&\longrightarrow M_S,\\
A_t\int \phi_tQ_{t,v}\,d\rho_{t,a}&\longrightarrow M_{\phi S}.
\end{aligned}
\]
If these four limits are the corresponding integrals against \(\mu_a\), with limiting score \(S_v\), then
\[
t\operatorname{Cov}_{t,a}(\phi_t,D_vL_a)
\longrightarrow
\operatorname{Cov}_{\bar\mu_a}(\phi_\infty,S_v).
\]

This is just quotient-limit algebra after the four substantive asymptotic statements. It requires neither an abstract derivative-interchange theorem nor uniformity in \(a\) for the pointwise conclusion.

**Make this the generic bridge interface.** A locally uniform version follows from locally uniform convergence of the four quantities, with the limiting mass bounded away from zero.

### What actually converges under scaling?

Use distinct notation for the physical loss direction and the face-unit direction:
\[
D_vL_a(w)=M(w)\,R_v^{\mathrm{unit}}(w).
\]
On a fixed monomialized stratum,
\[
tM(\Psi_t(x))\longrightarrow BP(x),
\qquad
R_v^{\mathrm{unit}}(\Psi_t(x))
\longrightarrow R_v^{\mathrm{unit}}(u_\infty(x)).
\]
Therefore
\[
tD_vL_a(\Psi_t(x))
\longrightarrow
BP(x)R_v^{\mathrm{unit}}(u_\infty(x)).
\]

It is **not generally**
\[
tR_v(u_\infty)+\cdots.
\]
The vanishing monomial factor is essential. The physical score direction and the unit score direction should probably have different names in Lean.

### Can the existing term theorems do it?

Yes, if they support triangular-array observables and the needed domination. Not simply because they accept a fixed bounded \(\phi\).

You need a lemma of the form:

> Rescaled kernels converge, rescaled scores converge, and their products with the observable have an integrable envelope; therefore the score-weighted term integrals converge.

Typically, the extra radial factor is absorbed using
\[
P e^{-cP}\le C e^{-(c/2)P}.
\]
That is precisely why your current score envelope is well aligned with the bridge.

### Minimal first instance

I would start with a **regular fixed-divisor model**
\[
L_a(w)=a w^p,\qquad a\in[a_-,a_+]\subset(0,\infty).
\]
Under \(y=t^{1/p}w\),
\[
tD_vL_a=v y^p,
\]
so the bridge is direct dominated convergence, uniformly in \(a\).

For a genuinely nontrivial assembled test, take **two labelled copies** with coefficients \(a_1,a_2\), and an observable distinguishing the copies. Their limiting masses are proportional to \(a_j^{-1/p}\). This tests the relative-mass term rather than merely a collapsing observable.

I would **not** use \(w^4+s w^2\) at \(s=0\) as the first ordinary bridge. That is a change of scaling stratum. With
\[
c=s\sqrt t,\qquad y=t^{1/4}w,
\]
the appropriate response identity is
\[
\partial_c\mathbb E[\psi(y)]
=
-\operatorname{Cov}(\psi(y),y^2),
\qquad
\partial_c=t^{-1/2}\partial_s.
\]
It is an excellent first **wall-response** theorem, but it requires a renormalized parameter derivative.

---

## 3. The `Phase` family

I recommend **a small affine-family abstraction, followed by a mixture constructor as its main producer**.

The essential family data are:

1. Fixed chart and monomial data.
2. Fixed amplitude/density data.
3. Units
   \[
   U_a(z)=\sum_i a_i h_i(z).
   \]
4. The phase identity for every admissible parameter.
5. Local uniform upper and positive lower bounds on \(U_a\).

This is the abstraction the response theorem actually consumes. It avoids making differentiation depend on the internal proof fields of individual `Phase` records.

Then add `Phase.mixture` under the stronger, concrete hypothesis that the component phases share the **same phase monomial factor**:
\[
f_i\circ\chi=Mh_i.
\]
You obtain
\[
\left(\sum_i a_if_i\right)\circ\chi=M\sum_i a_ih_i.
\]

### What can break?

**The common divisor is the main structural obstruction.**  
For \(w^4+s w^2\), factoring out \(w^2\) gives unit \(w^2+s\), which is not uniformly positive at \(s=0\). No record abstraction removes that genuine degeneration.

**`bounds`.**  
You need a locally uniform positive lower bound on the aggregate unit. It is not necessary to bound every mixture weight away from zero. For example, on the simplex, common component bounds
\[
0<c\le h_i\le C
\]
already imply \(c\le U_a\le C\), including at simplex boundary points. Local signed perturbations can also be allowed whenever aggregate positivity persists.

**`dens_eq`.**  
The phase identity is linear under the shared-factor hypothesis. The Jacobian/prior density is fixed chart data; it should not be added as though it were another phase component.

**\(B>0\).**  
If \(B\) comes from fixed scaling data, it should remain fixed. If \(B\) varies with \(a\), then the score gains the derivative of \(B\). Freeze the geometric normalization first.

Also distinguish two-sided ambient derivatives from feasible directional derivatives on a constrained weight simplex.

---

## 4. The general two-monomial wall

### First abstraction: the one-dimensional real-power model

Yes. It is the right first abstraction, and it can include uniform response immediately.

Define
\[
F(c)=\int_0^\infty e^{-y^p-cy^q}\,dy,\qquad p>q>0.
\]
Then
\[
Z(t,s)=t^{-1/p}F(st^{1-q/p})
\]
exactly, and
\[
F(0)=\Gamma(1+1/p),\qquad
c^{1/q}F(c)\longrightarrow\Gamma(1+1/q).
\]
Thus
\[
\lambda(\sigma)=\max\left(\frac1p,\frac{1-\sigma}{q}\right),
\qquad
\sigma_*=1-\frac qp.
\]

A valuable strengthening is
\[
F^{(n)}(c)=(-1)^n\int_0^\infty y^{nq}e^{-y^p-cy^q}\,dy,
\]
with uniform domination on compact \(c\)-sets in \([0,\infty)\).

For the cut domain \((0,1)\),
\[
t^{1/p}Z(t,ct^{-\sigma_*})
=
\int_0^{t^{1/p}}e^{-y^p-cy^q}\,dy.
\]
The omitted tail vanishes uniformly for \(c\ge0\), also for each fixed derivative order. **This cut does not generate a second crossover.**

### The multidimensional chart is substantially deeper

For
\[
\int_{(0,1)^d}x^{b-1}
e^{-t x^\alpha-t^{1-\sigma}x^{\alpha'}}\,dx,
\]
the exponent is governed by
\[
\lambda(\sigma)=
\min\left\{
b\cdot r:
r\ge0,\quad
\alpha\cdot r\ge1,\quad
\alpha'\cdot r\ge1-\sigma
\right\}.
\]
Under the usual positive monomial hypotheses, the dimension of the minimizing face controls the logarithmic multiplicity. This introduces polyhedral walls, logarithmic normalization, and potentially several scaling charts.

The cube cut appears as \(r\ge0\); it is genuine asymptotic geometry, not always a negligible tail.

Your second crossover is an excellent concrete illustration:
\[
Z(t,s)=\int_0^1\int_0^1e^{-tx(y+s)}\,dx\,dy.
\]
Here
\[
tZ(t,s)
=
\log\frac{1+s}{s}
-E_1(ts)+E_1(t(1+s)),
\]
so \(s=c/t\) gives
\[
tZ(t,c/t)-\log t\longrightarrow-\log c-E_1(c).
\]
This is a two-monomial cube-chart phenomenon involving a logarithmic channel. It is not the generic effect of merely having a finite cut.

So: **prove the one-dimensional uniform profile first; use the logarithmic example as the second abstract template; only then generalize to polyhedral charts.**

---

## 5. Ranked next five packages

| Rank | Package | Principal deliverable |
|---|---|---|
| **1** | **Score-weighted asymptotic bridge** | Four-integral covariance bridge; rescaled score domination lemma; one regular model and a two-term relative-mass test. |
| **2** | **Affine phase families and atlas instantiation** | Fixed-chart affine units, local uniform bounds, `Phase.mixture`, and one actual atlas `ScoreData` instance. |
| **3** | **Uniform one-dimensional wall profiles and response** | Real \(p>q>0\), compact-uniform profile derivatives, cut-domain convergence, correctly scaled wall response. |
| **4** | **Normalized cumulant response** | For affine \(L_s\), \(D_s^n\langle\phi\rangle=(-t)^n\kappa(\phi,\Delta,\ldots,\Delta)\), with \(n\) copies of \(\Delta\). |
| **5** | **Thermodynamic-length asymptotics** | Score-variance asymptotics and an integrable pathwise envelope, including treatment of degenerating endpoints. |

For the fifth item, keep two regimes separate:
\[
g_t=t^2\operatorname{Var}_t(D_sL).
\]
A tight limiting rescaled score can give \(g_t=O(1)\); a moving-minimizer regime can give \(g_t\sim t\,g_\infty\), hence length of order \(\sqrt t\). The latter is not a universal consequence of the singular response theorem.

### Single most valuable theorem now

> **Locally uniform convergence of assembled score-weighted asymptotics implies locally uniform convergence of posterior directional derivatives to the limiting disjoint-union covariance.**

Make its abstract hypothesis the four normalized integrals, and its atlas-facing hypothesis a rescaled-score domination condition. That theorem connects the two response layers without obscuring the exact additional analytic work required.