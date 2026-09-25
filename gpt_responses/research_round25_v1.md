## 1. The core object: a response geometry, with a distinguished radial direction

The most compelling formulation is not “a distance from featurelessness” alone. It is:

> **The data manifold, modulo posterior-invisible directions, carries the pullback of Fisher–Rao geometry under the response map. Loss-neutral data select a distinguished radial family whose geometry is controlled by the state density. Regular mean coordinates describe the interior; rescaled profile coordinates describe singular transitions.**

This unifies your four candidates, but assigns them different roles:

- **The response map and its pullback metric are the central object.**
- **Mean coordinates provide its regular atlas and convex duality.**
- **The temperature line is a distinguished radial probe**, not generally a shortest path.
- **The state density governs radial singularities.**
- **Wall profiles describe how these radial geometries change across strata.**

There are two important qualifications.

First, the law of \(L\) determines the partition function, loss statistics, and radial thermodynamic geometry—not arbitrary posterior expectations by itself. For a general observable \(\varphi\), one additionally needs its conditional mean given \(L\).

Second, with the normalization in the question,
\[
\ell=\int_0^1 t\sqrt{\operatorname{Var}_s(\Delta)}\,ds,
\]
the susceptibility identity gives
\[
\boxed{\ell^2\le t\bigl(\langle\Delta\rangle_0-\langle\Delta\rangle_1\bigr).}
\]
The displayed bound without \(t\) belongs to the metric \(t\operatorname{Cov}\), rather than \(t^2\operatorname{Cov}\). This is worth reconciling before building the global formulation.

---

## 2. A precise structural theorem list

### A. Response quotient and Fisher immersion

Let \(P_a\) be a finite-dimensional affine family at fixed \(t>0\), with bounded contrasts \(R_1,\dots,R_n\). Assume the base posterior is a probability measure equivalent to the reference measure on its support.

Then:

1. The posterior-invisible directions are exactly
   \[
   N=\{v:R_v\text{ is almost surely constant}\}.
   \]
2. They are independent of \(a\).
3. The response form
   \[
   G_a(v,w)=t^2\operatorname{Cov}_a(R_v,R_w)
   \]
   descends to a positive-definite metric on \(\mathbb R^n/N\).
4. The response map on this quotient is a Fisher–Rao immersion.

A particularly beautiful concrete realization is the square-root map
\[
\Psi(a)=2\sqrt{\frac{dP_a}{dP_0}}\in L^2(P_0).
\]
It lands on the sphere of radius \(2\), and
\[
D\Psi(a)[v]
   =-t\bigl(R_v-\langle R_v\rangle_a\bigr)
      \sqrt{\frac{dP_a}{dP_0}},
\]
hence
\[
\boxed{\langle D\Psi[v],D\Psi[w]\rangle_{L^2}=G_a(v,w).}
\]

This is the cleanest bridge between your covariance formalization and actual posterior geometry.

**A useful consequence:** thermodynamic length can diverge while ambient Fisher–Rao distance remains bounded:
\[
d_{\mathrm{FR}}(P,Q)
 =2\arccos\int\sqrt{dP\,dQ}\le \pi.
\]
Thus the \(\log t\) and \(\sqrt t\) laws measure the length of distinguished response paths, not necessarily endpoint distance in the full posterior space.

### B. Upgrade the local mean chart to a global convex chart

Your proposed open-embedding result is immediate conceptual closure:

> If the contrasts are nondegenerate, the mean map is a homeomorphism onto an open subset of \(\mathbb R^n\), and its inverse has derivative \((Dm)^{-1}\).

But bounded contrasts support a stronger theorem.

Let
\[
K=\overline{\operatorname{conv}}\bigl(\operatorname{ess\,range}_{P_0}R\bigr),
\]
and assume \(K\) has nonempty interior. Then
\[
\boxed{m:\mathbb R^n\longrightarrow\operatorname{int}K
       \text{ is a global diffeomorphism}.}
\]

Indeed, for \(x\in\operatorname{int}K\), minimize
\[
a\longmapsto A(a)+t\,a\cdot x,
\qquad
A(a)=\log\int e^{-t a\cdot R}\,dP_0.
\]
Interior membership gives coercivity; strict convexity gives uniqueness; the critical-point equation is \(m(a)=x\).

In mean coordinates, if \(C_a=\operatorname{Cov}_a(R,R)\), then
\[
\boxed{G^{\mathrm{mean}}_m(\delta m,\delta m)
       =\delta m^\top C_a^{-1}\delta m.}
\]
Notice that the explicit \(t^2\) disappears.

**Lean:** open embedding is very low cost given your current theorems. Surjectivity onto \(\operatorname{int}K\) is a separate, substantial convex-analysis theorem; do not make it a prerequisite for landing the open embedding.

### C. State-density reduction, including observables

Write \(\nu=L_*P_{\mathrm{prior}}\), after subtracting the essential minimum of \(L\). Then
\[
Z(u)=\int e^{-u\ell}\,d\nu(\ell),\qquad
\nu_u(d\ell)=Z(u)^{-1}e^{-u\ell}\nu(d\ell),
\]
and
\[
L_*P_u=\nu_u.
\]

For observables depending on the loss,
\[
\langle f(L)\rangle_u=\int f(\ell)\,d\nu_u(\ell).
\]

For general integrable \(\varphi\), the measurable-space-safe statement is
\[
\langle\varphi\rangle_u
 =\frac{\int e^{-u\ell}\,d[L_*(\varphi P_{\mathrm{prior}})](\ell)}
        {Z(u)}.
\]
When conditional expectations admit the appropriate representation, this becomes
\[
\langle\varphi\rangle_u
 =\int \mathbb E_{\mathrm{prior}}[\varphi\mid L=\ell]\,d\nu_u(\ell).
\]

This distinguishes **radial geometry** from **the full observable response** without losing either.

### D. Regular-variation theorem for radial susceptibility

A strong and clean theorem is:

> Let \(\nu\) be supported on \([0,\infty)\), with \(0<Z(u)<\infty\) for \(u>0\). If \(Z\) is regularly varying at infinity with index \(-\lambda\), \(\lambda>0\), then under \(\nu_u\),
> \[
> uL\Rightarrow\operatorname{Gamma}(\lambda,1),
> \]
> all fixed nonnegative integer moments converge, and
> \[
> \boxed{u^2\operatorname{Var}_{\nu_u}(L)\longrightarrow\lambda.}
> \]

**No derivative control is needed for this leading variance limit.**

The key identities are
\[
\mathbb E_u[e^{-s uL}]
 =\frac{Z((1+s)u)}{Z(u)}
 \longrightarrow(1+s)^{-\lambda},
\]
and, for \(0<\varepsilon<1\),
\[
\mathbb E_u[e^{\varepsilon uL}]
 =\frac{Z((1-\varepsilon)u)}{Z(u)}.
\]
The latter is uniformly bounded for sufficiently large \(u\), giving uniform integrability of every polynomial moment.

For a Lean implementation, a monotone-density/regular-variation route for the Laplace moments may be cheaper than weak convergence plus uniform integrability. The theorem above explains *why* derivative assumptions are unnecessary.

However,
\[
Z(u)\sim C u^{-\lambda}(\log u)^k
\]
alone does **not** justify differentiating its remainder to obtain the \(1/\log u\) correction. That requires quantitative second-order input, or direct moment estimates.

### E. Singular profiles are transition models, not yet ordinary atlas charts

Your wall charts are exact, temperature-dependent blow-up charts. They should initially be organized as a **rescaled response atlas**, with:

- regular charts inside chambers;
- profile charts in shrinking neighborhoods of walls;
- overlap/matching theorems between their asymptotic metrics.

Calling their union an ordinary manifold atlas would be premature: dimensions or ranks can change, and chart maps depend on \(t\). The deeper eventual object is a stratified or blown-up compactification, but the matching theorems should come first.

---

## 3. Multiplicity: the law is correct, and direct moments are the cleanest proof

Let
\[
d\nu(\ell)=C\,\ell^{\lambda-1}(-\log\ell)^k\,1_{(0,1)}\,d\ell,
\qquad \lambda>0,\quad k=m-1\in\mathbb N.
\]
The normalization \(C\) cancels from all posterior moments.

Then, for the exact density above,
\[
\boxed{
u^2\operatorname{Var}_u(L)
 =\lambda-\frac{k}{\log u}
       +O\!\left(\frac1{\log^2u}\right).
}
\]
Consequently,
\[
\boxed{
\ell(t)
 =\sqrt\lambda\log t
 -\frac{k}{2\sqrt\lambda}\log\log t
 +K+O\!\left(\frac1{\log t}\right).
}
\]
Here \(\ell(t)=\int_0^t\sqrt{\operatorname{Var}_u(L)}\,du\); any other fixed lower endpoint changes only \(K\).

Thus you obtain more than \(O(1)\): the centered length converges.

### The key moment calculation

Put \(T=\log u\) and
\[
J_j(u)=\int_0^u s^{\lambda+j-1}e^{-s}(T-\log s)^k\,ds.
\]
Then
\[
u^j\mathbb E_u[L^j]=\frac{J_j(u)}{J_0(u)}.
\]

For \(\alpha>0\), define
\[
b_\alpha
 =\frac1{\Gamma(\alpha)}
    \int_0^\infty s^{\alpha-1}e^{-s}\log s\,ds.
\]
Integration by parts gives the only special-function identity needed:
\[
b_{\alpha+1}=b_\alpha+\frac1\alpha.
\]

Binomial expansion and tail estimates give
\[
\frac{J_j(u)}{\Gamma(\lambda+j)T^k}
 =1-\frac{k b_{\lambda+j}}T+O(T^{-2}).
\]
Taking ratios,
\[
u\mathbb E_u[L]
 =\lambda-\frac{k}{T}+O(T^{-2}),
\]
\[
u^2\mathbb E_u[L^2]
 =\lambda(\lambda+1)-\frac{k(2\lambda+1)}T+O(T^{-2}).
\]
Subtracting the square of the first identity gives the variance law.

This route needs neither \(E_1\) nor derivatives of incomplete Gamma functions.

### One fully explicit remainder bound

The following is deliberately conservative, but has no hidden constants.

For integers \(r\ge1\), set
\[
H_{\alpha,r}=\frac{r!}{\alpha^{r+1}}+\Gamma(\alpha+r),
\]
so that
\[
\int_0^\infty s^{\alpha-1}e^{-s}|\log s|^r\,ds
 \le H_{\alpha,r}.
\]
Define
\[
E_\alpha=
 \frac{(1+k)H_{\alpha,2}
       +\displaystyle\sum_{r=2}^{k}\binom{k}{r}H_{\alpha,r}}
      {\Gamma(\alpha)}.
\]
For \(u\ge e\),
\[
\left|
\frac{J_j(u)}{\Gamma(\lambda+j)T^k}
 -1+\frac{k b_{\lambda+j}}T
\right|
\le \frac{E_{\lambda+j}}{T^2}.
\]

To turn this into an explicit variance bound, put
\[
B=\frac{kH_{\lambda,1}}{\Gamma(\lambda)},\qquad
T_0=\max\{1,4B,2\sqrt{E_\lambda}\},
\]
\[
d_1=-\frac{k}{\lambda},\qquad
d_2=-k\left(\frac1\lambda+\frac1{\lambda+1}\right),
\]
and
\[
D_j=2\left[
 E_{\lambda+j}+E_\lambda
 +|d_j|(B+E_\lambda)
\right],\qquad j=1,2.
\]
Then, for \(\log u\ge T_0\),
\[
\boxed{
\left|u^2\operatorname{Var}_u(L)
       -\lambda+\frac{k}{\log u}\right|
 \le \frac{C_{\lambda,k}}{\log^2u},
}
\]
where
\[
C_{\lambda,k}
=\lambda(\lambda+1)D_2+k^2
 +2(\lambda+k)\lambda D_1+(\lambda D_1)^2.
\]

The estimates behind this are elementary:

- on \((0,1)\), logarithmic moments are bounded by \(r!/\alpha^{r+1}\);
- on \((1,\infty)\), use \((\log s)^r\le s^r\);
- on the omitted tail \(s\ge u\), use \(\log s\ge T\);
- the denominator is at least \(1/2\) after normalization.

**Lean recommendation:** prove a reusable three-moment ratio lemma first. Then establish the \(J_j\) expansion. The case \(k=1\) is an excellent first landing, but arbitrary integer \(k\) is primarily a finite-sum generalization—not a new special-function project.

The square-root step is then routine:
\[
u\sqrt{\operatorname{Var}_u(L)}
 =\sqrt\lambda-\frac{k}{2\sqrt\lambda\,T}+O(T^{-2}).
\]
The remainder is integrable against \(du/u=dT\), proving convergence of the centered length.

---

## 4. The negative profile closes the wall-to-chamber picture

Let
\[
h(c)=\sqrt{\operatorname{Var}_c(y^q)},\qquad
dP_c(y)\propto e^{-y^p-cy^q}\,dy,\quad y>0,
\]
with \(0<q<p\).

### Exact two-sided window

Yes, state explicitly the corollary
\[
\boxed{
\ell_t(-c_-t^{-\sigma_*},c_+t^{-\sigma_*})
 =\int_{-c_-}^{c_+}h(c)\,dc.
}
\]
It costs almost nothing and makes clear that the wall chart crosses the phase boundary rather than merely approaching it.

### Negative-tail asymptotic

Write \(c=-b\), \(b\to\infty\). The minimum occurs at
\[
y_b=\left(\frac{qb}{p}\right)^{1/(p-q)},
\]
and
\[
V_b''(y_b)=p(p-q)y_b^{p-2}.
\]
Local Gaussian concentration gives
\[
\operatorname{Var}_{-b}(y^q)
 \sim\frac{q^2y_b^{2q-2}}{p(p-q)y_b^{p-2}}.
\]
Therefore
\[
\boxed{
h(-b)\sim K_{p,q}\,
 b^{\frac{2q-p}{2(p-q)}},
}
\]
where
\[
K_{p,q}
 =\frac{q}{\sqrt{p(p-q)}}
   \left(\frac qp\right)^{\frac{2q-p}{2(p-q)}}.
\]

Set
\[
\beta=\frac{p}{2(p-q)}>0.
\]
The exponent above is \(\beta-1>-1\), so
\[
\int_0^B h(-b)\,db
 \sim \frac{K_{p,q}}{\beta}B^\beta.
\]

Combining this with the exact scaling identity gives, for fixed \(A>0\),
\[
\boxed{
\frac{\ell_t(-A,0)}{\sqrt t}
 \longrightarrow
 K_-(A):=\frac{K_{p,q}}{\beta}A^\beta.
}
\]
The identity \(\sigma_*\beta=1/2\) explains the chamber scale.

This is more satisfying than proving the negative chamber independently: **the chamber law is the far-negative asymptote of the exact wall profile.**

**Lean route:** rescale \(y=b^{1/(p-q)}z\), obtaining a fixed potential
\[
z^p-z^q
\]
with large parameter \(b^{p/(p-q)}\). Its minimizer lies strictly inside the half-line. Localize around that minimizer, where real powers are smooth, and control the complement exponentially.

For the variance asymptotic, use centered moments or a Gaussian limit with moment bounds. Leading asymptotics of two uncentered moments alone will not survive their cancellation.

---

## 5. Geodesics and “distance from featurelessness”

### Mixture lines are exponential geodesics—not usually Fisher geodesics

An affine-loss line is a geodesic for the exponential connection of information geometry.

For ambient Fisher–Rao geometry there is a sharp characterization:

> A nonconstant affine-loss line is an unparameterized Fisher–Rao geodesic exactly when its contrast \(\Delta\) takes two essential values.

Indeed, under the square-root embedding,
\[
\psi'=-\frac t2(\Delta-\langle\Delta\rangle)\psi,
\]
and its sphere-covariant acceleration is proportional to
\[
\bigl((\Delta-\langle\Delta\rangle)^2
      -\operatorname{Var}(\Delta)\bigr)\psi.
\]
For this to be tangent to the curve, the centered contrast must satisfy a quadratic equation almost surely: its essential range has at most two points. Conversely, two-valued contrasts trace a great-circle arc.

This is a statement about **ambient** Fisher–Rao geodesics. Intrinsic geodesics of a response submanifold are a different question.

### The radial functional

Define
\[
D_t(L)=\int_0^t\sqrt{\operatorname{Var}_u(L)}\,du.
\]
The robust properties are:

- monotonicity in \(t\);
- invariance under adding constants to \(L\);
- positive scaling:
  \[
  D_t(aL+b)=D_{at}(L),\qquad a>0;
  \]
- invariance under replacing the model by its loss law;
- the multiplicity-sensitive asymptotics above.

There is also a useful genuine subadditivity theorem under independence. For a product prior and additive loss \(L=L_1+L_2\),
\[
\boxed{
\sqrt{D_t(L_1)^2+D_t(L_2)^2}
 \le D_t(L_1+L_2)
 \le D_t(L_1)+D_t(L_2).
}
\]
The pointwise variance adds, and the inequalities are integral norm inequalities. For \(n\) identical independent factors,
\[
D_t(L_1+\cdots+L_n)=\sqrt n\,D_t(L_1).
\]

For mixtures of data distributions on the **same** weight space, independence is absent and the tilting measure changes. No comparable mixture-convexity or subadditivity property should be assumed without a separate theorem.

I would call \(D_t\) **radial response length**, reserving “distance” for a genuine endpoint metric.

---

## 6. Ranked next plan: six items

| Rank | Target | Beauty/depth versus Lean cost |
|---|---|---|
| **1** | **Global open mean embedding**, including the quotient by constant contrasts | Very high return from the completed local layer. Land this now; treat the full \(\operatorname{int}K\) theorem as a later strengthening. |
| **2** | **State-density reduction**, then the regular-variation variance theorem | The reduction is cheap and reorganizes all radial results. The Tauberian theorem is deeper and more expensive, but removes artificial derivative hypotheses. |
| **3** | **Multiplicity-sensitive length**, first \(k=1\), then integer \(k\) | A genuinely new geometric detector of Watanabe multiplicity. Direct truncated moments give the best formalization path; avoid \(E_1\). |
| **4** | **Negative-profile matching theorem** \(h(-b)\sim Kb^{\beta-1}\) | Closes the wall picture and derives the negative chamber from one exact profile. Prefer this organization over an isolated chamber theorem. |
| **5** | **Square-root Fisher immersion and two-valued geodesic characterization** | Establishes the literal geometry and prevents confusion between path length and endpoint distance. Moderate \(L^2\)/manifold infrastructure cost. |
| **6** | **Radial functional laws and profile-overlap organization** | Scaling, independent-product inequalities, and the two-sided window are inexpensive. A full stratified atlas should wait for matching theorems and uniform estimates. |

**My strongest recommendation:** do not begin with uniform Laplace \(C\). First make the existing structure global and expose the one-dimensional radial reduction. Then land multiplicity and negative-profile matching.

The resulting synthesis would be exceptionally clean:

> **Mean coordinates identify the regular response space; state-density exponents measure radial depth; exact wall profiles explain how that depth reorganizes when the data cross singular strata.**