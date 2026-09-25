The bounded case is now structurally complete. I would shift the centre of gravity to **entropy minimisation and the exact geometry of the non-steep image**, rather than immediately to a general large-deviation theorem.

Two corrections are important:

1. **The gamma boundary means are interior points of the moment body**, not boundary points of its closed convex hull. They are boundary points of the **mean image of the open natural-parameter domain**.
2. In mean coordinates, the observable-response integrand needs an **inverse covariance**. It is not generally `Cov(φ, R_{ṁ})` when `ṁ` denotes the mean-coordinate velocity.

## 1. Revised ranking

| Rank | Target | Reason |
|---|---|---|
| **1** | **Legendre identity + constrained relative-entropy minimisation** | Cheap after `DualPotential`; gives the cleanest interpretation of what the response manifold actually parametrises. |
| **2** | **The wall mean band, including the chamber curve** | The main new geometry beyond the completed bounded theory: a nonconvex mean image strictly inside the moment body. |
| **3** | **Temperature-slice variational principle and reduced potential** | Turns “slices are graphs” into constrained thermodynamics, with a particularly beautiful residual-variance identity. |
| **4** | **A scoped non-steep boundary-extension theorem** | Generalise exactly the mechanism used by the wall. Defer an omnibus “iff steep” theorem. |
| **5** | **`N^⊥` / affine-hull reduction** | Removes the remaining artificial minimality hypothesis and replaces interior by relative interior. Useful also when `L₀` is dependent on the contrasts. |
| **6** | **Two-term wall law** | Valuable quantitative refinement, but less structural than the band and variational picture. |
| **7** | **Mean-segment observable transport** | A short, attractive corollary; worth landing opportunistically rather than making it a major project. |
| **8** | **Full finite-dimensional Cramér theorem** | Mathematically natural, but not a cheap consequence of the existing differential geometry. It brings substantial probability infrastructure. |

### My choice for the most beautiful missing statement

For a probability prior \(P_0\), write
\[
dP_\theta=e^{-\langle\theta,S\rangle-\psi(\theta)}\,dP_0,
\qquad m=\mathbb E_{P_\theta}S.
\]
Then, for every probability \(Q\) with the same statistic mean and appropriate finite integrability,
\[
\boxed{
D(Q\Vert P_0)
=
I(m)+D(Q\Vert P_\theta).
}
\]

Consequently,
\[
\boxed{
I(m)=\min_{\mathbb E_QS=m}D(Q\Vert P_0),
}
\]
with unique minimiser \(P_\theta\).

This extends your family-internal Pythagoras theorem to **all admissible distributions**, not merely other members of the family. It says that the chart assigns to each response the least-informative distribution realising that response.

For a clean first formal statement, assume:

- \(P_0,Q\) are probability measures;
- \(Q\ll P_0\);
- \(D(Q\Vert P_0)<\infty\);
- each component of \(S\) is \(Q\)-integrable;
- \(\mathbb E_QS=m(\theta)\).

In the bounded setting the statistic-integrability conditions disappear. The proof is the log-density identity integrated against \(Q\), followed by nonnegativity of KL. This is not yet Cramér’s theorem, but it identifies exactly the same candidate rate function.

**Normalisation warning:** if \(\psi\) is the raw log partition of a finite, unnormalised prior, the rate/entropy potential is
\[
-\langle\theta,m\rangle-\psi(\theta)+\psi(0).
\]
Bregman identities do not detect this additive constant; rate-function statements do.

---

## 2. The wall: correct moment-body geometry

Let \(p>q>0\), \(r=p/q>1\), and
\[
dP_{\alpha,\beta}(x)
=
Z(\alpha,\beta)^{-1}e^{-\alpha x^p-\beta x^q}\,dx.
\]
Put
\[
u=\mathbb E x^p,\qquad v=\mathbb E x^q.
\]

The full finite-partition domain is
\[
D=\{(\alpha,\beta):\alpha>0\}
 \ \cup\ \{(0,\beta):\beta>0\}.
\]
Its interior is just \(\alpha>0\), with unrestricted \(\beta\).

### Moment body

The statistic curve is \((z^r,z)\), \(z>0\). Its closed convex hull is
\[
\boxed{
C=\{(u,v):v\ge0,\ u\ge v^r\}.
}
\]
In particular,
\[
\operatorname{int}C=\{(u,v):v>0,\ u>v^r\}.
\]

The vertical half-line at \(v=0\) really does occur in the **closure** of the convex hull: very small mass at a very large \(z\) can retain a positive \(r\)-th moment while its first moment tends to zero.

### Mean image

Define
\[
C_\Gamma
=
\frac{\Gamma((p+1)/q)\,\Gamma(1/q)^{r-1}}
     {\Gamma((q+1)/q)^r}.
\]
Then the desired distinction is
\[
\boxed{
m(\operatorname{int}D)
=
\{(u,v):v>0,\ v^r<u<C_\Gamma v^r\},
}
\]
whereas
\[
\boxed{
m(D)
=
\{(u,v):v>0,\ v^r<u\le C_\Gamma v^r\}.
}
\]

Thus:

- the lower curve \(u=v^r\) is a moment-body boundary and is not attained;
- the gamma curve \(u=C_\Gamma v^r\) is attained at finite boundary parameters;
- that gamma curve lies **strictly inside the moment body**;
- the open family misses the whole region \(u\ge C_\Gamma v^r\), not merely a curve;
- allowing finite-partition boundary parameters adds the curve, but not the region above it.

Moreover,
\[
\overline{\operatorname{conv}(m(\operatorname{int}D))}=C.
\]
So the proposed claim that gamma means are not interior points of the closed convex hull of the mean range goes in exactly the wrong direction.

### Chamber curve

If “chambers” refers to the sign of \(\beta\), the separating curve is \(\beta=0\):
\[
u=C_pv^r,\qquad
C_p=
\frac{\Gamma((p+1)/p)\,\Gamma(1/p)^{r-1}}
     {\Gamma((q+1)/p)^r}.
\]
One obtains
\[
1<C_p<C_\Gamma,
\]
and
\[
\begin{array}{c|c}
\beta<0 & v^r<u<C_pv^r\\
\beta=0 & u=C_pv^r\\
\beta>0,\ \alpha>0 & C_pv^r<u<C_\Gamma v^r.
\end{array}
\]

The two constant inequalities can be proved geometrically from strict monotonicity, without a separate gamma-function inequality project.

---

## 3. A general theorem that actually yields the band

The assumptions “continuous, \(0\le g\le f\), growth-ordered” are insufficient.

They do not guarantee:

- a prescribed moment body;
- existence of every fixed-\(g\)-mean fibre;
- finite means at the natural-domain boundary;
- a one-dimensional lower envelope;
- the required endpoint limits.

Also, \(x^q\le x^p\) fails near zero when \(p>q\). The relevant condition is eventual growth domination, not global ordering.

### Recommended structural setting

Change variables conceptually to
\[
z=g(x),\qquad f(x)=F(g(x)).
\]
Work directly with a positive Borel measure \(\rho\) on \((0,\infty)\):
\[
dP_{\alpha,\beta}(z)
=
Z(\alpha,\beta)^{-1}e^{-\alpha F(z)-\beta z}\,d\rho(z).
\]

Assume:

1. **Full support and local finiteness:** \(\rho\) is locally finite and every nonempty open interval has positive mass.
2. **Strictly convex lower envelope:** \(F:(0,\infty)\to[0,\infty)\) is continuous and strictly convex.
3. **Interior exponential integrability:** for every \(\alpha>0,\beta\in\mathbb R\),
   \[
   \int (1+F^2+z^2)e^{-\alpha F-\beta z}\,d\rho<\infty.
   \]
4. **Boundary exponential integrability:** for every \(\beta>0\),
   \[
   \int (1+F^2+z^2)e^{-\beta z}\,d\rho<\infty.
   \]
5. **Boundary mean coverage:** under \(P_{0,\beta}\),
   \[
   \mathbb E z\longrightarrow0\quad(\beta\to\infty),
   \qquad
   \mathbb E z\longrightarrow\infty\quad(\beta\downarrow0).
   \]

For formalisation, I would initially package the differentiability and fixed-\(\alpha\) mean-coverage conclusions as explicit hypotheses, then discharge them in a separate exponential-integrability module. This avoids burying the geometric theorem under domination arguments.

The monomial instance uses
\[
F(z)=z^r,\qquad
d\rho(z)=\frac1q z^{1/q-1}\,dz.
\]

### Fixed-mean parameterisation

For each \(\alpha\ge0\) and \(v>0\), let \(\beta(\alpha,v)\) be the unique solution of
\[
\mathbb E_{\alpha,\beta}z=v,
\]
where \(\beta(0,v)>0\).

Set
\[
U(\alpha,v)=\mathbb E_{\alpha,\beta(\alpha,v)}F(z),
\qquad
H(v)=U(0,v).
\]

The general conclusion is
\[
\boxed{
\{(\mathbb EF,\mathbb Ez):\alpha>0\}
=
\{(u,v):v>0,\ F(v)<u<H(v)\},
}
\]
and adjoining the boundary family changes \(u<H(v)\) to \(u\le H(v)\).

### Proof, in formaliser-sized pieces

#### A. Solve each mean fibre

At fixed \(\alpha>0\),
\[
\partial_\beta\mathbb Ez=-\operatorname{Var}(z)<0.
\]

The endpoint limits
\[
\mathbb Ez\to0\quad(\beta\to+\infty),
\qquad
\mathbb Ez\to\infty\quad(\beta\to-\infty)
\]
follow from full support and exponential integrability. A useful proof is to apply secant inequalities to the convex scalar log partition, using positive mass in intervals near any chosen support point.

This gives existence, uniqueness and continuity of \(\beta(\alpha,v)\).

#### B. Differentiate along the fibre

Implicit differentiation yields
\[
\partial_\alpha\beta(\alpha,v)
=
-\frac{\operatorname{Cov}(F,z)}{\operatorname{Var}(z)}.
\]
Hence
\[
\boxed{
\partial_\alpha U
=
-\operatorname{Var}(F)
+\frac{\operatorname{Cov}(F,z)^2}{\operatorname{Var}(z)}
<0.
}
\]

Strictness is the positive covariance determinant. Equality would make \(F(z)\) affine in \(z\) almost surely; full support, continuity and strict convexity exclude that.

This is the central band lemma. It is a **Schur complement**, not a Laplace asymptotic.

If \(F\) is also strictly increasing, then \(\operatorname{Cov}(F,z)>0\), so \(\beta(\alpha,v)\) is strictly decreasing. That additional hypothesis gives the simple chamber ordering.

#### C. The boundary endpoint

Prove
\[
\beta(\alpha,v)\to\beta(0,v),\qquad
U(\alpha,v)\to H(v)
\quad(\alpha\downarrow0).
\]

A Lean-friendly route avoids a one-sided implicit-function theorem:

1. bracket \(\beta(0,v)\) by two positive values;
2. use dominated convergence at those two values;
3. use monotonicity to trap \(\beta(\alpha,v)\);
4. pass the moments to the limit under a common integrable bound.

The boundary exponential-moment assumptions provide the domination.

#### D. The concentrated endpoint — without Laplace asymptotics

The elegant target is
\[
U(\alpha,v)\longrightarrow F(v)\quad(\alpha\to\infty).
\]

Jensen gives the lower bound. For the upper bound, use the boundary probability
\[
Q_0=P_{0,\beta(0,v)}
\]
as reference.

For any probability \(Q\) with \(\mathbb E_Qz=v\), finite \(D(Q\Vert Q_0)\), and finite \(\mathbb E_QF\), the Gibbs variational inequality gives
\[
U(\alpha,v)
\le
\mathbb E_QF+\frac{D(Q\Vert Q_0)}{\alpha}.
\]

Construct such \(Q\) concentrated in two small intervals, one on each side of \(v\), with their mixture weights chosen to give mean exactly \(v\). Then
\[
\mathbb E_QF\to F(v).
\]
First let \(\alpha\to\infty\), then shrink the intervals.

This proves the endpoint using entropy and continuity alone. **No quadratic expansion, moving-minimum theorem, or two-term Laplace estimate is required.**

If this is the only use, package the two-interval construction as an “approximately optimal mean-constrained competitor” lemma.

#### E. Obtain the band by the intermediate value theorem

For fixed \(v\), \(U(\cdot,v)\) is continuous and strictly decreasing, with endpoints \(H(v)\) and \(F(v)\). Surjectivity onto the interval is now purely one-dimensional.

### What is genuinely Laplace-asymptotic?

Not the exact band, its boundary extension, or its chamber decomposition.

Laplace machinery enters for:

- rates of approach to \(F(v)\);
- asymptotics of \(\beta(\alpha,v)\);
- Gaussian fluctuation limits;
- first and second correction terms;
- uniformity as \(v\) varies or approaches an endpoint.

That is a good reason to land the band **before** the two-term wall law.

---

## 4. What to formalise about non-steepness

I would not start with the broad iff statement.

A clean general boundary theorem is:

> Let \(D^\circ\) be the open natural domain of a minimal finite-dimensional exponential family. Suppose \(\theta_n\in D^\circ\) tends to a finite boundary parameter \(\bar\theta\), and the unnormalised densities and their first statistic moments converge in \(L^1\). Then
> \[
> m(\theta_n)\to m(\bar\theta).
> \]
> If the boundary tilted law is equivalent to the reference law and has finite first moments, then \(m(\bar\theta)\) lies in the interior of the moment body.

The second conclusion follows by the same supporting-hyperplane argument already used in `MomentBody`: equality in a supporting inequality would force an a.e. affine relation.

Add:

> This boundary mean is not attained at an interior parameter.

For this, use strict identifiability across all finite-partition parameters. One clean proof uses the two KL identities: equal means force the Jeffreys divergence to vanish, hence the tilted laws coincide, hence the parameter difference is an a.e. constant statistic combination.

That gives the exact obstruction:
\[
\boxed{
\text{a finite boundary tilt produces an interior moment-body point missing from }m(D^\circ).
}
\]

For a σ-finite base, first select one normalisable interior tilt as a probability reference. All such tilts have the same null sets, so the convex support is independent of that selection.

A later abstract theorem can use the standard framework:

- maximal natural domain, not an artificially restricted parameter set;
- proper closed log-Laplace function;
- nonempty full-dimensional domain;
- minimality;
- essential smoothness/steepness.

In that framework, Legendre duality gives the familiar full mean-domain result. The wall only needs the much smaller boundary-extension theorem above.

---

## 5. Temperature slices: variational geometry and residual variance

Use canonical joint parameters \((t,b)\), where \(b=ta\):
\[
\psi(t,b)=\log\mathbb E_{P_0}e^{-tL_0-\langle b,R\rangle}.
\]
Let \(I(e,M)\) be the normalised joint Legendre potential.

Assume the joint statistic \((L_0,R)\) is minimal. At the slice point
\[
(e,M)=\bigl(h_t(M),M\bigr),
\]
you obtain
\[
\partial_e I(e,M)=-t.
\]

Therefore
\[
\boxed{
J_t(M)
=
\inf_e\bigl(I(e,M)+te\bigr)+\psi(t,0),
}
\]
and the unique minimiser is \(e=h_t(M)\).

For a first real-valued theorem, take the infimum over the admissible **interior fibre**. A global infimum over all \(e\in\mathbb R\) requires the extended-valued Legendre potential.

### Hessian

Write the joint covariance as
\[
C=
\begin{pmatrix}
C_{00}&C_{0R}\\
C_{R0}&C_{RR}
\end{pmatrix},
\qquad H=D^2I=C^{-1}.
\]
Then
\[
D^2J_t
=
H_{RR}-H_{R0}H_{00}^{-1}H_{0R}
=
\boxed{C_{RR}^{-1}}.
\]

**Coordinate warning:** this equals \(G_{RR}^{-1}\) if \(G_{RR}\) means the Fisher block in canonical \(b\)-coordinates. In your \(a\)-coordinates,
\[
G_{aa}=t^2C_{RR},
\qquad
D^2J_t=t^2G_{aa}^{-1}.
\]

### The especially beautiful additional identity

Keep \(M\) fixed and vary \(t\). Then
\[
\boxed{
\partial_t h_t(M)
=
-\left(
\operatorname{Var}(L_0)
-
\operatorname{Cov}(L_0,R)\,
C_{RR}^{-1}\,
\operatorname{Cov}(R,L_0)
\right).
}
\]

Thus the slice energy decreases at the **residual variance of \(L_0\) after linear regression on the preserved responses**.

This is the same Schur-complement mechanism as the wall’s fixed-mean monotonicity. That is a worthwhile unification: one abstract “constrained exponential response” lemma can power both developments.

If \(L_0\) is affine in \(R\), the joint minimality assumption fails and \(\partial_e I\) is not an ordinary ambient derivative. The constrained variational statement survives; the differential statement belongs on the affine hull. This is a concrete motivation for `N^⊥`.

---

## 6. The finite-dimensional Legendre identity

Yes: on the existing response space, this should be a short corollary, not a new duality development.

Use canonical notation
\[
D\psi(\theta)[h]=-\langle m(\theta),h\rangle.
\]
Fix \(m=m(\theta_*)\). Convexity gives, for every admissible \(\theta\),
\[
\psi(\theta)
\ge
\psi(\theta_*)-\langle m,\theta-\theta_*\rangle.
\]
Rearrange:
\[
-\langle\theta,m\rangle-\psi(\theta)
\le
-\langle\theta_*,m\rangle-\psi(\theta_*)
=I(m).
\]

### Recommended theorem order

First prove the inequality, parameterised by \(\theta_*\):
```text
dual_objective_le_at_mean
```

Then package it as
```text
IsMaxOn (fun θ => -pairing θ (mean θ₀) - logZ θ) D θ₀
```
with membership of \(\theta_0\) stated separately as needed.

Then specialise \(\theta_0=\theta(m)\).

Only afterwards add an `sSup` corollary. An attained maximum immediately supplies the nonemptiness and bounded-above facts that real-valued `sSup` needs.

Also add uniqueness of the maximiser under minimality. Strict convexity of \(\psi\) is sufficient.

### Lean route

- Reuse the tangent inequality for a convex differentiable function.
- If the API is inconvenient, restrict to the scalar segment
  \[
  s\mapsto\psi(\theta_*+s(\theta-\theta_*))
  \]
  and apply the one-dimensional tangent inequality.
- Rewrite the derivative using the landed Fréchet formula.
- Finish by linear algebraic rearrangement.

For the bounded family, \(D=\mathbb R^J\), so domain bookkeeping is minimal. “About 40 lines” is credible once the pairing and derivative rewrites are already ergonomic.

For unbounded families, state the first version on the open natural domain. Extension to finite boundary parameters is a separate supporting-inequality lemma, obtainable by approximation or directly by Jensen under \(P_{\theta_*}\).

This identifies \(I\) with the Legendre transform **on the mean image**. A full Cramér theorem additionally needs the extended-valued transform at boundary and unattained means, plus the actual iid large-deviation bounds. I would not assume a ready-made Mathlib theorem without checking the current checkout.

---

## 7. The observable segment: one correction, one useful bonus

Let
\[
m_s=(1-s)m_0+sm_1,\qquad d=m_1-m_0,
\]
and let \(C_s=\operatorname{Cov}_{P_{\theta(m_s)}}(R,R)\).

Your landed regression theorem gives
\[
\boxed{
\mathbb E_{m_1}\phi-\mathbb E_{m_0}\phi
=
\int_0^1
\operatorname{Cov}_{m_s}\!\left(\phi,R_{C_s^{-1}d}\right)\,ds.
}
\]

The inverse covariance is essential. Your proposed notation is correct only if \(R_{\dot m}\) has already been defined to mean the statistic associated with the covariance-preimage of \(\dot m\).

There is a nice endpoint-only energy identity:
\[
\int_0^1 d^\top D^2I(m_s)d\,ds
=
D(P_1\Vert P_0)+D(P_0\Vert P_1),
\]
where here \(P_0,P_1\) denote the two endpoint family members.

Consequently,
\[
\boxed{
|\Delta\mathbb E\phi|^2
\le
\left(\int_0^1\operatorname{Var}_{m_s}(\phi)\,ds\right)
\left(D(P_1\Vert P_0)+D(P_0\Vert P_1)\right).
}
\]

For bounded statistics and bounded \(\phi\), compactness of the mean segment and continuity of the inverse chart should make the FTC hypotheses straightforward.

---

**Recommended next sequence:** land `LegendreMaximum` and the constrained KL identity; isolate the Schur-complement fixed-mean derivative; use it for both `WallMeanBand` and `TemperatureReduction`; then formalise the boundary-extension obstruction. That sequence adds a genuinely new organising principle rather than merely extending the already-complete bounded chart.