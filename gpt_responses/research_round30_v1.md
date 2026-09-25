There are two important corrections before the ranking:

1. **The wall family is non-steep, and its mean image is a proper subset of the convex support.**
2. **The three-regime wall law is not a finite/logarithmic/power classification of temperature-ray distances to the mean boundary.** Temperature rays have logarithmically infinite Fisher length in all three chambers. The wall law concerns lengths of *data-direction curves at increasing temperature*.

I will use
\[
dP_\theta(x)=Z(\theta)^{-1}e^{-\theta_1x^p-\theta_2x^q}\,dx,
\qquad 0<q<p.
\]
The assumption \(q<p\) is essential to the domain you proposed. If your wall modules use another normalization of the large parameter, the logarithmic coefficient must be translated accordingly.

## 1. The wall as a joint exponential family

### 1.1 Exact natural domain

For \(0<q<p\),
\[
\boxed{\mathcal D
=\{(\alpha,\beta):\alpha>0,\ \beta\in\mathbb R\}
 \cup\{(0,\beta):\beta>0\}.}
\]

There are no additional points. Integrability at zero is automatic; infinity gives precisely these conditions.

Its open natural domain is
\[
\mathcal D^\circ=(0,\infty)\times\mathbb R.
\]

Two distinctions from the probability-base theory:

* \((0,0)\notin\mathcal D\): there is **no normalized featureless anchor at zero** for Lebesgue measure.
* Every \((0,\beta)\), \(\beta>0\), has finite moments of every polynomial order. Thus the family really is non-steep at this boundary.

You can reuse the probability-base machinery after choosing any integrable reference parameter, but the translated parameter domain is not all of \(\mathbb R^2\).

### 1.2 Exact mean domain

Put
\[
r=p/q>1,\qquad k=1/q,\qquad z=x^q.
\]
Then the base measure becomes \(q^{-1}z^{k-1}dz\), and write
\[
u=E[z^r]=E[x^p],\qquad v=E[z]=E[x^q].
\]

Define
\[
C_\Gamma=\frac{\Gamma(k+r)}{\Gamma(k)k^r}.
\]
Then
\[
\boxed{\eta(\mathcal D^\circ)
 =\{(u,v):v>0,\quad v^r<u<C_\Gamma v^r\}.}
\]
Including the integrable natural boundary,
\[
\boxed{\eta(\mathcal D)
 =\{(u,v):v>0,\quad v^r<u\le C_\Gamma v^r\}.}
\]

The upper boundary consists exactly of the gamma laws \(\alpha=0,\beta>0\).

By comparison,
\[
\operatorname{conv}\{(x^p,x^q):x>0\}
 =\{(u,v):v>0,\ u\ge v^r\},
\]
and its closed convex hull is
\[
\{(u,v):v\ge0,\ u\ge v^r\}.
\]
So the mean image is a **proper curved band inside the convex support**. In particular, the inequality suggested in the question has its orientation reversed when \(q<p\).

A useful proof organization is to fix \(v>0\). For every \(\alpha>0\), there is a unique \(\beta(\alpha,v)\) giving that mean. Along this curve,
\[
\frac{du}{d\alpha}\Big|_v
=-\left(
 \operatorname{Var}(z^r)
 -\frac{\operatorname{Cov}(z^r,z)^2}{\operatorname{Var}(z)}
 \right)<0.
\]
The endpoints are:

* \(\alpha\downarrow0\): \(\beta\to k/v\), \(u\to C_\Gamma v^r\);
* \(\alpha\to\infty\): concentration at \(z=v\), \(u\to v^r\).

This is a clean route, but the fixed-mean concentration endpoint is a genuine additional lemma—not just an application of your fixed-direction endpoint theorem.

### 1.3 The chambers in mean coordinates

Set
\[
C_W=\frac{1/p}
 {\left(\Gamma((q+1)/p)/\Gamma(1/p)\right)^{p/q}}.
\]
Then \(1<C_W<C_\Gamma\), and
\[
\begin{array}{c|c}
\text{natural chamber}&\text{mean image}\\ \hline
\beta<0 & v^r<u<C_Wv^r\\
\beta=0 & u=C_Wv^r\\
\beta>0,\ \alpha>0 & C_Wv^r<u<C_\Gamma v^r.
\end{array}
\]

Thus the wall is a homogeneous curve splitting the mean band, not a boundary of that band.

For the temperature rays \((\alpha,\beta)=(t,ta)\):

* **\(a>0\):**
  \[
  v\sim\frac1{qta},\qquad
  u\sim\frac{\Gamma((p+1)/q)}{\Gamma(1/q)}(ta)^{-p/q}.
  \]
  They approach the origin asymptotically along the gamma edge.

* **\(a=0\):**
  \[
  u=\frac1{pt},\qquad
  v=\frac{\Gamma((q+1)/p)}{\Gamma(1/p)}t^{-q/p}.
  \]
  They approach the origin exactly along the wall curve.

* **\(a<0\):**
  \[
  x_*(a)=(-aq/p)^{1/(p-q)},\qquad
  \eta(t,ta)\longrightarrow(x_*^p,x_*^q).
  \]
  They approach the lower, deterministic edge **away from the origin**.

So “near the corner” describes the nonnegative chambers, not a fixed negative-\(a\) temperature ray.

### 1.4 Which lengths have the three regimes?

For a temperature ray, its Fisher speed is
\[
\sqrt{\operatorname{Var}_{t,a}(\ell_a)},\qquad
\ell_a=x^p+ax^q.
\]
The leading asymptotics are
\[
\operatorname{Var}_{t,a}(\ell_a)\sim \frac{\kappa_a}{t^2},
\qquad
\kappa_a=
\begin{cases}
1/q&a>0,\\
1/p&a=0,\\
1/2&a<0.
\end{cases}
\]
Consequently,
\[
\boxed{\int^{T}\sqrt{\operatorname{Var}_{t,a}(\ell_a)}\,dt
 \sim\sqrt{\kappa_a}\log T}
\]
in **all three cases**.

The finite/logarithmic/\(\sqrt t\) classification instead applies to
\[
L_t([a_0,a_1])
=\int_{a_0}^{a_1}t\sqrt{\operatorname{Var}_{t,a}(x^q)}\,da,
\]
the length of a data segment at fixed temperature.

This is still literally Fisher geometry, but it is the geometry of a **family of curves**, not the length of one temperature ray approaching its endpoint.

There is also a finite-distance boundary phenomenon: approaching \((0,\beta)\), \(\beta>0\), from \(\alpha>0\) has finite local Fisher length. This is the non-steep gamma edge away from the corner.

### 1.5 Lean-ready mean-coordinate statements

For the joint dual potential use the sign-correct convention
\[
I(m)=\sup_{\theta\in\mathcal D}
 \{-\langle\theta,m\rangle-\psi(\theta)\}
=\psi^*(-m).
\]
On the open attained mean domain,
\[
\nabla I(m)=-\theta(m),\qquad D^2I(m)=G(\theta(m))^{-1}.
\]

The reusable path theorem is
\[
\boxed{
\operatorname{Length}_G(\theta)
=\int
 \sqrt{\langle \dot m,D^2I(m)\dot m\rangle},
\qquad m=\eta\circ\theta.
}
\]
Hypotheses: a \(C^1\) path in the regular natural domain, invertible covariance, and the usual integrability conditions for the length integral.

For your scalar ray chart, an especially clean endpoint theorem is:

> If \(m(t)\downarrow b\) and
> \[
> (x-b)^2I''(x)\longrightarrow\kappa>0
> \quad(x\downarrow b),
> \]
> then the response distance to \(b\) is infinite, and
> \[
> \int_x^{x_0}\sqrt{I''(y)}\,dy
> \sim\sqrt\kappa\log\frac1{x-b}.
> \]

For the wall temperature rays, \(\kappa=\kappa_a\) above. This gives the correct boundary-distance theorem directly in your existing `RayCramer` language.

A power-law integral criterion for \(\sqrt{I''}\) would be a small, useful generalization.

---

## 2. Bounded statistics beyond finite alphabets: the full theorem is true

Let \((X,\mu)\) be a probability space and
\[
S:X\to E
\]
be measurable and essentially bounded, with \(E\) finite-dimensional Euclidean. Define
\[
\psi(\theta)=\log\int e^{-\langle\theta,S\rangle}\,d\mu,
\qquad
\eta(\theta)=E_\theta[S],
\]
and let
\[
C=\overline{\operatorname{conv}}(\operatorname{essRange}_\mu S).
\]

Under minimality,
\[
\operatorname{Var}_\mu(\langle h,S\rangle)>0
\quad\text{for every }h\ne0,
\]
the answer is
\[
\boxed{\operatorname{range}\eta=\operatorname{interior}C.}
\]

Thus closure equality is true but unnecessarily weak. Boundedness supplies an everywhere-finite natural domain, eliminating the wall’s non-steep obstruction.

Without minimality,
\[
\boxed{\operatorname{range}\eta=\operatorname{relativeInterior}C.}
\]
For a global chart, restrict natural parameters to \(N^\perp\), where
\[
N=\{h:\langle h,S\rangle\text{ is a.e. constant}\}.
\]

The essential range must be taken with respect to the actual prior probability measure. An equivalent strictly positive prior density does not change its null sets.

### Reusing the finite proof

The exact replacement for \(\pi_{\min}\) is a **uniform positive-mass cap lemma**.

For \(x\in\operatorname{int}C\), there exist \(c>0\) and \(m>0\) such that, for every unit vector \(e\),
\[
\mu\{y:-\langle e,S(y)-x\rangle\ge c\}\ge m.
\]
Then
\[
\boxed{\psi(\theta)+\langle\theta,x\rangle
 \ge c\|\theta\|+\log m.}
\]

Proof of the cap lemma:

1. An interior ball at \(x\) supplies a support point sufficiently far in every negative direction.
2. A small neighborhood of an essential-range point has positive mass.
3. Essential boundedness makes this directional inequality stable under perturbing the direction.
4. Compactness of the unit sphere reduces to finitely many neighborhoods.
5. Take the minimum of their positive masses.

Your extreme-value and first-order-condition proof then runs essentially unchanged.

**Lean recommendation:** first prove the coercive lower bound as a standalone lemma. It is the genuinely new measure-theoretic ingredient. Keep essential-range packaging separate from the optimization proof.

---

## 3. The two-term wall law

### 3.1 First fix the normalization explicitly

For the displayed family \(e^{-t(x^p+ax^q)}dx\), the exact scaling is
\[
A=a\,t^{(p-q)/p}.
\]
Let
\[
f(A)=\sqrt{\operatorname{Var}_{A}(y^q)},
\qquad
dP_A(y)\propto e^{-y^p-Ay^q}\,dy.
\]
Then
\[
\boxed{L_t([a_0,a_1])
=\int_{a_0t^{(p-q)/p}}^{a_1t^{(p-q)/p}}f(A)\,dA.}
\]

At the positive end,
\[
f(A)\sim\frac1{\sqrt q\,A}.
\]
Therefore, for \(a_1>0\),
\[
L_t([0,a_1])
=\frac{p-q}{p\sqrt q}\log t+O(1).
\]

So **\(1/\sqrt q\) is the coefficient of \(\log A\)**. With the temperature parameter in the question, the coefficient of \(\log t\) is \((p-q)/(p\sqrt q)\). If the landed theorem uses \(1/\sqrt q\log t\), its \(t\) must be a rescaled wall parameter or its length must be defined differently.

That normalization check should precede the next formalization.

### 3.2 Recommended sub-step order

1. Exact scaling to the universal \(A\)-family.
2. Positive-end expansion with an integrable remainder.
3. Negative-end saddle normalization, including the exact Jacobian.
4. Expansion of a **centered, rescaled observable’s variance**.
5. Square-root expansion.
6. A general renormalized-primitive lemma.
7. Substitute the temperature-dependent endpoints.

This keeps all delicate Laplace work independent of the final length theorem.

### 3.3 The expanding-window theorem to target

Let \(\phi\) have a unique interior minimum \(y_0>0\), normalized by
\[
\phi(y_0)=\phi'(y_0)=0,\qquad \lambda=\phi''(y_0)>0.
\]
Write
\[
\mu_3=\phi'''(y_0),\qquad \mu_4=\phi''''(y_0).
\]
Under local Taylor regularity and tail hypotheses ensuring that the discarded polynomial moments are exponentially small, put
\[
D_B=(-y_0\sqrt B,\infty).
\]

For every fixed polynomial \(P\), target
\[
\begin{aligned}
&\int_{D_B}P(z)e^{-B\phi(y_0+z/\sqrt B)}\,dz\\
&=\int_{\mathbb R}P(z)e^{-\lambda z^2/2}
 \left[
 1-\frac{\mu_3z^3}{6\sqrt B}
 +\frac1B\left(\frac{\mu_3^2z^6}{72}
                  -\frac{\mu_4z^4}{24}\right)
 \right]dz
 +o(B^{-1}).
\end{aligned}
\]

Concrete sufficient hypotheses for the wall application:

* \(\phi\) is \(C^5\) near \(y_0\);
* a uniform quadratic lower bound near \(y_0\);
* a positive gap off that neighborhood;
* coercive growth at infinity sufficient for the required polynomial moments.

For proof engineering, use a growing central window such as \(|z|\le B^\delta\) with a small fixed \(\delta>0\), and treat its complement separately.

`HalfLineLaplace.tendsto_sqrt_mul_integral` supplies the leading Gaussian limit and useful infrastructure. **It does not by itself supply the expansion:** the new work is controlling the Taylor remainder after multiplication by \(B\).

I would expose the polynomial-moment expansion as the reusable theorem, not a theorem specialized to partition functions.

### 3.4 Centering avoids unnecessarily high derivatives

For a smooth observable \(h\), set
\[
H_B=\sqrt B\,(h(Y_B)-h(y_0)),
\qquad dP_B\propto e^{-B\phi(y)}dy.
\]
Then
\[
\operatorname{Var}(H_B)=c_0+\frac{c_1}{B}+o(B^{-1}),
\]
where, writing \(h_j=h^{(j)}(y_0)\),
\[
c_0=\frac{h_1^2}{\lambda},
\]
and
\[
\boxed{
c_1=
\frac{h_2^2/2+h_1h_3}{\lambda^2}
-\frac{2h_1h_2\mu_3+h_1^2\mu_4/2}{\lambda^3}
+\frac{h_1^2\mu_3^2}{\lambda^4}.
}
\]

This route needs only the second-order local density expansion and the cubic observable expansion. Expanding three uncentered Laplace integrals far enough and then cancelling is substantially more expensive.

### 3.5 Does \(o(1/B)\) suffice?

**Yes, for the additive-constant wall law.** In fact, on the negative side, a relative \(O(1/B)\) estimate without an explicit coefficient already gives the necessary integrability.

The universal negative tail has the form
\[
f(-A)=K A^e\left(1+\frac{d}{A^{p/(p-q)}}
 +o\!\left(A^{-p/(p-q)}\right)\right),
\]
where
\[
e=\frac{2q-p}{2(p-q)},\qquad e+1=\frac{p}{2(p-q)}.
\]
The correction exponent is
\[
e-\frac{p}{p-q}=-1-\frac{p}{2(p-q)}<-1.
\]
Thus subtracting the leading power leaves an integrable tail.

Together with the positive-end expansion, this gives a finite renormalized constant. For \(a_-<0<a_+\),
\[
\boxed{
L_t([a_-,a_+])
=\sqrt t\,A_-(a_-)
+\frac{p-q}{p\sqrt q}\log t
+C(a_-,a_+)+o(1).
}
\]
Here
\[
A_-(a_-)=
\int_{a_-}^{0}
\frac{q\,x_*(a)^{q-1}}
 {\sqrt{\ell_a''(x_*(a))}}\,da.
\]

What is lost by choosing \(o(1/B)\)?

* Nothing needed for existence of the additive constant.
* No explicit uniform remainder bound follows.
* You cannot claim a stronger algebraic error rate beyond what the little-\(o\) statement and integration actually yield.

A general warning belongs in the primitive lemma: an \(o(1/A)\) remainder is **not** necessarily integrable. The negative-wall argument succeeds because its transformed correction exponent is strictly below \(-1\).

---

## 4. Newly cheap consequences of the joint family

### 4.1 Anchor length: the clean bound uses both KL directions

For the segment \(s\mapsto s\theta\), let
\[
V(s)=\operatorname{Var}_{s\theta}(S_\theta).
\]
You have
\[
D(P_\theta\|P_0)=\int_0^1sV(s)\,ds.
\]
The reverse identity is
\[
D(P_0\|P_\theta)=\int_0^1(1-s)V(s)\,ds.
\]
Consequently Cauchy–Schwarz gives
\[
\boxed{
L^2\le D(P_\theta\|P_0)+D(P_0\|P_\theta).
}
\]

The proposed bound \(L^2\le2D(P_\theta\|P_0)\) is false in general.

A bounded-statistic counterexample is the fair Bernoulli prior, tilted towards the zero atom. As the tilt tends to infinity,
\[
L\longrightarrow\pi/2,\qquad
D(P_\theta\|P_0)\longrightarrow\log2,
\]
and \(\pi^2/4>2\log2\).

**Cheap target:** reverse-anchor identity plus the Jeffreys bound. No projection or duality infrastructure is needed.

### 4.2 Full dual potential and inverse response

This is now one of the strongest next targets.

For bounded minimal \(S\), on \(U=\operatorname{int}C\), define
\[
\theta(m)=\eta^{-1}(m),\qquad
I(m)=-\langle\theta(m),m\rangle-\psi(\theta(m)).
\]
Then prove
\[
I(m)=\sup_\vartheta
 \{-\langle\vartheta,m\rangle-\psi(\vartheta)\},
\]
\[
\nabla I=-\theta,\qquad D^2I=G^{-1},
\]
and
\[
\boxed{
D(P_\theta\|P_\vartheta)
=B_I(\eta(\theta),\eta(\vartheta)).
}
\]

This is the multivariate version of `RayCramer`, with the essential new ingredient being inverse differentiation for the mean map.

For Lean, define \(I\) first using the inverse chart, and prove the supremum characterization afterward. That avoids making extended-real convex conjugacy the foundation of the differential calculations.

Also, call natural and mean segments **affine geodesics for the dual connections**, not Fisher–Rao Riemannian geodesics. They are generally not the latter.

### 4.3 Generalized Pythagoras: start with the three-point identity

The exact algebraic identity is
\[
\boxed{
D(P_\theta\|P_\vartheta)
-D(P_\theta\|P_\zeta)
-D(P_\zeta\|P_\vartheta)
=
\langle\vartheta-\zeta,\eta(\theta)-\eta(\zeta)\rangle.
}
\]

It immediately yields Pythagoras under the displayed orthogonality condition.

For example, if \(\zeta\) minimizes \(D(P_\theta\|P_\xi)\) over an affine natural family \(A\), then
\[
\eta(\theta)-\eta(\zeta)\perp\operatorname{direction}(A).
\]
Therefore the Pythagorean equality holds for every \(\vartheta\in A\).

For a convex constraint rather than an affine one, the first-order condition gives the corresponding inequality.

**Lean order:** three-point identity → orthogonality corollary → projection optimality. Do not make projection existence a prerequisite for landing the identity.

### 4.4 Fixed-temperature images are graphs, with a useful variational description

You correctly rejected the hyperplane interpretation.

Fix \(t>0\). The measure
\[
d\mu_t=Z(t,0)^{-1}e^{-tL_0}\,d\mu
\]
is a positive prior for the contrast family. Therefore
\[
a\longmapsto M(t,a)
\]
covers the interior of the contrast convex support under contrast minimality.

The augmented mean image is a graph
\[
\boxed{\eta_0=h_t(M)}
\]
over that contrast mean domain.

When the augmented family is minimal and the full dual potential is available, this graph is characterized by
\[
\boxed{\partial_{\eta_0}I(\eta_0,M)=-t.}
\]
It is a level set of a **dual coordinate**, not a primal affine hyperplane.

Even better, its reduced rate potential is
\[
\boxed{
J_t(M)
=\inf_e\{I(e,M)+te\}+\psi(t,0).
}
\]
The minimizer is \(e=h_t(M)\). This identifies the temperature slice as a partial minimization of the joint rate function.

Two differential consequences:
\[
Dh_t=G_{0R}G_{RR}^{-1},\qquad
D^2J_t=G_{RR}^{-1}.
\]

At \(t=0\), distinguish the full natural hyperplane \(\theta_0=0\) from the pullback \(\Theta(0,a)\): the latter collapses to the prior.

---

## 5. Revised ranking

Here is my ranking by mathematical payoff relative to expected formal cost.

### 1. Bounded-statistic moment-body theorem

\[
\operatorname{range}\eta=\operatorname{int}
 \overline{\operatorname{conv}}(\operatorname{essRange}S).
\]

This removes the finite-alphabet restriction from the central map theorem. The finite-direction positive-mass argument is the key new lemma.

### 2. Full mean-coordinate potential

Inverse mean chart, multivariate Cramér potential, inverse Hessian, dual Bregman identity, and path-length transport.

This turns “the mean map is a chart” into “the response geometry is completely described in either coordinate system.”

### 3. Three-point identity and the two anchor-length identities

A very cheap release, potentially before either large item:

* generalized Pythagoras under orthogonality;
* reverse anchor;
* \(L^2\le\) Jeffreys divergence.

These are immediate dividends of what has landed.

### 4. Fixed-temperature graph and partial minimization

First land coverage of the contrast mean domain using the tilted prior. Add the dual-coordinate graph characterization after item 2.

This directly answers what “data manifold at fixed temperature” means inside the joint geometry.

### 5. Degenerate \(N^\perp\) packaging

Still worthwhile, now with a clearer payoff:
\[
N^\perp\ \simeq\ \operatorname{ri}C.
\]
I would prove the full-dimensional bounded theorem first, then obtain this by restriction to the affine span, rather than burdening the initial coercivity proof with relative-interior bookkeeping.

### 6. Exact wall mean band and the geometric interpretation theorem

The non-steep band is a beautiful counterpoint to the bounded-statistic theorem. Start with:

1. exact natural domain;
2. explicit gamma boundary;
3. chamber-separating wall curve;
4. fixed-mean monotonicity;
5. endpoint completion and mean-band surjectivity.

It is conceptually valuable but not as cheap as the finite polytope result might suggest.

### 7. Two-term wall law

Do the centered expanding-window variance lemma, then the renormalized primitive. Prefer a little-\(o\) theorem initially; an explicit \(O(B^{-2})\) remainder is not needed for the additive constant.

### 8. Abstract moving minimum

Still last unless another application demands uniformity in an external parameter. For the homogeneous two-monomial wall, exact scaling removes the moving minimum before the delicate analysis begins.

**Overall:** the best next expansion is not another endpoint theorem. It is the pair
\[
\boxed{\text{bounded-statistic mean-body surjectivity}
\quad+\quad
\text{full dual response potential}.}
\]
Together they give the programme’s global coordinate geometry beyond finite alphabets; the wall then becomes a precise and illuminating example of what changes when boundedness—and hence steepness at the natural boundary—is lost.