## Main recommendation

Build the joint exponential-family object next, but change two parts of the proposed statement:

1. **The joint kernel is larger than the data kernel unless an additional minimality condition holds.**
2. **Restricting natural parameters to \(t>0\) need not give a convex mean-image.** It gives an open image and a global chart onto that image. Convexity of the mean-image belongs to the **full natural-parameter family**.

This correction actually suggests a cleaner construction: build the full finite exponential family once, quotient its invisible directions, and obtain both existing charts by restriction.

---

# 1. The joint chart

## 1.1 Use one augmented statistic

Let \(\Omega\) be a nonempty finite alphabet, with weights \(w_\omega>0\), and put
\[
S(\omega)=(L_0(\omega),R_1(\omega),\ldots,R_k(\omega)).
\]
Define, on all of \(\mathbb R^{k+1}\),
\[
\psi(\theta)=\log\sum_{\omega\in\Omega}
w_\omega e^{-\langle\theta,S(\omega)\rangle},
\qquad
P_\theta(\omega)=
w_\omega e^{-\langle\theta,S(\omega)\rangle-\psi(\theta)}.
\]

Your physical parameterization is
\[
\Theta(t,a)=(t,ta),\qquad F(t,a)=\psi(\Theta(t,a)).
\]

All boundedness, integrability, and smoothness hypotheses are automatic here. Strict positivity is needed only on the effective support; zero-weight atoms can be removed.

The fundamental formulas are
\[
\nabla\psi(\theta)=-\mathbb E_\theta S,\qquad
D^2\psi(\theta)[h,j]=\operatorname{Cov}_\theta(S_h,S_j).
\]

In particular, **the Hessian of \(\psi\) is positive**, whereas the derivative of the mean map is negative. Keep that sign distinction explicit when reusing `QuotientMeanMap`.

### The natural dual coordinate is not quite the proposed one

The dual coordinate is
\[
\eta(\theta)=(\mathbb E_\theta L_0,M_\theta),
\]
not \((\mathbb E_\theta L_a,M_\theta)\).

Indeed,
\[
\mathbb E_\theta L_a=\eta_0+a\cdot M_\theta.
\]
This is a useful response observable, but its conversion from \(\eta\) depends on the parameter \(a\). It should not be assumed to be a global dual chart or to descend through statistical equivalences.

## 1.2 The correct joint kernel

Define
\[
N=\{(s,v):sL_0+R_v\text{ is constant on the support}\}.
\]
Then, for every \(\theta\),
\[
\ker D^2\psi(\theta)=N.
\]

Your existing data kernel satisfies
\[
\{0\}\times K\subseteq N,
\]
but equality requires
\[
L_0\notin \operatorname{span}\{1,R_1,\ldots,R_k\}.
\tag{minimal-temperature}
\]

Equivalently, **every** affine loss \(L_a\) is nonconstant. Nonconstancy of \(L_a\) at one particular point is insufficient.

For example, if \(L_0=R_1\), then temperature and the first data coordinate are redundant, even though \(L_a\) is nonconstant for most \(a\).

Thus there are two clean theorem versions:

* **General:** quotient by \(N\).
* **Preserve the temperature coordinate:** assume `(minimal-temperature)` and quotient only the data directions by \(K\).

For Lean, restricting to \(E=N^\perp\) is likely substantially cheaper than developing the smooth quotient-space interface.

## 1.3 Exact global injectivity

For \(\eta(\theta)=\mathbb E_\theta S\), \(d=\vartheta-\theta\),
\[
\langle\eta(\vartheta)-\eta(\theta),d\rangle
=
-\int_0^1
\operatorname{Var}_{\theta+sd}(S_d)\,ds.
\]

Because every posterior has the same strictly positive support,
\[
d\notin N
\quad\Longrightarrow\quad
\operatorname{Var}_{\theta+sd}(S_d)>0
\quad\text{for every }s.
\]

Consequently,
\[
\eta(\theta)=\eta(\vartheta)
\iff
\vartheta-\theta\in N.
\]

This is exactly your existing segment argument with the statistic enlarged by one component. There is no new global injectivity mechanism.

The relevant condition is positivity of variance for **every nonzero joint contrast modulo \(N\)**, not merely \(\operatorname{Var}(L_a)>0\).

## 1.4 The theorem I would actually formalize

Write \(S_E=\operatorname{proj}_E S\), and
\[
\eta_E(\theta)=\mathbb E_\theta S_E,\qquad \theta\in E.
\]

**Joint mean-chart theorem.** Under the finite-alphabet hypotheses above:

1. \(\psi|_E\) is smooth and has positive-definite Hessian.
2. \(\eta_E\) is injective, with invertible derivative everywhere.
3. \(\eta_E\) is an open embedding, with smooth local—and hence global-on-image—inverse.
4. For any open convex \(D\subseteq E\), the restriction
   \[
   \eta_E:D\longrightarrow\eta_E(D)
   \]
   has the same properties.
5. For the full domain,
   \[
   \eta_E(E)=
   \operatorname{int}_E\operatorname{conv}\{S_E(\omega):\omega\in\Omega\}.
   \tag{moment-polytope}
   \]

Items 1–4 are the cheap core. Item 5 is an additional surjectivity theorem.

A standard proof of item 5 minimizes
\[
\theta\longmapsto \psi(\theta)+\langle\theta,x\rangle
\]
for \(x\) in the interior of the moment polytope. Interior membership gives coercivity; strict convexity gives uniqueness.

### Why the \(t>0\) image need not be convex

Take three equally weighted atoms with
\[
S_1=(1,0),\qquad S_2=(0,1),\qquad S_3=(1,2).
\]
They affinely span \(\mathbb R^2\). For natural coordinates \((t,b)\),
\[
\frac{p_1p_3}{p_2^2}=e^{-2t}.
\]
Thus \(t>0\) corresponds to \(p_2^2>p_1p_3\).

Both
\[
(.80,.19,.01),\qquad (.01,.19,.80)
\]
satisfy this inequality; their midpoint does not. Since the mean coordinate is an affine isomorphism of this probability simplex, the restricted mean-image is nonconvex.

So: **open global chart on the positive-temperature region; convex global chart on the full natural family.**

## 1.5 Metric and KL compatibility

For a physical tangent vector \((s,v)\),
\[
D\Theta(t,a)(s,v)=(s,as+tv),
\]
and hence
\[
g_{(t,a)}((s,v),(s,v))
=
\operatorname{Var}_{t,a}(sL_a+tR_v).
\]

This gives exactly the blocks in the question:
\[
g_{tt}=\operatorname{Var}(L_a),\quad
g_{ta_i}=t\operatorname{Cov}(L_a,R_i),\quad
g_{a_i a_j}=t^2\operatorname{Cov}(R_i,R_j).
\]

But the ordinary Hessian in physical coordinates has
\[
\partial_t\partial_{a_i}F
=-M_i+t\operatorname{Cov}(L_a,R_i).
\]
That extra \(-M_i\) is why the Hessian statement must be made in natural coordinates.

The KL identity is
\[
\boxed{
\mathrm{KL}(P_\theta\Vert P_\vartheta)
=
\psi(\vartheta)-\psi(\theta)
-\langle\nabla\psi(\theta),\vartheta-\theta\rangle.
}
\]
Thus it is \(B_\psi(\vartheta,\theta)\), with the usual Bregman convention: **the parameter order is reversed relative to the distribution order**.

The two restrictions are now literal:

* fixed \(a\): \(\theta=u(1,a)\), giving `RayChart`;
* fixed \(t\): \(\theta=(t,ta)\), giving `MeanMapChart` and `QuotientMeanMap`.

### The 600-line question

I would target a roughly 600-line **compatibility/open-embedding package**, not promise a 600-line moment-polytope diffeomorphism theorem.

The economical implementation is to apply the existing multivariate machinery to \(S=(L_0,R)\), at temperature \(1\), and then pull back along \(\Theta\). The main uncertainty is inverse-chart packaging, not analysis.

Do **not** put moment-polytope surjectivity or a new general smooth-quotient API inside that budget.

---

# 2. Cramér form of the ray

Let
\[
J=m((0,\infty)),\qquad u:J\to(0,\infty)
\]
be the inverse chart.

Define the real-valued chart representative
\[
I_J(x)=-x\,u(x)-F(u(x)).
\tag{1}
\]

Then prove that, for \(x\in J\),
\[
I_J(x)=\sup_{v>0}(-vx-F(v)).
\tag{2}
\]

This order is Lean-friendly: define a manifestly finite function first, then identify it with the supremum.

## 2.1 Lean-ready hypotheses and conclusions

A minimal calculus-facing interface is:

* \(F,m,V:\mathbb R\to\mathbb R\);
* for every \(u>0\),
  \[
  F'(u)=-m(u),\qquad m'(u)=-V(u),\qquad V(u)>0;
  \]
* \(F\) is convex on \((0,\infty)\);
* \(m:(0,\infty)\to J\) is the supplied homeomorphism.

Then:

\[
I_J(m(u))=-u\,m(u)-F(u),
\]
\[
I_J'(m(u))=-u,
\qquad
I_J''(m(u))=\frac1{V(u)}.
\]

For \(V(u)=\operatorname{Var}_u(\ell)\),
\[
I_J(m(u))
=
\mathrm{KL}(P_u\Vert P_0)-F(0).
\]

The proof is particularly short after the inverse chart exists:
\[
u'(x)=-\frac1{V(u(x))},
\]
and differentiating (1) cancels the two terms involving \(u'(x)\):
\[
I_J'(x)=-u(x).
\]

No additional moment order is needed for these pointwise derivative statements. In particular, a local inverse derivative theorem plus the supplied homeomorphism can avoid a fresh \(C^1\)-IFT construction.

For **\(C^2\) packaging and the length substitution**, add continuity of \(V\) on \((0,\infty)\). This is automatic for a finite alphabet. In the general tilted setting, use your existing local domination/moment-continuity infrastructure.

Pointwise existence of three tilted moments alone is not, in isolation, a differentiation-under-the-integral hypothesis. But if `RayChart` already supplies the stated derivative identities, that analytic work has been paid for.

## 2.2 Supremum and convexity

For each \(x=m(u)\), the tangent inequality for \(F\) proves that \(v=u\) maximizes the expression in (2). This supplies both:

* nonemptiness of the set defining `sSup`;
* its boundedness above.

These facts matter if the definition uses real `sSup`. Outside \(J\), an unrestricted real `sSup` is not a reliable representation of an infinite rate function; use an extended-real supremum there.

Convexity follows as a supremum of affine functions, or locally from
\[
I_J''>0.
\]

Also call this a **one-sided Cramér transform**: \(v>0\) captures the lower-loss side. It is not the full two-sided Cramér transform unless the parameter domain is enlarged.

For a normalized prior, \(F(0)=0\). Otherwise the normalized rate is
\[
\mathcal I=I+F(0).
\]

## 2.3 Metric and length

Since \(dm=-V(u)\,du\),
\[
\boxed{
ds^2=V(u)\,du^2=I_J''(m)\,dm^2.
}
\]

For \(0<u_0<u_1\), assuming \(V\) continuous,
\[
\int_{u_0}^{u_1}\sqrt{V(u)}\,du
=
\int_{m(u_1)}^{m(u_0)}\sqrt{I_J''(x)}\,dx.
\]

I would formalize the second derivative first as the derivative of the explicit function \(x\mapsto-u(x)\), then identify it with `deriv (deriv I_J)` if that final syntax is desirable.

---

# 3. The endpoint without regular variation

Yes: there is a clean general theorem, and it is worth doing. Regular variation controls the **rate and self-similarity**; it is unnecessary for endpoint identification.

## Exact hypotheses

Let \(\ell\) be measurable and \(\alpha\in\mathbb R\). Assume:

1. \(\ell\ge\alpha\) almost everywhere;
2. for every \(\varepsilon>0\),
   \[
   \nu\{\ell<\alpha+\varepsilon\}>0;
   \]
3. for some \(u_0\ge0\),
   \[
   0<Z(u_0)=\int e^{-u_0\ell}\,d\nu<\infty.
   \]

Then all tilted polynomial moments exist for \(u>u_0\), and
\[
\boxed{\lim_{u\to\infty}m(u)=\alpha.}
\]

These hypotheses express finite essential infimum directly, avoiding any initial need to manipulate an extended-real `essInf`.

No nondegeneracy is needed: a constant loss is included.

## A proof with a useful quantitative lemma

Normalize the \(u_0\)-tilt to a probability \(Q\), put
\[
Y=\ell-\alpha\ge0,\qquad r=u-u_0.
\]
Then
\[
m(u)-\alpha=
\frac{\mathbb E_Q[Y e^{-rY}]}{\mathbb E_Q[e^{-rY}]}.
\]

For \(\varepsilon>0\), let
\[
c_\varepsilon=Q(Y\le\varepsilon/2)>0.
\]
For \(r\ge1/\varepsilon\), splitting at \(Y=\varepsilon\) gives
\[
0\le m(u)-\alpha
\le
\varepsilon+
\frac{\varepsilon}{c_\varepsilon}e^{-r\varepsilon/2}.
\]

This uses only
\[
\sup_{y\ge\varepsilon}y e^{-ry}
=\varepsilon e^{-r\varepsilon}.
\]

That elementary estimate is probably the most reusable Lean lemma in the proof.

For a finite alphabet, add the stronger endpoint:
\[
P_u\longrightarrow
\pi(\,\cdot\mid \ell=\min\ell).
\]
It identifies the endpoint distribution, not merely its mean.

---

# 4. Two-term wall law

The confirmed coefficient is consistent with the full local calculation. The important implementation distinction is:

> A second-order Taylor calculation can identify the coefficient with an \(o(B^{-1})\) error. To obtain the claimed \(O(B^{-2})\) remainder, one must also control the intervening odd order and an order-four remainder in \(B^{-1/2}\).

## 4.1 Normalization and the relevant derivatives

Use
\[
\phi(z)=z^p-\frac pq z^q+\frac pq-1,\qquad p>q>0,
\]
so \(\phi(1)=\phi'(1)=0\). Set
\[
A=\phi''(1)=p(p-q),
\]
\[
a_3=\phi'''(1)=A(p+q-3),
\]
\[
a_4=\phi''''(1)
=A\bigl(p^2+pq+q^2-6p-6q+11\bigr).
\]

Let \(z\) have normalized density \(e^{-B\phi(z)}\) on \((0,\infty)\), and put
\[
\varepsilon=B^{-1/2},\quad y=(z-1)/\varepsilon,\quad
Y_B=\sqrt B(z^q-1).
\]

Write
\[
d_1=q,\quad d_2=\frac{q(q-1)}2,\quad
d_3=\frac{q(q-1)(q-2)}6.
\]
Then
\[
Y_B=d_1y+\varepsilon d_2y^2+\varepsilon^2d_3y^3+\cdots.
\]

Let \(\mu_j\) denote moments of \(N(0,A^{-1})\). The required even moments are
\[
\mu_2=A^{-1},\quad
\mu_4=3A^{-2},\quad
\mu_6=15A^{-3},\quad
\mu_8=105A^{-4}.
\]

## 4.2 Exactly which terms enter \(c_1\)

The weight expansion is
\[
e^{-B\phi(1+\varepsilon y)}
=e^{-Ay^2/2}
\left[
1-\varepsilon\frac{a_3y^3}{6}
+\varepsilon^2\left(
\frac{a_3^2y^6}{72}-\frac{a_4y^4}{24}
\right)+\cdots
\right].
\]

The order-\(\varepsilon^2\) normalization correction is
\[
z_2=\frac{a_3^2\mu_6}{72}-\frac{a_4\mu_4}{24}.
\]

The mean is
\[
\mathbb E Y_B=\varepsilon h_1+O(\varepsilon^3),
\qquad
h_1=d_2\mu_2-\frac{d_1a_3\mu_4}{6}
=\frac{q(2-p)}{2A}.
\]

The second moment is
\[
\mathbb E Y_B^2=d_1^2\mu_2+\varepsilon^2 n_2+O(\varepsilon^4),
\]
where
\[
\begin{aligned}
n_2={}&(d_2^2+2d_1d_3)\mu_4
-\frac{d_1d_2a_3}{3}\mu_6\\
&+d_1^2\left(
\frac{a_3^2\mu_8}{72}-\frac{a_4\mu_6}{24}
\right)
-d_1^2\mu_2z_2.
\end{aligned}
\]

Therefore
\[
c_0=\frac{q^2}{A},
\qquad
c_1=n_2-h_1^2
=\frac{q^2(p-2)}{2p^2(p-q)}.
\]

The contributions are, in order:

1. quadratic/cubic terms of the observable;
2. observable–cubic-potential interaction;
3. squared cubic and quartic potential terms;
4. partition-function normalization;
5. subtraction of the squared mean.

The last two are especially easy to lose in a formal derivation.

### Odd terms that must be controlled

The order-\(\varepsilon\) and order-\(\varepsilon^3\) contributions to the normalized second moment vanish by parity. The order-\(\varepsilon^2\) contribution to the mean vanishes by parity.

The order-three weight polynomial is
\[
W_3(y)=
-\frac{\phi^{(5)}(1)y^5}{120}
+\frac{a_3a_4y^7}{144}
-\frac{a_3^3y^9}{1296},
\]
which is odd.

Thus \(\phi^{(5)}(1)\) does **not** enter \(c_1\), but controlling that order is part of obtaining the \(O(B^{-2})\) remainder.

## 4.3 Abstract expanding-window theorem

Here is a useful reusable version.

Assume \(\phi:(0,\infty)\to\mathbb R\) satisfies:

* \(\phi\ge0\);
* \(\phi(1)=\phi'(1)=0\), \(\phi''(1)=A>0\);
* \(\phi\) is \(C^6\) on a neighborhood of \(1\);
* for some \(0<\rho<1\), \(\eta>0\),
  \[
  |z-1|\ge\rho\Longrightarrow\phi(z)\ge\eta;
  \]
* for some \(B_0>0\), all polynomial weights needed below are integrable against \(e^{-B_0\phi(z)}\,dz\).

For a fixed polynomial \(P\), define
\[
T_B(P)=
\sqrt B\int_0^\infty
P(\sqrt B(z-1))e^{-B\phi(z)}\,dz.
\]

Then
\[
\begin{aligned}
T_B(P)
={}&\int_{\mathbb R}P(y)e^{-Ay^2/2}
\left[1+B^{-1/2}W_1(y)+B^{-1}W_2(y)
+B^{-3/2}W_3(y)\right]dy\\
&+O(B^{-2}),
\end{aligned}
\]
with \(W_1,W_2,W_3\) as above.

For an even \(P\), the half-integer terms vanish.

The proof uses the symmetric local window
\[
|y|<\rho\sqrt B;
\]
the omitted Gaussian tails and the original integral outside the local neighborhood are exponentially small. Shrinking \(\rho\) permits a Gaussian-polynomial bound on the Taylor remainder throughout the expanding window.

For a general observable \(g\), add:

* \(g\) is \(C^5\) near \(1\);
* \((1+|g|^2)e^{-B_0\phi}\) is integrable.

Then Taylor-expand
\[
\frac{g(1+\varepsilon y)-g(1)}{\varepsilon}
\]
inside this theorem. The monomial specialization satisfies all these hypotheses.

A good final Lean-facing output is
\[
\left(B\mapsto
\operatorname{Var}(Y_B)-c_0-\frac{c_1}{B}\right)
=O_{\mathrm{atTop}}\left(B\mapsto\frac1{B^2}\right).
\]

## 4.4 From variance to the wall primitive

Under the conventional wall scaling
\[
h(s)=\sqrt{\operatorname{Var}_{s}(x^q)},\qquad
P_s(dx)\propto e^{-(x^p+s x^q)}\,dx,
\]
put
\[
\beta=\frac{p}{2(p-q)},\qquad
D=\left(\frac qp\right)^{p/(p-q)}.
\]
For \(r\to\infty\), the negative-chamber rescaling has
\[
B=Dr^{2\beta}.
\]

Consequently,
\[
h(-r)
=k_-r^{\beta-1}
\left[
1+d\,r^{-2\beta}+O(r^{-4\beta})
\right],
\qquad
d=\frac{p-2}{4pD}.
\]

Hence there is a renormalized constant \(C_-\) such that
\[
\int_{-r}^{0}h(s)\,ds
=
\frac{k_-}{\beta}r^\beta+C_-
-\frac{k_-d}{\beta}r^{-\beta}
+O(r^{-3\beta}).
\]

Combining this with `WallRecedesStrong`,
\[
\begin{aligned}
\int_{-R}^{S}h(s)\,ds
={}&\frac{k_-}{\beta}R^\beta
+\frac1{\sqrt q}\log S+C\\
&-\frac{k_-d}{\beta}R^{-\beta}
+O(R^{-3\beta})+O(S^{-\delta}).
\end{aligned}
\]

Two cautions:

* The local coefficient \(c_1\) does not determine \(C\); that constant depends on the whole crossover profile.
* Along a coupled \(R,S\) limit, the positive-tail error can obscure the displayed negative-tail correction. A genuinely ordered two-term expansion must compare those rates.

### Recommended sub-step order

1. Formalize the Gaussian-moment coefficient algebra.
2. Prove the polynomial expanding-window expansion.
3. Specialize to the normalization, mean, and second moment.
4. Prove variance division/subtraction and square-root asymptotic lemmas.
5. Transfer to \(h(-r)\).
6. Integrate to the renormalized primitive and combine tails.

This keeps the hardest analysis isolated from both monomial algebra and wall bookkeeping.

---

# 5. What else is newly cheap?

## The featureless anchor in natural coordinates

The full finite exponential family contains \(\theta=0\), with
\[
P_0=\frac{w}{\sum w}.
\]

Every physical ray \(t\mapsto(t,ta)\) starts there. In physical coordinates the entire set \(\{0\}\times\mathbb R^k\) collapses to this one posterior; in natural coordinates there is no artificial singularity.

Moreover,
\[
\mathrm{KL}(P_\theta\Vert P_0)
=
\psi(0)-\psi(\theta)+\langle\nabla\psi(\theta),\theta\rangle.
\]

The integral Hessian formula gives
\[
\boxed{
\mathrm{KL}(P_\theta\Vert P_0)
=
\int_0^1 s\,
\operatorname{Var}_{s\theta}(S_\theta)\,ds.
}
\]

This is a particularly good bridge theorem: **the departure from the featureless prior is the integrated response form along the natural ray**.

Call this maximal entropy only when the prior is uniform; otherwise it is the distinguished prior, or the zero relative-entropy point.

## Finite-alphabet face endpoints

For each natural direction \(h\),
\[
P_{rh}\longrightarrow
\pi(\,\cdot\mid S_h=\min S_h).
\]
The limiting mean lies on the corresponding exposed face of the moment polytope.

This gives a genuine global boundary map: natural directions select faces, and the prior resolves ties within each selected face. The convergence proof is just finite sums and exponential decay. General normal-fan packaging can wait.

---

# Revised ranking

| Rank | Item | Reason |
|---|---|---|
| **1** | Augmented-statistic joint family; joint kernel; natural-coordinate pullback; KL/Bregman identity | Directly connects all landed charts |
| **2** | \(N^\perp\) open-embedding packaging, including the featureless anchor and radial KL integral | Converts local formulas into one global response chart |
| **3** | Ray Cramér curvature theorem | Small increment; makes Fisher geometry intrinsic in response coordinates |
| **4** | General essential-infimum endpoint, plus finite-alphabet endpoint distribution | Completes the featureless-to-ground-state ray without regular variation |
| **5** | Full-family moment-polytope image theorem | Strongest global-map statement, but a separate coercivity/surjectivity proof |
| **6** | Two-term wall law | Valuable sharp asymptotics; more analysis and narrower scope |
| **7** | Abstract moving-minimum theorem | Broadens the wall model, but less urgent than joining the existing geometry |

The most consequential shift is to regard \((t,a)\) as a useful **parameterization of one exponential family**, rather than to construct a new joint theory directly in those coordinates. Then the quotient, potential, KL divergence, prior anchor, ray chart, and data slices become manifestations of the same object.