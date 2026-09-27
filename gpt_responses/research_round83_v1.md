The next picture should have **two distinct completions**:

1. a **compact, globally continuous Hellinger response family**, parametrised by the entire closed moment polytope;
2. the **Fisher-length completion**, which selects the accessible part of that family and can carry a stronger topology.

Uniqueness identifies responses where Fisher endpoints exist. The next major tasks are to construct those endpoints and to separate Fisher accessibility from ordinary continuity of the response law.

Three corrections to the proposed picture are important:

- The variational response should be **continuous across faces**, not jump when its support changes.
- Response information need **not** increase along an exponential data tilt.
- A face-chain theorem needs no additional global normal-translation hypothesis under your bounded-statistic assumptions. Compact-uniform bounded-tilt comparison supplies the needed control.

## Q1. Existence in higher codimension

### (a) The candidate theorem is true—and admits a stronger formulation

Write \(d_A\) for the intrinsic Fisher distance of the family based on \(\nu(\cdot\mid A)\).

Here is the useful intermediate theorem.

> **Accessible-face lifting.**  
> Let \(A\) be a charged exposed face event. Suppose some completion point \(x_0\in\widehat W\) has law
> \[
> Q_{x_0}=P^A_{v_0}.
> \]
> Then there is a map
> \[
> j_A:W_A\longrightarrow\widehat W
> \]
> satisfying
> \[
> Q_{j_A(v)}=P^A_v,\qquad
> \operatorname{meanExt}(j_A(v))=m_A(v),
> \]
> and
> \[
> \widehat d_F(j_A(v),j_A(w))\le d_A(v,w).
> \]
> Consequently \(j_A\) extends to a nonexpanding map
> \[
> \widehat j_A:\widehat{W_A}\longrightarrow\widehat W.
> \]

The assumption can be supplied by an accessible normal ray, but the theorem itself does not need a ray.

This immediately gives your candidate:

> **Two-stage face-chain accessibility.**  
> Suppose \(A_1\) is an accessible charged exposed face, and \(A_2\subseteq A_1\) is accessible in the Fisher geometry based on \(\nu(\cdot\mid A_1)\). Then every specified accessible mean of the \(A_2\)-family is accessible in \(\widehat W\). In particular, under your two finite-normal-ray hypotheses,
> \[
> \exists x\in\widehat W,\qquad
> \operatorname{meanExt}(x)=M,\qquad
> Q_x=P^{A_2}_{v_M}.
> \]

Here conditioning twice equals conditioning directly, and bounded exponential tilting commutes with conditioning. Your fibre uniqueness makes the lift canonical.

Two useful strengthenings:

- \(A_1\) need not be a facet.
- Accessibility of one face-family law implies accessibility of **the whole open face family**.

The latter already says that accessible means form a union of relative face interiors, rather than an arbitrary subset within each stratum.

### What normal-translation control actually supplies

For a normal tilt \(a\) of \(A\),
\[
\operatorname{Var}_{P_{\theta+a}}f
\le \frac{\operatorname{Var}_{P_\theta}f}{P_\theta(A)}.
\]
Thus a translated full-family path \(\gamma\), with \(P_{\gamma(t)}(A)\ge q\), has length at most \(q^{-1/2}\operatorname{Length}(\gamma)\).

But:

- a lower bound along the **first ray** does not by itself give a uniform lower bound along every later tangential path;
- this estimate compares two **full-family** Fisher forms, not directly the full form with the face form.

For face-chain accessibility, no additional global bound is necessary. One uses compact-by-compact control, choosing the normal depth separately for successive finite segments.

### (b) A clean proof route

There are two routes. I would formalise the stronger, ray-independent one.

#### Step 1: bounded tilts act on the completion

For \(h\in W\), let \(T_h(\theta)=\theta+h\), and put
\[
R_h=\operatorname*{ess\,osc}_\nu\langle h,S\rangle.
\]
The density ratio is bounded by \(e^{R_h}\). Hence
\[
\operatorname{Var}_{P_{\theta+h}}\langle w,S\rangle
\le e^{R_h}\operatorname{Var}_{P_\theta}\langle w,S\rangle,
\]
and therefore
\[
d_F(\theta+h,\eta+h)\le e^{R_h/2}d_F(\theta,\eta).
\]
Applying the same estimate to \(-h\) gives a bi-Lipschitz translation action on \(\widehat W\).

On completion laws this action is exactly
\[
Q\longmapsto
\frac{e^{-\langle h,S\rangle}Q}
     {\int e^{-\langle h,S\rangle}\,dQ}.
\]

Define
\[
j_A(v)=T_{v-v_0}(x_0),
\]
using the canonical inclusion \(W_A\subseteq W\).

#### Step 2: identify the infinitesimal metric along the face orbit

Take \(\theta_n\to x_0\) in the completion. Then \(P_{\theta_n}\to P^A_{v_0}\) in Hellinger and \(L^1\).

For a fixed \(C^1\) face path \(v(t)\), consider
\[
\gamma_n(t)=\theta_n+v(t)-v_0.
\]
Bounded tilting gives convergence of these laws to \(P^A_{v(t)}\), uniformly on the compact parameter interval. Boundedness of \(S\) then gives uniform convergence of the relevant covariance forms. Thus
\[
\operatorname{Length}_F(\gamma_n)
\longrightarrow
\operatorname{Length}_{F,A}(v).
\]
Pass to the completion at the endpoints and take the infimum over face paths:
\[
\widehat d_F(j_A(v),j_A(w))\le d_A(v,w).
\]

This proves the lifting theorem without a normal-cone argument.

#### The normal-ray version

Yes, for
\[
\theta_r(v)=v-r u_1
\]
with the understood projection into \(W\),
\[
\operatorname{Var}_{P_{\theta_r(v)}}\langle w,S\rangle
\longrightarrow
\operatorname{Var}_{P^{A_1}_v}\langle w,S\rangle
\]
uniformly for \(v\) in compact sets and \(w\) in bounded sets.

Indeed,
\[
P_{\theta_r(v)}(\cdot\mid A_1)=P^{A_1}_v
\]
exactly. Uniform bounded-tilt comparison yields
\[
\sup_{v\in K}P_{\theta_r(v)}(A_1^c)\to0.
\]
The mixture formula for variance then proves uniform convergence of the covariance forms.

Also, finite ray length transfers from one tangential basepoint to every other:
\[
\operatorname{rayTail}_{v}(r)
\le
e^{\operatorname{ess\,osc}\langle v-v_1,S\rangle/2}
\operatorname{rayTail}_{v_1}(r).
\]
The factor is bounded on compact sets of \(v\).

For an explicit interior path, approximate successive finite segments of the face ray at increasing normal depths. Choose depths so that:

- horizontal length errors are summable;
- vertical adjustment costs, bounded using `fisherDist_ray_le_rayTail`, are summable.

The resulting locally piecewise-\(C^1\) interior path has finite length and the required endpoint. This is also a direct use of your existing ray infrastructure.

### (c) A multiscale sufficient criterion

There is a clean sufficient criterion, but I would treat it as a later module, not the primary abstraction.

Suppose two bounded nonnegative deficits \(g_1,g_2\) satisfy
\[
A=\{g_1=g_2=0\},\qquad \mu(A)=p>0,
\]
where \(\mu\) is a fixed bounded tilt of \(\nu\). Set
\[
\Phi_i(s,t)=
\int g_i^2e^{-s g_1-t g_2}\,d\mu.
\]
For a staircase path
\[
(s_n,t_n)\to(s_{n+1},t_n)\to(s_{n+1},t_{n+1}),
\]
with both coordinates increasing to infinity, a sufficient condition is
\[
\sum_n\left[
(s_{n+1}-s_n)\sqrt{\Phi_1(s_n,t_n)}
+
(t_{n+1}-t_n)\sqrt{\Phi_2(s_{n+1},t_n)}
\right]<\infty.
\]
Its Fisher length is bounded by \(p^{-1/2}\) times this sum, since the normalising constant is at least \(p\), and variance is bounded by the corresponding second moment.

This becomes a two-dimensional shell criterion by bounding \(\Phi_i\) with the masses of dyadic rectangles in \((g_1,g_2)\), including the zero rows and columns.

For a relative supporting functional on \(A_1\), polyhedrality lets you add a sufficiently large multiple of the first deficit to make it nonnegative on the whole polytope.

This is a useful **sufficient** multiscale test, not a claimed characterisation. Face-chain lifting is the more reusable theorem.

---

## Q2. The global response map

### (i) The variational response should be globally continuous

I would replace the proposed “continuous on faces, jumps across faces” statement by:

> **Closed-mean Hellinger continuity.**  
> Under the charged-polytope assumptions,
> \[
> M\longmapsto Q_M
> \]
> is continuous on the entire closed moment body, both in \(L^1(\nu)\) and in Hellinger distance.

Support loss does not imply a discontinuity: the mass outside the limiting face tends to zero.

There is also a basic geometric issue with the proposed jump: a point in the relative interior of a face cannot be approached by points in its proper subfaces. The meaningful cross-face limit approaches a lower face from larger faces.

#### A proof particularly suited to your Pythagoras theorem

Let
\[
\mathcal I(M)=D(Q_M\Vert\nu).
\]

**1. Polyhedral recovery.** For \(M_n\to M\), polyhedral geometry gives
\[
M_n=(1-\varepsilon_n)M+\varepsilon_n y_n,
\qquad \varepsilon_n\to0,\quad y_n\in K.
\]
In fact, locally one can take \(\varepsilon_n\le C_M\|M_n-M\|\).

Represent \(y_n\) by mixtures of vertices, and realise those mixtures by laws on the charged vertex events. Their entropies are uniformly bounded by
\[
C=\max_{v\text{ vertex}}\log\frac1{\nu\{S=v\}}.
\]
Mixing with \(Q_M\) gives feasible laws \(R_n\) such that
\[
R_n\to Q_M\text{ in }L^1,
\qquad
\limsup_n D(R_n\Vert\nu)\le\mathcal I(M).
\]

**2. Lower semicontinuity.** Identify \(\mathcal I\) with the convex conjugate of log-Laplace on the closed polytope. The boundary equality follows by normal tilting; finite Fisher length is not needed. Thus \(\mathcal I\) is lower semicontinuous, and the recovery argument proves continuity.

**3. Pythagoras.**
\[
D(R_n\Vert Q_{M_n})
=
D(R_n\Vert\nu)-\mathcal I(M_n)\to0.
\]
Pinsker, followed by the triangle inequality, gives
\[
Q_{M_n}\to Q_M\quad\text{in }L^1.
\]

This produces a beautiful theorem:

> The closed moment polytope is homeomorphic to the Hellinger closure of the interior exponential family.

It is a **compact response compactification**, whether or not every point is Fisher-accessible.

For comparison, if \(R=Q(\cdot\mid B)\), then, with unscaled root-\(L^2\) Hellinger distance,
\[
H(Q,R)^2=2-2\sqrt{Q(B)},\qquad
\operatorname{TV}(Q,R)=1-Q(B).
\]
For an arbitrary \(R\) supported on \(B\), these are lower bounds, not generally equalities. They describe conditioning, not a discontinuity of \(M\mapsto Q_M\).

### (ii) Response curves: correct speed, but no general monotone information

For the square-root embedding,
\[
\left\|\frac{d}{dt}\sqrt{P_{\theta_t}}\right\|_{L^2(\nu)}
=\frac12|\theta'_t|_{F,\theta_t}.
\]
Thus the speed is Fisher speed in the Fisher–Rao normalisation \(2H\), and half Fisher speed in unscaled Hellinger geometry.

Finite response length gives a completion endpoint. Separately, global Hellinger continuity would give:

> If \(m(\rho_t)\to M\), then \(Q_{m(\rho_t)}\to Q_M\) in Hellinger, even when Fisher accessibility has not been established.

That is the clean separation between response convergence and response length.

Information is **not** generally monotone. A small counterexample uses three groups:
\[
\nu=(1/2,\,2/5,\,1/10),\quad
S=(0,1,0),\quad h=(0,1,2).
\]
Then
\[
m_t=\frac{(2/5)e^t}{1/2+(2/5)e^t+(1/10)e^{2t}}.
\]
It initially increases from \(2/5\), attains a maximum, and returns to \(2/5\) at \(t=\log5\). Consequently
\[
\mathcal I(m_t)
=
D\!\left(\operatorname{Bern}(m_t)\Vert
\operatorname{Bern}(2/5)\right)
\]
first becomes positive and later returns to zero.

If desired, realise these weights by a uniform featureless law on ten atoms.

What *is* always monotone is the data information:
\[
\frac d{dt}D(\rho_t\Vert\nu)=t\,\operatorname{Var}_{\rho_t}h\ge0
\quad(t\ge0).
\]
For response information,
\[
\frac d{dt}\mathcal I(m_t)
=-\langle\theta_t,m'_t\rangle,
\]
whose sign needs an additional alignment hypothesis.

### (iii) The precise ray-plus-log budget

Write, on the eventual interval,
\[
v(t)=|\theta'_t|_F,\quad
c(t)=\|\operatorname{dataCov}(t)\|,\quad
r(t)=\operatorname{depth}(t),\quad
a(r)=\sqrt{\operatorname{raySpeedSq}(r)}.
\]
Assume your estimates are
\[
v\le C_1c+C_2a(r)|r'|,
\]
\[
a(r)(-r')_+\le C_3\bigl(H-\mathbb E_{\rho_t}h\bigr)+C_4c,
\]
with \(r(t)\to\infty\) and \(a\) integrable at infinity.

The exact bookkeeping identity is
\[
\int_T^\infty a(r)|r'|
=
\operatorname{rayTail}(r(T))
+2\int_T^\infty a(r)(-r')_+.
\]
Therefore
\[
\boxed{
\begin{aligned}
\int_T^\infty v(t)\,dt
\le{}&
(C_1+2C_2C_4)\int_T^\infty c(t)\,dt\\
&+C_2\,\operatorname{rayTail}(r(T))\\
&+2C_2C_3\int_T^\infty
\bigl(H-\mathbb E_{\rho_t}h\bigr)\,dt .
\end{aligned}}
\]

For \(\rho_t\propto e^{th}\nu\), if \(H=\operatorname{ess\,sup}h\) and \(\nu\{h=H\}>0\),
\[
\int_T^\infty(H-\mathbb E_{\rho_t}h)\,dt
=
\log\frac1{\rho_T\{h=H\}}.
\]
Hence the last term is exactly the promised logarithmic penalty.

If the effective statistic has a uniform centred bound \(B\),
\[
c(t)\le B\sqrt{\operatorname{Var}_{\rho_t}h},
\]
giving a data-length budget with coefficient \(B(C_1+2C_2C_4)\).

A coefficient-one “data length plus correction” bound does **not** follow from the supplied estimates. Also, when \(\nu\{h=H\}=0\), the logarithmic term diverges; this sufficient budget then says nothing about finiteness.

### (iv) Package covariance coercivity, not eigenvalues

Let \(U\) be a convex neighbourhood in the relative interior of the moment body. Package
\[
\lambda>0,\qquad
\forall m\in U,\ \forall w\in W,\quad
\operatorname{fisherVar}(\theta(m),w)
\ge\lambda\|w\|^2.
\]

Pull back the straight segment from \(m\) to \(n\). The inverse derivative gives
\[
|\theta'(t)|_F^2
=
\langle m'(t),C_{\theta(t)}^{-1}m'(t)\rangle
\le\lambda^{-1}\|m'(t)\|^2,
\]
and hence
\[
d_F(\theta(m),\theta(n))
\le\frac{\|m-n\|}{\sqrt\lambda}.
\]

If \(B\) bounds the norm of the effective, suitably centred statistic,
\[
\|m(Q)-m(R)\|\le2B\,H(Q,R),
\]
so
\[
d_F(\Phi(Q),\Phi(R))
\le\frac{2B}{\sqrt\lambda}H(Q,R).
\]

Coercivity on inverse-chart points is the right Lean interface. Minimum eigenvalues can later provide witnesses on compact subsets.

### What is the core?

The central object is
\[
\mathcal R:\ Q\longmapsto Q_{m(Q)}.
\]
It is an idempotent response map onto the variational family, with:

- global continuity in Hellinger;
- information-projection characterisation;
- smooth inverse-covariance differential on each open face;
- local metric distortion controlled by covariance comparison;
- Fisher endpoint realisation precisely where accessibility is established.

The next particularly deep differential statement is the **relative-covariance criterion**. For a data curve with score \(g\), put
\[
b=\mathbb E_\rho[(S-m)g].
\]
Then response speed squared is
\[
b^\top C_{Q_m}^{-1}b.
\]
If
\[
C_\rho\preceq\kappa C_{Q_m}
\]
on \(W\), this is at most \(\kappa\,\mathbb E_\rho g^2\). At a matched law, \(\kappa=1\), recovering an orthogonal-projection contraction.

That is the infinitesimal mechanism of “mapping responses across the data manifold.”

I would not yet assert that \(\widehat W\) is the whole face-family union. The justified target is:

> \(\widehat W\) maps injectively and continuously into the compact variational response family; its image is a union of accessible open-face strata.

Showing that the inverse has exactly the proposed face-mass topology is a separate global metric theorem. Uniqueness alone does not establish it.

---

## Q3. Ten next modules

Each is a plausible ≤300-line target **once its stated dependencies exist**; I would keep the geometric and analytic helper lemmas separate.

| Rank | Module | Statement and proof route |
|---|---|---|
| **1** | **`BoundedTiltCompletionAction`** — infrastructure | Bounded tilts act bi-Lipschitzly on \(\widehat W\), and tilt completion laws. Prove density-ratio variance bounds; extend translations and identify laws by Hellinger continuity. |
| **2** | **`TiltedFisherCompactConvergence`** — infrastructure | Hellinger convergence of base laws gives compact-uniform convergence of covariance forms under bounded parameter tilts. Control denominators uniformly; use bounded first and second moments. |
| **3** | **`AccessibleFaceOrbit`** — **deep** | One accessible \(P^A_{v_0}\) gives a canonical nonexpanding \(j_A:W_A\to\widehat W\). Use the completion action; approximate each compact face path by translated interior paths. |
| **4** | **`FaceCompletionLift`** — **deep** | Extend \(j_A\) to \(\widehat{W_A}\), preserving laws and means. Use uniform extension into a complete target; identify laws along Cauchy representatives. |
| **5** | **`FaceChainAccessibility`** — **deep** | Accessibility through a finite chain of face-family endpoints implies ambient accessibility. Compose face-completion lifts; identify iterated conditioning with the final face family. |
| **6** | **`PolyhedralEntropyRecovery`** — geometric infrastructure | Nearby means admit feasible laws converging to \(Q_M\) with entropy limsup at most \(\mathcal I(M)\). Prove the local radial polytope lemma; mix \(Q_M\) with bounded-entropy charged-vertex laws. |
| **7** | **`ClosedMeanResponseContinuity`** — **deep** | \(M\mapsto Q_M\) is globally Hellinger-continuous; its image is the compact Hellinger closure of the family. Combine conjugate lower semicontinuity, recovery, Pythagoras and Pinsker. |
| **8** | **`ResponseLocalMetricControl`** — **deep** | Coercivity gives \(d_F\le\lambda^{-1/2}\|\Delta m\|\), hence local Hellinger Lipschitz response. Pull back straight mean segments using the inverse derivative; integrate the covariance-inverse bound. |
| **9** | **`WeightedDepthVariation`** — infrastructure | Weighted depth variation equals signed ray travel plus twice weighted backtracking. Apply the chain rule to a primitive of ray speed; pass to improper integrals using the ray tail. |
| **10** | **`FacetResponseLengthBudget`** — **deep/application** | Bound eventual response length by covariance length, ray tail and the top-event logarithm. Insert the landed estimates into module 9; evaluate the integrated data gap by log-normaliser differentiation. |

If the immediate priority is the global response map rather than more accessibility, move **6–8 ahead of 3–5**. They deliver a complete closed-polytope law-level theorem without waiting for Fisher existence.

---

## Q4. Sanity and cheap strengthenings

The eight statements are coherent as stated. The most useful refinements are these.

### 1. Remove exposed vertices as arbitrary anchors in face normal forms

If \(a_n\) is invisible on \(W_A\), then
\[
\langle a_n,z-z_0\rangle=0
\]
for every \(z,z_0\in\operatorname{aff}F_A\).

Thus the constant and outside-gap conclusions do not depend on which face anchor is chosen. Keep a charged vertex for proofs needing an atom, but export the geometric theorem with an arbitrary anchor in the face’s affine hull.

Since \(M\in\operatorname{ri}F_A\), its minimal face is \(F_A\); the explicit minimal-face membership should usually be an internal lemma, not a public hypothesis.

### 2. Strengthen vertex gaps to divergence

For every other charged generator \(w\ne M\),
\[
\frac{P_{\theta_n}\{S=w\}}{P_{\theta_n}\{S=M\}}
=
\frac{\nu\{S=w\}}{\nu\{S=M\}}
e^{-\langle\theta_n,w-M\rangle}.
\]
Mass concentration at \(M\) therefore gives
\[
\langle\theta_n,w-M\rangle\to+\infty,
\]
not merely eventual nonnegativity.

### 3. Charge only actual vertices

Charging every member of an arbitrary generating finset is stronger than necessary when the finset contains redundant points. The natural assumption is that every extreme point of the polytope is charged. The cheapest implementation is to pass to a vertex finset once.

### 4. Keep normal-shift bounds, but add bounded-tilt transport

`NormalShiftBoundaryCost` and normal-cone coalescence remain valuable quantitative tools. The biggest cheap conceptual strengthening is not a better constant: it is the completion action of **all bounded tilts**, which turns one boundary endpoint into a whole face family.

### 5. Export the completed projection identity

After global response continuity, every \(x\in\widehat W\) satisfies
\[
Q_x=Q_{\operatorname{meanExt}(x)}.
\]
This follows directly from an interior approximating sequence. It cleanly packages all completed laws as variational responses, independent of the accessibility construction used.

### 6. Keep three endpoint assertions distinct

Future interfaces should distinguish:

1. mean convergence;
2. Hellinger convergence of response laws;
3. finite Fisher response length and its completion endpoint.

The first two become globally linked by closed-mean continuity. The third is the genuinely metric accessibility question. Any endpoint-versus-length equivalence should retain the special hypotheses of the data-path theorem rather than become a generic fact about convergent curves.

**The most beautiful next pair is `FaceCompletionLift` plus `ClosedMeanResponseContinuity`: one explains how finite-length geometry descends through faces; the other shows that the global response law already varies continuously across the entire polytope.**