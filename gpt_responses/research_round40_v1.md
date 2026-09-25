## 1. Audit

The principal identities look correct. The important qualifications concern the quantifiers in the LD lower bound, the reference measure used for boundary mass, and what “finite at the boundary” means.

### 1.1 Profile geometry

With the raw log-partition convention
\[
A(t,\eta)=\log\int e^{-tL_0-\eta\cdot R}\,d\pi,
\qquad
I_t(M)=\sup_\eta\{-\eta\cdot M-A(t,\eta)\},
\]
the signs in
\[
J(\mu(\theta))+tu(\theta)-I_t(M)
 =\mathrm{KL}(P_\theta\Vert P_{t,a}),
\qquad M=m_t(a),
\]
are correct.

Consequently:

- \(I_t(M)\le J(\mu)+tu\) on the full-mean fibre over \(M\);
- equality holds at the temperature-\(t\) lift;
- the stated Pythagoras identity holds whenever the feature responses agree;
- the normalized sampling rate is
  \[
  \mathcal I_t(M):=I_t(M)+A_t(0),
  \]
  and
  \[
  \mathcal I_t(m_t(a))
  =\mathrm{KL}(P_{t,a}\Vert P_{t,0}).
  \]

The Pythagoras identity needs equality of **feature means**, not equality of full means. Indeed, \(\log(dP_{t,a}/dP_{t,b})\) is affine in \(R\).

Likewise,
\[
D_\mu\mathcal S=\theta,\qquad D_\mu^2\mathcal S=-G_\theta^{-1}
\]
have the correct signs for the negative-exponent convention. Normalizing \(\pi\) only adds a constant to \(\mathcal S\).

### 1.2 Schur complement

Write
\[
G=\begin{pmatrix}\sigma^2&c^\top\\c&V\end{pmatrix},
\qquad
b=V^{-1}c,
\qquad
H=L_0-b\cdot R,
\qquad
\delta=\operatorname{Var}(H).
\]
Then
\[
\delta=\sigma^2-c^\top V^{-1}c
\]
and
\[
d^\top G^{-1}d
=d_R^\top V^{-1}d_R+
 \frac{(d_0-b\cdot d_R)^2}{\delta}
\]
are correct.

The `hjnd` witness is exactly
\[
(1,-b).
\]
It is nonzero because its first coordinate is \(1\), and
\[
(1,-b)^\top G(1,-b)=\operatorname{Var}(H)>0.
\]
Here \(b\) is frozen at the parameter under consideration; there is no differentiation of \(b\) in this argument.

The minimal-lift statement concerns the **mean-coordinate** metric \(G^{-1}\). Its minimum is \(d_R^\top V^{-1}d_R\). In coefficient coordinates, the slice Fisher metric is \(t^2V\), not \(V\) or \(tV\).

### 1.3 Wall ray

Along
\[
a_\lambda=a-\frac{\lambda}{t}u,
\]
the density acquires the factor \(e^{\lambda R_u}\), so the direction and signs are correct.

The Bhatia–Davis estimate follows from
\[
-\|R_u\|_\infty\le R_u\le\beta:
\qquad
\operatorname{Var}(R_u)
\le(\beta-\mathbb ER_u)(\mathbb ER_u+\|R_u\|_\infty)
\le(\beta+\|R_u\|_\infty)(\beta-\mathbb ER_u).
\]

**An everywhere upper bound is stronger than necessary.** The measure-invariant hypotheses are:

\[
R_u\le\beta\quad\pi\text{-a.e.},
\qquad
\pi(R_u>\beta-\varepsilon)>0\quad(\varepsilon>0).
\]

These say that \(\beta\) is the essential supremum. Under the usual finite, positive exponential densities, prior-positive sets and posterior-positive sets coincide.

Two consequences for the next layer:

1. Define the moment body using the **essential range**, not arbitrary values on prior-null points.
2. An everywhere-bound theorem is a perfectly good first implementation, but the geometric theorem should preferably have an a.e. interface.

Also, \(G(u,u)\to0\) should identify the embedding: for the full covariance matrix this means
\[
G((0,u),(0,u))\to0.
\]
It does not assert convergence of the entire matrix to a singular matrix unless matrix convergence is separately established.

### 1.4 LD bounds

The upper-bound architecture is sound. Bounded features eliminate the need for a separate exponential-tightness argument.

The lower bound needs the explicit quantifiers:
\[
\forall\delta>0,\quad \exists N,\quad \forall n\ge N,\quad
P_a^{\otimes n}(\bar R_n\in G)
\ge e^{-n(\mathrm{KL}(P_b\Vert P_a)+\delta)}.
\]

It is generally **not** an all-\(n\) assertion: lattice effects alone rule that out. The change-of-measure proof first produces an exponential factor times a tilted probability tending to \(1\); the latter is absorbed into the \(\delta\)-slack.

For a baseline \(P_{t,a}\), the corresponding rate is
\[
\mathcal I_{t,a}(M)
=I_t(M)+ta\cdot M+A_t(a).
\]
Thus \(I_t+A_t(0)\) is specifically the rate for sampling from \(P_{t,0}\).

---

## 2. Where the remaining depth lies

### Ranking

1. **Complete the rate function on the whole moment body, and close Cramér.** Include the exposed-face entropy decomposition as the boundary interpretation.
2. **Temperature compatibility at fixed response.** This makes the slices into one thermodynamic object rather than a collection of geometries.
3. **Dual affine connections through the cubic tensor.** A clean synthesis of the already-landed bending and duality.
4. **Fisher lengths of the two journeys.** The common-energy identity is more canonical than a proposed ordering.
5. **Full-geometry stability instantiation.** Useful completion, but lower conceptual novelty.

The largest remaining gap is now **domain completion**, not another interior differential identity. The interior programme is unusually complete; its natural next capstone is to say exactly what happens at every attainable, unattained, and boundary response.

## 3. Top pick: whole-body rate geometry and Cramér

Let \(Q=P_{t,0}\), and let
\[
K=\overline{\operatorname{conv}}(\operatorname{ess\,ran}_Q R).
\]
Work in the visible affine hull if necessary; under feature nondegeneracy this is the ambient feature space.

### A. The canonical extended rate

Define
\[
\Lambda(q)=\log\mathbb E_Q e^{q\cdot R},
\qquad
\mathcal I(M)=\sup_{q\in\mathbb R^d}
 \{q\cdot M-\Lambda(q)\}.
\]

This is the right extended object. It satisfies
\[
\mathcal I(M)=I_t(M)+A_t(0)\quad(M\in\operatorname{int}K),
\qquad
\mathcal I(M)=+\infty\quad(M\notin K).
\]

**Those two clauses do not determine the boundary values.** Assigning \(+\infty\) to all of \(\partial K\) is generally wrong.

You do not need an extended-real *conjugate API*. A thin bespoke definition suffices:

- each Chernoff score \(q\cdot M-\Lambda(q)\) is real;
- take their supremum in an extended codomain;
- prove the few required order lemmas directly.

Because the \(q=0\) score is \(0\), an `ENNReal` supremum of the nonnegative parts is also a viable implementation. This avoids negative extended values entirely.

### B. Geometry and attainment

Prove:

1. \(K\) is compact and convex.
2. \(\mathbb E_PR\in K\) for every \(P\ll Q\).
3. \(\mathcal I\ge0\), is convex and lower semicontinuous, and has compact sublevel sets.
4. Every \(M\in\operatorname{int}K\) is a tilted mean.
5. At that mean,
   \[
   \mathcal I(M)=\mathrm{KL}(P_{t,a}\Vert Q).
   \]

Item 4 deserves an explicit audit: a local inverse chart, injectivity, and openness do **not** by themselves prove that the image is all of \(\operatorname{int}K\). If that surjectivity has not landed, it is part of this capstone.

A standard proof minimizes
\[
q\longmapsto\Lambda(q)-q\cdot M.
\]
For interior \(M\), compactness of the unit sphere and positive mass in suitable support caps give coercivity.

### C. Radial interior approximation

Fix \(M_*\in\operatorname{int}K\), preferably \(M_*=\mathbb E_QR\), and set
\[
M_\varepsilon=(1-\varepsilon)M+\varepsilon M_*.
\]
For \(M\in K\) and \(0<\varepsilon\le1\),
\[
M_\varepsilon\in\operatorname{int}K.
\]

If \(\mathcal I(M)<\infty\), convexity gives
\[
\mathcal I(M_\varepsilon)
\le(1-\varepsilon)\mathcal I(M)+\varepsilon\mathcal I(M_*).
\]
Lower semicontinuity then yields
\[
\mathcal I(M_\varepsilon)\longrightarrow\mathcal I(M).
\]
The same convergence holds in the extended sense when \(\mathcal I(M)=+\infty\).

This is precisely the missing open-set step: if \(M\in G\) and \(G\) is open, then \(M_\varepsilon\in G\) for small \(\varepsilon\).

### D. Full Cramér theorem

For closed \(F\) and open \(G\),
\[
\limsup_{n\to\infty}\frac1n
 \log Q^{\otimes n}(\bar R_n\in F)
\le-\inf_F\mathcal I,
\]
\[
\liminf_{n\to\infty}\frac1n
 \log Q^{\otimes n}(\bar R_n\in G)
\ge-\inf_G\mathcal I.
\]

If extended logarithms are inconvenient, the following eventual-exponential interface is enough:

- if \(c<\inf_F\mathcal I\), eventually
  \[
  Q^{\otimes n}(\bar R_n\in F)\le e^{-nc};
  \]
- if \(c>\inf_G\mathcal I\), eventually
  \[
  Q^{\otimes n}(\bar R_n\in G)\ge e^{-nc}.
  \]

It exposes exactly the usable content and handles zero probabilities cleanly.

### E. Exposed faces and the entropy cost of a wall

Let
\[
F=\{x\in K:u\cdot x=\beta\},
\qquad
\beta=\sup_{x\in K}u\cdot x.
\]
Then
\[
u\cdot M\le\beta\qquad(M\in K).
\]

More substantially, any law with mean in \(F\) must be supported on \(R^{-1}(F)\): a nonnegative random variable with zero expectation vanishes a.e.

Write
\[
p_F=Q(R\in F).
\]
If \(p_F=0\), then
\[
\mathcal I(M)=+\infty\qquad(M\in F).
\]
If \(p_F>0\), let \(Q_F=Q(\,\cdot\mid R\in F)\). Then
\[
\boxed{\quad
\mathcal I(M)=-\log p_F+\mathcal I_F(M),
\qquad M\in F,
\quad}
\]
where \(\mathcal I_F\) is the mean rate under \(Q_F\).

This is the useful missing depth: **the boundary inherits a lower-dimensional rate geometry, with an entry cost \(-\log p_F\).**

One route is the entropy representation
\[
\mathcal I(M)
=\inf_{\nu:\,\int x\,d\nu=M}
 \mathrm{KL}(\nu\Vert Q_R),
\]
on feature laws. Using feature laws avoids unnecessary assumptions about disintegration on the original sample space.

### F. The precise blow-up criterion

The global assertion
\[
\mathcal I(M_n)\to+\infty
\quad\text{whenever }M_n\in\operatorname{int}K,\ 
\operatorname{dist}(M_n,\partial K)\to0
\]
holds **iff every proper exposed face has zero \(Q\)-mass**.

The mechanism is:

- zero mass on every supporting face gives infinite rate at every boundary point;
- lower semicontinuity and compactness give uniform divergence toward the boundary;
- a positive-mass face has at least one finite-rate boundary point—its conditional mean—and radial approximation supplies a bounded-rate interior approach.

But the pointwise formulation needs care:

> Positive mass on a face does not imply finite rate at every point of that face, nor bounded rate along every approach to it.

The conditional rate \(\mathcal I_F\) may itself diverge at the boundary of its own moment body.

### G. Upgrade the wall ray to conditional convergence

For the ray based at \(P_{t,a}\):

- if the top face has positive mass, the ray converges in total variation to
  \[
  P_{t,a}(\,\cdot\mid R_u=\beta);
  \]
- if it has zero mass, the mean still approaches the supporting face and the normal variance vanishes, but there is no such absolutely continuous conditional limit.

In the positive-mass case,
\[
\mathrm{KL}(P_{t,a_\lambda}\Vert P_{t,0})
\longrightarrow
\mathrm{KL}\!\left(
P_{t,a}(\,\cdot\mid R_u=\beta)\Vert P_{t,0}
\right).
\]
In the zero-mass case this KL diverges to \(+\infty\).

This gives theorem VI an exact probabilistic interpretation, not merely metric degeneration.

### Main pitfalls

- Use the actual essential moment body, not the feature bounding box.
- Use relative interior/boundary in the degenerate case.
- Separate interior finite-tilt attainment from boundary finite-rate attainment.
- Positive face mass gives a conditional problem, not automatic finiteness everywhere.
- Keep \(\mathcal I_t=I_t+A_t(0)\) distinct from the raw dual potential.
- Preserve the “eventually” quantifier in both LD interfaces.

---

## 4. The other candidates

### Temperature compatibility: the next differential capstone

At fixed response \(M\), write \(\eta(t)=t\,a_t(M)\), and let \(c=\operatorname{Cov}(R,L_0)\). Then
\[
\eta'(t)=-V^{-1}c=-b,
\]
\[
\boxed{\quad
\partial_t I_t(M)=u_t(M),\qquad
\partial_t^2I_t(M)=-\delta_t(M).
\quad}
\]

Thus \(I_t(M)\) is strictly concave in \(t\) under `hjnd`. The fixed-response full-mean velocity is
\[
\frac d{dt}(u_t(M),M)=(-\delta,0),
\]
while the natural velocity is \((1,-b)\), and its Fisher energy is exactly \(\delta\).

There is also a particularly clean entropy identity:
\[
\frac d{dt}\mathcal S_t(M)=-t\delta_t(M).
\]

**Normalization trap:** for the normalized sampling rate,
\[
\partial_t\mathcal I_t(M)
=u_t(M)-\mathbb E_{P_{t,0}}L_0,
\]
not simply \(u_t(M)\). Its second derivative need not be negative.

### Dual cubic tensor and affine connections

Let \(C\) be the third central-moment tensor of \(R\), and let \(C(x,y)\) denote contraction in two slots.

For an e-journey \(a(s)=a_0+sh\),
\[
m''(s)=t^2C(h,h).
\]

For an m-journey \(m(s)=m_0+sv\), put \(w=V^{-1}v\). Then
\[
\boxed{\quad
a''(s)=\frac1tV^{-1}C(w,w).
\quad}
\]

In \(a\)-coordinates:
\[
\Gamma^{(e)}=0,\qquad
\Gamma^{(m)}(h,k)=-tV^{-1}C(h,k),
\]
and the Levi–Civita connection is their average.

This is a concise formal package: the same cubic tensor measures the failure of each affine journey to be affine in the other chart.

### Journey lengths: common energy before comparison

For endpoints \(a_0,a_1\), responses \(m_0,m_1\), and the standard affine parametrizations,
\[
E_e=E_m
=-t(a_1-a_0)\cdot(m_1-m_0)
=\mathrm{KL}(P_0\Vert P_1)+\mathrm{KL}(P_1\Vert P_0).
\]

Therefore
\[
L_e^2\le \mathrm{Jeffreys}(P_0,P_1),
\qquad
L_m^2\le \mathrm{Jeffreys}(P_0,P_1).
\]

Equality is exactly constant Fisher speed in the corresponding affine parameter:

- e-journey:
  \[
  t^2h^\top V(a(s))h\ \text{is constant};
  \]
- m-journey:
  \[
  v^\top V(a(s))^{-1}v\ \text{is constant}.
  \]

Do not replace this condition by “the family is Gaussian” or “the cubic tensor vanishes everywhere”; those are much stronger.

There is no general ordering supplied by dual flatness between \(L_e\) and \(L_m\). In one response dimension they trace the same interval, so their lengths are equal. For a formal “neither is universally shorter” theorem in higher dimensions, require explicit examples within the bounded-feature class. The **equal-energy theorem** is already exact, canonical, and directly downstream of your paired KL integrals.

---

## 5. Note structure

**Consolidate now, but make it a structural pass rather than another prose rewrite.**

At roughly fifty Lean paragraphs, navigation and dependency visibility are already mathematical concerns. Waiting for the next capstone risks hiding the distinction between interior geometry and completed rate geometry.

Your proposed order is good, with two adjustments:

1. distinguish ambient full geometry from fixed-temperature slices early;
2. reserve a final section explicitly for completion at the boundary.

A workable spine is:

1. **Model, visible quotient, and charts**
2. **Covariance metric and dual potentials**
3. **Journeys, cubic response, and stability**
4. **Profiling and conditioning geometry**  
   Pythagoras, contraction, Schur minimal lift
5. **Temperature compatibility**
6. **Sampling: fluctuation–response and LD**
7. **Moment body, walls, and completed rate geometry**

Add a small dependency table recording for each bundle:

- coordinates and reference measure;
- local versus global hypotheses;
- nondegeneracy required;
- finite/interior versus extended/boundary status.

Keep the seven-theorem overview as the conceptual front door. The catalogue should be the dependency-organized back door.

**Recommendation:** consolidate the architecture now; then land the whole-body rate/Cramér bundle, with conditional face geometry as its interpretation. That closes the largest remaining conceptual gap between the beautiful interior atlas and the actual boundary of the data-response manifold.