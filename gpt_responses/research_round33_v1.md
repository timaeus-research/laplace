## 1. Audit

The main structure is correct. I see several convention/hypothesis points worth making explicit, but no substantive obstruction.

### Normalisation and signs

All your formulas are consistent with
\[
A(t,\beta)=\log\!\int e^{-tL_0-\beta\cdot R}\,\pi\,d\mu,
\qquad
J(t,M)=\sup_\beta\{-\beta\cdot M-A(t,\beta)\},
\]
where \(\beta=ta\). Then
\[
\nabla_MJ=-\beta,\qquad \partial_t\beta|_M=-b,
\]
so the mixed Hessian entry of \(J\) is indeed **\(+b\)**:
\[
D^2J=
\begin{pmatrix}
-\sigma^2&b^\top\\
b&C^{-1}
\end{pmatrix}.
\]
Thus “\(\partial_t\beta=-b\)” and the displayed block Hessian agree.

Two naming caveats:

* At fixed \(t>0\), \(P_{t,0}\propto e^{-tL_0}\pi\) is the **baseline posterior**, not generally the normalised prior. The genuine prior occurs at \(t=0\).
* Along the fixed-\(a\) annealing ray, the decreasing energy is \(\mathbb E_t[L_a]\), with derivative \(-\operatorname{Var}_t(L_a)\). Your statements with \(L_0\) are the \(a=0\) instance.

The constrained-response, regression-residual, and third-cumulant formulas otherwise have the correct factors and signs.

### (a) Slice-map injectivity: feature nondegeneracy suffices

Yes. For the signed natural-coordinate convention above,
\[
D\,\mathrm{sliceMap}(t,\beta)[\tau,u]
=
\bigl(\tau,\,-\tau\,\operatorname{Cov}(R,L_0)-Cu\bigr).
\]
A kernel vector has \(\tau=0\), hence \(Cu=0\). Feature nondegeneracy gives \(u=0\).

There is **no need for nondegeneracy of the enlarged family \((L_0,R)\)**. In particular, this works when \(L_0\) is affine in \(R\), including when the residual variance vanishes identically.

Indeed, in \((t,\beta)\)-coordinates the same local argument works at **every real \(t\)**. Restricting to \(t>0\) is needed for your original programme and the conversion \(a=\beta/t\), not for this slice derivative.

### (b) Negative temperatures

With bounded losses and a finite, nonzero prior measure, the annealing family and its differential identities work for all \(t\in\mathbb R\).

Even the displayed integrated inequalities remain valid for **every real \(T\)** if integrals are oriented:
\[
\int_0^T\operatorname{Var}_u(L_0)\,du=E(0)-E(T),
\]
\[
\mathrm{KL}(P_T\|\bar\pi)
=\int_0^T u\operatorname{Var}_u(L_0)\,du
\le T\bigl(E(0)-E(T)\bigr).
\]
For \(T<0\), both factors on the right are negative, so their product is nonnegative. The observable-response inequality also survives with oriented integrals.

The exception is terminology: a **length** should use an unoriented interval or an absolute speed integral, not a potentially negative integral from \(0\) to \(T\).

### (c) Data-mixture hypotheses

Uniform boundedness plus measurability and probability measures is an excellent standing interface. I would not weaken it merely for elegance.

The cleaner *abstract* interface is:

> Data perturbations determine bounded losses, and the loss map is affine, with its linear part taking admissible data directions into \(L^\infty\).

For a single segment, it is enough that \(L_{\nu_0},L_{\nu_1}\) are bounded measurable and that the affine loss identity holds. The uniformly bounded kernel is a convenient theorem producing this interface.

Two pitfalls when weakening it:

1. Pointwise-in-\(z\), almost-everywhere-in-\(x\) bounds may have varying null sets. Use a common domination statement or an appropriate Fubini argument.
2. Joint measurability of a bounded kernel does **not automatically** justify treating \(z\mapsto\ell(\cdot,z)\) as a Bochner-integrable \(L^\infty\)-valued map.

For Lean, the scalar kernel construction followed by the bounded-loss interface is likely cleaner than starting with Bochner integration into \(L^\infty\).

---

## 2. Re-ranking

My ranking by **substantive value to this programme**, rather than smallest implementation cost, is:

| Rank | Package | Reason |
|---|---|---|
| **1** | **Boundary geometry and ray endpoints** | Completes the response map beyond its interior chart and resolves the important, false-in-general boundary blow-up intuition. |
| **2** | **Effective feature space \(N^\perp\)** | Removes artificial nondegeneracy assumptions and identifies the intrinsic response dimension. |
| **3** | **Unified temperature–data response and integrability** | Gives the programme its clean global organising theorem; mostly assembly now. |
| **4** | **Exact KL three-point identity / mixed Pythagoras** | High explanatory value, low proof cost, and a precise expression of dual flatness. |
| **5** | **Cramér theorem for empirical response** | Gives the dual potential a second, operational meaning as the fluctuation cost. |
| **6** | **Second-order loss surface** | A beautiful small sequel, now directly accessible from `ThirdCumulant`. |
| **7** | **Thermodynamic length and metric bounds** | Useful, but avoid promising ordinary geodesics where only affine-connection geodesics exist. |
| **8** | **Wall-band instance / two-term wall law** | Valuable asymptotics, but less foundational than completing the global response geometry. |

**Scheduling qualification:** I would probably ship ranks 3, 4, and 6 as short consolidation modules while building rank 1. They are now inexpensive.

### 1. Boundary: distinguish three different assertions

Let
\[
q=P_{t,0},\qquad K=\text{essential moment body},\qquad
\mathcal I(y)=I_t(y)+A_t(0)
\]
on the interior, and extend \(\mathcal I\) by its full Legendre-transform definition.

Then:

* \(\overline{\operatorname{range}m}=K\) follows immediately from your interior-range theorem.
* \(\mathcal I\) is a **good rate function**: its sublevel sets are compact.
* It does **not** follow that \(\mathcal I\to+\infty\) at every boundary point.

The simplest counterexample is a Bernoulli statistic:
\[
R\in\{0,1\},\qquad q(R=1)=p.
\]
Then
\[
\mathcal I(1)=-\log p,\qquad
\mathcal I(0)=-\log(1-p),
\]
both finite.

The relevant distinction is **mass on supporting faces**. If
\[
F=\{x:v\cdot R(x)=\alpha\},
\qquad
\alpha=\operatorname*{ess\,inf}_q v\cdot R,
\]
then:

* if \(q(F)>0\), the minimizing ray converges to \(q(\,\cdot\,|F)\);
* if \(q(F)=0\), the ray concentrates arbitrarily close to the supporting face but cannot converge to an absolutely continuous conditional law on that face, and its KL cost diverges.

More generally, if a supporting hyperplane through a boundary response \(y\) has zero \(q\)-mass, then \(\mathcal I(y)=+\infty\).

So: **goodness is automatic here; boundary blow-up is an additional geometric–measure-theoretic property.**

### 2. \(N^\perp\): the intrinsic theorem

Define
\[
N=\{v:v\cdot R\text{ is }q\text{-a.e. constant}\}.
\]
The crisp package is:
\[
\ker C_a=N,\qquad
P_{a+n}=P_a\quad(n\in N),
\]
and
\[
m|_{N^\perp}:N^\perp\xrightarrow{\;\cong\;}\operatorname{ri}K,
\]
with smooth inverse in the appropriate affine-space sense.

For implementation, I would prefer **restriction to \(N^\perp\)** over beginning with a quotient. It has canonical representatives, an inherited inner product, and ordinary finite-dimensional linear algebra.

Feature-reparametrisation invariance is a good corollary, but state it for affine changes that are **invertible on the effective feature space**. An arbitrary matrix \(A\) may discard information; \(R\mapsto AR+c\) is not automatically geometry-preserving.

### 3. Unified two-axis response

For a differentiable data path with loss \(L_s\), write \(D_s=\partial_sL_s\). For a fixed observable \(\phi\),
\[
d\mathbb E[\phi]
=
-\operatorname{Cov}(\phi,L_s)\,dt
-t\operatorname{Cov}(\phi,D_s)\,ds.
\]
The mixed derivative is
\[
\partial_s\partial_t\mathbb E[\phi]
=
-\operatorname{Cov}(\phi,D_s)
+t\,\kappa_3(\phi,L_s,D_s)
=
\partial_t\partial_s\mathbb E[\phi].
\]

The partition potential satisfies
\[
d\log Z=-\mathbb E[L_s]\,dt-t\mathbb E[D_s]\,ds,
\]
and
\[
\partial_s\partial_t\log Z
=-\mathbb E[D_s]+t\operatorname{Cov}(L_s,D_s).
\]

This is exactly the desired integrability statement. One conceptual refinement: **\(\log Z\) is the potential for the loss-conjugate one-form; each observable expectation is itself a potential for its response one-form.**

I would first formalise a finite affine family of data losses. A global differential-geometric structure on all probability measures is unnecessary and introduces boundary/tangent-space complications.

### 4. Dual flatness: land the exact three-point identity

At fixed \(t\), with \(m_a=m(t,a)\),
\[
\begin{aligned}
\mathrm{KL}(P_a\|P_c)
={}&\mathrm{KL}(P_a\|P_b)
+\mathrm{KL}(P_b\|P_c)\\
&+t\,(c-b)\cdot(m_a-m_b).
\end{aligned}
\]
This is the cleanest Lean-friendly core of mixed Pythagoras.

If
\[
(c-b)\cdot(m_a-m_b)=0,
\]
the KL Pythagorean equality follows. This pairing is exactly Fisher orthogonality between the natural-coordinate leg and the mean-coordinate leg at \(b\).

It captures the intended geometry without requiring an entire formal theory of affine connections.

### 5. Cramér

Yes: for iid \(X_j\sim P_{t,0}\),
\[
\bar R_n=\frac1n\sum_{j=1}^nR(X_j)
\]
has rate
\[
\mathcal I(y)
=\sup_\lambda\left\{
\lambda\cdot y-\log\mathbb E_q e^{\lambda\cdot R}
\right\}.
\]
On the interior this is \(I_t(y)+A_t(0)\).

The important formal point is that the LDP needs the **extended rate on all response space**, not merely the interior-defined dual potential. Boundary theory therefore provides a useful foundation rather than being an unrelated embellishment.

### 6. Second-order loss surface: particularly clean formulas

Let
\[
b=C^{-1}\operatorname{Cov}(R,L_0),\qquad
H=L_0-b\cdot R,\qquad q_d=C^{-1}d.
\]
All quantities below are evaluated at fixed \((t,M)\). Then
\[
D_M^2h[d,e]
=
\kappa_3(R_{q_d},R_{q_e},H),
\]
\[
\partial_tD_Mh[d]
=
-\kappa_3(R_{q_d},H,H),
\]
and, as a pleasing completion,
\[
\partial_t^2h=\kappa_3(H,H,H).
\]

The derivatives of the regression coefficients disappear where needed because
\[
\operatorname{Cov}(H,R)=0.
\]
These formulas also show why no general convexity assertion for \(h\) in \(M\), or in \(t\), should be expected.

### 7. Length: what is actually true

The Fisher speeds are
\[
\sqrt{\operatorname{Var}(L_0)}
\quad\text{along annealing},\qquad
t\sqrt{\operatorname{Var}(D)}
\quad\text{along an affine data segment}.
\]
For \(T\ge0\),
\[
\left(\int_0^T\sqrt{\operatorname{Var}_u(L_0)}\,du\right)^2
\le T\bigl(E(0)-E(T)\bigr).
\]
For any observable,
\[
|\Delta\mathbb E[\phi]|
\le \int \sqrt{\operatorname{Var}(\phi)}\,ds_{\rm Fisher}.
\]

Natural-coordinate segments are \(e\)-geodesics; mean-coordinate segments are \(m\)-geodesics. **Neither is generally a length-minimising Levi–Civita geodesic.**

A genuine metric statement is the ambient Fisher–Rao lower bound:
\[
\operatorname{Length}_{\rm Fisher}(P_s)
\ge
2\arccos\!\int\sqrt{dP_0\,dP_1},
\]
under the convention \(g=\mathbb E[(d\log p)^2]\). The exponential-family intrinsic distance can be larger.

---

## 3. Top pick: a Lean-friendly boundary-ray package

I would begin with a scalar tilt theorem, then instantiate it with \(V=R_v\). This avoids entangling the first proof with convex-body infrastructure.

### Base definitions

Let \(q\) be a probability measure, \(V\) bounded measurable, and
\[
\alpha=\operatorname*{ess\,inf}_qV,\qquad W=V-\alpha\ge0\quad q\text{-a.e.}
\]
Define
\[
Z_\lambda=\mathbb E_q[e^{-\lambda W}],
\qquad
dq_\lambda=Z_\lambda^{-1}e^{-\lambda W}\,dq,
\qquad \lambda\ge0.
\]

### The initial theorem ladder

**A. Endpoint and exponential scale**
\[
\mathbb E_{q_\lambda}[V]\longrightarrow\alpha,
\qquad
-\frac1\lambda\log\mathbb E_q[e^{-\lambda V}]
\longrightarrow\alpha.
\]

**B. Exact face mass**
\[
Z_\lambda\longrightarrow q(V=\alpha).
\]

**C. Positive-mass face**

If \(p=q(V=\alpha)>0\), then for every bounded measurable \(\phi\),
\[
\mathbb E_{q_\lambda}[\phi]
\longrightarrow
\frac1p\int_{\{V=\alpha\}}\phi\,dq.
\]
Moreover,
\[
\mathrm{KL}(q_\lambda\|q)\longrightarrow-\log p.
\]

**D. Zero-mass face**

If \(q(V=\alpha)=0\), then
\[
\mathrm{KL}(q_\lambda\|q)\longrightarrow+\infty.
\]

Instantiate \(\lambda=ts\), \(V=R_v\), \(q=P_{t,0}\). This yields the several-dimensional supporting-face theorem along \(a=sv\).

### Main pitfall

**Do not infer the entropy limit merely from the normaliser limit.**

Indeed,
\[
\mathrm{KL}(q_\lambda\|q)
=-\lambda\,\mathbb E_{q_\lambda}[W]-\log Z_\lambda.
\]
When \(p>0\), prove separately
\[
\lambda\,\mathbb E_{q_\lambda}[W]\to0
\]
using bounded domination of \(\lambda W e^{-\lambda W}\).

When \(p=0\), the two displayed terms can compete. A robust proof uses concentration near the face and the binary KL lower bound for the events
\[
\{W\le\varepsilon\}.
\]
Their \(q_\lambda\)-probability tends to \(1\), while their \(q\)-probability tends to \(0\) as \(\varepsilon\downarrow0\).

Finally, use the **essential** endpoint and essential moment body throughout. A null-set feature value must not create a fictitious boundary face.

This package would add something genuinely new: not just that the interior response chart exists, but precisely how it terminates, when a boundary posterior exists, and when reaching the boundary costs infinite information.