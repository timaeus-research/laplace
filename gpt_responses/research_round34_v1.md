My recommendation is to **close the second-order loss surface next, but formulate it as a residual third-cumulant theorem**. This gives a particularly clean answer to the PI’s question: covariance controls the first response; a third cumulant of the part of the loss unexplained by the features controls its curvature.

Then turn to **reachability by actual data mixtures**. The unrestricted response chart is now largely understood; the next substantive question is which part of it the data manifold actually visits.

## 1. Audit

### Boundary rays

The conclusions are sound under the usual measurability, boundedness, and finite-positive-base-mass assumptions. Three qualifications deserve explicit attention.

**First: your essential-infimum distinction is exactly right.** The assumption
\[
\alpha\le V\quad\text{a.e.}
\]
only makes \(\alpha\) an essential lower bound. It does not imply
\[
\forall\varepsilon>0,\qquad \int_{\{V<\alpha+\varepsilon\}}\pi>0.
\]
Together, these two assumptions characterize \(\alpha\) as the essential infimum, in this finite real-valued setting. Keeping them separate is completely fine—and probably more convenient in Lean than introducing an essential-infimum API.

For example, \(V\equiv1\), \(\alpha=0\), has a zero-mass “face” but no concentration toward that face and no KL divergence. Thus the accessibility hypothesis is essential in `FaceInfinite`.

In the positive-face theorem it is automatic: positive mass on \(\{V=\alpha\}\) gives positive mass in every sublevel neighborhood.

**Second: check the normalization in the concentration bound.** Write
\[
Z_0=\int\pi,\qquad \bar\pi=\pi/Z_0,\qquad
A_\delta=\{V<\alpha+\delta\}.
\]
The standard bound is
\[
q_\lambda(A_\varepsilon^c)
\le
e^{-\lambda\varepsilon/2}
\frac{Z_0}{\int_{A_{\varepsilon/2}}\pi}
=
\frac{e^{-\lambda\varepsilon/2}}
     {\bar\pi(A_{\varepsilon/2})}.
\]
Your displayed \(Z_0/\bar\pi(A_{\varepsilon/2})\) appears to mix normalized and unnormalized conventions. Unless `Z₀` means something different there, audit that factor. Rescaling \(\pi\) should not change the bound.

**Third: the KL identity needs \(r=dq_\lambda/d\bar\pi\).** In particular,
\[
\mathrm{KL}(q_\lambda\Vert\bar\pi)
=
\log Z_0-\log(e^{\lambda\alpha}Z_\lambda)
-\lambda E_{q_\lambda}[V-\alpha].
\]
This makes the positive-face limit transparent.

The zero-face result does **not** by itself identify a limiting posterior: it proves concentration in shrinking energy neighborhoods and divergence of information cost. That is the appropriate general conclusion.

For the feature-ray instantiation, keep the parameter conversion explicit: if
\[
P_{t,a}\propto e^{-t(L_0+a\cdot R)}\pi,\qquad a=sv,
\]
then \(\lambda=ts\). The stated lower-face direction requires \(t>0\).

### `EffectiveFeatures`

The statements are right provided the following conventions are explicit:

- \(N=\{n:n\cdot R\text{ is a.e. constant}\}\), relative to the common base measure;
- all finite-parameter posteriors are equivalent to that base measure;
- \(W\) is a linear complement;
- `range m` means the range over the whole parameter space.

Then \(\ker C=N\), invariance along \(N\), and strict definiteness on \(W\) give the desired identifiability.

There is one important temperature caveat. If \(a\) enters through \(e^{-t a\cdot R}\), then at \(t=0\):

- \(C\) can still have kernel exactly \(N\);
- but \(m(a)\) is constant;
- the Fisher metric in \(a\)-coordinates is \(t^2C=0\).

Thus bijectivity of the restricted response map and positivity of that Fisher metric require \(t\ne0\), normally \(t>0\). No such caveat arises if the coordinates are already natural tilt parameters.

Finally, all “interior of the moment body” statements should use **relative interior in the effective affine hull**, unless full nondegeneracy has been assumed.

## 2. Re-ranking

| Rank | Direction | Why now |
|---|---|---|
| **1** | Second-order loss surface | Small remaining analytic gap; unusually strong invariant conclusion |
| **2** | Reachability by actual data distributions | Directly identifies the portion of the response manifold relevant to the programme |
| **3** | Thermodynamic/Fisher length | Cheap, geometric, and quantitatively interpretable |
| **4** | Global journey theorem | Valuable synthesis, but much of its mathematics is already landed |
| **5** | Chernoff and compact-set large-deviation upper bounds | Useful operational interpretation; avoid claiming a false finite-\(n\) closed-set bound |
| **6** | Walls/stratification | Best pursued through actual-data polytopes and exposed-face geometry, rather than as an isolated theory |

### The second-order obstruction is weaker than it looks

You cannot simply differentiate \(C_tb_t=c_t\) before establishing differentiability of \(b\). But neither an IFT nor a general inverse-differentiation theorem is necessary.

The cleanest elementary route is:

1. prove **continuity** of \(C_t^{-1}\), locally where \(\det C_t\ne0\);
2. use the exact identity
   \[
   b_{t+h}-b_t
   =
   C_{t+h}^{-1}
   \bigl[(c_{t+h}-c_t)-(C_{t+h}-C_t)b_t\bigr];
   \]
3. pass to the difference quotient.

This proves
\[
\dot b=C^{-1}(\dot c-\dot Cb)
\]
using only continuity of the inverse. If that continuity API is inconvenient, `adjugate / det` supplies it through polynomial continuity.

**Cramer differentiation is also valid**, but I would first try this continuity-plus-difference-identity route: less differentiation machinery, and better reuse.

Moreover, the temperature curvature of the loss surface needs only continuity of \(b\), not differentiability; see below. A genuine envelope theorem does not assume differentiability of the value function as an input—it proves it from suitable hypotheses.

## 3. Top pick: the residual-cumulant Hessian

Use joint natural coordinates
\[
P_{t,\lambda}\propto \exp(-tL_0+\lambda\cdot R)\pi,
\]
then the local mixed chart \((t,M)\), where \(M=E[R]\). Work on effective features so that \(C=\operatorname{Cov}(R,R)\) is invertible.

Define
\[
E=E[L_0],\qquad
c=\operatorname{Cov}(R,L_0),\qquad
b=C^{-1}c,
\]
and the centered regression residual
\[
H=(L_0-E)-b\cdot(R-M).
\]
Thus
\[
E[H]=0,\qquad \operatorname{Cov}(R,H)=0,\qquad
\sigma^2=E[H^2].
\]

### First derivative

For a displacement \(v=(\tau,\mu)\) in \((t,M)\),
\[
dE[v]=-\tau\sigma^2+b\cdot\mu.
\]

The corresponding centered score is
\[
S_v=-\tau H+(C^{-1}\mu)\cdot(R-M).
\]

### The central second-order theorem

For two displacements \(v,w\),
\[
\boxed{\quad D^2E[v,w]=E[H\,S_vS_w].\quad}
\]

This is a compact, coordinate-meaningful description of the entire Hessian. Its blocks are
\[
E_{tt}=E[H^3],
\]
\[
D_ME_t[\mu]
=
-E\!\left[H^2(C^{-1}\mu)\cdot(R-M)\right],
\]
and
\[
D_M^2E[\mu,\nu]
=
E\!\left[
H\,((C^{-1}\mu)\cdot(R-M))
  ((C^{-1}\nu)\cdot(R-M))
\right].
\]

In particular, along fixed-moment annealing,
\[
\boxed{
\frac{dE}{dt}=-\sigma^2,\qquad
\frac{d^2E}{dt^2}=E[H^3].
}
\]

This says exactly what remains after accounting for feature adjustment: **unexplained variance determines the descent; unexplained skewness determines its curvature.** There is no universal sign for the second derivative.

### Lean-friendly staging

I would split this into three small layers.

#### A. A purely finite-dimensional normal-equation lemma

Inputs:

- \(C(t)\) symmetric and invertible near \(t_0\);
- \(C,c\) differentiable at \(t_0\);
- \(C(t)b(t)=c(t)\) near \(t_0\);
- \(b\) continuous at \(t_0\).

Conclusion:
\[
b'(t_0)=C(t_0)^{-1}\bigl(c'(t_0)-C'(t_0)b(t_0)\bigr).
\]

The proof uses the difference identity above. This separates the entire matrix issue from probability.

#### B. An envelope lemma needing no derivative of \(b\)

Let
\[
s(t)=v(t)-c(t)^\top b(t).
\]
Under the same normal equations and symmetry, continuity of \(b\) suffices to obtain
\[
s'=v'-2b^\top c'+b^\top C'b.
\]

An especially convenient exact identity is
\[
\begin{aligned}
s(t+h)-s(t)
={}&\Delta v
-b(t+h)^\top\Delta c
-\Delta c^\top b(t)\\
&+b(t+h)^\top\Delta C\,b(t).
\end{aligned}
\]
Its difference quotient immediately has the required limit.

Instantiate
\[
v=\operatorname{Var}(L_0),\qquad s=\sigma^2.
\]
This bypasses both differentiability of the minimum and differentiability of the minimizer.

#### C. Probabilistic specialization

At fixed \(M\), the score is \(-H\). Hence
\[
C'_{ij}=-\kappa_3(R_i,R_j,H),\quad
c'_i=-\kappa_3(R_i,L_0,H),\quad
v'=-\kappa_3(L_0,L_0,H).
\]
Multilinearity gives
\[
(\sigma^2)'=-\kappa_3(H,H,H).
\]

Land the one-variable theorem first. Then use layer A and the existing mixed chart to package the full Hessian.

**Pitfalls:** use natural feature parameters, stay locally where the effective covariance is invertible, distinguish \(H\) from its uncentered version, and do not infer convexity from the curvature formula. No uniform global eigenvalue lower bound is needed.

## 4. Actual-data reachability: the next major direction

Suppose a finite family of actual data losses has the representation
\[
\ell(\cdot,z_j)=L_0+a_j\cdot R+k_j,
\]
where \(k_j\) is parameter-independent. For mixture weights \(w\in\Delta\),
\[
L_w=L_0+\left(\sum_jw_ja_j\right)\cdot R+\text{constant}.
\]

Thus the allowed coefficients form the polytope
\[
A=\operatorname{conv}\{a_j\}.
\]
Project it to the effective complement \(W\), obtaining \(B\). At fixed positive temperature, the reachable responses are exactly
\[
\boxed{\mathcal R_{\mathrm{data}}=m_t(B).}
\]

This is generally **not** all of \(\operatorname{relint}K\), and generally need not be convex.

With bounded finite-family coefficients, \(B\) is compact, so its response image is compact and remains inside the finite-parameter response range. Except in trivial cases, it cannot equal the whole relative interior of the moment body.

A good first theorem package is:

1. exact reachable-set equality;
2. response identifiability modulo affine mixture fibers and \(N\);
3. compactness of the reachable set;
4. reachability criterion
   \[
   M\text{ reachable}\iff m_t^{-1}(M)\in B.
   \]

This also gives “walls” a concrete meaning: faces of the **effective coefficient polytope** map to curved boundary strata of the reachable response set. These are distinct from infinite-parameter limiting faces of the moment body.

## 5. Length and journey: two useful corrections

### Length

Your annealing bound is immediate:
\[
\left(\int_0^T\sqrt{\operatorname{Var}_u(L)}\,du\right)^2
\le T\bigl(E(0)-E(T)\bigr).
\]

For a general regular path with centered score \(S_s\), Fisher speed
\(v_F(s)=\sqrt{E[S_s^2]}\), and fixed observable \(\phi\),
\[
|\Delta E[\phi]|
\le
\int\sqrt{\operatorname{Var}_s(\phi)}\,v_F(s)\,ds.
\]
Consequently, if \(\operatorname{Var}_s(\phi)\le V\),
\[
\operatorname{Length}_F\ge
\frac{|\Delta E[\phi]|}{\sqrt V}.
\]
For \(\phi\in[a,b]\), this gives \(2|\Delta E[\phi]|/(b-a)\). Very good cheap additions.

### Journey and KL orientation

For \(P_\eta\propto e^{\eta\cdot T}\pi\), let
\(\eta_s=\eta_0+s d\), \(d=\eta_1-\eta_0\). Then
\[
\boxed{
\mathrm{KL}(P_{\eta_1}\Vert P_{\eta_0})
=
\int_0^1 s\,G_{\eta_s}(d,d)\,ds.
}
\]
The weight \(1-s\) gives the **reverse** KL.

For an arbitrary smooth path starting at \(\eta_0\), the exact path-independent form is
\[
\boxed{
\mathrm{KL}(P_{\eta_1}\Vert P_{\eta_0})
=
\int_0^1
G_{\eta_s}(\eta_s-\eta_0,\dot\eta_s)\,ds.
}
\]
This is simply the differential of the endpoint KL potential. Unlike the segment integrand, it need not be pointwise nonnegative.

Also, for \(e^{-t(L_0+a\cdot R)}\), joint natural coordinates are \((-t,-ta)\), **not** \((t,a)\). At \(t=0\), the \(a\)-coordinates collapse. The prior is “maximal entropy” only with the appropriate reference-measure convention.

## 6. Chernoff: change the proposed statement

The finite-\(n\) inequality
\[
P(\bar R_n\in F)\le e^{-n\inf_F I}
\]
is false for general closed sets.

For a symmetric \(\{\!-1,1\}\)-valued variable, take \(n=1\) and
\(F=\{-1,1\}\). Then \(P(F)=1\), while \(\inf_F I=\log2\).

The safe progression is:

1. **halfspace Chernoff**
   \[
   P(u\cdot\bar R_n\ge r)
   \le
   \exp\!\left[-n\sup_{\lambda\ge0}
   \{\lambda r-\Lambda(\lambda u)\}\right];
   \]
2. finite unions, retaining the union-bound factor;
3. compact-set upper bounds with a finite-cover prefactor and a small exponent slack;
4. the asymptotic closed-set upper bound.

With bounded features, all empirical means lie in a fixed compact set, so exponential tightness is essentially automatic. A compact-cover proof can therefore deliver the **full Cramér upper-bound half** without general LDP machinery.

**Bottom line:** land the residual-cumulant Hessian, then restrict the completed ambient geometry to actual-data mixture polytopes. That moves the programme from “all possible exponential tilts” to a precise map of responses genuinely reachable by changing the data.