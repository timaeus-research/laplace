## 1. Audit: items 2–4 are correct, with two important convention qualifications

The qualifications concern **which coordinates `sliceInv` returns** and **what “score” means when discussing Amari connections**.

### A. Unified Hessian

Write
\[
C=\operatorname{Cov}(R,R),\qquad
b=C^{-1}\operatorname{Cov}(R,L_0),\qquad
H=L_0-b\cdot R.
\]
Centering \(H\) is immaterial for the variances and cumulants below. The essential identity is
\[
\operatorname{Cov}(R,H)=0.
\]

For a natural-coordinate path whose **energy score** is \(S\),
\[
\dot C=-\kappa_3(R,R,S),\qquad
\frac d{ds}\operatorname{Cov}(R,L_0)=-\kappa_3(R,L_0,S).
\]
Differentiating \(Cb=\operatorname{Cov}(R,L_0)\) gives exactly
\[
\dot b=-C^{-1}\kappa_3(R,H,S).
\]
Likewise,
\[
\frac d{ds}\operatorname{Var}(H)
=-\kappa_3(H,H,S),
\]
because the contribution from \(\dot H=-\dot b\cdot R\) vanishes by residual orthogonality.

Consequently, for constant chart vectors \(X=(\tau,v)\), \(Y=(\tau',w)\),
\[
Dh[X]=-\tau\operatorname{Var}(H)+v\cdot b
\]
and differentiating this expression along \(Y\) gives
\[
D_Y(Dh[X])
=\kappa_3\!\left(H,\tau H-(C^{-1}v)\cdot R,S_Y\right)
=\kappa_3(H,S_X,S_Y).
\]

**Yes: this is the full ordinary chart Hessian**, provided the gradient formula holds on the chart neighborhood and the gradient map has the asserted differentiability. If the formal theorem only differentiates scalar evaluations along lines, there remains a small distinction between that theorem and a packaged second Fréchet derivative; the mathematical formula is the same, and a differentiable explicit gradient closes the packaging gap.

**State symmetry separately.** It is a cheap, useful public theorem:
\[
D^2h[X,Y]=D^2h[Y,X].
\]
It also demonstrates symmetry directly from the cumulant, without invoking a separate Schwarz theorem.

### B. Entropy signs and normalization

For
\[
p_\theta=\frac{e^{-\theta\cdot F}\pi}{Z(\theta)},\qquad
A(\theta)=\log Z(\theta),\qquad m(\theta)=\mathbb E_\theta F,
\]
one has \(dA=-\langle m,d\theta\rangle\), hence
\[
\mathcal S(\theta)=\langle\theta,m(\theta)\rangle+A(\theta)-A(0)
\]
and
\[
d\mathcal S=\langle\theta,dm\rangle
=-G_\theta(\theta,\cdot).
\]

With \(F=(L_0,R)\), \(\theta=(t,q)\), and \(q=ta\), a fixed-response path satisfies
\[
d\mathcal S=t\,dh,
\]
so
\[
\boxed{\left.\frac{\partial\mathcal S}{\partial t}\right|_M
=-t\,\operatorname{Var}(H).}
\]

There is no missing factor of \(t\), normalization term, or sign. Monotone decrease follows for \(t\ge0\); strict decrease for \(t>0\) requires \(\operatorname{Var}(H)>0\).

### C. Joint-chart metric

The formula
\[
D\,\mathrm{sliceInv}(\tau,v)
=(\tau,-\tau b-C^{-1}v)
\]
is correct **when the inverse returns \((t,q)=(t,ta)\)**.

If it returns \((t,a)\), then, for \(t\ne0\),
\[
\delta a=-\frac{\tau}{t}(a+b)-\frac1tC^{-1}v.
\]

In natural coordinates the energy score is
\[
S_X=\tau H-(C^{-1}v)\cdot R.
\]
Residual orthogonality therefore gives
\[
G(X,Y)=\tau\tau'\operatorname{Var}(H)+v^\top C^{-1}w.
\]
The observable-length bound is correct under the usual differentiation and path-regularity hypotheses.

One useful qualification: the chart can exist with \(C>0\) even when \(\operatorname{Var}(H)=0\). In that case this joint Fisher form is **degenerate**, not a Riemannian metric.

### D. Response Hessian: definiteness and an especially clean invariant

Define
\[
T_H{}_{ij}=\kappa_3(H,R_i,R_j),\qquad
K_{ij}=D_M^2h[e_i,e_j].
\]
Then
\[
\boxed{K=C^{-1}T_HC^{-1}.}
\]
Thus \(K\) and \(T_H\) have the same inertia. In particular,
\[
K\succeq0
\iff
\mathbb E\!\left[(H-\mathbb EH)
\bigl(w\cdot(R-\mathbb ER)\bigr)^2\right]\ge0
\quad\text{for every }w.
\]

There is **no universal definiteness**. Already for a symmetric scalar response:

- \(L_0=R^2\) gives positive response curvature when \(R^2\) is nonconstant;
- \(L_0=c-R^2\), with \(c\) large enough to keep the loss nonnegative, gives negative curvature.

Your proposed contraction has two excellent interpretations. Set
\[
Q=(R-M)^\top C^{-1}(R-M).
\]
Then
\[
\begin{aligned}
\operatorname{tr}(CK)
&=\operatorname{tr}(C^{-1}T_H)\\
&=\kappa_3(H,R,R):C^{-1}\\
&=\operatorname{Cov}(H,Q).
\end{aligned}
\]
It measures whether residual loss is associated with **large whitened response excursions**.

More importantly, your derivative theorem immediately gives
\[
\left.\partial_t C\right|_M=-T_H,
\]
hence
\[
\boxed{\operatorname{tr}(CK)
=-\left.\partial_t\log\det C\right|_M.}
\]

This is the trace of the response Hessian against the inverse response metric. It is invariant under invertible affine changes of response coordinates. I would land the contraction identity now, and the log-determinant corollary when convenient.

---

## 2. The connection capstone: beautiful, but the full-chart “m-Hessian” identification is false

This deserves correction before it becomes an architectural premise.

### Full family

Assume the full Fisher matrix is nondegenerate. The full mixture coordinates are
\[
\eta=(h,M).
\]
Since \(h\) is itself one of these affine coordinates,
\[
\boxed{\operatorname{Hess}^{(m)}h=0.}
\]

Therefore the nonzero ordinary Hessian in mixed coordinates \((t,M)\) cannot be the full-family mixture-covariant Hessian.

For the full exponential connection, whose affine coordinates are \((t,q)\),
\[
\boxed{\operatorname{Hess}^{(e)}h[X,Y]
=\kappa_3(L_0,S_X,S_Y).}
\]
The residual \(H\), rather than \(L_0\), in the ordinary mixed-coordinate Hessian records the coordinate correction.

### Fixed-temperature family: the proposed interpretation becomes exactly right

Fix \(t\). The \(q\)-family is an exponential family with sufficient statistic \(R\), whose intrinsic mixture coordinates are \(M\). Consequently,
\[
\boxed{
\operatorname{Hess}^{(m,t)}h[v,w]
=D_M^2h[v,w]
=\kappa_3(H,V_v,V_w),
\qquad V_v=(C^{-1}v)\cdot R.
}
\]

Thus:

> **The response block of the loss Hessian is the intrinsic mixture Hessian of the loss expectation on the fixed-temperature exponential family.**

There is also a precise extrinsic formulation. Write \(\sigma^2=\operatorname{Var}(H)>0\). In the full family, \(\partial_t|_M\) is Fisher-normal to the fixed-\(t\) leaf. With the second fundamental form defined by normal projection of the ambient connection,
\[
B^{(e)}(v,w)=0,
\]
whereas
\[
\boxed{
B^{(m)}(v,w)
=-\frac{D_M^2h[v,w]}{\sigma^2}\,\partial_t\big|_M.
}
\]
The Levi–Civita second fundamental form is half this expression.

This is a genuine geometric capstone: **residual cumulants measure the mixture bending of an exponentially flat fixed-temperature family**.

Two cautions:

1. The response image itself is locally open in its affine hull, so its Euclidean second fundamental form is not the interesting object. The family of distributions, or the graph of \(h\), is.
2. Your \(S\) is an energy score: \(d\log p=-(S-\mathbb ES)\). With the conventional log-score definition, the Amari–Chentsov tensor is
   \[
   \mathbb E[d\log p_X\,d\log p_Y\,d\log p_Z]
   =-\kappa_3(S_X,S_Y,S_Z).
   \]
   Declare this sign convention before introducing \(\alpha\)-connections.

---

## 3. Deepest missing piece for the PI: global reachable-chart synthesis

My ranking now is:

1. **Global response-chart synthesis, then restriction to the actual reachable data locus.**
2. **Interior-threshold existence**, completing the Chernoff/projection story.
3. **The corrected fixed-temperature mixture-geometry capstone above.**
4. **Arcsine length bound.**
5. **Compact-cover Cramér.**
6. **Walls**, unless the intended data manifold actually meets a singular stratum.

The reason for promoting global synthesis is specific to the PI’s goal. You now have exceptionally rich local laws. The missing structural statement is:

> Which responses admit these laws, does each response have a unique canonical representative, and do all the local charts assemble into one global loss-and-entropy landscape?

That moves the programme from “local calculus plus journeys” to an actual **map of the response space**.

### Interior-threshold existence: sign and scope

For \(X=u\cdot R\),
\[
\frac{dP_\lambda}{dP_0}
=e^{\lambda X-\Lambda(\lambda)},\qquad
a_\lambda=a-\frac{\lambda}{t}u.
\]
Thus
\[
\boxed{
\frac d{d\lambda}\,u\cdot m(a_\lambda)
=\Lambda''(\lambda)
=\operatorname{Var}_{P_\lambda}(X)\ge0.
}
\]
There is no surviving \(1/t\). It is strictly positive when \(X\) is not almost surely constant.

For bounded \(X\),
\[
\mathbb E_{P_\lambda}X\longrightarrow\operatorname{ess\,sup}X,
\]
so every
\[
\mathbb E_{P_0}X<r<\operatorname{ess\,sup}X
\]
has a unique finite positive tilt.

**Do not state this from the threshold inequalities alone in an unbounded setting.** A finite right endpoint of the exponential-moment domain can have finite limiting tilted mean. For example, a density proportional to
\[
e^{-x}(1+x)^{-p},\qquad x\ge0,\quad p>2,
\]
has this obstruction. Boundedness, finiteness of all positive exponential moments, or an appropriate steepness hypothesis resolves it.

Also, a face-concentration theorem requiring positive mass on the exposed face may be too strong for this application. Convergence of the tilted mean to the essential supremum holds in the bounded case even when the maximizing level set has zero mass.

This completes the scalar rate/halfspace variational identity, not by itself the full vector Cramér theorem.

---

## 4. Top pick: a Lean-friendly global theorem

I would first prove the minimal, full-dimensional version, then transport it to \(N^\perp\).

### Mathematical specification

Let \(E\) be finite-dimensional Euclidean space. Assume:

- \(\pi\) is a finite nonzero measure;
- \(R:\Omega\to E\) is measurable and essentially bounded;
- the essential affine span of \(R\) is all of \(E\);
- \(I\subseteq\mathbb R\) is open;
- \(L_0\) is measurable and real-valued almost everywhere;
- for every \(t\in I\),
  \[
  0<\int e^{-tL_0}\,d\pi<\infty.
  \]

Put
\[
K=\overline{\operatorname{conv}}\operatorname{ess\,range}_\pi R,
\]
and
\[
A(t,q)=\log\int e^{-tL_0-q\cdot R}\,d\pi,\qquad
M(t,q)=\mathbb E_{t,q}R.
\]

The primary theorem is
\[
\boxed{
\forall t\in I,\quad
q\longmapsto M(t,q)
\text{ is a smooth bijection }E\longrightarrow\operatorname{int}K
\text{ with smooth inverse}.
}
\]

The joint theorem is
\[
\boxed{
(t,q)\longmapsto(t,M(t,q))
:
I\times E\;\cong\;I\times\operatorname{int}K
}
\]
as a smooth equivalence.

For a nonminimal response representation, replace \(E\) by \(N^\perp\) and \(\operatorname{int}K\) by \(\operatorname{relint}K\), using affine coordinates on its affine hull.

### Recommended proof decomposition

#### 1. Support and minimality

Prove:

- every finite tilt is equivalent to \(\pi\);
- hence all finite tilts have the same essential response support;
- \(C(t,q)\) is positive definite;
- \(M(t,q)\in\operatorname{int}K\).

The final point follows from supporting hyperplanes: a mean on a proper supporting hyperplane would force the entire response distribution onto that hyperplane.

#### 2. Coercivity of the dual objective

For prescribed \(M\in\operatorname{int}K\), define
\[
F_{t,M}(q)=A(t,q)+q\cdot M.
\]

The most useful standalone existence lemma is
\[
\boxed{
\exists c>0,\ \exists B\in\mathbb R,\quad
c\|q\|+B\le F_{t,M}(q)\quad\text{for every }q.
}
\]

This is the substantive global step. It can be proved by a finite cover of the unit sphere:

- interiority supplies a response-support point on the favorable side of each direction;
- a neighborhood of that support point has positive tilted base mass;
- finitely many such neighborhoods give a uniform positive lower bound.

Crucially, this is a lower bound on an **integral**, not merely on the support function.

#### 3. Minimize and identify the response

Continuity plus coercivity gives a minimizer \(q_*\). Since
\[
\nabla_qF_{t,M}=M-M(t,q),
\]
it satisfies
\[
M(t,q_*)=M.
\]

Positive definiteness of \(C=\nabla_q^2A\) gives strict convexity and uniqueness.

The first public existence theorem can therefore be the simple Lean-style specification
```text
M ∈ interior K → ∃! q, response t q = M
```
under the standing hypotheses.

#### 4. Glue the existing local inverses

Your local chart theorem already supplies smooth inverses because
\[
D_qM=-C.
\]
Global uniqueness makes every local inverse agree with the globally selected solution. This should be substantially cheaper than constructing a global smooth inverse directly.

### Immediate research-level corollaries

You obtain global functions
\[
q=q(t,M),\qquad h=h(t,M),\qquad \mathcal S=\mathcal S(t,M)
\]
on \(I\times\operatorname{int}K\), with all the landed differential identities valid there.

Then, for an actual data-to-response map \(d\mapsto M(d)\),
\[
d\longmapsto q(t,M(d))
\]
is the canonical parameter assignment wherever \(M(d)\in\operatorname{int}K\). The reachable response locus remains its own distinguished subset; it is **not** identified with the whole moment interior.

### Main pitfalls

- **Work in \(q=ta\), not \(a\).** Conversion back to \(a\) is only valid for \(t\ne0\).
- **Remove affine null directions first.** Otherwise uniqueness and coercivity both fail.
- **Use essential support.** Null-set response values must not enlarge \(K\).
- **Do not require \(\operatorname{Var}(H)>0\).** The global response chart needs only response minimality; full information geometry needs the additional residual nondegeneracy.
- **Treat the featureless endpoint honestly.** If integrability is known only for \(t\ge0\), smoothness on an open interval around \(0\) is unavailable. Prove the interior theorem for \(t>0\), then a separate one-sided extension at \(0\).
- **Global existence is not uniform conditioning.** As \(M\) approaches \(\partial K\), \(q\) can diverge and \(C^{-1}\) can blow up.

The strongest resulting narrative is:

> The interior response space has a unique global canonical parametrization; the actual data distributions occupy a specified reachable locus within it; residual variance controls the entropy cost of annealing, and residual third cumulants control the bending of posterior loss across that locus.

That is now the most direct capstone for the PI’s stated programme.