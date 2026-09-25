## Executive assessment

The new results fit together well. Two qualifications matter especially:

1. **The loss-surface \(MM\) block is generally not \(-C^{-1}\).** For \(h(t,M)=\mathbb E_{t,M}L_0\), it is another residual third-cumulant block. Completing all three blocks yields a particularly clean tensor theorem.
2. **The halfspace information-projection identity is correct with an interior optimizer, but is false without qualification when the infimum ranges only over finite-parameter family members.** Exposed boundary thresholds give the obstruction.

My ranking is:

1. **Chernoff ⇄ information projection**, initially as an attained-optimizer certificate.
2. **Complete the residual-cumulant Hessian**, preferably as one bilinear formula.
3. **Entropy/relative-entropy geometry of the joint response chart.**
4. **General-path Fisher length**, with an observable-dependent arcsine strengthening.
5. **Compact-cover Cramér upper bound.**
6. **Global reachable-chart synthesis**, with explicit nondegeneracy and temperature hypotheses.
7. **Walls**, unless there is now a precise response phenomenon they should explain.

The reachable-set properness witness is a small closure task worth doing immediately, rather than a research direction competing with these.

---

## 1. Audit

### 1a. Ray length

For the unconstrained ray
\[
P_u(dx)=Z(u)^{-1}e^{-uL_0(x)}\bar\pi(dx),
\]
the score is
\[
\partial_u\log p_u=-(L_0-\mathbb E_uL_0).
\]
Consequently,
\[
g_u(\partial_u,\partial_u)=\operatorname{Var}_u(L_0),
\qquad
\operatorname{Length}(T)=\int_0^T\sqrt{\operatorname{Var}_u(L_0)}\,du.
\]
Thus **yes: this is exactly Fisher length**, with the usual Fisher metric normalization.

Distinguish three paths:

- \(a=0\), varying temperature: speed squared \(\operatorname{Var}(L_0)\);
- fixed \(a\), varying temperature: speed squared \(\operatorname{Var}(L_0+a\cdot R)\);
- fixed \(M\), varying temperature: speed squared \(\operatorname{Var}(H)\), where \(H=L_0-b\cdot R\).

The last distinction becomes important when composing `RayLength` with the slice chart.

Your upper bound follows from Cauchy–Schwarz and
\[
E(0)-E(T)=\int_0^T\operatorname{Var}_u(L_0)\,du.
\]
It is correctly normalized.

#### The Popoviciu lower bound

The argument is right and generalizes directly to arbitrary regular paths:
\[
|\dot m_\varphi|
\le \sqrt{\operatorname{Var}(\varphi)}\,\sqrt{g(\dot\eta,\dot\eta)}
\le \frac{hi-lo}{2}\sqrt{g(\dot\eta,\dot\eta)}.
\]

There is a natural sharper version, but **not generally one depending only on directed KL**.

Set
\[
z(s)=\frac{\mathbb E_s\varphi-lo}{hi-lo}.
\]
The variance bound
\[
\operatorname{Var}_s(\varphi)
\le (\mathbb E_s\varphi-lo)(hi-\mathbb E_s\varphi)
\]
gives
\[
\boxed{
\operatorname{Length}
\ge
2\left|
\arcsin\sqrt{z(1)}-\arcsin\sqrt{z(0)}
\right|.
}
\]
This dominates the Popoviciu bound. It is the Fisher distance lower bound obtained by observing a bounded statistic through its associated Bernoulli channel.

For formalization, first assume the endpoint expectations—and hence, in your positive-density setting for a nonconstant observable, all path expectations—lie strictly between \(lo\) and \(hi\). Boundary extension can follow later.

There is also the distribution-level bound
\[
\operatorname{Length}
\ge
2\arccos\!\left(\int\sqrt{p_0p_1}\,d\mu\right),
\]
from the square-root embedding into the sphere of radius \(2\).

By contrast, inequalities such as
\[
\operatorname{Length}\ge\sqrt{2\,\mathrm{KL}(P_1\|P_0)}
\]
are false globally. Bernoulli exponential rays already have bounded Fisher length while directed KL can diverge. More strongly, a fixed positive directed KL can coexist with arbitrarily small Fisher distance and monotone-ray length. A KL-based lower bound requires additional uniform control, such as likelihood-ratio or metric-comparison bounds.

**Recommendation:** keep Popoviciu as the inexpensive universal theorem; add the arcsine observable bound before attempting KL comparisons.

---

### 1b. Chernoff and information projection

Assuming
\[
P_{t,a}(dx)
=
\exp[-tL_0(x)-t\,a\cdot R(x)-A_t(a)]\,\bar\pi(dx),
\]
your identity is correct for \(t\ne0\):
\[
\Lambda_a(\theta)
=
A_t(a-\theta/t)-A_t(a).
\]

Write
\[
D_a(u,r)
=
\sup_{\lambda\ge0}
\{\lambda r-\Lambda_a(\lambda u)\}.
\]

For every family member \(P_{t,b}\) and every \(\lambda\ge0\),
\[
\mathrm{KL}(P_{t,b}\|P_{t,a})
\ge
\lambda\,u\cdot m_t(b)-\Lambda_a(\lambda u).
\]
Therefore, whenever \(u\cdot m_t(b)\ge r\),
\[
\boxed{
D_a(u,r)\le \mathrm{KL}(P_{t,b}\|P_{t,a}).
}
\]

That is the unconditional direction.

#### Equality with an attained tilt

Suppose \(\lambda_*\ge0\), put
\[
a_*=a-\lambda_*u/t,
\]
and assume the complementary-slackness conditions
\[
u\cdot m_t(a_*)\ge r,
\qquad
\lambda_*\bigl(u\cdot m_t(a_*)-r\bigr)=0.
\]
Then
\[
\boxed{
D_a(u,r)
=
\mathrm{KL}(P_{t,a_*}\|P_{t,a})
=
\min_{\substack{b\\u\cdot m_t(b)\ge r}}
\mathrm{KL}(P_{t,b}\|P_{t,a}).
}
\]

This includes both regimes:

- \(r\le u\cdot m_t(a)\): choose \(\lambda_*=0\); the answer is \(0\).
- An upper-tail threshold attained by a positive tilt: choose \(\lambda_*>0\) with \(u\cdot m_t(a_*)=r\).

The most informative underlying theorem is the exact identity
\[
\boxed{
\begin{aligned}
\mathrm{KL}(P_{t,b}\|P_{t,a})
={}&\mathrm{KL}(P_{t,b}\|P_{t,a_*})\\
&+\lambda_*\bigl(u\cdot m_t(b)-r\bigr)
+\mathrm{KL}(P_{t,a_*}\|P_{t,a}).
\end{aligned}
}
\]
This is a halfspace Pythagorean identity, not merely an optimization equality.

It immediately gives uniqueness of the minimizing distribution. Uniqueness of its coefficient additionally requires feature minimality and \(t\ne0\).

#### Why the unrestricted finite-family statement fails

Take \(R\in\{0,1\}\), with \(P_{t,a}(R=1)=p\in(0,1)\), and choose \(r=1\). Then
\[
D_a(1,1)=-\log p<\infty.
\]
But every finite-parameter family member has expectation strictly below \(1\). Thus
\[
\{b:m_t(b)\ge1\}=\varnothing.
\]
Its extended-real infimum is \(+\infty\), not \(-\log p\).

The optimizer is the boundary distribution conditioned on \(R=1\), reached at infinite tilt.

Accordingly, use one of these formulations:

1. **Finite-tilt certificate:** the theorem above.
2. **Interior-threshold theorem:** under boundedness and nonconstancy of \(u\cdot R\),
   \[
   u\cdot m_t(a)<r<\operatorname*{ess\,sup}_{P_{t,a}}u\cdot R
   \]
   produces a finite tilt.
3. **Full extended-family theorem:** optimize over suitable boundary distributions or all probability measures, with genuine extended-real relative entropy.

The first is the cleanest next formalization. The second is the natural follow-up using monotonicity and the large-tilt limit.

#### Identification with the dual potential

Define, independently of existing sign conventions,
\[
J_t(M)=\sup_b\{-t\,b\cdot M-A_t(b)\}.
\]
For \(M=m_t(b)\),
\[
\mathrm{KL}(P_{t,b}\|P_{t,a})
=
J_t(M)+t\,a\cdot M+A_t(a).
\]
Thus the information projection is precisely minimization of the dual-potential/Bregman rate over the response halfspace.

For interior responses this identification is direct. Boundary responses require the extended conjugate, rather than just evaluation along the inverse response chart.

---

## 2. The full loss Hessian: a correction and a stronger target

Here I use the loss-surface interpretation
\[
h(t,M)=\mathbb E_{t,M}L_0.
\]
With
\[
C=\operatorname{Cov}(R,R),\quad
c=\operatorname{Cov}(R,L_0),\quad
b=C^{-1}c,\quad
H=L_0-b\cdot R,
\]
one has
\[
h_t=-\operatorname{Var}(H),
\qquad
D_Mh[v]=b\cdot v.
\]

For a response direction \(v\), define the observable
\[
V_v=(C^{-1}v)\cdot R.
\]
Then the missing blocks are
\[
\boxed{
D_M(h_t)[v]=-\kappa_3(H,H,V_v),
}
\]
and
\[
\boxed{
D_M^2h[v,w]=\kappa_3(H,V_v,V_w).
}
\]

In matrix notation,
\[
h_{MM}=C^{-1}K_HC^{-1},
\qquad
(K_H)_{ij}=\kappa_3(H,R_i,R_j).
\]
It is **not generally \(-C^{-1}\)**, and need not have a fixed sign.

A decisive sanity check: if \(L_0\) is affine in \(R\), then \(h\) is affine in \(M\), so \(h_{MM}=0\), although \(C^{-1}\) can be nonzero.

The inverse-covariance Hessian belongs to the convex dual potential—or, with a minus sign, the corresponding maximal relative entropy—not to the expected-loss surface.

### The unified theorem

For a joint tangent direction \(X=(\tau,v)\), set
\[
S_X=-\tau H+V_v.
\]
Then all three blocks combine as
\[
\boxed{
D^2h[X,Y]=\kappa_3(H,S_X,S_Y).
}
\]

This gives:

- \(tt\): \(\kappa_3(H,H,H)\);
- \(tM\): \(-\kappa_3(H,H,V_v)\);
- \(MM\): \(\kappa_3(H,V_v,V_w)\).

That is a more valuable endpoint than three isolated derivative theorems: **the entire loss curvature is one residual-cumulant tensor pulled back through the constrained score map.**

### Formalization strategy

Reuse the identity \(Cb=c\), rather than differentiating an explicit inverse.

For a response direction \(v\),
\[
C\,D_vb=D_vc-(D_vC)b.
\]
The covariance derivative under the score \(V_v\) gives
\[
D_vc-(D_vC)b=\kappa_3(R,H,V_v).
\]
Hence
\[
D_vb=C^{-1}\kappa_3(R,H,V_v).
\]

In the temperature direction, the score is \(-H\), giving
\[
\partial_tb=-C^{-1}\kappa_3(R,H,H).
\]

This is closely aligned with your successful “differentiate the identity” strategy in `ResidualFormDeriv`.

---

## 3. Re-ranking and extensions

### 1. Chernoff ⇄ information projection

This best closes the programme’s conceptual loop:
\[
\text{data coefficients}
\longrightarrow
\text{responses}
\longrightarrow
\text{dual/KL geometry}
\longrightarrow
\text{concentration}.
\]

Land the exact finite-tilt certificate first. It needs no asymptotic theorem, no global optimizer existence, and no boundary machinery.

### 2. Unified residual-cumulant Hessian

This remains exceptionally strong value. It completes a partially landed object and describes how the loss response changes in every joint direction.

It also prevents a conceptual misidentification of the loss Hessian with the entropy/dual Hessian.

### 3. Entropy geometry and the featureless point

This is core, but formulate it **relative to the prior/reference measure**.

Let
\[
\mathcal S(P)=-\mathrm{KL}(P\|\bar\pi).
\]
Then
\[
\mathcal S(P_{t,a})
=
t\,h+t\,a\cdot M+A_t(a),
\]
and on the joint response chart,
\[
\boxed{d\mathcal S=t\,dh+t\,a\cdot dM.}
\]

For \(a=0\), any admissible \(Q\) satisfying
\[
\mathbb E_Q L_0=\mathbb E_{P_{t,0}}L_0
\]
obeys
\[
\boxed{
\mathcal S(P_{t,0})-\mathcal S(Q)
=
\mathrm{KL}(Q\|P_{t,0})\ge0.
}
\]

Thus \(P_{t,0}\) is the unique **maximum-relative-entropy distribution at its loss expectation**.

It is maximum ordinary Shannon entropy only when the reference measure makes that identification valid, such as a uniform finite prior. With a nonuniform prior, an extra expected log-prior term intervenes.

Also distinguish:

- \(\bar\pi\): unconstrained maximum of \(-\mathrm{KL}(\cdot\|\bar\pi)\);
- \(P_{t,0}\): constrained maximum at a prescribed expected loss.

This is the mathematically precise version of “featureless maximum entropy.”

### 4. General-path Fisher geometry

Besides the observable length bound, the joint chart offers a particularly clean metric formula:
\[
\boxed{
g_{(t,M)}((\tau,v),(\tau,v))
=
\tau^2\operatorname{Var}(H)+v^\top C^{-1}v.
}
\]
Indeed, the score is \(S_X\), and \(\operatorname{Cov}(H,R)=0\).

This is an excellent new direction: **temperature motion and response motion are Fisher-orthogonal in the constrained chart**.

It explains the Schur complement geometrically and provides the correct length integrand for arbitrary joint-chart journeys. I would prioritize this formula over merely generalizing the Popoviciu proof.

### 5. Finite unions and compact-cover Cramér

The finite-cover theorem is immediate and useful:
\[
F\subseteq\bigcup_{i=1}^{N}\{x:\theta_i\cdot x\ge c_i\}
\quad\Longrightarrow\quad
\Pr(\bar R_n\in F)
\le
\sum_{i=1}^{N}e^{-n(c_i-\Lambda(\theta_i))}.
\]
If all exponents are at least \(\alpha\), this is \(Ne^{-n\alpha}\).

The conceptual next step is to construct a finite cover from pointwise dual witnesses. If compact \(F\) satisfies \(I(x)>\alpha\) everywhere, choose for each \(x\) a tilt witnessing this strict inequality, retain it on a neighborhood, and extract a finite subcover.

Keep the strict \(\alpha<\inf_F I\) formulation first. It avoids pretending that the finite prefactor is uniform as \(\alpha\) approaches the optimal rate.

### 6. Global reachable-chart synthesis

This is valuable as a capstone, but not just a composition theorem.

For
\[
(t,a)\mapsto(h,M),
\]
a full chart requires minimality of the **joint** statistics \((L_0,R)\). Feature covariance invertibility alone does not suffice: if \(L_0\) is affine in \(R\), the temperature direction collapses.

At \(t=0\), all finite \(a\) represent the same natural feature coefficient \(-ta=0\); hence this parameterization is not a chart there. Use natural coordinates to include the prior endpoint, and state chart claims on \(t>0\).

Restricting \(a\) to a polytope also does not make the response image convex or open. State an embedding/restriction result, not an unqualified global chart onto an open response domain.

Finally, distinguish the distribution of observed data from the posterior induced by it. `JourneyPotential` gives the KL between the relevant **family distributions**, not automatically KL between the raw data law and the prior.

### Immediate closure: reachable responses are proper

For positive response dimension, a nonempty compact subset of \(\operatorname{int}K\) cannot equal \(\operatorname{int}K\): a nonempty bounded open subset of a positive-dimensional Euclidean space is not compact.

This gives the missing witness abstractly. For an explicit witness, choose a boundary point and approach it from an interior point; compact containment excludes all sufficiently boundary-near points.

Handle dimension zero separately, and use relative interior if working after quotient/restriction.

---

## 4. Top pick: Lean-friendly finite-tilt certificate

I would make the foundational theorem **algebraic and attained**, leaving `sSup`, `iInf`, and optimizer existence to corollaries.

Fix \(t>0\), \(a,u,r\), and define
\[
\Lambda(\theta)=A_t(a-\theta/t)-A_t(a).
\]
For \(\lambda\ge0\), define
\[
a_*=a-(\lambda/t)u,
\qquad
D=\lambda r-\Lambda(\lambda u).
\]

Assume
\[
u\cdot m_t(a_*)\ge r,
\qquad
\lambda\bigl(u\cdot m_t(a_*)-r\bigr)=0.
\]

Prove these four assertions:

1. **Attained value**
   \[
   \mathrm{KL}(P_{t,a_*}\|P_{t,a})=D.
   \]

2. **Exact decomposition**, for every \(b\):
   \[
   \mathrm{KL}(P_{t,b}\|P_{t,a})
   =
   \mathrm{KL}(P_{t,b}\|P_{t,a_*})
   +\lambda(u\cdot m_t(b)-r)+D.
   \]

3. **Primal optimality**, for every feasible \(b\):
   \[
   D\le\mathrm{KL}(P_{t,b}\|P_{t,a}).
   \]

4. **Dual optimality**, for every \(\mu\ge0\):
   \[
   \mu r-\Lambda(\mu u)\le D.
   \]

A schematic theorem interface is:

```lean
-- Schematic: substitute the project's existing types and names.
theorem halfspace_projection_certificate
    (ht : 0 < t)
    (hlam : 0 ≤ lam)
    (hfeas : r ≤ dot u (response t aStar))
    (hcomp : lam * (dot u (response t aStar) - r) = 0) :
    familyKL t aStar a = rateCandidate ∧
    (∀ b, r ≤ dot u (response t b) →
      rateCandidate ≤ familyKL t b a) ∧
    (∀ μ, 0 ≤ μ →
      μ * r - logMGF (μ • u) ≤ rateCandidate)
```

Then package the attained values as:

- `IsLeast` of the feasible KL-value set;
- `IsGreatest` of the nonnegative-tilt objective-value set.

These forms are particularly Lean-friendly: the witnesses establish nonemptiness, and the inequalities establish the needed bounds. Real-valued `sSup`/`sInf` equalities can follow safely.

### Proof ingredients

The core log-density identity is
\[
\log\frac{dP_{t,a_*}}{dP_{t,a}}
=
\lambda\,u\cdot R-\Lambda(\lambda u).
\]
Integrating against \(P_{t,b}\) yields the decomposition. Integrating against \(P_{t,a_*}\), then using complementary slackness, gives the attained value.

For dual optimality, compare \(P_{t,a_*}\) with the tilt at any \(\mu\ge0\):
\[
\mu\,u\cdot m_t(a_*)-\Lambda(\mu u)
\le \mathrm{KL}(P_{t,a_*}\|P_{t,a}).
\]
Feasibility gives the desired bound with \(r\).

### Pitfalls to fence off explicitly

- **Division by \(t\):** use \(t>0\), or at least \(t\ne0\).
- **Boundary thresholds:** do not assert a finite optimizer without a strict-interior hypothesis.
- **Lean’s totalized real operations:** empty feasible sets and unbounded objectives need extended-real formulations; the certificate avoids both.
- **KL orientation:** the projection minimizes
  \(\mathrm{KL}(P_{t,b}\|P_{t,a})\), not the reverse.
- **Parameter uniqueness:** only claim it under minimality; distributional uniqueness is the primitive statement.
- **Measure-level KL:** start with the existing finite family-KL algebra. Extend to arbitrary measures only with explicit absolute-continuity and integrability treatment.

This first theorem already turns every attained Chernoff exponent into an exact geometric distance to a response constraint. The subsequent existence theorem then says which halfspaces admit that finite geometric projection.