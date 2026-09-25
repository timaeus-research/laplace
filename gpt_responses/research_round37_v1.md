## 1. Audit

Items 2, 4, and 5 are mathematically sound, subject to the measure-theoretic and extended-real qualifications below. The most important correction is that **“pointwise \(I>\alpha\)” and “\(\alpha<\inf I\)” are not equivalent in general; compactness and lower semicontinuity make them equivalent here.**

### (a) Essential infimum

Let
\[
d\bar\pi=\frac{\pi\,d\mu}{\int\pi\,d\mu},
\qquad 0<\int\pi\,d\mu<\infty,
\]
with \(\pi\ge0\). Then
\[
V\ge\alpha\quad\bar\pi\text{-a.e.},
\qquad
\forall\varepsilon>0,\quad
\bar\pi(V<\alpha+\varepsilon)>0
\]
is exactly the characterization
\[
\alpha=\operatorname*{ess\,inf}_{\bar\pi}V.
\]

There is one qualification concerning `∀ᵐ x`:

* If `hα` is taken under \(\bar\pi\), the characterization is exact.
* If it is taken under the ambient measure \(\mu\), it is potentially stronger: values of \(V\) where \(\pi=0\) are irrelevant to the essential infimum under \(\bar\pi\).
* If \(\pi>0\) \(\mu\)-a.e., the distinction disappears.

Your accessibility hypothesis is precisely the positive-near-minimum-mass condition, after normalization. No positive mass on \(\{V=\alpha\}\) is needed.

The concentration proof is also the right one. Its substantive assumptions are finite positive baseline mass, boundedness sufficient for the expectation estimate, and accessibility. A finite, strictly positive Gibbs reweighting preserves null sets and accessibility.

### (b) Arcsine interiority for all real parameters

Harmless for correctness, but stronger than the geometric theorem needs. The natural hypothesis is
\[
\forall s\in[0,1],\qquad
lo<\mathbb E_{\eta(s)}\phi<hi,
\]
with \(C^1\) regularity on a neighborhood of that interval, or the corresponding interval-local formulation.

Two useful observations:

1. If every finite Gibbs distribution is equivalent to the prior, and \(\phi\) is neither a.e. \(lo\) nor a.e. \(hi\), strict interiority can hold automatically throughout the natural-parameter domain.
2. Otherwise, requiring it on all of \(\mathbb R\) excludes irrelevant behavior outside the integration interval.

I would retain the landed theorem and add an interval-local wrapper. A later endpoint-continuity version can permit expectations equal to \(lo\) or \(hi\) at the endpoints: apply the interior theorem on truncated intervals and pass to the limit.

The factor \(2\) is correct:
\[
\frac{d}{ds}\bigl(2\arcsin\sqrt{z(s)}\bigr)
=\frac{z'(s)}{\sqrt{z(s)(1-z(s))}}.
\]

### (c) Compact-cover witnesses and the rate function

Use the extended-real rate function
\[
I(x)=\sup_\theta\{\theta\cdot x-\Lambda(\theta)\}.
\]

For each individual \(x\),
\[
\exists\theta,\quad \alpha<\theta\cdot x-\Lambda(\theta)
\quad\Longleftrightarrow\quad
\alpha<I(x),
\]
including \(I(x)=+\infty\).

Thus the displayed hypothesis is immediately equivalent to
\[
\forall x\in F,\quad \alpha<I(x).
\]

To identify this with \(\alpha<\inf_F I\), one additionally uses:

* \(F\) compact;
* \(I\) lower semicontinuous, as a supremum of continuous affine functions.

An extended-real l.s.c. function attains its infimum on a nonempty compact set. Hence the equivalence does hold in your setting. Without compactness it can fail: all values can exceed \(\alpha\) while their infimum equals \(\alpha\).

There is **no additional problem when \(I=+\infty\) on part or all of \(F\)**. For each finite \(\alpha\), choose finite pointwise witnesses and then a finite subcover. If \(I=+\infty\) throughout \(F\), this yields a bound at every finite exponential rate; the covering constant may depend on that rate.

Lean qualification: define the potentially infinite supremum in an extended-real type. An unrestricted `sSup` in \(\mathbb R\) does not represent \(+\infty\).

### (d) Accessible upper bound

Yes. If
\[
u\cdot R\le\beta\quad\bar\pi\text{-a.e.},
\qquad
\forall\varepsilon>0,\quad
\bar\pi(u\cdot R>\beta-\varepsilon)>0,
\]
then \(\beta=\operatorname*{ess\,sup}_{\bar\pi}u\cdot R\).

The same ambient-measure qualification as in (a) applies, but the theorem is valid even when its a.e. bound is stronger than necessary.

The strict threshold
\[
u\cdot m(a)<r<\beta
\]
is exactly the finite-tilt regime. In general \(r=\beta\) requires an infinite tilt, even when the limiting face has positive mass. Accessibility alone guarantees concentration toward the supremum, not attainment by a finite parameter.

Also, along \(a_\lambda=a-\lambda u/t\),
\[
\frac{d}{d\lambda}\,u\cdot m(a_\lambda)
=\operatorname{Var}_{a_\lambda}(u\cdot R),
\]
with no remaining \(1/t\). The cancellation is essential.

---

## 2. The statement of the theory

The organizing claim should be:

> **A finite-dimensional Gibbs family provides global response coordinates on the interior of its moment body. Data enter through a reachable moment map; covariance determines the local cost of changing those responses, third cumulants determine their constrained bending, and integrated information geometry controls journeys from a reference distribution to the calibrated data distribution. Boundary concentration and large deviations describe the limits and rarity of those responses.**

That is a theory, rather than a collection of derivative formulas.

I would present seven principal theorems.

### I. Global response atlas

For positive temperature and identifiable response coordinates,
\[
(t,a)\longmapsto (t,m_t(a))
\]
is a global chart onto
\[
(0,\infty)\times\operatorname{int}K.
\]

Every interior response is realized by exactly one finite parameter. The inverse, loss, and entropy are continuous; local smoothness follows from the nonsingular covariance Jacobian.

**Load-bearing:** `ChartSynthesis`, slice inversion, response range, injectivity, and the \(N^\perp\) reduction.

**Supporting:** the separate range/injectivity lemmas and chart-domain bookkeeping.

This theorem should appear before any extensive cumulant algebra. It tells the reader what space is being mapped.

### II. Data calibration factors through moments

For a data family \(d\mapsto\nu_d\), put
\[
M(d)=\mathbb E_{\nu_d}R.
\]
Whenever \(M(d)\in\operatorname{int}K\), there is a canonical calibrated distribution
\[
P_{t,a_t(M(d))}.
\]

For finite mixtures,
\[
M(w)=\sum_iw_iM_i,
\]
so the reachable response locus is a polytope intersected with \(\operatorname{int}K\).

This theorem explicitly says what information about the data the response model retains:

\[
M(d)=M(d')
\quad\Longrightarrow\quad
P_{t,a_t(M(d))}=P_{t,a_t(M(d'))}.
\]

**Load-bearing:** data mixtures, reachability polytopes, global chart.

**Still to package:** continuity, differentiability, and pullback landscapes under this canonical assignment.

This is the missing bridge between the response atlas and “the data manifold.”

### III. Covariance is the response metric

Write
\[
Z=R-M,\qquad C=\mathbb E[ZZ^\top],
\]
and let \(H\) be the centered loss residual after projection onto the response scores:
\[
H=(L-\mathbb EL)-\gamma^\top Z,
\qquad
\gamma=C^{-1}\operatorname{Cov}(R,L).
\]
For \(v\), set
\[
V_v=(C^{-1}v)^\top Z.
\]

In joint response coordinates, the score of \(X=(\tau,v)\) is
\[
S_X=-\tau H+V_v,
\]
and
\[
g(X,Y)
=\tau\tau'\operatorname{Var}(H)+v'^\top C^{-1}v.
\]

The corresponding first laws include
\[
\partial_t h\big|_M=-\operatorname{Var}(H),
\qquad
D_Mh[v]=\gamma^\top v,
\qquad
\partial_t\mathcal S\big|_M=-t\operatorname{Var}(H).
\]

**Load-bearing:** joint-chart Fisher metric, constrained responses, loss surface, entropy geometry.

This is the central infinitesimal theorem: the cost of a prescribed response change is inverse covariance, while constrained temperature motion is the orthogonal residual mode.

### IV. Third cumulants govern constrained bending

The unified statement is
\[
D^2h[X,Y]=\kappa_3(H,S_X,S_Y).
\]

Its blocks explain temperature curvature, mixed sensitivity, and fixed-temperature response curvature. In particular,
\[
D_M^2h[v,w]=\kappa_3(H,V_v,V_w).
\]

The interpretation matters:

> Expected loss is affine in the ambient mixture geometry. Its response-coordinate Hessian measures the bending of the fixed-temperature Gibbs family inside that affine space.

**Load-bearing:** unified Hessian, `LossHessianBlocks`, third-cumulant/Amari–Chentsov results.

**Next conceptual completion:** the explicit normal-acceleration theorem below.

### V. Integrated journeys from reference to data

A path of calibrated distributions carries:

* response displacement;
* accumulated Fisher length;
* KL endpoint quantities;
* entropy change;
* bounded-observable arcsine displacement.

This should be one journey theorem with named corollaries, not several unrelated paragraphs.

**Load-bearing:** featureless point, annealing ray, journey theorem, length identities, two-axis integrability, `ArcsineLength`.

There is an important naming distinction:

* \((t,0)\) is the **zero-response-field distribution at fixed \(t\)**.
* The genuinely featureless reference \(P_0=\bar\pi\) is at zero full natural parameter.

Unless the base loss is constant, \(P_{t,0}\neq P_0\). Thus a fixed-\(t\) segment from \(a=0\) to \(a_{\rm data}\) is not, by itself, the journey from maximal entropy relative to \(\bar\pi\).

For that full story, use either the natural ray from \(0\) to the data parameter, or the two-leg journey
\[
P_0\longrightarrow P_{t,0}\longrightarrow P_{t,a_{\rm data}}.
\]
The zero-temperature endpoint need not belong to the positive-temperature response chart.

### VI. Boundary approach and concentration

As parameters diverge in a direction, responses approach the associated exposed boundary, with concentration at essential extrema. Accessibility suffices for convergence of expectations; positive face mass gives stronger limiting-measure conclusions.

**Load-bearing:** boundary dichotomy, annealing concentration, properness, the new essential-extremum result.

This theorem explains the atlas’s missing boundary. Walls belong here as a refinement, not as a prerequisite for understanding the interior theory.

### VII. Variational cost and fluctuation rarity

For an accessible interior threshold, the finite tilt is the information projection, and
\[
\inf_{b:\,u\cdot m(b)\ge r}\operatorname{KL}(b\|a)
=
\sup_{\mu\ge0}\{\mu r-\Lambda_a(\mu u)\}.
\]

Compact-cover Chernoff then gives the compact-set upper large-deviation bound.

**Load-bearing:** information projection, `InteriorThreshold`, Chernoff, `CompactCoverCramer`.

This is the probabilistic interpretation of the response map: atypical responses have an information cost, and the calibrated tilt realizes the relevant cost.

### Consolidation rule

The note should contain these seven statements in this order. Module order belongs in an appendix.

Bhatia–Davis, permutation-product differentiation, finite-union bounds, matrix-inverse derivatives, and individual covariance identities are supporting infrastructure. Their importance to the proof does not make them independent narrative destinations.

---

## 3. Revised priorities

My strategic ranking is:

### 1. **(iv) Canonical assignment on the reachable data locus**

This closes the central explanatory gap: the atlas currently maps parameters to responses, but the programme is about data to posterior responses.

Package the continuous map, its differential, moment-fiber invariance, and the pullbacks of loss and entropy. This is substantial synthesis with limited new analytic machinery.

### 2. **(v) One reference-to-data journey theorem**

Do this with the reference distinction above made explicit. Ideally expose both:

* the true featureless-to-data natural ray;
* the fixed-temperature field journey.

Keep the package focused: endpoints, scores/speed, integrated response, KL identities, and the arcsine bound. State signed entropy change, not an unconditional “entropy drop” along an arbitrary fixed-\(t\) field segment.

### 3. **(iii) Explicit mixture second fundamental form**

This supplies the geometric explanation of your most distinctive local theorem.

For fixed \(t\), define
\[
\mathcal B(v,w)
=
V_vV_w-\mathbb E[V_vV_w]
-Z^\top C^{-1}\mathbb E[ZV_vV_w].
\]

Then prove:

1. symmetry and bilinearity;
2. normality:
   \[
   \mathbb E[\mathcal B(v,w)]=0,
   \qquad
   \mathbb E[Z\mathcal B(v,w)]=0;
   \]
3. the mixture-acceleration formula:
   \[
   \frac{D_M^2p[v,w]}{p}=\mathcal B(v,w);
   \]
4. the loss pairing:
   \[
   D_M^2h[v,w]
   =\mathbb E[H\mathcal B(v,w)]
   =\kappa_3(H,V_v,V_w).
   \]

Here \(\mathcal B\) is the Fisher-normal, density-normalized mixture acceleration. This specifies the ambient geometry and the normalization, avoiding an ambiguous theorem called merely “second fundamental form.”

For Lean, items 1, 2, and 4 can be stated entirely with expectations and finite-dimensional linear algebra. Add item 3 when the chosen density/function-space differentiation interface is convenient. Do not build a general infinite-dimensional submanifold library for this theorem.

### 4. **(i) Contraction and log determinant**

With
\[
Q=Z^\top C^{-1}Z,\qquad K=D_M^2h,
\]
the clean statement is
\[
\operatorname{tr}(CK)
=\mathbb E[HQ]
=\operatorname{Cov}(H,Q)
=-\partial_t\log\det C\big|_M.
\]

The first equality is an algebraic contraction of the response Hessian. Prove it independently of determinant differentiation.

The second half follows from
\[
\partial_t C\big|_M=-\mathbb E[HZZ^\top],
\qquad
\partial_t\log\det C
=\operatorname{tr}(C^{-1}\partial_t C).
\]

The determinant expansion is a reasonable finite-dimensional implementation. Prove a reusable Jacobi-style lemma rather than embedding the permutation expansion inside this application. Positive definiteness supplies both invertibility and \(\det C>0\).

This is a beautiful scalar summary of the bending theorem, but not a substitute for it.

### 5. **(vi) Tilt-based finite-\(n\) lower bound**

Yes: there is a clean theorem, and Chebyshev is enough.

Suppose
\[
\frac{dP_b}{dP_a}(x)
=\exp\{\theta\cdot R(x)-\Lambda_a(\theta)\}.
\]
Then
\[
D:=\operatorname{KL}(P_b\|P_a)
=\theta\cdot m_b-\Lambda_a(\theta).
\]

For \(\varepsilon,\delta>0\), choose \(0<\rho<\varepsilon\) with
\(\|\theta\|\rho\le\delta/2\). On
\(\{\|\bar R_n-m_b\|<\rho\}\), the product likelihood ratio is at most
\[
e^{n(D+\delta/2)}.
\]
Consequently,
\[
P_a^{\otimes n}(\bar R_n\in B(m_b,\varepsilon))
\ge
e^{-n(D+\delta/2)}
P_b^{\otimes n}(\bar R_n\in B(m_b,\rho)).
\]

Independence and finite second moments give
\[
P_b^{\otimes n}(\|\bar R_n-m_b\|\ge\rho)
\le \frac{\operatorname{tr}C_b}{n\rho^2}.
\]
For sufficiently large \(n\), the desired bound follows:
\[
P_a^{\otimes n}(\bar R_n\in B(m_b,\varepsilon))
\ge e^{-n(D+\delta)}.
\]

Two pitfalls:

* absorb the prefactor, rather than silently dropping it;
* use a smaller ball if the requested \(\varepsilon\) is too large for the likelihood-ratio error \(\delta\).

This gives a lower bound around every finite tilted mean. Extending it to a full open-set Cramér lower bound requires the additional rate-identification and approximation steps.

### 6. **(ii) Extended-real asymptotic compact upper bound**

Strategically this adds less geometry, but it is a cheap closure task. I would execute it early if the extended-real sequence API cooperates.

For compact \(F\),
\[
\limsup_{n\to\infty}
\frac1n\log P(\bar R_n\in F)
\le-\inf_F I.
\]

The principal pitfall is not analysis but formal semantics:

> Lean’s real logarithm at zero is not the probabilistic value \(-\infty\).

Use an extended-real log-probability, or first formulate the equivalent probability-root bound. Index with \(n+1\) to avoid \(1/0\).

If \(\inf_F I=+\infty\), prove the upper bound for every finite \(\alpha\); do not attempt to substitute \(\alpha=+\infty\) into the finite-cover theorem.

### 7. **Walls and finer boundary stratification**

Keep these after the interior synthesis. They will become compelling when the note has a precise question about transitions between limiting faces or about extending the response atlas to a stratified compactification.

### Two additional directions

**Quantitative stability on compact reachable regions.**  
On a compact subset of the chart domain, continuity and positive definiteness give uniform control of \(C^{-1}\). Along a convex response region this produces Lipschitz calibration bounds and controlled loss/entropy sensitivity. It answers: “How much can posterior parameters change under a small data perturbation?”

**Exact visible/invisible data directions.**  
For finite mixtures, the differential factors through
\[
h\longmapsto \sum_i h_iM_i.
\]
Its kernel is exactly the infinitesimal data variation invisible to the calibrated family. This gives a clean quotient of the data manifold, rather than pretending that mixture weights are identifiable from posterior responses.

---

## 4. Top pick: a Lean-friendly canonical-data theorem

Use a fixed \(t>0\) first. Write \(a_t\) for the response inverse, so
\[
m_t(a_t(M))=M.
\]

Let the finite component moments be \(M_i\), and define the continuous linear map
\[
Lw=\sum_iw_iM_i.
\]
Let
\[
U=L^{-1}(\operatorname{int}K).
\]
This is open in the ambient weight space. Define
\[
A_t(w)=a_t(Lw),\qquad w\in U.
\]

The probability simplex is then a restriction of this ambient construction.

### Recommended theorem bundle

#### A. Existence, uniqueness, and continuity
\[
m_t(A_t(w))=Lw,
\]
and \(A_t(w)\) is the unique finite parameter with that response.

Moreover, \(A_t\) is continuous on \(U\).

This should mostly be composition with the landed chart.

#### B. Differential
Under your convention \(D_am_t=-tC\),
\[
DA_t(w)[h]
=-\frac1t\,C_{t,A_t(w)}^{-1}Lh.
\]

A schematic Lean formulation is:

```lean
-- Schematic: use the seabed's coordinate and covariance-map types.
theorem hasFDerivAt_canonicalParameter
    (ht : 0 < t)
    (hw : momentMap w ∈ interior K) :
    HasFDerivAt
      (fun w => sliceInv t (momentMap w))
      ((-(1 / t)) •
        ((covarianceInvCLM t (sliceInv t (momentMap w))).comp
          momentCLM))
      w
```

If the inverse is totalized outside its domain, the proof must use the fact that \(U\) is an open neighborhood of \(w\). No behavior of the totalized inverse outside \(U\) should enter the statement’s mathematics.

Continuity of a partial homeomorphism alone does not prove this derivative. Use the slice inverse derivative already available, or establish it once by the finite-dimensional inverse function theorem.

#### C. Exact factorization and invisible directions
\[
Lw=Lw'\Longrightarrow A_t(w)=A_t(w'),
\]
and
\[
DA_t(w)[h]=0\quad\Longleftrightarrow\quad Lh=0.
\]

For simplex directions, add \(\sum_i h_i=0\). The ambient open extension avoids unnecessary `WithinAt` complications at boundary weights.

#### D. Pullback landscapes

Define
\[
\mathsf h_t(w)=h(t,Lw),
\qquad
\mathsf S_t(w)=\mathcal S(t,Lw).
\]

Then continuity follows immediately, and
\[
D\mathsf h_t(w)[h]=\gamma^\top Lh,
\]
\[
D^2\mathsf h_t(w)[h,k]
=\kappa_3(H,V_{Lh},V_{Lk}).
\]

Because the data-to-moment map is affine, there is no extra second-derivative term. The pulled-back Fisher metric is
\[
g_w(h,k)=(Lk)^\top C^{-1}Lh.
\]
It is generally semidefinite on weights and positive definite only after quotienting invisible directions.

### Main pitfalls

1. **Not every reachable boundary moment has a finite canonical parameter.** Restrict to \(Lw\in\operatorname{int}K\).
2. **Interior component moments are a useful sufficient condition.** If every \(M_i\in\operatorname{int}K\), the whole simplex is admissible. Do not assume this for arbitrary data components.
3. **Weights are not generally identifiable.** The parameter map factors through moments.
4. **Relative versus ambient differentiability matters.** The open preimage \(U\) gives a clean ambient extension.
5. **Coordinate conventions control the factor \(t\).** The derivative is \(-t^{-1}C^{-1}\) for \(a\), but \(-C^{-1}\) for the field coordinate \(ta\), with \(t\) fixed.
6. **Do not assert convexity of the loss or prior-relative entropy landscape.** Their Hessians contain the third-cumulant bending term. The appropriate reduced dual potential has the clean inverse-covariance convexity.

This package makes the programme’s central arrow explicit:
\[
\boxed{
\text{data}
\ \longrightarrow\
\text{reachable moments}
\ \longrightarrow\
\text{canonical Gibbs distribution}
\ \longrightarrow\
\text{loss, entropy, and information geometry}.
}
\]
The existing seabed then supplies the local laws, global journeys, and boundary limits of that arrow.