## 1. Audit

The main formulas in **1, 3, and 4 are consistent**, and the normalization correction in **6 is correct**. The qualifications below matter for the mathematical narrative—and, in one case, substantially strengthen the case for a local theorem.

### Item 1: mean journey and entropy

Write \(V_a=\operatorname{featCov}_a\), and let \(M_s=M_0+s\Delta\). Then
\[
a_s'=-\frac1tV_{a_s}^{-1}\Delta,\qquad
\frac{d^2}{ds^2}I(M_s)=\Delta^\top V_{a_s}^{-1}\Delta.
\]
There is **no remaining \(t\)** in the mean-coordinate Hessian.

The KL orientations and kernels are correct:
\[
\mathrm{KL}(P_{a_1}\Vert P_{a_0})
=\int_0^1(1-s)\,\Delta^\top V_{a_s}^{-1}\Delta\,ds,
\]
whereas along \(a_s=a_0+sv\),
\[
\mathrm{KL}(P_{a_1}\Vert P_{a_0})
=t^2\int_0^1s\,v^\top V_{a_s}v\,ds.
\]
Thus the Jeffreys and length inequalities stated in item 1 follow with the given normalization.

Likewise,
\[
\operatorname{meanEntropy}(M)=I(m(0))-I(M)
\]
has gradient \(ta(M)\) and Hessian \(-V^{-1}\). Antitonicity holds along the mean ray **starting at \(m(0)\)**; it is not a statement about arbitrary oriented mean paths.

### Item 3: stability—and why localization is important

The constants are correct. In particular,
\[
\mathrm{KL}(P_b\Vert P_a)\ge
\frac{t^2\alpha}{2}\|b-a\|^2
\]
is the sharp quadratic quantitative-identifiability statement under the stated covariance lower bound. The factor \(1/2\) cannot be improved from that hypothesis alone.

But:

> For bounded, nonconstant features, a uniform positive covariance lower bound over all \(a\in\mathbb R^d\) is impossible.

Your resulting global co-Lipschitz estimate would send an unbounded parameter space into a bounded response body. Equivalently, covariance degenerates along suitable parameter rays.

So the regional version is **not merely useful bookkeeping**: it is the practically nonvacuous version for bounded features.

Keep two localization hypotheses distinct:

* **Natural-side KL bounds and bi-Lipschitz bounds:** covariance bounds along the natural segment \(a_0+s(a_1-a_0)\) suffice.
* **Mean-side KL bounds via the inverse-Hessian proof:** covariance bounds along the lifted mean segment \(a(M_0+s\Delta)\) suffice.

A convex natural region ensures the first segment stays inside; it does **not** automatically ensure that its mean image contains the mean segment. A Lean-friendly design is to prove pathwise/segmentwise lemmas first, then package convex-region corollaries.

Without nondegeneracy, quantitative identifiability belongs on the visible quotient, not the original parameter space.

### Item 4: joint chart and its domain

Yes: `hjnd` is exactly the **minimality/nondegeneracy** condition needed for the unrestricted joint family’s ordinary full-dimensional mean chart:
\[
v\cdot S\text{ a.s. constant}\Longrightarrow v=0.
\]
It gives positive-definite \(G_\theta\) at every finite parameter, because exponential tilting preserves null sets.

Under your landed bounded/full-natural-domain assumptions,
\[
\operatorname{range}(\operatorname{fullMean})
=\operatorname{int}K,
\]
where \(K\) is the **closed convex hull of the essential support** of \(S\). Essential support matters: null-set feature values must not enlarge the body.

Two qualifications:

1. `hjnd` alone is not a general unbounded-family surjectivity theorem; the analytic assumptions behind `range_meanMap_slice` remain necessary.
2. This is the chart for **all joint natural parameters**
   \(\theta\in\mathbb R^{d+1}\). The physical parametrization
   \((t,a)\mapsto(t,ta)\), \(t>0\), covers only \(\theta_0>0\), whose mean image need not be convex. Apply the full-mean concavity theorem on \(\operatorname{int}K\), rather than silently identifying that domain with the positive-temperature image.

The entropy gradient, Hessian, and two-journey equality in item 4 are correct:
\[
\nabla_\mu\mathcal S=\theta(\mu),\qquad
D^2_\mu\mathcal S=-G_{\theta(\mu)}^{-1}.
\]

### Item 6: determinant normalization

Yes. In feature dimension \(d\), for \(t>0\),
\[
C=tV,\qquad \log\det C=d\log t+\log\det V,
\]
hence, at fixed response,
\[
-\partial_t\log\det C
=\operatorname{tr}(VK)-\frac dt.
\]

There is one important interpretive condition: the \(H\) in
\[
\partial_tV\big|_M=-T,\qquad
T_{ij}=\kappa_3(H,R_i,R_j)
\]
must be the **effective score along the fixed-response temperature path**, not simply \(L_0+a\cdot R\) with \(a\) held fixed.

Writing \(c=\operatorname{Cov}(R,L_0)\), it is, up to an irrelevant constant,
\[
H=L_0-R_{V^{-1}c}.
\]
Equivalently, \(H=L_0+R_{a+ta'}\), with \(a+ta'=-V^{-1}c\).

---

## 2. Ranking the missing pieces

My ranking for **depth and programme completion** is:

1. **(i) Slice/full compatibility: variational profiling, exact Pythagoras, Schur complement.**
2. **(iii) Full bounded-feature LDP, including the open lower bound.**
3. **(iv) Walls: ray concentration onto exposed faces and directional covariance collapse.**
4. **(ii) Arbitrary mean-path entropy balance.**
5. **(vi) Finite-sample fluctuation–response.**
6. **(v) Connections and mixture curvature.**

Implementation order need not follow that ranking: **(ii) and (vi) are excellent small corollaries to land immediately**.

The additional unifying piece is this:

> Slice profiling is simultaneously an information projection, a Schur-complement reduction of the Fisher metric, and a contraction of the full large-deviation rate.

That is the next capstone. It connects geometry, entropy, temperature, and probability rather than adding another isolated identity.

---

## 3. Top-pick theorem bundle: “profile geometry”

Use unrestricted joint coordinates
\[
\theta=(\tau,\eta),\qquad \mu=(u,M),
\]
where \(u=\langle L_0\rangle\), \(M=\langle R\rangle\). At physical temperature \(t>0\), \(\eta=ta\).

Let
\[
J(\mu)=-\theta(\mu)\cdot\mu-A(\theta(\mu)),
\]
and define the fixed-\(t\) lift
\[
\widehat\mu_t(M)=(u_t(M),M),\qquad
\theta(\widehat\mu_t(M))=(t,\eta_t(M)).
\]
Then
\[
I_t(M)=-\eta_t(M)\cdot M-A(t,\eta_t(M)).
\]

### A. Variational profiling, with an exact gap

For every admissible \((u,M)\),
\[
\boxed{
J(u,M)+tu-I_t(M)
=
\mathrm{KL}\!\left(P_{\theta(u,M)}
\,\middle\Vert\,P_{t,\eta_t(M)}\right).
}
\]
Consequently,
\[
\boxed{
I_t(M)=\min_{u:(u,M)\in\operatorname{int}K}
\{J(u,M)+tu\},
}
\]
with unique minimizer \(u_t(M)\).

This precisely answers the “\(\langle L_0\rangle\) free” question:

* The slice mean lift lets \(u\) vary.
* But \(u\) is **not arbitrary**: it minimizes the temperature-penalized full dual potential at each \(M\).
* The lift of a straight \(M\)-segment is generally **not a straight full-mean segment**, because \(u_t(M)\) is generally nonlinear.

Thus “constrained full m-journey” needs this variational interpretation, not a claim of affine geodesicity.

Suggested theorem shapes:

```text
profile_gap_eq_kl
profile_le
profile_eq_iff
sliceLift_unique_minimizer
```

Prove the gap identity first; obtain minimization from KL nonnegativity.

### B. Exact Pythagorean decomposition

For any full-family point \(Q=P_{\theta(u,M)}\) and any slice reference \(P_{t,\eta_0}\),
\[
\boxed{
\mathrm{KL}(Q\Vert P_{t,\eta_0})
=
\mathrm{KL}(Q\Vert P_{t,\eta_t(M)})
+
\mathrm{KL}(P_{t,\eta_t(M)}\Vert P_{t,\eta_0}).
}
\]

This is the desired decomposition into:

* a **fixed-response temperature leg**, from \(Q\) to its slice lift;
* a **slice response leg**, from that lift to the reference.

The proof is algebraic: the log-density ratio between the two slice distributions is affine in \(R\), and \(Q\) and its lift have the same \(R\)-mean.

**Pitfalls:** orientation matters; this is a KL/Pythagorean decomposition, not an additive decomposition of Fisher lengths. The temperature leg holds \(M\) fixed—not \(a\), and not \(\eta\).

### C. Schur complement: the metric decomposition

Write
\[
G=
\begin{pmatrix}
\sigma^2&c^\top\\
c&V
\end{pmatrix},
\qquad
\delta=\sigma^2-c^\top V^{-1}c.
\]
Under `hjnd`, \(\delta>0\), and
\[
\delta
=\operatorname{Var}\!\left(L_0-R_{V^{-1}c}\right).
\]

For full mean velocity \((\dot u,\dot M)\),
\[
\boxed{
(\dot u,\dot M)^\top G^{-1}(\dot u,\dot M)
=
\dot M^\top V^{-1}\dot M
+
\frac{(\dot u-c^\top V^{-1}\dot M)^2}{\delta}.
}
\]

This is an especially beautiful statement:

> The slice inverse-covariance metric is the minimum full inverse-covariance cost among all lifts of a prescribed response velocity.

The minimizing lift satisfies
\[
\dot u=c^\top V^{-1}\dot M,
\]
which is exactly the fixed-temperature slice tangent.

For Lean, a block linear-system proof may be easier than importing a general block-matrix inverse formula.

### D. Mixed coordinates \((t,M)\)

The derivative identities are
\[
D_Mu_t=c^\top V^{-1},\qquad
\partial_tu_t\big|_M=-\delta,\qquad
\partial_t\eta_t\big|_M=-V^{-1}c.
\]
Thus in mixed coordinates,
\[
\boxed{
g=\delta\,dt^2+dM^\top V^{-1}dM.
}
\]

The temperature and response directions are orthogonal in this chart. This gives a precise infinitesimal companion to the exact KL Pythagoras.

It also identifies the fixed-response score \(H\) used in your contraction theorem.

### E. Profile derivatives and entropy balance

The profile potential satisfies
\[
\partial_tI_t(M)=u_t(M),\qquad
\partial_t^2I_t(M)=-\delta.
\]
Hence the same residual fluctuation controls both temperature response and temperature concavity.

For any differentiable full mean path,
\[
\frac d{ds}\mathcal S
=t\,u'+\eta\cdot M'.
\]
In mixed coordinates this becomes
\[
\frac d{ds}\mathcal S
=-t\delta\,t'
+\bigl(\eta+tV^{-1}c\bigr)\cdot M'.
\]
In particular, along a fixed-response temperature path,
\[
\boxed{\partial_t\mathcal S\big|_M=-t\delta.}
\]

Call this an **entropy balance** before calling it entropy production: arbitrary path reversal reverses its sign. The monotonicity statement needs an oriented path, such as increasing \(t\ge0\) at fixed \(M\).

### F. Large-deviation contraction

Relative to \(P_{t,0}\), the full rate on interior joint means is
\[
\mathcal J_t(u,M)=J(u,M)+tu+A(t,0).
\]
Profiling gives
\[
\boxed{
\inf_u\mathcal J_t(u,M)
=I_t(M)+A(t,0)
=\mathrm{KL}(P_{t,\eta_t(M)}\Vert P_{t,0}).
}
\]

So `slice_variational`, Pythagoras, and rate contraction are three presentations of the same structure. State the interior result first; boundary contraction requires the extended rate, not an inverse chart at boundary points.

---

## 4. The other candidates: sharp targets and cautions

### Complete LDP

For bounded features, yes: the closed upper bound is the compact upper bound applied to \(F\cap B\), where \(B\) is a compact box containing every empirical response almost surely. No substantive exponential-tightness machinery is needed.

For the lower bound:

1. Tilt to an interior mean \(M\).
2. Use concentration under the tilted law and your likelihood-ratio lower bound.
3. Optimize over interior points of the open set.
4. Handle finite-rate boundary points by interior approximation.

Step 4 should not be omitted. If \(M_*\) is an interior mean with finite rate, then
\[
M_\lambda=(1-\lambda)M+\lambda M_*
\]
lies in the interior and, by convexity of the rate, approximates \(M\) without increasing its limiting cost. This bridges the chart’s interior domain and the full LDP.

### First wall theorem

For the bounded family, integrability loss is absent and finite-parameter inverse-chart failure is absent under nondegeneracy. The clean first target is therefore:

> Along a natural parameter ray, mass concentrates on an exposed minimizing face, and covariance in the ray direction vanishes.

For \(a=rv\), \(r\to\infty\), \(t>0\), let
\[
h=\operatorname*{ess\,inf} R_v.
\]
Relative to the slice base law \(P_{t,0}\),
\[
P_{t,rv}(R_v\ge h+\varepsilon)
\le
\frac{e^{-tr\varepsilon/2}}
{P_{t,0}(R_v\le h+\varepsilon/2)}.
\]
This yields
\[
v\cdot m_t(rv)\to h,\qquad
\operatorname{Var}_{t,rv}(R_v)\to0.
\]

Geometrically, the mean approaches the exposed face
\[
\{M\in K_R:v\cdot M=h\}.
\]
Do not claim convergence to a unique point unless that face is a singleton; tangential covariance can survive.

### Finite-sample fluctuation–response

For \(n\ge1\) independent posterior samples,
\[
\operatorname{Cov}(\overline R_n)=\frac1nV_a.
\]
Combined with \(Dm_t(a)=-tV_a\),
\[
\boxed{\operatorname{Cov}(\overline R_n)=-\frac1{nt}Dm_t(a).}
\]
This is a short, worthwhile bridge from response geometry to observable sampling noise.

### Connections

The mathematics is attractive, but label it carefully: \(D^2m=t^2\kappa_3\) is the second derivative of the coordinate transition. Calling it a second fundamental form requires a specified ambient statistical geometry and embedding. The cubic tensor and dual connections are the safer intrinsic first statements.

---

## 5. Consolidation of the seven-theorem overview

**Yes: update theorem V now.** The duality capstone is the precise result, not an optional corollary after the overview.

I would replace its central statement by something like:

> **V. Dual response geometry and the two journeys.**  
> On the visible mean domain, the natural-to-mean chart has derivative \(-tV\), its dual potential has Hessian \(V^{-1}\), and KL admits paired natural- and mean-segment fluctuation integrals. Relative entropy is concave in slice mean coordinates; in the joint family, entropy relative to the normalized prior is concave in full mean coordinates with Hessian \(-G^{-1}\).

Display the two KL integrals together. Then display
\[
\nabla_\mu\mathcal S=\theta,\qquad D^2_\mu\mathcal S=-G^{-1}.
\]
Those are the conceptual summit.

Without the current seven statements in front of us, I would preserve their numbering rather than manufacture a replacement architecture. The other changes should be surgical:

* **Identifiability theorem:** state the invisible quotient globally; distinguish it from quantitative conditioning.
* **Stability theorem:** present segmentwise/local ellipticity as primary, global ellipticity as a corollary.
* **Contraction theorem:** explicitly say “fixed response” and distinguish \(V\) from \(tV\).
* **Probability theorem:** identify the rate as the same dual potential, rather than a separately named construction.
* **Boundary discussion:** distinguish finite interior geometry from asymptotic face degeneration.
* **After profile geometry lands:** attach its Pythagoras and Schur-complement identities to V as the compatibility theorem linking slice and full geometry.

Finally, turn the 40-plus paragraphs into a dependency-organized catalogue beneath the overview: **chart → duality → journeys → conditioning → temperature compatibility → sampling/asymptotics → walls**. The overview should express the structure; the catalogue should document the formal coverage.