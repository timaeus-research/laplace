## Executive recommendation

**Make the next programme a calibrated response atlas:** first connect sampling energy to the deterministic certificate, then complete the observable Hessian calculus, and finally identify the saturated geometry explicitly.

There are two important audit points:

1. **“Every data law” must mean the laws in the seabed’s `DataLaw`, not every probability measure on \(X\).**
2. **Residual saturation must not silently be identified with `SpansAffine`.** Universal flatness of model-observable responses can hold while the statistics still discard within-fibre information.

Those qualifications strengthen, rather than diminish, the programme: they distinguish the geometry of the response quotient from identification of the original data law.

# Q1. Audit

This is an audit of the mathematical summary, not an inspection of the Lean declarations.

## A. Global hypotheses worth keeping visible

Several assumptions should appear prominently in the theorem-facing documentation:

- \(\nu\) is a probability measure, or the relative-entropy statements have the appropriate normalization.
- The Fisher form is positive definite **on \(W\)**; invisible directions have been removed.
- The inverse mean map is used only on its actual image
  \[
  \mathcal M=m(W),
  \]
  not on all of \(W\). Every local Taylor ball must lie in \(\mathcal M\).
- Observable and data-law integrability requirements are explicit. Bounded observables and bounded log-tilts make many of these automatic.
- “Geodesic at \(t\)” in the response-line criterion means **zero affine-parameter Levi–Civita acceleration**. It is stronger than being an unparameterized geodesic.

The last distinction matters even for a two-point simplex: a monotone one-dimensional response journey follows the minimizing geodesic image, but its mean-affine parameter need not be an affine geodesic parameter.

Also, “featureless maximum entropy” means **maximum entropy relative to \(\nu\)**. It is ordinary maximum Shannon entropy only when the reference masses are uniform.

## B. H3: identification without finite \(X\)

### The right statement

Under `SpansAffine`, the conclusion

> Every admissible `DataLaw ν` is a member of the exponential family

is correct, assuming an admissible data law has a log-density to which `SpansAffine` applies.

For example, if
\[
\rho_g(dx)=\frac{e^{g(x)}}{\int e^g\,d\nu}\nu(dx),
\qquad
g=\langle b,S\rangle+k\quad \nu\text{-a.e.},
\]
then directly
\[
\rho_g=P_{-b}.
\]
The invisible-direction API is exactly the right way to replace \(-b\) by its identifiable representative without choosing coordinates prematurely.

But it does **not** follow that every probability measure on \(X\) is a finite-parameter model law. In particular:

- finite exponential tilts are equivalent to \(\nu\);
- laws that put zero mass on a positive-\(\nu\) atom are generally boundary laws;
- singular laws are excluded;
- if `DataLaw` restricts log-densities, that restriction remains part of the statement.

### Does it need finite \(X\)?

No. The proof does not need literal finiteness of the underlying set.

However, with finite-dimensional \(W\), `SpansAffine` is extremely strong: the space of bounded measurable functions modulo \(\nu\)-a.e. equality is finite-dimensional. In the usual probability-space formulation, this forces a **finite atomic measure algebra**. An atom need not be a singleton, and \(X\) may contain arbitrarily many null points.

Thus the honest interpretation is:

> Finiteness of \(X\) is unnecessary; finite-dimensional full saturation forces finiteness of the observable measure algebra.

The eventual dimension statement should therefore be:

- finite discrete specialization:
  \[
  \dim W=|\{x:\nu\{x\}>0\}|-1;
  \]
- general formulation: number of positive measure-algebra atoms minus one.

Do not use topological support cardinality without additional assumptions.

Finally, a bijection alone does not establish `≃ₜ`. Your existing continuity of `lawResponse` and `modelLaw` supplies the necessary extra content; the topology on `DataLaw` should remain explicit.

## C. H1: flatness, legitimate tests, and a possible ambiguity

### The test \(F=r\) is legitimate

At a fixed \(\theta\), \(u\), and \(v\), the residual \(r_{uv}\) is a bounded measurable function, given bounded measurable \(S\). For diagonal flatness, take
\[
F=r_{uu}
\]
**frozen at the base point**. Do not differentiate a moving observable \(F_t=r^{\theta_t}_{u_tu_t}\).

Since \(E_\theta r_{uu}=0\), vanishing second response gives
\[
0=E_\theta[(r_{uu}-E_\theta r_{uu})r_{uu}]
  =E_\theta[r_{uu}^{\,2}].
\]
Hence \(r_{uu}=0\) almost everywhere. Polarization gives all \(r_{uv}=0\).

The quantification is nonvacuous provided:

- every tangent direction is represented by \(e=A_\theta u\);
- the response curve exists on an open interval around the base point;
- flatness ranges over all bounded measurable observables, not merely the sufficient statistics.

The last condition is essential: expectations of the sufficient statistics are affine along response lines by construction.

### What is pointwise?

The analytic equivalence is pointwise:
\[
\bigl(\forall F,e,\ D^2\mathcal R_F(m(\theta))[e,e]=0\bigr)
\quad\Longleftrightarrow\quad
\bigl(\forall u,v,\ r^\theta_{uv}=0\text{ a.e.}\bigr).
\]

Promoting this to a globally named property of the family requires a separate identification or propagation theorem.

### Residual saturation need not mean full identification

Here is the diagnostic example:

- \(X=\{1,2,3,4\}\);
- \(\nu\) uniform;
- \(S=\mathbf 1_{\{1,2\}}\).

The model changes the mass allocated to the two blocks while retaining uniform conditionals within each block. Every bounded observable has model expectation affine in the block mass. Thus all second response derivatives vanish.

Nevertheless, `SpansAffine` fails: an observable distinguishing \(1\) from \(2\) is not affine in \(S\). Many admissible data laws are not model laws.

Consequently:

> If `SATURATION` means residual closure, H1 is correct as summarized. If it means `SpansAffine` on all of \(X\), an observability hypothesis is missing.

A useful naming distinction would be **response-flat saturation** versus **full data-law saturation**.

## D. H6: the clean Fisher bridge

The correct Fisher-normalized norm for **mean noise** is not usually \(z\mapsto\sqrt{G_{\theta_0}(z,z)}\). It is the pullback through the inverse mean derivative:
\[
q_0(z)
 :=G_{\theta_0}(A_{\theta_0}^{-1}z,A_{\theta_0}^{-1}z),
\qquad
|z|_{*,0}:=\sqrt{q_0(z)}.
\]

Under the Euclidean identification \(A_0=-G_0^\sharp\),
\[
q_0(z)=\langle z,(G_0^\sharp)^{-1}z\rangle.
\]

First prove that this quadratic form is exactly the existing `samplingEnergy` quadratic form. Do not infer this merely from the word “Fisher-normalized.”

Define constants
\[
B_0=\sup_{|z|_{*,0}=1}\|z\|,
\qquad
\gamma_{\ell,0}
 =\sup_{G_0(v,v)=1}|\ell(v)|.
\]
Then
\[
\|z\|\le B_0|z|_{*,0},
\qquad
|\ell(A_0^{-1}z)|\le\gamma_{\ell,0}|z|_{*,0}.
\]

These give the improved certificate, on \(|\xi|_{*,0}\le r\):
\[
\boxed{
\ell(\widehat\theta)-\ell(\theta_0)
\ge
t\ell(A_0^{-1}e)
-\gamma_{\ell,0}r
-\|\ell\|K\bigl(|t|\|e\|+B_0r\bigr)^2
}
\]
provided \(|t|\|e\|+B_0r\le\delta\).

This is cleaner and sharper than bounding the linear noise term by
\(\|\ell\|\|A_0^{-1}\|B_0r\).

For the inherited coordinate sup norm, there is an especially pleasant formula. Writing \(\pi_j:W\to\mathbb R\) for coordinate evaluation and \(\pi_j^\sharp\) for its Euclidean representative,
\[
B_0=\max_j\sqrt{G_0(\pi_j^\sharp,\pi_j^\sharp)}.
\]
When the centered statistic lies in \(W\), this becomes
\[
B_0=\max_j\sqrt{\operatorname{Var}_{\theta_0}(S_j)}.
\]
Alternatively, \(\sqrt{\lambda_{\max}(G_0^\sharp)}\) is a simple valid bound.

Handle \(W=\{0\}\) separately or define the constants without a nonempty unit-sphere assumption.

# Q2. Next programme: six modules

I recommend the following implementation order.

| Rank | Module | Main payoff | Cost |
|---|---|---|---|
| 1 | `ResponseFisherNoiseBridge` | Exact compatibility of geometry and sampling | Low–medium |
| 2 | `ResponseProbabilisticResolution` | End-to-end chamber certification | Low after 1 |
| 3 | `ResponseObservableHessian` | Complete second-order observable calculus | Low |
| 4 | `ResponseLocalizedSamplingBias` | Statistical meaning of connection/third tensor | Medium |
| 5 | `ResponseSaturatedSimplex` | Concrete identification and dimension | Medium–high |
| 6 | `ResponseSimplexSphere` | Explicit intrinsic distance and optimal journeys | High, controlled after 5 |

The first three are the best immediate return. The last two supply the geometric culmination.

## 1. `ResponseFisherNoiseBridge`

### Statements

Prove:

1. positive definiteness of \(q_0\);
2. identification with the seabed’s sampling quadratic form;
3. \(\|z\|\le B_0\sqrt{q_0(z)}\);
4. \(|\ell(A_0^{-1}z)|\le\gamma_{\ell,0}\sqrt{q_0(z)}\);
5. the Fisher-radius version of H6.

### Proof route

Use the positive-definite Fisher form to equip \(W\) with a temporary inner-product structure, or keep everything as inequalities between quadratic forms. The latter may be cheaper in Lean than changing normed-space instances.

Separate:

- a generic finite-dimensional quadratic-form comparison theorem;
- its response-map specialization;
- the optional exact sup-norm constant.

This avoids paying spectral-theory costs merely to obtain an explicit finite constant.

## 2. `ResponseProbabilisticResolution`

Let \(X_1,\ldots,X_n\) be i.i.d. from a data law \(D\), and suppose
\[
E_D S=m(\theta_0)+te.
\]
Set
\[
\xi=\frac1n\sum_i S(X_i)-E_D S,
\qquad
\tau_0(D)=\operatorname{tr}(R_{\theta_0}C_D).
\]
After the quadratic-form identification,
\[
\Pr\{|\xi|_{*,0}>r\}
\le \frac{\tau_0(D)}{nr^2}.
\]

### Main theorem

If
\[
|t|\|e\|+B_0r\le\delta
\]
and
\[
t\ell(A_0^{-1}e)>
\gamma_{\ell,0}r+
\|\ell\|K(|t|\|e\|+B_0r)^2,
\]
then, with probability at least
\[
1-\frac{\tau_0(D)}{nr^2},
\]
the empirical response exists in the local inverse chart and satisfies
\[
\ell(\widehat\theta)>\ell(\theta_0).
\]

For failure probability \(\alpha\), choose
\[
r=\sqrt{\frac{\tau_0(D)}{n\alpha}},
\]
with the zero-variance case handled separately.

### Crucial honesty point

An empirical mean can lie on the boundary of the mean polytope with positive probability, even when the generating law is strictly positive. Therefore the theorem should certify **both local existence and the sign**, rather than assume a globally defined finite empirical response.

This module supplies the requested resolution story:

> Chamber crossing is certifiable when the directional truth shift exceeds sampling uncertainty plus nonlinear chart distortion.

Failure of this certificate means **not certified**, not automatically **statistically impossible**. A genuine impossibility theorem requires a testing lower bound; that is an excellent subsequent programme.

## 3. `ResponseObservableHessian`

Write
\[
\mathcal R_F(y)=E_{P_{m^{-1}(y)}}F,
\qquad
u=A_\theta^{-1}e,\quad v=A_\theta^{-1}d.
\]

### Mixed second response

Prove
\[
D^2\mathcal R_F(m(\theta))[e,d]
=
E_\theta[(F-E_\theta F)r_{uv}].
\]

Polarization is the cheapest proof **once the response observable is known to be \(C^2\)** and its Hessian is a symmetric bilinear map. Diagonal directional derivatives alone should not substitute for that regularity statement.

The estimate also polarizes into the useful bilinear bound
\[
|D^2\mathcal R_F[e,d]|
\le
\sqrt{\operatorname{Var}_\theta F}\,
\sqrt{E_\theta[r_{uv}^2]}.
\]

### Variance Hessian

Prove the more general mixed formula:
\[
D^2\operatorname{Var}(F)[e,d]
=
E_\theta[(F-E_\theta F)^2r_{uv}]
-
2D\mathcal R_F[e]D\mathcal R_F[d].
\]

Your proposed line formula follows immediately.

### Saturated consequence

Under residual flatness,
\[
D^2\operatorname{Var}(F)
=
-2\,D\mathcal R_F\otimes D\mathcal R_F.
\]
Thus posterior variance is concave on the convex mean domain, with a negative-semidefinite Hessian of rank at most one.

For a finite vector of observables, the covariance matrix is concave in Loewner order. This is a particularly good “beauty per Lean cost” corollary.

The exact mixture identity explains the geometry:
\[
\operatorname{Var}_{(1-t)P+tQ}F
=(1-t)\operatorname{Var}_P F+t\operatorname{Var}_Q F
+t(1-t)(E_PF-E_QF)^2.
\]

## 4. `ResponseLocalizedSamplingBias`

This is the natural statistical interpretation of \(C\).

Let \(h=m^{-1}\), based at \(y=m(\theta)\). Then
\[
D^2h(y)[e,d]
=
-C_\theta(A_\theta^{-1}e,A_\theta^{-1}d).
\]
A local \(C^3\) Taylor theorem gives
\[
h(y+z)
=
\theta+A_\theta^{-1}z
-\frac12C_\theta(A_\theta^{-1}z,A_\theta^{-1}z)
+O(\|z\|^3).
\]

For \(Z=S(X)-E_D S\), the leading sampling bias is consequently
\[
\boxed{
E[\widehat\theta_{\mathrm{loc}}]-\theta
=
-\frac1{2n}
E_D\!\left[
C_\theta(A_\theta^{-1}Z,A_\theta^{-1}Z)
\right]
+\text{controlled remainder}.
}
\]

For model sampling, the leading contraction is the Fisher trace:
\[
-\frac1{2n}\operatorname{tr}_{G_\theta}C_\theta.
\]

### Localization must be explicit

Do not write
\[
E[\xi\mid \|\xi\|\le\delta]=0.
\]
It is generally false.

For a reset localization
\[
\widehat\theta_{\rm loc}
=\theta+\mathbf1_E\bigl(h(y+\xi)-\theta\bigr),
\qquad E=\{\|\xi\|\le\delta\},
\]
the remainder includes:

- a truncated linear-mean term;
- a truncated quadratic-moment term;
- the cubic Taylor remainder.

A useful bound is
\[
\begin{aligned}
\|\text{remainder}\|
\le{}&
\|A_\theta^{-1}\|E[\|\xi\|\mathbf1_{E^c}]\\
&+\tfrac12\|B_\theta\|E[\|\xi\|^2\mathbf1_{E^c}]
+K_3E[\|\xi\|^3\mathbf1_E],
\end{aligned}
\]
where \(B_\theta[z,z]=C_\theta(A_\theta^{-1}z,A_\theta^{-1}z)\).

For bounded i.i.d. statistics in fixed dimension, a fourth-moment bound gives the first two terms \(O(n^{-2})\) for fixed \(\delta\), and the third \(O(n^{-3/2})\). No concentration machinery is necessary for this first theorem.

The reset estimator is a localization device, not automatically a practical estimator when \(\theta\) is unknown. Say so.

## 5. `ResponseSaturatedSimplex`

Specialize to a finite positive support
\[
I=\{x:\nu\{x\}>0\},
\]
under full `SpansAffine`.

### Main statements

1. \(\dim W=|I|-1\).
2. Model laws identify with
   \[
   \Delta_I^\circ
   =\{p:I\to\mathbb R:\ p_i>0,\ \sum_i p_i=1\}.
   \]
3. The mean map becomes the barycentric map
   \[
   p\longmapsto\sum_i p_iS(i).
   \]
4. The featureless response journey becomes
   \[
   p_t=(1-t)\nu+t\,p_{\rm data}.
   \]

### Proof route

The decisive linear algebra is the evaluation map
\[
W\longrightarrow
\left\{a:I\to\mathbb R:\sum_i\nu_i a_i=0\right\},
\qquad
b\longmapsto
\langle b,S-E_\nu S\rangle.
\]
Injectivity comes from removing invisible directions; surjectivity comes from `SpansAffine`.

For law identification, use
\[
g_i=\log(p_i/\nu_i)
\]
and H3. Package equality of measures from atom masses once, rather than repeatedly rewriting densities.

This module also establishes affine independence of the support statistic vectors. Without full saturation, their convex hull need not be a simplex and barycentric coordinates need not be unique.

## 6. `ResponseSimplexSphere`

Use the square-root embedding
\[
\Psi(p)=2(\sqrt{p_i})_{i\in I}.
\]
Its pullback metric is
\[
g_p(\dot p,\dot p)=\sum_i\frac{\dot p_i^2}{p_i}.
\]

For
\[
\alpha=\arccos\sum_i\sqrt{p_iq_i},
\]
the minimizing path is
\[
p_i(t)=
\left[
\frac{\sin((1-t)\alpha)}{\sin\alpha}\sqrt{p_i}
+
\frac{\sin(t\alpha)}{\sin\alpha}\sqrt{q_i}
\right]^2,
\]
with \(p=q\) treated separately.

Then
\[
\boxed{d_F(p,q)=2\arccos\sum_i\sqrt{p_iq_i}.}
\]

### Proof architecture

Prove this first for the abstract positive simplex:

1. square-root metric identity;
2. positivity and normalization of the great-circle path;
3. constant speed \(2\alpha\);
4. spherical lower bound for arbitrary admissible paths.

Only then transport it through Module 5 to the response family. This keeps differential geometry separate from atom bookkeeping.

For a nonsaturated family, the ambient sphere yields a **lower bound**
\[
d_F^{\rm model}(P,Q)\ge
2\arccos\!\int\sqrt{dP\,dQ},
\]
not generally equality: the spherical geodesic may leave the model.

# What I would defer

## A. A bare curvature-to-length-defect estimate

I would not promise
\[
L_F-d_F\lesssim\int\|C(\theta',\theta')\|
\]
without substantial additional hypotheses and a precise parameter convention.

For a mean-affine response line, the conventions in the question give
\[
\nabla^{LC}_{\dot\theta}\dot\theta
=-\frac12C(\dot\theta,\dot\theta).
\]
That is a useful exact theorem. But acceleration alone does not globally control failure to minimize: a geodesic can pass beyond its minimizing interval while its acceleration remains zero.

Furthermore, unparameterized bending is controlled by the **normal component** of acceleration, not its tangential speed-change component.

An honest quantitative theorem would need, for example:

- containment in a suitable convex normal neighborhood;
- curvature and injectivity-radius control;
- speed bounds or arc-length parameterization;
- a stated comparison theorem.

For now, the simplex sphere gives a cleaner exact comparison. Along the saturated featureless journey,
\[
L_F
=\int_0^1
\sqrt{\sum_i
\frac{(p_i-\nu_i)^2}{(1-t)\nu_i+tp_i}}
\,dt
\;\ge\;
2\arccos\sum_i\sqrt{\nu_ip_i}.
\]

## B. Two-scale CLT before the finite-sample theorem

The CLT is valuable, but the finite-probability certificate is both more immediately usable and more faithful to the resolution question. Build it first.

The subsequent lower-bound counterpart is also important: to prove genuine unresolvability, formulate two nearby data laws lying in different response chambers and bound their \(n\)-sample distinguishability. That turns the current sufficient resolution condition into a statistically meaningful two-sided story.

# Q3. Headline for D–H

\[
\boxed{
\theta_t=m^{-1}\!\bigl(m(0)+te\bigr),
\qquad
\frac{d}{dt}E_{P_{\theta_t}}F
=-\operatorname{Cov}_{\theta_t}
 \!\left(F,\left\langle A_{\theta_t}^{-1}e,S\right\rangle\right),
\qquad
\mathcal I''(t)
=G_{\theta_t}(A_{\theta_t}^{-1}e,A_{\theta_t}^{-1}e).
}
\]

Here \(e=E_\rho S-E_\nu S\): affine motion through data moments induces a canonical journey from the reference law to the information projection of the data. Fisher geometry measures its information cost, residuals measure nonlinear observable response, and the two-scale certificate separates directional truth shift from sampling uncertainty.

**The single most important remaining deliverable:** an end-to-end finite-sample theorem certifying existence and chamber orientation of the empirical response, with its target explicitly identified as \(P_{\Phi(g)}\)—not, outside full saturation, the entire original data law.