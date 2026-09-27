## Overall recommendation

**The next central theorem should connect the curvature defect to the response of arbitrary posterior observables.** It turns G3 from a curvature formula into an operational statement about what the response map does—and does not—capture.

Then complete two complementary pictures:

- an **exact global benchmark**: the saturated finite simplex as a spherical response manifold;
- an **honest sampling theory**: localized second-order bias and two-scale sign resolution, without pretending that empirical natural parameters always exist.

That is a coherent next programme. General geodesic ODEs and Gauss–Bonnet should wait.

---

# Q1. Audit

This is an audit of the mathematical summaries, not of the Lean declarations. I see no inherent contradiction in G, but several qualifications belong in its public statements.

## G2: the regression argument is sound

Let \(r\) be the residual after regression, and write
\[
c_r=\operatorname{Cov}_{P_\theta}(S,r).
\]
The essential argument is exactly:

1. domination gives \(c_r\in W\);
2. orthogonality to every structural score gives
   \(\langle u,c_r\rangle=0\) for every \(u\in W\);
3. hence \(c_r=0\);
4. `SpansAffine` gives \(r=\langle d,S\rangle+k\) almost everywhere;
5. consequently
   \[
   \operatorname{Var}_{P_\theta}(r)=\langle d,c_r\rangle=0.
   \]

The coefficient \(d\) need **not** belong to \(W\). This is precisely why the argument avoids any need to interpret `dirProj` as an orthogonal projection.

Thus `covVec_mem_dirSpan`, together with the already-proved score orthogonality and affine representability, really is sufficient. No stronger identity involving `invisibleSet` is needed.

### Is the a.e. formulation right?

Yes. It is the measure-invariant formulation:

- null support points should not affect saturation;
- bounded tilts are equivalent to \(\nu\), so \(\nu\)-a.e. representability transfers to every \(P_\theta\);
- the quantified functions should be the relevant bounded measurable observables, not arbitrary nonmeasurable functions.

Two qualifications:

- For a finite \(X\), the dimension is \(|\operatorname{supp}\nu|-1\), not necessarily \(|X|-1\).
- “\(K=1/4\)” is a statement about genuine two-planes. In dimensions zero or one it supplies no nonvacuous sectional-curvature assertion. If `K` is totalized using division by zero, retain the nondegenerate-plane hypotheses explicitly.

## G6: “the same jet for truth and sampling” needs a domain qualification

The deterministic statement is excellent. It does **not**, by itself, define \(\Phi(\widehat\rho_n)\).

There are two distinct obstacles:

1. An empirical law generally is not a bounded tilt of \(\nu\). In a nonatomic setting it may even be singular.
2. Its empirical moment can lie on the boundary of the moment body. Then a finite natural parameter need not exist.

In the saturated finite simplex, zero counts are exactly this second problem. In an unsaturated model, some zero counts can still yield an interior moment, so “zero counts imply failure” is not universally correct.

Recommended wording:

> The inverse-mean response has a single deterministic second jet, applicable both to truth perturbations and to empirical-moment perturbations whenever those moments lie in its interior domain. Sampling applications therefore require an interior event, localization, or an explicitly regularized estimator.

If the true moment is interior and observations are i.i.d. bounded, the empirical moment lies in a fixed interior neighborhood with probability tending to one, with quantitative concentration available. But this does not make the unlocalized estimator defined everywhere, nor justify an unconditional expectation of it.

## G5: sharpness and the square root of Jeffreys divergence

### Is \(d_F^2\le J\) sharp?

**Infinitesimally, yes, with optimal constant one.** For \(v\ne0\),
\[
d_F(\theta,\theta+\varepsilon v)^2
 =\varepsilon^2G_\theta(v,v)+o(\varepsilon^2),
\qquad
J(\theta,\theta+\varepsilon v)
 =\varepsilon^2G_\theta(v,v)+o(\varepsilon^2).
\]

Exact equality at distinct endpoints is much more restrictive. The proof through the natural segment requires both:

- that segment to minimize length;
- its Fisher speed to be constant.

In the present bounded-feature setting, constant nonzero speed along a nontrivial natural segment is impossible. Indeed, it would make the log-partition function quadratic along that line; real analyticity extends this identity, contradicting boundedness of the corresponding tilted mean. Thus distinct endpoints should give strict inequality here. This strictness is a separate theorem, not something automatically certified by the existing upper-bound proof.

Outside the bounded-feature setting, exact equality can occur—for example in fixed-covariance Gaussian location families.

### Is \(\sqrt J\) a metric?

The safe assertion is:

> The square root of Jeffreys divergence is not a metric in general, even within a one-dimensional exponential family.

Bernoulli distributions already suffice. For \(p<q\),
\[
J(p,q)=(q-p)\bigl(\operatorname{logit}q-\operatorname{logit}p\bigr).
\]
For \(p<q<r\), AM–GM gives
\[
\sqrt{J(p,r)}
\ \ge\
\sqrt{J(p,q)}+\sqrt{J(q,r)},
\]
with strict inequality unless the two logit secant slopes agree. Taking \(p=0.1,q=0.2,r=0.5\) gives a strict violation of the triangle inequality.

But “it is never a metric for an exponential family” is false: Gaussian location families provide a counterexample to that blanket claim.

---

# Q2. Recommended programme H

## Ranking

| Priority | Direction | Reason |
|---|---|---|
| 1 | Observable and fluctuation response | Directly answers the user; gives G3 a new operational meaning |
| 2 | Localized sampling bias and two-scale resolution | Completes the truth-versus-sampling story honestly |
| 3 | Finite simplex identification and spherical distance | Exact global model, explicit geodesics, excellent benchmark |
| 4 | Maximum-entropy potential and entropy clocks | Cheap, conceptually clarifying, prevents misleading entropy language |
| 5 | General LC-geodesic ODEs | Useful infrastructure, but comparatively expensive |
| 6 | Gauss–Bonnet/holonomy | Beautiful, but presently poor depth-per-Lean-cost |

The following six modules implement priorities 1–4.

---

## H1. `ResponseObservableTransport`

### Main theorem: the residual is the second response of every observable

For a bounded observable \(F\), put
\[
\mathcal R_F(\mu)=E_{P_{m^{-1}(\mu)}}F,
\qquad B_\theta=A_\theta^{-1}.
\]
At \(\mu=m(\theta)\), for mean directions \(e,d\in W\), set
\(u=B_\theta e,\ v=B_\theta d\). Prove
\[
D\mathcal R_F(\mu)[e]
 =-\operatorname{Cov}_{P_\theta}(F,f_u),
\qquad
D^2\mathcal R_F(\mu)[e,d]
 =E_{P_\theta}\!\left[(F-EF)\,r_{uv}\right].
\]

This is the strongest new conceptual bridge available from G.

**Interpretation:** the part of score multiplication missed by the structural features is exactly what bends the response of other observables along mean-straight journeys.

### Proof route

Differentiate the tilted expectation twice:
\[
\frac{d^2}{dt^2}E_{P_{\theta(t)}}F
=
E[(F-EF)f_{\dot\theta}^{\,2}]
-\operatorname{Cov}(F,f_{\ddot\theta}).
\]
On an affine mean path, G6 gives
\(\ddot\theta=-C(\dot\theta,\dot\theta)\). Substitute and use the definition of \(r\); obtain mixed directions by the mixed chain rule or polarization.

### Valuable corollaries

1. **A quantitative observable-curvature bound**
   \[
   |D^2\mathcal R_F[e,d]|
   \le
   \sqrt{\operatorname{Var}(F)}
   \sqrt{E[r_{uv}^{\,2}]}.
   \]

2. **Saturation as universal response flatness:** at a point, saturation is equivalent to vanishing mean-coordinate Hessians for every bounded observable. The converse can test against the bounded residual itself.

3. **The response of fluctuations**
   \[
   \frac d{dt}\operatorname{Var}_{P_{\theta(t)}}(F)
   =
   -\operatorname{Cov}\!\left((F-EF)^2,f_{\dot\theta}\right).
   \]

4. Along an affine mean path,
   \[
   \frac{d^2}{dt^2}\operatorname{Var}(F)
   =
   E[(F-EF)^2r_{uu}]
   -2\left(\frac d{dt}EF\right)^2.
   \]
   In a saturated family, posterior variance is therefore concave along every mean segment.

**Caution:** variance need not increase or decrease monotonically. Its first derivative is a mixed third moment, with no general sign.

---

## H2. `ResponseMaximumEntropyPotential`

This should establish the precise version of “from the featureless maximal-entropy law.”

### Three statements

**1. Reference-relative entropy.** Define
\[
H_\nu(\rho)=-\operatorname{KL}(\rho\Vert\nu).
\]
Then \(\nu\) is its unique maximizer, with value zero.

This is not a Shannon-entropy claim unless the reference is uniform in the appropriate finite setting.

**2. The model is the maximum-entropy section of the response fibres.**

For an interior moment \(\mu\), the law \(P_{m^{-1}(\mu)}\) uniquely maximizes \(H_\nu\) among admissible laws with that moment. This is immediately the KL Pythagorean theorem.

Initially state this on the law class already supported by the API. Extension to all dominated laws requires the relevant integrability assumptions; it is not free.

**3. The model information is a strictly convex mean-coordinate potential.**

Let
\[
\mathcal I(\mu)=\operatorname{KL}(P_{m^{-1}(\mu)}\Vert\nu).
\]
Then
\[
D\mathcal I(\mu)[e]=-\langle\theta,e\rangle,
\qquad
D^2\mathcal I(\mu)[e,d]
=-\langle B_\theta e,d\rangle
=G_\theta(B_\theta e,B_\theta d).
\]

Along the featureless mean journey \(\mu_t=m(0)+t\Delta\),
\[
\mathcal I''(t)=G_{\theta_t}(\dot\theta_t,\dot\theta_t),
\qquad \mathcal I'(0)=0.
\]
Hence model relative entropy decreases monotonically, strictly for a nonconstant journey after time zero.

### An important path distinction

For the **data power-tilt path** \(\rho_t=\nu.\mathrm{tilted}(tg)\),
\[
\frac d{dt}\operatorname{KL}(\rho_t\Vert\nu)
=t\,\operatorname{Var}_{\rho_t}(g)\ge0.
\]
But its **projected model information need not be monotone**.

A small counterexample: take uniform \(\nu\) on three points, \(S=1_{\{1\}}\), and \(g=(\log2,0,\log3)\). The response moment is
\[
\frac{2^t}{2^t+1+3^t},
\]
which equals \(1/3\) at both endpoints and is larger in between. Projected information rises and then returns to zero.

Thus the canonical mean journey and the projected power-tilt journey must not be conflated.

---

## H3. `ResponseFiniteSimplex`

Assume \(X\) is finite and nonempty, every atom has positive reference mass, and `SpansAffine S ν`.

### Main statements

1. \(\dim W=|X|-1\).
2. The feature points \(S(x)\) are affinely independent.
3. The moment map on probability vectors is an affine equivalence between the simplex and the moment body.
4. Consequently,
   \[
   W \;\cong_{\mathrm{smooth}}\;
   \{p:X\to\mathbb R:\ p_x>0,\ \sum_xp_x=1\},
   \qquad \theta\mapsto P_\theta .
   \]

### Proof route

Use affine evaluation:
\[
(b,k)\longmapsto\bigl(x\mapsto\langle b,S(x)\rangle+k\bigr).
\]
Surjectivity from `SpansAffine` gives affine independence and the dimension calculation. Then compose the existing mean-chart equivalence with the barycentric identification.

This route is preferable to constructing a natural parameter using `dirProj`. An arbitrary complementary projection need not preserve the represented law.

**Caution:** with zero reference masses, replace \(X\) by the support. The theorem is about the positive simplex, not its closed boundary.

---

## H4. `ResponseSimplexSphere`

This completes G5 sharply and supplies explicit LC geodesics without a general ODE development.

### Metric identification

Prove that
\[
p\longmapsto 2(\sqrt{p_x})_{x\in X}
\]
identifies the simplex Fisher metric with the induced metric on the positive orthant of the sphere of radius \(2\):
\[
G_p(\dot p,\dot q)=\sum_x\frac{\dot p_x\dot q_x}{p_x}.
\]

### Explicit minimizing path

For distinct positive \(p,q\), let
\[
\alpha=\arccos\sum_x\sqrt{p_xq_x}.
\]
Define
\[
s_x(t)=
\frac{\sin((1-t)\alpha)}{\sin\alpha}\sqrt{p_x}
+
\frac{\sin(t\alpha)}{\sin\alpha}\sqrt{q_x},
\qquad
p_x(t)=s_x(t)^2.
\]

On \([0,1]\):

- all coordinates remain positive;
- \(\sum_xp_x(t)=1\);
- the Fisher speed is \(2\alpha\).

Transport this path through H3 to an explicit `FisherPath`. Combine its upper bound with G5’s lower bound:
\[
\boxed{d_F(p,q)=2\arccos\sum_x\sqrt{p_xq_x}.}
\]

Handle \(p=q\) separately.

### Lean cautions

- Positivity should be proved before using the inverse chart.
- To satisfy a smooth-open-domain path interface, use positivity on the compact parameter interval to obtain a slightly larger open interval.
- The positive simplex is **not complete** when it has positive dimension: its boundary is at finite Fisher distance.
- The spherical path is generally not the mean-linear journey.

This module gives a global, explicit, curved model of the entire response space.

---

## H5. `ResponseLocalizedSamplingBias`

The correct target is a localized estimator, not an undefined empirical inverse.

Choose a ball \(B(\mu,\delta)\) inside the mean-chart domain, and define
\[
\widehat\theta_n^{\,\mathrm{loc}}
=
\begin{cases}
m^{-1}(\mu+e_n),&\|e_n\|<\delta,\\
\theta,&\text{otherwise}.
\end{cases}
\]

### Deterministic quantitative theorem

Upgrade G6 on a smaller ball to
\[
m^{-1}(\mu+e)
=
\theta+B_\theta e
-\tfrac12C_\theta(B_\theta e,B_\theta e)
+R(e),
\qquad
\|R(e)\|\le K\|e\|^3.
\]

The chart is smooth and finite-dimensional, so bounded third derivatives on a compact interior ball give this. If that Taylor API is costly, a uniform \(o(\|e\|^2)\) remainder is enough for the asymptotic theorem.

### Honest minimal bias theorem

It suffices to assume
\[
Ee_n=0,\qquad E[e_n\otimes e_n]=\Sigma/n,\qquad
E\|e_n\|^4=O(n^{-2}).
\]
Then
\[
E\widehat\theta_n^{\,\mathrm{loc}}-\theta
=
-\frac1{2n}
\sum_{i,j}\Sigma_{ij}
C_\theta(B_\theta b_i,B_\theta b_j)
+o(n^{-1}),
\]
where \((b_i)\) is a fixed orthonormal basis of \(W\).

For i.i.d. bounded observations, these moment hypotheses hold. With the cubic remainder, the remainder is in fact \(O(n^{-3/2})\), using the fourth-moment bound also to control the localization tails.

### What this establishes

It gives the curvature-induced bias for:

- correctly specified sampling;
- misspecified data laws having the same interior moment;
- any centered perturbations satisfying the stated moment bounds.

Under misspecification, \(\Sigma\) is the **data covariance**, not automatically the model Fisher covariance.

It does **not** establish an expectation formula for an unregularized estimator that is undefined or divergent on boundary events.

---

## H6. `ResponseTwoScaleResolution`

This module should have a deterministic/probabilistic core, with a CLT corollary only if the probability infrastructure makes it inexpensive.

Let the truth moment be \(\mu+te\), and let \(\xi_n\) be the sampling error centered at that truth. Around the baseline,
\[
\widehat\theta-\theta
=
B_\theta(te+\xi_n)
-\tfrac12C_\theta\!\left(B_\theta(te+\xi_n),B_\theta(te+\xi_n)\right)
+R(te+\xi_n).
\]

### First deliverable: finite-sample sign certification

For a wall covector \(a\), put \(\lambda(z)=\langle a,B_\theta z\rangle\). On \(\|\xi_n\|\le r\), an elementary second-order bound gives
\[
\langle a,\widehat\theta-\theta\rangle
\ge
t\lambda(e)-\|\lambda\|r
-K_a(|t|\|e\|+r)^2.
\]
Thus positivity of the right side certifies the sign on that event. Combine with the existing sampling-risk and concentration bounds.

A sharper version keeps the explicit quadratic term and uses a cubic remainder. That is the genuine upgrade over a first-order chamber-size comparison.

### Second deliverable: two-scale stochastic expansion

For \(t_n=h/\sqrt n\), writing \(Z_n=\sqrt n\,\xi_n\),
\[
\widehat\theta_n-\theta
=
\frac1{\sqrt n}B_\theta(he+Z_n)
-\frac1{2n}C_\theta\!\left(B_\theta(he+Z_n),B_\theta(he+Z_n)\right)
+o_p(n^{-1}).
\]

If \(Z_n\Rightarrow N(0,\Sigma)\) and
\[
\sigma_a^2=\lambda\Sigma\lambda^\ast>0,
\]
then
\[
\Pr\{\langle a,\widehat\theta_n-\theta\rangle>0\}
\longrightarrow
\Phi_{\mathrm{Gauss}}\!\left(\frac{h\lambda(e)}{\sigma_a}\right).
\]

For varying truth laws, the needed triangular-array CLT hypotheses must be stated, not inferred merely from convergence of their means.

### Crucial restraint

The curvature bias is order \(n^{-1}\); a regular sign CLT sees the order \(n^{-1/2}\) term. Therefore:

> A second-order Taylor expansion plus a CLT does not justify a second-order approximation to sign probabilities by inserting the bias into a Gaussian CDF.

Such an approximation also encounters skewness, the random quadratic term, and possibly lattice corrections. It needs Edgeworth-type or comparable distributional control.

Conversely, if the first-order wall response vanishes almost surely, a quadratic Gaussian limit can become leading order. That is a beautiful later theorem about tangential or first-order-unresolvable walls.

---

## What to defer

### General LC-geodesic ODEs

The immediate low-cost theorem is the exact criterion for an existing mean journey. Since
\[
\nabla^{LC}_{\dot\theta}\dot\theta
=
-\tfrac12C(\dot\theta,\dot\theta),
\]
its given parametrization is LC-geodesic iff \(C(\dot\theta,\dot\theta)=0\). Its regular image is locally an unparametrized LC geodesic iff
\[
C(\dot\theta,\dot\theta)\in\operatorname{span}\{\dot\theta\}.
\]

This criterion is worth adding as a corollary. General local ODE existence and uniqueness can follow later; global existence is not automatic, as the incomplete simplex already demonstrates.

### Gauss–Bonnet and holonomy

Defer. A triangle of mean journeys generally has nonzero LC geodesic curvature along its edges. Its Gauss–Bonnet formula therefore needs boundary-curvature terms, not merely integrated sectional curvature and corner angles.

The integration, orientation, parallel-transport, and boundary APIs would likely dominate the mathematical gain at this stage.

---

# Q3. Headline for D–G

\[
\boxed{
\operatorname{KL}(\rho_g\Vert\nu)
=
\underbrace{\operatorname{KL}(\rho_g\Vert P_{\Phi(g)})}_{\text{information invisible to the response}}
+
\underbrace{\int_0^1(1-t)\,
G_{\theta_t}(\dot\theta_t,\dot\theta_t)\,dt}_{\text{information carried by the response journey}},
\quad
\theta_t=m^{-1}\!\bigl((1-t)m(0)+tE_{\rho_g}S\bigr).
}
\]

Within the bounded-tilt/interior regime, posterior response is a smooth Fisher-geometric quotient, with a canonical journey from the reference law and an exact accounting of visible versus invisible information. Its curvature, intrinsic distance, and second jet describe how structural changes accumulate and how local sampling perturbations are converted into response-coordinate changes.

**What remains unestablished:** a globally defined boundary-aware empirical response theory, including rigorous higher-order sign probabilities and sampling bias without localization or regularization.