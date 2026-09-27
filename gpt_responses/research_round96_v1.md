## Executive recommendation

The next programme should connect three objects that are now present but not yet fully unified:

1. **The global information landscape:** response plus information left in the fibre.
2. **The intrinsic geometry of response space:** distance, curvature, and the distinction between the canonical journey and a shortest journey.
3. **The observational geometry:** how sampling blurs that landscape.

My ranking by beauty/depth per likely Lean cost is:

| Rank | Target | Assessment |
|---|---|---|
| 1 | General-endpoint action and Pythagoras | Small extension, substantial conceptual payoff |
| 2 | Concrete finite saturation | Essential completion of F5; unlocks exact simplex geometry |
| 3 | Curvature as constant curvature plus a score-product defect | Stronger and more illuminating than a curvature bound alone |
| 4 | Global information decomposition, with differential formulas | Directly serves the standing direction; topology must be explicit |
| 5 | Fisher distance and canonical-journey comparison | Beautiful, but the intrinsic-distance infrastructure may dominate |
| 6 | Second-order response and Fisher-normalised sampling resolution | Scientifically central; must separate exact tangent results from nonlinear asymptotics |

These can form six coherent modules. I would not make a CLT or a global nonlinear estimator-risk theorem the immediate critical path.

---

# Q1. Audit

## Overall verdict

Nothing in F is inherently dishonest as summarised. There are, however, several qualifications that should be visible in the mathematical narrative:

- F5 is currently a **conditional geometry theorem**, not yet a concrete simplex theorem.
- F4 is a **pointwise-in-\(t\), finite-sample sign guarantee**, not a simultaneous trajectory-recovery theorem.
- The local truth-shift version of F4 needs a **positive-time interpretation**.
- The featureless law is maximal entropy only with an appropriate reference-relative interpretation.
- F6 concerns stationarity, not global minimality.
- Empirical response parameters need not exist, even when the population response does.

The last point becomes crucial in the next programme.

## (a) Is `SaturatedAt` the right hypothesis?

Yes—for the algebraic conclusion you prove. More precisely, it says that the finite-dimensional space
\[
\mathbb R\,1+\{f_u:u\in W\}
\]
is closed under multiplication modulo almost-everywhere equality.

Because \(E_\theta f_u=0\), the constant term in the product decomposition is necessarily \(G_\theta(u,v)\). Thus your formulation is exactly the natural centred formulation of this closure property.

It is:

- sufficient for the constant-curvature computation;
- exactly the vanishing of the score-product residual described below;
- **not necessary merely for a particular sectional curvature to equal \(1/4\)**;
- not synonymous with “all probability laws on \(X\)” unless the scores actually span all centred functions.

For example, a model that changes only the weights of a finite partition, keeping the conditional law within each cell fixed, can satisfy this hypothesis even when \(X\) is infinite.

### The finite affine-basis instance

It holds if the intended affine-basis hypothesis means
\[
\operatorname{span}\{1,S_j:j\in J\}=\mathbb R^X,
\]
with \(X\) finite and \(\nu\{x\}>0\) for every \(x\).

Equivalently, the feature vectors \(S(x)\) are affinely independent as \(x\) ranges over \(X\), allowing redundant feature coordinates. Under this hypothesis,
\[
\dim W=|X|-1,
\]
and every \(P_\theta\)-centred function on \(X\) is \(f_c\) for a unique \(c\in W\).

Merely saying that some feature functions are affinely independent is not enough: **spanning modulo constants** is the operative condition.

### Clean Lean route

I would prove one reusable representation lemma before touching products:

> Every function on \(X\), after \(P_\theta\)-centring, is a centred score of a vector in \(W\).

The proof should use your existing projection API rather than construct a new basis of \(W\).

1. **Affine representation.**  
   From the spanning hypothesis, write
   \[
   h(x)=k+\langle b,S(x)\rangle
   \]
   for some ambient coefficient vector \(b\).

2. **Project the coefficient.**  
   Put \(c=\operatorname{dirProjL}(b)\). Your existing theorem says that replacing \(b\) by \(c\) changes `dirLoss` by a \(\nu\)-a.e. constant.

3. **Transfer the a.e. statement to \(P_\theta\).**  
   Use absolute continuity of the tilted law. There is no need to convert every intermediate equality to pointwise equality.

4. **Centre.**  
   Subtract the \(P_\theta\)-expectation. Both constants disappear, giving
   \[
   h-E_\theta h=f_c.
   \]

5. **Apply this to \(h=f_uf_v\).**  
   Its expectation is \(G_\theta(u,v)\), giving `SaturatedAt θ`.

If useful elsewhere, separately package the linear equivalence
\[
W\simeq\{h:X\to\mathbb R:E_\theta h=0\}.
\]
But it is not necessary for the shortest saturation proof.

Positive mass of each point also makes a.e. equality equivalent to pointwise equality, should the finite-dimensional linear algebra be easier on actual functions.

**Nonvacuity:** \(K=1/4\) requires a nondegenerate two-plane. For \(|X|\le2\), the sectional-curvature conclusion has no such instance. Include a three-point example or a dimension theorem to make this explicit.

## (b) Does the common sample space in F4 lose anything?

For the stated probability bound, essentially no statistical content is lost.

The proof uses, for each fixed \(t\):

- the correct marginal law;
- independence across sample index \(i\);
- finite variance;
- \(n>0\).

It uses no independence, continuity, or other relation between \(X_{t,i}\) and \(X_{s,j}\) when \(t\ne s\). Indeed, pairwise independence of the scalar observables suffices for the variance calculation.

But distinguish three claims:

1. **Pointwise guarantee:** valid for each small positive \(t\).
2. **Simultaneous guarantee:** valid for all \(t\) on one event.
3. **Sample-path regularity:** an empirical response trajectory continuous or differentiable in \(t\).

F4 proves the first, not the second or third. A common probability space alone provides neither of the latter.

For finite or suitably parameterised standard Borel spaces, common-space realisations are routine. In completely general measurable spaces, such a realisation should not silently be treated as automatic. A clean theorem interface can allow a separate probability space for each \(t\), with the common-space theorem as a convenience wrapper.

### Important sign qualification

The displayed event
\[
(\widehat M_t-c(0))d\le0
\]
describes the wrong sign when \(t>0\). For \(t<0\), the expected shift has the opposite sign.

Thus “eventually” should mean \(t\downarrow0\), not an unrestricted punctured neighbourhood. For a two-sided theorem, use the sign of \(td\), or directly compare with \(c(t)-c(0)\).

### Other audit points

- F3’s identities are genuinely exact, not merely local quadratic approximations.
- F6’s normalisation matches the conventional energy \(\frac12\int G(V,V)\). If you call \(\int G(V,V)\) the energy, the variation acquires a factor of two.
- F6 does not establish existence, uniqueness, or minimisation of LC geodesics.
- Smoothness on an open domain containing \([0,1]\) is exactly the right way to avoid endpoint derivative awkwardness in F2.

---

# Q2. The next six modules

## G1. `ResponseEndpointInformationAction`

**Priority: first.**

Let \(\mu_i=m(\theta_i)\), \(\Delta=\mu_1-\mu_0\), and
\[
\theta_t=m^{-1}(\mu_0+t\Delta),\qquad
e(t)=G_{\theta_t}(\dot\theta_t,\dot\theta_t).
\]

Prove:
\[
\begin{aligned}
\mathrm{KL}(P_{\theta_1}\Vert P_{\theta_0})
 &=\int_0^1(1-t)e(t)\,dt,\\
\mathrm{KL}(P_{\theta_0}\Vert P_{\theta_1})
 &=\int_0^1t\,e(t)\,dt,\\
J(P_{\theta_0},P_{\theta_1})
 &=\int_0^1e(t)\,dt
 =-\langle\theta_1-\theta_0,\mu_1-\mu_0\rangle.
\end{aligned}
\]

Then combine with the existing response Pythagoras:

> If \(\theta_1=\Phi(\rho)\), then
> \[
> \mathrm{KL}(\rho\Vert P_{\theta_0})
> =
> \mathrm{KL}(\rho\Vert P_{\theta_1})
> +\int_0^1(1-t)e(t)\,dt.
> \]

### Proof route

Reuse F2–F3 with the base point translated:

- mean-affine path regularity;
- \(\dot\theta=A^{-1}\Delta\);
- \(e=-\langle\dot\theta,\Delta\rangle\);
- derivative of the appropriate KL along the path;
- the same weighted integral argument.

No new geometric idea is required. This removes the accidental privilege of \(\theta=0\) from the mathematics while retaining its interpretive privilege.

**Caution:** prove that the segment remains in the mean-map domain using the existing mixture-law construction or convexity theorem. Do not implicitly assume the mean image is all of the ambient feature space.

---

## G2. `ResponseFiniteSaturation`

**Priority: second.**

Land:

1. the centred-function representation lemma;
2. `SaturatedAt θ` for every \(\theta\);
3. \(\dim W=|X|-1\);
4. constant curvature on nondegenerate planes;
5. ideally, identification of the model with the strictly positive finite simplex.

The last identification is straightforward mathematically: for a positive law \(p\), represent \(-\log(p/\nu)\) by features modulo constants, then project to \(W\).

### Why it matters

This turns F5 from an abstract conditional theorem into the exact model case against which the rest of the response geometry can be compared.

It also makes explicit that saturation is about **expressivity of the observables**, not a special choice of positive reference weights.

---

## G3. `ResponseCurvatureDefect`

**Priority: third; highest geometric payoff beyond the easy completions.**

Do not stop at a Cauchy–Schwarz curvature bound. Prove a Gauss-type identity measuring departure from saturation.

At a fixed \(\theta\), define
\[
r_{uv}=f_uf_v-G(u,v)+f_{C(u,v)}.
\]

The sign is important: your convention gives the score projection of \(f_uf_v-G(u,v)\) as \(-f_{C(u,v)}\).

Prove that \(r_{uv}\) is centred and orthogonal to every score. Then
\[
G(C(u,v),C(x,y))
=
E[f_uf_vf_xf_y]-G(u,v)G(x,y)-E[r_{uv}r_{xy}].
\]

For \(D=G(u,u)G(v,v)-G(u,v)^2>0\), this gives
\[
K_\theta(u,v)
=
\frac14+
\frac{E[r_{uu}r_{vv}]-E[r_{uv}^{\,2}]}{4D}.
\]

This says exactly:

> The response model inherits the sphere’s \(1/4\) curvature, corrected by the component of score products that the response coordinates cannot represent.

For the \(\alpha\)-connection, the corresponding sectional expression is multiplied by \(1-\alpha^2\).

### Proof route

Everything is finite-dimensional algebra plus expectations:

- the existing third-cumulant identity;
- symmetry of \(G(C(u,v),w)\);
- orthogonality of the residual;
- expansion of residual inner products;
- the existing commutator curvature formula.

An abstract Hilbert-space orthogonal-projection development is unnecessary.

### Bounds as corollaries

First prove the exact cubic formula
\[
K=\frac{\|C(u,v)\|_G^2-G(C(u,u),C(v,v))}{4D}.
\]

Then obtain
\[
|K|
\le
\frac{\|C(u,v)\|_G^2+
\|C(u,u)\|_G\|C(v,v)\|_G}{4D}.
\]

If \(\|C(u,v)\|_G\le\beta\|u\|_G\|v\|_G\), use a Fisher-orthonormal basis of the plane to get \(|K|\le\beta^2/2\).

**Cautions:**

- Neither nonnegative curvature nor \(K\le1/4\) holds automatically.
- Bounds based only on raw feature boundedness will generally deteriorate as Fisher eigenvalues degenerate.
- This is the geometry of the embedded model. It does not automatically make \(\Phi\) a global Riemannian-submersion quotient of the entire data manifold.

---

## G4. `ResponseGlobalInformationLandscape`

**Priority: fourth.**

Package the existing results as functions on the actual `DataLaw` space:

- response \(R(\rho)=\Phi(\rho)\);
- defect \(D(\rho)=\mathrm{KL}(\rho\Vert P_{R(\rho)})\);
- response information \(I(\rho)=\mathrm{KL}(P_{R(\rho)}\Vert\nu)\).

Then prove globally
\[
\mathrm{KL}(\rho\Vert\nu)=D(\rho)+I(\rho),
\]
with:

- \(D\ge0\);
- \(D=0\) exactly on the model;
- \(I\) constant on each response fibre;
- \(I\) equal to the weighted action of the canonical journey.

This upgrades “a theorem for each \(g\)” into an organised information landscape.

### Add differential formulas, not merely continuity

On a bounded-potential chart \(g\mapsto\rho_g\), in direction \(h\), write
\[
\delta\mu=\operatorname{Cov}_{\rho_g}(S,h),\qquad \theta=\Phi(g).
\]

Then
\[
DI_g[h]=-\langle\theta,\delta\mu\rangle,
\qquad
DD_g[h]=\operatorname{Cov}_{\rho_g}(g+\langle\theta,S\rangle,h).
\]

These formulas distinguish information that moves the response from information that remains unresolved within its fibre.

### Proof route

- Lift the existing Pythagoras and action theorems.
- Differentiate the explicit KL expression, or use the stationary-point/envelope cancellation from F1.
- Prove chartwise smoothness through exponential, integration, normalisation, and the smooth inverse mean map.

**Cautions:**

- “Smooth on `DataLaw`” requires a specified smooth structure.
- \(L^\infty\)-potential charts are a defensible setting.
- KL is not generally continuous in weak convergence or total variation without additional integrability control.
- Do not confuse the earlier homotopy-equivalence/fibre result with a bijection of all data laws and response coordinates.

---

## G5. `ResponseIntrinsicDistance`

**Priority: fifth, unless the seabed already has the needed length-space infrastructure.**

Define Fisher distance on \(W\) as the infimum of lengths of admissible piecewise smooth paths. Prove the chain
\[
2\arccos\operatorname{Aff}(P_{\theta_0},P_{\theta_1})
\le d_F(\theta_0,\theta_1)
\le L_F(\theta_\bullet)
\le \sqrt{J(P_{\theta_0},P_{\theta_1})},
\]
where \(\theta_\bullet\) is the mean-affine journey.

On data laws, define
\[
d_{\mathrm{resp}}(\rho,\sigma)=d_F(\Phi(\rho),\Phi(\sigma)).
\]

This is a pseudometric on data laws and a metric on response classes, once separation of \(d_F\) is established.

### Proof route

- Existing spherical lower bound, applied to every admissible path.
- The canonical journey as a competitor.
- Cauchy–Schwarz plus G1 for the upper bound.
- Local positive definiteness and continuity of Fisher for separation.

The spherical lower bound may also provide an economical separation proof, using identifiability.

### Saturated finite sharpening

After G2, prove the exact formula
\[
d_F(p,q)=2\arccos\sum_x\sqrt{p(x)q(x)}.
\]

The square-root great-circle interpolation stays strictly positive, so it remains inside the positive simplex. This supplies an explicit shortest journey, not just an existence theorem.

### What comparison is actually true?

The canonical m-geodesic has LC acceleration
\[
\ddot\theta+\tfrac12C(\dot\theta,\dot\theta)
=-\tfrac12C(\dot\theta,\dot\theta).
\]

Thus it is an affinely parametrised LC geodesic exactly when \(C(\dot\theta,\dot\theta)=0\). Its image can still be an LC geodesic after reparametrisation when this vector is proportional to \(\dot\theta\).

**Cautions:**

- \(\sqrt{\text{Jeffreys}}\) is not automatically a metric.
- Stationarity does not establish shortestness.
- Do not invoke Hopf–Rinow: the positive simplex is Fisher-incomplete.

---

## G6. `ResponseSamplingGeometry`

**Priority: sixth by Lean cost, but central to the scientific story.**

The right target is **exact tangent-space resolution plus a deterministic second-order transfer theorem**.

Let \(\rho\) be the true law, \(\theta=\Phi(\rho)\), \(H=-A_\theta\), and let \(B\) be the feature covariance under \(\rho\). For the empirical feature error \(e_n=\widehat\mu_n-\mu\), define the linearised response error
\[
\xi_n=A_\theta^{-1}e_n.
\]

Then prove the exact identity
\[
E\,G_\theta(\xi_n,\xi_n)
=
\frac1n\operatorname{tr}(H^{-1}B)
=:\frac{d_{\mathrm{eff}}(\rho)}n.
\]

Consequently,
\[
\Pr(\|\xi_n\|_{G_\theta}\ge r)
\le\frac{d_{\mathrm{eff}}(\rho)}{nr^2}.
\]

This is the coordinate-free, multidirectional analogue of F4.

### The essential correction

In general,
\[
d_{\mathrm{eff}}(\rho)\ne\dim W.
\]

It equals \(\dim W\) under correct specification, \(\rho=P_\theta\). Off-model, matching means does not match covariances. The correct object is the sandwich covariance, not Fisher covariance alone.

### Chamber resolution

Use the mean-space metric \(H^{-1}\). If the true mean lies at distance at least \(r\) from a chamber’s complement, then an empirical mean can leave the chamber only if its error has norm at least \(r\). The preceding Markov bound is then an exact finite-sample chamber guarantee.

For a single wall, retain F4’s sharper directional variance bound. The trace bound is a simultaneous geometric envelope, not a universal improvement.

### Second-order truth and sampling response

For a smooth truth path with mean \(\mu(t)\), put \(v=A^{-1}\dot\mu\). Prove
\[
\ddot\theta=A^{-1}\ddot\mu-C(v,v).
\]

For a small admissible mean perturbation \(e\), prove the deterministic expansion
\[
\theta(\mu+e)
=
\theta+A^{-1}e
-\tfrac12C(A^{-1}e,A^{-1}e)
+o(\|e\|^2).
\]

These are the same second jet applied to two different sources of displacement: truth and sampling. That is the clean mathematical realisation of the user’s resolution story.

### Critical cautions

- An empirical mean can lie on the boundary of the mean domain. The finite natural parameter then does not exist.
- In a finite saturated model, zero empirical cell counts are the elementary example.
- Therefore an exact theorem about \(\Phi(\widehat\rho_n)\) needs localisation, conditioning, or regularisation.
- Taking expectations of a local Taylor expansion requires remainder and tail control. An \(o(\|e\|^2)\) theorem alone does not prove an \(o(1/n)\) bias formula.

I would land the exact tangent risk and deterministic jet first. They provide useful, honest resolution mathematics without importing an entire asymptotic-statistics programme.

---

# Q3. Headline theorem for the note now

Use the result already proved, not the proposed generalisation:

> **Response information is the weighted Fisher action of the canonical journey; all remaining information lies in the response fibre.**

For \(\rho=\nu.\mathrm{tilted}(g)\) and
\(\theta_t=m^{-1}((1-t)m(0)+tE_\rho S)\),
\[
\boxed{\displaystyle
\mathrm{KL}(\rho\Vert\nu)
=
\underbrace{\mathrm{KL}\!\left(\rho\Vert P_{\Phi(g)}\right)}_{\text{information unresolved by the chosen features}}
+
\underbrace{\int_0^1(1-t)\,
G_{\theta_t}(\dot\theta_t,\dot\theta_t)\,dt}_{\text{information carried by the response journey}}.
}
\]

The journey is global and mean-affine; its endpoint is the unique information projection. “Unresolved” is relative to the selected feature family—it does not mean intrinsically meaningless.

## The maximal-entropy caveat

Yes, it needs a caveat.

- For finite \(X\) and uniform \(\nu\), the reference law is genuinely the Shannon maximum-entropy law.
- For general \(\nu\), it is the maximiser of **reference-relative entropy** \(-\mathrm{KL}(\rho\Vert\nu)\), not necessarily of Shannon or differential entropy.
- On an unbounded continuous space, an unconstrained maximum-entropy probability law may not exist.

I would therefore write **“the featureless reference law”**, adding “the maximal-entropy law when the reference is chosen accordingly.”

The next programme’s strongest new insight would be the pairing of G3 and G6: **unrepresented score products explain geometric bending; sampling covariance explains observational blurring.** Together they say not only where responses live, but how their geometry and resolvability depend on what the features fail to capture.