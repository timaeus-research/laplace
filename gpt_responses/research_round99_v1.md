## Verdict

**Land the testing lower bound next; then identify the saturated family with the positive simplex; then prove the sphere theorem.** Together these turn the local response calculus into a concrete geometric and statistical picture. Localised bias remains worthwhile, but it is no longer the highest-value next step.

The principal audit correction is this: **a sign statement about a globally defined chart inverse is not, by itself, an existence statement about a valid response.** The proof appears to contain the stronger statement already; export it.

# Q1. Audit of programme I

## (a) Probabilistic resolution: distinguish the good event from the stated event

Write
\[
\widehat M_n=m(\theta_0)+te+\xi_n,\qquad
E_r=\{q(\xi_n)<r^2\}.
\]
Your noise bridge gives, on \(E_r\),
\[
\|\widehat M_n-m(\theta_0)\|
\le |t|\|e\|+\frac{\|A\|}{\sqrt c}\,r
\le\delta.
\]

This does capture chart validity **provided the remainder lemma really supplies membership for that closed \(\delta\)-ball**, in the appropriate affine mean space. Check the boundary convention: if the available inclusion is only `Metric.ball ... δ ⊆ Ω`, a weak inequality at the last step is insufficient without some strictness or a smaller radius.

The honest exported event should be something like
\[
\left\{
\widehat M_n\in\Omega,\quad
m(\theta_r(\widehat M_n))=\widehat M_n,\quad
\ell(\theta_0)<\ell(\theta_r(\widehat M_n))
\right\}.
\]
Its probability is at least \(1-\tau/(nr^2)\).

Equivalently, state existence of a **valid** response:
\[
\Pr\!\left(
\exists\theta\in U,\ 
m(\theta)=\widehat M_n
\ \land\ 
\ell(\theta_0)<\ell(\theta)
\right)
\ge 1-\frac{\tau}{nr^2}.
\]
Include uniqueness within the chart—or globally on \(W\), if an existing injectivity theorem supplies it.

### What the present theorem actually says

If its conclusion contains only the sign inequality for the total function \(\theta_r\), then:

- it is a correct consequence of the stronger good-event inclusion;
- it does **not formally identify its event with “valid response exists and crosses the wall”**;
- accidental signs produced outside \(\Omega\) can enlarge its event.

Thus this is principally an **interface/interpretation defect**, not necessarily a proof defect. Prove
`noise_good_subset_valid_sign_event`, and make the strengthened probability statement primary. Keep the sign-only statement as a corollary.

Also make explicit:

1. \(r>0\), \(n>0\), and the sampling probability space;
2. the noise moment bound is under the **actual data law**, not silently under \(P_{\theta_0}\);
3. the empirical mean belongs almost surely to the affine space on which the chart is constructed;
4. the certificate includes chart containment as well as the Taylor sign margin.

There is no unconditional existence claim here. In the saturated finite case, an empirical distribution can have zero cells and hence fail to correspond to any finite parameter. The high-probability chart event is exactly what protects against this.

## (b) Variance concavity: yes, but name the hypothesis precisely

Your identity is
\[
V''(t)=
\mathbb E_{\theta_t}\!\left[(F-\mathbb E_{\theta_t}F)^2
r_{V_tV_t}\right]
-2\left(\frac{d}{dt}\mathbb E_{\theta_t}F\right)^2.
\]

Therefore the stated zero-pairing assumption is entirely sufficient:
\[
\forall t\in[a,b],\quad
\mathbb E_{\theta_t}\!\left[(F-\mathbb E_{\theta_t}F)^2
r_{V_tV_t}\right]=0
\quad\Longrightarrow\quad V''(t)\le0.
\]

But call it **observable-specific residual orthogonality**, or **vanishing variance-curvature pairing**. It is weaker than \(r_{V_tV_t}=0\) almost everywhere and is not a geometric flatness assertion about the whole model.

Useful hierarchy:

- \(r_{V_tV_t}=0\) a.e.: sufficient simultaneously for every admissible \(F\);
- the displayed pairing vanishes: sufficient for this \(F\);
- the pairing is nonpositive: also sufficient;
- most generally, the pairing is at most \(2(\frac d{dt}\mathbb EF)^2\).

Keep the zero-pairing theorem as a clean corollary of the inequality version.

Finally, retain the distinction already present in your summary: **symmetric bilinearity of `secondResponse` does not establish a Fréchet \(C^2\) Hessian theorem.** The one-dimensional variance differentiation and the endpoint regularity needed for `ConcaveOn` must stand on their own analytic results.

## (c) Saturated dimension: nonvacuous, with two degenerate cases

For finite \(X\), measurable singletons make every subset measurable, and every real-valued function is bounded. Strict positivity of every atom makes a.e. equality into pointwise equality. Consequently your score representation really identifies
\[
W\cong \ker\!\left(h\mapsto\sum_xP_\theta(x)h(x)\right),
\]
whose dimension is \(|X|-1\).

Nothing is inherently vacuous. Indeed, the categorical family is the canonical example.

The important qualifications are:

- **Empty \(X\):** incompatible with a probability law. It should be excluded automatically by the probability assumptions, rather than tolerated through truncated natural subtraction.
- **One-point \(X\):** \(W=0\). The theorem is valid, but there are no nontrivial response chambers or positive-dimensional geometry.
- **`SpansAffine` is the substantive hypothesis.** Merely defining \(W\) as the directional span of the features does not make saturation automatic.
- With full support on finite \(X\), the conclusion forces the feature points to be affinely independent in their affine span. In particular, distinct atoms cannot have identical feature vectors.
- If positivity is available at the reference law, exponential tilting preserves it. Avoid requiring a redundant separate positivity assumption at every \(\theta\).

The theorem is a strong saturation characterization, not merely a dimension count.

# Q2. Ranked next modules

Here is my ordering by **mathematical return relative to likely Lean cost**:

| Rank | Module | Return | Cost |
|---|---|---|---|
| 1 | `ResponseTestingResolution` | Statistical impossibility counterpart | Low–medium |
| 2 | `ResponseSimplexIdentification` | Exact global response atlas and mixture journey | Medium |
| 3 | `ResponseSimplexSphere` | Exact distance, geodesics, boundary geometry | Medium–high |
| 4 | `ResponseLocalizedSamplingBias` | Calibrates nonlinear estimator distortion | Medium |
| 5 | `ResponseGeometrySummary` | Makes D–I legible and reusable | Low if theorem-first |
| 6 | `ResponseMeanPolytopeJourney` | Extends the global journey beyond saturation | High |

The sixth is the major depth investment after the near-term closure.

## 1. `ResponseTestingResolution`

### Is the lower bound nearly free?

**Yes—with an important distance-range qualification.**

Let
\[
A(P,Q)=\int\sqrt{dP\,dQ},
\qquad d=d_F(\theta_0,\theta_1).
\]
The spherical lower bound on Fisher length gives
\[
2\arccos A(P_{\theta_0},P_{\theta_1})\le d.
\]
Hence, for \(0\le d\le\pi\),
\[
A(P_{\theta_0},P_{\theta_1})\ge\cos(d/2).
\]

Your existing product-affinity theorem then yields
\[
\boxed{
\inf_\varphi
\frac{P_{\theta_0}^{\,n}(\varphi=1)+
      P_{\theta_1}^{\,n}(\varphi=0)}2
\ \ge\
\frac{1-\sqrt{1-\cos^{2n}(d/2)}}2
}
\]
under that distance restriction.

This is **equal-prior average error**. It also bounds worst-case error from below, but it does not say that each of the two error probabilities separately exceeds the bound.

### The distance trap

For an arbitrary nonsaturated model, intrinsic Fisher distance can exceed \(\pi\). One cannot then insert a negative cosine and raise it to an even power: that produces spurious nonzero bounds.

A safe all-distance statement uses
\[
c(d)=\cos\!\left(\frac{\min(d,\pi)}2\right),
\]
giving the same expression with \(c(d)^{2n}\). For \(d\ge\pi\), this reduces to the trivial lower bound zero.

Alternatively, formulate the useful theorem only for \(d\le\pi\).

### Lean proof route

1. For every connecting Fisher path \(\gamma\), prove
   \(2\arccos A\le L_F(\gamma)\).
2. Pass to the intrinsic infimum using the distance API.
3. Apply cosine monotonicity on the correct interval.
4. Prove monotonicity of the existing testing bound in nonnegative affinity.
5. Specialise to chamber-label tests.

**An even cheaper first theorem:** if you exhibit a path of length \(L\le\pi\), use \(A\ge\cos(L/2)\). This avoids any friction around infima, empty path classes, or infinite distances.

A convenient elementary corollary is
\[
\operatorname{BayesErr}_n
\ge
\max\!\left\{0,\frac12-\frac{\sqrt n\,d}{4}\right\},
\]
using
\[
\cos^{2n}(d/2)\ge1-n\sin^2(d/2)\ge1-\frac{nd^2}{4}.
\]
The exact affinity bound remains the main theorem; the corollary exposes the scale.

### The honest two-sided resolution statement

**Achievability:** for a specified data law, a specified local certificate, and the requisite noise moment bound, the valid response has the certified sign with probability at least \(1-\tau/(nr^2)\).

**Obstruction:** for two specified model laws in opposite chambers, any chamber classifier has average error at least the affinity/distance expression above.

These are complementary, but **not yet a matched minimax theorem**:

- \(r\) is a certified noise radius; \(d\) is a separation between two laws.
- The upper bound contains \(\tau\), potentially dimension-dependent.
- The lower bound is binary and dimension-free.
- Local comparison estimates are needed to relate chamber margin, certified radius, and intrinsic separation.
- No uniform resolution is possible arbitrarily close to a chamber wall.

The clean headline is: **fixed-confidence discrimination of nearby alternatives requires \(nd^2\) bounded away from zero; a sufficiently buffered local certificate provides a corresponding sufficient condition, with its explicit variance and chart constants.**

## 2. `ResponseSimplexIdentification`

This is the highest-value geometric bridge.

For finite full-support saturated \(X\), define
\[
B(\theta)_x=P_\theta(\{x\}),\qquad
\Delta_X^\circ=\{p:\ p_x>0,\ \sum_xp_x=1\}.
\]

Prove:

1. \(B:W\to\Delta_X^\circ\) is a homeomorphism.
2. It and its inverse are smooth in appropriate finite-dimensional coordinates.
3. The mean map is
   \[
   m(\theta)=\sum_x B(\theta)_xS(x).
   \]
4. The barycentric map identifies \(\Delta_X^\circ\) with the relative interior of the feature simplex.

### Proof route

Use `ResponseSaturatedIdentification` for the abstract bijection/homeomorphism, then identify finite data laws with their atom masses.

For explicit smoothness, use the linear isomorphism
\[
L:W\longrightarrow \mathbb R^X/\mathbb R\mathbf1,
\qquad
L(\theta)=[x\mapsto-\langle\theta,S(x)\rangle].
\]
The inverse parameter is determined by
\[
L(\theta)=[\log(p/\nu)].
\]
This is often cleaner than differentiating an abstract inverse.

**Do not call \(W\cong\Delta^\circ\) a linear identification.** It is a nonlinear homeomorphism/diffeomorphism; the linear identification is with log-probabilities modulo constants, or with a simplex tangent space.

### The featureless journey

For positive target \(p\),
\[
p_t=(1-t)\nu+tp,\qquad
\theta_t=B^{-1}(p_t),\qquad 0\le t\le1.
\]
Then, pointwise,
\[
P_{\theta_t}=p_t,\qquad
m(\theta_t)=(1-t)m(0)+tm(\theta_1).
\]

This immediately gives, for every observable,
\[
\mathbb E_{\theta_t}F=(1-t)\mathbb E_\nu F+t\mathbb E_pF.
\]
And it upgrades the variance story to an exact identity:
\[
\operatorname{Var}_{p_t}F
=(1-t)\operatorname{Var}_\nu F+t\operatorname{Var}_pF
+t(1-t)(\mathbb E_pF-\mathbb E_\nu F)^2.
\]

Two cautions:

- An arbitrary reference \(\nu\) is not the Shannon maximum-entropy law. On a finite set, that is uniform; alternatively, explicitly mean maximum **relative** entropy with respect to \(\nu\).
- If the actual target has zero atoms, the journey belongs to the positive simplex only for \(t<1\). The endpoint is a boundary law, not a finite parameter.

This module makes “from featureless to actual data” mathematically literal.

## 3. `ResponseSimplexSphere`

For \(p,q\in\Delta_X^\circ\), prove
\[
\boxed{
d_F(B^{-1}p,B^{-1}q)
=2\arccos\sum_x\sqrt{p_xq_x}.
}
\]

The map
\[
p\longmapsto 2\sqrt p
\]
lands in the positive orthant of the radius-two sphere, and
\[
\|\dot p\|_F^2=\sum_x\frac{\dot p_x^2}{p_x}.
\]

### Proof route

Let \(\alpha=\arccos\sum_x\sqrt{p_xq_x}\). For \(p\ne q\), define
\[
u_s=
\frac{\sin((1-s)\alpha)}{\sin\alpha}\sqrt p+
\frac{\sin(s\alpha)}{\sin\alpha}\sqrt q,
\qquad p_s=u_s^2.
\]
Show:

- \(p_s\) remains strictly positive and sums to one;
- its Fisher speed is \(2\alpha\);
- \(\theta_s=B^{-1}(p_s)\) is an admissible smooth Fisher path;
- \(P_{\theta_s}=p_s\) pointwise;
- its length attains the existing spherical lower bound.

Handle \(p=q\) separately.

The smooth inverse from module 2 matters: a mere homeomorphism does not automatically produce an admissible differentiable lifted path.

### Beautiful consequences, with modest extra scope

- Constant sectional curvature \(1/4\), in dimensions where sectional curvature is applicable.
- Geodesic convexity of the positive orthant.
- Failure of metric completeness.
- Metric completion by the closed simplex with the same distance formula.

And importantly: **the mixture journey is mean-straight, not generally an affinely parametrised Levi–Civita geodesic.** The sphere arc and the mixture line answer different questions; your geodesic criterion explains the distinction.

## 4. `ResponseLocalizedSamplingBias`

Make this explicitly a **local or localised estimator theorem**, not a theorem about the arbitrary outside-chart extension.

For a response functional \(h\) and centred sample-mean noise \(\xi_n\), aim for
\[
\mathbb E[h(m+\xi_n)]-h(m)
=
\frac{1}{2n}\operatorname{tr}(H_h\Sigma)
+\text{controlled remainder},
\]
with the left-hand side interpreted through a valid global extension or a specified localisation.

A cubic Taylor remainder and fourth-moment estimate give the usual \(O(n^{-3/2})\) local remainder. But localisation introduces additional terms:

- truncation can destroy the exact cancellation of the linear term;
- the truncated quadratic moment differs from \(\Sigma/n\);
- outside-chart behaviour must be bounded or excluded by definition.

Use I3 to express the leading term through the residual tensor, but first supply the actual analytic Taylor hypothesis. Algebraic bilinearity alone is insufficient.

This answers a distinct scientific question: **how much apparent truth shift is curvature-induced sampling bias?**

## 5. `ResponseGeometrySummary`

Do this now as a **theorem-first summary module**, not yet as a large new abstraction.

Bundle or index:

- quotient/tangent identifications;
- Fisher nondegeneracy;
- information potential and dual coordinates;
- connections and curvature;
- response differential and bilinear second-response form;
- path-length comparison;
- local chart validity;
- probabilistic certificates and testing obstruction.

Keep optional analytic and global properties separate. A structure that requires completeness, global mean surjectivity, or analytic Hessians would overstate what is uniformly available.

My recommendation: first write one substantial theorem exposing the existing objects and compatibilities. Promote it to a reusable `ResponseGeometry` structure only when a second genuinely different implementation demonstrates which fields are intrinsic.

**Packaging is valuable; it should not substitute for the remaining geometry.**

## 6. `ResponseMeanPolytopeJourney`

This is the next major depth project beyond saturation.

For a finite full-support, possibly nonsaturated exponential family, prove
\[
m:W\overset{\sim}{\longrightarrow}
\operatorname{relint}\operatorname{conv}\{S(x):x\in X\}
\]
as a diffeomorphism, with the appropriate sign convention for the log-partition gradient.

Then every affine mean journey
\[
m_t=(1-t)m_\nu+tm_p
\]
has a unique lifted response as long as it remains in that relative interior.

### Proof route

For an interior target mean, minimise the strictly convex dual objective
\[
\theta\longmapsto
\log\sum_x\nu_xe^{-\langle\theta,S(x)\rangle}
+\langle\theta,m_{\mathrm{target}}\rangle.
\]
Interiorness gives coercivity on \(W\); strict convexity gives uniqueness; the first-order condition gives the prescribed mean. Existing local inverses then supply smoothness.

This is substantially more Lean work than the saturated simplex theorem, but it addresses the programme’s broadest ambition.

The essential interpretive distinction is:
\[
P_{\theta_t}\ne(1-t)\nu+tp
\quad\text{in general, while their feature means agree.}
\]
Outside saturation, the response atlas maps a **quotient of data space by feature means**. Making that quotient explicit is more informative than pretending every data distribution is itself a model law.

# Q3. Headline and remaining desideratum

With \(s_z\) denoting the score of a lifted mean-direction and the middle expression understood as the proved second-response form, rather than an unproved global \(C^2\) Hessian:
\[
\boxed{
\delta_z\mathbb E_\theta F
=\mathbb E_\theta[(F-\mathbb E_\theta F)s_z],
\qquad
\operatorname{secondResponse}(F;\theta,u,v)
=\mathbb E_\theta[(F-\mathbb E_\theta F)r_{uv}],
\qquad
q_\theta(z)=G_\theta(A_\theta^{-1}z,A_\theta^{-1}z).
}
\]

**The response map turns changes in data means into score-driven changes in expectations, with its nonlinear bending measured by an observable residual. The same Fisher geometry measures sampling uncertainty, so it governs both certified chamber crossings and the statistical impossibility of resolving sufficiently nearby alternatives.**

The single thing a careful reader would still want is a **global domain-and-continuation theorem**: exactly which journey from the declared featureless law to the actual data law admits a unique valid response, what happens at its boundary, and where its chamber margins cease to be statistically resolvable.