The deepest next step is to separate—and then reconnect—three structures:

1. **The response-law space:** now globally understood as the closed moment polytope, embedded in \(L^1\).
2. **The response metric:** Fisher length, its completion, and which boundary laws it reaches.
3. **The statistical observation map:** which changes in the data are visible through the structural statistic, at what sampling cost.

Your compactification essentially completes the first layer. The next major theorem should identify the differential geometry of the third layer; the next major existence theorem should connect the second layer to all accessible face strata.

One important caution throughout:

> \(Q_x=\Pi(\operatorname{meanExt}x)\) identifies completion **laws**, but does not by itself prove that two completion points with the same mean are equal.

That is a separate completion-fibre question.

# Q1. Global resolution

## A. Testing: a clean two-sided local theorem

Use the convention
\[
H^2(P,Q)=\int(\sqrt p-\sqrt q)^2,\qquad
A(P,Q)=1-\tfrac12H^2(P,Q).
\]
Then
\[
A(P^{\otimes n},Q^{\otimes n})=A(P,Q)^n.
\]

For the optimal sum of the two testing errors,
\[
R_n^*(P,Q)=1-\operatorname{TV}(P^{\otimes n},Q^{\otimes n}),
\]
the clean affinity sandwich is
\[
1-\sqrt{1-A(P,Q)^{2n}}
\;\le\;
R_n^*(P,Q)
\;\le\;
A(P,Q)^n.
\]

Together with your landed \(H\le d_F/2\), this gives the global one-way result
\[
R_n^*(P_\theta,P_{\theta'})
\ge
\max\!\left(0,1-\frac{\sqrt n}{2}d_F(\theta,\theta')\right).
\]

Thus \(d_F\ll n^{-1/2}\) implies indistinguishability **when the observations are drawn from the response laws**.

### An elementary local converse is already within reach

Suppose:

- \(M_0,M_1\in U\);
- \(U\subseteq\operatorname{ri}K\) is convex;
- \(C_{\theta(M)}\ge\lambda I_W\) on \(U\);
- \(\|S-a\|\le B\) almost surely, for a fixed centre \(a\).

For any two relevant laws,
\[
\|m(P)-m(Q)\|\le 2B\,H(P,Q).
\]
Your local metric control then gives
\[
\boxed{
\frac{\sqrt\lambda}{2B}\,
d_F(\theta(M_0),\theta(M_1))
\le
H(P_{\theta(M_0)},P_{\theta(M_1)})
\le
\frac12d_F(\theta(M_0),\theta(M_1)).
}
\]

This needs no new differential-geometric lower-bound machinery. Consequently, writing \(a_U=\sqrt\lambda/(2B)\),
\[
R_n^*\le
\exp\!\left(-\frac{n a_U^2}{2}d_F^2\right).
\]

That is the clean first two-sided result:

> On a coercive convex mean patch, the binary testing scale is \(n^{-1/2}\) in Fisher distance, with explicit patch-dependent constants.

A later, sharper theorem is the local asymptotic identity
\[
H(P_\theta,P_{\theta+d\theta})
=
\tfrac12\|d\theta\|_{F,\theta}+o(\|d\theta\|),
\]
uniformly on compact interior patches. The elementary bound above is enough to land the statistical theorem first.

There is no global converse from the currently listed results alone. Large intrinsic distance need not have a quantitative lower bound in extrinsic Hellinger distance without further geometry.

### Crucial distinction: samples from \(\rho\), or samples from \(\Phi(\rho)\)?

Closeness of responses does **not** imply indistinguishability of the original data laws:
\[
\Phi(\rho)=\Phi(\rho')
\]
can hold for highly distinguishable \(\rho,\rho'\).

Response testing and data testing coincide under a matched-model assumption. Otherwise, the precise claim is about information retained by the response map, not all information present in the samples.

## B. The trace identity needs no Fisher-orthonormal basis

Let \(W\) be the structural subspace and let \(C_\theta:W\to W\) be positive definite. Define the ambient inverse-on-\(W\) operator
\[
R_\theta
=
\iota_W\circ C_\theta^{-1}\circ \operatorname{proj}_W.
\]
Then
\[
\boxed{
\mathbb E\langle\widehat M-m,R_\theta(\widehat M-m)\rangle
=
\frac1n\operatorname{tr}(R_\theta C_\rho).
}
\]

At a matched law,
\[
R_\theta C_\theta=\operatorname{proj}_W,
\]
so
\[
\boxed{
\mathbb E\|\widehat M-m\|_{C_\theta^{-1}}^2
=
\frac{\dim W}{n}.
}
\]

A Lean-friendly proof is exactly your proposed ambient-coordinate route:

1. expand the quadratic form using the standard basis of `J → ℝ`;
2. use the covariance-of-the-sample-mean identity;
3. identify the resulting sum as a trace;
4. use `trace proj_W = finrank ℝ W`.

No Fisher-orthonormal basis is required. This is an exact statement about mean-coordinate error; it is not yet an exact statement about \(d_F(\theta(\widehat M),\theta(m))^2\).

### The companion exact theorem: optimal directional SNR

At a matched law, with \(b=-C_\theta\theta'\),
\[
\boxed{
\sup_{w\ne0}
\frac{\delta^2\langle w,b\rangle^2}
{\operatorname{Var}_{P_\theta}\langle w,S\rangle/n}
=
n\delta^2\,b^\top C_\theta^{-1}b
=
n\delta^2|\theta'|_F^2.
}
\]
The supremum is attained by \(w\propto\theta'\), when \(\theta'\ne0\).

This upgrades the directional floor into a particularly satisfying global-in-directions statement:

> Fisher speed is exactly the best structural signal-to-noise ratio per sample.

Here \(n^{-1/2}\) is the scale for a specified direction or binary alternative; \(\sqrt{d/n}\) is the aggregate \(d\)-dimensional estimation scale. They should not be conflated.

## C. “Chamber size” should be a margin, not a diameter

For a response class \(C\), the relevant local quantity is
\[
r_C(M)
=
\inf_{N\notin C} d_{\mathrm{resp}}(M,N),
\]
or, more conveniently for a first formal theorem, the frozen Fisher-mean margin
\[
r_C^{\mathrm{lin}}(M)
=
\inf_{N\notin C}
\|N-M\|_{C_{\theta(M)}^{-1}}.
\]

If an empirical mean lying in that ellipsoid remains in the same class, then the trace identity and Markov give
\[
\mathbb P(\widehat M\notin C)
\le
\frac{\operatorname{tr}(C_\theta^{-1}C_\rho)}
     {n\,r_C^{\mathrm{lin}}(M)^2}.
\]
At matching this is \(d/(nr^2)\).

This is a genuine, finite-sample class-stability statement. Local metric comparison translates it into a Fisher-margin statement.

Two qualifications:

- A chamber’s **diameter** does not control classification near its boundary.
- The faces of a single polytope give a stratification; their complement inside \(K\) is just \(\operatorname{ri}K\). Multiple interior chambers require an additional discriminant or class partition.

For the germ theorem, first specify the map
\[
M\longmapsto\text{germ/geometry class}.
\]
Then its class-changing locus supplies the walls, and distance to that locus supplies the margin. Chart transport alone does not produce a statistical separation theorem.

Also, \(r\lesssim\sqrt{d/n}\) does not by itself prove impossibility. Impossibility requires a nearby competing class and a testing lower bound.

# Q2. Multi-parameter data manifolds

I would land **(i) and (ii), together with the matched projection identity**, before volume or geodesics.

Let
\[
\rho_g=\frac{e^g\nu}{\int e^g\,d\nu},\qquad
m_g=\mathbb E_{\rho_g}S,\qquad
\Phi(g)=\theta(m_g).
\]
For a tangent score \(k\), put
\[
b_g(k)=\operatorname{Cov}_{\rho_g}(S,k).
\]

The central theorem is
\[
D\Phi_g[k]=-C_{\Phi(g)}^{-1}b_g(k),
\]
and, bilinearly,
\[
\boxed{
G_g^{\mathrm{resp}}(k,\ell)
=
\langle b_g(k),C_{\Phi(g)}^{-1}b_g(\ell)\rangle.
}
\]

## 1. Invisible directions and the observable quotient

Exactly,
\[
\ker G_g^{\mathrm{resp}}
=
\ker D\Phi_g
=
\{k:\operatorname{Cov}_{\rho_g}(S,k)=0\}.
\]

Thus this is generally a **positive-semidefinite pull-back tensor**, not a Riemannian metric on the whole data manifold.

On a constant-rank patch, it induces the response metric on the local quotient by fibres of \(\Phi\). This is the precise version of “the geometry of visible data changes”.

Do not claim a global manifold quotient without additional hypotheses.

## 2. Relative covariance is the correct amplification criterion

Suppose
\[
C_{\rho_g}\preceq \kappa_g C_{\Phi(g)}
\quad\text{on }W.
\]
Then
\[
\boxed{
G_g^{\mathrm{resp}}(k,k)
\le
\kappa_g\operatorname{Var}_{\rho_g}(k)
=
\kappa_g G_g^{\mathrm{data}}(k,k).
}
\]

A basis-free proof uses
\[
\langle b,C_\Phi^{-1}b\rangle
=
\sup_{w\ne0}
\frac{\operatorname{Cov}_{\rho_g}(\langle w,S\rangle,k)^2}
     {\operatorname{Var}_{P_{\Phi(g)}}\langle w,S\rangle},
\]
followed by covariance Cauchy–Schwarz and covariance domination.

This also yields path-length control:
\[
L_F(\Phi\circ\gamma)
\le
\int
\sqrt{\kappa_{\gamma(t)}}\,
|\dot\gamma(t)|_{\mathrm{data}}\,dt.
\]

## 3. At matching: an exact orthogonal decomposition

When \(\rho_g=P_{\Phi(g)}\), let
\[
k_{\mathrm{vis}}
=
\langle C_{\Phi(g)}^{-1}b_g(k),S-m_g\rangle,
\]
and
\[
k_{\mathrm{inv}}=k-\mathbb E_{\rho_g}k-k_{\mathrm{vis}}.
\]
Then \(k_{\mathrm{inv}}\) is orthogonal to every centred structural statistic, and
\[
\boxed{
\operatorname{Var}_{\rho_g}(k)
=
G_g^{\mathrm{resp}}(k,k)
+
\mathbb E_{\rho_g}k_{\mathrm{inv}}^2.
}
\]

This is the most beautiful statement in this direction:

> At a matched law, response formation is orthogonal projection of the data score onto the structural tangent space. Response Fisher energy is retained score energy; the residual is invisible energy.

It simultaneously explains contraction, null directions, equality cases, and your resolution story.

Away from matching, there is no unconditional contraction: the response model can amplify a data tangent because its covariance differs from the data covariance.

## 4. Why volume and geodesics come later

For an identifiable \(k\)-parameter data family with \(k\le d\), the response \(k\)-Jacobian is
\[
J_k\Phi
=
\sqrt{\det\!\big((G^{\mathrm{data}})^{-1}G^{\mathrm{resp}}\big)},
\]
and covariance domination gives \(J_k\Phi\le\kappa^{k/2}\). It vanishes at rank loss.

That is useful, but “how much response space is covered” additionally needs multiplicity and an area/coarea theorem. A determinant alone is not coverage.

There is also no general geodesic-preservation theorem. Your map need not be an isometry or a Riemannian submersion on the full data manifold. Length comparison is the robust statement to formalise first.

# Q3. Accessibility and face chains

## A. Union of accessible open-face strata is now cheap

For every face \(F\) with a well-defined face family, the desired theorem is
\[
\boxed{
\operatorname{meanExt}(\widehat W)\cap\operatorname{ri}F\ne\varnothing
\quad\Longrightarrow\quad
\operatorname{ri}F
\subseteq
\operatorname{meanExt}(\widehat W).
}
\]

Hence
\[
\operatorname{meanExt}(\widehat W)
=
\bigcup_{F\in\mathcal A}\operatorname{ri}F
\]
for a collection \(\mathcal A\) of accessible faces, including \(K\).

### Route

Choose \(x\) with \(\operatorname{meanExt}x=M_0\in\operatorname{ri}F\).

1. `CompletionLawEqProjection` gives \(Q_x=\Pi(M_0)\).
2. Identify this projection as \(P^F_{v_0}\).
3. For \(M\in\operatorname{ri}F\), use the face mean chart to find \(v\) with \(m_F(v)=M\).
4. Lift \(v-v_0\) to an ambient parameter shift \(h\).
5. Tilt equivariance gives
   \[
   Q_{\operatorname{tiltExt}h(x)}=P^F_v.
   \]
6. Its mean is \(M\).

You do not need completion injectivity. Once the projection/face-family identification is available, Pythagoras is only needed upstream to establish that identification.

## B. The stronger bridge: nonexpansion from any accessible face law

Fix an accessible \(x\) with \(Q_x=P^F_{v_0}\), and define
\[
j_{F,x}(v)=\operatorname{tiltExt}(v-v_0)x
\]
using a fixed ambient lift of the face parameter space.

The next metric theorem should be
\[
\boxed{
\widehat d_F(j_{F,x}(v),j_{F,x}(w))
\le d_F^{\,F}(v,w).
}
\]

Notably, this can start from an **arbitrary accessible lift**, not only a finite normal ray.

Proof route:

- choose \(\theta_n\to x\) in the ambient Fisher completion;
- translate a face parameter path by \(\theta_n-v_0\);
- prove its ambient covariance tensors converge uniformly along the compact path to the face covariance tensors;
- pass to lengths, then take the infimum over paths.

Bounded \(S\), \(L^1\)-convergence of the laws, and bounded tilts on compact parameter sets are the main ingredients.

This extends to a nonexpansive map
\[
\widehat j_{F,x}:\widehat W_F\longrightarrow\widehat W
\]
with compatible laws and means.

It is not yet legitimate to call this map canonical or injective.

## C. Face chains then become composition

The fundamental inheritance theorem is
\[
F\text{ ambient-accessible},\quad
G\subseteq F\text{ intrinsically accessible in the }F\text{-family}
\quad\Longrightarrow\quad
G\text{ ambient-accessible}.
\]

A flag
\[
K=F_0\supset F_1\supset\cdots\supset F_r
\]
with finite intrinsic normal rays at each step therefore makes \(F_r\) accessible.

The order is:

1. accessible open-face strata;
2. compact convergence under tilting;
3. accessible-face nonexpansion;
4. extension to face completions;
5. face-chain accessibility.

Finiteness of the face lattice does not itself prove finiteness of these Fisher normal rays.

# Q4. Ranked next modules

These are intended as narrow modules of roughly the requested size, assuming the existing differentiation, completion, and covariance APIs. I would keep the sharper asymptotic testing theorem and area/coarea machinery out of this tranche.

| Rank | Module | Type | Statement and route |
|---|---|---|---|
| **1** | `ResponsePullbackForm` | **Deep** | Multi-parameter derivative and bilinear pull-back formula; null space equals covariance-invisible directions. Differentiate the mean map and compose with the inverse chart derivative. |
| **2** | `ResponseScoreProjection` | **Deep** | Matched orthogonal score decomposition and unmatched relative-covariance comparison. Use the covariance quadratic form and Cauchy–Schwarz. |
| **3** | `AccessibleFaceStrata` | **Deep, cheap now** | One extended mean in \(\operatorname{ri}F\) implies all of \(\operatorname{ri}F\). Face chart plus completion tilt action. |
| **4** | `FisherNormalisedSampling` | **Deep** | Exact trace risk, matched \(d/n\), and optimal directional SNR. Ambient standard-basis expansion plus inverse-covariance algebra. |
| **5** | `ResponseLocalTesting` | **Deep** | Product affinity, testing-error sandwich, and explicit two-sided Fisher–Hellinger comparison on coercive convex patches. Use bounded-statistic mean control and your local metric theorem. |
| **6** | `TiltedFisherCompactConvergence` | Infrastructure with leverage | \(L^1\)-law convergence gives compact-uniform convergence of bounded-tilt covariance forms. Control tilt normalisers uniformly, then bounded moment integrals. |
| **7** | `AccessibleFaceNonexpansion` | **Deep** | Construct \(j_{F,x}\), prove nonexpansion, extend to face completions, identify means. Approximate \(x\) and compare lengths along fixed face paths. |
| **8** | `FaceChainAccessibility` | **Deep synthesis** | Intrinsic face accessibility transfers to ambient accessibility; finite normal-ray flags give accessible terminal faces. Compose the preceding extension maps. |
| **9** | `ResponseClassResolution` | **Deep application** | Define class margin and bound class-change probability by \(\operatorname{tr}(C_\theta^{-1}C_\rho)/(nr^2)\). Keep the class partition abstract so it later instantiates to germ classes. |
| **10** | `ResponsePathLengthBudget` | **Deep synthesis** | Response distance bounded by integrated pull-back speed; integrable tails imply Fisher completion convergence and accessibility of the limiting mean. Extract existing `hwin` bookkeeping, then generalise to multi-parameter paths. |

The last module gives an existence criterion independent of face chains:
\[
\int_0^\infty
\sqrt{b_t^\top C_{\Phi(t)}^{-1}b_t}\,dt<\infty
\quad\Longrightarrow\quad
\Phi(t)\text{ has a Fisher-completion limit}.
\]
If \(m_t\to M_\infty\), that limit has law \(\Pi(M_\infty)\).

This is exactly the missing bridge between your unconditional response-law convergence and metric accessibility.

The Hellinger version of `ResponseCompactification` is a small corollary, not one of the ten main projects.

# Q5. Corrections and naming

## 1. “Response compactification” is a law-space compactification

Your theorem identifies
\[
K\cong \{\Pi(M):M\in K\}\subset L^1(\nu).
\]
It does not yet identify \(K\) with the Fisher completion, nor show that all of \(K\) is accessible.

A docstring saying **“compactification of the interior response laws”** would remove the ambiguity without requiring a rename.

## 2. `DataManifoldResponseLaw` has a law limit, not necessarily a completion limit

The convergence
\[
\Pi(m_t)\to\Pi(M_\infty)
\]
does not imply that \(\theta_t\) is Fisher-Cauchy. Your result correctly avoids accessibility; keep that distinction explicit.

The proposed length-budget theorem supplies a sufficient condition for the stronger conclusion.

## 3. The resolution hypotheses formalise unit linearised SNR

Your assumptions
\[
0<\mathbb E\langle w,\widehat\Delta\rangle^2,
\qquad
\mathbb E\langle w,\widehat\Delta\rangle^2
\le
\delta^2\langle w,b_t\rangle^2
\]
are appropriate for:

> The linearised directional shift is at least one sampling standard deviation.

They are not, by themselves, a testing guarantee at a stated error probability.

I would use a name such as `LinearizedDirectionalSNRAtLeastOne`, or retain “resolvable” with that definition stated prominently.

For a finite shift, replace \(\delta b_t\) by
\[
m(\rho_{t+\delta})-m(\rho_t),
\]
or supply a Taylor-remainder bound. For confidence level \(1-\alpha\), introduce the corresponding threshold rather than treating one standard deviation as universal.

`hnoise` is a sensible exclusion of degenerate directions. For a total theorem, handle zero variance separately rather than divide by it.

## 4. Clarify the equality statement

At matching, \(w\propto\theta'\) attains the **response** directional bound and the optimal structural SNR.

It need not attain equality in the **data-score** Cauchy–Schwarz bound. That additionally requires the centred score \(h-\mathbb Eh\) to lie in the relevant one-dimensional structural span. The score-projection theorem exposes exactly this residual gap.

## 5. Coercivity controls the inverse chart in the upper-distance direction

A lower covariance bound gives
\[
d_F(\theta(M_0),\theta(M_1))
\lesssim\|M_1-M_0\|.
\]
It does not alone give the opposite mean-distance comparison. Upper covariance bounds, bounded-statistic Hellinger estimates, or other global controls supply that direction.

---

**My recommendation:** land `ResponsePullbackForm` and `ResponseScoreProjection` as the next conceptual centrepiece, and `AccessibleFaceStrata` as the next immediate boundary theorem.

Together they say:

> The data manifold maps to the response polytope by retaining structural score energy in the interior, while Fisher accessibility selects whole open-face strata on the boundary.

That is a considerably deeper picture than another isolated path estimate—and it connects directly to both the resolution story and the remaining existence problem.