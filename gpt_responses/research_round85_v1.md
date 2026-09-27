## Executive conclusion

There is now a natural centrepiece:

> **The response map is a covariance quotient of the data manifold. Its differential discards exactly the feature-invisible score directions; at matched laws it is a Riemannian submersion. Away from matching, one relative-covariance operator controls both differential amplification and the Fisher-normalised sampling noise.**

This is stronger and more unified than a contraction statement alone. The next major geometric theorem should be the **length-budget extension to the completion**.

Two cautions are important:

1. A chamber’s landed margin is a **mean-space covariance-ellipsoid margin**, not automatically an intrinsic Fisher-distance margin.
2. Testing statements involving response distance concern the **fitted laws**. Small response distance does not imply that the original data laws are statistically indistinguishable: they can differ greatly in covariance-invisible directions.

---

# Q1. The centrepiece theorem

Write, on \(W\),
\[
D=\rho_g,\qquad \theta=\Phi(g),\qquad
C=C_{P_\theta},\qquad C_D=C_{\rho_g},
\]
where covariance operators are positive and \(Dm(\theta)|_W=-C\). For a bounded contrast \(k\), write
\[
b_D(k)=\operatorname{Cov}_D(S,k)\in W.
\]

Under your standing bounded-statistic hypotheses, bounded tilting makes both \(C_D\) and \(C\) positive definite on \(W\).

## Proposed theorem: `ResponseQuotientNoise`

For bounded tilts \(g\), bounded contrasts \(k,\ell\), and \(v\in W\):

### 1. Differential and bilinear pullback
\[
D\Phi_g[k]=-C^{-1}b_D(k),
\]
and
\[
G_g(k,\ell)
 :=\big\langle D\Phi_g[k],C\,D\Phi_g[\ell]\big\rangle
 =\langle b_D(k),C^{-1}b_D(\ell)\rangle.
\]

Consequently,
\[
\ker D\Phi_g
 =\{k:b_D(k)=0\},
\qquad
G_g(k,k)=0\iff b_D(k)=0.
\]

This includes constants, but generally has a much larger kernel.

### 2. A canonical horizontal right inverse

Use centered contrasts and the data Fisher inner product
\[
\langle k,\ell\rangle_D=\operatorname{Cov}_D(k,\ell).
\]
The horizontal space is
\[
\mathcal H_D
 =\{\langle a,S-m_D\rangle:a\in W\},
\]
the orthogonal complement of the vertical space.

Define
\[
\boxed{\quad
\operatorname{hor}_g(v)
 =-\big\langle C_D^{-1}Cv,\ S-m_D\big\rangle .
\quad}
\]
Then
\[
D\Phi_g[\operatorname{hor}_g(v)]=v.
\]

Thus the differential is surjective, and this is its canonical horizontal right inverse. Moreover, among centered contrasts producing response velocity \(v\), it uniquely minimizes variance, up to equality \(D\)-a.e.:
\[
\min_{D\Phi_g[k]=v}\operatorname{Var}_D k
 =\langle Cv,C_D^{-1}Cv\rangle.
\]

**The correction to the proposed lift:** \(k=-\langle v,S\rangle\) works directly at matched laws. Away from matching, the factor \(C_D^{-1}C\) is necessary.

### 3. Matched-law Riemannian submersion

If \(D=P_\theta\), then
\[
\operatorname{hor}_g(v)=-\langle v,S-m_D\rangle
\]
and
\[
\operatorname{Var}_D(\operatorname{hor}_g(v))
 =\langle v,Cv\rangle.
\]

For every \(k\),
\[
k=k_{\mathrm{vis}}+k_{\mathrm{invis}}
\]
modulo constants, with
\[
G_g(k,k)=\operatorname{Var}_D k_{\mathrm{vis}},
\qquad
\operatorname{Var}_D k
 =G_g(k,k)+\operatorname{Var}_D k_{\mathrm{invis}}.
\]

Hence the precise statement is:

> **At every matched point, \(D\Phi\) is a Riemannian submersion from scores modulo constants onto \(W\) with its response Fisher metric.**

Away from matching it remains a submersion, but the quotient metric is
\[
v\longmapsto \langle Cv,C_D^{-1}Cv\rangle,
\]
not generally the response Fisher metric.

### 4. One relative-covariance operator controls amplification and noise

Define, conceptually,
\[
T_g=C^{-1/2}C_D C^{-1/2}.
\]
You need not formalize square roots to state the consequences.

If
\[
C_D\preceq \kappa C,
\]
then
\[
G_g(k,k)\le \kappa\,\operatorname{Var}_D k.
\]

Define the effective response dimension
\[
d_{\mathrm{eff}}(g):=\operatorname{tr}(C^{-1}C_D).
\]
For \(n\ge1\) iid observations from \(D\),
\[
\mathbb E\,
 \big\langle\widehat m_n-m_D,\,
 C^{-1}(\widehat m_n-m_D)\big\rangle
 =\frac{d_{\mathrm{eff}}(g)}n.
\]
In particular,
\[
d_{\mathrm{eff}}(g)\le\kappa\dim W,
\qquad
d_{\mathrm{eff}}(g)=\dim W
\quad\text{at matching}.
\]

The unifying interpretation is:

- the largest eigenvalue of \(T_g\) is the maximal squared differential amplification;
- its trace is \(n\) times the expected Fisher-normalised sampling displacement.

That is the clean bridge between **varying the truth** and **sampling the truth**.

For Lean, initially state the covariance domination and trace formulas without introducing spectral theory. The spectral interpretation belongs comfortably in the note.

---

## What resolution theorem actually follows?

The strongest immediate formulation is the margin theorem already latent in your modules.

For two data laws \(D_i\), means \(m_i\), fitted covariances \(C_i\), and disjoint mean-space classes \(\mathcal C_i\), suppose
\[
\{m_i+z:z\in W,\ \langle z,C_i^{-1}z\rangle<r_i^2\}
 \subseteq\mathcal C_i.
\]
Then, for samples of size \(n_i\),
\[
\boxed{\quad
\Pr\bigl(\widehat m_0\in\mathcal C_0
          \ \text{and}\ 
          \widehat m_1\in\mathcal C_1\bigr)
\ge
1-\frac{d_{\mathrm{eff},0}}{n_0r_0^2}
 -\frac{d_{\mathrm{eff},1}}{n_1r_1^2}.
\quad}
\]
Independence between the two experiments is not needed for this union bound.

At matching, replace each effective dimension by \(\dim W\).

### Why not immediately \(1-2\dim W/(n\delta^2)\)?

Because intrinsic centre separation \(\delta\) does not itself establish either ellipsoid margin. Even in a flat common metric, disjoint radius-\(\delta/2\) balls yield the elementary bound
\[
1-\frac{8\dim W}{n\delta^2},
\]
not the proposed constant \(2\).

On a curved response manifold, one additionally needs a local comparison between centre-based covariance ellipsoids and intrinsic Fisher balls.

For example, if the relevant mean segments stay in a patch where
\[
C_{\theta(M)}\succeq\lambda I,
\qquad C_{\theta(m)}\preceq\Lambda I,
\]
then
\[
d_F(\theta(m),\theta(m+z))
 \le \sqrt{\Lambda/\lambda}\,
       \sqrt{\langle z,C_{\theta(m)}^{-1}z\rangle}.
\]
An ellipsoid contained in that patch therefore gives a Fisher-ball margin with a condition-number loss. **Containment in the patch is an additional hypothesis**, not a consequence of the covariance inequality alone.

### The small-separation statement

For fitted laws separated by \(\delta=d_F(\theta,\eta)\),
\[
H\le\delta/2,
\qquad
A=1-H^2/2\ge1-\delta^2/8.
\]
Thus, when \(\delta^2\le8\),
\[
A(P_\theta^{\otimes n},P_\eta^{\otimes n})
 =A^n\ge(1-\delta^2/8)^n,
\]
and
\[
H(P_\theta^{\otimes n},P_\eta^{\otimes n})^2
 \le n\delta^2/4.
\]

That is a precise, framework-free statement of closeness when \(n\delta^2\ll1\). Call it **product-law affinity closeness**, rather than a testing-error theorem until the testing interface exists.

Conversely, your coercive-patch result gives affinity decay at large separation. These are complementary to the chamber bound, not a single sharp resolution threshold.

---

# Q2. Compact-uniform covariance convergence

## Basic theorem: no bounded-density assumption is needed

Suppose \(Q_n,Q\) have densities \(q_n,q\) with respect to \(\nu\), and
\[
\|q_n-q\|_{L^1(\nu)}\to0.
\]
Assume, as in the bounded-feature setting, that
\[
\|S-a\|\le B\quad \nu\text{-a.e.}
\]
for some \(a\).

Then
\[
\boxed{\quad
\|C_{Q_n}-C_Q\|_{\mathrm{op}}
 \le 3B^2\|q_n-q\|_1.
\quad}
\]
Indeed, bound the second-moment difference by \(B^2\|q_n-q\|_1\), and the difference of the mean outer products by \(2B^2\|q_n-q\|_1\).

In particular,
\[
\sup_{\|w\|\le R}
\left|\operatorname{Var}_{Q_n}\langle w,S\rangle
     -\operatorname{Var}_{Q}\langle w,S\rangle\right|
\le 3B^2R^2\|q_n-q\|_1.
\]

This gives uniform convergence on bounded sets, hence on compact sets.

If \(S\) is unbounded, plain \(L^1\) convergence is insufficient; one needs suitable uniform integrability of the feature second moments.

## Lean-level route

I would avoid operator norms initially:

1. Prove bounded-observable expectation stability:
   \[
   \left|\int f(q_n-q)\,d\nu\right|
   \le\|f\|_\infty\|q_n-q\|_1.
   \]
2. Apply it to centered coordinate features and their products.
3. Prove convergence of each covariance matrix entry.
4. Use finite sums to obtain a uniform quadratic-form bound.
5. Package the operator-norm version afterward if useful.

With finite \(J\), this is likely the shortest reliable route. Centering by \(a\) gives better constants but is not essential.

## Tilting is uniformly \(L^1\)-continuous over bounded contrasts

For a common bounded tilt \(h\),
\[
\left\|\frac{e^h q_n}{\int e^h q_n}
       -\frac{e^h q}{\int e^h q}\right\|_1
\le 2e^{\operatorname{osc}h}\|q_n-q\|_1.
\]
Thus \(\|h\|_\infty\le K\) gives the uniform bound
\[
2e^{2K}\|q_n-q\|_1.
\]

This is particularly valuable: convergence is uniform over **all common tilts bounded by \(K\)**. No compactness of that infinite-dimensional tilt class is required.

For varying tilts \(h_n\to h\), \(L^\infty\) convergence is a clean sufficient hypothesis. Uniform boundedness alone does not imply convergence. Uniform boundedness plus convergence in measure, relative to a fixed limiting law, is another possible route, but need not be the first formalization.

## Pullback-form continuity: the inverse is the additional issue

For fixed bounded \(k,\ell\),
\[
G_D(k,\ell)
 =\langle b_D(k),C_{\Pi(m_D)}^{-1}b_D(\ell)\rangle.
\]

The route is:

1. \(D_n\to D\) in \(L^1\) gives \(m_{D_n}\to m_D\).
2. Your projection-law continuity gives
   \[
   \Pi(m_{D_n})\to\Pi(m_D)\quad\text{in }L^1.
   \]
3. Covariance convergence gives convergence of fitted covariance operators.
4. If the limiting fitted covariance is positive definite on the fixed \(W\), inversion is continuous.
5. The forcings converge by bounded-observable estimates.

Therefore \(G_{D_n}\to G_D\), uniformly on bounded sets of bounded contrasts if formulated using their \(L^\infty\) norms.

For compact-uniform statements, assume a **uniform fitted covariance lower bound**
\[
C_{\Pi(m_D)}\succeq\lambda I,\qquad\lambda>0.
\]
At rank-dropping boundary limits, do not claim ambient inverse or pullback continuity. A fixed-face formulation must use that face’s direction space.

### Payoffs

On interior compact patches:

- continuity of the response pullback bilinear form;
- continuity of \(d_{\mathrm{eff}}(D)=\operatorname{tr}(C_{\Pi(m_D)}^{-1}C_D)\);
- stability of covariance ellipsoids and of specified strict margin certificates.

The last wording matters. **Arbitrary class margins need not be continuous** without regularity of the class and its boundary. Continuity of the forms gives stability of a margin certificate with slack, not automatically continuity of every class-margin functional.

---

# Q3. The length budget

The minimal geometric theorem should not mention bounded functions at all.

## Core theorem: `ResponsePathLengthBudget`

Let
\[
\theta:[0,\infty)\to W
\]
be locally \(C^1\), with Fisher speed
\[
s(t)=\sqrt{\langle\dot\theta(t),
                     C_{\theta(t)}\dot\theta(t)\rangle}.
\]
Suppose
\[
\int_0^\infty s(t)\,dt<\infty.
\]
Then:

1. For \(0\le a\le b\),
   \[
   d_F(\theta(a),\theta(b))
   \le\int_a^b s(t)\,dt.
   \]
2. The path is Fisher-Cauchy at infinity.
3. It converges to \(x_\infty\in\widehat W\).
4. The quantitative tail estimate holds:
   \[
   \widehat d(\theta(t),x_\infty)
   \le\int_t^\infty s(u)\,du.
   \]
5. Its means converge to \(\operatorname{meanExt}(x_\infty)\), and
   \[
   Q_{x_\infty}
   =\Pi\!\left(\lim_{t\to\infty}m(\theta(t))\right).
   \]

The mean limit need not be assumed separately. Under bounded features, your Hellinger and mean bounds already give
\[
\|m(\theta)-m(\eta)\|\le B\,d_F(\theta,\eta).
\]

## Bounded-tilt corollary

Assume
\[
t\mapsto g_t
\]
is locally \(C^1\) in \(L^\infty(\nu)\), or satisfies an elementary parameterized-tilt differentiation package sufficient to establish
\[
\frac{d}{dt}E_{\rho_{g_t}}S
 =\operatorname{Cov}_{\rho_{g_t}}(S,\dot g_t).
\]
Then the inverse mean chart gives a locally \(C^1\) response path, and
\[
s(t)^2=G_{g_t}(\dot g_t,\dot g_t).
\]

Hence
\[
\boxed{\quad
\int_0^\infty\sqrt{G_{g_t}(\dot g_t,\dot g_t)}\,dt<\infty
\Longrightarrow
\Phi(g_t)\to x_\infty\in\widehat W.
\quad}
\]

No global bound \(\sup_t\|g_t\|_\infty<\infty\) is needed. Indeed, imposing it would exclude much of the intended boundary-concentration story: uniformly bounded tilts keep the means in a compact interior region.

### Important correction: length versus energy

On an infinite time interval,
\[
\int_0^\infty G_{g_t}(\dot g_t,\dot g_t)\,dt<\infty
\]
does **not** imply convergence. Finite \(L^2\) speed is not finite \(L^1\) speed. A bounded oscillatory path with time dependence \(\sin(\log(1+t))\) illustrates the obstruction.

On a finite horizon, finite energy does imply finite length by Cauchy–Schwarz. Thus use:

- **finite length** on \([0,\infty)\);
- **finite energy** on a finite time interval.

## Lean implementation

Split this into two modules:

1. A metric/completion theorem consuming `FisherPath` restrictions and an integrable speed bound.
2. A response-chain-rule adapter producing those paths.

If \(L^\infty\)-valued calculus is expensive, first support
\[
g_t=\sum_{j=1}^N a_j(t)h_j
\]
with bounded \(h_j\) and \(C^1\) coefficients. This already gives genuinely multi-parameter paths and avoids an unnecessary Banach-manifold development.

---

# Q4. Nonexpansion and face chains still matter

`AccessibleFaceStrata` settles a **set-theoretic and identification** question:

- which relative interiors occur together;
- which law lies over each accessible mean;
- uniqueness of the completion point there.

It does not settle the **intrinsic geometry of a stratum**.

## `AccessibleFaceNonexpansion` remains valuable

For an accessible face \(F\), the desired map
\[
j_F:W_F\to\widehat W
\]
should satisfy
\[
\widehat d(j_F(v),j_F(w))
 \le d_F^{(F)}(v,w).
\]

This is not redundant. It provides:

1. control of boundary paths by the face Fisher metric;
2. extension to a \(1\)-Lipschitz map
   \[
   \widehat j_F:\widehat{W_F}\to\widehat W;
   \]
3. transfer of face-internal finite-length accessibility into ambient accessibility.

Do not expect equality merely from the available facts: ambient paths may shortcut through the interior or other strata.

### A promising proof route

Start with an ambient sequence converging to one accessible point of \(F\). Apply bounded tangential tilts along a compact face path. Your tilt action identifies the limiting endpoints; compact-uniform tilted covariance convergence identifies the limiting path lengths. Pass the ambient path-length inequality to the limit.

This is exactly where `TiltedFisherCompactConvergence` pays for itself.

## `FaceChainAccessibility` becomes compositional

The useful theorem is not another proof that one point gives the whole relative interior. It is:

> If \(F\) is ambient-accessible, and \(E\subseteq F\) is accessible in the intrinsic face model, then \(E\) is ambient-accessible.

More deeply, seek compatibility of the extension maps:
\[
\widehat j_F\circ\widehat j_E^{\,F}
 =\widehat j_E,
\]
where both constructions are defined.

This makes accessibility recursive and the boundary atlas coherent.

The criterion for initial accessibility remains a separate question. Every face of a polytope is exposed, but **existence of an exposing normal does not by itself establish finite Fisher length along its ray**. Any general-face ray theorem needs the same kind of integrability analysis as the facet case.

---

# Q5. Ranked next modules

Here is my ranking by depth × reachability.

| Rank | Module | Principal statement |
|---|---|---|
| **1** | `ResponseHorizontalLift` | Canonical right inverse \(v\mapsto-\langle C_D^{-1}Cv,S-m_D\rangle\); surjectivity; variance-minimizing lift; exact matched submersion. |
| **2** | `ResponseBilinearForm` / `ResponseQuotientNoise` | \(G(k,\ell)=\langle b(k),C^{-1}b(\ell)\rangle\); bilinear score decomposition; \(d_{\mathrm{eff}}\le\kappa\dim W\), linking amplification and noise. |
| **3** | `TiltedFisherCompactConvergence` | \(L^1\) law convergence implies compact-uniform covariance convergence, uniformly under bounded common tilts. |
| **4** | `ResponsePathLengthBudget` | Integrable pullback speed gives a completion endpoint, a tail-distance bound, and the projected limiting law. |
| **5** | `ResponseFormContinuity` | Interior continuity of pullback forms, horizontal lifts, effective dimension, and strict margin certificates. |
| **6** | `AccessibleFaceNonexpansion` | Face response chart is \(1\)-Lipschitz and extends to the intrinsic face completion. |
| **7** | `ResponseIntrinsicResolution` | Convert certified ellipsoid margins to intrinsic Fisher-ball margins on controlled patches; derive a correct two-class separation bound. |
| **8** | `FaceChainAccessibility` | Intrinsic face accessibility transfers to the ambient completion; establish compatibility along face inclusions. |
| **9** | `ResponseProductAffinity` | Small-\(n\delta^2\) product-affinity lower bounds, paired with the landed coercive-patch affinity upper bounds. |
| **10** | `ResponseHellingerAtlas` | Express the projected-law atlas in square-root \(L^2\) coordinates and identify its Hellinger topology, without conflating it with the Fisher completion topology. |

For rank 10, the elementary bridge is
\[
H^2\le\|p-q\|_1\le2H.
\]
Thus the landed \(L^1\) embedding has an immediate Hellinger reformulation. What is **not** immediate is that the Fisher completion equals the entire Hellinger closure.

## What the note should now claim

I would organize the response-map section around four main theorems.

### I. The covariance quotient theorem
`ResponsePullbackForm`, augmented by `ResponseHorizontalLift` and the bilinear form.

**Claim:** response discards precisely feature-invisible scores; matching makes the horizontal quotient exactly Fisher-isometric.

### II. The response noise and chamber theorem
`FisherNormalisedSampling` + `ResponseClassResolution`.

**Claim:** the expected normalized sampling displacement is \(d_{\mathrm{eff}}/n\), exactly \(\dim W/n\) at matching; certified chambers are stable above that scale.

### III. The local statistical geometry theorem
`ResponseLocalTesting`.

**Claim:** on controlled patches, response Fisher distance and fitted-law Hellinger distance are quantitatively comparable, with corresponding iid affinity bounds.

### IV. The stratified completion theorem
The earlier completion results + `AccessibleFaceStrata`.

**Claim:** accessible boundary means occur in whole relative face interiors, and the completion law is uniquely the information projection of the extended mean.

Then add the length-budget theorem as the bridge from **paths through data** to **endpoints in the stratified response atlas**.

---

# Q6. Corrections and preferred restatements

## 1. The signs are consistent

With \(Dm=-C\),
\[
\operatorname{responseVel}=-C^{-1}b,
\]
so
\[
-\langle\operatorname{responseVel},b\rangle
 =\langle b,C^{-1}b\rangle\ge0.
\]
Likewise, the sampling operator is negative and its energy is positive on \(W\).

For exposition, write the main formulas using positive covariance operators \(C\). Keep the negative derivative convention explicit at the interface.

## 2. Matched contraction is exactly right

Yes:
\[
G_g(k,k)\le\operatorname{Var}_{P_\theta}k
\]
is the correct contraction at a matched point.

The stronger, more informative restatement is
\[
G_g(k,k)=\operatorname{Var}_{P_\theta}k
\iff
k\text{ is a centered linear feature contrast, modulo constants/a.e. equality}.
\]

This is a pointwise differential contraction. It is not automatically a global contraction on the entire bounded-tilt data manifold.

## 3. Keep the ellipsoid margin as the primitive definition

Your current margin is the right primitive for the sampling theorem because the statistic controlled exactly is
\[
\langle\widehat m-m,C^{-1}(\widehat m-m)\rangle.
\]

Call it a **Fisher-normalised mean-ellipsoid margin**, or a **frozen Fisher margin**. Calling it simply a Fisher ball risks confusion with intrinsic response distance.

Then introduce separately:

- intrinsic Fisher-distance margins;
- Hellinger-law margins.

Prove transfer lemmas under explicit geometric hypotheses. A Hellinger margin should not replace the landed definition.

## 4. Exact noise is not exact expected response distance

The identity
\[
\mathbb E\,\operatorname{samplingEnergy}(\widehat m-m)=\dim W/n
\]
is exact for a frozen quadratic form. It is not an identity for
\[
\mathbb E\,d_F(\theta(\widehat m),\theta(m))^2,
\]
nor does it guarantee that \(\theta(\widehat m)\) exists in the interior.

This distinction should be visible in the note.

## 5. Featureless to actual data has a natural scope

For a target law with bounded log-density relative to \(\nu\), the path
\[
g_t=t\log(dD/d\nu),\qquad 0\le t\le1,
\]
lies directly in the bounded-tilt manifold.

For more general targets, use approximation or a limiting path. The completion theorem then identifies the **response endpoint**, not necessarily convergence of the full data law, and not recoverability of its invisible component.

Also, \(\nu\) is the featureless reference law; calling it “maximum entropy” requires the intended reference measure and constraint convention.

---

The deepest next move is therefore quite specific: **finish the horizontal quotient picture, then prove that its pullback speed budgets motion all the way to the completion.** The first tells you what a response direction means; the second tells you when an entire journey through data has a well-defined structural endpoint.