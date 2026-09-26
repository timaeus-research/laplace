## Executive verdict

**F is now the deepest next step—but the proposed ray/path equivalence is false in higher codimension.** There is a concrete charged-square example in which:

- the natural ray to a vertex has **infinite** Fisher length;
- a ray to an adjacent edge has **finite** Fisher length;
- a curved path remaining in the interior reaches the original vertex with **finite** Fisher length.

So the next structure is **flagwise accessibility and the intrinsic Fisher completion**, not another ray classification.

The other important correction is that **response projection is not globally Fisher-contracting**. Its exact differential distortion is governed by the mismatch between \(C_\rho\) and \(C_{q_{E_\rho S}}\). Your residual-variance theorem is its on-family, orthogonal-projection specialization.

---

# 1. Ranking and Lean routes

## 1. F: intrinsic Fisher completion, with flagwise access

The central question is now:

> Which completed responses \(q_M\) occur as finite-length endpoints of curves in the interior response manifold, and when do different approaches define the same point of the intrinsic metric completion?

The distinction between an \(L^1\) limit and an intrinsic completion point matters: your atlas identifies the limiting law, but does not by itself identify all finite-length approaches metrically.

**First precise target:** formalize the charged-square counterexample below. Then prove the **codimension-one path-independent criterion** and a **flag-lifting/accessibility theorem**. These establish both the positive theorem and the exact obstruction to extending it naively.

**Lean route.** Define Fisher speed either in natural coordinates,
\[
|\dot\eta|_{\mathrm F}^2=\operatorname{Var}_{P_\eta}\langle\dot\eta,S\rangle,
\]
or mean coordinates,
\[
|\dot M|_{\mathrm F}^2=\langle\dot M,C_{q_M}^{-1}\dot M\rangle,
\]
after reducing to identifiable coordinates. Start with the scalar speed lower bound and the coordinate-speed upper bound. The counterexample then uses your shell classification twice, elementary variance bounds, and a smooth monotone diagonal choice. The codimension-one theorem uses your vertex-gap criterion to bound the face-tangential parameter, followed by a Schur-complement estimate.

## 2. G′: nonlinear information projection and its exact differential geometry

The deepest extension of ResponseDefect is not “the defect is convex”—it generally is not—but the package:

1. global KL minimization and Pythagoras;
2. exact differential of response projection;
3. exact Fisher distortion;
4. a second-derivative identity explaining the failure of convexity.

This makes the distinction between **KL projection** and **Fisher orthogonal projection** completely explicit.

**Lean route.** Prove the arbitrary-data Pythagorean identity by subtracting log densities; the only cancellation needed is moment matching. Obtain the differential from your inverse mean-map machinery. Prove the covariance criterion for contraction by finite-dimensional linear algebra. Finally differentiate your covariance formula for \(\mathcal E'\), under suitable third-moment/differentiation hypotheses.

## 3. J: split the defect into “unrecorded information” and “non-exponential feature information”

There are two distinct reasons the response fails to recover the data law:

- information within the fibres of \(S\);
- information in the distribution of \(S\) beyond its mean.

Writing \(\rho^S\) for the law whose density relative to \(\nu\) is
\[
E_\nu\!\left[\frac{d\rho}{d\nu}\,\middle|\,\sigma(S)\right],
\]
the conceptual theorem is
\[
D(\rho\|q_M)
=
D(\rho\|\rho^S)+D(\rho^S\|q_M),
\qquad M=E_\rho S.
\]
Thus your defect itself has a second, statistically meaningful decomposition.

**Lean route.** Begin with a finite-valued statistic, where conditional densities are explicit normalized fibre densities. This should reuse the fibre results you just landed. Only afterward generalize through conditional expectation; avoid making full disintegration infrastructure a prerequisite.

## 4. H: characterize the response retraction, rather than seek false nonexpansiveness

The map is generally neither Fisher nor Hellinger 1-Lipschitz. What survives is:

- an orthogonal differential **at laws in the family**;
- a precise off-family distortion formula;
- a one-sided KL contraction when the comparison law lies in the family.

**Lean route.** Most of this should be corollaries of item 2. Formalize a small finite counterexample to block future false conjectures, then package covariance domination and density-ratio bounds as positive substitutes.

## 5. I: natural-parameter compactification topology

Still worthwhile, but your face/vertex-gap equivalence now contains much of its substance. Flags become more interesting when they encode **different metric access mechanisms**, rather than merely convergence.

**Lean route.** Build convergence and equivalence-of-approaches statements from `tendsto_meanMap_iff_faceMean_and_vertexGaps`; distinguish the response-space quotient topology from a finer flag compactification. Do not force a unique flag onto sequences that admit several asymptotic descriptions.

---

# 2. Top item: a precise higher-dimensional counterexample

Use \(S=\mathrm{id}\) on \([0,1]^2\), and the convention
\[
P_{(r,t)}(dx\,dy)\propto e^{-rx-ty}\nu(dx\,dy).
\]

Let
\[
K_0=0,\qquad K_n=\sum_{j=1}^n4^j,\qquad
y_n=2^{-(K_n+2)}.
\]
Take \(\nu\) to be the normalization of
\[
\delta_{(0,0)}+\delta_{(1,0)}+\delta_{(0,1)}+\delta_{(1,1)}
+
\sum_{n\ge1}16^{-n}
\sum_{k=K_{n-1}+1}^{K_n}\delta_{(2^{-k},y_n)}.
\]

This is a **charged square**: every vertex has positive mass.

Let \(M=(0,0)\). Then \(q_M=\delta_{(0,0)}\).

### Precise conclusions

1. For \(u=(1,1)\),
   \[
   P_{\lambda u}\longrightarrow q_M\quad\text{in }L^1,
   \qquad
   \int_0^\infty
   \sqrt{\operatorname{Var}_{P_{\lambda u}}(X+Y)}\,d\lambda
   =\infty.
   \]

2. There exists a \(C^1\) interior mean path
   \[
   M_s=\operatorname{meanMap}(\eta_s)\longrightarrow M
   \]
   with
   \[
   \int_0^\infty
   \sqrt{\operatorname{Var}_{P_{\eta_s}}
                  \langle\dot\eta_s,S\rangle}\,ds<\infty.
   \]

Thus, **finite accessibility of \(q_M\) is strictly weaker than finite length of the fixed-\(u\) natural ray to \(q_M\)**.

### Why the diagonal ray is infinite

For \(K_{n-1}<k\le K_n\),
\[
2^{-k}\le 2^{-k}+y_n\le \tfrac54\,2^{-k}.
\]
Consequently the diagonal-gap dyadic shells each carry, up to a bounded shift of shell indices, mass \(16^{-n}\).

There are \(4^n\) such shells in block \(n\). Hence
\[
\sum_k\sqrt{a_k}
\ \gtrsim\
\sum_n4^n\sqrt{16^{-n}}
=\sum_n1
=\infty.
\]

### Why the edge ray is finite

For the ray exposing the bottom edge \(G=\{y=0\}\), all \(4^n\) points of block \(n\) have the **same** gap \(y_n\). Its shell mass is therefore
\[
4^n16^{-n}=4^{-n}.
\]
Thus
\[
\sum_n\sqrt{4^{-n}}<\infty.
\]

On the bottom edge, the conditional family is just a two-point family, whose approach to \((0,0)\) has finite Fisher length.

### Why this really yields an interior path—not merely a concatenation through the boundary

There is a direct estimate.

Using the unnormalized measure above, put
\[
B(t)=\int y^2e^{-ty}\,d\nu_{\mathrm{unnorm}},
\qquad
H(t)=\sum_{\text{cloud atoms}}w\,x^2e^{-ty}.
\]
The finite bottom-edge ray implies
\[
\int_0^\infty\sqrt{B(t)}\,dt<\infty;
\]
the atom mass at \(y=0\) makes \(B(t)\) uniformly comparable to that ray’s variance.

Choose a smooth increasing \(t=t(r)\to\infty\) sufficiently fast that
\[
H(t(r))\le e^{-r}.
\]
The atom at \((0,0)\) keeps every partition function bounded below, so
\[
\operatorname{Var}_{P_{(r,t(r))}}X\le 3e^{-r},
\qquad
\operatorname{Var}_{P_{(r,t(r))}}Y\le B(t(r)).
\]
By the triangle inequality in centered \(L^2\),
\[
\sqrt{\operatorname{Var}(X+t'(r)Y)}
\le
\sqrt3\,e^{-r/2}+t'(r)\sqrt{B(t(r))}.
\]
Both terms are integrable. This proves finite interior access.

**Geometric interpretation:** first suppress the cloud in the \(y\)-direction, where many expensive diagonal shells collapse into one cheap shell per block; then move toward the vertex. A curved path can exploit information that a fixed normal ray cannot.

---

# 3. What is true for arbitrary paths?

## The proposed scalar lower bound is correct, with constant \(1\)

For an interior path \(M_s\), write \(C_s=C_{q_{M_s}}\). Then
\[
|\dot M_s|_{\mathrm F}
=\sqrt{\langle\dot M_s,C_s^{-1}\dot M_s\rangle}.
\]
Cauchy–Schwarz gives
\[
\boxed{
|\dot M_s|_{\mathrm F}
\ge
\frac{|\langle u,\dot M_s\rangle|}
{\sqrt{\operatorname{Var}_{q_{M_s}}\langle u,S\rangle}}.
}
\]
Therefore your proposed integrated inequality holds exactly.

**But its denominator is path-dependent.** The counterexample above shows that it cannot generally be replaced by the variance profile of the fixed-\(u\) ray.

## The sharp codimension-one positive theorem

In the charged-polytope setting, after removing nonidentifiable coordinates:

> If \(F\) is a facet and \(M\in\operatorname{ri}F\), then \(q_M\) is accessible by some finite-Fisher-length interior path iff the normal ray producing \(q_M\) has finite Fisher length—equivalently, iff its shell square-root sum converges.

This does **not** say every approaching path has finite length; arbitrary oscillations can create infinite length.

The proof mechanism is particularly clean. Any approaching natural parameter can be written
\[
\eta_s=r_su+v_s,
\qquad r_s\to\infty,\quad v_s\to v_M,
\]
with \(v_s\) face-tangential. Your face-conditioning criterion supplies the tangential convergence.

The covariance block matrix has normal Schur complement
\[
C_{nn}-C_{nT}C_{TT}^{-1}C_{Tn}.
\]
Because \(C_{TT}\) stays nondegenerate on the limiting face and off-face mass tends to zero,
\[
C_{nT}C_{TT}^{-1}C_{Tn}=o(C_{nn}).
\]
Bounded tangential tilts also make \(C_{nn}\) uniformly comparable to the reference ray variance. Thus every approaching path satisfies, eventually,
\[
|\dot\eta_s|_{\mathrm F}
\ge c\,|\dot r_s|\sqrt{V_{\mathrm{ray}}(r_s)}.
\]
Divergence of the ray integral forces divergence along every path.

**Higher-codimension obstruction:** the additional normal directions are not bounded, face-tangential nuisance parameters. They can run on different scales and reorganize which layers are expensive.

**Fix:** develop flagwise sufficient criteria and intrinsic completion estimates. The square example shows why this is genuinely new geometry.

## Do not use a universal \(D\le L_{\mathrm F}^2\) bound

Such an inequality is false. Already in the Bernoulli family, Fisher distances are bounded while KL divergence between interior laws can be arbitrarily large.

Hellinger/Fisher–Rao lower bounds are valid, but by themselves cannot detect your infinite-length-ray phenomenon.

---

# 4. Response projection is not globally Fisher-contracting

Let
\[
\Pi(\rho)=q_{E_\rho S},\qquad
C_\rho=\operatorname{Cov}_\rho(S),\qquad
C_q=\operatorname{Cov}_{\Pi(\rho)}(S).
\]
For a centered data score \(a\), set
\[
b=E_\rho[(S-E_\rho S)a].
\]
Then
\[
\boxed{
\|D\Pi_\rho[a]\|_{\mathrm F}^2=b^\top C_q^{-1}b.
}
\]

Its exact squared operator norm is
\[
\boxed{
\|D\Pi_\rho\|^2
=
\lambda_{\max}\!\left(C_q^{-1/2}C_\rho C_q^{-1/2}\right).
}
\]
Consequently:
\[
\boxed{
D\Pi_\rho\text{ contracts every score}
\iff C_\rho\preceq C_q.
}
\]

At \(\rho=q\), this is precisely Fisher orthogonal projection. Away from the family, covariance domination need not hold.

## A three-point counterexample along your exponential data path

Take \(\nu\) uniform on \(S=-1,0,1\), and
\[
h(-1)=h(0)=0,\qquad h(1)=1.
\]
At \(t=\log4\),
\[
\rho_t=(1/6,1/6,2/3),\qquad m_t=1/2,
\]
and
\[
\operatorname{Cov}_{\rho_t}(S,h)=1/3,\qquad
\operatorname{Var}_{\rho_t}h=2/9.
\]

The matching response has weights proportional to \(1,x,x^2\), where
\[
x=\frac{1+\sqrt{13}}2.
\]
Its statistic variance is
\[
C_q=\frac{13-2\sqrt{13}}{12}<\frac12.
\]
Therefore
\[
\frac{(1/3)^2}{C_q}>\frac29.
\]

**The response path is strictly faster than the data path, although \(h\) is bounded.**

## What positive hypotheses work?

- **Fixed \(h\), sufficiently small \(t\): yes**, under the continuity assumptions already needed for the differential formulas. If the residual variance at zero is positive, contraction persists by continuity. If it is zero, \(h\) is affine in \(S\), modulo constants and null sets, and the entire data path lies in the family: equality holds.

- **Covariance domination \(C_{\rho_t}\preceq C_{q_t}\): yes**, exactly.

- **Density domination \(\rho_t\le Kq_t\):**
  \[
  |\dot q_t|_{\mathrm F}^2\le K\,|\dot\rho_t|_{\mathrm F}^2.
  \]

- **A KL ball alone: no exact contraction**, nor a uniform \(1+o(1)\) distortion bound near the boundary. In the same three-point example, as \(t\to\infty\),
  \[
  D(\rho_t\|q_t)\to0,
  \qquad
  \frac{|\dot q_t|_{\mathrm F}^2}{|\dot\rho_t|_{\mathrm F}^2}\to\frac32.
  \]
  On a region where \(C_q\) has a uniform positive lower eigenvalue and \(S\) is bounded, Pinsker plus covariance estimates does give approximate contraction with distortion tending to \(1\) as KL tends to zero.

Nonnegativity of \(\mathcal E\) cannot establish global speed contraction.

---

# 5. The deeper defect identities

For arbitrary admissible \(\rho\), \(M=E_\rho S\), and any interior response \(q_N\),
\[
\boxed{
D(\rho\|q_N)
=
D(\rho\|q_M)+D(q_M\|q_N).
}
\]
Hence
\[
\boxed{
\mathcal E(\rho)=\min_N D(\rho\|q_N).
}
\]
For interior \(M\), the minimum is attained at \(q_M\); boundary formulations should distinguish the original family from its completion.

This also gives the surviving one-sided contraction:
\[
D(\Pi\rho\|q_N)\le D(\rho\|q_N).
\]

Along your data path, put
\[
L_t=\log\frac{d\rho_t}{dq_t},
\qquad b_t=\operatorname{Cov}_{\rho_t}(S,h).
\]
Then
\[
\boxed{
\mathcal E'(t)=\operatorname{Cov}_{\rho_t}(h,L_t)
}
\]
and, with sufficient differentiability,
\[
\boxed{
\mathcal E''(t)
=
\operatorname{Var}_{\rho_t}h
-b_t^\top C_{q_t}^{-1}b_t
+
\operatorname{Cov}_{\rho_t}
\!\left((h-E_{\rho_t}h)^2,L_t\right).
}
\]

This is the useful beyond-second-order identity:

- the first two terms are **data speed squared minus response speed squared**;
- the last is the **off-family correction**;
- at \(t=0\), \(L_0=0\), recovering your residual-variance theorem.

There is no general convexity. In the same three-point example,
\[
\mathcal E(0)=0,\qquad \mathcal E(t)>0\ \ (0<t<\infty),
\qquad \mathcal E(t)\to0\ \ (t\to\infty),
\]
because both paths converge to the same vertex law. A nonnegative convex function starting at zero cannot behave this way.

---

## Recommended next landing

I would prioritize:

1. **`FisherPathBounds`**: scalar lower bound and coordinate upper bound.
2. **`FisherAccessCounterexample`**: the charged square above.
3. **`FacetFisherAccess`**: path-independent codimension-one classification.
4. **`ResponseProjectionDifferential`**: exact covariance distortion and the three-point counterexample.
5. **`ResponseDefectEvolution`**: global Pythagoras and the exact \(\mathcal E''\) identity.

The conceptual leap is: **your completed response atlas is not yet its intrinsic Fisher completion, and flags can change accessibility—not just describe convergence.**