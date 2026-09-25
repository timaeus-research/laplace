## Executive recommendation

The next conceptual step is to distinguish three geometries that now coexist in the development:

1. **Data geometry:** which changes in \(q\) actually change the posterior?
2. **Intrinsic response geometry:** lengths and distances within the chosen affine family.
3. **Ambient statistical geometry:** Fisher–Rao distance between distributions, allowing paths outside that family.

Your landed results already show a striking separation: a featureless-to-data ray can have divergent intrinsic length while its ambient Fisher–Rao distance tends to \(\pi\). The next programme should make that separation—and the exact map from data directions to response directions—structural.

Two cautions are important:

- A straight natural-parameter line is **not generally a Fisher geodesic in a multiparameter family**.
- The existing negative-chamber leading equivalent does **not** yet imply the proposed two-term wall law. Its error could dominate \(\log t\).

Below, line estimates mean additional mathematical Lean, assuming the interfaces described in the question are reusable; they are not repository-level estimates.

---

# 1. Ranked next targets

## 1. Data-to-posterior quotient and response stability

**Why first:** this directly addresses “map the space of responses across the data manifold”, rather than only mapping an already-chosen parameter space.

### Precise theorem

Start with finite data space \(X\), a reference distribution \(q_*\), and
\[
L_q(w)=\sum_{x\in X}q_x\ell(x,w).
\]
Fix \(t>0\). Work on a relatively open domain of the simplex on which the partition function and the first two differentiated moments are finite, with local domination sufficient for differentiation under the integral.

For tangent vectors \(h,k\), where \(\sum_x h_x=\sum_x k_x=0\), put
\[
\delta L_h(w)=\sum_xh_x\ell(x,w).
\]

Then:

\[
D_q\langle O\rangle[h]
   =-t\,\operatorname{Cov}_{t,q}(O,\delta L_h),
\]
and the pullback Fisher metric is
\[
g_q(h,k)=t^2\operatorname{Cov}_{t,q}(\delta L_h,\delta L_k).
\]

Its kernel is exactly
\[
\ker g_q
 =\{h:\delta L_h\text{ is constant }\pi\text{-a.e.}\}.
\]
In particular, the kernel is independent of \(q\), since the Gibbs density is strictly positive.

Moreover,
\[
P_{t,q}=P_{t,q'}
\quad\Longleftrightarrow\quad
L_q-L_{q'}\text{ is constant }\pi\text{-a.e.}
\]

Thus the posterior map is an immersion after quotienting data directions by this fixed, statistically invisible subspace.

A useful response consequence is
\[
\bigl|D_q\langle O\rangle[h]\bigr|
 \le \sqrt{\operatorname{Var}_{t,q}(O)}\,\sqrt{g_q(h,h)}.
\]
Along a piecewise \(C^1\) data path,
\[
|\langle O\rangle_{q_1}-\langle O\rangle_{q_0}|
\le
\int_0^1
\sqrt{\operatorname{Var}_{q(s)}(O)}\,|\dot q(s)|_g\,ds.
\]

### Lean implementation

Do **not** begin with quotient manifolds. Choose a linear complement to the kernel, express the loss contrasts in a basis there, and invoke `MeanMapChart`/`MeanMapEmbedding`. The admissible data distributions map to a convex region in this effective parameter space.

**Builds on:** `FisherInformation`, `MeanMapChart`, `MeanMapEmbedding`, covariance differentiation.

**Cost:** roughly **500–1,000 lines** for finite data and a chosen complement; substantially more for a coordinate-free quotient-manifold API.

---

## 2. Square-root immersion, distance comparison, and the correct geodesic theorem

### Precise theorem

Let
\[
p_a=Z(a)^{-1}e^{-tL_a},\qquad
L_a=L_0+\sum_i a_iR_i
\]
on an open parameter domain \(U\subseteq\mathbb R^n\). Assume local exponential-moment domination strong enough to make the square-root map \(C^1\) into \(L^2(\pi)\). For example, locally require integrability of
\[
e^{-tL_a+\varepsilon\sum_i|R_i|}
\]
for some \(\varepsilon>0\).

Define
\[
\Psi(a)=2\sqrt{p_a}\in L^2(\pi).
\]
Then
\[
\|\Psi(a)\|_2=2,
\qquad
D\Psi_a[v]=-t(R_v-\langle R_v\rangle_a)\sqrt{p_a},
\]
and
\[
\langle D\Psi_a[v],D\Psi_a[w]\rangle
 =t^2\operatorname{Cov}_a(R_v,R_w)=G_a(v,w).
\]

Thus \(\Psi\) is an isometric immersion when the family is minimal.

For every piecewise \(C^1\) path \(\gamma\),
\[
2\arccos \rho(\gamma(0),\gamma(1))
 \le \operatorname{Length}_G(\gamma).
\]

### Two-valued contrast theorem

For a nonconstant affine line \(a(s)=a_0+sv\), under enough regularity for second derivatives:

> Its square-root image is an unparametrised great-circle arc if and only if \(R_v\) takes exactly two essential values.

Consequently, in the two-valued case,
\[
\operatorname{Length}_G(a|_{[s_0,s_1]})
 =2\arccos\rho(a(s_0),a(s_1)).
\]
It is therefore length-minimising even among all admissible posterior paths, not merely within the affine family.

**Important:** this characterises ambient Fisher–Rao geodesicity, not intrinsic geodesicity in an arbitrary subfamily. The distinction is expanded in §3 below.

**Builds on:** `Affinity`, `AngularBound`, `RadialCurvature`, `FisherInformation`.

**Cost:** **800–1,600 lines** for the immersion and path inequality; another **400–900** for the two-valued characterisation. The main cost is differentiation into `Lp`, not the covariance algebra.

---

## 3. Exact affinity–KL decomposition and universal dilation geometry

This is the best low-cost, high-beauty target.

### Exact weighted theorem

For parameters \(a,b\), let \(a_\theta=(1-\theta)a+\theta b\), and define
\[
C_\theta=(1-\theta)F(a)+\theta F(b)-F(a_\theta).
\]
Assume all relevant distributions and KL divergences exist, with the log-density ratios integrable. Then for any probability \(Q\) with the required finite divergences,
\[
(1-\theta)\operatorname{KL}(Q\|P_a)
+\theta\operatorname{KL}(Q\|P_b)
=
\operatorname{KL}(Q\|P_{a_\theta})+C_\theta.
\]

At the midpoint, \(B=-\log\rho(a,b)\), this becomes
\[
\frac12\operatorname{KL}(Q\|P_a)
+\frac12\operatorname{KL}(Q\|P_b)
=
\operatorname{KL}(Q\|P_m)+B.
\]

Hence the normalized geometric mean \(P_m\) is the unique minimizer, and
\[
B=\inf_Q\frac{\operatorname{KL}(Q\|P_a)+\operatorname{KL}(Q\|P_b)}2.
\]

Taking \(Q=P_a\) gives the deeper exact version of the proposed inequality:
\[
\boxed{\frac12\operatorname{KL}(P_a\|P_b)-B
       =\operatorname{KL}(P_a\|P_m).}
\]
There is an analogous identity with \(a,b\) reversed.

### Regular-variation corollary

Suppose \(Z\) is regularly varying with index \(-\lambda\), \(\lambda>0\), and use the associated first-moment asymptotic \(u\langle L\rangle_u\to\lambda\). For fixed \(c,d>0\),
\[
\operatorname{KL}(P_{cu}\|P_{du})
 \longrightarrow
 \lambda\left(\frac dc-1-\log\frac dc\right),
\]
and
\[
-\log\rho(cu,du)
 \longrightarrow
 \lambda\log\frac{c+d}{2\sqrt{cd}}.
\]
Your variance theorem also yields
\[
\int_{cu}^{du}\sqrt{\operatorname{Var}_v(L)}\,dv
 \longrightarrow \sqrt{\lambda}\,|\log(d/c)|.
\]

This is an exact asymptotic geometry in **log-temperature coordinates**: length, affinity and directed KL all have universal limits depending only on \(\lambda\).

One especially attractive endpoint identity is
\[
\frac12\operatorname{KL}(P_u\|P_0)
+\log\rho(0,u)
\longrightarrow
\lambda\left(\log2-\frac12\right),
\]
provided \(P_0\) exists and the displayed KL is finite.

**Builds on:** `InformationProjection`, `Affinity`, `TauberianVariance`, `FeaturelessLawFromPartition`.

**Cost:** **250–600 lines** for the exact decomposition; **250–500** for dilation limits, depending on the first-moment API.

---

## 4. All integer multiplicities, through a reusable normalized-moment expansion

### Precise theorem

For every \(k\in\mathbb N\), let the loss state measure on \((0,1)\) be
\[
(-\log\ell)^k\,d\ell.
\]
Let \(V_k(u)\) be the posterior loss variance. Then there exist \(U,C>0\) such that
\[
\left|u^2V_k(u)-\left(1-\frac{k}{\log u}\right)\right|
 \le \frac{C}{(\log u)^2},
 \qquad u\ge U.
\]
Therefore, for any fixed starting point at which the finite initial length is defined,
\[
\int_{u_0}^t\sqrt{V_k(u)}\,du
=
\log t-\frac{k}{2}\log\log t+K_{k,u_0}+o(1).
\]

The coefficient is indeed \(k\), and the Euler–Mascheroni contribution cancels. A complete proof architecture appears in §2.

**Builds on:** `MultiplicityModel`, `LogGammaTails`, `RenormalisedLength`.

**Cost:** **400–850 lines** if done through finite sums and three normalized-moment expansions.

I would land this before attempting the stronger wall expansion: it is bounded, reusable, and removes a conspicuous restriction.

---

## 5. Global wall chart and a genuinely two-term wall law

These should be separate deliverables: the chart is cheap; the second-order law is not.

### Global chart

For \(p>q>0\), set
\[
\nu_s(dy)\propto e^{-y^p-sy^q}\,dy,\qquad y>0,
\quad
m(s)=\mathbb E_{\nu_s}[y^q].
\]
Then
\[
m'(s)=-\operatorname{Var}_{\nu_s}(y^q)<0.
\]
Using the positive- and negative-chamber moment limits,
\[
m(+\infty)=0,\qquad m(-\infty)=+\infty.
\]
Therefore
\[
m:\mathbb R\longrightarrow(0,\infty)
\]
is a decreasing homeomorphism, and a \(C^1\) diffeomorphism once the derivative API is in place.

Strict positivity of the variance needs to be proved, not inferred from continuity: it follows because \(y^q\) is nonconstant under a strictly positive density.

**Cost:** **150–400 lines**, assuming the endpoint mean asymptotics are readily available.

### Strengthened wall law

Write
\[
\sigma=1-\frac qp,\qquad T=t^\sigma,\qquad
h(s)=\sqrt{\operatorname{Var}_{\nu_s}(y^q)}.
\]
The physical length satisfies
\[
\ell_t(a,b)=\int_{aT}^{bT}h(s)\,ds.
\]

A sufficient sharpened asymptotic package is
\[
h(-b)=L_{p,q}b^{\beta-1}+O(b^{-\beta-1}),
\]
and
\[
h(s)=\frac1{\sqrt q\,s}+O(s^{-1-\delta})
\quad(s\to+\infty)
\]
for some \(\delta>0\). In this model one expects \(\delta=p/q\).

These imply the stronger conclusion
\[
\boxed{
\ell_t(-A,a_1)
=
K_-(A)\sqrt t+\frac{\sigma}{\sqrt q}\log t+C_{A,a_1}+o(1)
}
\]
for \(A,a_1>0\).

**What is missing:** your present negative-chamber result only gives
\[
h(-b)=L_{p,q}b^{\beta-1}(1+o(1)).
\]
Its integrated error is merely \(o(\sqrt t)\), not \(o(\log t)\).

A clean route is a quantitative Laplace expansion proving
\[
\operatorname{Var}\!\left(\sqrt B(z^q-1)\right)
=\frac{q^2}{p(p-q)}+O(B^{-1}).
\]
The order-\(B^{-1/2}\) contribution to the second moment cancels by parity; the mean is \(O(B^{-1/2})\), so its square is \(O(B^{-1})\). This is precisely the useful quantitative refinement.

**Cost:** **1,200–2,500 lines** beyond the present half-line Laplace infrastructure.

### Correct phase diagram

For fixed \(a<b\), the leading regimes are:

| Endpoints | Leading length |
|---|---|
| \(a<b<0\) | \([K_-(-a)-K_-(-b)]\sqrt t\) |
| \(a< b=0\) | \(K_-(-a)\sqrt t\) |
| \(a<0<b\) | \(K_-(-a)\sqrt t+(\sigma/\sqrt q)\log t\) |
| \(a=0<b\) | \((\sigma/\sqrt q)\log t\) |
| \(0<a<b\) | \(\frac1{\sqrt q}\log(b/a)\), a finite limit |

Thus “the rate jumps from \(\log t\) to \(\sqrt t\)” is correct for paths anchored at the wall, but not for arbitrary positive-chamber endpoint pairs.

---

## 6. Interior-minimum geometry: explain the \(\sqrt t\) law

This is the deepest explanatory target, but I would keep its first version one-dimensional.

### Precise local theorem

Let
\[
L_a(x)=V(x)+a f(x)
\]
on an interval, with a smooth positive prior density \(r\). On a compact parameter interval \(J\), assume:

- a unique interior global minimizer \(x_a\);
- \(H_a=\partial_x^2L_a(x_a)>0\), uniformly bounded away from zero;
- sufficiently smooth dependence and uniformly controlled local Taylor remainders;
- a uniform positive energy gap away from a neighborhood of \(x_a\), plus integrable coercive tails.

Then
\[
t\,\operatorname{Var}_{t,a}(f)
\longrightarrow \frac{f'(x_a)^2}{H_a}
\]
uniformly on \(J\), and hence
\[
\frac{\ell_t(a_0,a_1)}{\sqrt t}
\longrightarrow
\int_{a_0}^{a_1}\frac{|f'(x_a)|}{\sqrt{H_a}}\,da.
\]
Differentiating the minimizer equation gives
\[
x_a'=-\frac{f'(x_a)}{H_a},
\]
so the limiting length is
\[
\boxed{\int_{a_0}^{a_1}\sqrt{H_a}\,|x_a'|\,da.}
\]

This says: the \(\sqrt t\) law measures motion of the posterior centre in units of its shrinking Gaussian width.

### State-density interpretation

After subtracting the minimum \(M_a=L_a(x_a)\), the local energy state density is
\[
d\mu_a(\varepsilon)
\sim
\frac{\sqrt2\,r(x_a)}{\sqrt{H_a}}\,
\varepsilon^{-1/2}\,d\varepsilon.
\]

It is **not a Gaussian peak in energy space**. The Gaussian appears in configuration space after rescaling \(x-x_a\); the energy density has a square-root singularity.

Accordingly, fixed-\(a\) cooling still has radial coefficient \(1/\sqrt2\):
\[
\operatorname{Var}_{t,a}(L_a)\sim\frac1{2t^2}.
\]
The \(\sqrt t\) wall length concerns variation of \(a\), which moves the minimizer. These are different directions.

For the two-monomial model,
\[
H_a=p(p-q)x_a^{p-2},
\]
and the limiting length from \(-A\) to the wall is
\[
\int_0^{x_{-A}}\sqrt{p(p-q)x^{p-2}}\,dx
=
2\sqrt{\frac{p-q}{p}}
\left(\frac{qA}{p}\right)^\beta
=K_-(A).
\]

The abstract theorem applies away from the wall; the existing wall machinery supplies the nonuniform endpoint passage.

**Builds on:** `HalfLineLaplace`, `NegativeChamber`, `StateDensity`.

**Cost:** **900–1,800 lines** for a reusable one-dimensional theorem; multivariate uniform Laplace theory is a separate, larger project.

---

# 2. General integer \(k\): the clean complete route

Use **finite binomial sums**, not differentiation in the exponent. The generating-function route introduces parameter differentiation, incomplete-Gamma regularity, and derivative interchange that the desired conclusion does not need.

## Step 1: Full log-Gamma moments and tails

For \(j\in\{0,1,2\}\), \(r\le k\), define
\[
M_{j,r}=\int_0^\infty s^j(\log s)^r e^{-s}\,ds,
\qquad
\Lambda_{j,r}(u)=\int_0^u s^j(\log s)^r e^{-s}\,ds.
\]

Prove absolute integrability, including at zero, and the convenient tail bound
\[
|M_{j,r}-\Lambda_{j,r}(u)|\le C_{j,r}u^{-2}
\quad(u\ge1).
\]

This need not be sharp. Exponential domination makes the tail estimate straightforward once the polynomial-log envelope is packaged.

Only the following full moments need explicit evaluation:
\[
M_{0,0}=M_{1,0}=1,\qquad M_{2,0}=2.
\]
Write
\[
c=M_{0,1}.
\]
Integration by parts gives
\[
M_{j+1,1}=(j+1)M_{j,1}+j!,
\]
hence
\[
M_{1,1}=c+1,\qquad M_{2,1}=2c+3.
\]

**Do not identify \(c=-\gamma\).** That identification contributes nothing to this proof.

Higher log moments require only finiteness.

## Step 2: Exact binomial formula

Let
\[
N_{j,k}(u)=\int_0^1
\ell^j(-\log\ell)^k e^{-u\ell}\,d\ell,
\qquad x=\log u.
\]
Changing variables \(s=u\ell\),
\[
u^{j+1}N_{j,k}(u)
=
\sum_{r=0}^k
(-1)^r\binom kr x^{k-r}\Lambda_{j,r}(u).
\]

For \(u>1\), define the normalized quantities
\[
A_j(u)=\frac{u^{j+1}N_{j,k}(u)}{(\log u)^k}.
\]

Now prove one generic finite-sum lemma yielding
\[
A_j(u)
=j!-\frac{kM_{j,1}}x+O(x^{-2}).
\]

The remainder has two parts:

1. \(r\ge2\): use \(x^{-r}\le x^{-2}\) for \(x\ge1\);
2. truncated/full moment replacement: use the tail bound, then \(u^{-2}=O(x^{-2})\).

Handle \(k=0\) either separately or by a small lemma that makes the absent linear term explicit. A separate \(k=0\) branch is likely simplest in Lean.

## Step 3: Three first-order expansions

You obtain
\[
A_0=1-\frac{kc}{x}+O(x^{-2}),
\]
\[
A_1=1-\frac{k(c+1)}x+O(x^{-2}),
\]
\[
A_2=2-\frac{k(2c+3)}x+O(x^{-2}).
\]

Choose an eventual threshold with \(A_0\ge1/2\). Then elementary quotient algebra gives
\[
\frac{A_1}{A_0}=1-\frac{k}{x}+O(x^{-2}),
\]
\[
\frac{A_2}{A_0}=2-\frac{3k}{x}+O(x^{-2}).
\]

Since
\[
u^2V_k(u)
=\frac{A_2}{A_0}
-\left(\frac{A_1}{A_0}\right)^2,
\]
the conclusion is
\[
\boxed{
u^2V_k(u)=1-\frac{k}{\log u}
+O((\log u)^{-2}).
}
\]

This explicitly exhibits the cancellation of \(c\).

### Suggested Lean interface

Make the central exported theorem an eventual inequality, matching the existing renormalization lemma:

```text
∃ C > 0, ∃ U > 1, ∀ u ≥ U,
  |u^2 * variance k u - (1 - (k : ℝ) / log u)|
    ≤ C / (log u)^2
```

Internally, either `IsBigO` or eventual inequalities are reasonable. Avoid forcing the final consumer to unpack several asymptotic algebra statements.

A reusable lemma for
\[
\frac{a_0+a_1/x+O(x^{-2})}
     {b_0+b_1/x+O(x^{-2})}
\]
with \(b_0\ne0\) would pay for itself here.

## Step 4: Feed renormalized length

Eventually \(u^2V_k(u)\) lies in a compact neighborhood of \(1\). The square-root estimate yields
\[
\sqrt{V_k(u)}
=
\frac1u-\frac{k}{2u\log u}
+O\!\left(\frac1{u(\log u)^2}\right).
\]

The remainder is integrable at infinity:
\[
\int_U^\infty\frac{du}{u(\log u)^2}
=\frac1{\log U}.
\]

Thus the existing `tendsto_renormalised_length` applies directly. Any initial segment below \(U>1\) is absorbed into the constant \(K\).

**Scope warning:** this is not a consequence of regular variation alone. Here the explicit state density supplies the second-order control needed to produce a finite renormalized constant.

---

# 3. What is true about lengths, distances, and geodesics?

## 3.1 The general hierarchy

For an affine family \(M\), define its intrinsic length distance \(d_M\). Then
\[
\boxed{
d_{\mathrm{FR}}(P_a,P_b)
\le d_M(a,b)
\le \operatorname{Length}_G(\gamma)
}
\]
for every family path \(\gamma\) joining \(a\) to \(b\), with
\[
d_{\mathrm{FR}}(P_a,P_b)=2\arccos\rho(a,b).
\]

The first distance permits paths through other distributions. The second only permits paths inside the specified family.

For strictly positive densities, the ambient minimizing arc is the positive great-circle arc in square-root coordinates. It need not belong to the affine family.

This is the right unifying theorem for the landed work.

## 3.2 A natural straight line is not generally intrinsically geodesic

Assume a minimal \(C^3\) family. Since
\[
g_{ij}=t^2\operatorname{Cov}(R_i,R_j),
\]
its metric derivatives satisfy
\[
\partial_k g_{ij}
=-t^3\kappa(R_i,R_j,R_k),
\]
where \(\kappa\) is the third joint cumulant.

For a natural-coordinate straight line with direction \(v\),
\[
g(\nabla_vv,w)
=-\frac{t^3}{2}\kappa(R_v,R_v,R_w).
\]

Therefore:

- The natural parameter itself is an affine geodesic parameter exactly when
  \[
  \kappa(R_v,R_v,R_w)=0
  \quad\text{for every }w.
  \]
- The line is an **unparametrised intrinsic geodesic** exactly when, at every point on it, there is a scalar \(c\) such that
  \[
  \kappa(R_v,R_v,R_w)
  =c\,\operatorname{Cov}(R_v,R_w)
  \quad\text{for every }w.
  \]

Even an intrinsic geodesic is only automatically locally minimizing; global minimization requires further structure.

A simple counterexample to general straight-line geodesicity is the full three-state categorical family and
\[
P_u\propto(1,e^{-u},e^{-2u}).
\]
Its contrast takes three values. The family contains the ambient great-circle shortcut, while this natural line is not that great circle.

## 3.3 What the two-valued theorem actually characterises

Along the natural line, write \(X=R_v-\mathbb E[R_v]\). The sphere-covariant acceleration of \(\Psi\) is
\[
\frac{t^2}{4}\bigl(X^2-\operatorname{Var}(R_v)\bigr)\Psi.
\]

For an unparametrised great circle this must be proportional to
\[
\Psi'=-\frac t2X\Psi.
\]
Thus \(X\) satisfies a quadratic equation almost everywhere and has at most two essential values.

This condition is stronger than the intrinsic cumulant condition: intrinsic geodesicity only tests the acceleration against tangent directions to the family.

In a one-dimensional family, the intrinsic condition is automatic. The ambient condition is not.

## 3.4 What is true for the featureless line

Suppose \(u\mapsto P_u\) is injective and has positive continuous variance.

Within that one-dimensional family, every absolutely continuous path joining \(P_s\) to \(P_t\) has length at least
\[
\int_s^t\sqrt{\operatorname{Var}_u(L)}\,du.
\]
Equality holds for monotone traversals. Arc-length reparametrization makes the ray intrinsically geodesic.

But embedding the same ray into a larger affine family can introduce shorter paths.

Under regular variation with \(\lambda>0\), your results therefore support the precise statement
\[
d_{\text{ray}}(P_{u_0},P_t)\sim\sqrt\lambda\log t,
\qquad
d_{\mathrm{FR}}(P_0,P_t)\longrightarrow\pi.
\]

There is no contradiction: **the ray is intrinsically infinite but lies in an ambient statistical region of bounded angular diameter.**

That is the geometric synthesis I would make explicit in the project narrative. It also explains why the data-quotient theorem comes first: before asking which featureless-to-data path is optimal, one must specify which posterior paths the data manifold actually permits.