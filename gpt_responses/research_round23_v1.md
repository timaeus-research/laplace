## Executive verdict

- **A is correct**, including the constant
  \[
  \frac{\sigma_*}{\sqrt q},\qquad \sigma_*=1-\frac qp.
  \]
  In this model you can prove **a convergent renormalized length**, stronger than the proposed \(O(1)\).
- The generalization needs **the response-active exponent**, not necessarily the RLCT of the entire dominant-side model.
- The shape-metric factor \(1/2\), the Gaussian formula, and the mean-map nondegeneracy condition are correct. One important qualification: **\(D_vH=\nabla^2R_v\) is not generally true when the minimizer moves**; it is true in your stationary-direction setting.
- My next-target order is **A, E, D, C, B**, with a small “active versus spectator directions” example accompanying A.

These are mathematical audits of the stated results and hypotheses, rather than an inspection of the Lean declarations.

---

## 1. The two-monomial wall: constants and matching

Put
\[
\alpha=\frac1q,\qquad r=\frac pq>1,\qquad
\sigma_*=1-\frac qp.
\]

### Fixed positive \(a\): the Gamma limit

Under
\[
e^{-t(w^p+aw^q)}\,dw,\qquad w>0,
\]
set \(X=ta\,w^q\). Its density is proportional to
\[
x^{\alpha-1}e^{-x-\varepsilon x^r},\qquad
\varepsilon=a^{-r}t^{1-r}.
\]

Thus \(X\) converges, with all fixed nonnegative moments, to
\(\mathrm{Gamma}(\alpha,\text{rate }1)\). In particular,
\[
g_t(a)=t^2\operatorname{Var}(w^q)
      =\frac1{a^2}\operatorname{Var}(X)
      \longrightarrow\frac{\alpha}{a^2}.
\]

The useful strengthening is
\[
\operatorname{Var}(X)=\alpha+O(\varepsilon).
\]
For the relevant moment integrals this follows directly from
\[
0\le 1-e^{-\varepsilon x^r}\le \varepsilon x^r
\]
and Gamma-moment integrability.

Consequently, convergence is uniform on every fixed compact interval
\(0<a_0\le a\le a_1\), giving
\[
\ell_t(a_0,a_1)\longrightarrow
\frac1{\sqrt q}\log\frac{a_1}{a_0}.
\]

### Exact matching through the profile

Let \(Y\) have profile density proportional to
\[
e^{-y^p-cy^q}\,dy,
\]
and write
\[
V(c)=\operatorname{Var}_c(Y^q),\qquad h(c)=\sqrt{V(c)}.
\]
Your exact window identity gives
\[
\ell_t(c_0t^{-\sigma_*},a_1)
=\int_{c_0}^{a_1t^{\sigma_*}}h(c)\,dc.
\]

Now set \(X=cY^q\). The same Gamma calculation has perturbation
\(\varepsilon=c^{-r}\), so
\[
V(c)=\frac{\alpha}{c^2}+O(c^{-2-r}),
\qquad
h(c)=\frac{\sqrt\alpha}{c}+O(c^{-1-r}).
\]

This is exactly the integrable tail error needed for matching. Define
\[
C(c_0)=\lim_{C\to\infty}
\left(\int_{c_0}^{C}h(c)\,dc-\sqrt\alpha\log C\right).
\]
The limit exists, and
\[
\boxed{
\ell_t(c_0t^{-\sigma_*},a_1)
=
\frac{\sigma_*}{\sqrt q}\log t
+\frac1{\sqrt q}\log a_1
+C(c_0)
+O\!\left(t^{-(p/q-1)}\right).
}
\]
Here \(a_1>0\) and \(c_0>0\) are fixed. The same conclusion holds for \(c_0=0\), using continuity of the profile metric near zero.

**Recommendation:** prove the integrable-tail statement and renormalized-limit theorem. Merely proving pointwise convergence at fixed \(a\) would not justify the moving-endpoint claim.

---

## 2. The clean general theorem—and its limits

The most reusable statement is geometric and profile-based.

### Profile-tail wall theorem

Suppose an exact or sufficiently accurate scaling identifies
\[
\ell_t(c_0t^{-\sigma},a_1)
=\int_{c_0}^{a_1t^\sigma}h(c)\,dc,
\]
and, for some \(\kappa>0\),
\[
h(c)-\frac{\sqrt\kappa}{c}\in L^1([1,\infty)).
\]
Then
\[
\ell_t(c_0t^{-\sigma},a_1)
=\sigma\sqrt\kappa\,\log t+O(1),
\]
indeed with a renormalized limit.

A weaker assumption \(ch(c)\to\sqrt\kappa\) gives only
\[
\frac{\ell_t}{\log t}\to\sigma\sqrt\kappa.
\]

That distinction matters for general singular models.

### Why “RLCT of the dominant side” needs qualification

Consider
\[
L_a(x,y)=x^2+y^4+ay^2
\]
with Lebesgue prior on \(\mathbb R^2\). Here
\[
\sigma_*=\frac12.
\]
For fixed \(a>0\), the full model has RLCT \(1\), but
\[
t^2\operatorname{Var}(y^2)\longrightarrow\frac1{2a^2}.
\]
Therefore the wall-distance coefficient is
\[
\frac1{2\sqrt2},
\]
not \(1/2\).

The \(x\)-mode contributes to the full RLCT but is a **spectator for this response**.

The right general quantity is
\[
\boxed{\kappa_{\rm resp}
=\lim_{c\to\infty}c^2\operatorname{Var}_c(R),}
\]
when the profile parameter couples linearly to \(R\). Under appropriate differentiated asymptotics, it is the exponent in
\[
Z_{\rm profile}(c)\sim Cc^{-\kappa_{\rm resp}}.
\]

In your one-dimensional model, \(\kappa_{\rm resp}=1/q\), so the distinction disappears.

### Logarithmic multiplicities can spoil the \(O(1)\)

If
\[
Z_{\rm profile}(c)\sim Cc^{-\kappa}(\log c)^k
\]
with sufficiently controlled derivatives, then
\[
h(c)=\frac{\sqrt\kappa}{c}
-\frac{k}{2\sqrt\kappa\,c\log c}
+\text{integrable remainder}.
\]
Hence the length includes
\[
-\frac{k}{2\sqrt\kappa}\log\log t.
\]

So the broadly robust conjecture is the **leading logarithmic coefficient**. Bounded renormalized remainder needs stronger tail information, such as absence of these logarithmic corrections.

---

## 3. What is the exponent gap?

For a weighted-homogeneous wall model, normalize the wall potential to weighted degree \(1\). If the perturbing observable \(R\) has weighted degree \(\rho\), then
\[
\boxed{\sigma_*=1-\rho.}
\]

Indeed, under the wall scaling,
\[
tL_0\rightsquigarrow L_0,\qquad
taR\rightsquigarrow at^{1-\rho}R.
\]
Thus the crossover variable is \(c=at^{\sigma_*}\).

For \(L_0=w^p,\ R=w^q\), the wall weight is \(1/p\), so \(\rho=q/p\).

In valuation language, if the selected wall valuation is \(\beta\) and the perturbation is the monomial \(w^\nu\), then
\[
\sigma_*=1-\langle\beta,\nu\rangle.
\]
With several active valuations or competing monomials, there can be multiple crossover slopes rather than one gap.

### Relation to the valuation LP

This is **not a codimension**, even a disguised integer codimension. It is a weighted-degree deficit or crossover exponent.

There is, however, a useful LP consistency relation. Suppose
\[
Z(t,a)=t^{-\lambda_{\rm wall}}\mathcal Z(at^\sigma),
\qquad
\mathcal Z(c)\sim Cc^{-\kappa}.
\]
Then
\[
\lambda_+=\lambda_{\rm wall}+\sigma\kappa.
\]
Along \(a=t^{-\gamma}\), in that chamber,
\[
\lambda(\gamma)=\lambda_+-\kappa\gamma.
\]

Thus:

- \(\sigma\) is the chamber width in logarithmic coupling coordinates;
- \(\kappa\) is the magnitude of the exponent slope;
- the distance coefficient is
  \[
  \sigma\sqrt\kappa
  =\sqrt{\sigma(\lambda_+-\lambda_{\rm wall})}.
  \]

This is a promising bridge to `coupledExponent`. But the LP determines exponents, not automatically the differentiated moment estimates needed for the metric.

The invariant geometric formulation is: **logarithmic scale separation multiplied by the limiting norm of the coupling-dilation vector \(a\partial_a\)**. That survives reparameterization; \(\sigma\) alone is tied to the chosen affine coupling coordinate.

### Comparison with the featureless law

The analogy is real:
\[
\text{length}\sim
\text{available logarithmic scale range}
\times
\text{limiting dilation speed}.
\]

But “partially featureless” should be explanatory language, not a theorem hypothesis. At the wall, one coupling vanishes while other terms still confine the posterior. Only the modes activated by that coupling contribute to the response speed.

---

## 4. Audit of the shape metric

### Stationary-direction shape limit

Yes:
\[
\boxed{
\frac12\operatorname{tr}(A_v\Sigma A_u\Sigma)
}
\]
is the correct bilinear shape metric.

Locally, when the linear terms vanish,
\[
R_v(m+z)=R_v(m)+\frac12z^\top A_vz+\cdots.
\]
For a centered Gaussian with covariance \(\Sigma/t\),
\[
\operatorname{Cov}\!\left(
\tfrac12z^\top A_vz,\tfrac12z^\top A_uz
\right)
=
\frac1{2t^2}\operatorname{tr}(A_v\Sigma A_u\Sigma).
\]
Multiplication by \(t^2\) gives your limit. The stated \(O(1/t)\) rate is consistent with the higher-order Laplace expansion; its proof depends on the precise remainder and localization content of your hypotheses.

### Important qualification about \(D_vH\)

For
\[
H(a)=\nabla_w^2L_a(m(a)),
\]
the total derivative is generally
\[
D_vH
=
\nabla^2R_v(m)
+
\nabla^3L_a(m)[Dm[v],\,\cdot,\,\cdot].
\]

Affineness in \(a\) does **not** eliminate the second term.

In your shape setting, however,
\[
\nabla R_v(m)=0
\quad\Longrightarrow\quad
Dm[v]=-H^{-1}\nabla R_v(m)=0,
\]
so \(D_vH=A_v\). Therefore your formula agrees with
\[
\frac12\operatorname{tr}(H^{-1}D_uH\,H^{-1}D_vH)
\]
for the stationary directions under discussion.

### Exact Gaussian audit

For \(H>0\) and symmetric \(B\),
\[
\boxed{
t^2\operatorname{Var}\!\left(\tfrac12w^\top Bw\right)
=\frac12\operatorname{tr}(BH^{-1}BH^{-1}).
}
\]
The sign and factor are correct.

Indeed, the covariance Fisher metric is
\[
g_C(U,V)=\frac12\operatorname{tr}(C^{-1}UC^{-1}V).
\]
With \(C=(tH)^{-1}\), its pullback to precision perturbations \(B_v,B_u\) is exactly your formula. Although \(BH^{-1}\) need not be symmetric, the diagonal expression is nonnegative by conjugating to \(H^{-1/2}BH^{-1/2}\).

---

## 5. Audit of mean-map injectivity

Your condition is precisely the right minimality condition:
\[
v\ne0\implies R_v\text{ is not prior-a.s. constant}.
\]

For \(t>0\), finite losses, and finite positive partition function, the Gibbs measure and the prior support have the same null sets. Therefore
\[
\ker(\operatorname{responseForm}_a)
=\{v:R_v\text{ is prior-a.s. constant}\},
\]
independently of \(a\).

Two qualifications worth keeping explicit:

1. For a general parameter domain, the segment argument requires a convex domain, or at least admissibility of the joining segment.
2. “Constant” is essential: excluding only a.s.-zero contrasts would miss normalization-invisible directions.

A natural companion theorem is the **quotient version**: divide parameter space by this constant-contrast subspace. The response becomes positive definite and the mean map becomes injective on the quotient.

---

## 6. E: the potential–entropy identity

This is worth formalizing, but fix the dual convention and account for \(L_0\).

Let
\[
F_t(a)=-\frac1t\log\int e^{-t(L_0+a\cdot R)}\,d\mu.
\]
Then \(F_t\) is concave and
\[
\nabla F_t(a)=m(a).
\]

Define
\[
J_t(m)=
\inf_{\nu:\,\mathbb E_\nu R=m}
\left[
\mathbb E_\nu L_0+\frac1tD(\nu\Vert\mu)
\right].
\]
The variational principle gives
\[
F_t(a)=\inf_m\bigl(J_t(m)+a\cdot m\bigr).
\]

For a realized mean \(m=m(a)\),
\[
\boxed{
J_t(m)=\sup_b\bigl(F_t(b)-b\cdot m\bigr)
=F_t(a)-a\cdot m
=\mathbb E_aL_0+\frac1tD(P_a\Vert\mu).
}
\]

Thus your proposed “negative relative entropy divided by \(t\)” identity is correct **when \(L_0=0\)**, with relative entropy understood as \(S_\mu=-D\), and with this specified dual convention.

For nonzero \(L_0\), either retain its expected energy or absorb it into the reference Gibbs measure. With normalized reference \(P_{t,0}\),
\[
J_t(m)-F_t(0)=\frac1tD(P_{t,a}\Vert P_{t,0})
\]
at realized means.

I would first formalize this **on the mean-map image**. Extending to all feasible means introduces closure and boundary-attainment questions that are unnecessary for the initial payoff.

---

## 7. Ranking and suggested bundle

| Rank | Target | Why |
|---|---|---|
| **1** | **A: receding wall, with renormalized limit** | A new geometric law, exact scaling already landed, short Gamma-tail proof |
| **2** | **E: constrained entropy duality** | Gives the map a global potential and a variational meaning; leverages landed uniqueness |
| **3** | **D: mean-map diffeomorphism onto its image** | Turns response coordinates into genuine coordinates; combines minimality, differentiation, and IFT |
| **4** | **C: uniform compact-family Laplace theory** | Major infrastructure for metric and length convergence, but probably the largest proof cost |
| **5** | **B: proper-prior neutral-line instance** | Valuable validation and removal of an idealization, but less new geometry than the above |

For D, once differentiability is available,
\[
Dm(a)[v]=-t\,\operatorname{Cov}_a(R,R_v)
=-\frac1tG_a v.
\]
Positive definiteness gives a local diffeomorphism; global injectivity gives a diffeomorphism onto the open image. For \(C^k\) or smooth conclusions, retain the corresponding higher regularity hypotheses.

### Essential addition for “a map of responses”

I would add **KL as the Bregman divergence of the log-partition potential**:
\[
\boxed{
D(P_a\Vert P_b)
=
A(b)-A(a)-DA(a)[b-a],
\qquad A=\log Z.
}
\]
Its local quadratic term is the response metric. Together with E and D, this connects:

- affine parameters;
- mean/response coordinates;
- local Fisher geometry;
- global posterior distinguishability;
- constrained entropy.

**Recommended next bundle:** the abstract profile-tail length lemma, the two-monomial renormalized wall theorem, the spectator-mode example, and the realized-mean entropy/KL identities. This would sharpen both the asymptotic geometry and the organizing meaning of the response map.