**The next flagship should be a measure-valued response theorem:** prove the density Peano expansion in integrated absolute value, and use it to make the response calculus simultaneous over all bounded observables. That is more than another Taylor theorem: it says that you have reconstructed the response of the *law*, not merely of each test function.

There is also a particularly clean scalar companion: the remaining fibre information along the atlas is exactly a weighted integral of Fisher speed. It helps clarify what finite rate does—and does not—give at the boundary.

## 1. Sanity checks

### (a) Geodesicity: correct for the stated parametrisation

In the radius-two square-root embedding,
\[
r_s'=\frac{r_s}{2}\ell_s,
\qquad
(r_s'')^{\mathrm{tan}}=-\frac{r_s}{4}B_{M_s}(\ell_s^2).
\]
Consequently the mixture-affine atlas is an **affinely parametrised Levi–Civita geodesic of the family** iff
\[
B_{M_s}(\ell_s^2)=0
\]
throughout the interval.

Two distinctions are worth making explicit:

* This is geodesicity **within the family**, not within the ambient sphere. The family-normal term can remain nonzero.
* “Not a geodesic even after reparametrisation” is stronger and does not follow. An unparametrised geodesic only requires tangential acceleration proportional to velocity; here that means \(B(\ell_s^2)\) is proportional to \(\ell_s\).

In particular, in a one-dimensional family every regular curve is locally a reparametrised geodesic, although its mean parameter need not be affine arclength.

### (b) Connections: signs and factors are correct

Write
\[
A_M(u,w):=\operatorname{Cov}_{Q}(S,\ell_u\ell_w)\in\mathbb V.
\]
With \(R=-\Sigma^{-1}\),
\[
\ell_u=\langle\Sigma^{-1}u,S-M\rangle,
\]
so
\[
G(A_M(u,w),v)=C(u,w,v).
\]
Since \(DG[v](u,w)=-C(u,v,w)\), the coordinate Koszul formula gives
\[
2G(\Gamma^{LC}(u,w),v)=-C(u,w,v).
\]
Thus
\[
\boxed{\Gamma^{LC}(u,w)=-\tfrac12 A_M(u,w).}
\]

For the dual connections induced on the exponential family,
\[
\boxed{\Gamma^{(m)}=0,\qquad
\Gamma^{(e)}(u,w)=-A_M(u,w).}
\]
Here covariance and inversion are understood intrinsically on \(\mathbb V\), as in the seabed.

A useful compatibility check is
\[
\ell_{A_M(u,w)}=B_M(\ell_u\ell_w).
\]
The square-root lift of \(\Gamma^{LC}(\Delta,\Delta)\) is therefore precisely
\[
\frac r2\ell_{\Gamma^{LC}(\Delta,\Delta)}
=-\frac r4 B_M(\ell_\Delta^2).
\]

### (c) “Only the normal part responds at second order”: correct with the qualifications

Self-adjointness of the orthogonal projection gives
\[
D^2F_\phi(M)[u,w]
=\mathbb E_Q[\phi N_M(\ell_u\ell_w)]
=\mathbb E_Q[(N_M\phi)\ell_u\ell_w].
\]

The important qualifications are:

1. **This is the ordinary Hessian in mixture-affine response coordinates**, with fixed observable \(\phi\) and fixed coordinate directions. It is not the Levi–Civita Hessian, nor the second derivative along an arbitrary accelerated path.
2. **Normality is taken at the base law \(Q\).** The formula does not say that the first-order response vanishes, that \(N_M\phi\) stays fixed along the atlas, or that the observable responds only at second order.

Constants and affine functions of \(S\) have identically zero second response. Conversely, \(N_M\phi\neq0\) need not produce a nonzero Hessian: it may be orthogonal to every \(N_M(\ell_u\ell_w)\).

## 2. What to land next

### First: the response of the law, in total variation

Prove
\[
\boxed{
\int\left|
q_{M+z}-q_M-q_M\ell_z-\frac12q_MN_M(\ell_z^2)
\right|\,d\nu=o(\|z\|^2).
}
\]

Equivalently,
\[
\sup_{\|g\|_\infty\le1}
\left|
\mathbb E_{\Pi(M+z)}g-\mathbb E_Qg
-\mathbb E_Q[g\ell_z]
-\frac12\mathbb E_Q[gN_M(\ell_z^2)]
\right|
=o(\|z\|^2).
\]

This equivalence uses the total-variation **norm of a signed measure**, without the factor \(1/2\) used in the probability-distance convention.

Its conceptual payoff is substantial:

> The score is the first derivative of the reconstructed law; the normalised quadratic score is its second derivative. Every bounded-observable response is obtained by pairing with these same two signed measures.

That is the right culmination of the programme.

### Second: compact-uniform density remainders

Do this at the density level rather than separately for \(H_{M,\phi}\). For every compact \(C\subset\operatorname{ri}K\),
\[
\sup_{\substack{M\in C\\0<\|z\|\le\delta}}
\frac{1}{\|z\|^2}
\int\left|
q_{M+z}-q_M-q_M\ell_{M,z}
-\frac12q_MN_M(\ell_{M,z}^2)
\right|d\nu
\longrightarrow0.
\]
Take \(\delta\) sufficiently small that all the indicated perturbations remain interior.

This simultaneously supplies compact-uniform response Taylor theorems for the entire unit ball of bounded observables.

### Third: the information companion

Fix a data law \(D\) with mean \(M_1=m_0+\Delta\), and set
\[
L_D(s):=\operatorname{KL}(D\Vert Q_s).
\]
Assuming finite \(\operatorname{KL}(D\Vert\nu)\), differentiation of the explicit log-density—not differentiation of \(D\)—gives
\[
\boxed{L_D'(s)=-(1-s)\kappa_s.}
\]
Indeed,
\[
\mathbb E_D\ell_s
=\langle\Sigma_s^{-1}\Delta,M_1-M_s\rangle
=(1-s)\kappa_s.
\]

For an interior endpoint,
\[
\boxed{
L_D(s)=\operatorname{KL}(D\Vert Q_1)
+\int_s^1(1-t)\kappa_t\,dt.
}
\]

This is an exceptionally clean companion to the observable accounting identity:

* observable change is linear response plus accumulated normal curvature plus fibre residual;
* information loss decreases by accumulated weighted Fisher speed;
* its terminal value is exactly the information unresolved by the features.

This concerns a **fixed data law** viewed against moving reconstructions. An arbitrary moving choice \(D_s\) in the fibres has additional variation that the moments alone cannot determine.

### Transport is downstream, not the next foundation

Total variation is native to the existing measurable setup. Wasserstein requires additional structure on the sample space. With a bounded metric, TV yields a transport bound immediately; with an unbounded metric, one needs weighted density estimates and moment control. I would not introduce that machinery before finishing the measure-valued theorem.

## 3. Boundary: separate three different claims

For \(f(s)=\mathbb E_{Q_s}\phi\), interior Taylor gives
\[
f(t)-f(0)
=t f'(0)+\int_0^t(t-s)f''(s)\,ds.
\]

### A. The triangular-kernel endpoint is clean

If \(Q_t\to Q_*\) in total variation, then for every bounded \(\phi\),
\[
\boxed{
\mathbb E_{Q_*}\phi-\mathbb E_\nu\phi
=
\lim_{t\uparrow1}
\left[
t\,\mathbb E_\nu(\phi\ell_0)
+\int_0^t(t-s)\,
\mathbb E_{Q_s}[\phi N_{M_s}(\ell_s^2)]\,ds
\right].
}
\]

No monotonicity of \(f\) is needed. In general, **\(f\) is not monotone**.

This is the safe boundary accounting statement. Add \(\mathbb E_D\phi-\mathbb E_{Q_*}\phi\) for a data law in the endpoint fibre. Do not automatically write it using an endpoint \(N_M\): the interior covariance and tangent structure can degenerate there.

### B. The fixed kernel \(1-s\) is a stronger assertion

Integration by parts gives
\[
\int_0^t(1-s)f''(s)\,ds
=f(t)-f(0)-f'(0)+(1-t)f'(t).
\]
Thus endpoint continuity alone does **not** establish the desired fixed-kernel identity. One additionally needs
\[
(1-t)f'(t)\longrightarrow0.
\]
Nor does this establish absolute integrability of \((1-s)f''(s)\).

The lower bound on \(\kappa\) does not settle either question. In particular, a lower bound on \((1-s)\kappa_s\) is not an obstruction to its integrability over a finite interval.

### C. Finite rate does give a beautiful positive scalar endpoint

Suppose the endpoint has a finite-rate information projection \(Q_*\), and the rate function is the entropy-minimisation value on the closed mean domain. Then
\[
I(M_s)\longrightarrow I(M_1).
\]
A standard proof uses the feasible mixture \((1-s)\nu+sQ_*\) for the upper bound and lower semicontinuity of the entropy value for the lower bound.

Writing \(i(s)=I(M_s)\), finite endpoint value and convexity imply
\[
(1-s)i'(s)\longrightarrow0.
\]
Hence
\[
\operatorname{KL}(Q_*\Vert Q_s)
=I(M_1)-i(s)-(1-s)i'(s)
\longrightarrow0,
\]
so Pinsker supplies total-variation convergence. Moreover,
\[
\boxed{
\operatorname{KL}(Q_*\Vert Q_s)
=\int_s^1(1-t)\kappa_t\,dt.
}
\]

This establishes weighted integrability of **Fisher speed squared**. It does not, by itself, establish absolute integrability of the signed normal-response field for every observable.

So: land the triangular endpoint under your actual endpoint convergence theorem; keep the fixed-kernel endpoint as a separately stated strengthening.

## 4. Precise top theorem and a no-`Lp` proof route

You can avoid the `Lp` API entirely. I would not use the quadratic density remainder twice as the main proof: a bound of order \(O(\|\eta\|^2)\) alone does not identify a second-order coefficient with an \(o(\|z\|^2)\) remainder.

Instead, use **continuity of the density Hessian in integrated absolute value**, followed by scalar Taylor pointwise.

### Definitions

On the response chart around \(M\), set
\[
q_z=q_{M+z},
\qquad
A_z[u]=q_z\ell_{M+z,u},
\]
and
\[
H_z[u,w]
=q_zN_{M+z}(\ell_{M+z,u}\ell_{M+z,w}).
\]

These are ordinary measurable functions. Their norms below are simply integrals of absolute values.

### Lemma 1: pointwise density Hessian

On a common full-measure set,
\[
Dq_z[u]=A_z[u],
\qquad
DA_z[w][u]=H_z[u,w].
\]

The crucial score identity is
\[
D\ell_{M+z,u}[w]
=-G_{M+z}(u,w)
-B_{M+z}(\ell_{M+z,u}\ell_{M+z,w}).
\]
Multiplication by \(q_z\), followed by the product rule, yields \(H_z\).

This should be close to a repackaging of `hasFDerivAt_famDens_response` and `hasFDerivAt_famDens_responseScore`.

### Lemma 2: local domination and integrated continuity

For a sufficiently small response ball, prove
\[
q_z\le Cq_0,
\qquad
|H_z[u,w]|\le Cq_0\|u\|\|w\|
\quad\text{a.e.}
\]

The first follows directly from bounded features:
\[
\frac{p_{\theta+\eta}}{p_\theta}
\le e^{2K\|\eta\|}.
\]
For the second use local boundedness of \(R\), bounded centred features, and the covariance-regression formula for \(B\).

Choose an orthonormal basis \((e_i)\) of \(\mathbb V\), and define
\[
d_H(z):=\sum_{i,j}\int
|H_z[e_i,e_j]-H_0[e_i,e_j]|\,d\nu.
\]
Pointwise continuity of the finite-dimensional coefficients and dominated convergence give
\[
d_H(z)\longrightarrow0.
\]
Bilinearity then gives the useful uniform estimate
\[
\int|(H_z-H_0)[u,w]|\,d\nu
\le d_H(z)\|u\|\|w\|.
\]

**This finite-basis construction is the substitute for an `L¹`-valued bilinear-map API.**

### Lemma 3: integrated scalar Taylor

For almost every sample point, apply scalar Taylor along \(t\mapsto tz\):
\[
q_z-q_0-A_0[z]-\tfrac12H_0[z,z]
=
\int_0^1(1-t)(H_{tz}-H_0)[z,z]\,dt.
\]

Domination permits the integral triangle inequality and interchange of the two integrations. Therefore
\[
\int|q_z-q_0-A_0[z]-\tfrac12H_0[z,z]|\,d\nu
\le
\|z\|^2\int_0^1(1-t)d_H(tz)\,dt.
\]

Given \(\varepsilon>0\), choose a response ball on which \(d_H<2\varepsilon\). The right side is at most
\[
\varepsilon\|z\|^2.
\]
That is exactly the required Peano statement.

### Lemma 4: simultaneous observable response

For bounded measurable \(g\),
\[
\left|\int g\,\mathrm{remainder}\,d\nu\right|
\le \|g\|_\infty\int|\mathrm{remainder}|\,d\nu.
\]
This immediately gives the uniform bounded-observable theorem. The converse equality with the supremum follows by choosing the sign of the remainder, but need not block the main landing.

### Compact-uniform version

Repeat integrated Hessian continuity with a variable base point. A compact subset of the interior has a small compact neighbourhood still inside the interior. Uniform continuity of the finitely many integrated Hessian coefficients on that neighbourhood gives the uniform modulus required by Lemma 3.

### Line estimate

With the stated derivative lemmas and the existing Taylor infrastructure, I would budget roughly:

| Component | Lean lines |
|---|---:|
| Pointwise Hessian packaging | 30–60 |
| Local density/Hessian domination | 70–130 |
| Finite-basis integrated continuity | 60–110 |
| Integrated Peano theorem | 50–90 |
| Observable/TV corollaries | 20–40 |
| **Core landing** | **230–430** |

Compact-uniform packaging could add approximately 80–160 lines. These are planning estimates; the main uncertainty is the existing ergonomics for regression coefficients and parameterised integrals, not the analytic argument.

## 5. The “one theorem” presentation

I would organise §7 around three layers:

1. **Reconstruction:** the feature mean selects the exponential-family law; the fibre contains what the features cannot resolve.
2. **Response of the law:** first derivative \(q\ell\), second derivative \(qN(\ell\ell)\), with a total-variation Peano remainder.
3. **Finite accounting:** integrate those responses from \(\nu\) to the reconstruction, then add the fibre residual; alongside this, integrate weighted Fisher speed to account for information.

The resulting message is unusually complete:

> Features determine a reconstructed law and its response geometry. Tangent scores carry first-order change; normal quadratic scores carry second-order change. Their accumulated response accounts for the reconstructed part of every observable, while the endpoint fibre records exactly what the features leave undetermined.

That is the deepest next landing without changing the programme or importing a new geometry.