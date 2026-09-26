## Verdict

The deepest remaining result is **a uniform second-order theorem for the entire reconstructed law**, not another scalar response identity:

> Reconstruction is a smooth section of the moment map; its differential is the visible projection, its nonlinear remainder is moment-invisible, and sampling averages its curvature.

This joins almost everything already landed. The key remaining analytic work is **an \(L^1\)-valued, locally uniform second-order expansion**.

Three qualifications matter:

1. Linewise second derivatives alone do **not** justify polarization or uniform signed-measure bias.
2. For a curved moment path, acceleration has an additional visible term.
3. Fisher contraction/Pythagoras holds naturally at the reconstructed law \(Q_M\), not generally at the original data law \(D\).

Below, assume finite-dimensional moment space, positive-definite covariance, and sufficient local domination for the indicated derivatives. Bounded features \(S\) give a particularly clean route. Without bounded features, use appropriate weighted spaces or exponential envelopes rather than automatically claiming TV smoothness.

---

## 1. Ranked remaining theorems

### Rank 1 — Uniform second jet and law-valued sampling bias

Write
\[
Y=S-M,\qquad C_M=E_{Q_M}[YY^\top],\qquad
\ell_{M,u}=\langle C_M^{-1}u,Y\rangle,
\]
and
\[
K_M(u,v)=E_{Q_M}[Y\ell_{M,u}\ell_{M,v}].
\]
Then define
\[
J_Mu=q_M\ell_{M,u},
\]
\[
H_M[u,v]
=q_M\bigl(\ell_{M,u}\ell_{M,v}
-g_M(u,v)-\ell_{M,K_M(u,v)}\bigr)
=q_MN_M(\ell_{M,u}\ell_{M,v}).
\]

**Target theorem.** Locally on the interior moment domain,
\[
q_{M+h}=q_M+J_Mh+\tfrac12H_M[h,h]+r_M(h),
\qquad
\frac{\|r_M(h)\|_1}{\|h\|^2}\longrightarrow0,
\]
with \(H_M\) continuous in bilinear-operator norm. Ideally package this as \(C^2\) into \(L^1(\nu)\).

For iid data with \(T=S-M\), empirical moments \(\widehat M_n\), and a suitably localized reconstruction \(\widetilde q_n\),
\[
n\bigl(E_D[\widetilde q_n]-q_M\bigr)
\longrightarrow
\frac12 E_D[H_M[T,T]]
\quad\text{in }L^1(\nu).
\]

Consequently, simultaneously for every \(\|F\|_\infty\le1\),
\[
n\bigl(E_D[\widetilde G_{F,n}]-G_F(M)\bigr)
\longrightarrow
\frac12E_D[b_{F,M}(T,T)],
\]
with convergence uniform over that unit ball.

**Seabed-level route.**

- Upgrade `atlasHess_eq_normalProj` from a pointwise identity to an \(L^1\)-valued second derivative.
- Establish local bounds for \(C_M^{-1}\), \(q_M\), and the relevant weighted moments.
- Prove continuity of the explicit bilinear map \(H_M\).
- Obtain a Bochner Taylor remainder and apply `EmpiricalMoments`-type concentration/uniform-integrability estimates.
- Reuse scalar `PlugInBias` algebra, but perform the final remainder estimate in \(L^1\).

This is the flagship because it turns the collection of scalar response theorems into **one theorem about every bounded observable at once**.

---

### Rank 2 — Reconstruction as a smooth retraction, with an exact projection differential

Let
\[
\mathsf m(d)=\int S d\,d\nu,\qquad
\mathcal R(d)=q_{\mathsf m(d)}.
\]
For bounded \(S\), extend \(\mathcal R\) locally to the open subset of the affine Banach space
\[
\{d\in L^1(\nu):\textstyle\int d\,d\nu=1\}
\]
whose moments lie in the interior domain. This avoids pretending that positive densities form an \(L^1\)-open set.

**Target theorem.**
\[
D\mathcal R_d[h]
=q_M\ell_{M,\int Sh\,d\nu},\qquad \int h\,d\nu=0.
\]
Moreover,
\[
\mathsf m\circ\mathcal R=\mathsf m,\qquad
\mathcal R\circ\mathcal R=\mathcal R,
\]
and, writing \(P_Mh=q_M\ell_{M,\int Sh}\),
\[
P_M^2=P_M,\qquad
\ker P_M=\{h:\int h=0,\ \int Sh=0\}.
\]

Thus the global response map factors exactly through the moment quotient, and its differential is a finite-rank projection.

**Fisher statement—with the correct base law.** If \(h=q_Ma\), \(E_{Q_M}a=0\), and \(a\in L^2(Q_M)\), then
\[
P_Mh=q_MB_Ma,
\]
\[
E_{Q_M}a^2
=g_M\!\left(\int Sh,\int Sh\right)+E_{Q_M}(N_Ma)^2.
\]

At a general data law \(D=d\nu\), taking \(h=da\) does **not** generally give contraction relative to \(E_Da^2\). Indeed, contraction for all centered data scores is equivalent to
\[
\operatorname{Cov}_D(S)\preceq C_M,
\]
which need not hold.

So: **visible Fisher projection at \(Q_M\)** is exact; “information contraction from arbitrary \(D\)” requires an extra hypothesis.

**Route:** the moment map is bounded linear; compose it with the existing \(L^1\) first derivative. Projection identities reduce to moment reproduction. `TangentPythagoras` supplies the metric statement.

---

### Rank 3 — Whole-law transport and invisible acceleration

For a \(C^2\) moment path \(M_t\),
\[
\dot q_t=q_t\ell_{M_t,\dot M_t},
\]
\[
\ddot q_t
=H_{M_t}[\dot M_t,\dot M_t]
+J_{M_t}\ddot M_t.
\]

The second term is essential. **Acceleration is wholly invisible only for affine moment paths**, or after subtracting the visible acceleration induced by \(\ddot M_t\).

For \(M_t=M_0+t\delta\),
\[
\ddot q_t=q_tN_{M_t}(\ell_{M_t,\delta}^2),
\qquad
\int\ddot q_t\,d\nu=0,\quad
\int S\ddot q_t\,d\nu=0,
\]
and
\[
q_t=q_0+tJ_{M_0}\delta+
\int_0^t(t-r)H_{M_r}[\delta,\delta]\,dr
\quad\text{in }L^1.
\]

There is also an exact, non-asymptotic invisibility identity:
\[
\int
\begin{pmatrix}1\\S\end{pmatrix}
\bigl(q_{M+h}-q_M-J_Mh\bigr)\,d\nu=0.
\]
Thus **all nonlinear deviation from the tangent prediction is invisible to the fitted features**, not merely its quadratic approximation.

**Route:** `CurveLength` for first-order transport; `AtlasHessian` plus \(L^1\) domination for the second derivative; Bochner FTC for the law-valued remainder. This is an excellent intermediate landing before the full flagship.

---

### Rank 4 — A computable all-orders invisible tower

Under stronger smoothness/domination, along \(M_s=M+s u\),
\[
\frac d{ds}\ell_{M_s,u}
=-g_{M_s}(u,u)-\ell_{M_s,K_{M_s}(u,u)}.
\]

Define
\[
P_0=1,\qquad
P_{k+1}=\partial_sP_k+\ell_{M_s,u}P_k.
\]
Then
\[
\frac{d^kq_{M_s}}{ds^k}=q_{M_s}P_k.
\]
In particular,
\[
P_1=\ell_u,\qquad P_2=N(\ell_u^2).
\]
Differentiating the exponential-family moments and inverse covariance gives a recursive cumulant calculus for subsequent \(P_k\).

For every \(k\ge2\),
\[
E_{Q_{M_s}}P_k=0,\qquad
E_{Q_{M_s}}[SP_k]=0.
\]

This is a beautiful strengthening: **every higher affine-atlas derivative is invisible**.

**Route:** a reusable differentiation-under-expectation lemma, `thirdOp`/`cumulantVec`, and differentiation of inverse covariance. Prove smoothness under an explicit envelope before pursuing a formal cumulant tower.

I would place the reverse-KL identity and tilt counterexample below these four. They complete the residual narrative, but do not deepen the response map as much as law-valued geometry does.

---

## 2. Is the linewise/polarization route sound and cheaper?

### Not from linewise existence alone

Knowing
\[
\frac{d^2}{dt^2}q_{M+tu}\Big|_{t=0}
\]
for every \(u\) does not establish that its dependence on \(u\) is quadratic. Polarization does not magically produce a bilinear Hessian, nor does scalar differentiability imply \(L^1\) differentiability.

Also, \(M+u\) need not lie in the moment domain. For arbitrary \(u\), use a sufficiently short segment \(M+tu\), not a unit-length atlas segment without qualification.

### A sound, potentially cheaper route

Prove the directional formula directly with the explicit candidate
\[
H_M[u,v]=q_MN_M(\ell_{M,u}\ell_{M,v}).
\]
This is visibly bilinear. Polarization then identifies mixed terms; it is not doing the analytic work.

The decisive uniformity is
\[
\lim_{\rho\downarrow0}
\sup_{0<\|h\|\le\rho}
\frac{\|q_{M+h}-q_M-J_Mh-\frac12H_M[h,h]\|_1}
{\|h\|^2}=0.
\]
For bias at one \(M\), this fixed-base uniform Peano estimate suffices. Compact-uniformity in \(M\) is useful but stronger than necessary.

A convenient sufficient condition is an \(L^1\) second derivative along every short segment together with operator-norm continuity of \(H\). Then
\[
r_M(h)=\int_0^1(1-t)
\bigl(H_{M+th}-H_M\bigr)[h,h]\,dt,
\]
so
\[
\|r_M(h)\|_1
\le\tfrac12\|h\|^2
\sup_{0\le t\le1}\|H_{M+th}-H_M\|_{\rm op}.
\]

In finite dimensions, local joint continuity plus compactness of direction spheres can supply this uniformity. Separate, direction-by-direction limits cannot.

### What sampling additionally needs

Let \(\Delta_n=\widehat M_n-M\). A clean sufficient package is:

- \(E\Delta_n=0\);
- \(\{n\|\Delta_n\|^2\}\) is uniformly integrable;
- reconstruction agrees with \(q_{M+\Delta_n}\) on a fixed local good event;
- outside it, use a uniformly \(L^1\)-bounded fallback—any probability density has norm one.

Uniform integrability makes the bad-event contributions negligible at scale \(n\), including the truncated linear term. Bounded features make stronger concentration estimates readily available.

Then independence gives
\[
nE[H_M[\Delta_n,\Delta_n]]=E[H_M[T,T]],
\]
while \(nE\|r_M(\Delta_n)\|_1\to0\).

Finally,
\[
\|f\|_1=\sup_{\|F\|_\infty\le1}\left|\int Ff\,d\nu\right|.
\]
Applying a scalar schema separately to every \(F\) gives only individual convergence. To obtain \(L^1\), every remainder/tail estimate must be uniform in \(F\), typically bounded by \(\|F\|_\infty\) times one vanishing quantity.

**Recommendation:** land the uniform \(L^1\) second jet first. It may be cheaper than developing a full `ContDiff` API, while already proving the flagship bias.

---

## 3. A closing main theorem

### **Response geometry: projection, invisible bending, and averaged curvature**

Let \(\nu=Q_{m_0}\) be the featureless reference, \(D\) a data law with interior moment \(M_*\), and
\[
D_t=(1-t)\nu+tD,\qquad M_t=m_0+t\delta,\qquad \delta=M_*-m_0.
\]
Under the preceding regularity assumptions:

1. **Exact factorization and projection**
   \[
   \mathcal R(D)=Q_{E_DS},\qquad
   D\mathcal R_d[h]=q_M\ell_{M,\int Sh}.
   \]
   At \(Q_M\), this is the Fisher-orthogonal visible projection.

2. **Whole-law response transport**
   \[
   q_{M_t}-q_{m_0}
   =\int_0^tq_{M_r}\ell_{M_r,\delta}\,dr.
   \]

3. **Invisible bending**
   \[
   q_{M_t}=q_{m_0}+tq_{m_0}\ell_{m_0,\delta}
   +\int_0^t(t-r)q_{M_r}N_{M_r}(\ell_{M_r,\delta}^2)\,dr,
   \]
   with the remainder carrying zero mass and zero feature moments.

4. **Sampling averages the bending**
   \[
   n(E\widetilde q_n-q_{M_*})
   \to\tfrac12E_D[H_{M_*}[S-M_*,S-M_*]]
   \quad\text{in }L^1.
   \]
   The limiting signed bias is itself invisible.

5. **The same atlas is a natural-gradient trajectory**
   Under \(t=1-e^{-\tau}\), \(M_t\) is the negative natural-gradient flow of
   \[
   L(M)=KL(Q_{M_*}\Vert Q_M),
   \]
   with the landed dissipation identity.

Every bounded-observable theorem follows by pairing these identities with \(F\). The landed influence covariance theorem supplies their stochastic first-order counterpart.

The closing picture is therefore:

> **Data move the moments; reconstruction lifts that motion visibly. Its nonlinear bending preserves those moments, sampling averages that bending into bias, and the straight moment atlas becomes a natural-gradient flow after changing its clock.**

Most of this package is already present. The missing bridge is precisely the uniform \(L^1\) second jet—not another isolated scalar identity.