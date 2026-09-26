## Recommendation

The next milestone should be **a differential geometry of data-to-response maps**, with sampling theory as a corollary—not another isolated asymptotic coefficient.

Use the following notation to avoid a Fisher-coordinate ambiguity:
\[
C_M=\operatorname{Cov}_{Q_M}(S)|_{\mathbb V},\qquad
H_M(u,v)=\langle u,C_M^{-1}v\rangle,\qquad Q_M=\Pi(M).
\]
Thus \(H_M=D^2\mathcal I(M)\) is the Fisher metric **in moment coordinates**. If your \(g_M\) denotes covariance in natural coordinates, \(H_M=g_M^{-1}\); if it already denotes the moment-coordinate Fisher metric, do not invert it again.

Below, assume finite-dimensional bounded features, \(\nu\) a probability measure, and \(F\in L^\infty(\nu)\). Line counts are rough additional Lean LOC, not repository-audited estimates. “New” means new capability for this programme, not necessarily a new result in the literature.

## 1. Ranked next theorems

### 1. Data-path transport and the exact mixture–atlas identification

**Statement.** Let \(t\mapsto D_t\) be a \(C^1\) curve of probability measures in total variation, with \(M_t=\int S\,dD_t\in\operatorname{ri}K\). Then
\[
\dot M_t=\int S\,d\dot D_t,\qquad
\dot\theta_t=C_{M_t}^{-1}\dot M_t,
\]
\[
\frac d{dt}[q_{M_t}]=[q_{M_t}\ell_{M_t,\dot M_t}]
\quad\text{in }L^1(\nu).
\]
Writing
\[
c_F(M)=\operatorname{Cov}_{Q_M}(S,F),\qquad
\psi_{F,M}(x)=\langle C_M^{-1}c_F(M),S(x)-M\rangle,
\]
gives
\[
\frac d{dt}G_F(M_t)=\int\psi_{F,M_t}\,d\dot D_t.
\]
Consequently,
\[
G_F(M_1)-G_F(M_0)
=\int_0^1\operatorname{lin}_{F,M_t}(\dot M_t)\,dt.
\]

For \(D_t=(1-t)\nu+tD\),
\[
M_t=m_0+t\delta,\qquad \delta=M-m_0.
\]
This is **exactly** the straight moment atlas, although generally \(D_t\ne Q_{M_t}\).

Moreover,
\[
\mathcal I'(M_t)=\langle\theta_t,\delta\rangle,\qquad
\frac{d^2}{dt^2}\mathcal I(M_t)=H_{M_t}(\delta,\delta).
\]
With the effective natural parameter normalized by \(\theta(m_0)=0\),
\[
\mathcal I(M_t)
=\int_0^t(t-r)H_{M_r}(\delta,\delta)\,dr.
\]
It is convex and nondecreasing, strictly increasing for \(t>0\) if \(\delta\ne0\).

**Route.** Bounded-feature integration is a continuous linear moment map; compose with the landed \(L^1\)-\(C^1\) theorem. Apply the dual-gradient identity \(D\mathcal I=\theta\) and covariance inverse derivative. Reuse TV–Fisher length.

**Cost:** 350–750 LOC; perhaps another 200–400 for a general measure-curve interface.

**New:** an operational answer to “how do expectations change when the data change?”, including invisible tangent directions \(\dot M_t=0\).

**Important:** for a general curved moment path,
\[
(\mathcal I\circ M)''=H_M(\dot M,\dot M)+\langle\theta,\ddot M\rangle.
\]
Convexity and monotonicity are not automatic outside the affine ray.

---

### 2. Information splitting along the atlas—with the correct nonmonotonicity theorem

**Statement.** Assume \(D\ll\nu\), \(KL(D\|\nu)<\infty\), and \(M\in\operatorname{ri}K\). Along the mixture path,
\[
KL(D_t\|\nu)=\mathcal I(M_t)+R(t),\qquad
R(t):=KL(D_t\|Q_{M_t}).
\]
Hence
\[
0\le R(t)\le t\,KL(D\|\nu)-\mathcal I(M_t).
\]
More informatively,
\[
R(t)\le tR(1)+t\mathcal I(M)-\mathcal I(M_t).
\]

If \(h=dD/d\nu-1\in L^2(\nu)\), then
\[
R(t)=\frac{t^2}{2}
\left[
\|h\|_{L^2(\nu)}^2-H_{m_0}(\delta,\delta)
\right]+o(t^2)
=\frac{t^2}{2}\|N_{m_0}h\|_2^2+o(t^2).
\]

**Route.** Integrate the bounded affine log-density
\(\log q_M=\langle\theta(M),S\rangle-A(\theta(M))\);
moment matching gives Pythagoras. Combine entropy convexity with the visible-information Hessian. For the local expansion, use the scalar entropy expansion under an \(L^2\) dominating bound.

**Cost:** 200–450 LOC for splitting/bounds if KL chain identities exist; 350–700 more for the \(L^2\) local expansion.

**New:** global information accounting plus a local orthogonal decomposition of data perturbations.

**Crucial correction:** \(R(t)\) is **not generally monotone**. See §2 below.

---

### 3. \(L^1\)-\(C^2\) reconstruction, then a uniform whole-atlas response theorem

This is the main structural investment.

**Statement.**
\[
M\longmapsto[q_M]\in L^1(\nu)
\quad\text{is }C^2,
\]
with
\[
D^2q_M[u,v]
=q_M\,N_M(\ell_{M,u}\ell_{M,v}),
\]
where \(N_M\) is the residual orthogonal to constants and scores.

Choose a compact convex interior neighborhood \(C\) of \(M\). For the whole empirical atlas, use the common event \(\widehat M_n\in C\), and otherwise fall back to the true deterministic atlas. Set
\[
U_n(s)=q_{m_0+s(\widehat M_n-m_0)},\qquad
U(s)=q_{M_s}
\]
on that event. Then, in \(C([0,1],L^1(\nu))\),
\[
n\bigl(\mathbb E U_n-U\bigr)
\longrightarrow
\left[s\mapsto
\frac{s^2}{2}\sum_{ab}\Gamma_{ab}
D^2q_{M_s}[\pi e_a,\pi e_b]\right].
\]
Also,
\[
\mathbb E\sup_s\|\widehat Q_n(s)-Q_{M_s}\|_{\rm TV}^2=O(n^{-1}).
\]

For bounded \(F,H\), the scalar path covariance has the sharper uniform limit
\[
n\operatorname{Cov}(\widehat G_F(s),\widehat G_H(r))
\longrightarrow
sr\sum_{ab}\Gamma_{ab}
\operatorname{lin}_{F,M_s}(\pi e_a)
\operatorname{lin}_{H,M_r}(\pi e_b).
\]

**Route.** Differentiate the score using \(D\theta=C^{-1}\), the inverse-matrix derivative, and the third cumulant. Bounded features provide local \(L^1\) domination. The displayed Hessian is precisely the normal-projection identity behind BiasForm. Work uniformly on
\(\operatorname{conv}(\{m_0\}\cup C)\), a compact interior set.

No analytic IFT or all-orders theorem is needed.

**Cost:** 800–1600 LOC for \(C^2\); 450–900 for pathwise consequences.

**New:** the reconstruction bias becomes a **measure-valued curvature field**, simultaneously controlling every bounded observable.

Do not call TV fluctuations a “variance” without specifying the functional. Squared TV norm is not a quadratic form, so it does not generally have a covariance-contraction coefficient. The \(O(n^{-1})\) bound and scalar covariance kernel are the clean CLT-free statements.

---

### 4. Visible-information bias and expected local information loss

**Statement.** For the same localization,
\[
n\left(\mathbb E\widehat{\mathcal I}_n-\mathcal I(M)\right)
\longrightarrow
\frac12\operatorname{tr}_{\mathbb V}(C_M^{-1}\Gamma_{\mathbb V}).
\]
Equivalently,
\[
\frac12\mathbb E_D\,H_M(S-M,S-M).
\]

An especially geometric companion is
\[
n\,\mathbb E\,KL(Q_{\widehat M_n}\|Q_M)
\longrightarrow
\frac12\operatorname{tr}_{\mathbb V}(C_M^{-1}\Gamma_{\mathbb V}),
\]
with the same localized convention.

In the well-specified case \(D=Q_M\), both coefficients are
\[
\frac12\dim\mathbb V.
\]

**Route.** A scalar \(C^2\) plug-in schema applied to \(\mathcal I\); for the companion use
\[
KL(Q_{M+z}\|Q_M)
=\mathcal I(M+z)-\mathcal I(M)-\langle\theta(M),z\rangle.
\]

**Cost:** 250–550 LOC after extracting the schema and identifying the Hessian.

**New:** an observable-free calibration of reconstruction complexity.

Yes: your proposed inverse-Fisher coefficient is correct **with the coordinate convention stated above**, and with covariance restricted to \(\mathbb V\).

---

### 5. Joint plug-in covariance, with variance and MSE as corollaries

Prove the joint version rather than separate variance and MSE theorems.

**Statement.**
\[
n\operatorname{Cov}(\widehat G_{F,n},\widehat G_{H,n})
\longrightarrow
\mathbb E_D[\psi_{F,M}\psi_{H,M}].
\]
Thus
\[
n\operatorname{Var}(\widehat G_{F,n})
\to V_F,\qquad
n\mathbb E(\widehat G_{F,n}-G_F(M))^2\to V_F,
\]
where
\[
V_F=c_F^\top C_M^{-1}\Gamma_{\mathbb V}C_M^{-1}c_F.
\]

**Correction:** under misspecification this is a **sandwich covariance**, not simply the Fisher-dual norm. Only when \(\Gamma=C_M\) does it become
\[
c_F^\top C_M^{-1}c_F
=\|dG_F\|_{H_M^{-1}}^2.
\]

**Route.** Uniform first-order remainder, exact empirical covariance, and Hoeffding tail control. ReconstructionBias gives bias \(O(n^{-1})\), whose square is negligible at scale \(n\).

**Cost:** 250–500 LOC.

**New:** the uncertainty geometry of reconstructed observables, including cross-observable coupling. This is cheap and worth landing, but less central than the transport theorem.

## 2. Is the mixture path canonical? What actually happens to invisible information?

It is canonical **for the affine structure on probability measures**: it needs no metric, works with zeros in \(dD/d\nu\), and maps exactly to your straight moment atlas.

It is not uniquely canonical. Exponential interpolation and Fisher–Rao geodesics express different geometries and generally induce different moment paths.

Also, \(\nu\) is “maximal entropy” in the **relative** sense: it minimizes \(KL(\cdot\|\nu)\). It need not maximize an independently chosen absolute entropy unless the reference structure makes it uniform.

With \(r=dD/d\nu\),
\[
\frac{dD_t}{d\nu}=1+t(r-1),\qquad
KL(D_t\|\nu)=\int [1+t(r-1)]\log[1+t(r-1)]\,d\nu.
\]
The reconstructed path has
\[
\dot\theta_t=C_{M_t}^{-1}\delta,\qquad
\dot q_t=q_t\ell_{M_t,\delta}.
\]
These are exact closed formulas in the seabed’s objects, although \(\theta_t\) itself is normally only implicit.

Both total and visible information are convex and nondecreasing along this ray, and
\[
\mathcal I(M_t)\le t\mathcal I(M),\qquad
KL(D_t\|\nu)\le tKL(D\|\nu).
\]

### Invisible information can form a hump

Take three points, uniform \(\nu\), feature \(S=0,1,2\), and
\[
D=Q_\theta,\qquad D\propto(1,a,a^2),\quad a\ne1.
\]
Then \(R(0)=R(1)=0\), but \(R(t)>0\) for \(0<t<1\): an interior mixture of these two exponential-family members is not itself in the family.

Indeed, writing its probabilities \(p_0,p_1,p_2\),
\[
p_0p_2-p_1^2
=\frac{t(1-t)(a-1)^2}{3(1+a+a^2)}>0,
\]
whereas exponential-family membership requires equality.

Thus “invisible information decreases toward the featureless end” is false as a global monotonicity assertion—even for perfectly specified endpoint data.

The strongest clean general replacement is:

* \(R(t)\to0\) as \(t\downarrow0\), with \(R(t)\le tKL(D\|\nu)\);
* the sharper visible-information-corrected envelope above;
* under \(L^2\) density perturbations, the exact quadratic normal-energy expansion.

At interior \(t\), one also has the diagnostic identity
\[
tR'(t)
=R(t)+KL(\nu\|D_t)-KL(\nu\|Q_{M_t}),
\]
which exposes why no fixed sign is available.

## 3. Reusable Mathlib-facing extraction

Extract two layers.

**First: empirical bilinear contraction.** For centered iid finite-dimensional \(Z_i\) with second moments and continuous bilinear \(B\),
\[
\mathbb E B(\bar Z_n,\bar Z_n)
=\frac1n\mathbb E B(Z_1,Z_1).
\]
Include the cross-bilinear form and continuous-linear image variants. This is broadly reusable probability infrastructure.

**Second: localized second-order delta lemma.** For a finite-dimensional sample mean and a map \(f\) into a Banach space, assume:

* a compact-uniform second-order Peano expansion;
* covariance scaling \(1/n\);
* sufficiently strong tail/uniform-integrability control;
* measurable bounded localization.

Then
\[
n(\mathbb E\widehat f_n-f(m))
\to \tfrac12\mathbb E D^2f(m)[Z_1,Z_1].
\]
Keep an abstract remainder/tail theorem separate from the bounded-iid Hoeffding specialization. The Banach-valued version directly supports the whole-atlas theorem.

The bilinear lemma is the easier upstream candidate; the localization schema merits a small reusable analysis/probability module first.

## 4. Referee-proof ReconstructionBias statement

A clean paper formulation is:

> Let \(X_i\) be iid with law \(D\), let \(S\) be bounded, and let \(M=\mathbb E_DS\in\operatorname{ri}K\). Choose a compact convex \(C\subset\operatorname{ri}K\) containing a relative neighborhood of \(M\). For bounded \(F\), define the localized plug-in by \(G_F(\widehat M_n)\) on \(\{\widehat M_n\in C\}\), with any fixed bounded fallback otherwise. Then
> \[
> n(\mathbb E\widehat G_{F,n}-G_F(M))
> \to\frac12\mathbb E_D b_{F,M}(S-M,S-M).
> \]

Address four points explicitly:

* **Localization:** legitimate, but this is not automatically a theorem about the raw plug-in. Removing localization requires global definition and tail/uniform-integrability control. The true-value fallback is an oracle device; any fixed bounded fallback gives the same limit.
* **Projection \(\pi\):** implementation scaffolding. Since \(S-M\in\mathbb V\) almost surely, the intrinsic coefficient is independent of the chosen projection. Prove this once.
* **Sup norm:** harmless finite-dimensional concentration machinery; state the final result intrinsically.
* **`DecidablePred`:** proof-irrelevant implementation detail. The mathematical issue is measurability of the localization event, supplied by compactness/closedness.

The beautiful endpoint is a single picture: **data tangents split into visible and invisible directions; visible directions transport responses by Fisher regression; curvature produces reconstruction bias; and the atlas integrates that geometry from the reference law to the observed moments.**