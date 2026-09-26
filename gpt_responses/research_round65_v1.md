## Recommendation

The next flagship should be **an explicit smooth response geometry, followed by a constructive featureless expansion with controlled remainder**.

The all-orders smoothness theorem establishes existence. What remains is to turn it into a usable map: **identify the derivatives, compute them from reference cumulants, and control the error in transporting responses from the reference to the data**. Analyticity is valuable, but only if accompanied by convergence control; a formal infinite expansion alone does not provide that map.

I would rank the remaining targets as follows.

## 1. Global smooth split retraction with an explicit invisible Hessian

Combine candidates (a) and (b) into one closing theorem. The smooth upgrade alone is assembly; the explicit Hessian gives it substantive content.

Write
\[
X_M=S-M,\qquad C_M=\operatorname{Cov}_{Q_M}(S)|_{\mathbb V},
\qquad
\ell_{M,u}=\langle C_M^{-1}u,X_M\rangle.
\]
Define the normal projection on observables by
\[
N_M f
=f-E_{Q_M}f
-\left\langle C_M^{-1}E_{Q_M}[X_Mf],X_M\right\rangle.
\]

Then, in intrinsic mean coordinates,
\[
Dp_M[u]=J_Mu=[q_M\ell_{M,u}],
\]
and
\[
\boxed{D^2p_M[u,v]
=H_M[u,v]
=[q_MN_M(\ell_{M,u}\ell_{M,v})].}
\]

Consequently:

* \(p:\Omega\to L^1(\nu)\) is \(C^\infty\);
* \(H_M[u,v]\in K\);
* on the unit-mass affine space,
  \[
  DR_d[h]=J_{m(d)}\,m(h),
  \qquad
  D^2R_d[h,k]=H_{m(d)}[m(h),m(k)];
  \]
* every \(C^2\) mean path satisfies
  \[
  \boxed{\frac{d^2}{dt^2}p(M_t)
  =H_{M_t}[\dot M_t,\dot M_t]+J_{M_t}\ddot M_t.}
  \]

This separates **curvature of the response section**, which is invisible, from **acceleration of the prescribed mean**, which is tangent.

Moreover, your normal form becomes a \(C^\infty\) diffeomorphism in affine/intrinsic coordinates:
\[
\Phi:U\overset{\sim}{\longrightarrow}\Omega\times K,
\qquad R\sim(M,k)\mapsto(M,0).
\]

### Seabed route

1. Assemble multivariate \(C^\infty\) of \(p\) from the \(L^1\) tilted-family theorem and intrinsic inverse chart.
2. Upgrade `DataRetraction` and `NormalForm` by composition and addition.
3. **Exploit polarization before developing a separate second-derivative infrastructure.** If `atlasHess` already identifies the \(L^1\) second derivative along every affine mean line, then
   \[
   D^2p_M[u,u]=[q_MN_M(\ell_{M,u}^2)]
   \]
   determines the symmetric bilinear Hessian. If it is only observable-level, first lift that equality to \(L^1\).
4. Apply the second-order chain rule.

This is the highest payoff-to-proof-cost target.

---

## 2. Constructive all-orders featureless jets, with an \(L^1\) Taylor remainder

This is the deepest immediately actionable theorem for the stated direction.

Use natural coordinates \(\eta=-\theta\), so \(D_\eta m=C\). Along
\[
M_s=m_0+sh,\qquad h=M-m_0,
\]
put \(\eta_k=\eta^{(k)}(0)\). Let \(\kappa_r\) denote the reference cumulant tensors, and let \(\kappa_{r+1}^{\sharp}\) be vector-valued, characterized by contraction against an additional vector.

Then
\[
\eta_1=C^{-1}h,
\]
and, for \(k\ge2\),
\[
\boxed{
\eta_k=-C^{-1}
\sum_{\substack{\pi\in\operatorname{Part}([k])\\|\pi|\ge2}}
\kappa_{|\pi|+1}^{\sharp}
\bigl[\eta_{|B|}:B\in\pi\bigr].
}
\]

For the log-density derivatives, define
\[
L_j
=\langle\eta_j,S-m_0\rangle
-\sum_{\substack{\pi\in\operatorname{Part}([j])\\|\pi|\ge2}}
\kappa_{|\pi|}
\bigl[\eta_{|B|}:B\in\pi\bigr].
\]
The density derivatives are the exponential Bell polynomials:
\[
P_k=\sum_{\pi\in\operatorname{Part}([k])}\prod_{B\in\pi}L_{|B|},
\qquad
p^{(k)}(0)=[P_k],
\]
assuming \(\nu\) is a probability reference, hence \(q_0=1\).

Thus
\[
\left.\frac{d^k}{ds^k}E_{Q_{M_s}}F\right|_{s=0}
=E_\nu[FP_k].
\]

The important companion is a **finite, nonformal expansion**. Whenever \([0,1]\subset D\),
\[
p(s)=\sum_{j=0}^n\frac{s^j}{j!}p^{(j)}(0)
+\frac1{n!}\int_0^s(s-t)^n p^{(n+1)}(t)\,dt
\]
in \(L^1\). Hence, for \(0\le s\le1\),
\[
\left\|p(s)-\sum_{j=0}^n\frac{s^j}{j!}p^{(j)}(0)\right\|_1
\le
\frac{s^{n+1}}{(n+1)!}
\sup_{0\le t\le s}\|p^{(n+1)}(t)\|_1.
\]

This one theorem controls **all bounded observables simultaneously**.

### Seabed route

Land orders \(1,2,3\) first; then define cumulants recursively and choose either partitions or multiindex Bell polynomials. Differentiate the implicit moment identity and normalized exponential identity. Your Bochner FTC infrastructure supplies the remainder by iteration.

One wording correction: coefficients are polynomial in cumulants **and entries of \(C^{-1}\)**, not generally polynomial in raw moments alone.

---

## 3. Quantitative local analyticity and finite-step continuation

The correct analytic target is not “the Taylor series at zero reaches the data.” It is:

> Around every interior mean, the response section has a convergent \(L^1\)-valued power series; compact interior paths can be covered by finitely many such neighborhoods, with controlled truncation errors.

For direct natural-parameter analyticity, bounded \(S\) gives the absolutely convergent series
\[
e^{\langle\eta+h,S\rangle}
=e^{\langle\eta,S\rangle}
\sum_{k\ge0}\frac{\langle h,S\rangle^k}{k!}
\]
in \(L^1\), with factorial norm bounds. Normalization uses the analytic reciprocal of the nonzero partition function. The mean map follows by bounded linear integration.

The inverse is the genuinely new ingredient.

### Route without a packaged analytic IFT

At a base point, write
\[
m(\eta_0+z)-m(\eta_0)=Cz+G(z),
\qquad G(0)=DG(0)=0.
\]
Solve
\[
z=C^{-1}h-C^{-1}G(z)
\]
using a contraction together with a power-series majorant. This proves convergence of the recursively constructed inverse coefficients. Alternatively, prove sufficiently strong factorial bounds on implicit derivatives and use Taylor remainder estimates.

This is **not a mathematical dead end**, but it is an infrastructure project. I would not promise that `HasFPowerSeriesAt` composition alone supplies inversion, nor assert an existing Mathlib theorem without checking the current tree.

Also:
\[
C^\infty\not\Rightarrow\text{analytic},
\qquad
\text{analytic along }[0,1]\not\Rightarrow
\text{Taylor convergence from }0\text{ at }1.
\]
Complex singularities can limit the latter radius even when the entire real path is regular. Finite-step analytic continuation is the robust global statement.

---

## 4. Boundary completion: mapping responses all the way to boundary data

This is the major issue not addressed by interior smoothness.

For **finite sample space**, positive reference weights, and moment polytope \(P\), prove:

> The entropy-projection section extends continuously to \(P\) in \(L^1\). At \(M\in\partial P\), it equals the exponential-family projection on the observations whose features lie in the minimal face containing \(M\), relative to the conditioned reference.

Consequently, affine featureless-to-data paths have a well-defined endpoint response even when their natural parameters diverge.

### Route

Finite-dimensional simplex compactness; continuity and strict convexity of relative entropy; continuity of the feasible-fiber optimization problem using polyhedral structure; then facial support and relative-interior exponential representation.

Do **not** claim this unchanged for general bounded features. For uniform reference on \([0,1]\), mean \(M\downarrow0\) forces concentration at \(0\), with no limiting probability density in \(L^1(\nu)\). A general boundary theorem needs a weaker topology and a larger target space.

If actual data can lie on boundary faces, this deserves promotion above analyticity.

---

## 5. Reconstruction CLT as the statistical corollary

For i.i.d. data with interior mean \(M\) and covariance \(\Sigma_\rho\),
\[
\sqrt n\bigl(p(\bar S_n)-p(M)\bigr)
\Longrightarrow J_MZ
\quad\text{in }L^1,
\qquad Z\sim N(0,\Sigma_\rho).
\]

The limit is finite-rank and tangent: first-order sampling fluctuations have no invisible component.

Route: finite-dimensional multivariate CLT plus the Fréchet delta method. Define a measurable fallback when \(\bar S_n\notin\Omega\); interiority makes that event asymptotically negligible.

This is valuable, but less central than explicit response transport. Also, empirical measures need not possess \(\nu\)-densities: formulate the plug-in law as \(p(\bar S_n)\), not automatically as \(R(d_n)\).

---

## Explicit featureless derivatives through order three

Here is a particularly clean statement, avoiding a full cumulant API.

At the reference, set
\[
X=S-m_0,\quad C=E_\nu[X\otimes X],\quad
a=C^{-1}h,\quad \ell=\langle a,X\rangle,
\]
\[
b=C^{-1}E_\nu[X\ell^2],\qquad r=\langle b,X\rangle.
\]
Define
\[
Nf=f-E_\nu f
-\left\langle C^{-1}E_\nu[Xf],X\right\rangle.
\]

Then
\[
\boxed{
p'(0)=[\ell],\qquad
p''(0)=[N(\ell^2)],\qquad
p'''(0)=[N(\ell^3-3\ell r)].
}
\]

For bounded \(F\), writing \(f(s)=E_{Q_{M_s}}F\),
\[
\boxed{
\begin{aligned}
f'(0)&=E_\nu[F\ell],\\
f''(0)&=E_\nu[(NF)\ell^2],\\
f'''(0)&=E_\nu[(NF)(\ell^3-3\ell r)].
\end{aligned}}
\]

These are excellent initial formal targets: short, intrinsic, and their higher-order invisibility is explicit.

For a conventional cumulant presentation, define
\[
c=C^{-1}\!\left(
3\kappa_3^\sharp(a,b)-\kappa_4^\sharp(a,a,a)
\right).
\]
Then
\[
\begin{aligned}
f'(0)&=\kappa_2(F,\ell),\\
f''(0)&=\kappa_3(F,\ell,\ell)-\kappa_2(F,r),\\
f'''(0)&=\kappa_4(F,\ell,\ell,\ell)
-3\kappa_3(F,\ell,r)
+\kappa_2(F,\langle c,X\rangle).
\end{aligned}
\]

Signs above use \(\eta=-\theta\); in particular \(\eta''(0)=-b\).

### Does the existing seabed already give order three?

**Not solely from the names `thirdOp`/`cumulantVec`/`atlasBend`.** Those plausibly provide \(b\), the second inverse-chart derivative, and \(p''\). A third response derivative generally involves fourth-order joint moments.

However, the projected formula
\[
p'''(0)=[N(\ell^3-3\ell r)]
\]
is a shortcut. It uses the existing bend \(b\), cubic score algebra, and regression projection, without separately formalizing the entire fourth-cumulant tensor or \(\theta'''(0)\). One can identify the remaining affine score terms by the mass/moment constraints. This is likely the cleanest next order.

Use `iteratedDerivWithin` on your open \(D\), but provide conversion lemmas to ordinary iterated derivatives at \(0\in D\). Openness removes within-domain ambiguity.

---

## Sanity checks on the landed claims

Nothing described is intrinsically inconsistent, but three qualifications are essential.

### 1. The product normal form is for signed densities

If
\[
U=\{d\in L^1:\text{mass}(d)=1,\ m(d)\in\Omega\},
\]
with no positivity constraint, then \(U\simeq\Omega\times K\) is correct.

If \(U\) means probability densities, the full product is generally false:
\[
\Phi(U)=\{(M,k):p(M)+k\ge0\ \text{a.e.}\}.
\]
The positive cone also generally has empty \(L^1\) interior. State clearly whether the smooth ambient manifold is the signed unit-mass affine space and actual distributions form a constrained subset.

### 2. Normal-form derivatives live on the affine tangent space

For zero-mass \(h\),
\[
D\Phi_d[h]=\bigl(m(h),\,h-J_Mm(h)\bigr),
\]
and
\[
D\Psi_{(M,k)}[u,v]=J_Mu+v.
\]
These are inverse tangent maps. They are not assertions of uniquely determined ambient derivatives on all of \(L^1\) unless an extension has been specified. Relative openness and intrinsic projection matter.

### 3. `invisible_tower` is correct for affine mean paths

For \(s\in D\), openness and smoothness allow bounded linear mass/moment maps to commute with iterated derivatives:
\[
\operatorname{mass}(p^{(k)}(s))=0\quad(k\ge1),
\]
\[
m(p'(s))=h,\qquad m(p^{(k)}(s))=0\quad(k\ge2).
\]
For curved paths, instead \(m(p^{(k)}(t))=M^{(k)}(t)\). The second derivative is not wholly invisible unless the mean acceleration vanishes.

Finally, “featureless maximal entropy” means maximal **relative** entropy with respect to the chosen reference; it is not automatically absolute maximum entropy. Projection uniqueness is uniqueness of laws/a.e. densities, and parameter uniqueness requires the intrinsic gauge.

**Bottom line:** land the explicit global Hessian, then the cubic featureless formula and \(L^1\) Taylor remainder. Those turn the all-orders existence theorem into an actual, observable-uniform response map.