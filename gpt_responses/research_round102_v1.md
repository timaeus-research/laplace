## Executive verdict

L2, L4, L5, and L7 are mathematically well targeted. Together they now distinguish three things that should remain separate:

1. **Response geometry:** how posterior expectations change with feature means.
2. **Sampling geometry:** how the data law distributes noise in those means.
3. **Information geometry:** which changes any statistical procedure can distinguish.

The next programme should connect these geometries, not add another layer of atlas terminology.

There are three important corrections to the proposed next steps:

- **Equal response does not mean statistically indistinguishable**, even by procedures using only observed features.
- The proposed minimax scale is inverted: for estimating \(\langle w,m_D\rangle\), the scale is
  \[
  \sqrt{\Sigma_D(w,w)/n},
  \]
  not \(1/\sqrt{n\Sigma_D(w,w)}\).
- **There is a Cauchy–Binet-free route to the finite-configuration uniform regression bound.** A hyperplane-arrangement argument appears particularly suitable: it proves that every positive-weight least-squares fit lies in the convex hull of finitely many interpolating fits.

I would make that last result a serious target rather than defer it indefinitely.

---

# 1. Audit of L

I can audit the mathematics displayed here, but not certify omitted Lean section hypotheses or proof dependencies.

## L2: correct sign, sensible localization, improvable constants

### Sign

The positive mean-coordinate derivative is correct. With your convention
\[
P_\theta\propto e^{-\langle\theta,S\rangle}\nu,
\]
both parameter derivatives carry a minus sign:
\[
D_\theta m=-G,\qquad
D_\theta E_\theta F[v]=-\operatorname{Cov}_\theta(F,\langle v,S\rangle).
\]
Passing to mean coordinates cancels them:
\[
D_m f_F[e]=\langle u_F,e\rangle.
\]

The stated Hessian identification is therefore consistent. In particular, the two inverse-chart directions in
\[
\operatorname{secondResponse}F\,\theta\,(A^{-1}e)\,(A^{-1}e)
\]
do not introduce an extra overall minus sign. The Hessian itself need not be positive.

Useful sanity tests are:

- constant \(F\): derivative and Hessian vanish;
- affine-feature \(F=\langle a,S\rangle+c\): \(f_F\) is affine in mean coordinates, so its Hessian vanishes;
- for this affine case, **reset localization can still introduce bias**. Zero Hessian does not imply zero localized bias.

### The \(\sum_j|u_{F,j}|/\delta^2\) term

This is correct for the displayed sup-norm pairing estimate. Outside the localization ball,
\[
|\langle u_F,z\rangle|
\le a_F\|z\|
\le \frac{a_F}{\delta^2}\|z\|^3,
\qquad
a_F=\sum_j|u_{F,j}|.
\]

A cleaner theorem would first use the actual operator norm
\[
a_F=\|Df_F(m_0)\|_{\mathrm{op}},
\]
and derive the coordinate sum as a corollary. That removes coordinate artifacts without changing the localization machinery.

A Fisher-normalized version is beautiful but is **a different localization theorem**. In the mean-space norm
\[
\|z\|_{G^{-1}}^2=\langle z,G^{-1}z\rangle,
\]
the dual derivative norm is
\[
\sqrt{G(u_F,u_F)}.
\]
For off-model sampling, the analogous data-normalized norm gives derivative size
\[
\sqrt{\Sigma_D(u_F,u_F)}.
\]
Neither is a drop-in replacement: the ball, third moment, Hessian norm, and concentration estimate must all use compatible norms.

**Recommendation:** general operator-norm statement now; covariance-normalized localization later.

### Hypotheses to inspect

Check that the full theorem includes:

- \(m_D=m(\theta_0)\);
- \(n>0\);
- the required joint independence for the third-moment bound, not merely pairwise independence;
- the fact that raw empirical displacements belong to \(W\) almost surely.

The last point explains why an arbitrary retraction \(p\), with no operator-norm bound, can disappear from the sampling constant. It is acting as the identity almost surely, not controlling arbitrary ambient vectors.

Also keep the wording “reset-localised posterior expectation.” An inverse chart evaluated outside its domain is not automatically the genuine empirical entropy projection.

## L4: correct, but singular covariance is not a corner

Positive definiteness is a clean first theorem. It is not automatic from \(D\ll\nu\).

For example, a data law may be concentrated at one feature value lying inside the ambient feature polytope. Its mean is interior, while its data covariance is zero. Boundary-supported laws and low-support empirical laws provide further examples.

Let
\[
N=\ker\Sigma_D,\qquad R=N^\perp.
\]
The correct singular geometry is:

- If \(e\in R\), the optimal squared SNR is
  \[
  \langle e,\Sigma_D^+e\rangle.
  \]
- If \(e\notin R\), some \(u\in N\) has \(\langle u,e\rangle\ne0\): the proposed displacement has a **noiseless linear witness**.

Do not encode the latter using ordinary real division by zero: Lean’s convention will give the wrong semantics.

A particularly clean extended formulation is
\[
\sup_{\Sigma_D(u,u)\le1}\langle u,e\rangle^2
=
\begin{cases}
\langle e,\Sigma_D^+e\rangle,&e\in R,\\
+\infty,&e\notin R.
\end{cases}
\]
It also avoids empty-set problems when \(\Sigma_D=0\).

An essential companion statement is:

> Every differentiable, dominated perturbation through \(D\), described by an \(L^2(D)\) score, has first-order mean displacement in \(R\).

Thus an off-range displacement is not a regular local alternative through \(D\). It generally requires changing support. “Infinite SNR” should not be presented as regular local statistical efficiency.

The existing chamber certificate is correct. `hK : 0 ≤ K` is harmless: an existing remainder constant can always be enlarged to a nonnegative one.

## L5: the right refinement notion

The \(\nu\)-a.e. affine definition is exactly the right notion for entropy projections. It includes:

- redundant coordinates;
- invertible affine reparametrizations;
- genuinely richer feature families;
- irrelevant changes on \(\nu\)-null sets.

Absolute continuity transports these identities to the data and projected laws.

Given your existing extended-valued Pythagorean theorem and finite fine rate, the two ladders are correct. No additional assumption \(KL(D\|\nu)<\infty\) is needed merely to state the residual ladder in \(\mathbb R_{\ge0}^\infty\).

But distinguish two claims:

- The newly acquired increment \(KL(R_T\|R_S)\) is finite under the finite-rate assumptions.
- The residual ladder may read
  \[
  \infty=\infty+\text{finite}.
  \]
  That is a valid identity, but not a finite numerical reduction of residual information.

The affine-predictor Pinsker certificate is especially good: it controls precisely the part of \(F\) not already represented by the coarse features.

For saturation, prove \(R_D=D\) by equality of bounded measurable integrals—or directly by indicator functions—rather than by subtracting extended KL values.

## L7: correct bound; the suggested affinity shortcut is false

Your bound
\[
\operatorname{error}\ge \frac{1-\sqrt{nKL(\mu\|\eta)}}2
\]
is correct.

But
\[
1-\rho^2\le KL/2
\]
is false in general. Take \(\mu=\eta(\,\cdot\mid A)\), with \(\eta(A)=a\). Then
\[
\rho^2=a,\qquad KL(\mu\|\eta)=-\log a.
\]
At \(a=1/2\), the proposed inequality becomes
\[
1/2\le(\log2)/2.
\]

The cheap route to the better constant is **Pinsker on the product laws**, not a stronger affinity inequality:
\[
KL(\mu^{\otimes n}\|\eta^{\otimes n})=nKL(\mu\|\eta).
\]
Since \(0\le\varphi\le1\), apply your bounded-observable Pinsker inequality to \(\varphi-1/2\):
\[
|E_{\mu^n}\varphi-E_{\eta^n}\varphi|
\le\sqrt{nKL(\mu\|\eta)/2}.
\]
Hence
\[
\boxed{\operatorname{error}\ge
\frac{1-\sqrt{nKL(\mu\|\eta)/2}}2.}
\]

This is inexpensive **if product-KL additivity is already accessible**. Otherwise it is a separate measure-theoretic task.

For the chamber story, the present constant is already sufficient to establish the \(n^{-1/2}\) resolution scale. Improve it opportunistically, not at the expense of boundary response calculus.

---

# 2. The central conceptual correction: fibres are not indistinguishability classes

The valid retraction statement is
\[
\mathcal R_S(D)=R_{m_S(D)},\qquad
\mathcal R_S^2=\mathcal R_S,
\]
on the appropriate finite-rate domain. Its fibres are exactly equal-feature-mean classes.

The proposed statistical interpretation is false.

Take
\[
X=\{-1,0,1\},\qquad S(x)=x,
\]
with a full-support reference law. The laws
\[
D_0=\delta_0,\qquad
D_1=\tfrac12\delta_{-1}+\tfrac12\delta_1
\]
have the same response mean. Yet one observation of \(S\) distinguishes them perfectly.

Even retaining only the empirical mean does not rescue the general claim: under \(D_0\) it is always zero; under \(D_1\), the probability of zero tends to zero.

The correct hierarchy is:

- equal **means**: identical population response;
- equal **feature pushforward laws**: indistinguishable from complete feature observations;
- small **data-law KL**: testing obstruction at a specified sample size.

What is both true and deep is the infinitesimal statement:
\[
D\mathcal R_S(D)[h]=0
\quad\Longleftrightarrow\quad
\operatorname{Cov}_D(S,h)=0.
\]
These are response-invisible tangent directions, not statistically invisible directions.

---

# 3. Programme M: seven ranked targets

Sizes below are relative to the seabed you describe, not claims about inspected Mathlib APIs.

## M1. Differentiate the response directly on the space of data laws

**Value: highest. Size: small–medium.**

Define
\[
\Psi_F(D)=E_{R_{m_D}}F.
\]
For bounded \(h\), set \(D_t\propto e^{th}D\). At an interior response,
\[
\boxed{
\frac d{dt}\Psi_F(D_t)\bigg|_0
=
\operatorname{Cov}_D(\langle u_F,S\rangle,h).
}
\]

Thus the data-law influence function is
\[
\operatorname{IF}_{F,D}(x)
=
\langle u_F,S(x)-m_D\rangle.
\]

This identifies, in one theorem:

- the response derivative on data-law tangent directions;
- its kernel;
- its sampling variance;
- the score direction producing the largest response per unit local information.

Indeed,
\[
|\dot\Psi_F|^2
\le
\Sigma_D(u_F,u_F)\operatorname{Var}_D(h),
\]
with equality for \(h\) proportional to \(\operatorname{IF}_{F,D}\).

Also prove the minimum-information lift:
\[
\inf_{\substack{E_Dh=0\\E_D[(S-m_D)h]=e}}E_Dh^2
=
\langle e,\Sigma_D^{-1}e\rangle,
\]
attained by
\[
h_e=\langle\Sigma_D^{-1}e,S-m_D\rangle.
\]

**Proof:** tilted-law differentiation, K5 chain rule, and the orthogonal decomposition \(h=h_e+(h-h_e)\).

This gives L4/L7 their missing variational meaning: the covariance-dual alternative is the **least-information way to realize a prescribed response velocity**.

## M2. A joint nonlinear covariance theorem

**Value: very high. Size: small–medium.**

Unify candidates (i) and (vi). For jointly localized observables,
\[
\boxed{
\operatorname{Cov}(\widehat f_{F,\mathrm{loc}},
                  \widehat f_{H,\mathrm{loc}})
=
\frac{\Sigma_D(u_F,u_H)}n+O(n^{-3/2}).
}
\]
And
\[
\boxed{
E[\langle u,\xi_n\rangle
(\widehat f_{F,\mathrm{loc}}-f_F)]
=
\frac{\Sigma_D(u,u_F)}n+O(n^{-3/2}).
}
\]

There is a useful proof that requires **no fourth-moment estimate**.

Write \(A_F(z)\) for the reset-localized increment and \(\ell_F(z)=\langle u_F,z\rangle\). Let
\[
|\ell_F(z)|\le a_F\|z\|,
\qquad
b_F=\tfrac12\|H_F\|+K_F\delta.
\]
Then globally,
\[
|A_F-\ell_F|\le c_F\|z\|^2,\qquad
|A_F|\le d_F\|z\|,
\]
where
\[
c_F=\max(b_F,a_F/\delta),\qquad
d_F=a_F+b_F\delta.
\]
Consequently,
\[
|A_FA_H-\ell_F\ell_H|
\le(c_Fd_H+a_Fc_H)\|z\|^3.
\]
For a centered displacement law,
\[
\left|\operatorname{Cov}(A_F,A_H)-E[\ell_F\ell_H]\right|
\le
(c_Fd_H+a_Fc_H)M_3+c_Fc_HM_2^2.
\]

Your existing moment estimates turn this into the desired rate. Package a finite family of observables as a covariance matrix only after proving this bilinear statement.

## M3. Uniform finite-configuration regression, without Cauchy–Binet

**Value: very high. Size: medium–large; polyhedral infrastructure is the risk.**

Here is a concrete route.

Choose affine coordinates on the feature hull. Let the finite configuration be \(s_i\in\mathbb R^d\), spanning affinely, and put
\[
a_i=(1,s_i)\in\mathbb R^{d+1}.
\]
For values \(f_i\), the weighted affine least-squares fit \(\beta\) satisfies
\[
\sum_i p_i(a_i\cdot\beta-f_i)a_i=0,\qquad p_i>0.
\]

Consider the hyperplanes
\[
a_i\cdot b=f_i.
\]
Let \(C\) be the closed sign cell containing \(\beta\): impose equality when its residual is zero and the corresponding weak sign inequality otherwise.

**Claim: \(C\) is bounded.**

Otherwise it has a nonzero recession direction \(v\). Thus
\[
(a_i\cdot\beta-f_i)(a_i\cdot v)\ge0
\]
for every \(i\), and \(a_i\cdot v=0\) on zero residuals. Pairing the normal equation with \(v\) gives a sum of nonnegative terms equal to zero. Strict positivity of the weights forces every \(a_i\cdot v=0\). The \(a_i\) span, so \(v=0\), a contradiction.

A bounded polyhedral cell is the convex hull of its vertices. Each vertex is an interpolating fit on an affinely independent \((d+1)\)-point subset. Therefore
\[
\boxed{
\beta(p)\in\operatorname{conv}\{\beta_B:B\text{ an affine basis}\}.
}
\]
In particular,
\[
\|u_F(p)\|\le \max_B\|u_B\|.
\]

This does not provide the volume-sampling weights, but it gives the uniform bound—and more than the bound—without determinants.

For finite-valued features on a general \(X\), reduce \(F\) to its reference-law conditional averages on feature fibres. Exponential tilting preserves these conditional laws.

Then integrate the bounded mean derivative along segments:
\[
\boxed{|f_F(M)-f_F(N)|\le L_F\|M-N\|.}
\]
Use the existing boundary completion to identify the Lipschitz extension with the entropy-projection expectation.

**Do not use closed-graph compactness alone:** singular boundary normal equations have nonunique solutions, so that argument does not establish boundedness.

Also, even a tail estimate \(KL(R_M\|Q_s)\le C(1-s)\) gives only a radial \(1/2\)-Hölder estimate through Pinsker, not Lipschitz continuity.

## M4. Facewise convergence of tangential response derivatives

**Value: very high. Size: medium after M3.**

Let \(M_k\) approach \(M\) in the relative interior of a face \(F\), and let \(W_F\) be its tangent direction space. In the finite-configuration setting, prove
\[
\boxed{
P_{W_F}u_H(M_k)\longrightarrow u_H^F(M).
}
\]

Here \(u_H^F\) is the regression direction for the entropy family restricted to the face.

**Proof route:**

1. Boundary completion gives convergence of the projected laws.
2. M3 bounds the full regression directions.
3. Take a convergent subsequence.
4. Pass the regression normal equations to the limit.
5. Test only with \(v\in W_F\).
6. Positive definiteness of the face covariance identifies the tangential projection uniquely.
7. Uniqueness upgrades subsequential convergence to convergence.

Do **not** demand convergence of the whole ambient regression vector. Normal components can retain approach-dependent information.

This is the genuinely new stratified calculus: the interior differential converges to the intrinsic differential of the limiting face.

## M5. Two-point minimax bounds for posterior expectations

**Value: high. Size: medium after M1.**

First prove a general Le Cam lemma. For a scalar functional with values differing by \(\Delta\),
\[
\boxed{
\max_{i=0,1}E_{D_i^n}|T-\psi(D_i)|
\ge
\frac{\Delta}{2}
\left(1-\sqrt{\frac{nKL(D_1\|D_0)}2}\right).
}
\]
A clipped, randomized test built from \(T\) gives this constant directly. A nearest-endpoint deterministic test loses an avoidable factor of two.

Now take
\[
\psi(D)=E_{R_{m_D}}F,\qquad
\sigma_F^2=\Sigma_D(u_F,u_F)>0,
\]
and choose alternatives
\[
D_t\propto
\exp\!\left(t\,\operatorname{IF}_{F,D}/\sigma_F\right)D.
\]
M1 and L7 give
\[
\psi(D_t)-\psi(D)=t\sigma_F+o(t),
\qquad
KL(D_t\|D)=t^2/2+o(t^2).
\]

At \(t=a/\sqrt n\), for \(0<a<2\),
\[
\liminf_n\sqrt n\,
\inf_T\max_{D'\in\{D,D_{a/\sqrt n}\}}
E_{D'^n}|T-\psi(D')|
\ge
\frac{a\sigma_F}{2}(1-a/2).
\]
Taking \(a=1\) yields \(\sigma_F/4\).

This matches M2’s sampling scale up to constants, without a CLT and without invoking an unproved general efficiency theorem.

## M6. Singular covariance and accessible response directions

**Value: high. Size: medium.**

Formalize the range/kernel version described in the audit, preferably initially by restricting the covariance form to \(N^\perp\), rather than introducing a general matrix pseudoinverse API.

Deliver three statements:

1. finite optimal SNR on the covariance range;
2. noiseless witnesses outside the range;
3. minimum-information lifts exist exactly on the range.

This also makes M1’s variational theorem valid for singular data laws. It is particularly relevant to support changes and boundary geometry, not merely an algebraic completion.

## M7. Refinement innovations: a local orthogonal information ladder

**Value: high. Size: medium–large.**

The finite global telescoping ladder is worth doing, but mostly as a corollary. The more substantial new theorem is its infinitesimal form.

Let \(D\) be an interior member of the coarsest family, hence of every finer family. In \(L^2_0(D)\), let
\[
V_0\subset V_1\subset\cdots\subset V_K
\]
be the centered feature spans, with orthogonal projections \(P_k\).

For bounded score \(h\), put \(D_t\propto e^{th}D\), and let \(R_k(t)\) be its level-\(k\) response. Prove
\[
\boxed{
\frac{KL(R_{k+1}(t)\|R_k(t))}{t^2}
\longrightarrow
\frac12\|(P_{k+1}-P_k)(h-E_Dh)\|_{L^2(D)}^2.
}
\]

The increments are orthogonal:
\[
\|P_Kh_0\|_2^2-\|P_0h_0\|_2^2
=
\sum_k\|(P_{k+1}-P_k)h_0\|_2^2.
\]

This says exactly which tangent information each refinement adds. The observable counterpart is
\[
D\Psi_{F,k}[h]
=
\langle P_k(F-E_DF),h-E_Dh\rangle_{L^2(D)}.
\]

The common-model base point is essential. Away from it, different levels regress under different projected laws; the simple orthogonal-projection story does not automatically survive.

---

# 4. What to do cheaply, and what to skip

### Cheap companions

- Prove transitivity of `Refines`, if absent.
- Prove idempotence of the response projection on its domain.
- Prove saturated finite-family reconstruction \(R_D=D\).
- Telescope the global ladder. With \(R_0=\nu\) and \(R_K=D\),
  \[
  KL(D\|\nu)=\sum_{k<K}KL(R_{k+1}\|R_k).
  \]
  Here \(\nu\) must be the probability reference law, or \(R_0\) its normalized version.
- Add the sharper testing constant if product-KL additivity is inexpensive.

### L3: skip a translation-only module

The derivative
\[
\frac d{ds}KL(D\|Q_s)=-(1-s)\kappa(s)
\]
is worth adding to the existing atlas theory on \(s<1\).

The affine-residual tail certificate is also genuinely useful, but its left side must subtract the predictor’s changing mean:
\[
\left|
E_{R_M}F-E_{Q_s}F
-\langle a,M-M_s\rangle
\right|^2
\le
2L^2\,KL(R_M\|Q_s).
\]
Unlike the refinement theorem, the two laws do **not** have equal coarse means.

Do not spend a module merely renaming `atlasCurv` as `journeyEnergy`.

### Skip these claims or routes

- Mean-response fibres as statistical indistinguishability classes.
- A compactness argument for uniform regression that ignores singular normal equations.
- A Lipschitz conclusion from a squared Pinsker tail estimate.
- Global monotonicity of observable sampling variance under refinement away from a common-model base point.

---

## Recommended implementation order

For throughput:
\[
\boxed{\text{M1}\;\to\;\text{M2}\;\to\;\text{M5}}
\]
while developing
\[
\boxed{\text{M3}\;\to\;\text{M4}}
\]
as the geometric workstream. Then M6 and M7.

The resulting mathematical story would be unusually complete:

> A data-law perturbation has a least-information response velocity; posterior observables have explicit influence functions and nonlinear sampling covariance; finite response maps remain Lipschitz up to the polytope boundary; their derivatives descend to facewise calculus; and the same variance governing empirical fluctuations supplies an unavoidable minimax resolution scale.

That is substantially more than packaging—and directly addresses the journey from the reference law to actual data, including what changes, what remains invisible to the chosen response, and what cannot be resolved from finite samples.