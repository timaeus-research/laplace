The architecture is now complete **as a map of the subject**. The most important correction is that entropy-graph convergence implies TV convergence, but the converse is false in general—even for a bounded, two-dimensional sufficient statistic. The most valuable small addition is \(C^1\); the most valuable probabilistic addition is the reconstruction-bias theorem, which needs no CLT.

## 1. The statement at the top of the note

Here is the version I would use. Write \(H\) for the centred moment map, \(M_0=E_\nu T\), \(g\) for the response-coordinate Fisher metric, and \(d_{\mathrm{TV}}=\frac12\|\cdot\|_1\). Assume the standing bounded-feature, minimality and probability-reference conventions.

> **Reconstruction across the response domain.** The minimum-relative-entropy reconstruction \(M\mapsto\Pi(M)\) maps admissible responses back to probability laws, starting at the reference law at its maximum-relative-entropy response. On the relative interior it has an \(L^1\) differential given by scores, with moment map as a left inverse and regression as its tangent projection; its normal second response, compact-uniform Taylor expansions and dual affine geometries describe the nonlinear departure from this tangent approximation. For every finite-rate response, reconstruction separates the information in a data law into resolved information and residual information, while radial transport from the reference response accounts for the resolved information through Fisher energy. Reconstruction extends to finite-rate boundary responses radially, and globally its change in total variation is controlled by the Jensen gap of the rate function; in particular it is continuous for the entropy-graph topology, not merely along interior paths. Finally, increasing the information resolution produces compatible reconstructions and an exact additive tower of resolved and residual information:
> \[
> Dp_M[u]=[q_M\ell_{M,u}],\qquad
> H\,Dp_M=\mathrm{id}_{\mathbb V},\qquad
> P_M:=Dp_MH,\quad P_M^2=P_M.
> \tag{1}
> \]
> \[
> \mathrm{KL}(D\|\nu)
> =\mathcal I(M)+\mathrm{KL}(D\|\Pi(M)),
> \qquad H(D)=M.
> \tag{2}
> \]
> \[
> \mathcal I(M)
> =\int_0^1(1-t)\,g_{M_t}(M-M_0,M-M_0)\,dt,
> \quad M_t=M_0+t(M-M_0);
> \qquad
> 2d_{\mathrm{TV}}(\Pi(\gamma_0),\Pi(\gamma_1))
> \le \int_0^1\sqrt{g_{\gamma_t}(\dot\gamma_t,\dot\gamma_t)}\,dt.
> \tag{3}
> \]
> \[
> \|r_A-r_B\|_{L^1(\nu)}^2
> \le \frac{2}{ab}
> \left[a\mathcal I(A)+b\mathcal I(B)-\mathcal I(aA+bB)\right],
> \qquad a,b>0,\quad a+b=1.
> \tag{4}
> \]
> \[
> \begin{aligned}
> \mathrm{KL}(D\|\Pi_c)
> &=\mathrm{KL}(D\|\Pi_f)+\mathrm{KL}(\Pi_f\|\Pi_c),\\
> \mathcal I_f&=\mathcal I_c+\mathrm{KL}(\Pi_f\|\Pi_c).
> \end{aligned}
> \tag{5}
> \]

Here (2) and (5) carry the standing finite-information hypotheses, and the length inequality initially concerns admissible interior piecewise-\(C^1\) curves. Its boundary version follows by endpoint limits when those limits and the length integral exist. The radial integral in (3) is an improper integral at a boundary endpoint.

### What is still missing or needs careful wording?

* **Do not call the established \(L^1\) reconstruction \(C^1\) yet.** “Differentiable with regression differential” is exactly right.
* **Do not advertise an \(L^1\)-valued second Fréchet derivative yet.** The pointwise normal Hessian and uniform second-order expansion are already substantial, but are not by themselves a \(C^2\) theorem.
* Make the TV convention explicit: your proved integral estimate controls **twice** the usual probability-theory TV distance.
* The arbitrary-curve length assertion in (3) is a small extension if only the radial version has landed.
* Define the entropy-graph topology explicitly as the topology induced by
  \[
  M\longmapsto (M,\mathcal I(M))
  \]
  on the finite-rate domain. Otherwise readers may hear “ordinary continuity on the finite-rate domain,” which is stronger and generally wrong.

### Topology or modulus?

**State both, with the modulus primary.** More precisely, call (4) a *square-root Jensen-gap modulus*, rather than simply a Lipschitz estimate. The continuity theorem is its qualitative global consequence.

For \(M_i\to M_*\) and \(\mathcal I(M_i)\to\mathcal I(M_*)<\infty\), lower semicontinuity at the mixed response makes the Jensen gap tend to zero. This is precisely why the entropy-graph topology is natural.

### The converse is false

TV convergence gives convergence of bounded moments and
\[
\mathcal I(M_*)\le \liminf_i\mathcal I(M_i),
\]
but not the reverse inequality. Even convergence of
\(\mathrm{KL}(\Pi(M_*)\|\Pi(M_i))\) to zero does not repair this.

Here is a concrete bounded-feature mechanism. Take a countable space with
\[
T(0)=(0,0),\qquad T(n)=(s_n,s_n^2),\qquad s_n=2^{-n},
\]
and reference masses
\[
\nu(n)=e^{-A_n},\qquad A_n=2^{n^2},\qquad
\nu(0)=p_0:=1-\sum_{n\ge1}e^{-A_n}>0.
\]
Use exponential-family parameters
\[
\theta_n=(2t_ns_n,-t_n),
\qquad
t_n=\frac{A_n-\log A_n}{s_n^2}.
\]
The unnormalised tilted mass at \(n\) is \(1/A_n\); fixed nonzero atoms are suppressed, and later atoms remain negligible. Thus, with \(Q_n\) the corresponding exponential tilt,
\[
Q_n\longrightarrow\delta_0 \quad\text{in TV},
\]
whereas
\[
\mathrm{KL}(Q_n\|\nu)
\longrightarrow
\log(1/p_0)+1/p_0
>
\mathrm{KL}(\delta_0\|\nu).
\]
Each \(Q_n\) is the reconstruction of its own mean, and \(\delta_0\) is the finite-rate reconstruction at response \(0\). Moreover,
\[
\mathrm{KL}(\delta_0\|Q_n)=\log\!\frac{Z_n}{p_0}\longrightarrow0.
\]
The vanishing mass at \(n\) carries a nonvanishing entropy contribution.

The clean positive replacement is:

> **If the limiting response is interior, TV convergence of reconstructions implies rate convergence**, because bounded features give moment convergence and \(\mathcal I\) is continuous on the relative interior.

More generally, the converse holds under uniform integrability of the entropy densities \(q_i\log q_i\). TV alone does not supply it.

## 2. \(C^1\): yes, land it now

Your argument is right. Write the estimate in a form that visibly controls the operator norm:
\[
\begin{aligned}
\|Dp_M-Dp_{M'}\|_{\mathrm{op}}
\le {}&
\left(\sup_{\|u\|\le1}\|\ell_{M,u}\|_\infty\right)
\|q_M-q_{M'}\|_1\\
&+\sup_{\|u\|\le1}
\|\ell_{M,u}-\ell_{M',u}\|_\infty .
\end{aligned}
\]

The second term has coefficient \(1\) because \(\int q_{M'}\,d\nu=1\). If
\(\ell_{M,u}(x)=\langle R_Mu,T(x)-M\rangle\) and \(\|T\|_\infty\le B\), then, up to your fixed coordinate norm constants,
\[
\sup_{\|u\|\le1}\|\ell_{M,u}-\ell_{M',u}\|_\infty
\le
(B+\|M\|)\|R_M-R_{M'}\|
+\|R_{M'}\|\,\|M-M'\|.
\]

The main pitfalls are bookkeeping:

1. **Take the supremum over unit \(u\).** A fixed-direction estimate is not operator-norm continuity.
2. Use an essential supremum unless you have selected canonical everywhere-defined interior densities and scores.
3. Work in a fixed response tangent space \(\mathbb V\), using affine coordinates on \(\operatorname{ri}K\).
4. Obtain the constants on a small compact neighbourhood contained in the relative interior.
5. If the derivative theorem is currently only for \(z\mapsto p(M+z)\) at zero, include the translation step connecting it to the derivative field of the charted reconstruction map.

**Yes, \(C^1\) is worth stating separately.** It turns a collection of derivatives into a genuine differential retraction and makes path calculus systematic. It is also a useful checkpoint for the \(L^1\) infrastructure.

### A less circular route to \(C^2\)

Do not wait for \(C^2\) and then polarise. Differentiate the score directly.

Once \(p\) is \(C^1\), expectations of bounded functions are \(C^1\), since integration against such a function is a continuous linear functional on \(L^1\). Consequently the covariance matrix is \(C^1\), and so is its inverse \(R\). The score derivative is
\[
D_M\ell_{M,u}[w]
=
-E_{Q_M}[\ell_{M,u}\ell_{M,w}]
-B_M(\ell_{M,u}\ell_{M,w}).
\]
Differentiating \(q_M\ell_{M,u}\) therefore gives
\[
D^2p_M[u,w]
=
\big[q_MN_M(\ell_{M,u}\ell_{M,w})\big],
\]
where \(N_M f=f-E_{Q_M}f-B_Mf\).

This proves the mixed formula **while proving differentiability of \(Dp\)**. Its continuity then follows from the same local bounded-score and \(L^1\)-continuity estimates. Your Peano theorem becomes an independent compatibility check, not the logical bridge to \(C^2\).

## 3. All-orders prototype: choose (a), but unnormalised

The single prototype I would choose is:

> For bounded measurable \(T\) and bounded measurable \(\phi\), the weighted Laplace transform
> \[
> L_\phi(\theta)=\int \phi(x)e^{\langle\theta,T(x)\rangle}\,d\nu(x)
> \]
> is `ContDiff ℝ ⊤`, with
> \[
> DL_\phi(\theta)[v]=L_{\phi\langle v,T\rangle}(\theta).
> \]

Why this one:

* On bounded parameter neighbourhoods, all differentiated integrands have immediate integrable domination.
* Differentiation stays within the same class of bounded multipliers.
* There is no normalisation, inverse covariance, response chart or cumulant bookkeeping.
* \(E_{P_\theta}\phi=L_\phi(\theta)/L_1(\theta)\) follows by division by a positive smooth function.
* The smooth mean map and smooth IFT then provide smooth response coordinates on the minimal response space.

For an induction using `contDiff_succ_iff_fderiv`, strengthen the induction hypothesis to **all bounded multipliers \(\phi\)**. The implementation issue to test is assembling the coordinate derivatives into a smooth continuous-linear-map-valued derivative field. Finite dimensionality makes this routine mathematically, but it is exactly the relevant Lean cost.

This prototype does not by itself prove all-orders **\(L^1\)-valued** smoothness; that needs the corresponding exponential-density map into \(L^1\). But it cleanly tests the main integration and derivative-bundling machinery. I would not begin with response-line recursions: those expose the complicated coefficients before establishing the smoothness infrastructure that explains them.

## 4. Low-cost additions, and reconstruction bias

### First: make orthogonality explicit

For centred \(g\in L^2(Q_M)\), the regression identity should be stated as
\[
\langle g-B_Mg,\ell_{M,u}\rangle_{L^2(Q_M)}=0
\qquad\text{for every }u.
\]
Thus \(B_M\) is the orthogonal projection onto the score space. In particular,
\[
\|g\|_2^2=\|B_Mg\|_2^2+\|g-B_Mg\|_2^2.
\]

This supplies the Hilbert-space meaning behind the tangent retraction and normal Hessian. It is a particularly good beauty-to-proof-cost addition. Be explicit that this is \(B_M\) on \(L^2(Q_M)\), not an assertion of orthogonality for \(P_M\) in unweighted \(L^2(\nu)\).

### Second: promote speed control to length control

For an interior \(C^1\) response curve,
\[
\left\|\frac{d}{dt}q_{\gamma_t}\right\|_1
=
E_{Q_{\gamma_t}}|\ell_{\gamma_t,\dot\gamma_t}|
\le
\sqrt{g_{\gamma_t}(\dot\gamma_t,\dot\gamma_t)}.
\]
Integrating proves the length inequality in (3). Once \(C^1\) is available, this is a natural short theorem. It turns a pointwise speed estimate into a global geometric statement.

### Third: the reconstruction-bias theorem is reachable

Let \(X_1,X_2,\dots\) be iid from the **data law** \(D\), let
\[
\widehat M_n=\frac1n\sum_{k=1}^nT(X_k),\qquad
M=E_DT\in\operatorname{ri}K,\qquad
\Gamma=\operatorname{Cov}_D(T),
\]
and take bounded \(F\). Put
\[
G(M')=E_{\Pi(M')}F.
\]
Then the target statement is
\[
E\,G(\widehat M_n)
=
G(M)+\frac{1}{2n}\sum_{i,j}\Gamma_{ij}\,
b_F[e_i,e_j]+o(n^{-1}),
\]
where
\[
b_F[u,w]
=
E_{\Pi(M)}
\!\left[F\,N_M(\ell_{M,u}\ell_{M,w})\right].
\]

Two qualifications matter.

**Definition off the interior.** If reconstruction is not defined for every empirical response, define \(G\) using any bounded measurable fallback outside a fixed interior neighbourhood of \(M\). The expansion is independent of that choice under the tail estimate below. Do not silently assume every empirical response has finite rate.

**Chebyshev alone is insufficient.** It gives only
\(\Pr(\widehat M_n\notin U)=O(1/n)\), which can alter the coefficient of \(1/n\). One needs an \(o(1/n)\) exceptional contribution, not merely \(O(1/n)\).

Under your bounded-feature assumptions, the cheapest route may be the fourth-moment estimate rather than Hoeffding:
\[
E\|\widehat M_n-M\|^4=O(n^{-2}).
\]
It follows by expanding centred iid sums coordinatewise: only paired indices and fourfold repeated indices survive.

Let \(h_n=\widehat M_n-M\). The local expansion is
\[
G(M+h)=G(M)+a_F[h]+\tfrac12b_F[h,h]+r(h),
\qquad r(h)=o(\|h\|^2).
\]
Now:

1. \(Eh_n=0\), so the linear contribution vanishes.
2. \(E[h_n\otimes h_n]=\Gamma/n\), giving the stated quadratic coefficient.
3. For any \(\varepsilon>0\), choose \(\delta\) so that
   \(|r(h)|\le\varepsilon\|h\|^2\) for \(\|h\|\le\delta\). Its expectation there is at most
   \(\varepsilon\,\operatorname{tr}\Gamma/n\).
4. On \(\|h_n\|>\delta\), bounded features, bounded \(G\), and
   \[
   \Pr(\|h_n\|>\delta)\le \delta^{-4}E\|h_n\|^4=O(n^{-2})
   \]
   make the entire exceptional contribution \(O(n^{-2})\).
5. Let \(\varepsilon\downarrow0\).

So this needs **no CLT, no \(C^2\) theorem, and no all-orders development**. Your uniform observable Peano theorem already supplies the essential local input.

With only finite second moments, a version is still possible using uniform integrability of \(n\|h_n\|^2\), established by truncating iid summands; but that is a more expensive proof than exploiting bounded features. The variance identity plus one Chebyshev application is not enough.

**Cost:** moderate and concentrated in reusable probability lemmas—empirical covariance and fourth-moment bounds. The geometric part is already paid for.

My order would now be: **\(C^1\); explicit orthogonality and path length; weighted-Laplace smoothness prototype; reconstruction bias.** The bias theorem is the strongest new interpretation: sampling covariance is contracted with the reconstruction’s normal curvature to produce a systematic observable drift.