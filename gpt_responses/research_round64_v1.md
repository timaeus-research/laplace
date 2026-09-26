## 1. What remains deepest: a global visible–invisible normal form

The closing theorem has essentially settled the **first- and second-order local response geometry**. The strongest next move is not another Taylor coefficient: it is to turn the response map into a **global coordinate decomposition of data space**, then identify its information geometry.

I would rank four targets.

### Rank 1 — Global normal form of the response retraction, with smooth curved-path transport

Let
\[
\mathcal H=\{d\in L^1(\nu):\textstyle\int d\,d\nu=1\},
\qquad
K=\{h:\textstyle\int h=0,\ m(h)=0\}.
\]
Let \(\Omega\) be your established open response domain, relative to the affine moment space, and put
\[
U=\{d\in\mathcal H:m(d)\in\Omega\},\qquad p(M)=[q_M].
\]

**Theorem.** The maps
\[
\Phi(d)=\bigl(m(d),\,d-p(m(d))\bigr),\qquad
\Phi^{-1}(M,k)=p(M)+k
\]
give a global \(C^1\) diffeomorphism
\[
U\;\simeq\;\Omega\times K.
\]
If \(p\) is \(C^\infty\), this is a \(C^\infty\) diffeomorphism. In these coordinates,
\[
R(M,k)=(M,0).
\]

This says precisely: **the response manifold is a global section, and every data perturbation has response coordinates plus an exactly invisible residual**. For actual densities, positivity cuts out the fibre
\[
k\in K,\qquad p(M)+k\ge0.
\]
Thus the signed ambient space trivializes globally; the positive-density region has additional fibrewise inequalities.

The accompanying second-order theorem is
\[
D^2R_d[h,k]
   =D^2p_{m(d)}[\bar m(h),\bar m(k)],
\]
where \(\bar m\) denotes moment directions in reduced coordinates. Along any \(C^2\), constant-mass path,
\[
\frac{d^2}{dt^2}p(m(d_t))
 =
 H_{M_t}[\dot M_t,\dot M_t]+J_{M_t}\ddot M_t.
\]
Consequently,
\[
\frac{d^2}{dt^2}E_{Q_{M_t}}F
 =
 b_{F,M_t}(\dot M_t,\dot M_t)
 +\operatorname{lin}_{F,M_t}(\ddot M_t).
\]

The first term has zero mass and zero moment; the second carries exactly the response acceleration. This is the clean separation between **bending of the response family** and **acceleration of the data’s response coordinates**.

**Route.** The \(C^1\) normal form is mostly assembly from `DataRetraction`, \(m\circ p=\mathrm{id}\), and continuity of the derivative. Establish \(p\in C^2\) or \(C^\infty\) by the bootstrap below, then use ordinary Fréchet chain rules. This is more central than all-orders formulas considered in isolation.

---

### Rank 2 — Variational dual foliation: exact KL splitting and Fisher orthogonality

For every probability density \(d\) with response \(M\), and every family member \(q_N\),
\[
\boxed{\quad
\mathrm{KL}(d\|q_N)
 =
 \mathrm{KL}(d\|q_M)+\mathrm{KL}(q_M\|q_N).
\quad}
\]
State this under your existing finite-KL/integrability hypotheses, or formulate carefully in extended nonnegative reals.

It gives simultaneously:

* \(q_M\) is the unique minimizer of \(Q\mapsto\mathrm{KL}(d\|Q)\) over the family;
* \(q_M\) is the unique minimizer of \(d'\mapsto\mathrm{KL}(d'\|\nu)\) among densities with moment \(M\);
* with \(\mathcal I(M)=\mathrm{KL}(q_M\|\nu)\),
  \[
  \mathrm{KL}(d\|\nu)=\mathcal I(M)+\mathrm{KL}(d\|q_M).
  \]

Thus visible information is the minimum information needed to produce the response; the residual is exactly the extra information in the data.

In reduced natural coordinates, with log-partition function \(\psi\),
\[
\mathrm{KL}(q_M\|q_N)
 =B_\psi(\theta_N,\theta_M)
 =B_{\psi^*}(M,N).
\]
Writing the arguments explicitly avoids the common reversal error.

**Route.** Integrate the affine log-density ratio:
\[
\log(q_M/q_N)
 =\langle\theta_M-\theta_N,T\rangle-\psi(\theta_M)+\psi(\theta_N).
\]
Its expectation under \(d\) equals its expectation under \(q_M\). Your existing `responseProjection_spec` may already contain the substantive KL identity; inspect before adding another theorem.

The genuinely useful geometric addition is the fibre/section orthogonality. At \(q_M\), equip suitable density tangents with
\[
\langle h,k\rangle_{q_M}=\int hk/q_M\,d\nu.
\]
Then
\[
J_Mu=q_M\ell_{M,u},\qquad
\langle J_Mu,k\rangle_{q_M}=0\quad(k\in K),
\]
and
\[
\langle J_Mu,J_Mv\rangle_{q_M}=g_M(u,v).
\]
Hence \(DR_{q_M}\) is the Fisher-orthogonal projection onto the family tangent space.

**Important limit:** this is not generally a Fisher Riemannian submersion at arbitrary data \(d\). The data Fisher metric uses \(d\), whereas your reconstruction derivative uses \(q_{m(d)}\). Away from the section, the two covariance geometries differ.

Also distinguish:

* response coordinates preserve mixtures:
  \[
  m(R((1-t)d_0+td_1))=(1-t)m(d_0)+tm(d_1);
  \]
* reconstructed densities generally do **not** preserve ambient mixtures.

The family is e-flat; fixed-moment fibres are mixture-flat. Say which KL minimization you mean rather than relying on the ambiguous phrase “e-nearest.”

---

### Rank 3 — The smooth invisible tower, obtained without a higher-order inverse theorem

Prove the response section is \(C^\infty\), then provide its recursive jets along affine response paths.

This upgrades “mapping expectations across data space” from two derivatives to a complete local response calculus. It also makes every higher nonlinear correction exactly moment-invisible.

The economical route is **smooth bootstrap from the already established first derivative**, not explicit differentiation of a high-order inverse-function theorem. Details below.

I would target \(C^\infty\) first. Analyticity is stronger, but adds a separate analytic inverse/ODE infrastructure obligation; a smooth bootstrap alone does not prove it.

---

### Rank 4 — Visible information as a sampling cost

For iid \(X_i\sim\nu\), with reduced empirical moment \(\widehat M_n\), Chernoff gives
\[
\Pr\!\left(
 \langle\theta,\widehat M_n\rangle\ge\langle\theta,M\rangle
\right)
\le
\exp\{-n(\langle\theta,M\rangle-\psi(\theta))\},
\]
assuming \(\psi(0)=0\).

Choosing \(\theta=\theta(M)\) gives
\[
\Pr\!\left(
 \langle\theta(M),\widehat M_n\rangle
 \ge\langle\theta(M),M\rangle
\right)\le e^{-n\mathcal I(M)}.
\]

This is an excellent finite-sample bridge: **visible information is the exponential cost of producing the response from the featureless law**.

But the half-space bound alone does not establish that \(\mathcal I\) is the full Cramér rate. That additionally needs lower bounds, typically by exponential change of measure plus an LLN, and the appropriate global upper-bound argument. A reconstruction-law LDP also needs care at boundary empirical moments, where your interior reconstruction may not exist.

I would do the elementary Chernoff theorem now; defer the full LDP and CLT until the analytic geometry above is consolidated. I cannot certify Mathlib’s current CLT coverage from the supplied inventory.

## 2. Exact all-orders recursions

Use reduced sufficient statistics \(T\in V\), removing affine redundancies. Write
\[
q_\theta(x)=\exp(\langle\theta,T(x)\rangle-\psi(\theta)),
\qquad
\mu(\theta)=\nabla\psi(\theta).
\]
Along the affine response path
\[
\mu_s=\mu_0+s\delta,\qquad \mu(\theta_s)=\mu_s,
\]
put \(v_j=\theta_s^{(j)}\), and let \(A_s=D^2\psi(\theta_s)\).

Define vector-valued cumulant contractions \(K_r\) by
\[
\langle K_r[a_1,\ldots,a_r],b\rangle
 =
D^{r+1}\psi(\theta_s)[a_1,\ldots,a_r,b].
\]
Thus \(K_1=A_s\).

### Natural-parameter recursion

For \(k\ge1\), the set-partition form of Faà di Bruno gives
\[
\mathbf1_{\{k=1\}}\delta
 =
\sum_{\pi\in\operatorname{Part}(\{1,\ldots,k\})}
K_{|\pi|}
   [v_{|B_1|},\ldots,v_{|B_{|\pi|}|}].
\]
The single-block term is \(A_sv_k\). Therefore
\[
v_1=A_s^{-1}\delta,
\]
and for \(k\ge2\),
\[
\boxed{
v_k=-A_s^{-1}
 \sum_{\substack{\pi\in\operatorname{Part}([k])\\|\pi|\ge2}}
 K_{|\pi|}[v_{|B_1|},\ldots,v_{|B_{|\pi|}|}].
}
\]
Every derivative on the right has order less than \(k\).

In particular,
\[
v_2=-A_s^{-1}K_2[v_1,v_1],
\]
\[
v_3=-A_s^{-1}
 \bigl(3K_2[v_1,v_2]+K_3[v_1,v_1,v_1]\bigr).
\]

### Density recursion

Let \(a_j=\partial_s^j\log q_{\theta_s}\). Then
\[
a_1=\langle v_1,T-\mu_s\rangle=\ell_s,
\]
and, for \(j\ge2\),
\[
\boxed{
a_j=\langle v_j,T-\mu_s\rangle
 -(j-1)\langle\delta,v_{j-1}\rangle.
}
\]
This simplification uses precisely that \(\mu_s\) is affine.

Define
\[
P_0=1,\qquad P_{k+1}=\partial_sP_k+\ell_sP_k.
\]
Then
\[
\partial_s^kq_{\theta_s}=q_{\theta_s}P_k.
\]
Equivalently, \(P_k\) is the complete exponential Bell polynomial in \(a_1,\ldots,a_k\):
\[
P_1=a_1,\quad
P_2=a_1^2+a_2,\quad
P_3=a_1^3+3a_1a_2+a_3.
\]

In particular,
\[
P_2
 =\ell_s^2-\langle\delta,v_1\rangle
   -\langle A_s^{-1}K_2[v_1,v_1],T-\mu_s\rangle
 =N_s(\ell_s^2).
\]

Once differentiation under the bounded moment functionals is justified,
\[
E_{Q_s}P_k=0\quad(k\ge1),\qquad
E_{Q_s}[TP_k]=0\quad(k\ge2).
\]

### Existing first rungs

Up to your coordinate conventions:

* `chartDerivEquiv`: the invertible covariance derivative and its inverse;
* `atlasVel`: \(v_1=A^{-1}\delta\);
* `thirdOp`/`cumulantVec`: the third-cumulant contraction \(K_2[v_1,v_1]\);
* `atlasBend`: \(v_2=-A^{-1}K_2[v_1,v_1]\);
* `atlasHess`: \(qP_2=qN(\ell^2)\).

### Cheapest regularity proof

You already have
\[
\theta'(s)=A(\theta(s))^{-1}\delta.
\]
If the covariance field is \(C^\infty\), inversion on invertible operators makes the right-hand vector field \(C^\infty\). Starting from \(C^1\), inductively:
\[
\theta\in C^r
\Longrightarrow \theta'\in C^r
\Longrightarrow \theta\in C^{r+1}.
\]

The same argument works multivariately from
\[
D\theta(M)=A(\theta(M))^{-1}.
\]
No higher inverse-function derivatives are needed. The recursion organizes the resulting derivatives; it does not by itself replace the regularity proof.

Finally prove \(\theta\mapsto[q_\theta]\) is \(C^\infty\) into \(L^1\). With bounded statistics, local domination is straightforward. This makes invisibility follow by applying continuous mass/moment functionals to \(L^1\) derivatives.

## 3. Sanity checks

1. **Signed base points are legitimate.** On \(U\subset\mathcal H\), reconstruction only uses the moment. A base point \(d_0\) need not be nonnegative. Interior response is enough for the local differential theorem.

2. **Do not state the identities on all \(L^1\).** The correct common domain is the fixed-mass, interior-response set. There,
   \[
   mR=m,\qquad R^2=R.
   \]
   Outside it, the moment may violate the family’s affine constraints or leave the chart domain.

3. **Derivative assertions belong to zero-mass tangents.**
   \[
   \ker DR_d=\{h\in T\mathcal H:m(h)=0\}.
   \]
   The supplied proof that \(m(h)\in V\) is exactly what makes projected-moment zero equivalent to full-moment zero. On unrestricted ambient \(L^1\), that equivalence need not hold.

4. **Clarify the norm-bound notation.** For a density tangent \(h\), the bound is
   \[
   \|DR_dh\|_1\le
   \sqrt{g_M(\bar m(h),\bar m(h))}.
   \]
   Writing \(\pi h\) requires an explicitly defined shorthand; \(h\) itself is not a moment vector.

5. **Uniform observable bias really is \(L^1\) bias** if the supremum ranges over all bounded measurable observables and the random densities admit the stated Bochner expectations. The duality is
   \[
   \|f\|_1=\sup_{\|F\|_\infty\le1}\left|\int Ff\right|.
   \]
   If “total variation distance” uses the probability convention, remember its factor \(1/2\).

6. **Invisible bending is not automatically Levi-Civita curvature.** Your Hessian is the second derivative in the ambient mixture-affine \(L^1\) coordinates. Calling it Fisher-Riemannian curvature would require an additional connection calculation.

Subject to these domain and terminology qualifications, the landed statements sound coherent. The most beautiful next theorem is the **global visible–invisible normal form**, coupled with exact KL splitting—not a longer closing package, but a structural explanation of why the whole response calculus works.