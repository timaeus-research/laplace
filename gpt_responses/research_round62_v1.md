## Recommendation

**Make the next flagship theorem the \(C^2\), \(L^1\)-valued response map, with an explicit Hessian whose values are invisible signed measures.** This unifies second-order transport, curvature, and uniform-in-observable bias.

In parallel, land two comparatively inexpensive structural results: **tangent-space Pythagoras** and the **exact natural-gradient interpretation of the atlas**. The latter gives a particularly beautiful answer to “how do we travel from featureless to observed?”

Throughout, work intrinsically on the identifiable direction space \(V\). Write
\[
T=S-M,\quad C_M=\operatorname{Cov}_{Q_M}(S),\quad
A_M=C_M^{-1},\quad g_M(u,v)=\langle u,A_Mv\rangle.
\]
Thus the reconstruction score is
\[
\ell_{M,u}=\langle A_Mu,T\rangle,\qquad
\operatorname{lin}_{F,M}(u)=E_{Q_M}[F\ell_{M,u}].
\]
Translate these into your existing \(R,\theta,\mathrm{dotJ}\) conventions; do not infer their signs from their names.

The LOC estimates below are incremental, assuming the infrastructure described, not repository-audited estimates.

## 1. Ranked theorem programme

### 1. The reconstruction Hessian is an invisible signed measure

Define the third-cumulant vector
\[
K_M(u,v)=E_{Q_M}[T\,\ell_{M,u}\ell_{M,v}].
\]
Then
\[
D^2q_M[u,v]
=q_M\Bigl(\ell_{M,u}\ell_{M,v}
-g_M(u,v)-\ell_{M,K_M(u,v)}\Bigr).
\tag{1}
\]

The flagship statement is that \(M\mapsto[q_M]\in L^1(\nu)\) is \(C^2\), with this continuous bilinear Hessian. Crucially,
\[
\int D^2q_M[u,v]\,d\nu=0,\qquad
\int S\,D^2q_M[u,v]\,d\nu=0.
\tag{2}
\]
So reconstruction curvature changes neither total mass nor the prescribed moments: **all second-order bending is invisible to the sufficient statistics.**

Let \(N_M\) remove the constant and feature-score components in \(L^2(Q_M)\). Then (1) becomes
\[
D^2q_M[u,v]=q_M N_M(\ell_{M,u}\ell_{M,v}),
\]
whenever the required \(L^2\) products exist.

**Seabed route.**

1. Differentiate \(C_M\) along a mean direction using the score identity.
2. Differentiate \(C_M^{-1}\):
   \[
   D(A_M)[v]u=-A_MK_M(u,v).
   \]
3. Differentiate \(\ell_{M,u}\):
   \[
   D\ell_{M,u}[v]=-g_M(u,v)-\ell_{M,K_M(u,v)}.
   \]
4. Differentiate your existing \(L^1\) derivative by the product rule.
5. Prove operator-norm continuity using compact-uniform integrable envelopes.

Bounded statistics make the envelope step straightforward. Otherwise, explicitly require a local exponential-moment envelope sufficient for the polynomial factors; \(C^1\) alone does not supply it.

**Payoff: signed-measure bias.** For the same localized estimator and tail controls used in your scalar bias schema,
\[
n\bigl(E[\widetilde q_n]-q_M\bigr)\longrightarrow
\beta_M
:=\frac12E_{X\sim D}\!\left[D^2q_M[T(X),T(X)]\right]
\quad\text{in }L^1(\nu).
\tag{3}
\]
Consequently,
\[
\sup_{\|F\|_\infty\le1}
\left|n(E\widetilde G_{F,n}-G_F(M))-\int F\beta_M\,d\nu\right|
\longrightarrow0.
\]
This is genuinely stronger than separately proving every scalar bias limit. Moreover, \(\beta_M\) has zero mass and zero feature moments.

**Expected LOC:** 500–1000 for \(C^2\)/Hessian; another 250–550 for Banach-valued bias.  
**New:** posterior-wide curvature and bias, independent of any chosen observable.

---

### 2. Tangent Pythagoras and the Fisher-dual influence function

At a reconstructed distribution \(Q_M\), take a data score
\[
a\in L^2_0(Q_M),\qquad u=E_{Q_M}[Ta].
\]
Define
\[
P_Ma=\ell_{M,u},\qquad N_Ma=a-P_Ma.
\]
Then \(P_M\) is the orthogonal projection onto the feature-score space, and
\[
\|a\|_2^2=g_M(u,u)+\|N_Ma\|_2^2.
\tag{4}
\]

For \(F\in L^2(Q_M)\),
\[
\psi_{F,M}=P_M(F-E_{Q_M}F),
\]
and
\[
E_{Q_M}[\psi_{F,M}\ell_{M,u}]
=\operatorname{lin}_{F,M}(u).
\tag{5}
\]
Writing \(c_F=\operatorname{Cov}_{Q_M}(S,F)\),
\[
\operatorname{Var}_{Q_M}(\psi_{F,M})
=\langle c_F,C_M^{-1}c_F\rangle
=\|dG_F\|_{g_M^{-1}}^2.
\tag{6}
\]

**Important notation correction:** if \(c_F\) denotes the covariance **vector**, the answer is \(g_M(c_F,c_F)\), not \(g_M^{-1}(c_F,c_F)\). The inverse metric acts on the differential \(dG_F\), a covector.

**Important scope correction:** at arbitrary \(D\), the pullback metric is
\[
a\longmapsto g_M(E_D[Ta],E_D[Ta]).
\tag{7}
\]
It is generally **not** the \(L^2(D)\)-orthogonal visible length. That length uses \(\Gamma_D^\dagger\), not \(C_M^{-1}\). Equality holds under covariance matching, in particular at \(D=Q_M\). Thus the sandwich covariance and the pullback metric are related but distinct objects.

**Seabed route:** prove the score Gram identity \(E[\ell_u\ell_v]=g(u,v)\); derive projection, kernel, orthogonality, then apply it to \(F-EF\).

**Expected LOC:** 200–400.  
**New:** the differential version of KL Pythagoras, plus the correct metric interpretation of influence and sandwich covariance.

---

### 3. The atlas is an exact natural-gradient learning trajectory

Fix the target moment \(M_*\), and define the loss
\[
L(M)=\mathrm{KL}(Q_{M_*}\Vert Q_M).
\]
Then
\[
dL_M[u]=g_M(M-M_*,u),
\qquad
\operatorname{grad}_{g}L(M)=M-M_*.
\tag{8}
\]
Therefore its negative Fisher-gradient flow from \(m_0\) is exactly
\[
M(\tau)=m_0+(1-e^{-\tau})(M_*-m_0).
\tag{9}
\]
This is your straight atlas with the time change \(s=1-e^{-\tau}\).

When finite and differentiable, \(\mathrm{KL}(D\Vert Q_M)\) has the same gradient whenever \(E_DS=M_*\). Using \(Q_{M_*}\) in the primary theorem avoids unnecessary entropy assumptions on \(D\).

Along this flow,
\[
\frac{d}{d\tau}L(M(\tau))
=-g_{M(\tau)}(M(\tau)-M_*,M(\tau)-M_*).
\tag{10}
\]

**Seabed route:** express family KL through the log-partition function; differentiate in mean coordinates; identify the metric gradient; verify the explicit curve and dissipation identity. No ODE existence machinery is needed.

Your affine atlas is also a **mixture-connection geodesic in mean coordinates**, not generally a Fisher–Rao Levi-Civita geodesic, and not generally an affine mixture of reconstructed measures.

For \(\delta=M_*-m_0\),
\[
\kappa(s)=g_{M_s}(\delta,\delta)
\]
is precisely squared Fisher speed. Hence
\[
\mathcal I(M_s)=\int_0^s(s-r)\kappa(r)\,dr
\]
is a **weighted kinetic-energy integral**, not the ordinary energy \(\frac12\int\kappa\), nor squared distance.

**Expected LOC:** 180–350 for gradient/flow/dissipation, excluding a general connection API.  
**New:** a canonical optimization meaning for the entire featureless-to-data response path.

---

### 4. Second-order expectation transport: curvature equals invisible interaction

Along \(M_t=m_0+t\delta\),
\[
\frac{d^2}{dt^2}G_F(M_t)
=b_{F,M_t}(\delta,\delta),
\]
with
\[
b_{F,M}(u,v)
=
E_{Q_M}[(F-G_F(M))\ell_u\ell_v]
-\operatorname{lin}_{F,M}(K_M(u,v)).
\tag{11}
\]
Equivalently,
\[
b_{F,M}(u,v)=E_{Q_M}[N_MF\,\ell_u\ell_v].
\tag{12}
\]
This makes the third-cumulant correction conceptually transparent: it subtracts the feature-visible part of the quadratic score interaction.

Prove the exact second-order transport formula
\[
G_F(M_t)=G_F(m_0)+t\,\operatorname{lin}_{F,m_0}(\delta)
+\int_0^t(t-r)b_{F,M_r}(\delta,\delta)\,dr.
\tag{13}
\]
For a general \(C^2\) response curve, add
\[
\operatorname{lin}_{F,M_t}(M_t'')
\]
to the acceleration.

**Seabed route:** identify your existing bias form with (11), using `thirdOp`/`cubicScore`; differentiate the first transport theorem; apply FTC twice. This can land before rank 1 if the scalar derivative infrastructure is ready.

**Expected LOC:** 150–350.  
**New:** an exact nonlinear response decomposition, not merely a local estimator-bias coefficient.

---

### 5. Invisible information is the squared normal data displacement

Assume \(Q_{m_0}=\nu\), \(D=(1+h)\nu\), \(h\in L^2(\nu)\), \(E_\nu h=0\), and the existing interior hypotheses. Then
\[
R(t)=\frac{t^2}{2}\|N_{m_0}h\|_{L^2(\nu)}^2+o(t^2).
\tag{14}
\]

**Seabed route—no \(C^2\) density theorem required:**

1. Prove
   \[
   \mathrm{KL}((1+th)\nu\Vert\nu)
   =\tfrac12t^2E_\nu h^2+o(t^2).
   \]
   Apply dominated convergence to
   \((1+th)\log(1+th)-th\); \(h\ge-1\) gives a uniform quadratic bound for \(t\le1/2\).
2. Apply landed information Taylor to \(u=E_\nu[Sh]\).
3. Subtract via KL Pythagoras.
4. Use (4).

**Expected LOC:** 180–350.  
**New:** a quantitative local measure of data variation that posterior reconstruction cannot see.

---

### 6. Residual diagnostics, including a tilt-path nonmonotonicity theorem

For \(0<t<1\), under finite-entropy/differentiation hypotheses,
\[
tR'(t)=R(t)+\mathrm{KL}(\nu\Vert D_t)
-\mathrm{KL}(\nu\Vert Q_{M_t}).
\tag{15}
\]

**Seabed route:** separately prove
\[
tA'=A+\mathrm{KL}(\nu\Vert D_t),\qquad
t\mathcal I'=\mathcal I+\mathrm{KL}(\nu\Vert Q_{M_t}),
\]
where \(A=\mathrm{KL}(D_t\Vert\nu)\), then subtract. Keep endpoint claims separate.

Do **not** pursue general monotonicity along exponential data paths: it is false.

A reusable counterexample is uniform \(\nu\) on \(\{0,1,2\}\), feature \(S(x)=x\), and
\[
P_\tau\propto(1,1,e^\tau).
\]
For every finite \(\tau>0\), \(P_\tau\) is outside the family, since \(p_0p_2\ne p_1^2\), so its residual is positive. Yet the residual tends to zero as \(\tau\to\infty\): compare against the family member proportional to
\[
(1,e^{\tau/2},e^\tau),
\]
whose KL divergence from \(P_\tau\) tends to zero. Choose \(D=P_A\) for sufficiently large \(A\); its exponential interpolation is \(P_{At}\), giving a nonmonotone residual on \([0,1]\).

The correct zero-residual statement is: the whole tilt path lies in the family iff \(\log(dD/d\nu)\) is affine in \(S\), under the usual positive-density/interior assumptions.

**Expected LOC:** 150–300 for (15); 300–600 for the counterexample.  
**New:** an exact sign diagnostic and a principled rejection of “exponential interpolation eliminates invisible humps.”

## 2. Which unfinished items now?

- **\(C^2\), \(L^1\)-valued reconstruction:** start now as the flagship.
- **\(L^2\) invisible-information expansion:** land now as a short, independent companion to tangent Pythagoras.
- **Residual derivative diagnostic:** useful, but defer behind transport and geometry unless it is a quick entropy-calculus corollary.

A practical landing order is **tangent geometry → scalar second transport → natural-gradient atlas**, while the \(L^1\) Hessian work proceeds.

## 3. Information-bias coefficient: yes, with the \(n\) placed correctly

Your limit is
\[
n\bigl(E\widetilde{\mathcal I}_n-\mathcal I(M)\bigr)
\longrightarrow
\frac12\operatorname{tr}_V(C_M^{-1}\Gamma_D).
\]
Under \(\Gamma_D=C_M\), the **limit coefficient** is \(\frac12\dim V\); the unscaled bias is
\[
E\widetilde{\mathcal I}_n-\mathcal I(M)
=\frac{\dim V}{2n}+o(n^{-1}).
\]
Use \(\dim V\), not the number of ambient feature coordinates. Retain the localization/extension convention unless boundary control justifies the raw empirical expression.

## 4. Referee-level intrinsic formulation

Let
\[
Z=S-M\in V,\qquad \Gamma_D=E_D[Z\otimes Z],
\]
and regard \(dG_F\in V^*\), \(b_F\in\operatorname{Sym}^2(V^*)\). State the primary results as
\[
\begin{aligned}
n\,\mathrm{Bias}(\widetilde G_F)&\to\tfrac12E_D[b_F(Z,Z)],\\
n\,\mathrm{Cov}(\widetilde G_F,\widetilde G_G)
&\to E_D[dG_F(Z)dG_G(Z)],\\
n\,\mathrm{Bias}(\widetilde{\mathcal I})
&\to\tfrac12E_D[g_M(Z,Z)].
\end{aligned}
\]
These require neither a projection nor a basis. Trace/contraction formulas should be corollaries. Describe \(b_F\) as the Hessian for the **affine mean-coordinate structure**, avoiding confusion with a Levi-Civita Hessian.

The resulting narrative is exceptionally coherent: **first-order motion is visible Fisher projection; second-order bending is invisible; sampling bias averages that bending; and the atlas itself is a natural-gradient learning trajectory.**