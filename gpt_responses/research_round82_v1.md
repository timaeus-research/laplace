## Executive answer

The best next step is **normal-cone fibre uniqueness**, but its engine is a different fixed-shift lemma from the one suggested in Q1(a). No estimate involving
\(\|a_n\|^2e^{-\operatorname{gap}(a_n)}\) is needed.

Three distinctions matter:

1. **Uniqueness is easier than accessibility.** A normal-translation argument can identify two existing completion points without producing either point.
2. **Accessibility need not be ray accessibility in higher codimension.** This failure can be made rigorous with charged square vertices.
3. **The response map is locally Hellinger-to-Fisher Lipschitz in the interior.** Infinite response length near the boundary does not contradict that local statement.

My recommendation is to build toward:

> **Stratified variational response:** the response law is the information projection determined by the data mean; on accessible strata, this law is represented by a unique Fisher-completion point.

Here are the precise ingredients.

---

# Q1. Higher codimension

Write
\[
P_\theta\propto e^{-\langle\theta,S\rangle}\nu,
\qquad A=S^{-1}(F),
\]
and use the sign-adjusted normal cone
\[
C_F=\{a:\langle a,S\rangle=c_a\text{ on }A,\ 
                    \langle a,S\rangle\ge c_a\quad\nu\text{-a.e.}\}.
\]
Assume throughout this discussion that the moment body is a compact polytope and \(S\) is essentially bounded.

## 1. The first theorem: normal-cone coalescence

I would first formalise the following **conditional** theorem, before proving that arbitrary sequences over \(\operatorname{ri}F\) admit its normal form.

### `NormalConeCauchyCoalescence`

Let
\[
\theta_n=v+a_n,\qquad \eta_n=v+b_n,
\qquad a_n,b_n\in C_F.
\]
Suppose:

- both sequences are Fisher-Cauchy;
- \(P_{\theta_n}(A)\to1\);
- \(P_{\eta_n}(A)\to1\).

Then
\[
d_F(\theta_n,\eta_n)\longrightarrow0.
\]

Thus their completion limits coincide.

This is genuinely codimension-free. It needs neither a preferred normal ray nor quantitative normal gaps.

### The key correction to the proposed grid

For fixed \(m\), it is generally **false** that
\[
d_F(v+b_m+a_n,v+b_m)\to0.
\]
The second point is fixed in the interior; the first approaches the boundary. Usually their distance tends to a positive number.

The correct fixed-shift statement is
\[
\boxed{\quad d_F(\theta_n,\theta_n+b_m)\to0
       \quad\text{for each fixed }m.\quad}
\]

Here \(b_m\), not \(a_n\), is the displacement whose cost is estimated. There is no growing vector in the variance bound.

## 2. Exact fixed-normal-shift lemma

For \(h\in C_F\), put
\[
B_h=\operatorname*{ess\,sup}
       |\langle h,S\rangle-c_h|.
\]

### `dist_add_normal_le_sqrt_faceComplement`

For every \(\theta\),
\[
\boxed{
d_F(\theta,\theta+h)
 \le B_h\sqrt{1-P_\theta(A)}.
}
\]

Indeed, along \(\theta+s h\), \(0\le s\le1\),

- tilting by \(sh\) increases \(P(A)\);
- \(Y_h=\langle h,S\rangle-c_h\) vanishes on \(A\);
- \(0\le Y_h\le B_h\).

Hence
\[
\operatorname{Var}_{P_{\theta+sh}}Y_h
 \le E_{P_{\theta+sh}}Y_h^2
 \le B_h^2P_{\theta+sh}(A^c)
 \le B_h^2P_\theta(A^c).
\]
Integrate the Fisher speed.

In particular, if \(P_{\theta_n}(A)\to1\), then for **every fixed** \(h\in C_F\),
\[
d_F(\theta_n,\theta_n+h)\to0.
\]

A bound \(B_h\le D\|h\|\) is available from bounded statistics, but is unnecessary for the limit argument.

## 3. The translated-grid proof, with the limits in the right order

The normal-tilt comparison gives, for any path \(\gamma\),
\[
L_F(\gamma+b)
 \le \int \frac{|\dot\gamma|_F}
                  {\sqrt{P_{\gamma}(A)}}.
\]
Consequently, if \(P_\gamma(A)\ge p>0\) along the path,
\[
L_F(\gamma+b)\le p^{-1/2}L_F(\gamma),
\qquad b\in C_F.
\]

**Important:** an endpoint lower bound on \(P(A)\) is not by itself enough; one must control \(P(A)\) along the short path.

That control comes from the root-density embedding. With \(H(P,Q)=\|\sqrt P-\sqrt Q\|_2\),
\[
|\sqrt{P(A)}-\sqrt{Q(A)}|
 \le H(P,Q)\le \tfrac12 d_F(P,Q)
\]
under the usual Fisher normalization. Thus sufficiently short paths starting sufficiently near face mass one stay, for example, in \(P(A)\ge1/4\).

Fix a large anchor \(N\). For \(n\ge N\), choose an almost-minimising short path from \(\theta_N\) to \(\theta_n\). Translating it by any \(b_m\) gives uniformly in \(m\)
\[
d_F(\theta_N+b_m,\theta_n+b_m)
 \le 2\bigl(d_F(\theta_N,\theta_n)+\varepsilon\bigr).
\]

Now use the grid:
\[
\begin{aligned}
d_F(\theta_n,\eta_m)
&\le d_F(\theta_n,\theta_n+b_m)\\
&\quad+d_F(\theta_n+b_m,\theta_N+b_m)\\
&\quad+d_F(\theta_N+b_m,\eta_m).
\end{aligned}
\]

Its three sides behave as follows.

- First side: tends to zero as \(n\to\infty\), **with \(m\) fixed**.
- Middle side: bounded uniformly in \(m\) by twice a Cauchy tail.
- Last side:
  \[
  \theta_N+b_m=\eta_m+a_N,
  \]
  so it tends to zero as \(m\to\infty\), because \(a_N\) is fixed.

Writing \(x=\lim[\theta_n]\), \(y=\lim[\eta_n]\), this yields
\[
d_{\widehat W_F}(x,y)
 \le 2d_{\widehat W_F}(x,[\theta_N]).
\]
Let \(N\to\infty\).

That is the complete mechanism. It does **not** estimate a segment in the growing direction \(a_n\).

### Suggested first module boundary

Land these three lemmas together or in two small modules:

1. fixed-normal-shift cost;
2. local uniform translation bound on short paths near \(P(A)=1\);
3. normal-cone Cauchy coalescence.

Then make the general fibre theorem a separate normal-form application.

---

## 4. Eventual cone membership: yes, with a normal-form theorem

### At a charged vertex

For \(F=\{M\}\), the correct criterion is
\[
\boxed{
m(\theta_n)\to M
\quad\Longrightarrow\quad
\langle\theta_n,w-M\rangle\to+\infty
\quad(w\ne M,\ w\text{ a vertex}).
}
\]

The sign is \(+\infty\) for your \(e^{-\langle\theta,S\rangle}\) convention.

One should not prove this merely by dividing two probabilities until one knows that the probability of the atom at \(M\) does not vanish. Charged vertices supply that missing step:

- select a vertex minimizing \(\langle\theta_n,w\rangle\);
- its charged atom has probability bounded below uniformly, since the density anywhere in the polytope is at most its value at that vertex;
- concentration of the mean at the exposed vertex \(M\) forces every such minimizer eventually to be \(M\);
- then \(P_{\theta_n}(S=M)\ge\nu(S=M)/\nu(\Omega)\);
- the other vertex probabilities vanish, so their ratios to the \(M\)-probability force the gaps to \(+\infty\).

Finite vertex sets then give eventual **strict** inequalities simultaneously.

Thus eventual membership in the closed cone is all the translation theorem needs, but the vertex-gap theorem actually gives membership in its interior, modulo ineffective directions.

### For a general face

The normal-form result should say, in the effective parameter space,
\[
\operatorname{proj}_{T_F}\theta_n\to v_M,
\]
and, for
\[
a_n=\operatorname{proj}_{T_F^\perp}\theta_n,
\]
\[
\langle a_n,w-z\rangle\to+\infty
\quad
(z\in F,\ w\text{ a vertex outside }F).
\]

Consequently:

- \(a_n\in\operatorname{ri}C_F\) eventually;
- \(P_{\theta_n}(A)\to1\);
- the tangential errors can be removed in Fisher distance.

The last step is easy once tangential convergence is known: bounded statistics give a global Euclidean-to-Fisher upper bound for parameter segments.

The difficult part is proving tangential convergence from mean convergence. That is a **separate polyhedral compactness/properness argument**, not an immediate consequence of the variance comparison.

So my answer to (b) is:

> **Confirmed at a vertex. For general \(F\), formalise it as a face-normal-form theorem, including tangential convergence and divergent outside-vertex gaps.**

Combined with coalescence, it gives singleton nonempty fibres over every face interior.

---

## 5. Accessibility: fixed rays are ready; ray necessity is false

For any \(u\in\operatorname{ri}C_F\), set
\[
\ell_u=\langle u,S\rangle-c_u\ge0.
\]
Then \(\ell_u=0\) exactly on \(A\), up to null sets, and your ray theorem applies to
\[
r\longmapsto v_M+ru.
\]

Thus the immediate sufficient theorem is:

> Summability of the dyadic shell roots for \(\ell_u\) implies accessibility of the face-family law.

For finitely many facet normals with the opposite sign convention, this is your “bisector” ray after sign adjustment.

### A useful additional fact

For a fixed polyhedral face, any two interior normal slacks are comparable:
\[
c\,\ell_u\le\ell_{u'}\le C\,\ell_u
\]
on the polytope. Therefore their dyadic shell-root criteria are equivalent.

So the alternative is not usually “find a clever interior ray”:

> Either all interior normal rays have finite length, or none do.

The genuinely new freedom is **multiscale paths approaching the boundary of the normal cone**.

### A rigorous charged-square mechanism

Here is a concrete way to substantiate the ray/path failure.

Take statistics in \([0,1]^2\), put positive mass on all four vertices, and add groups of atoms
\[
(x_j,y_{j,k}),\qquad 1\le k\le N_j,
\]
with total group mass \(a_j\), equally divided.

Choose:

- \(\sum_j\sqrt{a_j}<\infty\);
- \(\sum_j\sqrt{a_jN_j}=\infty\);
- \(x_j\) in distinct dyadic shells;
- the \(y_{j,k}\) in \(N_j\) widely spread dyadic shells, all much larger than \(x_j\);
- the groups in disjoint scale bands tending to zero.

For example, \(a_j\) proportional to \(2^{-4j}\), \(N_j=2^{4j}\), with sufficiently separated bands.

Then:

1. **The \(x\)-normal ray has finite length.**  
   Its nuisance shells have masses \(a_j\), so the criterion is
   \(\sum_j\sqrt{a_j}<\infty\).

2. **The exposed left edge contains only its two charged vertices.**  
   Its face family has a finite-length path to \((0,0)\).

3. **Every interior ray has infinite length.**  
   For any fixed \(u_1,u_2>0\), the slack
   \(u_1x_j+u_2y_{j,k}\) preserves all but a bounded number of the group’s separated \(y\)-scales. Its contribution is comparable to
   \[
   N_j\sqrt{a_j/N_j}=\sqrt{a_jN_j}.
   \]

4. **Nevertheless, the corner is accessible by an interior path.**  
   Alternate increasing \(x\)-tilt and increasing \(y\)-tilt. Choose the \(x\)-tilt large enough before each bounded \(y\)-interval that its vertical Fisher length approximates the left-edge length, with summable errors.

   The total horizontal cost is finite: normal translation by the current \(y\)-tilt bounds it by a fixed multiple of the finite \(x\)-ray length. The bottom-face probability along the unshifted \(x\)-ray is uniformly bounded below by the charged \((0,0)\) atom.

This is a real counterexample architecture, not just “tangential nuisance might run at different scales.” Formalising it is substantially more work than the uniqueness theorem.

### What characterisation should come next?

I would not promise a universal two-parameter shell criterion yet. The clean next sufficient principle is instead:

> **Face-chain accessibility:** a finite-length approach to a face, followed by a finite-length approach inside its face family, can be lifted to a finite-length interior approach, under suitable normal-translation control.

That captures the square construction and suggests a stratified, recursive geometry. It is not yet an accessibility characterisation.

---

## 6. Precise product theorem

### `ProductCornerCompletion`

Let
\[
\nu=\nu_1\otimes\nu_2,\qquad
S(x_1,x_2)=(S_1(x_1),S_2(x_2)),
\]
with each \(S_i\) a bounded one-dimensional statistic having charged endpoint \(m_i\). Use the full product exponential family.

Then:

1. the family factorises:
   \[
   P_{(\theta_1,\theta_2)}
   =P^1_{\theta_1}\otimes P^2_{\theta_2};
   \]
2. the Fisher metric is the orthogonal product;
3. the Fisher distance satisfies
   \[
   d_F((\theta_1,\theta_2),(\eta_1,\eta_2))^2
   =d_{F,1}(\theta_1,\eta_1)^2+
     d_{F,2}(\theta_2,\eta_2)^2;
   \]
4. the completion is the metric product of the completions;
5. the corner \((m_1,m_2)\) is accessible iff both endpoints are accessible;
6. equivalently, both one-dimensional shell-root sums are finite;
7. when accessible, its fibre is a singleton and its law is
   \[
   \nu_1(\,\cdot\mid S_1=m_1)
   \otimes
   \nu_2(\,\cdot\mid S_2=m_2).
   \]

In this product setting, accessibility **is** equivalent to finite length of every interior normal ray. Indeed
\[
\max(L_1,L_2)\le L_{\rm diagonal}\le L_1+L_2.
\]

This is an excellent theorem, but the distance/product-completion infrastructure may make it more than one 300-line module.

---

# Q2. The global response map

## 1. Interior local Lipschitz continuity is true

Your candidate (i) is not false as a **local interior** assertion.

The response factors as
\[
\Phi(Q)=m^{-1}(E_QS).
\]
For bounded statistics,
\[
\|E_QS-E_RS\|\le 2B\,H(Q,R),
\]
where \(B\) bounds \(\|S-c\|\) and \(H\) is the unscaled root-density distance.

In mean coordinates, the Fisher metric is
\[
ds_F^2=dm^\mathsf{T}C_{\theta(m)}^{-1}dm,
\qquad C_\theta=\operatorname{Cov}_{P_\theta}(S).
\]
On a sufficiently small convex mean neighbourhood where
\(C_{\theta(m)}\succeq\lambda I\),
\[
d_F(\Phi(Q),\Phi(R))
 \le \lambda^{-1/2}\|E_QS-E_RS\|
 \le \frac{2B}{\sqrt\lambda}H(Q,R).
\]

So:

> **The response map is locally Lipschitz from ambient data Hellinger distance to Fisher distance wherever the data mean is interior.**

The constant can diverge near the boundary. That is exactly how finite data length can coexist with infinite response length.

## 2. Exact pullback metric and local distortion

For the data family \(\rho_g\propto e^g\nu\), a tangent observable \(h\) gives
\[
b_g(h)=\operatorname{Cov}_{\rho_g}(S,h),
\]
and
\[
D\Phi_g[h]=-C_{\Phi(g)}^{-1}b_g(h).
\]
Hence the pulled-back response quadratic form is
\[
\boxed{
G^{\rm resp}_g(h,h)
=b_g(h)^\mathsf{T}C_{\Phi(g)}^{-1}b_g(h).
}
\]

It satisfies
\[
G^{\rm resp}_g(h,h)
\le
\lambda_{\max}\!\left(
 C_{\Phi(g)}^{-1/2}
 C_{\rho_g}
 C_{\Phi(g)}^{-1/2}
\right)
\operatorname{Var}_{\rho_g}(h).
\]

This is the precise comparison with data Fisher–Rao geometry:

- not a contraction in general;
- locally bounded distortion in the regular interior;
- contraction at a matched family law, where \(C_{\rho_g}=C_{\Phi(g)}\).

This deserves its own module: `ResponsePullbackMetric`.

---

## 3. The theorem deserving the global name

I recommend **`StratifiedVariationalResponse`**, assembled from smaller modules.

Its core is:

> For every interior mean, and every face-interior mean represented by a face exponential family, the response law is the unique relative-entropy minimiser among laws with that mean. If that mean is Fisher-accessible, its completion representative has exactly this law; once face-fibre uniqueness is available, that representative is unique.

This separates two different maps:

- the **variational response law**, which can exist even at an inaccessible boundary mean;
- the **completed Fisher response**, which exists only on accessible means.

Do not identify the whole closed moment body with the Fisher completion.

## 4. Boundary information projection: exact identity

Assume \(\nu\) is a probability measure. Let \(M\in\operatorname{ri}F\) and
\[
Q_M
=\frac{1_Ae^{-\langle v_M,S\rangle}}{Z_F(v_M)}\,\nu,
\qquad E_{Q_M}S=M.
\]

For every probability \(Q\ll\nu\) with \(E_QS=M\),
\[
\boxed{
D(Q\Vert\nu)
=
D(Q\Vert Q_M)+D(Q_M\Vert\nu).
}
\]
Consequently,
\[
D(Q\Vert\nu)\ge D(Q_M\Vert\nu),
\]
with equality iff \(Q=Q_M\).

The proof is short mathematically:

1. A supporting functional for \(F\) has nonnegative slack with \(Q\)-expectation zero, so \(Q(A)=1\).
2. The face density is strictly positive on \(A\), hence \(Q\ll Q_M\).
3. On \(A\),
   \[
   \log\frac{dQ_M}{d\nu}
   =-\langle v_M,S\rangle-\log Z_F(v_M).
   \]
4. Its expectation under either \(Q\) or \(Q_M\) is
   \[
   -\langle v_M,M\rangle-\log Z_F(v_M).
   \]
5. Apply the relative-entropy change-of-reference identity and KL nonnegativity.

Bounded statistics make the log reference-density ratio bounded on \(A\). Thus the identity also handles \(D(Q\Vert\nu)=+\infty\) without subtracting infinities.

### Lean skeleton

Schematic, rather than proposed existing identifiers:

```lean
-- Geometry, independent of completion.
lemma ae_mem_face_of_mean_mem_face
    (hQ : IsProbabilityMeasure Q)
    (hmean : mean Q S = M)
    (hM : M ∈ F) :
    ∀ᵐ x ∂Q, S x ∈ F := ...

-- Measure-theoretic bridge.
lemma ac_faceFamily_of_ac_of_mean
    (hQν : Q ≪ ν)
    (hmean : mean Q S = M) :
    Q ≪ faceFamilyLaw ν F S vM := ...

-- Bounded log-density on the common support.
lemma integral_log_faceDensity
    (hQν : Q ≪ ν)
    (hmean : mean Q S = M) :
    ∫ x, logFaceDensity ν F S vM x ∂Q
      = - inner vM M - log (facePartition ν F S vM) := ...

-- Extended-valued KL, or a finite-KL theorem plus an infinity case.
theorem faceResponse_kl_pythagoras :
    KL Q ν = KL Q QM + KL QM ν := ...

theorem faceResponse_unique_minimizer :
    KL QM ν ≤ KL Q ν ∧
      (KL Q ν = KL QM ν ↔ Q = QM) := ...
```

`CompletionSupportingFace` supplies the geometric pattern, but the first lemma should be generalised to **arbitrary laws with the prescribed mean**.

`ResponseBregman` and `ResponseDefectPythagoras` may supply most of the entropy algebra. They do not automatically supply the boundary support and absolute-continuity bridge.

---

# Q3. The featureless end and the whole curve

## 1. A particularly clean theorem at \(t=0\)

Assuming \(P_0=\nu\), let
\[
C=\operatorname{Cov}_\nu(S),\qquad
b=\operatorname{Cov}_\nu(S,h).
\]
Then
\[
\theta'_0=-C^{-1}b,
\]
and
\[
|\theta'_0|_F^2=b^\mathsf{T}C^{-1}b
\le \operatorname{Var}_\nu(h).
\]

More geometrically, if
\[
h_{\rm resp}
=\langle C^{-1}b,S-E_\nu S\rangle,
\]
then \(h_{\rm resp}\) is the \(L^2(\nu)\)-orthogonal projection of
\(h-E_\nu h\) onto the centred sufficient statistics, and
\[
\operatorname{Var}_\nu h
=
|\theta'_0|_F^2
+
\|h-E_\nu h-h_{\rm resp}\|_{L^2(\nu)}^2.
\]

Thus:

> At the featureless end, response is exactly Fisher-orthogonal projection; expansion can emerge only away from the matched base law.

This is more conceptually illuminating than another endpoint estimate.

Strictly speaking, \(\nu\) is the “featureless” reference law. Calling it maximum entropy without qualification requires a chosen reference notion of entropy.

## 2. No bound from charged top mass alone

Correct: charged top set, finite data Fisher length, and even the indicator formula
\[
L_{\rm data}=2\arccos\sqrt{p_0}
\]
do not force finite response length.

A meaningful upper bound must retain information about the model’s transverse ray geometry.

## 3. Yes: land the ray-plus-log bound

If your existing window estimate is exactly
\[
L_{\rm resp}
\le C_1\int D+
 C_2\left(\int g+2C_3\log(1/p_*)
                     +2C_4\int D\right)
\]
and
\[
\int D\le2B\,|J|\log(1/p_*),
\]
then direct substitution gives
\[
\boxed{
L_{\rm resp}
\le C_2\int g+
\left[
2B|J|(C_1+2C_2C_4)+2C_2C_3
\right]\log(1/p_*).
}
\]

If \(\int g=L_{\rm ray}\), this is precisely
\[
L_{\rm resp}\le A L_{\rm ray}+B_{\rm err}\log(1/p_*).
\]

If \(\int g\) is only bounded by a rescaled ray length, include that factor explicitly. If the window begins after a finite initial interval, retain its length as an additive term.

This theorem is worth landing because it cleanly separates:

- **geometric cost:** the model ray;
- **selection cost:** the logarithmic probability penalty;
- **tangential tracking:** controlled by the defect estimate.

Be explicit about what the constants and \(p_*\) depend on; this should not accidentally read as a uniform bound over all data tilts or models.

Under the finite-ray hypothesis, combining this with your endpoint theorem gives the continuous completed curve on \([0,\infty]\). Without that hypothesis, no universal finite-length statement is available.

---

# Q4. Ranked small-module programme

“Ready” below means mathematically reduced to the stated toolkit, not a guarantee about uninspected Lean API overhead.

| Rank | Module | One-line statement | Readiness / size |
|---:|---|---|---|
| **1** | `NormalConeCauchyCoalescence` | Two face-concentrating Fisher-Cauchy sequences with a common tangential base and normal-cone offsets have the same limit. | **Ready**, after the fixed-shift lemma; target ≤300 lines. |
| **2** | `FaceResponsePythagoras` | The face family law is the unique KL minimiser at its mean, with an exact boundary Pythagorean identity. | **Ready mathematically**; ≤300 if change-of-reference KL infrastructure exists. |
| **3** | `ResponsePullbackMetric` | The response metric is \(b^\mathsf TC_\theta^{-1}b\), with covariance-controlled local distortion. | **Ready**, likely ≤300 using current differentiation results. |
| **4** | `ResponseAtFeaturelessLaw` | At \(\nu\), response is orthogonal projection onto the sufficient-statistic tangent space. | **Ready**, excellent small module. |
| **5** | `FaceNormalForm` | Mean convergence to \(\operatorname{ri}F\) gives tangential convergence and divergent outside-vertex normal gaps. | **Next substantial proof**; split vertex and general-face versions. |
| **6** | `NormalShiftBoundaryCost` | A fixed normal shift costs at most \(B_h\sqrt{1-P_\theta(A)}\). | **Ready now**, small, and the dependency to implement first. |
| **7** | `ResponseLocalHellingerLipschitz` | On interior mean neighbourhoods, response is locally Hellinger-to-Fisher Lipschitz. | **Ready** if local inverse-mean regularity is packaged. |
| **8** | `FacetResponseLengthBudget` | \(L_{\rm resp}\le A L_{\rm ray}+B\log(1/p_*)\), with stated constants. | **Ready now**; mostly consolidation. |
| **9** | `NormalRayFaceAccessibility` | Any interior normal ray with summable slack-shell roots reaches the face response law. | **Ready now**, a reusable general-face wrapper. |
| **10** | `ProductFisherMetric` | Product families have the \(\ell^2\)-product Fisher distance and completion. | **Ready mathematically**; split distance and completion if needed. |
| **11** | `ProductCornerCompletion` | A product corner is accessible exactly when both one-dimensional shell criteria hold. | **Ready after product geometry**, then short. |
| **12** | `FaceChainAccessibility` | Finite-length approaches can be composed through nested faces by controlled interior lifts. | **Research next**, first state hypotheses carefully. |

**Implementation order:** fixed shift → coalescence → vertex normal form → general face normal form.

**Conceptual centrepiece:** boundary KL Pythagoras together with the response pullback metric.

That combination gives the programme its next structure: **one variational response law, a stratified accessibility geometry, and an interior differential map whose boundary singularities are measured by Fisher completion.**