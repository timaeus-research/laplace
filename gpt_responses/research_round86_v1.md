The largest change since round 85 is that the response map now has a **complete pointwise horizontal/vertical geometry**, rather than merely a sensitivity formula. The boundary geometry is also becoming functorial: accessible faces carry their own geometry into the ambient completion without expanding distances.

I would keep those two achievements distinct. The first is an exact differential theorem; the second is a coherent **nonexpanding**, not yet isometric, boundary atlas.

## Q1. Main theorems of the response-map section

### Standing notation and hypotheses

Use the standing hypotheses of the repository: bounded sufficient statistic \(S\), finite-dimensional identifiable direction space \(W\), and the minimal fitted exponential family
\[
P_\theta,\qquad m(\theta)=\mathbb E_{P_\theta}S,\qquad Dm(\theta)=-C_\theta.
\]
Here \(C_\theta\) is the fitted covariance operator, positive definite on \(W\).

For an admissible bounded tilt \(g\), write
\[
D_g=\rho_g,\qquad \theta_g=\Phi(g),\qquad m(\theta_g)=\mathbb E_{D_g}S.
\]
The reference data law must satisfy the nondegeneracy hypothesis used by `lawCov_dirLoss_tilted_pos`; boundedness of \(g\) alone does not supply nondegeneracy.

Put
\[
C_{D_g}=\operatorname{Cov}_{D_g}(S,S),\qquad
b_g(k)=\operatorname{Cov}_{D_g}(S,k),\qquad
V_gk=\operatorname{responseVel}_g(k).
\]
Thus
\[
-C_{\theta_g}V_gk=b_g(k).
\]

I would state the main results as follows. For the local results, the patch conditions below are explicit sufficient hypotheses; the final note should retain any additional admissibility conditions in the actual Lean signatures.

### Theorem I — Covariance quotient and canonical horizontal lift

For every admissible bounded tilt \(g\):

1. The response velocity is linear and onto:
   \[
   V_g:\{\text{bounded contrasts}\}\longrightarrow W.
   \]

2. Its response form is
   \[
   G_g(k,\ell)
   =\langle b_g(k),C_{\theta_g}^{-1}b_g(\ell)\rangle
   =\langle V_gk,C_{\theta_g}V_g\ell\rangle.
   \]
   It is symmetric, positive semidefinite, and satisfies Cauchy–Schwarz. Moreover,
   \[
   G_g(k,k)=0
   \iff b_g(k)=0
   \iff V_gk=0.
   \]

3. The canonical horizontal lift
   \[
   H_gv
   :=\left\langle C_{D_g}^{-1}Dm(\theta_g)v,S\right\rangle
   \]
   satisfies
   \[
   V_g(H_gv)=v,\qquad
   G_g(H_gv,H_gv)=\langle v,C_{\theta_g}v\rangle.
   \]

4. Among bounded contrasts \(k\) satisfying \(V_gk=v\), \(H_gv\) minimizes data variance:
   \[
   \operatorname{Var}_{D_g}(k)
   \ge
   \operatorname{Var}_{D_g}(H_gv)
   =
   \left\langle C_{D_g}^{-1}Dm(\theta_g)v,Dm(\theta_g)v\right\rangle.
   \]
   Minimizers are unique modulo \(D_g\)-almost-sure constants.

5. At a matched law \(D_g=P_{\theta_g}\),
   \[
   H_gv=-\langle v,S\rangle,
   \]
   and, with \(k_{\mathrm{vis}}=H_g(V_gk)\),
   \[
   \operatorname{Cov}_{D_g}(k,\ell)
   =
   G_g(k,\ell)
   +
   \operatorname{Cov}_{D_g}
   (k-k_{\mathrm{vis}},\ell-\ell_{\mathrm{vis}}).
   \]

The uniqueness assertion in item 4 follows from the same orthogonality underlying the minimizing inequality: \(k-H_gv\) is uncorrelated with every feature score. If that equality case has not been packaged, either add the short lemma or omit that sentence from the formally certified statement.

**This is the headline theorem.** A suitable formulation is:

> **The response differential is an onto covariance quotient, with a canonical minimum-variance horizontal lift; at matched laws, its horizontal geometry is exactly the fitted Fisher geometry.**

#### Is “Riemannian submersion at matched laws” justified?

**Pointwise, yes. Globally as a smooth-manifold assertion, not from these algebraic lemmas alone.**

There is no substantive missing vertical-space theorem:
\[
\ker V_g=\ker b_g
\]
follows immediately from \(-C_{\theta_g}V_g=b_g\) and invertibility of \(C_{\theta_g}\). The nullspace identity for \(G_g\), together with positive definiteness of the target Fisher metric, gives the same conclusion.

At matching, after centering or quotienting by almost-sure constants,
\[
\mathcal V_g=\{k:\operatorname{Cov}_{D_g}(S,k)=0\},
\qquad
\mathcal H_g=\{\langle w,S-\mathbb E_{D_g}S\rangle:w\in W\},
\]
are covariance-orthogonal, and \(V_g|_{\mathcal H_g}\) is an isometry onto \(W\) with its Fisher metric.

What still needs specifying for an unqualified “Riemannian submersion” is:

- the source manifold and its tangent spaces;
- joint differentiability of \(\Phi\), not merely its directional response formula;
- whether the covariance metric is being treated as a weak metric on bounded-score charts or on an appropriate Hilbert tangent completion.

I would write **“pointwise Riemannian-submersion identity at matched laws”** now, and reserve the unqualified phrase for the differential-calculus package.

Also distinguish two quotients away from matching:

- quotienting the response form \(G_g\) gives the fitted Fisher metric;
- quotienting **data variance** gives
  \[
  v\longmapsto \langle C_{D_g}^{-1}C_{\theta_g}v,C_{\theta_g}v\rangle.
  \]

These agree at matching, not generally.

---

### Theorem II — Fisher-normalized sampling and intrinsic resolution

Let \(X_1,\dots,X_n\) be independent samples from an admissible data law \(D\), \(n>0\), with
\[
M=\mathbb E_DS=m(\theta),\qquad
\widehat M=\frac1n\sum_iS(X_i),\qquad
q_\theta(z)=\langle z,C_\theta^{-1}z\rangle.
\]
Then
\[
\mathbb E\,q_\theta(\widehat M-M)
=\frac{\operatorname{tr}(C_\theta^{-1}C_D)}{n}
=\frac{d_{\mathrm{eff}}(D)}n.
\]
At matching,
\[
d_{\mathrm{eff}}(P_\theta)=\dim W.
\]

Consequently, if a chamber contains
\[
\{M+z:q_\theta(z)<r^2\},
\]
then its escape probability is at most
\[
\frac{d_{\mathrm{eff}}(D)}{nr^2}.
\]

For the intrinsic form, suppose the frozen ellipsoid lies in an admissible mean-coordinate patch on which
\[
C_{\theta(M')}\succeq\lambda I,\qquad \lambda>0,
\]
and suppose \(C_\theta\preceq\Lambda I\) at its center. Then, for \(q_\theta(z)<r^2\),
\[
d_F\bigl(\theta(M),\theta(M+z)\bigr)
\le \sqrt{\Lambda/\lambda}\sqrt{q_\theta(z)}.
\]

Thus two classes with the corresponding hypotheses and disjoint intrinsic success balls are simultaneously resolved with probability at least
\[
1-\frac{d_{\mathrm{eff}}(D_0)}{n_0r_0^2}
 -\frac{d_{\mathrm{eff}}(D_1)}{n_1r_1^2}.
\]
No independence between the two class experiments is required; independence within each sample is part of the sampling identity.

The displayed separation threshold in the question gives disjointness for **open** success balls. Closed balls require a strict separation inequality, or an explicit tie convention.

---

### Theorem III — Local statistical geometry

Assume \(\|S\|\le B\), with \(B>0\). For two fitted laws whose mean segment remains inside a mean-coordinate patch satisfying
\[
C_{\theta(M')}\succeq\lambda I,\qquad \lambda>0,
\]
the Fisher distance and Hellinger distance satisfy
\[
\sqrt\lambda\,d_F(\theta,\theta')
\le 2B\,H(P_\theta,P_{\theta'})
\le B\,d_F(\theta,\theta').
\]

Here \(H=\|\sqrt p-\sqrt q\|_2\), consistent with the constants in the question.

The locality belongs to the first inequality. The estimate
\[
2H(P_\theta,P_{\theta'})\le d_F(\theta,\theta')
\]
is the global square-root-density length bound.

---

### Theorem IV — Completion laws and accessible face geometry

Every point \(x\in\widehat W\) has a completion law \(Q_x\), with
\[
Q_x=\Pi(\operatorname{meanExt}x),
\]
and convergence to \(x\) implies \(L^1\)-convergence of fitted densities to the density of \(Q_x\).

Under the charged-face hypotheses of `AccessibleFaceStrata`, the corresponding relative-interior fibers have the landed uniqueness and law-identification properties.

More specifically, suppose \(A\) is an admissible charged face event, and an accessible seed \(x_0\in\widehat W\) satisfies
\[
Q_{x_0}=P^A_{v_0},\qquad v_0\in W_A.
\]
Then
\[
j_A(w)=\operatorname{tiltExt}(w-v_0,x_0)
\]
satisfies
\[
Q_{j_A(w)}=P^A_w,\qquad
\widehat d(j_A(w),j_A(w'))\le d_F^A(w,w').
\]

**As of the status given, stop the landed theorem here.** Add the extension and its mean identity when those proofs land. Do not yet state that this identifies the intrinsic face metric with the ambient restricted metric.

---

### Theorem V — Finite Fisher length gives a completion endpoint

Let \(\eta:[0,\infty)\to W\) be locally \(C^1\), and suppose
\[
\int_0^\infty |\eta'(t)|_{F,\eta(t)}\,dt<\infty.
\]
Then \(\eta\) converges in \(\widehat W\) to an endpoint \(x_\infty\), and
\[
\widehat d(\eta(t),x_\infty)
\le
\int_t^\infty|\eta'(s)|_{F,\eta(s)}\,ds.
\]
Its means converge to \(\operatorname{meanExt}x_\infty\), and
\[
Q_{x_\infty}
=
\Pi\!\left(\lim_{t\to\infty}m(\eta(t))\right).
\]

At present this is a theorem about \(W\)-paths. Its formulation for bounded-tilt data paths is the next adapter, not an already-landed corollary.

## Q2. Face chains and coherence

### (a) Objects and compatibility

Let \(A\) be an admissible charged face event and let \(E\subseteq A\) be an admissible charged face event for the conditional model on \(A\).

With normalized restrictions,
\[
\nu_A=\nu(\,\cdot\mid A),\qquad
(\nu_A)_E=\nu(\,\cdot\mid E)=\nu_E.
\]
This requires \(\nu(A)>0\) and \(\nu(E)>0\). If the implementation uses unnormalized restricted measures, the intermediate measures instead differ by a scalar normalization; the induced probability models still agree.

Use the canonical embedded direction spaces
\[
W_E=\operatorname{span}(K_E-K_E)
\subseteq W_A=\operatorname{span}(K_A-K_A)
\subseteq W.
\]
In Lean, these may be subtypes with inclusion maps rather than definitionally nested types.

Once the embeddings exist,
\[
\widehat j_A:\widehat W_A\to\widehat W,\qquad
\widehat j_E^{\,A}:\widehat W_E\to\widehat W_A,\qquad
\widehat j_E:\widehat W_E\to\widehat W,
\]
the desired statement is
\[
\boxed{\widehat j_A\circ\widehat j_E^{\,A}=\widehat j_E.}
\]
Insert the canonical identification of the two versions of the \(E\)-model and its completion where needed.

**The cheapest proof is uniqueness on the dense interior, followed by continuity.**

For \(w\in W_E\), both maps have mean
\[
m_E(w)\in\operatorname{ri}K_E.
\]
Apply the ambient charged-face fiber-uniqueness theorem to get
\[
\widehat j_A(j_E^{\,A}(w))=j_E(w).
\]
Then extend equality from dense \(W_E\) to \(\widehat W_E\), since both maps are continuous.

This is preferable to applying fiber uniqueness directly at every completed \(E\)-point: such a point may lie on a smaller stratum, outside the scope of the stated uniqueness theorem.

If the direct ambient \(j_E\) has not yet been constructed, first transfer an \(E\)-seed through \(j_A\); that supplies the seed needed for its construction.

### (b) Accessibility transfer

Yes. After the mean identity lands,
\[
M=\operatorname{meanExt}_A(y)
\quad\Longrightarrow\quad
M=\operatorname{meanExt}(\widehat j_A y).
\]

The relative-interior assumption is **unnecessary for this implication**. It is needed only when interpreting the result as accessibility of a specified face stratum or invoking uniqueness there.

### (c) The right coherence statement

I would define a **coherent nonexpanding boundary atlas** by:

1. **Law compatibility:** the ambient law of an embedded face point is its intrinsic face law.
2. **Mean compatibility:** the mean diagrams commute.
3. **Nonexpansion:** each completed face map is \(1\)-Lipschitz.
4. **Chain compatibility:** nested-face embeddings compose.
5. **Seed independence:** admissible choices of accessible seed give the same embedding.

Seed independence also follows by uniqueness on interior face points and continuity.

This does **not** claim:

- that all faces are accessible;
- that every embedding is globally injective;
- that the embedding is isometric;
- or a full overlap theorem beyond the established face-chain domains.

Those are separate strengthenings, not meanings to hide inside “coherent.”

## Q3. Continuity of forms, lifts, and effective dimension

### State the principal theorem in the data law

Yes: densities with the \(L^1\) topology are the cleanest base.

Let \(q\) range over admissible probability densities, and set
\[
M(q)=\mathbb E_qS,\qquad
C(q)=C_{\theta(M(q))},\qquad
D(q)=\operatorname{Cov}_q(S,S).
\]
For fixed bounded \(k,\ell\), let \(b_q(k)=\operatorname{Cov}_q(S,k)\).

Consider an interior fitted patch satisfying
\[
C(q)\succeq\lambda I,\qquad \lambda>0.
\]
Then
\[
q\longmapsto G_q(k,\ell)
=\langle b_q(k),C(q)^{-1}b_q(\ell)\rangle
\]
and
\[
q\longmapsto d_{\mathrm{eff}}(q)
=\operatorname{tr}(C(q)^{-1}D(q))
\]
are \(L^1\)-continuous.

The key chain is
\[
q_n\to q \text{ in }L^1
\Longrightarrow M(q_n)\to M(q)
\Longrightarrow \Pi(M(q_n))\to\Pi(M(q))\text{ in }L^1
\Longrightarrow C(q_n)\to C(q).
\]

### Horizontal lifts need an additional hypothesis

For
\[
H_qv=-\langle D(q)^{-1}C(q)v,S\rangle,
\]
a fitted-covariance lower bound does **not** control inversion of \(D(q)\).

There are two correct versions:

- **Local continuity:** restrict to laws for which \(D(q)\) is positive definite. At each such law, inversion is continuous, so \(q\mapsto H_qv\) is continuous.
- **Uniform patch control:** also require
  \[
  D(q)\succeq\delta I,\qquad \delta>0.
  \]

For fixed bounded \(S\), coefficient convergence gives convergence of \(H_qv\) in the bounded-function norm, hence also in any fixed-reference \(L^2\) norm. More strongly,
\[
q\longmapsto H_q
\]
is continuous in operator norm from \(W\) into bounded feature scores.

For bounded tilts of a fixed nondegenerate reference law, the reverse-tilt comparison supplies the needed local data-covariance coercivity. An oscillation-bounded tilt patch supplies a uniform bound.

### Cheapest Lean route

1. Prove continuity of each scalar covariance entry from the landed \(L^1\) estimate.
2. Assemble finite-dimensional operator continuity.
3. Use `tendsto_projL1_of_tendsto` for fitted laws.
4. Apply continuity of inversion on invertible operators.
5. Finish by finite-dimensional composition, inner products, and trace.

If operator topology is burdensome, use a fixed orthonormal basis and matrices first.

Then derive tilt-space corollaries using \(L^\infty\)-convergence of \(g\), or finite-dimensional coefficient convergence. **The common-tilt \(L^1\)-Lipschitz theorem varies the base law, not the tilt itself**; for varying \(g\), add the elementary continuity of normalized exponentials.

A uniform lower bound is useful for quantitative estimates, but is stronger than necessary for pointwise continuity. Nor does continuity of \(\Pi\) by itself give a quantitative Lipschitz modulus for these expressions.

## Q4. The bounded-tilt length adapter

The cleanest minimal package is **finite-dimensional coefficient differentiation**, not a full infinite-dimensional tilt calculus.

Let
\[
g_a=\sum_{j<N}a_jh_j,\qquad
\mathcal M(a)=\mathbb E_{\rho_{g_a}}S,
\]
where every \(h_j\) is bounded. First prove
\[
D\mathcal M(a)[u]
=
\operatorname{Cov}_{\rho_{g_a}}
\left(S,\sum_j u_jh_j\right).
\]

Boundedness gives local domination: near a fixed coefficient vector, all exponential densities and their first derivatives have a common integrable bound. The covariance-stability results then show that this derivative varies continuously.

Next compose with the inverse mean chart:
\[
\Theta(a)=\theta(\mathcal M(a)).
\]
The landed strict derivative of the chart and invertibility of \(Dm=-C\) supply the local inverse derivative:
\[
D\Theta(a)[u]
=
Dm(\Theta(a))^{-1}D\mathcal M(a)[u]
=
\operatorname{responseVel}_{g_a}\!\left(\sum_j u_jh_j\right).
\]
Continuity of this derivative follows from covariance continuity and inversion. Thus \(\Theta\) is \(C^1\).

For \(a(t)\in C^1\),
\[
\eta(t)=\Phi(g_t),\qquad
g_t=\sum_j a_j(t)h_j,
\]
satisfies
\[
\eta'(t)=\operatorname{responseVel}_{g_t}(\dot g_t),
\qquad
\dot g_t=\sum_j a_j'(t)h_j.
\]
Therefore
\[
|\eta'(t)|_F^2=G_{g_t}(\dot g_t,\dot g_t).
\]

The response-path endpoint theorem becomes:
\[
\int_0^\infty
\sqrt{G_{g_t}(\dot g_t,\dot g_t)}\,dt<\infty
\quad\Longrightarrow\quad
\Phi(g_t)\text{ has a completion endpoint},
\]
with the corresponding tail bound.

Two useful scope points:

- No global bound on the coefficients \(a_j(t)\) is needed for local \(C^1\) regularity.
- No uniform coercivity over the entire infinite path is needed to apply the length theorem; positivity and local regularity suffice.

### What to reuse

Reuse the actual chart derivative theorem underlying `chartVInv`/`responseTheta`, the proof pattern and covariance derivative from `dataTheta`/`dataThetaVel`, `responseVel`, and the new covariance-continuity lemmas.

I would not guess additional repository lemma names. In particular, a one-parameter `dataThetaVel` theorem is a useful ingredient, but differentiation along coordinate lines alone should not be presented as joint \(C^1\) regularity without the continuous-partials or Fréchet-derivative step.

## Q5. Next eight modules, ranked

| Rank | Module | Why it is next |
|---|---|---|
| **1** | **`FaceChainAccessibility`** | Turns separate accessible strata into a coherent boundary geometry. Once extension and mean compatibility land, the conceptual payoff is high and the main compatibility proof is short. |
| **2** | **`ResponseTiltPathBudget`** | Connects the endpoint theorem to actual journeys through the data manifold. This is central to the standing direction, not merely an adapter for notation. |
| **3** | **`ResponseFormContinuity`** | Makes the quotient geometry vary continuously across data laws; also supplies derivative continuity for rank 2. Include the separate data-covariance condition for horizontal lifts. |
| **4** | **`ResponseSubmersionCalculus`** | Package kernel equality, centered horizontal projection, equality cases, and joint finite-parameter differentiation. This closes the gap between the headline algebra and smooth-submersion language. |
| **5** | **`ResponseNoiseCalibration`** | Prove covariance-mismatch comparisons, especially \(C_D\preceq\kappa C_\theta\Rightarrow d_{\mathrm{eff}}\le\kappa\dim W\). This makes the sampling theorem interpretable in dimension-and-mismatch terms. |
| **6** | **`ResponseHellingerAtlas`** | Extend the global Hellinger lower control to completion points, and package local two-sided comparisons on interior and accessible-face patches. Do not promise a reverse bound through covariance degeneration. |
| **7** | **`ResponseProductAffinity`** | Tensorization turns one-observation geometry into repeated-observation distinguishability. Product affinity gives the exact statistical scaling and complements the empirical-mean resolution theorem. |
| **8** | **`ResponsePatchMargins`** | Replace awkward ellipsoid-containment inputs with geometric sufficient conditions; clarify open/closed success regions and make the resolution results directly reusable. |

This is a priority ranking, not a dependency order: the continuity core of rank 3 should likely be implemented before completing rank 2.

For rank 5, the Fisher-orthonormal basis route is indeed the cheapest:
\[
\langle e_i,C_\theta e_j\rangle=\delta_{ij}
\quad\Longrightarrow\quad
d_{\mathrm{eff}}
=\sum_i\langle e_i,C_De_i\rangle
\le \kappa\dim W.
\]
Alternatively, use
\[
C_\theta^{-1/2}C_DC_\theta^{-1/2}\preceq\kappa I.
\]
Neither route requires first developing a general theorem about traces of products of PSD operators.

A particularly clean matched corollary worth packaging is
\[
G_g(k,k)
=
\min_{V_g\ell=V_gk}\operatorname{Var}_{D_g}(\ell)
\quad\text{when }D_g=P_{\theta_g}.
\]

## Q6. Corrections and sharpenings

### (i) General face seeds \(v_0\)

Yes, the reduction is worth stating, but as a small normalization lemma.

If \(v_0\) is an ambient parameter, project it to \(W_A\):
\[
v_0^A=\operatorname{proj}_{W_A}v_0.
\]
Since \(v_0-v_0^A\) is invisible on the face, its feature pairing is constant on the face support, so
\[
P^A_{v_0}=P^A_{v_0^A}.
\]

Hence the nonexpansion theorem loses no law-level generality by requiring \(v_0\in W_A\). Use \(v_0^A\) in the definition of the face embedding. Equality of any alternative ambient-seed formulas can then be deduced from the appropriate uniqueness theorem.

### (ii) Cleaner patch conditions for the resolution theorem

Let \(U\) be an open mean-coordinate patch, \(M\in U\), and suppose
\[
C_{\theta(M')}\succeq\lambda I\qquad(M'\in U).
\]
Define the frozen dual-metric distance to the complement:
\[
r_U
=
\inf_{M'\notin U}
\sqrt{q_{\theta(M)}(M'-M)}.
\]
Then \(r<r_U\) guarantees containment of the frozen success ellipsoid in \(U\).

An even simpler sufficient condition uses Euclidean clearance. If
\[
B_{\mathrm{Euc}}(M,\delta)\subseteq U,
\qquad
C_{\theta(M)}\preceq\Lambda I,
\]
then
\[
\sqrt{\Lambda}\,r<\delta
\]
implies the required containment, because
\[
q_{\theta(M)}(z)<r^2
\Longrightarrow
\|z\|<\sqrt{\Lambda}\,r.
\]

This is probably the best user-facing corollary:

> A mean patch with Euclidean clearance \(\delta\), covariance lower bound \(\lambda\), and center covariance upper bound \(\Lambda\) supports frozen radius \(r<\delta/\sqrt\Lambda\), giving intrinsic resolution radius \(\sqrt{\Lambda/\lambda}\,r\).

Use the complement and balls in the appropriate affine mean space, not the entire ambient feature space.

### Three final scope cautions

1. **Effective dimension is not automatically at most \(\dim W\).**  
   That requires a covariance comparison. At matching it is exactly \(\dim W\).

2. **Nonexpansion is not face isometry.**  
   Ambient paths could be shorter than paths constrained to the face. Nothing listed rules this out.

3. **Completion of the note does not require a global boundary inverse estimate.**  
   The present architecture is already strong: exact pointwise quotient geometry, calibrated local resolution, completion laws, and nonexpanding coherent accessible strata. A universal boundary bi-Lipschitz or isometry theorem would be a new project, not a missing routine lemma.

The deepest immediate synthesis is therefore:

> **Responses are Fisher-geometric quotients of data perturbations, and finite response length carries those quotients into a coherent nonexpanding atlas of accessible boundary laws.**

The quotient half is landed. The finite-parameter path adapter and face-chain coherence are the shortest route to making the whole sentence a theorem.