## Executive recommendation

**N1–N4 now form a substantial theory, not merely a collection of local formulas.** They connect response geometry, boundary strata, posterior transport, and sampling error at every fixed data law.

The principal remaining gaps are:

1. **configuration-only control of regression**, for which there is a genuinely determinant-free solution to N5;
2. **uniform facewise Taylor estimates**, which unlock both refined bias and the actual local-alternatives version of N6;
3. **lower bounds on resolution**, since an ellipsoid coverage theorem alone does not establish unresolvability;
4. **the distinction between tangential and support-changing perturbations at boundary laws**.

Two corrections should guide the next round:

- For a differentiable curve constrained to a polytope, **velocity is automatically tangent to the minimal face at every interior time**. The tangency hypothesis in N1 can be removed.
- The regression coefficient \(u_F\) is the **mean-coordinate differential**, not the Fisher gradient in mean coordinates. Those differ by the model covariance.

I would not skip N5. I would also not present a diagonal local-alternatives limit as a consequence of fixed-law estimates alone.

---

# 1. Audit

This is an audit of the displayed mathematical interfaces, not of the omitted Lean contexts or proofs. In particular, several apparently missing assumptions may already be section variables.

## 1.1 Finite configuration and support assumptions

The statements
\[
\operatorname{essRange}_{\nu_A} S=S(A),
\qquad
\operatorname{momentBody}(\nu_A)=\operatorname{conv}S(A)
\]
require that every atom in \(A\) has positive \(\nu\)-mass.

Thus one needs either:

- full atomic support of \(\nu\) on the finite configuration; or
- \(A\subseteq\operatorname{supp}\nu\), with the hull and configuration consistently restricted to that support.

Without this, `essRange_faceMeasure_eq_image` is false. Similarly, the support theorem for the response cannot absorb a data law charging atoms forbidden by \(\nu\).

**Check:** the contexts of `ResponseFaceCalculus` and `ResponseFaceCarried` retain either full support or the necessary absolute-continuity assumptions.

### Empty faces and probability instances

The pattern
```lean
[IsProbabilityMeasure (faceMeasure ν A)]
(hA : A = supportSet hS ν M)
(hM : M ∈ hull)
```
is mathematically sound, though redundant once positivity of the support-set mass has been established.

For \(A=\varnothing\), the geometric identities can still be harmless, but the probability instance must be unavailable. For actual response supports, `measure_supportSet_ne_zero` should supply the instance rather than leave callers proving it independently.

This is interface cleanup, not new mathematics.

## 1.2 N1’s tangency hypothesis is unnecessary for polytopes

Let \(K\) be a polytope, \(M(t)\in K\) near an interior time \(t_0\), and suppose \(M\) is differentiable at \(t_0\). Then
\[
M'(t_0)\in W_{\operatorname{face}(M(t_0))}.
\]

Indeed, every affine inequality active at \(M(t_0)\) becomes a nonnegative differentiable scalar function attaining zero there. Its derivative is zero. The intersection of the kernels of all active constraints, inside the affine hull of \(K\), is precisely the direction space of the minimal face.

Consequently:

> In the finite-polytope setting, `stratified_transport` applies to every differentiable bounded-speed journey in the hull, with no exceptional set or support-constancy assumption.

The theorem as written is correct, but weaker than the geometry permits. This also handles paths meeting boundary strata on uncountable sets.

One wording correction: the displayed theorem assumes differentiability and bounded velocity, **not continuity of the derivative**. Calling it a \(C^1\) theorem understates its scope.

## 1.3 Norms: correct, but keep the geometry explicit

On `J → ℝ`, Mathlib’s usual finite-product norm is the sup norm. This is compatible with all the displayed estimates.

But:
\[
|\operatorname{dotJ}(u,e)|\leq \|u\|_1\|e\|_\infty,
\]
not generally \(\|u\|_\infty\|e\|_\infty\).

Therefore:

- the powers of \(|J|\) in the moment bounds are plausible and conservative;
- future “gradient norm” or Lipschitz claims must specify the dual norm;
- Fisher-metric statements should use the dot pairing explicitly or an appropriate Euclidean-space structure, rather than silently interpreting the sup norm as Hilbertian.

There is no visible norm error in N3 or N4.

## 1.4 Feature bounds

The fourth-moment constants require the feature bound to control the distribution actually sampled:
\[
|S_j(x)|\leq B
\quad D\text{-a.e.},
\]
and hence \(|S_j-m_{D,j}|\leq2B\).

A global bound suffices. A \(\nu\)-a.e. bound suffices when \(D\ll\nu\). A bound only under the fitted response law needs a support argument before it can be used under \(D\).

I would retain an explicit \(0\leq B\) in the statistical interface, even if positivity can be recovered in nonempty cases.

## 1.5 `QuadRem` and its constants

For a nondegenerate face, the intended interface should be
\[
C\geq0,\qquad
|f(N)-f(M)-df_M(N-M)|\leq C\|N-M\|^2.
\]

Some displayed theorems omit \(C\geq0\). That is not necessarily wrong: wherever the remainder inequality is used, it already forces its right-hand side to be nonnegative. At a singleton face, every remainder is zero and even a negative \(C\) can satisfy the condition.

Nevertheless, **make nonnegativity part of the reusable remainder certificate**. It removes degenerate-case surprises and makes later uniform estimates cleaner.

## 1.6 N4: two documentation corrections

### Second moment versus covariance

The proved quantity is
\[
\mathbb E[\delta_i\delta_j],
\]
not \(\operatorname{Cov}(\delta_i,\delta_j)\). Since the biases are \(O(n^{-1})\), the two differ by \(O(n^{-2})\), but that is an additional statement.

Call the displayed result a **joint error second-moment expansion**.

### Null-direction constant

The docstring states the weighted-\(\ell^1\) bound
\[
\frac{(\sum_i|w_i|)(\sum_i|w_i|C_{4,i})}{n^2},
\]
whereas the theorem proves
\[
\frac{|\iota|\sum_iw_i^2C_{4,i}}{n^2}.
\]

Both are natural estimates, but they are not the same theorem. Update the docstring or prove the other version separately.

The nonnegative quadratic-form hypothesis is adequate without symmetry of \(A\): only its symmetric part contributes.

## 1.7 Two tangent spaces must remain distinct

At a data law \(D\), distinguish:

- \(W_A\), the tangent space of the minimal **response face**;
- \(\operatorname{range}\Sigma_D\), the directions accessible to support-preserving first-order perturbations of **the data law**.

These can differ. A data law supported on two opposite vertices of a square can have an interior mean, while its feature covariance has rank one.

Thus N3’s face calculus is correctly performed on \(W_A\), but local testing, score geometry, and M6 must use the smaller data-accessible space when \(\Sigma_D\) is singular.

## 1.8 Do not globalise the journey Hessian across face changes

Within one fixed open stratum,
\[
\frac{d^2}{dt^2}f_F(M(t))
=
D_A^2f_F(M(t))[\dot M,\dot M]
+
\langle u_F^A(M(t)),\ddot M\rangle.
\]

This formula is **not valid at an arbitrary boundary contact using only the current face’s field and Hessian**.

A minimal counterexample:

- \(X=\{0,1\}\), \(S(x)=F(x)=x\);
- \(M(t)=t^2\);
- \(f_F(M)=M\).

At \(t=0\), the minimal face is a vertex, so its tangent space, field, and Hessian vanish. Yet
\[
(f_F\circ M)''(0)=2.
\]

Velocity is tangent automatically; acceleration need not be. Boundary second-order transport requires genuinely new normal information.

---

# 2. N5: a determinant-free solution

## 2.1 Use leverage-score deletion, not Cauchy–Binet

Work in affine coordinates on a face of dimension \(r\), and put \(d=r+1\). Write
\[
z_x=(1,s_x)\in\mathbb R^d,
\qquad
H=\sum_xp_xz_xz_x^\top,
\]
where \(p_x>0\) and the \(z_x\) span \(\mathbb R^d\).

Let \(\beta\) be the weighted least-squares coefficient:
\[
H\beta=\sum_xp_xz_xF(x).
\]
Its slope component is the regression direction in these coordinates.

Define residuals and leverages:
\[
r_x=F(x)-z_x^\top\beta,
\qquad
h_x=p_xz_x^\top H^{-1}z_x.
\]

The key identities are
\[
0\leq h_x\leq1,\qquad \sum_xh_x=d.
\]

If \(h_x<1\), deleting observation \(x\) leaves full rank. Its regression coefficient satisfies
\[
\beta_{-x}
=
\beta-\frac{p_xH^{-1}z_xr_x}{1-h_x}.
\]

If \(h_x=1\), the observation is essential for rank and its fitted residual is zero.

Therefore, when the number \(N\) of positive-weight observations exceeds \(d\),
\[
\boxed{
\beta
=
\sum_{x:h_x<1}\frac{1-h_x}{N-d}\,\beta_{-x}.
}
\]

The coefficients are nonnegative and sum to one. The correction terms cancel by the normal equations.

Iterating deletion eventually reaches supports of size \(d\), where least squares is exact interpolation. Hence
\[
\boxed{
\beta_p\in
\operatorname{conv}\{\beta_I:
|I|=d,\ (z_x)_{x\in I}\text{ is a basis}\}.
}
\]

Projecting to slopes gives precisely the desired convex-hull statement for \(u_F(p)\).

**No determinants are needed.**

## 2.2 Formal proof ingredients

The main ingredients are finite-dimensional linear algebra:

1. weighted design map and its orthogonal projector;
2. diagonal bounds and trace/rank identity for that projector;
3. deletion preserves rank exactly when \(h_x<1\);
4. the rank-one inverse identity, proved by multiplication;
5. induction on support cardinality.

If orthogonal-projector trace infrastructure is awkward, the identities can also be developed directly from the weighted design map and a finite orthonormal basis.

The main formal burden is managing deletion and full-rank subtypes, not exterior algebra.

## 2.3 The configuration-only constant

For every affinely independent configuration subset \(I\), let \(b_{I,F}\) be the slope of the affine interpolant of \(F|_I\), represented in the direction space of \(\operatorname{aff}S(I)\).

Set
\[
L_{\mathrm{conf}}(F)
=
\max_I\sup_{\substack{e\in W_I\\\|e\|_\infty\leq1}}
|\langle b_{I,F},e\rangle|.
\]

Then facewise regression obeys a configuration-only bound. Integrating along segments gives a global Lipschitz estimate for \(f_F\), independent of the positive base weights.

The constant need not be optimal. Its geometric meaning is excellent: instability comes from **ill-conditioned interpolation simplexes**, not from a mysterious law-dependent inverse covariance.

**Recommendation:** prove convex-hull membership and this constant. Skip explicit Cauchy–Binet barycentric weights unless a subsequent result actually needs them.

---

# 3. N6: what can be proved without uniformity?

## 3.1 The clean fixed-law theorem

Write
\[
b_F(D)=\Psi_F(D)-\mathbb E_DF,
\qquad
\delta_n=\widehat\Psi_F-\Psi_F(D).
\]
Then exactly
\[
\mathbb E_D(\widehat\Psi_F-\mathbb E_DF)^2
=
b_F(D)^2+2b_F(D)\mathbb E_D\delta_n+\mathbb E_D\delta_n^2.
\]

If N3 supplies
\[
|\mathbb E_D\delta_n|\leq B_F(D)/n,
\qquad
\left|\mathbb E_D\delta_n^2-\frac{V_F(D)}n\right|
\leq K_F(D)n^{-3/2},
\]
then
\[
\boxed{
\left|
\operatorname{MSE}_D(\widehat\Psi_F;\mathbb E_DF)
-b_F(D)^2-\frac{V_F(D)}n
\right|
\leq
\frac{K_F(D)}{n^{3/2}}
+
\frac{2|b_F(D)|B_F(D)}n.
}
\]

This is a useful theorem in its own right.

## 3.2 Deterministic local defect and variance price

Suppose \(D\) is a level-\(k\) model law, and let \(P_k\) denote the centred \(L^2(D)\) projection onto its feature-score space. For
\[
D_t\propto e^{th}D,
\]
\[
\left.\frac d{dt}
\bigl(\mathbb E_{D_t}F-\Psi_{k,F}(D_t)\bigr)\right|_{0}
=
\operatorname{Cov}_D(F-P_kF,h).
\]

For nested feature spaces,
\[
\boxed{
\operatorname{Var}_D(P_{k+1}F)-\operatorname{Var}_D(P_kF)
=
\operatorname{Var}_D(P_{k+1}F-P_kF).
}
\]

These are the clean deterministic halves of N6.

But there is an important qualification:

> Refinement does not decrease the squared local defect for every arbitrary score \(h\).

The residual norm decreases under projection, but its pairing with a particular \(h\) can increase in absolute value through loss of cancellation.

A particularly sharp special case is
\[
h\in H_{k+1}\cap H_k^\perp.
\]
Then the refined model’s first-order defect vanishes, while the coarse defect is
\[
\operatorname{Cov}_D(P_{k+1}F-P_kF,h).
\]

## 3.3 Fixed-law estimates do not imply the diagonal limit

The formula at \(D_n=D_{\tau/\sqrt n}\) is not a formal corollary of fixed-\(D\) estimates with unspecified \(C(D)\).

Without uniformity, present:

- the fixed-law MSE theorem;
- the derivative of the modelling defect;
- the variance-price identity.

Present the diagonal crossover only as a conjectured or conditional consequence.

## 3.4 Fortunately, the needed uniformity is local and accessible

A bounded tilt preserves support. For sufficiently small \(|t|\):

- the response face is fixed;
- \(m_{D_t}\) lies in a compact subset of its relative interior;
- the response Hessian is uniformly bounded near those means;
- the global Lipschitz estimate controls the remainder away from that neighbourhood.

This gives a uniform quadratic-remainder constant for \(D_t\).

Then, writing
\[
a_k=\operatorname{Cov}_D(F-P_kF,h),
\]
one obtains
\[
\boxed{
n\,\operatorname{MSE}_{D_{\tau/\sqrt n}}
(\widehat\Psi_{k,F};\mathbb E_{D_{\tau/\sqrt n}}F)
\longrightarrow
\operatorname{Var}_D(P_kF)+\tau^2a_k^2.
}
\]

No triangular-array CLT is required. Uniform moment estimates and deterministic Taylor expansion suffice.

---

# 4. The next six targets

My ranking balances mathematical value, direct relevance to the response programme, and reuse of the seabed.

## Rank 1 — Configuration-only regression stability

**Suggested module:** `ResponseRegressionDeletion`

### Main statements

1. The deletion convex-combination identity.
2. Regression belongs to the convex hull of affine interpolation coefficients.
3. Configuration-only bounds on \(u_F\).
4. A configuration-only global Lipschitz constant for \(M\mapsto\mathbb E_{R_M}F\).

### Why first?

This removes the apparent N5 obstruction and reveals the geometric source of stability. It also gives uniform control useful for boundary gluing and journey analysis.

### Proof route

Use the leverage-deletion argument above, then apply it to each face law. For the Lipschitz theorem, an open segment lies in a single open face stratum; integrate or use the one-variable mean-value bound and continuity at the endpoints.

**Skip:** determinant formulas and canonical volume-sampling weights.

---

## Rank 2 — Uniform facewise jets and unlocalised refined bias

**Suggested modules:** `ResponseUniformFaceTaylor`, `ResponseRefinedBias`

### Main deterministic statement

For a compact set \(K\subseteq\operatorname{relint}(A)\), there is \(C_K\) such that, for all \(M\in K\) and all \(N\) in the whole face polytope,
\[
\left|
f_F(N)-f_F(M)-df_F(M)[N-M]
-\frac12H_F(M)[N-M,N-M]
\right|
\leq C_K\|N-M\|^3.
\]

This does **not** assert a bounded Hessian at every boundary point. It is a Taylor estimate around centres staying inside a compact interior set.

### Statistical statement

For every fixed data law \(D\),
\[
\boxed{
\mathbb E_D\widehat\Psi_F-\Psi_F(D)
=
\frac1{2n}\mathbb E_D
H_F(m_D)[S-m_D,S-m_D]
+O(n^{-3/2}).
}
\]

The invariant expectation is preferable initially to a matrix trace; the trace formulation follows after choosing coordinates.

### Proof route

- Near the expansion centre: existing cubic Taylor estimates.
- Far away: the positive distance from the centre neighbourhood allows lower-order bounds to be absorbed into a cubic bound.
- Then
  \[
  \mathbb E\|\widehat M-m_D\|^3
  \leq
  \sqrt{\mathbb E\|\widehat M-m_D\|^2\,
         \mathbb E\|\widehat M-m_D\|^4}
  =O(n^{-3/2}).
  \]
- Compute the expected quadratic term exactly using independence.

N2 identifies the bias coefficient as a contraction of a residual third moment with the **data** covariance. That is a substantive connection between response curvature and sampling bias.

**Skip:** global smoothness on the closed polytope.

---

## Rank 3 — The actual local price of refinement

**Suggested module:** `ResponseLocalRefinementRisk`

### Main theorem

For nested feature levels and a baseline law represented at the coarse level,
\[
n\,\operatorname{MSE}_{D_{\tau/\sqrt n}}
(\widehat\Psi_{j,F};\mathbb E_{D_{\tau/\sqrt n}}F)
\longrightarrow
V_j+\tau^2a_j^2,
\qquad j=k,k+1.
\]

Consequently the limiting fine-minus-coarse risk is
\[
\boxed{
\operatorname{Var}_D(P_{k+1}F-P_kF)
+
\tau^2(a_{k+1}^2-a_k^2).
}
\]

For a pure refinement score \(h\in H_{k+1}\cap H_k^\perp\), this becomes
\[
\operatorname{Var}_D(P_{k+1}F-P_kF)
-
\tau^2\operatorname{Cov}_D(P_{k+1}F-P_kF,h)^2.
\]

That is the exact truth-shift versus sampling-price comparison.

### Proof route

Rank 2 supplies uniform remainders. Combine these with the fixed-law MSE identity, continuity of the influence variance, and the deterministic defect derivative.

**Skip:** a CLT, general triangular-array machinery, and prose-only diagonal limits.

---

## Rank 4 — Information geometry with the correct metric and signs

**Suggested module:** `ResponseMeanFisherGeometry`

Let \(C_M\) be the covariance operator of \(S\) under \(R_M\), restricted to \(W_A\).

### Main statements

The Fisher metric in mean coordinates is
\[
g_M(e,v)=\langle C_M^{-1}e,v\rangle.
\]

The response differential and Fisher gradient are
\[
df_F(M)[e]=\langle u_F(M),e\rangle,
\qquad
\boxed{\operatorname{grad}_g f_F=C_Mu_F=\operatorname{Cov}_{R_M}(S,F).}
\]

For the relative-entropy potential
\[
I_A(M)=\operatorname{KL}(R_M\|\nu_A),
\]
with the negative-exponent convention,
\[
dI_A(M)[e]=-\langle\theta_A(M),e\rangle,
\qquad
D^2I_A(M)=C_M^{-1}.
\]

For two means in the same open face,
\[
\boxed{
\operatorname{KL}(R_M\|R_N)
=
I_A(M)-I_A(N)-dI_A(N)[M-N].
}
\]

### A valuable consequence

At a model law \(D=R_M\), the differential of the data-to-response map sends a data score \(h\) to its feature-score orthogonal projection. Hence it contracts Fisher norm:
\[
\|\text{response score}\|_{L^2(D)}
\leq \|h\|_{L^2(D)}.
\]

Away from the model, do **not** claim this contraction: data covariance and fitted-model covariance differ.

### Proof route

Reuse chart derivatives, covariance duality, entropy identities, and regression orthogonality. No general Riemannian-manifold framework is necessary.

**Skip:** calling the response map itself a gradient flow. A gradient flow requires a chosen evolution and objective. Also, transport is the fundamental theorem for an exact one-form; a general stratified Stokes theorem is unnecessary here.

---

## Rank 5 — Genuine resolution lower bounds, including boundary leakage

**Suggested modules:** `ResponseTwoPointResolution`, `ResponseBoundaryDetection`

This is the missing other half of N4.

### Part A: tangential two-point lower bounds

For bounded mean-zero \(h\), consider
\[
D_\varepsilon=(1+\varepsilon h)D
\]
for sufficiently small \(\varepsilon\). Then
\[
\chi^2(D_\varepsilon^{\otimes n}\|D^{\otimes n})
=
(1+\varepsilon^2\mathbb E_Dh^2)^n-1.
\]

If a target functional has first derivative \(a\) along this path, its separation at \(\varepsilon=c/\sqrt n\) is
\[
\Delta_n=\frac{ca}{\sqrt n}+O(n^{-1}).
\]

For every estimator \(T\),
\[
\max_{Q\in\{D,D_\varepsilon\}}
\mathbb E_Q(T-\Psi(Q))^2
\geq
\frac{\Delta_n^2}{8}
\left(1-\operatorname{TV}(D^{\otimes n},D_\varepsilon^{\otimes n})\right).
\]

Use M6 to choose the least-cost score producing a prescribed accessible displacement \(e\). Its cost is the singular covariance-dual quadratic form.

This gives a precise meaning to:

> Response distinctions below the covariance-controlled sampling scale cannot be uniformly recovered.

For finitely many chamber labels, even a two-point theorem across one chamber boundary already establishes a meaningful impossibility result.

### Part B: support-changing alternatives have a different scale

Let \(D\) be carried by \(A\), and let \(Q(A)=0\). Put
\[
D_\varepsilon=(1-\varepsilon)D+\varepsilon Q.
\]
Then exactly
\[
\boxed{
\operatorname{TV}(D^{\otimes n},D_\varepsilon^{\otimes n})
=
1-(1-\varepsilon)^n.
}
\]

Thus support leakage becomes detectable at the \(1/n\) scale, not the \(1/\sqrt n\) scale.

This is crucial for a stratified resolution theory:

- support-preserving directions: covariance/Fisher \(n^{-1/2}\) scale;
- new-support contamination: rare-event \(n^{-1}\) scale.

N4’s null directions do not by themselves describe this second phenomenon.

**Skip initially:** full finite-chamber minimax optimisation, LAN, and asymptotic normality. Two-point bounds already establish genuine unresolvability.

---

## Rank 6 — Unrestricted journey calculus and boundary gluing

**Suggested modules:** `ResponsePolytopePathTangency`, `ResponseBoundaryTransport`

### First theorem: remove the stratification condition

Prove automatic tangency for differentiable polytope-valued paths. Deduce N1 with no support-switching assumptions.

### Main extension: absolutely continuous journeys

For every absolutely continuous
\[
M:[0,1]\to\operatorname{conv}S(X),
\]
prove
\[
\boxed{
f_F(M(1))-f_F(M(0))
=
\int_0^1
\langle u_F(M(t)),M'(t)\rangle\,dt.
}
\]

Proof:

1. a Lipschitz function composed with an absolutely continuous path is absolutely continuous;
2. \(M'\) exists almost everywhere;
3. automatic polytope tangency applies at those times;
4. use the existing line-to-path derivative lemma;
5. apply the absolutely continuous FTC.

This permits infinitely complicated face contacts without having to count them.

### Boundary gluing

Use `tendsto_faceProj_regressionDir` to state convergence of **restricted differentials**, rather than full coefficient vectors:
\[
df_F(M_n)|_{W_A}\longrightarrow df_F^A(M)
\]
as interior means approach \(M\in\operatorname{relint}(A)\).

With bounded full fields from Rank 1, this can also control pairings with convergent velocities whose limits lie in \(W_A\).

The intrinsic content is that tangential work glues correctly even when normal coefficients have no canonical boundary limit.

### Second order: deliberately restricted scope

Prove the journey Hessian on intervals contained in a fixed open stratum. Treat boundary contacts separately, explicitly retaining normal acceleration effects.

**Skip:** a universal second-order stratified formula using only the minimal-face Hessian. The Bernoulli example rules it out.

---

# 5. What this programme would establish

The resulting theory would have four complementary components:

1. **Exact transport:** posterior changes are integrals of a face-adaptive response differential along arbitrary absolutely continuous data-mean journeys.
2. **Geometric stability:** response sensitivity is controlled by the interpolation geometry of the feature configuration.
3. **Statistical curvature and refinement:** residual curvature determines bias, while refinement trades local modelling defect against increased sampling variance.
4. **Intrinsic resolution limits:** covariance geometry controls tangential distinguishability; rare-event geometry controls support changes.

Finally, the “featureless law” should be named precisely. With arbitrary base law \(\nu\), the starting point is the **zero-tilt reference law**, or maximiser of relative entropy with respect to that reference—not necessarily the Shannon maximum-entropy law. For uniform \(\nu\) on a finite configuration, those coincide.

**Immediate order of work:** remove the tangency hypothesis; prototype leverage deletion; prove compact-uniform face Taylor bounds. Those three steps unlock most of the remaining programme without a determinant detour or a CLT detour.