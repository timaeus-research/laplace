**Programme M is now close to a coherent local-to-boundary theory.** The next essential steps are M3, M4, and a fixed-base KL expansion for M7. I would not move to third-order ladder calculations yet.

There are three important corrections to the proposed narrative:

1. Your sign-cell proof of M3 is sound, but there is also a **finite-dimensional determinant proof that gives the stronger convex-hull statement without any polyhedral theory**.
2. Fisher metric coefficients can blow up at the boundary while **Fisher distance to the boundary remains finite**. The Euclidean bound is nevertheless genuinely stronger for the purposes here.
3. Chamber width is not the quantity controlling classification error: **distance to the chamber boundary is**. Likewise, the lower-bound scale is covariance-dependent, not uniformly Euclidean \(n^{-1/2}\).

I will separate mathematical statements from suggested Lean organisation; the latter is not meant as checked API code.

## 1. Audit of what landed

There is no apparent mathematical error in the displayed results. Since section variables and hypotheses are elided, this is an audit of their stated mathematical content, not of every elaborated dependency.

### M1: data influence

The derivative and influence variance are exactly the right ones:
\[
D\Psi_F(D)[h]
=\operatorname{Cov}_D(\langle u_F,S\rangle,h),
\qquad
\operatorname{Var}_D(IF_{F,D})=\Sigma_D(u_F,u_F).
\]

The important distinction is correctly maintained:

- \(u_F\) is computed using the **response-law Fisher form**;
- the influence variance is computed using the **data-law covariance**.

The minimum-information lift is also correct. The positive-definiteness assumption is sufficient rather than essential; M6 now supplies its proper replacement.

### M2: joint sampling covariance

The statements have the right leading terms and remainder scale. In particular, no fourth-moment assumption is inherently needed for these reset-localised estimates: the linear–quadratic errors use third moments, while the product of mean errors is controlled by \(M_2^2\).

Two scope qualifications should remain explicit in downstream uses:

- These are covariance estimates for the **reset-localised estimator**, not yet the actual globally defined empirical response.
- The displayed theorem takes a chart radius and cubic remainder bounds as hypotheses. It is an explicit local estimate, not by itself a uniform-in-\(D\) theorem.

For the arbitrary linear retraction `p`, the key supporting fact is that the centred empirical feature mean belongs to \(W\) almost surely, so `p` is the identity on the actual random input. That is what prevents arbitrary retraction norms from entering the displayed constants.

### M5: two-point minimax

The positivity hypothesis
\[
\sigma_F^2=\Sigma_D(u_F,u_F)>0
\]
is exactly what makes this first-order construction separate the functional values. When it vanishes, the theorem should not manufacture an \(n^{-1/2}\) obstruction; higher-order or support-changing alternatives are a different problem.

There is one important nonvacuity qualification. Writing \(\sigma_F=\sqrt{\sigma_F^2}\), the limit is positive only when
\[
0<a\sigma_F<\sqrt2.
\]
For larger \(a\), the theorem remains true but gives a nonpositive asymptotic lower bound.

A useful short companion is the optimised choice
\[
a=\frac{1}{\sqrt2\,\sigma_F},
\qquad
\sqrt n\,L_n\longrightarrow \frac{\sigma_F}{4\sqrt2}.
\]
This turns the existing theorem into an immediately readable positive resolution obstruction. It does **not** assert a sharp asymptotic minimax constant.

### Companions

Idempotence and saturation are correct and important.

For saturation, `genRate ≠ ⊤` is the natural safe hypothesis for the existing projection API. It is weaker than assuming \(KL(D\Vert\nu)<\infty\): it only asks that the moment constraint have finite optimal rate.

In the finite full-support setting, this finiteness hypothesis is automatic for every feasible mean. Prove that specialisation and remove the hypothesis from the finite-configuration corollary.

Also keep in mind how strong `SpansAffine` is: it is exact saturation of all bounded measurable observables modulo \(\nu\), not merely separation of points or density in some function class.

### M6: singular covariance

The annihilation condition is precisely right:
\[
\langle u,e\rangle=0\quad\text{for every }u\in\ker\Sigma_D.
\]
It characterises which functionals descend to the covariance quotient and hence which velocities are attainable by bounded scores.

Two interpretation points:

- `dataDualSing` is a representative, not necessarily a canonically chosen Moore–Penrose vector. Its covariance energy is canonical.
- Your definition permits \(e:J\to\mathbb R\), rather than \(e\in W\). Every displayed pairing sees only the component of \(e\) in \(W\). For a literal “response velocity” statement, use \(e\in W\), or state that the represented velocity is its Euclidean projection onto \(W\).

The off-annihilator SNR result is valid. But “unbounded SNR” here is an algebraic statement about noiseless feature directions. It is **not** a claim that such displacements are attainable by dominated bounded-score perturbations; `annihilator_of_lift` proves exactly the contrary.

---

## 2. M3: the sign-cell route is sound

Work with the finite-dimensional coefficient space
\[
B=\mathbb R\times W
\]
and regard \(a_x\) as the linear functional
\[
a_x(c,u)=c+\langle u,S(x)\rangle.
\]
This avoids pretending that the raw vector \(S(x)\) itself belongs to \(W\).

### 2.1 Audit of the bounded-cell argument

Your cell definition is correct:

- for \(\sigma_x=\pm1\), impose the corresponding weak residual inequality;
- for \(\sigma_x=0\), impose the exact residual equality.

The exact equalities on the zero coordinates are essential.

Also essential is that the witness has **exact sign pattern** \(\sigma\). Mere membership of a least-squares minimiser in the closed cell would not suffice.

For a recession direction \(v\), one obtains
\[
\sigma_x a_x(v)\ge0
\quad(\sigma_x\ne0),
\qquad
a_x(v)=0
\quad(\sigma_x=0).
\]
Since \(\sigma_x=\operatorname{sign}(r_x)\), this implies
\[
r_xa_x(v)\ge0.
\]
Pairing the normal equations with \(v\) yields
\[
0=\sum_x p_xr_xa_x(v).
\]
Every \(p_x\) is strictly positive, so every product vanishes. Thus:

- if \(r_x\ne0\), then \(a_x(v)=0\);
- if \(r_x=0\), the cell equality already gives \(a_x(v)=0\).

Injectivity of the design map gives \(v=0\), a contradiction.

**So step 2 is airtight with the exact-pattern qualification.**

### 2.2 A cheaper version of your proof

You do not need a general theorem producing a recession ray from an unbounded convex set.

Choose \(b_n\in C_\sigma\) with
\[
\|b_n-\beta\|\to\infty,
\qquad
v_n=\frac{b_n-\beta}{\|b_n-\beta\|}.
\]
Extract a convergent subsequence \(v_n\to v\), with \(\|v\|=1\).

Divide each cell inequality by \(\|b_n-\beta\|\) and pass to the limit:
\[
0\le
\frac{\sigma_x r_x(\beta)}{\|b_n-\beta\|}
+\sigma_xa_x(v_n)
\quad\Longrightarrow\quad
\sigma_xa_x(v)\ge0.
\]
The zero-sign equalities give \(a_x(v)=0\) directly.

Then use the normal-equation argument above. This eliminates convexity, closedness, and recession-ray infrastructure from the proof.

For the uniform bound, it is also unnecessary to define a supremum for each cell. Prove:

> Every realised sign pattern admits a radius bounding its cell.

Then combine the finitely many radii using finite choice and a finite maximum.

### 2.3 An alternative: weighted interpolation gives the convex hull directly

There is a useful stronger route that requires **no vertex theory at all**.

Choose coordinates on \(B\), let \(d=\dim B\), and let \(A\) be the design matrix with rows \(a_x\). For each \(d\)-element subset \(I\subseteq X\) with invertible \(A_I\), define the interpolating fit
\[
b_I=A_I^{-1}F_I.
\]
For positive weights \(p_x\), the weighted least-squares fit satisfies
\[
\boxed{\quad
\beta(p)=\sum_I \lambda_I(p)b_I,
\qquad
\lambda_I(p)=
\frac{\det(A_I)^2\prod_{x\in I}p_x}
{\sum_K\det(A_K)^2\prod_{x\in K}p_x}.
\quad}
\]
The coefficients are nonnegative and sum to one.

This follows from Cauchy–Binet plus Cramer’s rule. For each coordinate, replace the corresponding column of \(A\) by \(F\), apply Cauchy–Binet to the resulting normal-equation determinant, and identify the interpolating coordinate by Cramer’s rule.

Consequently,
\[
\|\beta(p)\|\le \max_I\|b_I\|.
\]

This proves the convex-hull statement that the earlier polyhedral route sought. It also yields a configuration-dependent operator bound
\[
\|u_F(p)\|\le C_{S,\nu}\|F\|_\infty.
\]

**Lean recommendation:** use the normalised-sequence sign-cell argument if compactness is already comfortable in the seabed. Use the determinant route if Cauchy–Binet and matrix-coordinate infrastructure are readily available. The determinant identity is mathematically stronger, but not obviously shorter to formalise.

M4 needs only the bound, not the convex-hull representation.

---

## 3. What the free Fisher bound does—and does not—give

From the regression identity,
\[
G_\theta(u_F,u_F)
=\operatorname{Cov}_{P_\theta}(F,\langle u_F,S\rangle).
\]
Cauchy–Schwarz gives
\[
G_\theta(u_F,u_F)\le \operatorname{Var}_{P_\theta}(F).
\]
If \(|F|\le B\), then
\[
\sqrt{G_\theta(u_F,u_F)}\le B.
\]
Thus \(2B\) is safe but unnecessary under an absolute-value bound by \(B\).

This indeed gives a Fisher-distance Lipschitz estimate. In natural parameters,
\[
\left|\frac d{dt}E_{P_{\theta(t)}}F\right|
\le B\sqrt{G_{\theta(t)}(\dot\theta,\dot\theta)}.
\]
In mean coordinates the corresponding metric is the inverse Fisher form.

However:

> The Fisher metric tensor may diverge at the boundary without the boundary being infinitely far away.

For Bernoulli mean \(m\),
\[
ds^2=\frac{dm^2}{m(1-m)},
\]
and the boundary is at finite Fisher distance. Near \(m=0\), distance scales like \(\sqrt m\), not \(m\).

So your proposed explanation should be adjusted. The Euclidean result matters because:

- Fisher control alone does not imply a linear modulus in Euclidean mean displacement;
- it does not bound coefficients in covariance directions that are degenerating;
- M4 requires exactly that coefficient control.

The Euclidean Lipschitz theorem has real additional content even when all relevant Fisher journeys have finite length.

---

## 4. M4: the precise facewise statement

Let \(C=\operatorname{conv}S(X)\). Let \(A\) denote a face, with support atoms \(X_A\), and set
\[
W_A=\operatorname{span}\{S(x)-S(y):x,y\in X_A\}\subseteq W.
\]
Let
\[
\pi_A:W\to W_A
\]
be the **Euclidean orthogonal projection for `dotJ`**.

Take \(M\in\operatorname{relint}(A)\). Write
\[
R_M=P^A_v
\]
using the face chart, and let \(u_H^A(v)\in W_A\) be the regression direction defined with the face Fisher form.

### M4 theorem

For every sequence \(M_k\in\Omega_m\) with \(M_k\to M\),
\[
\boxed{\quad
\pi_A\!\left(u_H(\theta_r(M_k))\right)
\longrightarrow u_H^A(v).
\quad}
\]

Equivalently, after embedding \(W_A\) into \(W\), the projected ambient regression directions converge to the embedded face regression direction.

The limit is a **tangential derivative on the face**. There is no assertion of a canonical limit of the full ambient \(u_H\).

At a vertex, \(W_A=0\), and the statement correctly becomes trivial.

### Best proof organisation

First prove a law-level regression stability lemma:

> If \(P_k\to P_A\) in \(L^1\), the ambient regression directions are uniformly bounded, and the covariance of \(P_A\) is positive definite on \(W_A\), then their \(W_A\)-projections converge to the face regression direction.

For \(w\in W_A\),
\[
\operatorname{Cov}_{P_k}
(\langle u_k,S\rangle,\langle w,S\rangle)
=
\operatorname{Cov}_{P_k}(H,\langle w,S\rangle).
\]

On the face, \(\langle u_k-\pi_Au_k,S\rangle\) is constant. Therefore
\[
\operatorname{Cov}_{P_A}
(\langle u_k,S\rangle,\langle w,S\rangle)
=
G_A(\pi_Au_k,w).
\]
Covariance continuity, together with the uniform bound on \(u_k\), allows replacement of \(P_k\) by \(P_A\). Positive definiteness of \(G_A\) then identifies the limit.

There is a useful quantitative version. In Euclidean operator notation, let \(C_k,C_A\) be covariance operators and \(c_k,c_A\) the \(H\)-covariance vectors. If \(\|u_k\|\le L_H\), then
\[
\boxed{\quad
\|\pi_Au_k-u_H^A\|
\le
\lambda_A^{-1}
\bigl(\|c_k-c_A\|+\|C_k-C_A\|L_H\bigr),
\quad}
\]
where \(\lambda_A>0\) is the smallest face covariance eigenvalue.

You can formalise this using the norm of the inverse face covariance map instead of eigenvalues.

### Dependency on boundary continuity

K1’s boundary journey supplies convergence along a particular path, not automatically along every \(M_k\to M\).

The clean chain is:

1. M3 gives a Lipschitz extension of every observable response.
2. K1 identifies its boundary value with \(E_{R_M}H\).
3. Apply this to atom indicators to obtain \(R_{M_k}\to R_M\) in \(L^1\).
4. Apply the law-level M4 lemma.

This is noncircular. M4 is not needed to identify the continuous boundary extension.

**Size:** the law-level stability lemma is modest once M3 exists. Face-chart coercions and identifying the embedded regression direction are likely to be the larger formalisation cost.

---

## 5. M7: use a common model base, not merely common interior means

The correct base hypothesis is
\[
D=P^S_{\theta_0}.
\]
With `Refines S T ν`, \(D\) is also a \(T\)-model law: the log density of \(D\) relative to \(\nu\) is affine in \(S\), hence affine in \(T\).

Merely requiring that \(m_S(D)\) and \(m_T(D)\) are interior is **not enough**. Then the two response laws at \(t=0\) can differ, and their KL gap need not even vanish.

For a first theorem, it is reasonable to accept explicitly
\[
D=P^S_{\theta_0}=P^T_{\eta_0},
\]
and provide a separate refinement lemma supplying \(\eta_0\).

Let
\[
D_t=D.\mathrm{tilted}(th),\qquad
R_S(t)=R^S_{m_S(D_t)},\qquad
R_T(t)=R^T_{m_T(D_t)}
\]
for bounded \(h\). Set
\[
g_S=\langle u_h^S,S\rangle,\qquad
g_T=\langle u_h^T,T\rangle.
\]

### M7 statement

As \(t\to0\), \(t\ne0\),
\[
\boxed{
\frac{KL(R_T(t)\Vert R_S(t))}{t^2}
\longrightarrow
\frac12\left(
\operatorname{Var}_D(g_T)-\operatorname{Var}_D(g_S)
\right)
=
\frac12\operatorname{Var}_D(g_T-g_S).
}
\]

The last equality is the nested-projection Pythagorean identity. No identification of the raw, uncentred functions as orthogonal projections is required: their centred versions are the projections of \(h-E_Dh\).

In Lean, use the punctured neighbourhood filter and finite KL real values, or `.toReal` with local finiteness already established.

### 5.1 The exact identity that removes the cross term

Because \(D\) and \(R_S(t)\) are \(S\)-model laws and \(R_T(t)\) has the same \(S\)-moments as \(R_S(t)\),
\[
\boxed{
KL(R_T(t)\Vert D)
=
KL(R_T(t)\Vert R_S(t))
+
KL(R_S(t)\Vert D).
}
\]

There is **no cross term**.

Likewise,
\[
\boxed{
KL(D_t\Vert D)
=
KL(D_t\Vert R_S(t))
+
KL(R_S(t)\Vert D).
}
\]

These follow because
\(\log(dR_S(t)/dD)\) is affine in \(S\), so its expectations agree under the relevant moment-matching laws.

A reusable “Pythagoras relative to a model base” theorem is the right bridge here.

### 5.2 The main analytic lemma

Prove first
\[
\boxed{
\frac{KL(R_S(t)\Vert D)}{t^2}
\longrightarrow
\frac12\operatorname{Var}_D(g_S).
}
\]

The response parameter path is
\[
\theta(t)=\theta_r(m_S(D_t)).
\]
With your negative-exponent convention,
\[
\boxed{\theta'(0)=-u_h^S.}
\]
Indeed,
\[
m'_S(0)=\operatorname{Cov}_D(S,h),
\qquad
Dm_{\theta_0}=-G_{\theta_0}
\]
under the Euclidean identification.

Now use the local model-law KL expansion:
\[
KL(P_{\theta_0+\delta}\Vert P_{\theta_0})
=
\frac12G_{\theta_0}(\delta,\delta)+o(\|\delta\|^2).
\]
Since
\[
\theta(t)-\theta_0=-t\,u_h^S+o(t),
\]
the claimed limit follows.

This requires only first-order differentiability of the response parameter path plus the second-order KL expansion. It avoids differentiating the whole moving-law KL expression twice.

### 5.3 The defect theorem is true and worth landing

Combining the exact identity with the existing tilt expansion gives
\[
\boxed{
\frac{KL(D_t\Vert R_S(t))}{t^2}
\longrightarrow
\frac12\left(
\operatorname{Var}_D(h)-\operatorname{Var}_D(g_S)
\right)
=
\frac12\operatorname{Var}_D(h-g_S).
}
\]

This is precisely:

> **To second order, information invisible to the response is the variance of the score residual.**

It deserves its own theorem, not merely an intermediate calculation.

Then M7 follows either by subtracting the two defect limits using the existing ladder, or—more directly—by subtracting the two response-to-base limits using the exact identity above.

### Suggested order inside M7

1. Common-base representation under refinement.
2. Relative-base Pythagoras.
3. Response parameter velocity \(=-u_h\).
4. Response-to-base KL quadratic limit.
5. Defect quadratic limit.
6. Nested score covariance identity and infinitesimal ladder.

The substantive analytic work is item 4. The rest should mostly reuse moment matching, regression identities, and existing KL algebra.

---

## 6. After M: the six highest-value targets

### 1. Global closed-polytope response and law-valued retraction

Prove
\[
|E_{R_M}F-E_{R_N}F|\le L_F\|M-N\|,
\qquad M,N\in C.
\]
Then apply this to atom indicators to obtain a law-valued Lipschitz bound
\[
\|R_M-R_N\|_1\le L_R\|M-N\|.
\]

For finite \(X\), define
\[
\mathcal R(D)=R_{m_D}.
\]
This is a Lipschitz retraction of the data simplex onto the **embedded closed exponential family**
\[
\{R_M:M\in C\}\subseteq\Delta(X).
\]

Be precise about the geometry:

- \(D\mapsto m_D\) maps the simplex onto the polytope.
- \(M\mapsto R_M\) is its section.
- Their composite is the actual retraction.
- Fibres are moment fibres, not KL level sets; KL supplies their Pythagorean geometry.

If `Φ` denotes natural parameters rather than mean coordinates or response laws, do not extend this conclusion to `Φ`: natural parameters generally diverge at the boundary.

### 2. A canonical base-to-data journey with an exact response integral

Let \(\nu_0\) be the normalised reference law, and take
\[
D_t=(1-t)\nu_0+tD,\qquad
M_t=(1-t)m_{\nu_0}+tm_D.
\]
Then
\[
Q_t=R_{M_t}
\]
is a canonical response journey with
\[
Q_0=\nu_0,\qquad Q_1=R_{m_D}.
\]
For \(t<1\), the means are interior when \(\nu_0\) has full support.

M3 should give the endpoint-valid identity
\[
\boxed{
E_{Q_1}F-E_{Q_0}F
=
\int_0^1
\left\langle
u_F(\theta_r(M_t)),m_D-m_{\nu_0}
\right\rangle\,dt.
}
\]

This directly answers the standing direction: the total change in posterior expectation is the integral of its response field along a canonical path through the data manifold.

The endpoint is \(D\) only under saturation. And \(\nu_0\) is the featureless minimum-relative-information law; it is the maximal Shannon-entropy law only when the reference is uniform.

### 3. Uniform, unlocalised empirical response risk

With empirical mean \(\widehat M_n\), use the actual estimator
\[
\widehat\Psi_F=E_{R_{\widehat M_n}}F,
\]
including boundary empirical means. Then
\[
E_D|\widehat\Psi_F-\Psi_F(D)|
\le
L_F\sqrt{\frac{\operatorname{tr}\operatorname{Cov}_D(S)}n}
\le \frac{C_{S,F}}{\sqrt n}.
\]
Also
\[
E_D|\widehat\Psi_F-\Psi_F(D)|^2
\le
\frac{L_F^2\operatorname{tr}\operatorname{Cov}_D(S)}n.
\]

This is more valuable now than another local asymptotic coefficient: it removes localisation, handles faces, and is uniform over all data laws on the finite configuration.

Second moments suffice; Hoeffding is unnecessary for these expectation bounds. Add exponential tails afterward if convenient.

### 4. The correct chamber-resolution theorem

For the chamber \(C_D\) containing \(m_D\), define its margin
\[
r_D=\operatorname{dist}(m_D,\text{points assigned to other chambers}).
\]
If \(r_D>0\), then
\[
\Pr_D(\text{wrong chamber})
\le
\Pr_D(\|\widehat M_n-m_D\|\ge r_D)
\le
\frac{\operatorname{tr}\operatorname{Cov}_D(S)}
{nr_D^2}.
\]

A chamber’s width alone cannot imply this: the true mean may lie arbitrarily close to its boundary.

For the lower bound, use M6’s least-information score for an attainable direction \(e\):
\[
I_D(e)=\langle e,\Sigma_D^+e\rangle.
\]
Its tilt gives
\[
m(D_t)=m(D)+te+o(t),
\qquad
KL(D_t\Vert D)=\frac{t^2}{2}I_D(e)+o(t^2).
\]
If the alternatives lie in different chambers and \(nt^2I_D(e)\) is small, Le Cam obstructs reliable classification.

Thus the correct slogan is:

> **Chambers below the local information scale are unresolvable, when they are separated along an attainable direction.**

There is no universal Euclidean \(n^{-1/2}\) boundary statement. Singular strata and support-changing alternatives can have different scales.

### 5. The global refinement information budget

For a finite nested ladder with \(R_0=\nu_0\),
\[
KL(D\Vert\nu_0)
=
KL(D\Vert R_K)
+
\sum_{k<K}KL(R_{k+1}\Vert R_k).
\]
If the last family is saturated, \(R_K=D\), and
\[
\boxed{
KL(D\Vert\nu_0)
=
\sum_{k<K}KL(R_{k+1}\Vert R_k).
}
\]

Add the observable consequence
\[
|E_DF-E_{R_K}F|
\le
\operatorname{osc}(F)
\sqrt{\frac{KL(D\Vert R_K)}2}.
\]

This supplies a genuine stopping criterion for refinement: remaining unresolved information bounds remaining observable error.

The finite telescoping identity itself is inexpensive; the information-to-observable certificate makes it more than packaging.

### 6. Matched upper and lower local resolution in several observables

For \(F_1,\ldots,F_r\), define
\[
V_{ij}=\Sigma_D(u_{F_i},u_{F_j}).
\]
M2 already gives the estimator’s leading joint covariance. Combine M1, M5, and M6 to show that every scalar contrast has the corresponding local two-point obstruction, including singular contrasts.

This makes \(V/n\) an **observable resolution ellipsoid**, not merely an asymptotic covariance matrix. It is a direct, interpretable map of which combinations of posterior expectations the data can resolve.

## What to defer

- **Third-order M7:** defer. Cubic coefficients are coordinate- and path-sensitive, and they do not yet improve the global response or resolution story.
- **Product-KL additivity:** useful infrastructure, especially for cleaner testing constants, but not the next conceptual milestone.
- **Full ambient regression convergence at faces:** do not make it the target. Tangential convergence is the intrinsic statement.
- **A universal chamber-width lower bound:** skip in that form; replace it by the margin upper bound and attainable-direction information lower bound.

The resulting architecture is particularly clean:

\[
\boxed{
\begin{array}{c}
\text{M3: global stability in mean coordinates}\\
\Downarrow\\
\text{M4: compatible tangential calculus on every face}\\
\Downarrow\\
\text{canonical global response journeys}
\end{array}
\qquad
\begin{array}{c}
\text{M7: resolved versus invisible score information}\\
\Downarrow\\
\text{global refinement information budget}\\
\Downarrow\\
\text{sampling-calibrated resolution}
\end{array}
}
\]

That connects the featureless reference, the actual data, the geometry of posterior expectation changes, and the sampling limit on how finely that geometry can be resolved.