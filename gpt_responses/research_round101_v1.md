## Verdict

Programme K has reached a real milestone: **the response exists globally as a law, even where its natural parameter ceases to exist**. Programme L should now make that global response quantitatively useful for observables and statistical decisions.

Three points deserve emphasis:

1. **K4 has the correct weight.**
2. **K5 has the correct mean-coordinate influence, but its Fisher-coordinate expression has a minus sign**, because your exponential family uses `−⟨θ,S⟩`.
3. There is a stronger boundary result worth pursuing than mere convergence: **for a fixed finite feature configuration, every posterior expectation is globally Lipschitz in the mean**. A finite weighted-regression identity appears to provide a particularly beautiful proof. This would remove localisation from several qualitative sampling and chamber statements.

I would not spend a principal programme-L slot on extrinsic Gauss.

---

# 1. Audit of K4–K6

## K4: the information budget is correctly oriented

Write
\[
P_t=P_{\theta_t},\qquad e=m_D-m_0,\qquad
V_t=A_{\theta_t}^{-1}e,\qquad
g(t)=G_{\theta_t}(V_t,V_t).
\]

With your sign convention,
\[
A_\theta=-K_\theta,
\]
where \(K_\theta\) is the covariance operator of the features on \(W\).

Let
\[
H(M)=\mathrm{KL}(R_M\|\nu).
\]
On the relative interior,
\[
DH(M)[e]=-\langle\theta_r(M),e\rangle,\qquad
D^2H(M)[e,e]=G_\theta(A_\theta^{-1}e,A_\theta^{-1}e).
\]
Along the journey, \(H'(0)=0\). Consequently,
\[
\mathrm{KL}(P_T\|\nu)=\int_0^T(T-t)g(t)\,dt.
\]

Thus **the boundary weight \(1-t\) is exactly right**.

### The reverse formula

For \(T<1\),
\[
\boxed{\mathrm{KL}(\nu\|P_T)=\int_0^T t\,g(t)\,dt.}
\]

At the endpoint, the correct general statement is extended-real:
\[
\boxed{\mathrm{KL}(\nu\|R_D)=\int_0^1 t\,g(t)\,dt\in[0,\infty].}
\]

There is an important dichotomy:

- If \(m_D\) is in the relative interior, both sides are finite.
- If \(m_D\) lies in a proper face and \(\nu\) charges every atom, \(R_D\) vanishes somewhere that \(\nu\) does not. Both sides are \(+\infty\).

So this is worth landing, but **not as a universal equality of `toReal`s**. `ENNReal.toReal ∞ = 0` would destroy its mathematical meaning.

A useful companion is
\[
\mathrm{KL}(P_T\|\nu)+\mathrm{KL}(\nu\|P_T)
=T\int_0^Tg(t)\,dt.
\]

### A more valuable new orientation

The most useful next budget is arguably neither forward nor reverse, but **remaining information relative to the target**:
\[
\boxed{
\mathrm{KL}(R_D\|P_t)
=\int_t^1(1-s)g(s)\,ds.
}
\]

It implies
\[
\boxed{
\mathrm{KL}(D\|P_t)
=\mathrm{KL}(D\|R_D)+\int_t^1(1-s)g(s)\,ds.
}
\]

This tells us exactly how much of the present prediction error is still removable by continuing the journey, and how much is irreducibly invisible to the features.

One should not infer a naive additive decomposition using
\(\mathrm{KL}(P_t\|\nu)\): Bregman divergences do not telescope that way.

---

## K5: correct, but the Gram matrix should be the headline

The fundamental result is
\[
G_\theta(u_F,v)
=\operatorname{Cov}_{P_\theta}(F,\langle v,S\rangle).
\]

Its two principal consequences are:

1. **Regression/Pythagoras:** which part of an observable the response can move.
2. **The sampling Gram matrix:** how those movable parts fluctuate jointly.

The resolution floor is an excellent corollary, but not the organising theorem.

### The sign in Fisher coordinates

Your mean-coordinate derivative is correct:
\[
D\bigl(M\mapsto E_{R_M}F\bigr)[e]=\langle u_F,e\rangle.
\]

Since \(A=-K\),
\[
\boxed{
\langle u_F,e\rangle
=-G_\theta(u_F,A_\theta^{-1}e).
}
\]

Therefore the proposed expression \(G(u_F,A^{-1}e)\), without a minus sign, is not the same influence.

Equivalently, along a natural-parameter velocity \(V\),
\[
\frac d{dt}E_{P_{\theta_t}}F
=-G_{\theta_t}(u_F,V).
\]

Both coordinate descriptions are useful; neither needs to replace the other.

For a data-law perturbation, the corresponding centred influence function is
\[
\boxed{
\psi_{F,D}(x)
=\langle u_F(\theta_r(m_D)),S(x)-m_D\rangle.
}
\]
At a matched law this is precisely the centred feature-regression fit of \(F\).

### What the resolution floor does—and does not—say

The theorem correctly transfers a **linearised signal-to-noise criterion** from an observable to the structural displacement. Its positive-explained-variance hypothesis is necessary: a constant response observable has neither signal nor noise.

But it is not yet a statistical impossibility theorem about all procedures or nonlinear chamber classifiers. That requires a testing bound. I recommend adding one in L.

---

## K6: correct under saturation; do not generalise the isometry

For a saturated family, the positive model is the positive simplex. Its intrinsic Fisher distance really is
\[
d(p,q)=2\arccos\sum_x\sqrt{p_xq_x}.
\]
The positive orthant’s short spherical arcs stay positive, so there is no intrinsic-versus-ambient discrepancy there.

The completion statement is consequently correct and substantial.

The chord estimate is also correct:
\[
2\alpha\le \pi\|\sqrt p-\sqrt q\|.
\]
Here the root vectors have norm one. The constant is not sharp on the positive orthant, but that is not a programme-worthy issue.

### The important hypothesis audit

For a **non-saturated** exponential family, generally only
\[
d_{\mathrm{spherical}}(P,Q)\le d_{\mathrm{Fisher,intrinsic}}(P,Q)
\]
holds. Equality need not hold.

For example, a one-parameter family on three atoms with feature values \(0,1,2\) gives a root-vector curve that is not a great circle. Its intrinsic lengths cannot generally equal ambient spherical distances.

Thus inspect the fully elaborated type of `isometry_toSph`:

- Is `hspan` genuinely among its hypotheses?
- Does `FisherSpace` carry the intrinsic path metric, rather than an ambient metric introduced by definition?

The completion proof’s application of `isometry_toSph ... hspan` suggests the saturation hypothesis is present, but the abbreviated theorem display alone does not establish this.

Diameter \(\pi\) is attained when there are at least two atoms. For one atom the diameter is zero. Neither case threatens the theorem as stated.

---

# 2. Programme L: seven ranked targets

My proposed theme is:

> **Globally regular observable responses, quantitatively calibrated against sampling and feature blindness.**

## L1. A finite regression convex-hull theorem, hence global Lipschitz response

**Highest-value new structural theorem.**  
Suggested modules: `ResponseRegressionConvexHull`, `ResponseObservableLipschitz`.

Let \(d=\dim W\). Choose affine coordinates for the feature configuration. Let \(\mathcal B\) be the finite collection of subsets \(B\subseteq X\) of size \(d+1\) on which the feature vectors are affinely independent.

For each \(B\in\mathcal B\), there is a unique affine interpolant
\[
a_B+\langle u_B,S(x)\rangle=F(x),\qquad x\in B,
\]
with \(u_B\in W\).

For **any strictly positive law \(p\)**, let \(u_F(p)\) be its covariance-regression direction. Then
\[
\boxed{
u_F(p)=\sum_{B\in\mathcal B}\lambda_B(p)u_B,
\qquad
\lambda_B(p)\ge0,\quad \sum_B\lambda_B(p)=1.
}
\]

In coordinates, if \(Z_B\) is the square affine-design matrix,
\[
\lambda_B(p)=
\frac{\det(Z_B)^2\prod_{x\in B}p_x}
{\sum_{C\in\mathcal B}\det(Z_C)^2\prod_{x\in C}p_x}.
\]

This is the weighted least-squares/volume-sampling identity, obtained from Cauchy–Binet and Cramer’s rule.

### Consequence: regression directions do not blow up

Set
\[
L_F=\max_{B\in\mathcal B}\|u_B\|.
\]
Then
\[
\boxed{\|u_F(p)\|\le L_F}
\]
uniformly over all positive laws.

This matters for your boundary question. In a fixed finite feature configuration, degeneration of the Fisher matrix does **not** by itself imply divergence of the regression direction for a fixed observable: its covariance right-hand side degenerates compatibly.

### Consequence: the entire closed response is Lipschitz

Using the mean derivative and then the continuous boundary extension,
\[
\boxed{
|E_{R_M}F-E_{R_N}F|
\le L_F\|M-N\|
}
\]
for all \(M,N\) in the moment polytope.

In particular,
\[
\boxed{
|E_{P_t}F-E_{R_D}F|
\le L_F(1-t)\|m_D-m_0\|.
}
\]

Taking atom indicators also gives a global Lipschitz bound for the response-law map into total variation, with a feature-configuration-dependent constant.

This is considerably stronger than endpoint convergence.

### Observable journey variation

Now one can genuinely prove
\[
\operatorname{Var}_{[a,b]}
\bigl(t\mapsto E_{P_t}F\bigr)
\le L_F\|e\|(b-a),
\]
and an absolutely convergent endpoint fundamental theorem:
\[
\boxed{
E_{R_D}F-E_\nu F
=\int_0^1\langle u_F(\theta_t),e\rangle\,dt.
}
\]

Notice that the derivative is **not**
\(\langle u_F,\dot\theta_t\rangle\).

**Proof size:** medium–large. The main investment is one finite linear-algebra identity; the response consequences should be short. This avoids difficult boundary asymptotics, Puiseux expansions, or o-minimal machinery.

**Important limitation:** \(L_F\) can be large for a poorly conditioned feature configuration. This is not a universal geometry-free bound.

---

## L2. Second-order sampling calculus for nonlinear posterior expectations

Suggested module: `ResponseObservableIIDExpansion`.

Assume \(m_D\) is interior and put \(\theta_0=\theta_r(m_D)\), without assuming \(D=P_{\theta_0}\). Define
\[
f_F(M)=E_{R_M}F.
\]

For \(e,h\in W\), let
\[
V_e=A_{\theta_0}^{-1}e,\qquad V_h=A_{\theta_0}^{-1}h.
\]
The crucial Hessian theorem is
\[
\boxed{
D^2f_F(m_D)[e,h]
=
E_{P_{\theta_0}}\!\left[
(F-E_{P_{\theta_0}}F)\,r_{V_eV_h}
\right].
}
\]

This is the clean observable counterpart of the connection bias.

### Nonlinear bias

For the reset-localised empirical response,
\[
\boxed{
E[\widehat f_{F,\mathrm{loc}}]-f_F(m_D)
=
\frac1{2n}\operatorname{tr}(\Sigma_DD^2f_F(m_D))
+O(n^{-3/2}).
}
\]

The sign is worth stressing: **the observable bias is not simply the negative connection-bias formula with \(F\) applied afterward**. The outer observable’s Hessian contributes too. The combined answer is the positive one-half contraction above.

### Nonlinear covariance

For two observables,
\[
\boxed{
\operatorname{Cov}(\widehat f_{F,\mathrm{loc}},
                   \widehat f_{H,\mathrm{loc}})
=
\frac1n
\operatorname{Cov}_D
\bigl(\langle u_F,S\rangle,\langle u_H,S\rangle\bigr)
+O(n^{-3/2}).
}
\]

At a matched law, its leading term is \(G(u_F,u_H)/n\).

**Proof route:** scalar Taylor expansion, the residual Hessian identity, K2’s third/fourth moment bounds, and the same localisation-tail bookkeeping already used for structural bias.

**Proof size:** medium. State explicit inequalities with explicit Taylor constants, not just asymptotic notation.

**Sanity checks:**

- If \(F\) is affine in \(S\), its response Hessian vanishes.
- For a saturated family every observable is affine in the mean. The unlocalised response is the empirical law, so the bias vanishes exactly and the covariance formula is exact.

L1 also permits replacing localisation by the actual globally defined empirical response, with a tail estimate controlling the difference.

---

## L3. The remaining-information theorem and observable error certificates

Suggested module: `ResponseJourneyRemainingInformation`.

Define
\[
\delta_D=\mathrm{KL}(D\|R_D),\qquad
\mathcal R(t)=\int_t^1(1-s)g(s)\,ds.
\]

Prove simultaneously:
\[
\boxed{
\mathrm{KL}(R_D\|P_t)=\mathcal R(t),\qquad
\mathrm{KL}(D\|P_t)=\delta_D+\mathcal R(t).
}
\]

For \(t<1\),
\[
\frac d{dt}\mathrm{KL}(D\|P_t)=-(1-t)g(t).
\]

This is a genuinely useful information budget: **continuing the response journey decreases data-to-model KL monotonically, down to exactly the feature-blindness defect**.

### Observable transfer with the right constants

Let \(\operatorname{osc}(F)=\max F-\min F\). Pinsker gives
\[
|E_DF-E_{P_t}F|
\le
\operatorname{osc}(F)
\sqrt{\frac{\delta_D+\mathcal R(t)}2}.
\]

A sharper structural formulation subtracts any affine feature predictor. For any \(a\in W\),
\[
\boxed{
\begin{aligned}
&\left|
E_DF-E_{P_t}F-\langle a,m_D-m_t\rangle
\right|\\
&\qquad\le
\operatorname{osc}(F-\langle a,S\rangle)
\sqrt{\frac{\delta_D+\mathcal R(t)}2}.
\end{aligned}
}
\]

At the endpoint,
\[
\boxed{
|E_DF-E_{R_D}F|
\le
\inf_a\operatorname{osc}(F-\langle a,S\rangle)
\sqrt{\frac{\delta_D}2}.
}
\]

This says more than a bound using \(\|F\|_\infty\): **only the feature-unexplained part of the observable can detect invisible information**.

Also useful:
\[
|E_{P_t}F-E_{R_D}F|
\le \operatorname{osc}(F)\sqrt{\mathcal R(t)/2}.
\]

**Proof size:** medium, probably smaller than L1. Use finite Bregman identities, K1 endpoint convergence, K4 integrability, then finite-law Pinsker.

**Caution:** K4’s weighted energy alone does not imply finite Fisher length or finite observable variation. A naive Cauchy–Schwarz argument introduces \(\int(1-t)^{-1}dt\). L1 supplies the missing observable regularity directly.

---

## L4. Misspecified resolution geometry and genuine chamber guarantees

Suggested modules: `ResponseMismatchResolution`, `ResponseChamberSampling`.

At an interior data mean, define
\[
\Sigma_D(u,v)
=\operatorname{Cov}_D(\langle u,S\rangle,\langle v,S\rangle).
\]

The correct sampling geometry is \(\Sigma_D\), not the model Fisher form. For an observable,
\[
\text{signal}=\langle u_F,e\rangle,\qquad
\text{noise variance}=\Sigma_D(u_F,u_F)/n.
\]

### Optimal observable resolution

If \(\Sigma_D\) is positive definite on \(W\),
\[
\boxed{
\sup_{u\ne0}
\frac{n\langle u,e\rangle^2}{\Sigma_D(u,u)}
=
n\langle e,\Sigma_D^{-1}e\rangle.
}
\]

Every \(u\) is realised by the observable \(F=\langle u,S\rangle\), so this is genuinely an optimisation over posterior observables.

At a matched law it reduces to K5’s structural Fisher signal.

Do not silently assume positive definiteness from an interior mean. An interior mean can be realised by a law supported on a lower-dimensional configuration. In the singular case:

- use the covariance inverse on its range;
- a displacement with a component in a noiseless direction can have infinite linearised signal-to-noise ratio.

### Nonlinear chamber membership

Suppose a chamber is defined by finitely many inequalities
\[
f_{F_k}(M)>c_k.
\]
If the true margins are \(\gamma_k>0\), L1 gives the deterministic certificate
\[
\boxed{
\|\widehat M_n-m_D\|
<
\min_k\frac{\gamma_k}{L_{F_k}}
\quad\Longrightarrow\quad
\widehat M_n\text{ lies in the same response chamber}.
}
\]

Combine this with a finite-dimensional Hoeffding bound. This produces a **nonlinear, nonlocalised, off-model chamber theorem**, including empirical means on the boundary.

For sharper local results, use
\[
f_F(m_D+\xi)-f_F(m_D)
=\langle u_F,\xi\rangle+O(\|\xi\|^2)
\]
and Bernstein with the actual variance \(\Sigma_D(u_F,u_F)\).

**Proof size:** small–medium for the covariance optimisation; medium for the probabilistic chamber theorem.

This is the correct next step beyond calling a signal-to-noise inequality “resolution”.

---

## L5. Nested-feature refinement: an exact information ladder to the data

Suggested module: `ResponseFeatureRefinement`.

This is my strongest additional candidate beyond your list.

Let feature family \(T\) refine \(S\): every \(S\)-feature is affine in the \(T\)-features. Let
\[
R_S=R_{S,D},\qquad R_T=R_{T,D}
\]
be projections relative to the same \(\nu\).

Then, including boundary cases,
\[
\boxed{
\mathrm{KL}(D\|R_S)
=
\mathrm{KL}(D\|R_T)+\mathrm{KL}(R_T\|R_S).
}
\]
And
\[
\boxed{
\mathrm{KL}(R_T\|\nu)
=
\mathrm{KL}(R_S\|\nu)+\mathrm{KL}(R_T\|R_S).
}
\]

Thus the information newly resolved by the richer features is exactly the reduction in invisible information.

For a nested sequence ending in a saturated family,
\[
\boxed{
\mathrm{KL}(D\|\nu)
=
\sum_k\mathrm{KL}(R_{k+1}\|R_k),
}
\]
provided the initial family is featureless, so \(R_0=\nu\).

There is also the observable certificate
\[
|E_{R_T}F-E_{R_S}F|
\le
\inf_a\operatorname{osc}(F-\langle a,S\rangle)
\sqrt{\mathrm{KL}(R_T\|R_S)/2}.
\]

This addresses an important conceptual limit of the current journey:

> With fixed features, the journey reaches \(R_D\), not generally \(D\). Feature refinement supplies a mathematically controlled route the rest of the way.

**Proof size:** medium. Reuse finite entropy-projection Pythagoras, carefully tracking face supports. The boundary support issue is substantive but should be accessible from K1.

---

## L6. Facewise response calculus and surviving boundary sensitivities

Suggested module: `ResponseFaceObservableGeometry`.

Let \(Q\) be a face of the moment polytope, and
\[
X_Q=\{x:S(x)\in Q\}.
\]
For \(M\in\operatorname{relint}Q\), the response is the restricted exponential-family response on \(X_Q\), with base law \(\nu(\,\cdot\mid X_Q)\).

Prove:

1. \(R_M\) is supported exactly on \(X_Q\).
2. On \(\operatorname{relint}Q\), the response is smooth in face coordinates.
3. For \(e\in W_Q=\operatorname{dirSpan}Q\),
   \[
   \boxed{
   D_Q(E_{R_M}F)[e]=\langle u_F^Q(M),e\rangle.
   }
   \]
4. If interior means \(M_k\to M\in\operatorname{relint}Q\), then
   \[
   \boxed{
   \operatorname{proj}_{W_Q}u_F(M_k)\longrightarrow u_F^Q(M).
   }
   \]

For the last theorem, L1 gives boundedness of the full regression directions. Pass to cluster points in the covariance equations. Restricted to \(W_Q\), the limiting Fisher form is nondegenerate, so all projected cluster points coincide.

This cleanly separates:

- **tangential response directions**, which survive as ordinary face geometry;
- **normal directions**, for which the endpoint covariance no longer determines a unique full regression vector.

It is stronger and more informative than attempting to prove convergence of \(\theta_t\), which normally fails.

**Proof size:** medium–large. The main work is transporting existing finite-family machinery to a face subtype and identifying the entropy projections. It opens a genuine stratified atlas.

I would postpone the full non-saturated intrinsic Fisher-completion theorem until this face calculus exists. K6 alone does not justify that completion.

---

## L7. A testing-theoretic resolution obstruction

Suggested module: `ResponseResolutionTesting`.

For two data laws \(D_0,D_1\), any test based on \(n\) independent observations satisfies
\[
\boxed{
P_{D_0^n}(\text{choose }1)
+
P_{D_1^n}(\text{choose }0)
\ge
1-\sqrt{\frac n2\,\mathrm{KL}(D_0\|D_1)}.
}
\]

Apply this when the two laws lie in distinct response chambers. Then small \(n\,\mathrm{KL}(D_0\|D_1)\) is a genuine impossibility result for uniformly reliable chamber identification—not merely a comparison of one estimator’s signal and variance.

### Connect it to the mismatch metric

For full-support \(D\), take local alternatives
\[
D_s(dx)\propto e^{s\langle a,S(x)\rangle}D(dx).
\]
Then
\[
m_{D_s}=m_D+s\Sigma_Da+O(s^2),
\]
and
\[
\mathrm{KL}(D_s\|D)
=\frac{s^2}{2}\Sigma_D(a,a)+O(s^3).
\]

Choosing \(a=\Sigma_D^{-1}e\),
\[
\boxed{
\mathrm{KL}(D_s\|D)
=\frac{s^2}{2}\langle e,\Sigma_D^{-1}e\rangle+O(s^3).
}
\]

Now L4’s optimal signal-to-noise geometry and an all-procedures testing obstruction meet in the same quadratic form.

**Proof size:** medium if product-KL and total-variation testing lemmas are already available; otherwise medium–large. Finite spaces make a direct proof feasible.

**Essential warning:** off model, one cannot replace the KL between data laws by the KL between their response projections in an unrestricted-data testing lower bound. The raw samples can reveal information that the response forgets.

---

# 3. Ranking your candidates

| Candidate | Recommendation |
|---|---|
| Nonlinear observable sampling bias/variance | **Core L2.** Complete the observable delta method, including the residual Hessian. |
| Observable journey and variation | **Core L1/L3.** Use the correct derivative and prove boundary regularity, rather than infer it from weighted energy. |
| Boundary behaviour of regression directions | **Core L1/L6.** Uniform boundedness and face-tangential convergence are sharper targets than parameter asymptotics. |
| Reverse journey/budget | Land the reverse-KL extended-real theorem as a companion. Do not give mere path reversal a major slot. |
| Pinsker/Hellinger transfer | **Core L3**, especially after subtracting affine feature predictors. |
| Off-model chamber resolution | **Core L4/L7.** Separate achievable confidence guarantees from impossibility bounds. |
| Extrinsic Gauss | Defer. Beautiful interpretation, but little new content unless it supports a new metric-completion or rigidity theorem. |

A distinction about the “reverse journey” is important: the actual mixture
\[
(1-t)D+t\nu
\]
is generally **not** a path in the exponential response family. Its response is the reversed mean journey, but the mixture itself retains feature-invisible information. If developed, study that distinction—not merely a reparametrised version of K4.

---

# 4. Final hypothesis and vacuity checklist

Nothing displayed in K1–K6 is visibly a known-false theorem under the intended hypotheses. But I would explicitly audit the following.

### 1. The base law is a probability law

Full support is not a substitute for `[IsProbabilityMeasure ν]`. The claimed featureless starting law is \(\nu\) only with the intended normalisation.

Also, unless \(\nu\) is uniform, “maximum entropy” means **maximum relative entropy/minimum KL to \(\nu\)**, not maximum Shannon entropy.

### 2. Boundary KL identities are genuinely finite where `toReal` is used

For K1/K4, full-support finite \(\nu\) makes \(\mathrm{KL}(D\|\nu)\) finite. One also needs—and mathematically has—
\[
\operatorname{supp}D\subseteq\operatorname{supp}R_D,
\]
which ensures \(\mathrm{KL}(D\|R_D)<\infty\).

For the reverse KL, finiteness fails on proper faces. Do not copy the `toReal` pattern there.

### 3. Saturation really reaches every intrinsic-isometry assertion

This is the main K6 audit item. A spherical embedding is always available; an intrinsic isometry is not.

### 4. Degenerate cases are harmless but should remain visible

- \(W=0\): all response observables are constant; the positive-variance resolution theorem is inapplicable.
- One atom: completion is a point, not a space of diameter \(\pi\).
- Interior mean does not imply nondegenerate data covariance.
- On non-finite spaces, boundedness/integrability of \(F\) is needed before interpreting a formal covariance functional as an actual observable derivative.

### 5. The value of the chart expression at \(t=1\) is immaterial to the integral

The endpoint parameter may not exist geometrically. A total Lean definition can assign some value there; its value on that Lebesgue-null singleton does not affect K4. Documentation should preserve this distinction.

---

## Recommended implementation order

Start with **L2 and L3** for relatively direct, high-value extensions of K. In parallel, develop the finite linear algebra for **L1**. Then use L1 to power **L4 and L6**. Add **L5** as the route from a fixed response to progressively richer responses, and **L7** to make “unresolvable” a theorem about statistical decisions.

The resulting programme would say:

> Every posterior observable has a globally controlled response across the closed data-mean polytope; its finite-sample bias and covariance are computable; its remaining error separates into unfinished journey and feature blindness; and the chambers it distinguishes have both achievable confidence bounds and information-theoretic resolution limits.