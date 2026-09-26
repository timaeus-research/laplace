## Executive verdict

The atlas is now **mathematically complete at second order, including finite-rate radial boundary completion**. What remains is not another missing Taylor estimate. It is chiefly:

1. making explicit what reconstruction does—and what information it necessarily leaves unresolved;
2. extending regularity to all orders;
3. identifying the correct topology for non-radial boundary stability;
4. turning the atlas into a statistical response theorem.

My strongest correction to the proposed next steps is:

> **Arbitrary interior approaches to a finite-rate boundary response need not give TV convergence.**  
> Entropy-continuous approaches do. This gives a clean, substantial replacement theorem.

And my strongest implementation recommendation is:

> Land **all higher responses are moment-normal** before spending heavily on Banach-valued analyticity.

---

# 1. Is this the right “one theorem”?

**Yes, based on the reported statements.** `response_atlas_reconstruction` has the right four layers:

- existence and identification of the reconstructed distribution;
- the response differential and normal second-order response;
- compact-uniform control and stability;
- radial transport from the reference distribution, including finite-rate boundary completion.

The information-budget identity is the correct capstone:
\[
\operatorname{KL}(D\|\nu)
=
\operatorname{KL}(D\|\Pi(M))
+
\int_0^1(1-s)\kappa_s\,ds.
\]

It says exactly how much information the chosen features reveal.

### One interpretive point is essential

The map is
\[
\nu\longrightarrow \Pi(M),
\]
not generally \(\nu\longrightarrow D\). The difference is not a technical defect:
\[
\operatorname{KL}(D\|\Pi(M))
\]
is the information invisible to the reconstruction constraints.

Also, “maximal entropy” here should mean **relative to the reference \(\nu\)**: \(\Pi(M)\) minimizes relative entropy to \(\nu\) at fixed response. It is not an absolute Shannon-entropy assertion unless the reference makes that interpretation appropriate.

I would put those two sentences directly beside the flagship theorem.

## Corollaries worth stating, but not adding to the conjunction

### Observable compact-uniform Taylor

For bounded \(F\), define
\[
a_F(M)[u]=E_{Q_M}[F\ell_{M,u}],
\]
\[
b_F(M)[u,v]
=
E_{Q_M}\!\left[F\,N_M(\ell_{M,u}\ell_{M,v})\right].
\]
Then your relative-uniform theorem immediately gives, uniformly on compact convex interior response sets,
\[
E_{Q_{M+z}}F
=
E_{Q_M}F+a_F(M)[z]+\frac12b_F(M)[z,z]
+o(\|z\|^2)\,\|F\|_\infty.
\]

This deserves a named theorem. It is the form most users of the atlas will actually apply.

### Interior second-order atlas-curve expansion

At \(s<1\), for admissible small \(h\),
\[
q_{s+h}
=
q_s\left[
1+h\ell_{M_s,\Delta}
+\frac{h^2}{2}N_{M_s}(\ell_{M_s,\Delta}^2)
\right]
+o_{L^1}(h^2).
\]

The expansion is uniform on compact subintervals of \([0,1)\). Do **not** imply uniformity up to the boundary without additional conditioning assumptions.

These are short extraction lemmas, not new foundational layers.

### Legendre geometry and the fibre split

The Legendre layer is the most valuable conceptual companion theorem:
\[
\nabla\mathcal I(M)=-\theta(M),\qquad
D^2\mathcal I(M)=\Sigma_M^{-1}=-R_M.
\]
It identifies the metric already governing your response bounds.

The fibre split is illuminating but belongs in a separate theorem. Under appropriate disintegration hypotheses, with \(Y=S(X)\),
\[
\operatorname{KL}(D\|\Pi(M))
=
\operatorname{KL}(D_Y\|(\Pi(M))_Y)
+
\int \operatorname{KL}(D(\cdot\mid y)\|\nu(\cdot\mid y))\,D_Y(dy).
\]
The reason is that exponential tilting by \(S\) preserves the conditional law given \(S\).

This separates the unresolved information into:

- information in the **feature distribution beyond its mean**;
- information **inside feature fibres**.

Beautiful, but potentially expensive measure-theoretically. It should not block the core atlas.

---

# 2. All orders: statement, coefficients, and Lean route

## The statement I would target

Work in coordinates on the affine response space \(m_0+\mathbb V\). Fix \(M_0\in\operatorname{ri}K\), and define
\[
\mathcal F_{M_0}(M)
=
\left[\frac{q_M}{q_{M_0}}\right]\in L^\infty(\nu).
\]

Prove:

> **Relative analytic reconstruction.**  
> \(\mathcal F_{M_0}\) is real-analytic at every \(M\in\operatorname{ri}K\), in response coordinates.

Equivalently, for each interior \(M\), there is a positive radius on which
\[
\frac{q_{M+z}}{q_M}
=
\sum_{n=0}^\infty\frac1{n!}A_n(M)[z,\ldots,z]
\]
converges in \(L^\infty(\nu)\).

Here
\[
A_n(M)
=
D_z^n\left.\left(\frac{q_{M+z}}{q_M}\right)\right|_{z=0}.
\]

Two important qualifications:

- The series coefficients are **local-base coefficients**. For the fixed-base map,
  \[
  D^n\mathcal F_{M_0}(M)
  =
  \frac{q_M}{q_{M_0}}\,A_n(M).
  \]
- This is an \(L^\infty\) statement, hence an almost-everywhere statement. A theorem for every \(x\) needs chosen representatives and pointwise bounded-feature hypotheses.

## The first coefficients

With the derivative convention above,
\[
A_0=1,\qquad A_1[u]=\ell_{M,u},
\]
and
\[
A_2[u,v]=N_M(\ell_{M,u}\ell_{M,v}).
\]

The factorial belongs in the Taylor series, not in \(A_n\).

## General coefficient identities

Write
\[
\psi(\theta)=\log Z(\theta),\qquad
\Theta_n=D^n\theta(M),
\]
and let \(G_n\) be the \(n\)-th response derivative of \(\log q_M\).

For a partition \(\pi\) of \(\{1,\dots,n\}\), write
\[
\Theta_B=\Theta_{|B|}[u_i:i\in B].
\]
Then
\[
G_n[u_1,\ldots,u_n]
=
\langle\Theta_n[u_1,\ldots,u_n],M-S\rangle
-
\sum_{\substack{\pi\\|\pi|\ge2}}
D^{|\pi|}\psi(\theta)
[\Theta_B:B\in\pi].
\]
Since
\[
D^k\psi(\theta)[v_1,\ldots,v_k]
=
(-1)^k\operatorname{Cum}_{Q_M}
(\langle v_1,S\rangle,\ldots,\langle v_k,S\rangle),
\]
this is the desired cumulant description.

The density coefficients are the Bell-partition polynomials:
\[
A_n[u_1,\ldots,u_n]
=
\sum_{\pi}
\prod_{B\in\pi}G_{|B|}[u_i:i\in B].
\]

A particularly useful recursion is
\[
A_{n+1}(M)[u_1,\ldots,u_n,v]
=
D_M\big(A_n(M)[u_1,\ldots,u_n]\big)[v]
+
\ell_{M,v}A_n(M)[u_1,\ldots,u_n].
\]

For repeated directions, setting \(a_n=A_n[u^n]\) and \(g_n=G_n[u^n]\),
\[
a_{n+1}
=
\sum_{k=0}^{n}\binom nk\,g_{k+1}a_{n-k}.
\]

If you also want a recursion for the inverse-map derivatives, differentiate
\[
m(\theta(M))=M.
\]
For \(n\ge2\),
\[
\Sigma_M\Theta_n
=
\sum_{\substack{\pi\\|\pi|\ge2}}
D^{|\pi|}m(\theta)[\Theta_B:B\in\pi],
\]
where \(D^km\) is the vector-valued \((k+1)\)-st cumulant with sign \((-1)^k\). All operators are understood on the identifiable direction space.

I would **not** formalize all of this combinatorics before the analytic theorem. The recursion is a cheaper first API than a full partition formula.

## Cheapest Lean route

I cannot verify exact Mathlib identifiers from the description, so I would not budget against any of the proposed names without inspecting the checked-out version. In particular, audit the **analytic inverse theorem first**.

| Route | Assessment | Rough additional proof lines |
|---|---|---:|
| **(a) Analytic calculus + analytic inverse** | Clearly best if the inverse theorem and Banach-algebra exponential API are available in usable form | 250–650 |
| **(b) Explicit norm-majorized series** | Good fallback for natural coordinates; does not itself solve analyticity of the inverse response map | 400–900 for natural coordinates; substantially more for the inverse |
| **(c) Higher-order explicit ratio estimates** | Good for any fixed finite order; poor route to all-orders analyticity unless factorial growth is controlled uniformly | 250–600 for a finite-order framework; 800+ for an actual analytic majorant |

These are engineering estimates, not verified counts; missing inverse-function infrastructure can dominate them.

### Route (a), specifically

At a fixed natural base \(\theta_0\), use
\[
\eta\mapsto
\frac{\exp(-\langle\eta,S\rangle)}
{E_{\theta_0}\exp(-\langle\eta,S\rangle)}.
\]

The clean composition is:

1. a bounded linear map \(\eta\mapsto-\langle\eta,S\rangle\) into \(L^\infty\);
2. Banach-algebra exponential;
3. the bounded linear expectation functional;
4. scalar reciprocal near the positive denominator;
5. scalar multiplication;
6. composition with analytic \(\theta(M)-\theta_0\).

You do **not** need inversion of an arbitrary \(L^\infty\) element. Only scalar inversion of the normalizer is needed.

Also, the numerator is entire; the normalized complexified ratio need not be entire because the complexified normalizer can have zeros. The real normalized map is analytic everywhere in natural coordinates because the real normalizer is positive.

### Route (b)

The bound
\[
\left\|\frac{(-\langle\eta,S\rangle)^n}{n!}\right\|_\infty
\le\frac{(K\|\eta\|)^n}{n!}
\]
makes the exponential series easy mathematically.

The real cost is assembling the multilinear power series, scalar reciprocal, and then the analytic inverse. If the analytic inverse theorem is absent, this route does not magically avoid that obstruction.

### Route (c)

A theorem giving derivatives of every finite order is not yet analyticity. You need a common radius and bounds of the form
\[
\|A_n(M)\|\le C\,n!\,r^{-n}.
\]
Without that, higher-order ratio lemmas buy smoothness, not convergence of the Taylor series.

## Higher moment-normality: yes, land it first

This does **not** need analyticity.

Suppose reconstruction is \(C^n\) into \(L^\infty\), or into \(L^1\) with the required weighted moment maps continuous. Then
\[
E_{Q_M}A_1[u]=0,\qquad
E_{Q_M}[S A_1[u]]=u,
\]
and for \(n\ge2\),
\[
E_{Q_M}A_n[u_1,\ldots,u_n]=0,
\]
\[
E_{Q_M}[S A_n[u_1,\ldots,u_n]]=0.
\]

Proof: apply the continuous linear functionals
\[
f\mapsto E_{Q_M}f,\qquad
f\mapsto E_{Q_M}[Sf]
\]
to
\[
E_{Q_M}\frac{q_{M+z}}{q_M}=1,\qquad
E_{Q_M}\left[S\frac{q_{M+z}}{q_M}\right]=M+z,
\]
and differentiate.

Thus, for \(n\ge2\),
\[
N_M A_n=A_n.
\]

This is a genuinely structural theorem:

> The first response moves the prescribed moments. Every higher response changes only the distributional shape normal to those constraints.

A generic “derivatives of affine conserved quantities vanish” lemma could make the final specialization very short. Prove it under \(C^n\) assumptions first; then discharge those assumptions using smooth inverse-function machinery, without waiting for analyticity.

---

# 3. What is deepest and reachable next?

My ranking beyond the analytic project is:

1. **Legendre closure plus entropy-controlled non-radial boundary stability.**
2. **Statistical response: empirical consistency, delta method, and second-order observable bias.**
3. **Dual-flat geometry and matched-velocity comparison of exponential and response-affine curves.**
4. **Feature-fibre information decomposition.**
5. **Transport**, unless the seabed already contains useful metric and transport-inequality assumptions.

The inexpensive observable and curve corollaries should be landed before any of these larger projects.

## Why unrestricted non-radial TV continuity is false

Take a countable sample space with atoms \(0,1,2,\ldots\), all of positive \(\nu\)-mass. Let the feature vectors lie on the unit circle, with
\[
S(n)\longrightarrow S(0),
\]
all distinct, and with full two-dimensional affine span.

Each \(S(n)\) is uniquely exposed by the linear functional \(x\mapsto\langle S(n),x\rangle\). Consequently, by taking
\[
\theta_n=-t_nS(n),\qquad t_n\to\infty
\]
sufficiently rapidly, one can arrange
\[
P_{\theta_n}(\{n\})\ge1-\frac1n.
\]

Then
\[
M_n=E_{P_{\theta_n}}S\longrightarrow S(0),
\]
and every \(M_n\) is an interior response. But the unique distribution with mean \(S(0)\) is \(\delta_0\), and
\[
\mathcal I(S(0))=\log\frac1{\nu(\{0\})}<\infty.
\]
Nevertheless,
\[
\|P_{\theta_n}-\delta_0\|_{\mathrm{TV}}\longrightarrow1.
\]

So finite rate **at the limit point** is not enough.

There is also a sign correction to the proposed reverse-KL formula. With your convention \(p_\theta=e^{-\langle\theta,S\rangle}/Z\),
\[
\boxed{
\operatorname{KL}(Q_*\|Q_M)
=
\mathcal I(M_*)-\mathcal I(M)
+\langle\theta(M),M_*-M\rangle.
}
\]
The last sign is **plus**.

Convexity alone does not force this expression to vanish along arbitrary approaches.

## Dual atlas: what skewness actually controls

The endpoint-matched curves
\[
\theta_s=s\theta(M),\qquad M_s=m_0+s(M-m_0)
\]
generally have **different first velocities**. Their difference is therefore not generally a second-order skewness effect.

The clean comparison is local and matched-velocity. At \(M\), compare
\[
Q^{m}_t=Q_{M+tu},
\qquad
Q^{e}_t=P_{\theta(M)+tR_Mu}.
\]
Both have first density derivative \(q_M\ell_{M,u}\). Their second derivatives are
\[
(q^{m})''_0=q_MN_M(\ell_{M,u}^2),
\]
\[
(q^{e})''_0=q_M\big(\ell_{M,u}^2-E_{Q_M}\ell_{M,u}^2\big).
\]

Thus
\[
(q^{m})''_0-(q^{e})''_0
=
-q_M\,\operatorname{Proj}_{\mathrm{feature\ tangent}}
(\ell_{M,u}^2).
\]

The full discrepancy is a **third-cumulant vector**, not one scalar skewness. Its pairing with the velocity score is
\[
E_{Q_M}\left[
\ell_{M,u}\frac{(q^{m})''_0-(q^{e})''_0}{q_M}
\right]
=
-E_{Q_M}\ell_{M,u}^3.
\]

That is the precise, clean skewness statement.

## Transport

Bounded features alone impose no useful transport geometry on the underlying sample space. If that space has bounded diameter, TV immediately controls Wasserstein distance. More substantial results require additional assumptions such as a transport inequality, coercivity, or Lipschitz structure.

I would not introduce those just to obtain another metric version of an already strong theorem.

---

# 4. Top item: Legendre closure and entropy-continuous boundary stability

This has an unusually cheap route because your radial reverse-KL tail is already available.

## 4.1 Boundary dual representation

Define
\[
\mathcal J(M)
=
\sup_\theta\{-\langle\theta,M\rangle-\log Z(\theta)\}.
\]

Prove, at every finite-rate response,
\[
\boxed{\mathcal I(M)=\mathcal J(M).}
\]

### Lemma-level route

1. **Dual lower bound.** For any feasible \(D\),
   \[
   -\langle\theta,M\rangle-\log Z(\theta)
   \le \operatorname{KL}(D\|\nu).
   \]
   Apply this to the boundary projection to get \(\mathcal J(M)\le\mathcal I(M)\).

2. **Radial dual approximation.** For the radial interior points \(M_s\),
   \[
   -\langle\theta_s,M\rangle-\log Z(\theta_s)
   =
   \mathcal I(M)-\operatorname{KL}(Q_M\|Q_s).
   \]

3. **Use the landed tail limit.**
   The right side tends to \(\mathcal I(M)\).

4. **Conclude equality.**

This avoids developing weak compactness of entropy sublevels merely to obtain this representation.

Since \(\mathcal J\) is a supremum of continuous affine functions, it is convex and lower semicontinuous. Consequently \(\mathcal I\) has those properties on its identified finite-rate domain. A statement covering every infinite-rate point as well needs the corresponding extended-value identification; do not silently obtain that from the finite-rate theorem.

## 4.2 Segment continuity

For finite-rate \(A,B\), convexity and lower semicontinuity give
\[
\mathcal I((1-t)A+tB)\longrightarrow\mathcal I(B)
\qquad(t\uparrow1).
\]

This is stronger than the special reference-to-boundary segment statement, while still being cheap.

## 4.3 Quantitative entropy-gap control of TV

Write \(Q_A=\Pi(A)\), and use the \(L^1\) convention for density distance. Prove
\[
\boxed{
\|q_A-q_B\|_1^2
\le
4\left[
\mathcal I(A)+\mathcal I(B)
-2\mathcal I\!\left(\frac{A+B}{2}\right)
\right].
}
\]

### Proof skeleton

Let \(H=(Q_A+Q_B)/2\). Its response is \((A+B)/2\), so
\[
\mathcal I\!\left(\frac{A+B}{2}\right)
\le \operatorname{KL}(H\|\nu).
\]

The entropy gap decomposes as
\[
\frac{\mathcal I(A)+\mathcal I(B)}2-\operatorname{KL}(H\|\nu)
=
\frac12\operatorname{KL}(Q_A\|H)
+\frac12\operatorname{KL}(Q_B\|H).
\]
Pinsker bounds the right side below by
\[
\frac18\|q_A-q_B\|_1^2.
\]

No boundary natural parameter is needed.

## 4.4 Non-radial stability theorem

If finite-rate responses satisfy
\[
M_n\to M_*,
\qquad
\mathcal I(M_n)\to\mathcal I(M_*),
\]
then
\[
\boxed{\|q_{M_n}-q_{M_*}\|_1\to0.}
\]

Apply the entropy-gap inequality and lower semicontinuity at
\[
\frac{M_n+M_*}{2}\longrightarrow M_*.
\]

This identifies a natural boundary completion topology:
\[
M\mapsto (M,\mathcal I(M)).
\]

**Interpretation:** response convergence together with visible-information convergence controls the entire reconstructed distribution.

### Estimate and pitfalls

Roughly:

- dual representation and l.s.c.: **120–300 lines**;
- Jensen–Shannon entropy identity and gap inequality: **150–350 lines**;
- sequential stability and segment corollaries: **60–150 lines**.

Main pitfalls:

- KL orientation and the sign of \(\theta\);
- midpoint admissibility and finite rate;
- handling entropy identities without informal subtraction of infinities;
- distinguishing \(L^1\) distance from TV distance;
- not claiming unrestricted boundary continuity.

---

# 5. Second item: the statistical response theorem

This gives the atlas an operational meaning: how reconstructed distributions respond to actual sampled data.

Let \(X_i\) be i.i.d. with law \(D\), and assume
\[
M=E_D S\in\operatorname{ri}K,
\qquad
\widehat M_n=\frac1n\sum_{i=1}^nS(X_i).
\]
Set
\[
\Gamma=\operatorname{Cov}_D(S).
\]

Crucially, \(\Gamma\) is the **data covariance**, not necessarily \(\Sigma_M\).

## 5.1 Almost-sure TV consistency

Boundedness of \(S\) gives
\[
\widehat M_n\to M\quad\text{a.s.}
\]
Choose a compact convex neighbourhood \(C\) of \(M\) inside the relative interior. Eventually \(\widehat M_n\in C\), so
\[
\|q_{\widehat M_n}-q_M\|_1
\le L_C\|\widehat M_n-M\|\to0
\quad\text{a.s.}
\]

This is indeed now almost immediate.

The theorem estimates \(\Pi(M)\), not \(D\), unless \(D\) belongs to the reconstructed family.

## 5.2 Second-order stochastic response

Put \(h_n=\widehat M_n-M\). Your existing relative-uniform theorem gives
\[
\frac{q_{\widehat M_n}}{q_M}
=
1+\ell_{M,h_n}
+\frac12N_M(\ell_{M,h_n}^2)
+o_p(n^{-1})
\]
in \(L^\infty(\nu)\), once
\[
h_n=O_p(n^{-1/2})
\]
is supplied.

That is an exceptionally direct reuse of the landed theorem.

With a finite-dimensional CLT,
\[
\sqrt n\,h_n\Rightarrow G,\qquad G\sim N(0,\Gamma),
\]
one obtains
\[
\sqrt n\left(\frac{q_{\widehat M_n}}{q_M}-1\right)
\Rightarrow \ell_{M,G}.
\]

For formalization, I would land the **observable version first**, avoiding unnecessary Banach-valued probability infrastructure.

## 5.3 Observable delta method

For bounded \(F\),
\[
\sqrt n\left(E_{\Pi(\widehat M_n)}F-E_{\Pi(M)}F\right)
\Rightarrow
N\!\left(0,\;a_F(M)\Gamma a_F(M)^\top\right).
\]

The second-order correction is
\[
\frac12 b_F(M)[h_n,h_n].
\]

With suitable control of exceptional empirical responses,
\[
n\left(
E\!\left[E_{\Pi(\widehat M_n)}F\right]
-
E_{\Pi(M)}F
\right)
\longrightarrow
\frac12\sum_{i,j}\Gamma_{ij}\,
b_F(M)[e_i,e_j].
\]

This is a particularly beautiful result:

> The sampling covariance contracts with the atlas’s normal second response to produce reconstruction bias.

### Lemma-level route

1. Coordinatewise SLLN for bounded features.
2. Eventual membership in a compact interior neighbourhood.
3. Apply reconstruction Lipschitzness.
4. State a deterministic observable Taylor lemma.
5. Combine its remainder with root-\(n\) control.
6. Apply a finite-dimensional CLT and the scalar delta method.
7. For expectation-level bias, add tail and uniform-integrability estimates.

### Estimate and pitfalls

Assuming the relevant probability APIs are already usable:

- SLLN + TV consistency: **80–200 lines**;
- deterministic-to-stochastic second-order transfer: **120–300 lines**;
- observable CLT: **200–600 lines**;
- expectation-level second-order bias: **250–600 additional lines**.

The last two are highly library-dependent.

Main pitfalls:

- \(\widehat M_n\) can lie on the boundary for small \(n\). Use eventual statements or define a bounded extension outside the chosen neighbourhood.
- Almost-sure consistency alone does not justify expectation-level bias.
- Bounded features supply strong tail control, but it must actually be invoked.
- For the bias theorem, keep the observable estimator bounded on exceptional events.
- Do not substitute model covariance \(\Sigma_M\) for data covariance \(\Gamma\).

---

## Recommended landing order

1. **Named observable Taylor and atlas-curve corollaries.**
2. **Generic higher-derivative conservation ⇒ moment-normality.**
3. **Audit analytic inverse machinery; pursue route (a) if available.**
4. **Boundary dual representation + entropy-gap TV stability.**
5. **Empirical TV consistency, then observable stochastic response.**
6. **Matched-velocity dual-curve comparison.**

The next unifying sentence is no longer merely “we can reconstruct and differentiate.”

It is:

> **The features determine the tangent response; all nonlinear corrections are moment-normal; visible-information continuity controls boundary stability; and sampling fluctuations propagate through exactly this same response geometry.**