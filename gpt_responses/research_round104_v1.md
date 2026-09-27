## Executive verdict

The programme has reached a genuine milestone: **the response is now a globally stable map on a finite moment polytope, its differential integrates to the full change in expectation, and sampling imposes both upper and lower resolution bounds.**

The next step should not be another collection of first-order consequences. It should be:

> **Stratified transport, second-order response geometry, and the statistical cost of refinement.**

There are three important audit qualifications:

1. The displayed norm on `J → ℝ` is ordinarily the **sup norm**, not the Euclidean norm.
2. A face-tangential response field does **not** describe an inward derivative from that face.
3. An ambient displacement `e : J → ℝ` annihilating `dataKer ⊆ W` need not belong to `W`. The attainable-displacement interpretation needs that additional condition.

None of these appears to invalidate the displayed analytic conclusions, but they matter substantially for the note.

---

# 1. Audit

I can audit the mathematical shapes shown here; omitted section hypotheses and auxiliary definitions still need checking against the files.

## 1.1 M3 and M3b: correct, but distinguish three constants

Write, using Euclidean coordinates on \(W\),
\[
L_2(F)=\sup_\theta\|u_F(\theta)\|_2,\qquad
L_1(F)=\sup_\theta\|u_F(\theta)\|_1.
\]
Then
\[
|f_F(N)-f_F(M)|
\le L_2(F)\|N-M\|_2
\le L_1(F)\|N-M\|_\infty,
\]
where \(f_F(M)=E_{R_M}F\).

Your displayed M3b theorem is exactly the second type of bound. It is mathematically natural and entirely adequate.

**Lean audit point:** unless you have explicitly transported another norm, `‖M - N‖` for `M N : J → ℝ` is the Pi sup norm. Thus:

- “Euclidean Lipschitz” is not literally the displayed statement;
- the displayed chamber ball is a sup-norm ball;
- `traceCov/n` remains a valid upper bound for the squared sup-norm sampling error, but is not generally its exact expectation.

The Euclidean theorem is obtainable separately, with the appropriate norm conversion.

### Should the note have an explicit constant?

**Yes, as a second theorem, not as a replacement for the sign-cell proof.**

The sign-cell argument establishes the surprising phenomenon economically. Cauchy–Binet explains its geometry and gives a computable certificate.

Choose affine coordinates \(z_x\in\mathbb R^d\) for the configuration and rows
\[
a_x=(1,z_x).
\]
For each affine basis \(I\) of \(d+1\) configuration points, let
\[
(\alpha_I,b_I)=A_I^{-1}F_I
\]
be the affine interpolant of \(F\) on \(I\). Weighted least squares satisfies
\[
(\alpha_p,b_p)=\sum_I\omega_I(p)(\alpha_I,b_I),
\]
where
\[
\omega_I(p)=
\frac{\det(A_I)^2\prod_{x\in I}p_x}
{\sum_K\det(A_K)^2\prod_{x\in K}p_x}.
\]
Consequently,
\[
\|u_F(\theta)\|_2\le \max_I\|b_I\|_2.
\]

This constant is optimal **over all strictly positive weighting schemes**: concentrate the weights on a maximizing basis. It need not be optimal over the smaller set of weights realized by your exponential family.

That distinction makes a good note-level statement: an explicit, configuration-only stability constant, not a claim of optimality for the model.

---

## 1.2 M4: the Riesz projection is acceptable, and identification is cheap

Let \(V=W_A\), where \(A=\operatorname{supp}R_M\). For the Euclidean orthogonal projection \(P_V\),
\[
u-P_Vu\perp W_A.
\]
Therefore
\[
x\longmapsto \langle u-P_Vu,S(x)\rangle
\]
is constant on \(A\). Hence, for every \(w\in V\),
\[
\Sigma_{R_M}(u-P_Vu,w)=0.
\]
Thus \(P_Vu\) satisfies precisely the defining equations of `faceProj`; positive definiteness on \(V\) gives uniqueness.

So:
\[
\boxed{\operatorname{faceProj}u=P_{W_A}u.}
\]

Two qualifications:

- This identification is special to the covariance support geometry. It is **not true for an arbitrary** positive-definite restriction of a bilinear form to an arbitrary subspace.
- Because the ambient Lean space uses the sup norm, “Euclidean orthogonal projection” should be defined through `dotJ` or an explicit Euclidean-space transport, not inferred from the existing norm.

Keep the general Riesz-projection stability estimate as it is. Add the support-span identification as a short geometric corollary. The note should state the convergence with \(P_{W_A}\).

---

## 1.3 M7a: base change is valid at finite-rate boundary means

The identity behind it is
\[
\log\frac{dP_{\theta_0}}{d\nu}
=-\langle\theta_0,S\rangle-\log Z(\theta_0).
\]
For every feasible \(Q\) with mean \(M\),
\[
\mathrm{KL}(Q\|P_{\theta_0})
=
\mathrm{KL}(Q\|\nu)
+\langle\theta_0,M\rangle+\log Z(\theta_0).
\]
The added term is constant over the constraint set. Bounded features make the density ratio bounded above and away from zero, so finiteness is preserved.

This argument does not require \(M\) to be interior. The finite-rate hypothesis is an appropriate way to exclude infeasible/default-valued projection behavior.

**One audit check worth making:** for the defect and ladder limits, record that the KL quantities are finite near zero. An `ENNReal.toReal` limit alone can conceal infinities. Here bounded tilts and feasibility should supply finiteness, so this is a supporting lemma/check rather than an expected obstruction.

---

## 1.4 Journey endpoint: harmless junk, but do not replace inward derivatives by tangential ones

The value at \(t=1\) is irrelevant to the Lebesgue integral. There is no mathematical defect.

However, the proposed interpretation needs correction:

> M4 supplies the limiting **tangential component**, not a canonical full limiting response gradient.

At a vertex \(W_A=\{0\}\), the tangential response gradient is zero. Nevertheless, moving inward from that vertex can change a posterior expectation to first order.

For example, for the Bernoulli feature and observable \(F=S\),
\[
f_F(M)=M.
\]
At \(M=0\), the face-tangential field is zero, while the inward derivative is \(1\).

Therefore:

- assigning the tangential field at the journey endpoint is legitimate because it changes a null set;
- it is not legitimate to say it represents the derivative in every feasible direction there;
- there is generally no single continuous ambient gradient field on the closed polytope.

The beautiful replacement is a **stratified differential**: each face carries its own smooth response field, and it integrates along absolutely continuous paths. More below.

---

## 1.5 The resolution floor: tests are the right primitive, but chamber separation is missing

The randomized-test formulation is stronger and cleaner than a Boolean-only formulation. Keep it.

But the theorem currently says:

> these two sampling laws cannot be reliably distinguished.

To conclude:

> their chambers cannot be reliably classified,

you must additionally prove that the two population means receive **different chamber labels**.

If both means lie in the same chamber, classification can be perfect while testing remains difficult. In particular, a fixed population mean with positive chamber margin will generally remain in its chamber under sufficiently small \(n^{-1/2}\)-alternatives.

Add a classifier corollary with the explicit hypothesis
\[
C(m_D)\ne C(m_{D_{a/\sqrt n}}).
\]
For a two-label classifier, the sum of its two error probabilities is bounded below by \(2L_n\), with the orientation of the test chosen consistently. Multiclass classifiers reduce to a binary test and give the same kind of conclusion.

### Important ambient-displacement issue

In the displayed statement,
```lean
{e : J → ℝ}
(he : ∀ u ∈ dataKer ..., dotJ (u : J → ℝ) e = 0)
```
annihilation alone does not imply \(e\in W\).

For example, a nonzero \(e\in W^\perp\) annihilates all of `dataKer`, yet cannot be a mean displacement. The covariance dual then represents the \(W\)-component of \(e\), not necessarily \(e\) itself.

Thus the advertised “mean speed \(e\)” needs either:

- `e : W`, or
- an additional hypothesis `e ∈ W`.

The displayed testing theorem can remain true without it; its geometric interpretation cannot.

Finally, the lower bound is informative only when its limiting constant is positive. State the smallness condition on \(a\) in the headline corollary. Likewise for `minimax_two_point_contrast`. Your Pinsker constants appear conservative rather than false.

---

## 1.6 Two smaller interpretation checks

### Refinement budget

The stopping criterion is sound. It is informative only when the total budget is finite, and gives
\[
\text{observable error}^2
\le 2L^2\left[\mathrm{KL}(D\|R_0)-\text{resolved budget}\right]
\]
when real-valued subtraction is justified. An infinite total budget gives no stopping certificate.

### “Featureless distribution of maximal entropy”

For arbitrary \(\nu\), the correct phrase is:

> the featureless reference law, maximizing entropy relative to \(\nu\).

It maximizes ordinary Shannon entropy only when the reference is uniform on the finite configuration. The constant-feature lemma is worth adding, but it is not a new research programme.

---

# 2. Next programme: six ranked targets

## Programme N: stratified response transport and second-order resolution

The central organizing fact should be:

> Every finite-data law lives statistically inside its minimal moment face, even when that face lies on the boundary of the global polytope.

This resolves the boundary-bias question much more cleanly than trying to extend ambient Hessians continuously.

---

## N1. Exact face restriction and stratified transport

**Rank 1. High value; medium proof investment.**

For a face \(A\) of the moment polytope, let
\[
X_A=\{x:S(x)\in A\},\qquad
\nu_A=\nu(\,\cdot\,\mid X_A).
\]
Prove, for \(M\in A\),
\[
\boxed{R_M^\nu=R_M^{\nu_A}}
\]
after embedding the restricted configuration into \(X\).

The proof is elementary geometry plus entropy minimization:

1. Every law with mean in \(A\) is supported on \(X_A\).
2. On laws supported there,
   \[
   \mathrm{KL}(Q\|\nu)
   =\mathrm{KL}(Q\|\nu_A)-\log\nu(X_A).
   \]
3. The minimizers coincide.

Then interior response calculus applies on \(\operatorname{relint}A\).

### Capstone statement

Let \(M:[0,1]\to\mathrm{hull}\) be absolutely continuous. Let \(A_t\) be the minimal face containing \(M(t)\), and let \(u_F^{A_t}\) be its face regression direction. Then
\[
\boxed{
f_F(M(1))-f_F(M(0))
=
\int_0^1
\langle u_F^{A_t}(M(t)),\dot M(t)\rangle\,dt.
}
\]

For almost every \(t\),
\[
\dot M(t)\in W_{A_t}.
\]

This is the correct meaning of a response field on the closed polytope.

**Proof route:** finitely many face strata, facewise smoothness, global Lipschitz continuity, and the fact that an absolutely continuous nonnegative constraint has derivative zero almost everywhere on its zero set.

A law-valued version is especially attractive:
\[
\frac{d}{dt}R_{M(t)}\{x\}
=
R_{M(t)}\{x\}\,
\ell_{\dot M(t)}^{A_t}(x)
\quad\text{a.e.}
\]
Here \(\ell_e^A\) is the centered face feature score solving the covariance equation for displacement \(e\).

This goes substantially beyond a facewise line integral: it gives transport along arbitrary data journeys.

---

## N2. The response Hessian is a residual third moment

**Rank 2. High value; medium investment, reusing covariance differentiation.**

Fix \(M\in\operatorname{relint}A\), set \(Q=R_M\), and define
\[
r_F^A
=
F-E_QF-\langle u_F^A,S-M\rangle.
\]
For \(e\in W_A\), let \(v_e\in W_A\) solve
\[
\Sigma_Q(v_e,w)=\langle e,w\rangle
\quad(w\in W_A),
\]
and write
\[
\ell_e(x)=\langle v_e,S(x)-M\rangle.
\]

Then:
\[
\boxed{
D_A^2f_F(M)[e,d]
=
E_Q[r_F^A\,\ell_e\ell_d].
}
\]

This is a particularly good “beauty and depth” theorem:

- the first derivative is regression;
- the second derivative is the interaction of two feature scores with the unexplained observable;
- affine feature observables have zero response curvature.

**Proof route:** differentiate the normal equations. The derivative of \(u_F\) is determined by the third centered moment of the regression residual.

Prove this on a model first, then transfer it to each face using N1.

### Do not target an ambient boundary Hessian

It need not exist. Take a three-point configuration
\[
S\in\{0,1,3/2\},
\]
positive reference weights, and \(F=\mathbf1_{\{S=3/2\}}\). Near mean \(m=0\),
\[
f_F(m)\sim C m^{3/2}.
\]
The response is globally Lipschitz, but has no finite inward second derivative at zero.

Thus M4 cannot supply the proposed ambient closed-polytope \(C^2\) extension.

---

## N3. Face-adaptive asymptotic linearity, bias, and sharp risk

**Rank 3. Very high statistical value; medium investment after N1–N2.**

Let \(D\) be any law on the finite configuration, \(M=m_D\), and \(A\) its minimal moment face.

First prove:
\[
D(X_A)=1.
\]
Hence every empirical mean lies in \(A\), almost surely. The estimator only explores the face where \(M\) is relatively interior.

Define the face influence
\[
\psi_F(x)=\langle u_F^A(M),S(x)-M\rangle.
\]
Then obtain
\[
\boxed{
\widehat\Psi_F-\Psi_F
=
\frac1n\sum_{i=1}^n\psi_F(X_i)+\mathcal R_n,
\qquad
E_D\mathcal R_n^2\le \frac{C_D}{n^2}.
}
\]

Consequences:
\[
E_D\widehat\Psi_F-\Psi_F
=
\frac{1}{2n}\operatorname{tr}
\bigl(\operatorname{Cov}_D(S)\,D_A^2f_F(M)\bigr)
+O_D(n^{-3/2}),
\]
and
\[
E_D(\widehat\Psi_F-\Psi_F)^2
=
\frac{\operatorname{Var}_D\psi_F}{n}
+O_D(n^{-3/2}).
\]

Here the trace contraction is taken in face coordinates; it is coordinate-independent.

**Proof route:** local smoothness on the face, bounded finite samples, fourth moments of the empirical mean, and a global remainder bound obtained by treating the complement of a fixed local neighborhood crudely.

No CLT is needed.

This is the right answer to candidate (ii): **yes at every fixed finite-configuration law, using relative-face derivatives; no as a general ambient boundary-Hessian statement.** Constants need not be uniform as laws move between faces.

Also specify the target: the estimator is first-order unbiased for \(\Psi_F(D)\), not generally for \(E_DF\).

---

## N4. Joint resolution ellipsoids, including null directions

**Rank 4. High value; relatively cheap after N3.**

For finitely many observables, let
\[
\delta_n=(\widehat\Psi_{F_i}-\Psi_{F_i})_i,\qquad
V=\operatorname{Cov}_D((\psi_{F_i})_i).
\]
Prove
\[
E[\delta_n\delta_n^\top]
=
\frac Vn+O_D(n^{-3/2})
\]
in a matrix norm, with an explicit remainder bound if desired.

For \(\lambda>0\), Markov gives
\[
\boxed{
P\!\left(
n\,\delta_n^\top(V+\lambda I)^{-1}\delta_n\ge r^2
\right)
\le
\frac{
\operatorname{tr}((V+\lambda I)^{-1}V)
+C_D/(\lambda\sqrt n)
}{r^2}.
}
\]

If \(V\) is positive definite, take \(\lambda=0\) with the corresponding inverse-dependent constant.

For singular \(V\), do not simply ignore the kernel. Prove the stronger complementary statement:
\[
\boxed{
E\|P_{\ker V}\delta_n\|^2=O_D(n^{-2}).
}
\]
The first-order sampling fluctuation vanishes exactly in those directions; only nonlinear response error remains.

This is cleaner than calling a scalar Chebyshev bound “two-sided resolution.” Chebyshev gives an upper coverage guarantee, not a matching lower tail bound.

One caveat: an ellipsoid using the unknown \(D\), hence unknown \(V\), is an **oracle coverage theorem**. A computable confidence region requires conservative known quantities or covariance estimation with its own error control.

---

## N5. Explicit barycentric regression and configuration condition numbers

**Rank 5. Medium investment; strong explanatory payoff.**

Formalize the Cauchy–Binet representation from §1.1:
\[
u_F(p)\in\operatorname{conv}\{b_I\}.
\]

Besides the explicit Lipschitz constant, this provides:

- a finite certificate for stability;
- a precise explanation of why Fisher degeneracy does not force response-gradient blow-up;
- a configuration condition number separating feature geometry from reference weights;
- a bridge to computational certification.

The theorem should be proved for arbitrary positive weights, then specialized to the model. That makes it new mathematics rather than another proof of M3.

A useful operator version is a bound on the affine interpolation slope maps \(F\mapsto b_I\), yielding one configuration constant valid for all bounded observables.

---

## N6. The local statistical price of refinement

**Rank 6. High conceptual value; medium-to-large investment.**

This connects the entropy ladder to estimation of actual data expectations.

Let \(D\) be a common model law for a finite nested feature chain. Let \(P_k\) denote the centered \(L^2(D)\)-projection onto level-\(k\) feature scores. Fix a bounded score \(h\), and consider
\[
D_n\propto e^{\tau h/\sqrt n}D.
\]
For iid samples from \(D_n\), estimate \(E_{D_n}F\) using the level-\(k\) empirical response.

The target theorem is
\[
\boxed{
nE_{D_n}\bigl(\widehat\Psi_{k,F}-E_{D_n}F\bigr)^2
\longrightarrow
\operatorname{Var}_D(P_kF)
+
\tau^2\operatorname{Cov}_D(F-P_kF,h)^2.
}
\]
Here \(P_kF\) means projection of the centered observable.

This identifies:

- **sampling cost:** \(\operatorname{Var}_D(P_kF)\);
- **local truth-shift bias:** the score component that the level-\(k\) response fails to see.

For nested levels,
\[
\operatorname{Var}_D(P_{k+1}F)-\operatorname{Var}_D(P_kF)
=
\operatorname{Var}_D(P_{k+1}F-P_kF).
\]

Thus adding features increases first-order sampling variance at a common model base while improving the space of truth shifts that can be represented.

**Important:** for a fixed \(F,h\), the scalar squared bias need not decrease monotonically under refinement; cancellation can disappear. What decreases monotonically is the residual \(L^2\) norm, and corresponding worst-case bias over bounded-\(L^2\) score classes.

This is the precise version of “refine only below the available resolution budget.” It complements, rather than repackages, the KL ladder.

---

# 3. Your other candidates: what to skip or narrow

## General-\(X\) global Lipschitz continuity: false without stronger assumptions

There is a simple bounded, continuous counterexample.

Take
\[
X=[0,1],\quad \nu=\text{uniform},\quad S(x)=x,\quad F(x)=x^\alpha,
\qquad 0<\alpha<1.
\]
For
\[
P_t(dx)\propto e^{-tx}\,dx,\qquad t\to\infty,
\]
one has
\[
m_t\sim t^{-1},
\qquad
E_{P_t}F\sim \Gamma(1+\alpha)t^{-\alpha}.
\]
Thus the response behaves like
\[
f_F(m)\sim \Gamma(1+\alpha)m^\alpha
\]
near zero and is not globally Lipschitz, even when considering only interior means.

The endpoint has infinite rate, but that does not rescue a uniform interior Lipschitz bound.

The finite-configuration theorem is genuinely special. Tail assumptions might provide a modulus of continuity, but boundedness of features and observables alone does not.

## Infinite \(\mathrm{KL}(D\|\nu)\): separate input entropy from mean rate

The response depends on \(D\) only through \(m_D\). Therefore the natural hypothesis is about the **target mean**, not the input law’s KL.

- On a finite configuration with full-support \(\nu\), every probability law has finite KL anyway.
- On general \(X\), infinite input KL can coexist with an interior, finite-rate mean; then the ordinary mean-path calculus still applies.
- At an infinite-rate boundary mean, existence of a suitable endpoint response is a separate issue. A boundary probability law may require a weak extension outside \(Q\ll\nu\).

So first prove a **mean-endpoint version** of the journey theorem, removing unnecessary hypotheses on the representing data law. Do not promise a general infinite-rate endpoint theorem before specifying the endpoint object.

## Constant-feature maximum-entropy lemma

Do it now as a small lemma:
\[
S_0\text{ constant}\quad\Longrightarrow\quad R_0=\nu
\]
for normalized \(\nu\) and its feasible mean.

It improves the narrative considerably, but does not deserve one of the six programme slots.

---

# 4. The note: an eight-theorem spine

I would use the following order, with technical stability lemmas supporting rather than interrupting the story.

1. **Entropy response and sufficiency of the mean.**  
   The response to a data law is the unique relative-entropy projection determined by its feature mean, with the featureless response equal to the reference law.

2. **Differential response equals regression.**  
   The change in a posterior expectation is the pairing of the mean displacement with the regression direction of the observable.

3. **Closed-polytope stability and face calculus.**  
   Despite Fisher degeneracy, the finite-configuration response is globally Lipschitz, and its tangential differential converges to the regression field of the limiting face.

4. **The journey integral.**  
   The entire change from the featureless reference to the data response is the integral of this response field along the mean journey, including boundary endpoints.

5. **Information retained and information discarded.**  
   At a model base, the quadratic response defect is precisely the variance of the score residual after feature regression.

6. **The refinement ladder.**  
   Refining features spends the unresolved KL budget in exact nonnegative increments, whose infinitesimal forms are orthogonal regression increments.

7. **Sampling stability and chamber margins.**  
   Empirical responses exist for every sample, obey global risk bounds, and preserve chamber assignments when the population mean has adequate margin.

8. **The attainable resolution floor.**  
   Covariance determines which mean shifts are attainable and their least information cost, producing matching-scale obstructions to distinguishing responses or differently labelled chambers.

After Programme N, enrich theorem 3 with stratified transport, theorem 7 with face-adaptive second-order risk, and theorem 8 with the joint ellipsoid and local refinement tradeoff.

**The central narrative should now be:** regression gives the response velocity; stability lets that velocity reach the boundary; integration reconstructs the journey; entropy identifies what was lost; sampling determines which parts of the resulting map can actually be resolved.