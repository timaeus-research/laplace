## 1. Recommended shape of the multivariate programme

### (a) First milestone: recover \(H\), not the full jet package

The right first milestone is the self-contained Hessian-recovery theorem:

\[
q^{-2}\Cov_{L,q}(w_i,w_j)\longrightarrow (H^{-1})_{ij},
\qquad q=t^{-1/2}\to0,
\]

followed by the pairwise consequence that matching normalized moments through \(o(q^2)\) forces \(H_1=H_2\).

I would not begin by porting the full one-dimensional profile/weighted-jet machinery. Hessian recovery already forces the project to settle all genuinely new foundations:

1. scalar dilation and volume scaling on \(\mathbb R^d\);
2. dominated convergence on expanding rescaled domains;
3. integrability of polynomially weighted multivariate Gaussian kernels;
4. normalized first and second Gaussian moments;
5. the representation of Hessians and their inverses;
6. covariance bookkeeping.

Once those are stable, the higher-jet theorem should be built as a second layer using the pairwise-difference method. Starting with the general homogeneous-correction package risks debugging scaling, Gaussian integration, polynomial representation, and Taylor bookkeeping simultaneously.

A good intermediate abstraction is not yet “all jets,” but a small rescaled-profile theorem:

> If
> \[
> V_q(x)\to \tfrac12\langle x,Hx\rangle
> \]
> pointwise and \(V_q(x)\ge c\|x\|^2\) on the rescaled domain, then normalized integrals of \(1,x_i,x_ix_j\) converge to the corresponding Gaussian moments.

That is reusable later without committing to the full jet API.

### (b) Multivariate replacement for \(x=qu\)

Fix

\[
E=\operatorname{EuclideanSpace}\mathbb R(\operatorname{Fin}d)
\]

and the homothety \(S_q(x)=q\,x\), with \(q>0\). The wrapper you want is mathematically

\[
\int_E f(w)\,dw
=
q^d\int_E f(qx)\,dx,
\]

or equivalently

\[
(S_q)_*(\mathrm{vol})=q^{-d}\,\mathrm{vol}.
\]

For the local Laplace integral this gives

\[
\int_U \phi(w)e^{-L(w)/q^2}\,dw
=
q^d\int_E
\mathbf 1_U(qx)\,\phi(qx)e^{-L(qx)/q^2}\,dx.
\]

I would isolate this behind one project-local lemma rather than allow downstream proofs to depend directly on whichever Mathlib change-of-variables theorem currently exposes the result. Plausible underlying routes are:

- a linear-equivalence change-of-variables theorem with
  \(\det(qI)=q^d\);
- a statement about `Measure.map` under scalar multiplication;
- product-volume scaling on `Fin d → ℝ`.

The project-facing API should provide both:

```lean
∫ w, f w ∂volume = q ^ d * ∫ x, f (q • x) ∂volume
```

for integrable functions, and preferably a nonnegative/`lintegral` version. The latter often makes integrability proofs less circular.

Restrict initially to `0 < q`. Supporting arbitrary nonzero \(q\) introduces \(|q|^d\) and no useful mathematics.

### (c) Injectivity: use full support and variance, not zero-set geometry

Yes, the clean route is the same full-support argument as in one dimension, and it is even simpler than proving that multivariate polynomial zero sets are nowhere dense.

Let \(\gamma_H\) be the normalized Gaussian measure with density proportional to

\[
e^{-\langle x,Hx\rangle/2}.
\]

Its density is continuous and strictly positive everywhere, so \(\gamma_H\) has full support. Then establish the general lemma:

> If \(\mu\) has full support, \(f\) is continuous and square-integrable, and
> \(\Var_\mu(f)=0\), then \(f\) is constant.

Indeed, variance zero says \(f=c\) almost everywhere. If \(f(x_0)\ne c\), continuity gives a nonempty open neighborhood on which \(|f-c|\) is bounded below; full support gives that neighborhood positive measure, a contradiction.

For a nonzero homogeneous polynomial \(Q\) of degree \(k>0\):

- \(Q(0)=0\);
- there is some \(x\) with \(Q(x)\ne0\);

so \(Q\) is not constant. Therefore

\[
\Var_{\gamma_H}(Q)>0.
\]

No theorem about nowhere-dense polynomial zero sets is required.

---

## 2. Pairwise differences and the multivariate moment matrix

The pairwise-difference route avoids Wick/Isserlis formulas.

Suppose two losses agree below degree \(k\), and their degree-\(k\) difference is the homogeneous polynomial

\[
Q(x)=\sum_{|\beta|=k}c_\beta x^\beta.
\]

After rescaling and dividing by the appropriate power of \(q\), the first unknown contribution to a **normalized** moment tested against \(x^\alpha\) is

\[
-\Cov_{\gamma_H}(x^\alpha,Q).
\]

Thus the relevant matrix is actually the centered Gram matrix

\[
G_{\alpha\beta}
=
\Cov_{\gamma_H}(x^\alpha,x^\beta)
=
M_{\alpha+\beta}-M_\alpha M_\beta,
\qquad |\alpha|=|\beta|=k.
\]

For odd \(k\), the individual degree-\(k\) moments vanish by symmetry, so this reduces to the raw moment matrix \(M_{\alpha+\beta}\). For even \(k\), the centering term must be retained because the posterior data are normalized.

The best proof of injectivity does not explicitly invert this matrix. If all degree-\(k\) monomial tests vanish, linearity gives

\[
\Cov_{\gamma_H}(P,Q)=0
\]

for every homogeneous degree-\(k\) polynomial \(P\). Taking \(P=Q\),

\[
\Var_{\gamma_H}(Q)=0,
\]

hence \(Q=0\). This proves that the covariance Gram matrix is positive definite on the space of positive-degree homogeneous polynomials.

### Lean difficulty

This route is substantially easier than formalizing Isserlis:

- no pairing enumeration;
- no combinatorics of even multi-indices;
- no closed formulas for mixed moments;
- no matrix determinant computation.

The main prerequisites are only:

1. all polynomial moments are finite under the quadratic Gaussian;
2. the Gaussian measure has full support;
3. polynomial evaluation is continuous;
4. a nonzero homogeneous polynomial of positive degree is nonconstant.

For identifiability, avoid introducing a concrete Gram matrix at first. Prove an abstract lemma of the form

```lean
(∀ P ∈ homogeneousDegree k, covariance μ P Q = 0) → Q = 0
```

and instantiate \(P=Q\). If an eventual constructive coefficient extractor is desired, finite-dimensionality then turns the injective covariance map into an invertible matrix after choosing the monomial basis.

A useful implementation choice is to postpone multi-index machinery. Initially represent the new Taylor term as a function \(Q:E\to\mathbb R\) equipped with:

- continuity;
- polynomial-growth bounds;
- homogeneity of degree \(k\);
- a nonzero witness.

Only later identify it with `MvPolynomial (Fin d) ℝ`, indexed by multi-indices `Fin d →₀ ℕ` of total degree \(k\). The latter subtype and its finite enumeration are avoidable in the analytic heart of the proof.

---

## 3. Tide-sized stages for the first milestone: \(H\)-recovery only

I would stage it as follows.

### Stage H0: fix the ambient representation

Use

```lean
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
```

which is coordinate-accessible like `Fin d → ℝ` while also composing with inner products, continuous linear maps, and Hilbert-space Gaussian APIs.

Use:

- `x i` for coordinates;
- `volume` on \(E\);
- matrices at the theorem boundary if the Hessian naturally arrives as a matrix;
- a self-adjoint linear operator or quadratic form internally if that better matches Gaussian/spectral APIs.

Do not make diagonal \(H\) part of the theorem statement.

### Stage H1: scalar-dilation wrapper

Prove project-local change-of-variables lemmas for \(x\mapsto qx\), \(q>0\):

```lean
integral_smul_domain
lintegral_smul_domain
```

with Jacobian \(q^d\), plus a convenient restricted-domain/indicator formulation.

**Main trap:** the pushforward factor is \(q^{-d}\), whereas substitution in
\(\int f(w)\,dw\) produces \(q^d\). Fix one orientation and test it on an indicator of a box or ball.

### Stage H2: the pure quadratic Gaussian package

For positive-definite \(H\), define

\[
K_H(x)=e^{-\langle x,Hx\rangle/2},
\qquad
Z_H=\int K_H.
\]

Prove:

\[
0<Z_H<\infty,
\]

\[
\int x_iK_H(x)\,dx=0,
\]

and

\[
\frac1{Z_H}\int x_ix_jK_H(x)\,dx=(H^{-1})_{ij}.
\]

Also prove integrability of

\[
(1+\|x\|+\|x\|^2)e^{-c\|x\|^2}.
\]

This is the largest API spike. First investigate whether Mathlib’s multivariate Gaussian measure already supplies the covariance theorem **and** a usable density identification. If the density bridge is awkward, use:

1. the standard \(H=I\) Gaussian;
2. a positive square root/whitening map \(H^{1/2}\);
3. linear change of variables.

The determinant factor cancels after normalization. Whitening is preferable to diagonalization: explicit diagonal reduction imports eigenbasis choices and coordinate transport that the final theorem does not need.

### Stage H3: local quadratic rescaling

From \(C^2\) regularity at \(0\), \(DL(0)=0\), and \(D^2L(0)=H\), prove for fixed \(x\):

\[
\frac{L(qx)-L(0)}{q^2}
\longrightarrow
\frac12\langle x,Hx\rangle.
\]

From the local nondegenerate lower bound, obtain on the rescaled domain:

\[
\frac{L(qx)-L(0)}{q^2}\ge c\|x\|^2.
\]

Package these as the hypotheses consumed by the next stage.

### Stage H4: dominated convergence for moments \(0,1,2\)

For

\[
h(x)\in\{1,\;x_i,\;x_ix_j\},
\]

prove

\[
\int
\mathbf 1_U(qx)\,h(x)
e^{-(L(qx)-L(0))/q^2}\,dx
\longrightarrow
\int h(x)e^{-\langle x,Hx\rangle/2}\,dx.
\]

Use domination by

\[
(1+\|x\|^2)e^{-c\|x\|^2}.
\]

This should be one reusable finite-family theorem or three simple corollaries of a generic dominated-convergence lemma.

**Main trap:** the domain expands with \(q\). Writing it as an indicator on the fixed space \(E\) is much cleaner than integrating over the set \(q^{-1}U\).

### Stage H5: normalize and form covariance

Cancel the common \(q^d e^{-L(0)/q^2}\) factors and divide by the zeroth moment. Deduce

\[
q^{-1}\E_q[w_i]\to0,
\]

\[
q^{-2}\E_q[w_iw_j]\to(H^{-1})_{ij},
\]

and hence

\[
q^{-2}\Cov_q(w_i,w_j)\to(H^{-1})_{ij}.
\]

The first-moment limit is needed: covariance is not automatically the raw second moment merely because the minimum has been translated to zero.

### Stage H6: pairwise Hessian recovery

State the first identifiability result:

> If two admissible losses with minima at \(0\) have normalized coordinate first and second moments agreeing to the required order—equivalently their covariance matrices differ by \(o(q^2)\)—then
> \[
> H_1^{-1}=H_2^{-1},
> \]
> hence \(H_1=H_2\).

This is the multivariate analogue of `base_recovery`. Only after this theorem is stable should the project proceed to homogeneous degree-\(k\) pairwise differences.

## Representation recommendation

Use `EuclideanSpace ℝ (Fin d)` throughout. It should preserve the coordinate behavior of `Fin d → ℝ` while composing better with:

- inner products and quadratic forms;
- positive/self-adjoint operators;
- square roots and spectral results;
- Mathlib’s Hilbert-space Gaussian infrastructure.

Fubini over coordinates is still available because the underlying type is a finite function space, although decomposition of `Fin (d+1)` may need an explicit equivalence. Since the recommended proof does not require repeated coordinatewise Fubini once the Gaussian package is established, that cost should not drive the global representation choice.

In short: **Hessian recovery first; one robust dilation wrapper; whitening rather than diagonalizing; covariance-Gram injectivity rather than Wick formulas; and full support plus continuity rather than multivariate polynomial zero-set theory.**