## 1. Mathematical correctness of A–D

**Yes, with explicit normalization and nondegeneracy hypotheses.** D’s spectrum-independence argument is correct under the note’s parameterization, where every direction has the same limiting relative-error coefficient.

### A. Linearity and bilinearity

These are the right supporting lemmas. Under the stated weighted-integrability assumptions,
\[
\mathbb E\!\left[\sum_i a_i\phi_i\right]
 =\sum_i a_i\mathbb E[\phi_i],
\qquad
\operatorname{Cov}\!\left[\sum_i a_i\phi_i,\psi\right]
 =\sum_i a_i\operatorname{Cov}[\phi_i,\psi].
\]

Two distinctions matter for totalised integrals:

- Finite-sum linearity needs integrability; scalar-multiplication identities can generally be proved without it.
- These identities do **not** require \(Z\ne0\): division by the common denominator distributes even with totalised division. However, constant/translation identities used in C require
  \[
  \mathbb E[1]=1.
  \]
  Establish this from the integrable density and \(Z\ne0\), rather than treating it as automatic.

Thus add small lemmas for expectation of constants and covariance invariance under adding constants. They will make C substantially cleaner.

### B. Integrability transport

Correct for orthogonal \(Q\), with the admissible oscillator parameters and \(t>0\).

On the separable side, express the weighted monomial as
\[
\prod_k x_k^{e_k}e^{-t\ell_k(x_k)},
\]
then use one-dimensional integrability and `Integrable.fintype_prod`. For a coordinate product, use
\[
e_k=\mathbf1_{k=i}+\mathbf1_{k=j},
\]
so the diagonal case \(i=j\) correctly produces degree two.

You will also need the degree-zero case for density integrability and, after affine reconstruction, integrability of the **ambient** coordinates and their products.

### C. Ambient moments

Correct:
\[
\mathbb E_w[w_j]-c_j
 =\sum_iQ_{ji}\mathbb E_{\ell_i}[u_i],
\qquad
\operatorname{Cov}_w(w_j,w_k)
 =\sum_iQ_{ji}Q_{ki}\operatorname{Var}_{\ell_i}(u_i).
\]

The proof is exactly affine reconstruction, normalized constant identities, bilinearity, frame independence, and diagonal separable covariance. The ambient mean limit follows by finite-sum limit rules:
\[
t(\mathbb E_w[w_j]-c_j)
 \longrightarrow
 -\sum_iQ_{ji}\frac{\alpha_i}{2\lambda_i^2}.
\]

### D. Relative Frobenius error

Correct, assuming a **nonempty finite index type**, \(\lambda_i>0\), and the common directional limit
\[
t(\lambda_i tV_i(t)-1)\longrightarrow b,
\qquad b=a^2-\tfrac12.
\]

Let
\[
r_i(t)=\lambda_i tV_i(t)-1,\qquad
W=\sum_i\lambda_i^{-2}>0.
\]
Orthogonal invariance and diagonal reduction give, for \(t\ne0\),
\[
R(t)^2:=
\frac{\|\operatorname{Cov}_w(t)-S_w(t)\|_F^2}
     {\|S_w(t)\|_F^2}
=\frac{\sum_i\lambda_i^{-2}r_i(t)^2}{W}.
\]
Consequently,
\[
t^2R(t)^2
=\frac{\sum_i\lambda_i^{-2}(t\,r_i(t))^2}{W}
\longrightarrow b^2,
\]
and therefore
\[
tR(t)\longrightarrow |b|.
\]

So the claimed expansion is valid, including \(b=0\), where it says \(R(t)=o(1/t)\).

**The universality comes from the common directional coefficient, not from rotation alone.** If the directional limits were \(b_i\), the limit would instead be
\[
tR(t)\longrightarrow
\sqrt{\frac{\sum_i\lambda_i^{-2}b_i^2}
           {\sum_i\lambda_i^{-2}}}.
\]
That distinction is worth documenting.

The numerical check is consistent with this result, but the asymptotic theorem alone does not certify the finite-\(t\) value at \(t=10\).

## 2. Least-painful Lean route for B

**Use route (i) for this tide.** You already have the matrix integrability equivalence, so applying it to \(Q^\mathsf T\), then transporting through translation, introduces the least new infrastructure.

Package the result once as an affine-frame integrability transport lemma. The coordinate and product cases can then instantiate it rather than repeat change-of-variables machinery. Check the orientation of `comp_sub_right` against
\[
w\mapsto g(Q^\mathsf T(w-c));
\]
that bookkeeping is the principal nuisance.

Route (ii) is mathematically attractive if more frame-transport results are planned. Crucially:

- **Forward transport** of an integrable, appropriately measurable target function through a measure-preserving map does not mathematically require a measurable equivalence.
- A two-way `Integrable` equivalence can involve additional measurability-reflection hypotheses; a measurable embedding/equivalence supplies these conveniently.
- The precise hypotheses of the named Mathlib `integrable_comp` theorem should be checked in your checkout rather than inferred from its name.

Here the affine frame is a continuous affine bijection anyway, so a `MeasurableEquiv` is available. Nevertheless, building that interface solely for B is unnecessary given the existing matrix lemma.

## 3. Cleanest formulation of D

**Make the squared-ratio `Tendsto` theorem primary:**
\[
\operatorname{Tendsto}\left(
t\mapsto
t^2\frac{\sum_{j,k}(\operatorname{Cov}_w(t)_{jk}-S_w(t)_{jk})^2}
          {\sum_{j,k}S_w(t)_{jk}^2}
\right)
(\mathrm{atTop})
\left(\mathcal N\bigl((a^2-\tfrac12)^2\bigr)\right).
\]

A clean proof decomposition is:

1. Exact Frobenius identities under orthogonal conjugation.
2. The eventual weighted-sum identity above, using \(t>0\).
3. Finite-sum convergence and division by the fixed positive \(W\).
4. Optionally, a square-root corollary stating \(tR(t)\to|a^2-\tfrac12|\).

No monotonicity or weighted-mean bound is needed. A small generic weighted finite-sum convergence lemma is reasonable only if it actually shortens the proof.

Also check the note’s denominator convention. Your formula normalizes by the **prediction**. If the plotted error instead normalizes by the exact covariance, the exact identity changes, but the leading coefficient remains the same because
\[
\|\operatorname{Cov}_w(t)\|_F/\|S_w(t)\|_F\to1.
\]

**Do not introduce \(\Sigma_{\mathrm{ULA}}\)** here. This is Laplace prediction versus exact Gibbs covariance. Likewise, this theorem covers the leading Laplace covariance prediction; it does not automatically establish error rates for all four predictions mentioned in the panel.

## Vote

**Formalise A–D**, with A kept to the lemmas C actually uses, B implemented through the existing matrix-plus-translation route, and D delivered first as the squared-ratio limit. C is the essential ambient-moment bridge; D is a small, meaningful payoff that should remain in scope.