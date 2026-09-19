## 1. Correctness and the clean condition

**A and B are correct. C’s linear-algebra statement is correct, but its claimed consequence about recovery from all asymptotic orders does not follow.** Two distinctions are essential:

- homogeneous **polynomials** versus arbitrary continuous homogeneous functions;
- detecting a perturbation at its **first possible rate** versus detecting it somewhere in the **entire expansion**.

### (A) Use the space of homogeneous polynomial diagonals

Let \(\mathcal H_k\) be the finite-dimensional space of degree-\(k\) homogeneous polynomials, equivalently diagonals of symmetric \(k\)-tensors, and define
\[
\mathcal T_{S,H,k}:\mathcal H_k\longrightarrow \mathbb R^\iota,
\qquad
Q\longmapsto \bigl(\operatorname{Cov}_{\gamma_H}(\phi_i,Q)\bigr)_i.
\]

Then
\[
\ker\mathcal T_{S,H,k}=\{0\}
\]
is exactly the clean condition for **uniform degree-\(k\) recovery at the leading rate, conditional on equal lower jets**.

Your stronger hypothesis, injectivity on all continuous polynomially-growing homogeneous functions, still gives a valid theorem. But it is unnecessarily strong: in \(d\ge2\), that space is generally infinite-dimensional, so finite families cannot satisfy it even at a fixed degree. For compatibility with your existing finite monomial results, quantify over polynomial/tensor diagonals.

Statement-level Lean shape, using schematic names:
```lean
def observablePairingMap :
    HomogeneousPolynomialSpace d k →ₗ[ℝ] (ι → ℝ) := ...

theorem kthJet_eq_of_observable_rates
    (hinj : Function.Injective (observablePairingMap H φ))
    (hlower : EqualJetsBelow k L₁ L₂)
    (hrates : ∀ i, Tendsto
      (fun q =>
        (A₁.rescaledMoment (φ i) q -
         A₂.rescaledMoment (φ i) q) / q^(k-2))
      (𝓝[>] 0) (𝓝 0)) :
    iteratedFDeriv ℝ k L₁ 0 = iteratedFDeriv ℝ k L₂ 0
```
If introducing a polynomial-space bundle is expensive, make `hinj` a kernel-zero hypothesis directly on symmetric-tensor diagonals.

### Dependence on \(H\), and the proposed \(k\)-jet reduction

The pairing generally depends on \(H\). However, **“the \(k\)-jets of the tests span \(\mathcal H_k\)” is not sufficient**, because the pairing uses the actual rescaled test on Gaussian space, not its germ at zero.

Already in one dimension, set
\[
\phi(x)=x^k-cx^{k+2},
\qquad
c=\frac{\operatorname{Cov}(X^k,X^k)}
        {\operatorname{Cov}(X^{k+2},X^k)}.
\]
The denominator is nonzero for a nondegenerate centered Gaussian and \(k>0\). Then \(\phi\) has the same \(k\)-jet as \(x^k\), but
\[
\operatorname{Cov}(\phi(X),X^k)=0.
\]

A genuinely \(H\)-uniform sufficient condition is
\[
\mathcal H_k\subseteq \operatorname{span}\{\phi_i\}+\mathbb R\mathbf 1
\]
as **functions**, not merely as jets. Covariance annihilates constants, and your rigidity theorem finishes the argument.

In particular, spanning by actual degree-\(k\) homogeneous polynomial tests works for every positive-definite \(H\).

Also avoid replacing “\(k\)-jet” by “degree-\(k\) Hermite component”: a degree-\(k\) homogeneous polynomial generally has Hermite components in degrees \(k,k-2,\ldots\). The correct finite-dimensional object is the Gaussian \(L^2\) projection onto the space of **centered homogeneous polynomials**.

### (B) Correct, and worth stating as an iff

Under the hypotheses of the pairing-limit theorem:
\[
\left[\forall i,\quad
\Delta M_i(q)=o(q^{k-2})\right]
\iff
\left[\forall i,\quad
\operatorname{Cov}_{\gamma_H}(\phi_i,Q_k)=0\right].
\]

This is the most informative relative statement. It says precisely what the data fail to see **at that rate**.

### (C) The count is correct, but not optimal in higher dimension

The exact dimension is
\[
\dim\mathcal H_k=\binom{k+d-1}{d-1}.
\]
Thus any family of \(n\) tests has a nonzero kernel whenever
\[
\binom{k+d-1}{d-1}>n.
\]

Your two-coordinate argument gives the simpler sufficient condition \(k+1>n\), hence \(k\ge n\). It is sharp as a dimension count for \(d=2\), but in \(d>2\) the full dimension count can give failure earlier. For the Laplace application, retain \(k>2\).

**The important correction:** C+B+B′ do **not** prove that no finite family recovers the full jet from its entire expansions. A perturbation invisible at order \(q^{k-2}\) may be visible later.

For example, with \(H=I\), take locally
\[
L_0(x)=\tfrac12|x|^2,\qquad
L_\varepsilon(x)=\tfrac12|x|^2+\varepsilon x_1^3,
\qquad \phi(x)=x_1^2.
\]
The degree-three covariance vanishes by parity. Nevertheless, the next correction is nonzero:
\[
M_\varepsilon(q)-M_0(q)
=
\frac{\varepsilon^2q^2}{2}
\operatorname{Cov}(X_1^2,X_1^6)+o(q^2)
=
45\varepsilon^2q^2+o(q^2).
\]
A sufficiently small localization ball makes both losses admissible.

Consequently, the justified conclusion is:

> No fixed finite family is injective on homogeneous perturbations at their first possible asymptotic rate in every degree, when \(d\ge2\).

The stronger full-expansion impossibility claim requires a separate argument.

The one-dimensional observation about \(\{x^2,x^3\}\) is correct for this leading-rate induction: \(x^2\) detects every positive even degree and \(x^3\) every odd degree.

## 2. Scope and the cost of B′

I recommend **A+B+C, with C explicitly limited to leading-rate noninjectivity**. This is a coherent theorem package:

1. define the observation operator;
2. identify its kernel with leading-rate indistinguishability;
3. deduce recovery from injectivity;
4. give a finite-dimensional obstruction to injectivity.

I would not estimate its Lean cost confidently without inspecting the available covariance linearity and polynomial-space infrastructure.

B′ adds an important but narrower benefit: it turns an algebraic kernel direction into an **actual pair of certified losses**. It still does not establish full-expansion indistinguishability.

### A cheaper B′ target

If the objective is existential sharpness, do not perturb an arbitrary certified \(L_1\). Start from the quadratic loss:
\[
L_0(x)=\tfrac12H(x,x),\qquad L_1(x)=L_0(x)+Q(x).
\]
For \(k>2\),
\[
|Q(x)|\le C\|x\|^k
\]
and shrinking the ball preserves a quadratic lower bound. Since \(L_1\) is a polynomial of degree at most \(k\), its order-\(k\) Taylor remainder is zero.

This avoids much of the general package-addition machinery, though you still need to identify the polynomial’s Taylor coefficients.

I would split the formal work into:

```lean
-- Algebraic/analytic polynomial lemma
theorem diagonalPolynomial_jets_at_zero ...

-- Domain-construction lemma
theorem higherLaplaceDomain_quadratic_add_homogeneous ...
```

For arbitrary-base perturbation, the useful abstraction is instead:

```lean
theorem HigherLaplaceDomain.add_homogeneousPerturbation
    (hjets : ... lower derivatives vanish ...)
    (hkjet : ... kth derivative prescribed ...)
    (hbound : ∀ x, ‖Q x‖ ≤ C * ‖x‖^k)
    ...
```

This isolates the derivative API problem from the shrinking-ball argument. An explicit polynomial Taylor series via `HasFTaylorSeriesUpTo` is conceptually appropriate, but whether it is cheaper than multilinear differentiation depends on existing bridges to your `taylorHomogeneousTerm`; I would not promise an API shortcut without checking them.

For the paper, “perturb by \(Q\) and shrink the ball” is a reasonable short justification of realizability. For Lean, B′ is a useful separate follow-up rather than a prerequisite for the main observation-operator theorem.

## 3. Better nearby approximation statements

### Best addition: recovery modulo the invisible subspace

Without injectivity, the leading coefficients determine exactly
\[
[Q_k]\in \mathcal H_k/\ker\mathcal T_{S,H,k}.
\]

Equivalently, equip \(\mathcal H_k\) with
\[
\langle P,Q\rangle_H=\operatorname{Cov}_{\gamma_H}(P,Q).
\]
For \(k>0\), your rigidity result makes this positive definite. The data determine the orthogonal projection of \(Q_k\) onto
\[
(\ker\mathcal T_{S,H,k})^\perp.
\]

This is a clean answer to “what approximation results from fewer observables?”:

> Fewer observables recover the visible component of the homogeneous Taylor term, leaving precisely a covariance-orthogonal invisible component.

A cheap formal statement needs no quotient or orthogonal-projection API:
```lean
theorem pairingData_eq_iff_sub_mem_kernel
    (Q R : HomogeneousPolynomialSpace d k) :
    observablePairingMap H φ Q = observablePairingMap H φ R ↔
      Q - R ∈ LinearMap.ker (observablePairingMap H φ)
```
The substantive theorem connects the pairing data to your proven asymptotic limits.

For finitely many tests, a later quantitative extension is a singular-value estimate:
\[
\|Q_{\mathrm{visible}}\|_H
\le C_{S,H,k}\|\mathcal T_{S,H,k}Q\|.
\]
That gives stable recovery from noisy leading coefficients, not just qualitative identifiability.

### Your \(D+1\) proposal

With equal jets below \(k=D+1\) and a kernel perturbation,
\[
\Delta M_i(q)=o(q^{D-1})
\]
is exactly B. Realizing a nonzero such perturbation requires B′ or an equivalent construction.

Replace “S spans degree-\(\le D\) jets” by injectivity of the appropriate observation operators in degrees \(3,\ldots,D\), or by an actual-function spanning condition.

There is no additional “all orders” conclusion contained in that little-\(o\) statement. Agreement through more asymptotic orders imposes further equations involving higher Taylor terms and nonlinear expressions in the earlier perturbation. The cubic example above exhibits the obstruction immediately.

Likewise, “monomials through degree \(N\) recover the \(N\)-jet” is a sufficiency statement; **“exactly the \(N\)-jet” should not mean they contain no information about higher jets.**

### Localization and germs

Shrinking a fixed localization ball is harmless for algebraic asymptotics under the certified quadratic lower bound: the removed annulus contributes exponentially small terms, including with polynomially growing rescaled tests. But transferring between packages with different balls may need an explicit lemma unless your pairing theorem already handles it.

Finally, distinguish **full Taylor jet** from **smooth germ**. Smooth flat perturbations can change the germ without changing any Taylor coefficient or power-series Laplace asymptotics. Germ recovery needs analyticity, another suitable uniqueness class, or stronger data than these asymptotic coefficients.

## 4. Single tide target

Make the central theorem the **leading-rate observation-operator characterization**, with injective recovery and finite-family kernel obstruction as corollaries. Add the quotient interpretation in the exposition, and possibly its inexpensive kernel statement in Lean. Defer perturbation-package construction.

**Vote: A+B+C, restricted to polynomial/tensor diagonals and explicitly framed as leading-rate recovery—not a no-finite-family theorem for entire asymptotic expansions.**