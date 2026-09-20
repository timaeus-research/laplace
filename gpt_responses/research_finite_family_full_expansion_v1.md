There is an important distinction in your formulation:

1. **Fixed rescaled tests:** observe \(M_{L,h}(P_i)\), with \(P_i(z)\) independent of \(h\).
2. **Fixed physical tests:** observe \(\langle\phi_i(x)\rangle_{L,t}\), so the rescaled test is \(\phi_i(hz)\).

These are interchangeable for homogeneous polynomials, but **not for arbitrary continuous polynomial-growth observables**.

This distinction changes the answer. **As (A) is literally stated for physical observables, it is false:** one continuous polynomial-growth observable can recover every jet, and hence every analytic germ modulo constants. The observable is nonsmooth and encodes countably many angular tests using different fractional homogeneities.

For the fixed-rescaled-test interpretation, I do not have a general resolution of (A). The dimension count, kernel theorem, and Gaussian-relative rigidity do not resolve it.

## 1. A single continuous physical observable that identifies all jets

Here is a construction valid for every \(d\ge2\) and every fixed positive-definite Hessian \(H\).

Whiten coordinates, writing
\[
y=H^{1/2}x,\qquad r=|y|,\qquad \theta=y/|y|.
\]
The reference Gaussian in \(y\)-coordinates is standard.

Let
\[
Y_0,Y_1,\ldots
\]
be a real orthonormal spherical-harmonic basis on \(S^{d-1}\), including \(Y_0=1\), with sphere measure normalized to be a probability measure. Enumerate it by nondecreasing harmonic degree.

Choose distinct, strictly increasing exponents
\[
0<a<\alpha_0<\alpha_1<\cdots<b<1
\]
and positive weights \(w_j\) satisfying
\[
\sum_j w_j\|Y_j\|_\infty<\infty.
\]
Define
\[
\phi(x)=
\begin{cases}
\displaystyle\sum_{j=0}^\infty
 w_j r^{\alpha_j}Y_j(\theta),&x\ne0,\\
0,&x=0.
\end{cases}
\]

Then \(\phi\) is continuous and has polynomial growth, since
\[
|\phi(x)|\le C(r^a+r^b).
\]

### Claim

Under the usual local Laplace hypotheses, if two smooth losses with Hessian \(H\) satisfy
\[
\langle\phi\rangle_{L_1,t}
-
\langle\phi\rangle_{L_2,t}
=\operatorname{SuperPoly},
\]
then all their positive-degree Taylor coefficients agree.

Consequently, for analytic losses,
\[
L_1-L_1(0)=L_2-L_2(0)
\]
near \(0\).

### Proof

Suppose instead that the first differing homogeneous Taylor coefficient is
\[
Q_k=T_kL_1-T_kL_2\ne0,\qquad k\ge3.
\]
Set \(h=t^{-1/2}\) and
\[
P_j(z)=|z|^{\alpha_j}Y_j(z/|z|)
\]
in whitened coordinates. Homogeneity gives
\[
\phi(hz)=\sum_j w_jh^{\alpha_j}P_j(z).
\]

The usual first-discrepancy calculation, now with a uniformly polynomially bounded \(h\)-dependent test, gives
\[
\begin{split}
\Delta(h)
&:=\langle\phi\rangle_{L_1,h^{-2}}
-\langle\phi\rangle_{L_2,h^{-2}}\\
&=-h^{k-2}\sum_j w_jh^{\alpha_j}
  \operatorname{Cov}_\gamma(P_j,Q_k)
  +O(h^{k-1+a}).
\end{split}
\tag{1}
\]
This is not an immediate application of a theorem for one fixed test, but its proof uses the same weighted Taylor estimates: uniformly for \(0<h\le1\),
\[
|\phi(hz)|\le Ch^a(|z|^a+|z|^b).
\]

Write
\[
Q_k(r\theta)=r^k\sum_j c_jY_j(\theta).
\]
Only finitely many \(c_j\) are nonzero.

For every nonconstant harmonic,
\[
\operatorname{Cov}_\gamma(P_j,Q_k)
=c_j\,\mathbb E R^{k+\alpha_j}.
\]
For the constant harmonic,
\[
\operatorname{Cov}_\gamma(P_0,Q_k)
=c_0\,\operatorname{Cov}(R^{\alpha_0},R^k).
\]
The latter covariance is strictly positive: both functions are strictly increasing and \(R\) is nondegenerate.

Thus:

* only finitely many covariances in (1) are nonzero;
* they all vanish iff \(Q_k=0\).

Choose the smallest exponent \(\alpha_*\) having nonzero covariance. Equation (1) implies
\[
\Delta(h)\sim C_*h^{k-2+\alpha_*},
\qquad C_*\ne0.
\]
Indeed, all other nonzero terms have larger exponents, and
\[
k-1+a>k-2+b>k-2+\alpha_*.
\]
This contradicts superpolynomial agreement. ∎

### What this answers—and what it does not

This disproves (A), **in both the smooth-jet and analytic-germ categories, for the literal physical-observable formulation**.

However, this observable generally does **not** have an ordinary integer-power expansion in \(h\). It has fractional homogeneities, with accumulation among their exponents. Its superpolynomial agreement condition is perfectly meaningful, but it lies outside a formulation requiring every physical observable to possess an ordinary half-integer Laplace expansion.

In particular, this construction does **not** answer the problem
\[
L\longmapsto
\bigl(\text{ordinary full expansion of }M_{L,h}(P_i)\bigr)_{i=1}^n
\]
for fixed rescaled \(P_i\).

**Recommendation:** explicitly choose one of these formulations before stating the open problem. The unrestricted physical-continuous version already has a positive identifiability theorem.

Also, in the smooth category the conclusion should be **equality of jets**, not equality of germs: flat perturbations are invisible to ordinary local asymptotics.

---

## 2. Your proposed elementary finite families are not globally identifying

Regardless of the distinction above, there are simple analytic counterexamples for the suggested polynomial families.

### Radial families

Any family of \(H\)-radial observables is invariant under \(H\)-orthogonal changes of variables. Thus, if
\[
L_2(x)=L_1(Rx),\qquad R^\top HR=H,
\]
then all radial moments agree exactly on an \(H\)-invariant localization domain.

Choosing \(L_1\) nonradial gives distinct analytic germs with the same Hessian. Therefore
\[
\{q,q^2\}
\]
cannot identify arbitrary analytic germs.

This is fully consistent with Gaussian-relative rigidity: the quadratic reference is itself rotation invariant.

### All monomials of degree at most two

Even this family is not globally identifying.

In whitened coordinates take
\[
L_1(y)=\frac12|y|^2+\varepsilon\sum_{i=1}^d y_i^4,
\qquad
L_2(y)=L_1(Ry),
\]
where \(\varepsilon>0\) and \(R\) is an orthogonal transformation not preserving \(\sum_i y_i^4\).

On a ball, the \(L_1\)-posterior is invariant under coordinate sign changes and permutations. Hence, for every \(t\),
\[
\mathbb E_{L_1,t}y=0,\qquad
\mathbb E_{L_1,t}(yy^\top)=c(t)I.
\]
The rotated posterior has exactly the same first and second moments. The germs are nevertheless distinct.

The same pair also agrees on every radial observable. These are **polynomial analytic counterexamples**, with no convergence construction required.

For non-invariant localization domains containing a common neighborhood of the minimum, one can usually replace exact equality by exponentially small disagreement, assuming the standard localization gap.

---

## 3. Assessment of the fixed-rescaled-test problem

For the interpretation closest to your `momentCoeff` and `pairingMap` machinery, your assessment is essentially correct, with two qualifications.

### 3.1 Truncation dimension count is valid but unnecessary

For fixed rescaled \(P_1,\ldots,P_n\), coefficients through order \(h^{J-2}\) depend on jets through degree \(J\). Dimension arguments therefore prove noninjectivity once the source dimension exceeds the target dimension.

But your single-top-degree kernel construction proves the desired truncated statement more directly and more strongly: it produces a collision **with the quadratic reference**.

### 3.2 The surjective induction is a valid conditional theorem

Write the coefficient recursion schematically as
\[
C_m(u_3,\ldots,u_{m+2})
=
-A_{m+2}u_{m+2}
+B_m(u_3,\ldots,u_{m+1}),
\]
where
\[
A_jQ=(\operatorname{Cov}_\gamma(P_i,Q))_{i=1}^n.
\]

If \(A_j\) is surjective for every \(j\ge j_0\), and some starting degree \(s\ge j_0\) has nonzero kernel, then:

1. keep the lower jets equal;
2. change degree \(s\) by a nonzero kernel element;
3. solve the subsequent affine equations using surjectivity.

This produces distinct formal jets with identical coefficients at every order.

A Borel realization then gives smooth losses. Positive definiteness of the prescribed Hessian ensures a strict local minimum after shrinking the neighborhood. Equality of all expansion coefficients gives superpolynomial agreement whenever the all-orders expansion hypotheses are available.

The genuinely conditional part is surjectivity, not the recursion.

### 3.3 Missing ranges are real compatibility equations

If \(A_j\) is not surjective, the equation is solvable precisely when its right-hand side lies in \(\operatorname{range}A_j\). Equivalently, every left-annihilator imposes a constraint on previous choices.

There is no general argument that “many remaining jet variables” automatically satisfy these constraints. Your two-radial Gaussian rigidity theorem demonstrates why such an argument would be invalid: later equations can impose positive-definite conditions on an earlier kernel direction.

Parity sometimes eliminates an equation automatically—for example, an even test and an even loss give an even expansion—but it does not eliminate arbitrary cokernel constraints.

**I cannot give a general proof or counterexample for unrestricted finite families of fixed rescaled tests from these ingredients.** In particular, I would not state universal formal/smooth blindness as a theorem without an additional argument handling these compatibility conditions.

### 3.4 Analytic realization is another independent gap

Even under the surjectivity hypothesis, formal solvability does not imply analytic solvability.

One needs a majorant argument controlling both:

* norms of selected right inverses \(A_j^{-1}\);
* growth of the recursively generated nonlinear terms.

Merely making the initial perturbation small, or requesting summably small higher coefficients, does not establish either property. Formal solutions of the affine recursion can have zero radius of convergence.

Nor does finite-truncation dimension growth alone justify a claim about positive-dimensional **full** formal or analytic fibres. Finite-level collisions need not form compatible infinite branches.

---

## 4. Statement (C): yes, your existing kernel construction is essentially enough

Use the convention that “through order \(J-2\)” means coefficients
\[
m=0,\ldots,J-2.
\]
Since your forward theorem uses \(m<N\), take \(N=J-1\).

Let
\[
L_0=P=\tfrac12qform,\qquad L_Q=P+Q,\qquad Q\in H_J.
\]
Then
\[
c_m(L_Q,P_i)=c_m(L_0,P_i)
\quad(m<J-2),
\]
and
\[
c_{J-2}(L_Q,P_i)-c_{J-2}(L_0,P_i)
=-\operatorname{Cov}_\gamma(P_i,Q).
\]

Consequently, every nonzero
\[
Q\in\ker A_J
\]
gives two distinct polynomial jets with identical data through order \(J-2\).

For \(d\ge2\), your sufficient condition \(J\ge\max(n,3)\) supplies such a \(Q\).

No invariance of domain or semialgebraic dimension theorem is needed.

### An even shorter route from the existing blindness theorem

If `exists_pair_finite_family_blind` already gives
\[
M_{L_Q,h}(P_i)-M_{L_0,h}(P_i)=o(h^{J-2}),
\]
and both sides have expansions through that order, uniqueness of asymptotic coefficients implies that all coefficients through \(J-2\) agree.

So there are two routes:

* **algebraic:** prove the explicit top-degree coefficient formulas;
* **asymptotic:** combine existing blindness with coefficient uniqueness.

The latter may be the shortest retained proof.

### The exact gap between (C) and full blindness

(C) gives
\[
\forall J\;\exists(L_{1,J},L_{2,J})
\quad\text{matching through order }J-2.
\]
Full blindness requires
\[
\exists(L_1,L_2)\;\forall J
\quad\text{matching through order }J-2,
\]
with some fixed finite-degree jet discrepancy.

In the top-degree construction, the first discrepancy escapes to degree \(J\). Its limiting formal pair can therefore be the identical pair.

Furthermore, retaining a fixed nonzero discrepancy requires solving all subsequent compatibility equations; analytic realization additionally requires convergence.

That is the honest gap.

For arbitrary **physical continuous** tests, however, (C)'s claimed finite-dimensional ordinary coefficient map need not exist. The construction in §1 exploits exactly that failure.

---

## 5. Recommended formalization order

The estimates below are rough **retained Lean lines**, not verified repository estimates. They assume your cited infrastructure and suitable expansion-uniqueness lemmas.

### Rank 1: coefficient uniqueness from a little-\(o\) difference

Schematic statement:

```lean
theorem coeff_eq_of_sub_isLittleO
    (hf : HasExpansion f a N)
    (hg : HasExpansion g b N)
    (hfg : (fun h => f h - g h) =o[𝓝[>] 0]
      (fun h => h ^ r))
    (hr : r < N) :
    ∀ m ≤ r, a m = b m
```

**Estimate:** 30–100 lines if not already available.

**Status:** routine asymptotic formalization.

### Rank 2: truncated coefficient collision

```lean
theorem exists_polynomial_pair_same_coeffs_through
    (hd : 2 ≤ d)
    (hJ : max n 3 ≤ J) :
    ∃ Q : HomogeneousPolynomial d J,
      Q ≠ 0 ∧
      ∀ i m, m ≤ J - 2 →
        coeff (quadraticLoss H + Q) (P i) m =
        coeff (quadraticLoss H) (P i) m
```

Actual statements will need explicit certified domains or a package-independent coefficient definition.

**Estimate:** 40–150 lines over existing blindness and uniqueness.

**Status:** best immediate target; not research.

### Rank 3: noninjectivity of the truncated data map

```lean
theorem not_injective_truncatedData
    (hd : 2 ≤ d)
    (hJ : max n 3 ≤ J) :
    ¬ Function.Injective (truncatedData H P J)
```

**Estimate:** 20–80 lines after Rank 2, excluding construction of a new jet-coordinate API.

**Status:** routine corollary.

This is the clean theorem to advertise as **finite-order nonidentifiability**, not full-expansion nonidentifiability.

### Rank 4: analytic counterexample for radial and quadratic probes

Formalize the rotated quartic example above.

**Estimate:** 150–500 lines, depending on orthogonal change-of-variables and symmetry APIs.

**Status:** established mathematics; meaningful complementary result. It separates Gaussian-relative rigidity from global identifiability without Borel machinery.

### Rank 5: conditional formal lifting

```lean
theorem exists_distinct_formalJets_same_all_coeffs
    (hsurj : ∀ j ≥ j₀, Function.Surjective (pairingMap H P j))
    (hker : ∃ Q, Q ≠ 0 ∧ pairingMap H P s Q = 0)
    (hs : j₀ ≤ s) :
    ∃ u v : FormalLossJet H,
      u ≠ v ∧
      ∀ i m, formalCoeff u (P i) m = formalCoeff v (P i) m
```

**Estimate:** 200–600 lines if formal jets and triangular coefficient dependence are already packaged.

**Status:** routine mathematics, potentially substantial infrastructure.

Keep formal lifting separate from smooth realization.

### Rank 6: Borel realization and its domain certification

I cannot reliably confirm a current Mathlib theorem named `exists_smooth_of_jet`, or an equivalent multivariate Borel extension theorem, without checking the actual checkout. **Do not budget this step as an available one-line invocation.**

Even with Borel realization, you must connect the resulting function to your `HigherLaplaceDomain` packages and localization assumptions.

**Estimate:** highly dependent on existing support; potentially thousands of lines if Borel's theorem itself must be developed.

**Status:** classical mathematics, not the research obstruction.

### Rank 7: the one-observable physical encoding theorem

The construction in §1 needs spherical-harmonic completeness/decomposition, a uniformly convergent observable series, and a weighted \(h\)-dependent first-discrepancy estimate.

**Estimate:** likely infrastructure-dominated; hundreds of lines only if those ingredients already exist, otherwise much more.

**Status:** a separate mathematical result, not a corollary of the current fixed-test engine.

### Genuinely unresolved work for the fixed-rescaled formulation

* Eliminating arbitrary cokernel compatibility obstructions.
* Proving universal formal or smooth blindness, or finding a globally identifying finite rescaled family.
* Establishing analytic lifting with convergence control in any proposed general construction.

These should not be presented as mere formalization tasks.

---

## Bottom line

* **Literal (A), allowing arbitrary continuous physical observables: false.** A single fractional-homogeneity encoded observable identifies all jets and analytic germs modulo constants.
* **Fixed rescaled observables / ordinary coefficient sequences:** the general full-expansion question is not resolved by the supplied arguments, and I do not supply a resolution here.
* **\(\{q,q^2\}\) and all degree-\(\le2\) monomials:** not globally identifying, even among polynomial analytic losses.
* **(C): yes.** Your existing high-degree kernel pair plus coefficient uniqueness is essentially the complete proof.
* The highest-value immediate formalization is **truncated coefficient noninjectivity**, with the quantifier gap to full blindness stated explicitly.