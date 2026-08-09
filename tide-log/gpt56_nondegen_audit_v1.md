## 1. Priority among A–E

There are two useful orderings: **implementation order** and **logical importance for the full theorem**.

### Recommended implementation order

1. **(B) Data bridge and theorem-shaped inverse wrapper**
2. **(D) Location recovery**
3. **(C) Analytic germ corollary**
4. **(A) Arbitrary-order forward Laplace expansion**
5. **(E) Explicit coefficient-level triangular reconstruction**

This gets the cheap, theorem-visible gains first. However, in terms of what is logically missing from the complete nondegenerate Theorem 3.1, **(A) is more important than (C)**. Thus the strategic order is:

\[
\boxed{B \;>\; D \;>\; A \;>\; C \;>\; E.}
\]

A practical project plan would do the small \(B,D,C\) tides first, then treat \(A\) as the remaining major project.

### What each item actually completes

- **(B)** changes the current recovery results from internal rate hypotheses into the note’s own “same full asymptotic expansion” language. This is the highest-value immediate target.
- **(D)** is necessary because the current multivariate recovery is anchored at a known minimum. The literal theorem also says that the data determine \(w^*\).
- **(A)** is indispensable for the converse “the jet determines the expansion coefficients,” and hence for the claimed bijection onto the image.
- **(C)** completes the analytic corollary once inverse jet recovery is available, but it does not replace the forward half.
- **(E)** gives a constructive coefficient-by-coefficient decoder, but it is not needed for injectivity or for the bijection onto the image once (A) and (B) exist.

Consequently:

> **(B)+(C) is not enough to say that Theorem 3.1 and Corollary 3.2 have been formalized.**

It gives a strong anchored inverse theorem and its analytic consequence. It still omits:

1. recovery of the unknown location \(w^*\), unless (D) is added;
2. existence of the full expansion and dependence of its coefficients on the jet, i.e. (A).

A fair milestone claim after \(B+C\) would be:

> Equality modulo superpolynomial errors of the localized moment family determines the full positive-order smooth jet at a fixed nondegenerate minimum; for analytic losses, it determines the analytic germ modulo a constant.

After \(B+C+D\), it becomes the full **inverse/recovery half** of the note’s statement.

### One packaging target that is easy to overlook

The literal wrapper should assemble all three inverse stages:

1. first moments recover and align \(w^*\);
2. second moments/covariances recover the Hessian;
3. the higher-order theorem recovers \(D^kL(w^*)\) inductively.

The current higher-order package assumes the lower-order/shared quadratic data in some form, so (B) is not merely one substitution lemma: the only genuinely new asymptotic argument is the substitution lemma, but there is also theorem-level plumbing through location, covariance, Hessian, and the higher-order induction.

---

## 2. SuperPoly as the data bridge

### Is it faithful?

Yes, for the **recovery direction** it is faithful and sufficient.

If the note defines “same asymptotic expansion” by saying that the difference is smaller than every inverse power,

\[
f_1(t)-f_2(t)=o(t^{-N})\qquad\text{for every }N,
\]

then `SuperPoly` is exactly the appropriate quotient relation on moment functions.

There is one logical qualification:

- If full asymptotic expansions have already been proved to exist, equality of all coefficients is equivalent to superpolynomial difference.
- Without an existence theorem, `SuperPoly` equality should be described as **equality modulo flat/superpolynomial errors**, rather than independently as equality of two already-existing coefficient families.

For inverse recovery this distinction is harmless: the proof only uses the superpolynomial consequence.

### The substitution argument

Let

\[
g(q)=f(q^{-2}), \qquad q\to0^+.
\]

Since \(q^{-2}\to+\infty\), composition gives

\[
f(t)=o(t^{-N})
\quad\Longrightarrow\quad
g(q)=o(q^{2N}).
\]

To obtain \(g=o(q^r)\), choose \(N\) with \(2N\ge r\). Then

\[
\frac{g(q)}{q^r}
=
\frac{g(q)}{q^{2N}}\,q^{2N-r}\longrightarrow 0.
\]

Thus for every fixed \(k\),

\[
g(q)=o(q^{k-2})
\]

by taking \(2N\ge k-2\).

This also survives any fixed polynomial rescaling. For example, if the recovery theorem uses \(q^{-m}g(q)\), choose

\[
2N\ge m+k-2.
\]

That is important because the raw normalized moments and the rescaled moment functions used by the induction may differ by powers of \(q\).

### Lean/filter traps

The main technical points are:

1. **Use the one-sided filter**
   \[
   \mathcal N[>]0
   \]
   or `nhdsWithin 0 (Set.Ioi 0)`. This avoids irrelevant sign and real-power issues.

2. Prove explicitly that
   ```lean
   Tendsto (fun q : ℝ => q⁻²) (𝓝[>] 0) atTop
   ```
   in the appropriate notation.

3. Apply little-\(o\) composition along that map.

4. Add a closure lemma saying that a superpolynomially small function remains sufficiently small after multiplication by any fixed power of \(q^{-1}\).

5. If the Hessian bridge uses covariance rather than raw second moments, derive flatness of covariance differences from flatness of the individual moments. This needs boundedness/convergence of the lower moments because covariance contains products:
   \[
   \operatorname{Cov}(X,Y)=E[XY]-E[X]E[Y].
   \]

6. Ensure the observable family is expressed in fixed/global coordinates until the two minima have been shown equal. Otherwise “moments centered at \(w_1^*\)” and “moments centered at \(w_2^*\)” are not directly the same data.

There is no exponent obstruction from using only integer \(N\) in `SuperPoly`: arbitrary integer inverse powers dominate every required integer or half-integer asymptotic order.

---

## 3. Minimal honest forward-direction theorem

A fixed leading-order or first-correction result is not enough for the stated core. It would add more examples of the already-merged forward fragments, but it would not establish the “full expansion” or the jet-to-coefficient map.

The right minimal target is an **arbitrary finite-order theorem**, from which the smooth all-orders statement is an immediate wrapper.

### Suggested theorem shape

Work with:

- a localized integral near \(w^*\);
- \(DL(w^*)=0\);
- positive-definite Hessian \(H=D^2L(w^*)\);
- a cutoff supported in a neighborhood where a uniform quadratic lower bound holds;
- \(q=t^{-1/2}\);
- centered polynomial observables, initially monomials.

For every multi-index \(\alpha\) and every \(N\), prove the existence of coefficients \(c_{\alpha,0},\dots,c_{\alpha,N}\) such that

\[
q^{-|\alpha|}
\left\langle (w-w^*)^\alpha\right\rangle_{q^{-2}}
=
\sum_{j=0}^{N}c_{\alpha,j}q^j+o(q^N)
\qquad(q\to0^+).
\]

With one additional derivative and stronger remainder bookkeeping, one can instead state

\[
q^{-|\alpha|}
\left\langle (w-w^*)^\alpha\right\rangle_{q^{-2}}
=
\sum_{j=0}^{N}c_{\alpha,j}q^j+O(q^{N+1}).
\]

The \(o(q^N)\) version is probably the cleaner first target. Quantifying over all \(N\) for smooth \(L\) gives the full Poincaré expansion.

The coefficient theorem should say at least:

> \(c_{\alpha,j}\) depends only on \(H^{-1}\) and the derivatives
> \[
> D^3L(w^*),\ldots,D^{j+2}L(w^*).
> \]

Equivalently, losses with equal jets through order \(j+2\) have equal coefficients through order \(j\).

That dependence statement is enough for the forward half of Theorem 3.1. It is not necessary initially to expose a polished closed formula for every coefficient.

### Natural coefficient construction

After \(w=w^*+qz\),

\[
q^{-2}\bigl(L(w^*+qz)-L(w^*)\bigr)
=
\frac12 H[z,z]
+\sum_{s\ge1}q^sV_s(z),
\]

where

\[
V_s(z)=\frac{1}{(s+2)!}D^{s+2}L(w^*)[z^{s+2}].
\]

Then truncate

\[
\exp\left(-\sum_{s\ge1}q^sV_s(z)\right)
\]

to order \(N\). Its coefficient at \(q^j\) is a finite universal polynomial in \(V_1,\ldots,V_j\). Integrating these polynomial coefficients against the Gaussian with Hessian \(H\) gives expansions of the unnormalized numerator and denominator. The normalized coefficients are then obtained by formal division.

This construction directly proves “universal polynomial in the finite jet” without requiring the inverse triangular argument.

### Realistic staging into tides

1. **Rescaling and localization**
   - change variables \(w=w^*+qz\);
   - prove Gaussian domination from the quadratic lower bound;
   - show the contribution outside a fixed small neighborhood is exponentially, hence superpolynomially, small.

2. **Finite Taylor expansion of the exponent**
   - package \(V_1,\ldots,V_N\);
   - prove a controlled remainder after exponentiation;
   - establish an integrable Gaussian-polynomial majorant.

3. **Unnormalized numerator expansion**
   - prove the arbitrary-\(N\) expansion for
     \[
     \int z^\alpha e^{-\frac12H[z,z]}e^{-\sum q^sV_s(z)}\,dz.
     \]

4. **Denominator and quotient**
   - apply the numerator theorem with \(P=1\);
   - prove the denominator tends to a positive Gaussian integral;
   - formalize finite-order division of asymptotic expansions.

5. **Coefficient/jet packaging**
   - state that the order-\(j\) coefficient uses only derivatives through \(j+2\);
   - prove compatibility as \(N\) varies;
   - derive the smooth all-orders expansion.

6. **Return to \(t\) and connect to `Phi`**
   - substitute \(q=t^{-1/2}\);
   - package all monomial observables into the expansion family;
   - combine with (B) for the bijection-onto-image statement.

### Scope recommendation

Do not spend a tide merely on another fixed correction order unless it is explicitly a reusable prototype for stages 2–4. Given the user’s stated concern, the high-value theorem is:

> **For arbitrary \(N\), a finite expansion exists and its coefficients depend only on the finite jet.**

That is the smallest honest theorem that scales to “all orders.” The full explicit combinatorial formula can remain abstract or be postponed.

---

## 4. Cheapest recovery of \(w^*\)

The cheapest statement is the convergence of the normalized first moment:

\[
\frac{\int w\,e^{-tL(w)}\chi(w)\,dw}
     {\int e^{-tL(w)}\chi(w)\,dw}
\longrightarrow w^*.
\]

Coordinatewise,

\[
\langle w_i\rangle_t\longrightarrow w_i^*.
\]

No argmax or local-mass reconstruction is needed.

Given the already-merged anchored result

\[
q^{-1}E_q[w_i]\longrightarrow0
\]

at a minimum placed at \(0\), the translated statement is immediate:

\[
E_q[w_i-w_i^*]=o(q),
\]

hence

\[
E_q[w_i]\longrightarrow w_i^*.
\]

For two losses with minima \(w_1^*,w_2^*\), if their first-moment functions differ superpolynomially, then in particular their difference tends to zero. Taking limits gives

\[
w_1^*=w_2^*.
\]

This is worth a small tide because it:

- closes an explicit clause of Theorem 3.1;
- removes the “minimum fixed at \(0\)” mismatch;
- permits the subsequent Hessian and higher-jet arguments to be placed in common centered coordinates.

The observable family must contain the uncentered coordinate functions \(w\mapsto w_i\), or equivalent affine observables. If the supplied data consist only of moments centered at an already-known \(w^*\), then location recovery is circular and must be added separately.

## Bottom line

The best immediate package is:

1. **(B)** SuperPoly-to-\(q\)-rate bridge and full inverse wrapper;
2. **(D)** first-moment location recovery;
3. **(C)** analytic germ modulo constants.

That completes the literal inverse theorem and analytic consequence. The remaining substantive half of the main theorem is **(A)**, best formulated as an arbitrary finite-order localized Laplace expansion with coefficients depending on the finite jet. **(E)** should remain last unless a constructive coefficient decoder is itself a desired deliverable.