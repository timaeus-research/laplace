(1) **Correctness**

- **A:** correct.
- **C:** correct.
- **B:** also correct **mathematically**:
  \[
  \langle x^{2m}y^{2n}\rangle_t
  = \Big(\frac{24}{t}\Big)^{(m+n)/2}
    \frac{\Gamma((2m+1)/4)\Gamma((2n+1)/4)}{\Gamma(1/4)^2},
  \qquad t>0.
  \]

  The only real caveat is **Lean syntax / coercions**, not the formula itself.

  In Lean, avoid anything that looks like nat-division in the exponent:
  - **bad:** `((m + n) / 2 : ℝ)` if `/` happens in `ℕ` first,
  - **good:** `(((m + n : ℕ) : ℝ) / 2)` or `((m : ℝ) + (n : ℝ)) / 2`.

  Also, because the exponent may be half-integral when `m+n` is odd, this should be via **`Real.rpow`**, not nat `^`.

  Practically, the cleanest Lean statement is often to **leave it factored**:
  \[
  \Big(\frac{24}{t}\Big)^{m/2}\Big(\frac{24}{t}\Big)^{n/2}
  \]
  with real exponents, and only combine with `Real.rpow_add` later if desired.

---

(2) **Minimal good Tide target**

**Candidate A**.

Why:
- It is only a small step beyond the existing `cov_affine_semiDegenerate`.
- It gives the most useful downstream interface immediately.
- It avoids the extra exponent/cast bookkeeping of B.
- It subsumes C conceptually: C is the moment table you prove on the way to A.

If you wanted the **absolute smallest** landing, C is smaller; but as a “good Tide target” that feels finished and useful, **A is the better choice**.

---

(3) **Better nearby candidates / factorings**

Yes: two lightweight extractions seem worth it.

1. **Generic covariance algebra for `gibbsCov`**
   Pull out lemmas like:
   - bilinearity in each argument,
   - symmetry,
   - constants have zero covariance,
   - affine-shift invariance.

   This is worthwhile: it removes repeated affine-expansion boilerplate from both `SemiDegenerate` and future 2D files.

2. **Generic separable/additive-potential factorisation**
   For potentials of the form
   \[
   L(x,y)=U(x)+V(y),
   \]
   prove once:
   - partition function factorises,
   - expectations of separable observables factorise:
     \[
     \langle f(x)g(y)\rangle = \langle f(x)\rangle_U \langle g(y)\rangle_V.
     \]

   That abstraction is very close to your current seabed and covers both:
   - semidegenerate: \(U(x)=x^4/24,\; V(y)=\lambda y^2/2\),
   - pure quartic: \(U=V=x^4/24\).

If you only extract **one** thing first, I’d do the **covariance algebra lemmas**. If you extract **two**, add the **separable-potential factorisation**. Once that exists, **B becomes almost free**.

A smaller additional theorem that may also be nice is a generic “affine covariance from coordinate covariance matrix” lemma in 2D:
\[
\operatorname{Cov}(a\cdot z + c,\; b\cdot z + d)=a^\top \Sigma b.
\]
But bilinearity + symmetry already gets you most of that.

**I back Candidate A.**