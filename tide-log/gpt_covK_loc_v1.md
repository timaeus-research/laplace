## 1. Differentiating the inverse: both routes are viable

**The `Ring.inverse` route is viable and is the shortest conceptual proof. B(iv) is the more instance-robust fallback, not necessarily the least painful first choice.**

### Recommended first attempt: the ring-inverse derivative

Work in a section with a **coherent operator-norm instance hierarchy**, using the local instances
```lean
attribute [local instance]
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
```
The intended proof is:

1. Set `A s := s • H + γ • 1`.
2. Convert `IsUnit (A t).det` into `IsUnit (A t)`, and obtain a unit representing `A t`.
3. Apply `hasFDerivAt_ringInverse` at that unit.
4. Compose with
   ```lean
   HasDerivAt A H t
   ```
5. Rewrite `Ring.inverse` as matrix inverse using `Matrix.nonsing_inv_eq_ringInverse`.

The resulting derivative is
\[
S'(t)=-S(t)HS(t).
\]

**Yes, completeness supplies `HasSummableGeomSeries` for this Banach-ring setup.** Finite real matrices are complete in the operator norm; there is no additional analytic hypothesis to prove about the resolvent. In the checked-out Mathlib version, I would immediately test synthesis of:
```lean
CompleteSpace (Matrix (Fin d) (Fin d) ℝ)
HasSummableGeomSeries (Matrix (Fin d) (Fin d) ℝ)
```
after selecting the operator-norm instances. The engineering issue is instance coherence, not the existence of geometric-series summability.

There is an important qualification about extracting entries:

> Do not assume that `hasDerivAt_pi` will apply directly to a derivative established under the operator norm.

Its usual function-space formulation uses the Pi normed-space instances. Instead, compose the matrix derivative with the continuous linear map
\[
M\longmapsto M_{ij}.
\]
This is continuous under the operator norm and can also be obtained from the corresponding linear map by finite dimensionality. Exporting an **entrywise derivative theorem** from this local section avoids exposing the norm choices downstream.

### B(iv): a very reasonable fallback

Your elementary route is sound:

\[
S(s)-S(t)
=S(s)(A(t)-A(s))S(t)
=-(s-t)\,S(s)HS(t).
\]

Continuity of the determinant gives eventual invertibility near `t`; the adjugate formula gives entrywise continuity of `S`. On a sufficiently small punctured neighborhood,
\[
\frac{S(s)_{ij}-S(t)_{ij}}{s-t}
=-\bigl(S(s)HS(t)\bigr)_{ij},
\]
whose limit is the required derivative.

The main Lean work is:

- carrying eventual invertibility into the punctured neighborhood;
- cancelling `s - t` using `s ≠ t`;
- expressing matrix-product continuity through finite sums.

This route avoids selecting a matrix norm altogether. Over `ℝ`, reducing `IsUnit (A t).det` to `(A t).det ≠ 0` also makes the continuity arguments more standard.

### Differentiating determinant and adjugate directly

This is possible, but I would not choose it. Differentiating their finite polynomial expressions is straightforward in principle; identifying the resulting quotient-rule expression with `−S * H * S` is the unattractive part.

A better variant, if needed, is:

1. prove differentiability of the inverse locally through the adjugate formula;
2. differentiate `A(s) * S(s) = 1`;
3. solve `H * S + A * S' = 0` for `S'`.

Even that generally involves more infrastructure than either preferred route.

## 2. For C: use a hybrid, with entrywise assembly as the default

For this target, I recommend:

> **Prove the inverse derivative once using the operator norm, export its entrywise version, and assemble C using finite-sum derivative lemmas.**

This separates the genuinely analytic result from the index algebra and avoids carrying matrix-norm instances through the rest of the development.

A warning about the alternative: the entrywise sup norm and the operator norm are not interchangeable Lean instances. In particular, the entrywise maximum norm does not generally satisfy the normed-ring inequality with constant one. Do not independently activate a conflicting `Matrix.normedAddCommGroup` while using the operator-norm ring structure.

An entirely matrix-valued proof is also reasonable if you expect to reuse its infrastructure:

- `S ↦ trace (B * S)` is linear;
- `S ↦ contractT T S` is linear for fixed `T`;
- entry evaluation and fixed-vector dot products are linear;
- finite dimensionality gives continuity of these linear maps.

But **`mulVec` is bilinear, not jointly linear**. In
\[
S(s)\bigl(s\,\operatorname{contractT}(T,S(s))\bigr),
\]
both inputs vary. You still need a bilinear product rule, either packaged as continuous bilinear maps or proved through sums.

For one scalar theorem, finite sums are usually the smaller investment. I would introduce helper derivative lemmas for `contractT`, `mulVec`, and dot products rather than unfold everything in one proof.

## 3. The algebra is correct; the assumptions can be sharpened

Write
\[
S=(tH+\gamma I)^{-1},\qquad
R=SHS,\qquad
C=T:S,\qquad D=T:R.
\]
At an invertible point,
\[
S'=-R,\qquad C'=-D,\qquad (tC)'=C-tD.
\]

For
\[
F(t)=\frac12\operatorname{tr}(BS)-\frac12 b^{\mathsf T}S(tC),
\]
the trace contribution is
\[
-\frac{d}{dt}\frac12\operatorname{tr}(BS)
=\frac12\operatorname{tr}(BSHS)
=\frac12\operatorname{tr}(HSBS).
\]
The last step uses cyclicity, not symmetry.

The cubic contribution satisfies
\[
\frac{d}{dt}\bigl[b^{\mathsf T}S(tC)\bigr]
=-t\,b^{\mathsf T}RC+b^{\mathsf T}SC-t\,b^{\mathsf T}SD.
\]
Thus
\[
-F'(t)
=\frac12\operatorname{tr}(HSBS)
+\frac12b^{\mathsf T}SC
-\frac t2b^{\mathsf T}SHSC
-\frac t2b^{\mathsf T}SD.
\]
When `S` is symmetric, \(b^{\mathsf T}S=(Sb)^{\mathsf T}\), giving exactly the displayed formula.

### Hypotheses

For the proposed theorem, these suffice:

- finite real matrices;
- `IsUnit (t • H + γ • 1).det`;
- symmetry of `H`.

There are **no sign assumptions on `t` or `γ`**, and **no requirement that `H` itself be invertible**. Nor are symmetry of `B`, tensor symmetries of `T`, or positive definiteness needed for this algebraic identity.

More precisely:

- Local invertibility is the condition used by the inverse-derivative argument.
- Symmetry of `H` is a convenient sufficient condition for symmetry of `S`.
- **Only symmetry of `S(t)` is needed for the final displayed rewriting at that point.** Symmetry of `H` is not intrinsically necessary.

Without symmetry, the derivative identity still holds, but the second and fourth displayed terms use \(S^{\mathsf T}b\), not \(Sb\). This suggests a useful separation: prove the derivative formula first in its `bᵀS` form without symmetry, then derive `covKFormulaLoc` under symmetry.

Finally, `covKFormulaLoc_eq_neg_deriv` follows directly from the `HasDerivAt` theorem’s derivative equality and sign simplification.

## 4. Scope and vote

**Vote: A + B + C, with flexibility about B’s implementation.**

- **A:** Define the local quantities and prove the zero-`γ` compatibility lemma. This is independent of the analytic route and should require no new symmetry hypothesis.
- **B:** Target the reusable resolvent derivative. Try `Ring.inverse` first; retain the elementary resolvent/slope argument as the fallback.
- **C:** Assemble the scalar derivative, perform the symmetry and trace rewrites, and extract the negative-derivative identity.

I would **not require all of B(i)–(iv)** if the ring-inverse proof succeeds: eventual invertibility and adjugate continuity are supporting lemmas for the elementary implementation, not necessary deliverables for C.

**Final vote: yes—A plus a reusable inverse-along-a-line derivative plus C is a coherent, worthwhile target. Prefer the ring-inverse/entrywise hybrid; do not spend the tide formalizing both inverse-derivative routes.**