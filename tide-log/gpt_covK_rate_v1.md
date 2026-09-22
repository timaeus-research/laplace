## 1. Constants and proof organisation

**All six constants in A are correct.** Write \(M_j(t)=\langle x^j\rangle\), and introduce the normalized moments
\[
Z_1=tM_1,\quad Z_2=tM_2,\quad Z_3=t^2M_3,\quad
Z_4=t^2M_4,\quad Z_5=t^3M_5,\quad Z_6=t^3M_6.
\]
The supplied sharp rates give \(Z_j=a_j+O(1/t)\), with
\[
(a_1,a_2,a_3,a_4,a_5,a_6)
=
\left(
-\frac{\alpha}{2\lambda^2},
\frac1\lambda,
-\frac{5\alpha}{2\lambda^3},
\frac3{\lambda^2},
-\frac{35\alpha}{2\lambda^4},
\frac{15}{\lambda^3}
\right).
\]

Using `gibbsCov_pow_pow`, the bookkeeping is:

| Pair | Exact expression for \(t^2\operatorname{Cov}\) | Constant |
|---|---|---|
| \((2,2)\) | \(Z_4-Z_2^2\) | \(3/\lambda^2-1/\lambda^2=2/\lambda^2\) |
| \((3,2)\) | \((Z_5-Z_3Z_2)/t\) | \(0\) |
| \((4,2)\) | \((Z_6-Z_4Z_2)/t\) | \(0\) |
| \((2,1)\) | \(Z_3-Z_2Z_1\) | \(-5\alpha/(2\lambda^3)+\alpha/(2\lambda^3)=-2\alpha/\lambda^3\) |
| \((3,1)\) | \(Z_4-Z_3Z_1/t\) | \(3/\lambda^2\) |
| \((4,1)\) | \((Z_5-Z_4Z_1)/t\) | \(0\) |

In particular, the energy–quadratic and energy–linear constants are
\[
\frac{\lambda}{2}\frac{2}{\lambda^2}=\frac1\lambda,
\]
and
\[
\frac{\lambda}{2}\left(-\frac{2\alpha}{\lambda^3}\right)
+\frac{\alpha}{6}\frac3{\lambda^2}
=-\frac{\alpha}{2\lambda^2}.
\]
Thus the probe \((B/2)x^2+bx\) has precisely
\[
C=\frac{B}{2\lambda}-\frac{b\alpha}{2\lambda^2}.
\]

### Recommended organisation

Use A, with a small collection of **pointwise quantitative algebra lemmas**:

* addition and scalar multiplication of rated quantities;
* the proposed product lemma;
* a rated-to-bounded lemma:
  \[
  |X-a|\le K/t,\quad t\ge1,\quad K\ge0
  \Longrightarrow |X|\le |a|+K;
  \]
* bounded-over-\(t\):
  \[
  |X|\le D,\quad t>0\Longrightarrow |X/t|\le D/t.
  \]

Your product constant is correct:
\[
|XY-ab|
\le \frac{K|b|+K'|a|+KK'}{t}.
\]
Expand using
\[
XY-ab=(X-a)b+a(Y-b)+(X-a)(Y-b),
\]
then use \(t^{-2}\le t^{-1}\).

For the expressions already divided by \(t\), **boundedness suffices**. There is no need to calculate their first-order coefficients.

Expanding \(\langle\ell\psi\rangle-\langle\ell\rangle\langle\psi\rangle\) directly is valid, but merely groups the same products differently. A is more reusable and localizes the power bookkeeping. **The even-moment order-two theorem is not needed** for this target.

## 2. Lean bookkeeping

The main correction is that **`ring` does not use `t ≠ 0` to cancel denominators automatically**. Even after rewriting division as multiplication by an inverse, cancellation still needs an explicit step.

For your example, a genuinely `field_simp`-free proof is:

```lean
example (t a b : ℝ) (ht : t ≠ 0) :
    t ^ 2 * a * b = ((t ^ 2 * a) * (t * b)) / t := by
  apply (eq_div_iff ht).2
  ring
```

Recommended precautions:

* Extract a common threshold \(T\ge1\), then establish `0 < t` and `t ≠ 0` once.
* Keep normalization identities separate from analytic inequalities. First rewrite covariances into the table above; then apply rate/boundedness lemmas.
* Instantiate the moment theorems at concrete natural indices early. Normalize factorial constants and casts separately from the covariance algebra.
* For division inequalities, use positivity explicitly. Converting the scaled error into \(K/t^3\) uses \(t^2>0\), not merely \(t\ne0\).
* Discharge polynomial integrability before invoking covariance linearity. In Lean, integral linearity should not be treated as an unconditional algebraic identity.

A convenient interface for each pair theorem is exactly
\[
\exists K,T,\quad 0\le K\ \land\ 1\le T\ \land\
\forall t\ge T,\quad |t^2\operatorname{Cov}-c|\le K/t.
\]
The algebra helpers themselves can remain pointwise, avoiding repeated existential/filter manipulation.

## 3. The rotated headline and relative error

**Yes: the rotated \(K/t^3\) absolute-error statement is the right unconditional headline.** It connects directly to the note’s formula:
\[
\left|\operatorname{Cov}[L\circ A,\psi]
-\operatorname{covKFormula}(t,H,T,B,b)\right|
\le \frac K{t^3}.
\]

The scaled version should also be retained:
\[
|t^2\operatorname{Cov}[L\circ A,\psi]-C_d|\le K/t,
\]
where
\[
C_d=\sum_i\left(
\frac{(Q^\top BQ)_{ii}}{2\lambda_i}
-\frac{(Q^\top b)_i\alpha_i}{2\lambda_i^2}
\right).
\]

The remaining quantitative steps in C are straightforward:

* Finite sums: choose a common threshold and sum error constants.
* Off-diagonal pairs: if
  \[
  |\langle x\rangle_j|\le A_j/t,\qquad
  |t^2\operatorname{Cov}_i[\ell_i,x]|\le D_i,
  \]
  then the exact pair identity yields
  \[
  |t^2\operatorname{Cov}_L[L,u_i u_j]|
  \le \frac{A_jD_i+A_iD_j}{t}.
  \]
* Full quadratic probes: weight these bounds by \(|B_{ij}|/2\), retaining the original ordered double sum. No symmetry assumption on \(B\) is needed.
* Rotation: use the existing exact probe/Gibbs transport identities and `covKFormula_rot`; limits alone would not transfer a rate.

The relative corollary is worth stating, but **only with \(C_d\ne0\)**:
\[
\left|
\frac{\operatorname{Cov}[L\circ A,\psi]}
     {\operatorname{covKFormula}(t,H,T,B,b)}-1
\right|
\le \frac{K}{|C_d|\,t}.
\]
When \(C_d=0\), the absolute theorem instead says the covariance is \(O(t^{-3})\); relative error against the zero prediction is undefined.

Also, “relative error proportional to \(1/t\)” should be read here as **an \(O(1/t)\) upper bound**, not a nonzero asymptotic coefficient or a two-sided \(\Theta(1/t)\) claim.

## 4. Scope and vote

I would stage the implementation as:

1. quantitative algebra helpers and A;
2. B, including the absolute \(K/t^3\) and nonzero-constant relative corollaries;
3. C, culminating in the rotated formula.

C introduces no new asymptotic analysis: its ingredients are boundedness, finite sums, and exact identities already in the seabed. It also delivers the statement in the note’s actual frame, rather than leaving that connection implicit.

**Vote: A+B+C as one tide, staged internally, with the rotated absolute-error theorem as the headline and the relative theorem as a conditional corollary.**