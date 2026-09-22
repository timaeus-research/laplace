## 1. Correctness and hidden hypotheses

**A and C are correct. B’s formula is correct, but “the localiser drops out” is false.**

Assume real matrices, orthogonal square \(Q\), \(\lambda_i>0\), fixed parameters, \(g\ge0\), and eventually \(t\ge1\), alongside the hypotheses of the landed covariance theorem.

- **A:** Orthogonal invariance gives
  \[
  \|Q\operatorname{diag}(a)Q^\top\|_F^2=\sum_i a_i^2.
  \]
  The stated scaled rate follows from the entrywise order-two expansion, and is equivalent to the unscaled \(K/t^5\) rate.

- **B:** Both scalar identities are correct:
  \[
  \frac1{t\lambda+g}-\frac1{t\lambda}
  =-\frac{g}{t\lambda(t\lambda+g)},
  \]
  \[
  t^2\left(\frac1{t\lambda+g}-\frac1{t\lambda}\right)
       +\frac g{\lambda^2}
  =\frac{g^2}{\lambda^2(t\lambda+g)}
  \le\frac{g^2}{\lambda^3t}.
  \]
  Thus the leading discrepancy from \(H^{-1}/t\) is indeed \(V/t^2\).

  **However, \(V\) still depends on the localiser:**
  \[
  v_i=\frac{\alpha_i^2}{\lambda_i^4}
      -\frac{g x_{0,i}\alpha_i}{\lambda_i^3}
      -\frac g{\lambda_i^2}
      -\frac{\gamma_i}{2\lambda_i^3}.
  \]
  Only the explicit \(+gH^{-2}\) in \(W\) cancels. A decisive check is the purely quadratic case: \(C=S\), so \(W=0\), but \(V=-gH^{-2}\).

- **C:** Correct for positive dimension. Set
  \[
  L=\sum_i\lambda_i^{-2}>0.
  \]
  `[Nonempty (Fin d)]` plus \(\lambda_i>0\) is sufficient. In dimension zero, the displayed squared formulas reduce to zero under Lean’s totalized division, but the usual interpretation as a relative error is undefined. **State C with nonemptiness rather than exploiting \(0/0=0\).**

One further correction: A’s informal **multiplicative** \((1+o(1))\) norm formulation requires \(W\ne0\). It is not equivalent when \(W=0\).

## 2. Interpretation against \(C=S+O(S^2)\)

The squared Frobenius statement is an excellent invariant, Lean-friendly quantitative version. It measures the remainder without suggesting a Loewner-order inequality or an identity proportional to the matrix \(S^2\).

The proposed **additive** norm wording is valid:
\[
\|C-S\|_F=\frac{\|W\|_F}{t^2}+O(t^{-3}),
\qquad
\frac{\|C-S\|_F}{\|S\|_F}
=\frac{\|W\|_F}{\|H^{-1}\|_F}\frac1t+O(t^{-2}).
\]
These remain valid when \(W=0\). Derive them from the **matrix remainder bound and reverse triangle inequality**, not merely by taking square roots of the squared asymptotic: when the leading coefficient vanishes, that loses the desired rate.

B is worth stating, with this wording:

> Changing the reference covariance from the Gaussian-prior resolvent to \(H^{-1}/t\) changes the leading discrepancy coefficient from \(W=V+gH^{-2}\) to \(V\). The explicit resolvent correction cancels; localiser dependence in \(V\) remains.

## 3. Lean route

### Square transport

Prefer one generic scalar lemma, then finite-sum transport. Put \(y=t^2x\). For \(K\ge0\), \(t\ge1\),
\[
|y-w|\le K/t,\qquad |y|\le |w|+K.
\]
Hence
\[
|y^2-w^2|
=|y-w|\,|y+w|
\le \frac Kt(2|w|+K).
\]
Finally normalize \((t^2x)^2=t^4x^2\) with `ring`.

This avoids expanding powers inside inequalities. Use `abs_mul`, the triangle inequality, and monotone multiplication; reserve `ring` for algebra and `positivity` for denominator conditions. If the existing `prod_rate` already handles scaled order-one rates, applying it to \(y\cdot y\) is even cheaper.

For invariance, reuse the landed trace lemmas:
\[
\sum_{jk}A_{jk}^2
=\operatorname{tr}(AA^\top)
=\sum_i (Q^\top A Q)_{ii}a_i
=\sum_i a_i^2,
\quad A=Q\operatorname{diag}(a)Q^\top.
\]
This is precisely the combination of `sum_sum_eq_trace`, symmetry, `trace_mul_conj_diagonal`, and `conj_conj`; avoid a fresh fourfold-sum proof.

### Ratio transport

Prove a reusable lemma. If
\[
|a(t)-a_0|\le k_a/t,\qquad |b(t)-L|\le k_b/t,\qquad L>0,
\]
enlarge the threshold so \(b(t)\ge L/2\). Then
\[
\left|\frac{a(t)}{b(t)}-\frac{a_0}{L}\right|
\le
\frac1t\left(\frac{2k_a}{L}
+\frac{2|a_0|k_b}{L^2}\right).
\]
A sufficient additional threshold is \(t\ge2k_b/L\), with nonnegative constants.

Apply this with
\[
a(t)=t^4\|C-S\|_F^2,\quad
b(t)=t^2\|S\|_F^2,\quad
a_0=\sum_iw_i^2.
\]
Use `field_simp` only after recording \(t\ne0\), \(L\ne0\), and \(b(t)\ne0\).

**Practical pitfall:** entrywise existential thresholds/constants must be uniformized over the finite index set before summing. Do not assume the covariance theorem already supplies one common pair.

## 4. Additional targets and vote

**Best cheap corollary this tide:** if \(\sum_iw_i^2>0\), obtain eventual two-sided bounds
\[
\frac{\sum_iw_i^2}{2t^4}
\le \|C-S\|_F^2
\le \frac{3\sum_iw_i^2}{2t^4}.
\]
This establishes sharp \(t^{-2}\) Frobenius order, not merely an upper bound. When \(W=0\), the original entrywise remainder instead yields \(\|C-S\|_F^2=O(t^{-6})\).

**Best next substantial target:** the derivative discrepancy, provided tides 80/81 already give the independent entrywise expansion
\[
-\partial_tC=H^{-1}/t^2+2V/t^3+O(t^{-4}).
\]
Then the same square-transport machinery gives
\[
\left|t^6\|-\partial_tC-H^{-1}/t^2\|_F^2
      -4\sum_i v_i^2\right|\le K/t.
\]
**Do not obtain that expansion by differentiating an \(O(t^{-3})\) remainder.** If the required derivative rate is not already landed, prefer the mean-discrepancy analogue.

The weighted trace is cheap, but its leading coefficient \(\sum_i\lambda_iw_i\) has **no universal sign** under the stated hypotheses; a sign theorem needs additional coefficient assumptions.

### Vote: **A+B+C**

Commit in that order, with A’s reusable square/invariance lemmas and C’s generic ratio lemma. Rename B to **“Changing the reference covariance”**, not “the localiser drops out.” If proof engineering overruns, preserve A+B and defer C rather than weakening the quantitative statements.