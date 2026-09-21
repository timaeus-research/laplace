## 1. Mathematics

**A–D are correct**, assuming a finite nonempty spectrum, \(p_i>0\), \(h\ge0\), and \(1-hp_i/2>0\).

- **A:** The double-sum identity has exactly the stated sign and factor \(2\). Comonotonicity makes \((r_i-r_j)(f_i-f_j)\ge0\), including ties; multiplying by \(v_iv_j\ge0\) preserves this. For the mean inequality, only positivity of the two denominator sums is needed, not pointwise strict positivity.
- **B:** Correct for an orthogonal eigenbasis of positive-definite \(P\). The minibatch trace formula needs only the diagonal entries of the transformed covariance; it does **not** assert that the entire minibatch covariance is diagonal.
- **C:** Exactly A with \(v_i=1/p_i\), \(r_i=p_i\), \(f_i=(1-hp_i/2)^{-1}\). The resulting LLC weights are \(v_ir_i=1\).
- **D:** Exactly A with
  \[
  v_i=\frac1{p_i(1-hp_i/2)},\quad r_i=p_i,\quad
  f_i=1+\frac{ht^2}{2}\tilde c_i.
  \]
  Thus \(v_ir_i=(1-hp_i/2)^{-1}\). The common LLC factor \(1/2\) cancels.

**Frobenius is genuinely different.** The trace comparison captures the weighting mechanism, but does not establish E5’s Frobenius comparison. Put \(g_i=(1-hp_i/2)^{-1}-1\). Then
\[
E_F=\sqrt{\frac{\sum_i g_i^2/p_i^2}{\sum_i1/p_i^2}},
\qquad
E_{\rm LLC}=\frac1d\sum_i g_i.
\]
Chebyshev applied to \(g^2\), with weights \(1/p^2\) and reweighting factor \(p^2\), bounds \(E_F\) by the **uniform RMS** of \(g\), not its mean.

Indeed, take \(p=(1,1.1)\), \(h=1.8\). Stability holds, \(g=(9,99)\), and
\[
E_F=\sqrt{\frac{9^2+90^2}{1+(10/11)^2}}\approx66.93
>54=E_{\rm LLC}.
\]
It even exceeds the LLC inflation **factor**, \(55\). So no universal proposed Frobenius bound under these hypotheses.

**Noise hypothesis:** `Monovary c̃ p` is a clear, sufficient interpretation, but stronger than merely “noise concentrated on stiff directions.” Your displayed double-sum condition is exactly the weaker weighted-covariance condition needed. For \(ht^2>0\), it is also necessary for D’s comparison; for \(ht^2=0\), both ratios equal one. Ideally expose a covariance-condition theorem, then derive the readable `Monovary` corollary.

## 2. Lean

- I know of no standard weighted Chebyshev lemma matching A; without checking the actual Mathlib checkout, I would not claim exhaustive absence. The direct double-sum proof is a good, robust route.
- Use `Finset.sum_mul_sum` and distributivity to normalize the sums, then `ring`; `ring` alone will not distribute through finite sums.
- The trichotomy proof is entirely appropriate: `sub_nonpos.mpr` / `sub_nonneg.mpr`, then `mul_nonneg_of_nonpos_of_nonpos` / `mul_nonneg`, followed by the nonnegative weight product. An existing `Monovary` difference-product characterization could shorten this, but verify its exact name and scalar orientation rather than depending on a guessed API.
- Repeating the explicit diagonal inverse verification is fine. Prefer extracting one reusable eigenbasis-inverse lemma if B’s two consequences need it.

## 3. Scope

A+B+C+D is coherent; **~250 lines is plausible but optimistic**, depending on spectral rewriting and denominator normalization.

Both proposed extras are cheap and valuable:
- State the **general Laplace-weight comparison** first; C becomes its specialization.
- Prove the **antivary reversal**, preferably from the same signed double-sum identity or by negating the observable.

Keep Frobenius outside the theorem claims, with the limitation documented.

Vote: A+B+C+D+extras
The core is correct and cohesive, and the general Laplace instance plus antivary reversal add useful coverage with little new machinery.