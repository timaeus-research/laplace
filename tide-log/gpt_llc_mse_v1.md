## 1. Mathematics

**A–D are correct**, with the usual seabed assumptions: zero initialization, the prescribed Gaussian innovations and independence, and **\(C,N>0\)**.

- **A:** Correct under a probability measure and integrability of \(X,X^2\).
- **Mean:** Correct:
  \[
  E\widehat\Lambda=\frac12\sum_i\frac{1-R_{2i}/N}{1-hp_i/2}
  =\Lambda_h-\mathrm{shortfall}.
  \]
  The exponent \(2(b+1+k)\) matches observations starting at time \(b+1\).
- **C signs:** Correct:
  \[
  E\widehat\Lambda-d/2=\mathrm{inflation}-\mathrm{shortfall}.
  \]
  Since \(0\le\mathrm{shortfall}\le\mathrm{shortfall}_{bd}\) and inflation is nonnegative, its absolute value is bounded by their stated sum.
- **D:** Correct. For \(a\ge0\),
  \[
  \sqrt{a+b^2}\le\sqrt a+|b|.
  \]
  Apply this after C’s upper bound; the envelope is nonnegative.
- **Hypotheses:** Separate exact identities from bounds. Exact B/C need only the mean theorem’s hypotheses and square integrability—not \(hp_i\le1\). Use the stable regime \(0<hp_i<2\) where appropriate. For bounded B/C and D, **\(0<hp_i\le1\)** is the right common hypothesis for reusing the existing envelope theorem. Do not implicitly claim that theorem already covers negative \(\rho_i\).

## 2. User-facing target

**D, targeting \(d/2\), is the best headline; C is its exact foundation; B is a useful diagnostic.** Give a relative version for \(d>0\):
\[
\frac{\sqrt{E(\widehat\Lambda-d/2)^2}}{d/2}
\le
\frac{2\sqrt{\mathrm{envelope}}}{d}
+\frac1d\sum_i\frac{hp_i/2}{1-hp_i/2}
+\frac1{dN}\sum_i
\frac{\rho_i^{2(b+1)}}{(1-\rho_i^2)(1-hp_i/2)}.
\]

Keep this spectral form primary, with a spectrum-free corollary. Under
\(0<hp_{\min}\le hp_i\le hp_{\max}\le1\), put \(r=1-hp_{\min}\). The last two terms are bounded by
\[
\frac{hp_{\max}/2}{1-hp_{\max}/2},
\qquad
\frac{r^{2(b+1)}}{N(1-r^2)(1-hp_{\min}/2)}.
\]
**The burn-in bound is valid, but requires coupled monotonicity**, not separate denominator comparisons: rewrite its summand as
\[
\frac{2\rho^{2b}}{1-\rho}\left(\frac{\rho}{1+\rho}\right)^2,
\]
which is increasing on \([0,1)\).

Two important qualifications:

- Relative RMSE is not a guarantee that every realization is within 2%; a probability statement requires a tail bound.
- \(hp_{\max}=0.2\) gives a worst-case relative inflation bound of **\(1/9\approx11.1\%\)**, not 2%. The observed 2% requires the actual spectrum or sharper assumptions.

## 3. Lean

- **A:** Prove directly unless an immediately applicable variance/bias identity is already imported. Expand the square, establish integrability of each term, use integral linearity and the probability-measure constant integral, then `ring`. This avoids dependence on the precise Mathlib variance API.
- **Square root:** Square-root subadditivity plus \(\sqrt{b^2}=|b|\) is shortest. Alternatively, use the lemma class characterizing \(\sqrt{x}\le y\) by \(0\le y\) and \(x\le y^2\); discharge the squared inequality using \(\sqrt a^{\,2}=a\).
- **Independence:** Yes: precompose joint independence by the injective map \(k\mapsto(c,k)\). Package this bridge once. Joint independence is genuinely needed for the pooled variance; per-chain independence alone does not control cross-chain covariance.

## 4. Scope

A+B+C+D is coherent; roughly 250 lines is plausible if integrability and the envelope are readily reusable. Prioritize the relative corollary. The isotropic specialization is cheap afterward. The “0.90 at \(d=2\)” example needs the actual spectrum, step size, burn-in, and clarification of observed versus expected value; chain length alone cannot establish it.

All four belong together: D exposes the three error sources, while A–C provide its exact and reusable foundation.

Vote: A+B+C+D