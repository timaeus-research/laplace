## 1. Correctness

**A, B, and C are correct. D is correct with its stated nondegeneracy hypotheses.**

For C, putting \(d=t\lambda_i+g\),
\[
P_i'(t)
=-\frac{\alpha_i(g-t\lambda_i)}{2d^3}
-\frac{a_i\lambda_i}{d^2}.
\]
Moreover,
\[
P_i(t)=\frac{c_{1i}}t+\frac{b_i}{t^2}+O(t^{-3}),
\qquad
b_i=\frac{\alpha_i g}{\lambda_i^3}-\frac{ga_i}{\lambda_i^2}
=\mathrm{locLeadingCoeff2}_i.
\]
Independently expanding this **exact derivative** gives
\[
P_i'=-\frac{c_{1i}}{t^2}-\frac{2b_i}{t^3}+O(t^{-4}).
\]
The covariance theorem supplies
\[
\mu_i'=-\frac{c_{1i}}{t^2}-\frac{2c_i'}{t^3}+O(t^{-4}),
\]
so indeed
\[
(\mu_i-P_i)'=-\frac{2r_i}{t^3}+O(t^{-4}).
\]

**Hypotheses/cautions:**
- All parameters, the frame, and the anchor are fixed as \(t\) varies.
- Require nonzero denominators eventually; \(\lambda_i>0\), with fixed \(g\), suffices after enlarging \(T\).
- Use actual derivative identities and derivative expansions: **differentiating an \(O(t^{-3})\) remainder is not justified by that remainder bound alone.**
- No \(r\ne0\) hypothesis is needed for A–C or the norm expansions.
- **Lean norm trap:** on ordinary `ι → ℝ`, the standard norm is the sup norm, not your Euclidean norm. Use explicit sums of squares or `EuclideanSpace`.

For D, writing \(R=\sum r_i^2\), \(C_1=\sum c_{1i}^2>0\), the precise relative squared statement is
\[
\left|t^2\frac{\|m-m_S\|_2^2}{\|m_S-c\|_2^2}
-\frac{R}{C_1}\right|\le \frac Kt
\]
eventually. Only the denominator coefficient must be positive here; two-sided positive bounds require \(R>0\).

## 2. Wording against the note

Your wording is right, preferably:

> For fixed parameters, the remainder in eq:mean has Euclidean norm  
> \(\|r\|_2/t^2+O(t^{-3})\). Its time derivative has Euclidean norm  
> \(2\|r\|_2/t^3+O(t^{-4})\), established independently from the derivative expansions.

Prove these directly by the reverse triangle inequality from the **vector** remainder bounds. This handles \(r=0\) without a separate square-root argument.

**Keep B alongside C**, but make C the headline: C differentiates the displayed approximation; B identifies the correction to the simpler leading derivative. Their coefficients are genuinely different.

## 3. Lean route

Your transport plan is sound. I would separate:

1. Exact orthogonal sum-of-squares preservation.
2. A finite-family squared-rate lemma.
3. Thin quadratic/cubic scaling wrappers.

This keeps all matrix algebra out of the asymptotic proofs. A dot-product proof of the exact identity is natural; if matrix API rewriting stalls, finite-sum expansion followed by the entrywise identity \(Q^\mathsf TQ=1\) is dependable.

For C, **differentiate inverse powers**, rather than a large quotient:
\[
P_i=(-\alpha_i/2)\,t\,d^{-2}+a_i d^{-1}.
\]
Use the affine derivative, `HasDerivAt.inv`, `pow`, products and sums; normalize to the displayed formula only afterward, using denominator nonvanishing and `field_simp`/`ring`.

For the derivative rate, do not build a general Taylor apparatus. Set \(z=g/(\lambda_i t)\); then
\[
P_i'
=\frac1{t^2}\left[
\frac{\alpha_i}{2\lambda_i^2}\frac{1-z}{(1+z)^3}
-\frac{a_i}{\lambda_i}\frac1{(1+z)^2}
\right].
\]
The useful exact cancellations are
\[
\frac{1-z}{(1+z)^3}-(1-4z)
=\frac{z^2(9+11z+4z^2)}{(1+z)^3},
\]
\[
\frac1{(1+z)^2}-(1-2z)
=\frac{z^2(3+2z)}{(1+z)^2}.
\]
With \(|z|\le\tfrac12\), these give the required quantitative bound immediately. Alternatively, clear denominators directly and bound the resulting rational remainder if that matches existing seabed lemmas better.

## 4. Priorities and vote

**Vote: A+B+C.** Land A first, B second, and C last; regard the rational derivative estimate as the scope risk. Add D only if the existing wrappers make it genuinely trivial—do not let relative-denominator bookkeeping displace C.

Cheap, useful additions:
- The two **unsquared norm** statements above.
- The degenerate consequences \(r=0\):
  \[
  \|m-m_S\|_2=O(t^{-3}),\qquad
  \|(m-m_S)'\|_2=O(t^{-4}).
  \]

**Best next target:** the energy discrepancy from the Gaussian trace prediction, using tide 73’s coefficient after verifying exactly which predictor was subtracted. It adds a new observable-level result; a joint mean/covariance/energy theorem is mostly packaging afterward.

The specialization \(w_0=c\) is a useful cheap corollary, not the next main target: it removes anchor terms but **does not generally eliminate the anharmonic mean residual**.