## 1. Algebra and remainder bookkeeping

**A, B, and C are correct as stated, with the usual convention that the remainder constant \(K\) can increase. D’s coefficient identities are correct; its interpretation needs qualification.**

Here \(\gamma\) denotes the **quartic coefficient**, while \(g\) denotes the **localiser strength**.

### A. Localised variance

Direct substitution gives
\[
\begin{aligned}
c_2'
&=B_2+ac_3+\frac{3p_3}{\lambda^2}
-\frac1\lambda\left(-\frac{a\alpha}{2\lambda^2}+\frac{p_3}{\lambda}\right)\\
&=\frac{5\alpha^2}{4\lambda^4}
-\frac{\gamma}{2\lambda^3}
-\frac{2a\alpha}{\lambda^3}
+\frac{a^2-g}{\lambda^2}.
\end{aligned}
\]
Since
\[
c^2=\frac{\alpha^2}{4\lambda^4}
-\frac{a\alpha}{\lambda^3}+\frac{a^2}{\lambda^2},
\]
we obtain
\[
\boxed{v'=\frac{\alpha^2}{\lambda^4}
-\frac{a\alpha}{\lambda^3}
-\frac{g}{\lambda^2}
-\frac{\gamma}{2\lambda^3}.}
\]
Consequently,
\[
\boxed{v'+\frac{g}{\lambda^2}
=\frac{\alpha^2}{\lambda^4}
-\frac{\gamma}{2\lambda^3}
-\frac{a\alpha}{\lambda^3}.}
\]

The remainder argument is immediate **after a boundedness/square estimate**, not with literally the same \(K\). Write \(m=t\langle x\rangle_{\rm loc}\), and suppose the input constants are \(K_m,K_2\). For \(t\ge1\), putting \(M=|c'|+K_m\) gives
\[
|m-c|\le\frac Mt,\qquad
|m^2-c^2|\le\frac{M(2|c|+M)}t.
\]
Using
\[
t\operatorname{Var}_{\rm loc}
=t\langle x^2\rangle_{\rm loc}-\frac{m^2}{t},
\]
therefore yields
\[
\left|t\operatorname{Var}_{\rm loc}-\frac1\lambda-\frac{v'}t\right|
\le\frac{K_2+M(2|c|+M)}{t^2}.
\]
Divide by \(t>0\) to obtain the claimed unscaled \(O(t^{-3})\) statement.

The rational identity in A is also correct. In particular,
\[
\left|\frac1{t\lambda+g}
-\frac1{\lambda t}+\frac{g}{\lambda^2t^2}\right|
=\frac{g^2}{\lambda^2t^2(t\lambda+g)}
\le\frac{g^2}{\lambda^3t^3}.
\]
This proves A’s comparison against \(S\), with an enlarged constant.

### B. Displayed mean

Expansion of the two rational terms gives
\[
P_t=\frac1t\left(-\frac{\alpha}{2\lambda^2}+\frac a\lambda\right)
+\frac1{t^2}\left(\frac{\alpha g}{\lambda^3}-\frac{ag}{\lambda^2}\right)
+O(t^{-3}).
\]
Thus
\[
\boxed{c'_S=\frac{\alpha g}{\lambda^3}-\frac{ag}{\lambda^2}}
\]
and subtraction from the supplied \(c'\) gives
\[
\boxed{r=B_1+\frac{a\alpha^2}{\lambda^4}
-\frac{a\gamma}{2\lambda^3}
-\frac{\alpha a^2}{2\lambda^3}.}
\]

For a concrete Lean-friendly rational bound, valid for \(t>0\),
\[
\left|P_t-\frac ct-\frac{c'_S}{t^2}\right|
\le
\frac{g^2}{t^3}
\left(\frac{3|\alpha|}{2\lambda^4}
+\frac{|a|}{\lambda^3}\right).
\]
Combine this with the unscaled mean input to obtain B.

### C. Rotated covariance and mean transport

Both finite-sum transports are correct. Take a common threshold over the finitely many coordinates and sum the scalar remainder constants with absolute weights:
\[
K_j=\sum_i |Q_{ji}|K_i,\qquad
K_{jk}=\sum_i |Q_{ji}Q_{ki}|K_i.
\]
No additional cross-covariance terms occur: the stated product-measure covariance transport already eliminates them.

All these statements concern **fixed parameters**. They do not assert constants uniform in \(g\), the anchor, or the oscillator parameters.

## 2. D: correct conclusion, but revise “exactly through second order”

The precise, valid conclusion is:

> At the minimiser anchor, the coefficients of \(t^{-2}\) in the residuals of the displayed mean and covariance approximations equal the corresponding unlocalised second-order coefficients and are independent of \(g\).

I would replace the bold slogan by:

> **At the minimiser anchor, using \(S=(tH+gI)^{-1}\) absorbs all localiser-dependent contributions through order \(t^{-2}\); the remaining second-order coefficients are the unlocalised ones.**

This avoids suggesting that the displayed approximations themselves have zero second-order error. They generally do not: \(B_1\) and
\[
V_2=\frac{\alpha^2}{\lambda^4}-\frac{\gamma}{2\lambda^3}
\]
remain.

Also, strictly speaking, an \(O(S^2)\) assertion does not specify a coefficient. Your theorems identify the **\(t^{-2}\) coefficients of those remainders**, under the fixed-parameter scaling \(S\asymp t^{-1}\).

### Structural explanation

Yes: at anchor zero the density is exactly proportional to
\[
\exp\!\left[-t\left(
\frac{\lambda+g/t}{2}x^2+\frac{\alpha}{6}x^3+\frac{\gamma}{24}x^4
\right)\right].
\]
Thus the localiser replaces \(\lambda\) by
\[
\lambda_t=\lambda+\frac gt.
\]
The displayed leading terms are precisely
\[
-\frac{\alpha}{2t\lambda_t^2},\qquad \frac1{t\lambda_t}.
\]
A second-order correction \(B_1(\lambda_t)/t^2\) or \(V_2(\lambda_t)/t^2\) differs from its value at \(\lambda\) only at order \(t^{-3}\). This explains the cancellation.

**There is generally \(g\)-dependence at the next order.** In a higher-order expansion, the residual third-order coefficients acquire
\[
gB_1'(\lambda)
=g\left(\frac{25\alpha^3}{8\lambda^6}
-\frac{8\alpha\gamma}{3\lambda^5}\right)
\]
for the mean, and
\[
gV_2'(\lambda)
=g\left(-\frac{4\alpha^2}{\lambda^5}
+\frac{3\gamma}{2\lambda^4}\right)
\]
for the variance, in addition to their unlocalised third-order coefficients. Establishing that next-order expansion rigorously would require additional results; it is not supplied by the current remainder bounds.

Two wording safeguards:

- Do not mix the note’s localiser symbol \(\gamma\) with the oscillator’s quartic \(\gamma\); use \(g\) consistently here.
- Attribute the refined coefficient result to this separable oscillator setting, not to the note’s general displayed big-\(O\) formulas.

For nonzero anchor, D’s “only through \(a\)” statement is correct **for the residual second-order coefficients**, not for the full expectation, covariance, or remainder constants.

## 3. Best nearby bundle

**I back A+B+C+D, with D reworded as above.**

It closes a coherent gap: existing localisation estimates certify the order, while this bundle identifies the coefficients on the same exact measures. It needs no new integral expansions.

A sensible implementation order is:

1. **A:** scalar variance and comparison against scalar \(S\).
2. **B, scalar:** rational expansion of `locLeading`, then residual mean coefficient.
3. A reusable weighted finite-sum \(t^{-3}\) transport lemma.
4. **B and C, rotated:** applications of existing coordinate identities.
5. **D:** minimiser-anchor simplification corollaries.

The line estimate is plausible but not certified without inspecting the APIs. Explicitly budget for enlarged constants, common thresholds, denominator positivity, and coefficient normalization.

The rotated `eq:covK` second-order result is a worthwhile next tide, especially if scalar third/fourth-moment expansions are already available. But the off-diagonal pair terms introduce a different mixed-moment bookkeeping layer. It is less direct than completing the localised mean/covariance story now.

A cheap additional corollary would state the entrywise limits explicitly:
\[
t^2(\operatorname{Cov}_{\rm loc}-S)_{jk}
\longrightarrow
\sum_iQ_{ji}Q_{ki}
\left(\frac{\alpha_i^2}{\lambda_i^4}
-\frac{\gamma_i}{2\lambda_i^3}
-\frac{a_i\alpha_i}{\lambda_i^3}\right),
\]
and analogously for the mean residual. These make “identifies the coefficient” completely unambiguous.

## 4. Vote

**Vote: A+B+C+D, with enlarged remainder constants explicit and D phrased as absorption of all localiser-dependent terms through \(t^{-2}\), not exact second-order accuracy.**