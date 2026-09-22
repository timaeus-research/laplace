## 1. Correctness of A, B, and C

**A and B are correct under the standing coercivity/nondegeneracy assumptions of tides 65–68**, with all parameters fixed and the estimates asserted for sufficiently large positive \(t\). **C is correct for the Gaussian trace prediction, but its sign claim must not be transferred to the exact anharmonic energy.**

### A: the one-dimensional localised energy

Write \(D=\langle\phi\rangle\), \(m=\langle x\rangle_{\mathrm{loc}}\), and \(V=\operatorname{Var}_{\mathrm{loc}}(x)\).

**(i) The second-moment argument is correct.** For \(t>0\),
\[
t\langle x^2\rangle_{\mathrm{loc}}
=tV+tm^2
=tV+\frac{(tm)^2}{t}.
\]
Multiplication of the variance bound by \(t\) gives
\[
\left|tV-\frac{t}{t\lambda+g}\right|\le \frac{K_V}{t}.
\]
The sharp mean estimate implies, after taking \(t\ge1\),
\[
|tm|\le |c|+K_m,
\]
hence
\[
\left|t\langle x^2\rangle_{\mathrm{loc}}
-\frac{t}{t\lambda+g}\right|
\le \frac{K_V+(|c|+K_m)^2}{t}.
\]
This is a useful standalone intermediate lemma.

**(ii) The cubic identity and proposed moment bounds are correct:**
\[
x^3\phi
=x^3+gx_0x^4-\frac g2x^5+x^3(\phi-1-y).
\]
In particular, the minus sign and the fifth power are right.

Make the “\(\le\) even” step explicit:
\[
|x|^5\le x^4+x^6,\qquad
|x|^7\le x^6+x^8.
\]
Consequently,
\[
|x^3(\phi-1-y)|
\le C_1x^4+(C_1+C_2)x^6+C_2x^8.
\]
Using the even-moment rates and \(t\ge1\), its expectation multiplied by \(t\) is \(O(t^{-1})\). The \(x^5\) term is handled by the first inequality, while the unweighted cubic term uses `thirdMoment_bound`.

Choose the threshold so that `locDenominator_rate` gives \(D\ge\frac12\). Division then yields
\[
|t\langle x^3\rangle_{\mathrm{loc}}|\le K_3/t.
\]
Similarly, positivity and `locWeight_le` give
\[
0\le t\langle x^4\rangle_{\mathrm{loc}}
\le 2e^{gx_0^2/2}\,t\langle x^4\rangle
\le K_4/t.
\]

Linearity for the three polynomial terms now proves A. Use absolute values of the coefficients when assembling the final constant.

**Suggested proof order:** localised polynomial integrability → localised cubic and quartic bounds → localised raw second-moment bound → localised energy theorem.

### B: exact separation and the trace identity

**(iii) Both identities are correct.** After the orthogonal change of variables, the isotropic localiser separates coordinatewise. Its anchor must also be expressed in those coordinates. The resulting normalised measure is a product measure, so exactly
\[
\langle L\circ A\rangle_{\mathrm{loc}}
=\sum_i\langle\ell_i\rangle_{\mathrm{loc},i}.
\]

The observable is indeed the **original, unlocalised energy**, not the localised potential. Establish its integrability under the localised density before applying finite-sum linearity.

A formalisation caveat: the existing unlocalised theorem
`gibbsExpectation_energy_separableAnharmonic` is not by itself this localised identity. Prove the latter using the generic rotation/product/coordinate lemmas on the localised separable potential, as proposed.

For \(H=Q\operatorname{diag}(\lambda_i)Q^\top\),
\[
\frac12\operatorname{tr}\!\left(tH(tH+gI)^{-1}\right)
=\frac12\sum_i\frac{t\lambda_i}{t\lambda_i+g}.
\]
Your `locS_rot` → conjugation multiplication → cyclic trace route is appropriate. Apply A coordinatewise, take a common finite threshold, and sum the constants.

### C: distinguish the prediction from the exact energy

**(iv) The algebraic sign statement is correct for the trace prediction:**
\[
\frac12\sum_i\frac{t\lambda_i}{t\lambda_i+g}
=\frac d2-\frac12\sum_i\frac{g}{t\lambda_i+g}.
\]
Thus, for \(g\ge0\), it is at most \(d/2\); with positive eigenvalues,
\[
\frac12\operatorname{tr}\!\left(tH(tH+gI)^{-1}\right)
=\frac d2-\frac{g}{2t}\operatorname{tr}(H^{-1})+O(t^{-2}).
\]

B also implies
\[
\left|t\langle L\circ A\rangle_{\mathrm{loc}}-\frac d2\right|
\le K/t.
\]

**But B does not determine the sign of the exact energy’s \(1/t\) correction.** Its error is of exactly that order. Nor does B establish that localisation lowers the exact energy compared with its unlocalised value.

## 2. Wording and whether to pursue the first coefficient

Recommended wording:

> The exact localised anharmonic energy agrees with E3’s Gaussian trace prediction up to an absolute \(O(t^{-1})\) error, for fixed localisation strength and anchor.

Avoid saying this “identifies the leading localiser correction”: that correction is itself \(O(t^{-1})\), so the error can conceal or reverse it.

### A sharper statement exists, but requires sharper asymptotic lemmas

For orientation, put \(a=gx_0\). A standard rescaled Laplace expansion gives, under the standing assumptions ensuring concentration at the nondegenerate minimum \(0\),
\[
t\langle\ell\rangle_{\mathrm{loc}}
=\frac12+\frac1t\left[
\frac{a^2-g}{2\lambda}
-\frac{a\alpha}{2\lambda^2}
-\frac{\gamma}{8\lambda^2}
+\frac{5\alpha^2}{24\lambda^3}
\right]+o(t^{-1}).
\]
Equivalently,
\[
t\langle\ell\rangle_{\mathrm{loc}}
-\frac12\frac{t\lambda}{t\lambda+g}
=
\frac1t\left[
\frac{a^2}{2\lambda}
-\frac{a\alpha}{2\lambda^2}
-\frac{\gamma}{8\lambda^2}
+\frac{5\alpha^2}{24\lambda^3}
\right]+o(t^{-1}).
\]
For your numerical parameters, the bracket is approximately \(-0.0457\), consistent with the reported values.

**This coefficient is not certified by the listed bounds alone.** One needs asymptotic coefficients or limits for the relevant scaled moments and denominator, with remainders strong enough to identify the limit. The displayed variance estimate, for example, leaves an unidentified \(t^{-2}\) variance term that becomes a \(t^{-1}\) energy term.

**Recommendation: stop tide 69 at \(O(t^{-1})\).** The coefficient is a natural follow-up, not a small algebraic corollary. Likewise, the numerical evidence suggests sharpness for the tested parameters but does not prove it; the coefficient can vanish for special parameters.

## 3. Pitfalls and bundle recommendation

- **Observable:** keep the unlocalised energy explicit in theorem statements. Adding the localiser to the observable changes the result.
- **Displaced anchor:** even for a purely quadratic target,
  \[
  t\langle\ell\rangle_{\mathrm{loc}}
  =\frac12\frac{t\lambda}{t\lambda+g}
   +\frac{t\lambda g^2x_0^2}{2(t\lambda+g)^2}.
  \]
  Thus the trace expression alone is not the exact anchored Gaussian energy either; it is the covariance contribution.
- **\(t\)-dependent potential:** instantiate rotation and product lemmas pointwise in \(t\). Do not use a fixed-potential partition-function differentiation identity without accounting for the potential’s \(t\)-dependence.
- **Thresholds:** combine \(t\ge1\), \(D\ge\frac12\), and all existing rate thresholds once. Constants may depend on the fixed model, localiser, anchor, and dimension; these are not uniform-in-parameter claims.
- **\(g=0\):** entirely fine. Then \(\phi=1\), \(D=1\), and the trace prediction is \(d/2\). Avoid auxiliary proofs that divide by \(g\).
- **Naming:** distinguish quartic coefficient \(\gamma\) from localiser strength \(g\), especially when comparing with the note’s \(\gamma\).

**Vote: approve A + B, and include C with its sign claim explicitly restricted to the Gaussian trace prediction. Defer the first anharmonic correction coefficient to a separate tide.**