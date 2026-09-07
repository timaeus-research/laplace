## Verdict

**No blocking statement-level issues found.** The zero-phase dictionary, square-parameter transport, and constant cross-validation have the correct normalisations. The exponential-gap changes supply sufficient measurability and integrability assumptions.

The mirror sentence is correct **in the unit-amplitude setting \(y_{00}=1\)**. As a formula for general \(y_{00}\), its middle equality is missing that factor.

### Findings table

| Rank | Item | Finding |
|---|---|---|
| Blocking | Supplied theorem statements | **None found.** |
| Should-fix, if intended generally | Mirror sentence | The expression \(2\Gamma(p/2)\beta^{-p/2}/(1!\,2k_1\,2k_2)\) needs a factor \(y_{00}\), unless the sentence explicitly assumes \(y_{00}=1\). |
| Cosmetic | Bridge module docstring | `canonA_zero_delta_eq` does not match the supplied theorem name `canonA_zeroPhase_eq_two_mul_monomialMixedConst`. Update the reference. |
| Cosmetic / scope clarification | Exponential-gap prose | The Big-O theorem allows \(\beta=0\) and arbitrary \(\varepsilon\); its comparison function need not decay. Actual exponential decay and the stated little-o result apply under \(\beta>0,\varepsilon>0\). |
| Pass | Exact dictionary | Correct kernel, amplitude, domain, and parameter \(N^2\). |
| Pass | Square transport | Correct exponent \(-2l\) and multiplier \(2^r\). |
| Pass | Constant cross-validation | Correct factor \(2\); the equal-ratio and positivity hypotheses are sufficient. |
| Pass | Review-v5 gap fixes | The hypotheses ensure a genuinely integrable weighted integrand, not merely a totalised integral. |

## 1. Exact zero-phase dictionary

The supplied coefficient identities give
\[
\operatorname{ampCoeff}\,\beta\,0\,\delta\;k\;s=\delta_k,
\qquad
\operatorname{anaAmp}(\operatorname{ampCoeff}\,\beta\,0\,\delta)\,b\,u\,v\,s=1.
\]
Only the \((0,0)\) term survives in the double sum, so the clamps have no effect.

Consequently the quadratic integrand is exactly
\[
u^{h_1}v^{h_2}
\exp\!\left[-\beta(Nu^{k_1}v^{k_2})^2\right]
=
u^{h_1}v^{h_2}
\exp\!\left[-\beta N^2u^{2k_1}v^{2k_2}\right].
\]
This is the two-dimensional monomial integrand with parameter \(N^2\), not \(\beta N^2\) or \(N\): the monomial definition already supplies the factor \(\beta\).

The cutoff bridge identifies the iterated integral with the box integral, and `monomialBoxRealCutoff_one` supplies the unit-box identification. Thus **`twoDAmp_zeroPhase_eq_monomial_sq` is an exact integral dictionary**, not just an asymptotic equivalence.

No positivity assumptions on \(\beta,N\) are needed for this bounded-domain identity. Likewise, zero exponents are legitimate here; positive \(k_i\) become necessary for the later ratio formulas.

## 2. Square-parameter transport

Eventually \(N>1\), so
\[
(N^2)^{-l}=N^{-2l},
\qquad
(\log(N^2))^r=2^r(\log N)^r.
\]
Therefore, eventually,
\[
\frac{F(N^2)}{N^{-2l}(\log N)^r}
=
2^r\,
\frac{F(N^2)}{(N^2)^{-l}(\log(N^2))^r}.
\]
Since \(N^2\to+\infty\), the stated limit is \(2^rC\).

**The statement is correct for every real \(l,C\) and natural \(r\), including \(r=0\).** No additional global positivity assumptions on \(N\) are needed for an `atTop` limit.

## 3. Constant cross-validation and numerical check

The hypotheses imply
\[
p=\frac{h_1+1}{k_1}=\frac{h_2+1}{k_2}>0,
\]
so both monomial ratios equal \(p/2>0\). With zero phase and unit amplitude, \(x_{00}=0\) and \(y_{00}=1\). Hence
\[
A_p=\frac1{k_1k_2}
\int_0^\infty s^{p-1}e^{-\beta s^2}\,ds
=\frac{\Gamma(p/2)\beta^{-p/2}}{2k_1k_2}.
\]
Meanwhile,
\[
C_{\mathrm{mono}}
=\frac{\Gamma(p/2)\beta^{-p/2}}{(2-1)!}
 \frac1{2k_1}\frac1{2k_2}
=\frac{\Gamma(p/2)\beta^{-p/2}}{4k_1k_2}.
\]
Thus **\(A_p=2C_{\mathrm{mono}}\)**, exactly as stated.

### Numerical check

Take
\[
\beta=1,\quad h_1=h_2=1,\quad k_1=k_2=1,\quad p=2.
\]
Then
\[
\int_0^\infty s e^{-s^2}\,ds=\frac12,
\]
and
\[
A_2=\frac12,\qquad
C_{\mathrm{mono}}=\frac{\Gamma(1)}{4}=\frac14,
\qquad
2C_{\mathrm{mono}}=\frac12.
\]

The asymptotic scaling agrees:
\[
C_{\mathrm{mono}}(N^2)^{-p/2}\log(N^2)
=
2C_{\mathrm{mono}}N^{-p}\log N.
\]

## 4. Review-v5 exponential-gap fixes

The added hypotheses address the integrability concern directly:

- `ha` and `hf` give AE strong measurability of
  \[
  x\longmapsto a(x)e^{-\beta Nf(x)}
  \]
  under the restricted measure.
- The bound \(\lVert a(x)\rVert\le g(x)\) implies \(g(x)\ge0\) on \(S\).
- When \(\beta N\ge0\) and \(f(x)\ge\varepsilon\),
  \[
  \left|a(x)e^{-\beta Nf(x)}\right|
  \le e^{-\beta N\varepsilon}g(x).
  \]
- This majorant is integrable because `hg` supplies integrability of \(g\) on \(S\).

Thus `exp_gap_integrable` asserts genuine integrability, and the norm bound is analytically meaningful.

For the family Big-O theorem, \(N\ge0\) eventually, so \(\beta\ge0\) supplies the needed sign condition. No measurability in the parameter \(N\) is required. Under \(\beta,\varepsilon>0\), the scalar exponential is little-o of every scale covered by the statement: real power exponent \(l\), natural logarithmic exponent \(r\), and positive coefficient \(C\). Composing this with the Big-O estimate gives the corresponding little-o conclusion for the integral family.

**No Lean statement corrections are needed.** The geometric gap remains an explicit assumption, correctly distinguished from merely deleting a neighbourhood of the corner.

## Corrected mirror sentence

For \(\beta>0\), positive \(k_i\), and equal ratios \(p=(h_i+1)/k_i\), the version valid for general \(y_{00}\) is:

> The Taylor-tree leading log coefficient is
> \[
> A_p
> =\frac{y_{00}}{k_1k_2}\int_0^\infty s^{p-1}e^{-\beta s^2}\,ds
> =\frac{y_{00}}{2k_1k_2}S_{p/2}(0)
> =\frac{2y_{00}\Gamma(p/2)\beta^{-p/2}}
> {1!\,(2k_1)(2k_2)}.
> \]
> For unit amplitude \(y_{00}=1\), this is twice the monomial mixed constant, the factor \(2\) arising from \(\log(N^2)=2\log N\). In the variable \(n=N^2\), the coefficient of \(n^{-p/2}\log n\) is
> \[
> \frac{y_{00}\Gamma(p/2)\beta^{-p/2}}{4k_1k_2}.
> \]

Finally, \(t=s^2\) gives exactly
\[
J_p(a)=\frac12 S_{p/2}(a),
\qquad
S_{p/2}(0)=\beta^{-p/2}\Gamma(p/2).
\]
**The \(S/J\) normalisation and the conversion to the \(n\)-coefficient are correct.**
