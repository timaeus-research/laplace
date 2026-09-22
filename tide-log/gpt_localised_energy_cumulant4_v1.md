## 1. Correctness of A–C

**A1–A5 and B are correct. C is correct provided \(d>0\), with the ratio considered eventually where its denominator is nonzero.** All five constants are right:
\[
105/\lambda^4,\qquad 105/16,\qquad 3,\qquad -3d,\qquad 12/d.
\]

### A: moment and cumulant bookkeeping

Take all eventual thresholds at least \(1\).

- **A1:** The existing localiser comparison transfers the unlocalised even-moment bounds. For \(k\ge5\), \(t^5m_{2k}\) is bounded since \(t^{5-k}\le1\). The pointwise bound
  \[
  |x|^{2k+1}\le \tfrac12(x^{2k}+x^{2k+2})
  \]
  supplies the corresponding absolute odd-moment bound, hence the stated signed bound.

- **A2:** Your rescaling of the \(k=8\) recursion is exact. Since
  \[
  0<\frac{t}{t\lambda+g}\le\frac1\lambda,
  \]
  the listed bounds on \(t^4m_7,t^4m_8,t^5m_{10},t^5m_{11}\) give bounded \(t^5m_9\).

- **A3:** The \(k=7\) rescaling is also exact. Write its bracket as
  \[
  \frac{105}{\lambda^3}+O(1/t).
  \]
  All three error terms have the required rate:
  \[
  t^3m_7=O(1/t),\qquad t^4m_9=O(1/t),\qquad t^4m_{10}=O(1/t).
  \]
  **Yes: the improved signed ninth-moment estimate is needed for this argument and is supplied by A2.** An absolute Gaussian-scale ninth-moment bound alone would generally lose a half-power. Finally,
  \[
  \left|\frac{t}{t\lambda+g}-\frac1\lambda\right|
  =\frac{g}{\lambda(t\lambda+g)}
  \le\frac{g}{\lambda^2t},
  \]
  proving the claimed \(O(1/t)\) rate.

- **A4:** The leading two coefficients are correctly
  \[
  \frac{\lambda^4}{16}x^8+\frac{\lambda^3\alpha}{12}x^9.
  \]
  A2 handles degree \(9\); A1 handles degrees \(10,\ldots,16\). Thus \(t^4\langle\ell^4\rangle=105/16+O(1/t)\).

- **A5:** The cumulant polynomial and its limiting value \(3\) are correct. Assemble it using the bounded scaled moments \(t^j\langle\ell^j\rangle\), rather than manipulating unscaled remainders separately.

### B: differentiation

The \(t\)-independence of the localiser is exactly what makes
\[
M_r'=-M_{r+1}+M_rM_1,\qquad M_r=\langle\ell^r\rangle_{\rm loc}
\]
hold without another term. Differentiating
\[
\kappa_3=M_3-3M_2M_1+2M_1^3
\]
then gives \(\kappa_3'=-\kappa_4\) by a ring identity.

The proposed integrability extension suffices. Explicitly cover both cases:

- \(k=i\): the product is \(\ell_i^4\);
- \(k\ne i\): factorise the \(\ell_k\) and \(\ell_i^3\) factors.

For the Lean proof, one important detail is to establish the identity
\[
\operatorname{deriv}(\operatorname{deriv}E)(s)=\sum_i\kappa_{3,i}(s)
\]
**on a neighbourhood of the positive temperature \(t\)** before transferring `HasDerivAt`. Equality merely at \(t\) does not justify differentiating the replacement.

### C: quotient rate

Put
\[
V(t)=t^2\sum_i\operatorname{Var}_i(\ell_i),\qquad
H(t)=t^4\sum_i\kappa_{4,i}(\ell_i).
\]
Then
\[
V=d/2+O(1/t),\qquad H=3d+O(1/t).
\]
For \(d>0\), eventually \(V\ge d/4\), so
\[
\frac{H}{V^2}=\frac{12}{d}+O(1/t).
\]
The exact derivative identities identify this quotient with your proposed expression.

The observed \(O(t^{-2})\) cancellation is plausible, but **is not supplied by A+B or by differentiating tide 87’s remainder**. It would require stronger independently justified expansions.

## 2. Recommended bundle and formulation of C

**A+B+C is the strongest reasonably reachable bundle.** A carries the main new asymptotic work; B extends an existing differentiation pattern. Once those land, C is a small quotient-stability result, not another analytic campaign.

I would state C primarily as
\[
\left|
\frac{\sum_i\kappa_{4,i}(\ell_i)}
     {(\sum_i\operatorname{Var}_i(\ell_i))^2}
-\frac{12}{d}
\right|\le\frac Kt,
\qquad d>0,
\]
and provide the derivative-defined expression as a corollary.

This formulation:

- uses precisely the quantities already constructed;
- keeps nested `deriv` expressions out of the quotient estimate;
- separates the asymptotic algebra from the exact response identities.

Your derivative-defined formulation is valid, but call it a **normalised fourth-cumulant response ratio** unless you also establish that it is the excess kurtosis of the total energy.

A general cumulant-additivity theorem is unnecessary to make that last identification. A specialised independence lemma suffices:
\[
\mathbb E\!\left[\Big(\sum_iY_i\Big)^4\right]
=\sum_i\mathbb E[Y_i^4]
 +6\sum_{i<j}\mathbb E[Y_i^2]\mathbb E[Y_j^2],
\]
for centred independent \(Y_i\). Subtracting three times the squared total variance gives fourth-cumulant additivity. Still, I would not make this extra finite-product expansion a prerequisite for this tide.

## 3. Shortcuts and nearby opportunities

### Avoiding the nine explicit coefficients

There is a useful sparse alternative to the full expansion. Set
\[
a=\lambda/2,\qquad b=\alpha/6,\qquad c=\gamma/24.
\]
Then
\[
\ell^4=a^4x^8+4a^3b\,x^9+x^{10}R(x),
\]
where
\[
R(x)=4a^3c+6a^2(b+cx)^2
      +4ax(b+cx)^3+x^2(b+cx)^4.
\]
Since \(R\) has degree at most \(6\), there is \(C\ge0\) with
\[
|R(x)|\le C(1+x^6).
\]
Consequently,
\[
\left|\langle\ell^4\rangle-a^4m_8-4a^3b\,m_9\right|
\le C(m_{10}+m_{16}).
\]
A1–A3 immediately finish the proof.

This isolates the only problematic signed term, \(m_9\), and needs no intermediate coefficients. **Use it if polynomial-growth domination is already convenient in the library; otherwise, the existing explicit-expansion/assembly template is probably safer.**

### A Stein identity exists, but is not obviously cheaper

Define
\[
\delta=x\ell'-2\ell=\frac{\alpha}{6}x^3+\frac{\gamma}{12}x^4.
\]
Stein with test function \(x\ell^3\) gives
\[
2t\langle\ell^4\rangle
=7\langle\ell^3\rangle
 +3\langle\delta\ell^2\rangle
 -t\langle\delta\ell^3\rangle
 -g\langle x(x-x_0)\ell^3\rangle.
\]
The listed moment bounds make every correction, after multiplying by \(t^3\), \(O(1/t)\). Hence
\[
t^4\langle\ell^4\rangle
=\frac72\,t^3\langle\ell^3\rangle+O(1/t)
=\frac{105}{16}+O(1/t).
\]

This is conceptually attractive, but it **still needs A2** through the degree-nine term in \(\delta\ell^3\), and introduces several polynomial remainder estimates. It is not automatically a formalisation saving.

For the eighth moment itself, your \(k=7\) recursion is already the clean route.

## 4. Wording against the note

I would avoid an unqualified assertion that the Gamma **law** has been verified. Four cumulants do not establish a distributional limit or identify a law.

A precise gloss is:

> For fixed admissible quartic parameters and a fixed, temperature-independent localiser, the first four cumulants of the localised energy have the leading asymptotics of a Gamma distribution with shape \(d/2\) and rate \(t\), with \(O(1/t)\) errors after the corresponding \(t^n\) rescaling.

If fourth-cumulant additivity remains unformalised, make the formal claim slightly narrower:

> The localised energy’s cumulant-response hierarchy matches the Gamma\((d/2,\text{ rate }t)\) hierarchy through order four.

Keep these qualifications explicit:

- \(g,x_0\), quartic coefficients, and dimension are fixed.
- Constants and thresholds may depend on these parameters; no uniformity is claimed.
- This is the specified **localised Gibbs measure**, not automatically the posterior.
- The Gamma comparison concerns leading low-temperature cumulant asymptotics; it is neither an exact finite-\(t\) Gamma law nor, by itself, a proof of convergence in distribution.
- The normalised ratio \(12/d\) requires \(d>0\).

**Vote: A+B+C, with C stated first as the coordinate-cumulant ratio and then as a derivative-response corollary.**