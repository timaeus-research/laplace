## 1. A is correct; use a fifth-order remainder, not a sixth-order one

Write \(m_k=\langle x^k\rangle\), \(a=gx_0\), \(b=g/2\), and
\[
a_1=-\frac{\alpha}{2\lambda^2},\qquad
c_3=-\frac{5\alpha}{2\lambda^3}.
\]
The relevant unlocalised coefficients are
\[
B_1=\frac{2\alpha\gamma}{3\lambda^4}
       -\frac{5\alpha^3}{8\lambda^5},
\qquad
B_2=\frac{5\alpha^2}{4\lambda^4}
       -\frac{\gamma}{2\lambda^3}.
\]

### Numerator: the cheaper truncation

Use
\[
e^y=P_4(y)+R_5(y),\qquad
P_4(y)=\sum_{j=0}^4\frac{y^j}{j!},
\qquad |R_5(y)|\le C_M|y|^5
\quad(y\le M).
\]
Your small-\(|y|\)/large-\(|y|\) proof using `Real.exp_bound` works here, with \(C_M=e^M+3\).

Crucially,
\[
|xR_5(y)|
 \le 16C_M\bigl(|a|^5x^6+|b|^5|x|^{11}\bigr),
\]
and
\[
|x|^{11}\le \frac{x^{10}+x^{12}}2.
\]
Thus its expectation is \(O(t^{-3})\), using even-moment bounds through degree **12**.

The exact polynomial identity is only degree **9**:
\[
xP_4(ax-bx^2)
=x+ax^2+p_3x^3+p_4x^4+p_5x^5
  +q_6x^6+q_7x^7+q_8x^8+q_9x^9,
\]
where
\[
\begin{aligned}
p_3&=a^2/2-b,\\
p_4&=a^3/6-ab,\\
p_5&=a^4/24-a^2b/2+b^2/2,\\
q_6&=ab^2/2-a^3b/6,\\
q_7&=a^2b^2/4-b^3/6,\\
q_8&=-ab^3/6,\qquad q_9=b^4/24.
\end{aligned}
\]
All \(q_k\)-terms have expectation \(O(t^{-3})\) by absolute even-power bounds. The \(p_5m_5\) term is \(O(t^{-3})\) by the **signed fifth-moment bound**.

Consequently,
\[
N:=\langle x\phi\rangle
=m_1+am_2+p_3m_3+p_4m_4+O(t^{-3}).
\]

**Minimality qualification.** For generic \(a\ne0\), a remainder \(O(|y|^5)\) is the lowest ordinary exponential Taylor remainder that gives the desired estimate directly by absolute moments after multiplication by \(x\). A raw \(O(|y|^4)\) remainder does not suffice.

You can describe the proof as “fourth-order remainder with its leading \(x^5\) contribution extracted”, but you then need
\[
R_4(y)=y^4/24+O(|y|^5),
\]
or an equivalent refinement. That is effectively the same fifth-order estimate—not a consequence of the existing \(O(|y|^4)\) bound alone.

Your proposed sixth-order route is valid but unnecessary; its remainder requires even moments through degree **14** after multiplication by \(x\).

### Exactly which moment rates are needed?

For the numerator, only:
\[
\begin{aligned}
m_1&=a_1/t+B_1/t^2+O(t^{-3}),\\
m_2&=1/(\lambda t)+B_2/t^2+O(t^{-3}),\\
m_3&=c_3/t^2+O(t^{-3}),\\
m_4&=3/(\lambda^2t^2)+O(t^{-3}),\\
m_5&=O(t^{-3}).
\end{aligned}
\]

So:

- **Second-order coefficients are needed only for \(m_1,m_2\).**
- For \(m_3,m_4\), their leading coefficient with an \(O(t^{-3})\) error suffices. Neither \(B_3\) nor the next fourth-moment coefficient enters.
- For \(m_5\), no coefficient is needed: just \(|m_5|\le C/t^3\).
- No sixth-moment leading coefficient is needed; the even-moment bounds suffice.

Do not replace \(|m_5|\) by \(\langle |x|^5\rangle\): that loses the signed cancellation.

### Denominator

Yes: use
\[
e^y=P_3(y)+R_4(y),\qquad |R_4(y)|\le C_M|y|^4.
\]
The polynomial terms beyond degrees \(0,1,2\) involve \(m_3,\ldots,m_6\) and contribute \(O(t^{-2})\). Also,
\[
|y|^4\le 8(a^4x^4+b^4x^8),
\]
so
\[
D:=\langle\phi\rangle
=1+am_1+p_3m_2+O(t^{-2})
=1+\frac{d_1}{t}+O(t^{-2}),
\]
with
\[
\boxed{d_1=-\frac{a\alpha}{2\lambda^2}
                 +\frac{a^2-g}{2\lambda}.}
\]

### Independent coefficient calculation

The numerator expansion is
\[
tN=c+\frac{n_1}{t}+O(t^{-2}),
\qquad c=-\frac{\alpha}{2\lambda^2}+\frac a\lambda,
\]
where
\[
n_1=B_1+aB_2+p_3c_3+\frac{3p_4}{\lambda^2}.
\]
Explicitly,
\[
\boxed{
n_1=B_1+\frac{5a\alpha^2}{4\lambda^4}
-\frac{a\gamma}{2\lambda^3}
-\frac{5\alpha a^2}{4\lambda^3}
+\frac{5\alpha g}{4\lambda^3}
+\frac{a^3}{2\lambda^2}
-\frac{3ag}{2\lambda^2}.}
\]
Subtracting \(cd_1\) gives
\[
\boxed{
c'=B_1+\frac{a\alpha^2}{\lambda^4}
-\frac{a\gamma}{2\lambda^3}
+\frac{\alpha g}{\lambda^3}
-\frac{\alpha a^2}{2\lambda^3}
-\frac{ag}{\lambda^2}.}
\]
This agrees with A.

### Ratio step: avoid constructing an inverse expansion

Use `locDenominator_rate` to arrange \(D\ge1/2\). Set
\[
U=tN,\quad q=c+c'/t,\quad
U=c+n_1/t+\varepsilon_N,\quad
D=1+d_1/t+\varepsilon_D.
\]
Since \(n_1=c'+cd_1\),
\[
U-qD
=\varepsilon_N-c\varepsilon_D
-\frac{c'd_1}{t^2}-\frac{c'}t\varepsilon_D.
\]
For \(t\ge1\), every term is \(O(t^{-2})\), and division by \(D\ge1/2\) finishes.

This cross-multiplication proof is likely substantially easier in Lean than a separate reciprocal-series lemma.

---

## 2. Localised Stein works, but is cheaper only if weighted IBP is already easy

Let \(\mu_k=\langle x^k\rangle_{\rm loc}\). The identity is indeed
\[
(\lambda+g/t)\mu_1+\frac\alpha2\mu_2+\frac\gamma6\mu_3=\frac at.
\]
It is enough to establish
\[
\mu_2=\frac1{\lambda t}+\frac{L_2}{t^2}+O(t^{-3}),
\qquad
\mu_3=\frac{L_3}{t^2}+O(t^{-3}),
\]
where direct weighted-moment expansion gives
\[
\boxed{
L_2=B_2-\frac{2a\alpha}{\lambda^3}
                  +\frac{a^2-g}{\lambda^2},
\qquad
L_3=-\frac{5\alpha}{2\lambda^3}
                  +\frac{3a}{\lambda^2}.}
\]

Here is the precise truncation economy:

| Numerator | Exponential polynomial | Absolute remainder after weighting |
|---|---|---|
| \(\langle x^2\phi\rangle\) | \(P_3(y)\) | \(C x^2|y|^4\), controlled through degree 10 |
| \(\langle x^3\phi\rangle\) | \(P_2(y)\) | \(C |x|^3|y|^3\), controlled through degree 10 |

Thus
\[
\begin{aligned}
\langle x^2\phi\rangle
 &=m_2+am_3+p_3m_4+O(t^{-3}),\\
\langle x^3\phi\rangle
 &=m_3+am_4+O(t^{-3}).
\end{aligned}
\]
For the first ratio, subtract \(d_1/\lambda\) from the \(t^{-2}\) coefficient. For the second, \(D=1+O(t^{-1})\) already suffices.

Stein then yields
\[
c'=\frac{-\alpha L_2/2-\gamma L_3/6-gc}{\lambda},
\]
which simplifies to the same boxed formula above.

**Lean cost assessment:**

- This route avoids using the second-order \(m_1\) theorem, although that theorem is already available.
- It reduces the largest explicit polynomial degree to 8 and the largest needed even moment to 10.
- But it requires two weighted-moment estimates and a localised IBP theorem, including its integrability/boundary obligations.
- The direct route now has only a degree-9 identity—not degree 11—and reuses the existing mean theorem.

**Recommendation:** use the direct numerator/denominator route unless `ibp_anharmonic` already has a test-function interface that makes insertion of `locWeight` nearly automatic. Do not develop a new weighted IBP infrastructure merely to save two polynomial degrees here.

---

## 3. B: the coefficient is straightforward once \(P_t\) is pinned down

The supplied context does not include the actual definition of \(P_t\), \(S\), or `meanShiftLoc`, so this part needs one explicit qualification.

If the intended coordinatewise displayed approximation is the usual localised Gaussian-plus-skew expression
\[
P_t=
\frac{a}{t\lambda+g}
-\frac{t\alpha}{2(t\lambda+g)^2},
\]
then
\[
P_t=\frac ct+\frac{c'_S}{t^2}+O(t^{-3}),
\qquad
\boxed{c'_S=\frac{\alpha g}{\lambda^3}-\frac{ag}{\lambda^2}.}
\]
There are **no additional terms** in \(c'_S\) for this definition.

The residual coefficient is therefore
\[
\boxed{
r:=c'-c'_S
=B_1+\frac{a\alpha^2}{\lambda^4}
-\frac{a\gamma}{2\lambda^3}
-\frac{\alpha a^2}{2\lambda^3}.}
\]

For the separable E2 model, take
\[
a_i=g\bigl(Q^\top(w_0-c_{\rm ctr})\bigr)_i
\]
and define
\[
R_{\rm loc}=Q(r_i)_i.
\]
Then the clean statement is
\[
\left|
\left(
\langle w\rangle_{\rm loc}
-c_{\rm ctr}
-\operatorname{meanShiftLoc}
-gS(w_0-c_{\rm ctr})
-\frac{R_{\rm loc}}{t^2}
\right)_j
\right|
\le \frac{K_j}{t^3}.
\]
If `meanShift₂,loc` denotes the actual shift rather than its coefficient, define it as \(R_{\rm loc}/t^2\); otherwise call \(R_{\rm loc}\) the “second-order mean-shift coefficient”. Keep that distinction explicit.

### Pitfalls

1. **Check the exact \(P_t\).** If \(S\) is unlocalised, or `meanShiftLoc` is evaluated at a displaced mode, its \(t^{-2}\) coefficient can change. The boxed \(c'_S\) applies to the displayed rational expression above.
2. **Subtract \(c'_S\), not zero.** Adding the full \(c'/t^2\) to the existing approximation double-counts its own second-order contribution.
3. **Retain \(B_1\).** At \(g=0\), the residual is the unlocalised second-order correction \(B_1\), not zero.
4. **State fixed localiser parameters.** These estimates are for fixed \(g,x_0\); uniformity in \(g\) or the anchor requires additional bounds.
5. **Keep the separability hypothesis visible.** Coordinatewise \(r_i\) is not the general nonseparable multidimensional coefficient.
6. The vector lifting itself is cheap:
   \[
   |(Qe)_j|\le\sum_i|Q_{ji}|\,|e_i|.
   \]

Suggested wording: **“Identifies the \(t^{-2}\) coefficient of the exact localised mean, and hence the second-order residual of the displayed E2 approximation.”** This distinguishes an actual coefficient theorem from the earlier \(O(S^2)\) bound.

## Vote

**Strong yes on A, using \(P_4(y)\) with an \(O(|y|^5)\) remainder and cross-multiplied ratio bookkeeping.** It needs fewer moment coefficients and less polynomial algebra than proposed. **B is a good optional corollary once the exact \(P_t\) definition is checked. Defer C; do not introduce localised Stein solely for this tide.**