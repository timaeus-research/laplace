## 1. A–C: the coefficients are right, but two proof steps need correction

Assume throughout that \(\lambda>0\), and that \(a,g,\alpha,\gamma\) are fixed as \(t\to\infty\).

The main conclusions of A, B, and C are correct. However:

- **C has a missing factor \(1/t\)** in its displayed formula for \(t^2C_{4,2}\).
- **The quoted `locFifth_expansion` bound does not establish B’s \(O(1/t)\) rate.** It needs sharpening.

There is also an apparent numerical error in the quoted seventh-moment input; see §2.

### A: independent check

Write \(q_4=c_4'\). Direct substitution gives
\[
\begin{aligned}
q_4
&=C_4+ac_5+\frac{15p_3}{\lambda^3}
       -\frac{3d_1}{\lambda^2}\\
&=\frac{25\alpha^2}{2\lambda^5}
  -\frac{16a\alpha+4\gamma}{\lambda^4}
  +\frac{6(a^2-g)}{\lambda^3}\\
&=\frac{25\alpha^2-32a\alpha\lambda
       +12a^2\lambda^2-12g\lambda^2-8\gamma\lambda}
       {2\lambda^5}.
\end{aligned}
\]
Thus **A’s coefficient is correct**.

Its numerator argument is also sound: the signed seventh moment contributes only \(O(t^{-2})\) after multiplying by \(t^2\), and the even-moment envelope starts at degree eight.

### B: independent check of the limits

Let
\[
v=-\frac{35\alpha}{2\lambda^4}+\frac{15a}{\lambda^3},
\qquad
w=\frac{15}{\lambda^3}.
\]
The leading numerator terms are
\[
t^3\langle x^5\phi\rangle
=t^3\langle x^5\rangle+a\,t^3\langle x^6\rangle+O(t^{-1}),
\]
and
\[
t^3\langle x^6\phi\rangle
=t^3\langle x^6\rangle+O(t^{-1}).
\]
Division by \(D=\langle\phi\rangle=1+O(t^{-1})\) preserves these rates. Hence
\[
t^3m_5=v+O(t^{-1}),\qquad t^3m_6=w+O(t^{-1}).
\]

These statements are correct, **provided the first displayed numerator remainder is proved with a sharper estimate than the quoted `locFifth_expansion`**.

### C: explicit coefficient bookkeeping

Use the abbreviations
\[
b=\frac1\lambda,\quad
q=\frac3{\lambda^2},\quad
s=-\frac{5\alpha}{2\lambda^3}+\frac{3a}{\lambda^2},
\]
and write
\[
\begin{array}{ll}
tm_1=c+c'/t+O(t^{-2}),&
tm_2=b+c_2'/t+O(t^{-2}),\\
t^2m_3=s+O(t^{-1}),&
t^2m_4=q+q_4/t+O(t^{-2}),\\
t^3m_5=v+O(t^{-1}),&
t^3m_6=w+O(t^{-1}).
\end{array}
\]

For reference, the independently computed second-order coefficients are
\[
\boxed{
c'=-\frac{5\alpha^3}{8\lambda^5}
+\frac{2\alpha\gamma/3+a\alpha^2}{\lambda^4}
+\frac{\alpha g-\alpha a^2/2-a\gamma/2}{\lambda^3}
-\frac{ag}{\lambda^2}}
\]
and
\[
\boxed{
c_2'=\frac{5\alpha^2}{4\lambda^4}
-\frac{\gamma/2+2a\alpha}{\lambda^3}
+\frac{a^2-g}{\lambda^2}.}
\]

#### \(n=1\)

The four covariance expansions are
\[
\begin{aligned}
t^2C_{3,1}
 &=q+\frac{q_4-sc}{t}+O(t^{-2}),\\
t^2C_{4,1}
 &=\frac{v-qc}{t}+O(t^{-2}),\\
tC_{2,1}
 &=\frac{s-bc}{t}+O(t^{-2}),\\
tC_{1,1}
 &=b+\frac{c_2'-c^2}{t}+O(t^{-2}).
\end{aligned}
\]
Consequently, the constant coefficient in the reduction is
\[
\frac c2-\frac{\alpha q}{12}+\frac{ab}{2}=c.
\]
The \(1/t\) coefficient is
\[
K_1=\frac{c'}2
-\frac{\alpha}{12}(q_4-sc)
-\frac{\gamma}{24}(v-qc)
-\frac g2(s-bc)
+\frac a2(c_2'-c^2).
\]

Here are the required algebraic differences:
\[
\begin{aligned}
q_4-sc
 &=\frac{45\alpha^2}{4\lambda^5}
   -\frac{12a\alpha+4\gamma}{\lambda^4}
   +\frac{3a^2-6g}{\lambda^3},\\
v-qc&=-\frac{16\alpha}{\lambda^4}
       +\frac{12a}{\lambda^3},\\
s-bc&=-\frac{2\alpha}{\lambda^3}
       +\frac{2a}{\lambda^2},\\
c_2'-c^2
 &=\frac{\alpha^2}{\lambda^4}
   -\frac{\gamma/2+a\alpha}{\lambda^3}
   -\frac g{\lambda^2}.
\end{aligned}
\]
Substitution shows that the four terms after \(c'/2\) sum to \(3c'/2\). Therefore
\[
\boxed{K_1=2c'.}
\]

#### \(n=2\)

**Correct the exact identity to**
\[
\boxed{
t^2C_{4,2}
=\frac{t^3m_6}{t}
-\frac{(t^2m_4)(tm_2)}{t}.}
\]
The candidate’s second term is missing its denominator \(t\). Taken literally, that formula would even give the wrong constant coefficient.

The corrected expansions are
\[
\begin{aligned}
t^2C_{3,2}&=\frac{v-sb}{t}+O(t^{-2}),\\
t^2C_{4,2}&=\frac{w-qb}{t}+O(t^{-2}),\\
tC_{2,2}&=\frac{q-b^2}{t}+O(t^{-2}),\\
tC_{1,2}&=\frac{s-cb}{t}+O(t^{-2}).
\end{aligned}
\]
Thus the constant is \(b\), and the \(1/t\) coefficient is
\[
K_2=c_2'
-\frac{\alpha}{12}(v-sb)
-\frac{\gamma}{24}(w-qb)
-\frac g2(q-b^2)
+\frac a2(s-cb).
\]
Now
\[
v-sb=-\frac{15\alpha}{\lambda^4}+\frac{12a}{\lambda^3},
\quad
w-qb=\frac{12}{\lambda^3},
\quad
q-b^2=\frac2{\lambda^2},
\quad
s-cb=-\frac{2\alpha}{\lambda^3}+\frac{2a}{\lambda^2}.
\]
Hence
\[
K_2
=c_2'+\frac{5\alpha^2}{4\lambda^4}
-\frac{\gamma/2+2a\alpha}{\lambda^3}
+\frac{a^2-g}{\lambda^2}
=\boxed{2c_2'}.
\]

So **the main coefficient claim survives independent checking**, with the displayed scaling correction.

## 2. Remainder allocation and moment-input pitfalls

Put
\[
M_1=tm_1,\quad M_2=tm_2,\quad
M_3=t^2m_3,\quad M_4=t^2m_4,\quad
M_5=t^3m_5,\quad M_6=t^3m_6.
\]
Below, “second order” means constant plus \(1/t\), with \(O(t^{-2})\) error; “leading rate” means constant plus \(O(t^{-1})\).

### Inputs for \(n=1\)

| Term | Exact scaled expression | Required inputs |
|---|---|---|
| Reduction’s moment term | \(M_1/2\) | \(M_1\): second order |
| \(t^2C_{3,1}\) | \(M_4-M_3M_1/t\) | \(M_4\): second order; \(M_3,M_1\): leading rate in product |
| \(t^2C_{4,1}\) | \((M_5-M_4M_1)/t\) | \(M_5,M_4,M_1\): leading rate |
| \(tC_{2,1}\) | \((M_3-M_2M_1)/t\) | \(M_3,M_2,M_1\): leading rate |
| \(tC_{1,1}\) | \(M_2-M_1^2/t\) | \(M_2\): second order; \(M_1\): leading rate in square |

### Inputs for \(n=2\)

| Term | Exact scaled expression | Required inputs |
|---|---|---|
| Reduction’s moment term | \(M_2\) | \(M_2\): second order |
| \(t^2C_{3,2}\) | \((M_5-M_3M_2)/t\) | \(M_5,M_3,M_2\): leading rate |
| \(t^2C_{4,2}\) | \((M_6-M_4M_2)/t\) | \(M_6,M_4,M_2\): leading rate |
| \(tC_{2,2}\) | \((M_4-M_2^2)/t\) | \(M_4,M_2\): leading rate |
| \(tC_{1,2}\) | \((M_3-M_1M_2)/t\) | \(M_3,M_1,M_2\): leading rate |

In particular, **A is needed for the linear result, not for the square result**. No second-order third, fifth, or sixth moment is needed.

For products, leading-rate estimates imply eventual boundedness, and `prod_rate` gives the requisite \(O(t^{-1})\) product error. Mere convergence or boundedness is insufficient for the desired final \(O(t^{-2})\) error.

### Sharpening B’s fifth-moment estimate

The quoted bound begins with \(N_6\langle x^6\rangle\). After multiplication by \(t^3\), that is only \(O(1)\), not \(O(t^{-1})\).

A convenient repair uses the shared expansion
\[
x^2\phi=x^2+ax^3+p_3x^4+p_4x^5+R.
\]
Multiply by \(x^3\):
\[
x^5\phi=x^5+ax^6+p_3x^7+p_4x^8+x^3R,
\]
where
\[
|x^3R|\le H_6|x|^9+H_8|x|^{11}+H_{10}|x|^{13}.
\]
Use the **signed** seventh-moment bound and
\[
|x|^9\le x^8+x^{10},
\]
with analogous inequalities for degrees eleven and thirteen. Every error term then has expectation \(O(t^{-4})\), so scaling by \(t^3\) gives \(O(t^{-1})\).

The sixth-moment route is sound if its stated pointwise envelope is available. Again, retaining the signed \(x^7\) term is important.

### Seventh moment: two distinct cautions

1. **A needs the unlocalised quantity \(t^4\langle x^7\rangle\), not \(t^4m_7\).**  
   The unlocalised odd-moment theorem supplies the former’s boundedness. It does not directly supply a localised bound; that would require a numerator/denominator transfer.

2. **The quoted seventh-moment coefficient appears wrong.**  
   With the normalization consistent with the supplied \(c_5\) and \(C_4\),
   \[
   \ell(x)=\frac{\lambda x^2}{2}
          +\frac{\alpha x^3}{6}
          +\frac{\gamma x^4}{24},
   \]
   the leading seventh moment is
   \[
   t^4\langle x^7\rangle
   \longrightarrow
   -\frac{\alpha}{6}\frac{9!!}{\lambda^5}
   =-\frac{945\alpha}{6\lambda^5},
   \]
   **not** \(-105\alpha/(6\lambda^5)\). Check the actual theorem’s indexing and statement. A and B only need boundedness here, so this coefficient typo need not block them.

For Lean, also arrange a common threshold \(t\ge1\), \(D\ge1/2\), and the explicit nonzero hypotheses needed by denominator algebra.

## 3. Wording against E3/Setup

The derivative reading is fair **for the exact, fixed-localiser Gibbs measure and the observables actually proved**:
\[
\operatorname{Cov}_{\mathrm{loc},t}(\ell,f)
=-\partial_t\langle f\rangle_{\mathrm{loc},t}.
\]
Your moment and covariance expansions independently establish the corresponding coefficient identities.

I would phrase the result as:

> For the fixed isotropic localiser, the localised covK expansions for linear and quadratic raw probes agree through the \(t^{-3}\) covariance term with the coefficientwise negative \(t\)-derivatives of their expectation expansions. Their scaled \(1/t\) coefficients are \(2c'\) and \(2c_2'\).

Three qualifications matter:

- **Do not justify the rate by differentiating an \(O(t^{-3})\) remainder.** That operation is not valid without derivative control. The Stein reduction and moment estimates supply the rigorous result.
- **The localiser already enters the leading linear coefficient**, through \(c=-\alpha/(2\lambda^2)+a/\lambda\). It does not enter *only* at second order.
- **Raw second moment is not centred covariance.** If the note’s eq:cov denotes variance, then
  \[
  \operatorname{Var}_{\mathrm{loc}}(x)
  =\frac b t+\frac{c_2'-c^2}{t^2}+O(t^{-3}),
  \]
  and its negative derivative has scaled \(1/t\) coefficient
  \[
  2(c_2'-c^2),
  \]
  not \(2c_2'\). Equivalently, include the correction
  \[
  -\partial_t\operatorname{Var}(x)
  =\operatorname{Cov}(\ell,x^2)-2m_1\operatorname{Cov}(\ell,x).
  \]

This supports a precise second-order consistency statement for the quartic/product model. It does not, by itself, establish a general E3 theorem or justify differentiating arbitrary Laplace expansions.

## 4. D: correct, with the usual quadratic-probe convention

For \(i\ne j\), factorisation gives
\[
t^2\operatorname{Cov}(L,u_i u_j)
=m_j\bigl[t^2\operatorname{Cov}_i(\ell_i,x)\bigr]
+m_i\bigl[t^2\operatorname{Cov}_j(\ell_j,x)\bigr].
\]
Since
\[
m_i=\frac{c_i}{t}+O(t^{-2}),\qquad
t^2\operatorname{Cov}_i(\ell_i,x)=c_i+O(t^{-1}),
\]
this yields
\[
\boxed{
t^2\operatorname{Cov}(L,u_i u_j)
=\frac{2c_ic_j}{t}+O(t^{-2}).}
\]
Only leading rates are needed for this pair calculation.

For
\[
\psi(u)=\frac12u^\top\widetilde B u+\widetilde b^\top u,
\]
the proposed coefficient is therefore correct:
\[
C'_{\mathrm{loc}}
=\sum_i\left(\widetilde B_{ii}c'_{2,i}
                 +2\widetilde b_i c'_i\right)
+\sum_{i\ne j}\widetilde B_{ij}c_ic_j.
\]
The last sum is over **ordered** pairs; for symmetric \(\widetilde B\), it equals \(2\sum_{i<j}\widetilde B_{ij}c_ic_j\). These are raw quadratic probes, not centred cross-covariances.

D is worth having, but I would not let frame assembly crowd out the sharper fifth-moment lemma and the corrected C bookkeeping.

**Vote: approve A–C with the two proof corrections and the seventh-moment coefficient audit; bundle D only if the existing assembly makes it genuinely cheap.**