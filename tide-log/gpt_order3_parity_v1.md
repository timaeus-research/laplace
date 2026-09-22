## 1. Correctness of A–D

**A–D are mathematically correct under the existing decay hypotheses**, with constants allowed to depend on the fixed moment index and model parameters. The main correction is to the proposed generic ratio lemma in Question 3, not to A–D.

### A. Fourth-order integral remainder

Write \(A=\mathrm{cubicScale}(\lambda,\alpha)\), \(B=\mathrm{quarticScale}(\lambda,\gamma)\), and \(s=s_t(u)\). For \(t\ge1\),
\[
|s|^4
\le 8\left(\frac{A^4u^{12}}{t^2}+\frac{B^4u^{16}}{t^4}\right)
\le \frac{8(A^4+B^4)}{t^2}(u^{12}+u^{16}).
\]
Thus `abs_expRemainder_le_max 4` and `rescaled_max_decay` give
\[
\left|u^n e^{-u^2/2}
 \left(e^{-s}-1+s-\frac{s^2}{2}+\frac{s^3}{6}\right)\right|
\le
\frac{A^4+B^4}{3t^2}
 |u|^n(u^{12}+u^{16})e^{-c_0u^2}.
\]
The right-hand side is integrable. This proves A, including absolute integrability of the remainder integrand.

### B. Cubised decomposition and parity

The cubic identity is exactly
\[
s_t(u)^3=
\frac{A^3u^9}{t\sqrt t}
+\frac{3A^2Bu^{10}}{t^2}
+\frac{3AB^2u^{11}}{t^2\sqrt t}
+\frac{B^3u^{12}}{t^3}.
\]
Consequently, the additional terms contributed by \(-s_t^3/6\) are
\[
-\frac{A^3m_{n+9}}{6t\sqrt t}
-\frac{A^2Bm_{n+10}}{2t^2}
-\frac{AB^2m_{n+11}}{2t^2\sqrt t}
-\frac{B^3m_{n+12}}{6t^3}.
\]
Together with the quadratised decomposition, this gives precisely the proposed expansion:
\[
J_n=
m_n-\frac{A m_{n+3}}{\sqrt t}
-\frac{B m_{n+4}}t
+\frac{A^2m_{n+6}}{2t}
+\frac{ABm_{n+7}-A^3m_{n+9}/6}{t\sqrt t}
+O(t^{-2}).
\]

The four terms absorbed into the remainder have coefficients
\[
+\frac{B^2m_{n+8}}{2t^2},\quad
-\frac{A^2Bm_{n+10}}{2t^2},\quad
-\frac{AB^2m_{n+11}}{2t^2\sqrt t},\quad
-\frac{B^3m_{n+12}}{6t^3}.
\]
Their signs do not affect the bound, but these are the exact signs.

Both parity corollaries are correct:

- For even \(n\), all three half-integer-order terms displayed above vanish.
- For odd \(n\), \(m_n,m_{n+4},m_{n+6}\) vanish, leaving the stated odd expansion.

For Lean, corollaries indexed by `n = 2 * k` and `n = 2 * k + 1` may be cheaper than carrying general parity predicates.

The stronger odd remainder \(O(t^{-5/2})\) is consistent with parity, but **does not follow from A+B alone**: A bounds the unexpanded remainder only by \(O(t^{-2})\).

### C. Second moment and variance

The coefficient checks out. After normalization by \(J_0\),
\[
(-15B+\tfrac{105}{2}A^2)-(-3B+\tfrac{15}{2}A^2)
=45A^2-12B,
\]
so
\[
t\langle x^2\rangle
=\frac1\lambda+\frac{45A^2-12B}{\lambda t}+O(t^{-2}).
\]

Put \(\mu=-\alpha/(2\lambda^2)\). The existing mean estimate gives
\[
t\langle x\rangle=\mu+O(t^{-1}),
\]
and hence
\[
t\langle x\rangle^2
=\frac{(t\langle x\rangle)^2}{t}
=\frac{\mu^2}{t}+O(t^{-2}).
\]
The variance coefficient is therefore
\[
\frac{45A^2-12B}{\lambda}-\frac{\alpha^2}{4\lambda^4}
=\frac{\alpha^2}{\lambda^4}-\frac{\gamma}{2\lambda^3}.
\]

Multiplying the variance error by \(\lambda t\) gives the proposed relative-rate error \(O(t^{-1})\). Thus E7’s relative remainder after the one-loop correction is indeed \(O(t^{-2})\).

The fixed-dimensional separable and rotated forms follow by the same finite-sum and fixed-linear-map arguments as before, with constants adjusted.

### D. Energy, including the third-moment shortcut

**Yes: the sharper third-moment rate needs no new \(J_3\) expansion.**

Let \(g=\sqrt{2\pi}\). The existing delta estimate says
\[
J_3=-\frac{15Ag}{\sqrt t}+O(t^{-3/2}).
\]
Multiplication by \(\sqrt t\) gives
\[
\sqrt t\,J_3=-15Ag+O(t^{-1}).
\]
Together with \(J_0=g+O(t^{-1})\) and its eventual positive lower bound,
\[
t^2\langle x^3\rangle
=\frac{\sqrt t\,J_3}{\lambda^{3/2}J_0}
=-\frac{15A}{\lambda^{3/2}}+O(t^{-1})
=-\frac{5\alpha}{2\lambda^3}+O(t^{-1}).
\]

Likewise, the existing fourth-moment result already yields
\[
t^2\langle x^4\rangle=\frac3{\lambda^2}+O(t^{-1}),
\]
so division by \(t\) gives the desired statement.

Combining those estimates with **C’s sharpened second moment**,
\[
t\langle\ell\rangle
=\frac{\lambda}{2}t\langle x^2\rangle
+\frac{\alpha}{6}t\langle x^3\rangle
+\frac{\gamma}{24}t\langle x^4\rangle
=\frac12+\frac{5\alpha^2/(24\lambda^3)-\gamma/(8\lambda^2)}t
+O(t^{-2}).
\]

Thus D’s new third- and fourth-moment ingredients use existing results, but its final energy estimate depends on C’s second-moment improvement.

## 2. Best shape for A

**Use the direct fourth-power bound.** It has the cleanest polynomial envelope and matches `abs_expRemainder_le_max 4` directly.

A useful elementary proof of the real inequality is
\[
(x+y)^2\le2(x^2+y^2),\qquad
(x^2+y^2)^2\le2(x^4+y^4).
\]
Squaring the first inequality and applying the second gives
\[
(x+y)^4\le8(x^4+y^4).
\]
This avoids needing a special-purpose fourth-power inequality from Mathlib.

The suggested cubic-bound route is also valid, however. For example,
\[
|s_t(u)|\le
\frac{|A||u|^3+|B|u^4}{\sqrt t}
\qquad(t\ge1).
\]
Multiplying this by the existing bound on \(|s_t(u)|^3\) produces a polynomial-in-\(|u|\) envelope times \(t^{-2}\).

**Uniformity of that extra factor in \(u\) is unnecessary.** What is required is a \(t\)-independent, Gaussian-integrable polynomial envelope. So the objection in the question is too strong.

The downside is proof shape: this route creates more terms and odd absolute powers. Also, one should use it to bound \(|s|^4\), then apply the fourth-order exponential remainder theorem—not assume a relation between the third- and fourth-order remainder functions.

## 3. Ratio organization: useful, but correct the generic statement

The proposed lemma with only \(r(t)\ge t\) is **false**. Division creates an intrinsic \(t^{-2}\) term, even if the inputs have zero remainder.

For example, take
\[
X=1,\qquad Y=1+\frac1t.
\]
Both input expansions are exact, but
\[
\frac XY-\left(1-\frac1t\right)=\frac1{t(t+1)},
\]
which is not \(O(t^{-3})\). Thus \(r(t)=t^3\) is a counterexample.

### Correct general form

Under the proposed assumptions, the general conclusion is
\[
\left|\frac XY-\frac ac-\frac{bc-ad}{c^2t}\right|
\le \frac{K_1}{r(t)}+\frac{K_2}{t^2}
\]
eventually. A single \(K''/r(t)\) bound follows if, additionally,
\[
r(t)\le C t^2
\]
eventually.

The exact identity makes a compact Lean proof possible. Set
\[
p=\frac ac,\qquad q=\frac{bc-ad}{c^2},
\]
and write \(X=a+b/t+e_X\), \(Y=c+d/t+e_Y\). Then
\[
X-(p+q/t)Y
=e_X-(p+q/t)e_Y-\frac{qd}{t^2}.
\]
Once \(Y\ge c/2\), division and the triangle inequality finish the proof.

### Recommended implementation

For this tide, prove a **specialized \(t^{-2}\) ratio lemma**, preferably accepting an eventual denominator lower bound so it can reuse `J_0_eventually_bounded`. It avoids the extra infrastructure of an arbitrary rate function.

Then:

- specialize B’s even corollary to obtain the \(J_0,J_2\) input estimates;
- apply the ratio lemma once;
- perform the scaling and coefficient normalization.

You still need those specialized delta facts mathematically, but they become short applications rather than duplicated analytic proofs.

For D’s third moment, a simpler quotient-stability lemma suffices: numerator \(a+O(t^{-1})\), denominator \(c+O(t^{-1})\), \(c>0\).

## 4. Scope and vote

**A+B+C is one coherent tide.** It has a clean dependency chain:
\[
\text{fourth-order domination}
\;\longrightarrow\;
\text{parity-improved }J_n
\;\longrightarrow\;
\text{sharp normalized variance}.
\]
Its endpoint is exactly E7’s claimed rate.

D is a sensible stretch, not a separate analytical project: once C exists, the scalar energy result mainly needs the corrected third-moment quotient argument and assembly. The separable/rotated wrappers can nevertheless make its formalization footprint larger than its mathematical novelty suggests.

I would sharpen the plan by:

1. exposing A’s integrable pointwise envelope for reuse;
2. stating B’s parity corollaries with explicit even/odd indices;
3. adding a specialized \(t^{-2}\) ratio lemma;
4. recording explicitly that D’s energy result depends on C.

**Vote: A+B+C, with D as a stretch rather than an acceptance requirement.**