## 1. Symbolic verification

Write

\[
\varepsilon=t^{-1/2},\qquad
A=\frac{\alpha}{6\lambda^{3/2}},\qquad
B=\frac{\gamma}{24\lambda^2}.
\]

Indeed, under \(x=u/\sqrt{\lambda t}\),

\[
tV(x)
=\frac{u^2}{2}
+\frac{\alpha}{6\lambda^{3/2}}\frac{u^3}{\sqrt t}
+\frac{\gamma}{24\lambda^2}\frac{u^4}{t}.
\]

Thus the factorial normalizations are exactly

\[
A=\operatorname{cubicScale}(\lambda,\alpha)
=\frac{\alpha}{6\lambda^{3/2}},
\quad
B=\operatorname{quarticScale}(\lambda,\gamma)
=\frac{\gamma}{24\lambda^2}.
\]

### 1(a). Expansion of \(J_n\)

With \(s=A u^3\varepsilon+B u^4\varepsilon^2\),

\[
e^{-s}
=
1-Au^3\varepsilon
+\left(\frac{A^2}{2}u^6-Bu^4\right)\varepsilon^2
+O(\varepsilon^3).
\]

Hence

\[
J_n
=
m_n-Am_{n+3}\varepsilon
+\left(\frac{A^2}{2}m_{n+6}-Bm_{n+4}\right)\varepsilon^2
+O(\varepsilon^3).
\]

This is exactly the proposed coefficient.

If the literal relative \(t^{-1}\) corrections for odd Gibbs moments are wanted, one further term is needed:

\[
J_n
=
\cdots+
\left(ABm_{n+7}-\frac{A^3}{6}m_{n+9}\right)\varepsilon^3
+O(\varepsilon^4).
\]

For the fourth-cumulant limit, this third-order odd term is not needed.

---

### 1(b). Ratios and Gibbs moments

Let

\[
g_n=\frac{m_n}{m_0},
\qquad
g_0=1,\ g_2=1,\ g_4=3,\ g_6=15,\ g_8=105,\ g_{10}=945.
\]

Since

\[
\frac{J_0}{m_0}
=
1+\left(\frac{15}{2}A^2-3B\right)\varepsilon^2+O(\varepsilon^4),
\]

one obtains

\[
\frac{J_n}{J_0}
=
g_n-Ag_{n+3}\varepsilon
+
\left[
\frac{A^2}{2}(g_{n+6}-g_ng_6)
-B(g_{n+4}-g_ng_4)
\right]\varepsilon^2
+O(\varepsilon^3).
\]

In particular,

\[
\frac{J_2}{J_0}
=
1+(45A^2-12B)\varepsilon^2+o(\varepsilon^2),
\]

\[
\frac{J_4}{J_0}
=
3+(450A^2-96B)\varepsilon^2+o(\varepsilon^2),
\]

and the needed odd leading terms are

\[
\frac{J_1}{J_0}=-3A\varepsilon+o(\varepsilon),
\qquad
\frac{J_3}{J_0}=-15A\varepsilon+o(\varepsilon).
\]

Since

\[
\langle x^r\rangle
=(\lambda t)^{-r/2}\frac{J_r}{J_0},
\]

the required moment expansions are

\[
\boxed{
\langle x\rangle
=
-\frac{3A}{\sqrt\lambda}\,t^{-1}
+o(t^{-1})
}
\]

\[
\boxed{
\langle x^2\rangle
=
\frac1\lambda t^{-1}
+\frac{45A^2-12B}{\lambda}t^{-2}
+o(t^{-2})
}
\]

\[
\boxed{
\langle x^3\rangle
=
-\frac{15A}{\lambda^{3/2}}t^{-2}
+o(t^{-2})
}
\]

\[
\boxed{
\langle x^4\rangle
=
\frac3{\lambda^2}t^{-2}
+\frac{450A^2-96B}{\lambda^2}t^{-3}
+o(t^{-3})
}.
\]

The first one reproduces the existing result:

\[
-\frac{3A}{\sqrt\lambda}
=
-\frac{\alpha}{2\lambda^2}.
\]

For completeness, the literal relative-\(t^{-1}\) corrections to the odd moments are

\[
\langle x\rangle
=
\lambda^{-1/2}
\left[
-3A\,t^{-1}
+(96AB-135A^3)t^{-2}
+o(t^{-2})
\right],
\]

\[
\langle x^3\rangle
=
\lambda^{-3/2}
\left[
-15A\,t^{-2}
+(900AB-1620A^3)t^{-3}
+o(t^{-3})
\right].
\]

These require the cubic-in-\(\varepsilon\) expansion of \(J_1,J_3\), but should not be made dependencies of the minimal \(\kappa_4\) proof.

---

### 1(c). Fourth-cumulant cancellation

Define raw moments \(\mu_r=\langle x^r\rangle\). Then

\[
\kappa_4
=
\mu_4-4\mu_3\mu_1-3\mu_2^2
+12\mu_2\mu_1^2-6\mu_1^4.
\]

At order \(t^{-2}\),

\[
\mu_4-3\mu_2^2
=
\frac3{\lambda^2}t^{-2}
-\frac3{\lambda^2}t^{-2}
+O(t^{-3}),
\]

so the Gaussian term cancels.

At order \(t^{-3}\), after factoring out \(\lambda^{-2}\), the contributions are:

\[
\begin{array}{c|c}
\text{term}&t^{-3}\text{ coefficient}\\ \hline
\mu_4 & 450A^2-96B\\
-4\mu_3\mu_1 & -180A^2\\
-3\mu_2^2 & -270A^2+72B\\
12\mu_2\mu_1^2 & 108A^2\\
-6\mu_1^4 & 0
\end{array}
\]

Therefore

\[
t^3\kappa_4
\longrightarrow
\frac{108A^2-24B}{\lambda^2}.
\]

Substitution gives

\[
\frac{108}{\lambda^2}
\frac{\alpha^2}{36\lambda^3}
-
\frac{24}{\lambda^2}
\frac{\gamma}{24\lambda^2}
=
\boxed{
-\frac{\gamma}{\lambda^4}
+\frac{3\alpha^2}{\lambda^5}
}.
\]

So the normalization and the target are correct.

For \((\lambda,\alpha,\gamma)=(1.3,0.4,0.9)\), this is approximately

\[
-0.1858371,
\]

matching the reported numerical convergence.

---

## 2. Two-sided exponential remainder

The clean statement is the endpoint-maximum form:

\[
\boxed{
\left|
e^{-s}-\sum_{j=0}^{n-1}\frac{(-s)^j}{j!}
\right|
\le
\frac{|s|^n}{n!}\max(1,e^{-s})
}
\qquad(s\in\mathbb R).
\]

This follows directly from Taylor's integral remainder or the mean-value form: the exponential derivative on the interval between \(0\) and \(-s\) is bounded by

\[
\max(e^0,e^{-s})=\max(1,e^{-s}).
\]

A likely Lean-facing statement is conceptually:

```lean
theorem abs_expRemainder_le
    (n : ℕ) (s : ℝ) :
    |expRemainder n s|
      ≤ |s| ^ n / n.factorial * max 1 (Real.exp (-s))
```

with the usual casts adjusted to the repository's definition.

This is substantially preferable to

\[
e^{|s|}\frac{|s|^n}{n!}.
\]

The latter is true but analytically toxic here: for a quartic \(s_t\), the factor \(e^{|s_t|}\) can introduce a growing positive quartic exponential, which is not Gaussian-integrable. In contrast,

\[
e^{-u^2/2}\max(1,e^{-s_t(u)})
=
\max\!\left(e^{-u^2/2},
e^{-u^2/2-s_t(u)}\right),
\]

which is exactly the two-branch domination already supported by the coercivity infrastructure.

For the second-order expansion, use \(n=3\):

\[
|\operatorname{remainder}|
\le
\frac{|s_t(u)|^3}{6}\max(1,e^{-s_t(u)}).
\]

After division by \(\varepsilon^3\),

\[
\frac{|s_t(u)|^3}{\varepsilon^3}
\le
\bigl(|A||u|^3+|B|\varepsilon|u|^4\bigr)^3,
\]

which is uniformly polynomially dominated for \(t\ge t_0>0\).

---

## 3. Suggested staging: six minimal tides

The numerical checks should be regression checks, not trusted proof ingredients. Exact coefficient identities can additionally be checked in Lean with `ring`/`norm_num`.

### Tide 1 — Two-sided scalar Taylor remainder

**Statements**

- General endpoint-max remainder theorem.
- Specializations for orders \(3\) and optionally \(4\).
- A helper rewriting the Gaussian-weighted maximum into the two domination branches.

**Check**

Evaluate the inequality externally for positive and negative \(s\), several \(n\), especially large negative \(s\). This catches the sign convention in `expRemainder`.

---

### Tide 2 — Second-order \(J_n\) asymptotics

Add a new theorem rather than changing the existing leading-order API:

\[
t\left(
J_n(t)-m_n+\frac{A m_{n+3}}{\sqrt t}
\right)
\longrightarrow
\frac{A^2}{2}m_{n+6}-Bm_{n+4}.
\]

Or equivalently use an \(\varepsilon\)-normalized statement.

Specialize immediately to \(n=0,2,4\). The generic theorem is useful, but only these three should be dependencies of the main line.

**Check**

For the pinned parameters, compare numerically

\[
t\left(J_n-m_n+\frac{Am_{n+3}}{\sqrt t}\right)
\]

against the predicted coefficient for \(n=0,2,4\).

**Repository policy**

Supplement `J_n_asymptotic`; do not strengthen it in place. Its present rate statement is already useful and likely has many downstream dependencies.

---

### Tide 3 — Ratio and moment coefficient lemmas

**Statements**

Prove the four asymptotic facts actually needed:

\[
t\langle x\rangle\to-\frac{3A}{\sqrt\lambda},
\]

\[
t^2\left(\langle x^2\rangle-\frac1{\lambda t}\right)
\to\frac{45A^2-12B}{\lambda},
\]

\[
t^2\langle x^3\rangle\to-\frac{15A}{\lambda^{3/2}},
\]

\[
t^3\left(\langle x^4\rangle-\frac3{\lambda^2t^2}\right)
\to\frac{450A^2-96B}{\lambda^2}.
\]

Reuse the existing odd \(J_1,J_3\) limits. Do not prove their next coefficients on the critical path.

**Check**

Check the coefficients against direct numerical Gibbs integration. In particular,

\[
t\langle x\rangle\to-\frac{\alpha}{2\lambda^2}
\]

should agree with the existing theorem, giving a valuable cross-check.

---

### Tide 4 — Fourth-cumulant definition and algebraic assembly

**Statements**

- Introduce `kappa4` as the explicit raw-moment polynomial.
- Prove a purely algebraic asymptotic assembly lemma whose inputs are the four moment limits above.
- Isolate the coefficient identity

\[
(450-180-270+108)A^2+(-96+72)B
=108A^2-24B.
\]

This tide should contain no integration.

**Check**

Use `ring` or `ring_nf` to verify

\[
\frac{108A^2-24B}{\lambda^2}
=
-\frac{\gamma}{\lambda^4}
+\frac{3\alpha^2}{\lambda^5}
\]

after unfolding \(A,B\). Also `norm_num` the rational pinned parameter instance.

---

### Tide 5 — Analytic \(\kappa_4\) theorem

**Statement**

Combine Tides 3 and 4:

\[
\boxed{
\operatorname{Tendsto}
\left(t\mapsto t^3\kappa_4(t)\right)
\operatorname{atTop}
\left(
-\frac{\gamma}{\lambda^4}
+\frac{3\alpha^2}{\lambda^5}
\right)
}.
\]

Keep the theorem's assumptions aligned with the actual coercivity/unique-minimum assumptions of the \(J_n\) infrastructure.

**Check**

Run the reported \(t=100,\ldots,6400\) regression and retain the table in a note or test script:

\[
-0.18591\ \longrightarrow\ -0.185839
\]

against \(-0.1858371\).

---

### Tide 6 — Gamma recovery

Assuming \(L\) is the observed fourth-cumulant limit,

\[
L=-\frac{\gamma}{\lambda^4}
+\frac{3\alpha^2}{\lambda^5},
\]

prove

\[
\boxed{
\gamma=-\lambda^4L+\frac{3\alpha^2}{\lambda}
}.
\]

Then package this with the existing \(\lambda\)- and \(\alpha\)-recovery statements as the jet-recovery corollary.

**Check**

At the pinned values, substitution of \(L\approx-0.1858371\) recovers \(\gamma\approx0.9\).

---

### Which lemmas to change?

I would use the following policy:

- **Leave unchanged**
  - `J_n_asymptotic`
  - `J_2_asymptotic`
  - `tendsto_sqrt_t_mul_J_1`
  - `tendsto_sqrt_t_mul_J_3`
  - existing mean/covariance rate theorems.

- **Add**
  - a generic second-order `J_n` limit;
  - specializations for \(J_0,J_2,J_4\);
  - ratio/moment coefficient theorems;
  - `kappa4` and its assembly theorem.

- **Optionally add later**
  - third-order odd \(J_1,J_3\) asymptotics, if the note wants complete relative-\(t^{-1}\) expansions of every moment. They are not needed for gamma recovery.

This avoids destabilizing the existing first-order API and keeps the new proof line narrowly scoped.

---

## 4. Biggest risk

The main conceptual risk is not the cumulant algebra. It is the global-minimum/coercivity hypothesis.

For

\[
V(x)=\frac{\lambda}{2}x^2+\frac{\alpha}{6}x^3+\frac{\gamma}{24}x^4
=
x^2\left(
\frac\lambda2+\frac\alpha6x+\frac\gamma{24}x^2
\right),
\]

mere quartic coercivity, such as \(\gamma>0\), does not guarantee that the Gibbs measure at large \(t\) is governed by the germ at \(x=0\). If \(V\) is lower elsewhere, the measure localizes at another well and the proposed asymptotics are false.

A natural strict sufficient condition is

\[
\lambda>0,\qquad \gamma>0,\qquad
\alpha^2<3\lambda\gamma,
\]

which makes the quadratic factor strictly positive and \(0\) the unique global minimizer. Equality is also delicate: it can create another zero/minimizer, so the single-germ Laplace expansion need not survive unchanged.

I would advise against the programme only if:

1. the current theorem assumptions allow competing or lower wells but the intended theorem is still stated as a global Gibbs limit; or
2. the existing domination infrastructure cannot expose a uniform two-branch bound for
   \[
   e^{-u^2/2}\max(1,e^{-s_t(u)}).
   \]

Otherwise the programme looks technically well-scoped. The new analytic burden is essentially one second-order \(J_n\) theorem; the rest is ratio bookkeeping and a clean algebraic assembly.