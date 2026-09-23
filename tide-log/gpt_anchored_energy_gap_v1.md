## 1. Correctness of A–C

**Yes, under the intended hypotheses:** \(H\) is positive definite, \(U\) is orthogonal with \(U^\top HU=\operatorname{diag}(\lambda_i)\), \(g\ge 0\), \(t>0\), and \(v\) is fixed. Write \(a=U^\top v\).

### A: exact anchored Gaussian energy

The inverse conjugation identity gives
\[
U^\top m=\left(\frac{a_i}{t\lambda_i+g}\right)_i,
\qquad m=(tH+gI)^{-1}v,
\]
and hence
\[
m^\top Hm=\sum_i\frac{\lambda_i a_i^2}{(t\lambda_i+g)^2}.
\]
Thus, for the **quadratic surrogate energy**,
\[
\boxed{\mathcal E_t^{\rm anch}
=\frac12\sum_i\frac{t\lambda_i}{t\lambda_i+g}
+\frac t2\sum_i\frac{\lambda_i a_i^2}{(t\lambda_i+g)^2}.}
\]

For Lean, proving the displayed coordinate identity for \(U^\top m\) first may be simpler than establishing a general quadratic-form conjugation lemma.

### B: expansion and bounds

With
\[
A=\sum_i\frac{a_i^2}{2\lambda_i},
\qquad G=\sum_i\frac{g}{2\lambda_i},
\]
the expansion is indeed
\[
\boxed{\mathcal E_t^{\rm anch}
=\frac d2+\frac{A-G}{t}+O(t^{-2}).}
\]

Your proposed per-term bound is correct for \(t\ge1\), but there is a **stronger, simpler bound valid for every \(t>0\)**:
\[
\boxed{
\left|\frac{t\lambda a^2}{(t\lambda+g)^2}
-\frac{a^2}{\lambda t}\right|
\le \frac{2a^2g}{\lambda^2t^2}.
}
\]
Consequently, you can use the explicit constant
\[
K_{\rm anch}=\sum_i\frac{g^2/2+a_i^2g}{\lambda_i^2}
\]
in
\[
\left|\mathcal E_t^{\rm anch}-\frac d2-\frac{A-G}{t}\right|
\le \frac{K_{\rm anch}}{t^2}.
\]
If your rate convention requires a strictly positive constant, take \(K_{\rm anch}+1\).

### C: gap and coefficient

Let \(E_1=\sum_i e_{1i}\). Subtracting B from the landed exact-energy expansion gives
\[
t\langle L\circ A\rangle_{\rm loc}-\mathcal E_t^{\rm anch}
=\frac{E_1-A+G}{t}+O(t^{-2}).
\]
Therefore
\[
\boxed{
C_1'
=\sum_i\left(e_{1i}+\frac g{2\lambda_i}
-\frac{a_i^2}{2\lambda_i}\right)
=\sum_i\left(e_{0i}-\frac{a_i\alpha_i}{2\lambda_i^2}\right).
}
\]
The sign agrees with tide 94. The energy-gap remainder constant can simply be the sum of the exact-energy and Gaussian-energy constants.

## 2. Recommended route and generality

**Reuse `inv_shift_rate` for both Gaussian terms.** No cubic-denominator estimate is needed.

Set \(x=t\lambda>0\), \(q=1/(x+g)\), and \(r=1/x\). Then
\[
0<q\le r,\qquad |q-r|\le \frac g{x^2}.
\]

For the trace contribution:
\[
\left|\frac{x}{x+g}-1+\frac gx\right|
=g|r-q|\le \frac{g^2}{x^2}.
\]

For the mean contribution, use \(xr^2=r\):
\[
\begin{aligned}
|xa^2q^2-a^2r|
&=xa^2|q-r|(q+r)\\
&\le xa^2\frac g{x^2}\frac2x
=\frac{2a^2g}{x^2}.
\end{aligned}
\]
This is a small scalar lemma plus finite-sum bookkeeping. It avoids the \(t\ge1\) assumption and the extra \(g/\lambda^3\) term.

**Keep the Sampler theorem general in \(v\).** Its mathematical content is Gaussian linear algebra, independent of the E2 anchoring convention. In the E2 application, specialize to
\[
v=g\,w_0,\qquad w_0=Uu_0,\qquad U^\top v=g\,u_0.
\]
Prose is sufficient for exposition, but the actual bridge to C must of course prove this coordinate identification. A tiny specialization lemma is worthwhile if it avoids repeated matrix simplification.

## 3. Packaging, and the variance question

### “Two gaps, one coefficient”

This is worth highlighting, but I would prioritize **one canonical coefficient and two separately usable rate theorems**, rather than a conjunction theorem.

- If tide 94 already names the coefficient, reuse that name.
- If it uses an inline sum and changing it is cheap, introduce one shared definition, preferably in the common coefficient layer.
- Otherwise, keep the same sum and use a coefficient-identification lemma. Do not introduce parallel “transform” and “energy” definitions.

A conjunction theorem is optional downstream packaging. It can combine eventual thresholds by `max`, but contributes little mathematical content and may pull transform-specific hypotheses into an otherwise simpler energy API.

### Variance

Your anticipated coefficient is correct, with the scaling stated explicitly. For
\[
Q(u)=\tfrac12u^\top Hu,
\]
the proposed Gaussian formula yields
\[
\operatorname{Var}_{\rm anch}(tQ)
=\frac d2+\frac{2(A-G)}t+O(t^{-2}).
\]
Thus, if the landed exact variance theorem has coefficient \(2E_1\), then
\[
\operatorname{Var}_{\rm loc}(tL)
-\operatorname{Var}_{\rm anch}(tQ)
=\frac{2C_1'}t+O(t^{-2}),
\]
or equivalently
\[
\boxed{
\operatorname{Var}_{\rm loc}(L)
-\operatorname{Var}_{\rm anch}(Q)
=\frac{2C_1'}{t^3}+O(t^{-4}).
}
\]

**It is not an immediate consequence of the listed landed material.** The Gaussian side needs a fourth-moment identity or an independently justified parameter-differentiation theorem. An exact transform can provide another route, but only with the analytic justification identifying derivatives with moments. Neither the fixed-\(s\) transform remainder nor the Gaussian mean-energy formula alone supplies that bridge. Defer D this tide.

## 4. Wording against E3

Your interpretation is fair with three qualifications:

1. **Make the discrepancy signed and include the remainder.** “Misses by” can sound like a positive error.
2. **“Purely anharmonic” means it vanishes for a purely quadratic loss.** It does not mean independent of the anchor: the term \(-a_i\alpha_i/(2\lambda_i^2)\) explicitly couples anchoring and anharmonicity.
3. **Do not transfer the centred prediction’s shrinkage claim to the full anchored prediction.** The positive mean-energy term can put the anchored prediction above \(d/2\).

Suggested wording:

> For fixed \(g\) and anchor \(u_0\), the anchored Gaussian quadratic-energy prediction is the centred trace prediction plus \((t/2)m^\top Hm\). The exact localised LLC minus this anchored prediction is \(C_1'/t+O(t^{-2})\), where \(C_1'\) vanishes for a purely quadratic loss. Against the centred prediction, the corresponding coefficient is \(C_1=C_1'+A\). Thus the anchor’s mean-energy term accounts for exactly \(A\) of the first-order centred discrepancy.

Here \(A\) is its **first-order coefficient**, not the finite-\(t\) mean-energy term itself. Also retain the hypotheses and localisation regime of the landed E2 theorem; general-\(v\) Gaussian algebra does not automatically generalize that theorem.

For \(d=0\), all displayed sums are empty and the Gaussian statements remain valid without a separate nonempty-dimension assumption.

**Vote: A–C, with the sharper reciprocal-factorization proof of B, one shared coefficient identity, and D deferred.**