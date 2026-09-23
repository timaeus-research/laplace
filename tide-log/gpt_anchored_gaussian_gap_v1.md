## 1. Correctness: yes, with one wording qualification

Write
\[
k=1+s>0,\qquad
A=\sum_i\frac{a_i^2}{2\lambda_i},\qquad
G=\sum_i\frac{g}{2\lambda_i},\qquad
E=\sum_i e_{1i}.
\]
For the simple bounds below, assume \(t>0\), \(\lambda_i>0\), and \(g\ge0\). The asymptotic formulas also hold for fixed negative \(g\), but require different eventual denominator bounds.

**A′ is correct.** Multiplication by the quadratic exponential changes the precision but leaves the tilt unchanged:
\[
\Lambda=\frac{Z(Q+cH,v)}{Z(Q,v)}
=\exp\!\left(\frac12v^\top\big((Q+cH)^{-1}-Q^{-1}\big)v\right)
 \frac{\sqrt{\det Q}}{\sqrt{\det(Q+cH)}}.
\]
Both precisions must be positive definite. The exponent’s sign is correct: when \(cH\succeq0\), it is nonpositive.

**A″ is correct**, with \(a=U^\top v\):
\[
x_t=\frac12\sum_i a_i^2
 \left(\frac1{kt\lambda_i+g}-\frac1{t\lambda_i+g}\right)
=-\frac12\sum_i
 \frac{a_i^2st\lambda_i}{(t\lambda_i+g)(kt\lambda_i+g)}.
\]
Thus \(\Lambda^{G,\mathrm{anch}}=\Lambda^G e^{x_t}\).

**B is correct:**
\[
\Lambda^{G,\mathrm{anch}}
=k^{-d/2}\left(1+\frac{s(G-A)}{kt}\right)+O(t^{-2}).
\]

**C is correct:**
\[
\Lambda-\Lambda^{G,\mathrm{anch}}
=-k^{-d/2}\frac{sC_1'}{kt}+O(t^{-2}),\qquad
C_1'=E+G-A.
\]
The pointwise coefficient identity is exactly
\[
e_1+\frac g{2\lambda}-\frac{a^2}{2\lambda}
=\frac{5\alpha^2}{24\lambda^3}
 -\frac{\gamma}{8\lambda^2}
 -\frac{a\alpha}{2\lambda^2}
=e_0-\frac{a\alpha}{2\lambda^2}.
\]

**Qualification:** “captures every localiser effect” is too strong literally. The residual still depends on the localiser through \(a=g u_0\). What it captures is **every purely Gaussian localiser contribution** at this order. “Purely anharmonic residual” is appropriate if explained as “every residual term contains an anharmonic coefficient”; it does not mean “independent of the localiser.”

## 2. Bundle and proof route

### B: your route is good; use a reciprocal remainder first

A particularly simple scalar identity is
\[
\frac1{bt+g}-\frac1{bt}
=-\frac{g}{bt(bt+g)},\qquad b>0,
\]
hence, for \(g\ge0\),
\[
\left|\frac1{bt+g}-\frac1{bt}\right|
\le \frac{g}{b^2t^2}.
\]
Applying it separately with \(b=k\lambda_i\) and \(b=\lambda_i\) gives
\[
\left|x_t+\frac{sA}{kt}\right|\le\frac R{t^2},
\qquad
R=\sum_i\frac{ga_i^2}{2\lambda_i^2}(1+k^{-2}).
\]
This deliberately loose bound avoids expanding a product of denominators.

Separately, the exact difference-of-reciprocals identity gives
\[
|x_t|\le\frac{|s|A}{kt}.
\]
Thus \(t\ge\max(1,|s|A/k)\) suffices for \(|x_t|\le1\). Set \(b=-sA/k\). The exponential lemma then yields directly
\[
\left|e^{x_t}-1-\frac bt\right|
\le |e^{x_t}-1-x_t|+\left|x_t-\frac bt\right|
\le\frac{b^2+R}{t^2}.
\]

Combine this with tide 93’s centred expansion using the existing product rule. A two-factor specialization is worth adding only if the finite-product interface is cumbersome.

A reusable helper of the form **“first-order rate for an exponent implies first-order rate for its exponential”** would be a useful small addition, but is not necessary for this tide.

### A″: general tilt, then specialize

State A″ for **general \(v\)** and derive the \(v=g\,w_0\) version as a corollary. The proof is no harder, and this keeps the spectral calculation independent of the localiser.

Your conjugation identity is the right tool. I would package the intermediate result
\[
v^\top(rH+gI)^{-1}v
=\sum_i\frac{(U^\top v)_i^2}{r\lambda_i+g},
\]
under the relevant positivity hypotheses, and apply it at \(r=t\) and \(r=kt\).

The proof can be:
1. put \(a=U^\top v\);
2. use orthogonality to obtain \(v=Ua\);
3. rewrite the quadratic form as \(a^\top[U^\top(rH+gI)^{-1}U]a\);
4. apply `orthoOf_transpose_localised_inv_mul`;
5. simplify the diagonal quadratic form to a sum.

This avoids trace machinery. I would not rely on an unverified theorem name for the whole conjugation step; elementary `mulVec`/`dotProduct` associativity and transpose identities suffice.

Finally, make the coordinate identification explicit: the E2 specialization needs
\[
(U^\top v)_i=g\,u_{0i}
\]
in the same frame used by the E2 coefficient data.

## 3. Nearby results: energy, packaging, and the Gaussian law

### Energy: the coefficient is also \(C_1'\)

There is an extra-\(t\) typo in the proposed expression. The anchored Gaussian **scaled energy** is
\[
\mathcal E^{G,\mathrm{anch}}_t
=\frac t2\operatorname{tr}\!\big(H(tH+gI)^{-1}\big)
 +\frac t2m^\top Hm,
\]
not \(t\big(\frac12\operatorname{tr}(\cdots)+\frac t2m^\top Hm\big)\).

In eigen-coordinates,
\[
\mathcal E^{G,\mathrm{anch}}_t
=\frac12\sum_i\frac{t\lambda_i}{t\lambda_i+g}
 +\frac t2\sum_i\frac{\lambda_i a_i^2}{(t\lambda_i+g)^2}
=\frac d2+\frac{A-G}{t}+O(t^{-2}).
\]
Consequently, using the E2 energy expansion
\[
t\langle L\rangle=\frac d2+\frac E t+O(t^{-2}),
\]
the gap is
\[
t\langle L\rangle-\mathcal E^{G,\mathrm{anch}}_t
=\frac{C_1'}t+O(t^{-2}).
\]

**Important formalisation warning:** do not derive this by differentiating the landed fixed-\(s\) transform remainder. A pointwise-in-\(s\) \(O(t^{-2})\) estimate does not control its derivative. Use the existing energy theorem and expand the exact Gaussian energy independently. The derivative calculation is a consistency check.

If “three gaps” means transform, mean, and variance, the expected variance coefficient is \(2C_1'\):
\[
\operatorname{Var}(tL)-\operatorname{Var}_G(tL)
=\frac{2C_1'}t+O(t^{-2}).
\]
But that requires its own moment/remainder theorem or suitable derivative control; it is not a free consequence of this tide’s fixed-\(s\) estimates.

### Noncentral-\(\chi^2\) interpretation

Exactly,
\[
tL_G\ \overset d=\ 
\frac12\sum_i\frac{t\lambda_i}{t\lambda_i+g}
\left(Z_i+\frac{a_i}{\sqrt{t\lambda_i+g}}\right)^2,
\]
with independent standard normal \(Z_i\). This is a **weighted sum of independent noncentral \(\chi^2_1\) variables**, not generally one ordinary noncentral \(\chi^2\). Its Laplace transform is precisely A″.

This is useful explanatory packaging, but formalising the distributional statement would expand the tide considerably.

## 4. Recommended E2/E3 wording

I would use:

> E3’s anchored Gaussian prediction has the correct leading localised transform and captures all purely Gaussian localiser contributions at order \(1/t\). Its remaining first-order discrepancy is governed by
> \[
> C_1'=\sum_i\left(e_{0i}-\frac{a_i\alpha_i}{2\lambda_i^2}\right),
> \]
> an anharmonic coefficient that includes a cubic–anchor interaction. The centred prediction has instead \(C_1=C_1'+\sum_i a_i^2/(2\lambda_i)\), because it omits the nonzero Gaussian mean.

Two qualifications:
- Avoid “agrees through order \(1/t\)” unless \(C_1'=0\).
- At \(a=0\), the coefficient reduces to \(\sum e_{0i}\). For a genuinely quadratic model, the anchored Gaussian prediction is exact; merely setting the displayed cubic and quartic jets to zero establishes cancellation of this first-order coefficient, not global exactness.

**Vote: bundle A′ + A″ for general \(v\), then B + C in the E2 frame, including the coefficient-normal-form lemma.** Add the anchored energy corollary if the existing E2 energy rate theorem makes it short; defer distributional and variance packaging.