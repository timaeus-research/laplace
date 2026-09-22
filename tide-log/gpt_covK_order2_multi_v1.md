## 1. Correctness of A, B, C, and the coefficient

**A, B, and C are correct**, provided the bounds are understood for all sufficiently large positive \(t\). Two qualifications: the \(2\sum_{i<j}\) presentation assumes \(\widetilde B\) is symmetric, and D needs a non-cancellation qualification.

### Independent check of the off-diagonal coefficient

Put
\[
m_i(t)=\langle x\rangle_i,\qquad v_i(t)=\operatorname{Cov}_i[\ell_i,x].
\]
The supplied one-dimensional estimates give
\[
m_i(t)=\frac{a_i}{t}+O(t^{-2}),\qquad
v_i(t)=\frac{a_i}{t^2}+O(t^{-3}).
\]
Thus, for \(i\ne j\), the exact identity gives
\[
\begin{aligned}
\operatorname{Cov}[L,u_i u_j]
 &=m_jv_i+m_iv_j\\
 &=\frac{2a_i a_j}{t^3}+O(t^{-4}).
\end{aligned}
\]
Hence A’s scaled coefficient is indeed **\(2a_i a_j\)**.

Since the quadratic probe has coefficient \(\widetilde B_{ij}/2\) in the **ordered-pair** sum, its off-diagonal contribution to \(C'\) is
\[
\sum_{i\ne j}\widetilde B_{ij}a_i a_j.
\]
For symmetric \(\widetilde B\), this equals \(2\sum_{i<j}\widetilde B_{ij}a_i a_j\). Without symmetry, the unordered-pair version is
\[
\sum_{i<j}(\widetilde B_{ij}+\widetilde B_{ji})a_i a_j.
\]
The ordered-pair formula works without assuming symmetry; the skew part automatically contributes zero.

### Assembled coefficient and remainder orders

The coefficient is therefore
\[
\boxed{
C'=\sum_i\left(
\frac{\widetilde B_{ii}}2 C'_{\mathrm{sq},i}
+\widetilde b_i C'_{\mathrm{lin},i}
\right)
+\sum_{i\ne j}\widetilde B_{ij}a_i a_j.
}
\]
All three remainder orders are correct:
\[
t^2\operatorname{Cov}=C+\frac{C'}t+O(t^{-2}),
\]
\[
\operatorname{Cov}=\frac C{t^2}+\frac{C'}{t^3}+O(t^{-4}),
\]
and, when \(C\ne0\),
\[
\frac{\operatorname{Cov}}{\operatorname{covKFormula}}
=1+\frac{C'}{C\,t}+O(t^{-2}).
\]
The relative remainder constant can be taken as the scaled remainder constant divided by \(|C|\).

### Best presentation of the closed form

For Lean, retain
\[
\sum_{i\ne j}\widetilde B_{ij}a_i a_j
=a^\top\widetilde Ba-\sum_i\widetilde B_{ii}a_i^2.
\]
It avoids choosing an order on \(\iota\) and matches the existing pair sum.

For exposition, a nicer ambient presentation uses the **time-independent mean-shift coefficient**
\[
m=Qa,\qquad q_i=Qe_i.
\]
Then the off-diagonal correction is
\[
m^\top Bm-\sum_i a_i^2q_i^\top Bq_i.
\]
Using \(\mu=m/t\) is equivalent, but unnecessarily introduces \(t\) into a constant coefficient.

An especially clean presentation of the **whole coefficient** is
\[
\boxed{
C'=m^\top Bm+\operatorname{tr}(BS)+b^\top r,
}
\]
where
\[
S=Q\,\operatorname{diag}\!\left(\frac{C'_{\mathrm{sq},i}}2-a_i^2\right)Q^\top,
\qquad
r=Q(C'_{\mathrm{lin},i})_i.
\]
Here \(S\) is the second-order coefficient of the centered covariance matrix. This makes the mean-product contribution explicit. The diagonal/off-diagonal decomposition itself remains relative to the chosen separable frame; it is not invariant under arbitrary changes of eigenbasis.

## 2. Remainder-bookkeeping pitfalls

The proposed approach is sound. I would make these conditions explicit:

- **Require \(t\ge1\)** in the abstract product lemma, and nonnegative rate constants. Writing \(X=a+\delta_X\), \(Y=b+\delta_Y\),
  \[
  |XY-ab|
  \le\frac{|b|K_X+|a|K_Y}{t}+\frac{K_XK_Y}{t^2}
  \le\frac{|b|K_X+|a|K_Y+K_XK_Y}{t}.
  \]
  This is precisely the proposed bound. The additional division by \(t\) in the pair identity gives \(O(t^{-2})\).

- **Use common thresholds.** Take a finite maximum of all coordinate and pair thresholds, together with \(1\). Constants may depend on the fixed oscillator, dimension, rotation, and probe; this is not automatically uniform over those parameters.

- **Weight errors by absolute coefficients.** An assembled scaled remainder constant is
  \[
  K=\sum_{i,j}\frac{|\widetilde B_{ij}|}{2}K_{ij}
    +\sum_i|\widetilde b_i|K_{\mathrm{lin},i}.
  \]
  In particular, signed probe coefficients must not enter the bound without absolute values.

- **Handle the `if` by cases first.** In the diagonal branch, substitute \(j=i\) and simplify \(u_i u_i=u_i^2\). In the off-diagonal branch, apply the exact pair reduction. This is cleaner than trying to manipulate the unified expression directly.

- **Separate algebraic extraction from analytic assembly.** First obtain the ordered-pair coefficient using finite sums. Then prove a standalone algebra lemma extracting the diagonal and identifying the off-diagonal closed form.

- **Unscale only after recording \(t>0\).** Divide by \(t^2\) for the ambient bound, then by \(|C|/t^2\) for the relative bound. These steps should be separate lemmas or clearly separated proof blocks.

## 3. E2 wording, D, and nearby stronger targets

### Recommended wording for E2

> For the rotated separable oscillator and a general quadratic-affine probe, the Hessian-route formula has relative error
> \[
> \frac{\operatorname{Cov}_t[L,\psi]}{\operatorname{covKFormula}(t)}-1
> =\frac{C'}{C}\frac1t+O(t^{-2}),
> \qquad C\ne0,
> \]
> where \(C'\) includes the off-diagonal mean-shift contribution in the separable frame.

“Relative error proportional to \(1/t\)” is literally an asymptotic-equivalence claim only when \(C'\ne0\). If \(C'=0\), the relative error improves to \(O(t^{-2})\). The theorem should preserve that possibility.

### Concrete correction to D

D’s mechanism is fair, but its opening condition is insufficient: nonzero off-diagonal entries and nonzero products \(a_i a_j\) can still cancel in the sum.

Replace it with:

> The difference from the diagonal-only coefficient is exactly
> \(\sum_{i\ne j}\widetilde B_{ij}a_i a_j\). Thus off-diagonal probe components **can contribute** at second order, through products of leading mean shifts; the coefficients differ precisely when this sum is nonzero.

Also prefer “only the eigenframe-diagonal part of the **quadratic component** survives at leading order,” since the linear probe contributes there too.

### Nearby targets

The derivative interpretation is valuable:
\[
\operatorname{Cov}_t[L,\psi]=-\partial_t\langle\psi\rangle_t.
\]
It predicts the matching expectation expansion
\[
\langle\psi\rangle_t=\frac Ct+\frac{C'}{2t^2}+O(t^{-3}).
\]
But **do not differentiate an \(O(t^{-3})\) remainder without derivative control**. Prove the derivative identity by dominated differentiation, and obtain the covariance expansion through A–C. Bundle this only if the differentiation infrastructure already exists; otherwise keep it as an interpretive remark.

Two cheap corollaries are more attractive:
\[
\lim_{t\to\infty}t\left(
\frac{\operatorname{Cov}_t}{\operatorname{covKFormula}(t)}-1
\right)=\frac{C'}C,
\]
and, when \(C=0\) but \(C'\ne0\),
\[
\operatorname{Cov}_t=\frac{C'}{t^3}+O(t^{-4}),
\]
with relative error \(O(t^{-1})\) against this new leading term.

I would **not bundle a localized theorem**: it adds tail/localizer bookkeeping and potentially different differentiation hypotheses, without strengthening the core separable calculation.

## 4. Bundle choice

A supplies the missing analytic ingredient; B assembles it for the actual probe; C delivers the E2 statement. Keep D as B’s algebraic corollary with the corrected non-cancellation wording. The ambient matrix form is optional exposition, not essential formalization scope.

**Vote: A + B + C, with D as the corrected closed-form corollary; defer derivative and localized extensions.**