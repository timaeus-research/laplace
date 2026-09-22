## 1. Algebra: A is correct; B’s evaluation is correct, but the \(K=tL\) normalization needs fixing

Assume \(Q^\top Q=I\), with \(Q\) square, and put
\[
H=Q\operatorname{diag}(\lambda)Q^\top,\qquad
s_i=\frac1{\lambda_i t},\qquad
S=Q\operatorname{diag}(s)Q^\top.
\]
For the algebraic identities, assume \(t\ne0\) and every \(\lambda_i\ne0\). The analytic hypotheses already provide positive \(\lambda_i\), and eventually \(t>0\).

### A: mean shift

The contraction identity gives
\[
T:S=Q(\alpha s),
\]
where products inside the vector are componentwise. Consequently,
\[
S(T:S)=Q(\alpha s^2),
\]
and therefore
\[
-\frac t2 S(T:S)
=Q\left(-\frac{\alpha_i}{2\lambda_i^2t}\right)_i.
\]
Thus **`meanShift` has the correct sign and factor** for the unlocalized, \(\gamma=0\), reading of eq:mean.

The proposed coordinatewise rate follows from the one-dimensional rates and the separable marginal identity. Indeed, if
\[
\left|\langle u_i\rangle_t+\frac{\alpha_i}{2\lambda_i^2t}\right|
\le \frac{K_i}{t^2},
\]
then, above a common finite threshold,
\[
\left|\langle w_j\rangle_t-c_j-\operatorname{meanShift}_j(t)\right|
\le \frac{\sum_i|Q_{ji}|K_i}{t^2}.
\]
This also gives the proposed scaled residual limit.

Call this an **absolute \(O(t^{-2})\) error**, or an error of order \(t^{-1}\) after multiplying by \(t\). “Relative \(O(t^{-1})\)” requires a nonzero leading coefficient; a coordinate’s coefficient can vanish.

### B: four-term evaluation

Write
\[
M=Q^\top BQ,\qquad \beta=Q^\top b,\qquad
r_i=\lambda_i s_i^2=\frac1{\lambda_i t^2}.
\]
Then
\[
SHS=Q\operatorname{diag}(r)Q^\top,\quad
Sb=Q(s\beta),\quad
T:S=Q(\alpha s),\quad
T:(SHS)=Q(\alpha r).
\]
Here \(Sb=Q(s\beta)\) uses \(QQ^\top=I\), which follows from square-matrix orthogonality.

The four unweighted quantities are
\[
\begin{aligned}
\operatorname{tr}(HSBS)
 &=\sum_i M_{ii}\lambda_i s_i^2
 =\sum_i\frac{M_{ii}}{\lambda_i t^2},\\
(Sb)^\top(T:S)
 &=\sum_i\beta_i\alpha_i s_i^2
 =\sum_i\frac{\beta_i\alpha_i}{\lambda_i^2t^2},\\
b^\top SHS(T:S)
 &=\sum_i\beta_i\alpha_i r_i s_i
 =\sum_i\frac{\beta_i\alpha_i}{\lambda_i^2t^3},\\
(Sb)^\top(T:(SHS))
 &=\sum_i\beta_i\alpha_i s_i r_i
 =\sum_i\frac{\beta_i\alpha_i}{\lambda_i^2t^3}.
\end{aligned}
\]
After including the prefactors, the cubic contributions have coefficients
\[
+\tfrac12-\tfrac12-\tfrac12=-\tfrac12.
\]
Hence your proposed identity is correct:
\[
\operatorname{covKMatrix}(t)
=\frac{C}{t^2},\qquad
C=\sum_i\left(\frac{M_{ii}}{2\lambda_i}
-\frac{\beta_i\alpha_i}{2\lambda_i^2}\right).
\]

**However, this predicts \(\operatorname{Cov}_t[L,\psi]\), not \(\operatorname{Cov}_t[K,\psi]\) when \(K=tL\).** At each fixed \(t\),
\[
\operatorname{Cov}_t[K,\psi]
=t\,\operatorname{Cov}_t[L,\psi].
\]
Thus the displayed eq:covK has a normalization inconsistency as written: for \(K=tL\), its entire right-hand side must be multiplied by \(t\).

A simple diagnostic is the purely Gaussian case \(\alpha=0\):
\[
\operatorname{Cov}_t[L,\psi]
=\frac12\operatorname{tr}(HSBS),\qquad
\operatorname{Cov}_t[tL,\psi]
=\frac t2\operatorname{tr}(HSBS).
\]

I would either rename the proposed definition `covLMatrix`, or explicitly document that it predicts \(t^{-1}\operatorname{Cov}[K,\psi]\). Define the actual \(K\)-prediction as \(t\) times this expression.

### Probe identity

It is correct. Set \(z=w-c\) and \(u=Q^\top z\). Since \(QQ^\top=I\), \(z=Qu\), so
\[
\frac12z^\top Bz+b^\top z
=\frac12u^\top(Q^\top BQ)u+(Q^\top b)^\top u.
\]
**Symmetry of \(B\) is unnecessary** for this identity or the evaluation above.

## 2. Lean strategy

Your proposed trace route is sound. A slightly shorter route is to cyclically move the final \(S\):
\[
\operatorname{tr}(HSBS)
=\operatorname{tr}((SHS)B)
=\operatorname{tr}\bigl(\operatorname{diag}(r)(Q^\top BQ)\bigr)
=\sum_i r_iM_{ii}.
\]
This reuses the `SHS` identity needed by the other terms and avoids a separate trace computation involving two diagonal factors.

Recommended proof organization:

1. Derive \(QQ^\top=I\) once from `hQ`.
2. Establish the explicit formula for \(S\).
3. Establish the formula for \(SHS\) using `conj_mul_conj`.
4. Prove reusable conjugated-diagonal action and orthogonal dot-product lemmas.
5. Evaluate the four terms separately.
6. Finish with scalar denominator algebra.

Useful intermediate identities are
\[
\begin{aligned}
(QDQ^\top)(Qv)&=Q(Dv),\\
(Qv)^\top(Qw)&=v^\top w,\\
b^\top(Qv)&=(Q^\top b)^\top v.
\end{aligned}
\]
These also make the probe transport straightforward.

The principal `mulVec` pitfall is indeed **rewrite direction**:
```lean
M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v
```
collapses nested actions into a matrix product. To expand the action of a product, rewrite in the reverse direction. Keep a chosen normal form locally rather than simplifying indiscriminately in both directions.

Also:

- Matrix products require explicit reassociation before orthogonality rewrites.
- Dot-product transport can introduce `vecMul` or transposes; package the desired identity rather than repeatedly managing those conversions.
- Keep `s` and `r` abstract through the matrix calculations; use `field_simp`/`ring` only for the final scalar identities.
- Check the exact trace and dot-product lemma signatures in the installed Mathlib version. The identities are standard, but I would not commit to every suggested lemma name without checking.

## 3. Headline statement: scaled residual limit, not a new rate

For the definition currently proposed, the natural headline is
\[
t^2\bigl(\operatorname{Cov}_t[L,\psi]
-\operatorname{covLMatrix}(t)\bigr)\longrightarrow0.
\]
Also expose the coefficient limit
\[
t^2\operatorname{Cov}_t[L,\psi]\longrightarrow C.
\]
Together with the exact identity \(t^2\operatorname{covLMatrix}(t)=C\) for \(t\ne0\), the residual theorem is an immediate consequence of the seabed limit after probe transport.

For the note’s actual \(K=tL\), define
\[
\operatorname{covKPrediction}(t)=t\,\operatorname{covLMatrix}(t).
\]
Then state
\[
t\bigl(\operatorname{Cov}_t[K,\psi]
-\operatorname{covKPrediction}(t)\bigr)\longrightarrow0,
\qquad
t\,\operatorname{Cov}_t[K,\psi]\longrightarrow C.
\]

Do **not** claim an \(O(t^{-3})\) residual for the \(L\)-covariance from the existing limit. That needs additional quantitative moment estimates. The numerical convergence does not supply them.

Also, “relative \(o(1)\)” should be qualified by \(C\ne0\). The universally valid statement is an absolute \(o(t^{-2})\) residual for the \(L\)-covariance.

After correcting the normalization, a fair summary is:

> All four Laplace predictions are verified in matrix notation for the rotated separable anharmonic family, with no localization, at the stated asymptotic orders.

That should not imply a general-potential theorem, a localized mean theorem, or a covariance rate that has not been proved.

## 4. Scope and vote

**Vote: A+B, with the covariance normalization correction mandatory; C optional.**

A provides a genuine quantitative mean theorem. B provides the important ambient matrix/probe bridge and a qualitative asymptotic covariance theorem. C is useful as a lightweight specialization, but should not delay the core work. If included, explicitly distinguish the quartic coefficients \(\gamma_i\) from the note’s localization parameter \(\gamma\).