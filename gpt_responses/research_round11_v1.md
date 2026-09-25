## 1. Audit

**At the level of the stated mathematics, (a) and (b) look right.** I cannot audit the Lean implementation from the signatures alone, but the constants and proof architecture are consistent.

- **Spectator exponent:** the cancellation is exactly
  \[
  \Bigl(\prod_i\xi_i^{r_i}\Bigr)B_\xi^{-\beta}D_\xi^{-q\eta}
  =B^{-\beta}D^{-q\eta}
    \prod_i\xi_i^{r_i-\beta\kappa_i+\eta Q_i}
  =B^{-\beta}D^{-q\eta}\prod_i\xi_i^{d_i-1}.
  \]
  In particular, the sign of the \(\eta Q_i\) contribution is correct.
- **Trace hypothesis:** a.e. in \(\xi\) within the spectator box, with convergence for every \(u\in(0,\rho)\), is sufficient. It is somewhat stronger than necessary, but conveniently avoids exceptional-set bookkeeping.
- **Trace bounds:** the displayed bounds are global in \(\xi\), not in \(u\). Bounds only for a.e. \(\xi\) in the box would suffice. The stronger version is harmless; no upper bound on `atr` is needed because \(\beta>0\) and `atr ≥ amin > 0`.
- **Domination:** pointwise comparison with the constant-unit kernel is the right argument. This does not require a uniform rate of trace convergence.
- **Integral order:** spectator outside, \(u\) inside is correct. The density is nonnegative before multiplication by \(A\), and its integrability follows from \(d_i>0\), \(q\eta>0\), and the unit bounds.
- **Chart measure:** yes, for the intended map
  \[
  (\xi,u)\longmapsto \operatorname{rep}
       (\operatorname{bridgePt}(\operatorname{specPt}(e,\xi),u)),
  \]
  there is **no additional Jacobian**. This is the push-forward of the already specified parameter-space measure. A Jacobian would arise only if you subsequently expressed it relative to another reference measure. Noninjectivity of the map is also harmless.

The chart proof must, as presumably already done, establish nonnegativity of the density before using `ENNReal.ofReal`; otherwise `ofReal` would silently truncate its negative part.

### LP interface

Your theorem is exactly the useful **certificate-to-optimal-face interface**. Together with existence from positive face volume and the exponent identity, it closes the analytic/LP connection for supplied certificates.

It does **not** establish completeness of the certificate construction. I would not prioritize strong duality unless the note claims that every relevant LP face is covered. Moreover:

- ordinary duality gives nonnegative multipliers, not automatically the required strictly positive \(\beta,\eta\);
- strict spectator reduced costs require an appropriate strict-complementarity/optimal-face argument.

**Recommendation:** explicitly scope the result to faces admitting the displayed positive dual certificate. A general completeness theorem would be a separate substantial project.

## 2. The identically zero fibre constraint

**Your indicator description is correct for the constant-unit transverse calculation**, with two qualifications.

1. If several constraints vanish identically, retain the intersection of all their transverse half-spaces.
2. The inequality must retain whatever cutoff shifts occur in the actual fibre formula. If `Nv` already incorporates them, your formula is exact. It is a half-space in the linear transverse variables; after exponentiating variables, it need not look like a literal half-plane.

There is also an important **general-unit issue**:

> A solved coordinate whose face exponent is identically zero need not tend to zero along the transverse scaling.

Consequently, inserting an indicator while keeping the trace at **all active coordinates zero** is generally wrong. One must retain that coordinate in the limiting unit/weight evaluation. Thus this is not merely a different scalar constant for the general-unit theorem.

### Geometry

Write the constraint columns as \(a_i=(\kappa_i,Q_i)\). For a solved coordinate \(j\),

- `fibreCoef j = 0` says every free column lies in the span of the **other** solved column;
- `fibreA j = 0` says \((\delta,\gamma)\) lies in that same span.

Hence every point of the affine constraint fibre has \(\alpha_j=0\). With \(\kappa_i>0\), all the other columns have the same slope \(Q_i/\kappa_i\), while the exceptional solved column has a different slope. A nontrivial feasible target lies on the corresponding boundary ray of the column cone.

**Recommendation:** document this as an exclusion for now, including the failure of all-active-coordinate collapse. It deserves a separate boundary-regime theorem, not a small patch.

## 3. Solved-pair independence

Your proposed statement is right, but **the Jacobian ratio in the question is reversed**.

Let \(F_e\) be the projected face and \(M_e\) the solved matrix. The transition
\[
T:F_{e_1}\longrightarrow F_{e_2}
\]
satisfies
\[
|\det T_{\mathrm{lin}}|
 =\frac{|\det M_{e_2}|}{|\det M_{e_1}|}.
\]
Therefore
\[
\operatorname{vol}(F_{e_2})
 =\frac{|\det M_{e_2}|}{|\det M_{e_1}|}
   \operatorname{vol}(F_{e_1}),
\]
giving the desired normalized-volume identity.

### Economical proof

Use the augmented linear equivalence
\[
H_e(\alpha)
  =\bigl(\alpha_{\mathrm{free}(e)},\,
          \kappa\cdot\alpha,\,
          Q\cdot\alpha\bigr).
\]

1. Its absolute determinant is \(|\det M_e|\), independent of the sign convention for the second constraint.
2. The composite \(H_{e_2}H_{e_1}^{-1}\) has block form
   \[
   \begin{pmatrix}L&C\\0&I_2\end{pmatrix}.
   \]
3. Restricting the last two coordinates to \((\delta,\gamma)\) gives an affine equivalence with linear part \(L\).
4. It maps \(F_{e_1}\) exactly onto \(F_{e_2}\).
5. Apply the affine change-of-variables formula for volume.

This avoids Hausdorff measure entirely.

I would first expose the **ENNReal scaling identity**, then derive the `.toReal / |det|` form used by `faceConst`. Neither the nonzero-fibre-constraint hypotheses nor LP certificates are needed for this geometric identity. Keep the ambient active coordinate set fixed: changing which coordinates are spectators is a different assertion.

## 4. Moving parameters: try squeezing before building uniform DCT

This may be substantially easier than anticipated.

Factor out \(A(t)\). For the remaining nonnegative kernel, check monotonicity in:

- \(B\): decreasing, by the exponential;
- \(D\): according to the direction of its cutoff.

For fixed sufficiently small \(\varepsilon>0\), eventually
\[
B(t)\in[B_0-\varepsilon,B_0+\varepsilon],\qquad
D(t)\in[D_0-\varepsilon,D_0+\varepsilon].
\]
Monotonicity then traps the moving kernel between the two appropriate **fixed-parameter corner kernels**. Apply the theorem already proved to both corners, then let \(\varepsilon\downarrow0\). Their limiting constants converge by continuity of
\[
B^{-\beta}D^{-q\eta}.
\]
Finally multiply by \(A(t)\to A_0\). No sign condition on \(A(t)\) is needed if this multiplication is done last.

This works provided \(B,D\) enter only through those monotone factors/cutoffs and the units remain fixed. It avoids any new parameter-uniform DCT.

If you nevertheless want a DCT proof, the same worst-corner comparison supplies a uniform majorant on an eventual compact positive parameter rectangle. There is no need to control all parameter values globally.

## 5. Recommended order

1. **(d) Three-coordinate identification:** quick, concrete regression test connecting the abstract theorem to the motivating example.
2. **(g) Export to hironaka:** immediate payoff; include the certificate scope and degenerate-fibre exclusion in the note.
3. **(f) Moving parameters via squeezing:** likely inexpensive once monotonicity is packaged.
4. **(c) Solved-pair independence:** the principal remaining canonicity result. Move it ahead of (f) if the note presents `faceConst` as intrinsically attached to the face.
5. **(h) Only thin assembly corollaries:** since `ofTermData` already accepts these terms, avoid another assembly framework. One mixed vertex/tied/active example would be useful.
6. **(e) Degenerate fibre constraints:** defer as a genuinely different boundary regime.

For “distinguishability,” do **not** expect different LP faces automatically to yield different pushed-forward measures: `rep` can identify their images, and weights can create coincidences. Such a theorem needs explicit support-separation or identifiability hypotheses. Nonvanishing plus solved-pair independence are the more useful unconditional results here.