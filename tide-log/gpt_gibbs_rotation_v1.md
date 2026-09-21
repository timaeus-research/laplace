## 1. A is correct; make the change of variables the foundational lemma

For finite `ι`, let
\[
A(w)=Q^\mathsf T(w-c),\qquad B(u)=c+Qu.
\]
The assumption \(Q^\mathsf TQ=I\) suffices: since \(Q\) is square, it also gives \(QQ^\mathsf T=I\), so \(A\) and \(B\) are inverse. Moreover, \(|\det Q|=1\). Thus \(A\) preserves Lebesgue measure, and all three identities in A follow.

**One Lean-specific caveat:** an orthogonal matrix is not generally an isometry for the default norm on `ι → ℝ`, which is the sup norm. It is an isometry for the Euclidean norm. So “affine isometry” is mathematically appropriate, but do not expect to construct a normed-space `IsometryEquiv` on the existing Pi type directly. The determinant/Haar route avoids changing types.

### Recommended implementation

First prove a reusable integral identity, schematically:
```lean
integral_comp_orthogonal_affine
    (hQ : Q.transpose * Q = 1)
    (hg : AEStronglyMeasurable g volume) :
    (∫ w, g (Q.transpose *ᵥ (w - c))) = ∫ u, g u
```
Your existing `integral_comp_mulVec` with `M := Q.transpose`, followed by translation invariance, is a short, low-risk proof.

A `MeasurePreserving A volume volume` lemma is also a good public abstraction—especially if you want integrability transport—but is not necessary to unblock A+B. If convenient, package the affine map together with its explicit inverse and prove measure preservation once. Check the exact hypotheses of the installed `MeasurePreserving.integral_comp'`; an invertible measure-preserving map is the right structure for handling the totalized integral, not merely an arbitrary measure-preserving map.

### Hypotheses

I would use **weak hypotheses in the core, continuity wrappers for applications**:

- Partition function: AE strong measurability of \(e^{-tL}\).
- Expectation: additionally, AE strong measurability of \(\phi e^{-tL}\).
- Covariance: for the usual difference-of-moments definition, include the weighted integrands for \(\phi,\psi,\phi\psi\).

These match your existing integral theorem without imposing unnecessary regularity. Then continuous \(L,\phi,\psi\) give convenient corollaries; the polynomial anharmonic application should discharge them automatically.

You do **not** need \(Z>0\) or integrability merely to prove these equalities of Lean’s totalized expressions: the corresponding numerators and denominators agree. You **do** need the appropriate finiteness/positivity assumptions to interpret them as genuine Gibbs moments or use normalized-measure identities such as \(\langle1\rangle=1\).

The directional consequences are immediate from
\[
(Qe_i)\cdot(w-c)=(A(w))_i.
\]
Energy invariance is simply the expectation theorem with \(\phi=L\). It is worth exposing explicitly because it transfers the LLC result directly.

## 2. B transfers directly, with signed means treated separately

Once the directional covariance identity is available, the variance limit really is an equality rewrite:
\[
\operatorname{Var}_{L\circ A}\!\big[(Qe_i)\cdot(w-c)\big]
=\operatorname{Var}_{L}[u_i].
\]
So `simpa only [...] using ...` is likely the cleanest proof; `Filter.Tendsto.congr'` with an eventual equality is equally valid. If your equality theorem is stated only for \(t>0\), use eventual positivity at `atTop`.

There is **no new sign issue for the variance correction**. The hypothesis
\[
\alpha_i^2=a^2\lambda_i^3
\]
is exactly what a correction quadratic in \(\alpha_i\) needs. Keep all the existing one-dimensional hypotheses, including the quartic normalization and assumptions ensuring the relevant minimum dominates. Rotation introduces no additional ones.

For the **mean**, however, `halpha` alone cannot determine a signed answer. The coordinate-frame theorem gives
\[
t\langle u_i\rangle\longrightarrow-\frac{\alpha_i}{2\lambda_i^2}.
\]
Consequently, for each ambient coordinate \(j\),
\[
t\langle w_j-c_j\rangle_{L\circ A}
\longrightarrow
-\sum_i Q_{ji}\frac{\alpha_i}{2\lambda_i^2}.
\]
Use this sum, or \( -Q*ᵥ(\alpha_i/(2\lambda_i^2))_i\), rather than the ambiguous `Q diag(...)` notation. If you substitute \(\alpha_i=a\lambda_i^{3/2}s_i\), retain \(s_i\).

This ambient mean statement needs a little more than rewriting: use
\[
w-c=Q\,A(w),
\]
integrability of the coordinate moments, linearity of the integral, and a finite-sum limit. The directional mean and energy limits are direct rewrites. Writing \(\langle w\rangle=c+Q\langle u\rangle\) additionally uses normalization.

I would leave the Hessian identification as a remark or small optional lemma. It is true, but unnecessary for a theorem quantified over arbitrary orthogonal \(Q\), and tying it to `orthoOf` risks irrelevant eigenbasis-choice issues.

## 3. Keep C separate

C is worthwhile, but it proves a different layer of the story:

- **A:** exact Gibbs change of coordinates.
- **B:** the already-proved asymptotics in the note’s measured directions.
- **C:** equivariance of an algebraic one-loop approximation.

A+B close the stated gap completely. C adds substantial tensor bookkeeping without strengthening that bridge. Its follow-up should explicitly state the hypotheses required by the definition of `oneLoopCov`—especially those governing the inverse Hessian—and check the transformation convention against \(u=Q^\mathsf T(w-c)\).

**Vote: formalise A+B now, with a reusable affine integral/measure-preservation lemma; defer C to a separate tide.**