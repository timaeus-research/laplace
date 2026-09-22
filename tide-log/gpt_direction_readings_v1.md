## 1. A and B are correct, with a few scope conditions

Assume throughout that \(P\) is real symmetric positive definite and \(d>0\). Write
\[
D:=\sum_i p_i^{-2}>0.
\]

### A: directional reading

Correct—and symmetry of \(\Pi\) is unnecessary even for the general statement.

If \(Ps=ps\) and \(s^\top s=1\), then \(P^{-1}s=p^{-1}s\). Symmetry of \(P^{-1}\) also gives \(s^\top P^{-1}=p^{-1}s^\top\), hence
\[
s^\top(P^{-1}+P^{-1}\Pi P^{-1})s
=\frac1p+\frac{s^\top\Pi s}{p^2}.
\]

The `oneLoopCov` instantiation follows directly. In the Lean statement, either retain positive definiteness of \(P\), or explicitly retain symmetry and invertibility: **a unit right eigenvector of an arbitrary nonsymmetric matrix is not sufficient** for this argument.

Also, \(\Pi_{ss}\) should mean \(s^\top\Pi s\), or the corresponding diagonal entry in the eigenbasis—not necessarily a diagonal entry in the original coordinates.

### B: eigen-perturbation law

Both identities are correct:
\[
F^2:=\frac{\|\Sigma'-P^{-1}\|_F^2}{\|P^{-1}\|_F^2}
=\frac{\sum_i\delta_i^2}{D},
\]
and
\[
\frac12\operatorname{tr}(P\Sigma')-\frac d2
=\frac12\sum_i p_i\delta_i.
\]
Thus, defining the **absolute relative LLC error** by normalization against \(d/2\),
\[
L:=\frac{\left|\frac12\operatorname{tr}(P\Sigma')-\frac d2\right|}{d/2}
=\frac{|\sum_i p_i\delta_i|}{d}.
\]

For a single-direction perturbation of amplitude \(a\) in direction \(j\),
\[
F=\frac{|a|}{\sqrt D},\qquad L=\frac{p_j|a|}{d}.
\]

Your two denominator bounds are exactly right:
\[
\frac1{p_{\min}^2}\le D\le\frac d{p_{\min}^2}.
\]
The first uses a direction attaining \(p_{\min}\); the second bounds every summand.

Consequently:

- **Stiff direction:** \(F\le |a|p_{\min}\), so
  \[
  L\ge\frac{\kappa}{d}F.
  \]
- **Flat direction:** \(F\ge |a|p_{\min}/\sqrt d\), so
  \[
  F\ge\sqrt d\,L.
  \]

The squared versions are correct and well suited to Lean. They also include \(a=0\) without undefined ratios.

Two qualifications:

1. If \(\Sigma'\) must actually be a covariance, require
   \[
   p_i^{-1}+\delta_i\ge0
   \]
   for every \(i\), or strict inequalities for positive definiteness. The algebraic identities need no such condition.
2. “Exposes” is a sensitivity comparison, not a universal guarantee. The stiff-direction lower bound exceeds one when \(\kappa>d\); signed multidirectional shifts can cancel in the LLC statistic.

## 2. The LLC rendering is right at the stated quadratic, centered level

For the quadratic approximation
\[
K(x)=\frac12x^\top Hx,\qquad P=tH,
\]
and a centered distribution with covariance \(\Sigma\),
\[
t\langle K\rangle=\frac12\operatorname{tr}(P\Sigma).
\]
Therefore a perturbation \(a uu^\top\), with \(u\) a unit eigenvector of eigenvalue \(p\), shifts this statistic by
\[
\frac12\operatorname{tr}(P\,a uu^\top)=\frac12pa.
\]

That precisely captures the eigenvalue weighting intended by Summary 4.

I would nevertheless label this the **quadratic LLC statistic** or **covariance contribution to \(t\langle K\rangle\)**. For mean \(m\neq0\),
\[
t\langle K\rangle
=\frac12\operatorname{tr}(P\Sigma)+\frac12m^\top Pm.
\]
For a nonquadratic loss, higher-order terms contribute as well. In particular, inserting a one-loop covariance into the quadratic statistic does not, by itself, establish the complete one-loop correction to the full \(t\langle K\rangle\).

## 3. There is a clean, sharp C—but it is optional for this tide

For \(\delta_i\ge0\), let
\[
Q:=\sum_i p_i^2.
\]
Then
\[
p_{\min}\|\delta\|_2
\le \sum_i p_i\delta_i
\le \sqrt Q\,\|\delta\|_2.
\]
The first inequality uses nonnegativity; the second is Cauchy–Schwarz. Substituting the definitions of \(F,L\) yields the **sharp fixed-spectrum comparison**
\[
\boxed{
\frac{d}{\sqrt{QD}}\,L
\le F
\le
\frac{d}{p_{\min}\sqrt D}\,L.
}
\]
Equivalently, without square roots,
\[
\boxed{
\frac{d^2}{QD}L^2
\le F^2
\le
\frac{d^2}{p_{\min}^2D}L^2.
}
\]

Both constants are optimal:

- The upper bound is attained by inflation supported on one minimum-eigenvalue direction.
- The lower bound is attained by \(\delta_i=c p_i\), \(c>0\).

In particular,
\[
F\le \frac{d}{p_{\min}\sqrt D}L\le dL.
\]
So your weak bound is valid, but retaining \(D\) gives the exact best constant for the given spectrum. No weighted-mean formulation is needed.

Without the nonnegativity restriction, the lower bound on \(F\) remains valid, but the upper bound generally fails: nonzero signed perturbations can satisfy \(\sum_i p_i\delta_i=0\), giving \(L=0<F\).

### Recommendation

A directly formalizes E7. B directly formalizes the intended directional sensitivity claim and supplies the exact identities from which later comparisons can follow. The sharp C is mathematically worthwhile, but introduces a separate “all inflations” theorem rather than strengthening the central stiff-direction statement.

**Vote: formalise A + B now; defer C, recording the sharp fixed-spectrum comparison above as the natural follow-up.**