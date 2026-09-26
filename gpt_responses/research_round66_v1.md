## Verdict

The deepest remaining step is **controlled analytic continuation of the response map across the interior, joined—when \(X\) is finite—to a face-stratified boundary completion**.

That would turn your current result from “a smooth geometry with arbitrarily high-order approximations” into:

> **A convergent, quantitative response calculus covering the entire journey from featurelessness to the target, with a canonical description of what happens when that journey reaches the boundary.**

Two distinctions matter:

- \(C^\infty\) with Taylor remainders of each fixed order does **not** imply convergence of the Taylor series.
- Real analyticity throughout the atlas does **not** imply that the single Taylor series at the featureless point reaches the endpoint. Overlapping convergent charts are the right global statement.

I would rank four projects.

---

## 1. Quantitative analytic response atlas

### Precise target

Write \(P(M)=[q_M]\in L^1(\nu)\). Prove
\[
P:\Omega\longrightarrow L^1(\nu)
\quad\text{is real analytic}.
\]

Then strengthen this on the compact segment
\[
K=\{m_0+s\delta:0\le s\le1\}\subset\Omega.
\]

There exist \(A,r>0\), uniform over \(M\in K\), such that
\[
P(M+z)=\sum_{k=0}^\infty A_{M,k}(z,\ldots,z),
\qquad
\|A_{M,k}\|\le A r^{-k},
\]
for \(\|z\|<r\). Consequently,
\[
\left\|P(M+z)-\sum_{k=0}^n A_{M,k}(z^k)\right\|_1
\le
A\frac{(\|z\|/r)^{n+1}}{1-\|z\|/r}.
\]

Pairing gives the same bound simultaneously for all \(\|F\|_\infty\le1\). A finite chain of these charts covers the entire atlas.

### Quantitative geometry

Use Euclidean feature coordinates, let
\[
T_M=S-M,\qquad G_M=E_{Q_M}[T_MT_M^\top],
\]
and suppose along the segment
\[
\|T_M\|_\infty\le L,\qquad G_M\ge\lambda I.
\]
If \(\|S\|_\infty\le B\), one can take \(L=2B\).

A coarse but useful target is
\[
r=c\,\frac{\lambda^2}{L^3},
\]
with universal \(c>0\), and universal \(A\) after shrinking \(c\). This is not an optimal radius; it is a defensible quantitative inverse-function radius.

### Seabed route

Work locally around \(Q_M\), rather than repeatedly around \(\nu\):
\[
q_{M,\eta}
=
q_M\frac{e^{\langle\eta,T_M\rangle}}
{E_{Q_M}e^{\langle\eta,T_M\rangle}}.
\]

1. Complexify the finite-dimensional parameter space.
2. The numerator has an absolutely convergent \(L^1\)-valued exponential series.
3. For \(L\|\eta\|\) small, the denominator stays uniformly away from zero.
4. The centered mean map \(h_M(\eta)\) satisfies
   \[
   Dh_M(0)=G_M,\qquad
   \|Dh_M(\eta)-G_M\|\le C L^3\|\eta\|.
   \]
5. Solve \(h_M(\eta)=z\) by
   \[
   \eta=G_M^{-1}z-G_M^{-1}(h_M(\eta)-G_M\eta).
   \]
   On a natural-parameter ball of radius \(c\lambda/L^3\), this is a uniform contraction for \(\|z\|<c'\lambda^2/L^3\).
6. Obtain analytic dependence either through an analytic inverse theorem or through uniformly convergent analytic Picard iterates; alternatively build the coefficients with a majorant.

This proves convergence **and** produces the quantitative bounds missing from bare analyticity.

### What I would trust about Mathlib

I cannot inspect your checkout, so I would **not** promise that
`HasFPowerSeriesAt.hasFPowerSeriesAt_localInverse` exists.

I expect the analytic/power-series infrastructure, composition results, exponential analyticity, and differentiable local-inverse infrastructure to be available. I would not assume that the differentiable inverse API automatically supplies the required analytic inverse theorem.

Check the actual checkout first:

```bash
rg -n 'hasFPowerSeriesAt_localInverse|analyticAt_localInverse' Mathlib
rg -n 'localInverse|leftInv' Mathlib/Analysis/Analytic
rg -n 'HasFPowerSeriesAt.*comp|HasFPowerSeriesOnBall.*exp' Mathlib
rg -n 'namespace FormalMultilinearSeries|def leftInv|theorem leftInv' Mathlib
```

A formal inverse series alone is insufficient: the missing ingredient may be its **positive convergence radius**. Time-box this reconnaissance before committing to the majorant infrastructure.

### A cheap quantitative theorem before analyticity

There are already useful explicit bounds. Along a straight mean path, put \(D=\|\delta\|\). Under the bounds above,
\[
\|p'(s)\|_1\le \frac D{\sqrt\lambda},
\qquad
\|p''(s)\|_1\le \frac{LD^2}{\lambda^{3/2}}.
\]

The third-jet formula below gives
\[
\|p'''(s)\|_1\le \frac{4L^2D^3}{\lambda^{5/2}}.
\]
Hence
\[
\left\|p(s)-p(0)-sp'(0)-\tfrac12s^2p''(0)\right\|_1
\le
\frac{2L^2D^3}{3\lambda^{5/2}}s^3.
\]

This directly answers candidate (c), without waiting for an analytic inverse theorem.

---

## 2. Finite-space face completion

This is the strongest genuinely global addition.

### Precise target

Let \(X\) be finite, \(\nu(x)>0\), and
\[
C=\operatorname{conv}\{S(x):x\in X\}.
\]
Work relative to \(\operatorname{aff}C\), removing redundant feature coordinates.

For every \(M\in C\), define
\[
\overline Q_M
=
\arg\min\{\mathrm{KL}(D\|\nu):E_D S=M\}.
\]

Prove:

1. The minimizer exists and is unique.
2. \(M\mapsto\overline Q_M\) is continuous on \(C\), in total variation.
3. It agrees with \(Q_M\) on \(\operatorname{relint}C\).
4. If \(F\) is the minimal face containing \(M\), then
   \[
   \operatorname{supp}\overline Q_M
   =\{x:S(x)\in F\}.
   \]
5. On \(\operatorname{relint}F\), it is the smooth—and ultimately analytic—exponential-family section for the restricted reference measure and reduced feature space.
6. For every \(D\) with mean \(M\),
   \[
   \mathrm{KL}(D\|\nu)
   =
   \mathrm{KL}(D\|\overline Q_M)
   +
   \mathrm{KL}(\overline Q_M\|\nu).
   \]

Thus
\[
\overline R(D)=\overline Q_{E_DS}
\]
is a continuous retraction of the entire probability simplex onto the completed family, smooth along each face stratum.

### Seabed route

- Compact feasible simplex + continuity of \(x\log x\): existence.
- Strict convexity: uniqueness.
- Supporting-hyperplane equality: every feasible distribution is supported on the minimal face.
- Positivity on that face: mix with a feasible distribution positive on every face-supported state; the entropy derivative excludes zeros.
- Restricted Lagrange multipliers: exponential form and KL splitting.
- Continuity: compactness plus **feasible recovery sequences**.

That last step deserves emphasis: compactness and uniqueness alone are not the complete proof. You need to approximate a prescribed feasible distribution at \(M\) by feasible distributions at nearby \(M_n\). A polyhedral lifting lemma, or a suitable Hoffman error bound, supplies this.

Your boundary modules may already supply particular degenerating paths. The clean umbrella theorem is **path-independent extension**, not merely another asymptotic regime.

Do not promise transverse \(C^1\) regularity at the boundary. The natural result is continuous globally, smooth on strata.

---

## 3. Moving normal projection and the explicit Bell tower

This is the best next **short implementation**, though not the deepest remaining theorem.

There is a clean projection derivative. You do not need a third-order TV Peano theorem.

### Definitions

Along a straight mean atlas, write
\[
T=S-M_s,\quad G=E[TT^\top],\quad
\ell=T^\top G^{-1}\delta.
\]
Define
\[
L_s f=T^\top G^{-1}E[Tf],
\qquad
N_s f=f-Ef-L_s f,
\qquad
r=L_s(\ell^2),\quad c=E[\ell^2].
\]

Then
\[
\ell'=-c-r.
\]

### The clean operator identity

For a suitably differentiable bounded observable family \(f_s\),
\[
\boxed{\frac d{ds}(N_s f_s)
=
N_s f_s'-L_s(\ell_sN_s f_s).}
\]

Consequently,
\[
\boxed{\frac d{ds}[q_sN_s f_s]
=
[q_sN_s(f_s'+\ell_sN_s f_s)].}
\]

The second formula is especially valuable: it differentiates a normal density directly.

To prove the first, differentiate
\[
Nf=f-Ef-T^\top G^{-1}E[Tf],
\]
using
\[
T'=-\delta,\qquad G'=E[TT^\top\ell].
\]
The scalar terms cancel because
\[
E[f\ell]=\delta^\top G^{-1}E[Tf].
\]
The remaining regression terms combine into \(L(\ell Nf)\).

Now substitute \(f=\ell^2\):
\[
f'=-2c\ell-2\ell r,\qquad
\ell Nf=\ell^3-c\ell-\ell r.
\]
Since \(N\ell=0\),
\[
\boxed{p'''(s)=[q_sN_s(\ell_s^3-3\ell_sr_s)].}
\]
At featurelessness this is precisely your desired formula, with \(r\) as defined above.

### An even smaller dependency route

If differentiating the operator is cumbersome, use projection **after** differentiation.

Every positive-order derivative of \(\log q_s\) is affine in \(S\). Moreover, straight mean constraints imply
\[
E\!\left[\frac{q_s^{(k)}}{q_s}\right]=0,\qquad
E\!\left[T\frac{q_s^{(k)}}{q_s}\right]=0
\quad(k\ge2).
\]
Thus \(q_s'''/q_s\) is already normal. Apply \(N_s\) to
\[
q_s'''/q_s=\ell^3+3\ell\ell'+\ell'',
\]
and eliminate \(\ell''\) and the \(c\ell\) term.

This uses your existing smoothness and constraint differentiation, not a new Peano theorem.

### The tower

Let
\[
H_k=q_s^{(k)}/q_s,\qquad H_1=\ell.
\]
Ordinarily,
\[
H_{k+1}=H_k'+\ell H_k.
\]
For \(k\ge2\), \(H_k=N_sH_k\), giving the projected recursion
\[
H_{k+1}=N_s(H_k'+\ell H_k).
\]

Equivalently, with \(a_j=(\log q_s)^{(j)}\),
\[
H_k=N_s B_k(a_1,\ldots,a_{k-1},0),\qquad k\ge2,
\]
where \(B_k\) is the complete exponential Bell polynomial. The highest log derivative disappears because it is affine in \(S\).

This explains the invisible tower structurally, rather than coefficient by coefficient.

---

## 4. Functional reconstruction CLT and second-order stochastic response

This is more central to actual data than another deterministic curvature identity.

### Precise target

For iid data from \(D\), let
\[
M=E_DS\in\Omega,\quad
\widehat M_n=\frac1n\sum_{i=1}^nS(X_i),\quad
\Sigma_D=\operatorname{Cov}_D(S).
\]
If \(Z\sim N(0,\Sigma_D)\), prove in \(L^1(\nu)\)
\[
\sqrt n\bigl(P(\widehat M_n)-P(M)\bigr)
\Rightarrow DP_M[Z]=[q_M\ell_Z].
\]

Then prove the second-order limit
\[
n\bigl(P(\widehat M_n)-P(M)
-DP_M[\widehat M_n-M]\bigr)
\Rightarrow
\tfrac12[q_MN_M(\ell_Z^2)].
\]

The first limit is finite-rank Gaussian; the second is a normal-valued quadratic Gaussian response.

### Route

Finite-dimensional CLT + your \(L^1\) differentiability + Taylor remainder + continuous mapping/Slutsky. No empirical-process machinery is needed: reconstruction passes through finitely many moments.

Handle empirical means outside \(\Omega\) explicitly—by face completion, or a measurable fallback whose probability tends to zero. A bias limit needs uniform integrability, not merely convergence in distribution; bounded features and local concentration make that manageable.

Pairing immediately produces joint observable CLTs and their covariance:
\[
\operatorname{Cov}(F,G)
=
a_F^\top\Sigma_Da_G,
\qquad
a_F=G_M^{-1}E_{Q_M}[T_MF].
\]

---

## What I would not prioritize

### Intrinsic uniqueness

A useful theorem, but likely a short corollary:

> A family-valued map preserving feature means must equal \(R\).

Uniqueness of the mean parametrization already proves it. KL orthogonality can give an alternative characterization.

Avoid “\(m\)-affine retraction” without qualification: the **fibres** are mixture-affine; \(R\) itself generally is not.

### A Gauss–Bonnet analogue

There is an exact reconstruction identity
\[
P(M_1)-P(M_0)-DP_{M_0}[\delta]
=
\int_0^1(1-s)D^2P_{M_s}[\delta,\delta]\,ds.
\]
It beautifully identifies nonlinear endpoint response with accumulated invisible bending. But it is integral Taylor theory, not a new topological curvature theorem. Your information identities probably already capture the relevant endpoint scalar content.

---

## Sanity checks on the landed claims

### Global `fderiv` at locally smooth points

**Not an overclaim.** `fderiv` is pointwise and local. A globally defined extension that is smooth on an open neighborhood of the evaluation point has the correct global `fderiv` there.

For iterated `fderiv`, ensure that the first-derivative formula holds on an **open neighborhood**, not just at the single point. Then its derivative is legitimately computed there. Translation invariance plus interior openness is the right argument.

Be careful at boundaries: `fderivWithin` and totalized global `fderiv` are not interchangeable.

### Curved paths with `∀ t, M + γ t ∈ Ω`

Correct, but stronger than necessary. Interior membership at the evaluation point, continuity nearby, and local \(C^2\) regularity suffice. An interval-local formulation will be easier to apply to atlas segments.

The feature-acceleration identity follows exactly by differentiating the bounded linear moment map twice.

### One potentially substantive qualification

Check what \(U\) and \(K\) mean in
\[
U\simeq\Omega\times K.
\]

If \(\Psi(M,k)=P(M)+k\) and \(K\) is the **entire linear invisible kernel**, this is naturally a theorem about an ambient space of signed data with interior moments. It generally cannot describe only positive probability densities: arbitrary kernel translations destroy positivity.

So distinguish the ambient smooth product theorem from the positive-data locus, whose kernel slices are constrained. This may already be handled in your definitions; the prose should preserve that distinction.

**Recommendation:** land the moving-normal/third-jet theorem next; make controlled analytic continuation the flagship; make face completion the global capstone.