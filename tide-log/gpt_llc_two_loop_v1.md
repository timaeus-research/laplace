## 1. Coefficients and contractions: yes

Assume the Taylor convention
\[
V(x)=V_*+\frac12H_{ij}x_ix_j+\frac1{3!}T_{ijk}x_ix_jx_k
+\frac1{4!}Q_{ijkl}x_ix_jx_kx_l+\cdots,
\]
with symmetric derivative tensors, positive-definite \(H\), and \(S=(tH)^{-1}\).

Let \(X\sim N(0,S)\). The first correction to the Gaussian partition function is
\[
-\frac{t}{24}\mathbb E[Q[X^4]]
+\frac{t^2}{2(3!)^2}\mathbb E[T[X^3]^2].
\]

The Wick pairings give:

- **Quartic vertex:** three pairings, all giving \(q\). Thus the contribution is \(-tq/8\).
- **Two cubic vertices, three cross-edges:** \(3!=6\) pairings, all giving \(\theta\). Thus the contribution is \(t^2\theta/12\).
- **Two cubic vertices, one cross-edge:** choose its endpoint at each vertex in \(3\cdot3=9\) ways; the remaining two legs at each vertex pair internally. Thus the contribution is \(t^2\delta/8\).

These exhaust the \(15\) pairings of six legs. At this order, taking the logarithm leaves this correction unchanged.

For fixed \(H,T,Q_4\),
\[
\theta,\delta\propto t^{-3},\qquad q\propto t^{-2}.
\]
Consequently,
\[
-\partial_t\left(\frac{t^2}{12}\theta+\frac{t^2}{8}\delta-\frac t8q\right)
=\frac t{12}\theta+\frac t8\delta-\frac18q.
\]
Together with the Gaussian term, this is precisely your `twoLoopEnergy`.

**Energy convention:** it approximates \(\langle V-V_*\rangle\). For \(\langle V\rangle\), add \(V_*\).

### The `bubble` identification is exact

Expanding the definition,
\[
\sum_{ij}S_{ij}\operatorname{bubble}_{ij}
=\sum_{ijklmn}T_{ikl}T_{jmn}S_{ij}S_{km}S_{ln}.
\]
Relabel the first vertex’s indices as \((a,b,c)=(i,k,l)\) and the second’s as \((d,e,f)=(j,m,n)\). This becomes
\[
\sum_{abcdef}T_{abc}T_{def}S_{ad}S_{be}S_{cf}=\theta.
\]
This is just a dummy-index renaming; it does not even require tensor symmetry. Symmetry is required when identifying all the Wick pairings with these same contractions.

Likewise,
\[
q=\sum_{ij}\operatorname{contractQ}_{ij}S_{ij},
\qquad
\delta=(T:S)^\top S(T:S).
\]

On the rotated family, writing \(s_i=(\lambda_i t)^{-1}\),
\[
\theta=\delta=\sum_i\alpha_i^2s_i^3,\qquad
q=\sum_i\gamma_i s_i^2,
\]
so
\[
\operatorname{twoLoopEnergy}
=\frac d{2t}
+\frac1{t^2}\sum_i
\left(\frac{5\alpha_i^2}{24\lambda_i^3}
-\frac{\gamma_i}{8\lambda_i^2}\right).
\]

## 2. Staging: proposed addition, with a clear theorem boundary

Present this as a **suggested addition to E2/E7**, not as a `\leanref` purporting to certify an existing statement of this formula.

A suitable description is:

> **Proposed addition: the first finite-temperature correction to the LLC.** Define the standard two-loop energy contraction. Its evaluation on the rotated-separable family is formalised, together with an \(O(t^{-2})\) remainder for the scaled energy \(t\langle K\rangle\).

Keep three claims distinct:

1. **General tensor expression:** a definition, motivated by the standard Wick expansion.
2. **Rotated-family evaluation:** an exact algebraic theorem about that definition.
3. **Rotated-separable asymptotic approximation:** a theorem transferred from the scalar rate result.

The coefficients agree with the standard expansion for a general smooth non-separable potential, under suitable Laplace hypotheses. **There is no coefficient discrepancy**, but the proposed Lean results would not establish the general non-separable asymptotic theorem.

A useful algebraic regression test outside the separable family is \(H=I_2\), with
\[
T_{112}=T_{121}=T_{211}=1
\]
and every other component zero. Then
\[
\theta=3/t^3,\qquad \delta=1/t^3.
\]
This distinguishes the two contractions and catches a swapped or merged coefficient. It is a tensor test, not an analytic theorem about a cubic-only potential.

### Be careful with “E2’s exact \(4.76\)”

For \(d=10,a=\tfrac12,t=3\), the two-loop scaled prediction is
\[
5-\frac{35}{144}=4.756944\ldots,
\]
which rounds to \(4.76\).

That does **not** establish that the exact expectation rounds to \(4.76\). An asymptotic big-\(O\) theorem provides neither applicability at \(t=3\) nor a sufficiently small numerical error there without explicit thresholds and constants. Say:

> “The two-loop prediction is \(4.75694\ldots\), numerically matching the reported \(4.76\) at the displayed precision.”

Do not identify the prediction with the exact value.

Also, differentiating a formal free-energy expansion explains the coefficients, but differentiating an \(O(t^{-2})\) remainder is not automatically justified. Your scalar energy theorem avoids that gap.

## 3. Lean: prefer a reusable Frobenius-conjugation lemma

For real square matrices, prove once that
\[
\sum_{ij}(Q D_aQ^\top)_{ij}(Q D_bQ^\top)_{ij}
=\sum_p a_pb_p,
\qquad Q^\top Q=I.
\]

The trace route is clean:
\[
\begin{aligned}
\sum_{ij}A_{ij}B_{ij}
&=\operatorname{tr}(A^\top B)\\
&=\operatorname{tr}(Q D_aD_bQ^\top)\\
&=\operatorname{tr}(D_aD_b)\\
&=\sum_p a_pb_p.
\end{aligned}
\]

I would use this if the existing `conj_mul_conj` infrastructure fits. Entrywise expansion is an equally sound fallback: distribute the finite sums and apply
\[
\sum_iQ_{ip}Q_{ir}=\delta_{pr}
\]
twice.

**Pitfalls:**

- Entrywise contraction is \(\operatorname{tr}(A^\top B)\), not generally \(\operatorname{tr}(AB)\). Here \(A\) is symmetric, but make that step explicit.
- Transposition reverses multiplication order.
- Matrix associativity often needs explicit rewrites before an orthogonality or conjugation lemma matches.
- For trace invariance, a two-factor cyclic identity is enough:
  \[
  \operatorname{tr}((QD)Q^\top)
  =\operatorname{tr}(Q^\top(QD))
  =\operatorname{tr}(D).
  \]
  There is no mathematical problem with the proposed `trace_mul_cycle` route; check its exact orientation in the installed Mathlib.
- Over \(\mathbb R\), ordinary transpose is correct. Do not accidentally formulate a complex Frobenius statement without conjugation.
- Isolate \(\lambda_i\ne0\) and \(t\ne0\) before the final denominator algebra.

This lemma handles \(\theta\) and \(q\) directly from the existing closed forms. For \(\delta\), use orthogonal invariance of the vector quadratic form together with `contractT_rot`.

## 4. Scope: A+B, explicitly restricted

**A** is a good algebraic extension: define the contractions and energy, prove `twoLoopEnergy_rot`, then specialise the parameters.

**B** supplies the essential analytic meaning. From coordinatewise bounds
\[
\left|t\langle\ell_i\rangle-\frac12-\frac{c_i}{t}\right|
\le \frac{K_i}{t^2},
\]
choose a common threshold, enlarged to ensure \(t>0\), and sum:
\[
\left|t\langle L\rangle-\frac d2-\frac{\sum_i c_i}{t}\right|
\le\frac{\sum_iK_i}{t^2}.
\]
Divide by \(t\), identify A’s expression, and transfer through the rotated change of variables.

Ensure that product factorisation of the **normalised** expectation and its invariance under the change of variables are established, not merely factorisation of unnormalised integrals.

**Vote: YES on A+B.** Strong, bounded scope: an exact tensor evaluation plus a genuine remainder theorem for the rotated-separable family. Exclude a general non-separable rate theorem and any certification of the exact \(t=3\) value from this target.