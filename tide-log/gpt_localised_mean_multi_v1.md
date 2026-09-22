## 1. Correctness and hypotheses

**A, B, and C are mathematically correct**, with the asymptotic quantifiers made explicit and with positive time. C is the strongest match to the note’s displayed formula.

Use the hypotheses
\[
Q^\top Q=I,\qquad
\forall i,\quad \lambda_i>0,\quad \gamma_i>0,\quad
\alpha_i^2<3\lambda_i\gamma_i,\qquad g\ge0.
\]
The centre \(c\) and anchor \(w_0\) are arbitrary and fixed. Write
\[
a:=Q^\top(w_0-c),\quad H:=Q\operatorname{diag}(\lambda)Q^\top,
\quad \mathcal T:=\operatorname{rotT}(Q,\alpha).
\]
Use a threshold name such as \(t_0\), rather than \(T\), to avoid confusing it with the cubic tensor.

For each rate, state
\[
\exists K\ge0,\ \exists t_0\ge1,\ \forall t\ge t_0,\quad \cdots.
\]
Constants may depend on all fixed model parameters, including \(g,w_0,Q\), but not on \(t\).

### (i) Exact factorisation

Yes. Since \(Q\) is square and finite-dimensional, \(Q^\top Q=I\) also gives \(QQ^\top=I\). Consequently,
\[
\sum_j(w_j-w_{0,j})^2
=\sum_i\bigl((Q^\top(w-c))_i-a_i\bigr)^2.
\]
Thus, for \(t>0\),
\[
L_{\mathrm{loc},t}
=\operatorname{rotated}(Q,c,L'_t),\qquad
L'_t(u)=\sum_i\left[
\ell_i(u_i)+\frac g{2t}(u_i-a_i)^2
\right].
\]
Multiplication by \(t\) recovers exactly the intended localised density.

The geometric identity is the essential new ingredient. For the expectation reduction, one must also discharge the analytic premises of the existing transport and separability lemmas:

- continuity/measurability;
- finite, nonzero spectator partition functions;
- integrability of coordinate observables where linearity requires it.

These follow from the quartic tails and the existing one-dimensional infrastructure. In particular, positive quartic coefficients give integrability of all polynomial moments at each \(t>0\); the nonnegative localiser does not worsen the tails.

The key exact bridge is
\[
\boxed{
\left\langle (Q^\top(w-c))_i\right\rangle_{\mathrm{loc}}
=\operatorname{localisedMean}
  (\lambda_i,\alpha_i,\gamma_i,g,a_i,t).
}
\]
I would expose this as a reusable theorem, not bury it inside the rate proof.

### (ii) Matrix identities

All the proposed identities hold for \(t>0\). Set \(d_i=t\lambda_i+g>0\). Then
\[
tH+gI=Q\operatorname{diag}(d_i)Q^\top,\qquad
S_t:=\operatorname{locS}(g,H,t)
=Q\operatorname{diag}(d_i^{-1})Q^\top.
\]
Orthogonality in the tensor contraction yields
\[
\operatorname{meanShiftLoc}(t,g,H,\mathcal T)
=Q\left(-\frac{\alpha_i t}{2d_i^2}\right)_i,
\]
and
\[
gS_t(w_0-c)=Q\left(\frac{ga_i}{d_i}\right)_i.
\]
Their sum is therefore **exactly**
\[
Q\bigl(\operatorname{locLeading}(\lambda_i,\alpha_i,g,a_i,t)\bigr)_i.
\]

Similarly,
\[
\operatorname{meanShift}(t,H,\mathcal T)
+g(tH)^{-1}(w_0-c)
=\frac1tQ\left(-\frac{\alpha_i}{2\lambda_i^2}
+\frac{ga_i}{\lambda_i}\right)_i.
\]

In Lean, parenthesise the localisation term explicitly, for example
`g • (locS g H t *ᵥ (w₀ - c))`.

### (iii) Hidden hypotheses

- **Positive time:** essential for the intended density identity and the rate proofs. Lean’s total division makes `g / (2 * 0)` a defined expression, but it does not represent the intended localised density at \(t=0\).
- **\(g\ge0\):** retain it to apply tide 65. It is not intrinsically necessary for quartic-tail integrability, but extending the rate theorem to negative \(g\) is outside this tide.
- **No \(d\ge1\) is mathematically necessary.** Statements quantified over coordinates are vacuous for `Fin 0`; finite-dimensional sum identities still work.
- **Normalisation matters:** converting a centred expectation into
  \(\langle w_j\rangle-c_j\) requires the partition function to be nonzero. Prove this once alongside the integrability facts.
- All parameters are fixed as \(t\to\infty\). These are not uniform-in-anchor or uniform-in-\(g\) statements.

## 2. Target and proof organisation

**A+B+C is a reasonable mathematical scope**, provided the existing transport and integrability APIs are as reusable as described. The substantive endpoint should be C; B is a useful corollary, not a prerequisite for C.

The clean dependency graph is:
\[
\text{exact frame reduction}
\longrightarrow
\begin{cases}
\text{A, using `localisedMean_anharmonic_rate`},\\
\text{C, using `localisedMean_sub_locLeading_rate`},
\end{cases}
\]
with B obtained from A and the unlocalised matrix identity.

Also establish the exact ambient identity
\[
\langle w_j\rangle_{\mathrm{loc}}-c_j
=\sum_iQ_{ji}\operatorname{localisedMean}
(\lambda_i,\alpha_i,\gamma_i,g,a_i,t).
\]
This isolates all measure-theoretic bookkeeping from the asymptotics.

For example, if the one-dimensional leading-form errors satisfy
\[
|e_i(t)|\le \frac{K_i}{t\sqrt t},
\]
choose a common threshold and set
\[
K_j:=\sum_i|Q_{ji}|K_i.
\]
Then
\[
\left|\sum_iQ_{ji}e_i(t)\right|
\le\frac{K_j}{t\sqrt t}.
\]
A common \(K\) for all ambient coordinates is also available by finiteness.

**The proposed \(K/(t\sqrt t)\) rates are correct for both B and C.** For fixed parameters, their predictions differ by \(O(t^{-2})\). But there is no need to formalise that comparison to prove either result: use the corresponding one-dimensional theorem directly.

If time becomes tight, prioritise **the exact reduction, A, and C**. Do not spend the tide proving B’s matrix algebra while leaving the displayed-\(S\) statement unfinished.

## 3. What this certifies against the note

A suitable summary is:

> For E2’s rotated separable anharmonic target, with a fixed isotropic quadratic localiser, the exact localised Gibbs mean agrees with the displayed eq:mean prediction, using \(S=(tH+gI)^{-1}\), up to a coordinatewise \(O(t^{-3/2})\) error.

Explicitly,
\[
\langle w\rangle_{\mathrm{loc}}-c
=-\frac12S_t(t\mathcal T:S_t)
+gS_t(w_0-c)+R_t,
\qquad
|(R_t)_j|\le \frac{K_j}{t^{3/2}}.
\]
Finiteness of the dimension also gives a norm bound of the same order.

This certifies:

- the localisation contribution for **non-Gaussian anharmonic targets**;
- the correct rotated, ambient-coordinate formula;
- the note’s actual \(S=(tH+gI)^{-1}\), not just its leading approximation;
- use of the **exact localised measure**, not a Gaussian surrogate.

It **does not certify** the note’s \(O(S^2)\) remainder, which here corresponds to \(O(t^{-2})\). It also does not establish the formula for general nonseparable potentials, growing anchors/localiser strengths, or a full higher-order expansion. The numerical results are consistent with a sharper rate, but do not supply it.

### Nearby alternatives

An anisotropic localiser is a natural follow-up **if it is diagonal in the same separability frame**:
\[
\Gamma=Q\operatorname{diag}(\eta_i)Q^\top,\qquad \eta_i\ge0.
\]
Then the same proof uses one-dimensional strengths \(g\eta_i\).

There is an important caveat: **commutation with \(H\) alone does not guarantee this in the chosen anharmonic frame when \(H\) has repeated eigenvalues.** Diagonalising \(\Gamma\) within a degenerate eigenspace may destroy separability of the cubic and quartic terms. State same-frame diagonality, or supply additional hypotheses such as simple spectrum.

Localised covariance is also attractive, but it needs suitable localised second-moment estimates and covariance bookkeeping. It is not as immediate a reuse of tide 65 as C.

## 4. Vote

**Vote: A+B+C, with C the flagship theorem and the exact frame/ambient reduction identities as the reusable core.** If scope must shrink, retain **A+C** and defer B. Describe the outcome as a verification of eq:mean’s displayed prediction with a weaker \(O(t^{-3/2})\) remainder—not as a proof of its \(O(S^2)\) claim.