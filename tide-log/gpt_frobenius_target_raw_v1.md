## 1. Correctness of A–D

**A–D are mathematically correct, with one correction to the commentary in D:** for \(x,y\ge 0\),
\[
(x-y)^2\le x^2+y^2
\]
**is true**, since the omitted cross term is \(-2xy\le0\). The proposed max bound is also true and is sharper:
\[
(x-y)^2\le \max(x,y)^2\le x^2+y^2.
\]

Throughout, retain positive definiteness of \(Q\), \(C,N>0\), and the noise/integrability hypotheses from the existing ULA results. In particular, \(p_i>0\). These matter for the stationary-variance identities and the geometric-sum formula.

### A. Eigenbasis target law and mean

Correct. Writing
\[
\rho_i=1-hp_i,\qquad
s_{2,i}=\frac{2h}{1-\rho_i^2},\qquad
a_i=\frac1N\sum_{k<N}\rho_i^{2(b+1+k)},
\]
the diagonal Gram entries give
\[
\mathbb E\widehat\Sigma_{\mathrm{eig},ij}
=\delta_{ij}s_{2,i}(1-a_i).
\]
Thus the bias against \(\operatorname{diag}(s_2)\) is
\(-\operatorname{diag}(s_2a)\), giving exactly the stated squared-bias sum.

### B. Raw mean and burn-in formula

Correct:
\[
\mathbb E\widehat\Sigma_{\rm raw}
=U\operatorname{diag}\bigl(s_{2,i}(1-a_i)\bigr)U^\top,
\]
and
\[
a_i=
\frac{\rho_i^{2(b+1)}(1-\rho_i^{2N})}
     {N(1-\rho_i^2)}.
\]
Under \(0<hp_i\le1\), we have \(0\le\rho_i<1\), so
\[
0\le a_i\le \rho_i^{2(b+1)}.
\]

The exact mean and geometric identities actually work throughout the stable range \(0<hp_i<2\), including negative \(\rho_i\). The burn-in bound also survives because all relevant powers are even. Nevertheless, matching the existing E4 hypotheses is a sensible first implementation.

### C. Raw stationary-target MSE

Correct, using
\[
\frac{2h}{1-(1-hp_i)^2}
=\frac{1}{p_i(1-hp_i/2)}.
\]
Orthogonal invariance transfers both the target-error term and the centred term from the eigenbasis. The bias bound follows from
\[
(s_{2,i}a_i)^2\le s_{2,i}^2\rho_i^{4(b+1)}.
\]

### D. Raw posterior-target MSE

The sign and identity are correct:
\[
s_{2,i}-\frac1{p_i}
=\frac{h}{2-hp_i},
\]
hence
\[
s_{2,i}(1-a_i)-\frac1{p_i}
=\frac{h}{2-hp_i}-s_{2,i}a_i.
\]

This is genuine cancellation between stationary ULA inflation and zero-start deflation. Let
\[
d_i=\frac{h}{2-hp_i},\qquad
B_i=s_{2,i}\rho_i^{2(b+1)}.
\]
Since \(0\le s_{2,i}a_i\le B_i\),
\[
(d_i-s_{2,i}a_i)^2
\le \max(d_i,B_i)^2
\le d_i^2+B_i^2.
\]
Thus **both corollaries are valid**. The additive version may be easier to use and prove in Lean; the max version is tighter.

## 2. Strongest coherent single tide

**A+B+C+D form one coherent tide:** the progression is from the mean, through orthogonal transport, to the two targets explicitly named in E4. D is not a disconnected extension—it uses the same centred variance and changes only the deterministic bias.

I would structure the implementation around a reusable deterministic-target identity, if one is not already available:
\[
\mathbb E\|\widehat\Sigma-T\|_F^2
=
\mathbb E\|\widehat\Sigma-\mathbb E\widehat\Sigma\|_F^2
+\|\mathbb E\widehat\Sigma-T\|_F^2.
\]
For \(T=U\operatorname{diag}(t_i)U^\top\), B immediately makes the final term
\[
\sum_i\bigl(s_{2,i}(1-a_i)-t_i\bigr)^2.
\]
Then C and D are specializations to \(t_i=s_{2,i}\) and \(t_i=1/p_i\). This avoids duplicating integral-expansion arguments.

Prioritize the **exact identities** over multiple envelope variants. If the line budget slips, defer the max-bound corollary or relative wrappers before dropping D. The exact posterior identity is a principal deliverable.

## 3. Nearby additions and the \(P^{-1}\) comparison

### Relative form

Yes: a `frobenius_inv` lemma is a useful, inexpensive companion to `frobenius_ulaCov`:
\[
\|Q^{-1}\|_F^2=\sum_i\frac1{p_i^2}.
\]
It directly yields
\[
\frac{\mathbb E\|\widehat\Sigma_{\rm raw}-Q^{-1}\|_F^2}
     {\|Q^{-1}\|_F^2}
=
\frac{V+\sum_i(d_i-s_{2,i}a_i)^2}
     {\sum_i1/p_i^2},
\]
where \(V\) is the centred Frobenius MSE. For this interpretation and division of inequalities, establish denominator positivity; in Lean, that normally also requires a nonempty index type.

Be precise about terminology: this is **expected squared relative Frobenius error**. Its square root is relative root-mean-square error, not expected relative error. For the latter, Jensen gives an upper bound.

### Does comparison against \(P^{-1}\) need another term?

**No, provided \(P\) is the same precision matrix denoted \(Q\) here.** D already includes finite-step discretisation bias and finite-time zero-start bias, including their cancellation. No continuous-time correction is needed.

If \(P\neq Q\), however, equality of step sizes does not remove the target mismatch. The squared-bias term becomes
\[
\left\|U\operatorname{diag}\bigl(s_2(1-a)\bigr)U^\top-P^{-1}\right\|_F^2,
\]
which need not reduce to the stated eigenvalue sum.

**Vote: formalise A+B+C+D, prioritizing the exact mean and both exact raw-target MSE identities; add `frobenius_inv` and relative wrappers if budget permits.**