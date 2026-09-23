## 1. Correctness of A–D

Assume explicitly \(h>0\), \(p_i>0\), and \(hp_i<2\). Then \(|\rho_i|<1\), \(a_i>0\), and \(f_i(k)>0\) for \(k\ge1\).

**The formulas in A–D are correct, but the “vanishes identically iff” claim in A needs correction.**

Write
\[
r_i=\rho_i^2,\qquad
c_i=p_i b_i^2-\frac1{a_i}.
\]
The total mean bias is
\[
B_k=\frac12\sum_i r_i^k c_i.
\]

- If \(r_i>0\), mode \(i\)'s contribution has exactly the sign of \(c_i\), at every finite \(k\).
- If \(r_i=0\), its contribution is zero for every \(k\ge1\), regardless of \(c_i\).
- Different modes can cancel, particularly when they have equal \(r_i\).

Thus \(c_i=0\) for every \(i\) is **sufficient but not necessary** for \(B_k\equiv0\). The precise characterization for all \(k\ge1\) is
\[
B_k=0\ \text{for every }k\ge1
\quad\Longleftrightarrow\quad
\sum_{i:r_i=r}c_i=0
\quad\text{for every distinct }r>0.
\]
Modes with \(r_i=0\) are unconstrained. If you include \(k=0\), the group with \(r=0\) must also have coefficient sum zero. Your original iff holds when the \(r_i\) are distinct and nonzero.

### Cleaner transform and noncentrality

Define
\[
w_i(k)=\frac{f_i(k)}{a_i},
\qquad
\lambda_i(k)=p_i\rho_i^{2k}b_i^2.
\]
Then, for independent \(Z_i\sim N(0,1)\),
\[
E_k:=\frac12X_k^\top PX_k
\ \overset d=\ 
\frac12\sum_i
\left(\sqrt{w_i(k)}Z_i+\sqrt{p_i}\rho_i^k b_i\right)^2.
\]
Consequently, for \(k\ge1\),
\[
E_k\overset d=\sum_i\frac{w_i(k)}2\,
\chi_1^2\!\left(\delta_i(k)\right),
\qquad
\delta_i(k)=\frac{\lambda_i(k)}{w_i(k)}
=\frac{p_i a_i\rho_i^{2k}b_i^2}{f_i(k)},
\]
with independent summands. The mean and covariance entries in your noncentrality formula must be understood **in the eigenbasis**, not the original coordinates.

The cleanest transform for statements and limits is
\[
\boxed{
\mathbb E[e^{-sE_k}]
=
\prod_i(1+s w_i)^{-1/2}
\exp\!\left(-\frac{s}{2}\sum_i\frac{\lambda_i}{1+s w_i}\right).
}
\]
Equivalently, its exponential term is
\[
\exp\!\left(-\frac12\sum_i
\delta_i\frac{s w_i}{1+s w_i}\right).
\]
The \(w,\lambda\) version avoids division by \(f_i\) and extends directly to \(k=0\).

“Scaled noncentral \(\chi^2_1\)” is the least ambiguous distributional terminology. Ordinary Gamma shape \(1/2\) describes the central case; a noncentral Gamma interpretation requires the corresponding convention.

## 2. E4 reading and initialization

Your reading is fair, with two qualifications:

1. **Some hot modes do not imply positive total bias.** They make positive bias possible; the weighted sum decides.
2. **Each mode's bias magnitude decreases**, but opposing signs can produce cancellation, overshoot, and non-monotonicity in the total.

In particular:

- If all \(c_i\le0\), the mean approaches the stationary ULA mean monotonically from below.
- If all \(c_i\ge0\), it approaches monotonically from above.
- With mixed signs, neither assertion holds.

For a concrete non-monotone example, take
\[
r_1=\frac14,\quad r_2=\frac1{16},
\qquad c_1=-1,\quad c_2=8.
\]
These are realizable ULA parameters and initial coordinates. Then
\[
B_1=\frac18,\qquad B_2=-\frac1{64},
\]
and subsequently the bias returns toward zero from below. No individual mode changes sign.

A suitable note would be:

> In the local quadratic model, initialization exactly at the mode is cold: covariance builds up while the mean remains zero, so expected energy increases monotonically toward the stationary ULA value. An arbitrary initialization adds a decaying deterministic mean-energy term; its competition with covariance growth can cause overshoot or cancellation. Initialization at pretrained weights is a mode start only insofar as those weights are a stationary point of the actual local sampling objective.

That last qualification matters when the objective includes changed data, a prior, regularization, or another perturbation. Also, the exact ULA calculation does not automatically cover minibatch SGLD noise.

For “wait until energy stabilizes,” the main warning is:

> Energy stabilization is a useful diagnostic, not a certificate of stationarity. Opposing transient contributions can conceal substantial nonstationarity, and slowly relaxing modes may produce little visible energy drift.

Indeed, total expected energy can equal its stationary value for every \(k\), by the cancellation above, while the Gaussian mean and covariance remain nonstationary.

Finally, distinguish the two biases:
\[
\mathbb E[E_k]-\frac d2
=
B_k+
\frac12\sum_i\left(\frac1{a_i}-1\right).
\]
Burn-in removes \(B_k\), not the stationary ULA discretization bias.

## 3. Lean route and pitfalls

The proposed route is sound. I would establish the following reusable facts first:
\[
Q_k=\Sigma_k^{-1},\qquad v_k=Q_k m_k,
\]
\[
Q_k^{-1}=\Sigma_k,\qquad Q_k^{-1}v_k=m_k,
\]
and, in the chosen orthonormal eigenframe,
\[
U^\top m_k=(\rho_i^k b_i)_i,\qquad
U^\top\Sigma_k U=\operatorname{diag}\!\left(\frac{f_i}{p_i a_i}\right).
\]

### Mean

Apply `tiltedExpectation_quadForm`, then multiply by \(1/2\).

Reuse the **trace identity underlying** `burnIn_mean`, if available:
\[
\operatorname{tr}(P\Sigma_k)=\sum_i f_i/a_i.
\]
If `burnIn_mean` exposes only an expectation theorem, extracting a standalone trace lemma now will simplify both the arbitrary-start mean and variance.

### Variance

Apply `tiltedVar_quadForm` and use
\[
\operatorname{Var}\!\left(\tfrac12Y\right)=\tfrac14\operatorname{Var}(Y).
\]
The required identities are
\[
\operatorname{tr}(P\Sigma_kP\Sigma_k)=\sum_i w_i^2,
\qquad
(Pm_k)^\top\Sigma_k(Pm_k)=\sum_i\lambda_i w_i.
\]
This gives
\[
\operatorname{Var}(E_k)=\frac12\sum_iw_i^2+\sum_i\lambda_iw_i.
\]

### Transform

Your exponent calculation is correct:
\[
\frac12v^\top(Q+sP)^{-1}v-\frac12v^\top Q^{-1}v
=
-\frac12\sum_i\frac{s p_iq_i}{q_i+s p_i}\rho_i^{2k}b_i^2.
\]

A useful organizational alternative is a **shifted-to-centered factorization**:
\[
L_{Q,Qm}(s)
=
\exp\!\left(
\frac12(Qm)^\top(Q+sP)^{-1}(Qm)-\frac12m^\top Qm
\right)L_{Q,0}(s).
\]
Then invoke `laplace_ulaBurnIn` directly for \(L_{Q_k,0}(s)\). This avoids separately re-proving or extracting its determinant-ratio calculation.

### Main pitfalls

- Prove \(h>0\), \(|\rho_i|<1\), \(f_i>0\), and all denominator nonzero facts early.
- Establish positive definiteness of both \(Q_k\) and \(Q_k+sP\).
- Keep \(k\ge1\) for the analytic Gaussian-density formalism: \(\Sigma_0=0\) is singular.
- Handle matrix inverse, multiplication, and `mulVec` association explicitly; do not expect scalar algebra tactics to normalize them.
- Normalize
  \[
  (\rho_i^k b_i)^2=\rho_i^{2k}b_i^2
  \]
  in a separate scalar lemma.
- Preserve the factors \(1/2\) in the mean and \(1/4\) in the variance.
- Keep the existing scope honest: these are tilted-Gaussian expectation theorems until a separate trajectory-law identification is formalized.

## 4. Cheap additions worth making

**Highest value:**

1. **The \(k=0\) point mass**, stated separately:
   \[
   E_0=\tfrac12x_0^\top Px_0,\qquad
   \operatorname{Var}(E_0)=0,\qquad
   L_0(s)=e^{-s x_0^\top Px_0/2}.
   \]
   The \(w,\lambda\) transform reproduces this with \(w_i(0)=0\).

2. **Covariance monotonicity**, independent of the start. With \(A=I-hP\),
   \[
   \Sigma_{k+1}-\Sigma_k=2hA^{2k}\succeq0.
   \]
   Hence the covariance contribution to the mean is nondecreasing. This is stronger and more informative than only its trace monotonicity.

3. **Stationary variance limit**:
   \[
   \operatorname{Var}(E_k)\longrightarrow
   \frac12\sum_i\frac1{a_i^2}.
   \]
   This follows from the same finite-sum limits as D.

4. **A geometric bias bound.** If \(R=\max_i\rho_i^2<1\), then
   \[
   |B_k|\le \frac12R^k\sum_i|c_i|.
   \]
   This gives a quantitative burn-in statement without any monotonicity assumption.

**Pooled estimators:** cheap only if pooling independent chains at the same \(k\). For \(M\) independent replicates,
\[
\overline E_{k,M}
\overset d=
\sum_i\frac{w_i}{2M}\chi_M^2(M\delta_i),
\]
with independent mode summands.

Do **not** use this law for consecutive iterates of one chain. Those energies are correlated; their sum is a quadratic form of a stacked Gaussian path. I would defer that extension unless temporal pooling is the immediate application.

## 5. Vote

**Vote: land A–D with the corrected bias-sign/iff statements, prioritize the mean–bias and transform theorems, add variance and cheap limits, and defer correlated time-pooling.**