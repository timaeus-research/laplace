## 1. A–D are correct—with Gaussian innovations and the usual stability assumptions

Assume \(U\) is orthogonal, \(H=U\operatorname{diag}(\lambda)U^\top\), \(|\rho_i|<1\), and the innovations are **independent Gaussian** draws with covariance \(N\). The Gaussian qualification matters: constant innovation covariance alone does not imply a Gaussian \(k\)-step law or the Wick formulas in C.

### A. Finite-time law

Correct:
\[
\Sigma_k=\Sigma-A^k\Sigma(A^\top)^k
=\sum_{r=0}^{k-1}A^rN(A^\top)^r.
\]
In the frame,
\[
(\widehat\Sigma_k)_{ij}
=\widehat S_{ij}(1-\rho_i^k\rho_j^k)
=\widehat N_{ij}\sum_{r<k}(\rho_i\rho_j)^r.
\]
Thus, if \(N\succ0\), then \(\Sigma_k\succ0\) for \(k\ge1\), since the \(r=0\) summand is \(N\) and all remaining summands are PSD.

The law from a point start is
\[
K^k(x_0,\cdot)=\mathcal N(m_k,\Sigma_k),
\qquad
m_k=m+A^k(x_0-m).
\]
For \(k\ge1\), the tilted-Gaussian parameters
\[
(\Sigma_k^{-1},\Sigma_k^{-1}m_k)
\]
are right under the convention with exponent
\(-\tfrac12x^\top Px+b^\top x\). **Handle \(k=0\) separately as \(\delta_{x_0}\)**; it is not a positive-definite tilted Gaussian.

### B. Energy mean and conditional polynomial

Correct. In particular,
\[
K^kq(x)=\tfrac12x^\top B_kx+b_k^\top x+c_k,
\]
where
\[
B_k=(A^k)^\top HA^k,\qquad
b_k=(A^k)^\top H(I-A^k)m,
\]
and
\[
c_k=\tfrac12\operatorname{tr}(H\Sigma_k)
+\tfrac12((I-A^k)m)^\top H((I-A^k)m).
\]
Only \(c_k\) changes when the innovation covariance changes while the drift stays fixed. Your frame expression follows immediately.

### C. The asymmetric lag factors are correct

For \(X\sim\mathcal N(m,\Sigma)\), mixed Wick gives
\[
\operatorname{Cov}(q(X),K^\ell q(X))
=\tfrac12\operatorname{tr}(H\Sigma B_\ell\Sigma)
+(Hm)^\top\Sigma(B_\ell m+b_\ell).
\]
Here
\[
B_\ell m+b_\ell=A^\ell Hm,
\]
using the shared eigenframe. Consequently,
\[
c_\ell=
\frac12\sum_{ij}\lambda_i\lambda_j\widehat S_{ij}^{\,2}\rho_j^{2\ell}
+\sum_{ij}\lambda_i\lambda_j\widehat m_i\widehat m_j
\widehat S_{ij}\rho_j^\ell.
\]

The symmetrised version is
\[
c_\ell=
\frac14\sum_{ij}\lambda_i\lambda_j\widehat S_{ij}^{\,2}
(\rho_i^{2\ell}+\rho_j^{2\ell})
+\frac12\sum_{ij}\lambda_i\lambda_j\widehat m_i\widehat m_j
\widehat S_{ij}(\rho_i^\ell+\rho_j^\ell).
\]
I would **prove the asymmetric version first and present the symmetrised version as a corollary**. The justification is simply swapping \(i,j\), using symmetry of \(\widehat S\). No reversibility is needed; indeed, the chain is generally nonreversible when \(A\Sigma\ne\Sigma A\).

Do not replace the quadratic lag factor by \(\rho_i^\ell\rho_j^\ell\); that would be a different formula.

Finally, \(\operatorname{Cov}_\pi(q,K^\ell q)\) is not merely a proxy:
\[
\operatorname{Cov}_\pi(q,K^\ell q)
=\operatorname{Cov}(q(X_0),q(X_\ell))
\]
for the stationary Markov chain, by conditioning.

### D. Long-run variance

Correct:
\[
\tau^2_{\rm mb}
=\frac12\sum_{ij}\lambda_i\lambda_j\widehat S_{ij}^{\,2}
\frac{1+\rho_j^2}{1-\rho_j^2}
+\sum_{ij}\lambda_i\lambda_j\widehat m_i\widehat m_j\widehat S_{ij}
\frac{1+\rho_j}{1-\rho_j}.
\]
Absolute summability follows from \(|\rho_i|<1\) and finiteness of the index set, including when some \(\rho_i<0\).

This also proves
\[
\lim_{n\to\infty}
n\,\operatorname{Var}\!\left(\frac1n\sum_{r=0}^{n-1}q(X_r)\right)
=\tau^2_{\rm mb}
\]
under stationary initialization. A CLT is a separate theorem, not needed for that variance limit.

## 2. The corrected batch requirement is \(C=O(t^{-1})\), with a condition on the mean

Your later correction is the right one: **\(C=O(t^{-2})\) is unnecessarily strong for bounded scaled fluctuations.** There are two qualifications.

### Keep the exact fixed-\(\eta\) denominator

Suppose, for clarity, \(P=tH\), \(h=\eta/t\), with fixed
\(0<\eta\lambda_i<2\). Then
\[
\rho_i=1-\eta\lambda_i,\qquad
1-\rho_i\rho_j
=\eta(\lambda_i+\lambda_j-\eta\lambda_i\lambda_j).
\]
Therefore
\[
\widehat S_{ij}
=
\frac{2\eta\,\delta_{ij}/t+\eta^2\widehat C_{ij}}
{\eta(\lambda_i+\lambda_j-\eta\lambda_i\lambda_j)}.
\]
For fixed nonzero \(C\), the limiting minibatch contribution is
\[
E_{ij}
=\frac{\eta\,\widehat C_{ij}}
{\lambda_i+\lambda_j-\eta\lambda_i\lambda_j}.
\]
Dropping the last denominator term is a **small-\(\eta\) approximation**, not an asymptotic equivalence in \(t\) at fixed \(\eta\).

The ULA part is exactly
\[
\sigma_i^2=\frac{1}{t\lambda_i(1-\eta\lambda_i/2)}.
\]

More generally, require the \(\rho_i(t)\) to remain uniformly away from \(\pm1\); otherwise correlation-time growth changes the orders below.

### The mean contribution must also be controlled

With fixed dimension, uniformly controlled eigenvalues and stability gap,
\[
\tau^2=O\!\left(\|\Sigma\|^2+\|m\|^2\|\Sigma\|\right).
\]
Thus \(C=O(t^{-1})\) gives \(\Sigma=O(t^{-1})\), and
\[
t^2\tau^2=O(1+t\|m\|^2).
\]
So the claimed boundedness holds for the centred statistic, or when
\[
m=O(t^{-1/2}),
\]
as in particular when the Laplace displacement is \(O(t^{-1})\).

If \(m\) is fixed and nonzero, even ULA generally has a linear-energy contribution with \(t^2\tau^2=\Theta(t)\). Increasing the batch size cannot remove that baseline effect.

For fixed nonzero \(C\succeq0\), \(H\succ0\), fixed stable \(\eta\), and bounded \(m\), the centred quadratic contribution already gives
\[
\tau^2_{\rm mb}=\Theta(1),\qquad
t^2\tau^2_{\rm mb}=\Theta(t^2).
\]
Thus \(n=\Theta(t^2)\) is the stationary-sampling requirement for a fixed variance of the empirical average of \(tq\). This does **not** address its bias.

### Phrase bias and fluctuation separately

The additional stationary bias of \(tq\), relative to ULA with the same drift, is
\[
\Delta\mathbb E[tq]
=\frac t2\operatorname{tr}(HE)
=\frac{\eta t}{4}\sum_i
\frac{\widehat C_{ii}}{1-\eta\lambda_i/2}
\]
in the \(P=tH\) setting. This agrees with the stated tide-101 expression.

If \(C_B=C_*/B\), with a fixed nonzero PSD \(C_*\), then at fixed \(\eta\):

- **Bounded scaled fluctuations:** \(B=\Omega(t)\), subject to the mean condition above.
- **Bounded additional scaled bias:** also \(B=\Omega(t)\).
- **Vanishing additional scaled bias:** \(B/t\to\infty\).
- **Recovery of ULA’s scaled long-run variance:** likewise follows from \(C=o(t^{-1})\), under the same mean and stability assumptions.

A useful sentence for the note is:

> Linear batch growth controls both the scaled variance and the scaled minibatch bias, but generally leaves a nonzero bias and variance excess; superlinear batch growth removes the minibatch contribution. Longer runs reduce Monte Carlo variance, not stationary bias.

These comparisons isolate minibatch error; fixed-\(\eta\) ULA discretization bias may remain.

## 3. Lean route: sound, but separate law-level work from covariance algebra

Your proposed route is good. I would make the dependencies explicit:

1. **Finite innovation-sum identity.** Prove
   \[
   \Sigma_k=\sum_{r<k}A^rN(A^\top)^r.
   \]
   Then prove PD by separating the \(r=0\) term. This is often simpler than proving PD through entrywise geometric fractions. Keep the geometric-sum theorem for the explicit frame formula.

2. **Power/frame transport.** Establish once
   \[
   A^k=U\operatorname{diag}(\rho^k)U^\top,
   \qquad
   (A^\top)^k=(A^k)^\top.
   \]
   These should feed all subsequent covariance and conditional-energy calculations.

3. **Actual Gaussian kernel iteration.** The covariance iterate identity plus mean recursion does **not alone identify a probability law**. You also need closure of Gaussians under affine maps and independent Gaussian addition, or an equivalent Gaussian-kernel composition lemma. Keep the \(k=0\) Dirac case separate.

4. **Moment/integrability obligations.** Gaussian polynomial moments discharge the integrability needed for the conditional expectation, covariance shift, and mixed Wick. It is worth packaging these once rather than repeatedly solving them inside integral rewrites.

5. **Energy frame contraction.** Your Frobenius-invariance lemma is exactly appropriate. A trace version,
   \[
   \operatorname{tr}\!\left(
   U\operatorname{diag}(\lambda)U^\top\,UMU^\top
   \right)=\sum_i\lambda_iM_{ii},
   \]
   is an alternative if the existing energy theorem is already trace-based.

6. **Autocovariance.** First prove the mixed quadratic-polynomial covariance theorem, then specialize \(B_\ell,b_\ell\). The constant \(c_\ell\) should disappear before any frame expansion.

7. **Infinite sums.** Prove summability before invoking the finite-sum/`tsum` interchange. Use shifted powers \(\rho^{n+1}\) to represent positive lags; this avoids repeatedly subtracting the lag-zero term. Both \(\rho^\ell\) and \(\rho^{2\ell}\) are covered by absolute-value stability, without requiring \(\rho\ge0\).

8. **Interpretation theorem.** If the note calls \(\tau^2\) the asymptotic sampling variance, include either the stationary sample-mean variance limit or a precise pointer to the general theorem. Summing autocovariances and proving a CLT are distinct tasks.

One additional lemma is particularly valuable: the Lyapunov-to-resolvent identity below.

## 4. Add E—but strengthen it to the full long-run variance

The mean-part sign is actually controllable because \(E\) is not an arbitrary PSD matrix: it is the Lyapunov response to PSD added innovation covariance.

Write
\[
Q=h^2t^2\widehat C,\qquad
E_{ij}=\frac{Q_{ij}}{1-\rho_i\rho_j},
\qquad
v_i=\lambda_i\widehat m_i,
\qquad
f(r)=\frac{1+r}{1-r}.
\]
The key identity is
\[
\frac{f(\rho_i)+f(\rho_j)}
{2(1-\rho_i\rho_j)}
=\frac1{(1-\rho_i)(1-\rho_j)}.
\]
Symmetrizing the mean excess therefore gives
\[
\begin{aligned}
\Delta\tau^2_{\rm lin}
&=\sum_{ij}v_iv_jE_{ij}f(\rho_j)\\
&=\sum_{ij}
\frac{v_i}{1-\rho_i}\,
Q_{ij}\,
\frac{v_j}{1-\rho_j}\\
&=z^\top Qz\ge0,
\qquad z_i=\frac{v_i}{1-\rho_i}.
\end{aligned}
\]
This works even for negative stable \(\rho_i\).

More generally, the **entire** linear contribution has the manifestly nonnegative form
\[
\tau^2_{\rm lin}
=v^\top(I-R)^{-1}\widehat N(I-R)^{-1}v,
\qquad R=\operatorname{diag}(\rho).
\]
This is an excellent companion to D.

Your centred excess is also nonnegative: if \(D_{ii}=\sigma_i^2\),
\[
(D_{ij}+E_{ij})^2-D_{ij}^2
=2\sigma_i^2\delta_{ij}E_{ii}+E_{ij}^2,
\]
and all remaining weights are nonnegative for \(\lambda_i\ge0\). Hence, for the same drift and mean,
\[
\boxed{\tau^2_{\rm mb}\ge\tau^2_{\rm ULA}.}
\]
This supplies precisely the temporal inflation result requested in tide 104—not merely a stationary-variance comparison.

For Lean, the scalar rational identity should be a short denominator-nonzero/`field_simp`/`ring` argument; the conclusion is then PSD applied to \(z\).

As a useful special case, if \(P=tH\), then
\[
\Delta\tau^2_{\rm lin}
=\widehat m^\top\widehat C\,\widehat m
=m^\top Cm.
\]
The cancellation is exact.

The diagonal-\(\widehat S\) specialization is also worth adding as a regression theorem recovering tide 102. The scaling discussion is valuable, but I would keep its first version in prose unless the seabed already contains a parameterized asymptotic framework.

**Vote: A–D yes; prioritize full E via the resolvent identity and the diagonal recovery theorem, add symmetrization cheaply, and state the corrected scaling result with explicit mean and uniform-stability hypotheses.**