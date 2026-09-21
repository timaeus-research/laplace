## 1. Mathematics

**A–C are correct under the stated assumptions; D needs a stationary-normalization qualification.** Assume positive budgets \(C,N\), and \(d>0\) for relative errors.

- **A:** Each Wick contraction forces \(c=c'\). The first additionally forces \(i=i',j=j'\); the second forces \(i=j',j=i'\). Both surviving products are
  \[
  G_i(b+1+k,b+1+l)\,G_j(b+1+k,b+1+l).
  \]
  Summing over the common chain gives \(C/(CN)^2=1/(CN^2)\). Thus the proposed delta factor is correct, including when both contractions survive.

- **B:** Correct. On diagonal entries, A becomes
  \[
  \operatorname{Cov}(\mathrm{pSM}_{ii},\mathrm{pSM}_{jj})
  =\frac{2\delta_{ij}}{CN^2}\sum_{k,l}G_i(k,l)^2.
  \]
  Weighted covariance bilinearity gives the claimed formula, with arbitrary real weights.

- **C:** Correct: multiplication by \(t\) cancels the \(1/t\) in the energy decomposition, so the weights are **\(p_i/2\)**. Consequently,
  \[
  \operatorname{Var}(\widehat{\mathrm{LLC}})
  =\frac1{2CN^2}\sum_i p_i^2\sum_{k,l}H_i(b+1+k,b+1+l)^2.
  \]
  No additional \(t\)-factor remains.

- **Envelope:** For \(r,s\ge0\) and \(0\le\rho<1\),
  \[
  0\le \rho^{|r-s|}-\rho^{r+s}\le\rho^{|r-s|}.
  \]
  With \(q=\rho^2\),
  \[
  \sum_{k,l<N}q^{|k-l|}
  =N+2\sum_{m=1}^{N-1}(N-m)q^m
  \le N\frac{1+q}{1-q}.
  \]
  Combined with \(p_i^2s_{2,i}^2=(1-hp_i/2)^{-2}\), this gives exactly C’s constant.

- **D:** The ratio of the displayed **bound expressions** is indeed
  \[
  \frac{2\tau/(dCN)}{(d+1)\tau/(CN)}
  =\frac{2}{d(d+1)}.
  \]
  However, \(d/[2(1-hp/2)]\) is the **stationary mean**, not the zero-start finite-window mean. In the latter case,
  \[
  \mathbb E\widehat{\mathrm{LLC}}
  =\frac{d}{2(1-hp/2)}\,a_{b,N},\qquad
  a_{b,N}=1-\frac1N\sum_{k<N}\rho^{2(b+1+k)}.
  \]
  Thus D should explicitly compare bounds normalized by the **stationary** LLC mean and stationary covariance norm. Dividing C’s envelope by the actual finite-window mean squared instead gives the conservative bound \(2\tau/(dCN\,a_{b,N}^2)\). Also, this is a ratio of bounds—not necessarily actual errors—and variance does not include discretization or burn-in bias.

## 2. Lean architecture

- **Prove A first as a general theorem.** Initially leave the existing variance proof intact. Once A compiles, preferably replace that proof with its specialization, preserving the theorem’s statement and name. Avoid maintaining two large Wick/sum-expansion proofs.
- **For B, use exactly**
  ```lean
  fun ω => ∑ i, w i * pooledSecondMoment x N b i i ω
  ```
  and expand the weighted covariance double sum; A then kills off-diagonal terms.
- For explicit-integral covariance, **reuse or extract the seabed’s sum-expansion lemma** rather than introducing a different covariance interface. Mathlib has covariance APIs, but I would not assume a clean, directly matching lemma without checking the pinned version.
- Make integrability explicit: constituent statistics and pairwise products must be integrable. Derive this from the existing fourth-moment/linear-combination machinery. The most useful helper is a **weighted finite-sum covariance identity**, not just an unweighted variance identity.

## 3. ULA specialization

The existing Gaussian-table → real-chain → Gram-table route is appropriate unchanged.

Main precautions:

1. **Prove a pointwise statistic identity first**, outside the integral:
   \[
   t\,\frac1{CN}\sum_{c,k}\tfrac12\langle x_{c,k},Hx_{c,k}\rangle
   =\sum_i \frac{p_i}{2}\,\mathrm{pSM}_{ii}.
   \]
   Then rewrite the random variable in the variance theorem. This avoids repeatedly distributing integrals and proving integrability during the spectral rewrite.

2. Use finite-sum interchange and scalar algebra explicitly; do not expect `simp` alone to rearrange the three sums. Supply \(t\ne0\) for cancellation.

3. Keep coordinate normalization identical to `frobenius_ula_le`: orthonormal eigenvectors of \(tH\), projected chain coordinates, and noise scaling.

4. Derive the scalar side conditions once:
   \[
   0<hp_i\le1,\quad 0\le\rho_i<1,\quad
   1-\rho_i^2>0,\quad 1-hp_i/2>0.
   \]
   These give `hp < 2` for `ula_variance_eq`. Rewrite \(s_2\) using that lemma, then simplify \(p_i^2s_{2,i}^2\); avoid a large early `field_simp`.

5. Preserve the \(b+1+k\) indexing. The Toeplitz difference loses the common shift, but the zero-start correction does not.

## 4. Scope

**A+B+C, plus corrected algebraic D, is one coherent tide.** Approximately 400 lines is plausible if the integrability and finite-sum infrastructure really is reusable; those are the likely sources of expansion.

Cheap, valuable additions:

- Export **both exact ULA variance and its envelope**, rather than only using the exact formula internally.
- Combine the existing mean theorem with variance to obtain
  \[
  \mathbb E[(\widehat{\mathrm{LLC}}-d/2)^2]
  =\operatorname{Var}(\widehat{\mathrm{LLC}})
   +(\mathbb E\widehat{\mathrm{LLC}}-d/2)^2.
  \]
  This connects more directly to “within 2%” than variance alone.
- Defer a \(\kappa\)-dependent comparison: it requires choosing and explaining the normalization and spectral bounds. Do not duplicate the existing finite-chain mean-shortfall result.

The full package closes the LLC variance side cleanly, provided D explicitly uses stationary normalization.

Vote: A+B+C+D