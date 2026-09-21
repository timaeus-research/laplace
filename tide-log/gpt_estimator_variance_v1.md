## 1. A1–A4 are mathematically correct, with integrability qualifications

**A1:** Yes, the factor is **2**. Write
\[
M_{ab}=\mathbb E[f_af_b].
\]
The assumed identity gives
\[
\operatorname{Cov}(f_a^2,f_b^2)=2M_{ab}^2,
\]
and hence
\[
\operatorname{Var}\!\left(q\sum_{a\in s}f_a^2\right)
=2q^2\sum_{a,b\in s}M_{ab}^2.
\]
Here \(q\) may be any real number.

The important Lean qualification is that **square-integrability alone is insufficient**: you need integrability of \(f_a^2f_b^2\), including the diagonal \(f_a^4\). In Lean, merely asserting an equality involving its Bochner integral does not supply integrability. A clean sufficient hypothesis is
```lean
∀ a ∈ s, MemLp (f a) 4 P
```
together with the fourth-moment identities and `[IsProbabilityMeasure P]`.

Centering is not needed by the algebra once that particular fourth-moment identity is assumed; it is needed to obtain the identity in that form from Gaussianity.

**A2:** The sign and ordering are right. Put
\[
s_2=\frac{v}{1-\rho^2}.
\]
For \(k\le l\),
\[
\langle x_k,x_l\rangle
=s_2\,\rho^{l-k}(1-\rho^{2k}).
\]
Since \(s_2\ge0\) and \(0\le\rho<1\), this is nonnegative and at most \(s_2\rho^{l-k}\). Symmetry handles the other ordering. This factorised form may be easier in Lean than proving the power comparison in the difference formula.

Thus
\[
\langle x_k,x_l\rangle^2
\le s_2^2(\rho^2)^{\operatorname{dist}(k,l)}.
\]
The window shift disappears from the distance, so the Toeplitz bound applies uniformly in burn-in.

For pooling, orthogonality across chains kills the corresponding terms **provided the Wick identity holds across the whole pooled family**. Orthogonality alone does not imply that their squares are uncorrelated.

**A4:** Yes, with \(t=hp\in(0,1]\) and \(\rho=1-t\),
\[
\frac{1+\rho^2}{1-\rho^2}\le\frac1t.
\]
After multiplying by positive denominators this is exactly \(t^2\le t\). In fact,
\[
\frac1t-\frac{1+(1-t)^2}{1-(1-t)^2}
=\frac{1-t}{2-t}.
\]

Require \(C,N>0\), and use \(s_2^2\) internally rather than juggling a separate \(\sigma\): your notation \(\sigma^4\) means \((\sigma^2)^2=s_2^2\).

One wording correction: the relative standard-error bound is relative to the **stationary directional variance** \(s_2\), not necessarily to \(\mathbb E S\), which is smaller for a zero-start chain. It is also a variance bound, not an MSE bound; bias remains separate.

## 2. A3: finite induction is a sound route

Identical distribution is unnecessary. Independence, centering, and the stated second through fourth moments suffice.

I would prove a finite-linear-combination package containing
\[
\begin{aligned}
\mathbb EX&=0,\\
\mathbb EX^2&=\sum_i a_i^2,\\
\mathbb E[XY]&=\sum_i a_ib_i,\\
\mathbb E[X^2Y^2]
&=\left(\sum_i a_i^2\right)\left(\sum_i b_i^2\right)
  +2\left(\sum_i a_ib_i\right)^2.
\end{aligned}
\]
The first three can be separate preliminary lemmas, rather than all being maintained in one large induction.

Your induction formula is correct:
\[
\mathbb E[(X+ag)^2(Y+bg)^2]
=\mathbb E[X^2Y^2]+b^2\mathbb EX^2
+4ab\mathbb E[XY]+a^2\mathbb EY^2+3a^2b^2.
\]

### Independence idiom

The robust architecture is:

1. From `iIndepFun g P`, obtain independence of the coordinate block on \(s\) from \(g_n\), for \(n\notin s\).
2. Compose the block with the measurable map
   \[
   z\longmapsto\left(\sum_{i\in s}a_i z_i,\sum_{i\in s}b_i z_i\right).
   \]
3. Compose again with whichever polynomial in \(X,Y\) occurs in the expansion.
4. Factor its product with \(g_n^j\).

**Use the pair \((X,Y)\)**: separate proofs that \(X\) and \(Y\) are each independent of \(g_n\) do not suffice to justify independence of \(XY\) and \(g_n\).

`iIndepFun.indepFun_finset` and `IndepFun.comp` are the right API neighborhood; depending on the pinned signatures, the grouping theorem may be stated for two disjoint finite blocks rather than a block and a singleton. I cannot verify the September 2026 checkout here, so I would not treat those names or their argument order as certified.

Likewise, look for the `IndepFun.integral_mul_eq_mul_integral` and `IndepFun.integrable_mul` family. Check carefully whether the version takes measurable or a.e.-measurable functions.

### Integrability idiom

I recommend **`MemLp (g i) 4 P` as the public hypothesis**. On a probability space this supplies lower moments, finite linear combinations remain in \(L^4\), and Hölder handles mixed monomials of total degree at most four.

Internally, package the resulting integrability facts. Repeatedly rebuilding them around each `integral_add` will otherwise dominate the proof.

A useful fallback if induction becomes awkward is a finite four-index Wick lemma:
\[
\mathbb E[g_i g_j g_k g_l]
=\delta_{ij}\delta_{kl}+\delta_{ik}\delta_{jl}+\delta_{il}\delta_{jk}.
\]
Expanding finite sums then proves the linear-combination theorem. This trades block independence and polynomial induction for index-equality cases; I would start with your induction.

## 3. A5: try one-dimensional Gaussian transport first

The mathematical route is straightforward:
\[
\xi\sim\operatorname{stdGaussian}(E)
\quad\Longrightarrow\quad
\langle u,\xi\rangle\sim
\operatorname{gaussianReal}(0,\|u\|^2),
\]
where the second parameter is the variance. Therefore
\[
\mathbb E\langle u,\xi\rangle^3=0,\qquad
\mathbb E\langle u,\xi\rangle^4=3\|u\|^4.
\]

For \(\eta=\sqrt{2h}\langle u,\xi\rangle\),
\[
\mathbb E\eta^2=2h\|u\|^2,\qquad
\mathbb E\eta^3=0,\qquad
\mathbb E\eta^4=3(2h\|u\|^2)^2.
\]

I would inspect the checkout in this order:

1. A theorem identifying the pushforward of `stdGaussian` under a continuous linear functional.
2. Closure of `IsGaussian` or `HasGaussianLaw` under continuous linear maps, followed by identification of mean and variance.
3. Central/raw moment formulas for `gaussianReal`, plus its finite-moment or `MemLp` API.

I cannot responsibly supply exact current theorem names without inspecting the pin. Also expect the variance argument to require a nonnegative-real coercion.

**Prefer this to rebuilding coordinate independence.** The coordinate route introduces product-measure identification and finite-sum machinery just to prove a one-dimensional marginal fact. It is a good fallback if your existing `stdGaussian` implementation already exposes coordinates conveniently, but not my first choice.

Yes, a theorem with **explicit projected-innovation moment and \(L^4\) hypotheses** is a worthwhile endpoint. Label it accurately:

> ULA directional-estimator variance bound under projected fourth-moment assumptions.

That is not yet the fully discharged standard-Gaussian ULA corollary. Preserve the latter as an explicit follow-up rather than implying Gaussian discharge is finished.

## 4. Scope and recommended theorem ladder

**A is the best fit.** I would stage it as:

1. Abstract finite-family variance identity under Wick and integrability.
2. Deterministic AR(1) squared-inner-product bound.
3. Pooled estimator theorem under a window-level Wick hypothesis.
4. ULA algebraic specialization.
5. Independent-innovation fourth-moment theorem and its application to `realChain`.
6. Standard-Gaussian projected-noise discharge, if the API cooperates.

This leaves useful completed results even if Gaussian infrastructure takes longer than expected.

### Include the exact zero-start formula

For \(t_i=b+1+i\), with \(C\) chains having the same parameters and orthogonal cross-chain covariance, the exact pooled formula is
\[
\boxed{
\operatorname{Var}S
=\frac{2s_2^2}{CN^2}
 \sum_{i,j<N}
 \left(\rho^{\operatorname{dist}(i,j)}
       -\rho^{2(b+1)+i+j}\right)^2.
}
\]
It is a natural corollary of A1 plus `inner_x_x`, and cleanly exposes the zero-start correction before applying the stationary upper envelope.

### Keep the estimator name precise

Your \(S\) is the **pooled uncentred second moment**, not the pooled sample variance after subtracting an empirical mean. A known mean of zero makes this a natural variance estimator, but the two random estimators differ.

For a directional quadratic-loss contribution \((p/2)S\), its variance is simply \((p/2)^2\operatorname{Var}S\). Summing over eigendirections needs cross-direction fourth-order information; do not advertise the directional theorem as the full LLC variance law.

B is a reasonable cheap companion if its expectation formula follows directly from existing sums. I would prioritize completing A’s integrability and Gaussian discharge over expanding B, and leave C out of this tide.

**Vote: A.** Qualifications: explicitly distinguish uncentred second moment from sample variance, include \(L^4\)/product-integrability assumptions, and distinguish a conditional ULA theorem from the fully discharged Gaussian-noise result.