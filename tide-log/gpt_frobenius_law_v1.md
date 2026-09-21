## 1. Mathematical check: B and C are correct, with explicit qualifications

Assume throughout a probability measure, `C > 0`, `N > 0`, and real-valued chains starting at zero. For the envelope, assume `0 ≤ ρ i < 1`; then `s2 i = v / (1 - (ρ i)^2) ≥ 0`. The innovation variance `v` must be nonnegative, either explicitly or as a consequence of the moment hypothesis.

### B: Wick reduction and the factor

Write \(t_k=b+1+k\) and
\[
H_i(k,l)=s_i^2\bigl(\rho_i^{|t_k-t_l|}-\rho_i^{t_k+t_l}\bigr).
\]
Here \(s_i^2\) denotes your `s2 i`, not its square.

The Gram hypothesis gives
\[
E[x_{cki}x_{c'lj}]=\mathbf1_{c=c'}\mathbf1_{i=j}H_i(k,l).
\]
Consequently, Wick gives
\[
\operatorname{Cov}(x_{cki}x_{ckj},x_{c'li}x_{c'lj})
=
\mathbf1_{c=c'}(1+\mathbf1_{i=j})H_i(k,l)H_j(k,l).
\]

In particular:

- The **first pairing** survives for every pair of directions \(i,j\), provided \(c=c'\).
- The **second pairing** survives only when both \(c=c'\) and \(i=j\).
- Cross-chain covariance vanishes even for diagonal entries, because Wick subtracts the product of means.
- Cross-direction orthogonality does **not** make the variance of an off-diagonal estimator entry vanish.

Summing over chain pairs leaves exactly \(C\) terms. Thus
\[
\boxed{
\operatorname{Var}(\widehat\Sigma_{ij})
=
\frac{1+\mathbf1_{i=j}}{C N^2}
\sum_{k,l<N}H_i(k,l)H_j(k,l).
}
\]
The normalization is correct.

This uses the fourth-moment identity and the Gram table; full independence of the chain values is not additionally required.

### Exact zero-start expression

Your formula is correct provided the exponents use the **actual chain times**. With local window indices,
\[
H_i(k,l)
=
s_i^2\left(\rho_i^{|k-l|}
-\rho_i^{2(b+1)+k+l}\right).
\]
Do not accidentally use \(\rho_i^{k+l}\) with `k,l < N`: that would remove the burn-in shift.

The general Gram formula requires \(1-\rho_i^2\ne0\) when expressed using `v / (1 - ρ_i^2)`. The stable nonnegative assumptions already ensure this.

### C: envelope

Since \(t_k+t_l\ge |t_k-t_l|\), under \(0\le\rho_i<1\),
\[
0\le H_i(k,l)\le s_i^2\rho_i^{|k-l|}.
\]
Therefore
\[
H_i(k,l)H_j(k,l)
\le s_i^2s_j^2(\rho_i\rho_j)^{|k-l|}.
\]
For \(q=\rho_i\rho_j\in[0,1)\),
\[
\sum_{k,l<N}q^{|k-l|}
=
N+2\sum_{r=1}^{N-1}(N-r)q^r
\le N\frac{1+q}{1-q}.
\]
This yields exactly
\[
\boxed{
E\|\widehat\Sigma-E\widehat\Sigma\|_F^2
\le
\frac1{CN}
\sum_{i,j}(1+\mathbf1_{i=j})s_i^2s_j^2
\tau(\rho_i\rho_j),
\quad
\tau(q)=\frac{1+q}{1-q}.
}
\]

“Stationary envelope” is a good name: it bounds the zero-start centered error by replacing the zero-start Gram kernel with the stationary one.

### Relative form

Set \(d=|\iota|\), \(D=\sum_i(s_i^2)^2=\|\Sigma_\infty\|_F^2\), and let \(A\) denote the double sum in the envelope. If \(d>0\) and \(D>0\), define
\[
K=\frac{A}{dD}.
\]
Then
\[
\frac{E\|\widehat\Sigma-E\widehat\Sigma\|_F^2}{D}
\le K\frac d{CN}.
\]
Thus the **relative RMS** bound is
\[
\frac{\sqrt{E\|\widehat\Sigma-E\widehat\Sigma\|_F^2}}
{\|\Sigma_\infty\|_F}
\le \sqrt K\sqrt{\frac d{CN}}.
\]

So your displayed prefactor is the prefactor for **squared relative error**; its square root is the RMS prefactor.

For equal directions with positive common stationary variance,
\[
\frac{E\|\widehat\Sigma-E\widehat\Sigma\|_F^2}
{\|\Sigma_\infty\|_F^2}
\le \frac{(d+1)\tau(\rho^2)}{CN}.
\]
Again, take the square root for the RMS statement. For finite zero-start windows this is an upper bound, not generally an equality.

### Which target?

**Prove both, with the stationary-target theorem as the user-facing result.** The centered theorem is the clean process/combinatorics lemma.

The mean is
\[
E\widehat\Sigma_{ij}
=
\mathbf1_{i=j}s_i^2(1-a_i),
\qquad
a_i=\frac1N\sum_{k<N}\rho_i^{2(b+1+k)}.
\]
Hence
\[
\boxed{
E\|\widehat\Sigma-\Sigma_\infty\|_F^2
=
E\|\widehat\Sigma-E\widehat\Sigma\|_F^2
+\sum_i(s_i^2)^2a_i^2.
}
\]
For stable \(\rho_i\),
\[
a_i=
\frac{\rho_i^{2(b+1)}(1-\rho_i^{2N})}
{N(1-\rho_i^2)}.
\]

For this tide, the finite-sum bias formula is sufficient; the geometric closed form is optional.

Against the quoted E4 finding, “sampling fluctuation follows the square-root law, with an explicit initialization-bias correction” is the most accurate wording. If the note measures error against a continuous-time target rather than the ULA stationary covariance, **discretization bias remains another term**; this theorem does not remove it.

## 2. Lean architecture: recommend (b)

Separate three layers:

1. **Finite estimator algebra and Wick reduction.**
2. **A Gram-kernel specialization**, producing the `(if i = j then 2 else 1)` result.
3. **The `realChain` instance**, supplying linear-combination witnesses and the Gram table.

For the first two layers, you can simplify further by taking window-indexed values:
```lean
x : Fin C → ι → Fin N → Ω → ℝ
```
There is no need for the combinatorial theorem to see natural-number time, burn-in, or `realChain`.

Use a generic innovation index type and one common finite support:
```lean
g : α → Ω → ℝ
s : Finset α
```
with the relevant `FourthMomentTable` hypothesis and
```lean
∀ c i k, IsLinComb g s (x c i k)
```
Then instantiate `α := Fin C × ℕ × ι`.

I would first establish a raw covariance-sum identity before substituting the Gram hypothesis. That isolates analytic bookkeeping—integrability, expansion of integrals—from delta simplification.

For the concrete family, either curried `η` or uncurried `g` is fine. Curried `η` reads better in chain statements. Be explicit about product association:
```lean
-- Fin C × (ℕ × ι)
g a := η a.1 a.2.1 a.2.2
```
and use the correspondingly associated finite product
```lean
univ ×ˢ (range (T + 1) ×ˢ univ)
```
rather than relying on notation association.

Before duplicating the `isLinComb_realChain` induction, look for a small reusable lemma that lifts linear-combination support along an index embedding. Otherwise, a generalized chain lemma taking witnesses for the individual innovations is a better addition than a second specialized induction.

The cross-direction Gram theorem is the substantive concrete-instance addition: expand finite linear combinations and apply innovation orthogonality. Do not expect the existing same-direction theorem alone to discharge it.

## 3. Sum simplification and variance API

### Delta bookkeeping

Use
```lean
if i = j then (2 : ℝ) else 1
```
in the intermediate Lean theorem. It avoids casts and arithmetic involving an indicator. You can give a presentation corollary using `1 + if i = j then 1 else 0`.

Prove a **pointwise covariance simplification** before summing, by cases:
```lean
by_cases hij : i = j
· subst j
  ...
· ...
```
and similarly for `c = c'`. After substituting equal indices, `simp` and ring normalization should handle the kernel products.

Arrange the chain sums so the inner one is over the primed chain:
```lean
∑ c : Fin C, ∑ c' : Fin C,
  if c = c' then A else 0
```
With a suitable equality orientation, `simp` should collapse this to `(C : ℝ) * A`. If it does not, use the relevant `sum_ite_eq` or `sum_eq_single` lemma explicitly. Avoid making one giant `simp` invocation solve covariance substitution, directional cases, four sum rearrangements, and denominator cancellation at once.

Keep cancellation of `C` and `N` until the end, using their nonzero real casts.

### Explicit integrals versus `variance`

Stay with **explicit integrals** in the core development, matching the seabed. Introduce notation or a local definition if the expressions become unwieldy.

For A, the clean scalar building block is
\[
\int(S-a)^2
=
\left(\int S^2-(\int S)^2\right)
+\left(\int S-a\right)^2.
\]
State it under `MemLp S 2 P` or whatever equivalent integrability interface the existing proofs use, with `[IsProbabilityMeasure P]`. Then sum it over entries.

An optional wrapper identifying the explicit expression with Mathlib’s `variance` is useful, but not worth letting API conversions dominate this tide.

## 4. Scope and D

### Size

A+B+C is coherent, but **500 lines is optimistic** if it includes:

- the abstract covariance-sum theorem;
- the cross-direction chain Gram theorem;
- support transport;
- exact and envelope results;
- and polished relative/square-root corollaries.

Priority order:

1. A.
2. Abstract B.
3. Concrete chain B.
4. Exact centered C and envelope.
5. Stationary-target correction with finite-sum bias.

Defer elaborate relative-error packaging and the geometric bias closed form if necessary. Avoid presenting only an abstract Gram-conditioned theorem as though the concrete `FourthMomentTable` chain instance were already discharged.

### Gaussian discharge D

Yes, your plan is mathematically sound:

1. Restrict to finitely many chain/time indices.
2. Obtain joint Gaussianity of the independent Gaussian noise vectors.
3. Apply the continuous linear map collecting orthonormal projections.
4. Compute covariance:
   - same noise index: orthonormality and standard Gaussian covariance;
   - distinct noise indices: independence.
5. Deduce independence of the scalar coordinates from joint Gaussianity and diagonal covariance.
6. Scale by \(\sqrt{2h}\), then establish the required \(L^4\) membership and scalar moments.

Two qualifications:

- Require `0 ≤ h` to identify the scaled variance as \(2h\).
- Independence alone does not complete `FourthMomentTable`: explicitly discharge means, second/third/fourth moments and \(L^4\).

Also ensure the finite-window Gaussian theorem matches the downstream table interface. If that interface demands a table on the entire infinite innovation family, use finite restrictions to establish the needed global properties, or expose a finite-support version. A theorem only about `Fin T` should not silently be treated as a hypothesis about every natural time.

**Vote: A+B+C**, conditional on the innovation four-moment hypothesis, with **centered exact law + stationary envelope as the core**, and **explicit diagonal zero-start bias as the stationary-target corollary**. Describe the `sqrt(d/(CN))` result as a **relative RMS upper bound**, not an exact finite-sample scaling identity.