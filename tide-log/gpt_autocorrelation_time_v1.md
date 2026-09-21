## 1. Mathematics

**A is correct**, including `N = 0`, assuming `ρ ≠ 1`. The weighted geometric sum has exactly the stated numerator; substituting it into `sum_sum_pow_dist` gives A.

**B is correct**, subject to the Gram table’s hypotheses and a valid denominator `1 − ρ² ≠ 0`. At window times `t_k = b+1+k`,
\[
|t_k-t_l|=|k-l|,\qquad
\sum_{k,l<N}\rho^{t_k+t_l}
=\left(\sum_{k<N}\rho^{t_k}\right)^2.
\]
Thus the Toeplitz part is shift-invariant and the transient factorisation is right. Mean-zero innovations and zero initialisation give `E x_k = 0`, so second moments give the variance.

**C needs `v ≠ 0`**, normally stated as `v > 0`, for the normalized variance limit. Otherwise `v = 0` makes the normalized expression identically zero under Lean’s division convention, not `τ`. For fixed burn-in,
\[
G_N:=\sum_{k<N}\rho^{b+1+k}
=\rho^{b+1}\frac{1-\rho^N}{1-\rho}.
\]
Hence `G_N` is bounded and the transient correction **in `N Var/s₂`** is `G_N²/N = O(1/N)`. Its correction in the variance itself is `O(1/N²)`. The Toeplitz correction after dividing by `N` is also `O(1/N)`.

**D is correct** for `hp ≠ 0`. Consequently the note’s `20κ` is the approximation; the exact IAT is `20κ − 1`.

**E is correct with the usual positive-step, positive-eigenvalue and normalized-eigenvector hypotheses**, but its advertised range `0 < hp < 2` allows negative `ρ`. Generalize C to **`|ρ| < 1`** or restrict E to `hp ≤ 1`. All the identities and limits extend to `|ρ| < 1`.

**Terminology:** explicitly say that
\[
\tau=1+2\sum_{m\ge1}\rho^m
\]
is the **stationary** integrated autocorrelation time, and that the zero-start chain has the same asymptotic variance inflation. Its finite-time correlations are not the stationary correlations.

## 2. Lean

- **A:** induction is a dependable approach. Separate the new endpoint, then rewrite old summands using `m < N`. If weights use natural subtraction, that rewrite needs arithmetic side conditions (`omega`); casting first and working with real subtraction can simplify the algebra. `Finset.sum_range_id_mul_two` is an arithmetic-sum identity, not the weighted-geometric identity needed here. I would not depend on an unverified `geom_sum_deriv`-style API.
- **B:** `MemLp.integrable_mul` is the relevant lemma for two real-valued `L²` functions. `Integrable (f * g)` and `Integrable (fun x => f x * g x)` are definitionally equivalent for function multiplication. Check the exact argument convention in the pinned Mathlib.
- **Distances:** use `Nat.dist` or integer/real absolute differences—not `abs` of truncated natural subtraction.
- **C:** the named constant-over-natural and power-limit lemmas are the right idiom for nonnegative `ρ`; check their precise signatures locally. For negative `ρ`, use an absolute-value/norm power-limit lemma, or bound by `|ρ|^N`.
- State limits on **`atTop : Filter ℕ`**, with statistics defined for every `N`. Prove identities involving cancellation eventually, using `N ≥ 1`; `N = 0` is harmless. Obtain real nonzeroness with `exact_mod_cast`, and positivity with `positivity`. No restricted filter is necessary.

## 3. Scope

A–E form one coherent tide; **300 lines is plausible but optimistic**, particularly for the variance bookkeeping and ULA instantiation.

Cheap additions:
- State the stationary-IAT geometric-series identity.
- Add the stationary sample-mean closed form if the stationary covariance setup already exists.
- Add E1’s exact numerical instance: **`τ_flat = 199999`**, with `200000` the approximation.

ESS `N/τ` is only asymptotic here; avoid presenting it as the exact finite-window ESS.

Vote: A+B+C+D+E
The ULA instance closes the sampler-facing claim, provided C includes nondegeneracy and is extended to `|ρ| < 1`.