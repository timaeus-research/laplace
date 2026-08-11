1. **Candidate A is correct.** The decomposition
   \[
   a_i a_j-b_i b_j
   =a_i(a_j-b_j)+(a_i-b_i)b_j
   \]
   is valid. Each bare first moment is `o(q)` by `tendsto_normalized_first_moment`; transported first-moment differences are also `o(q)`, so both products are `o(q²)`. The transported second-moment difference is `o(q²)` using `isLittleO_pow_of_superPoly` with `m = 0`, `r = 2`.

   No extra analytic hypotheses are needed: integrability is already packaged/proved upstream. Junk values away from `0⁺` are irrelevant, and `posteriorMomentT_inv_sq` supplies the required eventual equality because positivity is eventual in `𝓝[>] 0`.

2. **Prefer the H-matrix-level result.** The tensor equality at order two requires a separate theorem identifying the package matrix `H` with `iteratedFDeriv ℝ 2 L 0`. That is mathematically valid under the higher regularity package, but it is a distinct Taylor/polarization bridge and fits better in the recomposition tide.

3. **A can be strengthened and simplified:** first-moment *agreement* is unnecessary. For each package independently, every first moment is `o(q)`, hence each product of first moments is `o(q²)`. Therefore superpolynomial agreement of only the second moments already makes the covariance difference `o(q²)`. Reusing `hessian_recovery` is still the cheapest route.

**Vote: A′ — H-matrix recovery from second-moment SuperPoly data alone.**