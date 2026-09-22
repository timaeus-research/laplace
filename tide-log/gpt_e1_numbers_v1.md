1. **The readings are right, with the stated caveat.** A is the directional ULA/Laplace variance ratio; B sums the same inflation across ten equally stiff directions. For E5, the Gaussian quadratic proxy gives
   \[
   \frac12\left(\frac43+\frac1{1-1/(4\kappa)}\right)
   =\frac76+\frac1{2(4\kappa-1)}.
   \]
   For \(\kappa\ge2500\), the correction is at most \(1/19998<10^{-4}\), so the proxy rounds to \(1.17\). “Applied to the stiff direction only” means retaining its inflation while approximating the flat factor by \(1\). **This certifies the arithmetic of the local Gaussian explanation, not the non-Gaussian Rosenbrock SGLD result.** Also, \(1.17\) is rounded, not exactly \((1+4/3)/2\).

2. **Worth landing as a small, coherent numerical-corollary tide**, provided the numbers are explicitly connected to `ulaCov_conj_apply` and `ula_llc`, rather than merely standalone `norm_num` identities. State A with the positivity/nonzero hypotheses needed for the ratio, and C as a two-eigenvalue Gaussian proxy—its name/docstring should not suggest a Rosenbrock sampler guarantee. A further clean consequence is
   \[
   \frac d2\le \mathrm{LLC}_{\mathrm{ULA}}
   \le \frac{d}{2(1-hp_{\max}/2)}
   \]
   under positive eigenvalues and \(0\le hp_{\max}<2\), with the upper bound attained in the isotropic case. Skip the log-spaced-spectrum decimals unless that spectrum is independently worth formalising.

3. **Vote: A + B + C**, with C explicitly scoped to the Gaussian-proxy arithmetic.