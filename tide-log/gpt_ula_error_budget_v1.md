## 1. Correctness of A–C and assumptions

**A–C are correct**, with the positivity and initialisation assumptions made explicit.

Use a finite-dimensional real space, an orthogonal frame \(U\), and
\[
p_i>0,\qquad h>0,\qquad hp_i<2.
\]
Then
\[
\rho_i=1-hp_i\in(-1,1),\qquad
\kappa_i=1-\frac{hp_i}{2}>0.
\]
For \(k\ge1\), \(f_i=1-\rho_i^{2k}>0\), so
\[
\Sigma_k=U\operatorname{diag}\!\left(\frac{f_i}{p_i\kappa_i}\right)U^\top
\]
is positive definite, as is its inverse. Here \(\Sigma_k\) is the covariance **from a deterministic start**. A random start generally contributes an additional propagated covariance.

For B, the stated Gaussian law follows with independent standard Gaussian innovations. Its natural parameters are indeed
\[
\bigl(\Sigma_k^{-1},\,\Sigma_k^{-1}m_k\bigr),
\]
assuming `tiltedExpectation` uses exponent \(-x^\top Rx/2+b^\top x\). The quadratic expectation and coordinate formula are correct.

For C, write
\[
b_i=\frac{a_i}{p_i},\qquad z_i=(Q^\top x_0)_i,\qquad
\mu_{k,i}=b_i+\rho_i^k(z_i-b_i).
\]
The per-mode identity is exactly
\[
\frac{t\lambda_i}{2p_i}
-\frac{t\lambda_i(1-\rho_i^{2k})}{2p_i\kappa_i}
=
-\frac{th\lambda_i}{4\kappa_i}
+\frac{t\lambda_i\rho_i^{2k}}{2p_i\kappa_i},
\]
because \(1-\kappa_i=hp_i/2\). Thus your `Burn_k` and full budget have the correct signs.

Under the convention **truth minus estimate**:

- stationary ULA discretisation contributes a **negative** term;
- the stationary ULA quadratic estimate is above the anchored Gaussian value when \(H\succ0\);
- the total burn-in term has **no fixed sign**, because its mean contribution can dominate its positive covariance-deficit contribution.

For \(P=tH+gI\), a frame diagonalising \(H\) automatically diagonalises \(P\), with \(p_i=t\lambda_i+g\). No separate simultaneous-diagonalisation theorem is needed. Use the **E2 frame**: replacing it with an arbitrary eigenframe of \(P\) can unnecessarily complicate the cubic/quartic coordinate data.

Finally, inherit all hypotheses of tide 95, including the nondegenerate minimum and localisation/tail assumptions. The exact sampler identity does not strengthen the analytic assumptions behind the \(O(t^{-2})\) remainder.

## 2. Interpretation, burn-in rate, and “first-order ULA bias”

For fixed \(\eta>0\), \(h=\eta/t\), and
\[
\eta\lambda_{\max}<2,
\]
stability holds for all sufficiently large \(t\), with a positive limiting stability margin. The positive stationary estimate bias is
\[
D_t=\frac{\eta}{4}\sum_i
\frac{\lambda_i}{1-\eta\lambda_i/2-\eta g/(2t)}
\longrightarrow
D_\infty=\frac{\eta}{4}\sum_i
\frac{\lambda_i}{1-\eta\lambda_i/2}.
\]
For small \(\eta\),
\[
D_\infty=\frac{\eta}{4}\operatorname{tr}H+O(\eta^2).
\]
So your interpretation is right: **fixed scaled step size leaves an \(O(1)\) LLC bias, while the anharmonic correction is \(O(t^{-1})\).**

### Correct the contraction notation and distinguish accuracy targets

The relevant contraction factor is
\[
r(t)=\max_i|\rho_i(t)|,
\]
not the minimum contraction magnitude. If “\(\rho_{\min}\)” means the mode associated with the smallest precision, that is safe only in a regime where it is actually the slowest mode; near the stability boundary, a negative \(\rho_i\) can dominate.

The useful exact expansion is
\[
\operatorname{Burn}_k
=
\frac t2\sum_i\frac{\lambda_i\rho_i^{2k}}{p_i\kappa_i}
-t\sum_i\lambda_i b_i\rho_i^k(z_i-b_i)
-\frac t2\sum_i\lambda_i\rho_i^{2k}(z_i-b_i)^2.
\]
For fixed \(x_0,a\), positive fixed \(\lambda_i\), and a uniform stability margin,
\[
|\operatorname{Burn}_k|
\le C\bigl(t\,r^{2k}+r^k+r^{2k}\bigr),
\]
where \(r<1\) is a uniform contraction bound.

Consequently:

- **Bounded transient:** \(k\gtrsim \log t/(2|\log r|)\).
- **Vanishing transient:** it suffices that
  \[
  k-\frac{\log t}{2|\log r|}\longrightarrow+\infty.
  \]
- **Transient \(O(t^{-1})\), comparable to anharmonicity:** it suffices that
  \[
  k\gtrsim \frac{\log t}{|\log r|}.
  \]

These are worst-case sufficient scales, not universal lower bounds: a start at the mode or missing projections onto slow modes improves them.

A good note formulation is:

> The anharmonic correction compares two equilibrium models. The ULA discretisation bias compares their Gaussian target with the sampler’s invariant law, while burn-in measures nonstationarity. At fixed \(h t=\eta\), the discretisation bias persists as \(t\to\infty\) and generally masks the \(t^{-1}\) anharmonic correction.

To make stationary discretisation bias \(O(t^{-1})\), take \(h=O(t^{-2})\); to make it \(o(t^{-1})\), take \(h=o(t^{-2})\). These changes also affect the mixing-time scaling.

### Exact Gaussian bias versus first-order bias

For \(q(x)=x^\top Hx/2\), the exact stationary bias is
\[
\mathbb E_{\rm ULA}q-\mathbb E_{\rm target}q
=\frac h4\operatorname{tr}\!\left(H(I-hP/2)^{-1}\right)
=\frac h4\operatorname{tr}(PH\Sigma_\infty).
\]
Multiply by \(t\) for the LLC statistic.

Call this the **exact Gaussian ULA bias**, whose fixed-\(P\), small-\(h\) first-order term is
\[
\frac h4\operatorname{tr}H.
\]
With \(P\sim tH\) and \(h=\eta/t\), \(hP\) need not be small: the denominator is important, rather than merely a negligible higher-order correction.

## 3. Lean route and pitfalls

Your proposed route is sound.

### A: separate spectral algebra from probability

First prove frame-general identities for:

1. \(I-hP=U\operatorname{diag}(\rho)U^\top\);
2. its powers;
3. \(\Sigma_\infty\), \(\Sigma_k\), and their diagonal inverses;
4. positivity for \(k\ge1\).

A clean covariance identity is
\[
\Sigma_k
=\Sigma_\infty-(I-hP)^k\Sigma_\infty((I-hP)^k)^\top.
\]
Alternatively, diagonalise the finite covariance sum and use
\[
1-\rho_i^2=2hp_i\kappa_i.
\]

Concrete pitfalls:

- Ensure both \(U^\top U=I\) and \(UU^\top=I\) are available. Derive the latter once for square matrices.
- Prove \(|\rho_i|<1\), \(\kappa_i>0\), and \(f_i>0\) separately before inversion.
- Keep \(k=0\) out of the density/precision representation: its law is a point mass.
- Normalise natural-number powers explicitly, especially
  \(\rho^{2k}=(\rho^k)^2\).
- Reuse the arbitrary-start recurrence theorem rather than rebuilding the probability argument in the new frame.

### B: isolate two reusable expectation lemmas

Prove the covariance contraction
\[
\sum_{i,j}H_{ij}(\Sigma_k)_{ij}
=\sum_i\lambda_i\,\frac{f_i}{p_i\kappa_i}
\]
and the mean identity
\[
m_k^\top Hm_k=\sum_i\lambda_i\mu_{k,i}^2.
\]

When passing from entrywise contraction to \(\operatorname{tr}(H\Sigma_k)\), explicitly supply symmetry: the trace uses \((\Sigma_k)_{ji}\). A frame-general trace lemma will pay off repeatedly.

### C: isolate the exact scalar budget

Prove the per-mode identity with just
\[
p\ne0,\qquad \kappa\ne0,\qquad \kappa=1-hp/2.
\]
Indeed, the algebra works with an arbitrary scalar in place of \(\rho^{2k}\). Then `field_simp; ring` should be robust after unfolding only the relevant definitions.

Finally sum the identity and combine it with `localisedEnergy_anchoredGap`.

**Preserve the existing remainder verbatim.** Since the sampler correction is exact, the \(O(t^{-2})\) constant and threshold remain independent of \(h,k,x_0\). This gives a genuinely uniform budget over all admissible sampler choices, including choices depending on \(t\).

## 4. Cheap additions worth making

In priority order:

1. **Stationary exact identity and stationary asymptotic budget.**  
   Define the stationary expectation directly; proving the identity does not require first formalising \(k\to\infty\). Add convergence separately if inexpensive.

2. **Expanded burn-in formula and an absolute bound.**  
   The three-term expansion above makes start dependence and logarithmic burn-in requirements transparent.

3. **Scaled-step limit.**  
   State \(\eta\lambda_{\max}<2\) explicitly. This corollary carries the main practical warning.

4. **Mode-start specialisation.**  
   If \(x_0=m\), the mean transient vanishes and burn-in is exactly the nonnegative covariance deficit. It is both useful and a good sign check.

5. **Variance of one sampled quadratic statistic**, if Gaussian fourth moments are already available. With
   \[
   v_i=\frac{f_i}{p_i\kappa_i},
   \]
   independence in the frame gives
   \[
   \operatorname{Var}\!\left(\frac t2X_k^\top HX_k\right)
   =
   \frac{t^2}{2}\sum_i\lambda_i^2v_i^2
   +t^2\sum_i\lambda_i^2\mu_{k,i}^2v_i.
   \]
   This is not automatically cheap without existing fourth-moment infrastructure.

Also label C an **expectation-bias budget**. A finite Monte Carlo estimate has an additional sampling fluctuation; for averages along one trajectory, its variance requires temporal covariances, not simply the single-time variance divided by sample count.

## 5. Vote

**Vote: land A → B → C, plus the stationary identity and expanded burn-in formula; correct the rate to the slowest absolute contraction and distinguish bounded burn-in from \(t^{-1}\)-accurate burn-in.**