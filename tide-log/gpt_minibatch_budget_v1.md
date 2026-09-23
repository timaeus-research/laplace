## 1. A–C: correct, with explicit hypotheses

Write
\[
p_i=t\lambda_i+g,\quad \rho_i=1-hp_i,\quad
\kappa_i=1-\frac{hp_i}{2},\quad \widehat C=U^\top CU.
\]
For the stationary interpretation, assume \(t,h>0\), \(C\succeq0\), square orthogonal \(U\), and
\[
0<hp_i<2
\]
for every mode. Also require that \(U\) diagonalizes \(H\), not merely an unrelated \(P\). This follows from \(P=tH+gI\), \(t\ne0\), and the stated diagonalization of \(P\).

### A: yes
In that frame,
\[
\widehat\Sigma^{mb}_{ij}
=\frac{2h\,\mathbf1_{i=j}+h^2t^2\widehat C_{ij}}
       {1-\rho_i\rho_j}.
\]
Using
\[
1-\rho_i^2=2hp_i\kappa_i
\]
gives exactly
\[
\widehat\Sigma^{mb}_{ii}
=\frac{1+ht^2\widehat C_{ii}/2}{p_i\kappa_i}.
\]

The entry formula is algebraic under weaker assumptions; stability is what makes it a unique stationary covariance.

### B: yes
Since \(U^\top HU=D_\lambda\),
\[
\frac t2\operatorname{tr}(H\Sigma^{mb})
=\frac t2\sum_i
 \frac{\lambda_i(1+ht^2\widehat C_{ii}/2)}
      {p_i\kappa_i}.
\]
Thus **only the diagonal of \(C\) in an \(H\)-eigenframe enters the quadratic mean**. This statement requires only second moments, not Gaussianity.

The full \(\widehat C\) generally affects the variance—but covariance alone determines that variance only with an additional distributional assumption, notably Gaussianity. Actual minibatch innovations need not produce a Gaussian stationary law.

### C: yes
Define the extra stationary energy
\[
M_{mb}:=\frac{ht^3}{4}\sum_i
       \frac{\lambda_i\widehat C_{ii}}{p_i\kappa_i}.
\]
Then stationary minibatch energy is stationary ULA energy plus \(M_{mb}\). Consequently the target-minus-sampler budget acquires exactly **\(-M_{mb}\)**, with the same target-side \(O(t^{-2})\) remainder.

For PSD \(H,C\), \(M_{mb}\ge0\): minibatching inflates the sampler statistic and lowers the target-minus-sampler difference.

One important scope restriction: this does **not** establish the same remainder for the minibatch sampler’s expectation of the actual nonquadratic loss. If minibatching destroys concentration, a separate bound on its anharmonic contribution is needed.

## 2. E8 interpretation and the three sampler biases

### Noise normalization

Yes, provided \(C_g\) denotes covariance of the stochastic estimator of **\(\nabla L\)**, rather than of \(t\nabla L\). Then
\[
\operatorname{Cov}(t\,\widehat{\nabla L}-t\nabla L)=t^2C_g,
\]
and an Euler step injects \(h^2t^2C_g\).

For uniform sampling without replacement,
\[
C_g=\frac1m\left(1-\frac mn\right)S^2
\]
uses the population scatter convention with denominator \(n-1\). If \(S^2\) instead uses denominator \(n\), the coefficient changes.

### Scaling with \(h=\eta/t\)

The exact minibatch term becomes
\[
M_{mb}
=\frac{\eta t}{4}\sum_i
 \frac{t\lambda_i}{t\lambda_i+g}
 \frac{\widehat C_{ii}}{\kappa_i},
\qquad
\kappa_i=1-\frac{\eta}{2}\left(\lambda_i+\frac gt\right).
\]
For fixed positive \(\lambda_i\), fixed \(C\), and a strict limiting stability margin,
\[
M_{mb}
=\frac{\eta t}{4}\sum_i
 \frac{\widehat C_{ii}}{1-\eta\lambda_i/2}+O(1).
\]
Sum only over positive-curvature modes if \(H\) has a kernel: modes with \(\lambda_i=0\) contribute exactly zero to this statistic.

So the proposed E8 reading is right. Two wording corrections:

- Keep the modewise \(\kappa_i\); there is no common scalar \(\kappa\) in general.
- Replacing the weighted sum by \(\operatorname{tr}C\) additionally requires weak discretization, or comparable modewise factors, and no relevant nullspace issue.

A useful note formulation is:

> Under the additive, constant-covariance approximation, the quadratic LLC statistic has stationary upward biases from discretization and minibatching. At \(h=\eta/t\), these are respectively
> \[
> D=\frac{\eta}{4}\sum_i\frac{\lambda_i}{\kappa_i},
> \qquad
> M_{mb}=\frac{\eta t}{4}\sum_i
> \frac{t\lambda_i}{p_i}\frac{\widehat C_{ii}}{\kappa_i}.
> \]
> The target-minus-sampler budget is \(C_1'/t-D-M_{mb}+Burn_k+O(t^{-2})\). Burn-in is a transient, generally signed correction.

In particular, the anharmonic contribution decays like \(1/t\), fixed-\(\eta\) discretization generally persists, and fixed-\(C\) minibatch inflation generally grows like \(t\).

To keep minibatch inflation bounded, the **relevant weighted covariance** must be \(O(1/t)\); \(C=O(1/t)\) is a convenient sufficient condition. To make it comparable to \(C_1'/t\), one needs \(O(1/t^2)\), at fixed \(\eta\). For \(m\ll n\), the first condition typically means \(m\) grows proportionally to \(t\); for fixed finite \(n\), retain the FPC and describe the eventual approach to full batching.

### Is the full state-dependent law needed?

**For an exact minibatch energy mean, generally yes.** The mean of a quadratic uses only covariance, but the covariance recursion itself depends on the state-dependent gradient-noise covariance:
\[
\Sigma_{k+1}
=A\Sigma_kA^\top+2hI+h^2t^2\,\mathbb E[C_g(X_k)].
\]

For linear regression, writing the gradient-estimator error as
\[
\zeta_B(x)=\Delta H_Bx-\Delta a_B,
\]
fresh independent batches give, at stationarity with mean \(m\),
\[
\mathbb E[C_g(X)]
=C_g(m)+\mathbb E_B[\Delta H_B\Sigma\Delta H_B^\top].
\]
The cross terms vanish after centering \(X-m\). The second term changes the stationary covariance and hence the energy mean.

Therefore:

- Constant \(C=C_g(m)\) is a reasonable **frozen-noise first approximation** when that second term is controlled.
- It is not an exact consequence of the full law.
- Near interpolation, \(C_g(m)\) can vanish, making the Hessian-fluctuation term particularly important.
- Deterministic drift stability alone need not ensure mean-square stability with multiplicative noise.

Conditional unbiasedness still preserves the anchored mean equation; state dependence does not by itself introduce a mean shift.

## 3. Lean route and pitfalls

Your route is good. I would factor it into three reusable algebraic lemmas.

### A: general-frame conjugation

Start from `lyapunovVia_conj_apply`, then prove
\[
U^\top(\operatorname{minibatchNoise}\ h\ t\ C)U
=2hI+h^2t^2(U^\top CU).
\]
Apply the entry theorem, and derive the diagonal version separately.

Pitfalls:

- Keep the frame square and finite. If later proofs require \(UU^\top=I\), obtain it explicitly from the orthogonality API rather than repeatedly reconstructing it from \(U^\top U=I\).
- Separate the polynomial identity
  \[
  1-(1-hp)^2=2hp(1-hp/2)
  \]
  from division cancellation.
- The diagonal cancellation needs \(h\ne0\). Lean’s totalized division otherwise permits algebraic “solutions” with no stationary interpretation.
- Isolate denominator nonvanishing from stability in helper lemmas; avoid making every matrix proof redo those inequalities.

### B: generic trace lemma first

Prove once:
\[
U^\top HU=D_\lambda
\quad\Longrightarrow\quad
\operatorname{tr}(HX)
=\sum_i\lambda_i(U^\top XU)_{ii}.
\]
Use trace cyclicity, associativity, orthogonality, then expand multiplication by a diagonal matrix. This lemma needs neither symmetry nor PSD of \(X\).

After that, B is substitution of A’s diagonal formula. Do not rely on diagonalization of \(P\) implicitly supplying diagonalization of \(H\): make that implication a separate lemma or pass the latter hypothesis directly.

### C: prove an exact energy split

Prove
\[
E_{mb}=E_{\mathrm{ULA}}+M_{mb}
\]
before touching the asymptotic budget. Then rewrite tide 100’s theorem.

The identity
\[
(1+x)/y=1/y+x/y
\]
is valid even for totalized division at \(y=0\), so distributive rewrites should suffice here. Reserve `field_simp` for the earlier cancellation lemma. Keeping the exact split separate also makes preservation of the existing remainder bound transparent.

Finally, keep Gaussianity and probabilistic existence out of these deterministic trace lemmas; attach those only when interpreting the matrices as moments of a law.

## 4. Cheap additions

### Highest value: nonnegative inflation

Under PSD assumptions and stability, formalize
\[
M_{mb}\ge0.
\]
Even stronger, the stable Lyapunov operator gives
\[
\Sigma^{mb}-\Sigma^{ULA}
=h^2t^2\sum_{r\ge0}A^rC(A^\top)^r\succeq0.
\]
The scalar result is cheaper and immediately supports the “inflates” wording.

### Exact scaling identity before asymptotics

The exact \(h=\eta/t\) identity above is cheap and avoids prematurely building a large asymptotic API.

If
\[
\kappa_i\ge\delta>0,\qquad g\ge0,\quad \lambda_i\ge0,
\]
then
\[
0\le M_{mb}
\le\frac{\eta t}{4\delta}\operatorname{tr}C.
\]
That directly formalizes a sufficient covariance-scaling condition.

### Variance: useful, but label it Gaussian

For \(X\sim N(m,\Sigma^{mb})\), \(H=H^\top\), and \(Q(X)=\frac12X^\top HX\),
\[
\operatorname{Var}(Q)
=\frac12\operatorname{tr}\!\big((H\Sigma^{mb})^2\big)
 +(Hm)^\top\Sigma^{mb}(Hm).
\]
For the LLC statistic \(tQ\), multiply by \(t^2\).

Writing \(S=U^\top\Sigma^{mb}U\) and \(b=U^\top m\),
\[
\operatorname{Var}(tQ)
=t^2\left[
\frac12\sum_{i,j}\lambda_i\lambda_jS_{ij}^2
+\sum_{i,j}\lambda_i\lambda_jb_ib_jS_{ij}
\right].
\]
This makes the off-diagonal dependence explicit. For actual non-Gaussian minibatch noise, additional third- and fourth-moment contributions may appear, so this is a Gaussian surrogate theorem, not a consequence of the covariance fixed point alone.

## 5. Vote

**Vote: land A–C plus exact scaling and nonnegative inflation; explicitly label constant-\(C\) as a frozen-noise approximation and defer variance unless its Gaussian hypothesis is front and center.**