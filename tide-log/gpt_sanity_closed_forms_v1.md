## 1. Correctness of A, B, and C

### A: the Rosenbrock formulas are correct

Assume \(a>0\), \(t>0\), and use the normalized Gibbs measure on all of \(\mathbb R^2\). Set
\[
Z_0=X-1,\qquad U=Y-X^2.
\]
The transformation
\[
(z,u)\longmapsto (1+z,\ u+(1+z)^2)
\]
preserves Lebesgue measure, and the transformed weight is
\[
e^{-tz^2/2}e^{-ta u^2/2}.
\]
Consequently,
\[
X=1+Z_0,\qquad Y=X^2+U,
\]
where \(Z_0\) and \(U\) are independent centered Gaussians with variances \(1/t\) and \(1/(ta)\).

This gives exactly
\[
\mathcal Z=\frac{2\pi}{t\sqrt a},
\]
and
\[
\begin{aligned}
E[X]&=1,& E[X^2]&=1+\frac1t,\\
E[Y]&=1+\frac1t,& E[XY]&=1+\frac3t,\\
E[Y^2]&=1+\frac6t+\frac3{t^2}+\frac1{ta}.
\end{aligned}
\]
Thus
\[
\operatorname{Cov}(X,Y)=
\begin{pmatrix}
1/t&2/t\\
2/t&4/t+2/t^2+1/(ta)
\end{pmatrix}.
\]

The Hessian and inverse-Hessian prediction are also correct:
\[
H=
\begin{pmatrix}
1+4a&-2a\\
-2a&a
\end{pmatrix},
\qquad
(tH)^{-1}=\frac1t
\begin{pmatrix}
1&2\\
2&4+1/a
\end{pmatrix}.
\]
Hence, **for covariance centered at the exact Gibbs mean**,
\[
\boxed{\operatorname{Cov}-(tH)^{-1}=\frac2{t^2}e_y e_y^\top.}
\]

An important distinction for the formal statement: the mean is not the mode. If instead you compute the second moment about \((1,1)\), then
\[
E[(Q-(1,1))(Q-(1,1))^\top]-(tH)^{-1}
=\frac3{t^2}e_y e_y^\top.
\]
Do not accidentally label this mode-centered second moment “covariance.”

Also,
\[
E[L]=\frac12\left(aE[U^2]+E[Z_0^2]\right)=\frac1t.
\]

The stiff-direction claim is an approximation, not an identity. For a unit Hessian eigenvector \(q_+\) with eigenvalue \(\lambda_+\),
\[
\frac{q_+^\top\operatorname{Cov}q_+}
     {q_+^\top(tH)^{-1}q_+}
=1+\frac{2\lambda_+(q_+)_y^2}{t}.
\]
At \(a=100\), the coefficient is approximately \(199.36\), so \(1+200/t\) is a reasonable approximation.

### B: correct, with explicit positivity assumptions on the window and chain counts

Add
\[
N>0,\qquad C>0,
\]
with \(b:\mathbb N\). Retain \(|\rho|<1\) and \(v>0\), so
\[
\sigma^2=\frac{v}{1-\rho^2}>0.
\]

For \(k\le l\),
\[
\langle x_k,x_l\rangle
=\sigma^2\left(\rho^{l-k}-\rho^{k+l}\right).
\]
This remains valid for negative \(\rho\).

Writing
\[
R_1=\sum_{k=b+1}^{b+N}\rho^k,\qquad
R_2=\sum_{k=b+1}^{b+N}\rho^{2k},
\]
and
\[
T_N=N+2\sum_{m=1}^{N-1}(N-m)\rho^m,
\]
B3 is exactly
\[
\boxed{
\sigma^2\frac{N-R_2}{N}
-\sigma^2\frac{T_N-R_1^2}{CN^2}.
}
\]
The sign and normalization are correct. In particular, the transient contribution \(R_1^2\) has a **positive** contribution after expanding the final subtraction.

This is the expected empirical variance with divisor \(CN\), not the Bessel-corrected estimator. If the note uses divisor \(CN-1\), multiply the displayed result by \(CN/(CN-1)\), assuming \(CN>1\).

### C: the trace identity is correct; the numerical claim needs qualification

Under the stated spectral assumptions,
\[
\operatorname{tr}(P\,\mathrm{ulaCov}(P,h))
=\sum_i\frac1{1-hp_i/2}.
\]
For its stationary-sampler interpretation, state \(h>0\), \(P\succ0\), and \(hp_i<2\). The algebraic identity itself can hold under weaker assumptions.

For \(P=tH\), take \(t>0\), \(H\succ0\), and write the result directly using the eigenvalues of \(H\):
\[
\frac t2\operatorname{tr}(H\,\mathrm{ulaCov}(tH,h))
=\frac12\sum_i\frac1{1-ht\lambda_i/2}.
\]

However, **\(hp_{\max}=1.9\) and \(d=10\) do not alone imply that this equals \(100\)**. They imply
\[
\frac12\sum_i\frac1{1-hp_i/2}\le100.
\]
Equality requires every \(hp_i=1.9\). A single direction at \(1.9\) contributes \(10\), not \(100\). If E1 is isotropic, the quoted value is correct; otherwise check the full spectrum.

## 2. Strongest coherent cluster for one excursion

I would choose **A0–A5, including the exact covariance–Laplace comparison**, rather than A+B+C.

The proposed full cluster contains two substantially independent pieces of infrastructure:

1. Nonlinear triangular changes of variables and Gaussian-polynomial integrability.
2. Finite-window Toeplitz sums and pooling identities.

Neither becomes materially easier after proving the other. C is comparatively cheap, but it does not make their union a coherent excursion.

A has a particularly good payoff: it turns the existing separable integration machinery into an exact result for a genuinely non-additively-separable potential. It also gives a sharp, interpretable discrepancy with Laplace rather than merely another closed form.

A useful staged scope is:

1. A reusable triangular transport lemma.
2. Gaussian-polynomial integrability after transport.
3. Partition function and the required raw moments.
4. Covariance and \(E[L]\).
5. The explicit \(2\times2\) inverse-Hessian comparison.

The stiff-eigenvector numerical approximation should remain commentary or a later corollary. It is not needed for the main exact theorem.

## 3. A0 and the integrability organization

### Prefer a shear abstraction, proved using Tonelli and translation invariance

The two proposed routes are not really competitors. My preference is:

> Prove the measure-preserving shear once using product integration and translation invariance; then use it as the interface for all signed integrals and integrability proofs.

For measurable \(g:\mathbb R\to\mathbb R\), define
\[
S_g(x,u)=(x,u+g(x)),\qquad
S_g^{-1}(x,y)=(x,y-g(x)).
\]
Prove that \(S_g\) preserves `volume.prod volume`.

The foundational proof should use **nonnegative integrands and Tonelli**, not signed Fubini. For nonnegative measurable \(F\),
\[
\begin{aligned}
\int^- F(S_g(x,u))\,d(x,u)
&=\int^-_x\int^-_u F(x,u+g(x))\\
&=\int^-_x\int^-_y F(x,y)\\
&=\int^- F.
\end{aligned}
\]
This avoids assuming precisely the integrability you later want to prove.

### Mathlib interfaces

The relevant standard interfaces include:

- `MeasureTheory.lintegral_prod`
- `MeasureTheory.integral_prod`
- `MeasureTheory.integrable_prod_iff`
- `MeasureTheory.integral_prod_mul`
- `MeasureTheory.Integrable.mul_prod`
- `MeasureTheory.MeasurePreserving`
- `MeasureTheory.MeasurePreserving.integral_comp`
- the `MeasurePreserving.integrable_comp` interface
- `MeasureTheory.integral_add_right_eq_self`
- `MeasureTheory.integral_sub_right_eq_self`

The composition lemmas have measurability/embedding side conditions that should be checked in your pinned Mathlib version. Package the shear as a measurable equivalence so both directions are available cleanly.

I would **not** plan around the existence of a theorem literally named `measurePreserving_prod_add`: I cannot confirm that exact declaration. Search locally for an existing skew-product result; otherwise the Tonelli proof above is a small, appropriate local lemma. A translation-preserves-Haar-measure theorem can supply the inner change of variables, including at the nonnegative-integral level.

### Use the fully centered transformation

Rather than repeatedly handling a shifted Gaussian in \(x\), use
\[
T(z,u)=(1+z,u+(1+z)^2).
\]
Prove, once,
\[
w(T(z,u))=G_t(z)G_{ta}(u),
\qquad G_c(r)=e^{-cr^2/2}.
\]

The weighted transport theorem then has the shape
\[
\int f(p)w(p)\,dp
=
\int f(T(z,u))G_t(z)G_{ta}(u)\,d(z,u),
\]
with an explicit integrability hypothesis or an established equivalence of the two integrability statements. A0 follows by product integration.

### Integrability: prove polynomial closure, not seven unrelated estimates

Yes, a universal theorem
```lean
∀ m n : ℕ,
  Integrable
    (fun p : ℝ × ℝ => p.1 ^ m * p.2 ^ n * weight a t p)
```
is a good public lemma.

But its proof should pass through a simpler transformed-coordinate statement:
\[
(z,u)\longmapsto z^i u^j G_t(z)G_{ta}(u)
\quad\text{is integrable}.
\]
Obtain that from the one-dimensional facts
\[
z^iG_t(z)\in L^1,\qquad u^jG_{ta}(u)\in L^1
\]
using `Integrable.mul_prod`.

Under \(T\), an original monomial becomes
\[
(1+z)^m\bigl(u+(1+z)^2\bigr)^n.
\]
Expand this into a finite sum of monomials and use integrability closure under scalar multiplication and finite sums. The integrability statement must cover odd powers too: cancellation of an odd integral is not an integrability proof.

There are two reasonable implementation choices:

- **Smallest local development:** expand powers with `add_pow` and finite-sum lemmas.
- **Reusable infrastructure:** prove that every bivariate polynomial times the product Gaussian is integrable, then instantiate it with the transported polynomial.

I would avoid introducing a large `MvPolynomial` evaluation layer solely for these seven observables unless the project already uses it.

For evaluating the seven integrals, explicit transported polynomial identities proved by `ring` are likely easier than a completely generic moment evaluator. Only Gaussian moments through degree four in \(z\), and degree two in \(u\), are required.

Finally, prove partition-function positivity before normalizing. Keep the analytic integration lemmas separate from the final `field_simp`/`ring` calculations.

## 4. The inner-product formulation of B is appropriate

It is an excellent deterministic core. The proof requires neither probability nor completeness: an arbitrary real inner product space suffices.

The probabilistic interpretation is precise. For real \(L^2\) random variables,
\[
\langle X,Y\rangle=E[XY],
\]
so
\[
\frac1M\sum_i\|X_i\|^2
-\left\|\frac1M\sum_iX_i\right\|^2
=
E\!\left[
\frac1M\sum_iX_i^2-
\left(\frac1M\sum_iX_i\right)^2
\right].
\]
No centering assumption is needed for this identity. Centered independent innovations are one sufficient way to obtain the stipulated orthogonality.

Do label the Lean result as a **second-moment/Gram-matrix theorem** until the \(L^2\) bridge is supplied. It is the algebraic content of the finite-chain prediction, not yet an instantiated theorem about random chains.

### Cleaner organization

I suggest four layers.

**1. General Gram-matrix identity.** For a finite family \(z_i\), \(M>0\),
\[
\left\|\frac1M\sum_i z_i\right\|^2
=\frac1{M^2}\sum_{i,j}\langle z_i,z_j\rangle.
\]
Then derive the pooled-variance functional from an arbitrary second-moment table.

Relevant Mathlib tools are `inner_sum`, `sum_inner`, `inner_smul_left`, `inner_smul_right`, `real_inner_self_eq_norm_sq`, and `Finset.sum_comm`. This is usually easier to prove by rewriting squared norms as self-inner-products than by manipulating norms directly.

**2. Orthogonal-chain pooling.** Prove that cross-chain Gram entries vanish. This isolates the factor \(1/C\) in the mean-square correction.

**3. AR(1) Gram table.** First establish
\[
x_k=\sum_{j=1}^k\rho^{k-j}\eta_j.
\]
Use noise orthogonality and a finite geometric sum to obtain B1. State B1 for \(k\le l\), then use inner-product symmetry for the reverse order.

**4. Toeplitz sum.** Prove separately
\[
\sum_{i,j<N}\rho^{\operatorname{dist}(i,j)}
=N+2\sum_{m=1}^{N-1}(N-m)\rho^m.
\]
This is a reusable finite-combinatorics result independent of AR(1).

For internal indexing, I would favor
```lean
i : Fin N
k i := b + i.val + 1
```
and `c : Fin C`. It makes cardinalities and product-index pooling simple. An `Ico`-indexed wrapper can then match the note.

For the Toeplitz proof, split into diagonal, upper triangle, and lower triangle; count upper-triangular pairs at distance \(m\). Do not combine that reindexing argument with the inner-product expansion in one large proof.

## 5. Nearby candidates worth considering

### A general curved-Gaussian valley

A natural reusable extension of A is
\[
L_g(x,y)=\frac{(x-\mu)^2+a(y-g(x))^2}{2}.
\]
For measurable \(g\), the same shear gives
\[
\mathcal Z_g=\frac{2\pi}{t\sqrt a}.
\]
Under the Gibbs measure,
\[
X\sim N(\mu,1/t),\qquad Y=g(X)+U,
\]
with independent \(U\sim N(0,1/(ta))\). Subject to the needed moment integrability,
\[
E[Y]=E[g(X)],
\]
\[
\operatorname{Cov}(X,Y)=\operatorname{Cov}(X,g(X)),
\qquad
\operatorname{Var}(Y)=\operatorname{Var}(g(X))+\frac1{ta}.
\]
For polynomial \(g\), the integrability infrastructure proposed above handles these automatically.

This is probably the best abstraction boundary for A: formalize the shear generally, but keep the first numerical moment application Rosenbrock-specific.

### Exact energy fluctuations for Rosenbrock

A cheap follow-on to A is
\[
E[L^2]=\frac2{t^2},
\qquad
\operatorname{Var}(L)=\frac1{t^2}.
\]
It uses the same degree-four Gaussian moments and strengthens the exact \(tE[L]=1\) statement.

The full statement that \(L\) is exponential with rate \(t\) is mathematically natural, but importing distributional machinery may make it a worse immediate target.

### ULA trace bias and bounds

Once C is proved, a useful compact cluster is
\[
\mathrm{LLC}_{\rm ULA}-\frac d2
=\frac12\sum_i
\frac{hp_i/2}{1-hp_i/2}.
\]
For \(h\ge0\) and \(hp_{\max}<2\),
\[
\frac d2
\le \mathrm{LLC}_{\rm ULA}
\le \frac{d}{2(1-hp_{\max}/2)}.
\]
This both quantifies inflation and states correctly what can be concluded from only the largest eigenvalue. It is a good low-risk excursion if the nonlinear transport work proves too large.

**Vote: A0–A5 alone—exact Rosenbrock Gibbs moments and covariance–Laplace discrepancy, built on a reusable measure-preserving shear lemma.**