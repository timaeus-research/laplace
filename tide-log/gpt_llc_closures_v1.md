## 1. Mathematical checks

### A. Minibatch inflation: correct, with the stated noise convention

Write
\[
d_i=1-\frac{hp_i}{2},\qquad c_i=(U^\top C U)_{ii}.
\]
Under \(h>0\), \(p_i>0\), and \(hp_i<2\), the covariance formula gives
\[
L_{\rm mb}:=\frac12\operatorname{tr}(P\Sigma_{\rm mb})
=\frac12\sum_i\frac{1+ht^2c_i/2}{d_i}.
\]
Consequently,
\[
\Delta:=L_{\rm mb}-L_{\rm ULA}
=\frac{ht^2}{4}\sum_i\frac{c_i}{d_i}.
\]

This is exactly consistent with injected covariance
\[
2hI+h^2t^2C_g.
\]
Here \(C_g\) must mean the covariance of the gradient noise **before multiplying it by \(t\)**. If it already includes that scaling, the extra \(t^2\) must disappear. Given the convention in the question, your coefficient is correct.

PSD gives \(c_i\ge0\), and orthogonality gives
\[
\sum_i c_i=\operatorname{tr}(U^\top C U)=\operatorname{tr}C.
\]
If \(p_i\le p_{\max}\) and \(hp_{\max}<2\), then
\[
\frac{ht^2}{4}\operatorname{tr}C
\le \Delta
\le \frac{ht^2}{4(1-hp_{\max}/2)}\operatorname{tr}C.
\]

**Wording qualification:** dividing these bounds by \(d/2\) gives inflation **normalised by the continuous-target LLC \(d/2\)**. It is not the same as \(\Delta/L_{\rm ULA}\). Also, total inflation above \(d/2\) includes the ordinary ULA discretisation bias as well as this minibatch increment. Require \(d>0\) for the normalised statement.

For Lean, I would prove the exact identity without PSD, then use PSD only in the inequality layer.

### B. Running mean: correct

Indeed,
\[
s_i^2=\frac{2h}{1-(1-hp_i)^2}
=\frac{1}{p_i(1-hp_i/2)},
\]
hence
\[
s_i^2\,t\lambda_i=s_i^2p_i=\frac1{1-hp_i/2}.
\]

For the mode-started chain, draw \(k\) therefore has expected loss-based LLC
\[
\frac12\sum_i\frac{1-\rho_i^{2k}}{1-hp_i/2}.
\]

For \(N>0\), averaging \(k=b+1,\ldots,b+N\) gives precisely your formula, because
\[
\frac1N\sum_{n=0}^{N-1}\rho_i^{2(b+1+n)}
=\frac{\rho_i^{2(b+1)}(1-\rho_i^{2N})}{N(1-\rho_i^2)}.
\]
Stability gives \(|\rho_i|<1\), so the shortfall is nonnegative and your upper bound follows from \(1-\rho_i^{2N}\le1\). Negative \(\rho_i\) causes no problem here: only even powers occur.

For a pooled average over \(C_{\rm chains}>0\) chains, the expectation is unchanged. **Independence between chains is not needed for this expectation identity**, only the appropriate marginal expectations.

The phrase “burn-in-only bias” is correct **relative to \(L_{\rm ULA}\)**. Relative to the continuous-target LLC, there is still discretisation bias. Absence of an autocorrelation bias term does not mean absence of autocorrelation effects on estimator variance.

### C. \(20\kappa\): correct, but label exactly what is controlled

If
\[
p_{\min}=p_{\max}/\kappa,\qquad hp_{\max}=1/10,
\]
then \(hp_{\min}=1/(10\kappa)\), and
\[
\frac{2}{hp_{\min}C_{\rm chains}N}
=\frac{20\kappa}{C_{\rm chains}N}.
\]
For \(\rho=1-hp_{\min}\), the more precise factor is
\[
\frac{1+\rho}{1-\rho}=20\kappa-1.
\]
Thus your \(20\kappa\) bound is slightly conservative.

I would state the budget condition as
\[
(C_{\rm chains}N:\mathbb R)\ge20\kappa M,\qquad M>0,
\]
rather than equality: draw counts are integers, whereas \(\kappa\) generally is not. This makes the autocorrelation contribution at most \(1/M\); **the burn-in contribution remains separate**.

Also check the hypotheses of the existing shortfall theorem. If it requires \(0\le\rho<1\), then \(p_{\max}\ge p_{\min}>0\), hence \(\kappa\ge1\), makes those hypotheses immediate.

## 2. Quadratic form: use the matrix route

I would **not build an `OrthonormalBasis` for this task**. You already have exactly the spectral factorisation and concrete columns you need.

Prove one reusable finite-dimensional lemma:
\[
H=U\operatorname{diag}(\lambda)U^\top
\quad\Longrightarrow\quad
x\mathbin{\cdot}(H x)
=\sum_i\lambda_i\bigl((U^\top x)_i\bigr)^2.
\]
This identity itself does not require a separate orthogonality hypothesis once the factorisation is supplied.

A robust proof decomposition is:

1. Define \(y=U^\top x\).
2. Use matrix/vector multiplication associativity to obtain
   \[
   Hx=U(\operatorname{diag}(\lambda)y).
   \]
3. Establish the elementary identity
   \[
   x\cdot(Uz)=(U^\top x)\cdot z.
   \]
4. Simplify the diagonal action.
5. Connect coordinates to the Euclidean inner product:
   \[
   (U^\top x)_i
   =\sum_j U_{ji}x_j
   =\langle\operatorname{orthoCol}(i),x\rangle.
   \]

`Matrix.mulVec_mulVec` and `Matrix.diagonal_mulVec` are standard names I would check first. I would not make the proof depend on remembering the exact argument orientation of `dotProduct_mulVec` or a transpose lemma. The key transpose/dot-product identity is a short finite-sum proof using `Finset.sum_comm` and commutativity of real multiplication.

Keep the matrix lemma on ordinary functions `ι → ℝ`, then add a thin `EuclideanSpace`/`toLp` wrapper. That avoids mixing matrix algebra with coercion normalisation throughout the main proof.

One further simplification: for the LLC theorem, diagonalise **\(P\)** and work directly with
\[
\frac12\langle x,Px\rangle.
\]
Convert to \((t/2)\langle x,Hx\rangle\) using \(P=t\smul H\) only at the boundary. This avoids introducing \(\lambda_i=p_i/t\) and unnecessary division-by-\(t\) obligations.

## 3. Which route for B?

There are two distinct deliverables:

- the average of the expected LLCs of the trajectory measures;
- the expectation of the actual pooled estimator on \(\Omega\).

The measure-level theorem makes the first easy, but does not automatically establish the second.

### Spectral evaluation at measure level

Conjugating the transient covariance gives
\[
\operatorname{tr}\!\left(PA^k\Sigma(A^\top)^k\right)
=\sum_i\frac{\rho_i^{2k}}{1-hp_i/2}.
\]
Thus `llc_ula_trajectory` immediately yields the single-time formula, followed by finite-sum algebra for the running mean.

This avoids all new square-integrability work. It is the quickest route **if a theorem already identifies the law of `ulaChain ... k` with that trajectory measure**.

### For the actual pooled estimator

If that law-identification bridge is absent, I would use your existing Ω-level projection/AR(1) infrastructure. Building a new distributional bridge could cost more than the direct moment calculation.

The useful intermediate theorem is simply
\[
\int \langle u_i,x_k\rangle^2
=s_i^2(1-\rho_i^{2k}),
\]
together with integrability of the square. Then the quadratic-form identity and integral linearity finish the single-time result.

For square integrability, if convenient, use the `MemLp.mul` route: two `MemLp 2` factors give an integrable product, then rewrite multiplication as a square. Be careful that the L² norm/integral theorem initially gives an integral of a squared norm; over \(\mathbb R\), simplify that to the ordinary square.

**My choice for this tide:** extract the finite geometric-sum calculation as a purely algebraic lemma, and use the Ω-level route for the promised pooled-estimator theorem unless the marginal-law bridge already exists. The existing `expected_pooled_sample_variance_ula` template is a strong reason not to introduce a second probability interface.

## 4. Scope and worthwhile additions

A+B+C is a coherent tide, but **400 lines is optimistic if B needs fresh integrability and quadratic-form infrastructure**. A and C are close to the seabed; B is the main uncertainty. A several-hundred-line result is plausible, but I would not constrain it to 400.

Suggested order:

1. A: trace identity and exact inflation.
2. A: PSD bounds and trace preservation.
3. C: scalar arithmetic corollary.
4. B: projected second moment, spectral quadratic form, pooled mean.

The best small addition is the explicit remainder bound. Set
\[
L_0=\frac{ht^2}{4}\operatorname{tr}C.
\]
Then
\[
\Delta-L_0
=\frac{h^2t^2}{8}\sum_i\frac{p_i c_i}{1-hp_i/2},
\]
and therefore
\[
0\le\Delta-L_0
\le
\frac{h^2t^2p_{\max}}{8(1-hp_{\max}/2)}
\operatorname{tr}C.
\]
You can derive the bound directly from A’s two-sided bound:
\[
\Delta-L_0\le L_0\frac{hp_{\max}/2}{1-hp_{\max}/2}.
\]
That makes “about” precise without asymptotic machinery. For a conventional uniform \(O(h^2)\) interpretation, additionally bound \(hp_{\max}/2\) away from \(1\).

I would add this before any further relative-error variants; normalisation by \(d/2\) is then just a corollary.

**Vote: A+B+C.** Qualifications: minibatch inflation is the increment above ULA; dimension-normalised inflation is not inflation relative to ULA; B’s burn-in-only bias is relative to the ULA stationary LLC; and C controls the autocorrelation contribution, not the whole finite-chain shortfall.