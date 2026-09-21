## 1. Correctness of the candidates

### A1: correct

Write \(h=\mathrm{lr}\) and \(B=I-\frac h2P\). Under
\[
P=P^\top\succ0,\qquad h>0,\qquad 2I-hP\succ0,
\]
both \(B\) and
\[
PB=P-\frac h2P^2
\]
are symmetric positive definite. Since \(P\) and \(B\) commute,
\[
\Sigma_{\mathrm{ULA}}=P^{-1}B^{-1}=(PB)^{-1}
\]
is symmetric positive definite.

The useful algebraic identity is
\[
I-A^2=2hPB,\qquad A=I-hP.
\]
Because \(\Sigma_{\mathrm{ULA}}\) commutes with \(A\),
\[
\Sigma_{\mathrm{ULA}}-A\Sigma_{\mathrm{ULA}}A
=(I-A^2)\Sigma_{\mathrm{ULA}}=2hI.
\]

This is a good standalone theorem. It needs no probability or infinite series.

### A2: correct, with an important symmetry qualification

For an arbitrary real matrix \(A\), the hypothesis
\[
\|A\|_{2\to2}<1
\]
is sufficient for a unique solution, among **all real matrices**, to
\[
\Sigma=A\Sigma A^\top+N.
\]
The solution is
\[
\Sigma_\infty=\sum_{k=0}^\infty A^kN(A^\top)^k.
\]
Symmetry of \(N\) is needed for symmetry of the solution, not for existence or uniqueness. If \(N\succeq0\), then \(\Sigma_\infty\succeq0\); if \(N\succ0\), then \(\Sigma_\infty\succ0\).

The finite recursion formula and convergence are also correct.

However, the further assertions
\[
\Sigma_k=\Sigma_\infty(I-A^{2k}),\qquad
\Sigma_\infty=(I-A^2)^{-1}N
\]
require **\(A=A^\top\)** as well as \(AN=NA\). Commutation of \(N\) with a general nonsymmetric \(A\) is not enough. In your ULA setting, symmetry is inherited from \(P\), so these assertions are fine; make that hypothesis explicit in a general-purpose theorem.

There is also a stronger finite-time identity, requiring no commutation:
\[
\boxed{\Sigma_k=\Sigma_\infty-A^k\Sigma_\infty(A^\top)^k}
\]
for the recursion started at zero. More generally,
\[
\Sigma_k-\Sigma_\infty
=A^k(\Sigma_0-\Sigma_\infty)(A^\top)^k.
\]
Once a fixed point is known, this follows by induction and proves convergence directly.

Two scope qualifications:

* Operator-norm contraction is sufficient, not necessary, for general nonsymmetric \(A\). Spectral radius \(<1\) is the usual broader stability condition.
* This finite-time covariance is **not yet the expected empirical sample variance** discussed in the note. Burn-in, pooling and sample-mean subtraction require temporal cross-covariances.

### A3: correct—and the diagonal claim can be strengthened

When \(C\) commutes with \(P\), choose a common orthonormal eigenbasis. Then
\[
(\Sigma_{\mathrm{mb}})_{ii}
=\frac{1+ht^2c_i/2}{p_i(1-hp_i/2)}.
\]
If \(P\) has repeated eigenvalues, an arbitrary eigenbasis of \(P\) need not diagonalise \(C\); say “a common eigenbasis.”

In fact, **commutation is unnecessary for the directional variance formula**. In any orthonormal eigenbasis of \(P\), write \(\widetilde C\) for the matrix of \(C\). Then
\[
\boxed{
\widetilde\Sigma_{ij}
=\frac{2h\,\delta_{ij}+h^2t^2\widetilde C_{ij}}
       {h(p_i+p_j)-h^2p_ip_j}.
}
\]
Consequently,
\[
\widetilde\Sigma_{ii}
=\frac{1+ht^2\widetilde C_{ii}/2}
       {p_i(1-hp_i/2)}
\]
without \(CP=PC\). Here \(\widetilde C_{ii}=v_i^\top Cv_i\), not necessarily an eigenvalue of \(C\).

This arbitrary-\(C\) formula is an especially attractive formalisation target.

The one-dimensional finite-time formula is correct for \(x_0=0\) and fresh independent centred innovations of variance \(2h\).

### Stability equivalence

For a nonempty finite-dimensional space, positive-definite symmetric \(P\), and \(h>0\),
\[
\|I-hP\|_{2\to2}=\max_i|1-hp_i|.
\]
Therefore
\[
\|I-hP\|_{2\to2}<1
\iff 0<hp_i<2\ \text{for every }i
\iff h\lambda_{\max}(P)<2.
\]

**The Euclidean operator norm matters.** The natural norm on `ι → ℝ` is a sup norm, not the Euclidean norm. The corresponding induced operator norm does not generally satisfy this equivalence.

For Lean, an eigenvalue-wise condition avoids both this norm issue and the empty-index issue associated with a maximum.

### B: correct

Under independence,
\[
AX+\sqrt{2h}\,\xi
\sim\mathcal N(0,A\Sigma A^\top+2hI).
\]
Thus A1 yields invariance of \(\mathcal N(0,\Sigma_{\mathrm{ULA}})\).

This establishes invariance, not automatically uniqueness of the invariant probability law. Uniqueness of a covariance fixed point is a different statement.

Also, do not silently extend Gaussian invariance to actual minibatch noise: its covariance can obey the Lyapunov law while its distribution is non-Gaussian.

### C: correct with explicit hypotheses

Assume \(H\) is symmetric and \(P=tH+\gamma I\succ0\). Then the centred Gaussian target gives
\[
\mathbb E[K]=\frac12\operatorname{tr}(HP^{-1}).
\]
For the specialisation \(\gamma=0\), require \(t>0\) and \(H\succ0\). Then
\[
t\mathbb E[K]=d/2.
\]

For the eigenvalue expression, state the usual \(H\succ0\), \(t>0\), \(\gamma\ge0\) assumptions, or more generally require all \(t\lambda_i+\gamma>0\).

The centre must be the minimiser. A displaced Gaussian mean \(\mu\) adds
\[
\frac12\mu^\top H\mu
\]
to \(\mathbb E[K]\).

## 2. What is realistic for one tide?

**I would back an algebraic/eigenbasis version of A, with C as a small bridge to the existing repository. I would defer B.**

I would not make “all of A via a generic Neumann-series development” the indivisible target. A useful sequence is:

1. **Diagonal Lyapunov solver.** For \(D=\operatorname{diag}(a_i)\), \(|a_i|<1\), prove that
   \[
   X_{ij}=\frac{N_{ij}}{1-a_ia_j}
   \]
   is the unique solution of \(X=DXD+N\).

2. **Transport through an orthogonal diagonalisation.** This gives the symmetric-matrix Lyapunov theorem and the arbitrary-\(C\) formula above.

3. **ULA closed form and positivity.**

4. **Finite-time identity**, proved by induction against the fixed point.

5. **Quadratic Gaussian expectation/LLC**, using the existing Gaussian second-moment theorem.

This gives the principal sampler-side predictions without constructing a Markov chain.

### Spectral route versus Neumann route

For this tide, the spectral route has a major advantage: after diagonalisation, the Lyapunov operator itself is diagonal on matrix entries:
\[
X_{ij}\longmapsto a_i a_jX_{ij}.
\]
Existence and uniqueness become scalar algebra. Finite-time convergence becomes convergence of finitely many geometric sequences.

The Neumann route is more reusable for nonsymmetric dynamics and the future “full law,” but brings additional infrastructure:

* a suitable complete normed space of matrices or operators;
* a submultiplicative norm;
* transpose/adjoint norm control;
* summability and shifting of infinite sums;
* identification of the selected matrix norm with Euclidean spectral information.

It is reasonable infrastructure work, but less tightly focused on this note’s first laws.

B is mathematically short but has a larger integration risk: Gaussian covariance representations, matrix-to-operator conversions, product measures or independence, and distribution identification. It can be its own next tide after the algebraic covariance layer exists.

## 3. Better nearby candidates

### Best addition: noncommuting minibatch noise

The arbitrary-\(C\) entry formula above is stronger than the commuting corollary and uses essentially the same spectral proof.

It also exposes exactly what noncommutation does: it creates off-diagonal covariance in the precision eigenbasis, while the diagonal inflation formula remains unchanged.

### A small, useful order theorem

For stable \(A\), the Lyapunov solution is monotone in the injected covariance:
\[
N_1\preceq N_2
\quad\Longrightarrow\quad
\Sigma(N_1)\preceq\Sigma(N_2).
\]
Hence additive minibatch noise implies
\[
\Sigma_{\mathrm{mb}}\succeq\Sigma_{\mathrm{ULA}}.
\]
For \(H\succeq0\), this also increases \(\frac12t\operatorname{tr}(H\Sigma)\).

This is particularly natural once a finite-sum/series representation has been established.

### Finite-chain covariance before empirical sample variance

The exact identity
\[
\Sigma_k-\Sigma_\infty
=A^k(\Sigma_0-\Sigma_\infty)(A^\top)^k
\]
is the best low-cost finite-chain target.

The next probabilistic extension should establish, for centred innovations independent of the past,
\[
\operatorname{Cov}(x_{r+\ell},x_r)=A^\ell\Sigma_r.
\]
That is the ingredient needed for expected sample-mean-subtracted variance and burn-in corrections. It would connect more directly to the note’s finite-chain diagnostic than Gaussian invariance alone.

### Full state-dependent law: worthwhile, but separate

The note’s full law is correct under appropriate assumptions:

* quadratic per-sample losses;
* fresh batches independent of the current state;
* unbiased minibatch gradients;
* centred state mean, as holds when starting at the minimiser;
* independent centred Langevin noise.

The centring condition matters because minibatch gradient offsets and minibatch Hessian fluctuations can be correlated; their cross terms vanish here because the state mean is zero.

Define a positive linear operator
\[
\mathcal T(X)
=AXA^\top+
h^2t^2c\sum_i D_iXD_i^\top.
\]
The covariance recursion is \(\Sigma_{k+1}=\mathcal T(\Sigma_k)+N\).

Crucially, **\(h\lambda_{\max}(P)<2\) no longer guarantees second-moment stability**. The extra multiplicative-noise term can destabilise \(\mathcal T\). A contraction or spectral-radius hypothesis must be imposed on \(\mathcal T\), not just on \(A\).

This is a good later application of a general fixed-point theorem for linear operators. Kronecker/vec notation is not necessary; it is likely more representation overhead than help initially.

### One-loop covariance: defer

The displayed one-loop formula is an asymptotic truncation, not an exact covariance identity for a general potential. A formal theorem needs a remainder and a precise scaling regime.

Existing higher-order covariance machinery may help, but extracting the \(t^{-2}\) coefficient of coordinate covariance still requires the relevant Gaussian contractions, normalisation terms, centring cancellations and remainder control. This is a different tide from sampler-side linear algebra.

## 4. Lean representation and proof interfaces

### Main statements: matrices

Use `Matrix ι ι ℝ`, with `[Fintype ι] [DecidableEq ι]`, for:

* precision, covariance and noise matrices;
* transpose;
* `Matrix.PosDef` and `Matrix.PosSemidef`;
* the Lyapunov equation;
* explicit entry and trace formulas.

This aligns with the desired statements and the matrix-facing multivariate Gaussian API.

Use continuous linear maps on **`EuclideanSpace ℝ ι`** when operator norms or Gaussian pushforwards are needed. Do not use the norm on `(ι → ℝ) →L[ℝ] (ι → ℝ)` as though it were the Euclidean spectral norm.

The existing IBP theorem can be connected by a conversion lemma. Keep that conversion at the boundary rather than forcing the entire sampler development into its representation.

### Inverses and positivity

I would lean on these interfaces, checking their precise names in the pinned checkout:

* positive definiteness implies invertibility/nonsingular determinant;
* `Matrix.mul_nonsing_inv` and `Matrix.nonsing_inv_mul`;
* transpose compatibility with inverse;
* positivity under congruence;
* orthogonal spectral decomposition.

A practical proof can establish the algebraic fixed-point identity under invertibility assumptions first, and discharge positivity/invertibility from the spectral hypotheses separately.

### Commutation

Avoid a general “rational functions of \(P\)” development. Establish only:

* \(P\) commutes with \(I-\frac h2P\) and \(I-hP\);
* commuting invertible elements commute with each other’s inverses;
* the resulting inverse product identity.

The generic `Commute` API is useful, but matrix `nonsing_inv` is a total operation and some abstract inverse lemmas expect units or a group. Explicit inverse identities, or temporarily packaging invertible matrices as units, may be simpler.

### Spectral norm bound

Use orthogonal diagonalisation on Euclidean space and the fact that the norm of a diagonal self-adjoint operator is the maximum absolute diagonal entry.

I would **not** require this equivalence to land in the first tide. State the initial spectral Lyapunov theorem using \(|a_i|<1\), and add the operator-norm wrapper afterward.

### Summability

If using the analytic route, the basic estimate is
\[
\|A^kN(A^\top)^k\|
\le \|N\|\,(\|A\|^2)^k.
\]
Then use geometric summability and norm comparison in a complete normed space. Ensure the selected matrix norm is actually submultiplicative and transpose-compatible; matrix topology instances alone do not provide those estimates.

Under the spectral route, instead prove summability entrywise from
\[
\sum_{k\ge0}(a_i a_j)^kN_{ij}.
\]
Finite-index matrix summability and scalar geometric-series results then do the work.

## Recommendation

**Back a tight “spectral Lyapunov laws + quadratic LLC” cluster:**

* unique Lyapunov solution for symmetric stable \(A\);
* ULA closed form, positive definiteness and uniqueness;
* arbitrary-\(C\) minibatch covariance entries, with the commuting case as a corollary;
* exact finite-time covariance identity;
* the Gaussian quadratic expectation/LLC bridge to the seabed.

Make the generic operator-norm Neumann theorem and Gaussian invariance separate follow-ups. This cluster captures the note’s central sampler predictions, strengthens its commuting-noise statement, and keeps the first tide primarily in finite-dimensional algebra rather than measure-theoretic plumbing.