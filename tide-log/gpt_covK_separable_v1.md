## 1. Correctness of A–C

**All three are correct**, with one dependency worth making explicit: C needs a one-dimensional mean limit, in addition to the listed covariance limits.

### A: single-coordinate covariances

Writing \(E_i\) and \(\operatorname{Cov}_i\) for expectation and covariance under the \(i\)-th marginal, product factorisation gives, for \(k\ne i\),
\[
E_L[f(u_k)g(u_i)]=E_k[f]E_i[g].
\]
Together with coordinate reduction, this proves
\[
\operatorname{Cov}_L[f(u_k),g(u_i)]=0.
\]
When \(k=i\), apply coordinate reduction to \(f\), \(g\), and \(fg\):
\[
\operatorname{Cov}_L[f(u_k),g(u_k)]
=\operatorname{Cov}_k[f,g].
\]

The hypotheses \(Z_m\ne0\) are important for eliminating the unused coordinates. Given the hypothesis-free product theorem and coordinate-reduction theorem described in the seabed, A should not need extra integrability hypotheses **as an identity for your totalised definitions**. For its usual probabilistic interpretation, the relevant moments should exist; they do for the polynomial observables used here.

### B: diagonal probes

The exact reduction is right:
\[
\operatorname{Cov}_L[L,\psi]
=\sum_i\operatorname{Cov}_i
 \left[\ell_i,\frac{B_i}{2}x^2+b_ix\right].
\]
Finite summation of the one-dimensional limits then gives the proposed limit.

The main bookkeeping obligation is the integrability needed for covariance bilinearity. In particular, check the **mixed products**
\[
\ell_k(u_k)\psi_i(u_i)e^{-tL(u)},
\]
not only the energy and probe separately. These follow by expanding the anharmonic energy and probe into finitely many monomials and using `integrable_monomial_separableAnharmonic`. They are not an additional analytic obstacle.

The diagonal matrix identification and rotated-frame corollary are appropriate final wrappers.

### C: off-diagonal probes

Both exact identities in the question are correct. For pairwise distinct \(k,i,j\),
\[
E_L[\ell_k(u_k)u_i u_j]
=E_k[\ell_k]E_i[x]E_j[x],
\]
and
\[
E_L[\ell_k(u_k)]E_L[u_i u_j]
=E_k[\ell_k]E_i[x]E_j[x].
\]
Thus the covariance vanishes exactly.

For \(i\ne j\),
\[
\operatorname{Cov}_L[\ell_i(u_i),u_i u_j]
=E_j[x]\operatorname{Cov}_i[\ell_i,x].
\]
Consequently, the useful exact endpoint is
\[
\boxed{
\operatorname{Cov}_L[L,u_i u_j]
=E_j[x]\operatorname{Cov}_i[\ell_i,x]
 +E_i[x]\operatorname{Cov}_j[\ell_j,x].
}
\]
The off-diagonal covariance is generally **not** exactly zero: the two displayed contributions remain.

Your proposed asymptotic argument works if \(tE_j[x]\) has a finite limit. But there is an easier route:
\[
t^2\operatorname{Cov}_L[L,u_i u_j]
=E_j[x]\bigl(t^2\operatorname{Cov}_i[\ell_i,x]\bigr)
 +E_i[x]\bigl(t^2\operatorname{Cov}_j[\ell_j,x]\bigr).
\]
Use the existing `covK_anharmonic_lin` limits and only
\[
E_i[x]\longrightarrow0.
\]

**Make this mean-limit dependency explicit.** It is weaker than the scaled-mean asymptotic in the proposed proof, but it is not explicitly included in the seabed list. If a scaled-mean theorem is already available, either approach is fine.

For the full quadratic probe, symmetry of \(B\) is not needed for the limiting statement: expand
\[
\frac12\sum_{i,j}B_{ij}u_i u_j.
\]
The diagonal terms give B, and every off-diagonal term tends to zero after scaling.

## 2. Least painful Lean route

I would use **a small sparse-product helper internally, with separate readable lemmas for the patterns actually needed**. Avoid a public theorem stated as “all but at most three factors are one”; that adds support bookkeeping without helping the main proof.

Suggested sequence:

1. **Two distinct coordinates**
   \[
   E_L[f(u_i)g(u_j)]=E_i[f]E_j[g]\qquad(i\ne j).
   \]
   Prove this once using `gibbsExpectation_prod_separable` and an `if`-defined factor family.

2. **A from coordinate reduction and the two-coordinate lemma.**  
   Split on \(i=j\). In the equal case, use the single-coordinate observable \(x\mapsto f(x)g(x)\); do not force repeated indices through the sparse-product encoding.

3. **Three pairwise-distinct coordinates**
   \[
   E_L[f(u_k)g(u_i)h(u_j)]
   =E_k[f]E_i[g]E_j[h].
   \]
   Reuse the same product-simplification machinery.

4. **C via three local cases:** \(k=i\), \(k=j\), or neither.  
   In the first two cases, combine the factors on the repeated coordinate before applying the two-coordinate lemma. In the third, use the three-coordinate lemma.

5. **Sum the coordinate-energy covariances**, obtaining the boxed two-term identity above. Prove the limit from that identity, rather than interleaving index case analysis with `Tendsto` arguments.

For the finite-product simplifications, an internal lemma for a family equal to \(1\) outside a specified finite set can be useful. But start with the two-coordinate proof; generalise only if the triple-coordinate proof genuinely duplicates substantial work.

A practical Lean detail: provide both orientations of the relevant inequalities to simplification, rather than expecting nested `if`s to discover them automatically.

This architecture keeps the separation clean:

- product identities and coordinate reduction;
- integrability and finite-sum bilinearity;
- one-dimensional limits and finite-limit algebra.

## 3. Is B a coherent tide without C?

**Yes.** A+B is a coherent, substantial result: it lifts the verified one-dimensional asymptotic to a separable \(d\)-dimensional energy, identifies the diagonal eigenframe coefficient, and transports it through rotation.

However, **B alone does not cover arbitrary random quadratic probes**. A probe diagonal in the energy eigenframe becomes a generally dense matrix after rotation, but it still belongs to a restricted family aligned with that eigenframe. It is not an arbitrary ambient quadratic.

So the honest scope is:

- **A+B:** covK for eigenframe-diagonal quadratic probes, including their rotated versions.
- **A+B+C:** covK for general quadratic probes on the separable oscillator, matching E2’s stated probe class.

B is therefore a good completed checkpoint, not a substitute for C when claiming coverage of E2’s random quadratics.

## Vote

**Formalise A+B+C, staged in that order, with A+B as the fallback completed tide.** C is needed for the full E2 claim, and the exact two-term identity plus the weaker mean limit \(E_i[x]\to0\) should keep its analytic burden small.