**Vote: A+B+C.** All three are correct under the inherited E2 hypotheses. Prioritise the exact bridge and the general rate; make the specialised corollaries cheap wrappers.

### 1. Correctness and hypotheses

- **No symmetry assumption on \(B\) is needed.** Every expression depends only on \(\operatorname{sym}B=(B+B^\top)/2\): \(C,H^{-1},V\) are symmetric, and a quadratic form annihilates the skew part.
- Your trace identification is correct:
  \[
  \operatorname{tr}(BC)=\sum_{j,k}B_{jk}C_{kj}
  =\sum_{j,k}B_{jk}C_{jk}.
  \]
  Likewise \((Q^\top BQ)_{ii}=\sum_{j,k}Q_{ji}B_{jk}Q_{ki}\), with no transpose correction needed.
- No extra anchor restriction or positivity condition on \(B\). Keep \(B,Q,c,g,w_0\) and the family parameters **fixed in \(t\)**. The localiser must be \(t\)-independent, as in the stated setup; otherwise the derivative’s score acquires an extra term.
- Coercivity, positive Hessian, nonzero normalisation and the required integrability are inherited from E2. Constants \(K,T\) may depend on \(B\) and all fixed parameters.
- The relative-form remark is valid for symmetric PSD nonzero \(B\), since then \(\operatorname{tr}(BH^{-1})>0\).

**No mathematical error found in A–C.**

### 2. Best Lean route for B

**Use the frame route given the landed API.** The off-diagonal cancellation is already available, whereas the frozen-probe route needs derivative support for an arbitrary quadratic probe and differentiability of the physical mean.

Keep the algebra modular:

1. Prove `localised_mean_coord`.
2. Prove the pointwise centred-coordinate transport.
3. Establish a centred-frame-pair lemma:
   \[
   \operatorname{Cov}_t\!\left(L,(u_i-\mu_i)(u_j-\mu_j)\right)
   =
   \begin{cases}D_i,&i=j,\\0,&i\ne j.\end{cases}
   \]
4. Expand the quadratic into finite scalar sums and apply that lemma.

This avoids making a large matrix quadratic-form identity carry the analytic proof. Also isolate `trace_mul_conj_diagonal` as reusable algebra.

The frozen-probe argument is mathematically excellent and works even without separability. Its key identity is indeed
\[
\langle\psi_m\rangle_s
=\operatorname{tr}(BC(s))+(m(s)-m)^\top B(m(s)-m),
\]
whose extra derivative vanishes at \(s=t\), **also for nonsymmetric \(B\)**.

**Pitfall:** do not apply the fixed-observable Gibbs derivative theorem directly to the moving probe \(\psi_{m(s)}\). Its parameter derivative has zero expectation, but that cancellation must be proved.

### 3. Wording and interpretation

Your invariant statement is right. I would say **“\(B\)-weighted centred covariance trace”** rather than “centred second moment” to prevent confusion with the raw moment.

For \(B=H\), state both conventions explicitly:
\[
-\partial_t\operatorname{tr}(HC(t))
=\frac d{t^2}+\frac{2\sum_i\lambda_i v_i}{t^3}+O(t^{-4}),
\]
and, for the frozen centred Gaussian quadratic energy
\(E_t(w)=\tfrac12(w-m(t))^\top H(w-m(t))\),
\[
\operatorname{Cov}_t(L\circ A,E_t)
=\frac d{2t^2}+\frac{\sum_i\lambda_i v_i}{t^3}+O(t^{-4}).
\]

**Worth stating**, while distinguishing this probe from the full anharmonic energy and the localiser’s potential.

Crucially, the derivative expansion follows from your derivative estimates—not by formally differentiating the note’s \(C=S+O(S^2)\).

### 4. Nearby candidates and next target

Best next target: **quantify the discrepancy from the Gaussian-prior covariance**. Given the covariance expansion with remainder \(O(t^{-3})\),
\[
S(t)=t^{-1}H^{-1}-g\,t^{-2}H^{-2}+O(t^{-3})
\]
yields
\[
C(t)-S(t)=t^{-2}(V+gH^{-2})+O(t^{-3}),
\]
and hence
\[
\left|\|C(t)-S(t)\|_F^2
-\frac{\|V+gH^{-2}\|_F^2}{t^4}\right|
\le \frac K{t^5}
\]
eventually. The coefficient is explicitly
\[
\|V+gH^{-2}\|_F^2=\sum_i\left(v_i+\frac g{\lambda_i^2}\right)^2.
\]
This connects directly to the note and cancels the pure Gaussian-localiser contribution.

Raw second moments are less invariant and introduce mean-drift terms. Third-cumulant derivatives are interesting but likely demand more new moment machinery.

**Commit A+B+C; if time tightens, cut specialised corollaries before cutting B.**