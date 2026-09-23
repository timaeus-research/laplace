## 1. Checks of A–D

**Yes: A–D are correct**, assuming \(P\) is symmetric positive definite, \(H,B\) are symmetric, and—in the eigenframe formulas—\(\lambda_i>0\), \(p_i=t\lambda_i+g>0\). For the simple remainder bounds below, take \(t>0\), \(g\ge0\).

### A: mixed Gaussian covariances

For the centered Gaussian, the three Wick contractions give
\[
\int (u^\top Hu)(u^\top Bu)\,gw
=Z\left(\operatorname{tr}(H\Sigma)\operatorname{tr}(B\Sigma)
       +2\operatorname{tr}(H\Sigma B\Sigma)\right).
\]
Both cross contractions equal the displayed mixed trace, using symmetry of \(H,B,\Sigma\).

Writing \(u=m+z\), the centered quadratic and linear pieces are orthogonal by oddness. Thus
\[
\operatorname{Cov}(u^\top Hu,u^\top Bu)
=2\operatorname{tr}(H\Sigma B\Sigma)
 +4(Hm)^\top\Sigma(Bm).
\]
The last scalar is automatically symmetric:
\[
(Hm)^\top\Sigma(Bm)=(Bm)^\top\Sigma(Hm),
\]
because \(\Sigma^\top=\Sigma\). No additional symmetrisation is needed.

Likewise,
\[
\operatorname{Cov}(u^\top Hu,b^\top u)
=2b^\top\Sigma(Hm).
\]

### B: eigenframe formula

Combining A with the two factors of \(1/2\) gives
\[
\operatorname{Cov}\left(\tfrac12u^\top Hu,
                  \tfrac12u^\top Bu+b^\top u\right)
=\tfrac12\operatorname{tr}(H\Sigma B\Sigma)
 +(Hm)^\top\Sigma(Bm)+b^\top\Sigma(Hm).
\]
In the \(U\)-frame,
\[
\Sigma=\operatorname{diag}(p_i^{-1}),\qquad m_i=a_i/p_i,
\]
so the three terms are respectively
\[
\frac12\sum_i\frac{\lambda_i\widetilde B_{ii}}{p_i^2},
\qquad
\sum_{i,j}\frac{\lambda_i a_i\widetilde B_{ij}a_j}{p_i^2p_j},
\qquad
\sum_i\frac{\widetilde b_i\lambda_i a_i}{p_i^2}.
\]
Multiplying by \(t^2\) gives B exactly. **No diagonal assumption on \(\widetilde B\)** is needed.

### C: expansion, including an explicit remainder constant

Write
\[
S_{\rm anch}(t)=A_0+\frac{A_1}{t}+R_{\rm anch}(t),
\]
where
\[
A_0=\sum_i\left(\frac{\widetilde B_{ii}}{2\lambda_i}
                   +\frac{\widetilde b_i a_i}{\lambda_i}\right),
\]
and
\[
A_1=-g\sum_i\frac{\widetilde B_{ii}}{\lambda_i^2}
+\sum_{i,j}\frac{\widetilde B_{ij}a_i a_j}{\lambda_i\lambda_j}
-2g\sum_i\frac{\widetilde b_i a_i}{\lambda_i^2}.
\]
These coefficients are correct.

One convenient explicit bound is
\[
|R_{\rm anch}(t)|\le \frac{K_{\rm anch}}{t^2},
\]
with
\[
\begin{aligned}
K_{\rm anch}={}&
\frac{3g^2}{2}\sum_i\frac{|\widetilde B_{ii}|}{\lambda_i^3}
+3g^2\sum_i\frac{|\widetilde b_i a_i|}{\lambda_i^3}\\
&+g\sum_{i,j}
\frac{|\widetilde B_{ij}a_i a_j|}{\lambda_i\lambda_j}
\left(\frac2{\lambda_i}+\frac1{\lambda_j}\right).
\end{aligned}
\]
This follows from, for \(x,y\ge0\),
\[
|(1+x)^{-2}-(1-2x)|\le3x^2,
\]
and
\[
|(1+x)^{-2}(1+y)^{-1}-1|\le2x+y.
\]
These are useful scalar helper lemmas for the Lean expansion.

### D: gap coefficients

Subtracting \(A_0\) from the local leading term gives
\[
\sum_i\widetilde b_i\left(c_i-\frac{a_i}{\lambda_i}\right)
=-\sum_i\frac{\widetilde b_i\alpha_i}{2\lambda_i^2}.
\]

For the diagonal quadratic coefficient,
\[
c'_{2,i}+\frac g{\lambda_i^2}-\frac{a_i^2}{\lambda_i^2}
=\frac{5\alpha_i^2}{4\lambda_i^4}
-\frac{2a_i\alpha_i}{\lambda_i^3}
-\frac{\gamma_i}{2\lambda_i^3}.
\]
For \(i\ne j\),
\[
c_ic_j-\frac{a_ia_j}{\lambda_i\lambda_j}
=\frac{\alpha_i\alpha_j}{4\lambda_i^2\lambda_j^2}
-\frac{\alpha_i a_j}{2\lambda_i^2\lambda_j}
-\frac{\alpha_j a_i}{2\lambda_j^2\lambda_i}.
\]
The linear coefficient is indeed
\[
2\left(m_{2,i}+\frac{ga_i}{\lambda_i^2}\right).
\]
All proposed cancellations and signs are correct.

Define the symmetric matrix \(\Gamma\) using those diagonal and off-diagonal entries. Then
\[
\Gamma_B=\operatorname{tr}(\widetilde B\Gamma)
+2\sum_i\widetilde b_i
 \left(m_{2,i}+\frac{ga_i}{\lambda_i^2}\right).
\]
Here the off-diagonal sum is over **ordered pairs** \(i\ne j\); if changed to \(i<j\), insert a factor of \(2\).

The final gap remainder constant can simply be \(K_{\rm loc}+K_{\rm anch}\).

## 2. Relation to the variance gap

Yes, the discrepancy is necessary and consistent. There is a clean identity worth recording.

Set
\[
L_2=\frac12\sum_i\lambda_i u_i^2,\qquad
L_3=\frac16\sum_i\alpha_i u_i^3,\qquad
L_4=\frac1{24}\sum_i\gamma_i u_i^4.
\]
Then exactly,
\[
\operatorname{Var}_{\rm loc}(L)
=\operatorname{Cov}_{\rm loc}(L,L_2)
+\operatorname{Cov}_{\rm loc}(L,L_3)
+\operatorname{Cov}_{\rm loc}(L,L_4).
\]
Consequently, at the coefficient level,
\[
\boxed{
2C_1'-\Gamma_H
=\sum_i\left(
-\frac{5\alpha_i^2}{6\lambda_i^3}
+\frac{a_i\alpha_i}{\lambda_i^2}
+\frac{\gamma_i}{4\lambda_i^2}
\right).
}
\]

The separate cubic and quartic contributions are
\[
t^2\operatorname{Cov}_{\rm loc}(L,L_3)
=\frac1t\sum_i\left(
\frac{a_i\alpha_i}{\lambda_i^2}
-\frac{5\alpha_i^2}{6\lambda_i^3}
\right)+O(t^{-2}),
\]
and
\[
t^2\operatorname{Cov}_{\rm loc}(L,L_4)
=\frac1t\sum_i\frac{\gamma_i}{4\lambda_i^2}
+O(t^{-2}).
\]
These sum to precisely the difference above.

A useful derivation uses
\[
\operatorname{Cov}_{\rm loc}(L,f)=-\partial_t\mathbb E_{\rm loc}[f],
\]
together with the leading moments
\[
\mathbb E[u_i^3]
=\left(\frac{3a_i}{\lambda_i^2}
-\frac{5\alpha_i}{2\lambda_i^3}\right)t^{-2}+O(t^{-3}),
\qquad
\mathbb E[u_i^4]=\frac3{\lambda_i^2}t^{-2}+O(t^{-3}).
\]
But **do not differentiate a bare \(O(t^{-3})\) theorem** without derivative control.

For this tide, the cheapest rigorous addition is the combined \(L_3+L_4\) rate, obtained directly from covariance additivity and the landed variance and quadratic-probe rates.

## 3. Lean route

**Prefer polarisation for `tiltedCov_quadForm`.** The landed variance theorem already contains essentially all the analytic work.

For \(q_H(u)=u^\top Hu\),
\[
2\operatorname{Cov}(q_H,q_B)
=\operatorname{Var}(q_{H+B})
-\operatorname{Var}(q_H)-\operatorname{Var}(q_B).
\]
Apply `tiltedVar_quadForm` three times, then expand the finite-dimensional algebra:

- the two trace cross terms agree by cyclicity;
- the two mean cross terms agree by symmetry of \(\Sigma\);
- finish the scalar coefficient arithmetic with `ring`.

**Check the landed theorem’s hypotheses first:** the probe matrix should require only symmetry, not positive definiteness. Positive definiteness belongs to \(P\). If the old theorem unnecessarily requires a positive-definite probe, generalise it or use the direct Wick proof.

For `tiltedCov_quadForm_linear`, use the shift proof:

1. \(q_H(m+z)=q_H(z)+2(Hm)^\top z+q_H(m)\);
2. the quadratic–linear centered covariance vanishes by reflection;
3. the linear–linear moment is \(w_1^\top\Sigma w_2\).

If a named mixed Wick integral is independently useful, polarise the landed centered square integral:
\[
q_Hq_B=\frac{q_{H+B}^2-q_H^2-q_B^2}{2}.
\]
A second four-index contraction proof is correct, but less attractive for maintenance.

For integrability, reuse the existing polynomial/Gaussian moment lemmas. If necessary, mixed-product integrability follows from
\[
2|q_Hq_B|\le q_H^2+q_B^2.
\]

### Eigenframe algebra

Your trace formula is correct:
\[
\operatorname{tr}\!\left(
\operatorname{diag}(\lambda_i/p_i)\,
\widetilde B\,
\operatorname{diag}(1/p_i)\right)
=\sum_i\frac{\lambda_i\widetilde B_{ii}}{p_i^2}.
\]
Do **not** commute \(\widetilde B\) through a diagonal matrix; it need not commute.

With the convention that the columns of \(U\) are eigenvectors, use
```lean
Uᵀ * B * U
Uᵀ *ᵥ b
Uᵀ *ᵥ v
```
and \(H=U\,\operatorname{diag}(\lambda)\,U^\top\). Prove once that the transformed probe is symmetric. Keep matrix distributivity/associativity and trace rewrites separate from the final scalar `ring` step.

## 4. Explicit E2 frame versus `orthoOf`

Your proposed explicit-frame Multi theorem is acceptable **as a staged result**, provided it says exactly what has been formalised: comparison against the explicit anchored frame expression. Prose identification does not itself give a Lean theorem about the actual Gaussian covariance.

My recommendation is a small bridge lemma rather than a general basis-independence theorem:

> Prove B for an arbitrary orthogonal \(U\) satisfying  
> \(U^\top H U=\operatorname{diag}(\lambda)\).

Then instantiate with:

- `orthoOf` for the canonical Sampler corollary;
- \(Q\) for the E2/Multi application.

This avoids comparing two spectral frames, including the nuisance of rotations inside repeated eigenspaces. It also gives the genuine Gaussian identification without a large new abstraction.

The local \(\alpha,\gamma\) data remain attached to the E2 separable frame; one should not suggest that their component formulas can be transported unchanged through arbitrary rotations of a degenerate eigenspace.

## 5. E3 wording

The intended message is good, but it needs three qualifications:

1. **“Quadratic” means purely quadratic about the specified center**, \(b=0\). A general degree-two polynomial includes a linear part.
2. **“Purely anharmonic” means vanishing in the harmonic limit**, not independent of the anchor: \(\Gamma\) contains \(a=g u_0\).
3. **“Which no Gaussian model reproduces” is too strong.** A Gaussian with an anharmonically corrected mean can reproduce this leading shift. The specified Hessian-based anchored Gaussian does not.

Also, the leading linear gap can vanish by cancellation, and \(\Gamma\) need not be positive semidefinite.

Suggested wording:

> For probes purely quadratic about the expansion center, the anchored Gaussian predicts the leading scaled susceptibility correctly. The local-minus-anchored correction is \(\operatorname{tr}(\widetilde B\Gamma)/t+O(t^{-2})\), where the symmetric, anchor-dependent matrix \(\Gamma\) vanishes in the harmonic limit. For a probe with a linear part, there is additionally a potentially nonzero leading discrepancy \(-\sum_i\widetilde b_i\alpha_i/(2\lambda_i^2)\), reflecting the cubic-induced mean shift absent from the specified anchored Gaussian.

“Correct at leading order” here is an absolute asymptotic statement, not necessarily a relative-error statement when the leading coefficient vanishes.

## 6. Vote

**Vote: land A–D; use polarisation, add the arbitrary-eigenframe bridge if feasible, record the combined cubic/quartic identity, and qualify the E3 Gaussian claim.**