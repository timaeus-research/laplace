## 1. Mathematics: A and the proposed recursion are correct

Write \(A_{ab}=\sum_{i\in s}a_i b_i\), and similarly for the other coefficient pairings. The expansion in the log has all 16 terms with the correct coefficients:

- one term with no \(G\);
- four terms with one \(G\);
- six terms with \(G^2\);
- four terms with \(G^3\);
- one term with \(G^4\).

Block independence and the prescribed moments therefore give exactly
\[
\begin{aligned}
E[X'Y'Z'W']={}&E[XYZW]\\
&+v\bigl(
\alpha\beta E[ZW]+\alpha\gamma E[YW]+\alpha\delta E[YZ]\\
&\hspace{31mm}
+\beta\gamma E[XW]+\beta\delta E[XZ]+\gamma\delta E[XY]
\bigr)\\
&+3v^2\alpha\beta\gamma\delta.
\end{aligned}
\]

The closed form is consistent under insertion. Indeed,
\[
\begin{aligned}
&(A_{ab}+\alpha\beta)(A_{cd}+\gamma\delta)
 +(A_{ac}+\alpha\gamma)(A_{bd}+\beta\delta)\\
&\qquad +(A_{ad}+\alpha\delta)(A_{bc}+\beta\gamma)
\end{aligned}
\]
is the old three-pairing expression plus
\[
\alpha\beta A_{cd}+\alpha\gamma A_{bd}+\alpha\delta A_{bc}
+\beta\gamma A_{ad}+\beta\delta A_{ac}+\gamma\delta A_{ab}
+3\alpha\beta\gamma\delta.
\]
Multiplying by \(v^2\) agrees with the recursion after applying the second-moment theorem.

**No identical-distribution hypothesis is needed.** Joint independence, the common four moments, and the integrability hypotheses suffice. In particular, no Gaussian-law hypothesis is needed. Pairwise independence alone would not suffice.

### A substantially shorter route: polarize the existing two-way identity

Before implementing the induction, I would try this. Let
\[
Q(U,V)=E[U^2V^2].
\]
Pointwise,
\[
\begin{aligned}
16XYZW={}&(X+Z)^2(Y+W)^2-(X-Z)^2(Y+W)^2\\
&-(X+Z)^2(Y-W)^2+(X-Z)^2(Y-W)^2.
\end{aligned}
\]
This is a `ring` identity. Consequently,
\[
16E[XYZW]
=Q(X+Z,Y+W)-Q(X-Z,Y+W)
-Q(X+Z,Y-W)+Q(X-Z,Y-W).
\]

Apply `integral_linComb_sq_mul_sq` to the four coefficient pairs
\[
(a+c,b+d),\quad(a-c,b+d),\quad(a+c,b-d),\quad(a-c,b-d).
\]
The result simplifies to
\[
16v^2(A_{ab}A_{cd}+A_{ac}A_{bd}+A_{ad}A_{bc}).
\]

**This derives A from the seabed without any quadruple independence lemma or new induction.** It also retains exactly the existing assumptions. My first implementation attempt would use this route.

---

## 2. Lean structure: general block lemma, concrete nested pairs—if needed

If you pursue induction or want the reusable infrastructure, my preference is:

1. **Prove (iii), the general measurable-block lemma.**
2. Derive **(i), the nested-pair specialization**, locally or as a small public lemma.
3. Use `Fin 4 → ℝ` only if subsequent developments genuinely need arbitrary finite families.

A schematic signature is:
```lean
-- Schematic; adapt measurable-space and independence arguments to the seabed.
lemma indepFun_block_map
    (h_indep : iIndepFun g P)
    (hn : n ∉ s)
    (F : (↥s → ℝ) → E)
    (hF : Measurable F) :
    IndepFun
      (fun ω => F (fun i : ↥s => g i ω))
      (g n) P := ...
```
Here `E` needs its measurable-space structure. The proof should reuse the existing `indepFun_finset s {n}` construction, composing the left block with `F` and the singleton block with coordinate evaluation.

There is no reason to make this lemma specific to linear combinations or fourth moments.

For the quadruple specialization, use
```lean
fun z =>
  ((∑ i : ↥s, a i * z i, ∑ i : ↥s, b i * z i),
   (∑ i : ↥s, c i * z i, ∑ i : ↥s, d i * z i))
```
with the coercions made explicit if necessary.

**Why nested pairs here?**

- Finite sums, scalar multiplication, and products are straightforward measurable constructions.
- `fun_prop` should handle much of this; explicit finite-sum measurability is a reliable fallback.
- Projection expressions beta-reduce predictably.
- A concrete polynomial such as
  ```lean
  fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
    p.1.1 * p.1.2 * p.2.1 * p.2.2
  ```
  requires no finite-index case analysis.

`Fin 4 → ℝ` is mathematically tidy and scales better, but concrete `![...]` evaluation can introduce extra simplifier work. It is not a major obstacle, just unnecessary machinery for a single four-variable theorem.

For rewriting, expose a factorization corollary whose conclusion already uses the desired integrands. Avoid repeatedly unfolding the block construction at use sites.

**Qualification:** with polarization, none of this infrastructure is necessary for A+B. I would not expand the tide solely to add it.

---

## 3. Integrability: avoid a generic list API for this tide

Your four-\(L^4\)-factor lemma is exactly the right primitive. A generic `Fin 4` product lemma is reasonable if repeated uses emerge; a list theorem introduces length and exponent bookkeeping without helping much here.

### With polarization

You need integrability of:

- \(XYZW\);
- the four square-product expressions in the polarization identity.

Each square-product expression is again a product of four \(L^4\) factors. For example,
\[
(X+Z)^2(Y-W)^2
=(X+Z)(X+Z)(Y-W)(Y-W).
\]
Use `MemLp.add`/`MemLp.sub`, then the existing four-factor lemma. If the seabed already exports square-product integrability, use that directly.

Thus the integral algebra is only a short `integral_sub` chain, plus the constant-multiple rule. A pointwise identity followed by `integral_congr_ae` keeps polynomial algebra separate from integration.

For the coefficient algebra, first normalize finite sums into named pairings. An auxiliary coefficient lemma proved by finite-sum distributivity and `ring` can be cleaner than asking the main proof to simultaneously simplify integrals, sums, and polynomials.

### With induction

Do not introduce a subset-indexed expansion merely to avoid 15 local facts. It shifts the burden into combinatorial indexing and identification of terms.

Instead, introduce a **local integrability helper parameterized by four factors**, and derive the needed monomial integrability expressions inline. Fix one multiplication association throughout and normalize powers with `pow_two` and associativity as needed.

One trap: the term
\[
G(\alpha YZW+\beta XZW+\gamma XYW+\delta XYZ)
\]
is integrable because its individual degree-four summands are integrable. It does **not** follow merely from integrability of \(G\) and the cubic polynomial. Preserve the \(L^4\)/Hölder argument.

Grouping by powers of \(G\) is excellent for the probabilistic reasoning, but expanded degree-four products are generally better for proving integrability.

---

## 4. Scope and the follow-up C

### A+B is a coherent tide

Yes. With direct induction, approximately 350 lines is plausible but sensitive to how reusable the seabed lemmas actually are. With polarization, I would expect a materially smaller proof.

B should be almost immediate:
\[
\begin{aligned}
&E[(XY)(ZW)]-E[XY]E[ZW]\\
&\qquad=v^2(A_{ac}A_{bd}+A_{ad}A_{bc}).
\end{aligned}
\]
Apply A and the two second-moment identities, then `ring`.

I would first expose B as an **integral-difference theorem**. A wrapper using Mathlib’s covariance definition can follow if that fits downstream APIs.

### C: separate the universal error decomposition from the process model

Let \(I\) be a finite coordinate type, and index chains and retained samples by `Fin C` and `Fin N`, with \(C,N>0\). Define
\[
\widehat\Sigma_{ij}
=\frac1{CN}\sum_{c,k}x_{c,k,i}x_{c,k,j}.
\]

#### Layer 1: an assumption-light Frobenius identity

For any square-integrable matrix-valued estimator,
\[
E\|\widehat\Sigma-\Sigma\|_F^2
=
\sum_{i,j}\operatorname{Var}(\widehat\Sigma_{ij})
+\sum_{i,j}(E\widehat\Sigma_{ij}-\Sigma_{ij})^2.
\]

Then obtain the desired variance sum from unbiasedness. In Lean, initially define the squared Frobenius error explicitly as
\[
\sum_{i,j}(\widehat\Sigma_{ij}-\Sigma_{ij})^2.
\]
This avoids unnecessary matrix-norm API work.

**Uncentred does not automatically mean unbiased for covariance:** you also need zero mean and the correct second-moment target.

#### Layer 2: the stationary, diagonal Gaussian-process calculation

Assume independent chains, zero means, and within each chain
\[
E[x_{c,k,i}x_{c,\ell,j}]=\delta_{ij}R_i(k,\ell).
\]
Assume the relevant four-way Wick identity, obtained from the innovation representation or joint Gaussianity.

Then B gives, for a fixed chain,
\[
\operatorname{Cov}
(x_{c,k,i}x_{c,k,j},x_{c,\ell,i}x_{c,\ell,j})
=(1+\delta_{ij})R_i(k,\ell)R_j(k,\ell).
\]
Cross-chain covariances vanish, so
\[
\boxed{
\operatorname{Var}(\widehat\Sigma_{ij})
=\frac{1+\delta_{ij}}{CN^2}
\sum_{k,\ell}R_i(k,\ell)R_j(k,\ell).
}
\]

This is a useful standalone theorem before specializing to ULA.

#### Layer 3: stationary AR(1) eigendirections

If
\[
R_i(k,\ell)=\lambda_i r_i^{|k-\ell|},
\qquad |r_i|<1,
\]
define
\[
\tau_N(q)=1+2\sum_{h=1}^{N-1}\left(1-\frac hN\right)q^h.
\]
Then
\[
\operatorname{Var}(\widehat\Sigma_{ij})
=\frac{\lambda_i\lambda_j(1+\delta_{ij})}{CN}
\tau_N(r_i r_j),
\]
and, targeting the stationary covariance,
\[
\boxed{
E\|\widehat\Sigma-\Sigma\|_F^2
=\frac1{CN}\sum_{i,j}
\lambda_i\lambda_j(1+\delta_{ij})\tau_N(r_i r_j).
}
\]

The autocorrelation times here are those of the **coordinate products**. For diagonal entries, the relevant argument is \(r_i^2\), not \(r_i\).

### Two important qualifications to the E4 wording

1. **The \(\sqrt{d/(CN)}\) law normally describes relative RMS Frobenius error**, not absolute Frobenius error. For \(\Sigma=\lambda I\) and temporally independent samples,
   \[
   E\|\widehat\Sigma-\Sigma\|_F^2
   =\frac{\lambda^2(d^2+d)}{CN},
   \]
   hence
   \[
   \frac{\sqrt{E\|\widehat\Sigma-\Sigma\|_F^2}}{\|\Sigma\|_F}
   =\sqrt{\frac{d+1}{CN}}.
   \]

2. **Stationary ULA covariance need not equal the intended target covariance.** If C targets the latter, include discretization bias, and initialization bias if the chain is not stationary. The variance-only formula cannot absorb those terms.

### Gaussian projections

Yes: `HasGaussianLaw.iIndepFun_of_covariance_inner` is conceptually the right tool, subject to its exact pinned signature.

For \(\xi\) standard Gaussian in a finite-dimensional real inner-product space:

- the projections along \(u_i\) are jointly Gaussian;
- their covariance is \(\langle u_i,u_j\rangle\);
- orthonormality makes the off-diagonal covariances zero;
- the Gaussian theorem yields mutual independence of the projections.

This is stronger than proving pairwise independence. Separately transport independence of the innovation vectors across chain/time indices through the projection maps; the within-vector Gaussian argument does not by itself establish that cross-time independence.

## Vote

**Vote: A+B**, preferably **via polarization of the existing two-way theorem**. Keep C as a follow-up, and phrase its eventual E4 claim with explicit normalization, stationarity/unbiasedness assumptions, and product-autocorrelation factors.