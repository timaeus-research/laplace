## 1. Correctness of Q1–Q3

**Q1 and Q2 are correct, with no symmetry assumption on \(H\).** For a real PSD matrix \(S\),
\[
\mathbb E[X_iX_j]=S_{ij}+m_im_j,
\]
so
\[
\mathbb E[\langle X,HX\rangle]
 =\sum_{i,j}H_{ij}S_{ij}+\langle m,Hm\rangle
 =\operatorname{tr}(HS)+\langle m,Hm\rangle.
\]

The last equality uses **symmetry of \(S\)**, not symmetry of \(H\):
\[
\operatorname{tr}(HS)=\sum_{i,j}H_{ij}S_{ji}
                    =\sum_{i,j}H_{ij}S_{ij}.
\]
For arbitrary matrices, the entrywise sum is instead \(\operatorname{tr}(HS^\mathsf T)\). Thus your proposed result is correctly stated for PSD \(S\), even when \(H\) is nonsymmetric.

**Q3 is also correct under the sampler’s admissibility hypotheses.** Writing \(P=tH\),
\[
t\,\mathbb E\!\left[\tfrac12\langle X,HX\rangle\right]
 =\tfrac12\operatorname{tr}(P\Sigma).
\]
For \(\Sigma=\operatorname{ulaCov}(P,h)\), this gives
\[
\frac12\sum_i\frac1{1-hp_i/2};
\]
for \(\Sigma=P^{-1}\), it gives \(d/2\).

Make explicit the hypotheses under which `ulaCov` is PSD and is the invariant covariance: typically \(P\succ0\), \(h>0\), and \(hp_i<2\) for every \(i\). Under these hypotheses each summand is greater than \(1\). Hence the ULA LLC is at least \(d/2\), and is strictly greater when the index type is nonempty. An unrestricted \(h\) does **not** support the inflation or invariant-law interpretation.

In the Hessian interpretation, assume \(t>0\). The trace calculation itself can avoid division by \(t\) entirely.

## 2. Recommended Lean route: second moments first

I would prove the following reusable core, making Q4 non-optional:
```lean
-- Schematic signature; include the project's usual typeclass assumptions.
theorem integral_coord_mul_multivariateGaussian
    (m : EuclideanSpace ℝ ι) (hS : S.PosSemidef) (i j : ι) :
    (∫ x, x.ofLp i * x.ofLp j ∂multivariateGaussian m S)
      = S i j + m.ofLp i * m.ofLp j
```
Its centred specialization is your Q4. Then prove Q2 by finite summation, and obtain Q1 by setting `m = 0`.

**Version caveat:** I cannot inspect your September 2026 pin here. I am treating the declarations marked “checked” in your context as established, but I cannot certify the exact signature or availability of additional declarations. In particular, do not build the proof around a guessed `covarianceBilin_apply'`.

### A. Isolate basis-coordinate identities

Set \(e_i\) to the standard Euclidean basis vector, using `EuclideanSpace.basisFun`. Alternatively, an explicit construction is:
```lean
let e : ι → EuclideanSpace ℝ ι :=
  fun i => WithLp.toLp 2 (Pi.single i (1 : ℝ))
```

Prove these local helpers once:
```lean
⟪e i, x⟫_ℝ = x.ofLp i
⟪x, e i⟫_ℝ = x.ofLp i
(e i).ofLp ⬝ᵥ S *ᵥ (e j).ofLp = S i j
```
The second inner-product orientation follows from the first by `real_inner_comm`. The last identity is just the single-coordinate simplification of `dotProduct` and `Matrix.mulVec`.

I would keep these as private helper lemmas rather than repeatedly unfolding the Euclidean-space implementation inside integral proofs.

### B. Establish integrability explicitly

From `IsGaussian.memLp_two_id`, obtain `MemLp` of each coordinate at exponent \(2\). The conceptual route is composition with the continuous linear coordinate functional
\[
\ell_i(x)=\langle x,e_i\rangle.
\]
Then apply `MemLp.integrable_mul` to obtain
```lean
Integrable (fun x : E => x.ofLp i * x.ofLp j) μ
```

The CLM-composition declaration to check locally is `ContinuousLinearMap.comp_memLp`; check its argument order rather than assuming dot notation will infer everything. If that API is inconvenient, coordinate domination
\[
|x_i|\le \|x\|
\]
and `MemLp.of_le` provide another route.

For nonzero means, also obtain integrability of coordinates from `IsGaussian.integrable_id` and the continuous linear coordinate maps. For centred-coordinate products, subtract the constant coordinate means at the `MemLp` level and again use `MemLp.integrable_mul`.

This matters: covariance notation by itself is not a substitute for the integrability hypotheses needed by `integral_add`, `integral_sub`, and `integral_finset_sum`.

### C. Rewrite covariance using the actual mean

Use:
- `covarianceBilin_multivariateGaussian hS (e i) (e j)`;
- `covarianceBilin_apply`, with `IsGaussian.memLp_two_id`;
- `integral_id_multivariateGaussian`.

The target intermediate identity is
\[
\int (x_i-m_i)(x_j-m_j)\,d\mu=S_{ij}.
\]

The exact left/right-inner-product orientation of `covarianceBilin_apply` is immaterial over \(\mathbb R\), but its declaration should be inspected:
```lean
#check covarianceBilin_apply
#print covarianceBilin_apply
```
Normalize either orientation with the basis helpers and `real_inner_comm`. Rewrite the mean using `integral_id_multivariateGaussian`, rather than expecting a large `simp` call to discover the centring argument automatically.

For \(m=0\), this immediately proves Q4. For general \(m\), expand
\[
(x_i-m_i)(x_j-m_j)
 =x_ix_j-m_ix_j-m_jx_i+m_im_j,
\]
integrate termwise, and use \(\int x_i=m_i\). The latter follows by applying the coordinate CLM to `integral_id_multivariateGaussian`, using the CLM/integral interchange API—typically `ContinuousLinearMap.integral_comp`, whose signature should also be checked.

### D. Expand the quadratic form and integrate finite sums

Prove the pointwise identity separately:
```lean
⟪x, euclid H x⟫_ℝ =
  ∑ i, ∑ j, H i j * (x.ofLp i * x.ofLp j)
```
Use your checked `inner_toEuclideanCLM`, then unfold `dotProduct` and `Matrix.mulVec`; distribute finite sums and finish scalar rearrangements with `ring`.

Next use:
- `integral_finset_sum`;
- `integral_const_mul`;
- the coordinate-product integrability lemmas.

The matrix-only final step is
```lean
(∑ i, ∑ j, H i j * S i j) = Matrix.trace (H * S)
```
using symmetry extracted from `hS.isHermitian`, `Matrix.mul_apply`, and `Matrix.trace`. Over \(\mathbb R\), normalize Hermitian symmetry to transpose symmetry once in a helper lemma.

I would also export
```lean
integrable_quadratic_multivariateGaussian
```
for arbitrary \(H\). You already prove everything needed for it, and it prevents later users from repeating the finite-sum integrability argument.

## 3. Coordinates versus a basis/covariance contraction

There is a clean one-sum alternative, but it is **not an `IsGaussian.ext` argument**. Extensionality proves equality of Gaussian laws; here the relevant facts are second moments and finite-dimensional linear algebra.

For centred \(X\) and an orthonormal basis \((e_i)\),
\[
\langle X,HX\rangle
 =\sum_i \langle X,e_i\rangle\langle X,He_i\rangle.
\]
Consequently,
\[
\mathbb E[\langle X,HX\rangle]
 =\sum_i\operatorname{covarianceBilin}(\mu)(e_i,He_i)
 =\operatorname{tr}(SH)
 =\operatorname{tr}(HS).
\]

**Using \(He_i\), rather than \(H^\mathsf T e_i\), gives a particularly direct contraction.** Your transpose variant is also valid here, but introduces an additional symmetry/transpose rewrite.

Advantages of the one-sum proof:
- fewer nested finite sums;
- a route toward a general quadratic-moment theorem for any law with finite second moment.

Disadvantages in this development:
- you need the basis expansion and its interaction with `euclid`;
- you still need product integrability;
- you do not automatically obtain the useful coordinate-second-moment lemma.

Given the existing matrix API and the proposed Q4, **coordinates are the lower-risk first implementation**. No density or nonsingular-covariance argument is needed, so singular PSD \(S\) is handled naturally.

## 4. Gibbs inverse covariance and the trace calculation

For \(P\succ0\), \(P^{-1}\succ0\), hence \(P^{-1}\) is PSD. The intended declaration chain is:
```lean
hP.inv.posSemidef
```
but check these declarations in the pin:
```lean
#check Matrix.PosDef.inv
#check Matrix.PosDef.posSemidef
#check Matrix.PosDef.det_pos
#check Matrix.mul_nonsing_inv
#check Matrix.trace_one
```
These are the relevant API names to inspect; the inverse and nonsingular-inverse application details should not be guessed from a different Mathlib version.

**Avoid `Matrix.inv_smul` altogether.** Obtain
```lean
hPP : P * P⁻¹ = 1
```
using positive definiteness, nonzero determinant, and `Matrix.mul_nonsing_inv`. Then calculate
\[
\begin{aligned}
t\,\operatorname{tr}(HP^{-1})
 &=\operatorname{tr}\bigl(t\mathbin{\bullet}(HP^{-1})\bigr)\\
 &=\operatorname{tr}\bigl((t\mathbin{\bullet}H)P^{-1}\bigr)\\
 &=\operatorname{tr}(PP^{-1})\\
 &=\operatorname{tr}(1)=d.
\end{aligned}
\]
The relevant scalar-rewrite declarations are `Matrix.trace_smul` and `Matrix.smul_mul`, subject to checking their orientation in your pin. Expanding the finite sums is a fallback if their rewrite direction is inconvenient.

This multiplied identity is better than
\[
\operatorname{tr}(HP^{-1})=d/t:
\]
it exactly matches the LLC theorem and needs no separate `t ≠ 0` hypothesis or division simplification. The divided statement requires `t ≠ 0`.

I would organize Q3 as:
1. a generic scaled Gaussian quadratic-expectation theorem;
2. its `ulaCov` specialization, followed by `trace_mul_ulaCov`;
3. its inverse-covariance specialization, followed by the identity above.

Then connect the ULA specialization to the existing `ula_llc` definition/theorem. No new invariance proof is necessary.

## 5. Nearby targets and corrections

Two worthwhile additions are small:

- **An expectation-level inflation corollary**, comparing the ULA invariant law with the Gibbs law, with strictness under `Nonempty ι`.
- **A finite-time Gaussian quadratic expectation corollary**, if `gaussStep_iterate_zero` already provides the covariance \(\Sigma_k\).

There is a missing factor in the proposed finite-time formula. With
\[
K(x)=\tfrac12\langle x,Hx\rangle,\qquad P=tH,
\]
the correct centred statement is
\[
\boxed{
t\,\mathbb E_k[K]
 =\frac t2\operatorname{tr}(H\Sigma_k)
 =\frac12\operatorname{tr}(P\Sigma_k).
}
\]
It is not generally \(\tfrac12\operatorname{tr}(H\Sigma_k)\).

For a Gaussian initial law with possibly nonzero mean, the corresponding formula is
\[
t\,\mathbb E_k[K]
 =\frac12\operatorname{tr}(P\Sigma_k)
  +\frac12\langle m_k,Pm_k\rangle.
\]
This follows directly from Q2 once the iterate’s mean and covariance are available.

The mean statement \(\mathbb E[X]=m\) is already `integral_id_multivariateGaussian`, so it is not a substantial new target. Also, do **not** infer convergence of these unbounded quadratic expectations merely from the existing convergence-in-law theorem. Use the explicit mean/covariance trajectory, or prove an appropriate uniform-integrability result.

**Vote: Q1–Q4 as one “Gaussian second moments → quadratic expectations → stationary ULA/Gibbs LLC comparison” cluster, with finite-time trajectories deferred.**