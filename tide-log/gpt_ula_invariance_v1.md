## 1. Correctness and hypotheses

**A1–A3 are mathematically correct**, provided A3 carries enough hypotheses to invoke both `ulaCov_posDef` and `ulaCov_fixed`. There are two useful simplifications.

### Generalise the noise covariance

Prove the following statement first, for two arbitrary PSD matrices:
\[
\bigl(N(0,\Sigma).\mathrm{map}\,L_A\bigr)*N(0,R)
  =N(0,A\Sigma A^\mathsf T+R).
\]

Its hypotheses are just:
- `Σ.PosSemidef`;
- `R.PosSemidef`;
- the usual finite-index assumptions, typically `[Fintype ι] [DecidableEq ι]`.

There is **no symmetry or invertibility requirement on `A`**. The target covariance is automatically PSD: PSD is preserved by congruence, and by addition.

Then specialise to `R = (2 * h) • 1`. For this, **`0 ≤ h` suffices**; strict positivity is unnecessary. In particular, the result also covers the deterministic step at `h = 0`.

A useful public theorem shape is:

```lean
-- Statement sketch, not checked Lean.
theorem multivariateGaussian_map_conv
    (hΣ : Σ.PosSemidef) (hR : R.PosSemidef) :
    ((multivariateGaussian 0 Σ).map
        (Matrix.toEuclideanCLM (𝕜 := ℝ) A)) ∗
        multivariateGaussian 0 R =
      multivariateGaussian 0 (A * Σ * Aᵀ + R)
```

### PSD hypotheses really matter

According to the supplied API, `multivariateGaussian` is defined for every matrix, but becomes `dirac μ` for a non-PSD matrix. Thus:

- `isGaussian_multivariateGaussian` does not establish that the supplied matrix is its covariance.
- `covarianceBilin_multivariateGaussian` and `charFun_multivariateGaussian` need their PSD hypotheses.
- You should explicitly prove PSD of `A * Σ * Aᵀ` and of `A * Σ * Aᵀ + R` before using those formulas.

Dropping the PSD hypotheses can make A1/A2 false. For example, an indefinite matrix can become a nonzero PSD matrix after projection by a singular `A`, while its original `multivariateGaussian` is a Dirac measure.

For A3, I would separate the probabilistic statement from the spectral assumptions:

1. Prove invariance assuming
   ```lean
   (ulaCov P h).PosSemidef
   0 ≤ h
   covStep (ulaStep P h) (ulaNoise h) (ulaCov P h) = ulaCov P h
   ```
2. Provide a corollary discharging those assumptions using `ulaCov_posDef` and `ulaCov_fixed`.

Remember that `h * p_i < 2` alone does **not** imply `0 ≤ h`.

Finally, the convolution statement describes the independent-noise update. To identify it explicitly with `√(2h) ξ`, prove or reuse
\[
(\mathrm{stdGaussian}\ E).\mathrm{map}
  \bigl(z\mapsto\sqrt{2h}\,z\bigr)
  =N(0,(2h)I).
\]
That is a small additional bridge, not something the convolution notation itself states.

## 2. Proof route and lemma organisation

**I recommend a hybrid route: A2 by `IsGaussian.ext`, centred Gaussian convolution by characteristic functions.** This uses the API you have already checked and avoids searching for convolution moment lemmas.

I am treating the names in your context as verified. Additional names mentioned below as search candidates are not verified against your pin.

### Step 1: linear push-forward, using Gaussian extensionality

Prove
\[
N(0,\Sigma).\mathrm{map}\,L_A=N(0,A\Sigma A^\mathsf T).
\]

The supplied lemmas give exactly the necessary structure:

- Gaussian instances:
  - `isGaussian_multivariateGaussian`;
  - `isGaussian_map`.
- Equality from moments:
  - `IsGaussian.ext`.
- Mean:
  - `IsGaussian.integrable_id`;
  - `integral_id_map`;
  - `integral_id_multivariateGaussian`.
- Covariance:
  - `IsGaussian.memLp_two_id`;
  - `covarianceBilin_map`;
  - `covarianceBilin_multivariateGaussian`.

The mean goal reduces to `L_A 0 = 0`.

After applying `covarianceBilin_map`, the covariance goal is the matrix identity
\[
(A^\mathsf T x)^\mathsf T\Sigma(A^\mathsf T y)
=x^\mathsf T(A\Sigma A^\mathsf T)y.
\]

Package this algebra separately. This prevents the Gaussian proof from becoming entangled with coercions between `EuclideanSpace`, coordinate functions, matrices, and continuous linear maps.

For PSD congruence, inspect the `Matrix.PosSemidef` namespace for names resembling `mul_mul_conjTranspose` or `conjTranspose_mul_mul`; **the exact available name and multiplication association need checking**. Over `ℝ`, conjugate transpose reduces to transpose.

### The adjoint identity

Yes, you should obtain
```lean
(Matrix.toEuclideanCLM (𝕜 := ℝ) A).adjoint =
  Matrix.toEuclideanCLM (𝕜 := ℝ) Aᵀ
```
structurally from the star-algebra equivalence.

The key is **`map_star`**, not a bespoke matrix-adjoint theorem:
\[
\operatorname{toEuclideanCLM}(A^\star)
  =\operatorname{toEuclideanCLM}(A)^\star.
\]
On real matrices, star is transpose; on continuous linear endomorphisms of this Hilbert space, star is adjoint.

I would prove this as one local bridge lemma. The exact simp lemmas converting these two stars should be checked in your checkout; do not assume `simpa` closes it without inspecting them. If that approach is awkward, `inner_toEuclideanCLM` plus uniqueness of the adjoint is a reliable fallback.

### Step 2: convolution of centred Gaussians, using characteristic functions

Prove, for PSD `S` and `R`,
\[
N(0,S)*N(0,R)=N(0,S+R).
\]

Use:
- `Measure.ext_of_charFun`;
- `charFun_conv`;
- `charFun_multivariateGaussian`;
- `Complex.exp_add`.

At each test vector `t`, the goal becomes
\[
e^{-t^\mathsf TSt/2}e^{-t^\mathsf TRt/2}
=e^{-t^\mathsf T(S+R)t/2}.
\]

After expanding the quadratic form of a sum, this is scalar algebra. Neither Gaussianity of the convolution nor a convolution covariance theorem is needed.

### Step 3: combine, then rewrite the covariance fixed point

A1 follows by rewriting with A2 and applying the convolution theorem. A3 follows by specialising and rewriting with `ulaCov_fixed`, after exposing `covStep`, `ulaStep`, or `ulaNoise` only as needed.

This route is preferable to inventing dependencies on unverified lemmas such as `integral_id_conv` or `covarianceBilin_conv`. Your supplied API already contains the map moment formulas; it does not establish the names or availability of convolution moment formulas.

An **all-characteristic-function route** is also good if you find an existing theorem for
\[
\operatorname{charFun}(\mu.\mathrm{map}\,L)(t)
=\operatorname{charFun}(\mu)(L^\dagger t).
\]
Do not assume its name is `charFun_map`. If absent, derive it from the definition, the map-integral formula, and the adjoint identity. That is one additional helper; the hybrid route avoids needing it.

## 3. Convolution, bind, and A4

On this additive Euclidean space, convolution represents
\[
\mu*\nu=(\mu.\mathrm{prod}\,\nu).\mathrm{map}
  \bigl((x,z)\mapsto x+z\bigr).
\]
Whether this is literally the unfolded definition or a theorem about the implementation is worth checking locally. The distinction does not affect the proof plan.

The exact bind identity you want is
\[
\mu.\mathrm{bind}\bigl(x\mapsto
    \nu.\mathrm{map}(z\mapsto L_Ax+z)\bigr)
=(\mu.\mathrm{map}\,L_A)*\nu.
\]
With the translation identity
\[
N(0,R).\mathrm{map}(z\mapsto m+z)=N(m,R),
\]
this yields A4.

Two cautions:

1. **Do not silently skip measurability.** To turn
   ```lean
   fun x ↦ multivariateGaussian (L_A x) R
   ```
   into a Markov kernel, you need measurable dependence on `x` and the probability-measure property.

2. **I cannot certify a dedicated bind–convolution lemma from the supplied API.** Search the measure convolution and bind files; otherwise prove the identity via the product-measure push-forward and bind integration formulas.

The measurability proof is particularly transparent using the defining sampling map
\[
(x,z)\longmapsto L_Ax+\operatorname{toEuclideanCLM}(\sqrt R)\,z,
\]
which is continuous.

**Recommendation:** defer the kernel packaging, but optionally include the explicit product-law theorem
\[
(\mu.\mathrm{prod}\,\nu).\mathrm{map}
  \bigl((x,z)\mapsto L_Ax+z\bigr)=\mu.
\]
It directly expresses one independent-noise update and is a smaller bridge from the convolution formulation.

## 4. The L² bridge

B is reachable, but it is a separate integration/independence excursion rather than a natural part of the Gaussian-measure proof.

A clean random-variable interface is:

```lean
variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (η : ℕ → Ω → ℝ)

-- For each k:
-- MemLp (η k) 2 P
-- ∫ ω, η k ω ∂P = 0
-- ∫ ω, (η k ω)^2 ∂P = v
--
-- For j ≠ k:
-- IndepFun (η j) (η k) P
```

**Pairwise independence suffices** for the white-noise inner products. Mutual independence is stronger than necessary.

Use `MemLp.toLp` to obtain elements of `Lp ℝ 2 P`, then `MeasureTheory.L2.inner_def` to reduce their inner products to
\[
\int \eta_j\eta_k\,dP.
\]

- For `j = k`, the second-moment assumption gives `v`.
- For `j ≠ k`, independence factors the expectation, and centring makes it zero.
- The almost-everywhere identification of `toLp` with its representative is required when rewriting the integral.

Search the `IndepFun` API for the integral-of-product factorisation theorem; names resembling `IndepFun.integral_mul_eq_mul_integral` are **search candidates, not names verified here**. `MemLp` at exponent two supplies integrability on a probability space and product integrability.

For this bridge, the second-moment hypothesis `∫ η_k² = v` is simpler than starting with a variance API: under the explicit zero-mean assumption it is exactly variance `v`.

An even cleaner architecture is:

1. Prove the L² translation assuming only
   \[
   \int\eta_j\eta_k\,dP=
   \begin{cases}v&j=k,\\0&j\ne k.\end{cases}
   \]
2. Separately derive that condition from pairwise independence and centring.

The abstract theorem only needs this second-order orthogonality. Any assumptions about the initial state in the earlier AR(1) theorem must also be transported; noise orthogonality alone does not discharge them.

Finally, identifying the resulting squared L² norms with expected sample variance still needs a finite-sum/integral bridge and the appropriate sample-size hypotheses.

## 5. Nearby targets

The best nearby extension is the **finite-time Gaussian marginal law**, not Gaussianity of the entire path.

Define
\[
\mu_{n+1}=(\mu_n.\mathrm{map}\,L_A)*N(0,R),
\qquad
\Sigma_{n+1}=A\Sigma_nA^\mathsf T+R.
\]
From `μ₀ = N(0,Σ₀)` with PSD `Σ₀`, induction gives
\[
\mu_n=N(0,\Sigma_n).
\]

Your existing identity
\[
\Sigma_n-\Sigma_\infty
=A^n(\Sigma_0-\Sigma_\infty)(A^\mathsf T)^n
\]
then becomes a statement about the actual marginal distributions, rather than merely a covariance recursion.

A useful modest generalisation is
\[
\bigl(N(m,\Sigma).\mathrm{map}\,L_A\bigr)*N(b,R)
=N(L_Am+b,A\Sigma A^\mathsf T+R).
\]
The proof has the same structure; characteristic functions additionally carry a linear phase. This handles nonzero initial means, with `mₙ = Aⁿm₀` for centred noise.

By contrast, Gaussianity of the whole finite trajectory requires a joint Gaussian input vector, independent initial state/noises, and a block-linear trajectory map. It is worthwhile, but not needed for invariance.

Also distinguish **invariance** from **uniqueness among all probability laws**. Uniqueness of a covariance fixed point does not establish uniqueness of invariant laws. Under stability, a characteristic-function argument can prove the latter without assuming an invariant law has finite second moments, but that is a separate theorem.

**Vote: A2 + general PSD-noise A1 + A3, with the finite-time Gaussian marginal law as the sole stretch target; defer kernels and the L² bridge.**