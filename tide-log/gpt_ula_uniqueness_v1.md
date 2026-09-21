## 1. Correctness and the right generality

**U is correct, including for arbitrary invariant probability measures with no moment assumption.** Characteristic functions are continuous for finite measures, regardless of whether moments exist.

I would separate the main probabilistic theorem from the spectral argument:

- **Abstract uniqueness theorem:** assume
  1. `R.PosSemidef` and `S.PosSemidef`;
  2. `covStep A R S = S`;
  3. for every `t`,
     ```lean
     Tendsto (fun n => euclid ((Aᵀ)^n) t) atTop (𝓝 0).
     ```
  Then every invariant probability measure is `N(0,S)`.

- **Spectral corollary:** discharge condition 3 using the existing orthogonal diagonalisation and `|a i| < 1`.
- **ULA corollary:** instantiate the abstract result with the existing `ulaCov_fixed`, `ulaCov_posDef`, and spectral bounds.

This makes the probabilistic theorem usable for nonsymmetric matrices later without undertaking a spectral-radius formalisation now.

### One hypothesis that needs attention

In the general statement, you must **establish that the Lyapunov fixed point `S` is PSD**, not merely that it is the unique fixed point. This follows mathematically from stability and `R.PosSemidef`, but it is a separate formal obligation unless your Lyapunov API already provides it.

A clean route is:

1. every `(covStep A R)^[n] 0` is PSD;
2. these matrices converge to `S`;
3. pass to the limit in symmetry and in each quadratic-form inequality.

For ULA this obligation is already covered by `ulaCov_posDef`.

I would not replace the spectral assumptions with a matrix-norm hypothesis for this step. The abstract decay hypothesis gives the desired generality without importing norm-choice complications.

## 2. Characteristic functions under linear maps—and a simpler uniqueness proof

### The map lemma

The reusable lemma you want is schematically:

```lean
lemma charFun_map_clm
    (μ : Measure E) [IsFiniteMeasure μ]
    (L : E →L[ℝ] E) (t : E) :
    charFun (μ.map L) t = charFun μ (L.adjoint t) := by
  ...
```

Here `E` should carry the real Hilbert-space and measurable-space assumptions required by the existing characteristic-function API. Specialising directly to `EuclideanSpace ℝ ι` is perfectly reasonable.

I cannot verify an existing Hilbert-space version’s name against your repository pin. `charFun_map_eq_charFunDual_smul` is relevant, but converting its dual-space formulation may be more work than proving this directly.

The direct proof uses:

- `charFun_apply`;
- `MeasureTheory.integral_map`;
- measurability of `L`, from `L.continuous.measurable`;
- continuity, hence strong measurability, of the complex exponential integrand;
- the adjoint identity
  \[
  \langle Lx,t\rangle=\langle x,L^\ast t\rangle.
  \]

Look in the `ContinuousLinearMap.adjoint_inner_left` / `adjoint_inner_right` family for the last step; the exact orientation may require `real_inner_comm`. This is a small helper worth proving once.

Then `euclid_adjoint` gives your matrix version:

```lean
charFun (μ.map (euclid A)) t =
  charFun μ (euclid Aᵀ t)
```

For continuity, `continuous_charFun` is the right lemma from the stated TaylorExpansion import. Use `[IsProbabilityMeasure μ]`, which supplies the finite-measure hypothesis needed by this API; **no moment hypothesis should be introduced**.

### Recommended simplification: divide by the stationary Gaussian characteristic function

You can avoid the iterated covariance formula in the uniqueness proof entirely.

Let
\[
B=\operatorname{euclid}(A^\mathsf T),\qquad
f(t)=\widehat\mu(t),\qquad
g(t)=\widehat{N(0,S)}(t),\qquad
r(t)=\widehat{N(0,R)}(t).
\]
Invariance of both measures gives
\[
f(t)=f(Bt)r(t),\qquad g(t)=g(Bt)r(t).
\]
By `charFun_multivariateGaussian` and `Complex.exp_ne_zero`,
\[
g(t)\ne0,\qquad r(t)\ne0.
\]
Consequently the function
\[
H(t)=f(t)/g(t)
\]
satisfies `H t = H (B t)`. Induction yields
\[
H(t)=H(B^n t).
\]
Since `B^n t → 0`, continuity gives
\[
H(t)=H(0)=1.
\]
Thus `f = g`, and `Measure.ext_of_charFun` finishes.

This proof reuses `invariant_of_covStep_fixed` and needs only:

1. the map lemma;
2. `charFun_conv`;
3. nonvanishing of Gaussian characteristic functions;
4. decay of the adjoint iterates;
5. `continuous_charFun`, `charFun_zero`, and `tendsto_nhds_unique`.

For Lean, proving just `ContinuousAt H 0` is enough. Its denominator is nonzero there because `g 0 = 1`. A global continuity lemma for `H` is also straightforward.

**This is my preferred uniqueness proof.** It avoids finite covariance sums, repeated quadratic-form algebra, and PSD bookkeeping for every finite-step covariance.

## 3. Matrix-power decay and covariance convergence

Use the product topology and finite-dimensional algebra. There is no need to select an operator norm.

### Step A: powers of the diagonalisation

Prove a reusable identity
\[
A^n=U\,\operatorname{diagonal}(i\mapsto a_i^n)\,U^\mathsf T.
\]

An induction is robust:

- at `n = 0`, use `U * Uᵀ = 1`;
- at the successor step, use `Uᵀ * U = 1`, associativity, and multiplication of diagonal matrices.

The `Matrix.diagonal_mul_diagonal` / `Matrix.diagonal_pow` API is worth checking locally, but an explicit induction is small enough that this need not depend on finding a conjugation-power lemma.

### Step B: diagonal convergence

For each index, use the checked lemma

```lean
tendsto_pow_atTop_nhds_zero_of_abs_lt_one
```

Then assemble
\[
\operatorname{diagonal}(i\mapsto a_i^n)\longrightarrow 0
\]
with `tendsto_pi_nhds` twice. Entrywise, split on whether the two indices coincide.

Finally, continuity of multiplication gives
\[
U D_n U^\mathsf T\longrightarrow U0U^\mathsf T=0.
\]

`Filter.Tendsto.mul` is the natural interface if the matrix topological-ring instances resolve. If that becomes awkward, the completely reliable fallback is the entry formula
\[
(A^n)_{ij}=\sum_k U_{ik}\,a_k^n\,U_{jk},
\]
using `tendsto_finset_sum`, `mul_const`, and `const_mul`.

**Important norm warning:** `|a_i| < 1` does not generally imply that the standard matrix infinity operator norm is below one. Orthogonal conjugation preserves the Euclidean operator norm, not the infinity operator norm. Thus `Matrix.linftyOpNormedRing` is not a shortcut for these hypotheses.

### Step C: transpose powers and action on vectors

Either use symmetry, or use
\[
(A^\mathsf T)^n=(A^n)^\mathsf T
\]
and continuity of transpose. For maximum reuse, the latter route is preferable.

For fixed `t`, prove decay of the matrix-vector action entrywise:
\[
\bigl((A^\mathsf T)^n t\bigr)_i
  =\sum_j ((A^\mathsf T)^n)_{ij}t_j.
\]
Again, `tendsto_pi_nhds` and `tendsto_finset_sum` suffice.

One small API lemma will help bridge this to the probabilistic theorem:

```lean
-- schematic
euclid ((Aᵀ)^n) t = (euclid Aᵀ)^[n] t
```

Prove it from the multiplication and identity properties of `toEuclideanCLM`, or by induction.

### Step D: covariance convergence

Your existing identity immediately gives
\[
(\operatorname{covStep} A R)^{[n]}X_0
 =S+A^n(X_0-S)(A^\mathsf T)^n\longrightarrow S.
\]

This is an excellent general-purpose lemma: **`X₀` does not need to be PSD** for the matrix convergence statement. PSD is needed only when interpreting it as a covariance.

For quadratic-form convergence, use continuity of the finite sum
\[
X\mapsto \sum_{i,j}t_iX_{ij}t_j.
\]
Do not introduce operator norms just for this step.

## 4. Lévy’s theorem and the scope of C

I cannot inspect the specified Mathlib pin here, so I cannot honestly certify the exact name or declaration of its Lévy theorem. Treat

```lean
ProbabilityMeasure.tendsto_iff_tendsto_charFun
```

as a **candidate to check**, not a verified API fact.

Useful local checks are:

```lean
#check ProbabilityMeasure.tendsto_iff_tendsto_charFun
#check ProbabilityTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun
#print continuous_charFun
#print Measure.ext_of_charFun
```

and:

```sh
rg -n 'tendsto_iff_tendsto_charFun|tendsto.*charFun|[Ll]evy' \
  Mathlib/Probability Mathlib/MeasureTheory
```

Besides the name, check the **ambient-space generality**: a theorem restricted to real-valued laws does not directly settle the Euclidean-space case.

The desired form is schematically
\[
\operatorname{Tendsto}(\mu_n,\mathcal N(\mu))
\iff
\forall t,\quad
\widehat{\mu_n}(t)\longrightarrow\widehat\mu(t),
\]
with `μₙ` and `μ` bundled as `ProbabilityMeasure E`. Weak convergence should be stated in that topology, **not as pointwise convergence of measures on all measurable sets**.

If the theorem exists at the required generality, add weak convergence as a thin corollary. Otherwise, do not let locating or generalising Lévy’s theorem block uniqueness.

For Gaussian starts, pointwise characteristic-function convergence is routine from:

- `gaussStep_iterate`;
- mean convergence;
- covariance convergence;
- `charFun_multivariateGaussian`;
- continuity of the exponential.

## 5. Nearby improvements and things to avoid

### A stronger nearby target: characteristic-function convergence from every initial law

The quotient argument also extends cheaply beyond Gaussian starts.

For any initial probability measure `μ₀`, put
\[
\mu_n=(\operatorname{gaussStep} A R)^{[n]}\mu_0.
\]
With `g` the stationary Gaussian characteristic function, the one-step identity gives
\[
\frac{\widehat{\mu_{n+1}}(t)}{g(t)}
 =
\frac{\widehat{\mu_n}(Bt)}{g(Bt)}.
\]
Therefore
\[
\widehat{\mu_n}(t)
 =
g(t)\,
\frac{\widehat{\mu_0}(B^n t)}{g(B^n t)}
 \longrightarrow g(t).
\]

This proves **pointwise characteristic-function convergence from arbitrary initial probability laws, without moments**. With the appropriate Lévy theorem, it proves weak convergence from every initial law.

It is a more valuable extension than separately targeting only Gaussian starts. However, keep it downstream of uniqueness so that probability-instance and iteration bookkeeping do not delay the central theorem.

### Suggested proof organisation

1. **Characteristic-function helpers**
   - continuous-linear-map pushforward;
   - `gaussStep` characteristic-function identity;
   - Gaussian characteristic functions are nonzero.

2. **Stability helpers**
   - powers of an orthogonal diagonalisation;
   - matrix-power decay;
   - adjoint-action decay;
   - covariance convergence.

3. **Abstract uniqueness**
   - PSD fixed covariance plus adjoint-action decay;
   - quotient argument and `Measure.ext_of_charFun`.

4. **ULA uniqueness**
   - existing fixed-point and positivity results;
   - eigenvalue bounds giving `|1 - h * p_i| < 1`.

5. **Optional attraction corollary**
   - arbitrary-start characteristic-function convergence;
   - weak convergence if the available Lévy API makes it inexpensive.

The stretch item D adds little: under stationarity, U already says every time marginal is Gaussian. For a non-Gaussian initial law, finite-time marginals generally are **not** Gaussian.

**Vote: U + C0—abstract moment-free uniqueness via the characteristic-function quotient, spectral decay helpers, and the ULA uniqueness corollary.**