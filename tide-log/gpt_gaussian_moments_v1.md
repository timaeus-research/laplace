## 1. Yes: second moments imply the stated IBP hypothesis, without derivatives

Assume `[Fintype ι] [DecidableEq ι]`, `P.PosDef`, and establish the identification
\[
(Hu)_i=\sum_k P_{ik}u_k.
\]
Write \(Z=\int g\), where \(g=\texttt{gaussianWeight H}\). Then
\[
\begin{aligned}
\int u_j(Hu)_i g(u)\,du
&=\sum_k P_{ik}\int u_j u_k g(u)\,du\\
&=Z\sum_k P_{ik}(P^{-1})_{kj}\\
&=Z\,\delta_{ij}.
\end{aligned}
\]
Together with integrability, `integral_sub` gives precisely `FubiniIBPHypothesis H i j`.

**An index detail worth making explicit:** apply the moment theorem with indices **`k j`**, after rewriting \(u_j u_k=u_k u_j\). This produces \((P^{-1})_{kj}\), so the final sum is directly `(P ⬝ P⁻¹) i j`. Otherwise you introduce an unnecessary symmetry rewrite.

The analytic prerequisite is real: moving finite sums and subtraction through Bochner integrals requires the relevant integrability facts. Thus the reduction is **D1 + D3 ⇒ IBP**, not merely a manipulation of arbitrary integrals.

### `toLin'` subtleties

- `Matrix.toLin'` gives an ordinary linear map on coordinate functions. The continuous linear map needs the finite-dimensional upgrade.
- Prove one bridge lemma, schematically
  ```lean
  matrixCLM_apply (u : ι → ℝ) : matrixCLM P u = P *ᵥ u
  ```
  and use it everywhere.
- This is the coordinate-basis construction. Do not accidentally substitute the Euclidean-space `toLin` construction, whose basis and types differ.
- `P.PosDef` supplies symmetry/Hermitianity as well as positivity. Mere positivity of \(u^\top P u\) without symmetry would not justify covariance \(P^{-1}\): the weight only sees the symmetric part.

There is no circularity provided D3 is proved by change of variables, **not by the existing theorem that already assumes `FubiniIBPHypothesis`**.

---

## 2. Prefer R1, with a small change-of-variables wrapper

**Given the infrastructure described, R1 is the more predictable route.** R2 becomes preferable only if your exact Mathlib pin already contains a usable nondegenerate Gaussian density theorem.

I cannot inspect that pin here. Consequently, the Haar-change-of-variables and Gaussian-density names below are **search targets, not assertions of exact available signatures**. The algebraic and integration API names are substantially more stable.

### Put the measure API behind one local theorem

For an invertible matrix `M`, the wrapper you want is
\[
\int f(u)\,du
=
|\det M|\;\int f(Mv)\,dv.
\]
Also expose the corresponding integrability equivalence.

The determinant direction is important:
\[
\operatorname{map}(v\mapsto Mv)(\mathrm{volume})
=|\det M|^{-1}\,\mathrm{volume}.
\]
The factor in the substitution formula is therefore \(|\det M|\), not its inverse.

Useful API/search points:

| Purpose | Names to inspect |
|---|---|
| Haar measure under a linear map | `MeasureTheory.Measure.addHaar_map_linearMap`, `map_linearMap_addHaar_eq_smul_addHaar` |
| Integration against a mapped/scaled measure | `MeasureTheory.integral_map`, `MeasureTheory.integral_smul_measure` |
| Product factorisation | `MeasureTheory.integral_fintype_prod_eq_prod`, `volume_pi` |
| Finite sums | `MeasureTheory.integral_finset_sum`, `MeasureTheory.integrable_finset_sum` |
| Coordinate matrix/linear-map conversion | `Matrix.toLin'`, `LinearMap.toMatrix'` |
| Determinants | `Matrix.det_mul`, `Matrix.det_transpose`, `Matrix.det_diagonal` |
| Matrix inverse identities | `Matrix.mul_nonsing_inv`, `Matrix.nonsing_inv_mul` |

Inspect whether the Haar theorem uses the linear-map determinant or a matrix determinant. If it uses the former, discharge that conversion once inside the wrapper rather than repeatedly in the Gaussian proofs.

### Recommended R1 organisation

Use the existing spectral decomposition to construct
\[
M=U\,\operatorname{diag}(p_i^{-1/2}).
\]
Prove these algebraic facts as a separate block:
\[
M^\top P M=I,\qquad MM^\top=P^{-1},\qquad \det M\ne0.
\]
Then
\[
g(Mv)=\exp\!\left(-\tfrac12\sum_i v_i^2\right)
=\prod_i \exp(-v_i^2/2).
\]

First establish the standard-coordinate package:
\[
Z_0=\int e^{-\sum v_i^2/2},\qquad
\int v_a v_b e^{-\sum v_i^2/2}=\delta_{ab} Z_0.
\]
Use product factorisation and the existing one-dimensional results:

- `a = b`: the one-dimensional second moment equals the zeroth moment;
- `a ≠ b`: a first-moment factor is zero by oddness.

Prove the integrability needed for these factorisations explicitly. For arbitrary `ι`, the moments require splitting `a = b` from `a ≠ b`; do not write a product modification that silently assumes distinct indices.

Then finite expansion gives
\[
\int u_i u_jg(u)
=|\det M| Z_0\sum_a M_{ia}M_{ja}
=Z(P^{-1})_{ij}.
\]

**Scope-saving observation:** this proves D3 without evaluating either \(Z_0\) or \(|\det M|\). The same factor \(|\det M|Z_0\) already equals \(Z\).

For D2, add
\[
Z_0=(\sqrt{2\pi})^d,\qquad
|\det M|=(\det P)^{-1/2}.
\]
The latter can be obtained from `Mᵀ P M = 1` by taking determinants; you need not simplify a product of inverse square roots eigenvalue by eigenvalue.

For the final Lean statement, ensure `d / 2` is **real division**:
```lean
(2 * Real.pi) ^ ((Fintype.card ι : ℝ) / 2)
```
Using a natural-number exponent with `d / 2` would be incorrect in odd dimension.

### Existing Gaussian theorems and R2

Search the pin before implementing R1:
```text
multivariateGaussian ... withDensity
multivariateGaussian ... density
integral_exp_neg_quadratic
gaussianIntegral
integral_cexp_neg_mul_sq
```
`integral_cexp_neg_mul_sq` and related one-dimensional Gaussian lemmas do not by themselves provide the positive-definite matrix theorem.

I would **not assume** a theorem named `multivariateGaussian_eq_withDensity` exists. A density theorem for invertible covariance is exactly the missing ingredient that would make R2 short. The covariance moment theorem alone does not identify your Lebesgue density.

Also, passing between `EuclideanSpace ℝ ι` and `ι → ℝ` needs a measure-transport lemma. The coordinate linear equivalence is not an isometry between the Euclidean norm and the Pi sup norm, although it does preserve the corresponding coordinate Lebesgue measures. Keep that distinction explicit.

---

## 3. D1: coercivity once, then use the existing coordinate-product majorants

Prove a reusable statement
\[
\exists a>0,\ \forall u,\quad
a\sum_i u_i^2\le u^\top P u.
\]

### Getting the lower bound

Since you already have `orthoOf` and `spectral_real`, the spectral route is likely cheapest:

1. Every eigenvalue is positive.
2. Choose a positive lower bound for the finite family of eigenvalues.
3. Apply the diagonal inequality in rotated coordinates.
4. Use orthogonality to identify the sums of squares.

`Matrix.PosDef.eigenvalues_pos` is a relevant API search target, as is the Hermitian eigenvalue API behind it. Check its actual binder/index conventions at the pin rather than building the proof around a guessed signature.

**Handle the empty index type.** There is no minimum eigenvalue when `ι` is empty. Either:
- handle the empty case first; or
- prove the existence of a positive common lower bound for the finite family using a construction with a positive default value.

All desired Gaussian statements remain valid in dimension zero: \(Z=1\), \(\det P=1\), and coordinate statements are vacuous.

Compactness of the unit sphere is an alternative, but be careful: the norm on `ι → ℝ` is the sup norm. If you want the quadratic Euclidean norm directly, use `EuclideanSpace` or explicitly work with \(\sum u_i^2\).

### Domination

Set \(c=a/2>0\). Then
\[
0\le g(u)\le e^{-c\sum_i u_i^2}.
\]
Use:

- continuity to establish `AEStronglyMeasurable`;
- `Real.exp_le_exp` for the pointwise comparison;
- the existing exponential integrability theorem;
- `Integrable.mono'`.

For coordinate products, reuse your existing theorem directly:
\[
|u_k u_jg(u)|
\le |u_k u_j e^{-c\sum_i u_i^2}|.
\]
The right-hand side is integrable by taking `.norm` of
`integrable_coord_mul_coord_mul_exp_neg_const_mul_sum_sq`.

This is cleaner than first proving \(|u_k u_j|\le\sum_i u_i^2\), which would then require another polynomial-Gaussian integrability lemma.

Finally,
\[
u_j(Hu)_i g(u)=\sum_k P_{ik}\,u_j u_k g(u).
\]
Obtain integrability using constant multiples and finite sums. No new domination argument is needed.

---

## 4. Package an analytic core, then thin adapters

I would avoid making the core theorem return one large nested conjunction. Use a small named proposition structure, schematically:

```lean
structure GaussianSecondMomentFacts (P : Matrix ι ι ℝ) : Prop where
  integrable_weight : ...
  integrable_coord_mul : ∀ k j, ...
  integrable_coord_apply : ∀ i j, ...
  second_moment : ∀ i j, ...
  fubini_ibp : ∀ i j, ...
```

Then expose:
```lean
gaussianSecondMomentFacts_of_posDef
gaussianZ_eq_of_posDef
```

Separating the normalising constant is useful: **the IBP clients do not need its closed form**.

Internally, make the final algebraic implication reusable:
```lean
fubiniIBP_of_integrable_of_secondMoment
```
Its assumptions should be exactly the integrability and moment statements it consumes, plus the matrix/inverse identification.

Finally add adapters for:

- the seabed’s scalar second-moment/IBP theorem;
- `localised_gaussian_K_expectation`;
- the Gaussian fields of existing hypothesis structures.

Two scope cautions:

1. **“With hypotheses `P.PosDef` only” means only the Gaussian analytic hypotheses disappear.** Any unrelated assumptions on localisation, observables, or asymptotic data remain.
2. Inspect `LaplaceCov6MomentHypotheses` carefully. D1–D3 establish moments only through degree two. If that structure requires sixth absolute moments or additional envelopes, these need extra proofs. They are true for PD Gaussians, but do not follow merely from the second-moment package.

A later convenience theorem named `gaussianHypotheses_of_posDef` can assemble everything once the exact target structure is understood.

---

## 5. Size and recommended cutoff

This is a medium-to-large excursion, not a single routine lemma. A planning estimate, assuming the existing spectral and one-dimensional infrastructure works as advertised:

| Subtask | Approximate new Lean |
|---|---:|
| Matrix/CLM bridge, coercivity, D1 | 100–250 lines |
| Change-of-variables wrapper and whitening algebra | 150–350 |
| Standard moments and D3 | 150–300 |
| Algebraic IBP discharge and adapters | 50–150 |
| D2 determinant/square-root/rpow simplification | 80–200 |

These are rough implementation ranges, not pin-verified estimates. API mismatch around Haar measure or spectral coordinates can dominate them.

**Cut D2 first if the excursion balloons.** D1 + D3 + IBP already remove the analytically unproved assumption from the multivariate track. The explicit partition function is valuable but independent of that immediate repair.

Next defer broad sixth-moment packages and refactoring every downstream theorem. Land the core result and one representative adapter first.

**Vote: target the PD Gaussian second-moment/IBP cluster—D1 + D3 + a thin hypothesis adapter via R1, deferring the closed-form normaliser D2.**