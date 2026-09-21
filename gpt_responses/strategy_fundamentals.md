## Executive recommendation

All three targets are mathematically worthwhile. None requires new measure-theoretic machinery beyond what you already have.

My recommended order is **B → A → C**, with a short API reconnaissance for A before starting B:

- **B:** fastest route to a new, note-specific result. Reuse the quartic integrability theorem by changing its parameter—not by a change of variables.
- **A:** broadly reusable. Try the continuous-multilinear route briefly; keep Leibniz as a reliable fallback.
- **C:** use **general-\(H\) Stein**, then specialize to the standard Gaussian. Do not build the general result through multiplicity cases or whitening unless the repo already has a convenient observable-level whitening theorem.

The intended formulas are correct. The main qualifications are:

1. B1 needs separate normalization/positivity facts before becoming a Gibbs-expectation statement.
2. C2 is correct even for nonsymmetric \(A,B\), **provided \(\Sigma\) is symmetric**.
3. C3 needs tensor symmetry to combine its three contractions.
4. These exact identities do not themselves formalize the note’s asymptotic remainder estimates.

**API caveat:** I cannot inspect or compile against your checkout here. Names quoted in your excerpts are confirmed by those excerpts; names marked **[check]** below are search/check candidates, not claims about v4.33.0.

---

# A. Jacobi and log-determinant derivatives

## Statements

A1 is correct with:

```lean
[Fintype ι] [DecidableEq ι]
```

No invertibility, symmetry, or positivity is needed. The empty-index case is valid too.

A2 is correct under `((H s₀).det ≠ 0)`. Write the function explicitly as:

```lean
fun s => Real.log ((H s).det)
```

The derivative of Mathlib’s real logarithm at a negative nonzero argument is indeed \(1/x\), so this gives the log-absolute-determinant formula. You do **not** need a separate hypothesis that the determinant stays nonzero near `s₀`: differentiability gives continuity, and the chain-rule API only needs nonvanishing at the point.

The positive-determinant wrapper should simply pass `ne_of_gt hpos`.

## First try: continuous multilinearity, using columns via transpose

I would spend a bounded amount of time investigating this route before doing Leibniz.

The useful construction is not a special “column determinant” API. Instead:

1. Take the row determinant alternating map.
2. Forget alternation.
3. Make the resulting multilinear map continuous.
4. Apply it to the **rows of \(H^\mathsf T\)**.

Schematically:

```lean
-- Schematic, not checked Lean:
D : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ
D x = Matrix.det x

x s := (H s)ᵀ
x' := H'ᵀ
```

Then `D (x s) = (H s).det` by `Matrix.det_transpose`, and the derivative is the sum of determinants obtained by replacing one row of `Hᵀ`, hence one column of `H`.

API reconnaissance:

- `Matrix.detRowAlternating` — given in your question.
- `AlternatingMap.toMultilinearMap` — expected standard projection.
- `MultilinearMap.toContinuousMultilinearMap` **[check]**.
- `MultilinearMap.continuous_of_finiteDimensional` **[check]**.
- `ContinuousMultilinearMap.linearDeriv_apply` **[check]**.
- `hasDerivAt_pi` / `hasFDerivAt_pi` **[check signatures/names]**.
- `ContinuousMultilinearMap.hasFDerivAt` — confirmed by your pin.

The mathematical reason continuity is automatic is that every input space `ι → ℝ` is finite-dimensional. If the bundled conversion exists, this route avoids essentially all permutation algebra.

**Decision rule:** if constructing `D` and evaluating `D.linearDeriv` takes more than a small prototype, switch to Leibniz. Do not develop a new finite-dimensional multilinear-continuity framework just for Jacobi.

## A reusable algebraic helper

Prove this independently of differentiation:

```lean
∑ i, (A.updateCol i (fun j => B j i)).det =
  (A.adjugate * B).trace
```

Your Cramer route is exactly right:

\[
\det(A[i\leftarrow B_{\cdot i}])
=(\operatorname{adj}A\,B_{\cdot i})_i.
\]

Use the supplied:

- `Matrix.cramer_apply`
- `Matrix.cramer_eq_adjugate_mulVec`

and expand:

- `Matrix.trace`
- `Matrix.mul_apply`
- `Matrix.mulVec`

There should be no substantial mathematics left after those rewrites. In particular,

\[
\sum_i\sum_j \operatorname{adj}(A)_{ij}B_{ji}
=\operatorname{tr}(\operatorname{adj}(A)B).
\]

This is also a good place to catch transpose mistakes.

I cannot confirm an existing theorem for this exact sum on your pin. It is short enough that I would prove a local helper rather than spend long searching.

## Leibniz fallback: make column replacement a separate lemma

Yes, Leibniz is a reliable route. Use `Matrix.det_apply'`, not `det_apply`, if possible: real multiplication by the cast sign is easier than differentiating through a unit action.

Before touching derivatives, prove:

\[
\det(A[i\leftarrow b])
=
\sum_\sigma \varepsilon_\sigma\,
b_{\sigma(i)}
\prod_{j\ne i}A_{\sigma(j),j}.
\]

The key point is that with your determinant convention,

```lean
A.updateCol i b (σ j) j
```

branches on **`j = i`**, not on `σ j = i`. Thus there is no permutation-injectivity bookkeeping here.

Implementation advice:

- Split the product at `i`.
- On `univ.erase i`, simplify the update using `j ≠ i`.
- Never divide by `A (σ i) i`: A1 must cover singular matrices and zero entries.
- Keep the update-column lemma separate from the differentiated determinant expression.
- Use `Finset.sum_comm` only after both expressions are in the same fixed normal form.

Names to check:

- `HasDerivAt.sum` / `HasDerivAt.fun_sum` **[check]**
- `HasDerivAt.prod` / `HasDerivAt.finset_prod` **[check]**
- `Finset.mul_prod_erase` **[check exact orientation]**

The likely derivative-product output may differ by commutativity from your preferred ordering. Resolve that with `ring` inside individual summands, not global rewriting of the entire determinant expansion.

## A2: use the inverse formula, not cancellation of matrices

After A1 and `HasDerivAt.log`, the derivative is

\[
\frac{\operatorname{tr}(\operatorname{adj}(A)B)}{\det A}.
\]

Use the supplied `Matrix.nonsing_inv_apply` to obtain

\[
A^{-1}=(\det A)^{-1}\,\operatorname{adj}(A).
\]

Convert `det A ≠ 0` into `IsUnit A.det` using `isUnit_iff_ne_zero`. The resulting `h.unit⁻¹` coercion may require a small helper, but this remains simpler than multiplying `mul_adjugate` by inverses.

Then expand the trace or use scalar-linearity lemmas. No trace-cyclic identity is needed.

## Estimated size

Including reusable helpers and wrappers:

| Route | Estimated lines |
|---|---:|
| Continuous-multilinear packaging works directly | 130–220 |
| Leibniz fallback | 220–350 |
| A2 and positive wrapper, within either total | 25–50 |

A full multivariate `HasFDerivAt` theorem for determinant would be a useful bonus, but I would not make it a prerequisite for the path statement.

---

# B. Radial virial and localized quartic moments

## B1: correct hypotheses and proof

Your hypotheses suffice. Let

\[
F(r)=r^2e^{-U(r)},\qquad
F'(r)=2r e^{-U(r)}-r^2U'(r)e^{-U(r)}.
\]

Assume:

- `ContinuousWithinAt U (Ici 0) 0`;
- the specified derivative hypothesis on `Ioi 0`;
- integrability of both terms on the right;
- `Tendsto F atTop (𝓝 0)`.

Then the supplied
`integral_Ioi_of_hasDerivAt_of_tendsto`
gives exactly the desired identity.

**Endpoint distinctions:**

- `F 0 = 0` is algebraic and needs no continuity assumption on `U`.
- Right-continuity of `U` suffices for the required right-continuity of `F`.
- It is stronger than necessary: one could assume right-continuity of `F` directly, or suitable control near zero.

I would state the main theorem with right-continuity of `U`, because it is natural for applications. An auxiliary theorem with hypotheses directly on `F` is probably unnecessary: Mathlib’s FTC theorem already provides it.

For Lean, deliberately define `F'` in the **difference-of-two-integrable-functions** form above. Obtain its integrability via scalar multiplication and subtraction. Do not leave the derivative as an expanded product-rule expression.

Useful APIs:

- `HasDerivAt.pow`, `.neg`, `.exp`, `.mul`
- `Integrable.const_mul`, `Integrable.sub`
- `MeasureTheory.integral_sub`
- `MeasureTheory.integral_const_mul`

The derivative proof should end with a small `convert … using 1 <;> ring`.

## B2: the constants are correct

For

\[
U(r)=\frac{t}{15}r^4+\frac{\gamma}{2}r^2,
\]

we have

\[
rU'(r)=\frac{4t}{15}r^4+\gamma r^2.
\]

Thus

\[
4t\langle K\rangle+\gamma\langle r^2\rangle=2,
\]

and your conclusion follows:

\[
t\langle K\rangle=\frac12-\frac{\gamma}{4}\langle r^2\rangle.
\]

The loss

\[
L=K+\frac{\gamma}{2t}r^2
\]

is correct when `t > 0`. Isolate the exponent identity as a simp/helper lemma; it will otherwise recur throughout the proof.

## Integrability: change the quartic theorem’s parameter

This is substantially cheaper than Gaussian domination.

Set \(a=t/15>0\). Your existing theorem with parameter **`24 * a`** gives

\[
x^n\exp\!\left(- (24a)\frac{x^4}{24}\right)
=x^n e^{-a x^4}.
\]

So:

```lean
quartic_integrable_pow_pot n (t := 24 * a) ...
```

followed by pointwise algebra gives the exact majorant you need. There is **no scaling change of variables**.

Then restrict to `Ioi 0`. For \(r>0\), \(\gamma\ge0\),

\[
0\le r^n e^{-a r^4-\gamma r^2/2}
\le r^n e^{-a r^4}.
\]

Use `Integrable.mono'` on the restricted measure, with measurability from continuity. Expected restriction API: `Integrable.integrableOn` **[check invocation]**.

Prove one reusable lemma for all `n : ℕ`. The B2 radial integrands only need:

- \(n=1\): partition function;
- \(n=3\): radius-squared numerator;
- \(n=5\): quartic numerator and the quartic part of the virial integrand.

Odd powers are harmless on `Ioi 0`; take care not to use their nonnegativity globally on `ℝ`.

## Decay: use the supplied exponential theorem with \(n=1\)

Avoid introducing Gaussian-tail bounds.

For \(r\ge1\),

\[
0\le r^2e^{-a r^4-\gamma r^2/2}
\le r^4e^{-a r^4}
=\frac1a\,(a r^4)e^{-a r^4}.
\]

Now compose

```lean
Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
```

with `r ↦ a * r ^ 4`, whose limit is `atTop`, and squeeze.

The polynomial-at-infinity API needs checking—look for `tendsto_pow_atTop` and positive constant multiplication lemmas—but the exponential part is exactly the theorem you already located.

## Important planar/Gibbs bookkeeping

Two points can otherwise cause late proof failures.

### 1. Radius versus radius squared

Your polar theorem accepts `G (z.1^2 + z.2^2)`. For a general radius-profile `U`, the corresponding `G` is

\[
G(s)=e^{-U(\sqrt{s})}.
\]

On the radial side use `Real.sqrt_sq_eq_abs` and `r > 0`.

For B2, avoid square roots entirely:

\[
G(s)=\exp(-ts^2/15-\gamma s/2).
\]

This is much cleaner.

### 2. Integral equalities do not establish integrability

Lean’s integral is totalized. Your unconditional `integral_radial` equality is not by itself a proof that a planar integrand is integrable.

You will need either:

- an integrability-transfer lemma for the polar change of variables; or
- a direct domination argument by the already-integrable unlocalized quartic planar integrands.

Search around the polar equivalence for an integrability counterpart to `integral_comp_polarCoord_symm` **[exact name unknown]**.

Also prove the localized partition function is positive before dividing. One convenient route is positivity of the radial integral of the continuous, strictly positive-on-`Ioi 0` integrand. `MeasureTheory.integral_pos_iff_support_of_nonneg_ae` is a candidate **[check signature]**.

## Estimated size

| Component | Lines |
|---|---:|
| B1 | 50–85 |
| Quartic domination and decay helpers | 70–130 |
| Planar integrability, positivity, B2 | 100–180 |
| **Total** | **220–395** |

The upper end is mainly polar integrability bookkeeping, not the FTC argument.

---

# C. Gaussian fourth moments and contractions

## Correctness and symmetry

### C1

Correct. Use a real-valued Kronecker delta, for example:

```lean
if a = b then (1 : ℝ) else 0
```

and be explicit that the exponent in the normalizing constant is real:

```lean
(2 * Real.pi) ^ ((d : ℝ) / 2)
```

### C2

Your general formula is correct:

\[
\operatorname{Cov}(x^\mathsf TAx,x^\mathsf TBx)
=
\operatorname{tr}(A\Sigma B\Sigma)
+\operatorname{tr}(A\Sigma B^\mathsf T\Sigma).
\]

Here \(A,B\) may be arbitrary real matrices; \(\Sigma\) must be symmetric.

For symmetric \(A,B\), division by four gives the stated half-quadratic formula. In fact symmetry of either one suffices to identify the two traces, but the symmetric-\(A,B\) wrapper is the natural Hessian-facing statement.

Check how `Matrix.PosDef` on your pin packages Hermitian symmetry; use the corresponding projection rather than adding a redundant hypothesis if possible. Candidate projections are `Matrix.PosDef.isHermitian` / `.isSymm` **[check]**.

### C3

With

\[
(T:\Sigma)_j=\sum_{k,l}T_{jkl}\Sigma_{kl},
\]

the formula is correct for fully symmetric \(T\):

\[
E[(g^\mathsf Tx)T(x,x,x)]
=3(\Sigma g)^\mathsf T(T:\Sigma).
\]

Without symmetry, retain three distinct contractions. Full tensor symmetry is sufficient and convenient, even though one can weaken it.

## Best route: a general covariance-form Stein lemma

Prove this reusable wrapper first:

\[
E_H[D_{\Sigma e_a}f]=E_H[x_a f].
\]

Set

```lean
e a := EuclideanSpace.single a (1 : ℝ)
v a := Matrix.toEuclideanCLM (𝕜 := ℝ) H⁻¹ (e a)
```

Then establish:

\[
H v_a=e_a,\qquad
\tfrac12\,qderiv(H,x,v_a)=x_a.
\]

The second identity uses symmetry of \(H\). Both terms in `qderiv` become \(x_a\).

Do this algebra once. It isolates the matrix/Euclidean coercion work from every moment proof.

You can first prove the **unnormalized** wrapper:

\[
\int x_a f(x)\,k_H(x)\,dx
=
\int D_{v_a}f(x)\,k_H(x)\,dx.
\]

Normalize later using `integral_quadKernel_pos hH`. This keeps the Stein proof independent of expectation-linearity infrastructure.

## Exact choices of \(f,v\)

### Second moments

For indices \(a,b\), use

\[
f(x)=x_b,\qquad v=\Sigma e_a.
\]

Then

\[
D_vf=\Sigma_{ba},
\qquad
E[x_ax_b]=\Sigma_{ba}=\Sigma_{ab}.
\]

Even if general second moments already exist elsewhere, this is a short corollary of your new wrapper and a useful sanity check.

### Fourth moments

For indices \(a,b,c,e\), use

\[
f(x)=x_bx_cx_e,\qquad v=\Sigma e_a.
\]

Its directional derivative is

\[
\Sigma_{ba}x_cx_e
+\Sigma_{ca}x_bx_e
+\Sigma_{ea}x_bx_c.
\]

Applying second moments gives

\[
E[x_ax_bx_cx_e]
=
\Sigma_{ab}\Sigma_{ce}
+\Sigma_{ac}\Sigma_{be}
+\Sigma_{ae}\Sigma_{bc}.
\]

There is no index-multiplicity case split. Repeated indices automatically produce the coefficients \(3\), etc.

This is “Stein twice” in the useful sense: one linear-moment lemma, then one cubic test function.

### Standard Gaussian

Specialize to \(H=I\), identify `quadKernel 1 = stdKernel`, and multiply by the standard partition function. There is no reason to separately prove C1 using product measures once this general result exists.

## Polynomial-growth and smoothness obligations

For the two tests:

| Test function | Growth degree | Directional derivative degree |
|---|---:|---:|
| \(x_b\) | 1 | 0 |
| \(x_bx_cx_e\) | 3 | 2 |

Use:

```lean
EuclideanSpace.proj (𝕜 := ℝ) i
```

for coordinate derivatives, exactly as your existing radial Stein proof does.

Recommended small helpers:

1. polynomial growth of a coordinate;
2. coordinate-product derivative formula;
3. polynomial growth of that derivative.

For growth:

\[
|x_i|\le\|x\|,
\]

and for fixed \(v\),

\[
|D_v(x_bx_cx_e)|
\le (|v_b|+|v_c|+|v_e|)\|x\|^2.
\]

Prefer `.mul`, `.add`, and constant-growth lemmas if imports permit. Your `.add` currently lives in `SufficientFamilies`; avoid importing a large downstream file merely for that elementary closure lemma. Move it to a foundational growth file or prove a local helper.

After rewriting the derivative explicitly, use polynomial-growth closure. Do not try to prove growth of an opaque `fderiv` expression.

Smoothness is just repeated multiplication of continuous-linear coordinate projections. `fun_prop` may solve it; explicit `.contDiff.mul` proofs are robust.

## C2 and C3: separate integration from finite-sum algebra

First prove general coordinate Wick. Then make the contraction lemmas **purely algebraic**, parameterized by a symmetric matrix `Σ`.

For C2:

1. Expand each quadratic form as a double sum.
2. Exchange finite sums and integrals, supplying weighted polynomial integrability.
3. Apply second/fourth coordinate moments.
4. Cancel the pairing corresponding to the product of means.
5. Identify the remaining two sums with traces.

Useful established names:

- `Matrix.mul_apply`
- `Matrix.trace`
- `Finset.sum_comm`
- `Finset.sum_mul`, `Finset.mul_sum`
- `MeasureTheory.integral_finset_sum`

Keep a fixed summation order while identifying each trace. Avoid asking `simp` to discover four-index permutations.

For C3, first prove the raw three-pairing contraction with no tensor symmetry. Then use tensor symmetry and sum reindexing to show the three terms agree. Representing `T` initially as

```lean
Fin d → Fin d → Fin d → ℝ
```

is likely cheaper than introducing a bundled symmetric trilinear-map interface.

## Why not whitening?

Whitening is competitive only if the repo already has something like

\[
E_H[F]=E_I[F\circ W]
\]

for arbitrary integrable observables, together with \(WW^\mathsf T=\Sigma\).

A bare `whiteningInv` construction is not enough to make that route cheaper: you still need change-of-variables, observable integrability, coordinate expansion, and matrix identities. General Stein avoids all of that.

For **C1 alone**, the existing `stein_coord` in `MonomialVisibility.lean` is worth inspecting. It may already provide the standard-kernel wrapper. For C1–C3 together, general-\(H\) Stein is the better foundation.

## Estimated size

| Component | Lines |
|---|---:|
| Covariance-form Stein wrapper and growth helpers | 100–180 |
| General second/fourth moments and C1 | 90–160 |
| C2 finite-sum/trace contraction | 100–180 |
| C3 tensor contraction | 70–140 |
| **Total** | **360–660** |

These estimates assume no new whitening machinery and no tensor abstraction layer.

---

## Scope boundaries worth recording

- **B:** \(\gamma\ge0\) is a proof-friendly restriction, not mathematically necessary. Quartic confinement permits every real \(\gamma\), but handling negative \(\gamma\) needs a different domination bound. Defer it.
- **C:** positive-definite precision covers nondegenerate Gaussians. Singular Gaussian covariance requires a separate pushforward formulation; inverse-precision kernels do not cover it.
- **A:** Jacobi does not formalize differentiation of the moving minimizer \(w^*(s)\); that remains a separate implicit-function/chain-rule step.
- **C and the note:** fourth moments prove the displayed Gaussian polynomial coefficients, not the \(O(\|\Sigma\|^3)\) remainder. A third-order Taylor expansion with only an absolute fourth-order remainder bound is not by itself enough to obtain that remainder order; additional smoothness and cancellation estimates are needed.

**Bottom line:** implement B with quartic domination, A with a short multilinear feasibility test followed by Leibniz if necessary, and C around one general-\(H\) coordinate Stein wrapper. The biggest avoidable costs are Gaussian domination in B, permutation multiplicity cases in C, and mixing determinant differentiation with adjugate algebra in A.