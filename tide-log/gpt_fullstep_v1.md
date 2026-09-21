## 1. Correctness of F1–F5

**Yes, with the positivity hypotheses carried explicitly into F4/F5.** There are two distinctions worth making:

- F1 needs only contraction; neither `c ≥ 0` nor positivity of `N` is needed.
- The clean, short proofs of F4/F5 take a **PSD additive fixed point** as input. Merely supplying its fixed-point equation is not enough for the proposed induction.

Write
\[
T(X)=AXA^\mathsf T,\qquad
S(X)=c\sum_iD_iXD_i^\mathsf T,\qquad L=T+S.
\]
Then `fullStep X = L X + N`.

### F1: correct

On a complete normed matrix space, `LipschitzWith K L` and `K < 1` imply that `X ↦ L X + N` is contracting. Banach gives existence, uniqueness among **all matrices**, and convergence from every starting matrix.

Use `K : ℝ≥0`, as expected by `LipschitzWith` and `ContractingWith`.

### F2: correct

The displayed bound is valid:
\[
\|L(X)-L(Y)\|
 \le \left(\|A\|\|A^\mathsf T\|
       +c\sum_i\|D_i\|\|D_i^\mathsf T\|\right)\|X-Y\|.
\]

**Do not replace `‖Aᵀ‖` by `‖A‖` in the infinity-operator norm.** Transposition is not generally an isometry for that norm: it exchanges maximum absolute row sum with maximum absolute column sum. You do not need a transpose-norm lemma for F2 as written.

This is a sufficient condition, potentially substantially stronger than spectral stability.

### F3: correct

For `N.PosSemidef` and `0 ≤ c`, `fullStep` preserves PSD. Start at zero, apply preservation inductively, and pass to the limit in the closed PSD cone.

For real matrices, remember that PSD includes **symmetry**, not just nonnegative quadratic forms.

### F4/F5: correct, with a particularly short proof

Suppose explicitly that
```lean
hadd : covStep A N Σadd = Σadd
haddPSD : Σadd.PosSemidef
```
and define
\[
B=S(\Sigma_{\rm add}),\qquad \Delta=\Sigma_{\rm full}-\Sigma_{\rm add}.
\]
Then \(B\succeq0\), and subtraction of the fixed-point equations gives
\[
\Delta=L(\Delta)+B.
\]

For F4, iterate `fullStep` from `Σadd`. The differences from `Σadd` satisfy
\[
Y_0=0,\qquad Y_{k+1}=L(Y_k)+B.
\]
Each `Yk` is PSD; convergence and closedness give \(\Delta\succeq0\).

**F5 then needs no further limiting argument:**
\[
\Delta-B=L(\Delta)\succeq0.
\]

Your monotonicity argument is also correct. If you formalise it, define Loewner comparison through PSD differences. Note that
\[
\operatorname{fullStep}(X)-\operatorname{covStep}(X)=S(X)\succeq0
\]
requires `X.PosSemidef`; it does not hold for arbitrary `X`.

**Where does `haddPSD` come from?** Under F2, the additive map is also contracting because
\[
\|A\|\|A^\mathsf T\|
\le \|A\|\|A^\mathsf T\|+c\sum_i\|D_i\|\|D_i^\mathsf T\|<1.
\]
Thus the same zero-iteration argument constructs a PSD additive fixed point.

Full contraction of `L` alone also forces additive stability in this finite-dimensional setting with `c ≥ 0`, but proving that is a separate positivity/spectral argument—not simply “delete a summand from a Lipschitz estimate.” For example, one can exploit \(T^k(I)\preceq L^k(I)\) to obtain decay of powers of `A`. I would **not** include that detour in this excursion: take a PSD additive fixed point as input, and discharge that input in the F2 corollary.

## 2. Norm choice and theorem organisation

I recommend **a norm-independent Banach helper, followed by a concrete infinity-operator-norm matrix development**.

### Abstract helper

The right abstraction is an ordinary complete normed additive group, not an arbitrary `PseudoEMetricSpace`:
```lean
variable {E : Type*}
  [NormedAddCommGroup E] [CompleteSpace E]
```

Given `L : E → E`, `b : E`, `hL : LipschitzWith K L`, and `hK : K < 1`, apply Banach to `fun x => L x + b`.

Linearity is not even needed for this helper. Translation preserves distances, which proves the affine map has the same Lipschitz constant.

Use the supplied API:
- `ContractingWith.fixedPoint`
- `ContractingWith.fixedPoint_isFixedPt`
- `ContractingWith.fixedPoint_unique`
- `ContractingWith.tendsto_iterate_fixedPoint`

An arbitrary pseudometric introduces avoidable difficulties: distance zero need not imply equality, and an arbitrary metric need not make translation an isometry.

### Concrete matrix layer

Locally select the operator-norm structures, using the instance names in your context:
```lean
attribute [local instance]
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
```
Check the resulting `Norm`, additive normed structure, and real normed-space structure together. Do not independently install the elementwise normed-group instance in this section.

Then try:
```lean
example : CompleteSpace (Matrix ι ι ℝ) := by
  infer_instance
```
Finite dimensionality over `ℝ` should supply completeness through `FiniteDimensional.complete`. This is preferable to obtaining completeness from the underlying iterated function space: that route can accidentally use the elementwise norm structure.

I cannot inspect your exact pin here, so the instance activation and argument order should be checked locally rather than treated as a tested code block.

### The Lipschitz estimate

Define the real quantity
```lean
q := ‖A‖ * ‖A.transpose‖
   + c * ∑ i, ‖D i‖ * ‖(D i).transpose‖
```
prove `0 ≤ q`, and package it as an `ℝ≥0`. Avoid repeated `Real.toNNReal` coercion simplification.

Useful algebraic helpers are:
```lean
fullLinear_sub :
  fullLinear A D c X - fullLinear A D c Y =
    fullLinear A D c (X - Y)

fullStep_sub_fullStep :
  fullStep A N D c X - fullStep A N D c Y =
    fullLinear A D c (X - Y)
```

Prove the norm bound with:
- `norm_add_le`
- `norm_sum_le`
- `norm_smul`
- `Matrix.linfty_opNorm_mul`, or generic `norm_mul_le` under the selected instance
- `abs_of_nonneg hc`

Then convert the distance estimate using `lipschitzWith_iff_dist_le_mul`.

The infinity-operator norm makes this estimate natural and avoids dimension factors. The elementwise norm is reasonable for an **abstract-only** F1 theorem, but is less attractive for the advertised checkable condition.

## 3. Closedness of the PSD cone

First check whether your pin already exposes the result. I would search before proving it:
```text
rg 'isClosed.*[Pp]osSemidef|[Pp]osSemidef.*isClosed|posSemidef.*[Tt]endsto' Mathlib
```
`Matrix.isClosed_setOf_posSemidef` is a plausible search name, **not a lemma name I can certify for your pin**.

If absent, prove one reusable helper, rather than embedding the limit argument in F3:
```lean
-- Schematic signature
theorem posSemidef_of_tendsto
    (hX : ∀ k, (X k).PosSemidef)
    (hlim : Tendsto X atTop (𝓝 S)) :
    S.PosSemidef
```

There are two parts:

1. **Symmetry passes to the limit.** For each `i j`, pass to the limit in
   `X k i j = X k j i`.
2. **Quadratic forms remain nonnegative.** For each vector `v`, obtain
   ```lean
   Tendsto (fun k => v ⬝ᵥ (X k *ᵥ v))
     atTop (𝓝 (v ⬝ᵥ (S *ᵥ v)))
   ```
   and apply `ge_of_tendsto` with the eventual nonnegativity hypothesis.

Entrywise symmetry is often simpler than transporting the entire transpose map through continuity.

**The norm-sensitive issue is coordinate continuity.** For the elementwise norm, function-space continuity lemmas handle this directly. Under the operator-norm instance, do not assume those lemmas elaborate unchanged. Coordinate evaluation is a real linear map on a finite-dimensional space, so `LinearMap.continuous_of_finiteDimensional` gives a robust route. The quadratic-form map, with `v` fixed, is also linear in the matrix argument.

Alternatively prove
```lean
IsClosed {X : Matrix ι ι ℝ | X.PosSemidef}
```
as the intersection of the entrywise symmetry conditions and all quadratic-form nonnegativity conditions, and subsequently use `IsClosed.mem_of_tendsto`.

For preservation, the central algebraic lemmas are the ones you identified:
- `Matrix.PosSemidef.add`
- `Matrix.PosSemidef.smul`
- `Matrix.PosSemidef.conjTranspose_mul_mul_same`

Check the orientation of the last lemma. If it proves positivity of `Bᴴ * X * B`, instantiate it with `B = Dᵀ` to get `D * X * Dᵀ`, simplifying conjugate transpose over `ℝ`. No symmetry hypothesis on `D` is needed.

## 4. Loewner order versus matrix `≤`

**Use `PosSemidef (Y - X)` directly in this excursion.**

There are two issues to avoid:

- Matrix notation unfolds to a function type, so pointwise order infrastructure is nearby.
- Loewner-order infrastructure may be available through additional imports, but its exact instances and compatibility conditions are pin-dependent.

The names `Matrix.instPartialOrder` and `Matrix.le_iff`, without checking their types and activated instances, do not establish which order is in use.

If your pin has the relevant order module, inspect it:
```text
rg 'instPartialOrder|le_iff|StarOrderedRing' Mathlib/Analysis/Matrix Mathlib/LinearAlgebra/Matrix
```
In particular, check whether `Matrix.PosSemidef.le_iff` actually exists rather than designing the proof around it.

The theorem conclusions you want are unambiguous:
```lean
(Σfull - Σadd).PosSemidef
```
and
```lean
(Σfull - Σadd -
  c • ∑ i, D i * Σadd * (D i).transpose).PosSemidef
```

No order instance is needed for either proof. Even monotonicity can be expressed directly:
```lean
(Y - X).PosSemidef →
  (fullStep A N D c Y - fullStep A N D c X).PosSemidef
```

## 5. Scope and recommended proof organisation

This is a coherent target cluster, provided you avoid three side quests:

1. A general matrix Loewner-order API.
2. Deriving additive stability from arbitrary-norm contraction of the full positive operator.
3. Deriving the covariance law from the stochastic minibatch model.

The last distinction matters: the proposed result validates and solves the stated affine covariance law. It does not yet prove that the SGLD random update obeys that law. Likewise, instantiating the minibatch coefficient requires the usual size assumptions to prove `c ≥ 0`.

I would organise the work as follows:

1. **Definitions and identities:** `fullLinear`, `fullStep`, subtraction identities.
2. **Abstract contraction wrapper:** fixed point, uniqueness, convergence.
3. **Operator-norm criterion:** F2 and the additive contraction corollary.
4. **PSD infrastructure:** preservation and a reusable limit-closedness lemma.
5. **PSD fixed point:** F3 by iteration from zero.
6. **Comparison with a supplied PSD additive fixed point:** F4 by shifted iteration.
7. **First-order inflation:** F5 directly from the fixed-point difference identity.

F4/F5 are inexpensive once the PSD limit lemma exists; they are worth retaining. The main implementation risks are norm-instance coherence and closedness, not the comparison argument.

**Vote: F1–F5 as one full-step contraction/PSD-inflation cluster, using the infinity-operator norm and a supplied PSD additive fixed point for the comparison theorems.**