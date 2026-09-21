**A is mathematically correct, and A+B+C is a sensible target.** The proposed finite-dimensional Gaussian/covariance route works. However, I would first look for an **independent-block flattening lemma**: establish independence of the orthonormal projections of one Gaussian vector, then combine this with independence of the vectors across `(c,k)`. That can eliminate both the cross-block covariance calculation and the finite-time-window machinery.

I cannot inspect your pinned Mathlib source here, so below I distinguish reliable proof structure from lemma names that need checking.

## 1. Joint Gaussianity and covariance

### The proposed route works on a finite index set

For a finite block index `A`, set
\[
Z(\omega)(a)=\xi_a(\omega),\qquad
L(z)(a,i)=\langle u_i,z(a)\rangle.
\]
Then:

1. Independent Gaussian `ξ a` give `HasGaussianLaw Z`.
2. `L` is a continuous linear map, built from evaluation CLMs, `innerSL`, and a finite Pi constructor.
3. Hence `L ∘ Z` has a Gaussian law.
4. Its distinct coordinate covariances vanish.
5. The jointly Gaussian independence criterion gives independence of its scalar coordinates.

There is no requirement that the **sup-norm Pi space itself be a Hilbert space**: it is the ambient space for the Gaussian random element and the CLM. The coordinate spaces used by the covariance-inner criterion are `ℝ`.

### Different blocks

For `a ≠ a'`, use independence of `ξ a` and `ξ a'`, then compose with the measurable projections:
\[
\langle u_i,\xi_a\rangle\quad\text{and}\quad
\langle u_j,\xi_{a'}\rangle
\]
are independent.

`IndepFun.covariance_eq_zero` is a plausible search target, but I would **not commit to that exact identifier or argument list without checking**. Search for both orientations of the name:
```text
covariance_eq_zero
covariance.*indep
IndepFun.*covariance
```

The safe integrability budget is:

- both projections are `MemLp ... 2 P`;
- therefore both are integrable;
- their product is integrable.

Thus you can satisfy a covariance theorem formulated with `L²` assumptions, or fall back to
\[
\operatorname{cov}(X,Y)=\int XY-\left(\int X\right)\left(\int Y\right)
\]
and the independent-product integral theorem. Mathematically, independence plus individual `L¹` integrability already suffices here; using the available Gaussian `L²` facts avoids API-sensitive minimality.

### Same block

Prefer this order:

1. transport covariance through `P.map (ξ a) = stdGaussian`;
2. evaluate `covarianceBilin_stdGaussian` on the two projection functionals.

The target identity is
\[
\operatorname{cov}_P(\langle u,\xi_a\rangle,\langle v,\xi_a\rangle)
=\langle u,v\rangle.
\]

Depending on the covariance-bilinear API, the arguments will be either vectors or their Riesz-dual CLMs. This is a type-matching issue, not a mathematical obstacle.

**Polarisation is a good fallback**, especially if your seabed already has an easy second-moment transport lemma. For centered projections,
\[
\operatorname{cov}(X,Y)=\int XY
=\frac14\left(\int(X+Y)^2-\int(X-Y)^2\right).
\]
Apply the second-moment formula to `u + v` and `u - v`. Those vectors need not be unit, so make sure the available lemma returns `‖w‖²` for arbitrary `w`, rather than handling only unit vectors.

I would not start with polarisation: it introduces subtraction-of-integrals and integrability bookkeeping that the covariance API may already package.

### A potentially shorter architecture: one block, then flatten

Prove once:
```lean
-- Schematic statement, not checked syntax
lemma iIndepFun_inner_of_stdGaussian
    (hξ : HasGaussianLaw ξ P)
    (hlaw : P.map ξ = stdGaussian)
    (hu : Orthonormal ℝ u) :
    iIndepFun (fun i ω => ⟪u i, ξ ω⟫_ℝ) P
```

Alternatively, prove coordinate independence directly under `stdGaussian`, then transport it to `ξ`.

Now the whole coordinate vector
```lean
fun ω i => ⟪u i, ξ a ω⟫_ℝ
```
is a measurable function of the independent block `ξ a`. Consequently:

- these coordinate vectors are independent across `a`;
- their coordinates are independent within each `a`;
- flattening gives independence across `(a,i)`.

Look for an `iIndepFun` theorem involving `uncurry`, `prod`, `pi`, or independent groups. **Group independence is essential**: pairwise cross-block independence alone would not justify flattening. Here you have the stronger hypothesis needed.

If this theorem is readily available, it is my preferred route.

## 2. Scalar inner products and `Orthonormal`

### Scalar factors should cause only minor friction

The criterion’s hypothesis may quantify over `x y : ℝ`:
\[
\operatorname{cov}(\langle x,X_i\rangle,\langle y,X_j\rangle)=0.
\]
Once you have `cov[X_i,X_j] = 0`, use
\[
\langle x,z\rangle_{\mathbb R}=xz,\qquad
\operatorname{cov}(xX_i,yX_j)=xy\,\operatorname{cov}(X_i,X_j).
\]

A local scalar-inner simplification lemma plus covariance scaling should suffice. Do not expect supplying only the `x = y = 1` case to discharge the theorem automatically; explicitly bridge from coordinate covariance to arbitrary scalar probes.

### State A using `Orthonormal ℝ u`

Yes. A helper for a general orthonormal family is cleaner than one specialized to `orthoCol`.

You can generalize the direction index separately from the ambient Euclidean-space index, but that is optional. For this tide,
```lean
u : ι → EuclideanSpace ℝ ι
hu : Orthonormal ℝ u
```
is a reasonable scope.

For `orthoCol`, prove a separate helper from `orthoOf_transpose_mul`:
\[
\langle \operatorname{orthoCol}(i),\operatorname{orthoCol}(j)\rangle
=(U^\mathsf TU)_{ij}=\delta_{ij}.
\]

The likely work is:

- unfold the column representation;
- rewrite the Euclidean inner product as a coordinate sum;
- match it to `Matrix.mul_apply`;
- use the matrix identity;
- conclude via the characterization of orthonormality by these inner products.

This helper is worth isolating. Unit-column norms alone do not supply the off-diagonal condition.

## 3. Keep the ℕ-indexed interface

**Choose (a), unless block flattening avoids the window entirely.** Do not change the chain theorems merely to accommodate the Gaussian proof.

### Best case: flatten independent blocks directly

Take the block index to be `Fin C × ℕ`. The Gaussian argument occurs only inside the finite direction space. A general independent-block assembly theorem can then handle the infinite block family without ever constructing a Gaussian random element in an infinite-dimensional Pi space.

This is a significant simplification.

### Otherwise: finite restrictions, then recover global independence

Independence is determined by finite subfamilies. The exact wrapper lemma needs source inspection, but even if there is no conveniently named equivalence, this is close to the defining finite-event formulation of `iIndepFun`.

For any finite set
```lean
s : Finset (Fin C × ℕ × ι)
```
choose a common `T` greater than every time appearing in `s`. The selected family is an injective reindexing of the family on
```lean
Fin C × Fin T × ι.
```
Restrict finite-window independence to that family, then discharge the finite-subfamily criterion.

Two cautions:

- Independence is readily **restricted** along an injection; independence of one restriction does not imply independence of the whole family.
- When proving Gaussianity for a selected family, do not reindex the input vectors by the selected triples and claim they remain independent: several triples may use the **same** `(c,k)`. Assemble the Gaussian vector using the distinct block indices, then project.

Also watch the associativity:
```lean
Fin C × ℕ × ι
```
is right-associated, whereas block flattening naturally produces
```lean
(Fin C × ℕ) × ι.
```
Use an explicit product-associativity equivalence rather than fighting definitional equality.

### Why not (b) or (c)?

- **Padding with zeros** preserves independence, but destroys the required variance and fourth moment beyond the window when `v ≠ 0`. Thus it does not produce the existing global `FourthMomentTable`.
- **Adding independent copies** changes the probability-space construction and creates a law-comparison task. You already have the infinite independent noise family; there is nothing to gain.

## 4. B, C, and likely size

### B should be routine after A

Compose each scalar coordinate with multiplication by `Real.sqrt (2*h)` to get independence of `projNoise`. The remaining fields are the existing unit-direction facts:

- `L⁴`;
- mean zero;
- second moment `2*h`;
- third moment zero;
- fourth moment `3*(2*h)^2`.

Prefer factoring these existing per-element proofs into reusable helpers over duplicating them. No positivity stronger than `0 ≤ h` should be needed for B; the degenerate `h = 0` case is valid.

### C should retain the existing infinite-time theorem

Instantiate with
```lean
η c k i := projNoise h (orthoCol hP i) (ξ c) k
```
and use `inner_ulaChain_eq_realChain`.

The likely work is bookkeeping:

- match the exact coordinate-estimator definition;
- derive the required bounds on `ρ i = 1 - h*p i`;
- discharge denominator positivity;
- match the `(1 + δᵢⱼ)` factor;
- rewrite from eigenbasis coordinates to the claimed Frobenius expression, if this is not already packaged.

“Unconditional” should mean **the extra `FourthMomentTable` hypothesis is discharged**. Gaussian-noise, block-independence, step-size, sample-size, and initialization assumptions remain.

### Instances and law construction

For finite Pi types of Euclidean spaces, the standard topology, normed-space, measurable-space, Borel-space, and countability instances should generally be routine. The main hazards are representation changes between ordinary Pi types and `EuclideanSpace`/`PiLp`, not missing mathematics.

For `HasGaussianLaw ξ P`, retain explicit measurability or a.e. measurability of `ξ`. Do not plan around map equality alone automatically supplying the relevant field. Package the law once from:

- the needed measurability assumption;
- `P.map ξ = stdGaussian`;
- Gaussianity of `stdGaussian`.

Then reuse that helper.

### Size estimate

**~400 lines is plausible, but optimistic until the independence-combination API is settled.**

- With a usable block-flattening lemma and covariance transport API: quite plausible.
- With finite-window extraction, a hand-built finite-subfamily wrapper, and polarisation: expect noticeably more.

I would implement in this order:

1. `Orthonormal ℝ (orthoCol hP)`.
2. Independence of projections within one standard-Gaussian block.
3. Global independence, preferably by block flattening.
4. Global `FourthMomentTable`.
5. E4 specialization.

**Vote: A+B+C**, with A stated for an orthonormal family and the final table kept on `Fin C × ℕ × ι`. Prefer the one-block Gaussian proof plus independent-block flattening; retain the finite-window Gaussian/covariance route as the fallback.