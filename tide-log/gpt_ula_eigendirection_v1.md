**G is the right bridge theorem**, with three important qualifications: the projection needs a **left eigenvector** (or symmetry of the precision matrix), the innovation-variance statement needs **`0 ≤ h`**, and the stationary-variance parametrisation needs **nondegeneracy/stability assumptions** beyond those needed for the finite-chain identity.

I would organise this as a deterministic projection theorem, a moment-based probabilistic theorem, and Gaussian/spectral corollaries.

I cannot check your Mathlib pin here. Below, I distinguish the names already checked in your context from additional API details whose exact signatures should be checked locally.

## 1. Correct statement and independence assumptions

### The eigenvector hypothesis needs symmetry

Write `Q` for the precision matrix and `μ` for the probability measure, avoiding the overloaded `P`.

The identity you need is
\[
\langle u,(I-hQ)z\rangle=(1-hp)\langle u,z\rangle.
\]
A right eigenvector hypothesis `Q *ᵥ u = p • u` **does not imply this for an arbitrary matrix**. It does imply it if `Q` is symmetric. Alternatively, assume directly that `Qᵀ *ᵥ u = p • u`.

For example, with \(Q=\begin{pmatrix}p&a\\0&q\end{pmatrix}\), \(u=e_1\) is a right eigenvector, but the first coordinate of \(Qz\) also contains \(az_2\).

In your positive-definite/spectral setting, symmetry is presumably already available. Make it explicit in the theorem or obtain it from the existing precision-matrix hypothesis.

### Separate the deterministic and probabilistic content

First prove a theorem with **no measure-theoretic assumptions**:

- `B : E →L[ℝ] E`;
- `u : E`, `ρ : ℝ`;
- `hproj : ∀ z, inner ℝ u (B z) = ρ * inner ℝ u z`;
- a vector recursion started at zero.

Then its projection is `realChain ρ η`, where `η` is the projected vector innovation. A schematic statement is:
```lean
-- Schematic: adapt recursion names to the project.
theorem projection_eq_realChain
    (hproj : ∀ z, inner ℝ u (B z) = ρ * inner ℝ u z) :
    ∀ k ω, inner ℝ u (w k ω) = realChain ρ η k ω
```
The proof is induction on `k`, using `inner_add`, `inner_smul_right`, and `hproj`. Neither `‖u‖ = 1` nor Gaussianity belongs in this lemma.

Then specialise to `B = euclid (ulaStep Q h)` and `ρ = 1 - h*p`.

**Check the innovation indexing carefully:** both recursions must use `η (k+1)` if the vector recursion uses `ξ (k+1)`. Noise at time zero may then be unused.

### Pairwise independence suffices—but not for every interpretation

For the expected pooled variance, pairwise independence across distinct `(c,k)` is enough. Indeed, your existing AR theorem only needs `MemLp` and the uncentred second-moment table.

Thus the clean layering is:

1. **Moment-table bridge:** assume the projected innovations satisfy the existing AR hypotheses.
2. **Gaussian pairwise-independent corollary:** derive that table using `white_of_indep`.
3. Optionally accept `iIndepFun` in a convenience wrapper, extracting pairwise independence with `iIndepFun.indepFun`.

There is one semantic distinction worth preserving:

- Pairwise independence suffices for the **expected quadratic statistic**.
- Mutual independence is the natural assumption if you also claim the usual **ULA Markov-chain law**, with fresh noise independent of the entire past.

Pairwise independence alone does not guarantee that latter property.

Finally, require `[IsProbabilityMeasure μ]`, and assume `0 ≤ h` for innovation variance `2*h`. For negative `h`, `Real.sqrt (2*h)` is zero, so the claimed variance is wrong.

## 2. Gaussian second moments and the Lean route

I recommend first proving a reusable lemma for arbitrary `u`, without normalising it:
\[
\int \langle u,\xi(\omega)\rangle\,d\mu=0,\qquad
\int \langle u,\xi(\omega)\rangle^2\,d\mu=\|u\|^2,
\]
together with `MemLp (fun ω => inner ℝ u (ξ ω)) 2 μ`.

The unit-vector case is then just rewriting.

### Work under `stdGaussian E` first

Introduce the functional explicitly:
```lean
let L : StrongDual ℝ E := innerSL ℝ u
```
Prove the scalar facts under `stdGaussian E`, and only afterwards transfer them through the law of `ξ`.

This avoids repeatedly mixing:

- the coercion `StrongDual → function`;
- composition with `ξ`;
- rewriting the pushforward measure;
- the variance/second-moment calculation.

For the mean, use the checked `integral_id_stdGaussian` and commute `L` with the integral. The proposed `L.integral_comp_comm` route is appropriate; check its integrability argument and rewrite orientation locally. The Gaussian `MemLp` fact supplies integrability on a probability space.

For the second moment, there are two good routes.

**Route A: variance.**

Use your checked
```lean
variance_dual_stdGaussian L
```
and rewrite centred variance as the second moment using the zero mean.

The norm identity needed is
```lean
‖(innerSL ℝ u : StrongDual ℝ E)‖ = ‖u‖
```
The suggested `innerSL_apply_norm` is the name to check for this partial-application norm identity; it may also be handled by `simp`. Do not confuse it with the norm of the entire map `innerSL ℝ`.

I would not commit to `variance_def'` or `variance_eq_integral_sub_sq` without checking the pin. Prefer the centred-square characterisation
\[
\operatorname{Var}(L)=\int (L-\textstyle\int L)^2
\]
if it is readily available: with zero mean, no expansion of integrals is needed.

**Route B: covariance.**

Since you already checked `covarianceBilin_stdGaussian = innerSL ℝ`, specialise that equality at `u,u`. After identifying it with scalar covariance and using the zero mean, it gives
\[
\int \langle u,z\rangle\langle u,z\rangle\,d\gamma(z)
=\langle u,u\rangle.
\]

This avoids the dual-norm lemma altogether. It also generalises immediately to
\[
\int \langle u,z\rangle\langle v,z\rangle\,d\gamma(z)
=\langle u,v\rangle.
\]
I would favour this route **if the project already has a convenient scalar-covariance bridge**; otherwise the checked variance theorem is likely shorter.

### Transfer through the law

Use `MeasureTheory.integral_map` with `μ.map ξ = stdGaussian E`, once for the linear observable and once for its square.

For `MemLp`, use the corresponding map-measure equivalence rather than trying to obtain it from the numerical integral calculation. A candidate API name to check is `memLp_map_measure_iff`; inspect its measurability assumptions and direction.

For a first implementation, assuming `Measurable (ξ k)` is simpler than supporting only `AEMeasurable`. The latter is mathematically sufficient but can entail additional AE composition bookkeeping.

### Scale at the end

Set \(a=\sqrt{2h}\), then derive
\[
\int (aL(\xi))^2=a^2\|u\|^2=2h\|u\|^2.
\]

The key checked-by-standard-API algebraic fact is:
```lean
Real.sq_sqrt (show 0 ≤ 2 * h by positivity)
```
Use the usual `MemLp` constant-multiplication operation and `integral_const_mul`. Keeping scaling separate makes the Gaussian lemma reusable.

## 3. Off-diagonal moments

Yes, your proposed proof is correct.

For distinct indices `a` and `b`, obtain
```lean
IndepFun (ξ a) (ξ b) μ
```
and push it through the continuous linear functional using `IndepFun.comp`. The required measurability comes from continuity of `L`; with an explicitly typed `L`, `L.continuous.measurable` is the standard route.

Then apply the checked
```lean
IndepFun.integral_mul_eq_mul_integral
```
and use the two zero means:
\[
\int L(\xi_a)L(\xi_b)
=\left(\int L(\xi_a)\right)\left(\int L(\xi_b)\right)=0.
\]

The `MemLp ... 2` facts provide the relevant integrability; check whether the pinned independence lemma expects integrability arguments explicitly.

For pooled chains, flatten the index:
```lean
fun a : Fin C × ℕ => ξ a.1 a.2
```
and split on equality of pairs. Reconcile pair equality with the existing table’s condition
```lean
c = c' ∧ j = k
```
using `Prod.ext_iff` and simplification.

Since `white_of_indep` already packages exactly this argument, **reuse it** rather than prove a second white-noise theorem specialised to ULA.

## 4. Extracting the spectral column

Yes: your proposed algebra is the clean route, and it avoids searching for an additional spectral-theorem API.

Let `U := orthoOf hQ` and `D := Matrix.diagonal p`. From
\[
Q=UDU^\mathsf T,\qquad U^\mathsf TU=I
\]
derive
\[
QU=UD.
\]
This uses only associativity and `orthoOf_transpose_mul`:
\[
(UDU^\mathsf T)U=UD(U^\mathsf TU)=UD.
\]

For fixed `i`, take the `(j,i)` entry of `QU = UD`. With
```lean
Matrix.mul_apply
Matrix.diagonal_apply
```
and simplification, this gives the coordinatewise eigenvector identity.

For the norm, take the `(i,i)` entry of `Uᵀ U = 1`:
\[
\sum_j U_{ji}^2=1.
\]
Use
```lean
Matrix.mul_apply
Matrix.transpose_apply
Matrix.one_apply
```
and your Euclidean inner-product/squared-norm formula. Finish with the unit norm using nonnegativity of norms, if required.

**Important typing pitfall:** the raw column
```lean
fun j => U j i
```
must be packaged as an element of `EuclideanSpace ℝ ι`. The ordinary function-space norm is not the Euclidean norm. Use the project’s existing Euclidean conversion and coordinate simp lemmas.

I would package two explicit results:

- the column is a unit vector in `EuclideanSpace ℝ ι`;
- `euclid Q` sends it to `p i • u`.

Working directly with entries is robust and avoids depending on the exact signature of `Matrix.mulVec_single`.

## 5. Remaining corrections and scope

### Separate finite-chain validity from stationary parametrisation

The finite-chain moment identity does not inherently require stability. But the interpretation
\[
\sigma^2=\frac{2h}{1-(1-hp)^2}
=\frac1{p(1-hp/2)}
\]
needs nonzero denominators and cancellation assumptions.

For the usual stationary ULA statement, assume
\[
p>0,\qquad h>0,\qquad hp<2.
\]
These give `|1 - h*p| < 1` and positive denominators. Establish their nonzeroness before `field_simp`, then finish algebraically with `ring`.

At `h = 0`, the chain and innovations are zero, and the moment theorem remains valid. But the displayed quotient identity generally **fails in Lean’s total division convention**: its left side is `0 / 0 = 0`, while its right side is `1 / p`.

### State the conclusion as an expectation

The exact conclusion is:
\[
\mathbb E[\text{pooled sampled variance}]
=\text{finite-chain AR(1) prediction}.
\]
The realised sampled variance is a random variable, not pathwise equal to that deterministic prediction.

### A nearby extension, but not a separate target

The arbitrary-vector Gaussian lemma naturally gives projected innovation variance `2*h*‖u‖²`; the unit case should be a corollary. A two-vector version also gives innovation covariance `2*h*inner ℝ u v`.

That is useful reusable infrastructure, but I would not expand this step into concentration bounds or independence of complete eigendirection processes. The deterministic bridge plus pooled expected-variance corollary already closes the gap in E1/E2/E4.

**Vote: G1–G4 as one “actual ULA → pooled eigendirection AR(1) expected variance” cluster, built around a deterministic projection lemma and the existing moment-table theorem.**