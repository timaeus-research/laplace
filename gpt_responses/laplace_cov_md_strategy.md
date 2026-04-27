Short answer: **do a hybrid of (A) and (C)**.

- Use **(A)** for the real analytic content: shift to `w* = 0`, rescale by `x = u / √t`, Taylor-expand `L, φ, ψ`, dominate by a Gaussian, and get the `O(t⁻²)` remainder.
- Use **(C)** only for the Gaussian moment identification:
  \[
  \frac{\int u_i u_j e^{-\frac12 u^\top H u}\,du}{\int e^{-\frac12 u^\top H u}\,du}
  = (H^{-1})_{ij}.
  \]
  That avoids diagonalisation, determinants, and most of the multivariate Gaussian-library question.

I would **not** make (B) the main route. In Lean, orthogonal diagonalisation + change of variables + determinant bookkeeping is exactly the sort of overhead that balloons.

---

## Executive recommendation

### Best route
Prove a theorem of the form:

> If `L` has a nondegenerate minimum at `w*`, `φ(w*) = ψ(w*) = 0`, and you have:
> - a quadratic leading term `½ ⟪z, H z⟫`,
> - cubic remainder for `L`,
> - quadratic remainder for `φ, ψ`,
> - global coercive domination / localization,
>
> then
> \[
> \mathrm{Cov}_t[\phi,\psi]
> = \frac1t \, D\phi(w*) \circ H^{-1} \circ (D\psi(w*))^\sharp + O(t^{-2}).
> \]

### Proof architecture
1. **Normalize**: shift so `w* = 0`, subtract `L(0)`, so `L 0 = 0`.
2. **Rescale only by `√t`**, not by `H^{1/2}`:
   \[
   t L(u/\sqrt t)=\frac12 \langle u, H u\rangle + r_t(u),\qquad r_t(u)=O(\|u\|^3/\sqrt t).
   \]
3. Expand observables:
   \[
   \phi(u/\sqrt t)=t^{-1/2}\ell_\phi(u)+O(t^{-1}\|u\|^2),\quad
   \psi(u/\sqrt t)=t^{-1/2}\ell_\psi(u)+O(t^{-1}\|u\|^2).
   \]
4. Use even/odd symmetry to kill the `t^{-3/2}` terms.
5. Reduce the leading term to anisotropic Gaussian second moments.
6. Identify those moments with `H⁻¹` using a **coordinatewise IBP / Stein identity**.

That route is the closest analogue of what already worked in 1D, but avoids the nastiest multivariate linear-algebra overhead.

---

# Why this hybrid beats pure A/B/C

## Why not pure (A)?
Pure (A) usually tempts you into proving the full multivariate Gaussian normalization:
\[
\int e^{-\frac12 u^\top H u} du = (2\pi)^{d/2} (\det H)^{-1/2},
\]
and then explicit moment formulas. For `lem:laplace_cov`, **you do not need that**. The partition-function constant cancels in the covariance ratio.

## Why not pure (C)?
Pure Stein/IBP doesn’t remove the need for:
- local Taylor expansion,
- tail domination,
- `O(t⁻²)` remainder control,
- oddness cancellation.

So it won’t save the hard part. It’s best used only to identify the Gaussian covariance matrix.

## Why not (B)?
Diagonalisation/rotation is elegant on paper, but in Lean it means:
- spectral theorem setup,
- orthogonal matrix infrastructure,
- change-of-variables under a linear equivalence,
- determinant absolute values,
- normalization constants.

That’s a lot of API fighting for no gain on this theorem.

---

# Concrete Lean strategy I’d recommend

## Phase 1: state a theorem under explicit local-expansion hypotheses
Do **not** start by formalizing “Hessian at a nondegenerate critical point” as the theorem’s main input.

Instead, prove a theorem under hypotheses like:

- `L0 : E → ℝ`, `φ0 ψ0 : E → ℝ`, with `E := EuclideanSpace ℝ ι`
- `L0 0 = 0`, `φ0 0 = 0`, `ψ0 0 = 0`
- linear maps `dφ dψ : E →L[ℝ] ℝ`
- symmetric positive-definite operator `H : E →L[ℝ] E`
- local estimates:
  - `|L0 z - (1/2) * ⟪z, H z⟫| ≤ C * ‖z‖^3` for `‖z‖ ≤ r`
  - `|φ0 z - dφ z| ≤ Cφ * ‖z‖^2`
  - `|ψ0 z - dψ z| ≤ Cψ * ‖z‖^2`
- global domination/localization:
  - either global coercivity,
  - or “outside a ball, `L0 ≥ η > 0`”.

Then later prove a corollary deriving these hypotheses from `ContDiff` + nondegenerate minimum.

This is a big simplifier.

---

## Phase 2: build multivariate Gaussian domination/integrability
You’ll want lemmas like:

- `Integrable (fun u : E => ‖u‖^k * Real.exp (-c * ‖u‖^2))`
- same with coordinate monomials `u i`, `u i * u j`, etc.
- odd integrals vanish against even Gaussian:
  - `∫ u_i * exp(-Q u) = 0`
  - `∫ cubic_odd(u) * exp(-Q u) = 0`

For a first pass, I’d target `E = EuclideanSpace ℝ (Fin d)` rather than an arbitrary finite-dimensional inner product space.

---

## Phase 3: prove the Gaussian covariance identity by IBP
This is the key “Stein” piece.

Let
\[
Q(u)=\frac12 \langle u, H u\rangle.
\]
For coordinates `i,j`, prove:
\[
0 = \int \partial_i\!\big(u_j e^{-Q(u)}\big)\,du
  = \delta_{ij}\int e^{-Q}
    - \sum_k H_{ik}\int u_j u_k e^{-Q}.
\]
Hence the moment matrix `M` satisfies
\[
H M = Z I,\qquad Z = \int e^{-Q},
\]
so
\[
M = Z H^{-1}.
\]

This is perfect for Lean because:
- no determinant,
- no diagonalisation,
- later generalizes to 4th moments by repeating the same trick.

This is exactly the infrastructure you want if `lem:laplace_cov2` is coming later.

---

## Phase 4: assemble covariance asymptotic directly
Don’t first formalize every separate mean asymptotic.

For `φ(w*) = ψ(w*) = 0`, you can go more directly:

- numerator:
  \[
  \int \phi \psi \, e^{-tL}
  = t^{-d/2-1}\Big(M_{\phi,\psi} + O(t^{-1})\Big)
  \]
  after oddness kills the `t^{-1/2}` correction.
- partition function:
  \[
  Z_t = t^{-d/2}(Z_H + O(t^{-1}))
  \]
- means:
  \[
  \langle \phi\rangle_t = O(t^{-1}),\quad
  \langle \psi\rangle_t = O(t^{-1}),
  \]
  so their product is `O(t⁻²)` automatically.

That gives the covariance theorem with less bureaucracy than the 1D path had.

---

# Answers to your six sub-questions

## 1. Mathlib coverage of multivariate Gaussian moments
My advice: **plan as if Mathlib does not already have the exact theorem you want**.

I would not expect a turnkey lemma of the form
```lean
∫ x, x i * x j * exp (-(1/2) * xᵀ A x)
  = ((2 * π)^(d/2) / sqrt (det A)) * (A⁻¹ i j)
```
ready for direct use.

There is Gaussian/distribution infrastructure in Mathlib, but historically the pain point is not “Gaussian exists”, it’s:
- exact Lebesgue-density integral formulas,
- matrix-parameterized moments,
- determinant-normalization lemmas in the shape you want.

So for this project: **don’t depend on that existing**.

Instead, build only:
- oddness under even density,
- second-moment identity via IBP,
- later fourth moments via repeated IBP.

That is likely both shorter and more robust.

---

## 2. `Σ = H⁻¹` in Lean
I would separate **internal proof representation** from **final theorem presentation**.

### Internally
Use either:
- a continuous linear map `H : E →L[ℝ] E` plus an explicit inverse witness `Σ : E →L[ℝ] E` with
  ```lean
  H.comp Σ = ContinuousLinearMap.id ℝ E
  Σ.comp H = ContinuousLinearMap.id ℝ E
  ```
  or
- a continuous linear equivalence `A : E ≃L[ℝ] E` representing the Hessian operator.

This is easier than making `Matrix.inv` the core object in the proof.

### Externally
For the user-facing theorem on `EuclideanSpace ℝ (Fin d)`, you can package `H` as a matrix and define `Σ := H⁻¹`.

### For gradients
I’d define your own helper:
```lean
noncomputable def gradVec (f : E → ℝ) (x : E) : E := ...
```
using the Riesz identification between `E →L[ℝ] ℝ` and `E`.

That makes the final statement readable:
```lean
(1 / t) * inner (gradVec φ w*) (Σ (gradVec ψ w*))
```
instead of dragging dual-space coercions through every theorem.

---

## 3. Coercivity hypothesis
Yes: the right abstract hypothesis is **not** a polynomial class, but an analytic one.

For a first theorem, I’d take something like:
\[
\exists c,C,\ c>0 \ \wedge\ \forall x,\ c\|x-w^*\|^2 - C \le L(x)-L(w^*).
\]

After shifting to `w*=0`, `L(0)=0`, that becomes a clean global lower bound.

### Even better long-term split
Have two theorem layers:

1. **Core theorem** under either:
   - global coercivity, or
   - a local minimum plus a positive gap outside a neighborhood.

2. **Corollaries** for polynomial/coercive classes.

That will scale better than baking “quartic polynomial” into the multivariate statement.

---

## 4. Wick contractions / Isserlis
I would assume **no useful turnkey Wick/Isserlis theorem** exists in Mathlib for your exact use.

But for your purposes, that’s fine.

For `lem:laplace_cov2`, don’t wait for a Wick library. Prove bespoke Gaussian moment lemmas by repeated IBP:
- second moments: one IBP,
- fourth moments: two IBPs.

That yields the pairing formula you need, without multilinear-map abstraction.

So my recommendation is:

- **Do not** build a general Wick theorem first.
- Build a small file of Gaussian moment identities tailored to:
  - 2nd moments now,
  - 4th moments later.

That is the Lean-efficient path.

---

## 5. Cost estimate
Your estimate is **slightly optimistic**, depending on theorem scope.

### If you prove:
- on `EuclideanSpace ℝ (Fin d)`,
- under explicit local expansion hypotheses,
- with global coercivity,
- and you avoid determinant normalization / spectral theorem,

then **1500–2500 LOC** is plausible.

### If you also insist on:
- deriving everything from `ContDiff`/Hessian automatically,
- polished coordinate-free statement,
- matrix/operator interop,
- general localization theorem,

then I’d budget more like **2500–4000 LOC** and **3–7 days**, not 1–2.

The main risk isn’t the math; it’s:
- finite-dimensional analysis API,
- Fubini/integrability lemmas on `EuclideanSpace`,
- derivative/Hessian packaging.

---

## 6. Verifier doc first?
Yes—**I would do a minimal verifier doc now or in parallel**.

Reason:
- it’s cheap,
- immediately improves reader trust,
- doesn’t block the multivariate proof,
- and the multivariate project is large enough that it’s good to land something communicative first.

My preference:
- spend **2–3 hours** on a one-page verifier guide,
- then start the multivariate development.

That feels like the right balance.

---

# What I would actually build next

## Recommended file sequence
Something like:

1. `Laplace/Multi/Basic.lean`
   - `E := EuclideanSpace ℝ (Fin d)`
   - multivariate `partitionFunction`, `gibbsExpectation`, `gibbsCov`

2. `Laplace/Multi/GaussianDomination.lean`
   - integrability of `‖u‖^k exp(-c‖u‖²)`
   - oddness/evenness lemmas

3. `Laplace/Multi/QuadraticApprox.lean`
   - local cubic remainder for `L`
   - linear observable remainder bounds
   - rescaled perturbation bounds

4. `Laplace/Multi/GaussianIBP.lean`
   - anisotropic Gaussian second moment = inverse Hessian
   - later fourth moments

5. `Laplace/Multi/Covariance.lean`
   - main `lem:laplace_cov`

6. later `Laplace/Multi/Covariance2.lean`
   - `lem:laplace_cov2`

---

# Bottom line

## My strategic recommendation
- **Use (A)+(C)**.
- More specifically:
  - **scalar rescaling + local Taylor + Gaussian domination** for the asymptotic machinery,
  - **coordinatewise Gaussian IBP** for the `H⁻¹` coefficient.
- **Avoid (B)** as the main plan.

## Why this is the right Lean route
It minimizes dependence on:
- spectral theorem,
- determinant formulas,
- multivariate Gaussian normalization libraries,
- heavy matrix change-of-variables infrastructure.

And it sets you up cleanly for `lem:laplace_cov2`.

If you want, I can sketch the exact normalized theorem statement I’d recommend writing first in Lean, with hypotheses chosen to minimize API pain.