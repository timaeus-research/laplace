Short version:

- **Yes, Fubini + a custom 1D full-line FTC lemma is the right Lean route.**
- **Do not start with an operator-valued second-moment map.** Prove a **columnwise vector identity** first.
- **Do not use adjoints/Fréchet derivative for `quadForm` here.** Prove a **1D slice derivative** by expanding `quadForm H (u + h • eᵢ)`.

That is the lowest-friction path in Mathlib.

---

## 1. Cleanest IBP framework on `ι → ℝ`

### Recommendation
Use:

1. a **coordinate-splitting equivalence**
   \[
   (ι \to \mathbb R) \simeq ((\{k // k \neq i\}\to\mathbb R)\times \mathbb R),
   \]
2. then `MeasureTheory.integral_prod` / Fubini,
3. then a **bespoke 1D lemma**
   \[
   \int_{\mathbb R} f'(x)\,dx = 0
   \]
   under `Tendsto f atTop (𝓝 0)`, `Tendsto f atBot (𝓝 0)`, and integrability of `deriv f`.

I would **not** look for a direct multivariate FTC theorem on Pi-space; in practice that’s more painful than helpful.

### Mathlib infrastructure to use

The pieces you’ll likely want are:

- **Fubini/product integral**
  - `MeasureTheory.integral_prod`
  - `MeasureTheory.Integrable.prod_left_ae`
  - `MeasureTheory.Integrable.prod_right_ae`

- **1D FTC on intervals**
  - one of
    - `intervalIntegral.integral_deriv_eq_sub`
    - `intervalIntegral.integral_deriv_eq_sub'`
  depending on the hypotheses you can supply.

- **Change-of-coordinates / split off one coordinate**
  - Search first for something like:
    - `Equiv.piSplitAt`
    - `Equiv.piEquivPiSubtypeProd`
    - `MeasurableEquiv.piCongrLeft`
  - If none is convenient, **just define your own `splitAt i`**. That is completely reasonable here.

### Important caveat
A `MeasurableEquiv` is **not automatically measure-preserving** for arbitrary measures. So if you split coordinates via an equivalence, you either need:

- an existing theorem that this particular equivalence preserves `volume`, or
- a small lemma proving the pushforward of `volume` is the product `volume`.

That is boilerplate, but it’s the only slightly annoying measure-theoretic part.

### My actual Lean recommendation
Write your own:

```lean
def splitAt (i : ι) : (ι → ℝ) ≃ (({k // k ≠ i} → ℝ) × ℝ)
def unsplitAt ...
```

and prove once that it preserves `volume`. After that, the file becomes much easier to read.

---

## 2. Best statement of `M = Z · H⁻¹`

### Strong recommendation: use a **column-vector theorem**
This is cleaner than both your (a) and (b) as a first target.

Define:

```lean
noncomputable def gaussianWeight (H) (u : ι → ℝ) : ℝ :=
  Real.exp (-(1/2 : ℝ) * quadForm H u)

noncomputable def gaussianZ (H) : ℝ :=
  ∫ u : ι → ℝ, gaussianWeight H u

noncomputable def momentColumn (H) (j : ι) : ι → ℝ :=
  fun k => ∫ u : ι → ℝ, u k * u j * gaussianWeight H u
```

Then prove:

```lean
theorem gaussian_ibp_column
    (j : ι) :
    H (momentColumn H j) = (gaussianZ H) • Pi.single j (1 : ℝ)
```

This is exactly the matrix equation \(H M = Z I\), but without building an operator/matrix first.

Then derive the inverse corollary:

```lean
theorem momentColumn_eq_zmul_inverse
    (Σ : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hΣ : H.comp Σ = ContinuousLinearMap.id ℝ _)
    (hH_inj : Function.Injective H)
    (j : ι) :
    momentColumn H j = (gaussianZ H) • Σ (Pi.single j (1 : ℝ))
```

and finally evaluate at coordinate `i`:

```lean
corollary gaussian_second_moment_eq_inverse_entry
    (i j : ι) :
    (∫ u, u i * u j * gaussianWeight H u)
      = (gaussianZ H) * (Σ (Pi.single j (1 : ℝ))) i
```

### Why this is better
- avoids premature construction of an operator `M_op`,
- avoids row/column indexing confusion,
- matches the actual IBP proof,
- still gives the clean downstream inverse formula.

If you later want the operator equation, derive it from the columnwise theorem.

---

## 3. Differentiating `quadForm H u` in coordinate `i`

### Recommendation
Do **not** use the adjoint API here.

The Lean-friendly proof is:

1. define `e i := Pi.single i (1 : ℝ)`,
2. prove the algebraic increment formula
   \[
   \operatorname{quadForm} H (u + h e_i)
   = \operatorname{quadForm} H u + 2 h (H u)_i + h^2 (H e_i)_i
   \]
   using symmetry,
3. conclude the slice derivative.

This is much easier than a full `HasFDerivAt` proof.

### Key helper lemmas you want

#### Basis expansion
```lean
lemma eq_sum_stdBasis (u : ι → ℝ) :
    u = ∑ k, u k • Pi.single k (1 : ℝ)
```

#### Column expansion of `H`
```lean
lemma H_apply_eq_sum (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (u : ι → ℝ) (i : ι) :
    (H u) i = ∑ k, ((H (Pi.single k (1 : ℝ))) i) * u k
```

#### Coordinate symmetry
From your inner-product symmetry hypothesis, immediately derive:

```lean
lemma H_coord_symm (i k : ι) :
    (H (Pi.single k (1 : ℝ))) i = (H (Pi.single i (1 : ℝ))) k
```

Then stop using inner products in the proof.

#### Quadratic increment
```lean
lemma quadForm_add_smul_stdBasis
    (i : ι) (u : ι → ℝ) (h : ℝ) :
    quadForm H (u + h • Pi.single i (1 : ℝ)) =
      quadForm H u + 2 * h * (H u) i + h^2 * (H (Pi.single i (1 : ℝ))) i
```

This is the crucial calculus input.

### Slice derivative
For fixed “other coordinates” `y`, set
```lean
u x := unsplitAt i (y, x)
```
or equivalently `Function.update u0 i x`. Then prove:

```lean
HasDerivAt (fun x => (1/2 : ℝ) * quadForm H (u x)) ((H (u x0)) i) x0
```

and hence

```lean
HasDerivAt (fun x => gaussianWeight H (u x))
  (-(H (u x0)) i * gaussianWeight H (u x0)) x0
```

Then product rule gives the derivative of
`x ↦ (u x j) * gaussianWeight H (u x)`.

---

## 4. `Pi.single` vs basis notation

Use `Pi.single i 1` underneath, but define a local abbreviation/notational wrapper.

For example:

```lean
local notation "e[" i "]" => (Pi.single i (1 : ℝ))
```

or

```lean
local def stdBasis (i : ι) : ι → ℝ := Pi.single i (1 : ℝ)
```

This is worth it. It makes the quadratic expansion much more readable.

---

## 5. Sanity check: what’s missing from the strategy?

The **main missing piece is analytic, not algebraic**.

### Very important
`positive diagonal` is **not enough** for the full theorem unless you separately assume the needed integrability/Fubini/boundary hypotheses.

It is enough to see that each **slice in `x_i`** has Gaussian decay in `x_i`, because
\[
(H e_i)_i > 0.
\]
But it does **not** by itself give global integrability in the remaining coordinates.

So in Lean, you should choose one of two approaches:

### Option A: explicit analytic hypotheses
This is the easiest formalization route.

State the core IBP theorem with assumptions like:

- `Integrable (gaussianWeight H)`
- `Integrable (fun u => u j * (H u) i * gaussianWeight H u)`
- boundary vanishing on slices
- enough Fubini hypotheses

Then prove the identity.

This aligns well with your project’s “explicit estimates” philosophy.

### Option B: add a coercivity hypothesis
Instead of deriving coercivity from positive-definite inside this file, assume:

```lean
(h_coercive : ∃ c > 0, ∀ u, c * ‖u‖^2 ≤ quadForm H u)
```

This is much more Lean-friendly than proving coercivity from positive-definite via compactness of the sphere.

Then you can derive Gaussian integrability and boundary vanishing from that.

### My advice
For Phase 4, I would **not** try to prove all decay/integrability facts from `hH_pos` alone in the same file. Split it:

1. `GaussianIBPCore`: IBP under explicit integrability/slice hypotheses.
2. `GaussianDecay` or later helper lemmas: coercivity/positivity ⇒ those hypotheses.

That keeps the proof modular and much less brittle.

---

## Suggested proof structure

Here is the structure I would aim for.

### Step 0: definitions
```lean
gaussianWeight
gaussianZ
momentColumn
```

### Step 1: linear algebra helpers
- `eq_sum_stdBasis`
- `H_apply_eq_sum`
- `H_coord_symm`
- `quadForm_add_smul_stdBasis`

### Step 2: 1D full-line derivative lemma
A reusable theorem of the form:

```lean
lemma integral_deriv_eq_zero_of_tendsto
    {f : ℝ → ℝ}
    (h_deriv_int : Integrable (deriv f))
    (h_cont : Continuous f)
    (h_diff : Differentiable ℝ f)
    (h_top : Tendsto f atTop (𝓝 0))
    (h_bot : Tendsto f atBot (𝓝 0)) :
    ∫ x, deriv f x = 0
```

proved from interval FTC on `(-R, R)` and `R → ∞`.

### Step 3: slice derivative formula
For fixed `i j` and fixed outer variable `y`, define
```lean
f_y(x) := (u_yx j) * gaussianWeight H (u_yx)
```
where `u_yx := unsplitAt i (y, x)`.

Prove:
```lean
deriv f_y x =
  (if i = j then 1 else 0) * gaussianWeight H (u_yx)
  - (u_yx j) * (H (u_yx)) i * gaussianWeight H (u_yx)
```

### Step 4: apply the 1D lemma
Get
```lean
0 = ∫ x,
      (if i = j then 1 else 0) * gaussianWeight H (u_yx)
      - (u_yx j) * (H (u_yx)) i * gaussianWeight H (u_yx)
```

### Step 5: integrate in the outer variables
Use Fubini to deduce
```lean
∫ u, (u j) * (H u) i * gaussianWeight H u
  = (if i = j then 1 else 0) * gaussianZ H
```

### Step 6: rewrite `(H u) i` as a finite sum
Using
```lean
(H u) i = ∑ k, H_ik * u k
```
deduce
```lean
∑ k, H_ik * (∫ u, u k * u j * gaussianWeight H u)
  = (if i = j then 1 else 0) * gaussianZ H
```

That is exactly
```lean
(H (momentColumn H j)) i = ((gaussianZ H) • e[j]) i
```

### Step 7: invert using `Σ`
If `H.comp Σ = id` and `H` is injective, conclude
```lean
momentColumn H j = (gaussianZ H) • Σ e[j]
```

Injectivity from positive-definite is easy and worth isolating as a separate lemma.

---

## Practical recommendation on theorem packaging

I would export **three** theorems, in this order:

### 1. Core scalar IBP identity
```lean
theorem gaussian_ibp_coord
    (i j : ι) :
    ∫ u, u j * (H u) i * gaussianWeight H u
      = (if i = j then 1 else 0) * gaussianZ H
```

### 2. Column-vector form
```lean
theorem gaussian_ibp_column
    (j : ι) :
    H (momentColumn H j) = (gaussianZ H) • e[j]
```

### 3. Inverse-entry corollary
```lean
theorem gaussian_second_moment_eq_inverse_entry
    (Σ : ...)
    ...
    (i j : ι) :
    ∫ u, u i * u j * gaussianWeight H u
      = gaussianZ H * (Σ e[j]) i
```

That gives you both proof ergonomics and downstream usability.

---

## LOC estimate

My estimate:

- **Core IBP theorem under explicit analytic hypotheses**: about **150–250 LOC**
- **If you also derive integrability/boundary decay from positive-definite/coercive assumptions in the same file**: more like **300–500 LOC**

So your “similar to Phase 2” guess is right **only if** you don’t try to force all Gaussian decay from `hH_pos` in one shot.

---

## Bottom line

If I were writing `GaussianIBP.lean`, I would do:

1. **Use a custom split-at-coordinate equivalence + Fubini.**
2. **Prove a bespoke 1D `∫ deriv = 0` helper.**
3. **Work with `momentColumn H j`, not an operator-valued `M_op`.**
4. **Differentiate `quadForm` by the quadratic increment identity, not by adjoints.**
5. **Assume explicit integrability/coercivity hypotheses unless you really want a separate Gaussian-decay file.**

If you want, I can next sketch the actual Lean declarations/lemma statements in file order, with suggested names and a plausible proof script outline.