## 1. Representation of the quadratic form

Use

```lean
def qform (H : Matrix (Fin d) (Fin d) ℝ) (x : EuclidD d) : ℝ :=
  ⟪x, Matrix.toEuclideanCLM H x⟫_ℝ

def K (H : Matrix (Fin d) (Fin d) ℝ) (x : EuclidD d) : ℝ :=
  Real.exp (-qform H x / 2)
```

as the public representation.

This is the best interface for both sides:

* Whitening naturally says
  ```lean
  qform H x = ‖Matrix.toEuclideanCLM (CFC.sqrt H) x‖ ^ 2.
  ```
* The Taylor/Hessian consumer naturally produces a continuous bilinear form, which can be converted locally to an operator \(H\) and then written as `⟪x, H x⟫`.
* Norm bounds and positivity use the inner-product/CLM API directly.
* Coordinates should only appear in the final statements about `i`, `j`.

I would not expose `x ⬝ᵥ H *ᵥ x` in the main statements. It is useful as an internal bridge, but it creates coercion friction because `EuclideanSpace ℝ (Fin d)` is not definitionally just `Fin d → ℝ`.

Likewise, `Matrix.toBilin` is useful when converting the Hessian, but it is less convenient for whitening and operator norm estimates.

### Conversion lemmas

Make two small project-local simp lemmas rather than depending heavily on exact EuclideanSpace implementation lemmas:

```lean
lemma qform_eq_dotProduct_mulVec
    (H : Matrix (Fin d) (Fin d) ℝ) (x : EuclidD d) :
    qform H x =
      dotProduct (fun i ↦ x i) (H *ᵥ fun i ↦ x i) := by
  simp [qform, Matrix.toEuclideanCLM, dotProduct]
```

The exact unfolding simp set may only need

```lean
simp [qform, Matrix.toEuclideanCLM, Matrix.mulVec, dotProduct]
```

in the pinned version.

For products, the useful matrix lemma is:

```lean
Matrix.mulVec_mulVec
```

which rewrites

```lean
(A * B) *ᵥ x = A *ᵥ (B *ᵥ x).
```

For symmetry/transpose manipulations, use the matrix’s `IsHermitian`/symmetric fact and prove a local lemma of the form

```lean
lemma inner_toEuclideanCLM
    (hA : A.IsHermitian) (x y : EuclidD d) :
    ⟪x, Matrix.toEuclideanCLM A y⟫_ℝ =
      ⟪Matrix.toEuclideanCLM A x, y⟫_ℝ := ...
```

Then the central bridge is:

```lean
lemma qform_eq_norm_sqrt
    (hH : H.PosDef) (x : EuclidD d) :
    qform H x =
      ‖Matrix.toEuclideanCLM (CFC.sqrt H) x‖ ^ 2 := ...
```

Its proof uses:

* `hH.posSemidef`,
* the square-root multiplication theorem for positive semidefinite matrices,
* `(hH.posDef_sqrt).isHermitian`,
* `Matrix.mulVec_mulVec`.

The exact name of the `sqrt H * sqrt H = H` theorem has moved more often than the surrounding API; use the theorem exposed from `hH.posSemidef` in the pinned `Analysis/Matrix/Order.lean` and hide it behind this local lemma.

### Hessian conversion

If `D²L(0)` arrives as a continuous bilinear/multilinear map, define the matrix by basis evaluation, with the order chosen to match `mulVec`:

```lean
H i j := D2L (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
```

and prove once:

```lean
D2L x x = ⟪x, Matrix.toEuclideanCLM H x⟫_ℝ
```

by expanding in the orthonormal coordinate basis. Thus the asymptotic/Taylor stage can remain in the natural `iteratedFDeriv` representation until its final handoff to H2.

---

## 2. Clean whitening sequence

Let

```lean
abbrev E := EuclidD d

let S : Matrix (Fin d) (Fin d) ℝ := CFC.sqrt H
let B : E →L[ℝ] E := Matrix.toEuclideanCLM S
let Blin : E →ₗ[ℝ] E := B.toLinearMap
```

Do **not** start with `CFC.sqrt H⁻¹`. Use \(B=\sqrt H\), make the substitution \(y=Bx\), and only then use \(B^{-1}\) on polynomial factors. This avoids proving that `sqrt H⁻¹` is the inverse of `sqrt H`.

### Step A: invertibility

From

```lean
hS : S.PosDef := hH.posDef_sqrt
```

obtain injectivity of `Blin`, hence

```lean
have hdet : LinearMap.det Blin ≠ 0 := ...
```

The route is either the finite-dimensional determinant/injectivity equivalence or a direct contradiction from positive-definiteness:

```lean
B x = 0
→ ⟪x, B x⟫ = 0
→ x = 0
```

using `hS`.

I recommend retaining

```lean
LinearMap.det Blin
```

throughout the proof. There is no need to identify it with `Matrix.det S`: the determinant factor cancels from M1/M2, and for Z only its nonzeroness matters.

If you really need the transport, the underlying coordinate lemma is in the `Matrix.toLin` family, commonly `Matrix.det_toLin`; an extra coercion equality is then needed because `toEuclideanCLM` is a CLM on `EuclideanSpace`. That transport buys nothing here.

Define

```lean
let jac : ℝ := |LinearMap.det Blin|⁻¹
```

and record

```lean
have hjac : 0 < jac := inv_pos.mpr (abs_pos.mpr hdet)
```

### Step B: measure-level change of variables

Apply exactly

```lean
map_linearMap_addHaar_eq_smul_addHaar hdet
```

to `Blin`:

```lean
Measure.map Blin volume = jac • volume
```

up to the local identification of Euclidean `volume` with the relevant additive Haar measure.

The orientation is:

\[
\int_E \varphi(Bx)\,dx
  = |\det B|^{-1}\int_E \varphi(y)\,dy.
\]

Indeed,

```lean
∫ y, φ y ∂Measure.map Blin volume = ∫ x, φ (B x) ∂volume
```

and the map measure is `jac • volume`.

Package this immediately as a local change-of-variables lemma, preferably in both integral and `lintegral` forms:

```lean
lemma integral_comp_B
    (hφ : Integrable φ) :
    ∫ x, φ (B x) = jac * ∫ y, φ y := ...

lemma lintegral_comp_B
    (hφ : AEMeasurable φ) :
    ∫⁻ x, φ (B x) = ENNReal.ofReal jac * ∫⁻ y, φ y := ...
```

The `lintegral` version is particularly useful for proving integrability without circularly assuming it.

### Step C: quadratic transport

First prove the forward identity, not an inverse identity:

```lean
have hq (x : E) :
    qform H x = ‖B x‖ ^ 2 := by
  ...
```

The calculation is

\[
\begin{aligned}
\langle x,Hx\rangle
 &= \langle x,B(Bx)\rangle \\
 &= \langle Bx,Bx\rangle \\
 &= \|Bx\|^2.
\end{aligned}
\]

The ingredients are:

1. `S * S = H`;
2. `Matrix.mulVec_mulVec`;
3. self-adjointness of `B`, obtained from
   ```lean
   (hH.posDef_sqrt).isHermitian
   ```
   and the local `inner_toEuclideanCLM` lemma.

Consequently,

```lean
K H x = Real.exp (-‖B x‖ ^ 2 / 2)
```

and if

```lean
k₀ y := Real.exp (-‖y‖ ^ 2 / 2)
```

then

```lean
K H x = k₀ (B x).
```

This is considerably easier than directly proving

```lean
⟪B⁻¹ y, H (B⁻¹ y)⟫ = ‖y‖².
```

### Step D: normalization

Let

```lean
Z₀ := ∫ y : E, k₀ y
```

Using the Gaussian integral theorem with `b = 1 / 2`, obtain its explicit value, integrability, and positivity.

Then:

```lean
∫ x, K H x = jac * Z₀
```

so positivity follows from `hjac` and `0 < Z₀`.

Be careful that, in Lean, positivity of a Bochner integral does not itself certify integrability: the Bochner integral is defined to be zero for nonintegrable functions. Prove `Integrable (K H)` separately, preferably before the positivity theorem.

### Step E: moments

Let `C := B⁻¹`, preferably as a continuous linear equivalence or inverse CLM. Under \(y=Bx\),

\[
x = C y.
\]

Thus

\[
\int x_i K_H(x)\,dx
 = \mathrm{jac}\int (Cy)_i k_0(y)\,dy.
\]

Linearity plus the standard first-moment theorem gives zero.

For the second moment,

\[
\int x_i x_j K_H(x)\,dx
 = \mathrm{jac}\int (Cy)_i(Cy)_j k_0(y)\,dy.
\]

If the standard package exposes coordinate moments,

\[
\int y_a y_b k_0(y)\,dy = Z_0\,\delta_{ab},
\]

then expansion gives

\[
\int (Cy)_i(Cy)_j k_0(y)\,dy
 = Z_0 (CC^\mathsf{T})_{ij}.
\]

Since \(B\) is symmetric, so is \(C\), and

\[
CC^\mathsf{T}=C^2=B^{-2}=H^{-1}.
\]

Hence

```lean
∫ x, x i * x j * K H x = jac * Z₀ * H⁻¹ i j
```

and division by

```lean
∫ x, K H x = jac * Z₀
```

cancels both factors.

A cleaner standard-Gaussian API is coordinate-free:

```lean
∫ y, ℓ y * k₀ y = 0

∫ y, ℓ y * m y * k₀ y
  = Z₀ * ⟪riesz ℓ, riesz m⟫
```

for continuous linear functionals `ℓ`, `m`. Then use

```lean
ℓ y := (C y) i
m y := (C y) j
```

and only convert the resulting covariance operator to `H⁻¹` at the end. This avoids a large finite-sum calculation in the whitening layer.

### Step F: all polynomial moments

From boundedness of `C`,

\[
\|Cy\| \le \|C\|\,\|y\|.
\]

Therefore

\[
(1+\|Cy\|^n)k_0(y)
 \le (1+\|C\|^n\|y\|^n)k_0(y).
\]

So the all-\(n\) standard integrability theorem transfers directly through the same change of variables.

For this part, use `lintegral`/`HasFiniteIntegral` first, because it avoids requiring integrability in the change-of-variables theorem you are using to prove integrability.

---

## Standard Gaussian proof and the Pi bridge

For the standard package, use:

```lean
PiLp.volume_preserving_ofLp
```

to move between

```lean
EuclideanSpace ℝ (Fin d)
```

and

```lean
Fin d → ℝ.
```

For a pure product integrand, the finite-product theorem to look for in the pinned tree is the `integral_fintype_prod_eq_prod` family. If its hypotheses or measure normalization are awkward, I would not spend time forcing it. A robust alternative is induction on the finite index set using binary

```lean
MeasureTheory.integral_prod
```

and Tonelli/Fubini, together with the `ofLp` measure-preserving bridge.

In particular, prove standard results in the stronger form:

```lean
std_integrable_poly :
  ∀ n, Integrable (fun y : E ↦ (1 + ‖y‖ ^ n) * k₀ y)

std_first_linear :
  ∀ ℓ : E →L[ℝ] ℝ, ∫ y, ℓ y * k₀ y = 0

std_second_linear :
  ∀ ℓ m : E →L[ℝ] ℝ,
    ∫ y, ℓ y * m y * k₀ y
      = Z₀ * ⟪riesz ℓ, riesz m⟫
```

even if they are proved internally from coordinate Fubini. This is the right abstraction boundary for whitening.

---

## 3. Tide staging

Use **two tides**.

### Tide H2a: standard isotropic Gaussian

Prove once on every `EuclideanSpace ℝ (Fin d)`:

1. `k₀` measurable and integrable;
2. explicit `Z₀` and `0 < Z₀`;
3. all polynomial moments integrable;
4. first moments vanish;
5. normalized covariance is the identity;
6. ideally the first/second statements for arbitrary continuous linear functionals.

This tide contains all Pi/Fubini and one-dimensional Gaussian work.

### Tide H2b: whitening

Assuming `hH : H.PosDef`:

1. define `B = toEuclideanCLM (CFC.sqrt H)`;
2. prove `B` invertible;
3. prove `qform H x = ‖B x‖²`;
4. instantiate the Haar change-of-variables theorem;
5. transfer integrability, Z, M1, and M2 from H2a;
6. cancel the common Jacobian/normalization factors.

This tide should contain no one-dimensional integration and ideally no Fubini.

### Hardest step

The hardest mathematical/API step is the **standard all-polynomial integrability plus finite-product Fubini package**, especially the identification between:

* EuclideanSpace volume,
* PiLp/function-space volume,
* a finite product of one-dimensional Lebesgue measures.

Once that package exists, whitening is mostly linear algebra and measure transport.

### Most likely API mismatch

The most likely mismatch is not the Gaussian formula itself but the combination of:

1. `EuclideanSpace`/`PiLp` coercions,
2. `toEuclideanCLM` versus its underlying `LinearMap`,
3. matrix transpose/adjoint conventions,
4. the exact measure used by `map_linearMap_addHaar_eq_smul_addHaar`.

Avoid one major source of friction by never transporting the determinant back to `Matrix.det (CFC.sqrt H)`. Keep `LinearMap.det B.toLinearMap` as an opaque nonzero Jacobian; it cancels in M2 and only positivity is needed for Z.