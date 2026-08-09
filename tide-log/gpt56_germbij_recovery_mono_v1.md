## 1. Hypotheses for A

The hypotheses are sufficient.

- `hc₁` is not needed for domination or integrability.
- For the proposed openness argument, you need `{x | L₁ x < L₂ x}` to be open. Having both `hc₁` and `hc₂` is a simple sufficient condition:
  ```lean
  isOpen_lt hc₁ hc₂
  ```
- More minimally, replace both continuity assumptions by
  ```lean
  IsOpen {x | L₁ x < L₂ x}
  ```
  together with enough measurability of the second exponential to use `Integrable.mono'`.

The integrability data are sufficient:

1. `h₁` gives integrability of `e^{-tL₁}`.
2. `hc₂` gives measurability of `e^{-tL₂}`.
3. From `L₁ ≤ L₂` and `t > 0`,
   \[
   e^{-tL₂(x)} \le e^{-tL₁(x)},
   \]
   so `Integrable.mono'` gives integrability of the second exponential.
4. Then `h₁.sub h₂` gives integrability of the difference, and `integral_sub h₁ h₂` is available.

Thus no separate integrability hypothesis for `L₂` or the difference is required.

A slightly more foundational theorem would replace continuity/nonempty strict locus by the direct condition
```lean
0 < volume {x | L₁ x < L₂ x}
```
and then derive your continuous witness theorem as a corollary.

---

## 2. Relevant API and proof details

### `Integrable.mono'`

The intended usage is:

```lean
h₁.mono' hmeas hdom
```

where, schematically,

```lean
h₁    : Integrable f μ
hmeas : AEStronglyMeasurable g μ
hdom  : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖f x‖
```

For the second exponential:

```lean
let f₁ : ℝ → ℝ := fun x => Real.exp (-(t * L₁ x))
let f₂ : ℝ → ℝ := fun x => Real.exp (-(t * L₂ x))

have hf₂_cont : Continuous f₂ :=
  Real.continuous_exp.comp ((continuous_const.mul hc₂).neg)

have hf₂_meas : AEStronglyMeasurable f₂ volume :=
  hf₂_cont.aestronglyMeasurable
```

Then:

```lean
have hf₂_le : ∀ x, f₂ x ≤ f₁ x := by
  intro x
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (mul_le_mul_of_nonneg_left (hle x) ht.le)

have h₂ : Integrable f₂ := by
  apply h₁.mono' hf₂_meas
  filter_upwards with x
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hf₂_le x
```

Using `Real.exp_nonneg` and `norm_of_nonneg` is another possible normalization, but the `abs_of_pos (Real.exp_pos _)` version tends to be predictable over `ℝ`.

### Strict positivity of the difference

Define:

```lean
let d : ℝ → ℝ := fun x => f₁ x - f₂ x
```

Pointwise nonnegativity:

```lean
have hd_nonneg : ∀ x, 0 ≤ d x := by
  intro x
  exact sub_nonneg.mpr (hf₂_le x)
```

Integrability:

```lean
have hd_int : Integrable d := h₁.sub h₂
```

For a point in the strict locus:

```lean
have strict_exp {x : ℝ} (hx : L₁ x < L₂ x) :
    f₂ x < f₁ x := by
  apply Real.exp_lt_exp.mpr
  exact neg_lt_neg (mul_lt_mul_of_pos_left hx ht)
```

The clean support inclusion is:

```lean
have hsubset :
    {x | L₁ x < L₂ x} ⊆ Function.support d := by
  intro x hx
  change d x ≠ 0
  exact ne_of_gt (sub_pos.mpr (strict_exp hx))
```

Recall that `Function.support d` is definitionally `{x | d x ≠ 0}`, so `change` usually handles this directly.

### Open strict locus

```lean
have hopen : IsOpen {x | L₁ x < L₂ x} :=
  isOpen_lt hc₁ hc₂

have hnonempty : ({x | L₁ x < L₂ x} : Set ℝ).Nonempty := by
  rcases hx₀ with ⟨x₀, hx₀⟩
  exact ⟨x₀, hx₀⟩
```

For Lebesgue measure on `ℝ`, the standard result is exposed as `IsOpen.measure_pos`; dot notation is generally the easiest form:

```lean
have hopen_pos : 0 < volume {x | L₁ x < L₂ x} :=
  hopen.measure_pos hnonempty
```

Then:

```lean
have hsupp_pos : 0 < volume (Function.support d) :=
  lt_of_lt_of_le hopen_pos (measure_mono hsubset)
```

### `integral_pos_iff_support_of_nonneg`

For pointwise nonnegativity, use the non-`ae` theorem. In this API family, the theorem takes the integrability and nonnegativity hypotheses and characterizes positivity by positivity of the support measure. A typical use is:

```lean
have hd_pos : 0 < ∫ x, d x := by
  exact
    (MeasureTheory.integral_pos_iff_support_of_nonneg hd_int hd_nonneg).2
      hsupp_pos
```

If elaboration selects the `ae` version instead, the corresponding form is:

```lean
have hd_nonneg_ae : ∀ᵐ x ∂volume, 0 ≤ d x :=
  Filter.Eventually.of_forall hd_nonneg

have hd_pos : 0 < ∫ x, d x := by
  exact
    (MeasureTheory.integral_pos_iff_support_of_nonneg_ae hd_int hd_nonneg_ae).2
      hsupp_pos
```

The pointwise version is preferable here because you already have pointwise order.

Finally:

```lean
have hsub :
    (∫ x, d x) = partitionFunction L₁ t - partitionFunction L₂ t := by
  simpa [d, f₁, f₂, partitionFunction] using integral_sub h₁ h₂

rw [hsub] at hd_pos
linarith
```

Depending on how `partitionFunction` is reducible, the final block may simply be:

```lean
rw [integral_sub h₁ h₂] at hd_pos
simpa [partitionFunction, d, f₁, f₂] using hd_pos
```

---

## 3. B and `StrictAntiOn`

Your understanding of `StrictAntiOn` is correct. Operationally, the proof starts as:

```lean
intro b₁ hb₁ b₂ hb₂ hb
```

with:

```lean
hb₁ : b₁ ∈ Set.Ici 0   -- hence 0 ≤ b₁
hb₂ : b₂ ∈ Set.Ici 0
hb  : b₁ < b₂
```

The only additional point is that applying A with

```lean
L₁ x = V x + b₁ * g x
L₂ x = V x + b₂ * g x
```

requires integrability of the `b₁` perturbation. This follows from the baseline integrability because `b₁ ≥ 0` and `g ≥ 0`:

\[
V(x)\le V(x)+b₁g(x),
\qquad
e^{-t(V+b₁g)}\le e^{-tV}.
\]

So B needs a small preliminary domination argument for each `b₁ ∈ Ici 0`.

The pointwise potential order is:

```lean
have hpot_le : ∀ x, V x + b₁ * g x ≤ V x + b₂ * g x := by
  intro x
  exact add_le_add_left (mul_le_mul_of_nonneg_right hb.le (hg_nonneg x)) _
```

The strict witness is:

```lean
have hpot_lt :
    V x₀ + b₁ * g x₀ < V x₀ + b₂ * g x₀ := by
  exact add_lt_add_left (mul_lt_mul_of_pos_right hb hgx₀) _
```

Continuity:

```lean
have hcont (b : ℝ) :
    Continuous (fun x => V x + b * g x) :=
  hcV.add (continuous_const.mul hcg)
```

A recommended statement is:

```lean
theorem partitionFunction_strictAntiOn_nonnegPerturbation
    {V g : ℝ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hV : Continuous V)
    (hg : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hx₀ : ∃ x₀, 0 < g x₀)
    (hV_int : Integrable fun x => Real.exp (-(t * V x))) :
    StrictAntiOn
      (fun b => partitionFunction (fun x => V x + b * g x) t)
      (Set.Ici 0) := by
  ...
```

No subtlety beyond deriving perturbed integrability from `hV_int`.

---

## 4. C and injectivity

The relevant theorem is:

```lean
StrictAntiOn.injOn
```

With dot notation:

```lean
have hinj :
    Set.InjOn
      (fun b => partitionFunction (fun x => V x + b * g x) t)
      (Set.Ici 0) :=
  hanti.injOn
```

Then equality recovery is simply:

```lean
exact hanti.injOn hb₁ hb₂ hZ
```

where `hb₁ : b₁ ∈ Set.Ici 0` and similarly for `b₂`. Since membership in `Ici 0` reduces to `0 ≤ b`, the supplied hypotheses often work directly; otherwise:

```lean
exact hanti.injOn (show b₁ ∈ Set.Ici 0 from hb₁)
  (show b₂ ∈ Set.Ici 0 from hb₂) hZ
```

A quotable final theorem shape:

```lean
theorem quarticCoefficient_eq_of_partitionFunction_eq
    {t b₁ b₂ : ℝ}
    (ht : 0 < t)
    (hb₁ : 0 ≤ b₁)
    (hb₂ : 0 ≤ b₂)
    (hZ :
      partitionFunction
          (fun x : ℝ => kthPotential 1 x + b₁ * x ^ 4) t
        =
      partitionFunction
          (fun x : ℝ => kthPotential 1 x + b₂ * x ^ 4) t) :
    b₁ = b₂ := by
  have hanti :
      StrictAntiOn
        (fun b =>
          partitionFunction
            (fun x : ℝ => kthPotential 1 x + b * x ^ 4) t)
        (Set.Ici 0) := by
    -- Apply B with g x = x^4 and x₀ = 1.
    ...

  exact hanti.injOn hb₁ hb₂ hZ
```

If the project wants the seabed normalization visible in the theorem statement, use `x ^ 2 / 2` rather than `kthPotential 1`; otherwise the latter better records the connection to the existing hierarchy.

---

## 5. Better minimal candidate

The most reusable minimal result is a measure-theoretic core:

```lean
theorem partitionFunction_lt_of_le_of_strictOnPositiveMeasure
    {L₁ L₂ : ℝ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hle : ∀ x, L₁ x ≤ L₂ x)
    (hmeas₂ :
      AEStronglyMeasurable
        (fun x => Real.exp (-(t * L₂ x))) volume)
    (h₁ : Integrable fun x => Real.exp (-(t * L₁ x)))
    (hstrict : 0 < volume {x | L₁ x < L₂ x}) :
    partitionFunction L₂ t < partitionFunction L₁ t
```

Then A is the topological corollary:

```lean
continuous + nonempty strict locus
    ⇒ open nonempty strict locus
    ⇒ positive volume
    ⇒ core theorem
```

This cleanly separates:

- measure-theoretic strict integral monotonicity;
- topological production of a positive-measure strict locus;
- coefficient recovery.

You could also formulate the core with `hle` only almost everywhere, but then the strict set/support bookkeeping becomes slightly less pleasant. For the current application, pointwise order is appropriate.

---

## 6. Vote

Yes: **A + B + C in one file**, but organized as a theorem ladder:

1. positive-measure strict monotonicity core;
2. A as the continuous/nonempty-open-locus corollary;
3. B as nonnegative-ray strict antitonicity;
4. C as the quartic recovery application.

A name such as `Laplace/OrderRecovery.lean` or `Laplace/PartitionFunction/StrictMonotonicity.lean` would fit. This gives the file a coherent story: strict order of potentials, strict antitonicity of partition functions, then single-temperature coefficient identifiability.