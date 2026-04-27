Here’s the glue I’d use.

## Q1/Q2: don’t split with `setIntegral` unless you must

For **inequalities**, the cleanest idiom is:

- define two **global** bounds `Glocal`, `Gtail`,
- prove pointwise `|f u| ≤ Glocal u + Gtail u` by `by_cases hu : ‖u‖ ≤ δ * Real.sqrt t`,
- then use `norm_integral_le_integral_norm` + `integral_mono_ae` + `integral_add`.

This avoids `indicator`, `setIntegral`, `integral_add_compl` entirely.

### Template

```lean
let s : Set (ι → ℝ) := {u | ‖u‖ ≤ δ * Real.sqrt t}

let Glocal : (ι → ℝ) → ℝ :=
  fun u => (Cs / Real.sqrt t) *
    (‖u‖ ^ 3 * Real.exp (-(α * ‖u‖ ^ 2)))

let Gtail : (ι → ℝ) → ℝ :=
  fun u => (2 * Real.exp (-(β * t))) *
    Real.exp (-(α * ‖u‖ ^ 2))

have hpt : ∀ u, |f u| ≤ Glocal u + Gtail u := by
  intro u
  by_cases hu : ‖u‖ ≤ δ * Real.sqrt t
  · have hloc := abs_gaussianWeight_mul_exp_sub_one_le_local
      V H hc_pos hR_pos hCs_nn hV.coercive_bound hV.local_bound
      hδ_pos hδ_le_R hδ_const ht_pos u hu
    have hloc' : |f u| ≤ Glocal u := by
      simpa [f, Glocal, α, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using hloc
    have htail_nn : 0 ≤ Gtail u := by positivity
    linarith
  · have hu' : δ * Real.sqrt t < ‖u‖ := lt_of_not_ge hu
    have htail := abs_gaussianWeight_mul_exp_sub_one_le_tail
      V H hc_pos hR_pos hCs_nn hV.coercive_bound hV.local_bound
      hδ_pos ht_pos u hu'
    have htail' : |f u| ≤ Gtail u := by
      simpa [f, Gtail, α, β, mul_assoc, mul_left_comm, mul_comm] using htail
    have hloc_nn : 0 ≤ Glocal u := by positivity
    linarith
```

Then:

```lean
have hGlocal_int : Integrable Glocal := by
  simpa [Glocal, integral_const_mul] using
    (integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) (α := α) hα_pos 3).const_mul
      (Cs / Real.sqrt t)

have hGtail_int : Integrable Gtail := by
  simpa [Gtail, integral_const_mul] using
    (integrable_exp_neg_const_norm_sq (ι := ι) (α := α) hα_pos).const_mul
      (2 * Real.exp (-(β * t)))

have hf_int : Integrable f := by
  -- from `h_int_rescaled.sub hGauss.int_gW`, then `congr`
  ...

have habs_int : Integrable (fun u => |f u|) := hf_int.norm

have h_int_le :
    ∫ u, |f u| ≤ ∫ u, (Glocal u + Gtail u) := by
  exact integral_mono_ae habs_int (hGlocal_int.add hGtail_int)
    (Filter.Eventually.of_forall hpt)
```

If your snapshot wants `integral_mono_of_nonneg`, use that instead; same structure.

---

If you **really** want `setIntegral`, use indicators, not `integral_add_compl` first. For a measurable `s`:

```lean
have hs : MeasurableSet s := by
  exact (isClosed_le continuous_norm continuous_const).measurableSet

rw [← MeasureTheory.integral_indicator hs]
```

and bound `s.indicator g ≤ g` pointwise. But I would avoid this for the asymptote proofs.

---

## Q3: yes, prove a separate denominator lemma

I would definitely factor out:

```lean
lemma rescaledPartition_ge_half_gaussianZ
    ...
    : ∃ T₁ : ℝ, 1 ≤ T₁ ∧ ∀ t ≥ T₁,
        gaussianZ H / 2 ≤ rescaledPartition V t := by
```

Use the partition asymptote once, then reuse it in observable + pair.

### Skeleton

```lean
obtain ⟨K, T, hT, hpart⟩ :=
  rescaledPartition_eq_gaussianZ_add_O_inv_sqrt V H Hinv hV hGauss

let T₁ : ℝ := max T (max 1 (((2 * |K|) / gaussianZ H) ^ 2))
refine ⟨T₁, le_max_of_le_right (le_max_of_le_left le_rfl), ?_⟩
intro t ht

have htT : T ≤ t := le_of_max_le_left ht
have ht' : max 1 (((2 * |K|) / gaussianZ H) ^ 2) ≤ t := le_of_max_le_right ht
have ht1 : 1 ≤ t := le_of_max_le_left ht'
have htsq : ((2 * |K|) / gaussianZ H) ^ 2 ≤ t := le_of_max_le_right ht'
have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos

have hpart' : |rescaledPartition V t - gaussianZ H| ≤ |K| / Real.sqrt t := by
  calc
    |rescaledPartition V t - gaussianZ H|
      ≤ K / Real.sqrt t := hpart t htT
    _ ≤ |K| / Real.sqrt t := by
      gcongr
      exact le_abs_self K

have hsqrt :
    (2 * |K|) / gaussianZ H ≤ Real.sqrt t := by
  apply Real.le_sqrt
  · positivity
  · positivity
  · exact htsq

have hhalf : |K| / Real.sqrt t ≤ gaussianZ H / 2 := by
  calc
    |K| / Real.sqrt t
      = (gaussianZ H / 2) *
          (((2 * |K|) / gaussianZ H) / Real.sqrt t) := by
          field_simp [hGauss.Z_pos.ne']
    _ ≤ (gaussianZ H / 2) * 1 := by
          gcongr
          exact (div_le_iff hsqrt_pos).2 hsqrt
    _ = gaussianZ H / 2 := by ring

have habs := abs_le.mp hpart'
linarith
```

---

## Q4: partition asymptote proof recipe

This is the one I’d write almost exactly.

### Constants

```lean
let c : ℝ := hV.coercive_const
let R : ℝ := hV.local_radius
let Cs : ℝ := hV.local_const
let δ : ℝ := min R (c / (4 * (Cs + 1)))
let α : ℝ := c / 4
let β : ℝ := c * δ ^ 2 / 4

let Mlocal : ℝ := ∫ u : ι → ℝ, ‖u‖ ^ 3 * Real.exp (-(α * ‖u‖ ^ 2))
let Mtail  : ℝ := ∫ u : ι → ℝ, Real.exp (-(α * ‖u‖ ^ 2))
```

### Threshold and constant

```lean
refine ⟨Cs * Mlocal + 2 * Mtail, max 1 (1 / β ^ 2), le_max_left _ _, ?_⟩
intro t ht
```

### Positivity facts

```lean
have hc_pos : 0 < c := hV.coercive_const_pos
have hR_pos : 0 < R := hV.local_radius_pos
have hCs_nn : 0 ≤ Cs := hV.local_const_nonneg
have hδ_pos : 0 < δ := by
  dsimp [δ]
  exact lt_min hR_pos (by positivity)
have hδ_le_R : δ ≤ R := by
  dsimp [δ]
  exact min_le_left _ _
have hδ_le_aux : δ ≤ c / (4 * (Cs + 1)) := by
  dsimp [δ]
  exact min_le_right _ _
have hδ_const : Cs * δ ≤ c / 4 := by
  have hCs1_pos : 0 < Cs + 1 := by linarith
  calc
    Cs * δ ≤ Cs * (c / (4 * (Cs + 1))) :=
      mul_le_mul_of_nonneg_left hδ_le_aux hCs_nn
    _ = (Cs / (Cs + 1)) * (c / 4) := by
      field_simp
    _ ≤ 1 * (c / 4) := by
      gcongr
      rw [div_le_one hCs1_pos]
      linarith
    _ = c / 4 := by ring

have hα_pos : 0 < α := by
  dsimp [α]
  linarith
have hβ_pos : 0 < β := by
  dsimp [β]
  positivity

have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
have htβ : 1 / β ^ 2 ≤ t := le_trans (le_max_right _ _) ht
have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
```

### Integrability + partition-difference identity

```lean
have h_int_rw :
    Integrable (fun u : ι → ℝ =>
      gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))) :=
  integrable_rescaled_weight V hV.V_continuous H hc_pos hV.coercive_bound ht_pos

have h_part_id :=
  rescaledPartition_sub_gaussianZ_eq_integral V H t hGauss.int_gW h_int_rw
```

Define the difference integrand:

```lean
let F : (ι → ℝ) → ℝ := fun u =>
  gaussianWeight H u * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
```

and show integrable:

```lean
have hF_int : Integrable F := by
  refine (h_int_rw.sub hGauss.int_gW).congr ?_
  filter_upwards with u
  simp [F]
  ring
```

### Global local+tail majorant

```lean
let Glocal : (ι → ℝ) → ℝ := fun u =>
  (Cs / Real.sqrt t) * (‖u‖ ^ 3 * Real.exp (-(α * ‖u‖ ^ 2)))

let Gtail : (ι → ℝ) → ℝ := fun u =>
  (2 * Real.exp (-(β * t))) * Real.exp (-(α * ‖u‖ ^ 2))
```

Integrable:

```lean
have hGlocal_int : Integrable Glocal := by
  simpa [Glocal, Mlocal, integral_const_mul, mul_assoc, mul_left_comm, mul_comm]
    using
      (integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) (α := α) hα_pos 3).const_mul
        (Cs / Real.sqrt t)

have hGtail_int : Integrable Gtail := by
  simpa [Gtail, Mtail, integral_const_mul, mul_assoc, mul_left_comm, mul_comm]
    using
      (integrable_exp_neg_const_norm_sq (ι := ι) (α := α) hα_pos).const_mul
        (2 * Real.exp (-(β * t)))
```

Pointwise bound = by_cases on local/tail, as in Q1.

### Main `calc`

```lean
have h_main :
    |rescaledPartition V t - gaussianZ H|
      ≤ (Cs / Real.sqrt t) * Mlocal
        + (2 * Real.exp (-(β * t))) * Mtail := by
  have h_int_le :
      ∫ u, |F u| ≤ ∫ u, (Glocal u + Gtail u) := by
    exact integral_mono_ae hF_int.norm (hGlocal_int.add hGtail_int)
      (Filter.Eventually.of_forall hpt)
  calc
    |rescaledPartition V t - gaussianZ H|
      = |∫ u, F u| := by rw [h_part_id, F]
    _ ≤ ∫ u, |F u| := norm_integral_le_integral_norm hF_int
    _ ≤ ∫ u, (Glocal u + Gtail u) := h_int_le
    _ = ∫ u, Glocal u + ∫ u, Gtail u := by
          rw [integral_add hGlocal_int hGtail_int]
    _ = (Cs / Real.sqrt t) * Mlocal
        + (2 * Real.exp (-(β * t))) * Mtail := by
          simp [Glocal, Gtail, Mlocal, Mtail, integral_const_mul]
```

### Convert tail `exp(-βt)` to `1/√t`

```lean
have htail_sqrt : Real.exp (-(β * t)) ≤ 1 / Real.sqrt t :=
  exp_neg_const_mul_le_inv_sqrt hβ_pos htβ

have hMlocal_nn : 0 ≤ Mlocal := by
  dsimp [Mlocal]
  apply integral_nonneg
  intro u
  positivity

have hMtail_nn : 0 ≤ Mtail := by
  dsimp [Mtail]
  apply integral_nonneg
  intro u
  positivity

calc
  |rescaledPartition V t - gaussianZ H|
    ≤ (Cs / Real.sqrt t) * Mlocal
        + (2 * Real.exp (-(β * t))) * Mtail := h_main
  _ ≤ (Cs / Real.sqrt t) * Mlocal
        + (2 * (1 / Real.sqrt t)) * Mtail := by
        gcongr
  _ = (Cs * Mlocal + 2 * Mtail) / Real.sqrt t := by
        field_simp [hsqrt_pos.ne']
        ring
```

That’s the whole proof shape.

---

## Q5: observable theorem — best decomposition

Yes: the clean decomposition is

\[
N_t(\phi)=\frac1{\sqrt t}\int \langle a,u\rangle g_W
+\frac1{\sqrt t}\int \langle a,u\rangle g_W(\exp(-s_t)-1)
+\int r_t(u)\,g_W\,\exp(-s_t)
\]

where

\[
r_t(u)=\phi((\sqrt t)^{-1}u)-(\sqrt t)^{-1}\langle a,u\rangle.
\]

The first integral is exactly the odd Gaussian one and vanishes.

So define:

```lean
let rem : (ι → ℝ) → ℝ := fun u =>
  φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u
```

Then from `rescaledNumerator_eq_linear_plus_remainder`:

```lean
have hnum_split :
    rescaledNumerator V t φ
      = (Real.sqrt t)⁻¹ *
          (∫ u, dot a u * gaussianWeight H u *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1))
        + ∫ u, rem u * gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)) := by
  -- use `rescaledNumerator_eq_linear_plus_remainder`
  -- then split `exp(-s_t) = (exp(-s_t) - 1) + 1`
  -- and kill `∫ dot a u * gaussianWeight H u = 0`
```

### What to prove next

Prove two helper bounds:

```lean
lemma rescaledNumerator_linear_correction_bound_inv :
  ∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
    |(Real.sqrt t)⁻¹ *
      ∫ u, dot a u * gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1)| ≤ K / t

lemma rescaledNumerator_remainder_bound_inv :
  ∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
    |∫ u, rem u * gaussianWeight H u *
      Real.exp (-(rescaledPerturbation V H t u))| ≤ K / t
```

Then `N_t = O(1/t)` by triangle inequality, and divide by `D_t ≥ Z/2`.

### Bounds to use

For the **linear correction term**, use `A := ∑ i, |a i|` and `abs_dot_le_l1_mul_norm`.

- Local:
  ```lean
  |(1/√t) * dot a u * gW * (exp(-s_t)-1)|
    ≤ (A * Cs / t) * ‖u‖^4 * exp(-α ‖u‖²)
  ```
- Tail:
  ```lean
  |(1/√t) * dot a u * gW * (exp(-s_t)-1)|
    ≤ (2 * A / √t) * ‖u‖ * exp(-α ‖u‖²) * exp(-β t)
  ```
  and use `exp(-β t) ≤ 1/√t` to get `≤ const/t * ‖u‖ * exp(-α‖u‖²)`.

For the **remainder term**:

- Local: from `abs_rescaledObservable_linear_error_le` + `rescaled_weight_le_coercive`
  ```lean
  |rem u * rescaledWeight|
    ≤ (Cφ / t) * ‖u‖^2 * exp(-(c * ‖u‖²))
  ```
- Tail: use polynomial growth of `φ`, plus
  ```lean
  rescaledWeight ≤ exp(-c ‖u‖²)
  ```
  and on the tail
  ```lean
  exp(-c ‖u‖²)
    ≤ exp(-((c/2) * ‖u‖²)) * exp(-((c * δ² / 2) * t))
  ```
  so you want one extra scalar helper:

### Add this helper now

```lean
lemma exp_neg_const_mul_le_inv
    {β : ℝ} (hβ_pos : 0 < β) {t : ℝ} (ht : 4 / β ^ 2 ≤ t) :
    Real.exp (-(β * t)) ≤ 1 / t := by
  have hβ2_pos : 0 < β / 2 := by linarith
  have ht' : 1 / (β / 2) ^ 2 ≤ t := by
    simpa [div_eq_mul_inv, pow_two] using ht
  have hhalf :=
    exp_neg_const_mul_le_inv_sqrt (β := β / 2) hβ2_pos ht'
  have ht_pos : 0 < t := lt_of_lt_of_le (by positivity) ht
  calc
    Real.exp (-(β * t))
      = (Real.exp (-((β / 2) * t))) ^ 2 := by
          congr 1
          ring
    _ ≤ (1 / Real.sqrt t) ^ 2 := by
          gcongr
    _ = 1 / t := by
          field_simp [Real.sq_sqrt ht_pos.le]
```

That helper makes the observable tail completely painless.

Then final quotient step:

```lean
have hD : gaussianZ H / 2 ≤ rescaledPartition V t := ...
have hD_pos : 0 < rescaledPartition V t := lt_of_lt_of_le (by positivity) hD

calc
  |rescaledExpectation V t φ|
    = |rescaledNumerator V t φ / rescaledPartition V t| := by
        simp [rescaledExpectation]
  _ = |rescaledNumerator V t φ| / rescaledPartition V t := by
        rw [abs_div, abs_of_pos hD_pos]
  _ ≤ |rescaledNumerator V t φ| / (gaussianZ H / 2) := by
        gcongr
  _ ≤ (K_N / t) / (gaussianZ H / 2) := by
        gcongr
  _ = (2 * K_N / gaussianZ H) / t := by
        field_simp [hGauss.Z_pos.ne']
```

---

## Q6: pair theorem — do **numerator first**, then quotient

This is the cleanest route.

### Step 1: pair numerator asymptote

Prove:

```lean
lemma rescaledPairNumerator_eq_main_add_O_inv_sqrt :
  ∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
    |t * rescaledNumerator V t (fun w => φ w * ψ w)
      - gaussianZ H * dot a (Hinv b)| ≤ K / Real.sqrt t
```

Use `pair_product_expansion`, multiply by `t`, and integrate termwise.

After multiplying by `t`, the expansion is:

- leading term:
  ```lean
  dot a u * dot b u
  ```
- two cross terms:
  ```lean
  (Real.sqrt t) * dot a u * remψ u
  (Real.sqrt t) * dot b u * remφ u
  ```
- quadratic remainder:
  ```lean
  t * remφ u * remψ u
  ```

For the leading term:

```lean
∫ dot a u * dot b u * gaussianWeight H u
  = gaussianZ H * dot a (Hinv b)
```

via `gaussian_dot_mul_dot`.

But because your actual weight is `gW * exp(-s_t)`, split it as:

```lean
∫ dot a u * dot b u * gW * exp(-s_t)
 = ∫ dot a u * dot b u * gW
 + ∫ dot a u * dot b u * gW * (exp(-s_t) - 1)
```

The second piece is `O(1/√t)`.

### Sizes of the residual terms

Let `A := ∑ i, |a i|`, `B := ∑ i, |b i|`.

- leading correction local:
  ```lean
  |dot a u * dot b u * gW * (exp(-s_t)-1)|
    ≤ (A * B * Cs / √t) * ‖u‖^5 * exp(-α ‖u‖²)
  ```
- leading correction tail:
  ```lean
  ≤ 2 * A * B * ‖u‖^2 * exp(-α ‖u‖²) * exp(-β t)
  ```
  then `exp(-β t) ≤ 1/√t`.

- cross term local:
  since `|remψ| ≤ Cψ ‖u‖² / t`,
  ```lean
  |√t * dot a u * remψ u * rescaledWeight|
    ≤ (A * Cψ / √t) * ‖u‖^3 * exp(-(c ‖u‖²))
  ```
- cross term tail:
  use polynomial growth for `remψ`, coercive tail split
  ```lean
  rescaledWeight ≤ exp(-((c/2) ‖u‖²)) * exp(-((c δ² / 2) t))
  ```
  and then `√t * exp(-γ t) ≤ 1/√t` from `exp_neg_const_mul_le_inv`.

- quadratic remainder local:
  ```lean
  |t * remφ u * remψ u * rescaledWeight|
    ≤ (Cφ * Cψ / t) * ‖u‖^4 * exp(-(c ‖u‖²))
    ≤ const / √t * ‖u‖^4 * exp(-(c ‖u‖²))
  ```
  for `t ≥ 1`.
- quadratic remainder tail:
  polynomial growth + exponential tail gives again `O(1/√t)`.

So the pair numerator proof is exactly the observable proof pattern, just with more terms.

---

## Final quotient step for pair

Once you have

```lean
|t * rescaledNumerator V t (fun w => φ w * ψ w)
  - gaussianZ H * dot a (Hinv b)| ≤ K_N / √t
```

and

```lean
|rescaledPartition V t - gaussianZ H| ≤ K_D / √t
```

plus `rescaledPartition ≥ gaussianZ/2`, you can avoid messy quotient algebra by using:

\[
\frac{N_t}{D_t} - m
= \frac{N_t - Zm}{D_t} + m \frac{Z - D_t}{D_t}
\]

with `m := dot a (Hinv b)` and `Z := gaussianZ H`.

Lean form:

```lean
have h_alg :
    (t * rescaledNumerator V t (fun w => φ w * ψ w)) / rescaledPartition V t
      - dot a (Hinv b)
    =
    (t * rescaledNumerator V t (fun w => φ w * ψ w)
      - gaussianZ H * dot a (Hinv b)) / rescaledPartition V t
    + dot a (Hinv b) *
        (gaussianZ H - rescaledPartition V t) / rescaledPartition V t := by
  field_simp
  ring
```

Then:

```lean
calc
  |t * rescaledExpectation V t (fun w => φ w * ψ w) - dot a (Hinv b)|
    = | ... | := by simp [rescaledExpectation, h_alg]
  _ ≤ |t * rescaledNumerator ... - gaussianZ H * dot a (Hinv b)|
        / (gaussianZ H / 2)
      + |dot a (Hinv b)| *
        |gaussianZ H - rescaledPartition V t| / (gaussianZ H / 2) := by
        -- abs_add + denominator lower bound
  _ ≤ ...
  _ ≤ K / Real.sqrt t := ...
```

---

## Bottom line

My recommendations:

1. **For Q1/Q2:** avoid `setIntegral`; patch local/tail pointwise bounds into a global bound `≤ Glocal + Gtail`.
2. **For Q3:** yes, prove `rescaledPartition_ge_half_gaussianZ`.
3. **For Q4:** the partition proof is straightforward with `norm_integral_le_integral_norm`, `integral_mono_ae`, and `integral_add`.
4. **For Q5/Q6:** do **numerator asymptote first**, then divide by the denominator using the half-`Z` lower bound.
5. Add one scalar helper:
   - `exp_neg_const_mul_le_inv`
   
   You will use it repeatedly.

If you want, I can next write the **actual Lean skeleton** for the partition theorem in near-compilable form.