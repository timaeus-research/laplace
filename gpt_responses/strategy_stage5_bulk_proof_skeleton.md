Short answer first:

- **For the full `bulkErrASymmIntegrand`**, the cleanest pointwise bounds are the **weighted** ones, i.e. with  
  `Real.exp (-(c * ‖u‖^2))` on the RHS.
- If you want **polynomial-only** bounds, they should really be for the **core bracket**
  (the symmetrized algebraic factor before multiplying by `gaussianWeight H u` / coercive weight), not for the full integrand.
- Also: for the local/tail split in Lemma 3, the clean split is with  
  `R := min hφ.toObservableTensorApprox.jet_radius hV.toPotentialTensorApprox.jet_radius`.  
  If your tail lemma is only stated with `hφ.jet_radius`, the assembly is only direct if you already know `hφ.jet_radius ≤ hV.jet_radius`.

## Recommended shapes

Let
`c := hV.toPotentialApprox.coercive_const > 0`
and
`R := min hφ.toObservableTensorApprox.jet_radius hV.toPotentialTensorApprox.jet_radius`.

Then the clean shapes are:

- **Local core bound**:
  ```lean
  |coreSymmA ... t u| ≤ C₆ * ‖u‖^6 / t + C₈ * ‖u‖^8 / t
  ```
  hence
  ```lean
  ≤ K_loc / t * (1 + ‖u‖^8)
  ```

- **Local full integrand bound**:
  ```lean
  |bulkErrASymmIntegrand ... t u|
    ≤ K_loc / t * (1 + ‖u‖^8) * Real.exp (-(c * ‖u‖^2))
  ```

- **Tail full integrand bound**:
  if `R * Real.sqrt t < ‖u‖`, then
  ```lean
  |bulkErrASymmIntegrand ... t u|
    ≤ K_tail * (1 + ‖u‖^M) * Real.exp (-(c * ‖u‖^2))
  ```
  and then absorb `1/t` on the tail via
  `1 ≤ ‖u‖^2 / (R^2 * t)`:
  ```lean
  ≤ K_tail / (R^2 * t) * (‖u‖^2 + ‖u‖^(M+2)) * Real.exp (-(c * ‖u‖^2))
  ```

That last weighted tail shape is the one you want in the integral lemma.

---

Below is a **proof skeleton** for the three lemmas. I’ve kept the structure explicit and marked the arithmetic / exact simp lemmas as `sorry`/TODO.

---

## 1. `abs_bulkErrA_local_le`

```lean
private lemma abs_bulkErrA_local_le
    (V φ : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    (hφ : ObservableQuinticApprox φ (0 : ι → ℝ)) :
    ∃ K_loc : ℝ, 0 ≤ K_loc ∧ ∀ t : ℝ, 1 ≤ t →
      ∀ u : ι → ℝ,
        ‖u‖ ≤ hφ.toObservableTensorApprox.jet_radius * Real.sqrt t →
        ‖u‖ ≤ hV.toPotentialTensorApprox.jet_radius * Real.sqrt t →
        |bulkErrASymmIntegrand V φ H b hφ.toObservableTensorApprox t u|
          ≤ K_loc / t * (1 + ‖u‖ ^ 8) := by
  classical

  -- Recommended helper: a cubic bound for `expPotCubic`.
  obtain ⟨C3, hC3_nonneg, hC3⟩ :
      ∃ C3 : ℝ, 0 ≤ C3 ∧
        ∀ {t : ℝ}, 0 < t → ∀ u : ι → ℝ,
          |expPotCubic V H hV.toPotentialTensorApprox t u|
            ≤ C3 * ‖u‖ ^ 3 / Real.sqrt t := by
    -- TODO: prove from the definition of `expPotCubic`
    sorry

  let Cb : ℝ := ‖b‖
  let K₁ : ℝ := Cb * hφ.Q_const
  let K₂ : ℝ := Cb * hφ.toObservableTensorApprox.jet_const * (2 * C3)
  let K₃ : ℝ := Cb * hφ.toObservableTensorApprox.jet_const * hV.Q_const

  refine ⟨K₁ + K₂ + K₃ * (hV.toPotentialTensorApprox.jet_radius ^ 2) + 1, by positivity, ?_⟩
  intro t ht u huφ huV

  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hsqrt_nonneg : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have huφ_neg :
      ‖-u‖ ≤ hφ.toObservableTensorApprox.jet_radius * Real.sqrt t := by
    simpa using huφ
  have huV_neg :
      ‖-u‖ ≤ hV.toPotentialTensorApprox.jet_radius * Real.sqrt t := by
    simpa using huV

  -- Expand the symmetrized integrand into the common `gaussianWeight H u`
  -- times the bracket `r(u)e^{-s(u)} - r(-u)e^{-s(-u)}`.
  have h_expand :
      bulkErrASymmIntegrand V φ H b hφ.toObservableTensorApprox t u
        =
      gaussianWeight H u
        * (t * Real.sqrt t * dot b u)
        * ((expNumObsRem φ 0 hφ.toObservableTensorApprox t u)
              * Real.exp (-(rescaledPerturbation V H t u))
          - (expNumObsRem φ 0 hφ.toObservableTensorApprox t (-u))
              * Real.exp (-(rescaledPerturbation V H t (-u)))) := by
    -- TODO: unfold `bulkErrASymmIntegrand`, `bulkErrA`; use `dot b (-u) = - dot b u`
    sorry

  rw [h_expand]

  set r : (ι → ℝ) → ℝ := fun v =>
    expNumObsRem φ 0 hφ.toObservableTensorApprox t v
  set s : (ι → ℝ) → ℝ := fun v =>
    rescaledPerturbation V H t v

  have h_split :
      r u * Real.exp (-(s u)) - r (-u) * Real.exp (-(s (-u)))
        =
      (r u - r (-u)) * Real.exp (-(s u))
        + r (-u) * (Real.exp (-(s u)) - Real.exp (-(s (-u)))) := by
    ring

  have hg_nonneg : 0 ≤ gaussianWeight H u := by
    -- TODO
    sorry

  -- Crude coercive weight bounds; for Lemma 1 you only need `≤ 1`.
  have h_weight_u_le_one :
      gaussianWeight H u * Real.exp (-(s u)) ≤ 1 := by
    -- TODO: `rescaled_weight_le_coercive` + `exp (-(c*‖u‖^2)) ≤ 1`
    sorry

  have h_weight_neg_le_one :
      gaussianWeight H u * Real.exp (-(s (-u))) ≤ 1 := by
    -- TODO: same, using `‖-u‖ = ‖u‖`
    sorry

  have h_weight_max_le_one :
      gaussianWeight H u
        * max (Real.exp (-(s u))) (Real.exp (-(s (-u)))) ≤ 1 := by
    -- TODO: derive from the previous two
    sorry

  have hdot :
      |dot b u| ≤ Cb * ‖u‖ := by
    -- TODO: Cauchy–Schwarz / `abs_dot_le_norm`
    sorry

  have hr_diff :
      |r u - r (-u)| ≤ hφ.Q_const * ‖u‖ ^ 5 / (t ^ 2 * Real.sqrt t) := by
    simpa [r] using
      abs_expNumObsRem_sub_neg_quintic_le
        (φ := φ) (hφ := hφ) (ht := ht0) (u := u) huφ

  have hr_neg :
      |r (-u)| ≤ hφ.toObservableTensorApprox.jet_const * ‖u‖ ^ 4 / t ^ 2 := by
    simpa [r, norm_neg] using
      abs_expNumObsRem_local_le
        (φ := φ) (a := (0 : ι → ℝ))
        (hφ := hφ.toObservableTensorApprox) (ht := ht0) (u := -u) huφ_neg

  have hs_diff :
      |s u - s (-u)|
        ≤ (2 * C3) * ‖u‖ ^ 3 / Real.sqrt t
          + hV.Q_const * ‖u‖ ^ 5 / (t * Real.sqrt t) := by
    -- TODO:
    -- use `abs_rescaledPerturbation_sub_neg_quintic_le`
    -- and the bound on `expPotCubic`
    sorry

  have hexp_diff :
      |Real.exp (-(s u)) - Real.exp (-(s (-u)))|
        ≤ |s u - s (-u)| * max (Real.exp (-(s u))) (Real.exp (-(s (-u)))) := by
    -- TODO: mean value / standard exponential-difference estimate
    sorry

  -- Term A: odd observable remainder difference => `O(‖u‖^6 / t)`.
  have hA :
      |gaussianWeight H u * (t * Real.sqrt t * dot b u)
          * ((r u - r (-u)) * Real.exp (-(s u)))|
        ≤ K₁ * ‖u‖ ^ 6 / t := by
    -- TODO: `abs_mul`, `hdot`, `hr_diff`, `h_weight_u_le_one`
    sorry

  -- Term B before local absorption:
  -- cubic-potential piece gives `‖u‖^8 / t`,
  -- quintic-potential remainder gives `‖u‖^10 / t^2`.
  have hB_pre :
      |gaussianWeight H u * (t * Real.sqrt t * dot b u)
          * (r (-u) * (Real.exp (-(s u)) - Real.exp (-(s (-u)))))|
        ≤ K₂ * ‖u‖ ^ 8 / t + K₃ * ‖u‖ ^ 10 / t ^ 2 := by
    -- TODO: `abs_mul`, `hr_neg`, `hexp_diff`, `hs_diff`, `h_weight_max_le_one`
    sorry

  have hu_sq :
      ‖u‖ ^ 2 ≤ hV.toPotentialTensorApprox.jet_radius ^ 2 * t := by
    -- TODO: from `huV`
    sorry

  have hB :
      |gaussianWeight H u * (t * Real.sqrt t * dot b u)
          * (r (-u) * (Real.exp (-(s u)) - Real.exp (-(s (-u)))))|
        ≤ (K₂ + K₃ * hV.toPotentialTensorApprox.jet_radius ^ 2) * ‖u‖ ^ 8 / t := by
    -- TODO: absorb `‖u‖^10 / t^2` using `hu_sq`
    sorry

  have h_poly_pack :
      K₁ * ‖u‖ ^ 6 / t
        + (K₂ + K₃ * hV.toPotentialTensorApprox.jet_radius ^ 2) * ‖u‖ ^ 8 / t
      ≤ (K₁ + K₂ + K₃ * hV.toPotentialTensorApprox.jet_radius ^ 2 + 1) / t
          * (1 + ‖u‖ ^ 8) := by
    -- TODO: elementary packaging; use `‖u‖^6 ≤ 1 + ‖u‖^8`
    sorry

  calc
    |gaussianWeight H u * (t * Real.sqrt t * dot b u)
        * (r u * Real.exp (-(s u)) - r (-u) * Real.exp (-(s (-u))))|
      = |gaussianWeight H u * (t * Real.sqrt t * dot b u)
          * ((r u - r (-u)) * Real.exp (-(s u))
            + r (-u) * (Real.exp (-(s u)) - Real.exp (-(s (-u)))))| := by
          rw [h_split]
    _ ≤ |gaussianWeight H u * (t * Real.sqrt t * dot b u)
            * ((r u - r (-u)) * Real.exp (-(s u)))|
        + |gaussianWeight H u * (t * Real.sqrt t * dot b u)
            * (r (-u) * (Real.exp (-(s u)) - Real.exp (-(s (-u)))))| := by
          exact abs_add _ _
    _ ≤ K₁ * ‖u‖ ^ 6 / t
        + (K₂ + K₃ * hV.toPotentialTensorApprox.jet_radius ^ 2) * ‖u‖ ^ 8 / t := by
          gcongr
    _ ≤ (K₁ + K₂ + K₃ * hV.toPotentialTensorApprox.jet_radius ^ 2 + 1) / t
          * (1 + ‖u‖ ^ 8) := h_poly_pack
```

---

## 2. `abs_bulkErrA_tail_le`

### Important note
As written, this tail statement only uses `hφ.jet_radius`. That is fine for a **standalone** tail bound, but for the **assembly** I recommend using
```lean
R := min hφ.toObservableTensorApprox.jet_radius hV.toPotentialTensorApprox.jet_radius
```
instead. Otherwise the local/tail dichotomy is not exhaustive unless you know `hφ.jet_radius ≤ hV.jet_radius`.

Skeleton in your requested shape:

```lean
private lemma abs_bulkErrA_tail_le
    (V φ : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    (hφ : ObservableQuinticApprox φ (0 : ι → ℝ)) :
    ∃ K_tail : ℝ, ∃ M : ℕ, 0 ≤ K_tail ∧ ∀ t : ℝ, 1 ≤ t →
      ∀ u : ι → ℝ,
        hφ.toObservableTensorApprox.jet_radius * Real.sqrt t < ‖u‖ →
        |bulkErrASymmIntegrand V φ H b hφ.toObservableTensorApprox t u|
          ≤ K_tail * (1 + ‖u‖ ^ M) := by
  classical

  let R : ℝ := hφ.toObservableTensorApprox.jet_radius
  let Cb : ℝ := ‖b‖

  obtain ⟨Cglob, N, hCglob_nonneg, hglob⟩ :=
    abs_expNumObsRem_global_le
      (φ := φ) (a := (0 : ι → ℝ)) (hφ := hφ.toObservableTensorApprox)

  let K₀ : ℝ := 2 * Cb * Cglob / R ^ 3

  refine ⟨K₀ + 1, N + 4, by positivity, ?_⟩
  intro t ht u hu_tail

  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hR_pos : 0 < R := by
    -- TODO: jet-radius positivity
    sorry
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0

  have hdot :
      |dot b u| ≤ Cb * ‖u‖ := by
    -- TODO
    sorry

  have h_t32 :
      t * Real.sqrt t ≤ ‖u‖ ^ 3 / R ^ 3 := by
    -- TODO:
    -- from `R * sqrt t < ‖u‖`, cube both sides
    sorry

  have hr_u :
      |expNumObsRem φ 0 hφ.toObservableTensorApprox t u|
        ≤ Cglob * (1 + ‖u‖ ^ N) := by
    simpa using hglob t ht u

  have hr_neg :
      |expNumObsRem φ 0 hφ.toObservableTensorApprox t (-u)|
        ≤ Cglob * (1 + ‖u‖ ^ N) := by
    simpa [norm_neg] using hglob t ht (-u)

  have hweight_u_le_one :
      gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u)) ≤ 1 := by
    -- TODO
    sorry

  have hweight_neg_le_one :
      gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t (-u))) ≤ 1 := by
    -- TODO
    sorry

  have h_expand :
      bulkErrASymmIntegrand V φ H b hφ.toObservableTensorApprox t u
        =
      (t * Real.sqrt t * dot b u
          * expNumObsRem φ 0 hφ.toObservableTensorApprox t u
          * gaussianWeight H u
          * Real.exp (-(rescaledPerturbation V H t u)))
      +
      (t * Real.sqrt t * dot b (-u)
          * expNumObsRem φ 0 hφ.toObservableTensorApprox t (-u)
          * gaussianWeight H u
          * Real.exp (-(rescaledPerturbation V H t (-u)))) := by
    -- TODO: unfold and simp
    sorry

  rw [h_expand]

  have hterm_u :
      |t * Real.sqrt t * dot b u
          * expNumObsRem φ 0 hφ.toObservableTensorApprox t u
          * gaussianWeight H u
          * Real.exp (-(rescaledPerturbation V H t u))|
      ≤ K₀ / 2 * (‖u‖ ^ 4 + ‖u‖ ^ (N + 4)) := by
    -- TODO:
    -- `t*sqrt t ≤ ‖u‖^3 / R^3`, `|dot b u| ≤ Cb*‖u‖`, global remainder growth,
    -- weight factor `≤ 1`
    sorry

  have hterm_neg :
      |t * Real.sqrt t * dot b (-u)
          * expNumObsRem φ 0 hφ.toObservableTensorApprox t (-u)
          * gaussianWeight H u
          * Real.exp (-(rescaledPerturbation V H t (-u)))|
      ≤ K₀ / 2 * (‖u‖ ^ 4 + ‖u‖ ^ (N + 4)) := by
    -- TODO: same as previous term
    sorry

  have h_pack :
      K₀ / 2 * (‖u‖ ^ 4 + ‖u‖ ^ (N + 4))
        + K₀ / 2 * (‖u‖ ^ 4 + ‖u‖ ^ (N + 4))
      ≤ (K₀ + 1) * (1 + ‖u‖ ^ (N + 4)) := by
    -- TODO: absorb `‖u‖^4` into `1 + ‖u‖^(N+4)`
    sorry

  calc
    |(t * Real.sqrt t * dot b u
          * expNumObsRem φ 0 hφ.toObservableTensorApprox t u
          * gaussianWeight H u
          * Real.exp (-(rescaledPerturbation V H t u)))
      +
      (t * Real.sqrt t * dot b (-u)
          * expNumObsRem φ 0 hφ.toObservableTensorApprox t (-u)
          * gaussianWeight H u
          * Real.exp (-(rescaledPerturbation V H t (-u))))|
      ≤ |t * Real.sqrt t * dot b u
            * expNumObsRem φ 0 hφ.toObservableTensorApprox t u
            * gaussianWeight H u
            * Real.exp (-(rescaledPerturbation V H t u))|
        + |t * Real.sqrt t * dot b (-u)
            * expNumObsRem φ 0 hφ.toObservableTensorApprox t (-u)
            * gaussianWeight H u
            * Real.exp (-(rescaledPerturbation V H t (-u)))| := by
          exact abs_add _ _
    _ ≤ K₀ / 2 * (‖u‖ ^ 4 + ‖u‖ ^ (N + 4))
        + K₀ / 2 * (‖u‖ ^ 4 + ‖u‖ ^ (N + 4)) := by
          gcongr
    _ ≤ (K₀ + 1) * (1 + ‖u‖ ^ (N + 4)) := h_pack
```

---

## 3. `abs_integral_bulkErrA_le`

Here is the assembly skeleton I recommend.

### Key point
This is much cleaner if you use **weighted** local/tail pointwise bounds.  
So below I insert two local helper claims:

- `hlocalW`
- `htailW`

These are just the weighted versions of Lemmas 1 and 2:
same proof, but **do not** finish by throwing away the coercive factor with `≤ 1`.

```lean
private lemma abs_integral_bulkErrA_le
    (V φ : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    (hφ : ObservableQuinticApprox φ (0 : ι → ℝ)) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |∫ u : ι → ℝ,
          bulkErrA φ b hφ.toObservableTensorApprox t u
          * gaussianWeight H u
          * Real.exp (-(rescaledPerturbation V H t u))|
        ≤ K / t := by
  classical

  let R : ℝ :=
    min hφ.toObservableTensorApprox.jet_radius hV.toPotentialTensorApprox.jet_radius
  have hR_pos : 0 < R := by
    -- TODO
    sorry

  let c : ℝ := hV.toPotentialApprox.coercive_const
  have hc_pos : 0 < c := hV.toPotentialApprox.coercive_const_pos

  obtain ⟨Kloc, hKloc_nonneg, hloc⟩ :=
    abs_bulkErrA_local_le
      (V := V) (φ := φ) (H := H) (b := b) (hV := hV) (hφ := hφ)

  -- If your current tail lemma is stated with `hφ.jet_radius`, either:
  --   * restate it with `R`, or
  --   * use it only when `R = hφ.jet_radius`.
  obtain ⟨Ktail, M, hKtail_nonneg, htail⟩ :=
    abs_bulkErrA_tail_le
      (V := V) (φ := φ) (H := H) (b := b) (hV := hV) (hφ := hφ)

  have h_int0 :
      Integrable (fun u : ι → ℝ => ‖u‖ ^ (0 : ℕ) * Real.exp (-(c * ‖u‖ ^ 2))) := by
    simpa using integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc_pos 0

  have h_int8 :
      Integrable (fun u : ι → ℝ => ‖u‖ ^ (8 : ℕ) * Real.exp (-(c * ‖u‖ ^ 2))) := by
    simpa using integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc_pos 8

  have h_int2 :
      Integrable (fun u : ι → ℝ => ‖u‖ ^ (2 : ℕ) * Real.exp (-(c * ‖u‖ ^ 2))) := by
    simpa using integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc_pos 2

  have h_intM2 :
      Integrable (fun u : ι → ℝ => ‖u‖ ^ (M + 2) * Real.exp (-(c * ‖u‖ ^ 2))) := by
    simpa using integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hc_pos (M + 2)

  have h_int_local_model :
      Integrable (fun u : ι → ℝ => (1 + ‖u‖ ^ 8) * Real.exp (-(c * ‖u‖ ^ 2))) := by
    -- TODO: package `h_int0.add h_int8`
    sorry

  have h_int_tail_model :
      Integrable (fun u : ι → ℝ => (‖u‖ ^ 2 + ‖u‖ ^ (M + 2)) * Real.exp (-(c * ‖u‖ ^ 2))) := by
    -- TODO: package `h_int2.add h_intM2`
    sorry

  let Iloc : ℝ := ∫ u : ι → ℝ, (1 + ‖u‖ ^ 8) * Real.exp (-(c * ‖u‖ ^ 2))
  let Itail : ℝ := ∫ u : ι → ℝ, (‖u‖ ^ 2 + ‖u‖ ^ (M + 2)) * Real.exp (-(c * ‖u‖ ^ 2))

  refine ⟨(Kloc * Iloc + (Ktail / R ^ 2) * Itail) / 2, 1, le_rfl, ?_⟩
  intro t ht

  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hsqrt_nonneg : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t

  -- Weighted local bound: same proof as Lemma 1, but keep the coercive exponential.
  have hlocalW :
      ∀ u : ι → ℝ,
        ‖u‖ ≤ R * Real.sqrt t →
        |bulkErrASymmIntegrand V φ H b hφ.toObservableTensorApprox t u|
          ≤ (Kloc / t) * (1 + ‖u‖ ^ 8) * Real.exp (-(c * ‖u‖ ^ 2)) := by
    intro u hu
    have huφ :
        ‖u‖ ≤ hφ.toObservableTensorApprox.jet_radius * Real.sqrt t := by
      -- TODO: from `hu` and `R ≤ ...`
      sorry
    have huV :
        ‖u‖ ≤ hV.toPotentialTensorApprox.jet_radius * Real.sqrt t := by
      -- TODO: from `hu` and `R ≤ ...`
      sorry
    -- TODO:
    -- either:
    --   (1) prove a weighted analogue of Lemma 1 and use it here,
    -- or
    --   (2) inline the last part of the Lemma 1 proof, but use
    --       `rescaled_weight_le_coercive` instead of `≤ 1`.
    sorry

  -- Weighted tail bound: same proof as Lemma 2, but keep the coercive exponential.
  have htailW :
      ∀ u : ι → ℝ,
        R * Real.sqrt t < ‖u‖ →
        |bulkErrASymmIntegrand V φ H b hφ.toObservableTensorApprox t u|
          ≤ Ktail * (1 + ‖u‖ ^ M) * Real.exp (-(c * ‖u‖ ^ 2)) := by
    intro u hu
    -- TODO: weighted analogue of Lemma 2, using `R`
    sorry

  let majorant : (ι → ℝ) → ℝ := fun u =>
    (Kloc / t) * (1 + ‖u‖ ^ 8) * Real.exp (-(c * ‖u‖ ^ 2))
      + (Ktail / (R ^ 2 * t)) * (‖u‖ ^ 2 + ‖u‖ ^ (M + 2))
          * Real.exp (-(c * ‖u‖ ^ 2))

  have h_major_nonneg : ∀ u : ι → ℝ, 0 ≤ majorant u := by
    intro u
    dsimp [majorant]
    positivity

  have h_pointwise :
      ∀ u : ι → ℝ,
        |bulkErrASymmIntegrand V φ H b hφ.toObservableTensorApprox t u|
          ≤ majorant u := by
    intro u
    by_cases hu : ‖u‖ ≤ R * Real.sqrt t
    · have h1 := hlocalW u hu
      have h2 : 0 ≤ (Ktail / (R ^ 2 * t)) * (‖u‖ ^ 2 + ‖u‖ ^ (M + 2))
          * Real.exp (-(c * ‖u‖ ^ 2)) := by positivity
      exact le_trans h1 <| by
        dsimp [majorant]
        nlinarith
    · have hu' : R * Real.sqrt t < ‖u‖ := lt_of_not_ge hu
      have h1 := htailW u hu'
      have h_absorb :
          Ktail * (1 + ‖u‖ ^ M) * Real.exp (-(c * ‖u‖ ^ 2))
            ≤ (Ktail / (R ^ 2 * t)) * (‖u‖ ^ 2 + ‖u‖ ^ (M + 2))
                * Real.exp (-(c * ‖u‖ ^ 2)) := by
        -- TODO:
        -- from `1 ≤ ‖u‖^2 / (R^2 * t)` on the tail
        -- then multiply by nonnegative factors
        sorry
      have h2 : 0 ≤ (Kloc / t) * (1 + ‖u‖ ^ 8) * Real.exp (-(c * ‖u‖ ^ 2)) := by
        positivity
      exact le_trans h1 <| by
        dsimp [majorant]
        nlinarith

  have h_int_major_local :
      Integrable (fun u : ι → ℝ =>
        (Kloc / t) * (1 + ‖u‖ ^ 8) * Real.exp (-(c * ‖u‖ ^ 2))) := by
    -- TODO: constant multiple of `h_int_local_model`
    sorry

  have h_int_major_tail :
      Integrable (fun u : ι → ℝ =>
        (Ktail / (R ^ 2 * t)) * (‖u‖ ^ 2 + ‖u‖ ^ (M + 2))
          * Real.exp (-(c * ‖u‖ ^ 2))) := by
    -- TODO: constant multiple of `h_int_tail_model`
    sorry

  have h_int_major : Integrable majorant := by
    -- NOTE: Pi.add gotcha: give the integrability witness for the one-lambda function.
    -- TODO
    sorry

  have h_int_symm :
      Integrable (fun u : ι → ℝ =>
        bulkErrASymmIntegrand V φ H b hφ.toObservableTensorApprox t u) := by
    -- TODO: dominate by `majorant`; use `Integrable.mono'`
    sorry

  have h_symm_int :
      |∫ u : ι → ℝ, bulkErrASymmIntegrand V φ H b hφ.toObservableTensorApprox t u|
        ≤ ∫ u : ι → ℝ, majorant u := by
    calc
      _ ≤ ∫ u : ι → ℝ,
            |bulkErrASymmIntegrand V φ H b hφ.toObservableTensorApprox t u| := by
          simpa using
            norm_integral_le_integral_norm
              (f := fun u : ι → ℝ =>
                bulkErrASymmIntegrand V φ H b hφ.toObservableTensorApprox t u)
      _ ≤ ∫ u : ι → ℝ, majorant u := by
          refine integral_mono_ae ?_
          exact Filter.Eventually.of_forall h_pointwise

  have h_major_eval :
      ∫ u : ι → ℝ, majorant u
        ≤ (Kloc * Iloc + (Ktail / R ^ 2) * Itail) / t := by
    -- TODO:
    -- expand `majorant`, pull out constants, rewrite with `Iloc`, `Itail`
    -- use `t > 0`
    sorry

  have hsymm :=
    bulkErrA_symmetric
      (V := V) (φ := φ) (H := H) (b := b)
      (hφ := hφ.toObservableTensorApprox) (t := t)

  have h_two :
      2 * |∫ u : ι → ℝ,
            bulkErrA φ b hφ.toObservableTensorApprox t u
              * gaussianWeight H u
              * Real.exp (-(rescaledPerturbation V H t u))|
        =
      |∫ u : ι → ℝ, bulkErrASymmIntegrand V φ H b hφ.toObservableTensorApprox t u| := by
    -- TODO: take `abs` of `hsymm`; simplify `|2 * x| = 2 * |x|`
    sorry

  have h_final_symm :
      2 * |∫ u : ι → ℝ,
            bulkErrA φ b hφ.toObservableTensorApprox t u
              * gaussianWeight H u
              * Real.exp (-(rescaledPerturbation V H t u))|
        ≤ (Kloc * Iloc + (Ktail / R ^ 2) * Itail) / t := by
    calc
      _ = |∫ u : ι → ℝ, bulkErrASymmIntegrand V φ H b hφ.toObservableTensorApprox t u| := h_two
      _ ≤ ∫ u : ι → ℝ, majorant u := h_symm_int
      _ ≤ (Kloc * Iloc + (Ktail / R ^ 2) * Itail) / t := h_major_eval

  have htwo_pos : (0 : ℝ) < 2 := by norm_num

  have h_final :
      |∫ u : ι → ℝ,
          bulkErrA φ b hφ.toObservableTensorApprox t u
            * gaussianWeight H u
            * Real.exp (-(rescaledPerturbation V H t u))|
        ≤ ((Kloc * Iloc + (Ktail / R ^ 2) * Itail) / 2) / t := by
    -- TODO: divide the previous inequality by `2`
    sorry

  simpa [Iloc, Itail, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h_final
```

---

## What I would change if this were my file

I would introduce two tiny helper lemmas:

```lean
private lemma abs_bulkErrASymmIntegrand_local_weighted_le ...
private lemma abs_bulkErrASymmIntegrand_tail_weighted_le ...
```

with conclusions

```lean
≤ K_loc / t * (1 + ‖u‖^8) * Real.exp (-(c * ‖u‖^2))
```

and

```lean
≤ K_tail * (1 + ‖u‖^M) * Real.exp (-(c * ‖u‖^2))
```

Then:

- Lemma 1/2 as you wrote become optional/crude corollaries by dropping the exponential with `≤ 1`.
- Lemma 3 becomes almost identical to your Lemma B assembly.

So, to your direct question:

> should the pointwise bound on `bulkErrASymmIntegrand` include the `exp(-c·‖u‖²)` factor?

**Yes**, if the lemma is literally about `bulkErrASymmIntegrand` and you want it to feed the integral bound cleanly.  
If you want a polynomial-only statement, it should be for the **unsmeared symmetrized core**, not the full integrand.

If you want, I can also write the two weighted helper lemma statements/skeletons explicitly; that would likely make the final sorry much shorter than forcing the polynomial-only versions into the integration step.