Below is a direct paste attempt.  
If your file uses slightly different names, the only likely renames are:
`abs_gaussianWeight_mul_exp_sub_one_local_le`,
`abs_gaussianWeight_mul_exp_sub_one_tail_le`,
and `hGauss.int_4moment (k := 6)`.

```lean
private lemma expNumErr₂_bound
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hGauss : LaplaceCov4MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |expNumErr₂ V φ a H hφ t| ≤ K / t ^ 2 := by
  obtain ⟨Cs, T₁, hT₁, hlocal⟩ :=
    abs_gaussianWeight_mul_exp_sub_one_local_le
      (V := V) (H := H) (Hinv := Hinv) hV hGauss
  obtain ⟨Ct, T₂, hT₂, htail⟩ :=
    abs_gaussianWeight_mul_exp_sub_one_tail_le
      (V := V) (H := H) (Hinv := Hinv) hV hGauss

  let Cφ : ℝ := ‖hφ.Φ‖ / 6
  let f₁ : (ι → ℝ) → ℝ :=
    fun u => ‖u‖ ^ (6 : ℕ) * Real.exp (-(hV.c / 4) * ‖u‖ ^ (2 : ℕ))
  let f₂ : (ι → ℝ) → ℝ :=
    fun u => ‖u‖ ^ (6 : ℕ) * gaussianWeight H u
  let I₁ : ℝ := ∫ u : ι → ℝ, f₁ u
  let I₂ : ℝ := ∫ u : ι → ℝ, f₂ u
  let K : ℝ := Cφ * (|Cs| * I₁ + |Ct| * I₂)
  let T₀ : ℝ := max 1 (max T₁ T₂)

  refine ⟨K, T₀, by
    dsimp [T₀]
    exact le_max_left _ _, ?_⟩
  intro t ht

  have h1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have h12 : max T₁ T₂ ≤ t := le_trans (le_max_right _ _) ht
  have ht1 : T₁ ≤ t := le_trans (le_max_left _ _) h12
  have ht2 : T₂ ≤ t := le_trans (le_max_right _ _) h12
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) h1

  have hΦdiag :
      ∀ u : ι → ℝ, |hφ.Φ (fun _ : Fin 3 => u)| ≤ ‖hφ.Φ‖ * ‖u‖ ^ (3 : ℕ) := by
    intro u
    simpa [Fin.prod_univ_three, pow_two, pow_succ, mul_assoc, mul_left_comm, mul_comm]
      using (hφ.Φ.le_opNorm (fun _ : Fin 3 => u))

  have hcubic :
      ∀ u : ι → ℝ,
        |expNumCubic φ a hφ t u| ≤ (Cφ / (t * Real.sqrt t)) * ‖u‖ ^ (3 : ℕ) := by
    intro u
    unfold expNumCubic
    dsimp [Cφ]
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)]
    have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    have hcoef : |(Real.sqrt t)⁻¹ / t| = 1 / (t * Real.sqrt t) := by
      rw [abs_of_pos]
      · field_simp [ht0.ne', hsqrt.ne']
        ring
      · positivity
    rw [hcoef]
    have hΦu := hΦdiag u
    have hnn : 0 ≤ (1 / (t * Real.sqrt t) : ℝ) := by positivity
    have hnn' : 0 ≤ (1 / 6 : ℝ) := by norm_num
    gcongr
    exact hΦu

  have hsimpCs :
      (Cφ / (t * Real.sqrt t)) * (|Cs| / Real.sqrt t) = Cφ * |Cs| / t ^ 2 := by
    have hsqrt : Real.sqrt t ≠ 0 := by positivity
    field_simp [pow_two, ht0.ne', hsqrt]
    ring
  have hsimpCt :
      (Cφ / (t * Real.sqrt t)) * (|Ct| / Real.sqrt t) = Cφ * |Ct| / t ^ 2 := by
    have hsqrt : Real.sqrt t ≠ 0 := by positivity
    field_simp [pow_two, ht0.ne', hsqrt]
    ring

  have hpow6 : ∀ u : ι → ℝ, ‖u‖ ^ (3 : ℕ) * ‖u‖ ^ (3 : ℕ) = ‖u‖ ^ (6 : ℕ) := by
    intro u
    rw [← pow_add]
    norm_num

  have hI₁_int : Integrable f₁ := by
    dsimp [f₁]
    simpa [pow_two] using
      integrable_norm_pow_mul_exp_neg_mul_norm_sq
        (α := (ι → ℝ)) (n := 6) (a := hV.c / 4) (by positivity)

  have hI₂_int : Integrable f₂ := by
    dsimp [f₂]
    simpa using hGauss.int_4moment (k := (6 : ℕ)) (by norm_num)

  have hdom :
      ∀ u : ι → ℝ,
        ‖expNumCubic φ a hφ t u
            * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
            * gaussianWeight H u‖
          ≤ (Cφ * |Cs| / t ^ 2) * f₁ u + (Cφ * |Ct| / t ^ 2) * f₂ u := by
    intro u
    by_cases hu : ‖u‖ ≤ hV.δ * Real.sqrt t
    · have hloc :=
          le_trans (hlocal t ht1 u hu) (by
            have : Cs ≤ |Cs| := le_abs_self Cs
            gcongr)
      calc
        ‖expNumCubic φ a hφ t u
            * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
            * gaussianWeight H u‖
            = |expNumCubic φ a hφ t u|
              * |(Real.exp (-(rescaledPerturbation V H t u)) - 1) * gaussianWeight H u| := by
                rw [norm_eq_abs, mul_assoc, abs_mul]
        _ ≤ ((Cφ / (t * Real.sqrt t)) * ‖u‖ ^ (3 : ℕ)) *
              ((|Cs| / Real.sqrt t) * ‖u‖ ^ (3 : ℕ)
                * Real.exp (-(hV.c / 4) * ‖u‖ ^ (2 : ℕ))) := by
              gcongr
              · exact hcubic u
              · exact hloc
        _ = (Cφ * |Cs| / t ^ 2) * f₁ u := by
              dsimp [f₁]
              rw [hpow6 u, hsimpCs]
              ring
        _ ≤ (Cφ * |Cs| / t ^ 2) * f₁ u + (Cφ * |Ct| / t ^ 2) * f₂ u := by
              positivity
    · have htail' : hV.δ * Real.sqrt t ≤ ‖u‖ := le_of_not_ge hu
      have htl :=
          le_trans (htail t ht2 u htail') (by
            have : Ct ≤ |Ct| := le_abs_self Ct
            gcongr)
      calc
        ‖expNumCubic φ a hφ t u
            * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
            * gaussianWeight H u‖
            = |expNumCubic φ a hφ t u|
              * |(Real.exp (-(rescaledPerturbation V H t u)) - 1) * gaussianWeight H u| := by
                rw [norm_eq_abs, mul_assoc, abs_mul]
        _ ≤ ((Cφ / (t * Real.sqrt t)) * ‖u‖ ^ (3 : ℕ)) *
              ((|Ct| / Real.sqrt t) * ‖u‖ ^ (3 : ℕ) * gaussianWeight H u) := by
              gcongr
              · exact hcubic u
              · exact htl
        _ = (Cφ * |Ct| / t ^ 2) * f₂ u := by
              dsimp [f₂]
              rw [hpow6 u, hsimpCt]
              ring
        _ ≤ (Cφ * |Cs| / t ^ 2) * f₁ u + (Cφ * |Ct| / t ^ 2) * f₂ u := by
              positivity

  have hDomInt :
      Integrable (fun u : ι → ℝ =>
        (Cφ * |Cs| / t ^ 2) * f₁ u + (Cφ * |Ct| / t ^ 2) * f₂ u) := by
    exact (hI₁_int.const_mul _).add (hI₂_int.const_mul _)

  have hmain :=
    norm_integral_le_of_norm_le hDomInt (Filter.Eventually.of_forall hdom)

  calc
    |expNumErr₂ V φ a H hφ t|
        = ‖∫ u : ι → ℝ,
            expNumCubic φ a hφ t u
              * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
              * gaussianWeight H u‖ := by
            simp [expNumErr₂, Real.norm_eq_abs]
    _ ≤ ∫ u : ι → ℝ,
          (Cφ * |Cs| / t ^ 2) * f₁ u + (Cφ * |Ct| / t ^ 2) * f₂ u := hmain
    _ = (Cφ * |Cs| / t ^ 2) * I₁ + (Cφ * |Ct| / t ^ 2) * I₂ := by
          dsimp [I₁, I₂]
          rw [integral_add, integral_const_mul, integral_const_mul]
          · exact (hI₁_int.const_mul _)
          · exact (hI₂_int.const_mul _)
    _ = K / t ^ 2 := by
          dsimp [K]
          field_simp [pow_two, ht0.ne']
          ring
```

If you want, I can also give a version that avoids the `integrable_norm_pow_mul_exp_neg_mul_norm_sq` line and instead uses whatever sixth-moment local-envelope lemma you already proved in `CovarianceSharp.lean`.