Best choice: **(a)**.  
Keep `abs_integral_bulkErrA_le` as the asymptotic/bound theorem, and add a small private helper

```lean
integrable_bulkErrA_mul_rescaled_weight
```

proved from the same polynomial-dominance estimate you already use in `abs_integral_bulkErrA_le`.

I would **not** refactor the asymptotic theorem unless several downstream assemblers need the witness. If you do refactor, the clean signature is:

```lean
private theorem abs_integral_bulkErrA_le'
    ... :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ t : ℝ, T₀ ≤ t →
        Integrable (fun u : ι → ℝ =>
          bulkErrA φ b hφ.toObservableTensorApprox t u *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))) ∧
        |∫ u : ι → ℝ,
            bulkErrA φ b hφ.toObservableTensorApprox t u *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u))|
          ≤ K / t
```

But I’d still keep it separate.

---

## Step 3 helper: recommended shape

This is the pattern you asked for: `Integrable.mono'` + continuity + polynomial Gaussian dominance.

```lean
private theorem integrable_bulkErrA_mul_rescaled_weight
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    (hφ : ObservableQuinticApprox φ (0 : ι → ℝ))
    (hGauss : LaplaceCov6MomentHypotheses H Hinv)
    {t : ℝ} (ht : 1 ≤ t) :
    Integrable (fun u : ι → ℝ =>
      bulkErrA φ b hφ.toObservableTensorApprox t u *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) := by
  let f : (ι → ℝ) → ℝ := fun u =>
    bulkErrA φ b hφ.toObservableTensorApprox t u *
      gaussianWeight H u *
      Real.exp (-(rescaledPerturbation V H t u))

  have hcont : Continuous f := by
    -- patch exact lemma name
    simpa [f, mul_assoc] using
      continuous_bulkErrA_mul_rescaled_weight
        (φ := φ) (H := H) (b := b)
        hφ.toObservableTensorApprox t

  -- Stronger pointwise bound used in your bulk theorem proof.
  -- If you don't already have it as a lemma, extract it once.
  obtain ⟨C, N, hC_nonneg, hdom⟩ :=
    abs_bulkErrA_mul_rescaled_weight_le_polynomialGaussian
      (V := V) (φ := φ) (H := H) (Hinv := Hinv) (b := b)
      hV hφ hGauss ht
  -- hdom :
  --   ∀ u, ‖f u‖ ≤ C * (1 + ‖u‖ ^ N) * Real.exp (-hGauss.c * ‖u‖^2)

  have hInt_dom :
      Integrable (fun u : ι → ℝ =>
        C * (1 + ‖u‖ ^ N) * Real.exp (-hGauss.coerciveConst * ‖u‖ ^ 2)) := by
    -- patch exact lemma / field names
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      integrable_polynomial_mul_gaussian
        (c := hGauss.coerciveConst)
        hGauss.coerciveConst_pos (C := C) (N := N)

  exact Integrable.mono'
    hcont.aestronglyMeasurable
    hInt_dom
    (Filter.Eventually.of_forall hdom)
```

If you don’t yet have
`abs_bulkErrA_mul_rescaled_weight_le_polynomialGaussian`,
that’s the one lemma worth extracting from the bulk proof, not the whole asymptotic theorem signature.

---

## Main theorem assembly skeleton

Below is the clean structure. Exact field names in `hGauss` / coercivity args may need patching.

```lean
private theorem rescaledIntegral_cross_linear_connected_asymptotic
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    (hφ : ObservableQuinticApprox φ (0 : ι → ℝ))
    (hGauss : LaplaceCov6MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |t * Real.sqrt t *
          (∫ u : ι → ℝ, dot b u *
              expCovPhiConn V φ H Hinv (0 : ι → ℝ)
                hV.toPotentialTensorApprox hφ.toObservableTensorApprox t u *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))
        - ((1 / 2 : ℝ) * dot (Hinv b)
              (tensorContractMatrix hφ.toObservableTensorApprox.Φ Hinv)
          - (1 / 2 : ℝ) * dot b
              (Hinv (hφ.toObservableTensorApprox.A
                (Hinv (tensorContractMatrix hV.T Hinv))))
          - (1 / 2 : ℝ) * dot (Hinv b)
              (tensorContractMatrix hV.T
                (Hinv.comp (hφ.toObservableTensorApprox.A.comp Hinv))))
          * rescaledPartition V t|
        ≤ K / t := by
  obtain ⟨KE, TE, hE⟩ :=
    rescaledIntegral_evenCross_asymptotic
      V H Hinv b hφ.Φ hV.toPotentialJetApprox
      hφ.Φ_symm hGauss.toLaplaceCov4MomentHypotheses

  obtain ⟨KO, TO, hO⟩ :=
    rescaledIntegral_oddCross_asymptotic
      V H Hinv b hφ.A hV hφ.A_symm hGauss

  obtain ⟨KB, TB, hB⟩ :=
    abs_integral_bulkErrA_le V φ H b hV hφ

  refine ⟨KE + KO + KB, max 1 (max TE (max TO TB)), le_max_left _ _, ?_⟩
  intro t ht

  have ht1 : (1 : ℝ) ≤ t := by
    exact le_trans (le_max_left _ _) ht

  have ht_pos : 0 < t := by
    linarith

  have hTE : TE ≤ t := by
    exact le_trans
      (le_trans (le_max_left _ _) (le_max_right _ _))
      ht

  have hTO : TO ≤ t := by
    exact le_trans
      (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
      ht

  have hTB : TB ≤ t := by
    exact le_trans
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
      ht

  let w : (ι → ℝ) → ℝ := fun u =>
    gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))

  let f : (ι → ℝ) → ℝ := fun u =>
    dot b u *
      expCovPhiConn V φ H Hinv (0 : ι → ℝ)
        hV.toPotentialTensorApprox hφ.toObservableTensorApprox t u *
      w u

  let fE : (ι → ℝ) → ℝ := fun u =>
    crossEvenKernel b hφ.Φ u * w u

  let fO : (ι → ℝ) → ℝ := fun u =>
    crossOddKernel hφ.A Hinv b u * w u

  let fB : (ι → ℝ) → ℝ := fun u =>
    bulkErrA φ b hφ.toObservableTensorApprox t u * w u

  let CE : ℝ :=
    (1 / 2 : ℝ) * dot (Hinv b)
      (tensorContractMatrix hφ.toObservableTensorApprox.Φ Hinv)

  let CO₁ : ℝ :=
    (1 / 2 : ℝ) * dot b
      (Hinv (hφ.toObservableTensorApprox.A
        (Hinv (tensorContractMatrix hV.T Hinv))))

  let CO₂ : ℝ :=
    (1 / 2 : ℝ) * dot (Hinv b)
      (tensorContractMatrix hV.T
        (Hinv.comp (hφ.toObservableTensorApprox.A.comp Hinv)))

  let D : ℝ := rescaledPartition V t

  have hIntE : Integrable fE := by
    -- patch exact auxiliary args from your existing setup
    simpa [fE, w, mul_assoc, mul_left_comm, mul_comm] using
      integrable_crossEvenKernel_mul_rescaled_weight
        V H Hinv b hφ.Φ
        hV.cubicControl hGauss.c_pos hGauss.coercive
        ht_pos

  have hIntO : Integrable fO := by
    simpa [fO, w, mul_assoc, mul_left_comm, mul_comm] using
      integrable_crossOddKernel_mul_rescaled_weight
        V H Hinv hφ.A b
        hV.cubicControl hGauss.c_pos hGauss.coercive
        ht_pos

  have hIntB : Integrable fB := by
    simpa [fB, w, mul_assoc, mul_left_comm, mul_comm] using
      integrable_bulkErrA_mul_rescaled_weight
        V φ H Hinv b hV hφ hGauss ht1

  have hPoint :
      ∀ u, (t * Real.sqrt t) * f u
        = fE u + (Real.sqrt t) * fO u + fB u := by
    intro u
    calc
      (t * Real.sqrt t) * f u
          = ((t * Real.sqrt t) *
              (dot b u *
                expCovPhiConn V φ H Hinv (0 : ι → ℝ)
                  hV.toPotentialTensorApprox hφ.toObservableTensorApprox t u)) * w u := by
              dsimp [f]
              ring
      _ = (crossEvenKernel b hφ.Φ u
            + Real.sqrt t * crossOddKernel hφ.A Hinv b u
            + bulkErrA φ b hφ.toObservableTensorApprox t u) * w u := by
            rw [cross_linear_connected_pointwise
              V φ H Hinv b
              hV.toPotentialTensorApprox hφ.toObservableTensorApprox
              ht_pos u]
      _ = fE u + (Real.sqrt t) * fO u + fB u := by
            dsimp [fE, fO, fB, w]
            ring

  have hIntScaled :
      Integrable (fun u => (t * Real.sqrt t) * f u) := by
    have hIntRhs :
        Integrable (fun u => fE u + (Real.sqrt t) * fO u + fB u) := by
      exact ((hIntE.add (hIntO.const_mul _)).add hIntB)
    exact hIntRhs.congr <|
      Filter.Eventually.of_forall (fun u => (hPoint u).symm)

  have hts_ne : t * Real.sqrt t ≠ 0 := by
    positivity

  have hIntF : Integrable f := by
    have h :=
      hIntScaled.const_mul ((t * Real.sqrt t)⁻¹)
    refine h.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro u
    field_simp [hts_ne]
    ring

  have hIntSO : Integrable (fun u => (Real.sqrt t) * fO u) := by
    exact hIntO.const_mul _

  have hIntegral :
      (t * Real.sqrt t) * (∫ u, f u)
        = (∫ u, fE u) + (Real.sqrt t) * (∫ u, fO u) + ∫ u, fB u := by
    calc
      (t * Real.sqrt t) * (∫ u, f u)
          = ∫ u, (t * Real.sqrt t) * f u := by
              symm
              simpa using
                (MeasureTheory.integral_const_mul (r := (t * Real.sqrt t)) (f := f))
      _ = ∫ u, (fE u + (Real.sqrt t) * fO u + fB u) := by
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.Eventually.of_forall hPoint
      _ = ∫ u, (fE u + (Real.sqrt t) * fO u) + ∫ u, fB u := by
            rw [MeasureTheory.integral_add (hIntE.add hIntSO) hIntB]
      _ = (∫ u, fE u + ∫ u, (Real.sqrt t) * fO u) + ∫ u, fB u := by
            rw [MeasureTheory.integral_add hIntE hIntSO]
      _ = (∫ u, fE u) + (Real.sqrt t) * (∫ u, fO u) + ∫ u, fB u := by
            rw [MeasureTheory.integral_const_mul]
            ring

  have hEven :
      |(∫ u, fE u) - CE * D| ≤ KE / t := by
    simpa [fE, w, CE, D, mul_assoc, mul_left_comm, mul_comm] using
      hE t hTE

  have hOdd :
      |(Real.sqrt t) * (∫ u, fO u) + (CO₁ + CO₂) * D| ≤ KO / t := by
    simpa [fO, w, CO₁, CO₂, D, mul_assoc, mul_left_comm, mul_comm] using
      hO t hTO

  have hBulk :
      |∫ u, fB u| ≤ KB / t := by
    simpa [fB, w, mul_assoc, mul_left_comm, mul_comm] using
      hB t hTB

  have hsplit :
      (t * Real.sqrt t) * (∫ u, f u) - (CE - CO₁ - CO₂) * D
        = ((∫ u, fE u) - CE * D)
          + (((Real.sqrt t) * (∫ u, fO u) + (CO₁ + CO₂) * D) + ∫ u, fB u) := by
    rw [hIntegral]
    ring

  have hfrac :
      KE / t + (KO / t + KB / t) = (KE + KO + KB) / t := by
    field_simp [ht_pos.ne']
    ring

  calc
    |(t * Real.sqrt t) * (∫ u, f u) - (CE - CO₁ - CO₂) * D|
        = |((∫ u, fE u) - CE * D)
            + (((Real.sqrt t) * (∫ u, fO u) + (CO₁ + CO₂) * D) + ∫ u, fB u)| := by
            rw [hsplit]
    _ ≤ |(∫ u, fE u) - CE * D|
          + |((Real.sqrt t) * (∫ u, fO u) + (CO₁ + CO₂) * D) + ∫ u, fB u| := by
          simpa using abs_add_le
            ((∫ u, fE u) - CE * D)
            (((Real.sqrt t) * (∫ u, fO u) + (CO₁ + CO₂) * D) + ∫ u, fB u)
    _ ≤ |(∫ u, fE u) - CE * D|
          + (|(Real.sqrt t) * (∫ u, fO u) + (CO₁ + CO₂) * D| + |∫ u, fB u|) := by
          gcongr
          simpa using abs_add_le
            ((Real.sqrt t) * (∫ u, fO u) + (CO₁ + CO₂) * D)
            (∫ u, fB u)
    _ ≤ KE / t + (KO / t + KB / t) := by
          gcongr
    _ = (KE + KO + KB) / t := hfrac
  -- final `simpa` to unfold `f, CE, CO₁, CO₂, D`
  -- if needed:
  -- simpa [f, w, CE, CO₁, CO₂, D, sub_eq_add_neg,
  --   mul_assoc, mul_left_comm, mul_comm]
```

---

## Practical advice

- **Do not inline** the bulk integrability proof into the main theorem.
- Add **one small helper**:
  - either `integrable_bulkErrA_mul_rescaled_weight`, or even better
  - a pointwise domination lemma like
    `abs_bulkErrA_mul_rescaled_weight_le_polynomialGaussian`.
- Then the main theorem stays purely “assembly”.

If you want, I can also give you a **more aggressive golfed version** of the theorem proof with the `max`-threshold facts and the final `simpa` already compressed.