import Laplace.OneD.GaussianMoments

/-!
# Gaussian tail bounds (Mill's ratio)

For the standard 1D Gaussian, we prove the elementary tail estimate:

  `∫ x in Ioi M, exp(-x²/2) dx ≤ exp(-M²/2) / M`,  for `M > 0`.

This is the technical input that makes Laplace localisation precise: away from
a neighbourhood of the minimum, the integrand of `exp(-tL(w))` is exponentially
suppressed in `t`.

## Strategy

1. **Antiderivative**: `∫_{Ioi M} x · exp(-x²/2) dx = exp(-M²/2)` (FTC-2 + limit).
2. **Pointwise bound**: for `x ≥ M ≥ 0`, `M · exp(-x²/2) ≤ x · exp(-x²/2)`.
3. **Integrate**: `M · ∫_{Ioi M} exp(-x²/2) dx ≤ exp(-M²/2)`. Divide by `M`.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.OneD

/-- The derivative of `-exp(-x²/2)` is `x · exp(-x²/2)`. -/
private lemma hasDerivAt_neg_exp_neg_sq_half (x : ℝ) :
    HasDerivAt (fun y : ℝ => -Real.exp (-(y ^ 2) / 2)) (x * Real.exp (-(x ^ 2) / 2)) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
    have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have := (hp.neg).div_const 2
    convert this using 1
    ring
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2) / 2))
      (-x * Real.exp (-(x ^ 2) / 2)) x := by
    have := (Real.hasDerivAt_exp (-(x ^ 2) / 2)).comp x h1
    simpa [mul_comm] using this
  convert h2.neg using 1
  ring

/-- `exp(-x²/2) → 0` as `x → ∞`. -/
private lemma tendsto_exp_neg_sq_half_atTop :
    Tendsto (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
    tendsto_pow_atTop (n := 2) (by norm_num : 2 ≠ 0)
  have hneg : Tendsto (fun x : ℝ => -(x ^ 2)) atTop atBot := tendsto_neg_atTop_atBot.comp hsq
  have h1 : Tendsto (fun x : ℝ => -(x ^ 2) / 2) atTop atBot :=
    (hneg.atBot_div_const (by norm_num : (0 : ℝ) < 2)).congr (fun x => by ring)
  exact Real.tendsto_exp_atBot.comp h1

/-- The improper integral `∫_{Ioi M} x · exp(-x²/2) dx` equals `exp(-M²/2)`. -/
theorem integral_Ioi_id_mul_exp_neg_sq_half (M : ℝ) :
    ∫ x in Ioi M, x * Real.exp (-(x ^ 2) / 2) = Real.exp (-(M ^ 2) / 2) := by
  -- Via FTC-2 on `(M, ∞)` with antiderivative `f x = -exp(-x²/2)`.
  set f : ℝ → ℝ := fun x => -Real.exp (-(x ^ 2) / 2) with hf
  set f' : ℝ → ℝ := fun x => x * Real.exp (-(x ^ 2) / 2) with hf'
  have hderiv : ∀ x ∈ Ici M, HasDerivAt f (f' x) x :=
    fun x _ => hasDerivAt_neg_exp_neg_sq_half x
  -- Integrability of f' on Ioi M: f' is continuous + decays fast enough.
  -- For our purposes the easy bound is `|f' x| ≤ |x| · exp(-x²/2)`, and
  -- `x · exp(-x²/2)` is integrable on (Ioi 0); on Ioi M for M < 0 we split.
  have hint_pos : IntegrableOn f' (Ioi (0 : ℝ)) := by
    have := integrableOn_rpow_mul_exp_neg_mul_sq
      (b := (1/2 : ℝ)) (s := 1) (by norm_num) (by norm_num)
    have heq : (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(1/2) * x ^ 2)) =
        f' := by
      ext x
      simp only [hf', Real.rpow_one]
      congr 1; congr 1; ring
    rwa [heq] at this
  -- Integrability on Ioi M follows by handling Ioi M ⊆ ℝ piecewise.
  have hint : IntegrableOn f' (Ioi M) := by
    by_cases hM : 0 ≤ M
    · exact hint_pos.mono_set (fun x hx => lt_of_le_of_lt hM hx)
    · push_neg at hM
      have hcont_Icc : ContinuousOn f' (Set.Icc M 0) := by
        intro x _
        refine ContinuousAt.continuousWithinAt ?_
        exact (continuous_id.mul
          (Real.continuous_exp.comp
            ((continuous_neg.comp (continuous_pow 2)).div_const 2))).continuousAt
      have h1 : IntegrableOn f' (Set.Ioc M 0) :=
        (hcont_Icc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
      have h2 : IntegrableOn f' (Ioi (0 : ℝ)) := hint_pos
      have hsplit : Ioi M = Ioc M 0 ∪ Ioi 0 := by
        ext x
        constructor
        · intro hx
          rcases le_or_gt x 0 with hx0 | hx0
          · exact Or.inl ⟨hx, hx0⟩
          · exact Or.inr hx0
        · rintro (⟨h1, _⟩ | hx0)
          · exact h1
          · exact lt_of_le_of_lt hM.le hx0
      rw [hsplit]
      exact h1.union h2
  -- f tends to 0 at infinity.
  have htends : Tendsto f atTop (𝓝 0) := by
    have := tendsto_exp_neg_sq_half_atTop
    simpa [hf] using this.neg
  -- Apply FTC-2:
  have := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := f) (f' := f') (m := 0) hderiv hint htends
  -- this: ∫ x in Ioi M, f' x = 0 - f M = exp(-M²/2)
  rw [this]
  simp [hf]

/-- **Mill's ratio bound** (one-sided): for `M > 0`,

  `∫ x in Ioi M, exp(-x²/2) dx ≤ exp(-M²/2) / M`. -/
theorem gaussian_tail_bound_Ioi {M : ℝ} (hM : 0 < M) :
    ∫ x in Ioi M, Real.exp (-(x ^ 2) / 2) ≤ Real.exp (-(M ^ 2) / 2) / M := by
  -- On Ioi M: M · exp(-x²/2) ≤ x · exp(-x²/2). Integrate, then divide by M.
  have hint_exp : IntegrableOn (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) (Ioi M) := by
    have := integrableOn_rpow_mul_exp_neg_mul_sq
      (b := (1/2 : ℝ)) (s := 0) (by norm_num) (by norm_num)
    have heq : (fun x : ℝ => x ^ (0 : ℝ) * Real.exp (-(1/2) * x ^ 2)) =
        (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) := by
      ext x
      rw [Real.rpow_zero, one_mul]
      congr 1; ring
    rw [heq] at this
    exact this.mono_set (fun x hx => lt_of_lt_of_le hM hx.le)
  have hint_xexp : IntegrableOn (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) (Ioi M) := by
    have := integrableOn_rpow_mul_exp_neg_mul_sq
      (b := (1/2 : ℝ)) (s := 1) (by norm_num) (by norm_num)
    have heq : (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(1/2) * x ^ 2)) =
        (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) := by
      ext x
      rw [Real.rpow_one]
      congr 1; ring
    rw [heq] at this
    exact this.mono_set (fun x hx => lt_of_lt_of_le hM hx.le)
  -- Pointwise inequality: M · exp(-x²/2) ≤ x · exp(-x²/2) for x ∈ Ioi M.
  have hineq : ∀ᵐ x ∂(volume.restrict (Ioi M)),
      M * Real.exp (-(x ^ 2) / 2) ≤ x * Real.exp (-(x ^ 2) / 2) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    filter_upwards with x hx
    have : M ≤ x := hx.le
    have hpos : 0 < Real.exp (-(x ^ 2) / 2) := Real.exp_pos _
    exact mul_le_mul_of_nonneg_right this hpos.le
  -- Integrate the inequality.
  have hint : M * ∫ x in Ioi M, Real.exp (-(x ^ 2) / 2) ≤
      ∫ x in Ioi M, x * Real.exp (-(x ^ 2) / 2) := by
    rw [← integral_const_mul]
    exact MeasureTheory.integral_mono_ae (hint_exp.const_mul M) hint_xexp hineq
  rw [integral_Ioi_id_mul_exp_neg_sq_half] at hint
  -- hint: M * (∫ exp(-x²/2)) ≤ exp(-M²/2). Divide by M.
  rwa [le_div_iff₀ hM, mul_comm]

/-- The lower-tail integral equals the upper-tail integral by symmetry. -/
theorem integral_Iio_neg_eq_integral_Ioi (M : ℝ) :
    ∫ x in Iio (-M), Real.exp (-(x ^ 2) / 2) =
      ∫ x in Ioi M, Real.exp (-(x ^ 2) / 2) := by
  -- Step 1: replace `Iio (-M)` by `Iic (-M)` (singleton has volume 0).
  rw [← integral_Iic_eq_integral_Iio]
  -- Step 2: substitute `x ↦ -x` via `integral_comp_neg_Iic`.
  -- The integrand is even, so `f(-x) = f(x)`.
  have hsub := integral_comp_neg_Iic (-M) (fun y : ℝ => Real.exp (-(y ^ 2) / 2))
  -- hsub : ∫ x in Iic (-M), exp(-((-x)^2)/2) = ∫ x in Ioi (-(-M)), exp(-x²/2)
  rw [show (-(-M) : ℝ) = M from neg_neg M] at hsub
  -- Even-function: `(-x)^2 = x^2`, so the LHS of hsub is what we want.
  rw [show (fun x : ℝ => Real.exp (-((-x) ^ 2) / 2)) =
        (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) from by
        ext x; rw [neg_pow_two]] at hsub
  exact hsub

/-- **Two-sided Gaussian tail bound**: for `M > 0`,

  `∫ x in Iio (-M), exp(-x²/2) dx + ∫ x in Ioi M, exp(-x²/2) dx ≤ 2 exp(-M²/2) / M`. -/
theorem gaussian_tail_bound_two_sided {M : ℝ} (hM : 0 < M) :
    (∫ x in Iio (-M), Real.exp (-(x ^ 2) / 2)) +
        ∫ x in Ioi M, Real.exp (-(x ^ 2) / 2) ≤
      2 * Real.exp (-(M ^ 2) / 2) / M := by
  rw [integral_Iio_neg_eq_integral_Ioi]
  rw [show (∫ x in Ioi M, Real.exp (-(x ^ 2) / 2)) +
        ∫ x in Ioi M, Real.exp (-(x ^ 2) / 2) =
      2 * ∫ x in Ioi M, Real.exp (-(x ^ 2) / 2) by ring]
  rw [show (2 * Real.exp (-(M ^ 2) / 2) / M : ℝ) =
        2 * (Real.exp (-(M ^ 2) / 2) / M) by ring]
  exact mul_le_mul_of_nonneg_left (gaussian_tail_bound_Ioi hM) (by norm_num)

/-- The derivative of `-x · exp(-x²/2)` is `(x² - 1) · exp(-x²/2)`. -/
private lemma hasDerivAt_neg_id_mul_exp_neg_sq_half (x : ℝ) :
    HasDerivAt (fun y : ℝ => -y * Real.exp (-(y ^ 2) / 2))
      ((x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2)) x := by
  -- d/dx[-x · g(x)] = -g(x) - x · g'(x), where g(x) = exp(-x²/2), g'(x) = -x · g(x).
  -- So d/dx[-x · g(x)] = -g(x) - x · (-x · g(x)) = -g(x) + x² g(x) = (x² - 1) g(x).
  have hg : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2) / 2))
      (-x * Real.exp (-(x ^ 2) / 2)) x := by
    have hp : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
      have hq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have := (hq.neg).div_const 2
      convert this using 1
      ring
    have := (Real.hasDerivAt_exp (-(x ^ 2) / 2)).comp x hp
    simpa [mul_comm] using this
  have hid : HasDerivAt (fun y : ℝ => -y) (-1) x :=
    (hasDerivAt_id x).neg
  -- Product rule: (u · v)' = u' v + u v'
  have := hid.mul hg
  -- this : HasDerivAt (fun y ↦ -y · exp(-y²/2)) (-1 · exp(-x²/2) + (-x) · (-x · exp(-x²/2))) x
  convert this using 1
  ring

/-- The improper integral `∫_{Ioi M} (x² - 1) · exp(-x²/2) dx` equals `M · exp(-M²/2)`. -/
theorem integral_Ioi_sq_sub_one_mul_exp_neg_sq_half (M : ℝ) :
    ∫ x in Ioi M, (x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2) = M * Real.exp (-(M ^ 2) / 2) := by
  set f : ℝ → ℝ := fun x => -x * Real.exp (-(x ^ 2) / 2) with hf
  set f' : ℝ → ℝ := fun x => (x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2) with hf'
  have hderiv : ∀ x ∈ Ici M, HasDerivAt f (f' x) x :=
    fun x _ => hasDerivAt_neg_id_mul_exp_neg_sq_half x
  -- Integrability: split into x²·exp(-x²/2) - exp(-x²/2), each integrable on Ioi M.
  have hint_x2 : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2) / 2)) (Ioi M) := by
    have := integrableOn_rpow_mul_exp_neg_mul_sq
      (b := (1/2 : ℝ)) (s := 2) (by norm_num) (by norm_num)
    have heq : (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-(1/2) * x ^ 2)) =
        (fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2) / 2)) := by
      ext x
      rw [show x ^ (2 : ℝ) = x ^ (2 : ℕ) from rpow_natCast x 2]
      congr 1; ring
    rw [heq] at this
    -- Need integrability on `Ioi M`, but we only have it on `Ioi 0`.
    by_cases hM : 0 ≤ M
    · exact this.mono_set (fun x hx => lt_of_le_of_lt hM hx)
    · push_neg at hM
      have hcont_Icc : ContinuousOn (fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2) / 2))
          (Set.Icc M 0) := by
        intro x _
        refine ContinuousAt.continuousWithinAt ?_
        exact ((continuous_pow 2).mul (Real.continuous_exp.comp
          ((continuous_neg.comp (continuous_pow 2)).div_const 2))).continuousAt
      have h1 : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2) / 2))
          (Set.Ioc M 0) :=
        (hcont_Icc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
      have hsplit : Ioi M = Ioc M 0 ∪ Ioi 0 := by
        ext x
        constructor
        · intro hx
          rcases le_or_gt x 0 with hx0 | hx0
          · exact Or.inl ⟨hx, hx0⟩
          · exact Or.inr hx0
        · rintro (⟨h1, _⟩ | hx0)
          · exact h1
          · exact lt_of_le_of_lt hM.le hx0
      rw [hsplit]
      exact h1.union this
  have hint_e : IntegrableOn (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) (Ioi M) := by
    have := integrableOn_rpow_mul_exp_neg_mul_sq
      (b := (1/2 : ℝ)) (s := 0) (by norm_num) (by norm_num)
    have heq : (fun x : ℝ => x ^ (0 : ℝ) * Real.exp (-(1/2) * x ^ 2)) =
        (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) := by
      ext x
      rw [Real.rpow_zero, one_mul]
      congr 1; ring
    rw [heq] at this
    by_cases hM : 0 ≤ M
    · exact this.mono_set (fun x hx => lt_of_le_of_lt hM hx)
    · push_neg at hM
      have hcont_Icc : ContinuousOn (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) (Set.Icc M 0) := by
        intro x _
        refine ContinuousAt.continuousWithinAt ?_
        exact (Real.continuous_exp.comp
          ((continuous_neg.comp (continuous_pow 2)).div_const 2)).continuousAt
      have h1 : IntegrableOn (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) (Set.Ioc M 0) :=
        (hcont_Icc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
      have hsplit : Ioi M = Ioc M 0 ∪ Ioi 0 := by
        ext x
        constructor
        · intro hx
          rcases le_or_gt x 0 with hx0 | hx0
          · exact Or.inl ⟨hx, hx0⟩
          · exact Or.inr hx0
        · rintro (⟨h1, _⟩ | hx0)
          · exact h1
          · exact lt_of_le_of_lt hM.le hx0
      rw [hsplit]
      exact h1.union this
  have hint : IntegrableOn f' (Ioi M) := by
    have : f' = fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2) / 2) - Real.exp (-(x ^ 2) / 2) := by
      ext x; simp only [hf']; ring
    rw [this]; exact hint_x2.sub hint_e
  -- f tends to 0 at infinity (x · exp(-x²/2) → 0).
  have htends : Tendsto f atTop (𝓝 0) := by
    -- Reduce to `IsLittleO` against `exp(-bx)` plus `exp(-bx) → 0`.
    have h1 : (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(1/2) * x ^ 2)) =o[atTop]
              (fun x : ℝ => Real.exp (-(1/2) * x)) :=
      rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (by norm_num : (0 : ℝ) < 1/2) 1
    have h2 : Tendsto (fun x : ℝ => Real.exp (-(1/2) * x)) atTop (𝓝 0) := by
      have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := 0) (b := 1/2)
        (by norm_num : (0 : ℝ) < 1/2)
      simpa [Real.rpow_zero] using this
    have h3 : Tendsto (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(1/2) * x ^ 2)) atTop (𝓝 0) :=
      h1.tendsto_zero_of_tendsto h2
    have heq : (fun x : ℝ => -x * Real.exp (-(x ^ 2) / 2)) =
        (fun x : ℝ => -(x ^ (1 : ℝ) * Real.exp (-(1/2) * x ^ 2))) := by
      ext x
      rw [Real.rpow_one]
      congr 1; congr 1; ring
    rw [hf, heq]
    simpa using h3.neg
  -- Apply FTC-2.
  have := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := f) (f' := f') (m := 0) hderiv hint htends
  rw [this]
  simp [hf]

/-- **Second-order tail decomposition**: for any `M`,

  `∫_{Ioi M} x² · exp(-x²/2) dx = M · exp(-M²/2) + ∫_{Ioi M} exp(-x²/2) dx`. -/
theorem integral_Ioi_sq_mul_exp_neg_sq_half (M : ℝ) :
    ∫ x in Ioi M, x ^ 2 * Real.exp (-(x ^ 2) / 2) =
      M * Real.exp (-(M ^ 2) / 2) + ∫ x in Ioi M, Real.exp (-(x ^ 2) / 2) := by
  -- Rewrite x²·g = (x² - 1)·g + 1·g, then split the integral.
  have hint_x2 : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2) / 2)) (Ioi M) := by
    have := integrableOn_rpow_mul_exp_neg_mul_sq
      (b := (1/2 : ℝ)) (s := 2) (by norm_num) (by norm_num)
    have heq : (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-(1/2) * x ^ 2)) =
        (fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2) / 2)) := by
      ext x
      rw [show x ^ (2 : ℝ) = x ^ (2 : ℕ) from rpow_natCast x 2]
      congr 1; ring
    rw [heq] at this
    by_cases hM : 0 ≤ M
    · exact this.mono_set (fun x hx => lt_of_le_of_lt hM hx)
    · push_neg at hM
      have hcont_Icc : ContinuousOn (fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2) / 2))
          (Set.Icc M 0) := by
        intro x _
        refine ContinuousAt.continuousWithinAt ?_
        exact ((continuous_pow 2).mul (Real.continuous_exp.comp
          ((continuous_neg.comp (continuous_pow 2)).div_const 2))).continuousAt
      have h1 : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2) / 2))
          (Set.Ioc M 0) :=
        (hcont_Icc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
      have hsplit : Ioi M = Ioc M 0 ∪ Ioi 0 := by
        ext x
        refine ⟨fun hx => ?_, ?_⟩
        · rcases le_or_gt x 0 with h0 | h0
          · exact Or.inl ⟨hx, h0⟩
          · exact Or.inr h0
        · rintro (⟨h1, _⟩ | h0)
          · exact h1
          · exact lt_of_le_of_lt hM.le h0
      rw [hsplit]; exact h1.union this
  have hint_e : IntegrableOn (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) (Ioi M) := by
    have := integrableOn_rpow_mul_exp_neg_mul_sq
      (b := (1/2 : ℝ)) (s := 0) (by norm_num) (by norm_num)
    have heq : (fun x : ℝ => x ^ (0 : ℝ) * Real.exp (-(1/2) * x ^ 2)) =
        (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) := by
      ext x
      rw [Real.rpow_zero, one_mul]
      congr 1; ring
    rw [heq] at this
    by_cases hM : 0 ≤ M
    · exact this.mono_set (fun x hx => lt_of_le_of_lt hM hx)
    · push_neg at hM
      have hcont_Icc : ContinuousOn (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) (Set.Icc M 0) := by
        intro x _
        refine ContinuousAt.continuousWithinAt ?_
        exact (Real.continuous_exp.comp
          ((continuous_neg.comp (continuous_pow 2)).div_const 2)).continuousAt
      have h1 : IntegrableOn (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) (Set.Ioc M 0) :=
        (hcont_Icc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
      have hsplit : Ioi M = Ioc M 0 ∪ Ioi 0 := by
        ext x
        refine ⟨fun hx => ?_, ?_⟩
        · rcases le_or_gt x 0 with h0 | h0
          · exact Or.inl ⟨hx, h0⟩
          · exact Or.inr h0
        · rintro (⟨h1, _⟩ | h0)
          · exact h1
          · exact lt_of_le_of_lt hM.le h0
      rw [hsplit]; exact h1.union this
  -- Decompose the integrand: `x² · g = (x² - 1) · g + g`.
  -- Apply `setIntegral_add` directly via integrability of the two pieces.
  have hint_diff : IntegrableOn (fun x : ℝ => (x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2))
      (Ioi M) := by
    have heq2 : (fun x : ℝ => (x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2)) =
        (fun x : ℝ =>
          x ^ 2 * Real.exp (-(x ^ 2) / 2) - Real.exp (-(x ^ 2) / 2)) := by
      ext x; ring
    rw [heq2]; exact hint_x2.sub hint_e
  have heq : ∀ x : ℝ, x ^ 2 * Real.exp (-(x ^ 2) / 2) =
      (x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2) + Real.exp (-(x ^ 2) / 2) := by
    intro x; ring
  calc (∫ x in Ioi M, x ^ 2 * Real.exp (-(x ^ 2) / 2))
      = ∫ x in Ioi M, ((x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2)
                        + Real.exp (-(x ^ 2) / 2)) := by
          refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
          exact heq x
    _ = (∫ x in Ioi M, (x ^ 2 - 1) * Real.exp (-(x ^ 2) / 2))
          + ∫ x in Ioi M, Real.exp (-(x ^ 2) / 2) := by
          exact MeasureTheory.integral_add hint_diff hint_e
    _ = M * Real.exp (-(M ^ 2) / 2) + ∫ x in Ioi M, Real.exp (-(x ^ 2) / 2) := by
          rw [integral_Ioi_sq_sub_one_mul_exp_neg_sq_half]

/-- **Rescaled first-moment closed form**: for `b > 0` and any `M`,

  `∫ x in Ioi M, x · exp(-(b x²)/2) dx = exp(-(b M²)/2) / b`.

The proof rescales `u = x √b` and applies the standard formula. -/
theorem integral_Ioi_id_mul_exp_neg_b_sq_half {b : ℝ} (hb : 0 < b) (M : ℝ) :
    ∫ x in Ioi M, x * Real.exp (-(b * x ^ 2) / 2) =
      Real.exp (-(b * M ^ 2) / 2) / b := by
  set s := Real.sqrt b with hs_def
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hb
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hsq : s ^ 2 = b := Real.sq_sqrt hb.le
  -- After substitution `u = x · s`, the integrand `x · exp(-(b x²)/2)` becomes
  -- `(u/s) · exp(-(u²)/2)` times the Jacobian `1/s`, so a factor of `1/s²= 1/b` overall.
  have hkey : ∫ x in Ioi M, x * Real.exp (-(b * x ^ 2) / 2) =
      s⁻¹ * ∫ u in Ioi (M * s), (u / s) * Real.exp (-(u ^ 2) / 2) := by
    have h := integral_comp_mul_right_Ioi
      (fun u : ℝ => (u / s) * Real.exp (-(u ^ 2) / 2)) M hs_pos
    -- h : ∫ x in Ioi M, ((x*s)/s) * exp(-((x*s)^2)/2) = s⁻¹ • ∫ u in Ioi (M*s), (u/s) * exp(-u²/2)
    rw [show (fun x : ℝ => x * Real.exp (-(b * x ^ 2) / 2)) =
          (fun x : ℝ => ((x * s) / s) * Real.exp (-((x * s) ^ 2) / 2)) by
          ext x
          rw [show (x * s) ^ 2 = b * x ^ 2 by rw [mul_pow, hsq]; ring,
              mul_div_cancel_right₀ x hs_ne]]
    rw [h, smul_eq_mul]
  rw [hkey]
  -- Pull out `1/s`: `∫ (u/s) · exp(-u²/2) = (1/s) · ∫ u · exp(-u²/2)`.
  rw [show (fun u : ℝ => u / s * Real.exp (-(u ^ 2) / 2)) =
        (fun u : ℝ => s⁻¹ * (u * Real.exp (-(u ^ 2) / 2))) by
        ext u; rw [div_eq_mul_inv]; ring]
  rw [integral_const_mul, integral_Ioi_id_mul_exp_neg_sq_half]
  -- Goal: s⁻¹ * (s⁻¹ * exp(-(M*s)²/2)) = exp(-(b*M²)/2) / b.
  rw [show (M * s) ^ 2 = b * M ^ 2 by rw [mul_pow, hsq]; ring]
  rw [show (s⁻¹ * (s⁻¹ * Real.exp (-(b * M ^ 2) / 2)) : ℝ) =
        Real.exp (-(b * M ^ 2) / 2) * (s⁻¹ * s⁻¹) by ring]
  rw [show (s⁻¹ * s⁻¹ : ℝ) = (s * s)⁻¹ by rw [mul_inv]]
  rw [show (s * s : ℝ) = b from by rw [← sq]; exact hsq]
  field_simp

/-- **Rescaled second-moment closed form**: for `b > 0` and any `M`,

  `∫ x in Ioi M, x² · exp(-(b x²)/2) dx
    = M · exp(-(b M²)/2) / b + (1/b) · ∫ x in Ioi M, exp(-(b x²)/2) dx`.

This is the harmonic-Gibbs version of `integral_Ioi_sq_mul_exp_neg_sq_half`, the
key input for second-moment localisation. -/
theorem integral_Ioi_sq_mul_exp_neg_b_sq_half {b : ℝ} (hb : 0 < b) (M : ℝ) :
    ∫ x in Ioi M, x ^ 2 * Real.exp (-(b * x ^ 2) / 2) =
      M * Real.exp (-(b * M ^ 2) / 2) / b
        + (1 / b) * ∫ x in Ioi M, Real.exp (-(b * x ^ 2) / 2) := by
  set s := Real.sqrt b with hs_def
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hb
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hsq : s ^ 2 = b := Real.sq_sqrt hb.le
  -- LHS via substitution u = x·s:
  -- ∫ x² · exp(-(b x²)/2) dx = (1/s³) · ∫ u² · exp(-u²/2) du
  have hLHS : ∫ x in Ioi M, x ^ 2 * Real.exp (-(b * x ^ 2) / 2) =
      s⁻¹ * ∫ u in Ioi (M * s), (u / s) ^ 2 * Real.exp (-(u ^ 2) / 2) := by
    have h := integral_comp_mul_right_Ioi
      (fun u : ℝ => (u / s) ^ 2 * Real.exp (-(u ^ 2) / 2)) M hs_pos
    rw [show (fun x : ℝ => x ^ 2 * Real.exp (-(b * x ^ 2) / 2)) =
          (fun x : ℝ => ((x * s) / s) ^ 2 * Real.exp (-((x * s) ^ 2) / 2)) by
          ext x
          rw [show (x * s) ^ 2 = b * x ^ 2 by rw [mul_pow, hsq]; ring,
              mul_div_cancel_right₀ x hs_ne]]
    rw [h, smul_eq_mul]
  rw [hLHS]
  -- Simplify (u/s)² = u² / s² = u² / b.
  rw [show (fun u : ℝ => (u / s) ^ 2 * Real.exp (-(u ^ 2) / 2)) =
        (fun u : ℝ => b⁻¹ * (u ^ 2 * Real.exp (-(u ^ 2) / 2))) by
        ext u
        rw [div_pow, show (s : ℝ) ^ 2 = b from hsq, div_eq_mul_inv]; ring]
  rw [integral_const_mul, integral_Ioi_sq_mul_exp_neg_sq_half]
  -- Goal: s⁻¹ * (b⁻¹ * (M·s · exp(-(M·s)²/2) + ∫ exp(-u²/2))) = M · exp(-(b M²)/2)/b + (1/b)·∫ ...
  -- Convert the inner Gaussian-tail integral back to b-form via substitution.
  rw [show (M * s) ^ 2 = b * M ^ 2 by rw [mul_pow, hsq]; ring]
  -- Rewrite ∫_{Ioi (M·s)} exp(-u²/2) du in terms of the rescaled form.
  have htail : ∫ u in Ioi (M * s), Real.exp (-(u ^ 2) / 2) =
      s * ∫ x in Ioi M, Real.exp (-(b * x ^ 2) / 2) := by
    have h := integral_comp_mul_right_Ioi
      (fun u : ℝ => Real.exp (-(u ^ 2) / 2)) M hs_pos
    rw [show (fun x : ℝ => Real.exp (-(b * x ^ 2) / 2)) =
          (fun x : ℝ => Real.exp (-((x * s) ^ 2) / 2)) by
          ext x
          rw [show (x * s) ^ 2 = b * x ^ 2 by rw [mul_pow, hsq]; ring]]
    rw [h, smul_eq_mul]
    field_simp
  rw [htail]
  -- Now the goal is a pure arithmetic identity in s, b, and the integrals.
  field_simp

/-- **Rescaled tail bound**: for `b, M > 0`,

  `∫ x in Ioi M, exp(-(b x²)/2) dx ≤ exp(-(b M²)/2) / (b · M)`.

This is the version we need for localising the harmonic Gibbs measure as `t → ∞`:
setting `b = λ t`, the right-hand side decays as `exp(-λ t M²/2) / (λ t M)`. -/
theorem gaussian_tail_bound_rescaled_Ioi {M b : ℝ} (hM : 0 < M) (hb : 0 < b) :
    ∫ x in Ioi M, Real.exp (-(b * x ^ 2) / 2) ≤
      Real.exp (-(b * M ^ 2) / 2) / (b * M) := by
  -- Substitute `u = x · √b`. Then `Ioi M` maps to `Ioi (M √b)` and the integrand
  -- becomes `exp(-u²/2) / √b · du`.
  set s := Real.sqrt b with hs_def
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hb
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hsq : s ^ 2 = b := Real.sq_sqrt hb.le
  -- Integral comp_mul_right gives `∫ x in ℝ, f(x · s) = (1/|s|) · ∫ y, f y`.
  -- For setIntegral over Ioi M, use the half-line version `integral_comp_mul_right_Ioi`.
  have hkey : ∫ x in Ioi M, Real.exp (-(b * x ^ 2) / 2) =
      s⁻¹ * ∫ u in Ioi (M * s), Real.exp (-(u ^ 2) / 2) := by
    have h := integral_comp_mul_right_Ioi
      (fun u : ℝ => Real.exp (-(u ^ 2) / 2)) M hs_pos
    -- h : ∫ x in Ioi M, exp(-((x*s)^2)/2) = |s|⁻¹ • ∫ u in Ioi (M * s), exp(-u²/2)
    rw [show (fun x : ℝ => Real.exp (-(b * x ^ 2) / 2)) =
          (fun x : ℝ => Real.exp (-((x * s) ^ 2) / 2)) by
          ext x; rw [show (x * s) ^ 2 = b * x ^ 2 by rw [mul_pow, hsq]; ring]]
    rw [h, smul_eq_mul]
  rw [hkey]
  -- Apply standard Mill's ratio: ∫_{Ioi (M*s)} exp(-u²/2) ≤ exp(-(M*s)²/2) / (M*s).
  have hMs_pos : 0 < M * s := mul_pos hM hs_pos
  have htail := gaussian_tail_bound_Ioi hMs_pos
  calc s⁻¹ * ∫ u in Ioi (M * s), Real.exp (-(u ^ 2) / 2)
      ≤ s⁻¹ * (Real.exp (-((M * s) ^ 2) / 2) / (M * s)) := by
        apply mul_le_mul_of_nonneg_left htail (le_of_lt (inv_pos.mpr hs_pos))
    _ = Real.exp (-(b * M ^ 2) / 2) / (b * M) := by
        rw [show (M * s) ^ 2 = b * M ^ 2 by rw [mul_pow, hsq]; ring]
        rw [show s⁻¹ * (Real.exp (-(b * M ^ 2) / 2) / (M * s)) =
              Real.exp (-(b * M ^ 2) / 2) / (s * (M * s)) by
              field_simp]
        rw [show s * (M * s) = M * (s * s) from by ring,
            show s * s = b by rw [← sq]; exact hsq]
        rw [show M * b = b * M by ring]

end Laplace.OneD
