import Laplace.Multi.Basic
import Laplace.Multi.QuadraticApprox
import Laplace.Multi.GaussianIBP
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Rescaled integrals and the change-of-variables bridge

For the multivariate Laplace asymptotic, we substitute `w = (√t)⁻¹ • u`
in the Gibbs expectation `gibbsExpectation V t F`. The Jacobian of the
dilation contributes `(√t)⁻^d` (where `d = Fintype.card ι`) to both
numerator and denominator, so it cancels in the ratio.

This file:

- defines `rescaledPartition`, `rescaledNumerator`, `rescaledExpectation`,
  `rescaledCov` on the rescaled `u`-space;
- proves the Jacobian-scaling identities for numerator and denominator;
- proves the bridge `gibbsExpectation V t F = rescaledExpectation V t F`
  for `t > 0`.

The downstream `Multi/Covariance.lean` works entirely on the rescaled
side after invoking the bridge.

Strategy per GPT-5.5 Pro Phase 5 memo
(`gpt_responses/phase5_covariance.md`): one change-of-variables lemma
up front, then never go back to the original variable in the proof.
-/

namespace Laplace.Multi

open MeasureTheory Module

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rescaled partition function:
`Z_t' := ∫ exp(-(t · V ((√t)⁻¹ u))) du`.

Related to `partitionFunction V t = ∫ exp(-(t · V w)) dw` by the dilation
identity `partitionFunction V t = (√t)⁻^d · rescaledPartition V t`. -/
noncomputable def rescaledPartition (V : (ι → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ u : ι → ℝ, Real.exp (-(t * V ((Real.sqrt t)⁻¹ • u)))

/-- The rescaled numerator for an observable `F`:
`N_t' := ∫ F((√t)⁻¹ u) · exp(-(t · V ((√t)⁻¹ u))) du`. -/
noncomputable def rescaledNumerator
    (V : (ι → ℝ) → ℝ) (t : ℝ) (F : (ι → ℝ) → ℝ) : ℝ :=
  ∫ u : ι → ℝ, F ((Real.sqrt t)⁻¹ • u) *
    Real.exp (-(t * V ((Real.sqrt t)⁻¹ • u)))

/-- The rescaled expectation: `N_t' / Z_t'`. -/
noncomputable def rescaledExpectation
    (V : (ι → ℝ) → ℝ) (t : ℝ) (F : (ι → ℝ) → ℝ) : ℝ :=
  rescaledNumerator V t F / rescaledPartition V t

/-- The rescaled covariance:
`Cov'_t[φ, ψ] := E'_t[φψ] - E'_t[φ] · E'_t[ψ]`. -/
noncomputable def rescaledCov
    (V : (ι → ℝ) → ℝ) (t : ℝ) (φ ψ : (ι → ℝ) → ℝ) : ℝ :=
  rescaledExpectation V t (fun w => φ w * ψ w) -
    rescaledExpectation V t φ * rescaledExpectation V t ψ

section Dilation

/-- **Dilation identity for ℝ-valued integrals on `ι → ℝ`**: for any
nonzero `R : ℝ` and integrand `g : (ι → ℝ) → ℝ`,

  `∫ u, g (R • u) du = |R|⁻^d · ∫ w, g w dw`

where `d = Fintype.card ι`. Specializes `Measure.integral_comp_smul` to
the standard `volume` on `ι → ℝ` (which is an additive Haar measure
by `isAddHaarMeasure_volume_pi`). -/
lemma integral_comp_smul_pi (g : (ι → ℝ) → ℝ) (R : ℝ) :
    ∫ u : ι → ℝ, g (R • u) = |R ^ (Fintype.card ι)|⁻¹ * ∫ w : ι → ℝ, g w := by
  have h := Measure.integral_comp_smul (μ := (volume : Measure (ι → ℝ))) g R
  rw [Module.finrank_pi (R := ℝ)] at h
  simp only [smul_eq_mul, abs_inv] at h
  exact h

/-- **Numerator dilation identity**: for `t > 0`,
`rescaledNumerator V t F = (√t)^d · ∫ F(w) · exp(-tV(w)) dw`. -/
lemma rescaledNumerator_eq_smul
    (V F : (ι → ℝ) → ℝ) {t : ℝ} (ht : 0 < t) :
    rescaledNumerator V t F
      = (Real.sqrt t) ^ (Fintype.card ι) *
          ∫ w : ι → ℝ, F w * Real.exp (-(t * V w)) := by
  have h := integral_comp_smul_pi (fun w => F w * Real.exp (-(t * V w)))
              ((Real.sqrt t)⁻¹)
  -- h : ∫ u, F((√t)⁻¹•u) · ... = |((√t)⁻¹)^d|⁻¹ * ∫ w, F(w) · ...
  have h_abs : |((Real.sqrt t)⁻¹) ^ (Fintype.card ι)|⁻¹
      = (Real.sqrt t) ^ (Fintype.card ι) := by
    rw [abs_of_pos
        (by positivity : (0 : ℝ) < ((Real.sqrt t)⁻¹) ^ (Fintype.card ι))]
    rw [inv_pow, inv_inv]
  rw [h_abs] at h
  unfold rescaledNumerator
  exact h

/-- **Partition dilation identity**: for `t > 0`,
`rescaledPartition V t = (√t)^d · partitionFunction V t`. -/
lemma rescaledPartition_eq_smul
    (V : (ι → ℝ) → ℝ) {t : ℝ} (ht : 0 < t) :
    rescaledPartition V t
      = (Real.sqrt t) ^ (Fintype.card ι) * partitionFunction V t := by
  unfold partitionFunction rescaledPartition
  have h := rescaledNumerator_eq_smul V (fun _ : ι → ℝ => (1 : ℝ)) ht
  unfold rescaledNumerator at h
  simp only [one_mul] at h
  exact h

/-- **Change-of-variables bridge for expectations**: for `t > 0`,

  `gibbsExpectation V t F = rescaledExpectation V t F`. -/
theorem gibbsExpectation_eq_rescaledExpectation
    (V F : (ι → ℝ) → ℝ) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation V t F = rescaledExpectation V t F := by
  have hsqrt_pow_pos :
      (0 : ℝ) < (Real.sqrt t) ^ (Fintype.card ι) := by positivity
  have hsqrt_pow_ne :
      (Real.sqrt t) ^ (Fintype.card ι) ≠ 0 := ne_of_gt hsqrt_pow_pos
  unfold gibbsExpectation rescaledExpectation
  rw [rescaledPartition_eq_smul V ht, rescaledNumerator_eq_smul V F ht]
  -- Goal: numerator / partition = (s · numerator) / (s · partition)
  rw [mul_div_mul_left _ _ hsqrt_pow_ne]

/-- **Change-of-variables bridge for covariances**: for `t > 0`,

  `gibbsCov V t φ ψ = rescaledCov V t φ ψ`. -/
theorem gibbsCov_eq_rescaledCov
    (V φ ψ : (ι → ℝ) → ℝ) {t : ℝ} (ht : 0 < t) :
    gibbsCov V t φ ψ = rescaledCov V t φ ψ := by
  unfold gibbsCov rescaledCov
  rw [gibbsExpectation_eq_rescaledExpectation V (fun w => φ w * ψ w) ht,
      gibbsExpectation_eq_rescaledExpectation V φ ht,
      gibbsExpectation_eq_rescaledExpectation V ψ ht]

end Dilation

section RescaledLocalBounds

/-- The quadratic form scales as the square: `quadForm H (c • u) = c² · quadForm H u`. -/
lemma quadForm_smul (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (c : ℝ) (u : ι → ℝ) :
    quadForm H (c • u) = c ^ 2 * quadForm H u := by
  unfold quadForm
  rw [ContinuousLinearMap.map_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Pi.smul_apply, smul_eq_mul]
  ring

/-- **Rescaled cubic bound on the perturbation**: under the local cubic
remainder hypothesis, for `t > 0` and `‖u‖ ≤ R · √t`,

  `|rescaledPerturbation V H t u| ≤ C · ‖u‖³ / √t`. -/
lemma abs_rescaledPerturbation_le
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    {R C : ℝ}
    (h_local : ∀ w : ι → ℝ, ‖w‖ ≤ R →
      |V w - (1/2) * quadForm H w| ≤ C * ‖w‖ ^ 3)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ R * Real.sqrt t) :
    |rescaledPerturbation V H t u| ≤ C * ‖u‖ ^ 3 / Real.sqrt t := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_inv_pos : 0 < (Real.sqrt t)⁻¹ := by positivity
  -- Step 1: Bound `‖(√t)⁻¹ • u‖ ≤ R`.
  have h_norm : ‖(Real.sqrt t)⁻¹ • u‖ ≤ R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_inv_pos]
    rw [show (Real.sqrt t)⁻¹ * ‖u‖ = ‖u‖ / Real.sqrt t from by
        field_simp]
    rwa [div_le_iff₀ hsqrt_pos]
  -- Step 2: Apply the local bound at the rescaled point.
  have h_loc := h_local ((Real.sqrt t)⁻¹ • u) h_norm
  rw [quadForm_smul] at h_loc
  -- Step 3: ((√t)⁻¹)² = t⁻¹, so t · ((√t)⁻¹)² = 1.
  have h_t_inv_sq : t * ((Real.sqrt t)⁻¹) ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt ht.le]
    exact mul_inv_cancel₀ (ne_of_gt ht)
  -- Step 4: ((√t)⁻¹)³ = ((√t)⁻¹)² · (√t)⁻¹, and t · ((√t)⁻¹)³ = (√t)⁻¹.
  have h_t_inv_cube : t * ((Real.sqrt t)⁻¹) ^ 3 = (Real.sqrt t)⁻¹ := by
    rw [show ((Real.sqrt t)⁻¹) ^ 3 = ((Real.sqrt t)⁻¹) ^ 2 * (Real.sqrt t)⁻¹
        from by ring]
    rw [← mul_assoc, h_t_inv_sq, one_mul]
  -- Step 5: ‖(√t)⁻¹ • u‖³ = ((√t)⁻¹)³ · ‖u‖³.
  have h_norm_smul_cube : ‖(Real.sqrt t)⁻¹ • u‖ ^ 3
      = ((Real.sqrt t)⁻¹) ^ 3 * ‖u‖ ^ 3 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_inv_pos, mul_pow]
  rw [h_norm_smul_cube] at h_loc
  -- Step 6: Multiply both sides of h_loc by t (≥ 0).
  -- Goal: |rescaledPerturbation V H t u| = |t · V((√t)⁻¹ • u) - (1/2) quadForm H u|
  --     ≤ C · ‖u‖³ / √t.
  unfold rescaledPerturbation
  -- LHS = |t·V(...) - (1/2) quadForm H u|.
  -- Note: t · ((1/2) ((√t)⁻¹)² · quadForm H u) = (1/2) · quadForm H u (by h_t_inv_sq).
  -- So LHS = |t · (V(...) - (1/2) ((√t)⁻¹)² quadForm H u)|
  --        = t · |V(...) - (1/2) ((√t)⁻¹)² quadForm H u|.
  have h_rearrange :
      t * V ((Real.sqrt t)⁻¹ • u) - (1/2) * quadForm H u
        = t * (V ((Real.sqrt t)⁻¹ • u)
            - (1/2) * (((Real.sqrt t)⁻¹) ^ 2 * quadForm H u)) := by
    have : t * ((1/2) * (((Real.sqrt t)⁻¹) ^ 2 * quadForm H u))
        = (1/2) * quadForm H u := by
      have : t * (((Real.sqrt t)⁻¹) ^ 2 * quadForm H u)
          = quadForm H u := by
        rw [← mul_assoc, h_t_inv_sq, one_mul]
      linarith
    linarith
  rw [h_rearrange, abs_mul, abs_of_pos ht]
  -- Goal: t · |V((√t)⁻¹ u) - (1/2)((√t)⁻¹)² quadForm H u| ≤ C · ‖u‖³ / √t
  calc t * |V ((Real.sqrt t)⁻¹ • u)
            - (1/2) * (((Real.sqrt t)⁻¹) ^ 2 * quadForm H u)|
      ≤ t * (C * (((Real.sqrt t)⁻¹) ^ 3 * ‖u‖ ^ 3)) :=
        mul_le_mul_of_nonneg_left h_loc (le_of_lt ht)
    _ = (t * ((Real.sqrt t)⁻¹) ^ 3) * (C * ‖u‖ ^ 3) := by ring
    _ = (Real.sqrt t)⁻¹ * (C * ‖u‖ ^ 3) := by rw [h_t_inv_cube]
    _ = C * ‖u‖ ^ 3 / Real.sqrt t := by field_simp

/-- The `dot` form is linear in the second argument: `dot a (c • u) = c · dot a u`. -/
lemma dot_smul (a : ι → ℝ) (c : ℝ) (u : ι → ℝ) :
    dot a (c • u) = c * dot a u := by
  unfold dot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Pi.smul_apply, smul_eq_mul]; ring

/-- **Rescaled quadratic bound on an observable**: under the local linear
remainder `|φ w - ⟨a, w⟩| ≤ C ‖w‖²` on `‖w‖ ≤ R`, for `t > 0` and
`‖u‖ ≤ R · √t`,

  `|φ((√t)⁻¹ u) - (√t)⁻¹ · ⟨a, u⟩| ≤ C · ‖u‖² / t`. -/
lemma abs_rescaledObservable_linear_error_le
    (φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    {R C : ℝ}
    (h_local : ∀ w : ι → ℝ, ‖w‖ ≤ R →
      |φ w - dot a w| ≤ C * ‖w‖ ^ 2)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ R * Real.sqrt t) :
    |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u|
      ≤ C * ‖u‖ ^ 2 / t := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_inv_pos : 0 < (Real.sqrt t)⁻¹ := by positivity
  -- Step 1: ‖(√t)⁻¹ • u‖ ≤ R.
  have h_norm : ‖(Real.sqrt t)⁻¹ • u‖ ≤ R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_inv_pos]
    rw [show (Real.sqrt t)⁻¹ * ‖u‖ = ‖u‖ / Real.sqrt t from by field_simp]
    rwa [div_le_iff₀ hsqrt_pos]
  -- Step 2: Apply the local bound.
  have h_loc := h_local ((Real.sqrt t)⁻¹ • u) h_norm
  rw [dot_smul] at h_loc
  -- h_loc : |φ((√t)⁻¹•u) - (√t)⁻¹ · dot a u| ≤ C · ‖(√t)⁻¹•u‖²
  -- Step 3: ‖(√t)⁻¹ • u‖² = ((√t)⁻¹)² · ‖u‖² = ‖u‖² / t.
  have h_norm_sq : ‖(Real.sqrt t)⁻¹ • u‖ ^ 2 = ‖u‖ ^ 2 / t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_inv_pos, mul_pow]
    rw [inv_pow, Real.sq_sqrt ht.le]
    field_simp
  rw [h_norm_sq] at h_loc
  calc |φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u|
      ≤ C * (‖u‖ ^ 2 / t) := h_loc
    _ = C * ‖u‖ ^ 2 / t := by ring

end RescaledLocalBounds

section GaussianFactorization

/-- **Pointwise factorization of the rescaled weight** (via `rescaling_identity`):

  `exp(-(t · V ((√t)⁻¹ u))) = gaussianWeight H u · exp(-rescaledPerturbation V H t u)`.

This lets us express rescaled integrals as Gaussian integrals against the
`exp(-s_t)` correction, which is the form on which all asymptotic estimates
operate. -/
lemma rescaled_weight_factor
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (t : ℝ) (u : ι → ℝ) :
    Real.exp (-(t * V ((Real.sqrt t)⁻¹ • u)))
      = gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)) := by
  unfold gaussianWeight
  rw [← Real.exp_add]
  congr 1
  -- LHS: -(t · V((√t)⁻¹ • u))
  -- RHS: -(1/2) quadForm H u + (-rescaledPerturbation V H t u)
  -- where rescaledPerturbation = t · V((√t)⁻¹ • u) - (1/2) quadForm H u.
  unfold rescaledPerturbation
  ring

/-- **Numerator factorization**: the rescaled numerator equals the Gaussian
integral of `F((√t)⁻¹ u)` against the `exp(-s_t)` correction. -/
lemma rescaledNumerator_eq_gaussian_form
    (V F : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (t : ℝ) :
    rescaledNumerator V t F
      = ∫ u : ι → ℝ, F ((Real.sqrt t)⁻¹ • u) * gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)) := by
  unfold rescaledNumerator
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  show F ((Real.sqrt t)⁻¹ • u) * Real.exp (-(t * V ((Real.sqrt t)⁻¹ • u)))
    = F ((Real.sqrt t)⁻¹ • u) * gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))
  rw [rescaled_weight_factor V H t u]
  ring

/-- **Partition factorization**: similar form with `F = 1`. -/
lemma rescaledPartition_eq_gaussian_form
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (t : ℝ) :
    rescaledPartition V t
      = ∫ u : ι → ℝ, gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)) := by
  unfold rescaledPartition
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  exact rescaled_weight_factor V H t u

end GaussianFactorization

section ExpErrorBounds

/-- **Scalar `exp(-r) - 1` bound**: for any real `r`,
`|exp(-r) - 1| ≤ |r| · exp |r|`.

Used in the partition expansion `exp(-s_t) ≈ 1 + O(s_t)`. -/
lemma abs_exp_neg_sub_one_le (r : ℝ) :
    |Real.exp (-r) - 1| ≤ |r| * Real.exp |r| := by
  rcases lt_or_ge r 0 with hr | hr
  swap
  · -- Case r ≥ 0: exp(-r) ≤ 1, so |exp(-r) - 1| = 1 - exp(-r).
    -- We have 1 - exp(-r) ≤ r ≤ r · exp(r) = |r| · exp(|r|).
    have h1 : Real.exp (-r) ≤ 1 :=
      le_trans (Real.exp_le_exp.mpr (by linarith : (-r : ℝ) ≤ 0))
        (le_of_eq Real.exp_zero)
    have h2 : 1 - Real.exp (-r) ≤ r := by
      have := Real.add_one_le_exp (-r)
      linarith
    have h3 : Real.exp (-r) - 1 ≤ 0 := by linarith
    rw [abs_of_nonpos h3, abs_of_nonneg hr]
    have h_exp_r : 1 ≤ Real.exp r := Real.one_le_exp hr
    calc -(Real.exp (-r) - 1) = 1 - Real.exp (-r) := by ring
      _ ≤ r := h2
      _ = r * 1 := (mul_one r).symm
      _ ≤ r * Real.exp r := mul_le_mul_of_nonneg_left h_exp_r hr
  · -- Case r < 0: exp(-r) > 1, so |exp(-r) - 1| = exp(-r) - 1.
    -- Setting y = -r > 0, we want exp(y) - 1 ≤ y · exp(y).
    -- Equivalent to exp(y) · (1 - y) ≤ 1, i.e., 1 - y ≤ exp(-y).
    -- Latter follows from exp(z) ≥ 1 + z (with z = -y).
    have hy : (0 : ℝ) < -r := by linarith
    have h1 : 1 ≤ Real.exp (-r) := Real.one_le_exp hy.le
    have h_exp_neg_r_pos : 0 < Real.exp (-r) := Real.exp_pos _
    rw [abs_of_neg hr]
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.exp (-r) - 1)]
    -- Goal: exp(-r) - 1 ≤ (-r) · exp(-r).
    -- Equivalent to exp(-r) · (1 - (-r)) ≤ 1, i.e. (1 + r) ≤ exp(r).
    have h_exp_r : 1 + r ≤ Real.exp r := by
      have := Real.add_one_le_exp r
      linarith
    -- So 1 - (-r) ≤ exp(r), hence exp(-r) · (1 - (-r)) ≤ exp(-r) · exp(r) = exp(0) = 1.
    have h_prod : Real.exp (-r) * (1 - (-r)) ≤ 1 := by
      have h_one_sub_le : 1 - (-r) ≤ Real.exp r := by linarith
      have hmul : Real.exp (-r) * (1 - (-r)) ≤ Real.exp (-r) * Real.exp r :=
        mul_le_mul_of_nonneg_left h_one_sub_le h_exp_neg_r_pos.le
      have h_exp_sum : Real.exp (-r) * Real.exp r = 1 := by
        rw [← Real.exp_add]; simp
      linarith
    linarith

end ExpErrorBounds

end Laplace.Multi
