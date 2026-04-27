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

section PartitionDiffIntegral

open MeasureTheory

/-- **Partition difference as an integral**: under integrability of the
Gaussian weight and of the rescaled-weight factorization,

  `rescaledPartition V t - gaussianZ H
    = ∫ u, gaussianWeight H u · (exp(-rescaledPerturbation V H t u) - 1) du`. -/
lemma rescaledPartition_sub_gaussianZ_eq_integral
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (t : ℝ)
    (h_int_gW : Integrable (gaussianWeight H))
    (h_int_rescaled : Integrable
      (fun u : ι → ℝ =>
        gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))) :
    rescaledPartition V t - gaussianZ H
      = ∫ u : ι → ℝ, gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1) := by
  unfold gaussianZ
  rw [rescaledPartition_eq_gaussian_form V H t]
  -- LHS: ∫ gW · exp(-s_t) - ∫ gW = ∫ (gW · exp(-s_t) - gW) = ∫ gW · (exp(-s_t) - 1).
  rw [← integral_sub h_int_rescaled h_int_gW]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  ring

end PartitionDiffIntegral

section NumeratorSplit

open MeasureTheory

/-- **Rescaled numerator decomposition**: for any observable `φ` with
gradient `a`, given integrability of the two pieces,

  `rescaledNumerator V t φ
    = (√t)⁻¹ · ∫ ⟨a, u⟩ · gaussianWeight H u · exp(-s_t(u)) du
      + ∫ (φ((√t)⁻¹ u) - (√t)⁻¹ · ⟨a, u⟩)
          · gaussianWeight H u · exp(-s_t(u)) du`.

Algebraic decomposition `φ((√t)⁻¹ u) = (√t)⁻¹ · ⟨a, u⟩ + remainder`
applied inside the rescaled-numerator integral.

Used in the observable-asymptote argument: the linear-part integral
vanishes by `integral_odd_mul_gaussian_eq_zero` (when `exp(-s_t) ≈ 1`),
leaving the quadratic-remainder integral as the leading term. -/
lemma rescaledNumerator_eq_linear_plus_remainder
    (V φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (t : ℝ)
    (h_int_lin : Integrable
      (fun u : ι → ℝ => dot a u * gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))))
    (h_int_rem : Integrable
      (fun u : ι → ℝ =>
        (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))) :
    rescaledNumerator V t φ
      = (Real.sqrt t)⁻¹ *
          (∫ u : ι → ℝ, dot a u * gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)))
        + ∫ u : ι → ℝ,
            (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
              gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)) := by
  rw [rescaledNumerator_eq_gaussian_form V φ H t]
  -- Goal: ∫ φ((√t)⁻¹ • u) · gW · exp(-s_t) du
  --     = (√t)⁻¹ · ∫ ⟨a, u⟩ · gW · exp(-s_t) du
  --       + ∫ (φ((√t)⁻¹ • u) - (√t)⁻¹ ⟨a, u⟩) · gW · exp(-s_t) du.
  -- Move (√t)⁻¹ inside the integral.
  rw [show
      (Real.sqrt t)⁻¹ *
        ∫ u : ι → ℝ, dot a u * gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))
        = ∫ u : ι → ℝ, (Real.sqrt t)⁻¹ * (dot a u * gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)))
      from (integral_const_mul _ _).symm]
  rw [← integral_add (h_int_lin.const_mul _) h_int_rem]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  ring

end NumeratorSplit

section CoerciveDomination

/-- **Algebraic identity**: `gaussianWeight H u · exp(-rescaledPerturbation V H t u)
= exp(-(t · V ((√t)⁻¹ u)))`.

Direct from the definitions: the rescaled weight in the original
`exp(-tV)` form. -/
lemma gaussianWeight_mul_exp_neg_s_t
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (t : ℝ) (u : ι → ℝ) :
    gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))
      = Real.exp (-(t * V ((Real.sqrt t)⁻¹ • u))) := by
  rw [rescaled_weight_factor V H t u]

/-- **Coercive domination**: under the coercivity hypothesis
`c · ‖w‖² ≤ V w`, the rescaled weight `gaussianWeight H u · exp(-s_t)`
is bounded above by `exp(-c · ‖u‖²)` for `t > 0`, INDEPENDENT of `t`.

This is the key uniform-in-`t` tail-domination lemma: any polynomial
times the rescaled weight is integrable (against the Lebesgue measure),
with bound independent of `t`, so dominated convergence theorems apply
to the family of integrals indexed by `t`. -/
lemma rescaled_weight_le_coercive
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    {t : ℝ} (ht : 0 < t) (u : ι → ℝ) :
    gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))
      ≤ Real.exp (-(c * ‖u‖ ^ 2)) := by
  rw [gaussianWeight_mul_exp_neg_s_t V H t u]
  -- Goal: exp(-tV((√t)⁻¹ u)) ≤ exp(-c‖u‖²).
  -- Use coercivity: c · ‖(√t)⁻¹ u‖² ≤ V((√t)⁻¹ u), so
  -- ct · ‖(√t)⁻¹ u‖² ≤ tV((√t)⁻¹ u). And ‖(√t)⁻¹ u‖² = (1/t) ‖u‖².
  -- Therefore c · ‖u‖² ≤ tV((√t)⁻¹ u), hence -tV((√t)⁻¹ u) ≤ -c · ‖u‖².
  apply Real.exp_le_exp.mpr
  rw [neg_le_neg_iff]
  -- Goal: c · ‖u‖² ≤ t · V((√t)⁻¹ • u).
  have h_coer_at : c * ‖(Real.sqrt t)⁻¹ • u‖ ^ 2 ≤ V ((Real.sqrt t)⁻¹ • u) :=
    h_coer ((Real.sqrt t)⁻¹ • u)
  have h_norm_sq : ‖(Real.sqrt t)⁻¹ • u‖ ^ 2 = ‖u‖ ^ 2 / t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < (Real.sqrt t)⁻¹), mul_pow]
    rw [inv_pow, Real.sq_sqrt ht.le]
    field_simp
  rw [h_norm_sq] at h_coer_at
  -- h_coer_at : c · (‖u‖²/t) ≤ V((√t)⁻¹ • u).
  -- Multiply by t > 0: c · ‖u‖² ≤ t · V((√t)⁻¹ • u). ✓
  have ht_le : c * ‖u‖ ^ 2 ≤ t * V ((Real.sqrt t)⁻¹ • u) := by
    have := mul_le_mul_of_nonneg_left h_coer_at ht.le
    rw [show t * (c * (‖u‖ ^ 2 / t)) = c * ‖u‖ ^ 2 from by field_simp] at this
    exact this
  exact ht_le

/-- **Coordinate bound by sup-norm**: `|u i| ≤ ‖u‖` for the standard
Pi sup-norm. (Mathlib's `norm_le_pi_norm`, restated.) -/
lemma abs_apply_le_norm (u : ι → ℝ) (i : ι) : |u i| ≤ ‖u‖ := by
  have := norm_le_pi_norm u i
  simpa [Real.norm_eq_abs] using this

/-- Sum-of-squares bounded by `card ι · ‖u‖²` (componentwise sup bound). -/
lemma sum_sq_le_card_mul_sq_norm (u : ι → ℝ) :
    ∑ i, (u i) ^ 2 ≤ Fintype.card ι * ‖u‖ ^ 2 := by
  have h_each : ∀ i : ι, (u i) ^ 2 ≤ ‖u‖ ^ 2 := by
    intro i
    have h := abs_apply_le_norm u i
    have h_sq : (u i) ^ 2 = |u i| * |u i| := by rw [← sq_abs, sq]
    have h_norm_sq : ‖u‖ ^ 2 = ‖u‖ * ‖u‖ := sq ‖u‖
    rw [h_sq, h_norm_sq]
    exact mul_self_le_mul_self (abs_nonneg _) h
  calc ∑ i, (u i) ^ 2 ≤ ∑ _i : ι, ‖u‖ ^ 2 := Finset.sum_le_sum (fun i _ => h_each i)
    _ = Fintype.card ι * ‖u‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ]
        ring

/-- **Sup-norm-squared bounded by sum-of-squares**: `‖u‖² ≤ ∑ i, u_i²`. -/
lemma sq_norm_le_sum_sq (u : ι → ℝ) :
    ‖u‖ ^ 2 ≤ ∑ i, (u i) ^ 2 := by
  have h_sum_nn : 0 ≤ ∑ i, (u i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [show ‖u‖ ^ 2 = ‖u‖ * ‖u‖ from sq ‖u‖]
  rw [show (∑ i, (u i) ^ 2 : ℝ)
        = Real.sqrt (∑ i, (u i) ^ 2) * Real.sqrt (∑ i, (u i) ^ 2) from
      (Real.mul_self_sqrt h_sum_nn).symm]
  have h_norm_le_sqrt : ‖u‖ ≤ Real.sqrt (∑ i, (u i) ^ 2) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    rw [show |u i| = Real.sqrt ((u i) ^ 2) from by rw [Real.sqrt_sq_eq_abs]]
    apply Real.sqrt_le_sqrt
    exact Finset.single_le_sum (f := fun j => (u j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  exact mul_self_le_mul_self (norm_nonneg _) h_norm_le_sqrt

/-- **Sup-norm coercivity ⇒ sum-of-squares coercivity** (bridge):
under `c · ‖w‖² ≤ V w` (sup-norm) and `Nonempty ι`,
`(c / |ι|) · ∑ w_i² ≤ V w`.

Direct from `‖w‖² ≥ (1/|ι|) · ∑ w_i²`, equivalently the
`sum_sq_le_card_mul_sq_norm` bound. -/
lemma coercive_sum_sq_of_norm
    (V : (ι → ℝ) → ℝ)
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    [hne : Nonempty ι]
    (w : ι → ℝ) :
    (c / Fintype.card ι) * ∑ i, (w i) ^ 2 ≤ V w := by
  have hd : (0 : ℝ) < Fintype.card ι := by
    rw [show (Fintype.card ι : ℝ) = ((Fintype.card ι : ℕ) : ℝ) from rfl]
    exact_mod_cast Fintype.card_pos
  have h_le : ∑ i, (w i) ^ 2 ≤ Fintype.card ι * ‖w‖ ^ 2 :=
    sum_sq_le_card_mul_sq_norm w
  have h1 : (c / Fintype.card ι) * ∑ i, (w i) ^ 2
      ≤ (c / Fintype.card ι) * (Fintype.card ι * ‖w‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h_le (div_nonneg hc_pos.le hd.le)
  have h2 : (c / Fintype.card ι) * (Fintype.card ι * ‖w‖ ^ 2) = c * ‖w‖ ^ 2 := by
    field_simp
  rw [h2] at h1
  exact le_trans h1 (h_coer w)

/-- **Coercive domination, sum-of-squares form**: under `c · ‖w‖² ≤ V w`,
the rescaled weight satisfies

  `gaussianWeight H u · exp(-rescaledPerturbation V H t u)
    ≤ Real.exp (-((c / |ι|) · ∑ i, u_i²))`

uniformly in `t > 0`. The sum-of-squares form connects directly to
`integrable_exp_neg_const_mul_sum_sq` from `Multi/GaussianDomination.lean`,
giving polynomial-times-rescaled-weight integrability uniformly in `t`. -/
lemma rescaled_weight_le_sum_sq_coercive
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    [Nonempty ι]
    {t : ℝ} (ht : 0 < t) (u : ι → ℝ) :
    gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))
      ≤ Real.exp (-((c / Fintype.card ι) * ∑ i, (u i) ^ 2)) := by
  rw [gaussianWeight_mul_exp_neg_s_t V H t u]
  apply Real.exp_le_exp.mpr
  rw [neg_le_neg_iff]
  -- Goal: (c / |ι|) · ∑ u_i² ≤ t · V((√t)⁻¹ u).
  have h_coer_at := coercive_sum_sq_of_norm V hc_pos h_coer ((Real.sqrt t)⁻¹ • u)
  -- h_coer_at : (c / |ι|) · ∑ ((√t)⁻¹ u i)² ≤ V ((√t)⁻¹ • u).
  have h_sum_sq : ∑ i, ((Real.sqrt t)⁻¹ • u) i ^ 2
      = (∑ i, (u i) ^ 2) / t := by
    have h_each : ∀ i, ((Real.sqrt t)⁻¹ • u) i ^ 2 = (u i) ^ 2 / t := by
      intro i
      rw [Pi.smul_apply, smul_eq_mul, mul_pow, inv_pow, Real.sq_sqrt ht.le]
      ring
    rw [show (∑ i, ((Real.sqrt t)⁻¹ • u) i ^ 2) = ∑ i, (u i) ^ 2 / t from by
      apply Finset.sum_congr rfl; intro i _; exact h_each i]
    rw [Finset.sum_div]
  rw [h_sum_sq] at h_coer_at
  -- Multiply h_coer_at by t > 0.
  have h := mul_le_mul_of_nonneg_left h_coer_at ht.le
  rw [show t * ((c / Fintype.card ι) * ((∑ i, (u i) ^ 2) / t))
        = (c / Fintype.card ι) * ∑ i, (u i) ^ 2 from by field_simp] at h
  exact h

end CoerciveDomination

section CoerciveIntegrability

open MeasureTheory

/-- Continuity of `quadForm H` as a function on `ι → ℝ`. -/
lemma continuous_quadForm (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    Continuous (fun u : ι → ℝ => quadForm H u) := by
  unfold quadForm
  apply continuous_finset_sum
  intro i _
  exact (continuous_apply i).mul ((continuous_apply i).comp H.continuous)

/-- Continuity of `gaussianWeight H`. -/
lemma continuous_gaussianWeight (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    Continuous (fun u : ι → ℝ => gaussianWeight H u) := by
  unfold gaussianWeight
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_quadForm H))

/-- Continuity of `rescaledPerturbation V H t` (assuming continuous `V`). -/
lemma continuous_rescaledPerturbation
    {V : (ι → ℝ) → ℝ} (hV : Continuous V) (H : (ι → ℝ) →L[ℝ] (ι → ℝ)) (t : ℝ) :
    Continuous (fun u : ι → ℝ => rescaledPerturbation V H t u) := by
  unfold rescaledPerturbation
  refine (continuous_const.mul (hV.comp ?_)).sub
    (continuous_const.mul (continuous_quadForm H))
  exact continuous_const.smul continuous_id

/-- **Integrability of the rescaled weight under coercivity**: for any
`t > 0`, `gW · exp(-rescaledPerturbation)` is integrable, dominated by
`exp(-((c/|ι|) · ∑ u_i²))` from Phase 2. -/
lemma integrable_rescaled_weight
    (V : (ι → ℝ) → ℝ) (hV_cont : Continuous V) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    [Nonempty ι]
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))) := by
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hd : (0 : ℝ) < (c / Fintype.card ι) := div_pos hc_pos hcard
  have h_dom :=
    integrable_exp_neg_const_mul_sum_sq (ι := ι) (c := c / Fintype.card ι) hd
  refine h_dom.mono' ?_ ?_
  · -- AE strongly measurable from continuity.
    have h_cont :
        Continuous (fun u : ι → ℝ =>
          gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))) :=
      (continuous_gaussianWeight H).mul
        (Real.continuous_exp.comp
          (continuous_rescaledPerturbation hV_cont H t).neg)
    exact h_cont.aestronglyMeasurable
  · filter_upwards with u
    have h_le := rescaled_weight_le_sum_sq_coercive V H hc_pos h_coer ht u
    have h_lhs_nn : 0 ≤ gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) :=
      mul_nonneg (gaussianWeight_pos H u).le (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg h_lhs_nn]
    exact h_le

/-- Integrability of `(∑ u_i²) · exp(-c · ∑ u_k²)`: directly from
Phase 2's diagonal second-moment integrability summed over indices. -/
lemma integrable_sum_sq_mul_exp_neg_const_mul_sum_sq
    {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ι → ℝ =>
      (∑ i, (u i) ^ 2) * Real.exp (-(c * ∑ k, (u k) ^ 2))) := by
  have h_each : ∀ i : ι,
      Integrable (fun u : ι → ℝ =>
        (u i) ^ 2 * Real.exp (-(c * ∑ k, (u k) ^ 2))) := by
    intro i
    have h := integrable_coord_mul_coord_mul_exp_neg_const_mul_sum_sq
      (ι := ι) (c := c) hc i i
    apply h.congr
    filter_upwards with u
    show u i * u i * Real.exp (-(c * ∑ k, u k ^ 2))
      = u i ^ 2 * Real.exp (-(c * ∑ k, u k ^ 2))
    ring
  have h_sum :
      Integrable (fun u : ι → ℝ =>
        ∑ i, (u i) ^ 2 * Real.exp (-(c * ∑ k, (u k) ^ 2))) :=
    integrable_finset_sum Finset.univ (fun i _ => h_each i)
  apply h_sum.congr
  filter_upwards with u
  show ∑ i, (u i) ^ 2 * Real.exp (-(c * ∑ k, u k ^ 2))
    = (∑ i, (u i) ^ 2) * Real.exp (-(c * ∑ k, u k ^ 2))
  rw [Finset.sum_mul]

/-- **Integrability of `‖u‖² · rescaledWeight`** under coercivity:
`u ↦ ‖u‖² · gaussianWeight H u · exp(-rescaledPerturbation V H t u)`
is integrable, dominated by `‖u‖² · exp(-((c/|ι|) · ∑ u_i²))` ≤
`(∑ u_i²) · exp(-((c/|ι|) · ∑ u_i²))` from Phase 2. -/
lemma integrable_sq_norm_mul_rescaled_weight
    (V : (ι → ℝ) → ℝ) (hV_cont : Continuous V) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    [Nonempty ι]
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      ‖u‖ ^ 2 * (gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)))) := by
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hd : (0 : ℝ) < (c / Fintype.card ι) := div_pos hc_pos hcard
  have h_dom_int :=
    integrable_sum_sq_mul_exp_neg_const_mul_sum_sq (ι := ι)
      (c := c / Fintype.card ι) hd
  refine h_dom_int.mono' ?_ ?_
  · -- AE strongly measurable.
    have h_cont :
        Continuous (fun u : ι → ℝ =>
          ‖u‖ ^ 2 *
            (gaussianWeight H u *
              Real.exp (-(rescaledPerturbation V H t u)))) :=
      (continuous_norm.pow 2).mul
        ((continuous_gaussianWeight H).mul
          (Real.continuous_exp.comp
            (continuous_rescaledPerturbation hV_cont H t).neg))
    exact h_cont.aestronglyMeasurable
  · filter_upwards with u
    have h_rw_le := rescaled_weight_le_sum_sq_coercive V H hc_pos h_coer ht u
    have h_norm_sq_le : ‖u‖ ^ 2 ≤ ∑ i, (u i) ^ 2 := sq_norm_le_sum_sq u
    have h_norm_sq_nn : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
    have h_rw_nn : 0 ≤ gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) :=
      mul_nonneg (gaussianWeight_pos H u).le (Real.exp_pos _).le
    have h_lhs_nn : 0 ≤ ‖u‖ ^ 2 *
        (gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u))) :=
      mul_nonneg h_norm_sq_nn h_rw_nn
    rw [Real.norm_eq_abs, abs_of_nonneg h_lhs_nn]
    -- ‖u‖² · rescaledW ≤ ‖u‖² · exp(-(c/|ι|) · ∑ u_i²) ≤ (∑ u_i²) · exp(...)
    calc ‖u‖ ^ 2 * (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)))
        ≤ ‖u‖ ^ 2 *
            Real.exp (-((c / Fintype.card ι) * ∑ i, (u i) ^ 2)) :=
          mul_le_mul_of_nonneg_left h_rw_le h_norm_sq_nn
      _ ≤ (∑ i, (u i) ^ 2) *
            Real.exp (-((c / Fintype.card ι) * ∑ i, (u i) ^ 2)) :=
          mul_le_mul_of_nonneg_right h_norm_sq_le (Real.exp_pos _).le

/-- **Coordinate moment integrability against the rescaled weight**: for
each `i`, `u i · rescaledWeight` is integrable. Proved via dominated
convergence using the absolute-value bound and Phase 2's first-moment
Gaussian integrability. -/
lemma integrable_coord_mul_rescaled_weight
    (V : (ι → ℝ) → ℝ) (hV_cont : Continuous V) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    [Nonempty ι]
    {t : ℝ} (ht : 0 < t) (i : ι) :
    Integrable (fun u : ι → ℝ =>
      u i * (gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)))) := by
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hd : (0 : ℝ) < (c / Fintype.card ι) := div_pos hc_pos hcard
  have h_dom_int := integrable_coord_mul_exp_neg_const_mul_sum_sq
    (ι := ι) (c := c / Fintype.card ι) hd i
  -- `h_dom_int.norm` is `Integrable ‖u_i · exp(-...)‖ = Integrable |u_i| · exp(-...)`.
  have h_abs_dom : Integrable (fun u : ι → ℝ =>
      |u i| * Real.exp (-((c / Fintype.card ι) * ∑ k, (u k) ^ 2))) := by
    apply h_dom_int.norm.congr
    filter_upwards with u
    have h_exp_pos : 0 < Real.exp (-((c / Fintype.card ι) * ∑ k, (u k) ^ 2)) :=
      Real.exp_pos _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos h_exp_pos]
  refine h_abs_dom.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    refine (continuous_apply i).mul ((continuous_gaussianWeight H).mul ?_)
    exact Real.continuous_exp.comp
      (continuous_rescaledPerturbation hV_cont H t).neg
  · filter_upwards with u
    have h_rw_le := rescaled_weight_le_sum_sq_coercive V H hc_pos h_coer ht u
    have h_rw_nn : 0 ≤ gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) :=
      mul_nonneg (gaussianWeight_pos H u).le (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h_rw_nn]
    -- |u i| · rescaledW ≤ |u i| · exp(-(c/|ι|) · ∑ u_i²).
    exact mul_le_mul_of_nonneg_left h_rw_le (abs_nonneg _)

/-- **Pointwise triangle-style bound** for the partition integrand:
`|gW(u) · (exp(-s_t(u)) - 1)| ≤ gW(u) + exp(-(c·‖u‖²))`
under coercivity. This is the simplest absolute pointwise bound that
makes `gW · (exp(-s_t) - 1)` dominated by an integrable function
uniformly in `t > 0`. -/
lemma abs_gaussianWeight_mul_exp_sub_one_le_uniform
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    {t : ℝ} (ht : 0 < t) (u : ι → ℝ) :
    |gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
      ≤ gaussianWeight H u + Real.exp (-(c * ‖u‖ ^ 2)) := by
  set g := gaussianWeight H u
  set r := Real.exp (-(rescaledPerturbation V H t u))
  have hg_pos : 0 < g := gaussianWeight_pos H u
  have hr_pos : 0 < r := Real.exp_pos _
  -- |g · (r - 1)| ≤ g · |r - 1| ≤ g · (r + 1) = g·r + g.
  -- And g·r ≤ exp(-c‖u‖²) by `rescaled_weight_le_coercive`.
  have h_gr_le : g * r ≤ Real.exp (-(c * ‖u‖ ^ 2)) :=
    rescaled_weight_le_coercive V H hc_pos h_coer ht u
  rw [abs_mul, abs_of_pos hg_pos]
  calc g * |r - 1| ≤ g * (r + 1) := by
        apply mul_le_mul_of_nonneg_left _ hg_pos.le
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · linarith
        · have h_r_nn : 0 ≤ r := hr_pos.le
          linarith
    _ = g * r + g := by ring
    _ ≤ Real.exp (-(c * ‖u‖ ^ 2)) + g := by linarith
    _ = g + Real.exp (-(c * ‖u‖ ^ 2)) := by ring

end CoerciveIntegrability

section PairSplit

open MeasureTheory

/-- **Pointwise pair-product expansion** for two observables φ, ψ with
gradients a, b: writing `r_φ(w) := φ(w) - dot a w` and similarly `r_ψ`,

  `φ((√t)⁻¹ u) · ψ((√t)⁻¹ u)
    = (1/t) · dot a u · dot b u
      + (√t)⁻¹ · dot a u · r_ψ((√t)⁻¹ u)
      + (√t)⁻¹ · r_φ((√t)⁻¹ u) · dot b u
      + r_φ((√t)⁻¹ u) · r_ψ((√t)⁻¹ u)`.

Direct algebraic identity. Used in the **pair asymptote** to extract
the `(1/t) · ⟨a, Hinv b⟩` leading term and bound the residuals. -/
lemma pair_product_expansion
    (φ ψ : (ι → ℝ) → ℝ) (a b : ι → ℝ) (t : ℝ) (ht : 0 < t) (u : ι → ℝ) :
    φ ((Real.sqrt t)⁻¹ • u) * ψ ((Real.sqrt t)⁻¹ • u)
      = (1/t) * (dot a u * dot b u)
        + (Real.sqrt t)⁻¹ * dot a u *
            (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u)
        + (Real.sqrt t)⁻¹ * dot b u *
            (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u)
        + (φ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot a u) *
            (ψ ((Real.sqrt t)⁻¹ • u) - (Real.sqrt t)⁻¹ * dot b u) := by
  -- Set X = φ((√t)⁻¹ u), A = (√t)⁻¹ · dot a u (analogously Y, B).
  -- Then φψ = X · Y, and the RHS is (1/t) · (a·u)(b·u) + A · (Y - B) + B · (X - A) + (X - A)(Y - B).
  -- Expand: (X - A)(Y - B) = XY - XB - AY + AB. So:
  --  RHS = AB + A·(Y - B) + B·(X - A) + (X - A)(Y - B)
  --      = AB + AY - AB + BX - AB + XY - XB - AY + AB
  --      = XY. ✓
  -- Note (1/t) · (a·u)(b·u) = ((√t)⁻¹)² · dot a u · dot b u = A · B.
  have h_t_inv_sq : (1/t : ℝ) = ((Real.sqrt t)⁻¹) ^ 2 := by
    rw [inv_pow, Real.sq_sqrt ht.le]; ring
  rw [show (1/t : ℝ) * (dot a u * dot b u) =
      ((Real.sqrt t)⁻¹ * dot a u) * ((Real.sqrt t)⁻¹ * dot b u) from by
    rw [h_t_inv_sq]; ring]
  ring

end PairSplit

end Laplace.Multi
