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

section QuadFormLowerBound

/-- **Quadratic lower bound for `(1/2) · quadForm H`** under
coercivity + local cubic remainder hypotheses (the analytic content of
`PotentialApprox`). Concretely: `(c/2) · ‖u‖² ≤ (1/2) · quadForm H u`
for all `u`. -/
lemma quadForm_lower_bound
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    {R : ℝ} (hR_pos : 0 < R)
    {C : ℝ} (hC_nn : 0 ≤ C)
    (h_local : ∀ w : ι → ℝ, ‖w‖ ≤ R →
      |V w - (1/2) * quadForm H w| ≤ C * ‖w‖ ^ 3) :
    ∀ u : ι → ℝ, (c/2) * ‖u‖ ^ 2 ≤ (1/2) * quadForm H u := by
  -- Choose r := min R (c / (2 * (C + 1))).
  set r := min R (c / (2 * (C + 1))) with hr_def
  have hC1_pos : (0 : ℝ) < C + 1 := by linarith
  have hr_pos : 0 < r := lt_min hR_pos (by positivity)
  have hr_le_R : r ≤ R := min_le_left _ _
  have hr_le_bound : r ≤ c / (2 * (C + 1)) := min_le_right _ _
  have hCr_le : C * r ≤ c / 2 := by
    calc C * r ≤ C * (c / (2 * (C + 1))) :=
          mul_le_mul_of_nonneg_left hr_le_bound hC_nn
      _ = (C / (C + 1)) * (c / 2) := by field_simp
      _ ≤ 1 * (c / 2) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith : (0:ℝ) ≤ c/2)
          rw [div_le_one hC1_pos]
          linarith
      _ = c / 2 := one_mul _
  -- Step 1: bound holds on ‖w‖ ≤ r.
  have h_local_bound : ∀ w : ι → ℝ, ‖w‖ ≤ r →
      (c / 2) * ‖w‖ ^ 2 ≤ (1/2) * quadForm H w := by
    intro w hw
    have hw_nn : 0 ≤ ‖w‖ := norm_nonneg _
    have h_coer_w := h_coer w  -- c · ‖w‖² ≤ V w
    have h_local_w := h_local w (le_trans hw hr_le_R)
    -- |V w - (1/2) quadForm H w| ≤ C ‖w‖³.
    have h_lb : V w - C * ‖w‖ ^ 3 ≤ (1/2) * quadForm H w := by
      have h := abs_le.mp h_local_w
      linarith
    -- C ‖w‖³ = C · ‖w‖² · ‖w‖ ≤ C · ‖w‖² · r ≤ (c/2) · ‖w‖².
    have h_cube_le : C * ‖w‖ ^ 3 ≤ (c / 2) * ‖w‖ ^ 2 := by
      have h_cube : ‖w‖ ^ 3 = ‖w‖ ^ 2 * ‖w‖ := by ring
      rw [h_cube]
      calc C * (‖w‖ ^ 2 * ‖w‖) = (C * ‖w‖) * ‖w‖ ^ 2 := by ring
        _ ≤ (C * r) * ‖w‖ ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hw hC_nn) (sq_nonneg _)
        _ ≤ (c / 2) * ‖w‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hCr_le (sq_nonneg _)
    -- Combine: V w ≥ c‖w‖², so (1/2) quadForm H w ≥ V w - C‖w‖³ ≥ c‖w‖² - (c/2)‖w‖² = (c/2)‖w‖².
    linarith
  -- Step 2: extend to all u by homogeneity.
  intro u
  by_cases hu : u = 0
  · subst hu; simp [quadForm]
  · -- u ≠ 0: set λ := r / ‖u‖ > 0, w := λ • u, ‖w‖ = r.
    have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    set lam : ℝ := r / ‖u‖ with hlam_def
    have hlam_pos : 0 < lam := div_pos hr_pos hu_norm_pos
    set w : ι → ℝ := lam • u with hw_def
    have hw_norm : ‖w‖ = r := by
      rw [hw_def, norm_smul, Real.norm_eq_abs, abs_of_pos hlam_pos, hlam_def]
      field_simp
    have h_w_in : ‖w‖ ≤ r := le_of_eq hw_norm
    have h_w_bound := h_local_bound w h_w_in
    -- (c/2) · r² ≤ (1/2) · quadForm H w = (1/2) · lam² · quadForm H u.
    rw [hw_norm] at h_w_bound
    rw [show (1/2 : ℝ) * quadForm H w = (1/2) * (lam ^ 2 * quadForm H u) from by
      rw [hw_def, quadForm_smul]] at h_w_bound
    -- (c/2) r² ≤ (lam²/2) · quadForm H u, i.e., (c/2) · ‖u‖² ≤ (1/2) quadForm H u.
    -- Since lam² = r²/‖u‖², (lam²/2) · quadForm = (r²/(2‖u‖²)) · quadForm.
    -- So (c/2) r² ≤ (r²/(2‖u‖²)) · quadForm, i.e., (c/2) ‖u‖² ≤ (1/2) quadForm.
    have h_lam_sq : lam ^ 2 = r ^ 2 / ‖u‖ ^ 2 := by
      rw [hlam_def]; ring
    rw [h_lam_sq] at h_w_bound
    -- Now h_w_bound : (c/2) · r² ≤ (1/2) · ((r²/‖u‖²) · quadForm H u)
    -- Rearrange: (c/2) · ‖u‖² ≤ (1/2) · quadForm H u.
    have hr_sq_pos : 0 < r ^ 2 := by positivity
    have h_u_sq_pos : 0 < ‖u‖ ^ 2 := by positivity
    have h_eq : (1 / 2 : ℝ) * (r ^ 2 / ‖u‖ ^ 2 * quadForm H u)
        = (r ^ 2 / ‖u‖ ^ 2) * ((1 / 2) * quadForm H u) := by ring
    rw [h_eq] at h_w_bound
    -- (c/2) · r² ≤ (r²/‖u‖²) · ((1/2) quadForm). Multiply both sides by ‖u‖²/r²:
    -- (c/2) · ‖u‖² ≤ (1/2) · quadForm.
    have h_div :
        (c/2) * ‖u‖ ^ 2 = (c/2) * r ^ 2 * (‖u‖ ^ 2 / r ^ 2) := by
      field_simp
    rw [h_div]
    have h_target : (c/2) * r ^ 2 * (‖u‖ ^ 2 / r ^ 2)
        ≤ (r ^ 2 / ‖u‖ ^ 2) * ((1 / 2) * quadForm H u) * (‖u‖ ^ 2 / r ^ 2) := by
      apply mul_le_mul_of_nonneg_right h_w_bound
      positivity
    have h_cancel : (r ^ 2 / ‖u‖ ^ 2) * ((1 / 2) * quadForm H u)
            * (‖u‖ ^ 2 / r ^ 2) = (1 / 2) * quadForm H u := by
      field_simp
    rw [h_cancel] at h_target
    exact h_target

/-- **Gaussian weight bounded by an explicit Gaussian** under the
quadratic lower bound: if `κ_H · ‖u‖² ≤ (1/2) quadForm H u`,
then `gaussianWeight H u ≤ exp(-(κ_H · ‖u‖²))`. -/
lemma gaussianWeight_le_exp_neg_const_sq
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    {κ : ℝ}
    (h_lb : ∀ u : ι → ℝ, κ * ‖u‖ ^ 2 ≤ (1/2) * quadForm H u)
    (u : ι → ℝ) :
    gaussianWeight H u ≤ Real.exp (-(κ * ‖u‖ ^ 2)) := by
  unfold gaussianWeight
  apply Real.exp_le_exp.mpr
  have := h_lb u
  linarith

/-- **Linear-functional bound by sup-norm**: `|⟨a, u⟩| ≤ (∑ |a_i|) · ‖u‖`
(sup-norm), via the triangle inequality and `abs_apply_le_norm`. -/
lemma abs_dot_le_l1_mul_norm (a u : ι → ℝ) :
    |dot a u| ≤ (∑ i, |a i|) * ‖u‖ := by
  unfold dot
  calc |∑ i, a i * u i|
      ≤ ∑ i, |a i * u i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |u i| := by
        apply Finset.sum_congr rfl
        intro i _; rw [abs_mul]
    _ ≤ ∑ i, |a i| * ‖u‖ := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (abs_apply_le_norm u i) (abs_nonneg _)
    _ = (∑ i, |a i|) * ‖u‖ := by rw [Finset.sum_mul]

end QuadFormLowerBound

section PolynomialGaussianDecay

/-- For `x ≥ 0`, `x ≤ exp x`. Direct from `Real.add_one_le_exp`. -/
lemma le_exp_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x ≤ Real.exp x := by
  have h := Real.add_one_le_exp x
  have hone : (1 : ℝ) ≤ Real.exp x := by
    calc (1 : ℝ) ≤ 1 + 0 := by linarith
      _ ≤ 1 + x := by linarith
      _ ≤ Real.exp x := by linarith
  linarith

/-- For `x ≥ 0` and `k : ℕ`, `x^k ≤ exp(k · x)`. -/
lemma pow_le_exp_nsmul_of_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    x ^ k ≤ Real.exp (k * x) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hexp_pos : 0 < Real.exp ((n:ℝ) * x) := Real.exp_pos _
    have hx_le : x ≤ Real.exp x := le_exp_self_of_nonneg hx
    calc x ^ (n + 1) = x ^ n * x := by ring
      _ ≤ Real.exp ((n:ℝ) * x) * x :=
          mul_le_mul_of_nonneg_right ih hx
      _ ≤ Real.exp ((n:ℝ) * x) * Real.exp x :=
          mul_le_mul_of_nonneg_left hx_le hexp_pos.le
      _ = Real.exp ((n:ℝ) * x + x) := (Real.exp_add _ _).symm
      _ = Real.exp ((↑(n + 1) : ℝ) * x) := by
          congr 1; push_cast; ring

/-- For `α > 0`, `k : ℕ`, and `x ≥ 0`,
`x^k · exp(-α · x²) ≤ exp(k²/(4α))`. -/
lemma pow_mul_exp_neg_sq_le_const
    (k : ℕ) {α : ℝ} (hα_pos : 0 < α) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k * Real.exp (-(α * x ^ 2)) ≤ Real.exp ((k:ℝ) ^ 2 / (4 * α)) := by
  -- x^k · exp(-αx²) ≤ exp(kx) · exp(-αx²) = exp(kx - αx²) ≤ exp(k²/(4α)).
  have h_pow_le := pow_le_exp_nsmul_of_nonneg hx k
  have hexp_neg_sq_pos : 0 < Real.exp (-(α * x ^ 2)) := Real.exp_pos _
  -- Bound on quadratic: kx - αx² ≤ k²/(4α).
  -- α · (x - k/(2α))² ≥ 0 ⟹ αx² - kx + k²/(4α) ≥ 0 ⟹ kx - αx² ≤ k²/(4α).
  have h_quad : (k:ℝ) * x - α * x ^ 2 ≤ (k:ℝ) ^ 2 / (4 * α) := by
    have h_sq : 0 ≤ α * (x - (k:ℝ) / (2 * α)) ^ 2 :=
      mul_nonneg hα_pos.le (sq_nonneg _)
    have h_expand : α * (x - (k:ℝ) / (2 * α)) ^ 2
        = α * x ^ 2 - (k:ℝ) * x + (k:ℝ) ^ 2 / (4 * α) := by
      have h2α_ne : (2 * α : ℝ) ≠ 0 := by positivity
      have h4α_ne : (4 * α : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    linarith
  -- Combine.
  calc x ^ k * Real.exp (-(α * x ^ 2))
      ≤ Real.exp ((k:ℝ) * x) * Real.exp (-(α * x ^ 2)) :=
        mul_le_mul_of_nonneg_right h_pow_le hexp_neg_sq_pos.le
    _ = Real.exp ((k:ℝ) * x + -(α * x ^ 2)) := by rw [← Real.exp_add]
    _ = Real.exp ((k:ℝ) * x - α * x ^ 2) := by ring_nf
    _ ≤ Real.exp ((k:ℝ) ^ 2 / (4 * α)) := Real.exp_le_exp.mpr h_quad

/-- **Polynomial-Gaussian decay (scalar form)**: for `α > 0`, `k : ℕ`,
and `x ≥ 0`,
`x^k · exp(-α · x²) ≤ M_k · exp(-(α/2) · x²)`
with `M_k := exp(k²/(2α))`. -/
lemma pow_mul_exp_neg_sq_le_half_decay
    (k : ℕ) {α : ℝ} (hα_pos : 0 < α) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k * Real.exp (-(α * x ^ 2))
      ≤ Real.exp ((k:ℝ) ^ 2 / (2 * α)) * Real.exp (-((α / 2) * x ^ 2)) := by
  -- x^k · exp(-α·x²) = (x^k · exp(-(α/2)·x²)) · exp(-(α/2)·x²) ≤ M_k · exp(-(α/2)·x²).
  -- Use pow_mul_exp_neg_sq_le_const with α' = α/2.
  have hα2_pos : 0 < α / 2 := by linarith
  have h_const := pow_mul_exp_neg_sq_le_const k hα2_pos hx
  -- h_const : x^k · exp(-((α/2) * x²)) ≤ exp(k²/(4 · α/2)) = exp(k²/(2α)).
  have h_4α2 : (4 : ℝ) * (α / 2) = 2 * α := by ring
  rw [h_4α2] at h_const
  -- Now: x^k · exp(-((α/2) · x²)) ≤ exp(k² / (2α)).
  -- Multiply both sides by exp(-(α/2) · x²).
  have hexp_pos : 0 < Real.exp (-((α / 2) * x ^ 2)) := Real.exp_pos _
  have h_split :
      x ^ k * Real.exp (-(α * x ^ 2))
        = (x ^ k * Real.exp (-((α / 2) * x ^ 2)))
            * Real.exp (-((α / 2) * x ^ 2)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [h_split]
  exact mul_le_mul_of_nonneg_right h_const hexp_pos.le

end PolynomialGaussianDecay

section PolynomialMomentIntegrability

open MeasureTheory

/-- **Sup-norm² ≥ (1/|ι|) · ∑ u_i²**: derived directly from
`sum_sq_le_card_mul_sq_norm`. -/
lemma sq_norm_ge_sum_sq_div_card [hne : Nonempty ι] (u : ι → ℝ) :
    (1 / Fintype.card ι) * (∑ i, (u i) ^ 2) ≤ ‖u‖ ^ 2 := by
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h_le : ∑ i, (u i) ^ 2 ≤ Fintype.card ι * ‖u‖ ^ 2 := sum_sq_le_card_mul_sq_norm u
  have h := mul_le_mul_of_nonneg_left h_le (le_of_lt (one_div_pos.mpr hcard))
  rw [show (1 / Fintype.card ι : ℝ) * (Fintype.card ι * ‖u‖ ^ 2)
        = ‖u‖ ^ 2 from by field_simp] at h
  exact h

/-- **`‖u‖^k · gaussianWeight H u · exp(-rescaledPerturbation V H t u)`
is integrable** under coercivity, for any `k : ℕ` and `t > 0`.

Bound chain:
1. `gW · exp(-s_t) ≤ exp(-c · ‖u‖²)` (uniform-in-`t` coercive domination).
2. `‖u‖^k · exp(-c · ‖u‖²) ≤ M_k · exp(-(c/2) · ‖u‖²)` (poly-Gaussian decay).
3. `‖u‖² ≥ (1/|ι|) · ∑ u_i²`, so `exp(-(c/2) · ‖u‖²) ≤ exp(-(c/(2|ι|)) · ∑ u_i²)`.
4. The latter is integrable from Phase 2.
-/
lemma integrable_pow_norm_mul_rescaled_weight
    (V : (ι → ℝ) → ℝ) (hV_cont : Continuous V) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    {c : ℝ} (hc_pos : 0 < c)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    [Nonempty ι]
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ι → ℝ =>
      ‖u‖ ^ k * (gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)))) := by
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hc_half_card_pos : (0 : ℝ) < c / (2 * Fintype.card ι) := by positivity
  -- Dominating function: `M_k · exp(-(c/(2|ι|)) · ∑ u_i²)`.
  set M_k : ℝ := Real.exp ((k:ℝ) ^ 2 / (2 * c)) with hM_def
  have hM_nn : 0 ≤ M_k := (Real.exp_pos _).le
  have h_dom_int :=
    (integrable_exp_neg_const_mul_sum_sq (ι := ι) hc_half_card_pos).const_mul M_k
  refine h_dom_int.mono' ?_ ?_
  · -- AE strongly measurable: continuous.
    have h_cont : Continuous (fun u : ι → ℝ =>
        ‖u‖ ^ k *
          (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)))) :=
      (continuous_norm.pow k).mul
        ((continuous_gaussianWeight H).mul
          (Real.continuous_exp.comp
            (continuous_rescaledPerturbation hV_cont H t).neg))
    exact h_cont.aestronglyMeasurable
  · filter_upwards with u
    -- Step 1: gW · exp(-s_t) ≤ exp(-c · ‖u‖²).
    have h_rw_le := rescaled_weight_le_coercive V H hc_pos h_coer ht u
    have h_rw_nn : 0 ≤ gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)) :=
      mul_nonneg (gaussianWeight_pos H u).le (Real.exp_pos _).le
    have h_norm_pow_nn : 0 ≤ ‖u‖ ^ k := pow_nonneg (norm_nonneg _) k
    have h_lhs_nn : 0 ≤ ‖u‖ ^ k * (gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) :=
      mul_nonneg h_norm_pow_nn h_rw_nn
    -- Step 2: ‖u‖^k · exp(-c‖u‖²) ≤ M_k · exp(-(c/2)‖u‖²).
    have h_poly_decay := pow_mul_exp_neg_sq_le_half_decay k hc_pos (norm_nonneg u)
    -- h_poly_decay : ‖u‖^k · exp(-(c · ‖u‖²)) ≤ exp(k²/(2c)) · exp(-(c/2) · ‖u‖²)
    -- Step 3: exp(-(c/2)‖u‖²) ≤ exp(-(c/(2|ι|)) · ∑ u_i²).
    have h_sum_to_norm := sq_norm_ge_sum_sq_div_card u
    -- `(1/|ι|) · ∑ ≤ ‖u‖²`, so `(c/2) · ‖u‖² ≥ (c/(2|ι|)) · ∑ u_i²`,
    -- so `exp(-(c/2)‖u‖²) ≤ exp(-(c/(2|ι|)) · ∑ u_i²)`.
    have h_exp_le : Real.exp (-((c / 2) * ‖u‖ ^ 2))
        ≤ Real.exp (-((c / (2 * Fintype.card ι)) * ∑ i, (u i) ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have : (c / 2) * ‖u‖ ^ 2 ≥ (c / (2 * Fintype.card ι)) * ∑ i, (u i) ^ 2 := by
        have hbound : (1 / (Fintype.card ι : ℝ)) * (∑ i, (u i) ^ 2) ≤ ‖u‖ ^ 2 := h_sum_to_norm
        have h_mul := mul_le_mul_of_nonneg_left hbound (by linarith : (0:ℝ) ≤ c/2)
        rw [show (c / 2 : ℝ) * ((1 / (Fintype.card ι : ℝ)) * (∑ i, (u i) ^ 2))
              = (c / (2 * Fintype.card ι)) * ∑ i, (u i) ^ 2 from by
            field_simp] at h_mul
        linarith
      linarith
    -- Combine pieces.
    rw [Real.norm_eq_abs, abs_of_nonneg h_lhs_nn]
    calc ‖u‖ ^ k *
          (gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)))
        ≤ ‖u‖ ^ k * Real.exp (-(c * ‖u‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h_rw_le h_norm_pow_nn
      _ ≤ M_k * Real.exp (-((c / 2) * ‖u‖ ^ 2)) := h_poly_decay
      _ ≤ M_k *
          Real.exp (-((c / (2 * Fintype.card ι)) * ∑ i, (u i) ^ 2)) :=
          mul_le_mul_of_nonneg_left h_exp_le hM_nn

end PolynomialMomentIntegrability

section LocalPartitionBound

/-- **Local pointwise bound for the partition integrand**: under
hypotheses extracted from `PotentialApprox`, on the Taylor-validity
region `‖u‖ ≤ δ · √t` (where `δ` is chosen so that
`local_const · δ ≤ c / 4`),

  `|gaussianWeight H u · (exp(-rescaledPerturbation V H t u) - 1)|
    ≤ (local_const · ‖u‖³ / √t) · exp(-((c/4) · ‖u‖²))`.

Proof chain:
1. `|s_t| ≤ Cs · ‖u‖³ / √t` (rescaled cubic) and on local region
   `‖u‖ ≤ δ √t`, this is `≤ Cs · δ · ‖u‖²` and `Cs · δ ≤ c/4`.
2. So `|s_t| ≤ (c/4) · ‖u‖²` on the local region.
3. `gW ≤ exp(-(c/2) · ‖u‖²)` via `quadForm_lower_bound` +
   `gaussianWeight_le_exp_neg_const_sq`.
4. `|exp(-s_t) - 1| ≤ |s_t| · exp(|s_t|) ≤ (Cs ‖u‖³/√t) · exp((c/4)‖u‖²)`.
5. Combine:
   `gW · |exp(-s_t) - 1|
     ≤ exp(-(c/2)‖u‖²) · (Cs ‖u‖³/√t) · exp((c/4)‖u‖²)
     = (Cs ‖u‖³/√t) · exp(-(c/4)‖u‖²)`. -/
lemma abs_gaussianWeight_mul_exp_sub_one_le_local
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    {c R Cs δ : ℝ}
    (hc_pos : 0 < c)
    (hR_pos : 0 < R) (hCs_nn : 0 ≤ Cs)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    (h_local : ∀ w : ι → ℝ, ‖w‖ ≤ R →
      |V w - (1/2) * quadForm H w| ≤ Cs * ‖w‖ ^ 3)
    (hδ_pos : 0 < δ) (hδ_le_R : δ ≤ R)
    (hδ_const : Cs * δ ≤ c / 4)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ δ * Real.sqrt t) :
    |gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
      ≤ (Cs * ‖u‖ ^ 3 / Real.sqrt t) *
          Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h_norm_nn : 0 ≤ ‖u‖ := norm_nonneg _
  -- Step 1: ‖u‖ ≤ δ · √t ≤ R · √t (via δ ≤ R), so abs_rescaledPerturbation_le applies.
  have hu_le_R_sqrt : ‖u‖ ≤ R * Real.sqrt t :=
    le_trans hu (mul_le_mul_of_nonneg_right hδ_le_R hsqrt_pos.le)
  have h_st_le := abs_rescaledPerturbation_le V H h_local ht u hu_le_R_sqrt
  -- |s_t(u)| ≤ Cs · ‖u‖³ / √t.
  -- Step 2: on local region ‖u‖ ≤ δ √t, ‖u‖³/√t ≤ δ · ‖u‖².
  have h_cube_to_sq : ‖u‖ ^ 3 / Real.sqrt t ≤ δ * ‖u‖ ^ 2 := by
    have h_cube : ‖u‖ ^ 3 = ‖u‖ ^ 2 * ‖u‖ := by ring
    rw [h_cube]
    rw [div_le_iff₀ hsqrt_pos]
    calc ‖u‖ ^ 2 * ‖u‖ ≤ ‖u‖ ^ 2 * (δ * Real.sqrt t) :=
          mul_le_mul_of_nonneg_left hu (sq_nonneg _)
      _ = δ * ‖u‖ ^ 2 * Real.sqrt t := by ring
  -- Step 3: |s_t(u)| ≤ Cs · δ · ‖u‖² ≤ (c/4) · ‖u‖².
  have h_st_le_quart : |rescaledPerturbation V H t u| ≤ (c / 4) * ‖u‖ ^ 2 := by
    calc |rescaledPerturbation V H t u|
        ≤ Cs * ‖u‖ ^ 3 / Real.sqrt t := h_st_le
      _ = Cs * (‖u‖ ^ 3 / Real.sqrt t) := by ring
      _ ≤ Cs * (δ * ‖u‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h_cube_to_sq hCs_nn
      _ = (Cs * δ) * ‖u‖ ^ 2 := by ring
      _ ≤ (c / 4) * ‖u‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hδ_const (sq_nonneg _)
  -- Step 4: gW · exp(|s_t|) ≤ exp(-(c/2)‖u‖²) · exp((c/4)‖u‖²) = exp(-(c/4)‖u‖²).
  have h_gW_le : gaussianWeight H u ≤ Real.exp (-((c / 2) * ‖u‖ ^ 2)) := by
    -- From quadForm_lower_bound: (c/2) ‖u‖² ≤ (1/2) quadForm H u.
    -- So gW = exp(-(1/2) quadForm) ≤ exp(-(c/2) ‖u‖²).
    have h_qlb := quadForm_lower_bound V H hc_pos h_coer hR_pos hCs_nn h_local u
    unfold gaussianWeight
    apply Real.exp_le_exp.mpr
    linarith
  -- Step 5: |exp(-s_t) - 1| ≤ |s_t| · exp(|s_t|) ≤ (Cs ‖u‖³/√t) · exp((c/4) ‖u‖²).
  have h_exp_sub_one_bound :
      |Real.exp (-(rescaledPerturbation V H t u)) - 1|
        ≤ Cs * ‖u‖ ^ 3 / Real.sqrt t *
            Real.exp ((c / 4) * ‖u‖ ^ 2) := by
    calc |Real.exp (-(rescaledPerturbation V H t u)) - 1|
        ≤ |rescaledPerturbation V H t u| *
            Real.exp |rescaledPerturbation V H t u| :=
          abs_exp_neg_sub_one_le _
      _ ≤ (Cs * ‖u‖ ^ 3 / Real.sqrt t) *
            Real.exp ((c / 4) * ‖u‖ ^ 2) := by
          apply mul_le_mul h_st_le _ (Real.exp_pos _).le _
          · apply Real.exp_le_exp.mpr; exact h_st_le_quart
          · positivity
  -- Step 6: gW · |exp(-s_t) - 1| ≤ exp(-(c/2)‖u‖²) · (Cs ‖u‖³/√t) · exp((c/4)‖u‖²)
  --                              = (Cs ‖u‖³/√t) · exp(-(c/4)‖u‖²).
  have h_gW_pos : 0 < gaussianWeight H u := gaussianWeight_pos H u
  rw [abs_mul, abs_of_pos h_gW_pos]
  calc gaussianWeight H u *
          |Real.exp (-(rescaledPerturbation V H t u)) - 1|
      ≤ Real.exp (-((c / 2) * ‖u‖ ^ 2)) *
          ((Cs * ‖u‖ ^ 3 / Real.sqrt t) *
            Real.exp ((c / 4) * ‖u‖ ^ 2)) := by
          apply mul_le_mul h_gW_le h_exp_sub_one_bound (abs_nonneg _)
            (Real.exp_pos _).le
    _ = (Cs * ‖u‖ ^ 3 / Real.sqrt t) *
          (Real.exp (-((c / 2) * ‖u‖ ^ 2)) *
            Real.exp ((c / 4) * ‖u‖ ^ 2)) := by ring
    _ = (Cs * ‖u‖ ^ 3 / Real.sqrt t) *
          Real.exp (-((c / 2) * ‖u‖ ^ 2) + (c / 4) * ‖u‖ ^ 2) := by
          rw [← Real.exp_add]
    _ = (Cs * ‖u‖ ^ 3 / Real.sqrt t) *
          Real.exp (-((c / 4) * ‖u‖ ^ 2)) := by
          congr 2; ring

end LocalPartitionBound

section TailPartitionBound

/-- **Tail pointwise bound** on the partition integrand outside the
local Taylor region: for `‖u‖ > δ · √t`,

  `|gW · (exp(-s_t) - 1)| ≤ 2 · exp(-((c/4) · ‖u‖²)) · exp(-((c · δ²/4) · t))`.

This decomposes the uniform bound (Phase 5.4s) into a Gaussian factor
(integrable) times an explicit `t`-dependent decay factor. The
exponential `exp(-(cδ²/4) · t)` decays faster than any power of `1/√t`,
so the tail contribution to the partition asymptote is `o(1/√t)`. -/
lemma abs_gaussianWeight_mul_exp_sub_one_le_tail
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    {c R Cs : ℝ}
    (hc_pos : 0 < c) (hR_pos : 0 < R) (hCs_nn : 0 ≤ Cs)
    (h_coer : ∀ w : ι → ℝ, c * ‖w‖ ^ 2 ≤ V w)
    (h_local : ∀ w : ι → ℝ, ‖w‖ ≤ R →
      |V w - (1/2) * quadForm H w| ≤ Cs * ‖w‖ ^ 3)
    {δ : ℝ} (hδ_pos : 0 < δ)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : δ * Real.sqrt t < ‖u‖) :
    |gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
      ≤ 2 * Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
          Real.exp (-((c * δ ^ 2 / 4) * t)) := by
  -- First, the uniform bound: |gW · (exp(-s_t) - 1)| ≤ gW + exp(-c‖u‖²).
  have h_uniform :=
    abs_gaussianWeight_mul_exp_sub_one_le_uniform V H hc_pos h_coer ht u
  -- gW ≤ exp(-(c/2)‖u‖²) from quadForm lower bound.
  have h_qlb := quadForm_lower_bound V H hc_pos h_coer hR_pos hCs_nn h_local
  have h_gW_le : gaussianWeight H u ≤ Real.exp (-((c / 2) * ‖u‖ ^ 2)) := by
    unfold gaussianWeight
    apply Real.exp_le_exp.mpr
    have := h_qlb u
    linarith
  -- exp(-c‖u‖²) ≤ exp(-(c/2)‖u‖²) since c ≥ c/2.
  have h_e_le : Real.exp (-(c * ‖u‖ ^ 2)) ≤ Real.exp (-((c / 2) * ‖u‖ ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have h_norm_sq_nn : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
    have : (c / 2) * ‖u‖ ^ 2 ≤ c * ‖u‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ h_norm_sq_nn
      linarith
    linarith
  -- So |gW · (exp(-s_t) - 1)| ≤ 2 · exp(-(c/2)‖u‖²).
  have h_le_2_exp :
      |gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
        ≤ 2 * Real.exp (-((c / 2) * ‖u‖ ^ 2)) := by
    calc |gaussianWeight H u *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
        ≤ gaussianWeight H u + Real.exp (-(c * ‖u‖ ^ 2)) := h_uniform
      _ ≤ Real.exp (-((c / 2) * ‖u‖ ^ 2)) +
            Real.exp (-((c / 2) * ‖u‖ ^ 2)) :=
          add_le_add h_gW_le h_e_le
      _ = 2 * Real.exp (-((c / 2) * ‖u‖ ^ 2)) := by ring
  -- On the tail, ‖u‖² > δ² · t, so (c/2)‖u‖² ≥ (c/4)‖u‖² + (cδ²/4) · t.
  have h_norm_sq_lb : (δ * Real.sqrt t) ^ 2 < ‖u‖ ^ 2 := by
    have h_pos : 0 ≤ δ * Real.sqrt t := by positivity
    have := mul_self_lt_mul_self h_pos hu
    rw [show (δ * Real.sqrt t) * (δ * Real.sqrt t) = (δ * Real.sqrt t) ^ 2 from by ring,
        show ‖u‖ * ‖u‖ = ‖u‖ ^ 2 from by ring] at this
    exact this
  have h_norm_sq_lb' : δ ^ 2 * t < ‖u‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ht.le] at h_norm_sq_lb; exact h_norm_sq_lb
  have h_split : (c / 2) * ‖u‖ ^ 2 ≥
      (c / 4) * ‖u‖ ^ 2 + (c * δ ^ 2 / 4) * t := by
    have h1 : (c / 4) * ‖u‖ ^ 2 + (c * δ ^ 2 / 4) * t
        ≤ (c / 4) * ‖u‖ ^ 2 + (c / 4) * ‖u‖ ^ 2 := by
      have hc4_pos : 0 < c / 4 := by linarith
      have h_le : (c * δ ^ 2 / 4) * t ≤ (c / 4) * ‖u‖ ^ 2 := by
        rw [show (c * δ ^ 2 / 4) * t = (c / 4) * (δ ^ 2 * t) from by ring]
        exact mul_le_mul_of_nonneg_left h_norm_sq_lb'.le hc4_pos.le
      linarith
    linarith
  -- exp(-(c/2)‖u‖²) ≤ exp(-(c/4)‖u‖²) · exp(-(cδ²/4) t).
  have h_exp_split :
      Real.exp (-((c / 2) * ‖u‖ ^ 2))
        ≤ Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
            Real.exp (-((c * δ ^ 2 / 4) * t)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  -- Combine.
  calc |gaussianWeight H u *
          (Real.exp (-(rescaledPerturbation V H t u)) - 1)|
      ≤ 2 * Real.exp (-((c / 2) * ‖u‖ ^ 2)) := h_le_2_exp
    _ ≤ 2 * (Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
          Real.exp (-((c * δ ^ 2 / 4) * t))) :=
        mul_le_mul_of_nonneg_left h_exp_split (by norm_num : (0:ℝ) ≤ 2)
    _ = 2 * Real.exp (-((c / 4) * ‖u‖ ^ 2)) *
          Real.exp (-((c * δ ^ 2 / 4) * t)) := by ring

end TailPartitionBound

section NormPowExpIntegrability

open MeasureTheory

/-- **Integrability of `‖u‖^k · exp(-α ‖u‖²)`** for any `α > 0`, `k : ℕ`,
under `Nonempty ι`. Dominated by `M_k · exp(-(α/(2|ι|)) · ∑ u_i²)`
from Phase 2's `integrable_exp_neg_const_mul_sum_sq`. -/
lemma integrable_norm_pow_mul_exp_neg_const_sq
    [Nonempty ι] {α : ℝ} (hα_pos : 0 < α) (k : ℕ) :
    Integrable (fun u : ι → ℝ =>
      ‖u‖ ^ k * Real.exp (-(α * ‖u‖ ^ 2))) := by
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hα_card_pos : 0 < α / (2 * Fintype.card ι) := by positivity
  set M_k : ℝ := Real.exp ((k:ℝ) ^ 2 / (2 * α)) with hM_def
  have hM_nn : 0 ≤ M_k := (Real.exp_pos _).le
  have h_dom_int :=
    (integrable_exp_neg_const_mul_sum_sq (ι := ι) hα_card_pos).const_mul M_k
  refine h_dom_int.mono' ?_ ?_
  · -- AE strongly measurable: continuous.
    exact ((continuous_norm.pow k).mul
      (Real.continuous_exp.comp (continuous_const.mul
        (continuous_norm.pow 2)).neg)).aestronglyMeasurable
  · filter_upwards with u
    have h_norm_pow_nn : 0 ≤ ‖u‖ ^ k := pow_nonneg (norm_nonneg _) k
    have h_lhs_nn : 0 ≤ ‖u‖ ^ k * Real.exp (-(α * ‖u‖ ^ 2)) :=
      mul_nonneg h_norm_pow_nn (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg h_lhs_nn]
    -- ‖u‖^k · exp(-α‖u‖²) ≤ M_k · exp(-(α/2)‖u‖²) (poly-Gaussian decay).
    have h_decay := pow_mul_exp_neg_sq_le_half_decay k hα_pos (norm_nonneg u)
    -- exp(-(α/2)‖u‖²) ≤ exp(-(α/(2|ι|)) · ∑ u_i²) (sum-norm bridge).
    have h_sum_to_norm := sq_norm_ge_sum_sq_div_card u
    have h_exp_le : Real.exp (-((α / 2) * ‖u‖ ^ 2))
        ≤ Real.exp (-((α / (2 * Fintype.card ι)) * ∑ i, (u i) ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have h_lb : (1 / (Fintype.card ι : ℝ)) * (∑ i, (u i) ^ 2) ≤ ‖u‖ ^ 2 :=
        h_sum_to_norm
      have h_mul := mul_le_mul_of_nonneg_left h_lb (by linarith : (0:ℝ) ≤ α/2)
      rw [show (α / 2 : ℝ) * ((1 / (Fintype.card ι : ℝ)) * (∑ i, (u i) ^ 2))
            = (α / (2 * Fintype.card ι)) * ∑ i, (u i) ^ 2 from by
          field_simp] at h_mul
      linarith
    calc ‖u‖ ^ k * Real.exp (-(α * ‖u‖ ^ 2))
        ≤ M_k * Real.exp (-((α / 2) * ‖u‖ ^ 2)) := h_decay
      _ ≤ M_k *
            Real.exp (-((α / (2 * Fintype.card ι)) * ∑ i, (u i) ^ 2)) :=
          mul_le_mul_of_nonneg_left h_exp_le hM_nn

/-- Integrability of `exp(-α ‖u‖²)` (k = 0 case). -/
lemma integrable_exp_neg_const_norm_sq
    [Nonempty ι] {α : ℝ} (hα_pos : 0 < α) :
    Integrable (fun u : ι → ℝ => Real.exp (-(α * ‖u‖ ^ 2))) := by
  have h := integrable_norm_pow_mul_exp_neg_const_sq (ι := ι) hα_pos 0
  apply h.congr
  filter_upwards with u
  show ‖u‖ ^ 0 * Real.exp (-(α * ‖u‖ ^ 2)) = Real.exp (-(α * ‖u‖ ^ 2))
  ring

end NormPowExpIntegrability

section TailExpDecayHelper

/-- **Exp tail beats `1/√t`**: for `β > 0` and `t ≥ 1/β²`,
`exp(-β · t) ≤ 1 / Real.sqrt t`.

Uses `exp(βt) ≥ βt` (from `Real.add_one_le_exp`) and that `√t ≤ βt` for
`t ≥ 1/β²`. -/
lemma exp_neg_const_mul_le_inv_sqrt
    {β : ℝ} (hβ_pos : 0 < β) {t : ℝ} (ht : 1 / β ^ 2 ≤ t) :
    Real.exp (-(β * t)) ≤ 1 / Real.sqrt t := by
  have hβ_sq_pos : (0 : ℝ) < β ^ 2 := by positivity
  have ht_pos : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  -- Step 1: β · √t ≥ 1.
  have hβsqrt_ge_one : 1 ≤ β * Real.sqrt t := by
    have h_sq_bound : 1 ≤ (β * Real.sqrt t) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ht_pos.le]
      have h := mul_le_mul_of_nonneg_left ht (le_of_lt hβ_sq_pos)
      rw [show (β ^ 2 : ℝ) * (1 / β ^ 2) = 1 from by field_simp] at h
      linarith
    have h_prod_pos : 0 < β * Real.sqrt t := mul_pos hβ_pos hsqrt_pos
    nlinarith [sq_nonneg (β * Real.sqrt t - 1)]
  -- Step 2: √t ≤ β · t.
  have h_sqrt_le_betat : Real.sqrt t ≤ β * t := by
    have h := mul_le_mul_of_nonneg_left hβsqrt_ge_one hsqrt_pos.le
    rw [mul_one] at h
    have h_eq : Real.sqrt t * (β * Real.sqrt t)
        = β * (Real.sqrt t * Real.sqrt t) := by ring
    rw [h_eq, Real.mul_self_sqrt ht_pos.le] at h
    exact h
  -- Step 3: exp(-βt) = 1/exp(βt). And exp(βt) ≥ βt ≥ √t > 0.
  have hβt_nn : 0 ≤ β * t := mul_nonneg hβ_pos.le ht_pos.le
  have h_exp_lb : β * t ≤ Real.exp (β * t) := by
    have h := Real.add_one_le_exp (β * t)
    linarith
  have h_exp_ge_sqrt : Real.sqrt t ≤ Real.exp (β * t) :=
    le_trans h_sqrt_le_betat h_exp_lb
  -- Step 4: exp(-βt) ≤ 1/√t.
  rw [Real.exp_neg]
  rw [show (1 : ℝ) / Real.sqrt t = (Real.sqrt t)⁻¹ from one_div _]
  exact inv_anti₀ hsqrt_pos h_exp_ge_sqrt

/-- **Exp tail beats `1/t`**: for `β > 0` and `t ≥ 4/β²`,
`exp(-β · t) ≤ 1/t`. Squared form of `exp_neg_const_mul_le_inv_sqrt`. -/
lemma exp_neg_const_mul_le_inv
    {β : ℝ} (hβ_pos : 0 < β) {t : ℝ} (ht : 4 / β ^ 2 ≤ t) :
    Real.exp (-(β * t)) ≤ 1 / t := by
  have hβ2_pos : 0 < β / 2 := by linarith
  have ht' : 1 / (β / 2) ^ 2 ≤ t := by
    rw [show (β / 2 : ℝ) ^ 2 = β ^ 2 / 4 from by ring]
    rw [show (1 : ℝ) / (β ^ 2 / 4) = 4 / β ^ 2 from by
      rw [show (1 : ℝ) / (β ^ 2 / 4) = 1 * (4 / β ^ 2) from by
          rw [div_div_eq_mul_div]; ring]; ring]
    exact ht
  have hhalf := exp_neg_const_mul_le_inv_sqrt hβ2_pos ht'
  have ht_pos : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have h_inv_sqrt_pos : (0 : ℝ) < 1 / Real.sqrt t := by positivity
  have h_exp_eq : Real.exp (-(β * t)) = (Real.exp (-((β / 2) * t))) ^ 2 := by
    have h_pow : (Real.exp (-((β / 2) * t)))^2
        = Real.exp (-((β / 2) * t)) * Real.exp (-((β / 2) * t)) := sq _
    rw [h_pow, ← Real.exp_add]
    congr 1
    ring
  rw [h_exp_eq]
  have h_sq_le : (Real.exp (-((β / 2) * t)))^2 ≤ (1 / Real.sqrt t)^2 := by
    have h_pos : 0 ≤ Real.exp (-((β / 2) * t)) := (Real.exp_pos _).le
    exact sq_le_sq' (by linarith [h_inv_sqrt_pos.le]) hhalf
  have h_sq_eq : (1 / Real.sqrt t : ℝ) ^ 2 = 1 / t := by
    rw [div_pow, one_pow, Real.sq_sqrt ht_pos.le]
  rw [← h_sq_eq]
  exact h_sq_le

end TailExpDecayHelper

end Laplace.Multi
