import Laplace.Multi.Basic
import Laplace.Multi.QuadraticApprox
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

variable {ι : Type*} [Fintype ι]

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

end Laplace.Multi
