/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ThermoLengthAsymptotic
import Laplace.Multi.ResponseNullspace

/-!
# Integrated susceptibility and strict identifiability along a mixture line

Along a mixture line `L_s = L₀ + sΔ` the master identity `d/ds ⟨Δ⟩_s = −t Var_s(Δ)` integrates to
the **integrated-susceptibility identity**

  `∫₀¹ t Var_{t,s}(Δ) ds = ⟨Δ⟩_{t,0} − ⟨Δ⟩_{t,1}`   (`TiltData.integrated_susceptibility`):

the total Fisher "mass" of the segment is the drop of the mean loss contrast between its
endpoints, which for a bounded contrast is at most `2M`, uniformly in `t`. By Cauchy–Schwarz the
thermodynamic length of the segment therefore satisfies

  `ℓ(t)² ≤ t (⟨Δ⟩_{t,0} − ⟨Δ⟩_{t,1}) ≤ 2Mt`   (`thermoLength_sq_le`, `thermoLength_le_sqrt_osc`):

two data distributions with bounded loss contrast are never further apart than `√(2Mt)` in the
response geometry — the `√t` scale of "different truths", to be compared with the `√λ log t` of
the featureless point (`ThermoLengthAsymptotic`).

The nullspace theorem (`tiltCov_self_eq_zero_iff`) upgrades the monotonicity of the mean map to
**strict identifiability**: if the contrast is not almost surely constant on the support of the
prior, then `Var_s(Δ) > 0` for every `s` (`mixCov_self_pos`), the mean map `s ↦ ⟨Δ⟩_{t,s}` is
strictly decreasing (`mixExp_strictAnti`) and injective (`mixExp_injective`): the position on the
line is read off from the response.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- `(∫₀¹ g)² ≤ ∫₀¹ g²` for continuous `g` (Cauchy–Schwarz on `[0,1]`, via `Var ≥ 0`). -/
theorem sq_intervalIntegral_le_intervalIntegral_sq {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ s in (0 : ℝ)..1, g s) ^ 2 ≤ ∫ s in (0 : ℝ)..1, g s ^ 2 := by
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  set m := ∫ s in Ioc (0 : ℝ) 1, g s with hm
  have hgi : Integrable g (volume.restrict (Ioc (0 : ℝ) 1)) := hg.integrableOn_Ioc
  have hg2 : Integrable (fun s ↦ g s ^ 2) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (hg.pow 2).integrableOn_Ioc
  have h1 : Integrable (fun s ↦ g s ^ 2 - 2 * m * g s) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hg2.sub (hgi.const_mul _)
  have h2 : Integrable (fun _ : ℝ ↦ m ^ 2) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have h0 : 0 ≤ ∫ s in Ioc (0 : ℝ) 1, (g s - m) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioc fun s _ ↦ sq_nonneg _
  have e : ∫ s in Ioc (0 : ℝ) 1, (g s - m) ^ 2 = (∫ s in Ioc (0 : ℝ) 1, g s ^ 2) - m ^ 2 := by
    calc ∫ s in Ioc (0 : ℝ) 1, (g s - m) ^ 2
        = ∫ s in Ioc (0 : ℝ) 1, ((g s ^ 2 - 2 * m * g s) + m ^ 2) :=
          setIntegral_congr_fun measurableSet_Ioc fun s _ ↦ by ring
      _ = (∫ s in Ioc (0 : ℝ) 1, (g s ^ 2 - 2 * m * g s)) + ∫ _ in Ioc (0 : ℝ) 1, m ^ 2 :=
          integral_add h1 h2
      _ = ((∫ s in Ioc (0 : ℝ) 1, g s ^ 2) - 2 * m * m) + m ^ 2 := by
          rw [integral_sub hg2 (hgi.const_mul _), MeasureTheory.integral_const_mul]
          simp only [integral_const, measureReal_def, Measure.restrict_apply MeasurableSet.univ,
            univ_inter, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal zero_le_one, one_smul]
          rw [← hm]
      _ = (∫ s in Ioc (0 : ℝ) 1, g s ^ 2) - m ^ 2 := by ring
  linarith

variable [Nonempty X] {π L₀ Δ : X → ℝ} {t M : ℝ}

/-- **Integrated susceptibility**: `∫₀¹ t Var_{t,s}(Δ) ds = ⟨Δ⟩_{t,0} − ⟨Δ⟩_{t,1}`. -/
theorem TiltData.integrated_susceptibility (h : TiltData μ (baseWeight π L₀ t) Δ M) :
    ∫ s in (0 : ℝ)..1, t * mixCov μ π L₀ Δ Δ Δ t s =
      mixExp μ π L₀ Δ Δ t 0 - mixExp μ π L₀ Δ Δ t 1 := by
  have hΔ : Bdd Δ := ⟨h.R_meas, M, h.R_bound⟩
  have hcont : Continuous fun s ↦ -t * mixCov μ π L₀ Δ Δ Δ t s :=
    continuous_iff_continuousAt.mpr fun s ↦ (h.hasDerivAt_neg_mul_mixCov hΔ s).continuousAt
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s ↦ mixExp μ π L₀ Δ Δ t s) (f' := fun s ↦ -t * mixCov μ π L₀ Δ Δ Δ t s)
    (a := 0) (b := 1) (fun s _ ↦ h.hasDerivAt_mixExp hΔ s) (hcont.intervalIntegrable 0 1)
  have e : ∀ s, t * mixCov μ π L₀ Δ Δ Δ t s = -(-t * mixCov μ π L₀ Δ Δ Δ t s) := fun s ↦ by ring
  simp_rw [e]
  rw [intervalIntegral.integral_neg, key]
  ring

omit [Nonempty X] in
/-- The Fisher speed of a mixture line is `t² Var_s(Δ)`. -/
theorem fisherSpeed_mixture (π L₀ Δ : X → ℝ) (t s : ℝ) :
    fisherSpeed μ π (pathLoss L₀ Δ) (fun _ ↦ Δ) t s = t ^ 2 * mixCov μ π L₀ Δ Δ Δ t s := rfl

/-- The mixture-line covariance is continuous in the mixture weight (`t ≠ 0`). -/
theorem TiltData.continuous_mixCov (h : TiltData μ (baseWeight π L₀ t) Δ M) (ht : t ≠ 0)
    {φ : X → ℝ} (hφ : Bdd φ) : Continuous fun s ↦ mixCov μ π L₀ Δ φ Δ t s := by
  have hcont : Continuous fun s ↦ -t * mixCov μ π L₀ Δ φ Δ t s :=
    continuous_iff_continuousAt.mpr fun s ↦ (h.hasDerivAt_neg_mul_mixCov hφ s).continuousAt
  have e : (fun s ↦ mixCov μ π L₀ Δ φ Δ t s) =
      fun s ↦ (-t)⁻¹ * (-t * mixCov μ π L₀ Δ φ Δ t s) := by
    funext s
    rw [← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr ht), one_mul]
  rw [e]
  exact continuous_const.mul hcont

/-- **The length of a mixture segment is controlled by the drop of the mean contrast**:
`ℓ(t)² ≤ t (⟨Δ⟩_{t,0} − ⟨Δ⟩_{t,1})`. -/
theorem TiltData.thermoLength_sq_le (h : TiltData μ (baseWeight π L₀ t) Δ M) (ht : 0 < t) :
    thermoLength μ π (pathLoss L₀ Δ) (fun _ ↦ Δ) t ^ 2 ≤
      t * (mixExp μ π L₀ Δ Δ t 0 - mixExp μ π L₀ Δ Δ t 1) := by
  have hΔ : Bdd Δ := ⟨h.R_meas, M, h.R_bound⟩
  rw [← h.integrated_susceptibility, ← intervalIntegral.integral_const_mul]
  have hnn : ∀ s, 0 ≤ t ^ 2 * mixCov μ π L₀ Δ Δ Δ t s := fun s ↦
    mul_nonneg (sq_nonneg _) (h.mixCov_self_nonneg hΔ s)
  have hc : Continuous fun s ↦ Real.sqrt (t ^ 2 * mixCov μ π L₀ Δ Δ Δ t s) :=
    Real.continuous_sqrt.comp (continuous_const.mul (h.continuous_mixCov ht.ne' hΔ))
  have := sq_intervalIntegral_le_intervalIntegral_sq hc
  have e : ∀ s, Real.sqrt (t ^ 2 * mixCov μ π L₀ Δ Δ Δ t s) ^ 2 =
      t * (t * mixCov μ π L₀ Δ Δ Δ t s) := fun s ↦ by
    rw [Real.sq_sqrt (hnn s)]
    ring
  simp_rw [e] at this
  unfold thermoLength
  simp only [fisherSpeed_mixture]
  exact this

/-- **The `√t` scale**: two data distributions with loss contrast bounded by `M` are at
thermodynamic distance at most `√(2Mt)`. -/
theorem TiltData.thermoLength_le_sqrt_osc (h : TiltData μ (baseWeight π L₀ t) Δ M)
    (ht : 0 < t) :
    thermoLength μ π (pathLoss L₀ Δ) (fun _ ↦ Δ) t ≤ Real.sqrt (2 * M * t) := by
  have hb : ∀ s, |mixExp μ π L₀ Δ Δ t s| ≤ M := fun s ↦ by
    rw [mixExp_eq_tiltExp]
    exact h.abs_tiltExp_le_of_bound h.R_meas h.R_bound t s
  have h0 := hb 0
  have h1 := hb 1
  rw [abs_le] at h0 h1
  refine Real.le_sqrt_of_sq_le ?_
  calc thermoLength μ π (pathLoss L₀ Δ) (fun _ ↦ Δ) t ^ 2
      ≤ t * (mixExp μ π L₀ Δ Δ t 0 - mixExp μ π L₀ Δ Δ t 1) := h.thermoLength_sq_le ht
    _ ≤ t * (2 * M) := mul_le_mul_of_nonneg_left (by linarith) ht.le
    _ = 2 * M * t := by ring

/-- **Non-degenerate contrasts have positive variance at every point of the line**: if `Δ` is not
almost surely constant on the support of the prior then `Var_{t,s}(Δ) > 0`. -/
theorem TiltData.mixCov_self_pos (h : TiltData μ (baseWeight π L₀ t) Δ M)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → Δ x = c) (s : ℝ) :
    0 < mixCov μ π L₀ Δ Δ Δ t s := by
  have hΔ : Bdd Δ := ⟨h.R_meas, M, h.R_bound⟩
  refine lt_of_le_of_ne (h.mixCov_self_nonneg hΔ s) fun h0 ↦ hnd ?_
  rw [mixCov_eq_tiltCov] at h0
  have h0' := (h.tiltCov_self_eq_zero_iff hΔ t s).mp h0.symm
  refine ⟨tiltExp μ (baseWeight π L₀ t) Δ Δ t s, ?_⟩
  filter_upwards [h0'] with x hx hπ
  exact hx (mul_ne_zero (Real.exp_pos _).ne' hπ)

/-- **Strict identifiability along a mixture line**: for `t > 0` and a non-degenerate contrast the
mean map `s ↦ ⟨Δ⟩_{t,s}` is strictly decreasing. -/
theorem TiltData.mixExp_strictAnti (h : TiltData μ (baseWeight π L₀ t) Δ M) (ht : 0 < t)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → Δ x = c) :
    StrictAnti fun s ↦ mixExp μ π L₀ Δ Δ t s := by
  have hΔ : Bdd Δ := ⟨h.R_meas, M, h.R_bound⟩
  refine strictAnti_of_deriv_neg fun s ↦ ?_
  rw [(h.hasDerivAt_mixExp hΔ s).deriv]
  have := h.mixCov_self_pos hnd s
  nlinarith

/-- The position on a mixture line is determined by the response `⟨Δ⟩_{t,s}`. -/
theorem TiltData.mixExp_injective (h : TiltData μ (baseWeight π L₀ t) Δ M) (ht : 0 < t)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → Δ x = c) :
    Function.Injective fun s ↦ mixExp μ π L₀ Δ Δ t s :=
  (h.mixExp_strictAnti ht hnd).injective

end Laplace.Multi
