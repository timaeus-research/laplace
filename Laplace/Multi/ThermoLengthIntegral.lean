/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.PathHessian
import Laplace.Multi.ThermoLength

/-!
# The integrated thermodynamic-length inequality

Along a `C²` path of bounded losses the displacement of every observable is bounded by the
integral of its posterior standard deviation times the Fisher speed:

  `|⟨φ⟩_{s₁} − ⟨φ⟩_{s₀}| ≤ ∫_{s₀}^{s₁} √Var_s(φ) √g_s ds`
  (`PathData2.abs_priorExp_sub_le_integral`).

This is the integrated form of `ThermoLength.abs_deriv_le_sqrt_fisherSpeed`; the `C²` hypothesis
is what makes the Fisher speed continuous in `s` (through `PathData2.hasDerivAt_pathMean`), so
that the right-hand side is an honest interval integral. For a standardised observable
(`Var_s(φ) ≤ 1` along the path) the bound is the thermodynamic length `∫ √g_s ds` of the path.
-/

open MeasureTheory Filter Topology intervalIntegral

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

namespace PathData2

variable {π : X → ℝ} {L L' L'' : ℝ → X → ℝ} {S ML M' M'' : ℝ}

/-- `s ↦ E_s[L̇_s²]` is differentiable along a `C²` path. -/
theorem differentiableAt_priorExp_sq (h : PathData2 μ π L L' L'' S ML M' M'') (t : ℝ) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Set.Ioo (-S) S) :
    DifferentiableAt ℝ (fun s ↦ priorExp μ π (L s) (fun x ↦ L' s x * L' s x) t) s₀ := by
  have hp := h.toPathData
  have hN := hp.hasDerivAt_num' (f := fun s x ↦ L' s x * L' s x)
    (f' := fun s x ↦ L'' s x * L' s x + L' s x * L'' s x)
    (fun s ↦ (hp.L'_meas s).mul (hp.L'_meas s))
    (fun s ↦ ((h.L''_meas s).mul (hp.L'_meas s)).add ((hp.L'_meas s).mul (h.L''_meas s)))
    (Mf := M' * M') (fun s hs x ↦ by
      rw [abs_mul]
      exact mul_le_mul (hp.L'_bound s hs x) (hp.L'_bound s hs x) (abs_nonneg _)
        (le_trans (abs_nonneg _) (hp.L'_bound s hs x)))
    (Mf' := M'' * M' + M' * M'') (fun s hs x ↦ by
      have h1 := h.L''_bound s hs x
      have h2 := hp.L'_bound s hs x
      have hM' : 0 ≤ M' := le_trans (abs_nonneg _) h2
      have hM'' : 0 ≤ M'' := le_trans (abs_nonneg _) h1
      calc |L'' s x * L' s x + L' s x * L'' s x|
          ≤ |L'' s x * L' s x| + |L' s x * L'' s x| := abs_add_le _ _
        _ ≤ M'' * M' + M' * M'' := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul h1 h2 (abs_nonneg _) hM'')
            (mul_le_mul h2 h1 (abs_nonneg _) hM'))
    (fun x s hs ↦ (h.hasDeriv' x s hs).mul (h.hasDeriv' x s hs)) t hs₀
  have hZ := hp.hasDerivAt_num (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1)
    (fun _ ↦ by simp) t hs₀
  simp only [one_mul] at hZ
  have hZpos := hp.priorZ_pos t hs₀
  unfold priorZ at hZpos
  exact (hN.div hZ hZpos.ne').differentiableAt

/-- The Fisher speed is continuous along a `C²` path. -/
theorem continuousAt_fisherSpeed (h : PathData2 μ π L L' L'' S ML M' M'') (t : ℝ) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Set.Ioo (-S) S) : ContinuousAt (fun s ↦ fisherSpeed μ π L L' t s) s₀ := by
  have h1 := h.differentiableAt_priorExp_sq t hs₀
  have h2 := (h.hasDerivAt_pathMean t hs₀).differentiableAt
  unfold fisherSpeed priorCov
  exact (continuousAt_const.mul (h1.continuousAt.sub (h2.continuousAt.mul h2.continuousAt)))

/-- The posterior variance of a bounded observable is continuous along a `C¹` path. -/
theorem continuousAt_priorCov_self [Nonempty X] (h : PathData μ π L L' S ML M') {φ : X → ℝ}
    (hφm : Measurable φ)
    {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ) (t : ℝ) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (-S) S) :
    ContinuousAt (fun s ↦ priorCov μ π (L s) φ φ t) s₀ := by
  have hMφ : 0 ≤ Mφ := le_trans (abs_nonneg _) (hφ (Classical.arbitrary X))
  have h1 := h.hasDerivAt_priorExp (f := fun x ↦ φ x * φ x) (hφm.mul hφm) (Mf := Mφ * Mφ)
    (fun x ↦ by rw [abs_mul]; exact mul_le_mul (hφ x) (hφ x) (abs_nonneg _) hMφ) t hs₀
  have h2 := h.hasDerivAt_priorExp hφm hφ t hs₀
  unfold priorCov
  exact h1.continuousAt.sub (h2.continuousAt.mul h2.continuousAt)

/-- **The integrated thermodynamic-length inequality**:
`|⟨φ⟩_{s₁} − ⟨φ⟩_{s₀}| ≤ ∫_{s₀}^{s₁} √Var_s(φ) √g_s ds` along a `C²` path. -/
theorem abs_priorExp_sub_le_integral [Nonempty X] (h : PathData2 μ π L L' L'' S ML M' M'')
    {φ : X → ℝ}
    (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ) (t : ℝ) {s₀ s₁ : ℝ}
    (hs₀ : s₀ ∈ Set.Ioo (-S) S) (hs₁ : s₁ ∈ Set.Ioo (-S) S) (hle : s₀ ≤ s₁) :
    |priorExp μ π (L s₁) φ t - priorExp μ π (L s₀) φ t| ≤
      ∫ s in s₀..s₁, Real.sqrt (priorCov μ π (L s) φ φ t) *
        Real.sqrt (fisherSpeed μ π L L' t s) := by
  have hp := h.toPathData
  have hmem : ∀ s ∈ Set.Icc s₀ s₁, s ∈ Set.Ioo (-S) S := fun s hs ↦
    ⟨lt_of_lt_of_le hs₀.1 hs.1, lt_of_le_of_lt hs.2 hs₁.2⟩
  have hmem' : ∀ s ∈ Set.uIcc s₀ s₁, s ∈ Set.Ioo (-S) S := fun s hs ↦
    hmem s (by rwa [Set.uIcc_of_le hle] at hs)
  have hderiv : ∀ s ∈ Set.uIcc s₀ s₁, HasDerivAt (fun s ↦ priorExp μ π (L s) φ t)
      (-t * priorCov μ π (L s) φ (L' s) t) s := fun s hs ↦
    hp.hasDerivAt_priorExp hφm hφ t (hmem' s hs)
  have hcont : ContinuousOn (fun s ↦ -t * priorCov μ π (L s) φ (L' s) t) (Set.uIcc s₀ s₁) :=
    fun s hs ↦
      (h.hasDerivAt_neg_mul_pathCov hφm hφ t (hmem' s hs)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun s ↦ -t * priorCov μ π (L s) φ (L' s) t) volume s₀ s₁ :=
    hcont.intervalIntegrable
  have hcontR : ContinuousOn (fun s ↦ Real.sqrt (priorCov μ π (L s) φ φ t) *
      Real.sqrt (fisherSpeed μ π L L' t s)) (Set.uIcc s₀ s₁) := fun s hs ↦
    ((Real.continuous_sqrt.continuousAt.comp
      (continuousAt_priorCov_self hp hφm hφ t (hmem' s hs))).mul
      (Real.continuous_sqrt.continuousAt.comp
        (h.continuousAt_fisherSpeed t (hmem' s hs)))).continuousWithinAt
  have hintR : IntervalIntegrable (fun s ↦ Real.sqrt (priorCov μ π (L s) φ φ t) *
      Real.sqrt (fisherSpeed μ π L L' t s)) volume s₀ s₁ := hcontR.intervalIntegrable
  rw [← integral_eq_sub_of_hasDerivAt hderiv hint]
  calc |∫ s in s₀..s₁, -t * priorCov μ π (L s) φ (L' s) t|
      ≤ ∫ s in s₀..s₁, |-t * priorCov μ π (L s) φ (L' s) t| := by
        have := norm_integral_le_integral_norm (μ := volume)
          (f := fun s ↦ -t * priorCov μ π (L s) φ (L' s) t) hle
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∫ s in s₀..s₁, Real.sqrt (priorCov μ π (L s) φ φ t) *
          Real.sqrt (fisherSpeed μ π L L' t s) := by
        refine integral_mono_on hle hint.abs hintR fun s hs ↦ ?_
        exact hp.abs_deriv_le_sqrt_fisherSpeed ⟨hφm, Mφ, hφ⟩ t (hmem s hs)

end PathData2

end Laplace.Multi
