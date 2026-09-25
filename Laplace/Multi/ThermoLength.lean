/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.PathResponse

/-!
# The Fisher speed of a data path bounds every standardised response

Along a `C¹` path of losses `s ↦ L_s` the posterior moves with **Fisher speed**
`g_s = t² Var_s(L̇_s)` (`fisherSpeed`; the response form of `ResponseMap` evaluated on the
velocity of the path), and the thermodynamic length of the path is `∫ √g_s ds`. The master
identity `d/ds ⟨φ⟩_s = −t Cov_s(φ, L̇_s)` and Cauchy–Schwarz give

  `|d/ds ⟨φ⟩_s| ≤ √Var_s(φ) · √g_s`   (`PathData.abs_deriv_le_sqrt_fisherSpeed`),

so the change of any observable along a segment of the path is bounded by its posterior standard
deviation times the Fisher speed, integrated: with `C ≥ √Var_s(φ) √g_s` on `[s₀, s₁]`,

  `|⟨φ⟩_{s₁} − ⟨φ⟩_{s₀}| ≤ C (s₁ − s₀)`   (`PathData.abs_priorExp_sub_le`).

This is the path-level form of the response bound `(t Cov_a(φ, R_v))² ≤ Var_a(φ) g_a(v, v)`: the
Fisher speed is the maximal standardised response along the path, and the thermodynamic length is
the maximal standardised displacement between the featureless reference and the data.
-/

open MeasureTheory Filter Topology

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The Fisher speed `g_s = t² Var_{t,L_s}(L̇_s)` of a path of losses. -/
noncomputable def fisherSpeed (μ : Measure X) (π : X → ℝ) (L L' : ℝ → X → ℝ) (t s : ℝ) : ℝ :=
  t ^ 2 * priorCov μ π (L s) (L' s) (L' s) t

namespace PathData

variable {π : X → ℝ} {L L' : ℝ → X → ℝ} {S ML M' : ℝ}

/-- The base weight of the path at `s` satisfies the `TiltData` hypotheses (with the zero
residual). -/
theorem tiltData_base [Nonempty X] (h : PathData μ π L L' S ML M') (t : ℝ) {s : ℝ}
    (hs : s ∈ Set.Ioo (-S) S) : TiltData μ (baseWeight π (L s) t) (fun _ ↦ 0) 0 where
  ν_meas := (Real.measurable_exp.comp ((h.L_meas s).const_mul t).neg).mul h.π_meas
  ν_int := by
    have := h.integrable_integrand (f := fun _ ↦ (1 : ℝ)) measurable_const (Mf := 1)
      (fun _ ↦ by simp) t hs
    simp only [one_mul] at this
    exact this
  ν_nonneg x := mul_nonneg (Real.exp_pos _).le (h.π_nonneg x)
  ν_pos := h.priorZ_pos t hs
  R_meas := measurable_const
  R_bound _ := by simp

/-- **Cauchy–Schwarz along the path**: `|t Cov_s(φ, L̇_s)| ≤ √Var_s(φ) √g_s`. -/
theorem abs_deriv_le_sqrt_fisherSpeed [Nonempty X] (h : PathData μ π L L' S ML M') {φ : X → ℝ}
    (hφ : Bdd φ) (t : ℝ) {s : ℝ} (hs : s ∈ Set.Ioo (-S) S) :
    |-t * priorCov μ π (L s) φ (L' s) t| ≤
      Real.sqrt (priorCov μ π (L s) φ φ t) * Real.sqrt (fisherSpeed μ π L L' t s) := by
  have hd := h.tiltData_base t hs
  have hL' : Bdd (L' s) := ⟨h.L'_meas s, M', h.L'_bound s hs⟩
  have hcs := hd.abs_tiltCov_le hφ hL' t 0
  have hB := hd.tiltCov_self_nonneg hL' t 0
  unfold fisherSpeed
  simp only [priorCov_eq_tiltCov_zero (R := fun _ ↦ (0 : ℝ))]
  rw [abs_mul, abs_neg, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]
  calc |t| * |tiltCov μ (baseWeight π (L s) t) φ (L' s) (fun _ ↦ 0) t 0|
      ≤ |t| * (Real.sqrt (tiltCov μ (baseWeight π (L s) t) φ φ (fun _ ↦ 0) t 0) *
          Real.sqrt (tiltCov μ (baseWeight π (L s) t) (L' s) (L' s) (fun _ ↦ 0) t 0)) :=
        mul_le_mul_of_nonneg_left hcs (abs_nonneg t)
    _ = _ := by ring

/-- **The Fisher speed bounds the displacement of every observable**: if
`√Var_s(φ) √g_s ≤ C` on `[s₀, s₁]` then `|⟨φ⟩_{s₁} − ⟨φ⟩_{s₀}| ≤ C (s₁ − s₀)`. -/
theorem abs_priorExp_sub_le [Nonempty X] (h : PathData μ π L L' S ML M') {φ : X → ℝ}
    (hφ : Bdd φ) (t : ℝ) {s₀ s₁ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (-S) S) (hs₁ : s₁ ∈ Set.Ioo (-S) S)
    (hle : s₀ ≤ s₁) {C : ℝ}
    (hC : ∀ s ∈ Set.Icc s₀ s₁,
      Real.sqrt (priorCov μ π (L s) φ φ t) * Real.sqrt (fisherSpeed μ π L L' t s) ≤ C) :
    |priorExp μ π (L s₁) φ t - priorExp μ π (L s₀) φ t| ≤ C * (s₁ - s₀) := by
  obtain ⟨hφm, Mφ, hφb⟩ := hφ
  have hmem : ∀ s ∈ Set.Icc s₀ s₁, s ∈ Set.Ioo (-S) S := fun s hs ↦
    ⟨lt_of_lt_of_le hs₀.1 hs.1, lt_of_le_of_lt hs.2 hs₁.2⟩
  have hderiv : ∀ s ∈ Set.Icc s₀ s₁, HasDerivWithinAt (fun s ↦ priorExp μ π (L s) φ t)
      (-t * priorCov μ π (L s) φ (L' s) t) (Set.Icc s₀ s₁) s := fun s hs ↦
    (h.hasDerivAt_priorExp hφm hφb t (hmem s hs)).hasDerivWithinAt
  have hbound : ∀ s ∈ Set.Icc s₀ s₁, ‖-t * priorCov μ π (L s) φ (L' s) t‖ ≤ C := fun s hs ↦ by
    rw [Real.norm_eq_abs]
    exact (h.abs_deriv_le_sqrt_fisherSpeed ⟨hφm, Mφ, hφb⟩ t (hmem s hs)).trans (hC s hs)
  have := norm_image_sub_le_of_norm_deriv_le_segment' hderiv
    (fun s hs ↦ hbound s (Set.Ico_subset_Icc_self hs)) s₁ (Set.right_mem_Icc.mpr hle)
  simpa [Real.norm_eq_abs] using this

end PathData

end Laplace.Multi
