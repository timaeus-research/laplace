/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseStructure
import Laplace.Multi.EndpointTail

/-!
# Information along the atlas

The companion of the accounting identity for information. Fix a data law `D` with interior
response `M = m₀ + Δ` and finite information, and let `Q_s = Π(M_s)` be the atlas. Then

`KL(D‖Q_s) = KL(D‖Π(M)) + ∫_s^1 (1−t) κ(t) dt` (`klDiv_data_atlas_eq_integral`),

so the information lost by the reconstruction at stage `s` is the information unresolved by the
features plus the accumulated weighted Fisher speed of the remaining path; in particular
`KL(D‖ν) = KL(D‖Π(M)) + ∫₀¹ (1−t) κ(t) dt` (`klDiv_data_eq_add_integral`), the profile is antitone
in `s` (`klDiv_data_atlas_antitone`) and differentiable on `(0,1)` with derivative `−(1−s) κ(s)`
(`hasDerivAt_klDiv_data_atlas`).
-/

open MeasureTheory Filter Topology Set InformationTheory intervalIntegral

namespace Laplace.Multi

section Information

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤) (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hS hfin hrel

/-- The curvature is continuous on `[0,1]`. -/
theorem continuousOn_atlasCurv : ContinuousOn (atlasCurv hS ν hfin) (Icc (0 : ℝ) 1) :=
  fun _ hs ↦ (hasDerivAt_atlasCurv' hS ν hfin hrel hs.1 hs.2).continuousAt.continuousWithinAt

theorem intervalIntegrable_one_sub_mul_atlasCurv {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ (1 - t) * atlasCurv hS ν hfin t) volume a b :=
  (((continuous_sub_left (1 : ℝ)).continuousOn).mul ((continuousOn_atlasCurv hS ν hfin hrel).mono
    (by rw [uIcc_of_le hab]; exact Icc_subset_Icc ha hb))).intervalIntegrable

/-- **Information along the atlas**: for a data law `D` with response `M` and finite information,
`KL(D‖Q_s) = KL(D‖Π(M)) + ∫_s^1 (1−t) κ(t) dt`. -/
theorem klDiv_data_atlas_eq_integral (D : Measure X) [IsProbabilityMeasure D]
    (hDkl : klDiv D ν ≠ ⊤) (hD : (fun j ↦ ∫ x, S j x ∂D) = M) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) :
    (klDiv D (responseProjection hS ν (atlasPath S ν M s))).toReal =
      (klDiv D (responseProjection hS ν M)).toReal +
        ∫ t in s..1, (1 - t) * atlasCurv hS ν hfin t := by
  have hrel' := atlas_mem_intrinsicInterior' hS ν hfin hrel hs0 hs1.le
  obtain ⟨hQP, -, -, hpyth⟩ := responseProjection_spec hS ν hfin
  have hDQ : klDiv D (responseProjection hS ν M) ≠ ⊤ := by
    have h := hpyth D inferInstance hD
    rw [h] at hDkl
    exact (ENNReal.add_ne_top.1 hDkl).1
  have hQQ := klDiv_responseProjection_interior_ne_top hS ν hfin hrel'
  have h1 := klDiv_responseProjection_target_eq hS ν D hDkl hrel
  have h2 := klDiv_responseProjection_target_eq hS ν D hDkl hrel'
  rw [hD] at h1 h2
  rw [klDiv_self, add_zero] at h1
  rw [← h1] at h2
  rw [h2, ENNReal.toReal_add hDQ hQQ,
    toReal_klDiv_responseProjection_atlas_eq_integral hS ν hfin hs0 hs1]

/-- **The information budget**: `KL(D‖ν) = KL(D‖Π(M)) + ∫₀¹ (1−t) κ(t) dt`. -/
theorem klDiv_data_eq_add_integral (D : Measure X) [IsProbabilityMeasure D]
    (hDkl : klDiv D ν ≠ ⊤) (hD : (fun j ↦ ∫ x, S j x ∂D) = M) :
    (klDiv D ν).toReal = (klDiv D (responseProjection hS ν M)).toReal +
      ∫ t in (0 : ℝ)..1, (1 - t) * atlasCurv hS ν hfin t := by
  have h := klDiv_data_atlas_eq_integral hS ν hfin hrel D hDkl hD (le_refl 0) zero_lt_one
  have e : responseProjection hS ν (atlasPath S ν M 0) = ν := by
    rw [responseProjection_eq_familyMeasure_responseTheta hS ν
      (atlas_mem_intrinsicInterior' hS ν hfin hrel (le_refl 0) zero_le_one)]
    exact atlas_zero_eq hS ν
  rw [e] at h
  exact h

/-- The information profile along the atlas is antitone. -/
theorem klDiv_data_atlas_antitone (D : Measure X) [IsProbabilityMeasure D]
    (hDkl : klDiv D ν ≠ ⊤) (hD : (fun j ↦ ∫ x, S j x ∂D) = M) {s s' : ℝ} (hs0 : 0 ≤ s)
    (hss' : s ≤ s') (hs1 : s' < 1) :
    (klDiv D (responseProjection hS ν (atlasPath S ν M s'))).toReal ≤
      (klDiv D (responseProjection hS ν (atlasPath S ν M s))).toReal := by
  rw [klDiv_data_atlas_eq_integral hS ν hfin hrel D hDkl hD hs0 (hss'.trans_lt hs1),
    klDiv_data_atlas_eq_integral hS ν hfin hrel D hDkl hD (hs0.trans hss') hs1]
  have h1 := intervalIntegrable_one_sub_mul_atlasCurv hS ν hfin hrel hs0 hs1.le hss'
  have h2 := intervalIntegrable_one_sub_mul_atlasCurv hS ν hfin hrel (hs0.trans hss')
    (le_refl 1) hs1.le
  rw [← integral_add_adjacent_intervals h1 h2]
  have : 0 ≤ ∫ t in s..s', (1 - t) * atlasCurv hS ν hfin t :=
    integral_nonneg hss' fun t ht ↦
      mul_nonneg (by linarith [ht.2, hs1]) (atlasCurv_nonneg hS ν hfin t)
  linarith

/-- **The information profile decreases at the weighted Fisher speed**: on `(0,1)`,
`d/ds KL(D‖Q_s) = −(1−s) κ(s)`. -/
theorem hasDerivAt_klDiv_data_atlas (D : Measure X) [IsProbabilityMeasure D]
    (hDkl : klDiv D ν ≠ ⊤) (hD : (fun j ↦ ∫ x, S j x ∂D) = M) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) :
    HasDerivAt (fun s ↦ (klDiv D (responseProjection hS ν (atlasPath S ν M s))).toReal)
      (-((1 - s) * atlasCurv hS ν hfin s)) s := by
  have hint := intervalIntegrable_one_sub_mul_atlasCurv hS ν hfin hrel hs0.le (le_refl 1) hs1.le
  have hcontOn : ContinuousOn (fun t ↦ (1 - t) * atlasCurv hS ν hfin t) (Ioo (0 : ℝ) 1) :=
    ((continuous_sub_left (1 : ℝ)).continuousOn).mul
      ((continuousOn_atlasCurv hS ν hfin hrel).mono Ioo_subset_Icc_self)
  have hcont : ContinuousAt (fun t ↦ (1 - t) * atlasCurv hS ν hfin t) s :=
    hcontOn.continuousAt (Ioo_mem_nhds hs0 hs1)
  have hmeas := hcontOn.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo s ⟨hs0, hs1⟩
  have h := (integral_hasDerivAt_left hint hmeas hcont).const_add
    (klDiv D (responseProjection hS ν M)).toReal
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hs0 hs1] with t ht
  exact klDiv_data_atlas_eq_integral hS ν hfin hrel D hDkl hD ht.1.le ht.2

end Information

end Laplace.Multi
