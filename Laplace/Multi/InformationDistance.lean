/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.TargetPythagoras
import Laplace.Multi.VisibleBudget

/-!
# The information distance from the featureless posterior to the data

For a data law `D` of finite information,

  `KL(D ‖ ν) = ∫₀¹ (1 − s) κ(s) ds + L + R`          (`toReal_klDiv_eq_integral_atlasCurv_add`)

where `κ` is the curvature of the atlas path from `m₀` to `M_D`, `L = KL(D ‖ D↑)` the fibre
information and `R = KL(S_*D ‖ S_*Π(M_D))` the marginal residual; and along the bridge
`D_s = (1−s)ν + sD`, whose response is the atlas point `M_s`,

  `KL(D_s ‖ ν) = ∫₀ˢ (s − u) κ(u) du + L_s + R_s`  
        (`toReal_klDiv_bridge_eq_integral_atlasCurv_add`).

The distance travelled from the featureless posterior to the data is the integrated curvature of
the straight response path, plus what the atlas cannot see: this is the whole map of responses in
one line, valid for every finite-information data law, boundary responses included.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **The information distance decomposes along the atlas path**:
`KL(D‖ν) = ∫₀¹ (1−s) κ(s) ds + L + R`. -/
theorem toReal_klDiv_eq_integral_atlasCurv_add (D : Measure X) [IsProbabilityMeasure D]
    (hDkl : klDiv D ν ≠ ⊤) :
    (klDiv D ν).toReal =
      (∫ s in Ioo (0 : ℝ) 1, (1 - s) * atlasCurv hS ν
        (fun h ↦ hDkl (klDiv_eq_top_of_genRate_eq_top hS ν D h)) s) +
      (klDiv D (statisticLift ν D (statPoint S))).toReal +
      (klDiv (D.map (statPoint S))
        ((responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D)).map (statPoint S))).toReal := by
  have hfin : genRate ν S (fun i ↦ ∫ x, S i x ∂D) ≠ ⊤ := fun h ↦
    hDkl (klDiv_eq_top_of_genRate_eq_top hS ν D h)
  obtain ⟨-, -, -, hpyth⟩ := responseProjection_spec hS ν hfin
  have h1 := hpyth D inferInstance rfl
  have hsplit := klDiv_responseProjection_eq_statisticLift_add_map' hS ν D hDkl
  have hne1 : klDiv D (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D)) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at h1
    exact hDkl h1
  have hne2 : klDiv D (statisticLift ν D (statPoint S)) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at hsplit
    exact hne1 hsplit
  have hne3 : klDiv (D.map (statPoint S))
      ((responseProjection hS ν (fun i ↦ ∫ x, S i x ∂D)).map (statPoint S)) ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hsplit
    exact hne1 hsplit
  rw [h1, hsplit, ENNReal.toReal_add (by rw [← hsplit]; exact hne1) hfin,
    ENNReal.toReal_add hne2 hne3, genRate_toReal_eq_integral_atlasCurv hS ν hfin]
  ring

omit [Nonempty X] [Nonempty J] in
/-- The response of the bridge `aν + bD` (`a + b = 1`) is the atlas point at time `b`. -/
theorem atlasPath_eq_mixture_mean (D : Measure X) [IsProbabilityMeasure D] {a b : ℝ≥0}
    (hab : a + b = 1) :
    atlasPath S ν (fun i ↦ ∫ x, S i x ∂D) b = fun i ↦ ∫ x, S i x ∂(a • ν + b • D) := by
  rw [mean_mixture hS ν D a b, ← meanMap_zero_eq_mean ν]
  unfold atlasPath
  have : (a : ℝ) = 1 - b := by
    have := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) hab
    simp only [NNReal.coe_add, NNReal.coe_one] at this
    linarith
  rw [this]

/-- **The information distance along the bridge**:
`KL(D_s ‖ ν) = ∫₀ˢ (s − u) κ(u) du + L_s + R_s` for `D_s = (1−s)ν + sD`, `s < 1`. -/
theorem toReal_klDiv_bridge_eq_integral_atlasCurv_add (D : Measure X) [IsProbabilityMeasure D]
    (hDkl : klDiv D ν ≠ ⊤) {a b : ℝ≥0} (hab : a + b = 1) (hb : b < 1) :
    (klDiv (a • ν + b • D) ν).toReal =
      (∫ u in (0 : ℝ)..b, ((b : ℝ) - u) * atlasCurv hS ν
        (fun h ↦ hDkl (klDiv_eq_top_of_genRate_eq_top hS ν D h)) u) +
      (klDiv (a • ν + b • D) (statisticLift ν (a • ν + b • D) (statPoint S))).toReal +
      (klDiv ((a • ν + b • D).map (statPoint S))
        ((responseProjection hS ν (fun i ↦ ∫ x, S i x ∂(a • ν + b • D))).map (statPoint
        S))).toReal := by
  have hDν : D ≪ ν := (klDiv_ne_top_iff.1 hDkl).1
  have hfinD : genRate ν S (fun i ↦ ∫ x, S i x ∂D) ≠ ⊤ := fun h ↦
    hDkl (klDiv_eq_top_of_genRate_eq_top hS ν D h)
  have := isProbabilityMeasure_mixture ν D hab
  have hkl : klDiv (a • ν + b • D) ν ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (klDiv_mixture_le ν ν D Measure.AbsolutelyContinuous.rfl hDν hab)
    rw [klDiv_self, mul_zero, zero_add]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hDkl
  have hfin : genRate ν S (fun i ↦ ∫ x, S i x ∂(a • ν + b • D)) ≠ ⊤ := fun h ↦
    hkl (klDiv_eq_top_of_genRate_eq_top hS ν _ h)
  obtain ⟨-, -, -, hpyth⟩ := responseProjection_spec hS ν hfin
  have h1 := hpyth (a • ν + b • D) inferInstance rfl
  have hsplit := klDiv_responseProjection_eq_statisticLift_add_map' hS ν (a • ν + b • D) hkl
  have hne1 : klDiv (a • ν + b • D)
      (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂(a • ν + b • D))) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at h1
    exact hkl h1
  have hne2 : klDiv (a • ν + b • D) (statisticLift ν (a • ν + b • D) (statPoint S)) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at hsplit
    exact hne1 hsplit
  have hne3 : klDiv ((a • ν + b • D).map (statPoint S))
      ((responseProjection hS ν (fun i ↦ ∫ x, S i x ∂(a • ν + b • D))).map (statPoint S)) ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hsplit
    exact hne1 hsplit
  have hI : (genRate ν S (fun i ↦ ∫ x, S i x ∂(a • ν + b • D))).toReal =
      ∫ u in (0 : ℝ)..b, ((b : ℝ) - u) * atlasCurv hS ν hfinD u := by
    rw [← atlasPath_eq_mixture_mean hS ν D hab]
    exact genRate_atlasPath_eq_integral hS ν hfinD b.coe_nonneg hb
  rw [h1, hsplit, ENNReal.toReal_add (by rw [← hsplit]; exact hne1) hfin,
    ENNReal.toReal_add hne2 hne3, hI]
  ring

end Laplace.Multi
