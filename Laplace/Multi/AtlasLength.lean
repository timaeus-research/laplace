/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AtlasEnergy

/-!
# Length versus energy on the atlas

The Fisher length of the atlas path `s ↦ Π(M_s)` from the featureless posterior to an interior
representative is `Len = ∫₀¹ √κ(s) ds`, while its Fisher energy is
`∫₀¹ κ = KL(Π(M)‖ν) + KL(ν‖Π(M))` (`integral_atlasCurv_eq_symm_klDiv`). By Cauchy–Schwarz on the
unit interval,

`Len² ≤ KL(Π(M)‖ν) + KL(ν‖Π(M))`,

with equality exactly when the speed `√κ` is constant. The length is an intrinsic Fisher–Rao
quantity; the energy is the symmetrised divergence. Neither is a directional divergence.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Length

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤)
include hS hfin

/-- The Fisher length of the atlas path. -/
noncomputable def atlasLength : ℝ := ∫ s in Ioo (0 : ℝ) 1, Real.sqrt (atlasCurv hS ν hfin s)

/-- **Length is bounded by energy**: `(∫₀¹ √κ)² ≤ ∫₀¹ κ`. -/
theorem atlasLength_sq_le_integral_atlasCurv
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    atlasLength hS ν hfin ^ 2 ≤ ∫ s in Ioo (0 : ℝ) 1, atlasCurv hS ν hfin s := by
  have hint := integrableOn_atlasCurv hS ν hfin hrel
  have hκ0 : ∀ s, 0 ≤ atlasCurv hS ν hfin s := atlasCurv_nonneg hS ν hfin
  have hmeas : AEStronglyMeasurable (fun s ↦ Real.sqrt (atlasCurv hS ν hfin s))
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hint.aestronglyMeasurable
  have hf : MemLp (fun s ↦ Real.sqrt (atlasCurv hS ν hfin s)) (ENNReal.ofReal 2)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq hmeas]
    refine hint.congr (Eventually.of_forall fun s ↦ ?_)
    beta_reduce
    rw [Real.sq_sqrt (hκ0 s)]
  have hg : MemLp (fun _ : ℝ ↦ (1 : ℝ)) (ENNReal.ofReal 2) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    memLp_const 1
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun s ↦ Real.sqrt_nonneg _) (Eventually.of_forall fun _ ↦ zero_le_one)
    hf hg
  simp only [mul_one, Real.rpow_two, one_pow] at hH
  have hone : ∫ _s in Ioo (0 : ℝ) 1, (1 : ℝ) = 1 := by
    rw [integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
      ENNReal.toReal_ofReal zero_le_one, one_smul]
  have hsq : ∀ s, Real.sqrt (atlasCurv hS ν hfin s) ^ 2 = atlasCurv hS ν hfin s := fun s ↦
    Real.sq_sqrt (hκ0 s)
  simp only [hsq, hone, Real.one_rpow, mul_one] at hH
  have hE0 : 0 ≤ ∫ s in Ioo (0 : ℝ) 1, atlasCurv hS ν hfin s := integral_nonneg fun s ↦ hκ0 s
  have hL0 : 0 ≤ atlasLength hS ν hfin := integral_nonneg fun s ↦ Real.sqrt_nonneg _
  calc atlasLength hS ν hfin ^ 2
      ≤ ((∫ s in Ioo (0 : ℝ) 1, atlasCurv hS ν hfin s) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ hL0 hH 2
    _ = ∫ s in Ioo (0 : ℝ) 1, atlasCurv hS ν hfin s := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hE0]
        norm_num

/-- **Length versus energy**: the Fisher length of the atlas path is bounded by the square root of
the symmetrised divergence, `Len² ≤ KL(Π(M)‖ν) + KL(ν‖Π(M))`. -/
theorem atlasLength_sq_le_symm_klDiv
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    atlasLength hS ν hfin ^ 2 ≤
      (klDiv (responseProjection hS ν M) ν).toReal +
        (klDiv ν (responseProjection hS ν M)).toReal := by
  rw [← integral_atlasCurv_eq_symm_klDiv hS ν hfin hrel]
  exact atlasLength_sq_le_integral_atlasCurv hS ν hfin hrel

end Length

end Laplace.Multi
