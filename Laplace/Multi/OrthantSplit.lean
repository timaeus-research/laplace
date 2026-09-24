/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.GaussianMomentsPosDef

/-!
# Splitting a Lebesgue integral on `ι → ℝ` into orthants

Astra's step 1.1 (`research_kernel_asymptotics_v1`): real powers apply only to positive
magnitudes, so the unsolved coordinates of a wall chart are split into the `2^m` open orthants and
each orthant is reflected onto the positive one. `lintegral_eq_sum_orthants`:
`∫ f = ∑_ε ∫_{(0,∞)^ι} f(ε · x) dx` for measurable `f`, since the coordinate hyperplanes are null
and the reflections preserve Lebesgue measure.
-/

open MeasureTheory Set Function
open scoped Matrix ENNReal

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sign `±1` attached to a Boolean. -/
def bsign (b : Bool) : ℝ := if b then 1 else -1

theorem bsign_mul_self (b : Bool) : bsign b * bsign b = 1 := by cases b <;> simp [bsign]

theorem abs_bsign (b : Bool) : |bsign b| = 1 := by cases b <;> simp [bsign]

theorem bsign_ne_zero (b : Bool) : bsign b ≠ 0 := by cases b <;> simp [bsign]

/-- The reflection of `x` into the orthant of sign pattern `ε`. -/
def orth (ε : ι → Bool) (x : ι → ℝ) : ι → ℝ := fun j ↦ bsign (ε j) * x j

omit [Fintype ι] [DecidableEq ι] in
theorem orth_orth (ε : ι → Bool) (x : ι → ℝ) : orth ε (orth ε x) = x := by
  funext j
  simp only [orth, ← mul_assoc, bsign_mul_self, one_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem abs_orth (ε : ι → Bool) (x : ι → ℝ) (j : ι) : |orth ε x j| = |x j| := by
  simp only [orth, abs_mul, abs_bsign, one_mul]

/-- The open orthant of sign pattern `ε`. -/
def orthant (ε : ι → Bool) : Set (ι → ℝ) := Set.pi univ fun j ↦ {y | 0 < bsign (ε j) * y}

/-- The positive orthant. -/
def posOrthant : Set (ι → ℝ) := Set.pi univ fun _ ↦ Ioi 0

omit [Fintype ι] [DecidableEq ι] in
theorem mem_posOrthant {x : ι → ℝ} : x ∈ (posOrthant : Set (ι → ℝ)) ↔ ∀ j, 0 < x j := by
  simp [posOrthant]

omit [Fintype ι] [DecidableEq ι] in
theorem orth_mem_orthant_iff (ε : ι → Bool) (x : ι → ℝ) :
    orth ε x ∈ orthant ε ↔ x ∈ (posOrthant : Set (ι → ℝ)) := by
  simp only [orthant, posOrthant, Set.mem_univ_pi, mem_ofPred_eq, orth, ← mul_assoc,
    bsign_mul_self, one_mul, mem_Ioi]

omit [Fintype ι] [DecidableEq ι] in
theorem preimage_orth_orthant (ε : ι → Bool) :
    orth ε ⁻¹' orthant ε = (posOrthant : Set (ι → ℝ)) := by
  ext x
  exact orth_mem_orthant_iff ε x

omit [Fintype ι] [DecidableEq ι] in
theorem measurableSet_orthant [Finite ι] (ε : ι → Bool) : MeasurableSet (orthant ε) :=
  MeasurableSet.pi countable_univ fun _ _ ↦
    measurableSet_lt measurable_const (measurable_const.mul measurable_id)

omit [Fintype ι] [DecidableEq ι] in
theorem orthant_disjoint : Pairwise (Disjoint on (orthant : (ι → Bool) → Set (ι → ℝ))) := by
  intro ε ε' hne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  refine Set.disjoint_left.2 fun w h1 h2 ↦ ?_
  have h1j := Set.mem_univ_pi.mp h1 j
  have h2j := Set.mem_univ_pi.mp h2 j
  simp only [mem_ofPred_eq] at h1j h2j
  cases hε : ε j <;> cases hε' : ε' j <;> simp_all [bsign] <;> linarith

omit [Fintype ι] [DecidableEq ι] in
theorem iUnion_orthant : ⋃ ε : ι → Bool, orthant ε = {w : ι → ℝ | ∀ j, w j ≠ 0} := by
  ext w
  simp only [Set.mem_iUnion, orthant, Set.mem_univ_pi, mem_ofPred_eq]
  constructor
  · rintro ⟨ε, hε⟩ j
    exact right_ne_zero_of_mul (hε j).ne'
  · intro hw
    refine ⟨fun j ↦ decide (0 < w j), fun j ↦ ?_⟩
    by_cases hj : 0 < w j
    · simp [bsign, hj]
    · have : w j < 0 := lt_of_le_of_ne (not_lt.mp hj) (hw j)
      simp [bsign, hj]
      linarith

omit [DecidableEq ι] in
theorem volume_compl_ne_zero : volume {w : ι → ℝ | ∀ j, w j ≠ 0}ᶜ = 0 := by
  have e : {w : ι → ℝ | ∀ j, w j ≠ 0}ᶜ = ⋃ j, {w | w j = 0} := by
    ext w
    simp [not_forall]
  rw [e]
  refine measure_iUnion_null fun j ↦ ?_
  rw [volume_pi]
  exact Measure.pi_hyperplane _ j 0

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_orth (ε : ι → Bool) : Measurable (orth ε) :=
  measurable_pi_lambda _ fun j ↦ measurable_const.mul (measurable_pi_apply j)

omit [DecidableEq ι] in
/-- Reflections preserve Lebesgue measure. -/
theorem map_orth_volume (ε : ι → Bool) : Measure.map (orth ε) volume = volume := by
  classical
  have hdet : (Matrix.diagonal fun j ↦ bsign (ε j)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ bsign_ne_zero _
  have hres : (fun v ↦ (Matrix.diagonal fun j ↦ bsign (ε j)) *ᵥ v) = orth ε := by
    funext v j
    rw [Matrix.mulVec_diagonal]
    rfl
  have h := map_mulVec_volume (Matrix.diagonal fun j ↦ bsign (ε j)) hdet
  rw [hres, Matrix.det_diagonal, Finset.abs_prod] at h
  simp only [abs_bsign, Finset.prod_const_one, inv_one, ENNReal.ofReal_one, one_smul] at h
  exact h

/-- **The orthant split**: `∫ f = ∑_ε ∫_{(0,∞)^ι} f(ε · x) dx`. -/
theorem lintegral_eq_sum_orthants (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ w, f w = ∑ ε : ι → Bool, ∫⁻ x in posOrthant, f (orth ε x) := by
  calc ∫⁻ w, f w = ∫⁻ w in {w : ι → ℝ | ∀ j, w j ≠ 0}, f w := by
        rw [← setLIntegral_univ, setLIntegral_congr (ae_eq_univ.2 volume_compl_ne_zero).symm]
    _ = ∫⁻ w in ⋃ ε : ι → Bool, orthant ε, f w := by rw [iUnion_orthant]
    _ = tsum fun ε : ι → Bool ↦ ∫⁻ w in orthant ε, f w :=
        lintegral_iUnion (fun _ ↦ measurableSet_orthant _) orthant_disjoint f
    _ = ∑ ε : ι → Bool, ∫⁻ w in orthant ε, f w := tsum_fintype _
    _ = ∑ ε : ι → Bool, ∫⁻ x in posOrthant, f (orth ε x) := by
        refine Finset.sum_congr rfl fun ε _ ↦ ?_
        calc ∫⁻ w in orthant ε, f w
            = ∫⁻ w, f w ∂((Measure.map (orth ε) volume).restrict (orthant ε)) := by
              rw [map_orth_volume]
          _ = ∫⁻ w, f w ∂((volume.restrict (orth ε ⁻¹' orthant ε)).map (orth ε)) := by
              rw [Measure.restrict_map (measurable_orth ε) (measurableSet_orthant ε)]
          _ = ∫⁻ x in orth ε ⁻¹' orthant ε, f (orth ε x) := lintegral_map hf (measurable_orth ε)
          _ = ∫⁻ x in posOrthant, f (orth ε x) := by rw [preimage_orth_orthant]

end Laplace.Multi
