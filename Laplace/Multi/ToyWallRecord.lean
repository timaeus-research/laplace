/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.WallPhaseData

/-!
# A toy wall record: the identity chart for `F = (1 + x²) s² x²`

A concrete `WallChartsData` with one chart, the identity representative on the sup-norm ball of
radius `1` in `Fin 2 → ℝ` (truth coordinate `z 0 = s`, loss coordinate `z 1 = x`), the truth
monomial `s` itself (`S = 1`, `q = (1, 0)`, solve index `0`), a continuous density equal to `1` on
the ball of radius `1/2` and vanishing off the open unit ball, and the slab
`L' = [-1/2, 1/2] × closedBall(1/2)` (which is the sup-norm ball of radius `1/2`). Its phase data
for `F = (1 + x²) s² x²`: exponents `kF = (2, 2)`, Jacobian exponents `0`, unit `a = 1 + x²`
bounded between `1` and `2` on the unit ball, `b = 1`, weight the density. This instance feeds the
analytic layer in `ToyWallLimit`.
-/

open Real MeasureTheory Set
open scoped ENNReal

namespace Laplace.Multi.ToyWall

/-- The toy loss `F(s, x) = (1 + x²) s² x²`. -/
noncomputable def toyF (z : Fin 2 → ℝ) : ℝ := (1 + z 1 ^ 2) * z 0 ^ 2 * z 1 ^ 2

/-- The toy density: `1` on the ball of radius `1/2`, `0` off the unit ball, continuous. -/
noncomputable def toyDens (u : Fin 2 → ℝ) : ℝ := min 1 (max 0 (2 - 2 * ‖u‖))

theorem toyDens_nonneg (u : Fin 2 → ℝ) : 0 ≤ toyDens u := le_min zero_le_one (le_max_left _ _)

theorem toyDens_le_one (u : Fin 2 → ℝ) : toyDens u ≤ 1 := min_le_left _ _

theorem continuous_toyDens : Continuous toyDens :=
  continuous_const.min (continuous_const.max (continuous_const.sub (continuous_const.mul
    continuous_norm)))

theorem toyDens_eq_one {u : Fin 2 → ℝ} (hu : ‖u‖ ≤ 1 / 2) : toyDens u = 1 := by
  unfold toyDens
  rw [min_eq_left]
  exact le_max_of_le_right (by linarith)

theorem toyDens_supp {u : Fin 2 → ℝ} (hu : toyDens u ≠ 0) : ‖u‖ < 1 := by
  by_contra h
  apply hu
  unfold toyDens
  rw [max_eq_left (by linarith [not_lt.mp h]), min_eq_right zero_le_one]

/-- The slab `[-1/2, 1/2] × closedBall(1/2)` in the split coordinates. -/
def toyL' : Set (Fin 2 → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) (0 : Fin 2)) ⁻¹'
    (Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Metric.closedBall (0 : Fin 1 → ℝ) (1 / 2))

theorem toyL'_eq : toyL' = Metric.closedBall (0 : Fin 2 → ℝ) (1 / 2) := by
  ext z
  simp only [toyL', mem_preimage, mem_prod, mem_Icc, mem_closedBall_zero_iff,
    pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.norm_eq_abs, abs_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩ i
    fin_cases i
    · exact ⟨h1, h2⟩
    · have := h3 0
      simpa [Fin.tail] using this
  · intro h
    refine ⟨h 0, fun j ↦ ?_⟩
    have := h 1
    rw [Fin.fin_one_eq_zero j]
    simpa [Fin.tail] using this

theorem measurableSet_toyL' : MeasurableSet toyL' := by
  rw [toyL'_eq]
  exact Metric.isClosed_closedBall.measurableSet

theorem toyL'_subset : toyL' ⊆ Metric.closedBall (0 : Fin 2 → ℝ) 1 := by
  rw [toyL'_eq]
  exact Metric.closedBall_subset_closedBall (by norm_num)

/-- The toy chart record: one identity chart. -/
noncomputable def toyData : WallChartsData 1 0 toyL' where
  ι := Unit
  rep := fun _ u ↦ u
  rep_cont := fun _ ↦ continuous_id
  ρ := fun _ ↦ 1
  ρ_pos := fun _ ↦ one_pos
  dom := fun _ ↦ Metric.closedBall (0 : Fin 2 → ℝ) 1 ∩ toyL'
  dom_eq := fun _ ↦ rfl
  dom_meas := fun _ ↦ Metric.isClosed_closedBall.measurableSet.inter measurableSet_toyL'
  dens := fun _ ↦ toyDens
  dens_cont := fun _ ↦ continuous_toyDens
  dens_nonneg := fun _ ↦ toyDens_nonneg
  dens_supp := fun _ u hu ↦ mem_ball_zero_iff.mpr (toyDens_supp hu)
  S := fun _ ↦ 1
  S_ne := fun _ ↦ one_ne_zero
  q := fun _ ↦ ![1, 0]
  k := fun _ ↦ 0
  q_pos := fun _ ↦ by simp
  truth := fun _ u _ ↦ by
    simp [truthMono, Fin.prod_univ_two]
  transport := fun Ψ _ ↦ by
    rw [Fintype.sum_unique, Set.inter_eq_right.mpr toyL'_subset]
    refine (setLIntegral_congr_fun measurableSet_toyL' fun u hu ↦ ?_).symm
    rw [toyDens_eq_one (by rw [toyL'_eq] at hu; exact mem_closedBall_zero_iff.mp hu),
      ENNReal.ofReal_one, mul_one]

theorem toyData_rep (i : toyData.ι) (u : Fin 2 → ℝ) : toyData.rep i u = u := rfl

theorem toyData_dens (i : toyData.ι) (u : Fin 2 → ℝ) : toyData.dens i u = toyDens u := rfl

theorem toyData_ρ (i : toyData.ι) : toyData.ρ i = 1 := rfl

theorem toyData_S (i : toyData.ι) : toyData.S i = 1 := rfl

theorem toyData_q (i : toyData.ι) : toyData.q i = ![1, 0] := rfl

theorem toyData_k (i : toyData.ι) : toyData.k i = 0 := rfl

/-- The phase data of the toy chart for `F = (1 + x²) s² x²`. -/
noncomputable def toyPhase : toyData.Phase toyF where
  kF := fun _ ↦ ![2, 2]
  hJ := fun _ ↦ ![0, 0]
  a := fun _ u ↦ 1 + u 1 ^ 2
  b := fun _ _ ↦ 1
  wt := fun _ ↦ toyDens
  a_cont := fun _ ↦ by fun_prop
  b_cont := fun _ ↦ continuous_const
  wt_cont := fun _ ↦ continuous_toyDens
  wt_nonneg := fun _ ↦ toyDens_nonneg
  wt_le_one := fun _ ↦ toyDens_le_one
  ma := fun _ ↦ 1
  Ma := fun _ ↦ 2
  mb := fun _ ↦ 1
  Mb := fun _ ↦ 1
  ma_pos := fun _ ↦ one_pos
  mb_pos := fun _ ↦ one_pos
  a_bounds := fun _ u hu ↦ by
    have h1 : |u 1| ≤ 1 := by
      have := norm_le_pi_norm u 1
      rw [Real.norm_eq_abs] at this
      exact this.trans (mem_closedBall_zero_iff.mp hu)
    have h2 : u 1 ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) h1
    constructor
    · rw [abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg (u 1)]
    · rw [abs_of_nonneg (by positivity)]
      linarith
  b_bounds := fun _ _ _ ↦ by simp
  phase := fun _ u _ ↦ by
    simp only [toyData_rep, toyF, Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.succ_zero_eq_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
    ring
  dens_eq := fun _ u _ ↦ by
    simp only [toyData_dens, Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.succ_zero_eq_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, pow_zero, mul_one, abs_one]

end Laplace.Multi.ToyWall
