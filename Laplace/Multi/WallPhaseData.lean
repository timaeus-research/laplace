/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.WallChartsData

/-!
# The phase data of a wall atlas

The enrichment of `WallChartsData` by the analytic data of the charts (Astra,
`research_kernel_asymptotics_v1`, 7.4): on the box of each chart, `F ∘ rep_i = a_i · ∏ u^{k_i}`
with a continuous unit `a_i` bounded away from `0` and `∞` on the closed box, and the density is
`dens_i = wt_i · |b_i ∏ u^{h_i}|` with a continuous partition weight `wt_i ∈ [0, 1]` and a
continuous
Jacobian unit `b_i` with two-sided bounds (`WallChartsData.Phase`). This is exactly what
`WallAtlas.euclidean_export` provides (hironaka branch `wall-atlas`); the asymptotic analysis of the
kernels of `wall_fibre_identity` reads the exponents `k_i, h_i, q_i` and the unit bounds from here.
-/

open Real MeasureTheory Set

namespace Laplace.Multi

variable {m : ℕ}

/-- The phase data of a wall atlas over `L'`, for the loss `F`. -/
structure WallChartsData.Phase {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}
    (D : WallChartsData m ℓ L') (F : (Fin (m + 1) → ℝ) → ℝ) where
  /-- Exponents of the loss and of the Jacobian. -/
  kF : D.ι → Fin (m + 1) → ℕ
  hJ : D.ι → Fin (m + 1) → ℕ
  /-- Units of the loss and of the Jacobian, and the partition weight. -/
  a : D.ι → (Fin (m + 1) → ℝ) → ℝ
  b : D.ι → (Fin (m + 1) → ℝ) → ℝ
  wt : D.ι → (Fin (m + 1) → ℝ) → ℝ
  a_cont : ∀ i, Continuous (a i)
  b_cont : ∀ i, Continuous (b i)
  wt_cont : ∀ i, Continuous (wt i)
  wt_nonneg : ∀ i u, 0 ≤ wt i u
  wt_le_one : ∀ i u, wt i u ≤ 1
  /-- Two-sided bounds of the units on the closed boxes. -/
  ma : D.ι → ℝ
  Ma : D.ι → ℝ
  mb : D.ι → ℝ
  Mb : D.ι → ℝ
  ma_pos : ∀ i, 0 < ma i
  mb_pos : ∀ i, 0 < mb i
  a_bounds : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
    ma i ≤ |a i u| ∧ |a i u| ≤ Ma i
  b_bounds : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
    mb i ≤ |b i u| ∧ |b i u| ≤ Mb i
  /-- The loss and the density on the box. -/
  phase : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
    F (D.rep i u) = a i u * ∏ j, u j ^ kF i j
  dens_eq : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
    D.dens i u = wt i u * |b i u * ∏ j, u j ^ hJ i j|

namespace WallChartsData.Phase

variable {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)} {D : WallChartsData m ℓ L'}
  {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)

/-- The absolute value of the loss on the box: `|F ∘ rep_i| = |a_i| ∏ |u_j|^{k_ij}`. -/
theorem abs_loss (i : D.ι) {u : Fin (m + 1) → ℝ}
    (hu : u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i)) :
    |F (D.rep i u)| = |P.a i u| * ∏ j, |u j| ^ P.kF i j := by
  rw [P.phase i u hu, abs_mul, Finset.abs_prod]
  simp only [abs_pow]

/-- The two-sided monomial bounds of the loss on the box. -/
theorem abs_loss_bounds (i : D.ι) {u : Fin (m + 1) → ℝ}
    (hu : u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i)) :
    P.ma i * ∏ j, |u j| ^ P.kF i j ≤ |F (D.rep i u)| ∧
      |F (D.rep i u)| ≤ P.Ma i * ∏ j, |u j| ^ P.kF i j := by
  rw [P.abs_loss i hu]
  have hp : 0 ≤ ∏ j, |u j| ^ P.kF i j := Finset.prod_nonneg fun j _ ↦ by positivity
  exact ⟨mul_le_mul_of_nonneg_right (P.a_bounds i u hu).1 hp,
    mul_le_mul_of_nonneg_right (P.a_bounds i u hu).2 hp⟩

/-- The density on the box is bounded by the Jacobian monomial. -/
theorem dens_le (i : D.ι) {u : Fin (m + 1) → ℝ}
    (hu : u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i)) :
    D.dens i u ≤ P.Mb i * ∏ j, |u j| ^ P.hJ i j := by
  rw [P.dens_eq i u hu, abs_mul, Finset.abs_prod]
  simp only [abs_pow]
  have hp : 0 ≤ ∏ j, |u j| ^ P.hJ i j := Finset.prod_nonneg fun j _ ↦ by positivity
  calc P.wt i u * (|P.b i u| * ∏ j, |u j| ^ P.hJ i j)
      ≤ 1 * (P.Mb i * ∏ j, |u j| ^ P.hJ i j) := by
        refine mul_le_mul (P.wt_le_one i u) (mul_le_mul_of_nonneg_right (P.b_bounds i u hu).2 hp)
          (mul_nonneg (abs_nonneg _) hp) zero_le_one
    _ = P.Mb i * ∏ j, |u j| ^ P.hJ i j := one_mul _

end WallChartsData.Phase

end Laplace.Multi
