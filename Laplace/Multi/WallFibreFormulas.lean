/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# The fibre formulas of a wall-adapted monomial chart, one truth variable

The algebraic content of the fibre part of the `OneParameterWallMonomialAtlas` spec
(`docs/hironaka_wall_atlas_spec.md`). In a chart with coordinates `(u, v)`, `u ∈ ℝ^ι` and `v` the
solved coordinate, suppose on a sign branch `|s| = |v|^{q_ℓ} ∏ |u_i|^{q_i}` with `q_ℓ > 0`. Then the
fibre over `s` is parametrised by `u` through `v(u, s) = (|s| ∏ |u_i|^{-q_i})^{1/q_ℓ}`
(`wallSolve`), and the monomials of the chart restrict to the fibre as monomials in `|s|` and `|u|`:
`|v|^{K_ℓ} ∏ |u_i|^{K_i} = |s|^{K_ℓ/q_ℓ} ∏ |u_i|^{K_i − q_i K_ℓ/q_ℓ}` (`wallSolve_monomial`), and
the
relative density `|v|^{H_ℓ} ∏ |u_i|^{H_i} · |v| / (q_ℓ |s|)` (total Jacobian over `|∂s/∂v|`) equals
`(1/q_ℓ) |s|^{(H_ℓ+1)/q_ℓ − 1} ∏ |u_i|^{H_i − q_i (H_ℓ+1)/q_ℓ}` (`wallSolve_density`). These are the
exponents `ν, κ_i, p, r_i` of the spec.
-/

open Real

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-- The solved coordinate `v(u, s) = (|s| ∏ |u_i|^{-q_i})^{1/q_ℓ}`. -/
noncomputable def wallSolve (q : ι → ℝ) (qℓ : ℝ) (s : ℝ) (u : ι → ℝ) : ℝ :=
  (|s| * ∏ i, |u i| ^ (-q i)) ^ (1 / qℓ)

theorem wallSolve_pos {q : ι → ℝ} {qℓ s : ℝ} {u : ι → ℝ} (hs : s ≠ 0) (hu : ∀ i, u i ≠ 0) :
    0 < wallSolve q qℓ s u :=
  Real.rpow_pos_of_pos (mul_pos (abs_pos.mpr hs)
    (Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos (abs_pos.mpr (hu i)) _)) _

/-- The solved coordinate satisfies the base equation `|v|^{q_ℓ} ∏ |u_i|^{q_i} = |s|`. -/
theorem wallSolve_base {q : ι → ℝ} {qℓ : ℝ} (hq : 0 < qℓ) {s : ℝ} (hs : s ≠ 0) {u : ι → ℝ}
    (hu : ∀ i, u i ≠ 0) :
    wallSolve q qℓ s u ^ qℓ * ∏ i, |u i| ^ (q i) = |s| := by
  unfold wallSolve
  have hp : 0 < ∏ i, |u i| ^ (-q i) := Finset.prod_pos fun i _ ↦
    Real.rpow_pos_of_pos (abs_pos.mpr (hu i)) _
  rw [← Real.rpow_mul (mul_pos (abs_pos.mpr hs) hp).le, one_div_mul_cancel hq.ne', Real.rpow_one,
    mul_assoc, ← Finset.prod_mul_distrib]
  have : ∀ i, |u i| ^ (-q i) * |u i| ^ (q i) = 1 := fun i ↦ by
    rw [← Real.rpow_add (abs_pos.mpr (hu i)), neg_add_cancel, Real.rpow_zero]
  simp only [this, Finset.prod_const_one, mul_one]

/-- A chart monomial on the fibre:
`v^{Kℓ} ∏ |u_i|^{K_i} = |s|^{Kℓ/qℓ} ∏ |u_i|^{K_i − q_i Kℓ/qℓ}`. -/
theorem wallSolve_monomial {q : ι → ℝ} {qℓ : ℝ} {s : ℝ} (hs : s ≠ 0) {u : ι → ℝ}
    (hu : ∀ i, u i ≠ 0) (K : ι → ℝ) (Kℓ : ℝ) :
    wallSolve q qℓ s u ^ Kℓ * ∏ i, |u i| ^ (K i) =
      |s| ^ (Kℓ / qℓ) * ∏ i, |u i| ^ (K i - q i * Kℓ / qℓ) := by
  unfold wallSolve
  have hp : 0 < ∏ i, |u i| ^ (-q i) := Finset.prod_pos fun i _ ↦
    Real.rpow_pos_of_pos (abs_pos.mpr (hu i)) _
  have hs0 : 0 < |s| := abs_pos.mpr hs
  rw [← Real.rpow_mul (mul_pos hs0 hp).le, Real.mul_rpow hs0.le hp.le, ← Real.finsetProd_rpow _ _
    (fun i _ ↦ Real.rpow_nonneg (abs_nonneg _) _), one_div_mul_eq_div, mul_assoc,
    ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← Real.rpow_mul (abs_nonneg _), ← Real.rpow_add (abs_pos.mpr (hu i))]
  congr 1
  ring

/-- The relative density on the fibre: `|v|^{Hℓ} ∏|u_i|^{H_i} · v / (qℓ |s|) =
`(1/qℓ) |s|^{(Hℓ+1)/qℓ − 1} ∏ |u_i|^{H_i − q_i (Hℓ+1)/qℓ}`. -/
theorem wallSolve_density {q : ι → ℝ} {qℓ : ℝ} (hq : 0 < qℓ) {s : ℝ} (hs : s ≠ 0) {u : ι → ℝ}
    (hu : ∀ i, u i ≠ 0) (H : ι → ℝ) (Hℓ : ℝ) :
    wallSolve q qℓ s u ^ Hℓ * (∏ i, |u i| ^ (H i)) * wallSolve q qℓ s u / (qℓ * |s|) =
      1 / qℓ * |s| ^ ((Hℓ + 1) / qℓ - 1) * ∏ i, |u i| ^ (H i - q i * (Hℓ + 1) / qℓ) := by
  have hv := wallSolve_pos (q := q) (qℓ := qℓ) hs hu
  have hs0 : 0 < |s| := abs_pos.mpr hs
  have e : wallSolve q qℓ s u ^ Hℓ * (∏ i, |u i| ^ (H i)) * wallSolve q qℓ s u =
      wallSolve q qℓ s u ^ (Hℓ + 1) * ∏ i, |u i| ^ (H i) := by
    rw [Real.rpow_add hv, Real.rpow_one]; ring
  rw [e, wallSolve_monomial hs hu H (Hℓ + 1), Real.rpow_sub hs0, Real.rpow_one]
  field_simp

end Laplace.Multi
