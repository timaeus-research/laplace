/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.OneLoop

/-!
# The one-loop covariance of a separable anharmonic potential (E2, E7)

The sanity note's separable potential `L = ∑ᵢ (λᵢ/2 uᵢ² + αᵢ/6 uᵢ³ + gᵢ/24 uᵢ⁴)` has cubic tensor
`Tᵢᵢᵢ = αᵢ` and quartic tensor `Qᵢᵢᵢᵢ = gᵢ` (all other entries zero) in its eigenframe. This file
evaluates the one-loop functional `oneLoopCov` of `Laplace/Multi/OneLoop.lean` on it:

* `contractQ_sep`, `contractT_sep`, `bubble_sep`, `tadpoleLine_sep`, `oneLoopPi_sep`: the pieces
  of the functional on a diagonal `S` are diagonal, `Πᵢᵢ = −(t/2) gᵢ sᵢ + t² αᵢ² sᵢ²`;
* `oneLoopCov_separable`: `oneLoopCov t (diag λ) (sepT α) (sepQ g)` is diagonal with entries
  `1/(λᵢ t) + (αᵢ²/λᵢ⁴ − gᵢ/(2λᵢ³))/t²`, the one-dimensional second-order variance of
  `oneLoopCov_oneDim` in each direction: the functional respects separability, so E7's
  "one dimension at a time" comparison is the `d`-dimensional prediction;
* `oneLoopCov_separable_note`, `oneLoopCov_separable_note_ratio`: in the note's parametrisation
  `αᵢ² = a² λᵢ³`, `gᵢ = λᵢ²` the entry is `1/(λᵢ t) + (a² − 1/2)/(λᵢ t²)` and the relative
  second-order correction is `(a² − 1/2)/t` in every direction (E2's "relative error ∝ 1/t").
-/

open Matrix

namespace Laplace.Multi

variable {d : ℕ}

/-- The cubic tensor of a separable potential: `Tᵢᵢᵢ = αᵢ`, all other entries `0`. -/
def sepT (α : Fin d → ℝ) : Fin d → Fin d → Fin d → ℝ :=
  fun i j k => if i = j ∧ j = k then α i else 0

/-- The quartic tensor of a separable potential: `Qᵢᵢᵢᵢ = gᵢ`, all other entries `0`. -/
def sepQ (g : Fin d → ℝ) : Fin d → Fin d → Fin d → Fin d → ℝ :=
  fun i j k l => if i = j ∧ j = k ∧ k = l then g i else 0

/-- `(t • diag λ)⁻¹ = diag (1/(tλᵢ))`. -/
theorem smul_diagonal_inv {lam : Fin d → ℝ} {t : ℝ} (hlam : ∀ i, lam i ≠ 0) (ht : t ≠ 0) :
    (t • diagonal lam)⁻¹ = diagonal (fun i => 1 / (t * lam i)) := by
  apply Matrix.inv_eq_right_inv
  have h : t • diagonal lam = diagonal (fun i => t * lam i) := by
    rw [← diagonal_smul]
    rfl
  rw [h, diagonal_mul_diagonal]
  have : (fun i => t * lam i * (1 / (t * lam i))) = fun _ => (1 : ℝ) :=
    funext fun i => mul_one_div_cancel (mul_ne_zero ht (hlam i))
  rw [this, diagonal_one]

/-- The quartic tadpole of the separable tensor on a diagonal `S`: `(Q:S)ᵢⱼ = δᵢⱼ gᵢ sᵢ`. -/
theorem contractQ_sep (g s : Fin d → ℝ) :
    contractQ (sepQ g) (diagonal s) = diagonal (fun i => g i * s i) := by
  ext i j
  simp only [contractQ, sepQ, Matrix.of_apply, diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
    rw [Finset.sum_eq_single i (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
    simp
  · simp [hij]

/-- `(T:S)ₗ = αₗ sₗ` for the separable tensor on a diagonal `S`. -/
theorem contractT_sep (α s : Fin d → ℝ) :
    contractT (sepT α) (diagonal s) = fun l => α l * s l := by
  funext l
  simp only [contractT, sepT, diagonal_apply]
  rw [Finset.sum_eq_single l (fun m _ hm => by simp [Ne.symm hm]) (by simp)]
  rw [Finset.sum_eq_single l (fun n _ hn => by simp [Ne.symm hn]) (by simp)]
  simp

/-- The cubic bubble of the separable tensor on a diagonal `S`: `(TSST)ᵢⱼ = δᵢⱼ αᵢ² sᵢ²`. -/
theorem bubble_sep (α s : Fin d → ℝ) :
    bubble (sepT α) (diagonal s) = diagonal (fun i => α i ^ 2 * s i ^ 2) := by
  ext i j
  simp only [bubble, sepT, Matrix.of_apply, diagonal_apply]
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
  rw [Finset.sum_eq_single i (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
  rw [Finset.sum_eq_single i (fun m _ hm => by simp [Ne.symm hm]) (by simp)]
  rw [Finset.sum_eq_single i (fun n _ hn => by simp [Ne.symm hn]) (by simp)]
  by_cases hij : i = j
  · subst hij
    simp
    ring
  · simp [hij, Ne.symm hij]

/-- The cubic tadpole on the line of the separable tensor on a diagonal `S`:
`(T·S·(T:S))ᵢⱼ = δᵢⱼ αᵢ² sᵢ²`. -/
theorem tadpoleLine_sep (α s : Fin d → ℝ) :
    tadpoleLine (sepT α) (diagonal s) = diagonal (fun i => α i ^ 2 * s i ^ 2) := by
  ext i j
  simp only [tadpoleLine, contractT_sep, Matrix.of_apply, diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp only [sepT, true_and]
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
    rw [Finset.sum_eq_single i (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
    simp
    ring
  · simp [sepT, hij]

/-- `Π` of the separable tensors on a diagonal `S`: `Πᵢⱼ = δᵢⱼ (−(t/2) gᵢ sᵢ + t² αᵢ² sᵢ²)`. -/
theorem oneLoopPi_sep (t : ℝ) (α g s : Fin d → ℝ) :
    oneLoopPi t (sepT α) (sepQ g) (diagonal s) =
      diagonal (fun i => -(t / 2) * (g i * s i) + t ^ 2 * (α i ^ 2 * s i ^ 2)) := by
  rw [oneLoopPi, contractQ_sep, bubble_sep, tadpoleLine_sep]
  simp only [← diagonal_smul, diagonal_add]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **The one-loop covariance of a separable anharmonic potential is diagonal with the
one-dimensional second-order variances**: for `H = diag λ`, `Tᵢᵢᵢ = αᵢ`, `Qᵢᵢᵢᵢ = gᵢ`,
`oneLoopCov = diag (1/(λᵢ t) + (αᵢ²/λᵢ⁴ − gᵢ/(2λᵢ³))/t²)`. -/
theorem oneLoopCov_separable {lam : Fin d → ℝ} (α g : Fin d → ℝ) {t : ℝ} (hlam : ∀ i, lam i ≠ 0)
    (ht : t ≠ 0) :
    oneLoopCov t (diagonal lam) (sepT α) (sepQ g) =
      diagonal (fun i =>
        1 / (lam i * t) + (α i ^ 2 / lam i ^ 4 - g i / (2 * lam i ^ 3)) / t ^ 2) := by
  rw [oneLoopCov, smul_diagonal_inv hlam ht, oneLoopPi_sep, diagonal_mul_diagonal,
    diagonal_mul_diagonal, diagonal_add]
  congr 1
  funext i
  have := hlam i
  field_simp
  ring

/-- **The note's parametrisation** `αᵢ² = a² λᵢ³`, `gᵢ = λᵢ²`: the one-loop variance along direction
`i` is `1/(λᵢ t) + (a² − 1/2)/(λᵢ t²)`. -/
theorem oneLoopCov_separable_note {lam α : Fin d → ℝ} {a t : ℝ} (hlam : ∀ i, 0 < lam i)
    (hα : ∀ i, α i ^ 2 = a ^ 2 * lam i ^ 3) (ht : t ≠ 0) (i : Fin d) :
    oneLoopCov t (diagonal lam) (sepT α) (sepQ (fun i => lam i ^ 2)) i i =
      1 / (lam i * t) + (a ^ 2 - 1 / 2) / (lam i * t ^ 2) := by
  rw [oneLoopCov_separable α _ (fun i => (hlam i).ne') ht, diagonal_apply_eq, hα]
  have := (hlam i).ne'
  field_simp

/-- **The relative second-order correction is `(a² − 1/2)/t` in every direction**: the ratio of
the second-order term to the Laplace variance `1/(λᵢ t)` does not depend on `λᵢ`. -/
theorem oneLoopCov_separable_note_ratio {lam α : Fin d → ℝ} {a t : ℝ} (hlam : ∀ i, 0 < lam i)
    (hα : ∀ i, α i ^ 2 = a ^ 2 * lam i ^ 3) (ht : t ≠ 0) (i : Fin d) :
    (oneLoopCov t (diagonal lam) (sepT α) (sepQ (fun i => lam i ^ 2)) i i - 1 / (lam i * t)) /
        (1 / (lam i * t)) =
      (a ^ 2 - 1 / 2) / t := by
  rw [oneLoopCov_separable_note hlam hα ht i]
  have := (hlam i).ne'
  field_simp
  ring


/-! ### The anharmonic potential has a unique global minimum -/

/-- `λ/2 u² + α/6 u³ + g/24 u⁴ = u² (g u² + 4α u + 12λ)/24`. -/
theorem anharmonic_factor (lam alpha g u : ℝ) :
    lam / 2 * u ^ 2 + alpha / 6 * u ^ 3 + g / 24 * u ^ 4 =
      u ^ 2 * (g * u ^ 2 + 4 * alpha * u + 12 * lam) / 24 := by
  ring

/-- **`α² < 3λg` keeps the minimum unique**: the one-dimensional anharmonic potential is positive
away from `0` (a unique global minimiser; other stationary points are excluded only under the
stronger `α² < (8/3)λg`). -/
theorem anharmonic_pos {lam alpha g : ℝ} (hg : 0 < g) (hdisc : alpha ^ 2 < 3 * lam * g) {u : ℝ}
    (hu : u ≠ 0) :
    0 < lam / 2 * u ^ 2 + alpha / 6 * u ^ 3 + g / 24 * u ^ 4 := by
  rw [anharmonic_factor]
  have hq : 0 < g * u ^ 2 + 4 * alpha * u + 12 * lam := by
    have h1 : 0 < g * (g * u ^ 2 + 4 * alpha * u + 12 * lam) := by
      have : g * (g * u ^ 2 + 4 * alpha * u + 12 * lam) =
          (g * u + 2 * alpha) ^ 2 + (12 * lam * g - 4 * alpha ^ 2) := by ring
      rw [this]
      nlinarith [sq_nonneg (g * u + 2 * alpha)]
    exact pos_of_mul_pos_right h1 hg.le
  positivity

/-- **The note's parametrisation**: with `α² = a² λ³` and `g = λ²`, the discriminant condition
`α² < 3λg` is `a² < 3`. -/
theorem disc_iff_note {lam alpha a : ℝ} (hlam : 0 < lam) (hα : alpha ^ 2 = a ^ 2 * lam ^ 3) :
    alpha ^ 2 < 3 * lam * lam ^ 2 ↔ a ^ 2 < 3 := by
  rw [hα]
  have h3 : 0 < lam ^ 3 := pow_pos hlam 3
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- **Absolute relative second-order correction** `|a² − 1/2|/t` for `t > 0`. -/
theorem oneLoopCov_separable_note_abs_ratio {lam α : Fin d → ℝ} {a t : ℝ} (hlam : ∀ i, 0 < lam i)
    (hα : ∀ i, α i ^ 2 = a ^ 2 * lam i ^ 3) (ht : 0 < t) (i : Fin d) :
    |(oneLoopCov t (diagonal lam) (sepT α) (sepQ (fun i => lam i ^ 2)) i i - 1 / (lam i * t)) /
        (1 / (lam i * t))| =
      |a ^ 2 - 1 / 2| / t := by
  rw [oneLoopCov_separable_note_ratio hlam hα ht.ne' i, abs_div, abs_of_pos ht]

end Laplace.Multi
