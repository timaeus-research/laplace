/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FibreKernel
import Laplace.Multi.WallFibreFormulas

/-!
# The explicit form of the fibre kernels

The solved coordinate of the fibre kernel (`solvedCoord (solvedCoeff k S q w) (q k) s`) is the
`wallSolve` of `WallFibreFormulas` for the unsolved exponents `q ∘ succAbove k`, whenever `|S| = 1`
(`solvedCoord_eq_wallSolve`). Hence, on a fibre with all unsolved coordinates nonzero, a chart
monomial `|u^K|` at `u = (w, ±V)` reads `|s|^{K_k/q_k} ∏ |w_j|^{K_j − q_j K_k/q_k}`
(`abs_monomial_insertNth_solved`) and the kernel density `|u^h| · V/(q_k|s|)` reads
`(1/q_k) |s|^{(h_k+1)/q_k − 1} ∏ |w_j|^{h_j − q_j (h_k+1)/q_k}` (`density_insertNth_solved`): the
fibre formulas `ν = K_k/q_k`, `κ_j = K_j − q_j ν`, `p = (h_k+1)/q_k − 1`, `r_j = h_j − q_j (p+1)`
of the spec, now attached to the kernels of `wall_fibre_identity`.
-/

open Real MeasureTheory Set

namespace Laplace.Multi

variable {m : ℕ}

/-- The absolute value of a monomial at `insertNth k v w` splits off the solved coordinate. -/
theorem abs_monomial_insertNth (k : Fin (m + 1)) (K : Fin (m + 1) → ℕ) (v : ℝ) (w : Fin m → ℝ) :
    |∏ j, (k.insertNth v w : Fin (m + 1) → ℝ) j ^ K j| =
      |v| ^ (K k : ℝ) * ∏ j, |w j| ^ (K (k.succAbove j) : ℝ) := by
  rw [Finset.abs_prod, Fin.prod_univ_succAbove _ k, Fin.insertNth_apply_same]
  simp only [Fin.insertNth_apply_succAbove, abs_pow, Real.rpow_natCast]

/-- The solved coordinate of the kernel is the `wallSolve` of the fibre formulas (`|S| = 1`). -/
theorem solvedCoord_eq_wallSolve (k : Fin (m + 1)) {S : ℝ} (hS : |S| = 1) (q : Fin (m + 1) → ℕ)
    (s : ℝ) (w : Fin m → ℝ) :
    solvedCoord (solvedCoeff k S q w) (q k) s =
      wallSolve (fun j : Fin m ↦ (q (k.succAbove j) : ℝ)) (q k) s w := by
  unfold solvedCoord solvedCoeff wallSolve
  congr 1
  rw [abs_mul, hS, one_mul, Finset.abs_prod, div_eq_mul_inv, ← Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [abs_pow, Real.rpow_neg (abs_nonneg _), Real.rpow_natCast]

/-- A chart monomial on the fibre, in the solved point `(w, ±V)`:
`|u^K| = |s|^{K_k/q_k} ∏ |w_j|^{K_j − q_j K_k/q_k}`. -/
theorem abs_monomial_insertNth_solved (k : Fin (m + 1)) {S : ℝ} (hS : |S| = 1)
    (q : Fin (m + 1) → ℕ) (K : Fin (m + 1) → ℕ) {s : ℝ} (hs : s ≠ 0) {w : Fin m → ℝ}
    (hw : ∀ j, w j ≠ 0) (σ : ℝ) (hσ : |σ| = 1) :
    |∏ j, (k.insertNth (σ * solvedCoord (solvedCoeff k S q w) (q k) s) w : Fin (m + 1) → ℝ) j ^
        K j| =
      |s| ^ ((K k : ℝ) / q k) * ∏ j, |w j| ^ ((K (k.succAbove j) : ℝ) - q (k.succAbove j) *
        (K k : ℝ) / q k) := by
  rw [abs_monomial_insertNth, abs_mul, hσ, one_mul, abs_of_nonneg (solvedCoord_nonneg _ _ _),
    solvedCoord_eq_wallSolve k hS q s w,
    wallSolve_monomial hs hw (fun j ↦ (K (k.succAbove j) : ℝ)) (K k : ℝ)]

/-- The kernel density on the fibre: `|u^h| · V/(q_k |s|) = (1/q_k) |s|^{(h_k+1)/q_k − 1}
∏ |w_j|^{h_j − q_j (h_k+1)/q_k}`. -/
theorem density_insertNth_solved (k : Fin (m + 1)) {S : ℝ} (hS : |S| = 1)
    {q : Fin (m + 1) → ℕ} (hq : 0 < q k) (h : Fin (m + 1) → ℕ) {s : ℝ} (hs : s ≠ 0)
    {w : Fin m → ℝ} (hw : ∀ j, w j ≠ 0) (σ : ℝ) (hσ : |σ| = 1) :
    |∏ j, (k.insertNth (σ * solvedCoord (solvedCoeff k S q w) (q k) s) w : Fin (m + 1) → ℝ) j ^
        h j| * (solvedCoord (solvedCoeff k S q w) (q k) s / (q k * |s|)) =
      1 / q k * |s| ^ (((h k : ℝ) + 1) / q k - 1) *
        ∏ j, |w j| ^ ((h (k.succAbove j) : ℝ) - q (k.succAbove j) * ((h k : ℝ) + 1) / q k) := by
  have hq' : (0 : ℝ) < q k := by exact_mod_cast hq
  rw [abs_monomial_insertNth, abs_mul, hσ, one_mul, abs_of_nonneg (solvedCoord_nonneg _ _ _),
    solvedCoord_eq_wallSolve k hS q s w, ← mul_div_assoc,
    wallSolve_density hq' hs hw (fun j ↦ (h (k.succAbove j) : ℝ)) (h k : ℝ)]

end Laplace.Multi
