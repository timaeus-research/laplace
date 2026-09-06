/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.Ladder

/-!
# Extension of the fluctuation function to non-positive order (grammar §4 `defn:S_negative`)

For `λ > 0` the fluctuation function `S_λ` is given by its integral. The grammar paper extends it to
`λ ≤ 0` (away from the poles `λ ∈ {0, -1/2, -1, …}`) by the recursion

  `S_λ(a) = (β^{1/2} / (2λ)) · b S_{λ+1/2}(a)`,   `b = 2β^{-1/2}∂_a - β^{1/2}a`,

which lowers the order by `1/2` each time until it reaches the integral regime. We formalise the
extension along a fixed base order `μ > 0` by the number of half-steps taken below it: `Sneg β μ k`
represents `S_{μ - k/2}`. The extension satisfies the **lowering** ladder relation of
`lem:extended_ladder`, `b S_{ρ} = (2ρ-1) β^{-1/2} S_{ρ-1/2}`, *definitionally* (the recursion
rearranged).

The **raising** relation `b† S_λ = β^{1/2} S_{λ+1/2}` and the general-`Q` number operator
additionally require the `C^∞`-smoothness of the extension (to apply `b`, `b†` and the Weyl
commutator `[b,b†]=1`), and are left for a follow-up.
-/

open Real

namespace Laplace.Grammar

/-- The fluctuation function extended below a base order `μ > 0`: `Sneg β μ k` is `S_{μ - k/2}(a)`,
defined by the paper's downward recursion `S_λ = (β^{1/2}/(2λ)) b S_{λ+1/2}` (grammar §4
`defn:S_negative`). At `k = 0` it is the integral `S_μ`. -/
noncomputable def Sneg (β μ : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun a => fluctuation β μ a
  | (k + 1) => fun a =>
      β ^ ((1 : ℝ) / 2) / (2 * (μ - (↑(k + 1)) / 2)) * lowerOp β (Sneg β μ k) a

/-- The base case: `Sneg β μ 0 = S_μ`. -/
theorem Sneg_zero (β μ : ℝ) : Sneg β μ 0 = fun a => fluctuation β μ a := rfl

/-- **Extended lowering relation** (grammar §4 `lem:extended_ladder`):
`b S_ρ = (2ρ-1)β^{-1/2} S_{ρ-1/2}` for the extended fluctuation function, at `ρ = μ - k/2`
(provided `ρ - 1/2 = μ - (k+1)/2` is not a pole). This is the defining recursion rearranged: the
`β^{1/2}/(2λ)` prefactor inverts to `(2λ)/β^{1/2} = (2ρ-1)/β^{1/2}`. -/
theorem Sneg_lowering (β μ : ℝ) (hβ : 0 < β) (k : ℕ) (hlam : μ - (↑(k + 1)) / 2 ≠ 0) (a : ℝ) :
    lowerOp β (fun a => Sneg β μ k a) a
      = (2 * (μ - ↑k / 2) - 1) * β ^ (-(1 : ℝ) / 2) * Sneg β μ (k + 1) a := by
  have hβh : β ^ (-(1 : ℝ) / 2) * β ^ ((1 : ℝ) / 2) = 1 := by rw [← Real.rpow_add hβ]; norm_num
  have hlam2 : 2 * (μ - (↑(k + 1)) / 2) ≠ 0 := by intro h; apply hlam; linarith [h]
  have hnum : 2 * (μ - ↑k / 2) - 1 = 2 * (μ - (↑(k + 1)) / 2) := by push_cast; ring
  rw [show Sneg β μ (k + 1) a = β ^ ((1 : ℝ) / 2) / (2 * (μ - (↑(k + 1)) / 2))
        * lowerOp β (fun a => Sneg β μ k a) a from rfl,
    show (2 * (μ - ↑k / 2) - 1) * β ^ (-(1 : ℝ) / 2)
        * (β ^ ((1 : ℝ) / 2) / (2 * (μ - (↑(k + 1)) / 2)) * lowerOp β (fun a => Sneg β μ k a) a)
      = ((2 * (μ - ↑k / 2) - 1) / (2 * (μ - (↑(k + 1)) / 2)))
        * (β ^ (-(1 : ℝ) / 2) * β ^ ((1 : ℝ) / 2)) * lowerOp β (fun a => Sneg β μ k a) a by ring,
    hβh, hnum, div_self hlam2]
  ring

end Laplace.Grammar
