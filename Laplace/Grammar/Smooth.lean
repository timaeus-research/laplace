/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.Extended

/-!
# Smoothness of the fluctuation function and its extension

The fluctuation function `S_λ` is `C^∞` in `a`: its family is closed under `a`-differentiation
(`S'_λ = β S_{λ+1/2}`), so every iterated derivative exists and is continuous. We prove
`ContDiff ℝ ∞ (fun a => S_λ a)` for `λ > 0`, that the ladder operator `lowerOp` preserves `C^∞`,
and hence that the extension `Sneg β μ k` (grammar §4 `defn:S_negative`) is `C^∞` for `μ > 0`. This
is the analytic input needed to apply the ladder operators and the Weyl commutator to the extension,
i.e. to lift `lem:extended_ladder`'s raising relation to `λ ≤ 0`.
-/

open Real

namespace Laplace.Grammar

/-- Finite smoothness `ContDiff ℝ n` of the fluctuation function, for every `n : ℕ` and `λ > 0`, by
induction: each derivative is `β · S_{λ+1/2}`, staying in the family. -/
theorem contDiff_nat_fluctuation (β : ℝ) (hβ : 0 < β) :
    ∀ (n : ℕ) (lam : ℝ), 0 < lam → ContDiff ℝ (n : WithTop ℕ∞) (fun a => fluctuation β lam a) := by
  intro n
  induction n with
  | zero =>
    intro lam hlam
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun a =>
      (hasDerivAt_fluctuation β lam hβ hlam a).continuousAt
  | succ n ih =>
    intro lam hlam
    have hd : deriv (fun a => fluctuation β lam a) = fun a => β * fluctuation β (lam + 1 / 2) a :=
      funext fun a => deriv_fluctuation β lam hβ hlam a
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun a => (hasDerivAt_fluctuation β lam hβ hlam a).differentiableAt, ?_, ?_⟩
    · intro h; exact absurd h (by simp)
    · rw [hd]; exact (ih (lam + 1 / 2) (by linarith)).const_smul β

/-- **The fluctuation function is `C^∞`** in `a` (for `λ > 0`). -/
theorem contDiff_fluctuation (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a => fluctuation β lam a) :=
  contDiff_infty.2 fun n => by exact_mod_cast contDiff_nat_fluctuation β hβ n lam hlam

/-- The lowering operator preserves `C^∞`. -/
theorem contDiff_lowerOp (β : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (lowerOp β f) := by
  have hderiv : ContDiff ℝ (⊤ : ℕ∞) (deriv f) := (contDiff_infty_iff_deriv.1 hf).2
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun a => 2 * β ^ (-(1 : ℝ) / 2) * deriv f a) :=
    contDiff_const.mul hderiv
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun a => β ^ ((1 : ℝ) / 2) * (a * f a)) :=
    contDiff_const.mul (contDiff_id.mul hf)
  exact h1.sub h2

/-- **The extension `Sneg` is `C^∞`** (for base order `μ > 0`), by induction using
`contDiff_lowerOp`. -/
theorem contDiff_Sneg (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a => Sneg β μ k a) := by
  induction k with
  | zero => exact contDiff_fluctuation β μ hβ hμ
  | succ k ih =>
    have he : (fun a => Sneg β μ (k + 1) a)
        = fun a => β ^ ((1 : ℝ) / 2) / (2 * (μ - (↑(k + 1)) / 2))
          * lowerOp β (fun a => Sneg β μ k a) a := rfl
    rw [he]
    exact contDiff_const.mul (contDiff_lowerOp β _ ih)

/-- `Sneg` is differentiable (from `C^∞`). -/
theorem differentiable_Sneg (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ) (k : ℕ) :
    Differentiable ℝ (fun a => Sneg β μ k a) :=
  (contDiff_Sneg β μ hβ hμ k).differentiable (by norm_num)

/-- The derivative of `Sneg` is differentiable (from `C^∞`), so `Sneg` is `C²`-enough for the
ladder-operator commutator. -/
theorem differentiable_deriv_Sneg (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ) (k : ℕ) :
    Differentiable ℝ (deriv (fun a => Sneg β μ k a)) :=
  ((contDiff_infty_iff_deriv.1 (contDiff_Sneg β μ hβ hμ k)).2).differentiable
    (by norm_num)

end Laplace.Grammar
