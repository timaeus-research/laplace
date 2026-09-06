/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.Fluctuation

/-!
# The oscillator ladder algebra (grammar §4 `lem:oscillator_algebra`)

The fluctuation function carries a quantum-harmonic-oscillator ladder: with the raising and lowering
operators

  `b† = β^{-1/2} ∂_a`,   `b = 2β^{-1/2} ∂_a - β^{1/2} a`

acting on functions of `a`, one has the **canonical commutator** `[b, b†] = 1` (the Weyl relation,
from `[a, ∂_a] = -1`), and the ladder actions

  `b† S_λ = β^{1/2} S_{λ+1/2}`,   `b S_λ = (2λ-1) β^{-1/2} S_{λ-1/2}`.

We formalise `b`, `b†` as operators on `ℝ → ℝ`, prove `[b, b†] f = f` for any `C²` function `f`, and
identify the ladder actions on the fluctuation function (the raising action is the derivative
ladder, the lowering action is `fluctuation_lowering`).
-/

open Real

namespace Laplace.Grammar

/-- The raising operator `b† = β^{-1/2} ∂_a` on functions of `a`. -/
noncomputable def raiseOp (β : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun a => β ^ (-(1 : ℝ) / 2) * deriv f a

/-- The lowering operator `b = 2β^{-1/2} ∂_a - β^{1/2} a` on functions of `a`. -/
noncomputable def lowerOp (β : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun a => 2 * β ^ (-(1 : ℝ) / 2) * deriv f a - β ^ ((1 : ℝ) / 2) * (a * f a)

/-- **The canonical commutator** (grammar §4 `lem:oscillator_algebra`): `[b, b†] = 1`, i.e.
`b(b† f) - b†(b f) = f` for every twice-differentiable `f`. The `2β^{-1}f''` and `a f'` terms
cancel;
what survives is `β^{-1/2}β^{1/2} f = f`. -/
theorem ladder_commutator (β : ℝ) (hβ : 0 < β) (f : ℝ → ℝ)
    (hf1 : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f)) (a : ℝ) :
    lowerOp β (raiseOp β f) a - raiseOp β (lowerOp β f) a = f a := by
  have hr2 : β ^ ((1 : ℝ) / 2) * β ^ (-(1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hβ, show (1 : ℝ) / 2 + -(1 : ℝ) / 2 = 0 by norm_num, Real.rpow_zero]
  have hd_raise : deriv (raiseOp β f) a = β ^ (-(1 : ℝ) / 2) * deriv (deriv f) a := by
    rw [show raiseOp β f = fun x => β ^ (-(1 : ℝ) / 2) * deriv f x from rfl]
    exact (((hf2 a).hasDerivAt).const_mul (β ^ (-(1 : ℝ) / 2))).deriv
  have hd_lower : deriv (lowerOp β f) a
      = 2 * β ^ (-(1 : ℝ) / 2) * deriv (deriv f) a
        - β ^ ((1 : ℝ) / 2) * (1 * f a + a * deriv f a) := by
    have h1 : HasDerivAt (fun x => 2 * β ^ (-(1 : ℝ) / 2) * deriv f x)
        (2 * β ^ (-(1 : ℝ) / 2) * deriv (deriv f) a) a := ((hf2 a).hasDerivAt).const_mul _
    have h2 : HasDerivAt (fun x => β ^ ((1 : ℝ) / 2) * (x * f x))
        (β ^ ((1 : ℝ) / 2) * (1 * f a + a * deriv f a)) a :=
      ((hasDerivAt_id a).mul ((hf1 a).hasDerivAt)).const_mul (β ^ ((1 : ℝ) / 2))
    rw [show lowerOp β f
        = fun x => 2 * β ^ (-(1 : ℝ) / 2) * deriv f x - β ^ ((1 : ℝ) / 2) * (x * f x) from rfl]
    exact (h1.sub h2).deriv
  have hlower_outer : lowerOp β (raiseOp β f) a
      = 2 * β ^ (-(1 : ℝ) / 2) * deriv (raiseOp β f) a
        - β ^ ((1 : ℝ) / 2) * (a * raiseOp β f a) := rfl
  have hraise_outer : raiseOp β (lowerOp β f) a = β ^ (-(1 : ℝ) / 2) * deriv (lowerOp β f) a := rfl
  have hraise_val : raiseOp β f a = β ^ (-(1 : ℝ) / 2) * deriv f a := rfl
  rw [hlower_outer, hraise_outer, hd_raise, hd_lower, hraise_val]
  linear_combination (f a) * hr2

/-- Power identity `β^{-1/2}·β = β^{1/2}` used by the ladder actions. -/
private theorem rpow_neg_half_mul_self (β : ℝ) (hβ : 0 < β) :
    β ^ (-(1 : ℝ) / 2) * β = β ^ ((1 : ℝ) / 2) := by
  nth_rewrite 2 [show (β : ℝ) = β ^ (1 : ℝ) from (Real.rpow_one β).symm]
  rw [← Real.rpow_add hβ, show -(1 : ℝ) / 2 + 1 = (1 : ℝ) / 2 by norm_num]

/-- **Raising action** (grammar §4 `lem:oscillator_algebra`): `b† S_λ = β^{1/2} S_{λ+1/2}` — the
derivative ladder `S'_λ = β S_{λ+1/2}` recast through `b† = β^{-1/2}∂_a`. -/
theorem raiseOp_fluctuation (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    raiseOp β (fun a => fluctuation β lam a) a
      = β ^ ((1 : ℝ) / 2) * fluctuation β (lam + 1 / 2) a := by
  rw [show raiseOp β (fun a => fluctuation β lam a) a
      = β ^ (-(1 : ℝ) / 2) * deriv (fun a => fluctuation β lam a) a from rfl,
    deriv_fluctuation β lam hβ hlam a,
    show β ^ (-(1 : ℝ) / 2) * (β * fluctuation β (lam + 1 / 2) a)
      = (β ^ (-(1 : ℝ) / 2) * β) * fluctuation β (lam + 1 / 2) a by ring,
    rpow_neg_half_mul_self β hβ]

/-- **Lowering action** (grammar §4 `lem:oscillator_algebra`): `b S_λ = (2λ-1) β^{-1/2} S_{λ-1/2}`
for `λ > 1/2` — the lowering identity `2S'_λ - βa S_λ = (2λ-1)S_{λ-1/2}` recast through
`b = 2β^{-1/2}∂_a - β^{1/2}a`. -/
theorem lowerOp_fluctuation (β lam : ℝ) (hβ : 0 < β) (hlam : 1 / 2 < lam) (a : ℝ) :
    lowerOp β (fun a => fluctuation β lam a) a
      = (2 * lam - 1) * β ^ (-(1 : ℝ) / 2) * fluctuation β (lam - 1 / 2) a := by
  have hlow := fluctuation_lowering β lam hβ hlam a
  rw [show lowerOp β (fun a => fluctuation β lam a) a
      = β ^ (-(1 : ℝ) / 2) * (2 * deriv (fun a => fluctuation β lam a) a
        - β * a * fluctuation β lam a) by
    rw [show lowerOp β (fun a => fluctuation β lam a) a
        = 2 * β ^ (-(1 : ℝ) / 2) * deriv (fun a => fluctuation β lam a) a
          - β ^ ((1 : ℝ) / 2) * (a * fluctuation β lam a) from rfl,
      ← rpow_neg_half_mul_self β hβ]
    ring, hlow]
  ring

end Laplace.Grammar
