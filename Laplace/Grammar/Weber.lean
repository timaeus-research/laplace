/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.Fluctuation

/-!
# Weber's equation for the fluctuation function

The grammar paper §4 (`prop:fluctuation_weber`) shows that the substitution
`S_λ(a) = e^{βa²/8} f(a√(β/2))` turns the fluctuation ODE (iii) into **Weber's equation**

  `f''(z) + (1/2 - 2λ - z²/4) f(z) = 0`,

the standard form of the parabolic cylinder equation with parameter `ν = -2λ`. In particular
the Weber order depends only on the RLCT `λ`, not on the inverse temperature `β`.

We formalise this for `f(z) = e^{-z²/4} S_λ(z√(2/β))` (the substitution solved for `f`), building
only on the derivative ladder and ODE of `Fluctuation.lean`; no parabolic-cylinder machinery is
needed.
-/

open Real

namespace Laplace.Grammar

/-- The Weber substitution function `f(z) = e^{-z²/4} S_λ(z√(2/β))`, so that
`S_λ(a) = e^{βa²/8} f(a√(β/2))`. -/
noncomputable def weberSub (β lam z : ℝ) : ℝ :=
  Real.exp (-z ^ 2 / 4) * fluctuation β lam (z * Real.sqrt (2 / β))

/-- **Weber's equation for the fluctuation function** (grammar §4 `prop:fluctuation_weber`):
the substitution `f(z) = e^{-z²/4} S_λ(z√(2/β))` satisfies
`f''(z) + (1/2 - 2λ - z²/4) f(z) = 0`. -/
theorem fluctuation_weber (β lam z : ℝ) (hβ : 0 < β) (hlam : 0 < lam) :
    deriv (deriv (fun z => weberSub β lam z)) z
      + (1 / 2 - 2 * lam - z ^ 2 / 4) * weberSub β lam z = 0 := by
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  simp only [weberSub]
  set k : ℝ := Real.sqrt (2 / β) with hk
  have hk_sq : k ^ 2 = 2 / β := by rw [hk]; exact Real.sq_sqrt (by positivity)
  have hkβ : β * k ^ 2 = 2 := by rw [hk_sq]; field_simp
  -- derivative of the linear argument `w ↦ w * k`
  have hL : ∀ w : ℝ, HasDerivAt (fun x : ℝ => x * k) k w := by
    intro w; simpa using (hasDerivAt_id w).mul_const k
  -- Gaussian derivative
  have hE : ∀ w : ℝ, HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 / 4))
      (-w / 2 * Real.exp (-w ^ 2 / 4)) w := by
    intro w
    have hq : HasDerivAt (fun x : ℝ => -x ^ 2 / 4) (-w / 2) w := by
      have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * w) w := by simpa using hasDerivAt_pow 2 w
      rw [show (-w / 2 : ℝ) = -(2 * w) / 4 by ring]; exact h2.neg.div_const (4 : ℝ)
    simpa [mul_comm] using hq.exp
  have hNegHalf : ∀ w : ℝ, HasDerivAt (fun x : ℝ => -x / 2) (-1 / 2 : ℝ) w := by
    intro w; simpa using (hasDerivAt_id w).neg.div_const (2 : ℝ)
  -- chain rule for the two fluctuation compositions (∘ form on hT avoids comp's HOU splitting `β*·`)
  have hS : ∀ w : ℝ, HasDerivAt (fun x : ℝ => fluctuation β lam (x * k))
      (β * fluctuation β (lam + 1 / 2) (w * k) * k) w := by
    intro w
    exact (hasDerivAt_fluctuation β lam hβ hlam (w * k)).comp w (hL w)
  have hT : ∀ w : ℝ, HasDerivAt ((fun a => β * fluctuation β (lam + 1 / 2) a) ∘ (fun x : ℝ => x * k))
      (β ^ 2 * fluctuation β (lam + 1) (w * k) * k) w := by
    intro w
    exact (hasDerivAt_deriv_fluctuation β lam hβ hlam (w * k)).comp w (hL w)
  -- first derivative of `G = fun z => e^{-z²/4} S_λ(z k)`
  have hf1 : ∀ w : ℝ, HasDerivAt (fun z => Real.exp (-z ^ 2 / 4) * fluctuation β lam (z * k))
      (Real.exp (-w ^ 2 / 4) * ((-w / 2) * fluctuation β lam (w * k)
        + k * (β * fluctuation β (lam + 1 / 2) (w * k)))) w := by
    intro w; exact ((hE w).mul (hS w)).congr_deriv (by ring)
  have hdf : deriv (fun z => Real.exp (-z ^ 2 / 4) * fluctuation β lam (z * k))
      = fun w => Real.exp (-w ^ 2 / 4) * ((-w / 2) * fluctuation β lam (w * k)
        + k * (β * fluctuation β (lam + 1 / 2) (w * k))) :=
    funext fun w => (hf1 w).deriv
  -- derivative of the bracket
  have hB : ∀ w : ℝ, HasDerivAt (fun x : ℝ => (-x / 2) * fluctuation β lam (x * k)
        + k * (β * fluctuation β (lam + 1 / 2) (x * k)))
      ((-1 / 2) * fluctuation β lam (w * k)
        + (-w / 2) * (β * fluctuation β (lam + 1 / 2) (w * k) * k)
        + k * (β ^ 2 * fluctuation β (lam + 1) (w * k) * k)) w := by
    intro w
    exact (((hNegHalf w).mul (hS w)).add ((hT w).const_mul k)).congr_deriv (by ring)
  -- second derivative
  have hf2 : HasDerivAt (fun w => Real.exp (-w ^ 2 / 4) * ((-w / 2) * fluctuation β lam (w * k)
        + k * (β * fluctuation β (lam + 1 / 2) (w * k))))
      (Real.exp (-z ^ 2 / 4) * ((z ^ 2 / 4 - 1 / 2) * fluctuation β lam (z * k)
        - z * k * (β * fluctuation β (lam + 1 / 2) (z * k))
        + k ^ 2 * (β ^ 2 * fluctuation β (lam + 1) (z * k)))) z :=
    ((hE z).mul (hB z)).congr_deriv (by ring)
  have hddf : deriv (deriv (fun z => Real.exp (-z ^ 2 / 4) * fluctuation β lam (z * k))) z
      = Real.exp (-z ^ 2 / 4) * ((z ^ 2 / 4 - 1 / 2) * fluctuation β lam (z * k)
        - z * k * (β * fluctuation β (lam + 1 / 2) (z * k))
        + k ^ 2 * (β ^ 2 * fluctuation β (lam + 1) (z * k))) := by
    rw [hdf]; exact hf2.deriv
  rw [hddf]
  have hode : β ^ 2 * fluctuation β (lam + 1) (z * k)
      = (z * k * β / 2) * (β * fluctuation β (lam + 1 / 2) (z * k))
        + lam * β * fluctuation β lam (z * k) := fluctuation_ode β lam hβ hlam (z * k)
  calc Real.exp (-z ^ 2 / 4) * ((z ^ 2 / 4 - 1 / 2) * fluctuation β lam (z * k)
        - z * k * (β * fluctuation β (lam + 1 / 2) (z * k))
        + k ^ 2 * (β ^ 2 * fluctuation β (lam + 1) (z * k)))
      + (1 / 2 - 2 * lam - z ^ 2 / 4) * (Real.exp (-z ^ 2 / 4) * fluctuation β lam (z * k))
      = Real.exp (-z ^ 2 / 4) * ((β * k ^ 2 - 2)
          * (lam * fluctuation β lam (z * k)
            + (z * k / 2) * (β * fluctuation β (lam + 1 / 2) (z * k)))) := by
        rw [hode]; ring
    _ = 0 := by rw [hkβ]; ring

end Laplace.Grammar
