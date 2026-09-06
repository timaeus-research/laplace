/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# Hermite polynomials, the Hermite ODE, and integer-order parabolic cylinder functions

The grammar paper §4 (`lem:qho`, `eq:Dn_hermite`) identifies the integer-order parabolic cylinder
function with a Hermite polynomial times a Gaussian, `D_n(z) = e^{-z²/4} He_n(z)` (in the
probabilist normalisation `He_n`; the paper's physicist form `2^{-n/2} e^{-z²/4} H_n(z/√2)` agrees
via `H_n(x) = 2^{n/2} He_n(x/√2)`).

Mathlib has the (probabilist) Hermite polynomials `Polynomial.hermite` and the recurrence
`hermite (n+1) = X·hermite n - (hermite n)'`, but neither the **derivative-lowering** identity
`He_n' = n·He_{n-1}` nor the **Hermite ODE** `He_n'' - X·He_n' + n·He_n = 0`. We supply both, then
prove that `D_n(z) = e^{-z²/4} He_n(z)` satisfies the **parabolic cylinder equation** at integer order

  `f''(z) + (n + 1/2 - z²/4) f(z) = 0`,

i.e. Weber's equation with `ν = n` — the quantum harmonic oscillator content of `lem:qho`.
-/

open Real Polynomial

namespace Laplace.Grammar

/-- **Derivative-lowering for (probabilist) Hermite polynomials**: `He_{n+1}' = (n+1)·He_n`.
Mathlib has the recurrence but not this; proved by induction from `hermite_succ`. -/
theorem derivative_hermite (n : ℕ) :
    Polynomial.derivative (hermite (n + 1)) = (n + 1) • hermite n := by
  induction n with
  | zero => simp [hermite_zero]
  | succ n ih =>
    have key : Polynomial.derivative (hermite n) = X * hermite n - hermite (n + 1) := by
      rw [hermite_succ n]; ring
    rw [hermite_succ (n + 1), map_sub, Polynomial.derivative_mul, Polynomial.derivative_X,
      one_mul, ih, map_nsmul, key]
    ring

/-- **The Hermite differential equation** (probabilist form): `He_n'' = X·He_n' - n·He_n`,
equivalently `He_n'' - X·He_n' + n·He_n = 0`. -/
theorem hermite_ode (n : ℕ) :
    Polynomial.derivative (Polynomial.derivative (hermite n))
      = X * Polynomial.derivative (hermite n) - n • hermite n := by
  cases n with
  | zero => simp [hermite_zero]
  | succ m =>
    have key : Polynomial.derivative (hermite m) = X * hermite m - hermite (m + 1) := by
      rw [hermite_succ m]; ring
    rw [derivative_hermite m, map_nsmul, key, smul_sub, mul_smul_comm]

/-- Integer-order parabolic cylinder function `D_n(z) = e^{-z²/4} He_n(z)` (grammar §4
`eq:Dn_hermite`, probabilist normalisation), using Mathlib's Hermite polynomials. -/
noncomputable def parCylNat (n : ℕ) (z : ℝ) : ℝ :=
  Real.exp (-z ^ 2 / 4) * aeval z (hermite n)

/-- **The parabolic cylinder equation at integer order** (grammar §4 `lem:qho`):
`D_n` satisfies Weber's equation `f''(z) + (n + 1/2 - z²/4) f(z) = 0` (order `ν = n`). This is the
quantum-harmonic-oscillator identification: the normalisable wavefunctions are `ψ_n ∝ D_n`. -/
theorem parCylNat_weber (n : ℕ) (z : ℝ) :
    deriv (deriv (fun z => parCylNat n z)) z
      + ((n : ℝ) + 1 / 2 - z ^ 2 / 4) * parCylNat n z = 0 := by
  simp only [parCylNat]
  have hodeEval : ∀ x : ℝ,
      aeval x (Polynomial.derivative (Polynomial.derivative (hermite n)))
        = x * aeval x (Polynomial.derivative (hermite n)) - (n : ℝ) * aeval x (hermite n) := by
    intro x; rw [hermite_ode]; simp [nsmul_eq_mul]
  have hE : ∀ w : ℝ, HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 / 4))
      (-w / 2 * Real.exp (-w ^ 2 / 4)) w := by
    intro w
    have hq : HasDerivAt (fun x : ℝ => -x ^ 2 / 4) (-w / 2) w := by
      have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * w) w := by simpa using hasDerivAt_pow 2 w
      rw [show (-w / 2 : ℝ) = -(2 * w) / 4 by ring]; exact h2.neg.div_const (4 : ℝ)
    simpa [mul_comm] using hq.exp
  have hHalf : ∀ w : ℝ, HasDerivAt (fun x : ℝ => x / 2) (1 / 2 : ℝ) w := by
    intro w; simpa using (hasDerivAt_id w).div_const (2 : ℝ)
  have hP0 : ∀ w : ℝ, HasDerivAt (fun x : ℝ => aeval x (hermite n))
      (aeval w (Polynomial.derivative (hermite n))) w :=
    fun w => (hermite n).hasDerivAt_aeval w
  have hP1 : ∀ w : ℝ, HasDerivAt (fun x : ℝ => aeval x (Polynomial.derivative (hermite n)))
      (aeval w (Polynomial.derivative (Polynomial.derivative (hermite n)))) w :=
    fun w => (Polynomial.derivative (hermite n)).hasDerivAt_aeval w
  -- first derivative
  have hf1 : ∀ w : ℝ, HasDerivAt (fun z => Real.exp (-z ^ 2 / 4) * aeval z (hermite n))
      (Real.exp (-w ^ 2 / 4) * (aeval w (Polynomial.derivative (hermite n))
        - w / 2 * aeval w (hermite n))) w := by
    intro w; exact ((hE w).mul (hP0 w)).congr_deriv (by ring)
  have hdf : deriv (fun z => Real.exp (-z ^ 2 / 4) * aeval z (hermite n))
      = fun w => Real.exp (-w ^ 2 / 4) * (aeval w (Polynomial.derivative (hermite n))
        - w / 2 * aeval w (hermite n)) :=
    funext fun w => (hf1 w).deriv
  -- bracket derivative
  have hB : ∀ w : ℝ, HasDerivAt (fun x : ℝ => aeval x (Polynomial.derivative (hermite n))
        - x / 2 * aeval x (hermite n))
      (aeval w (Polynomial.derivative (Polynomial.derivative (hermite n)))
        - (1 / 2 * aeval w (hermite n)
          + w / 2 * aeval w (Polynomial.derivative (hermite n)))) w := by
    intro w
    exact ((hP1 w).sub ((hHalf w).mul (hP0 w))).congr_deriv (by ring)
  -- second derivative
  have hf2 : HasDerivAt (fun w => Real.exp (-w ^ 2 / 4)
        * (aeval w (Polynomial.derivative (hermite n)) - w / 2 * aeval w (hermite n)))
      (Real.exp (-z ^ 2 / 4)
        * ((aeval z (Polynomial.derivative (Polynomial.derivative (hermite n)))
            - (1 / 2 * aeval z (hermite n)
              + z / 2 * aeval z (Polynomial.derivative (hermite n))))
          - z / 2 * (aeval z (Polynomial.derivative (hermite n))
            - z / 2 * aeval z (hermite n)))) z :=
    ((hE z).mul (hB z)).congr_deriv (by ring)
  have hddf : deriv (deriv (fun z => Real.exp (-z ^ 2 / 4) * aeval z (hermite n))) z
      = Real.exp (-z ^ 2 / 4)
        * ((aeval z (Polynomial.derivative (Polynomial.derivative (hermite n)))
            - (1 / 2 * aeval z (hermite n)
              + z / 2 * aeval z (Polynomial.derivative (hermite n))))
          - z / 2 * (aeval z (Polynomial.derivative (hermite n))
            - z / 2 * aeval z (hermite n))) := by
    rw [hdf]; exact hf2.deriv
  rw [hddf, hodeEval]
  ring

end Laplace.Grammar
