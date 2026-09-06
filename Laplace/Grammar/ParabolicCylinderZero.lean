/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.ParabolicCylinder
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The value of `D_{-ν}` at the origin

The grammar paper §4 records (in the proof of `cor:fluctuation_closed_form`) the value

  `D_{-ν}(0) = √π / (2^{ν/2} Γ((ν+1)/2))`.

The `ParabolicCylinder` module already gives `D_{-ν}(0) = 2^{ν/2-1} Γ(ν/2)/Γ(ν)` from the
`Γ`-integral; here we reconcile that with the paper's form via **Legendre's duplication formula**
`Γ(s) Γ(s+½) = Γ(2s) 2^{1-2s} √π` (Mathlib's `Real.Gamma_mul_Gamma_add_half`).
-/

open Real

namespace Laplace.Grammar

/-- The paper's form of the origin value (grammar §4, proof of `cor:fluctuation_closed_form`):
`D_{-ν}(0) = √π / (2^{ν/2} Γ((ν+1)/2))`, obtained from `parCylNeg_zero` by Legendre duplication. -/
theorem parCylNeg_zero_paper (ν : ℝ) (hν : 0 < ν) :
    parCylNeg ν 0 = Real.sqrt π / (2 ^ (ν / 2) * Real.Gamma ((ν + 1) / 2)) := by
  rw [parCylNeg_zero ν hν]
  have hleg := Real.Gamma_mul_Gamma_add_half (ν / 2)
  rw [show (2 : ℝ) * (ν / 2) = ν by ring, show ν / 2 + 1 / 2 = (ν + 1) / 2 by ring] at hleg
  have hΓν : (0 : ℝ) < Real.Gamma ν := Real.Gamma_pos_of_pos hν
  have hΓh : (0 : ℝ) < Real.Gamma ((ν + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  rw [div_eq_div_iff hΓν.ne' (by positivity)]
  have h1 : (2 : ℝ) ^ (ν / 2 - 1) * 2 ^ (ν / 2) = 2 ^ (ν - 1) := by
    rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  have h2 : (2 : ℝ) ^ (ν - 1) * 2 ^ (1 - ν) = 1 := by
    rw [← Real.rpow_add (by norm_num), show ν - 1 + (1 - ν) = 0 by ring, Real.rpow_zero]
  rw [show 2 ^ (ν / 2 - 1) * Real.Gamma (ν / 2) * (2 ^ (ν / 2) * Real.Gamma ((ν + 1) / 2))
        = (2 ^ (ν / 2 - 1) * 2 ^ (ν / 2)) * (Real.Gamma (ν / 2) * Real.Gamma ((ν + 1) / 2)) by ring,
    hleg, h1,
    show 2 ^ (ν - 1) * (Real.Gamma ν * 2 ^ (1 - ν) * Real.sqrt π)
        = (2 ^ (ν - 1) * 2 ^ (1 - ν)) * (Real.Gamma ν * Real.sqrt π) by ring, h2, one_mul]
  ring

end Laplace.Grammar
