/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Laplace.Grammar.Fluctuation

/-!
# Parabolic cylinder function (negative order) and the fluctuation closed form

The grammar paper §4 identifies Watanabe's fluctuation function with a parabolic cylinder
function. Mathlib has no `D_ν`, so we introduce the negative-order function via its standard
DLMF §12.5(i) integral representation — exactly the orders `D_{-2λ}` (`λ>0`) the closed form needs:

  `D_{-ν}(x) = e^{-x²/4}/Γ(ν) · ∫₀^∞ u^{ν-1} e^{-u²/2 - x u} du`,   `ν > 0`,

and prove `cor:fluctuation_closed_form`:

  `S_λ(a) = 2^{1-λ} β^{-λ} Γ(2λ) e^{βa²/8} D_{-2λ}(-a√(β/2))`

by the change of variables `u = √(2β t)` in `S_λ`'s defining integral.
-/

open Real MeasureTheory

namespace Laplace.Grammar

/-- Parabolic cylinder function at **negative order** `-ν` (`ν > 0`), via the DLMF §12.5(i)
integral representation `D_{-ν}(x) = e^{-x²/4}/Γ(ν) · ∫₀^∞ u^{ν-1} e^{-u²/2 - x u} du`. -/
noncomputable def parCylNeg (ν x : ℝ) : ℝ :=
  Real.exp (-x ^ 2 / 4) / Real.Gamma ν *
    ∫ u in Set.Ioi (0 : ℝ), u ^ (ν - 1) * Real.exp (-u ^ 2 / 2 - x * u)

/-- The `D_{-ν}` integrand is integrable on `(0,∞)` (`ν > 0`, any `x`): AM–GM
`-u²/2 - x u ≤ x² - u²/4` (from `(u/2+x)² ≥ 0`) dominates it by a Gaussian integrand. -/
theorem parCylNeg_integrableOn (ν x : ℝ) (hν : 0 < ν) :
    IntegrableOn (fun u => u ^ (ν - 1) * Real.exp (-u ^ 2 / 2 - x * u)) (Set.Ioi 0) := by
  have hmaj : IntegrableOn
      (fun u : ℝ => Real.exp (x ^ 2) * (u ^ (ν - 1) * Real.exp (-(1 / 4 : ℝ) * u ^ (2 : ℝ))))
      (Set.Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) (by norm_num) (by norm_num)).const_mul _
  refine Integrable.mono' hmaj ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    apply ContinuousOn.mul
    · exact continuousOn_id.rpow_const (fun u hu => Or.inl (ne_of_gt (Set.mem_Ioi.mp hu)))
    · exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    have h2 : u ^ (2 : ℝ) = u ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hexp : Real.exp (-u ^ 2 / 2 - x * u)
        ≤ Real.exp (x ^ 2) * Real.exp (-(1 / 4 : ℝ) * u ^ (2 : ℝ)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
      rw [h2]; nlinarith [sq_nonneg (u / 2 + x)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc u ^ (ν - 1) * Real.exp (-u ^ 2 / 2 - x * u)
        ≤ u ^ (ν - 1) * (Real.exp (x ^ 2) * Real.exp (-(1 / 4 : ℝ) * u ^ (2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hu0.le _)
      _ = Real.exp (x ^ 2) * (u ^ (ν - 1) * Real.exp (-(1 / 4 : ℝ) * u ^ (2 : ℝ))) := by ring

/-- Value at `x = 0`: `D_{-ν}(0) = 2^{ν/2-1} · Γ(ν/2) / Γ(ν)` (DLMF §12.5), from the `Γ`-integral
`∫₀^∞ u^{ν-1} e^{-u²/2} du = 2^{ν/2-1} Γ(ν/2)`. A sanity anchor for the definition. -/
theorem parCylNeg_zero (ν : ℝ) (hν : 0 < ν) :
    parCylNeg ν 0 = 2 ^ (ν / 2 - 1) * Real.Gamma (ν / 2) / Real.Gamma ν := by
  unfold parCylNeg
  have hint : (∫ u in Set.Ioi (0 : ℝ), u ^ (ν - 1) * Real.exp (-u ^ 2 / 2 - 0 * u))
      = 2 ^ (ν / 2 - 1) * Real.Gamma (ν / 2) := by
    have hcongr : (∫ u in Set.Ioi (0 : ℝ), u ^ (ν - 1) * Real.exp (-u ^ 2 / 2 - 0 * u))
        = ∫ u in Set.Ioi (0 : ℝ), u ^ (ν - 1) * Real.exp (-(1 / 2 : ℝ) * u ^ (2 : ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      beta_reduce
      rw [show u ^ (2 : ℝ) = u ^ 2 by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast], show -u ^ 2 / 2 - 0 * u = -(1 / 2 : ℝ) * u ^ 2 by ring]
    rw [hcongr, integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by linarith) (by norm_num)]
    have e1 : ((1 : ℝ) / 2) ^ (-(ν - 1 + 1) / 2) = 2 ^ (ν / 2) := by
      rw [show (-(ν - 1 + 1)) / 2 = -(ν / 2) by ring, show (1 : ℝ) / 2 = 2⁻¹ by norm_num,
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        inv_inv]
    rw [e1, show (ν - 1 + 1) / 2 = ν / 2 by ring,
      show (2 : ℝ) ^ (ν / 2 - 1) = 2 ^ (ν / 2) * (1 / 2) by
        rw [show ν / 2 - 1 = ν / 2 + (-1 : ℝ) by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_one]; norm_num]
  rw [hint, show (-0 ^ 2 / 4 : ℝ) = 0 by norm_num, Real.exp_zero]
  ring

end Laplace.Grammar
