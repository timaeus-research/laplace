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

/-- **Fluctuation as a parabolic-cylinder kernel integral.** The change of variables
`t = u²/(2β)` (scale by `2β`, then square) turns `S_λ` into
`2^{1-λ} β^{-λ} ∫₀^∞ u^{2λ-1} e^{-u²/2 + a√(β/2)·u} du`, whose integrand is the `D_{-2λ}`
kernel with `x = -a√(β/2)`. This isolates all change-of-variables work; `Γ` never enters. -/
theorem fluctuation_eq_kernel (β lam a : ℝ) (hβ : 0 < β) :
    fluctuation β lam a
      = (2 ^ (1 - lam) * β ^ (-lam))
        * ∫ u in Set.Ioi (0 : ℝ),
            u ^ (2 * lam - 1) * Real.exp (-u ^ 2 / 2 + a * Real.sqrt (β / 2) * u) := by
  have hβ0 : β ≠ 0 := hβ.ne'
  have h2β : (0 : ℝ) < 2 * β := by positivity
  have h2β0 : (2 * β : ℝ) ≠ 0 := h2β.ne'
  have hs2β : Real.sqrt (2 * β) ≠ 0 := (by positivity : (0 : ℝ) < Real.sqrt (2 * β)).ne'
  have hsqrt2 : Real.sqrt (2 * β) * Real.sqrt (β / 2) = β := by
    rw [← Real.sqrt_mul h2β.le, show 2 * β * (β / 2) = β ^ 2 by ring, Real.sqrt_sq hβ.le]
  have hbdiv : β / Real.sqrt (2 * β) = Real.sqrt (β / 2) := by
    rw [div_eq_iff hs2β, mul_comm]; exact hsqrt2.symm
  have hβp : β ^ (1 - lam) = β ^ (-lam) * β := by
    rw [show (1 : ℝ) - lam = -lam + 1 by ring, Real.rpow_add hβ, Real.rpow_one]
  have hconstant : (2 * β)⁻¹ * (2 * (2 * β) ^ (-(lam - 1))) = 2 ^ (1 - lam) * β ^ (-lam) := by
    rw [show -(lam - 1) = 1 - lam by ring, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hβ.le, hβp]
    field_simp
  set H : ℝ → ℝ := fun r =>
    (r / (2 * β)) ^ (lam - 1) *
      Real.exp (-β * (r / (2 * β)) + β * a * Real.sqrt (r / (2 * β))) with hHdef
  have step1 : fluctuation β lam a = ∫ t in Set.Ioi (0 : ℝ), H (2 * β * t) := by
    rw [fluctuation]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [hHdef]
    rw [show 2 * β * t / (2 * β) = t by field_simp]
  have step2 : (∫ t in Set.Ioi (0 : ℝ), H (2 * β * t))
      = (2 * β)⁻¹ • ∫ r in Set.Ioi (0 : ℝ), H r := by
    rw [integral_comp_mul_left_Ioi H 0 h2β, mul_zero]
  have step3 : (∫ r in Set.Ioi (0 : ℝ), H r)
      = ∫ x in Set.Ioi (0 : ℝ), (2 * x ^ ((2 : ℝ) - 1)) • H (x ^ (2 : ℝ)) :=
    (integral_comp_rpow_Ioi_of_pos (by norm_num : (0 : ℝ) < 2)).symm
  have step4 : (∫ x in Set.Ioi (0 : ℝ), (2 * x ^ ((2 : ℝ) - 1)) • H (x ^ (2 : ℝ)))
      = ∫ x in Set.Ioi (0 : ℝ), (2 * (2 * β) ^ (-(lam - 1)))
          * (x ^ (2 * lam - 1) * Real.exp (-x ^ 2 / 2 + a * Real.sqrt (β / 2) * x)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hpow : (x ^ 2 / (2 * β)) ^ (lam - 1) = (2 * β) ^ (-(lam - 1)) * x ^ (2 * lam - 2) := by
      rw [Real.div_rpow (by positivity) (by positivity),
        show (x ^ 2 : ℝ) ^ (lam - 1) = x ^ (2 * lam - 2) by
          rw [show (x : ℝ) ^ 2 = x ^ (2 : ℝ) by
                rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast],
            ← Real.rpow_mul hx0.le, show (2 : ℝ) * (lam - 1) = 2 * lam - 2 by ring],
        Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * β), div_eq_mul_inv]
      ring
    have hexp : -β * (x ^ 2 / (2 * β)) + β * a * Real.sqrt (x ^ 2 / (2 * β))
        = -x ^ 2 / 2 + a * Real.sqrt (β / 2) * x := by
      rw [Real.sqrt_div (sq_nonneg x), Real.sqrt_sq hx0.le, ← hbdiv]
      field_simp
    have hxx : x * x ^ (2 * lam - 2) = x ^ (2 * lam - 1) := by
      rw [show (2 : ℝ) * lam - 1 = 1 + (2 * lam - 2) by ring, Real.rpow_add hx0, Real.rpow_one]
    simp only [smul_eq_mul, hHdef]
    rw [show ((2 : ℝ) - 1) = 1 by norm_num, Real.rpow_one,
      show x ^ (2 : ℝ) = x ^ 2 by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast],
      hpow, hexp, ← hxx]
    ring
  rw [step1, step2, step3, step4, integral_const_mul, smul_eq_mul, ← mul_assoc, hconstant]

/-- **The fluctuation closed form** (grammar §4 `cor:fluctuation_closed_form`):
`S_λ(a) = 2^{1-λ} β^{-λ} Γ(2λ) e^{βa²/8} D_{-2λ}(-a√(β/2))`. Combines
`fluctuation_eq_kernel` with the definition of `parCylNeg`; the `Γ` and Gaussian prefactors
cancel to leave the kernel integral. -/
theorem fluctuation_closed_form (β lam a : ℝ) (hβ : 0 < β) (hlam : 0 < lam) :
    fluctuation β lam a
      = 2 ^ (1 - lam) * β ^ (-lam) * Real.Gamma (2 * lam) * Real.exp (β * a ^ 2 / 8)
        * parCylNeg (2 * lam) (-a * Real.sqrt (β / 2)) := by
  rw [fluctuation_eq_kernel β lam a hβ]
  have hInt : (∫ u in Set.Ioi (0 : ℝ),
        u ^ (2 * lam - 1) * Real.exp (-u ^ 2 / 2 - (-a * Real.sqrt (β / 2)) * u))
      = ∫ u in Set.Ioi (0 : ℝ),
        u ^ (2 * lam - 1) * Real.exp (-u ^ 2 / 2 + a * Real.sqrt (β / 2) * u) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    beta_reduce
    rw [show -u ^ 2 / 2 - (-a * Real.sqrt (β / 2)) * u
        = -u ^ 2 / 2 + a * Real.sqrt (β / 2) * u by ring]
  unfold parCylNeg
  rw [hInt]
  set I := ∫ u in Set.Ioi (0 : ℝ),
    u ^ (2 * lam - 1) * Real.exp (-u ^ 2 / 2 + a * Real.sqrt (β / 2) * u) with hIdef
  have hΓ : Real.Gamma (2 * lam) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  have hEne : Real.exp (β * a ^ 2 / 8) ≠ 0 := Real.exp_ne_zero _
  have hE2 : Real.exp (-(-a * Real.sqrt (β / 2)) ^ 2 / 4) = (Real.exp (β * a ^ 2 / 8))⁻¹ := by
    rw [← Real.exp_neg, show -(-a * Real.sqrt (β / 2)) ^ 2 / 4 = -(β * a ^ 2 / 8) by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ β / 2)]; ring]
  rw [hE2]
  field_simp

end Laplace.Grammar
