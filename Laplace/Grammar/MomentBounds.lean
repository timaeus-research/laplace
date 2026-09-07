/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LeadingCoeffVariants

/-!
# Uniform bounds for the transfer moments (grammar §4.2)

The constants of the density-transfer theorem (unit 83) — the weighted remainder moment `M_H`
and the tail moments `T_i` — are bounded explicitly in terms of the polynomial-exponential
bound `|c(s)| ≤ e^{βsa'}(A + Bs + Ds²)` and the log-weighted kernel moments
`Λ_{γ,j}(a') = ∫₀^∞ s^γ (1 + |log s|)^j e^{-βs² + βa's} ds` (`tailMoment_le_of_bound`,
`envMoment_le_of_bound`). Since `Λ_{γ,j}` is monotone in `a'`, these bounds are uniform over face
parameters `|a| ≤ L`, which is what the second-order theorem with noncritical coordinates needs.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- The log-weighted kernel moment `Λ_{γ,j}(a) = ∫₀^∞ s^γ (1+|log s|)^j e^{-βs²+βas} ds`. -/
noncomputable def logKernelMoment (β a γ : ℝ) (j : ℕ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), (1 + |Real.log s|) ^ j * (s ^ γ * quadKernel β a s)

theorem logKernelMoment_nonneg (β a γ : ℝ) (j : ℕ) : 0 ≤ logKernelMoment β a γ j :=
  setIntegral_nonneg measurableSet_Ioi fun s hs =>
    mul_nonneg (pow_nonneg (by positivity) _)
      (mul_nonneg (Real.rpow_nonneg (le_of_lt hs) _) (quadKernel_pos _ _ _).le)

/-- `Λ_{γ,j}` is monotone in the fluctuation parameter. -/
theorem logKernelMoment_mono (β γ : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (j : ℕ) {a a' : ℝ}
    (haa : a ≤ a') : logKernelMoment β a γ j ≤ logKernelMoment β a' γ j := by
  unfold logKernelMoment
  refine setIntegral_mono_on (logPowShift_weightedKernel_integrableOn β a γ 1 hβ hγ j)
    (logPowShift_weightedKernel_integrableOn β a' γ 1 hβ hγ j) measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  have hq : quadKernel β a s ≤ quadKernel β a' s := by
    unfold quadKernel
    exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg hβ.le hs0.le])
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hs0.le _))
    (pow_nonneg (by positivity) _)

/-- **Tail moment bound**: `|c s| ≤ e^{βsa'}(A + Bs + Ds²)` gives
`T ≤ A Λ_{a-1,j} + B Λ_{a,j} + D Λ_{a+1,j}` (all at `a'`). -/
theorem tailMoment_le_of_bound (β a' a A B D : ℝ) (hβ : 0 < β) (ha : -1 < a - 1)
    (j : ℕ) (c : ℝ → ℝ) (hc : Measurable c)
    (hbound : ∀ s, 0 < s → |c s| ≤ Real.exp (β * s * a') * (A + B * s + D * s ^ 2)) :
    tailMoment β a j c ≤ A * logKernelMoment β a' (a - 1) j + B * logKernelMoment β a' a j
      + D * logKernelMoment β a' (a + 1) j := by
  have h0 := logPowShift_weightedKernel_integrableOn β a' (a - 1) 1 hβ ha j
  have h1 := logPowShift_weightedKernel_integrableOn β a' a 1 hβ (by linarith) j
  have h2 := logPowShift_weightedKernel_integrableOn β a' (a + 1) 1 hβ (by linarith) j
  have h01 : IntegrableOn (fun s : ℝ =>
      A * ((1 + |Real.log s|) ^ j * (s ^ (a - 1) * quadKernel β a' s))
      + B * ((1 + |Real.log s|) ^ j * (s ^ a * quadKernel β a' s))) (Ioi 0) :=
    (h0.const_mul A).add (h1.const_mul B)
  have h012 : IntegrableOn (fun s : ℝ =>
      (A * ((1 + |Real.log s|) ^ j * (s ^ (a - 1) * quadKernel β a' s))
        + B * ((1 + |Real.log s|) ^ j * (s ^ a * quadKernel β a' s)))
      + D * ((1 + |Real.log s|) ^ j * (s ^ (a + 1) * quadKernel β a' s))) (Ioi 0) :=
    h01.add (h2.const_mul D)
  unfold tailMoment logKernelMoment
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (h0.const_mul A) (h1.const_mul B), ← integral_add h01 (h2.const_mul D)]
  refine setIntegral_mono_on (moment_integrableOn_of_bound' β a' (a - 1) A B D hβ ha j c hc hbound)
    h012 measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  have hq : Real.exp (-β * s ^ 2) * Real.exp (β * s * a') = quadKernel β a' s :=
    exp_mul_exp_eq_quadKernel β a' s
  have hs1 : s ^ a = s ^ (a - 1) * s := by
    rw [← Real.rpow_add_one hs0.ne']; ring_nf
  have hs2 : s ^ (a + 1) = s ^ (a - 1) * s ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hs0]; congr 1; push_cast; ring
  have hL : 0 ≤ (1 + |Real.log s|) ^ j := pow_nonneg (by positivity) _
  have hsa : 0 ≤ s ^ (a - 1) := Real.rpow_nonneg hs0.le _
  rw [hs1, hs2, ← hq]
  have := hbound s hs0
  calc s ^ (a - 1) * (1 + |Real.log s|) ^ j * (Real.exp (-β * s ^ 2) * |c s|)
      ≤ s ^ (a - 1) * (1 + |Real.log s|) ^ j
        * (Real.exp (-β * s ^ 2) * (Real.exp (β * s * a') * (A + B * s + D * s ^ 2))) := by
        gcongr
    _ = _ := by ring

/-- **Remainder moment bound**: for `0 ≤ H s ≤ e^{βsa'}(A + Bs + Ds²)`,
`M_H ≤ A Λ_{a-1,J} + B Λ_{a,J} + D Λ_{a+1,J}`. -/
theorem envMoment_le_of_bound (β a' a A B D : ℝ) (hβ : 0 < β) (ha : -1 < a - 1)
    (J : ℕ) (H : ℝ → ℝ) (hH : Measurable H) (hH0 : ∀ s, 0 ≤ H s)
    (hbound : ∀ s, 0 < s → H s ≤ Real.exp (β * s * a') * (A + B * s + D * s ^ 2)) :
    envMoment β a J H ≤ A * logKernelMoment β a' (a - 1) J + B * logKernelMoment β a' a J
      + D * logKernelMoment β a' (a + 1) J := by
  have hbound' : ∀ s, 0 < s → |H s| ≤ Real.exp (β * s * a') * (A + B * s + D * s ^ 2) := by
    intro s hs; rw [abs_of_nonneg (hH0 s)]; exact hbound s hs
  have := tailMoment_le_of_bound β a' a A B D hβ ha J H hH hbound'
  unfold tailMoment at this
  unfold envMoment
  refine le_trans (le_of_eq ?_) this
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [abs_of_nonneg (hH0 s)]

end Laplace.Grammar
