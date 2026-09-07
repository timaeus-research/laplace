/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PhasePosterior

/-!
# A formal counterexample: mixed ratios evaluate on the face, not at the corner

Unit 206. The paper's leading-coefficient formula reads the amplitude at the origin. For
**mixed** exponent ratios this is wrong: the leading coefficient of the dressed integral is the face
functional `amplitudeCoeff`, and here is the smallest instance, recorded as theorems.

`d = 2`, `h = (0, 2)`, `k = (1, 1)`, `β = 1`: ratios `1/2` and `3/2`, so `λ = 1/2`, `J = {0}`,
`m = 1`. Amplitude `η(u) = 1 + u₁`. Then
```
∫_{(0,1]²} (1 + u₁) u₁² e^{-N u₀² u₁²} du / N^{-1/2}  →  5√π/12      (mixed_counterexample_tendsto)
η(0) · (bare constant)                               =  √π/4        (mixed_counterexample_corner)
```
and `5√π/12 ≠ √π/4` (`mixed_ratio_corner_evaluation_fails`). The face functional is
`Γ(1/2)/2 · ∫₀¹ (1 + v) v dv = (√π/2)(1/2 + 1/3)`: the residual coordinate `u₁` carries the weight
`u₁^{h₁ - 2k₁λ} = u₁` and the amplitude is integrated against it, not evaluated at `u₁ = 0`.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.Grammar

namespace MixedCounterexample

/-- The exponents `h = (0, 2)`. -/
def hEx : Fin 2 → ℕ := ![0, 2]
/-- The exponents `k = (1, 1)`. -/
def kEx : Fin 2 → ℕ := ![1, 1]
/-- The amplitude `η(u) = 1 + u₁`. -/
noncomputable def ηEx (u : Fin 2 → ℝ) : ℝ := 1 + u 1

theorem hk : ∀ i, 0 < kEx i := by
  rw [Fin.forall_fin_two]
  exact ⟨one_pos, one_pos⟩

theorem ratio0 : ratioExp hEx kEx 0 = 1 / 2 := by
  simp [ratioExp, hEx, kEx]

theorem ratio1 : ratioExp hEx kEx 1 = 3 / 2 := by
  simp [ratioExp, hEx, kEx]
  norm_num

theorem hmin : ∀ i, (1 / 2 : ℝ) ≤ ratioExp hEx kEx i := by
  rw [Fin.forall_fin_two, ratio0, ratio1]
  norm_num

theorem hatt : ∃ i, ratioExp hEx kEx i = 1 / 2 := ⟨0, ratio0⟩

theorem multCount_eq : multCount (ratioExp hEx kEx) (1 / 2) = 1 := by
  unfold multCount
  rw [Fin.sum_univ_two, if_pos ratio0, if_neg (by rw [ratio1]; norm_num)]

/-- The bare mixed constant `Γ(1/2)/(2·(2+1-1)) = √π/4`. -/
theorem mixedConst_eq : monomialMixedConst hEx kEx (1 / 2) 1 = Real.sqrt π / 4 := by
  have h := monomialMixedConst_two_mixed 0 2 1 1 (1 / 2) 1 ratio0
    (by show ratioExp hEx kEx 1 ≠ 1 / 2; rw [ratio1]; norm_num)
  simp only [hEx, kEx] at h ⊢
  rw [h, Real.Gamma_one_half_eq]
  norm_num

/-- The shifted constant for `h = (0, 3)`: `Γ(1/2)/(2·(3+1-1)) = √π/6`. -/
theorem mixedConst_shift_eq :
    monomialMixedConst (fun i => hEx i + (![0, 1] : Fin 2 → ℕ) i) kEx (1 / 2) 1 =
      Real.sqrt π / 6 := by
  have hfun : (fun i => hEx i + (![0, 1] : Fin 2 → ℕ) i) = (![0, 3] : Fin 2 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  have hr0 : ratioExp (![0, 3] : Fin 2 → ℕ) ![1, 1] 0 = 1 / 2 := by
    simp [ratioExp]
  have hr1 : ratioExp (![0, 3] : Fin 2 → ℕ) ![1, 1] 1 ≠ 1 / 2 := by
    simp [ratioExp]
    norm_num
  rw [hfun]
  have h := monomialMixedConst_two_mixed 0 3 1 1 (1 / 2) 1 hr0 hr1
  simp only [kEx]
  rw [h, Real.Gamma_one_half_eq]
  norm_num

/-- **The face functional of `η = 1 + u₁` is `5√π/12`.** -/
theorem amplitudeCoeff_eq : amplitudeCoeff hEx kEx (1 / 2) 1 ηEx = 5 * Real.sqrt π / 12 := by
  have hA := face_moment_eq hEx kEx hk (1 / 2) 1 hmin (fun _ => 0) (fun _ _ => rfl)
  have hB := face_moment_eq hEx kEx hk (1 / 2) 1 hmin ![0, 1] (by
    rw [Fin.forall_fin_two]
    exact ⟨fun _ => rfl, fun h => absurd h (by rw [ratio1]; norm_num)⟩)
  have hI : ∀ γ : Fin 2 → ℕ, IntegrableOn (fun u => (∏ i, faceProj hEx kEx (1 / 2) u i ^ γ i) *
      (faceLeadConst hEx kEx (1 / 2) 1 * residualWeight hEx kEx (1 / 2) u)) (unitBox 2) := by
    intro γ
    refine (integrableOn_face_mul hEx kEx hk (1 / 2) hmin
      (fun x => faceLeadConst hEx kEx (1 / 2) 1 * ∏ i, x i ^ γ i)
      (continuous_const.mul (continuous_prod_pow γ))).congr_fun (fun u _ => ?_)
      (measurableSet_unitBox 2)
    ring
  have hsplit : amplitudeCoeff hEx kEx (1 / 2) 1 ηEx =
      (∫ u in unitBox 2, (∏ i, faceProj hEx kEx (1 / 2) u i ^ (fun _ : Fin 2 => 0) i) *
        (faceLeadConst hEx kEx (1 / 2) 1 * residualWeight hEx kEx (1 / 2) u)) +
      ∫ u in unitBox 2, (∏ i, faceProj hEx kEx (1 / 2) u i ^ (![0, 1] : Fin 2 → ℕ) i) *
        (faceLeadConst hEx kEx (1 / 2) 1 * residualWeight hEx kEx (1 / 2) u) := by
    unfold amplitudeCoeff
    rw [← integral_const_mul, ← integral_add (hI _) (hI _)]
    refine setIntegral_congr_fun (measurableSet_unitBox 2) fun u _ => ?_
    simp only [ηEx, Fin.prod_univ_two, pow_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
      pow_one, one_mul]
    ring
  rw [hsplit, hA, hB, mixedConst_shift_eq]
  have : monomialMixedConst (fun i => hEx i + (fun _ : Fin 2 => 0) i) kEx (1 / 2) 1 =
      monomialMixedConst hEx kEx (1 / 2) 1 := by
    congr 1
  rw [this, mixedConst_eq]
  ring

/-- **The corner evaluation gives `√π/4`.** -/
theorem corner_eq : ηEx 0 * monomialMixedConst hEx kEx (1 / 2) 1 = Real.sqrt π / 4 := by
  rw [mixedConst_eq]
  simp [ηEx]

/-- **Corner evaluation fails for mixed ratios.** -/
theorem corner_evaluation_fails :
    amplitudeCoeff hEx kEx (1 / 2) 1 ηEx ≠ ηEx 0 * monomialMixedConst hEx kEx (1 / 2) 1 := by
  rw [amplitudeCoeff_eq, corner_eq]
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  intro h
  nlinarith

/-- **The dressed integral itself**:
`∫_{(0,1]²} (1 + u₁) u₁² e^{-N u₀² u₁²} du / N^{-1/2} → 5√π/12`, the face value, not the corner
value `√π/4`. -/
theorem tendsto :
    Tendsto (fun N : ℝ => (∫ x in unitBox 2,
        ηEx x * ((∏ i, x i ^ hEx i) * Real.exp (-(1 * N * ∏ i, x i ^ (2 * kEx i))))) /
        N ^ (-(1 / 2 : ℝ))) atTop (𝓝 (5 * Real.sqrt π / 12)) := by
  have hT := amplitude_tendsto 1 hEx kEx hk (1 / 2) 1 (by norm_num) one_pos hmin hatt ηEx
    (continuous_const.add (continuous_apply 1))
  rw [multCount_eq, Nat.sub_self, amplitudeCoeff_eq] at hT
  simpa using hT

end MixedCounterexample

end Laplace.Grammar
