/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.QuadraticMonomialBridge
import Laplace.Grammar.TwoDGeneralSwap

/-!
# Zero-phase dictionary for unequal exponents

Unit 198. The quadratic-kernel chart programme (`twoDGeneral`, kernel `e^{-βn s² + β√n s a}`,
parameter `n`) and the monomial normal-moment programme (`monomialBoxReal`, kernel `e^{-βN u^{2k}}`)
were cross-validated at **equal** starting exponents in unit 193. Here the dictionary is extended to
**unequal** exponents `p₁ = (h₁+1)/k₁ ≠ p₂ = (h₂+1)/k₂`, where neither side carries a logarithm.

* `twoDGeneral_zeroPhase_eq_monomial`: at zero phase (`a = 0`) and unit cutoff, the quadratic chart
  integral **is** the two-dimensional unit-box monomial integral at the same parameter `n`
  (no square: the quadratic kernel `e^{-βn(u^{k₁}v^{k₂})²}` is `e^{-βn u^{2k₁}v^{2k₂}}`).
* `headline_quadratic_zeroPhase_mixed` (and the swapped `…'`): for `p₁ < p₂`,
  `n^{p₁/2} ∫₀¹∫₀¹ u^{h₁}v^{h₂} e^{-βn(u^{k₁}v^{k₂})²} → Γ(p₁/2) / (2k₁ β^{p₁/2} (h₂+1-p₁k₂))`,
  transported from the mixed-ratio monomial theorem (`monomialBoxReal_mixed_tendsto` at
  `λ = p₁/2`, `|J| = 1`).
* `noLogConst_zeroPhase_eq_monomialMixedConst`, `noLogConst_zeroPhase_eq`: the two programmes'
  leading constants agree, `(k₁k₂)⁻¹ noLogConst β 0 p₁ p₂ = monomialMixedConst … (p₁/2) β`, which
  evaluates the no-log constant of the quadratic programme in closed form at zero phase:
  `noLogConst β 0 p₁ p₂ = Γ(p₁/2) β^{-p₁/2} / (2(p₂ - p₁))` (for exponent ratios realised by
  natural data; the identity is obtained by uniqueness of limits, not by direct integration).

The audit of the factor of two: there is no logarithm and no square in the parameter here, so no
factor `2^r` appears (contrast `tendsto_powLog_comp_sq` in unit 193). Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set Asymptotics

namespace Laplace.Grammar

/-- At zero phase the general quadratic chart integral is the constant-amplitude chart integral
`twoDAmp` at `N = √n`. -/
theorem twoDGeneral_zeroPhase_eq_twoDAmp (β b n : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hn : 0 ≤ n) :
    twoDGeneral β 0 b n h₁ h₂ k₁ k₂ = twoDAmp β b (Real.sqrt n) h₁ h₂ k₁ k₂ (fun _ _ _ => 1) := by
  unfold twoDGeneral twoDAmp
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun v _ => ?_
  rw [show (Real.sqrt n * (u ^ k₁ * v ^ k₂)) ^ 2 = n * (u ^ k₁ * v ^ k₂) ^ 2 by
    rw [mul_pow, Real.sq_sqrt hn]]
  simp only [mul_zero, add_zero, mul_one]
  rw [show -β * (n * (u ^ k₁ * v ^ k₂) ^ 2) = -β * n * (u ^ k₁ * v ^ k₂) ^ 2 by ring]
  ring

/-- **Zero-phase dictionary, unit cutoff**: the zero-phase quadratic chart integral is the unit-box
monomial integral at the same parameter `n`. -/
theorem twoDGeneral_zeroPhase_eq_monomial (β n : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hn : 0 ≤ n) :
    twoDGeneral β 0 1 n h₁ h₂ k₁ k₂ = monomialBoxReal 2 ![h₁, h₂] ![k₁, k₂] β n := by
  rw [twoDGeneral_zeroPhase_eq_twoDAmp β 1 n h₁ h₂ k₁ k₂ hn, twoDAmp_const_eq_monomialCutoff,
    monomialBoxRealCutoff_one, Real.sq_sqrt hn]

/-- In dimension two with exactly one minimising coordinate the multiplicity is one. -/
theorem multCount_two_mixed (h₁ h₂ k₁ k₂ : ℕ) (l : ℝ)
    (h0 : ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] 0 = l)
    (h1 : ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] 1 ≠ l) :
    multCount (ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂]) l = 1 := by
  unfold multCount
  rw [Fin.sum_univ_two, if_pos h0, if_neg h1]

/-- The two-dimensional mixed monomial constant in closed form:
`Γ(λ) β^{-λ} / (2k₁ (h₂ + 1 - 2k₂λ))`. -/
theorem monomialMixedConst_two_mixed (h₁ h₂ k₁ k₂ : ℕ) (l β : ℝ)
    (h0 : ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] 0 = l)
    (h1 : ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] 1 ≠ l) :
    monomialMixedConst (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] l β =
      Real.Gamma l * β ^ (-l) / (2 * (k₁ : ℝ) * ((h₂ : ℝ) + 1 - 2 * (k₂ : ℝ) * l)) := by
  unfold monomialMixedConst
  rw [multCount_two_mixed h₁ h₂ k₁ k₂ l h0 h1, Fin.prod_univ_two, if_pos h0, if_neg h1]
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, div_eq_mul_inv, mul_inv, one_mul]
  ring

/-- **Monomial side, `d = 2`, `p₁ < p₂`**: the two-dimensional unit-box monomial integral is
`~ monomialMixedConst · n^{-p₁/2}` (no logarithm). -/
theorem monomial_two_mixed_tendsto (β : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (p₁ p₂ : ℝ) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hlt : p₁ < p₂) :
    Tendsto (fun n : ℝ => monomialBoxReal 2 ![h₁, h₂] ![k₁, k₂] β n / n ^ (-(p₁ / 2))) atTop
      (𝓝 (monomialMixedConst (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] (p₁ / 2) β)) := by
  have hk : ∀ i, 0 < (![k₁, k₂] : Fin 2 → ℕ) i := by
    rw [Fin.forall_fin_two]
    exact ⟨hk₁, hk₂⟩
  have hp₁0 : 0 < p₁ := by
    rw [← hp₁]
    have := hk₁
    positivity
  have h0 : ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] 0 = p₁ / 2 := by
    rw [ratioExp_vecCons_zero, ← hp₁]
    ring
  have h1' : ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] 1 = p₂ / 2 := by
    rw [ratioExp_vecCons_one, ← hp₂]
    ring
  have h1 : ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] 1 ≠ p₁ / 2 := by
    rw [h1']
    intro h
    linarith
  have hmin : ∀ i, p₁ / 2 ≤ ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] i := by
    rw [Fin.forall_fin_two, h0, h1']
    exact ⟨le_rfl, by linarith⟩
  have hT := monomialBoxReal_mixed_tendsto 1 ![h₁, h₂] ![k₁, k₂] hk (p₁ / 2) β (by positivity) hβ
    hmin ⟨0, h0⟩
  rw [multCount_two_mixed h₁ h₂ k₁ k₂ _ h0 h1] at hT
  simp only [Nat.sub_self, pow_zero, mul_one] at hT
  exact hT

/-- **Headline XII (zero-phase, unequal exponents, `p₁ < p₂`)**:
`n^{p₁/2} ∫₀¹∫₀¹ u^{h₁} v^{h₂} e^{-βn(u^{k₁}v^{k₂})²} dv du
  → Γ(p₁/2) / (2k₁ β^{p₁/2} (h₂+1-p₁k₂))`. -/
theorem headline_quadratic_zeroPhase_mixed (β : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (p₁ p₂ : ℝ) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hlt : p₁ < p₂) :
    Tendsto (fun n : ℝ => n ^ (p₁ / 2) * twoDGeneral β 0 1 n h₁ h₂ k₁ k₂) atTop
      (𝓝 (Real.Gamma (p₁ / 2) / (2 * (k₁ : ℝ) * β ^ (p₁ / 2) * ((h₂ : ℝ) + 1 - p₁ * k₂)))) := by
  have hT := monomial_two_mixed_tendsto β h₁ h₂ k₁ k₂ hβ hk₁ hk₂ p₁ p₂ hp₁ hp₂ hlt
  have h0 : ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] 0 = p₁ / 2 := by
    rw [ratioExp_vecCons_zero, ← hp₁]
    ring
  have h1 : ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] 1 ≠ p₁ / 2 := by
    rw [show ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] 1 = p₂ / 2 by
      rw [ratioExp_vecCons_one, ← hp₂]; ring]
    intro h
    linarith
  rw [monomialMixedConst_two_mixed h₁ h₂ k₁ k₂ _ β h0 h1] at hT
  have hc : Real.Gamma (p₁ / 2) * β ^ (-(p₁ / 2)) /
      (2 * (k₁ : ℝ) * ((h₂ : ℝ) + 1 - 2 * (k₂ : ℝ) * (p₁ / 2))) =
      Real.Gamma (p₁ / 2) / (2 * (k₁ : ℝ) * β ^ (p₁ / 2) * ((h₂ : ℝ) + 1 - p₁ * k₂)) := by
    rw [Real.rpow_neg hβ.le]
    have hb : β ^ (p₁ / 2) ≠ 0 := (Real.rpow_pos_of_pos hβ _).ne'
    field_simp
  rw [hc] at hT
  refine hT.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
  rw [twoDGeneral_zeroPhase_eq_monomial β n h₁ h₂ k₁ k₂ hn.le, Real.rpow_neg hn.le,
    div_inv_eq_mul, mul_comm]

/-- **Headline XII, swapped (`p₂ < p₁`)**: the minimum ratio is attained at the second coordinate,
so the first coordinate carries the residue factor `1/(h₁+1-p₂k₁)`. -/
theorem headline_quadratic_zeroPhase_mixed' (β : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (p₁ p₂ : ℝ) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hgt : p₂ < p₁) :
    Tendsto (fun n : ℝ => n ^ (p₂ / 2) * twoDGeneral β 0 1 n h₁ h₂ k₁ k₂) atTop
      (𝓝 (Real.Gamma (p₂ / 2) / (2 * (k₂ : ℝ) * β ^ (p₂ / 2) * ((h₁ : ℝ) + 1 - p₂ * k₁)))) := by
  have hT := headline_quadratic_zeroPhase_mixed β h₂ h₁ k₂ k₁ hβ hk₂ hk₁ p₂ p₁ hp₂ hp₁ hgt
  refine hT.congr' (Eventually.of_forall fun n => ?_)
  rw [twoDGeneral_swap]

/-- **Constant cross-validation**: the quadratic programme's no-log leading constant at zero phase
equals the monomial mixed constant at `λ = p₁/2`. Obtained by uniqueness of limits through the
exact dictionary. -/
theorem noLogConst_zeroPhase_eq_monomialMixedConst (β : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (p₁ p₂ : ℝ) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (hlt : p₁ < p₂) :
    1 / ((k₁ : ℝ) * k₂) * noLogConst β 0 p₁ p₂ =
      monomialMixedConst (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] (p₁ / 2) β := by
  have hp₁0 : 0 < p₁ := by
    rw [← hp₁]
    have := hk₁
    positivity
  have hE := twoDGeneral_isEquivalent_of_lt β 0 1 h₁ h₂ k₁ k₂ hβ one_pos hk₁ hk₂
    (by rw [hp₁, hp₂]; exact hlt)
  rw [hp₁, hp₂, Real.one_rpow, mul_one] at hE
  set C := 1 / ((k₁ : ℝ) * k₂) * noLogConst β 0 p₁ p₂ with hC
  have hCpos : 0 < C := by
    have := noLogConst_pos β 0 p₁ p₂ hβ hp₁0 hlt
    have := hk₁
    have := hk₂
    positivity
  have hT1 : Tendsto (fun n : ℝ => twoDGeneral β 0 1 n h₁ h₂ k₁ k₂ / n ^ (-(p₁ / 2))) atTop
      (𝓝 C) := by
    have hz : ∀ᶠ n in atTop, C * n ^ (-(p₁ / 2)) ≠ 0 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
      exact (mul_pos hCpos (Real.rpow_pos_of_pos hn _)).ne'
    have h1 := (isEquivalent_iff_tendsto_one hz).1 hE
    have h2 := h1.const_mul C
    rw [mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    have hpow : n ^ (-(p₁ / 2)) ≠ 0 := (Real.rpow_pos_of_pos hn _).ne'
    have hC0 : C ≠ 0 := hCpos.ne'
    simp only [Pi.div_apply]
    field_simp
  have hT2 := monomial_two_mixed_tendsto β h₁ h₂ k₁ k₂ hβ hk₁ hk₂ p₁ p₂ hp₁ hp₂ hlt
  refine tendsto_nhds_unique hT1 (hT2.congr' ?_)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
  rw [twoDGeneral_zeroPhase_eq_monomial β n h₁ h₂ k₁ k₂ hn.le]

/-- **Closed form of the no-log constant at zero phase**:
`noLogConst β 0 p₁ p₂ = Γ(p₁/2) β^{-p₁/2} / (2 (p₂ - p₁))`, for exponent ratios realised by natural
data `p₁ = (h₁+1)/k₁ < p₂ = (h₂+1)/k₂`. -/
theorem noLogConst_zeroPhase_eq (β : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (p₁ p₂ : ℝ) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (hlt : p₁ < p₂) :
    noLogConst β 0 p₁ p₂ = Real.Gamma (p₁ / 2) * β ^ (-(p₁ / 2)) / (2 * (p₂ - p₁)) := by
  have h := noLogConst_zeroPhase_eq_monomialMixedConst β h₁ h₂ k₁ k₂ hβ hk₁ hk₂ p₁ p₂ hp₁ hp₂ hlt
  have h0 : ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] 0 = p₁ / 2 := by
    rw [ratioExp_vecCons_zero, ← hp₁]
    ring
  have h1 : ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] 1 ≠ p₁ / 2 := by
    rw [show ratioExp (![h₁, h₂] : Fin 2 → ℕ) ![k₁, k₂] 1 = p₂ / 2 by
      rw [ratioExp_vecCons_one, ← hp₂]; ring]
    intro h
    linarith
  rw [monomialMixedConst_two_mixed h₁ h₂ k₁ k₂ _ β h0 h1] at h
  have hk₁' : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
  have hk₂' : (0 : ℝ) < k₂ := by exact_mod_cast hk₂
  have hh₂ : (h₂ : ℝ) + 1 = p₂ * k₂ := by
    rw [← hp₂]
    field_simp
  have hden : 2 * (k₁ : ℝ) * ((h₂ : ℝ) + 1 - 2 * (k₂ : ℝ) * (p₁ / 2)) =
      ((k₁ : ℝ) * k₂) * (2 * (p₂ - p₁)) := by
    rw [hh₂]
    ring
  rw [hden] at h
  have hkk : (k₁ : ℝ) * k₂ ≠ 0 := by positivity
  have hne : (2 : ℝ) * (p₂ - p₁) ≠ 0 := by
    have : (0 : ℝ) < p₂ - p₁ := by linarith
    positivity
  calc noLogConst β 0 p₁ p₂ = ((k₁ : ℝ) * k₂) * (1 / ((k₁ : ℝ) * k₂) * noLogConst β 0 p₁ p₂) := by
        field_simp
    _ = ((k₁ : ℝ) * k₂) * (Real.Gamma (p₁ / 2) * β ^ (-(p₁ / 2)) /
          (((k₁ : ℝ) * k₂) * (2 * (p₂ - p₁)))) := by rw [h]
    _ = Real.Gamma (p₁ / 2) * β ^ (-(p₁ / 2)) / (2 * (p₂ - p₁)) := by
        field_simp

end Laplace.Grammar
