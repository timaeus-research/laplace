/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.MonomialMixedAsymptotic

/-!
# Shifted monomial moments

First step of the continuous-amplitude milestone (Astra #16, route C). Dressing the bare normal
moment integral with a monomial `u^γ` shifts the exponents `h ↦ h + γ`. Normalising by the scale
`N^{-λ} (log N)^{|J|-1}` of the *undressed* integral (with `λ = min (hᵢ+1)/(2kᵢ)` attained on `J`):

* if `γ` vanishes on `J` (`γⱼ = 0` for all `j ∈ J`), the shifted exponents have the same minimum and
  the same multiplicity, and the normalised moment converges to the mixed constant of the shifted
  exponents, `Γ(λ) β^{-λ}/(|J|-1)! ∏_{J} 1/(2kᵢ) ∏_{∉J} 1/(hᵢ+γᵢ+1-2kᵢλ)`
  (`shiftedMoment_tendsto_of_face`);
* otherwise the normalised moment tends to `0` (`shiftedMoment_tendsto_zero`): either some minimal
  coordinate is unshifted, so the minimum is still `λ` but with strictly smaller multiplicity and
  the log power drops, or every minimal coordinate is shifted and the minimum strictly increases.

These are exactly the monomial moments of the face-supported limiting functional of the next units.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Laplace.Grammar

/-- `(log N)^a / (log N)^b → 0` for `a < b`. -/
theorem tendsto_log_pow_div_pow (a b : ℕ) (hab : a < b) :
    Tendsto (fun N => Real.log N ^ a / Real.log N ^ b) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℝ => Real.log N ^ (b - a)) atTop atTop :=
    (tendsto_pow_atTop (Nat.sub_ne_zero_of_lt hab)).comp Real.tendsto_log_atTop
  refine h1.inv_tendsto_atTop.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  simp only [Pi.inv_apply]
  rw [pow_sub₀ _ hlog hab.le, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]

theorem ratioExp_le_shift {d : ℕ} (h k γ : Fin d → ℕ) (hk : ∀ i, 0 < k i) (i : Fin d) :
    ratioExp h k i ≤ ratioExp (fun i => h i + γ i) k i := by
  unfold ratioExp
  have := hk i
  push_cast
  gcongr
  linarith [(Nat.cast_nonneg (γ i) : (0 : ℝ) ≤ γ i)]

theorem ratioExp_shift_eq_of_zero {d : ℕ} (h k γ : Fin d → ℕ) (i : Fin d) (hi : γ i = 0) :
    ratioExp (fun i => h i + γ i) k i = ratioExp h k i := by
  unfold ratioExp
  simp only [hi, add_zero]

theorem ratioExp_lt_shift {d : ℕ} (h k γ : Fin d → ℕ) (hk : ∀ i, 0 < k i) (i : Fin d)
    (hi : γ i ≠ 0) : ratioExp h k i < ratioExp (fun i => h i + γ i) k i := by
  unfold ratioExp
  have := hk i
  have hγ : (1 : ℝ) ≤ γ i := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hi
  push_cast
  gcongr
  linarith

/-- The shifted exponents are still bounded below by `λ`. -/
theorem shift_min {d : ℕ} (h k γ : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ)
    (hmin : ∀ i, l ≤ ratioExp h k i) : ∀ i, l ≤ ratioExp (fun i => h i + γ i) k i :=
  fun i => (hmin i).trans (ratioExp_le_shift h k γ hk i)

/-- **Face shifts** (`γ = 0` on `J`): the normalised shifted moment converges to the mixed constant
of the shifted exponents. -/
theorem shiftedMoment_tendsto_of_face (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (γ : Fin (d + 1) → ℕ)
    (hγ : ∀ i, ratioExp h k i = l → γ i = 0) :
    Tendsto (fun N => monomialBoxReal (d + 1) (fun i => h i + γ i) k β N /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (monomialMixedConst (fun i => h i + γ i) k l β)) := by
  have hmin' := shift_min h k γ hk l hmin
  have hatt' : ∃ i, ratioExp (fun i => h i + γ i) k i = l := by
    obtain ⟨i, hi⟩ := hatt
    exact ⟨i, by rw [ratioExp_shift_eq_of_zero h k γ i (hγ i hi), hi]⟩
  have hm : multCount (ratioExp (fun i => h i + γ i) k) l = multCount (ratioExp h k) l := by
    unfold multCount
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : ratioExp h k i = l
    · rw [if_pos hi, if_pos (by rw [ratioExp_shift_eq_of_zero h k γ i (hγ i hi), hi])]
    · rw [if_neg hi, if_neg]
      intro h'
      apply hi
      exact le_antisymm (h' ▸ ratioExp_le_shift h k γ hk i) (hmin i)
  have := monomialBoxReal_mixed_tendsto d (fun i => h i + γ i) k hk l β hl hβ hmin' hatt'
  rwa [hm] at this

/-- **Non-face shifts**: the normalised shifted moment tends to `0`. -/
theorem shiftedMoment_tendsto_zero (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (γ : Fin (d + 1) → ℕ)
    (hγ : ∃ j, ratioExp h k j = l ∧ γ j ≠ 0) :
    Tendsto (fun N => monomialBoxReal (d + 1) (fun i => h i + γ i) k β N /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop (𝓝 0) := by
  set h' : Fin (d + 1) → ℕ := fun i => h i + γ i with hh'
  have hmin' := shift_min h k γ hk l hmin
  set m := multCount (ratioExp h k) l with hm
  set m' := multCount (ratioExp h' k) l with hm'
  have hmpos : 0 < m := multCount_pos _ l hatt
  -- the shifted multiplicity is strictly smaller
  have hlt : m' < m := by
    obtain ⟨j, hj, hγj⟩ := hγ
    rw [hm, hm']
    unfold multCount
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
    · by_cases hi : ratioExp h' k i = l
      · rw [if_pos hi, if_pos (le_antisymm (hi ▸ ratioExp_le_shift h k γ hk i) (hmin i))]
      · rw [if_neg hi]
        exact Nat.zero_le _
    · rw [if_pos hj, if_neg (ne_of_gt (hj ▸ ratioExp_lt_shift h k γ hk j hγj))]
      exact one_pos
  by_cases hatt' : ∃ i, ratioExp h' k i = l
  · -- some minimal coordinate unshifted: same exponent, lower log power
    have hT := monomialBoxReal_mixed_tendsto d h' k hk l β hl hβ hmin' hatt'
    rw [← hm'] at hT
    have hm'pos : 0 < m' := multCount_pos _ l hatt'
    have hlog := tendsto_log_pow_div_pow (m' - 1) (m - 1) (by omega)
    have hprod := hT.mul hlog
    rw [mul_zero] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    have hlogN : Real.log N ≠ 0 := (Real.log_pos hN).ne'
    have h1 : Real.log N ^ (m' - 1) ≠ 0 := pow_ne_zero _ hlogN
    have h2 : Real.log N ^ (m - 1) ≠ 0 := pow_ne_zero _ hlogN
    field_simp
  · -- every minimal coordinate shifted: strictly larger minimal exponent
    push Not at hatt'
    have hl' : l < minRatio h' k := by
      obtain ⟨i, hi⟩ := exists_ratioExp_eq_minRatio h' k
      rw [← hi]
      exact lt_of_le_of_ne (hmin' i) (Ne.symm (hatt' i))
    have hE := monomialBoxReal_minRatio_isEquivalent d h' k hk β hβ
    have hE' : (fun N => monomialBoxReal (d + 1) h' k β N) ~[atTop]
        powLog (monomialMixedConst h' k (minRatio h' k) β) (minRatio h' k)
          (multCount (ratioExp h' k) (minRatio h' k) - 1) := hE
    have h1 : (fun N : ℝ => N ^ (-l) * Real.log N ^ (m - 1)) ~[atTop] powLog 1 l (m - 1) :=
      IsEquivalent.refl.congr_right (Eventually.of_forall fun N => by simp [powLog])
    exact tendsto_quotient_zero_of_lt _ _ _ _ _ _ _ _ hl' hE' h1

end Laplace.Grammar
