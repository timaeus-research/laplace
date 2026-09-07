/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.QuotientCalculus

/-!
# Leading-term extraction from the Taylor tree (equal starting exponents)

For equal starting exponents `p = (h₁+1)/k₁ = (h₂+1)/k₂` the retained exponent set of the Taylor
tree below `2T ≤ p + min(1/k₁, 1/k₂)` is `{p}` (`polesBelowGen_eq_singleton`), so the chart
integral satisfies `Z(N) = N^{−p}(A_p log N + B_p) + O(N^{−(p+δ)}(1 + log N))` for some `δ > 0`
(`chart_leading_isBigO`). Consequently `Z ~ A_p N^{−p} log N` when `A_p ≠ 0`
(`chart_isEquivalent_log`), and `Z ~ B_p N^{−p}` when `A_p = 0 ≠ B_p` (`chart_isEquivalent_const`):
the two leading behaviours entering the unequal-leading-term posterior ratio (Astra #14 rank 2).
Zero `sorry`/`axiom`.
-/

open Asymptotics Filter Real Topology

namespace Laplace.Grammar

/-- Below `2T ≤ p + min(1/k₁, 1/k₂)` the only retained exponent is `p`. -/
theorem polesBelowGen_eq_singleton (h₁ h₂ k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (p T : ℝ)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (hT₁ : p < 2 * T)
    (hT₂ : 2 * T ≤ p + 1 / k₁) (hT₃ : 2 * T ≤ p + 1 / k₂) :
    polesBelowGen h₁ h₂ k₁ k₂ p p T = {p} := by
  have hk₁' : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
  have hk₂' : (0 : ℝ) < k₂ := by exact_mod_cast hk₂
  ext α
  rw [mem_polesBelowGen_iff h₁ h₂ k₁ k₂ hk₁ hk₂ p p T hp₁ hp₂, Finset.mem_singleton]
  constructor
  · rintro ⟨hαT, ⟨i, rfl⟩ | ⟨j, rfl⟩⟩
    · have hi : uExp h₁ k₁ i = p + i / k₁ := by
        unfold uExp; push_cast; rw [← hp₁]; ring
      rw [hi] at hαT ⊢
      have : (i : ℝ) / k₁ < 1 / k₁ := by linarith
      rw [div_lt_div_iff_of_pos_right hk₁'] at this
      have hi0 : i = 0 := by exact_mod_cast (Nat.lt_one_iff.1 (by exact_mod_cast this))
      subst hi0; simp
    · have hj : vExp h₂ k₂ j = p + j / k₂ := by
        unfold vExp; push_cast; rw [← hp₂]; ring
      rw [hj] at hαT ⊢
      have : (j : ℝ) / k₂ < 1 / k₂ := by linarith
      rw [div_lt_div_iff_of_pos_right hk₂'] at this
      have hj0 : j = 0 := by exact_mod_cast (Nat.lt_one_iff.1 (by exact_mod_cast this))
      subst hj0; simp
  · intro hα
    rw [hα]
    exact ⟨hT₁, Or.inl ⟨0, uExp_zero h₁ k₁ p hp₁⟩⟩

/-- The gap above the leading exponent. -/
noncomputable def leadingGap (k₁ k₂ : ℕ) : ℝ := min (1 / (k₁ : ℝ)) (1 / (k₂ : ℝ)) / 2

theorem leadingGap_pos (k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) : 0 < leadingGap k₁ k₂ := by
  unfold leadingGap
  have hk₁' : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
  have hk₂' : (0 : ℝ) < k₂ := by exact_mod_cast hk₂
  positivity

/-- **Two-term expansion with a power-saving remainder** for equal starting exponents. -/
theorem chart_leading_isBigO (β b p ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hy : WSummable ρ y) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b)
        - N ^ (-p) * (canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) p * Real.log N
          + canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x y) b) (anaFaceV (ampCoeff β x y) b)
              (fun i j s => ampCoeff β x y (i, j) s) p))
      =O[atTop] fun N : ℝ => N ^ (-(p + leadingGap k₁ k₂)) * (1 + Real.log N) := by
  have hk₁' : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
  have hk₂' : (0 : ℝ) < k₂ := by exact_mod_cast hk₂
  set δ := leadingGap k₁ k₂ with hδdef
  have hδ : 0 < δ := leadingGap_pos k₁ k₂ hk₁ hk₂
  have hδ₁ : δ ≤ 1 / k₁ / 2 := by
    rw [hδdef]; unfold leadingGap; exact div_le_div_of_nonneg_right (min_le_left _ _) two_pos.le
  have hδ₂ : δ ≤ 1 / k₂ / 2 := by
    rw [hδdef]; unfold leadingGap; exact div_le_div_of_nonneg_right (min_le_right _ _) two_pos.le
  set T := (p + δ) / 2 with hT
  have h2T : 2 * T = p + δ := by rw [hT]; ring
  have hsing := polesBelowGen_eq_singleton h₁ h₂ k₁ k₂ hk₁ hk₂ p T hp₁ hp₂ (by linarith)
    (by rw [h2T]; have : 0 < 1 / (k₁ : ℝ) := by positivity
        linarith)
    (by rw [h2T]; have : 0 < 1 / (k₂ : ℝ) := by positivity
        linarith)
  have h := twoD_taylor_tree_general β b p p ρ h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ x y hx hy T
  rw [hsing, h2T] at h
  simpa [Finset.sum_singleton] using h

/-- `N^{−(p+δ)}(1 + log N) = o(N^{−p} log N)` for `δ > 0`. -/
theorem isLittleO_remainder_log (p δ : ℝ) (hδ : 0 < δ) (A : ℝ) (hA : A ≠ 0) :
    (fun N : ℝ => N ^ (-(p + δ)) * (1 + Real.log N)) =o[atTop] powLog A p 1 := by
  rw [isLittleO_iff_tendsto']
  · have h1 := tendsto_rpow_neg_atTop hδ
    have h2 : Tendsto (fun N : ℝ => (1 + Real.log N) / Real.log N) atTop (𝓝 1) := by
      have := Real.tendsto_log_atTop.inv_tendsto_atTop
      have h := this.const_add 1
      rw [add_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
      have : Real.log N ≠ 0 := (Real.log_pos hN).ne'
      simp only [Pi.inv_apply]
      field_simp
      ring
    have := (h1.mul h2).const_mul A⁻¹
    simp only [zero_mul, mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
    have hp : N ^ (-p) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    unfold powLog
    rw [pow_one, show N ^ (-(p + δ)) = N ^ (-p) * N ^ (-δ) by
      rw [← Real.rpow_add hN0]; congr 1; ring]
    field_simp
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN h0
    exfalso
    unfold powLog at h0
    have hN0 : 0 < N := by linarith
    have : A * N ^ (-p) * Real.log N ^ 1 ≠ 0 :=
      mul_ne_zero (mul_ne_zero hA (Real.rpow_pos_of_pos hN0 _).ne')
        (pow_ne_zero _ (Real.log_pos hN).ne')
    exact this h0

/-- `N^{−p} = o(N^{−p} log N)`. -/
theorem isLittleO_const_term (p : ℝ) (A B : ℝ) (hA : A ≠ 0) :
    (fun N : ℝ => B * N ^ (-p)) =o[atTop] powLog A p 1 := by
  rw [isLittleO_iff_tendsto']
  · have := Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul (B / A)
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
    have hp : N ^ (-p) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    unfold powLog
    simp only [Pi.inv_apply]
    field_simp
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN h0
    exfalso
    unfold powLog at h0
    have hN0 : 0 < N := by linarith
    exact (mul_ne_zero (mul_ne_zero hA (Real.rpow_pos_of_pos hN0 _).ne')
      (pow_ne_zero _ (Real.log_pos hN).ne')) h0

/-- `N^{−(p+δ)}(1 + log N) = o(B N^{−p})` for `δ > 0`, `B ≠ 0`. -/
theorem isLittleO_remainder_const (p δ : ℝ) (hδ : 0 < δ) (B : ℝ) (hB : B ≠ 0) :
    (fun N : ℝ => N ^ (-(p + δ)) * (1 + Real.log N)) =o[atTop] powLog B p 0 := by
  rw [isLittleO_iff_tendsto']
  · have := (tendsto_rpow_neg_mul_one_add_log δ hδ).const_mul B⁻¹
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    have hp : N ^ (-p) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    unfold powLog
    rw [pow_zero, mul_one, show N ^ (-(p + δ)) = N ^ (-p) * N ^ (-δ) by
      rw [← Real.rpow_add hN0]; congr 1; ring]
    field_simp
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN h0
    exfalso
    unfold powLog at h0
    have hN0 : 0 < N := by linarith
    rw [pow_zero, mul_one] at h0
    exact (mul_ne_zero hB (Real.rpow_pos_of_pos hN0 _).ne') h0

/-- **Log-leading case**: `Z ~ A_p N^{−p} log N` when `A_p ≠ 0`. -/
theorem chart_isEquivalent_log (β b p ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hy : WSummable ρ y)
    (hA : canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) p ≠ 0) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b)) ~[atTop]
      powLog (canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) p) p 1 := by
  set A := canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) p with hAdef
  set B := canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x y) b) (anaFaceV (ampCoeff β x y) b)
    (fun i j s => ampCoeff β x y (i, j) s) p with hBdef
  have hR := chart_leading_isBigO β b p ρ h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ x y hx hy
  rw [← hAdef, ← hBdef] at hR
  have hδ := leadingGap_pos k₁ k₂ hk₁ hk₂
  refine IsLittleO.isEquivalent ?_
  have hid : (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b)) - powLog A p 1
      = fun N => (twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b)
          - N ^ (-p) * (A * Real.log N + B)) + B * N ^ (-p) := by
    funext N; simp only [Pi.sub_apply]; unfold powLog; ring
  rw [hid]
  exact (hR.trans_isLittleO (isLittleO_remainder_log p _ hδ A hA)).add
    (isLittleO_const_term p A B hA)

/-- **Constant-leading case**: `Z ~ B_p N^{−p}` when `A_p = 0` and `B_p ≠ 0`. -/
theorem chart_isEquivalent_const (β b p ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hy : WSummable ρ y)
    (hA : canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) p = 0)
    (hB : canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x y) b) (anaFaceV (ampCoeff β x y) b)
      (fun i j s => ampCoeff β x y (i, j) s) p ≠ 0) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b)) ~[atTop]
      powLog (canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x y) b) (anaFaceV (ampCoeff β x y) b)
        (fun i j s => ampCoeff β x y (i, j) s) p) p 0 := by
  set B := canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x y) b) (anaFaceV (ampCoeff β x y) b)
    (fun i j s => ampCoeff β x y (i, j) s) p with hBdef
  have hR := chart_leading_isBigO β b p ρ h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ x y hx hy
  rw [hA, ← hBdef] at hR
  have hδ := leadingGap_pos k₁ k₂ hk₁ hk₂
  refine IsLittleO.isEquivalent ?_
  have hid : (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b)) - powLog B p 0
      = fun N => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b)
          - N ^ (-p) * (0 * Real.log N + B) := by
    funext N; simp only [Pi.sub_apply]; unfold powLog; ring
  rw [hid]
  exact hR.trans_isLittleO (isLittleO_remainder_const p _ hδ B hB)

end Laplace.Grammar
