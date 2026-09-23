/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LogSectorGeneral

/-!
# Auxiliary estimates for the untied coordinates

The ingredients of the dominated-convergence argument over the untied block in the single-monomial
power–log theorem: `1 + ∑ y ≤ ∏ (1 + y)` (`one_add_sum_le_prod_one_add`), integrability of
`e^{−εy}(1+y)^k` and `∫₀^∞ e^{−εy} dy = 1/ε` (`integrableOn_exp_neg_mul_one_add_pow`,
`integral_exp_neg_mul_Ioi`), the rescaled core identity at `s = t e^{−Y}` (`rpow_mul_coreIntegral`),
the uniform bound `(1+Y)^k C_k` on the rescaled inner integral (`inner_bound`) and its limit `Γ(λ)`
(`inner_tendsto`).
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

/-- `1 + ∑ y_j ≤ ∏ (1 + y_j)` for nonnegative `y`. -/
theorem one_add_sum_le_prod_one_add {ι : Type*} (s : Finset ι) (y : ι → ℝ) (hy : ∀ j, 0 ≤ y j) :
    1 + ∑ j ∈ s, y j ≤ ∏ j ∈ s, (1 + y j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h0 : 0 ≤ ∑ j ∈ s, y j := Finset.sum_nonneg fun j _ ↦ hy j
    nlinarith [hy a, mul_nonneg (hy a) h0]

/-- `e^{−εy}(1+y)^k` is integrable on `(0, ∞)` for `ε > 0`. -/
theorem integrableOn_exp_neg_mul_one_add_pow {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    IntegrableOn (fun y : ℝ ↦ exp (-(ε * y)) * (1 + y) ^ k) (Ioi 0) := by
  have h1 : IntegrableOn (fun y : ℝ ↦ y ^ (0 : ℝ) * exp (-ε * y ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) one_pos hε
  have h2 : IntegrableOn (fun y : ℝ ↦ y ^ (k : ℝ) * exp (-ε * y ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith) one_pos hε
  refine ((h1.add h2).const_mul (2 * 3 ^ k)).mono' ?_ ?_
  · exact (Measurable.aestronglyMeasurable
      ((measurable_const.mul measurable_id).neg.exp.mul
        ((measurable_const.add measurable_id).pow_const _)))
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun y hy ↦ ?_
    have hy : 0 < y := hy
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_zero, Real.rpow_one,
      Real.rpow_natCast, one_mul, neg_mul]
    have hpow : (1 + y) ^ k ≤ 2 * 3 ^ k * (1 + y ^ k) := by
      have := add_add_pow_le zero_le_one hy.le le_rfl k
      rw [add_zero, one_pow] at this
      have h0k : (0 : ℝ) ^ k ≤ 1 := by
        rcases Nat.eq_zero_or_pos k with hk | hk
        · rw [hk, pow_zero]
        · rw [zero_pow hk.ne']; exact zero_le_one
      have h3 : (0 : ℝ) ≤ 3 ^ k := by positivity
      have hyk : (0 : ℝ) ≤ y ^ k := pow_nonneg hy.le k
      calc (1 + y) ^ k ≤ 3 ^ k * (1 + y ^ k + 0 ^ k) := this
        _ ≤ 3 ^ k * (1 + y ^ k + 1) := by gcongr
        _ ≤ 2 * 3 ^ k * (1 + y ^ k) := by nlinarith [mul_nonneg h3 hyk]
    calc exp (-(ε * y)) * (1 + y) ^ k ≤ exp (-(ε * y)) * (2 * 3 ^ k * (1 + y ^ k)) :=
          mul_le_mul_of_nonneg_left hpow (exp_pos _).le
      _ = 2 * 3 ^ k * (exp (-(ε * y)) + y ^ k * exp (-(ε * y))) := by ring

/-- `∫₀^∞ e^{−εy} dy = 1/ε`. -/
theorem integral_exp_neg_mul_Ioi {ε : ℝ} (hε : 0 < ε) : ∫ y in Ioi 0, exp (-(ε * y)) = 1 / ε := by
  have := integral_rpow_mul_exp_neg_mul_rpow one_pos (by norm_num : (-1 : ℝ) < 0) hε
  simp only [Real.rpow_zero, one_mul, Real.rpow_one, zero_add, div_one, Real.Gamma_one, mul_one,
    neg_mul] at this
  rw [this, Real.rpow_neg_one, one_div]

/-- The rescaled core identity:
`t^λ J(t e^{−Y}) = e^{λY} ∫₀^{t e^{−Y}} u^{λ−1} e^{−u} (log t − Y − log u)^k`. -/
theorem rpow_mul_coreIntegral {t : ℝ} (ht : 0 < t) (lam : ℝ) (k : ℕ) (Y : ℝ) :
    t ^ lam * coreIntegral lam k (t * exp (-Y)) =
      exp (lam * Y) * ∫ u in Ioo 0 (t * exp (-Y)),
        u ^ (lam - 1) * exp (-u) * (log t - Y - log u) ^ k := by
  have ht' : 0 < t * exp (-Y) := by positivity
  have h := rpow_mul_integral_logSector ht' lam k
  unfold coreIntegral
  rw [log_mul ht.ne' (exp_pos _).ne', log_exp, ← sub_eq_add_neg] at h
  rw [← h, Real.mul_rpow ht.le (exp_pos _).le, ← Real.exp_mul]
  have : exp (-Y * lam) * exp (lam * Y) = 1 := by
    rw [← Real.exp_add]; convert Real.exp_zero using 2; ring
  calc t ^ lam * (∫ z in Ioi 0, exp (-(t * exp (-Y) * exp (-z))) * exp (-(lam * z)) * z ^ k)
      = (exp (-Y * lam) * exp (lam * Y)) * (t ^ lam * ∫ z in Ioi 0,
          exp (-(t * exp (-Y) * exp (-z))) * exp (-(lam * z)) * z ^ k) := by rw [this, one_mul]
    _ = _ := by ring

/-- The uniform bound on the rescaled inner integral (`log t ≥ 1`, `Y ≥ 0`). -/
theorem inner_bound {lam : ℝ} (hlam : 0 < lam) (k : ℕ) {t : ℝ} (ht : 1 ≤ log t) {Y : ℝ}
    (hY : 0 ≤ Y) :
    |∫ u in Ioo 0 (t * exp (-Y)), u ^ (lam - 1) * exp (-u) * (1 - (Y + log u) / log t) ^ k| ≤
      (1 + Y) ^ k * ∫ u in Ioi 0, u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ k := by
  have hG := integrableOn_gammaLog hlam k
  have hGnn : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ k :=
    fun u hu ↦ mul_nonneg (mul_nonneg (rpow_nonneg (le_of_lt hu) _) (exp_pos _).le)
      (pow_nonneg (by positivity) _)
  have hbd : ∀ u ∈ Ioo (0 : ℝ) (t * exp (-Y)),
      ‖u ^ (lam - 1) * exp (-u) * (1 - (Y + log u) / log t) ^ k‖ ≤
        (1 + Y) ^ k * (u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ k) := by
    intro u hu
    have hu0 : 0 < u := hu.1
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (rpow_nonneg hu0.le _),
      abs_of_nonneg (exp_pos _).le, abs_pow]
    have h1 : |1 - (Y + log u) / log t| ≤ (1 + Y) * (1 + |log u|) := by
      calc |1 - (Y + log u) / log t| ≤ |1| + |(Y + log u) / log t| := abs_sub _ _
        _ = 1 + |Y + log u| / log t := by
          rw [abs_one, abs_div, abs_of_pos (show (0 : ℝ) < log t by linarith)]
        _ ≤ 1 + |Y + log u| := by
          have := div_le_self (abs_nonneg (Y + log u)) ht
          linarith
        _ ≤ 1 + (Y + |log u|) := by
          have := abs_add_le Y (log u)
          rw [abs_of_nonneg hY] at this
          linarith
        _ ≤ (1 + Y) * (1 + |log u|) := by nlinarith [abs_nonneg (log u)]
    calc u ^ (lam - 1) * exp (-u) * |1 - (Y + log u) / log t| ^ k
        ≤ u ^ (lam - 1) * exp (-u) * ((1 + Y) * (1 + |log u|)) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) h1 k) (by positivity)
      _ = (1 + Y) ^ k * (u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ k) := by rw [mul_pow]; ring
  have hsub : Ioo (0 : ℝ) (t * exp (-Y)) ⊆ Ioi 0 := Ioo_subset_Ioi_self
  calc |∫ u in Ioo 0 (t * exp (-Y)), u ^ (lam - 1) * exp (-u) * (1 - (Y + log u) / log t) ^ k|
      ≤ ∫ u in Ioo 0 (t * exp (-Y)),
          (1 + Y) ^ k * (u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ k) := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le ((hG.mono_set hsub).const_mul _) ?_
        rw [ae_restrict_iff' measurableSet_Ioo]
        exact Eventually.of_forall hbd
    _ ≤ ∫ u in Ioi 0, (1 + Y) ^ k * (u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ k) := by
        refine setIntegral_mono_set (hG.const_mul _) ?_ (Eventually.of_forall hsub)
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
        refine Eventually.of_forall fun u hu ↦ ?_
        change (0 : ℝ) ≤ _
        exact mul_nonneg (pow_nonneg (by linarith) _) (hGnn u hu)
    _ = _ := integral_const_mul _ _

/-- The limit of the rescaled inner integral, for fixed `Y`. -/
theorem inner_tendsto {lam : ℝ} (hlam : 0 < lam) (k : ℕ) (Y : ℝ) :
    Tendsto (fun t ↦ ∫ u in Ioo 0 (t * exp (-Y)),
      u ^ (lam - 1) * exp (-u) * (1 - (Y + log u) / log t) ^ k) atTop (𝓝 (Gamma lam)) := by
  have hT : Tendsto (fun t : ℝ ↦ t * exp (-Y)) atTop atTop :=
    tendsto_id.atTop_mul_const (exp_pos _)
  have hcore := (tendsto_logSector_core hlam k).comp hT
  have hratio : Tendsto (fun t : ℝ ↦ ((log t - Y) / log t) ^ k) atTop (𝓝 1) := by
    have h1 : Tendsto (fun t : ℝ ↦ 1 - Y / log t) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
    rw [sub_zero] at h1
    have h2 := h1.pow k
    rw [one_pow] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have hlog : log t ≠ 0 := (log_pos ht).ne'
    congr 1
    field_simp
  have h := hratio.mul hcore
  rw [one_mul] at h
  refine h.congr' ?_
  -- the identity for `t e^{−Y} > 1`
  have hev : ∀ᶠ t : ℝ in atTop, 1 < t * exp (-Y) ∧ 1 < t := by
    filter_upwards [hT.eventually (eventually_gt_atTop 1), eventually_gt_atTop (1 : ℝ)] with t h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hev] with t ⟨ht', ht⟩
  have ht0 : 0 < t := by linarith
  have hlog : log t ≠ 0 := (log_pos ht).ne'
  have hlog' : log t + -Y ≠ 0 := by
    have h1 := log_pos ht'
    rw [log_mul ht0.ne' (exp_pos _).ne', log_exp] at h1
    exact h1.ne'
  have hs := rpow_mul_integral_logSector (by positivity : 0 < t * exp (-Y)) lam k
  simp only [Function.comp_def]
  rw [log_mul ht0.ne' (exp_pos _).ne', log_exp] at hs ⊢
  -- `∫ … (1 − (Y + log u)/log t)^k = (1/log t)^k ∫ … (log t + −Y − log u)^k`
  have e : ∀ u : ℝ, u ^ (lam - 1) * exp (-u) * (1 - (Y + log u) / log t) ^ k =
      (u ^ (lam - 1) * exp (-u) * (log t + -Y - log u) ^ k) * (1 / log t) ^ k := by
    intro u
    have e0 : 1 - (Y + log u) / log t = (log t + -Y - log u) * (1 / log t) := by
      field_simp
      ring
    rw [e0, mul_pow]
    ring
  simp_rw [e]
  rw [integral_mul_const, ← hs]
  generalize (∫ z in Ioi 0, exp (-(t * exp (-Y) * exp (-z))) * exp (-(lam * z)) * z ^ k) = J
  generalize (t * exp (-Y)) ^ lam = P
  have hk1 : (log t + -Y) ^ k ≠ 0 := pow_ne_zero _ hlog'
  have hk2 : log t ^ k ≠ 0 := pow_ne_zero _ hlog
  rw [sub_eq_add_neg, div_pow, div_pow, one_pow]
  field_simp

end Laplace.Multi
