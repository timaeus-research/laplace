/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.LogGammaTails
import Laplace.OneD.IntegralRemainder

/-!
# A scaled Laplace lemma on the half line

The centred saddle lemma behind the negative chamber (Astra, round 26, §3). For a potential
`φ : ℝ → ℝ` on `(0, ∞)` with `φ(1) = 0`, a quadratic lower bound `φ(z) ≥ c₁ (z − 1)²` on
`(0, z₁]` (`z₁ > 1`), a coercivity bound `φ(z) ≥ c₂ (z − 1)^α` (`0 < α ≤ 1`) beyond `z₁`, and the
second-order limit
`φ(1 + h)/h² → κ/2`, and for scaled observables `G B w` (the observable evaluated at `z = 1 + w/√B`)
with a polynomial bound and a pointwise limit `G B w → G∞ w`,

  `√B ∫₀^∞ G B (√B (z − 1)) e^{-B φ(z)} dz → ∫_ℝ G∞ w e^{-κ w²/2} dw`
  (`tendsto_sqrt_mul_integral`).

The proof is the substitution `z = 1 + w/√B` followed by dominated convergence on `ℝ`, with the
dominating function `C (1 + |w|)ⁿ (e^{-c₁ w²} + e^{-c₂ w^α} 1_{w > 0})`. The Gaussian moments
needed downstream are `∫ w e^{-κw²/2} = 0` and `∫ w² e^{-κw²/2} = (1/κ) ∫ e^{-κw²/2}`
(`integral_mul_exp_neg_half_mul_sq`, `integral_sq_mul_exp_neg_half_mul_sq`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The dominating function `(1 + |w|)ⁿ (e^{-c₁ w²} + e^{-c₂ w^α} 1_{w>0})` is integrable. -/
theorem integrable_dominating (n : ℕ) {c₁ c₂ α : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hα : 0 < α) :
    Integrable (fun w : ℝ ↦ (1 + |w|) ^ n *
      (Real.exp (-(c₁ * w ^ 2)) + (Ioi 0).indicator (fun w ↦ Real.exp (-(c₂ * w ^ α))) w)) := by
  have hpoly : ∀ w : ℝ, (1 + |w|) ^ n ≤ 2 ^ n * (1 + |w| ^ n) := fun w ↦ by
    calc (1 + |w|) ^ n ≤ (2 * max 1 |w|) ^ n := by
          gcongr
          rcases le_total 1 |w| with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h]; linarith
      _ = 2 ^ n * max 1 |w| ^ n := by rw [mul_pow]
      _ ≤ 2 ^ n * (1 + |w| ^ n) := by
          gcongr
          rcases le_total 1 |w| with h | h
          · rw [max_eq_right h]; linarith [pow_nonneg (abs_nonneg w) n]
          · rw [max_eq_left h, one_pow]; linarith [pow_nonneg (abs_nonneg w) n]
  -- Gaussian part
  have hG : Integrable (fun w : ℝ ↦ 2 ^ n * (1 + |w| ^ n) * Real.exp (-(c₁ * w ^ 2))) := by
    have h0 := Laplace.OneD.integrable_abs_pow_mul_exp_neg_mul_sq hc₁ 0
    have hn := Laplace.OneD.integrable_abs_pow_mul_exp_neg_mul_sq hc₁ n
    simp only [pow_zero, one_mul] at h0
    refine ((h0.add hn).const_mul (2 ^ n)).congr (Filter.Eventually.of_forall fun w ↦ ?_)
    simp only [Pi.add_apply]
    ring
  -- stretched-exponential part on `(0, ∞)`
  have hE : Integrable (fun w : ℝ ↦ 2 ^ n * (1 + |w| ^ n) *
      (Ioi 0).indicator (fun w ↦ Real.exp (-(c₂ * w ^ α))) w) := by
    have h0 : IntegrableOn (fun w : ℝ ↦ w ^ (0 : ℝ) * Real.exp (-c₂ * w ^ α)) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) hα hc₂
    have hn : IntegrableOn (fun w : ℝ ↦ w ^ (n : ℝ) * Real.exp (-c₂ * w ^ α)) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith) hα hc₂
    have hsum' : IntegrableOn (fun w : ℝ ↦ 2 ^ n *
        (w ^ (0 : ℝ) * Real.exp (-c₂ * w ^ α) + w ^ (n : ℝ) * Real.exp (-c₂ * w ^ α))) (Ioi 0) :=
      (h0.add hn).const_mul _
    have hsum : IntegrableOn (fun w : ℝ ↦ 2 ^ n * (1 + |w| ^ n) * Real.exp (-(c₂ * w ^ α)))
        (Ioi 0) := by
      refine hsum'.congr_fun (fun w hw ↦ ?_) measurableSet_Ioi
      have hw : 0 < w := hw
      simp only [abs_of_pos hw, Real.rpow_zero, Real.rpow_natCast, neg_mul]
      ring
    rw [← integrable_indicator_iff measurableSet_Ioi] at hsum
    refine hsum.congr (Filter.Eventually.of_forall fun w ↦ ?_)
    by_cases hw : w ∈ Ioi (0 : ℝ)
    · simp [Set.indicator_of_mem hw]
    · simp [Set.indicator_of_notMem hw]
  have hm : Measurable fun w : ℝ ↦ (1 + |w|) ^ n *
      (Real.exp (-(c₁ * w ^ 2)) + (Ioi 0).indicator (fun w ↦ Real.exp (-(c₂ * w ^ α))) w) :=
    Measurable.mul (by fun_prop) (Measurable.add (by fun_prop)
      (Measurable.indicator (by fun_prop) measurableSet_Ioi))
  refine (hG.add hE).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun w ↦ ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs]
  have hI : 0 ≤ (Ioi 0).indicator (fun w ↦ Real.exp (-(c₂ * w ^ α))) w :=
    Set.indicator_nonneg (fun w _ ↦ (Real.exp_pos _).le) w
  have hE0 : 0 ≤ Real.exp (-(c₁ * w ^ 2)) := (Real.exp_pos _).le
  rw [abs_of_nonneg (by positivity)]
  calc (1 + |w|) ^ n * (Real.exp (-(c₁ * w ^ 2)) +
        (Ioi 0).indicator (fun w ↦ Real.exp (-(c₂ * w ^ α))) w)
      ≤ 2 ^ n * (1 + |w| ^ n) * (Real.exp (-(c₁ * w ^ 2)) +
        (Ioi 0).indicator (fun w ↦ Real.exp (-(c₂ * w ^ α))) w) :=
        mul_le_mul_of_nonneg_right (hpoly w) (by positivity)
    _ = _ := by ring

/-- **The scaled Laplace lemma on the half line.** -/
theorem tendsto_sqrt_mul_integral {φ : ℝ → ℝ} (hφm : Measurable φ) (hφ1 : φ 1 = 0) {κ c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    {z₁ : ℝ} (hz₁ : 1 < z₁)
    (hquad : ∀ z, 0 < z → z ≤ z₁ → c₁ * (z - 1) ^ 2 ≤ φ z) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hlin : ∀ z, z₁ ≤ z → c₂ * (z - 1) ^ α ≤ φ z)
    (hlim : Tendsto (fun h ↦ φ (1 + h) / h ^ 2) (𝓝[≠] 0) (𝓝 (κ / 2)))
    {G : ℝ → ℝ → ℝ} {Ginf : ℝ → ℝ} (hGm : ∀ B, Measurable (G B)) {C : ℝ} {n : ℕ}
    (hGb : ∀ B, 1 ≤ B → ∀ w, -Real.sqrt B < w → |G B w| ≤ C * (1 + |w|) ^ n)
    (hGlim : ∀ w, Tendsto (fun B ↦ G B w) atTop (𝓝 (Ginf w))) :
    Tendsto (fun B ↦ Real.sqrt B *
        ∫ z in Ioi (0 : ℝ), G B (Real.sqrt B * (z - 1)) * Real.exp (-(B * φ z))) atTop
      (𝓝 (∫ w, Ginf w * Real.exp (-(κ / 2 * w ^ 2)))) := by
  -- the scaled integrand
  set H : ℝ → ℝ → ℝ := fun B w ↦ (Ioi (-Real.sqrt B)).indicator
    (fun w ↦ G B w * Real.exp (-(B * φ (1 + w / Real.sqrt B)))) w with hH
  -- change of variables
  have hsubst : ∀ B, 0 < B → Real.sqrt B *
      (∫ z in Ioi (0 : ℝ), G B (Real.sqrt B * (z - 1)) * Real.exp (-(B * φ z))) = ∫ w, H B w := by
    intro B hB
    have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
    rw [← integral_indicator measurableSet_Ioi]
    set F : ℝ → ℝ := (Ioi (0 : ℝ)).indicator
      (fun z ↦ G B (Real.sqrt B * (z - 1)) * Real.exp (-(B * φ z))) with hF
    have e1 : (∫ z, F z) = ∫ x, F (x + 1) := (integral_add_right_eq_self F 1).symm
    have e2 : (∫ x, F (x + 1)) = (1 / Real.sqrt B) * ∫ w, F (w / Real.sqrt B + 1) := by
      have := Measure.integral_comp_mul_left (fun x ↦ F (x + 1)) (1 / Real.sqrt B)
      simp only [one_div, inv_inv, abs_of_pos hsB, smul_eq_mul] at this
      simp only [div_eq_inv_mul]
      rw [this]
      field_simp
    rw [e1, e2, ← mul_assoc, mul_one_div_cancel hsB.ne', one_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
    simp only [hF, hH]
    by_cases hw : w ∈ Ioi (-Real.sqrt B)
    · have hz : w / Real.sqrt B + 1 ∈ Ioi (0 : ℝ) := by
        have : -Real.sqrt B < w := hw
        rw [mem_Ioi]
        have : -1 < w / Real.sqrt B := by rwa [lt_div_iff₀ hsB, neg_one_mul]
        linarith
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hw]
      have : Real.sqrt B * (w / Real.sqrt B + 1 - 1) = w := by
        rw [add_sub_cancel_right]
        field_simp
      rw [this, add_comm]
    · have hw' : w ≤ -Real.sqrt B := by simpa [Set.mem_Ioi, not_lt] using hw
      have hz : w / Real.sqrt B + 1 ∉ Ioi (0 : ℝ) := by
        rw [mem_Ioi, not_lt]
        have : w / Real.sqrt B ≤ -1 := by rw [div_le_iff₀ hsB]; linarith
        linarith
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hw]
  -- dominated convergence
  have hdom := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := H) (f := fun w ↦ Ginf w * Real.exp (-(κ / 2 * w ^ 2)))
    (bound := fun w ↦ |C| * ((1 + |w|) ^ n *
      (Real.exp (-(c₁ * w ^ 2)) + (Ioi 0).indicator (fun w ↦ Real.exp (-(c₂ * w ^ α))) w)))
    (Filter.Eventually.of_forall fun B ↦ by
      simp only [hH]
      exact (((hGm B).mul (Real.measurable_exp.comp ((hφm.comp (by fun_prop)).const_mul B).neg))
        |>.indicator measurableSet_Ioi).aestronglyMeasurable)
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
      refine Filter.Eventually.of_forall fun w ↦ ?_
      have hB0 : 0 < B := by linarith
      have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB0
      have hsB1 : 1 ≤ Real.sqrt B := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt hB
      simp only [hH, Real.norm_eq_abs]
      have hI : 0 ≤ (Ioi 0).indicator (fun w ↦ Real.exp (-(c₂ * w ^ α))) w :=
        Set.indicator_nonneg (fun w _ ↦ (Real.exp_pos _).le) w
      by_cases hw : w ∈ Ioi (-Real.sqrt B)
      · rw [Set.indicator_of_mem hw, abs_mul, Real.abs_exp]
        have hw' : -Real.sqrt B < w := hw
        have hGw := hGb B hB w hw'
        have hCw : |G B w| ≤ |C| * (1 + |w|) ^ n :=
          hGw.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
        -- the exponential factor
        have hexp : Real.exp (-(B * φ (1 + w / Real.sqrt B))) ≤
            Real.exp (-(c₁ * w ^ 2)) + (Ioi 0).indicator (fun w ↦ Real.exp (-(c₂ * w ^ α))) w := by
          have hz0 : 0 < 1 + w / Real.sqrt B := by
            have : -1 < w / Real.sqrt B := by rwa [lt_div_iff₀ hsB, neg_one_mul]
            linarith
          rcases le_or_gt w ((z₁ - 1) * Real.sqrt B) with hwB | hwB
          · -- `z ≤ z₁`: quadratic bound
            have hz2 : 1 + w / Real.sqrt B ≤ z₁ := by
              have : w / Real.sqrt B ≤ z₁ - 1 := by rw [div_le_iff₀ hsB]; exact hwB
              linarith
            have := hquad _ hz0 hz2
            have e : B * (c₁ * (1 + w / Real.sqrt B - 1) ^ 2) = c₁ * w ^ 2 := by
              rw [add_sub_cancel_left, div_pow, Real.sq_sqrt hB0.le]
              field_simp
            calc Real.exp (-(B * φ (1 + w / Real.sqrt B)))
                ≤ Real.exp (-(c₁ * w ^ 2)) := by
                  rw [Real.exp_le_exp, neg_le_neg_iff, ← e]
                  exact mul_le_mul_of_nonneg_left this hB0.le
              _ ≤ _ := le_add_of_nonneg_right hI
          · -- `z > z₁`: coercivity
            have hw0 : 0 < w := lt_trans (by positivity) hwB
            have hz2 : z₁ ≤ 1 + w / Real.sqrt B := by
              have : z₁ - 1 ≤ w / Real.sqrt B := by rw [le_div_iff₀ hsB]; exact hwB.le
              linarith
            have := hlin _ hz2
            have e : B * (c₂ * (1 + w / Real.sqrt B - 1) ^ α) =
                c₂ * (B ^ (1 - α / 2) * w ^ α) := by
              rw [add_sub_cancel_left, Real.div_rpow hw0.le hsB.le, Real.sqrt_eq_rpow,
                ← Real.rpow_mul hB0.le, show 1 / 2 * α = α / 2 by ring, Real.rpow_sub hB0,
                Real.rpow_one]
              have hBα : 0 < B ^ (α / 2) := Real.rpow_pos_of_pos hB0 _
              field_simp
            have hBα1 : 1 ≤ B ^ (1 - α / 2) := Real.one_le_rpow hB (by linarith)
            have hI' : (Ioi 0).indicator (fun w ↦ Real.exp (-(c₂ * w ^ α))) w =
                Real.exp (-(c₂ * w ^ α)) := Set.indicator_of_mem hw0 _
            calc Real.exp (-(B * φ (1 + w / Real.sqrt B)))
                ≤ Real.exp (-(c₂ * w ^ α)) := by
                  rw [Real.exp_le_exp, neg_le_neg_iff]
                  calc c₂ * w ^ α ≤ c₂ * (B ^ (1 - α / 2) * w ^ α) := by
                        refine mul_le_mul_of_nonneg_left ?_ hc₂.le
                        exact le_mul_of_one_le_left (Real.rpow_nonneg hw0.le _) hBα1
                    _ = B * (c₂ * (1 + w / Real.sqrt B - 1) ^ α) := e.symm
                    _ ≤ B * φ (1 + w / Real.sqrt B) := mul_le_mul_of_nonneg_left this hB0.le
              _ ≤ _ := by rw [hI']; linarith [Real.exp_pos (-(c₁ * w ^ 2))]
        calc |G B w| * Real.exp (-(B * φ (1 + w / Real.sqrt B)))
            ≤ (|C| * (1 + |w|) ^ n) * (Real.exp (-(c₁ * w ^ 2)) +
                (Ioi 0).indicator (fun w ↦ Real.exp (-(c₂ * w ^ α))) w) :=
              mul_le_mul hCw hexp (Real.exp_pos _).le (by positivity)
          _ = _ := by ring
      · rw [Set.indicator_of_notMem hw, abs_zero]
        positivity)
    ((integrable_dominating n hc₁ hc₂ hα0).const_mul _)
    (Filter.Eventually.of_forall fun w ↦ by
      -- pointwise limit
      have hev : ∀ᶠ B in atTop, H B w = G B w * Real.exp (-(B * φ (1 + w / Real.sqrt B))) := by
        filter_upwards [eventually_gt_atTop (w ^ 2), eventually_gt_atTop (0 : ℝ)] with B hB hB0
        simp only [hH]
        rw [Set.indicator_of_mem]
        rw [mem_Ioi, neg_lt]
        calc -w ≤ |w| := neg_le_abs w
          _ = Real.sqrt (w ^ 2) := (Real.sqrt_sq_eq_abs w).symm
          _ < Real.sqrt B := Real.sqrt_lt_sqrt (sq_nonneg _) hB
      refine (Tendsto.congr' (hev.mono fun B h ↦ h.symm) ?_)
      refine (hGlim w).mul ?_
      -- `B φ(1 + w/√B) → κ w²/2`
      by_cases hw0 : w = 0
      · subst hw0
        simp only [zero_div, add_zero, hφ1, mul_zero, neg_zero, Real.exp_zero, zero_pow,
          ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
        exact tendsto_const_nhds
      have hh : Tendsto (fun B ↦ w / Real.sqrt B) atTop (𝓝[≠] 0) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · have := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul w
          simpa [div_eq_mul_inv, Function.comp_def] using this
        · filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
          exact div_ne_zero hw0 (Real.sqrt_pos.mpr hB).ne'
      have hlim' := (hlim.comp hh).const_mul (w ^ 2)
      have e : ∀ B, 0 < B → B * φ (1 + w / Real.sqrt B) =
          w ^ 2 * (φ (1 + w / Real.sqrt B) / (w / Real.sqrt B) ^ 2) := fun B hB ↦ by
        have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
        rw [div_pow, Real.sq_sqrt hB.le]
        field_simp
      have hlim'' : Tendsto (fun B ↦ B * φ (1 + w / Real.sqrt B)) atTop (𝓝 (κ / 2 * w ^ 2)) := by
        refine (hlim'.congr' ?_).trans (by rw [mul_comm])
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
        simp only [Function.comp_apply]
        exact (e B hB).symm
      exact (Real.continuous_exp.tendsto _).comp hlim''.neg)
  refine hdom.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
  exact (hsubst B hB).symm


/-! ### Gaussian moments -/

/-- `∫ e^{-κ w²/2} dw = √2 √π/√κ`. -/
theorem integral_exp_neg_half_mul_sq {κ : ℝ} (hκ : 0 < κ) :
    ∫ w : ℝ, Real.exp (-(κ / 2 * w ^ 2)) = Real.sqrt 2 * Real.sqrt Real.pi / Real.sqrt κ := by
  have h := Laplace.OneD.integral_pow_mul_exp_neg_sq_half 0
  norm_num [Nat.doubleFactorial] at h
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have := Measure.integral_comp_mul_left (fun x : ℝ ↦ Real.exp (-x ^ 2 / 2)) (Real.sqrt κ)
  rw [h, abs_of_pos (inv_pos.mpr hs), smul_eq_mul] at this
  have e : ∀ w : ℝ, Real.exp (-(κ / 2 * w ^ 2)) = Real.exp (-(Real.sqrt κ * w) ^ 2 / 2) :=
    fun w ↦ by
    congr 1
    rw [mul_pow, Real.sq_sqrt hκ.le]
    ring
  simp_rw [e]
  rw [this]
  ring

/-- `∫ w e^{-κ w²/2} dw = 0`. -/
theorem integral_mul_exp_neg_half_mul_sq (κ : ℝ) :
    ∫ w : ℝ, w * Real.exp (-(κ / 2 * w ^ 2)) = 0 := by
  have h := integral_neg_eq_self (fun w : ℝ ↦ w * Real.exp (-(κ / 2 * w ^ 2))) volume
  simp only [neg_sq, neg_mul] at h
  rw [integral_neg] at h
  linarith

/-- `∫ w² e^{-κ w²/2} dw = (1/κ) ∫ e^{-κ w²/2} dw`. -/
theorem integral_sq_mul_exp_neg_half_mul_sq {κ : ℝ} (hκ : 0 < κ) :
    ∫ w : ℝ, w ^ 2 * Real.exp (-(κ / 2 * w ^ 2)) =
      (1 / κ) * ∫ w : ℝ, Real.exp (-(κ / 2 * w ^ 2)) := by
  have h := Laplace.OneD.integral_pow_mul_exp_neg_sq_half 1
  norm_num [Nat.doubleFactorial] at h
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have := Measure.integral_comp_mul_left (fun x : ℝ ↦ x ^ 2 * Real.exp (-x ^ 2 / 2)) (Real.sqrt κ)
  rw [h, abs_of_pos (inv_pos.mpr hs), smul_eq_mul] at this
  have e : ∀ w : ℝ, w ^ 2 * Real.exp (-(κ / 2 * w ^ 2)) =
      (1 / κ) * ((Real.sqrt κ * w) ^ 2 * Real.exp (-(Real.sqrt κ * w) ^ 2 / 2)) := fun w ↦ by
    rw [mul_pow, Real.sq_sqrt hκ.le]
    have : Real.exp (-(κ / 2 * w ^ 2)) = Real.exp (-(κ * w ^ 2) / 2) := by congr 1; ring
    rw [this]
    field_simp
  simp_rw [e]
  rw [MeasureTheory.integral_const_mul, this, integral_exp_neg_half_mul_sq hκ]
  have hk : Real.sqrt κ ≠ 0 := hs.ne'
  field_simp

end Laplace.Multi
