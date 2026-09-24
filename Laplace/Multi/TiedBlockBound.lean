/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LogSectorTied
import Laplace.Multi.LogModel

/-!
# An all-scale bound on the tied-block integral

The core integral `J_n(λ, s) = ∫₀^∞ e^{-s e^{-z}} e^{-λ z} z^n dz` of the logarithmic sector is
bounded, uniformly in `s > 0`, by `M s^{-λ} (1 + log⁺ s)^n` (`coreJ_le_bound`): for `s ≥ e` this
is the identity `s^λ J = ∫₀^s u^{λ-1} e^{-u} (log s − log u)^n du` with
`log s − log u ≤ log s (1 + |log u|)`, and for `s < e` the integral is at most its value at `s = 0`.
Hence the tied-block integral of `LogSectorTied` satisfies `TB(s) ≤ M' s^{-λ} (1 + log⁺ s)^k`
(`tiedBlockIntegral_le_bound`), the estimate that makes a dominated-convergence argument over the
untied coordinates of a partially tied face possible.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

/-- The core integral of the logarithmic sector. -/
noncomputable def coreJ (lam : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ z in Ioi 0, exp (-(t * exp (-z))) * exp (-(lam * z)) * z ^ n

theorem coreJ_nonneg (lam : ℝ) (n : ℕ) (t : ℝ) : 0 ≤ coreJ lam n t :=
  setIntegral_nonneg measurableSet_Ioi fun z hz ↦ by
    have : 0 < z := hz
    positivity

/-- The `t = 0` majorant `e^{-λz} z^n` in the form of the Gamma integrability lemma. -/
theorem integrableOn_exp_neg_mul_pow {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    IntegrableOn (fun z : ℝ ↦ exp (-(lam * z)) * z ^ n) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := lam)
    (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) one_pos hlam
  refine h.congr_fun (fun z _ ↦ ?_) measurableSet_Ioi
  beta_reduce
  rw [Real.rpow_natCast, Real.rpow_one, neg_mul, mul_comm]

theorem integrableOn_coreJ_integrand {lam : ℝ} (hlam : 0 < lam) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun z : ℝ ↦ exp (-(t * exp (-z))) * exp (-(lam * z)) * z ^ n) (Ioi 0) := by
  refine (integrableOn_exp_neg_mul_pow hlam n).mono' ?_ ?_
  · exact (((measurable_const.mul measurable_neg.exp).neg.exp.mul
      (measurable_const.mul measurable_id).neg.exp).mul (measurable_id.pow_const n))
      |>.aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun z hz ↦ ?_
    have hz : 0 < z := hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc exp (-(t * exp (-z))) * exp (-(lam * z)) * z ^ n
        ≤ 1 * exp (-(lam * z)) * z ^ n := by
          gcongr
          exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht (exp_pos _).le))
      _ = exp (-(lam * z)) * z ^ n := by rw [one_mul]

/-- The core integral is bounded by its `t = 0` value. -/
theorem coreJ_le_const {lam : ℝ} (hlam : 0 < lam) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    coreJ lam n t ≤ ∫ z in Ioi 0, exp (-(lam * z)) * z ^ n := by
  unfold coreJ
  refine setIntegral_mono_on (integrableOn_coreJ_integrand hlam n ht)
    (integrableOn_exp_neg_mul_pow hlam n) measurableSet_Ioi fun z hz ↦ ?_
  have hz : 0 < z := hz
  calc exp (-(t * exp (-z))) * exp (-(lam * z)) * z ^ n
      ≤ 1 * exp (-(lam * z)) * z ^ n := by
        gcongr
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht (exp_pos _).le))
    _ = exp (-(lam * z)) * z ^ n := by rw [one_mul]

/-- The growth bound for `t ≥ e`: `J ≤ M_n t^{-λ} (log t)^n` with the log-moment constant. -/
theorem coreJ_le_growth {lam : ℝ} (hlam : 0 < lam) (n : ℕ) {t : ℝ} (ht : exp 1 ≤ t) :
    coreJ lam n t ≤
      (∫ u in Ioi 0, u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ n) * t ^ (-lam) * log t ^ n := by
  have ht0 : 0 < t := (exp_pos 1).trans_le ht
  have hlogt : 1 ≤ log t := by
    rw [← log_exp 1]
    exact log_le_log (exp_pos 1) ht
  have hlog0 : 0 < log t := by linarith
  have hid := rpow_mul_integral_logSector ht0 lam n
  -- bound the substituted integral
  have hbound : ∫ u in Ioo 0 t, u ^ (lam - 1) * exp (-u) * (log t - log u) ^ n ≤
      log t ^ n * ∫ u in Ioi 0, u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ n := by
    rw [← integral_const_mul]
    have hI : IntegrableOn (fun u ↦ log t ^ n * (u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ n))
        (Ioi 0) := (integrableOn_gammaLog hlam n).const_mul _
    calc ∫ u in Ioo 0 t, u ^ (lam - 1) * exp (-u) * (log t - log u) ^ n
        ≤ ∫ u in Ioo 0 t, log t ^ n * (u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ n) := by
          refine setIntegral_mono_on ?_ (hI.mono_set Ioo_subset_Ioi_self) measurableSet_Ioo
            fun u hu ↦ ?_
          · refine (hI.mono_set Ioo_subset_Ioi_self).mono' ?_ ?_
            · exact (((measurable_id.pow_const _).mul measurable_neg.exp).mul
                ((measurable_const.sub Real.measurable_log).pow_const _)).aestronglyMeasurable
            · rw [ae_restrict_iff' measurableSet_Ioo]
              refine ae_of_all _ fun u hu ↦ ?_
              have hu0 : 0 < u := hu.1
              have hlu : log u ≤ log t := log_le_log hu.1 hu.2.le
              have hnn : 0 ≤ u ^ (lam - 1) * exp (-u) := by positivity
              rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (pow_nonneg (by linarith) _))]
              have hle : log t - log u ≤ log t * (1 + |log u|) := by
                have h1 : -log u ≤ |log u| := neg_le_abs _
                have h2 : |log u| ≤ log t * |log u| := le_mul_of_one_le_left (abs_nonneg _) hlogt
                nlinarith
              calc u ^ (lam - 1) * exp (-u) * (log t - log u) ^ n
                  ≤ u ^ (lam - 1) * exp (-u) * (log t * (1 + |log u|)) ^ n :=
                    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hle n) hnn
                _ = log t ^ n * (u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ n) := by
                    rw [mul_pow]; ring
          · have hu0 : 0 < u := hu.1
            have hlu : log u ≤ log t := log_le_log hu.1 hu.2.le
            have hnn : 0 ≤ u ^ (lam - 1) * exp (-u) := by positivity
            have hle : log t - log u ≤ log t * (1 + |log u|) := by
              have h1 : -log u ≤ |log u| := neg_le_abs _
              have h2 : |log u| ≤ log t * |log u| := le_mul_of_one_le_left (abs_nonneg _) hlogt
              nlinarith
            calc u ^ (lam - 1) * exp (-u) * (log t - log u) ^ n
                ≤ u ^ (lam - 1) * exp (-u) * (log t * (1 + |log u|)) ^ n :=
                  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hle n) hnn
              _ = log t ^ n * (u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ n) := by
                  rw [mul_pow]; ring
      _ ≤ ∫ u in Ioi 0, log t ^ n * (u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ n) := by
          refine setIntegral_mono_set hI ?_ (Eventually.of_forall Ioo_subset_Ioi_self)
          rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
          refine ae_of_all _ fun u hu ↦ ?_
          have : 0 < u := hu
          positivity
  have hpos : 0 < t ^ lam := rpow_pos_of_pos ht0 _
  have hJ : coreJ lam n t = t ^ (-lam) * (t ^ lam * coreJ lam n t) := by
    rw [← mul_assoc, ← Real.rpow_add ht0, neg_add_cancel, Real.rpow_zero, one_mul]
  rw [hJ]
  unfold coreJ
  rw [hid]
  calc t ^ (-lam) * ∫ u in Ioo 0 t, u ^ (lam - 1) * exp (-u) * (log t - log u) ^ n
      ≤ t ^ (-lam) * (log t ^ n * ∫ u in Ioi 0, u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ n) :=
        mul_le_mul_of_nonneg_left hbound (rpow_pos_of_pos ht0 _).le
    _ = _ := by ring

/-- **The all-scale bound on the core integral**: `J_n(λ, s) ≤ M s^{-λ} (1 + log⁺ s)^n`. -/
theorem coreJ_le_bound {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 0 < s →
      coreJ lam n s ≤ M * s ^ (-lam) * (1 + max 0 (log s)) ^ n := by
  set M₀ : ℝ := ∫ z in Ioi 0, exp (-(lam * z)) * z ^ n with hM₀
  set Mn : ℝ := ∫ u in Ioi 0, u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ n with hMn
  have hM₀0 : 0 ≤ M₀ := setIntegral_nonneg measurableSet_Ioi fun z hz ↦ by
    have : 0 < z := hz
    positivity
  have hMn0 : 0 ≤ Mn := setIntegral_nonneg measurableSet_Ioi fun u hu ↦ by
    have : 0 < u := hu
    positivity
  refine ⟨max (M₀ * exp lam) Mn, le_max_of_le_right hMn0, fun s hs ↦ ?_⟩
  have hspos : 0 < s ^ (-lam) := rpow_pos_of_pos hs _
  have hpow1 : 1 ≤ (1 + max 0 (log s)) ^ n :=
    one_le_pow₀ (by linarith [le_max_left 0 (log s)])
  rcases le_or_gt (exp 1) s with hse | hse
  · have hlog : 0 ≤ log s := log_nonneg ((Real.one_le_exp zero_le_one).trans hse)
    calc coreJ lam n s ≤ Mn * s ^ (-lam) * log s ^ n := coreJ_le_growth hlam n hse
      _ ≤ max (M₀ * exp lam) Mn * s ^ (-lam) * (1 + max 0 (log s)) ^ n := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right _ _) hspos.le)
            (pow_le_pow_left₀ hlog (by linarith [le_max_right 0 (log s)]) n)
            (pow_nonneg hlog _) (by positivity)
  · have h1 : coreJ lam n s ≤ M₀ := coreJ_le_const hlam n hs.le
    have h2 : M₀ ≤ M₀ * exp lam * s ^ (-lam) := by
      have : exp (-lam) ≤ s ^ (-lam) := by
        rw [Real.rpow_neg hs.le, Real.exp_neg]
        refine inv_anti₀ (rpow_pos_of_pos hs _) ?_
        calc s ^ lam ≤ (exp 1) ^ lam := Real.rpow_le_rpow hs.le hse.le hlam.le
          _ = exp lam := by rw [← Real.exp_mul, one_mul]
      calc M₀ = M₀ * exp lam * exp (-lam) := by
            rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        _ ≤ M₀ * exp lam * s ^ (-lam) :=
            mul_le_mul_of_nonneg_left this (mul_nonneg hM₀0 (exp_pos _).le)
    calc coreJ lam n s ≤ M₀ := h1
      _ ≤ M₀ * exp lam * s ^ (-lam) := h2
      _ ≤ max (M₀ * exp lam) Mn * s ^ (-lam) * (1 + max 0 (log s)) ^ n := by
          calc M₀ * exp lam * s ^ (-lam) = M₀ * exp lam * s ^ (-lam) * 1 := (mul_one _).symm
            _ ≤ max (M₀ * exp lam) Mn * s ^ (-lam) * (1 + max 0 (log s)) ^ n :=
              mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hspos.le) hpow1
                zero_le_one (by positivity)

/-- The tied-block integral as a multiple of the core integral. -/
theorem tiedBlockIntegral_eq_coreJ {k : ℕ} {A h : Fin (k + 1) → ℝ} (hA : ∀ i, 0 < A i) {lam : ℝ}
    (htied : ∀ i, (h i + 1) / A i = lam) (t : ℝ) :
    tiedBlockIntegral A h t = (∏ i, 1 / A i) * (1 / (k.factorial : ℝ)) * coreJ lam k t :=
  tiedBlockIntegral_eq hA htied t

/-- **The all-scale bound on the tied-block integral.** -/
theorem tiedBlockIntegral_le_bound {k : ℕ} {A h : Fin (k + 1) → ℝ} (hA : ∀ i, 0 < A i) {lam : ℝ}
    (hlam : 0 < lam) (htied : ∀ i, (h i + 1) / A i = lam) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 0 < s →
      tiedBlockIntegral A h s ≤ M * s ^ (-lam) * (1 + max 0 (log s)) ^ k := by
  obtain ⟨M, hM0, hM⟩ := coreJ_le_bound hlam k
  have hc : 0 ≤ (∏ i, 1 / A i) * (1 / (k.factorial : ℝ)) :=
    mul_nonneg (Finset.prod_nonneg fun i _ ↦ (one_div_pos.mpr (hA i)).le) (by positivity)
  refine ⟨(∏ i, 1 / A i) * (1 / (k.factorial : ℝ)) * M, mul_nonneg hc hM0, fun s hs ↦ ?_⟩
  rw [tiedBlockIntegral_eq_coreJ hA htied]
  calc (∏ i, 1 / A i) * (1 / (k.factorial : ℝ)) * coreJ lam k s
      ≤ (∏ i, 1 / A i) * (1 / (k.factorial : ℝ)) * (M * s ^ (-lam) * (1 + max 0 (log s)) ^ k) :=
        mul_le_mul_of_nonneg_left (hM s hs) hc
    _ = _ := by ring

end Laplace.Multi
