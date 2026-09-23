/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# The one-dimensional core of the logarithmic-sector asymptotics

For `λ > 0` and `n : ℕ`,
`t^λ (log t)^{-n} ∫₀^∞ exp(−t e^{−z}) e^{−λ z} z^n dz → Γ(λ)` (`tendsto_logSector_core`). This is
the integral left after the logarithmic coordinates `y_i = −A_i log x_i` and the simplex reduction
in the single-monomial power–log theorem (Astra, `research_kernel_asymptotics_v1`): the
substitution `u = t e^{−z}` turns it into `t^{-λ} ∫₀^t u^{λ−1} e^{−u} (log t − log u)^n du`, and
dominated convergence (envelope `u^{λ−1} e^{−u} (1 + |log u|)^n`, integrable by comparison with
three Gamma integrands, `integrableOn_gammaLog`) gives the Gamma integral.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

/-- `(a + b + c)^n ≤ 3^n (a^n + b^n + c^n)` for nonnegative reals. -/
theorem add_add_pow_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (n : ℕ) :
    (a + b + c) ^ n ≤ 3 ^ n * (a ^ n + b ^ n + c ^ n) := by
  set m := max (max a b) c with hm
  have hm0 : 0 ≤ m := le_trans ha ((le_max_left a b).trans (le_max_left _ c))
  have h1 : a + b + c ≤ 3 * m := by
    have := le_max_left (max a b) c
    have := le_max_right (max a b) c
    have := le_max_left a b
    have := le_max_right a b
    linarith
  have h2 : m ^ n ≤ a ^ n + b ^ n + c ^ n := by
    have hpa : 0 ≤ a ^ n := pow_nonneg ha n
    have hpb : 0 ≤ b ^ n := pow_nonneg hb n
    have hpc : 0 ≤ c ^ n := pow_nonneg hc n
    rcases max_cases (max a b) c with ⟨h, -⟩ | ⟨h, -⟩
    · rcases max_cases a b with ⟨h', -⟩ | ⟨h', -⟩
      · rw [hm, h, h']; linarith
      · rw [hm, h, h']; linarith
    · rw [hm, h]; linarith
  calc (a + b + c) ^ n ≤ (3 * m) ^ n := pow_le_pow_left₀ (by linarith) h1 n
    _ = 3 ^ n * m ^ n := mul_pow 3 m n
    _ ≤ 3 ^ n * (a ^ n + b ^ n + c ^ n) := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `1 + |log u| ≤ 1 + u^{-δ}/δ + u` for `u > 0`, `δ > 0`. -/
theorem one_add_abs_log_le {u δ : ℝ} (hu : 0 < u) (hδ : 0 < δ) :
    1 + |log u| ≤ 1 + u ^ (-δ) / δ + u := by
  rcases le_or_gt u 1 with h | h
  · have hlog : log u ≤ 0 := log_nonpos hu.le h
    rw [abs_of_nonpos hlog]
    have : log (u⁻¹) ≤ (u⁻¹) ^ δ / δ := log_le_rpow_div (inv_nonneg.mpr hu.le) hδ
    rw [log_inv, Real.inv_rpow hu.le, ← Real.rpow_neg hu.le] at this
    linarith
  · have hlog : 0 ≤ log u := log_nonneg h.le
    rw [abs_of_nonneg hlog]
    have := log_le_sub_one_of_pos hu
    have : 0 ≤ u ^ (-δ) / δ := div_nonneg (Real.rpow_nonneg hu.le _) hδ.le
    linarith

/-- Gamma-type integrability with a logarithmic moment. -/
theorem integrableOn_gammaLog {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    IntegrableOn (fun u ↦ u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ n) (Ioi 0) := by
  set δ : ℝ := lam / (2 * (n + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hnδ : (n : ℝ) * δ < lam := by
    rw [hδdef]
    have : (n : ℝ) < 2 * (n + 1) := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  -- the three Gamma integrands
  have hG1 : IntegrableOn (fun u ↦ exp (-u) * u ^ (lam - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent hlam
  have hG2 : IntegrableOn (fun u ↦ exp (-u) * u ^ (lam - n * δ - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by linarith)
  have hG3 : IntegrableOn (fun u ↦ exp (-u) * u ^ (lam + n - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by positivity)
  have hbound : IntegrableOn (fun u ↦ 3 ^ n * (exp (-u) * u ^ (lam - 1)) +
      3 ^ n * δ ^ (-(n : ℝ)) * (exp (-u) * u ^ (lam - n * δ - 1)) +
      3 ^ n * (exp (-u) * u ^ (lam + n - 1))) (Ioi 0) :=
    ((hG1.const_mul _).add (hG2.const_mul _)).add (hG3.const_mul _)
  refine hbound.mono' ?_ ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    exact ((measurable_id.pow_const _).mul (measurable_neg.exp)).mul
      ((measurable_const.add Real.measurable_log.abs).pow_const _)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun u hu ↦ ?_
    have hu : 0 < u := hu
    have hpos : 0 ≤ u ^ (lam - 1) * exp (-u) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ n
        ≤ u ^ (lam - 1) * exp (-u) * (1 + u ^ (-δ) / δ + u) ^ n :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (one_add_abs_log_le hu hδ) n) hpos
      _ ≤ u ^ (lam - 1) * exp (-u) * (3 ^ n * (1 ^ n + (u ^ (-δ) / δ) ^ n + u ^ n)) :=
          mul_le_mul_of_nonneg_left
            (add_add_pow_le zero_le_one (by positivity) hu.le n) hpos
      _ = 3 ^ n * (exp (-u) * u ^ (lam - 1)) +
          3 ^ n * δ ^ (-(n : ℝ)) * (exp (-u) * u ^ (lam - n * δ - 1)) +
          3 ^ n * (exp (-u) * u ^ (lam + n - 1)) := by
          have e1 : (u ^ (-δ) / δ) ^ n = δ ^ (-(n : ℝ)) * u ^ (-(n * δ)) := by
            rw [div_pow, div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_mul hu.le,
              ← Real.rpow_natCast δ, ← Real.rpow_neg hδ.le, mul_comm]
            congr 2
            ring
          have e2 : u ^ (lam - 1) * u ^ (-(n * δ)) = u ^ (lam - n * δ - 1) := by
            rw [← Real.rpow_add hu]; congr 1; ring
          have e3 : u ^ (lam - 1) * u ^ n = u ^ (lam + n - 1) := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hu]; congr 1; ring
          rw [e1, one_pow]
          calc u ^ (lam - 1) * exp (-u) * (3 ^ n * (1 + δ ^ (-(n : ℝ)) * u ^ (-(n * δ)) + u ^ n))
              = 3 ^ n * (exp (-u) * u ^ (lam - 1)) +
                3 ^ n * δ ^ (-(n : ℝ)) * (exp (-u) * (u ^ (lam - 1) * u ^ (-(n * δ)))) +
                3 ^ n * (exp (-u) * (u ^ (lam - 1) * u ^ n)) := by ring
            _ = _ := by rw [e2, e3]

/-- The image of the positive half-line under `z ↦ t e^{−z}` is `(0, t)`. -/
theorem image_mul_exp_neg_Ioi {t : ℝ} (ht : 0 < t) :
    (fun z : ℝ ↦ t * exp (-z)) '' Ioi 0 = Ioo 0 t := by
  ext u
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz : 0 < z := hz
    refine ⟨by positivity, ?_⟩
    have : exp (-z) < 1 := by
      calc exp (-z) < exp 0 := Real.exp_lt_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
    nlinarith
  · rintro ⟨hu0, hut⟩
    refine ⟨log (t / u), ?_, ?_⟩
    · exact log_pos ((one_lt_div hu0).mpr hut)
    · simp only
      rw [← log_inv, exp_log (inv_pos.mpr (div_pos ht hu0)), inv_div, mul_div_cancel₀ _ ht.ne']

/-- The substitution `u = t e^{−z}`:
`t^λ ∫₀^∞ e^{−t e^{−z}} e^{−λ z} z^n dz = ∫₀^t u^{λ−1} e^{−u} (log t − log u)^n du`. -/
theorem rpow_mul_integral_logSector {t : ℝ} (ht : 0 < t) (lam : ℝ) (n : ℕ) :
    t ^ lam * ∫ z in Ioi 0, exp (-(t * exp (-z))) * exp (-(lam * z)) * z ^ n =
      ∫ u in Ioo 0 t, u ^ (lam - 1) * exp (-u) * (log t - log u) ^ n := by
  have hder : ∀ z ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun z ↦ t * exp (-z)) (-(t * exp (-z)))
      (Ioi 0) z := fun z _ ↦ by
    have := ((hasDerivAt_neg z).exp).const_mul t
    simpa [mul_neg] using this.hasDerivWithinAt
  have hinj : InjOn (fun z : ℝ ↦ t * exp (-z)) (Ioi 0) := by
    intro z₁ _ z₂ _ h
    have h' : exp (-z₁) = exp (-z₂) := mul_left_cancel₀ ht.ne' h
    exact neg_injective (exp_injective h')
  rw [← image_mul_exp_neg_Ioi ht, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder
    hinj, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun z hz ↦ ?_
  have hz : 0 < z := hz
  simp only [smul_eq_mul]
  have hte : 0 < t * exp (-z) := by positivity
  have e2 : exp (-(lam * z)) = exp (-z) * exp (-z * (lam - 1)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : log t - (log t + -z) = z := by ring
  rw [abs_neg, abs_of_pos hte, log_mul ht.ne' (exp_pos _).ne', log_exp, e3,
    Real.mul_rpow ht.le (exp_pos _).le, ← Real.exp_mul, Real.rpow_sub_one ht.ne', e2]
  field_simp

/-- **The core limit.** `t^λ (log t)^{-n} ∫₀^∞ e^{−t e^{−z}} e^{−λ z} z^n dz → Γ(λ)`. -/
theorem tendsto_logSector_core {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    Tendsto (fun t ↦ t ^ lam / log t ^ n *
      ∫ z in Ioi 0, exp (-(t * exp (-z))) * exp (-(lam * z)) * z ^ n) atTop (𝓝 (Gamma lam)) := by
  have hlim : Tendsto (fun t ↦ ∫ u, (Ioo 0 t).indicator
      (fun u ↦ u ^ (lam - 1) * exp (-u) * (1 - log u / log t) ^ n) u) atTop
      (𝓝 (∫ u, (Ioi 0).indicator (fun u ↦ exp (-u) * u ^ (lam - 1)) u)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      ((Ioi 0).indicator (fun u ↦ u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ n)) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun t ↦ Measurable.aestronglyMeasurable ?_
      exact (((measurable_id.pow_const _).mul measurable_neg.exp).mul
        ((measurable_const.sub (Real.measurable_log.div_const _)).pow_const _)).indicator
        measurableSet_Ioo
    · filter_upwards [eventually_ge_atTop (exp 1)] with t ht
      refine Eventually.of_forall fun u ↦ ?_
      have hlogt : 1 ≤ log t := by
        rw [← log_exp 1]
        exact log_le_log (exp_pos 1) ht
      by_cases hu : u ∈ Ioo 0 t
      · rw [indicator_of_mem hu, indicator_of_mem (mem_Ioi.mpr hu.1), Real.norm_eq_abs, abs_mul,
          abs_mul, abs_of_nonneg (rpow_nonneg hu.1.le _), abs_of_nonneg (exp_pos _).le, abs_pow]
        have hcalc : |1 - log u / log t| ≤ 1 + |log u| := by
          calc |1 - log u / log t| ≤ |1| + |log u / log t| := abs_sub _ _
            _ = 1 + |log u| / log t := by
              rw [abs_one, abs_div, abs_of_pos (show (0 : ℝ) < log t by linarith)]
            _ ≤ 1 + |log u| := by
              have := div_le_self (abs_nonneg (log u)) hlogt
              linarith
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hcalc n)
          (mul_nonneg (rpow_nonneg hu.1.le _) (exp_pos _).le)
      · rw [indicator_of_notMem hu, norm_zero]
        refine indicator_nonneg (fun u hu ↦ ?_) _
        exact mul_nonneg (mul_nonneg (rpow_nonneg (le_of_lt hu) _) (exp_pos _).le)
          (pow_nonneg (by positivity) _)
    · exact (integrable_indicator_iff measurableSet_Ioi).mpr (integrableOn_gammaLog hlam n)
    · refine Eventually.of_forall fun u ↦ ?_
      by_cases hu : 0 < u
      · rw [indicator_of_mem (mem_Ioi.mpr hu), mul_comm (exp (-u))]
        have h1 : Tendsto (fun t ↦ u ^ (lam - 1) * exp (-u) * (1 - log u / log t) ^ n) atTop
            (𝓝 (u ^ (lam - 1) * exp (-u) * (1 - 0) ^ n)) :=
          tendsto_const_nhds.mul
            ((tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)).pow n)
        rw [sub_zero, one_pow, mul_one] at h1
        refine h1.congr' ?_
        filter_upwards [eventually_gt_atTop u] with t ht
        rw [indicator_of_mem (show u ∈ Ioo 0 t from ⟨hu, ht⟩)]
      · have h0 : ∀ t : ℝ, (Ioo 0 t).indicator
            (fun u ↦ u ^ (lam - 1) * exp (-u) * (1 - log u / log t) ^ n) u = 0 :=
          fun t ↦ indicator_of_notMem (fun h ↦ hu h.1) _
        rw [indicator_of_notMem (show u ∉ Ioi 0 from hu)]
        simp only [h0]
        exact tendsto_const_nhds
  rw [integral_indicator measurableSet_Ioi, ← Gamma_eq_integral hlam] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have hlog : 0 < log t := log_pos ht
  rw [integral_indicator measurableSet_Ioo, div_mul_eq_mul_div,
    rpow_mul_integral_logSector (by linarith) lam n, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioo fun u _ ↦ ?_
  rw [mul_div_assoc, ← div_pow, sub_div, div_self hlog.ne']

end Laplace.Multi
