/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.ProductDensity
import Laplace.Grammar.QuotientCalculus
import Laplace.Grammar.LogInsertions

/-!
# The general-`λ` Gamma/log asymptotic

The recursive product density of `ProductDensity.lean` reduces the `d`-fold monomial box
integral to a single weighted integral

  `∫₀¹ z^{λ-1} (-log z)^m e^{-βNz} dz`.

This file computes its large-`N` asymptotic:

  `∫₀¹ z^{λ-1} (-log z)^m e^{-βNz} dz ~ Γ(λ) β^{-λ} N^{-λ} (log N)^m`.

The proof substitutes `t = Nz`, expands `(log N - log t)^m` binomially, and shows every term
other than the top power of `log N` is `O((log N)^{m-1})` because the tail integrals
`∫₀^N t^{λ-1} (-log t)^j e^{-βt} dt` are uniformly bounded by the `(0,∞)`-integrable envelope
`|log t|^j t^{λ-1} e^{-βt}` (`log_pow_fluctuation_integrableOn`). The `j = 0` tail integral
converges to the Gamma integral `Γ(λ) β^{-λ}`.

The result is packaged both as a `Tendsto` for the normalised ratio and as an
`Asymptotics.IsEquivalent` against `powLog (Γ(λ) β^{-λ}) λ m`, so that the quotient calculus of
`QuotientCalculus.lean` applies directly; a Lebesgue-integral bridge connects it to the
`ENNReal`-valued product density.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Laplace.Grammar

/-- The weighted Gamma/log integral `∫₀¹ z^{λ-1} (-log z)^m e^{-βNz} dz`. -/
noncomputable def gammaLogIntegral (l : ℝ) (m : ℕ) (β N : ℝ) : ℝ :=
  ∫ z in Ioc (0 : ℝ) 1, logDensity l m z * Real.exp (-(β * N * z))

/-- The truncated tail integral `∫₀^N t^{λ-1} (-log t)^i e^{-βt} dt`. -/
noncomputable def logTailIntegral (l β : ℝ) (i : ℕ) (N : ℝ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) N, t ^ (l - 1) * (-Real.log t) ^ i * Real.exp (-(β * t))

/-- The Gamma integral: `∫₀^∞ t^{λ-1} e^{-βt} dt = Γ(λ) β^{-λ}`. -/
theorem integral_rpow_mul_exp_neg_mul (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) :
    ∫ t in Ioi (0 : ℝ), t ^ (l - 1) * Real.exp (-(β * t)) = Real.Gamma l * β ^ (-l) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := l - 1) (b := β) one_pos
    (by linarith) hβ
  simp only [Real.rpow_one, sub_add_cancel, div_one, neg_mul] at h
  rw [h]
  ring

/-- The envelope `|log t|^i t^{λ-1} e^{-βt}` is integrable on `(0, ∞)`. -/
theorem logTail_envelope_integrableOn (l β : ℝ) (i : ℕ) (hl : 0 < l) (hβ : 0 < β) :
    IntegrableOn (fun t => |Real.log t| ^ i * t ^ (l - 1) * Real.exp (-(β * t))) (Ioi 0) := by
  simpa using log_pow_fluctuation_integrableOn β l 0 i hβ hl

theorem logTail_norm_eq (l β : ℝ) (i : ℕ) (t : ℝ) (ht : 0 < t) :
    ‖t ^ (l - 1) * (-Real.log t) ^ i * Real.exp (-(β * t))‖ =
      |Real.log t| ^ i * t ^ (l - 1) * Real.exp (-(β * t)) := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg,
    abs_of_nonneg (Real.rpow_nonneg ht.le _), abs_of_pos (Real.exp_pos _)]
  ring

/-- The tail integrand is integrable on `(0, ∞)`. -/
theorem logTail_integrableOn (l β : ℝ) (i : ℕ) (hl : 0 < l) (hβ : 0 < β) :
    IntegrableOn (fun t => t ^ (l - 1) * (-Real.log t) ^ i * Real.exp (-(β * t))) (Ioi 0) := by
  have hmeas : Measurable fun t : ℝ => t ^ (l - 1) * (-Real.log t) ^ i * Real.exp (-(β * t)) := by
    fun_prop
  refine (logTail_envelope_integrableOn l β i hl hβ).mono' hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  exact (logTail_norm_eq l β i t ht).le

/-- Uniform bound on the truncated tail integrals by the full envelope integral. -/
theorem abs_logTailIntegral_le (l β : ℝ) (i : ℕ) (hl : 0 < l) (hβ : 0 < β) (N : ℝ) :
    |logTailIntegral l β i N| ≤
      ∫ t in Ioi (0 : ℝ), |Real.log t| ^ i * t ^ (l - 1) * Real.exp (-(β * t)) := by
  have henv := logTail_envelope_integrableOn l β i hl hβ
  unfold logTailIntegral
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (henv.mono_set Ioc_subset_Ioi_self) ?_).trans ?_
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
    exact (logTail_norm_eq l β i t ht.1).le
  · refine setIntegral_mono_set henv ?_ (Eventually.of_forall fun t ht => Ioc_subset_Ioi_self ht)
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    exact mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg ht.le _))
      (Real.exp_pos _).le

/-- **Substitution `t = Nz`**: the Gamma/log integral is `N^{-λ}` times the truncated integral
of `t^{λ-1} (log N - log t)^m e^{-βt}` over `(0, N]`. -/
theorem gammaLogIntegral_eq_scaled (l : ℝ) (m : ℕ) (β N : ℝ) (hN : 0 < N) :
    gammaLogIntegral l m β N =
      N ^ (-l) * ∫ t in Ioc (0 : ℝ) N,
        t ^ (l - 1) * (Real.log N - Real.log t) ^ m * Real.exp (-(β * t)) := by
  unfold gammaLogIntegral
  set F : ℝ → ℝ := fun t => logDensity l m (t / N) * Real.exp (-(β * t)) with hF
  have h1 : (fun z => logDensity l m z * Real.exp (-(β * N * z))) = fun z => F (N * z) := by
    funext z
    simp only [hF]
    rw [mul_div_cancel_left₀ _ hN.ne', mul_assoc]
  rw [h1, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_mul_left F hN.ne', mul_zero, mul_one,
    intervalIntegral.integral_of_le hN.le, smul_eq_mul]
  have h2 : ∫ t in Ioc (0 : ℝ) N, F t = N ^ (1 - l) * ∫ t in Ioc (0 : ℝ) N,
      t ^ (l - 1) * (Real.log N - Real.log t) ^ m * Real.exp (-(β * t)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    simp only [hF, logDensity]
    rw [Real.div_rpow ht.1.le hN.le, Real.log_div ht.1.ne' hN.ne', neg_sub,
      show N ^ (1 - l) = (N ^ (l - 1))⁻¹ by rw [← Real.rpow_neg hN.le, neg_sub]]
    ring
  have h3 : N ^ (-l) = N⁻¹ * N ^ (1 - l) := by
    rw [show -l = (-1 : ℝ) + (1 - l) by ring, Real.rpow_add hN, Real.rpow_neg hN.le,
      Real.rpow_one]
  rw [h2, h3, mul_assoc]

/-- **Binomial split** of the truncated integral into tail integrals. -/
theorem scaled_integral_eq_sum (l : ℝ) (m : ℕ) (β N : ℝ) (hl : 0 < l) (hβ : 0 < β) :
    ∫ t in Ioc (0 : ℝ) N, t ^ (l - 1) * (Real.log N - Real.log t) ^ m * Real.exp (-(β * t)) =
      ∑ j ∈ Finset.range (m + 1),
        Real.log N ^ j * (m.choose j : ℝ) * logTailIntegral l β (m - j) N := by
  have h1 : ∀ t, t ^ (l - 1) * (Real.log N - Real.log t) ^ m * Real.exp (-(β * t)) =
      ∑ j ∈ Finset.range (m + 1), Real.log N ^ j * (m.choose j : ℝ) *
        (t ^ (l - 1) * (-Real.log t) ^ (m - j) * Real.exp (-(β * t))) := by
    intro t
    rw [show Real.log N - Real.log t = Real.log N + -Real.log t by ring, add_pow,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [h1]
  rw [integral_finsetSum _ fun j _ =>
    ((logTail_integrableOn l β (m - j) hl hβ).mono_set Ioc_subset_Ioi_self).const_mul _]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- The `j = 0` tail integral converges to the Gamma integral. -/
theorem tendsto_logTailIntegral_zero (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) :
    Tendsto (fun N => logTailIntegral l β 0 N) atTop (𝓝 (Real.Gamma l * β ^ (-l))) := by
  have h := intervalIntegral_tendsto_integral_Ioi 0 (logTail_integrableOn l β 0 hl hβ) tendsto_id
  have h2 : ∫ t in Ioi (0 : ℝ), t ^ (l - 1) * (-Real.log t) ^ 0 * Real.exp (-(β * t)) =
      Real.Gamma l * β ^ (-l) := by
    rw [← integral_rpow_mul_exp_neg_mul l β hl hβ]
    simp
  rw [h2] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  unfold logTailIntegral
  exact intervalIntegral.integral_of_le hN

/-- Every lower-order binomial term is `o(1)` after normalising by `(log N)^m`. -/
theorem tendsto_logTail_term_zero (l β : ℝ) (m j : ℕ) (hl : 0 < l) (hβ : 0 < β) (hj : j < m) :
    Tendsto (fun N => Real.log N ^ j / Real.log N ^ m * logTailIntegral l β (m - j) N) atTop
      (𝓝 0) := by
  have hpow : Tendsto (fun N => Real.log N ^ j / Real.log N ^ m) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℝ => Real.log N ^ (m - j)) atTop atTop :=
      (tendsto_pow_atTop (Nat.sub_ne_zero_of_lt hj)).comp Real.tendsto_log_atTop
    refine h1.inv_tendsto_atTop.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
    simp only [Pi.inv_apply]
    rw [pow_sub₀ _ hlog hj.le, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
  refine hpow.zero_mul_isBoundedUnder_le ?_
  exact isBoundedUnder_of ⟨_, fun N => abs_logTailIntegral_le l β (m - j) hl hβ N⟩

/-- **Gamma/log asymptotic (ratio form)**:
`∫₀¹ z^{λ-1} (-log z)^m e^{-βNz} dz / (N^{-λ} (log N)^m) → Γ(λ) β^{-λ}`. -/
theorem tendsto_gammaLogIntegral_div (l : ℝ) (m : ℕ) (β : ℝ) (hl : 0 < l) (hβ : 0 < β) :
    Tendsto (fun N => gammaLogIntegral l m β N / (N ^ (-l) * Real.log N ^ m)) atTop
      (𝓝 (Real.Gamma l * β ^ (-l))) := by
  set G := Real.Gamma l * β ^ (-l) with hG
  have hterm : ∀ j ∈ Finset.range (m + 1),
      Tendsto (fun N => (m.choose j : ℝ) *
        (Real.log N ^ j / Real.log N ^ m * logTailIntegral l β (m - j) N)) atTop
        (𝓝 ((m.choose j : ℝ) * if j = m then G else 0)) := by
    intro j hj
    refine Tendsto.const_mul _ ?_
    rcases (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)).lt_or_eq with h | h
    · rw [if_neg h.ne]
      exact tendsto_logTail_term_zero l β m j hl hβ h
    · subst h
      rw [if_pos rfl, Nat.sub_self]
      refine (tendsto_logTailIntegral_zero l β hl hβ).congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
      rw [div_self (pow_ne_zero _ (Real.log_pos hN).ne'), one_mul]
  have hsum := tendsto_finsetSum _ hterm
  have hval : ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ) * if j = m then G else 0) = G := by
    simp [mul_ite, Finset.sum_ite_eq']
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  rw [gammaLogIntegral_eq_scaled l m β N hN0, scaled_integral_eq_sum l m β N hl hβ,
    mul_div_mul_left _ _ (Real.rpow_pos_of_pos hN0 _).ne', Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Gamma/log asymptotic (equivalence form)**:
`∫₀¹ z^{λ-1} (-log z)^m e^{-βNz} dz ~ Γ(λ) β^{-λ} N^{-λ} (log N)^m`, stated against the
`powLog` normal form of `QuotientCalculus.lean`. -/
theorem gammaLogIntegral_isEquivalent (l : ℝ) (m : ℕ) (β : ℝ) (hl : 0 < l) (hβ : 0 < β) :
    (fun N => gammaLogIntegral l m β N) ~[atTop] powLog (Real.Gamma l * β ^ (-l)) l m := by
  have hG : 0 < Real.Gamma l * β ^ (-l) :=
    mul_pos (Real.Gamma_pos_of_pos hl) (Real.rpow_pos_of_pos hβ _)
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  have h := (tendsto_gammaLogIntegral_div l m β hl hβ).div_const (Real.Gamma l * β ^ (-l))
  rw [div_self hG.ne'] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hlog : Real.log N ^ m ≠ 0 := pow_ne_zero _ (Real.log_pos hN).ne'
  simp only [Pi.div_apply, powLog]
  field_simp

/-- Lebesgue-integral bridge: the `ENNReal` product-density integrand integrates to
`ofReal (gammaLogIntegral l m β N)`. -/
theorem lintegral_logDensity_mul_exp (l : ℝ) (m : ℕ) (β N : ℝ) (hl : 0 < l) (hβN : 0 < β * N) :
    ∫⁻ z in Ioc (0 : ℝ) 1,
        ENNReal.ofReal (logDensity l m z) * ENNReal.ofReal (Real.exp (-(β * N * z))) =
      ENNReal.ofReal (gammaLogIntegral l m β N) := by
  unfold gammaLogIntegral
  have hint : IntegrableOn (fun z => logDensity l m z * Real.exp (-(β * N * z))) (Ioc 0 1) :=
    (logTail_integrableOn l (β * N) m hl hβN).mono_set Ioc_subset_Ioi_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun z => logDensity l m z * Real.exp (-(β * N * z)) :=
    (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun z hz =>
      mul_nonneg (logDensity_nonneg l m z hz.1 hz.2) (Real.exp_pos _).le)
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
  refine setLIntegral_congr_fun measurableSet_Ioc fun z hz => ?_
  exact (ENNReal.ofReal_mul (logDensity_nonneg l m z hz.1 hz.2)).symm

end Laplace.Grammar
