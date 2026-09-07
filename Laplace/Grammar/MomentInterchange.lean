/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.AllOrdersOneD

/-!
# Weighted `L¹` interchange for the log moments (grammar §4.2, analytic bridge)

The paper's coefficients are (convergent) series indexed by tree types, integrated against the
Gaussian weight `s^{α-1} (log s)^ℓ e^{-βs²}`. This file exposes the interchange API: if the weighted
`L¹` norms of the terms are summable, the log moment of the pointwise sum is the (absolutely
convergent) sum of the log moments (`hasSum_logMoment`, `logMoment_tsum`); a normal-convergence
hypothesis `∑_t |f_t(s)| ≤ G(s)` with a weighted-integrable `G` suffices
(`hasSum_logMoment_of_dominated`), in particular a `C (1+s)^D e^{βsa'}` envelope
(`hasSum_logMoment_of_envelope`). Zero `sorry`/`axiom`.
-/

open Real Finset MeasureTheory Set

namespace Laplace.Grammar

/-- The Gaussian log weight `w(s) = s^{α-1} (log s)^ℓ e^{-βs²}`. -/
noncomputable def momentWeight (β α : ℝ) (ℓ : ℕ) (s : ℝ) : ℝ :=
  s ^ (α - 1) * Real.log s ^ ℓ * Real.exp (-β * s ^ 2)

theorem momentWeight_measurable (β α : ℝ) (ℓ : ℕ) : Measurable (momentWeight β α ℓ) := by
  unfold momentWeight
  exact ((measurable_id.pow_const _).mul (Real.measurable_log.pow_const _)).mul
    (Real.measurable_exp.comp (measurable_const.mul (measurable_id.pow_const _)))

theorem logMoment_eq_integral_weight (β α : ℝ) (ℓ : ℕ) (c : ℝ → ℝ) :
    logMoment β α ℓ c = ∫ s in Ioi (0 : ℝ), momentWeight β α ℓ s * c s := by
  unfold logMoment momentWeight
  exact integral_congr_ae (Filter.Eventually.of_forall fun s => by ring)

/-- **Weighted `L¹` interchange.** If each weighted term is integrable and the weighted `L¹`
norms are summable, the log moment of the pointwise sum is the absolutely convergent sum of the
log moments. -/
theorem hasSum_logMoment {ι : Type*} [Countable ι] (β α : ℝ) (ℓ : ℕ) (f : ι → ℝ → ℝ)
    (hint : ∀ t, IntegrableOn (fun s => momentWeight β α ℓ s * f t s) (Ioi 0))
    (hsum : Summable fun t => ∫ s in Ioi (0 : ℝ), |momentWeight β α ℓ s * f t s|) :
    HasSum (fun t => logMoment β α ℓ (f t)) (logMoment β α ℓ (fun s => ∑' t, f t s)) := by
  simp only [logMoment_eq_integral_weight]
  have hsum' : Summable fun t => ∫ s in Ioi (0 : ℝ), ‖momentWeight β α ℓ s * f t s‖ := by
    simpa only [Real.norm_eq_abs] using hsum
  have h : HasSum (fun t => ∫ s in Ioi (0 : ℝ), momentWeight β α ℓ s * f t s)
      (∫ s in Ioi (0 : ℝ), ∑' t, momentWeight β α ℓ s * f t s) :=
    hasSum_integral_of_summable_integral_norm hint hsum'
  convert h using 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  exact (tsum_mul_left).symm

theorem logMoment_tsum {ι : Type*} [Countable ι] (β α : ℝ) (ℓ : ℕ) (f : ι → ℝ → ℝ)
    (hint : ∀ t, IntegrableOn (fun s => momentWeight β α ℓ s * f t s) (Ioi 0))
    (hsum : Summable fun t => ∫ s in Ioi (0 : ℝ), |momentWeight β α ℓ s * f t s|) :
    logMoment β α ℓ (fun s => ∑' t, f t s) = ∑' t, logMoment β α ℓ (f t) :=
  (hasSum_logMoment β α ℓ f hint hsum).tsum_eq.symm

/-- Normal convergence `∑_t |f_t(s)| ≤ G(s)` with `|w| G` integrable gives the integrability and
summability hypotheses of the interchange. -/
theorem weighted_summable_of_dominated {ι : Type*} [Countable ι] (w : ℝ → ℝ) (hw : Measurable w)
    (f : ι → ℝ → ℝ) (hf : ∀ t, Measurable (f t)) (G : ℝ → ℝ)
    (hsumm : ∀ s ∈ Ioi (0 : ℝ), Summable fun t => |f t s|)
    (hdom : ∀ s ∈ Ioi (0 : ℝ), ∑' t, |f t s| ≤ G s)
    (hG : IntegrableOn (fun s => |w s| * G s) (Ioi 0)) :
    (∀ t, IntegrableOn (fun s => w s * f t s) (Ioi 0)) ∧
      Summable fun t => ∫ s in Ioi (0 : ℝ), |w s * f t s| := by
  have hmeas : ∀ t, Measurable fun s => w s * f t s := fun t => hw.mul (hf t)
  have hlt : ∑' t, ∫⁻ s in Ioi (0 : ℝ), ‖w s * f t s‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum fun t => (hmeas t).enorm.aemeasurable]
    refine ne_top_of_le_ne_top (hasFiniteIntegral_iff_enorm.1 hG.hasFiniteIntegral).ne
      (lintegral_mono_ae ?_)
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
    have hG0 : 0 ≤ G s := (tsum_nonneg fun t => abs_nonneg _).trans (hdom s hs)
    calc ∑' t, ‖w s * f t s‖ₑ
        = ∑' t, ENNReal.ofReal |w s| * ENNReal.ofReal |f t s| := by
          simp only [Real.enorm_eq_ofReal_abs, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
      _ = ENNReal.ofReal |w s| * ENNReal.ofReal (∑' t, |f t s|) := by
          rw [ENNReal.tsum_mul_left,
            ENNReal.ofReal_tsum_of_nonneg (fun t => abs_nonneg _) (hsumm s hs)]
      _ ≤ ENNReal.ofReal |w s| * ENNReal.ofReal (G s) := by
          gcongr
          exact hdom s hs
      _ = ‖|w s| * G s‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hG0),
            ENNReal.ofReal_mul (abs_nonneg _)]
  refine ⟨fun t => ⟨(hmeas t).aestronglyMeasurable, ?_⟩, ?_⟩
  · exact hasFiniteIntegral_iff_enorm.2 ((ENNReal.le_tsum t).trans_lt hlt.lt_top)
  · refine (ENNReal.summable_toReal hlt).congr fun t => ?_
    rw [← integral_norm_eq_lintegral_enorm (hmeas t).aestronglyMeasurable]
    simp only [Real.norm_eq_abs]

/-- **Interchange under normal convergence.** -/
theorem hasSum_logMoment_of_dominated {ι : Type*} [Countable ι] (β α : ℝ) (ℓ : ℕ)
    (f : ι → ℝ → ℝ) (hf : ∀ t, Measurable (f t)) (G : ℝ → ℝ)
    (hsumm : ∀ s ∈ Ioi (0 : ℝ), Summable fun t => |f t s|)
    (hdom : ∀ s ∈ Ioi (0 : ℝ), ∑' t, |f t s| ≤ G s)
    (hG : IntegrableOn (fun s => |momentWeight β α ℓ s| * G s) (Ioi 0)) :
    HasSum (fun t => logMoment β α ℓ (f t)) (logMoment β α ℓ (fun s => ∑' t, f t s)) := by
  obtain ⟨hint, hsum⟩ := weighted_summable_of_dominated (momentWeight β α ℓ)
    (momentWeight_measurable β α ℓ) f hf G hsumm hdom hG
  exact hasSum_logMoment β α ℓ f hint hsum

/-- The weighted envelope `C (1+s)^D e^{βsa'}` is integrable against `|w|` for `α > 0`. -/
theorem momentWeight_envelope_integrableOn (β a' α C : ℝ) (hβ : 0 < β) (hα : 0 < α) (hC : 0 ≤ C)
    (ℓ D : ℕ) :
    IntegrableOn (fun s => |momentWeight β α ℓ s| * (C * (1 + s) ^ D * Real.exp (β * s * a')))
      (Ioi 0) := by
  have h := moment_integrableOn_of_envelope β a' (α - 1) C hβ (by linarith) ℓ D
    (fun s => C * (1 + s) ^ D * Real.exp (β * s * a')) (by fun_prop)
    (fun s hs => by rw [abs_of_nonneg (by positivity)])
  refine Integrable.mono' h ?_ ?_
  · exact ((continuous_abs.measurable.comp (momentWeight_measurable β α ℓ)).mul
      (by fun_prop)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hs
    have hCe : 0 ≤ C * (1 + s) ^ D * Real.exp (β * s * a') := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hCe)]
    have hw : |momentWeight β α ℓ s|
        = s ^ (α - 1) * |Real.log s| ^ ℓ * Real.exp (-β * s ^ 2) := by
      unfold momentWeight
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _), abs_pow,
        abs_of_pos (Real.exp_pos _)]
    rw [hw, abs_of_nonneg hCe]
    have hlog : |Real.log s| ^ ℓ ≤ (1 + |Real.log s|) ^ ℓ :=
      pow_le_pow_left₀ (abs_nonneg _) (by linarith) ℓ
    have hsα : 0 ≤ s ^ (α - 1) := Real.rpow_nonneg hs0.le _
    calc s ^ (α - 1) * |Real.log s| ^ ℓ * Real.exp (-β * s ^ 2)
          * (C * (1 + s) ^ D * Real.exp (β * s * a'))
        ≤ s ^ (α - 1) * (1 + |Real.log s|) ^ ℓ * Real.exp (-β * s ^ 2)
          * (C * (1 + s) ^ D * Real.exp (β * s * a')) := by gcongr
      _ = _ := by ring

/-- **Interchange under a `C (1+s)^D e^{βsa'}` envelope.** -/
theorem hasSum_logMoment_of_envelope {ι : Type*} [Countable ι] (β a' α C : ℝ) (hβ : 0 < β)
    (hα : 0 < α) (hC : 0 ≤ C) (ℓ D : ℕ) (f : ι → ℝ → ℝ) (hf : ∀ t, Measurable (f t))
    (hsumm : ∀ s ∈ Ioi (0 : ℝ), Summable fun t => |f t s|)
    (hdom : ∀ s ∈ Ioi (0 : ℝ), ∑' t, |f t s| ≤ C * (1 + s) ^ D * Real.exp (β * s * a')) :
    HasSum (fun t => logMoment β α ℓ (f t)) (logMoment β α ℓ (fun s => ∑' t, f t s)) :=
  hasSum_logMoment_of_dominated β α ℓ f hf _ hsumm hdom
    (momentWeight_envelope_integrableOn β a' α C hβ hα hC ℓ D)

end Laplace.Grammar
