/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.ChartPosteriorLimit

/-!
# The stochastic `1/log N` regime

Astra #19's next programme, first unit. For a corner-vanishing observable (`y_{φ,00} = 0`) with a
random phase, the chart posterior ratio decays like `1/log N` with a **random** limiting constant:

  `log N · Z_N[φ](X_n) / Z_N[1](X_n) ⇒ B^φ_p(Z) / A^1_p(Z)`

(`tendstoInDistribution_log_posterior`), where `X_n ⇒ Z` is the random coefficient input, `A^1_p`
is the (strictly positive) leading log coefficient of the denominator and `B^φ_p` the constant
coefficient of the numerator at the leading exponent.

Route (the feasibility gate of Astra #19 passes with the existing infrastructure):

* the numerator's leading log coefficient vanishes identically for every phase
  (`coeffA_withY_eq_zero`), so its B-slot normalised remainder is exactly `Z_N[φ]/N^{-p}`
  (`normB_withY_eq`), while the denominator's A-slot remainder is `Z_N[1]/(N^{-p} log N)`;
* both normalised remainders converge to the corresponding coefficients in probability along the
  same random input (`tendstoInMeasure_normB_withY_sub`, and unit 158 for the A-slot), giving joint
  convergence of the pair (`tendstoInDistribution_normBA_pair`);
* the positive-denominator quotient theorem (unit 157) and the exact identity
  `normB^φ / normA^1 = (Z[φ]/Z[1]) · log N` for `N > 1` finish.

The case `B^φ_p(Z) = 0` is covered (the limiting quotient is then `0`); NOT claimed: any rate beyond
the displayed scaled convergence in distribution, or random amplitudes.
-/

open MeasureTheory Filter Topology Real

namespace Laplace.Grammar

/-- A corner-vanishing fixed amplitude has vanishing leading log coefficient for every phase. -/
theorem coeffA_withY_eq_zero (β ρ : ℝ) (hρ : 0 < ρ) (h₁ h₂ k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (p : ℝ) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (yφ : ℕ × ℕ → ℝ)
    (hyφ : WSummable ρ yφ) (hy0 : yφ (0, 0) = 0) (a : CoeffPair) :
    coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ hρ yφ hyφ a) = 0 := by
  unfold coeffA
  simp only [toX_withY, toY_withY]
  rw [leading_log_coeff β h₁ h₂ k₁ k₂ hk₁ hk₂ p hp₁ hp₂, hy0]
  simp

/-- With a corner-vanishing amplitude the B-slot normalised remainder at the leading exponent is the
chart integral normalised by `N^{-p}`. -/
theorem normB_withY_eq (β b p ρ T : ℝ) (hρ : 0 < ρ) (h₁ h₂ k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (yφ : ℕ × ℕ → ℝ)
    (hyφ : WSummable ρ yφ) (hy0 : yφ (0, 0) = 0) (N : ℝ) (a : CoeffPair) :
    normB β b ρ p p T h₁ h₂ k₁ k₂ p N (withY ρ hρ yφ hyφ a) =
      chartZ β b ρ h₁ h₂ k₁ k₂ N (withY ρ hρ yφ hyφ a) / N ^ (-p) := by
  unfold normB
  rw [lowerPart_leading_eq_zero h₁ h₂ k₁ k₂ hk₁ hk₂ p T hp₁ hp₂,
    coeffA_withY_eq_zero β ρ hρ h₁ h₂ k₁ k₂ hk₁ hk₂ p hp₁ hp₂ yφ hyφ hy0 a]
  simp

/-- The A-slot normalised remainder at the leading exponent is the chart integral normalised by
`N^{-p} log N`. -/
theorem normA_leading_eq (β b p ρ T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (N : ℝ) (a : CoeffPair) :
    normA β b ρ p p T h₁ h₂ k₁ k₂ p N a =
      chartZ β b ρ h₁ h₂ k₁ k₂ N a / (N ^ (-p) * Real.log N) := by
  unfold normA
  rw [lowerPart_leading_eq_zero h₁ h₂ k₁ k₂ hk₁ hk₂ p T hp₁ hp₂, sub_zero]

/-- For `N > 1`: `normB^φ / normA^1 = (Z[φ]/Z[1]) · log N`. -/
theorem normB_div_normA_eq (β b p ρ T : ℝ) (hρ : 0 < ρ) (h₁ h₂ k₁ k₂ : ℕ) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (yφ : ℕ × ℕ → ℝ) (hyφ : WSummable ρ yφ) (hy0 : yφ (0, 0) = 0) (N : ℝ) (hN : 1 < N)
    (a a' : CoeffPair) :
    normB β b ρ p p T h₁ h₂ k₁ k₂ p N (withY ρ hρ yφ hyφ a) /
        normA β b ρ p p T h₁ h₂ k₁ k₂ p N a' =
      chartZ β b ρ h₁ h₂ k₁ k₂ N (withY ρ hρ yφ hyφ a) / chartZ β b ρ h₁ h₂ k₁ k₂ N a' *
        Real.log N := by
  rw [normB_withY_eq β b p ρ T hρ h₁ h₂ k₁ k₂ hk₁ hk₂ hp₁ hp₂ yφ hyφ hy0 N a,
    normA_leading_eq β b p ρ T h₁ h₂ k₁ k₂ hk₁ hk₂ hp₁ hp₂ N a']
  have hpow : N ^ (-p) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  field_simp

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}
  [l.IsCountablyGenerated]

omit [l.IsCountablyGenerated] in
/-- The B-slot error with a fixed amplitude tends to zero in probability for random phase data
converging in distribution. -/
theorem tendstoInMeasure_normB_withY_sub (β b p ρ r T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (_hbr : b < r) (_hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (hpT : p < 2 * T)
    (y : ℕ × ℕ → ℝ) (hy : WSummable ρ y) (X : ι → Ω → CoeffPair) (Z : Ω' → CoeffPair)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInMeasure μ (fun n ω =>
        normB β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ (lt_trans hb hbρ) y hy (X n ω))
          - coeffB β b ρ h₁ h₂ k₁ k₂ p (withY ρ (lt_trans hb hbρ) y hy (X n ω))) l
      (fun _ => 0) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hα : p ∈ polesBelowGen h₁ h₂ k₁ k₂ p p T :=
    (mem_polesBelowGen_iff h₁ h₂ k₁ k₂ hk₁ hk₂ p p T hp₁ hp₂ p).2
      ⟨hpT, Or.inl ⟨0, uExp_zero h₁ k₁ p hp₁⟩⟩
  obtain ⟨δ, hδ, hgap⟩ := exists_gap (polesBelowGen h₁ h₂ k₁ k₂ p p T) p
  have hX' : TendstoInDistribution (fun n => withY ρ hρ y hy ∘ X n) l (withY ρ hρ y hy ∘ Z)
      (fun _ => μ) μ' := hX.continuous_comp (continuous_withY ρ hρ y hy)
  have htight := normBounded_of_tendstoInDistribution _ _ hX'
  have h := tendstoInMeasure_zero_of_tight μ
    (fun n ω => normB β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ hρ y hy (X n ω))
      - coeffB β b ρ h₁ h₂ k₁ k₂ p (withY ρ hρ y hy (X n ω)))
    (fun n => withY ρ hρ y hy ∘ X n)
    (fun M n => errB |uniformTreeConst β b ρ M (2 * M) p p T h₁ h₂ k₁ k₂ 0|
      (ballCoeffBound β b ρ M h₁ h₂ k₁ k₂ (polesBelowGen h₁ h₂ k₁ k₂ p p T)) (2 * T) p δ
      (polesBelowGen h₁ h₂ k₁ k₂ p p T) (Nseq n))
    (fun M _ => (tendsto_errB _ _ _ _ _ _ hpT hδ).comp hN) (fun M hM => ?_) htight
  · exact h
  · filter_upwards [hN.eventually_ge_atTop (Real.exp 1)] with n hn ω hω
    exact normB_sub_le β b p p ρ T h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ M hM _ hω p hα δ hδ hgap
      (Nseq n) hn

/-- **Joint convergence** of the numerator B-slot and denominator A-slot normalised remainders for
two deterministic amplitudes and a common random phase. -/
theorem tendstoInDistribution_normBA_pair (β b p ρ r T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (hpT : p < 2 * T)
    (yφ y₁ : ℕ × ℕ → ℝ) (hyφ : WSummable ρ yφ) (hy₁ : WSummable ρ y₁)
    (X : ι → Ω → CoeffPair) (hXm : ∀ n, Measurable (X n)) (Z : Ω' → CoeffPair)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInDistribution (fun n ω =>
        (normB β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ (lt_trans hb hbρ) yφ hyφ (X n ω)),
          normA β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ (lt_trans hb hbρ) y₁ hy₁ (X n ω)))) l
      (fun ω => (coeffB β b ρ h₁ h₂ k₁ k₂ p (withY ρ (lt_trans hb hbρ) yφ hyφ (Z ω)),
        coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ (lt_trans hb hbρ) y₁ hy₁ (Z ω)))) (fun _ => μ) μ' := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 < r := lt_trans hb hbr
  have hp0 : 0 < p := by
    rw [← hp₁]; have : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
    positivity
  have hg : Continuous fun a : CoeffPair =>
      (coeffB β b ρ h₁ h₂ k₁ k₂ p (withY ρ hρ yφ hyφ a),
        coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ hρ y₁ hy₁ a)) :=
    ((continuous_coeffB β b ρ r h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ p hp0).comp
      (continuous_withY ρ hρ yφ hyφ)).prodMk
      ((continuous_coeffA β ρ r h₁ h₂ k₁ k₂ hβ hρ hr0 hrρ hk₁ hk₂ p hp0).comp
        (continuous_withY ρ hρ y₁ hy₁))
  have hA := hX.continuous_comp hg
  have hEφ := tendstoInMeasure_normB_withY_sub β b p ρ r T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂
    hp₁ hp₂ hpT yφ hyφ X Z hX Nseq hN
  have hE₁ := tendstoInMeasure_normA_withY_sub β b p ρ r T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂
    hp₁ hp₂ hpT y₁ hy₁ X Z hX Nseq hN
  have hE := tendstoInMeasure_prodMk_zero μ _ _ hEφ hE₁
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hA ?_ fun n => ?_
  · exact hE
  · exact ((measurable_normB_comp β b ρ r p p T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ p hp0
        (Nseq n) _ ((measurable_withY ρ hρ yφ hyφ).comp (hXm n))).prodMk
      (measurable_normA_comp β b ρ r p p T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ p (Nseq n) _
        ((measurable_withY ρ hρ y₁ hy₁).comp (hXm n)))).aemeasurable

/-- **The stochastic `1/log N` regime**: for a corner-vanishing observable and a random phase,
`log N · Z_N[φ]/Z_N[1] ⇒ B^φ_p(Z) / A^1_p(Z)`. -/
theorem tendstoInDistribution_log_posterior (β b p ρ r T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (hpT : p < 2 * T)
    (yφ y₁ : ℕ × ℕ → ℝ) (hyφ : WSummable ρ yφ) (hy₁ : WSummable ρ y₁) (hyφ0 : yφ (0, 0) = 0)
    (hy₁0 : 0 < y₁ (0, 0)) (X : ι → Ω → CoeffPair) (hXm : ∀ n, Measurable (X n))
    (Z : Ω' → CoeffPair) (hZm : Measurable Z) (hX : TendstoInDistribution X l Z (fun _ => μ) μ')
    (Nseq : ι → ℝ) (hN : Tendsto Nseq l atTop) :
    TendstoInDistribution (fun n ω =>
        chartZ β b ρ h₁ h₂ k₁ k₂ (Nseq n) (withY ρ (lt_trans hb hbρ) yφ hyφ (X n ω))
          / chartZ β b ρ h₁ h₂ k₁ k₂ (Nseq n) (withY ρ (lt_trans hb hbρ) y₁ hy₁ (X n ω))
          * Real.log (Nseq n)) l
      (fun ω => coeffB β b ρ h₁ h₂ k₁ k₂ p (withY ρ (lt_trans hb hbρ) yφ hyφ (Z ω))
        / coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ (lt_trans hb hbρ) y₁ hy₁ (Z ω))) (fun _ => μ) μ' := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 < r := lt_trans hb hbr
  have hp0 : 0 < p := by
    rw [← hp₁]; have : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
    positivity
  have hpair := tendstoInDistribution_normBA_pair β b p ρ r T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂
    hp₁ hp₂ hpT yφ y₁ hyφ hy₁ X hXm Z hX Nseq hN
  have hmeasB : ∀ n, Measurable fun ω =>
      normB β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ hρ yφ hyφ (X n ω)) :=
    fun n => measurable_normB_comp β b ρ r p p T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ p hp0
      (Nseq n) _ ((measurable_withY ρ hρ yφ hyφ).comp (hXm n))
  have hmeasA : ∀ n, Measurable fun ω =>
      normA β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ hρ y₁ hy₁ (X n ω)) :=
    fun n => measurable_normA_comp β b ρ r p p T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ p
      (Nseq n) _ ((measurable_withY ρ hρ y₁ hy₁).comp (hXm n))
  have hmeasCB : Measurable fun ω => coeffB β b ρ h₁ h₂ k₁ k₂ p (withY ρ hρ yφ hyφ (Z ω)) :=
    (measurable_coeffB β b ρ r h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ p hp0).comp
      ((measurable_withY ρ hρ yφ hyφ).comp hZm)
  have hmeasCA : Measurable fun ω => coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ hρ y₁ hy₁ (Z ω)) :=
    (measurable_coeffA β ρ r h₁ h₂ k₁ k₂ hβ hρ hr0 hrρ hk₁ hk₂ p hp0).comp
      ((measurable_withY ρ hρ y₁ hy₁).comp hZm)
  have hpos : ∀ᵐ ω ∂μ', 0 < coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ hρ y₁ hy₁ (Z ω)) :=
    Filter.Eventually.of_forall fun ω =>
      coeffA_leading_pos β ρ h₁ h₂ k₁ k₂ hβ hk₁ hk₂ p hp₁ hp₂ _ (by rw [toY_withY]; exact hy₁0)
  have hdiv := tendstoInDistribution_div_of_pos _ _ _ _ hmeasB hmeasA hmeasCB hmeasCA hpair hpos
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hdiv ?_ fun n =>
    (((measurable_chartZ_comp β b ρ h₁ h₂ k₁ k₂ hb hbρ (Nseq n) _
        ((measurable_withY ρ hρ yφ hyφ).comp (hXm n))).div
      (measurable_chartZ_comp β b ρ h₁ h₂ k₁ k₂ hb hbρ (Nseq n) _
        ((measurable_withY ρ hρ y₁ hy₁).comp (hXm n)))).mul_const _).aemeasurable
  have h := tendstoInMeasure_of_eventually_abs_le (l := l) μ
    (fun n ω =>
      chartZ β b ρ h₁ h₂ k₁ k₂ (Nseq n) (withY ρ hρ yφ hyφ (X n ω))
          / chartZ β b ρ h₁ h₂ k₁ k₂ (Nseq n) (withY ρ hρ y₁ hy₁ (X n ω)) * Real.log (Nseq n)
        - normB β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ hρ yφ hyφ (X n ω))
          / normA β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ hρ y₁ hy₁ (X n ω)))
    (fun _ => (0 : ℝ)) tendsto_const_nhds ?_
  · exact h
  · filter_upwards [hN.eventually_gt_atTop 1] with n hn ω
    rw [normB_div_normA_eq β b p ρ T hρ h₁ h₂ k₁ k₂ hk₁ hk₂ hp₁ hp₂ yφ hyφ hyφ0 (Nseq n) hn,
      sub_self, abs_zero]

end Laplace.Grammar
