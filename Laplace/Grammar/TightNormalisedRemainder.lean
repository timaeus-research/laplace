/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.FarPhase

/-!
# Normalised remainders for tight families of Taylor data (grammar §4.3)

The bounded-family theorems of unit 150 are localised: the deterministic norm bound `‖X n ω‖ ≤ M`
is replaced by **tightness** of the norms, `∀ η > 0, ∃ M, ∀ᶠ n, μ {‖X n‖ > M} ≤ η` (the paper's
appendix prop:convergence (i)). On the ball `‖X n‖ ≤ M` the error is deterministically small, and
off the ball the probability is at most `η`; so the error tends to `0` in probability
(`tendstoInMeasure_zero_of_tight`), and Mathlib's `tendstoInDistribution_of_tendstoInMeasure_sub`
gives `normA ⇒ A_α(Z)`, `normB ⇒ B_α(Z)` (`tendstoInDistribution_normA_tight`,
`tendstoInDistribution_normB_tight`). This is the form applicable to Gaussian-type limits, whose
Taylor data are not deterministically bounded. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real

namespace Laplace.Grammar

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Localisation lemma**: an error that is deterministically small on norm balls of a tight
family tends to zero in probability. -/
theorem tendstoInMeasure_zero_of_tight {ι : Type*} {l : Filter ι} (μ : Measure Ω)
    (f : ι → Ω → ℝ) (X : ι → Ω → CoeffPair) (e : ℝ → ι → ℝ)
    (he : ∀ M, 0 ≤ M → Tendsto (e M) l (𝓝 0))
    (hf : ∀ M, 0 ≤ M → ∀ᶠ n in l, ∀ ω, ‖X n ω‖ ≤ M → |f n ω| ≤ e M n)
    (htight : ∀ η : ENNReal, 0 < η → ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in l, μ {ω | M < ‖X n ω‖} ≤ η) :
    TendstoInMeasure μ f l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨M, hM, hev⟩ := htight η hη
  filter_upwards [hev, hf M hM, (he M hM).eventually (gt_mem_nhds hε)] with n hn hfn hlt
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs] at hω ⊢
  by_contra hcon
  exact absurd hω (not_le.2 (lt_of_le_of_lt (hfn ω (not_lt.1 hcon)) hlt))

variable {ι Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι} [l.IsCountablyGenerated]

/-- **A-slot for tight families**: the normalised remainder converges in distribution to the
limiting log coefficient. -/
theorem tendstoInDistribution_normA_tight (β b p₁ p₂ ρ r T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (X : ι → Ω → CoeffPair) (hXm : ∀ n, Measurable (X n))
    (htight : ∀ η : ENNReal, 0 < η → ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in l, μ {ω | M < ‖X n ω‖} ≤ η)
    (Z : Ω' → CoeffPair) (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) (α : ℝ) (hα : α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) :
    TendstoInDistribution (fun n ω => normA β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α (Nseq n) (X n ω)) l
      (coeffA β ρ h₁ h₂ k₁ k₂ α ∘ Z) (fun _ => μ) μ' := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 < r := lt_trans hb hbr
  obtain ⟨δ, hδ, hgap⟩ := exists_gap (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) α
  have hα0 : 0 < α := pos_of_mem_polesBelowGen h₁ h₂ k₁ k₂ hk₁ hk₂ p₁ p₂ T α hα
  have hαT : α < 2 * T := ((mem_polesBelowGen_iff h₁ h₂ k₁ k₂ hk₁ hk₂ p₁ p₂ T hp₁ hp₂ α).1 hα).1
  have hA := tendstoInDistribution_coeffA β ρ r h₁ h₂ k₁ k₂ hβ hρ hr0 hrρ hk₁ hk₂ α hα0 X Z hX
  refine tendstoInDistribution_of_tendstoInMeasure_sub
    (fun n ω => normA β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α (Nseq n) (X n ω)) _ hA ?_ fun n =>
    (measurable_normA_comp β b ρ r p₁ p₂ T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ α (Nseq n) (X n)
      (hXm n)).aemeasurable
  have h := tendstoInMeasure_zero_of_tight μ
    (fun n ω => normA β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α (Nseq n) (X n ω)
      - coeffA β ρ h₁ h₂ k₁ k₂ α (X n ω))
    X (fun M n => errA |uniformTreeConst β b ρ M (2 * M) p₁ p₂ T h₁ h₂ k₁ k₂ 0|
      (ballCoeffBound β b ρ M h₁ h₂ k₁ k₂ (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T)) (2 * T) α δ
      (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) (Nseq n))
    (fun M _ => (tendsto_errA _ _ _ _ _ _ hαT hδ).comp hN) (fun M hM => ?_) htight
  · exact h
  · filter_upwards [hN.eventually_ge_atTop (Real.exp 1)] with n hn ω hω
    exact normA_sub_le β b p₁ p₂ ρ T h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ M hM (X n ω) hω α hα δ
      hδ hgap (Nseq n) hn

/-- **B-slot for tight families** (subtracting the current `A_α`). -/
theorem tendstoInDistribution_normB_tight (β b p₁ p₂ ρ r T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (X : ι → Ω → CoeffPair) (hXm : ∀ n, Measurable (X n))
    (htight : ∀ η : ENNReal, 0 < η → ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in l, μ {ω | M < ‖X n ω‖} ≤ η)
    (Z : Ω' → CoeffPair) (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) (α : ℝ) (hα : α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) :
    TendstoInDistribution (fun n ω => normB β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α (Nseq n) (X n ω)) l
      (coeffB β b ρ h₁ h₂ k₁ k₂ α ∘ Z) (fun _ => μ) μ' := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 < r := lt_trans hb hbr
  obtain ⟨δ, hδ, hgap⟩ := exists_gap (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) α
  have hα0 : 0 < α := pos_of_mem_polesBelowGen h₁ h₂ k₁ k₂ hk₁ hk₂ p₁ p₂ T α hα
  have hαT : α < 2 * T := ((mem_polesBelowGen_iff h₁ h₂ k₁ k₂ hk₁ hk₂ p₁ p₂ T hp₁ hp₂ α).1 hα).1
  have hB := tendstoInDistribution_coeffB β b ρ r h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ α hα0 X Z
    hX
  refine tendstoInDistribution_of_tendstoInMeasure_sub
    (fun n ω => normB β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α (Nseq n) (X n ω)) _ hB ?_ fun n =>
    (measurable_normB_comp β b ρ r p₁ p₂ T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ α hα0 (Nseq n)
      (X n) (hXm n)).aemeasurable
  have h := tendstoInMeasure_zero_of_tight μ
    (fun n ω => normB β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α (Nseq n) (X n ω)
      - coeffB β b ρ h₁ h₂ k₁ k₂ α (X n ω))
    X (fun M n => errB |uniformTreeConst β b ρ M (2 * M) p₁ p₂ T h₁ h₂ k₁ k₂ 0|
      (ballCoeffBound β b ρ M h₁ h₂ k₁ k₂ (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T)) (2 * T) α δ
      (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) (Nseq n))
    (fun M _ => (tendsto_errB _ _ _ _ _ _ hαT hδ).comp hN) (fun M hM => ?_) htight
  · exact h
  · filter_upwards [hN.eventually_ge_atTop (Real.exp 1)] with n hn ω hω
    exact normB_sub_le β b p₁ p₂ ρ T h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ M hM (X n ω) hω α hα δ
      hδ hgap (Nseq n) hn

/-- Deterministically bounded families are tight (so unit 150 is a special case). -/
theorem tight_of_bounded {ι : Type*} {l : Filter ι} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → CoeffPair) (M : ℝ) (hM : 0 ≤ M) (hXb : ∀ n ω, ‖X n ω‖ ≤ M) :
    ∀ η : ENNReal, 0 < η → ∃ M' : ℝ, 0 ≤ M' ∧ ∀ᶠ n in l, μ {ω | M' < ‖X n ω‖} ≤ η := by
  intro η _
  refine ⟨M, hM, Eventually.of_forall fun n => ?_⟩
  have : {ω | M < ‖X n ω‖} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hXb n ω
  rw [this, measure_empty]
  exact (zero_le : (0 : ENNReal) ≤ η)

end Laplace.Grammar
