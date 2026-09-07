/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TightNormalisedRemainder

/-!
# Norm-boundedness in probability from convergence in distribution (grammar §4.3)

If the random Taylor data `X n : Ω → CoeffPair` converge in distribution to `Z`, then their norms
are bounded in probability: `∀ η > 0, ∃ M, ∀ᶠ n, μ {‖X n‖ > M} ≤ η`
(`normBounded_of_tendstoInDistribution`). Proof: the tail `μ' {‖Z‖ ≥ m}` tends to `0` as
`m → ∞` (continuity from above), and the portmanteau theorem on the closed set `{‖a‖ ≥ m}` bounds
the limsup of `μ {‖X n‖ ≥ m}` by `μ' {‖Z‖ ≥ m}`. Consequently the tightness hypothesis of unit 152
is automatic, and the ordered normalised remainders converge in distribution for ANY sequence of
measurable Taylor data converging in distribution (`tendstoInDistribution_normA'`,
`tendstoInDistribution_normB'`). Astra #12 rank 1. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real

namespace Laplace.Grammar

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}

/-- The tail probabilities of a real-valued (a.e.-measurable) norm tend to zero. -/
theorem tendsto_measure_norm_ge_atTop (Z : Ω' → CoeffPair) (hZ : AEMeasurable Z μ') :
    Tendsto (fun m : ℕ => μ' ((fun ω => ‖Z ω‖) ⁻¹' Set.Ici (m : ℝ))) atTop (𝓝 0) := by
  have hnull : ∀ m : ℕ, NullMeasurableSet ((fun ω => ‖Z ω‖) ⁻¹' Set.Ici (m : ℝ)) μ' :=
    fun m => hZ.norm.nullMeasurableSet_preimage measurableSet_Ici
  have hanti : Antitone fun m : ℕ => (fun ω => ‖Z ω‖) ⁻¹' Set.Ici (m : ℝ) := by
    intro m m' hmm' ω hω
    simp only [Set.mem_preimage, Set.mem_Ici] at hω ⊢
    exact le_trans (by exact_mod_cast hmm') hω
  have h := tendsto_measure_iInter_atTop (μ := μ') hnull hanti ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ m : ℕ, (fun ω => ‖Z ω‖) ⁻¹' Set.Ici (m : ℝ)) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Ici, Set.mem_empty_iff_false, iff_false,
      not_forall, not_le]
    exact exists_nat_gt _
  rw [hempty, measure_empty] at h
  exact h

/-- **Norm-boundedness in probability** of a sequence converging in distribution. -/
theorem normBounded_of_tendstoInDistribution (X : ι → Ω → CoeffPair) (Z : Ω' → CoeffPair)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') :
    ∀ η : ENNReal, 0 < η → ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in l, μ {ω | M < ‖X n ω‖} ≤ η := by
  intro η hη
  by_cases hηtop : η = ⊤
  · exact ⟨0, le_rfl, Eventually.of_forall fun n => by rw [hηtop]; exact le_top⟩
  have hZ : AEMeasurable Z μ' := hX.aemeasurable_limit
  have hhalf : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨m, hm⟩ := ((tendsto_measure_norm_ge_atTop Z hZ).eventually (gt_mem_nhds hhalf)).exists
  set F : Set CoeffPair := {a | (m : ℝ) ≤ ‖a‖} with hFdef
  have hF : IsClosed F := isClosed_le continuous_const continuous_norm
  have hFm : MeasurableSet F := hF.measurableSet
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hX.tendsto hF
  simp only [ProbabilityMeasure.coe_mk] at hport
  have hmap : ∀ n, (μ.map (X n)) F = μ (X n ⁻¹' F) := fun n =>
    Measure.map_apply_of_aemeasurable (hX.forall_aemeasurable n) hFm
  simp only [hmap, Measure.map_apply_of_aemeasurable hZ hFm] at hport
  have hZF : μ' (Z ⁻¹' F) < η / 2 := hm
  have hlt : limsup (fun n => μ (X n ⁻¹' F)) l < η :=
    lt_of_le_of_lt hport (lt_of_lt_of_le hZF ENNReal.half_le_self)
  refine ⟨m, Nat.cast_nonneg m, (eventually_lt_of_limsup_lt hlt).mono fun n hn => ?_⟩
  refine le_trans (measure_mono ?_) hn.le
  intro ω hω
  exact le_of_lt (show (m : ℝ) < ‖X n ω‖ from hω)

variable [l.IsCountablyGenerated]

/-- **A-slot, hypothesis-free form**: for measurable Taylor data converging in distribution, the
normalised remainder converges in distribution to the limiting log coefficient. -/
theorem tendstoInDistribution_normA' (β b p₁ p₂ ρ r T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (X : ι → Ω → CoeffPair) (hXm : ∀ n, Measurable (X n)) (Z : Ω' → CoeffPair)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) (α : ℝ) (hα : α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) :
    TendstoInDistribution (fun n ω => normA β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α (Nseq n) (X n ω)) l
      (coeffA β ρ h₁ h₂ k₁ k₂ α ∘ Z) (fun _ => μ) μ' :=
  tendstoInDistribution_normA_tight β b p₁ p₂ ρ r T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ hp₁ hp₂
    X hXm (normBounded_of_tendstoInDistribution X Z hX) Z hX Nseq hN α hα

/-- **B-slot, hypothesis-free form.** -/
theorem tendstoInDistribution_normB' (β b p₁ p₂ ρ r T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (X : ι → Ω → CoeffPair) (hXm : ∀ n, Measurable (X n)) (Z : Ω' → CoeffPair)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) (α : ℝ) (hα : α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) :
    TendstoInDistribution (fun n ω => normB β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α (Nseq n) (X n ω)) l
      (coeffB β b ρ h₁ h₂ k₁ k₂ α ∘ Z) (fun _ => μ) μ' :=
  tendstoInDistribution_normB_tight β b p₁ p₂ ρ r T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ hp₁ hp₂
    X hXm (normBounded_of_tendstoInDistribution X Z hX) Z hX Nseq hN α hα

end Laplace.Grammar
