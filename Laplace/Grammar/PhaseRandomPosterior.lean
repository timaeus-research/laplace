/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PhaseRandomTransfer

/-!
# The random per-stratum posterior expectation in general dimension

Unit 213 (Headline XVII). Deterministic observable `φ` and density `c > 0` (continuous on the closed
cube), random phase `ξ n : Ω → C([0,1]^d)` converging in distribution to `ξ`, deterministic scales
`N n → ∞`:
```
∫ φ c u^h e^{-βN_n²u^{2k}+βN_n u^k ξ_n} / ∫ c u^h e^{-βN_n²u^{2k}+βN_n u^k ξ_n}
   ⇒ phaseCoeff(ξ, φc) / phaseCoeff(ξ, c)
```
(`tendstoInDistribution_phase_posterior`): the numerator and denominator normalised integrals
converge jointly in distribution (Headline XVI applied to the pair, with the common scale
cancelling), and the limiting denominator is strictly positive (unit 205), so the
positive-denominator quotient theorem of unit 157 applies. In the equal-ratio case the limit is the
deterministic `φ(0)` (`tendstoInDistribution_phase_posterior_equal`): the corner value, whatever the
limiting phase — the general-`d` form of the `d = 2` chart posterior limit
`Z[φ]/Z[1] ⇒ y_{φ,00}/y_{1,00}`.

Scope: the observable and density are deterministic (the paper's `φ`, `c₀`); the phase is the only
random input; a single chart; convergence of the empirical phase process is a hypothesis.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.Grammar

/-- Pairing a random phase with a fixed amplitude. -/
theorem measurable_pair_const {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → C(closedCube d, ℝ)) (hX : Measurable X) (g : C(closedCube d, ℝ)) :
    Measurable (fun ω => ((X ω, g) : InputSpace d)) :=
  hX.prodMk measurable_const

theorem continuous_pair_const {d : ℕ} (g : C(closedCube d, ℝ)) :
    Continuous (fun f : C(closedCube d, ℝ) => ((f, g) : InputSpace d)) :=
  continuous_id.prodMk continuous_const

/-- `extCube (φ * c) = extCube φ * extCube c`. -/
theorem extCube_mul {d : ℕ} (φ c : C(closedCube d, ℝ)) :
    extCube (φ * c) = fun x => extCube φ x * extCube c x := by
  funext x
  simp [extCube]

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {L : Filter ι}
  [L.IsCountablyGenerated]

/-- **Joint convergence of the normalised numerator and denominator** along a random phase. -/
theorem tendstoInDistribution_normChart_pair (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (X : ι → Ω → C(closedCube (d + 1), ℝ))
    (hXm : ∀ n, Measurable (X n)) (Z : Ω' → C(closedCube (d + 1), ℝ)) (hZm : Measurable Z)
    (hX : TendstoInDistribution X L Z (fun _ => μ) μ') (Nseq : ι → ℝ) (hN : Tendsto Nseq L atTop)
    (hN0 : ∀ n, 0 ≤ Nseq n) (g₁ g₂ : C(closedCube (d + 1), ℝ)) :
    TendstoInDistribution (fun n ω => (normChart h k l β (Nseq n) (X n ω, g₁),
        normChart h k l β (Nseq n) (X n ω, g₂))) L
      (fun ω => (limChart h k l β (Z ω, g₁), limChart h k l β (Z ω, g₂))) (fun _ => μ) μ' := by
  have hcont : Continuous (fun f : C(closedCube (d + 1), ℝ) =>
      (limChart h k l β (f, g₁), limChart h k l β (f, g₂))) :=
    ((continuous_limChart d h k hk l β hl hβ hmin).comp (continuous_pair_const g₁)).prodMk
      ((continuous_limChart d h k hk l β hl hβ hmin).comp (continuous_pair_const g₂))
  have hlim := hX.continuous_comp hcont
  have hX₁ : TendstoInDistribution (fun n ω => ((X n ω, g₁) : InputSpace (d + 1))) L
      (fun ω => (Z ω, g₁)) (fun _ => μ) μ' := hX.continuous_comp (continuous_pair_const g₁)
  have hX₂ : TendstoInDistribution (fun n ω => ((X n ω, g₂) : InputSpace (d + 1))) L
      (fun ω => (Z ω, g₂)) (fun _ => μ) μ' := hX.continuous_comp (continuous_pair_const g₂)
  have herr₁ := tendstoInMeasure_normChart_sub d h k hk l β hl hβ hmin hatt
    (fun n ω => ((X n ω, g₁) : InputSpace (d + 1))) (fun ω => (Z ω, g₁))
    (measurable_pair_const Z hZm g₁) hX₁ Nseq hN
  have herr₂ := tendstoInMeasure_normChart_sub d h k hk l β hl hβ hmin hatt
    (fun n ω => ((X n ω, g₂) : InputSpace (d + 1))) (fun ω => (Z ω, g₂))
    (measurable_pair_const Z hZm g₂) hX₂ Nseq hN
  have herr := tendstoInMeasure_prodMk_zero μ _ _ herr₁ herr₂
  have hmeas : ∀ n, AEMeasurable (fun ω =>
      (normChart h k l β (Nseq n) (X n ω, g₁) - limChart h k l β (X n ω, g₁),
        normChart h k l β (Nseq n) (X n ω, g₂) - limChart h k l β (X n ω, g₂))) μ := fun n => by
    have hm₁ := measurable_pair_const (X n) (hXm n) g₁
    have hm₂ := measurable_pair_const (X n) (hXm n) g₂
    exact ((((continuous_normChart d h k l β (Nseq n) hβ (hN0 n)).measurable.comp hm₁).sub
      ((continuous_limChart d h k hk l β hl hβ hmin).measurable.comp hm₁)).prodMk
      (((continuous_normChart d h k l β (Nseq n) hβ (hN0 n)).measurable.comp hm₂).sub
      ((continuous_limChart d h k hk l β hl hβ hmin).measurable.comp hm₂))).aemeasurable
  have hsum := hlim.add_of_tendstoInMeasure_const herr hmeas
  refine hsum.congr (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
  · simp only [Pi.add_apply, Function.comp, Prod.mk_add_mk]
    congr 1 <;> ring
  · simp

/-- **Headline XVII (random phase, per-stratum posterior expectation, general dimension)**: for
deterministic continuous `φ` and `c > 0` on the closed cube and a random phase `X n ⇒ Z` in
`C([0,1]^d)`, the posterior quotient converges in distribution to the quotient of the limit
coefficients at the limiting phase. -/
theorem tendstoInDistribution_phase_posterior (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (X : ι → Ω → C(closedCube (d + 1), ℝ))
    (hXm : ∀ n, Measurable (X n)) (Z : Ω' → C(closedCube (d + 1), ℝ)) (hZm : Measurable Z)
    (hX : TendstoInDistribution X L Z (fun _ => μ) μ') (Nseq : ι → ℝ) (hN : Tendsto Nseq L atTop)
    (hN1 : ∀ n, 1 < Nseq n) (φ c : C(closedCube (d + 1), ℝ)) (hcpos : ∀ x, 0 < c x) :
    TendstoInDistribution (fun n ω =>
        chartIntegral (d + 1) h k β (Nseq n) (extCube (X n ω)) (extCube (φ * c)) /
          chartIntegral (d + 1) h k β (Nseq n) (extCube (X n ω)) (extCube c)) L
      (fun ω => limChart h k l β (Z ω, φ * c) / limChart h k l β (Z ω, c)) (fun _ => μ) μ' := by
  have hN0 : ∀ n, 0 ≤ Nseq n := fun n => by linarith [hN1 n]
  have hpair := tendstoInDistribution_normChart_pair d h k hk l β hl hβ hmin hatt X hXm Z hZm hX
    Nseq hN hN0 (φ * c) c
  have hcpos' : ∀ x ∈ closedCube (d + 1), 0 < extCube c x := fun x _ => hcpos _
  have hpos : ∀ᵐ ω ∂μ', 0 < limChart h k l β (Z ω, c) := Eventually.of_forall fun ω =>
    phaseCoeff_pos (d + 1) h k hk l β hl hβ hmin (extCube (Z ω)) (extCube c)
      (continuous_extCube _) (continuous_extCube _) hcpos'
  have hmU : ∀ n, Measurable (fun ω => normChart h k l β (Nseq n) (X n ω, φ * c)) := fun n =>
    (continuous_normChart d h k l β (Nseq n) hβ (hN0 n)).measurable.comp
      (measurable_pair_const (X n) (hXm n) _)
  have hmV : ∀ n, Measurable (fun ω => normChart h k l β (Nseq n) (X n ω, c)) := fun n =>
    (continuous_normChart d h k l β (Nseq n) hβ (hN0 n)).measurable.comp
      (measurable_pair_const (X n) (hXm n) _)
  have hmU₀ : Measurable (fun ω => limChart h k l β (Z ω, φ * c)) :=
    (continuous_limChart d h k hk l β hl hβ hmin).measurable.comp (measurable_pair_const Z hZm _)
  have hmV₀ : Measurable (fun ω => limChart h k l β (Z ω, c)) :=
    (continuous_limChart d h k hk l β hl hβ hmin).measurable.comp (measurable_pair_const Z hZm _)
  have hdiv := tendstoInDistribution_div_of_pos _ _ _ _ hmU hmV hmU₀ hmV₀ hpair hpos
  refine hdiv.congr (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => rfl)
  unfold normChart
  have hS : leadScale h k l (Nseq n) ≠ 0 := by
    have hN0' : 0 < Nseq n := by linarith [hN1 n]
    exact (mul_pos (Real.rpow_pos_of_pos hN0' _) (pow_pos (Real.log_pos (hN1 n)) _)).ne'
  exact div_div_div_cancel_right₀ hS _ _

/-- **Equal ratios**: the random posterior expectation converges to the deterministic corner value
`φ(0)`, whatever the limiting phase. -/
theorem tendstoInDistribution_phase_posterior_equal (m : ℕ) (h k : Fin (m + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hratio : ∀ i, ratioExp h k i = l)
    (X : ι → Ω → C(closedCube (m + 1), ℝ)) (hXm : ∀ n, Measurable (X n))
    (Z : Ω' → C(closedCube (m + 1), ℝ)) (hZm : Measurable Z)
    (hX : TendstoInDistribution X L Z (fun _ => μ) μ') (Nseq : ι → ℝ) (hN : Tendsto Nseq L atTop)
    (hN1 : ∀ n, 1 < Nseq n) (φ c : C(closedCube (m + 1), ℝ)) (hcpos : ∀ x, 0 < c x) :
    TendstoInDistribution (fun n ω =>
        chartIntegral (m + 1) h k β (Nseq n) (extCube (X n ω)) (extCube (φ * c)) /
          chartIntegral (m + 1) h k β (Nseq n) (extCube (X n ω)) (extCube c)) L
      (fun _ => φ ⟨0, fun _ _ => ⟨le_rfl, zero_le_one⟩⟩) (fun _ => μ) μ' := by
  have hT := tendstoInDistribution_phase_posterior m h k hk l β hl hβ (fun i => (hratio i).symm.le)
    ⟨0, hratio 0⟩ X hXm Z hZm hX Nseq hN hN1 φ c hcpos
  refine hT.congr (fun n => Eventually.of_forall fun ω => rfl) (Eventually.of_forall fun ω => ?_)
  unfold limChart
  rw [phaseCoeff_equal m h k l β hratio, phaseCoeff_equal m h k l β hratio]
  have hc0 : extCube c 0 ≠ 0 := (hcpos _).ne'
  have hJ : phaseMoment β (2 * l) (extCube (Z ω) 0) ≠ 0 :=
    (phaseMoment_pos β (2 * l) _ hβ (by positivity)).ne'
  have hK : ((m.factorial : ℝ) * ∏ i, (k i : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < ∏ i, (k i : ℝ) := Finset.prod_pos fun i _ => by exact_mod_cast hk i
    positivity
  rw [extCube_mul]
  simp only []
  rw [div_div_div_cancel_right₀ hK, mul_div_mul_right _ _ hJ, mul_div_cancel_right₀ _ hc0]
  simp only [extCube]
  congr 1
  exact Subtype.ext (clampCube_of_mem fun i _ => ⟨le_rfl, zero_le_one⟩)

end Laplace.Grammar
