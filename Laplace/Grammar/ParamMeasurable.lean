/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.FiniteTreeIntegration

/-!
# Measurability of the chart integral in the parameter (grammar §4.2, Astra #10 rank 2)

For a coefficient family `c : Ω → ℕ×ℕ → ℝ → ℝ` that is jointly measurable in `(w, s)` and has a
common radius `ρ > b`, the parametrised amplitude
`(w, z) ↦ anaAmp (c w) b z.1 z.2 (N z.1^{k₁} z.2^{k₂})` is measurable (`anaAmp_param_measurable`: rectangular partial sums are measurable and
converge everywhere on the box, so the limit is measurable), hence so is the product integrand,
and the
parametric Bochner integral gives measurability of `w ↦ Z_w(N)` (`twoDAmp_param_measurable`).
This discharges the first measurability hypothesis of `twoD_taylor_tree_integrated`. Zero
`sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics Topology

namespace Laplace.Grammar

/-- The phase variable `(w, z) ↦ N z.1^{k₁} z.2^{k₂}` is measurable. -/
theorem phase_param_measurable {Ω : Type*} [MeasurableSpace Ω] (N : ℝ) (k₁ k₂ : ℕ) :
    Measurable fun p : Ω × (ℝ × ℝ) => N * (p.2.1 ^ k₁ * p.2.2 ^ k₂) :=
  measurable_const.mul (((measurable_fst.comp measurable_snd).pow_const k₁).mul
    ((measurable_snd.comp measurable_snd).pow_const k₂))

/-- **The parametrised amplitude is measurable** for a jointly measurable family with a common
radius. -/
theorem anaAmp_param_measurable {Ω : Type*} [MeasurableSpace Ω] (b N ρ : ℝ) (k₁ k₂ : ℕ)
    (hb : 0 < b) (hbρ : b < ρ) (c : Ω → ℕ × ℕ → ℝ → ℝ)
    (hcm : ∀ ij, Measurable fun p : Ω × ℝ => c p.1 ij p.2) (H : Ω → ℝ → ℝ)
    (hc : ∀ w ij s, |c w ij s| * ρ ^ (ij.1 + ij.2) ≤ H w s) :
    Measurable fun p : Ω × (ℝ × ℝ) =>
      anaAmp (c p.1) b p.2.1 p.2.2 (N * (p.2.1 ^ k₁ * p.2.2 ^ k₂)) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hsm := phase_param_measurable (Ω := Ω) N k₁ k₂
  set term : ℕ × ℕ → Ω × (ℝ × ℝ) → ℝ := fun ij p =>
    c p.1 ij (N * (p.2.1 ^ k₁ * p.2.2 ^ k₂)) * clampB b p.2.1 ^ ij.1 * clampB b p.2.2 ^ ij.2
    with hterm
  have htm : ∀ ij, Measurable (term ij) := fun ij => by
    simp only [hterm]
    have hu : Measurable fun p : Ω × (ℝ × ℝ) => clampB b p.2.1 :=
      (clampB_continuous b).measurable.comp (measurable_fst.comp measurable_snd)
    have hv : Measurable fun p : Ω × (ℝ × ℝ) => clampB b p.2.2 :=
      (clampB_continuous b).measurable.comp (measurable_snd.comp measurable_snd)
    exact (((hcm ij).comp (measurable_fst.prodMk hsm)).mul (hu.pow_const _)).mul (hv.pow_const _)
  have hsum : ∀ p : Ω × (ℝ × ℝ), HasSum (fun ij => term ij p)
      (anaAmp (c p.1) b p.2.1 p.2.2 (N * (p.2.1 ^ k₁ * p.2.2 ^ k₂))) := by
    intro p
    have hH0 : 0 ≤ H p.1 (N * (p.2.1 ^ k₁ * p.2.2 ^ k₂)) :=
      le_trans (by positivity) (hc p.1 (0, 0) _)
    have hu : clampB b p.2.1 < ρ := lt_of_le_of_lt (clampB_le b _ hb.le) hbρ
    have hv : clampB b p.2.2 < ρ := lt_of_le_of_lt (clampB_le b _ hb.le) hbρ
    have := dbl_summable (fun ij => c p.1 ij (N * (p.2.1 ^ k₁ * p.2.2 ^ k₂))) ρ _
      (clampB b p.2.1) (clampB b p.2.2) hρ hH0 (fun ij => hc p.1 ij _) (clampB_nonneg _ _) hu
      (clampB_nonneg _ _) hv
    exact this.hasSum
  have htend : Tendsto (fun F : Finset (ℕ × ℕ) => fun p => ∑ ij ∈ F, term ij p) atTop
      (𝓝 fun p => anaAmp (c p.1) b p.2.1 p.2.2 (N * (p.2.1 ^ k₁ * p.2.2 ^ k₂))) :=
    tendsto_pi_nhds.2 fun p => hsum p
  exact measurable_of_tendsto_metrizable' atTop
    (fun F => Finset.measurable_sum F fun ij _ => htm ij) htend

/-- The parametrised product integrand is measurable. -/
theorem twoDIntegrand_param_measurable {Ω : Type*} [MeasurableSpace Ω] (β b N ρ : ℝ)
    (h₁ h₂ k₁ k₂ : ℕ) (hb : 0 < b) (hbρ : b < ρ) (c : Ω → ℕ × ℕ → ℝ → ℝ)
    (hcm : ∀ ij, Measurable fun p : Ω × ℝ => c p.1 ij p.2) (H : Ω → ℝ → ℝ)
    (hc : ∀ w ij s, |c w ij s| * ρ ^ (ij.1 + ij.2) ≤ H w s) :
    Measurable fun p : Ω × (ℝ × ℝ) =>
      twoDIntegrand β N h₁ h₂ k₁ k₂ (anaAmp (c p.1) b) p.2 := by
  have hsm := phase_param_measurable (Ω := Ω) N k₁ k₂
  unfold twoDIntegrand
  exact ((measurable_fst.comp measurable_snd).pow_const _).mul
    (((measurable_snd.comp measurable_snd).pow_const _).mul
      ((Real.measurable_exp.comp (measurable_const.mul (hsm.pow_const 2))).mul
        (anaAmp_param_measurable b N ρ k₁ k₂ hb hbρ c hcm H hc)))

/-- **The chart integral is measurable in the parameter.** -/
theorem twoDAmp_param_measurable {Ω : Type*} [MeasurableSpace Ω] (β b N ρ : ℝ)
    (h₁ h₂ k₁ k₂ : ℕ) (hb : 0 < b) (hbρ : b < ρ) (c : Ω → ℕ × ℕ → ℝ → ℝ)
    (hcc : ∀ w ij, Continuous (c w ij)) (hcm : ∀ ij, Measurable fun p : Ω × ℝ => c p.1 ij p.2)
    (H : Ω → ℝ → ℝ) (hH : ∀ w, Continuous (H w))
    (hc : ∀ w ij s, |c w ij s| * ρ ^ (ij.1 + ij.2) ≤ H w s) :
    Measurable fun w => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (c w) b) := by
  have hF := twoDIntegrand_param_measurable β b N ρ h₁ h₂ k₁ k₂ hb hbρ c hcm H hc
  have : SFinite (boxMeasure₂ b) := by unfold boxMeasure₂; infer_instance
  have hmeas : Measurable fun w =>
      ∫ z, twoDIntegrand β N h₁ h₂ k₁ k₂ (anaAmp (c w) b) z ∂(boxMeasure₂ b) :=
    (hF.stronglyMeasurable.integral_prod_right').measurable
  have heq : (fun w => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (c w) b))
      = fun w => ∫ z, twoDIntegrand β N h₁ h₂ k₁ k₂ (anaAmp (c w) b) z ∂(boxMeasure₂ b) :=
    funext fun w => twoDAmp_eq_prod β b N h₁ h₂ k₁ k₂ _
      (anaAmp_continuous (c w) b ρ (H w) hb hbρ (hcc w) (hH w) (hc w))
  rw [heq]
  exact hmeas

/-- The a.e.-strongly-measurable form used by `twoD_taylor_tree_integrated`. -/
theorem twoDAmp_param_aestronglyMeasurable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (β b N ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hb : 0 < b) (hbρ : b < ρ) (c : Ω → ℕ × ℕ → ℝ → ℝ)
    (hcc : ∀ w ij, Continuous (c w ij)) (hcm : ∀ ij, Measurable fun p : Ω × ℝ => c p.1 ij p.2)
    (H : Ω → ℝ → ℝ) (hH : ∀ w, Continuous (H w))
    (hc : ∀ w ij s, |c w ij s| * ρ ^ (ij.1 + ij.2) ≤ H w s) :
    AEStronglyMeasurable (fun w => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (c w) b)) μ :=
  (twoDAmp_param_measurable β b N ρ h₁ h₂ k₁ k₂ hb hbρ c hcc hcm H hH hc).aestronglyMeasurable

end Laplace.Grammar
