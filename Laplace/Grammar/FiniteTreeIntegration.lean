/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LeadingUnequal

/-!
# Integrating a finite expansion over parameters (grammar §4.2, Astra #10 rank 1)

`integral_finite_expansion`: an abstract lemma with no analytic machinery. If, for a.e. parameter
`w`, `|Z(w) − ∑_{α∈P} N^{−α}(A_α(w) log N + B_α(w))| ≤ K R` with a.e.-bounded, a.e.-strongly
measurable coefficients and a nonnegative integrable weight `ϱ`, then

  `|∫ Z ϱ − ∑_{α∈P} N^{−α}((∫ A_α ϱ) log N + ∫ B_α ϱ)| ≤ K R ∫ ϱ`.

No separate integrability of `Z` is needed. Specialisation `twoD_taylor_tree_integrated`: a
measurable family of analytic amplitudes with a common envelope has the SAME finite Taylor tree
after averaging over the parameters, with averaged canonical coefficients and the remainder
constant multiplied by the mass of the weight (measurability of the chart integral and of the
canonical coefficients in the parameter is taken as a hypothesis here). Probability corollary
`twoD_taylor_tree_expectation`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- **Abstract finite-expansion integration.** -/
theorem integral_finite_expansion {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (P : Finset ℝ)
    (Z : Ω → ℝ) (A B : ℝ → Ω → ℝ) (ϱ : Ω → ℝ) (hϱ0 : ∀ᵐ w ∂μ, 0 ≤ ϱ w) (hϱ : Integrable ϱ μ)
    (hZm : AEStronglyMeasurable Z μ) (hAm : ∀ α ∈ P, AEStronglyMeasurable (A α) μ)
    (hBm : ∀ α ∈ P, AEStronglyMeasurable (B α) μ) (KA KB : ℝ → ℝ)
    (hA : ∀ α ∈ P, ∀ᵐ w ∂μ, |A α w| ≤ KA α) (hB : ∀ α ∈ P, ∀ᵐ w ∂μ, |B α w| ≤ KB α)
    (K R N : ℝ)
    (hrem : ∀ᵐ w ∂μ, |Z w - ∑ α ∈ P, N ^ (-α) * (A α w * Real.log N + B α w)| ≤ K * R) :
    |(∫ w, Z w * ϱ w ∂μ)
        - ∑ α ∈ P, N ^ (-α) * ((∫ w, A α w * ϱ w ∂μ) * Real.log N + ∫ w, B α w * ϱ w ∂μ)|
      ≤ K * R * ∫ w, ϱ w ∂μ := by
  set E : Ω → ℝ := fun w => Z w - ∑ α ∈ P, N ^ (-α) * (A α w * Real.log N + B α w) with hE
  have hEm : AEStronglyMeasurable E μ := by
    refine hZm.sub ?_
    have hS : AEStronglyMeasurable
        (∑ α ∈ P, fun w => N ^ (-α) * (A α w * Real.log N + B α w)) μ :=
      Finset.aestronglyMeasurable_sum P fun α hα =>
        (((hAm α hα).mul_const _).add (hBm α hα)).const_mul _
    exact hS.congr (Filter.Eventually.of_forall fun w => by simp only [Finset.sum_apply])
  have hEi : Integrable (fun w => E w * ϱ w) μ :=
    hϱ.bdd_mul hEm (by filter_upwards [hrem] with w hw; rw [Real.norm_eq_abs]; exact hw)
  have hAi : ∀ α ∈ P, Integrable (fun w => A α w * ϱ w) μ := fun α hα =>
    hϱ.bdd_mul (hAm α hα)
      (by filter_upwards [hA α hα] with w hw; rw [Real.norm_eq_abs]; exact hw)
  have hBi : ∀ α ∈ P, Integrable (fun w => B α w * ϱ w) μ := fun α hα =>
    hϱ.bdd_mul (hBm α hα)
      (by filter_upwards [hB α hα] with w hw; rw [Real.norm_eq_abs]; exact hw)
  have hTi : ∀ α ∈ P, Integrable
      (fun w => N ^ (-α) * (Real.log N * (A α w * ϱ w) + B α w * ϱ w)) μ := fun α hα =>
    (((hAi α hα).const_mul _).add (hBi α hα)).const_mul _
  have hsum : ∀ w, Z w * ϱ w
      = E w * ϱ w + ∑ α ∈ P, N ^ (-α) * (Real.log N * (A α w * ϱ w) + B α w * ϱ w) := by
    intro w
    have : ∑ α ∈ P, N ^ (-α) * (A α w * Real.log N + B α w) * ϱ w
        = ∑ α ∈ P, N ^ (-α) * (Real.log N * (A α w * ϱ w) + B α w * ϱ w) :=
      Finset.sum_congr rfl fun α _ => by ring
    simp only [hE]
    rw [sub_mul, Finset.sum_mul, this]
    ring
  have hint : ∫ w, Z w * ϱ w ∂μ
      = ∫ w, E w * ϱ w ∂μ
        + ∑ α ∈ P, N ^ (-α) * (Real.log N * ∫ w, A α w * ϱ w ∂μ + ∫ w, B α w * ϱ w ∂μ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hsum),
      integral_add hEi (integrable_finsetSum P hTi), integral_finsetSum P hTi]
    congr 1
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [integral_const_mul, integral_add ((hAi α hα).const_mul _) (hBi α hα), integral_const_mul]
  have hbound : |∫ w, E w * ϱ w ∂μ| ≤ K * R * ∫ w, ϱ w ∂μ := by
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hϱ.const_mul _) ?_
    filter_upwards [hrem, hϱ0] with w hw hw0
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_right hw hw0
  rw [hint, show (∑ α ∈ P, N ^ (-α) * (Real.log N * ∫ w, A α w * ϱ w ∂μ + ∫ w, B α w * ϱ w ∂μ))
      = ∑ α ∈ P, N ^ (-α) * ((∫ w, A α w * ϱ w ∂μ) * Real.log N + ∫ w, B α w * ϱ w ∂μ) from
      Finset.sum_congr rfl fun α _ => by ring, add_sub_cancel_right]
  exact hbound

/-- Every retained pole is positive. -/
theorem pos_of_mem_polesBelowGen (h₁ h₂ k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (p₁ p₂ T α : ℝ)
    (hα : α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) : 0 < α := by
  unfold polesBelowGen at hα
  exact pos_of_mem_poleSet h₁ h₂ k₁ k₂ _ _ hk₁ hk₂ α (Finset.mem_filter.1 hα).1

/-- **The Taylor tree commutes with parameter averaging.** For a family of analytic amplitudes
with a common envelope and a nonnegative integrable weight, the averaged chart integral has the same
finite Taylor tree with averaged canonical coefficients; the remainder constant is multiplied by the
mass of the weight. Measurability in the parameter is assumed. -/
theorem twoD_taylor_tree_integrated {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (β b p₁ p₂ ρ C₀ L : ℝ) (h₁ h₂ k₁ k₂ D : ℕ) (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (c : Ω → ℕ × ℕ → ℝ → ℝ)
    (hcc : ∀ w ij, Continuous (c w ij)) (H : Ω → ℝ → ℝ) (hH : ∀ w, Continuous (H w))
    (hc : ∀ w ij s, |c w ij s| * ρ ^ (ij.1 + ij.2) ≤ H w s) (hC₀ : 0 ≤ C₀)
    (henv : ∀ w s, 0 ≤ s → H w s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L))
    (ϱ : Ω → ℝ) (hϱ0 : ∀ᵐ w ∂μ, 0 ≤ ϱ w) (hϱ : Integrable ϱ μ) (T N : ℝ) (hN : 1 ≤ N)
    (hZm : AEStronglyMeasurable (fun w => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (c w) b)) μ)
    (hAm : ∀ α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T,
      AEStronglyMeasurable (fun w => canonA β h₁ h₂ k₁ k₂ (fun i j s => c w (i, j) s) α) μ)
    (hBm : ∀ α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T,
      AEStronglyMeasurable (fun w => canonB β b h₁ h₂ k₁ k₂ (anaFaceU (c w) b) (anaFaceV (c w) b)
        (fun i j s => c w (i, j) s) α) μ) :
    |(∫ w, twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (c w) b) * ϱ w ∂μ)
        - ∑ α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T,
            N ^ (-α) * ((∫ w, canonA β h₁ h₂ k₁ k₂ (fun i j s => c w (i, j) s) α * ϱ w ∂μ)
                * Real.log N
              + ∫ w, canonB β b h₁ h₂ k₁ k₂ (anaFaceU (c w) b) (anaFaceV (c w) b)
                  (fun i j s => c w (i, j) s) α * ϱ w ∂μ)|
      ≤ uniformTreeConst β b ρ C₀ L p₁ p₂ T h₁ h₂ k₁ k₂ D * (N ^ (-(2 * T)) * (1 + Real.log N))
        * ∫ w, ϱ w ∂μ := by
  refine integral_finite_expansion μ (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T)
    (fun w => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (c w) b))
    (fun α w => canonA β h₁ h₂ k₁ k₂ (fun i j s => c w (i, j) s) α)
    (fun α w => canonB β b h₁ h₂ k₁ k₂ (anaFaceU (c w) b) (anaFaceV (c w) b)
      (fun i j s => c w (i, j) s) α) ϱ hϱ0 hϱ hZm hAm hBm
    (fun α => canonCEnv ρ C₀ h₁ h₂ k₁ k₂ α * envMoment β α 0 (gaussEnv β L D))
    (fun α => canonUEnv b ρ C₀ h₁ h₂ k₁ k₂ α * envMoment β α 0 (gaussEnv β L D)
      + canonVEnv b ρ C₀ h₁ h₂ k₁ k₂ α * envMoment β α 0 (gaussEnv β L D)
      + canonCEnv ρ C₀ h₁ h₂ k₁ k₂ α * envMoment β α 1 (gaussEnv β L D))
    ?_ ?_ (uniformTreeConst β b ρ C₀ L p₁ p₂ T h₁ h₂ k₁ k₂ D)
    (N ^ (-(2 * T)) * (1 + Real.log N)) N ?_
  · intro α hα
    have hαpos := pos_of_mem_polesBelowGen h₁ h₂ k₁ k₂ hk₁ hk₂ p₁ p₂ T α hα
    exact Filter.Eventually.of_forall fun w =>
      canonA_abs_le_env (c w) b ρ C₀ L β (H w) h₁ h₂ k₁ k₂ D hβ hb hbρ hk₁ hk₂ (hcc w) (hc w)
        (henv w) α hαpos
  · intro α hα
    have hαpos := pos_of_mem_polesBelowGen h₁ h₂ k₁ k₂ hk₁ hk₂ p₁ p₂ T α hα
    exact Filter.Eventually.of_forall fun w =>
      canonB_abs_le_env (c w) b ρ C₀ L β (H w) h₁ h₂ k₁ k₂ D hβ hb hbρ hk₁ hk₂ hC₀ (hcc w) (hH w)
        (hc w) (henv w) α hαpos
  · exact Filter.Eventually.of_forall fun w =>
      twoD_taylor_tree_uniform β b p₁ p₂ ρ C₀ L h₁ h₂ k₁ k₂ D hβ hb hbρ hk₁ hk₂ hp₁ hp₂ (c w)
        (hcc w) (H w) (hH w) (hc w) hC₀ (henv w) T N hN

/-- **The expectation of the chart integral** over a random analytic amplitude with a common
envelope has the Taylor tree with expected canonical coefficients. -/
theorem twoD_taylor_tree_expectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (β b p₁ p₂ ρ C₀ L : ℝ) (h₁ h₂ k₁ k₂ D : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (c : Ω → ℕ × ℕ → ℝ → ℝ)
    (hcc : ∀ w ij, Continuous (c w ij)) (H : Ω → ℝ → ℝ) (hH : ∀ w, Continuous (H w))
    (hc : ∀ w ij s, |c w ij s| * ρ ^ (ij.1 + ij.2) ≤ H w s) (hC₀ : 0 ≤ C₀)
    (henv : ∀ w s, 0 ≤ s → H w s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (T N : ℝ)
    (hN : 1 ≤ N)
    (hZm : AEStronglyMeasurable (fun w => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (c w) b)) μ)
    (hAm : ∀ α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T,
      AEStronglyMeasurable (fun w => canonA β h₁ h₂ k₁ k₂ (fun i j s => c w (i, j) s) α) μ)
    (hBm : ∀ α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T,
      AEStronglyMeasurable (fun w => canonB β b h₁ h₂ k₁ k₂ (anaFaceU (c w) b) (anaFaceV (c w) b)
        (fun i j s => c w (i, j) s) α) μ) :
    |(∫ w, twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (c w) b) ∂μ)
        - ∑ α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T,
            N ^ (-α) * ((∫ w, canonA β h₁ h₂ k₁ k₂ (fun i j s => c w (i, j) s) α ∂μ)
                * Real.log N
              + ∫ w, canonB β b h₁ h₂ k₁ k₂ (anaFaceU (c w) b) (anaFaceV (c w) b)
                  (fun i j s => c w (i, j) s) α ∂μ)|
      ≤ uniformTreeConst β b ρ C₀ L p₁ p₂ T h₁ h₂ k₁ k₂ D
        * (N ^ (-(2 * T)) * (1 + Real.log N)) := by
  have h := twoD_taylor_tree_integrated μ β b p₁ p₂ ρ C₀ L h₁ h₂ k₁ k₂ D hβ hb hbρ hk₁ hk₂ hp₁
    hp₂ c hcc H hH hc hC₀ henv (fun _ => 1) (Filter.Eventually.of_forall fun _ => zero_le_one)
    (integrable_const 1) T N hN hZm hAm hBm
  simp only [mul_one] at h
  have h1 : ∫ _w, (1 : ℝ) ∂μ = 1 := by simp
  rw [h1, mul_one] at h
  exact h

end Laplace.Grammar
