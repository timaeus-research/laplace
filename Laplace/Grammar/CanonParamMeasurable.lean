/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.ParamMeasurable

/-!
# Measurability of the canonical coefficients in the parameter (grammar §4.2, Astra #10 rank 3)

For a coefficient family jointly measurable in `(w, s)` with a common radius, the canonical
coefficient functions `U_α, V_α, C_α` are jointly measurable in `(w, s)` (via the series formulas
of unit 125: a canonical face coefficient is a `tsum` of measurable terms converging everywhere),
and the log moments of jointly measurable functions are measurable in the parameter
(`logMoment_param_measurable`, a parametric Bochner integral). Hence `w ↦ A_α(w)` and
`w ↦ B_α(w)` are measurable (`canonA_param_measurable`, `canonB_param_measurable`), and the
averaged Taylor tree holds with NO measurability hypotheses beyond joint measurability of the family
(`twoD_taylor_tree_integrated'`, `twoD_taylor_tree_expectation'`). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics Topology

namespace Laplace.Grammar

/-- A pointwise-convergent series of measurable functions is measurable. -/
theorem measurable_tsum_of_summable {X : Type*} [MeasurableSpace X] (term : ℕ → X → ℝ)
    (hm : ∀ j, Measurable (term j)) (hs : ∀ x, Summable fun j => term j x) :
    Measurable fun x => ∑' j, term j x :=
  measurable_of_tendsto_metrizable' atTop (fun F => Finset.measurable_sum F fun j _ => hm j)
    (tendsto_pi_nhds.2 fun x => (hs x).hasSum)

/-- Parametric log moments are measurable. -/
theorem logMoment_param_measurable {Ω : Type*} [MeasurableSpace Ω] (β α : ℝ) (ℓ : ℕ)
    (f : Ω → ℝ → ℝ) (hf : Measurable fun p : Ω × ℝ => f p.1 p.2) :
    Measurable fun w => logMoment β α ℓ (f w) := by
  unfold logMoment
  have hF : Measurable fun p : Ω × ℝ =>
      p.2 ^ (α - 1) * Real.log p.2 ^ ℓ * (Real.exp (-β * p.2 ^ 2) * f p.1 p.2) :=
    ((measurable_snd.pow_const _).mul ((Real.measurable_log.comp measurable_snd).pow_const _)).mul
      ((Real.measurable_exp.comp (measurable_const.mul (measurable_snd.pow_const 2))).mul hf)
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi 0))).measurable

/-- The collision coefficient is jointly measurable. -/
theorem canonC_param_measurable {Ω : Type*} [MeasurableSpace Ω] (h₁ h₂ k₁ k₂ : ℕ)
    (c : Ω → ℕ × ℕ → ℝ → ℝ) (hcm : ∀ ij, Measurable fun p : Ω × ℝ => c p.1 ij p.2) (α : ℝ) :
    Measurable fun p : Ω × ℝ => canonC h₁ h₂ k₁ k₂ (fun i j s => c p.1 (i, j) s) α p.2 := by
  by_cases hP : uExp h₁ k₁ (uIdx h₁ k₁ α) = α ∧ vExp h₂ k₂ (vIdx h₂ k₂ α) = α
  · simp only [canonC, hP, and_self, if_true]
    exact (hcm _).div_const _
  · simp only [canonC, hP, if_false]
    exact measurable_const

/-- The canonical `u`-face coefficient is jointly measurable (via its series formula). -/
theorem canonU_param_measurable {Ω : Type*} [MeasurableSpace Ω] (b ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ)
    (hb : 0 < b) (hbρ : b < ρ) (hk₁ : 0 < k₁) (c : Ω → ℕ × ℕ → ℝ → ℝ)
    (hcm : ∀ ij, Measurable fun p : Ω × ℝ => c p.1 ij p.2) (H : Ω → ℝ → ℝ)
    (hc : ∀ w ij s, |c w ij s| * ρ ^ (ij.1 + ij.2) ≤ H w s) (α : ℝ) :
    Measurable fun p : Ω × ℝ =>
      canonU b h₁ h₂ k₁ k₂ (anaFaceU (c p.1) b) (fun i j s => c p.1 (i, j) s) α p.2 := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  by_cases hP : uExp h₁ k₁ (uIdx h₁ k₁ α) = α
  · obtain ⟨i, rfl⟩ : ∃ i, uExp h₁ k₁ i = α := ⟨_, hP⟩
    set γ : ℝ := (k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1 with hγ
    have hfun : (fun p : Ω × ℝ => canonU b h₁ h₂ k₁ k₂ (anaFaceU (c p.1) b)
        (fun i j s => c p.1 (i, j) s) (uExp h₁ k₁ i) p.2)
        = fun p => 1 / (k₁ : ℝ) * ∑' j : ℕ, c p.1 (i, j) p.2 * axisPrim γ b j := by
      funext p
      rw [canonU_anaFaceU_series (c p.1) b ρ (H p.1) h₁ h₂ k₁ k₂ hb hbρ hk₁ (hc p.1) i]
    rw [hfun]
    refine measurable_const.mul (measurable_tsum_of_summable
      (fun j (p : Ω × ℝ) => c p.1 (i, j) p.2 * axisPrim γ b j) (fun j => (hcm (i, j)).mul_const _) ?_)
    intro p
    exact (axisFinitePart_series γ b ρ _ hb hbρ (fun j => c p.1 (i, j) p.2)
      (row_majorant (c p.1) ρ (H p.1) hρ (hc p.1) i p.2) (canonicalM γ) (lt_canonicalM γ)).1
  · have hno : ∀ i, uExp h₁ k₁ i ≠ α := fun i h => hP (by rw [← h, uIdx_uExp h₁ k₁ hk₁ i])
    have hfun : (fun p : Ω × ℝ => canonU b h₁ h₂ k₁ k₂ (anaFaceU (c p.1) b)
        (fun i j s => c p.1 (i, j) s) α p.2) = fun _ => 0 := by
      funext p
      rw [canonU_of_not b h₁ h₂ k₁ k₂ _ _ α hno]
    rw [hfun]
    exact measurable_const

/-- The canonical `v`-face coefficient is jointly measurable. -/
theorem canonV_param_measurable {Ω : Type*} [MeasurableSpace Ω] (b ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ)
    (hb : 0 < b) (hbρ : b < ρ) (hk₂ : 0 < k₂) (c : Ω → ℕ × ℕ → ℝ → ℝ)
    (hcm : ∀ ij, Measurable fun p : Ω × ℝ => c p.1 ij p.2) (H : Ω → ℝ → ℝ)
    (hc : ∀ w ij s, |c w ij s| * ρ ^ (ij.1 + ij.2) ≤ H w s) (α : ℝ) :
    Measurable fun p : Ω × ℝ =>
      canonV b h₁ h₂ k₁ k₂ (anaFaceV (c p.1) b) (fun i j s => c p.1 (i, j) s) α p.2 := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  by_cases hP : vExp h₂ k₂ (vIdx h₂ k₂ α) = α
  · obtain ⟨j, rfl⟩ : ∃ j, vExp h₂ k₂ j = α := ⟨_, hP⟩
    set γ : ℝ := (k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1 with hγ
    have hfun : (fun p : Ω × ℝ => canonV b h₁ h₂ k₁ k₂ (anaFaceV (c p.1) b)
        (fun i j s => c p.1 (i, j) s) (vExp h₂ k₂ j) p.2)
        = fun p => 1 / (k₂ : ℝ) * ∑' i : ℕ, c p.1 (i, j) p.2 * axisPrim γ b i := by
      funext p
      rw [canonV_anaFaceV_series (c p.1) b ρ (H p.1) h₁ h₂ k₁ k₂ hb hbρ hk₂ (hc p.1) j]
    rw [hfun]
    refine measurable_const.mul (measurable_tsum_of_summable
      (fun i (p : Ω × ℝ) => c p.1 (i, j) p.2 * axisPrim γ b i) (fun i => (hcm (i, j)).mul_const _) ?_)
    intro p
    exact (axisFinitePart_series γ b ρ _ hb hbρ (fun i => c p.1 (i, j) p.2)
      (col_majorant (c p.1) ρ (H p.1) hρ (hc p.1) j p.2) (canonicalM γ) (lt_canonicalM γ)).1
  · have hno : ∀ j, vExp h₂ k₂ j ≠ α := fun j h => hP (by rw [← h, vIdx_vExp h₂ k₂ hk₂ j])
    have hfun : (fun p : Ω × ℝ => canonV b h₁ h₂ k₁ k₂ (anaFaceV (c p.1) b)
        (fun i j s => c p.1 (i, j) s) α p.2) = fun _ => 0 := by
      funext p
      rw [canonV_of_not b h₁ h₂ k₁ k₂ _ _ α hno]
    rw [hfun]
    exact measurable_const

/-- **The canonical log coefficient is measurable in the parameter.** -/
theorem canonA_param_measurable {Ω : Type*} [MeasurableSpace Ω] (β : ℝ) (h₁ h₂ k₁ k₂ : ℕ)
    (c : Ω → ℕ × ℕ → ℝ → ℝ) (hcm : ∀ ij, Measurable fun p : Ω × ℝ => c p.1 ij p.2) (α : ℝ) :
    Measurable fun w => canonA β h₁ h₂ k₁ k₂ (fun i j s => c w (i, j) s) α :=
  logMoment_param_measurable β α 0 (fun w => canonC h₁ h₂ k₁ k₂ (fun i j s => c w (i, j) s) α)
    (canonC_param_measurable h₁ h₂ k₁ k₂ c hcm α)

/-- **The canonical constant coefficient is measurable in the parameter.** -/
theorem canonB_param_measurable {Ω : Type*} [MeasurableSpace Ω] (β b ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ)
    (hb : 0 < b) (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (c : Ω → ℕ × ℕ → ℝ → ℝ)
    (hcm : ∀ ij, Measurable fun p : Ω × ℝ => c p.1 ij p.2) (H : Ω → ℝ → ℝ)
    (hc : ∀ w ij s, |c w ij s| * ρ ^ (ij.1 + ij.2) ≤ H w s) (α : ℝ) :
    Measurable fun w => canonB β b h₁ h₂ k₁ k₂ (anaFaceU (c w) b) (anaFaceV (c w) b)
      (fun i j s => c w (i, j) s) α := by
  unfold canonB
  refine ((logMoment_param_measurable β α 0 _ ?_).add (logMoment_param_measurable β α 0 _ ?_)).sub
    (logMoment_param_measurable β α 1 _ (canonC_param_measurable h₁ h₂ k₁ k₂ c hcm α))
  · exact canonU_param_measurable b ρ h₁ h₂ k₁ k₂ hb hbρ hk₁ c hcm H hc α
  · exact canonV_param_measurable b ρ h₁ h₂ k₁ k₂ hb hbρ hk₂ c hcm H hc α

/-- **The averaged Taylor tree, with joint measurability of the family as the only measurability
hypothesis.** -/
theorem twoD_taylor_tree_integrated' {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (β b p₁ p₂ ρ C₀ L : ℝ) (h₁ h₂ k₁ k₂ D : ℕ) (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (c : Ω → ℕ × ℕ → ℝ → ℝ)
    (hcc : ∀ w ij, Continuous (c w ij)) (hcm : ∀ ij, Measurable fun p : Ω × ℝ => c p.1 ij p.2)
    (H : Ω → ℝ → ℝ) (hH : ∀ w, Continuous (H w))
    (hc : ∀ w ij s, |c w ij s| * ρ ^ (ij.1 + ij.2) ≤ H w s) (hC₀ : 0 ≤ C₀)
    (henv : ∀ w s, 0 ≤ s → H w s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L))
    (ϱ : Ω → ℝ) (hϱ0 : ∀ᵐ w ∂μ, 0 ≤ ϱ w) (hϱ : Integrable ϱ μ) (T N : ℝ) (hN : 1 ≤ N) :
    |(∫ w, twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (c w) b) * ϱ w ∂μ)
        - ∑ α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T,
            N ^ (-α) * ((∫ w, canonA β h₁ h₂ k₁ k₂ (fun i j s => c w (i, j) s) α * ϱ w ∂μ)
                * Real.log N
              + ∫ w, canonB β b h₁ h₂ k₁ k₂ (anaFaceU (c w) b) (anaFaceV (c w) b)
                  (fun i j s => c w (i, j) s) α * ϱ w ∂μ)|
      ≤ uniformTreeConst β b ρ C₀ L p₁ p₂ T h₁ h₂ k₁ k₂ D * (N ^ (-(2 * T)) * (1 + Real.log N))
        * ∫ w, ϱ w ∂μ :=
  twoD_taylor_tree_integrated μ β b p₁ p₂ ρ C₀ L h₁ h₂ k₁ k₂ D hβ hb hbρ hk₁ hk₂ hp₁ hp₂ c hcc H
    hH hc hC₀ henv ϱ hϱ0 hϱ T N hN
    (twoDAmp_param_aestronglyMeasurable μ β b N ρ h₁ h₂ k₁ k₂ hb hbρ c hcc hcm H hH hc)
    (fun α _ => (canonA_param_measurable β h₁ h₂ k₁ k₂ c hcm α).aestronglyMeasurable)
    (fun α _ => (canonB_param_measurable β b ρ h₁ h₂ k₁ k₂ hb hbρ hk₁ hk₂ c hcm H hc
      α).aestronglyMeasurable)

/-- **The expected Taylor tree**, with joint measurability of the random amplitude as the only
measurability hypothesis. -/
theorem twoD_taylor_tree_expectation' {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (β b p₁ p₂ ρ C₀ L : ℝ) (h₁ h₂ k₁ k₂ D : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (c : Ω → ℕ × ℕ → ℝ → ℝ)
    (hcc : ∀ w ij, Continuous (c w ij)) (hcm : ∀ ij, Measurable fun p : Ω × ℝ => c p.1 ij p.2)
    (H : Ω → ℝ → ℝ) (hH : ∀ w, Continuous (H w))
    (hc : ∀ w ij s, |c w ij s| * ρ ^ (ij.1 + ij.2) ≤ H w s) (hC₀ : 0 ≤ C₀)
    (henv : ∀ w s, 0 ≤ s → H w s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (T N : ℝ)
    (hN : 1 ≤ N) :
    |(∫ w, twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (c w) b) ∂μ)
        - ∑ α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T,
            N ^ (-α) * ((∫ w, canonA β h₁ h₂ k₁ k₂ (fun i j s => c w (i, j) s) α ∂μ)
                * Real.log N
              + ∫ w, canonB β b h₁ h₂ k₁ k₂ (anaFaceU (c w) b) (anaFaceV (c w) b)
                  (fun i j s => c w (i, j) s) α ∂μ)|
      ≤ uniformTreeConst β b ρ C₀ L p₁ p₂ T h₁ h₂ k₁ k₂ D
        * (N ^ (-(2 * T)) * (1 + Real.log N)) :=
  twoD_taylor_tree_expectation μ β b p₁ p₂ ρ C₀ L h₁ h₂ k₁ k₂ D hβ hb hbρ hk₁ hk₂ hp₁ hp₂ c hcc
    H hH hc hC₀ henv T N hN
    (twoDAmp_param_aestronglyMeasurable μ β b N ρ h₁ h₂ k₁ k₂ hb hbρ c hcc hcm H hH hc)
    (fun α _ => (canonA_param_measurable β h₁ h₂ k₁ k₂ c hcm α).aestronglyMeasurable)
    (fun α _ => (canonB_param_measurable β b ρ h₁ h₂ k₁ k₂ hb hbρ hk₁ hk₂ c hcm H hc
      α).aestronglyMeasurable)

end Laplace.Grammar
