/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.NormalCrossingLaw

/-!
# The normal-crossing example: genuine priors and positive evidence

Unit 221 (review v16 should-fix). Headlines XX–XX'' are stated for continuous weights `ρ` with
`ρ(0) > 0` and allow signed `ρ`; there the quotient `ncPosteriorMean` is an analytic object and
Lean's totalised division may return `0` at a finite sample size if the evidence vanishes. For a
**genuine prior weight** — `ρ ≥ 0` on the box and `ρ(0) > 0` — the evidence
`∫_{(-1,1]²} ρ · likelihood` is strictly positive at every sample size (`nc_evidence_pos`: `ρ` is
bounded below near the origin and the Gaussian likelihood is positive), so the posterior is a
probability measure (`ncPosteriorMean_one`: the posterior mean of `1` is `1`) and the headline
limits are statements about an actual normalised posterior. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set ProbabilityTheory

namespace Laplace.Grammar

/-- **Positive model integral for a nonnegative weight with `ρ(0) > 0`.** -/
theorem nc_integral_pos (ρ : (Fin 2 → ℝ) → ℝ) (hρ : Continuous ρ)
    (hρnn : ∀ x ∈ symBox 2, 0 ≤ ρ x) (hρ0 : 0 < ρ 0) (N z : ℝ) :
    0 < ∫ x in symBox 2, ρ x * ncKernel N z x := by
  obtain ⟨δ₁, hδ₁, hδ⟩ := Metric.continuousAt_iff.mp hρ.continuousAt (ρ 0 / 2) (by positivity)
  set δ : ℝ := min δ₁ 1 with hδdef
  have hδpos : 0 < δ := lt_min hδ₁ one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hball : Metric.ball (0 : Fin 2 → ℝ) δ ⊆ symBox 2 := by
    intro x hx
    rw [mem_ball_zero_iff, pi_norm_lt_iff hδpos] at hx
    intro i _
    have := hx i
    rw [Real.norm_eq_abs, abs_lt] at this
    exact ⟨by linarith, by linarith⟩
  set c : ℝ := ρ 0 / 2 * Real.exp (-(N ^ 2) / 2 - |N * z|) with hc
  have hcpos : 0 < c := by positivity
  have hlow : ∀ x ∈ Metric.ball (0 : Fin 2 → ℝ) δ, c ≤ ρ x * ncKernel N z x := by
    intro x hx
    have hxρ : ρ 0 / 2 ≤ ρ x := by
      have h := hδ (show dist x 0 < δ₁ from (Metric.mem_ball.mp hx).trans_le (min_le_left _ _))
      rw [Real.dist_eq, abs_lt] at h
      linarith [h.1]
    have hx' := hball hx
    have h0 : |x 0| ≤ 1 := abs_le.2 ⟨(hx' 0 (Set.mem_univ _)).1.le, (hx' 0 (Set.mem_univ _)).2⟩
    have h1 : |x 1| ≤ 1 := abs_le.2 ⟨(hx' 1 (Set.mem_univ _)).1.le, (hx' 1 (Set.mem_univ _)).2⟩
    have ht : |x 0 * x 1| ≤ 1 := by
      rw [abs_mul]
      exact mul_le_one₀ h0 (abs_nonneg _) h1
    have hxK : Real.exp (-(N ^ 2) / 2 - |N * z|) ≤ ncKernel N z x := by
      unfold ncKernel
      apply Real.exp_le_exp.2
      have hsq : (x 0 * x 1) ^ 2 ≤ 1 := by
        rw [← sq_abs]
        exact pow_le_one₀ (abs_nonneg _) ht
      have h2 : -(N ^ 2) / 2 ≤ -(N ^ 2 * (x 0 * x 1) ^ 2) / 2 := by nlinarith [sq_nonneg N]
      have h3 : -|N * z| ≤ N * z * (x 0 * x 1) := by
        calc -|N * z| ≤ -(|N * z| * |x 0 * x 1|) := by
              have := mul_le_of_le_one_right (abs_nonneg (N * z)) ht
              linarith
          _ = -|N * z * (x 0 * x 1)| := by rw [abs_mul (N * z) (x 0 * x 1)]
          _ ≤ N * z * (x 0 * x 1) := neg_abs_le _
      linarith
    calc c = ρ 0 / 2 * Real.exp (-(N ^ 2) / 2 - |N * z|) := rfl
      _ ≤ ρ x * ncKernel N z x :=
        mul_le_mul hxρ hxK (Real.exp_pos _).le ((by positivity : (0 : ℝ) ≤ ρ 0 / 2).trans hxρ)
  have hint : IntegrableOn (fun x => ρ x * ncKernel N z x) (symBox 2) :=
    integrableOn_piBox_Ioc_of_continuous 2 (-1) 1 _ (hρ.mul (continuous_ncKernel N z))
  have hnn : 0 ≤ᵐ[volume.restrict (symBox 2)] fun x => ρ x * ncKernel N z x :=
    ae_restrict_of_forall_mem (measurableSet_symBox 2) fun x hx =>
      mul_nonneg (hρnn x hx) (ncKernel_pos N z x).le
  calc (0 : ℝ) < volume.real (Metric.ball (0 : Fin 2 → ℝ) δ) • c := by
        rw [smul_eq_mul, measureReal_def]
        exact mul_pos (ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 hδpos).ne'
          measure_ball_lt_top.ne) hcpos
    _ ≤ ∫ x in Metric.ball (0 : Fin 2 → ℝ) δ, ρ x * ncKernel N z x :=
        setIntegral_ge_of_const_le Metric.isOpen_ball.measurableSet measure_ball_lt_top.ne hlow
          (hint.mono_set hball)
    _ ≤ ∫ x in symBox 2, ρ x * ncKernel N z x :=
        setIntegral_mono_set hint hnn (Filter.Eventually.of_forall hball)

/-- **Positive evidence at every sample size** for a genuine prior weight. -/
theorem nc_evidence_pos (n : ℕ) (hn : 0 < n) (y : Fin n → ℝ) (ρ : (Fin 2 → ℝ) → ℝ)
    (hρ : Continuous ρ) (hρnn : ∀ x ∈ symBox 2, 0 ≤ ρ x) (hρ0 : 0 < ρ 0) :
    0 < ∫ x in symBox 2, ρ x * ncLikelihood n y x := by
  have hC : 0 < ∏ i, gaussianPDFReal 0 1 (y i) :=
    Finset.prod_pos fun i _ => gaussianPDFReal_pos _ _ _ one_ne_zero
  simp only [ncLikelihood_eq n hn y]
  have h : ∫ x in symBox 2, ρ x * ((∏ i, gaussianPDFReal 0 1 (y i)) *
      ncKernel (Real.sqrt n) (ncPhase n y) x) = (∏ i, gaussianPDFReal 0 1 (y i)) *
      ∫ x in symBox 2, ρ x * ncKernel (Real.sqrt n) (ncPhase n y) x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [h]
  exact mul_pos hC (nc_integral_pos ρ hρ hρnn hρ0 _ _)

/-- The posterior is a probability measure: the posterior mean of `1` is `1`. -/
theorem ncPosteriorMean_one (n : ℕ) (hn : 0 < n) (y : Fin n → ℝ) (ρ : (Fin 2 → ℝ) → ℝ)
    (hρ : Continuous ρ) (hρnn : ∀ x ∈ symBox 2, 0 ≤ ρ x) (hρ0 : 0 < ρ 0) :
    ncPosteriorMean n y ρ (fun _ => 1) = 1 := by
  unfold ncPosteriorMean
  simp only [one_mul]
  exact div_self (nc_evidence_pos n hn y ρ hρ hρnn hρ0).ne'

end Laplace.Grammar
