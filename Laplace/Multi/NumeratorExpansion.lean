/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.WindowMajorant
import Laplace.Multi.LocationRecovery

/-!
# The numerator expansion

Stage 5c-ii of the forward-expansion programme, the final integration:
for continuous observables of polynomial growth, the rescaled
numerator `∫ z, D.integrand P q z` is an order-`N` asymptotic
polynomial at `0⁺` with coefficients
`a_j = ∫ z, P z · e^{-T₂(z)} · P_j(z)`. The window piece converges by
the filter-indexed dominated convergence theorem, with the indicator
folded into the integrand, the 5c-i majorant as dominator, and the
scalar graded expansion (activated pointwise by the vanishing scaled
remainder) as the limit; the two outer tails are beyond all orders by
the stage-2 mesoscopic calculus.
-/

open Real MeasureTheory Filter Topology Asymptotics

namespace Laplace.Multi

variable {d N : ℕ} {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

namespace ForwardExpansionDomain

/-- The Boltzmann factor factors through the exponent split (the
majorant tide's factoring, as a standalone lemma). -/
theorem boltzmann_factor_eq (D : ForwardExpansionDomain N L H)
    {q : ℝ} (hq : 0 < q) (z : EuclidD d) :
    Real.exp (-((L (q • z) - L 0) / q ^ 2)) =
      Real.exp (-taylorHomogeneousTerm 2 L z) *
        Real.exp (-(∑ s ∈ Finset.Icc 1 N,
          exponentTerm s L z * q ^ s + q ^ N * D.scaledRem q z)) := by
  have hsplit := D.exponent_split
    D.taylorHomogeneousTerm_one_eq_zero hq z
  have hSr : ∑ s ∈ Finset.range N,
      q ^ (s + 1) * exponentTerm (s + 1) L z =
      ∑ s ∈ Finset.Icc 1 N, exponentTerm s L z * q ^ s := by
    rw [← sum_range_shift_eq_sum_Icc
      (fun s ↦ exponentTerm s L z * q ^ s) N]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    ring
  rw [hsplit, hSr,
    show -(taylorHomogeneousTerm 2 L z +
        ∑ s ∈ Finset.Icc 1 N, exponentTerm s L z * q ^ s +
        q ^ N * D.scaledRem q z) =
      -taylorHomogeneousTerm 2 L z +
        -(∑ s ∈ Finset.Icc 1 N, exponentTerm s L z * q ^ s +
          q ^ N * D.scaledRem q z) from by ring,
    Real.exp_add]

/-- The expansion's coefficient integrals. -/
noncomputable def numeratorCoeff (_D : ForwardExpansionDomain N L H)
    (P : EuclidD d → ℝ) (j : ℕ) : ℝ :=
  ∫ z : EuclidD d, P z * Real.exp (-taylorHomogeneousTerm 2 L z) *
    correctionCoeffFn L N j z

/-- Integrability of the coefficient integrands. -/
theorem integrable_coeff_integrand (D : ForwardExpansionDomain N L H)
    {P : EuclidD d → ℝ} (hP_cont : Continuous P)
    (hP_growth : HasPolynomialGrowth P) (j : ℕ) :
    Integrable (fun z : EuclidD d ↦
      P z * Real.exp (-taylorHomogeneousTerm 2 L z) *
        correctionCoeffFn L N j z) := by
  obtain ⟨CP, n, hCP0, hCP⟩ := hP_growth
  obtain ⟨Cj, hCj0, hCj⟩ := abs_correctionCoeffFn_le L N j
  have hbase : ∀ z : EuclidD d, (1 : ℝ) ≤ 1 + ‖z‖ :=
    fun z ↦ by linarith [norm_nonneg z]
  refine Integrable.mono'
    (g := fun z : EuclidD d ↦ 2 * CP * Cj *
      ((1 + ‖z‖) ^ (n + (j + 2 * N)) *
        Real.exp (-(D.lambda / 2) * ‖z‖ ^ 2))) ?_ ?_ ?_
  · exact (integrable_one_add_norm_pow_mul_gaussian _
      (by linarith [D.lambda_pos])).const_mul _
  · exact ((hP_cont.mul (Real.continuous_exp.comp
      (taylorHomogeneousTerm_continuous 2 L).neg)).mul
      (continuous_correctionCoeffFn L N j)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z ↦ ?_
    have hP2 : |P z| ≤ 2 * CP * (1 + ‖z‖) ^ n := by
      calc |P z| ≤ CP * (1 + ‖z‖ ^ n) := hCP z
        _ ≤ CP * (2 * (1 + ‖z‖) ^ n) := by
            refine mul_le_mul_of_nonneg_left ?_ hCP0
            have h1 : ‖z‖ ^ n ≤ (1 + ‖z‖) ^ n := by
              gcongr
              linarith [norm_nonneg z]
            have h2 : (1 : ℝ) ≤ (1 + ‖z‖) ^ n :=
              one_le_pow₀ (hbase z)
            linarith
        _ = 2 * CP * (1 + ‖z‖) ^ n := by ring
    have hgauss : Real.exp (-taylorHomogeneousTerm 2 L z) ≤
        Real.exp (-(D.lambda / 2) * ‖z‖ ^ 2) := by
      apply Real.exp_le_exp.mpr
      have := D.t2_lower z
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    calc |P z| * Real.exp (-taylorHomogeneousTerm 2 L z) *
          |correctionCoeffFn L N j z|
        ≤ (2 * CP * (1 + ‖z‖) ^ n) *
            Real.exp (-(D.lambda / 2) * ‖z‖ ^ 2) *
            (Cj * (1 + ‖z‖) ^ (j + 2 * N)) := by
          refine mul_le_mul ?_ (hCj z) (abs_nonneg _) ?_
          · exact mul_le_mul hP2 hgauss (Real.exp_pos _).le
              (by positivity)
          · positivity
      _ = 2 * CP * Cj * ((1 + ‖z‖) ^ (n + (j + 2 * N)) *
            Real.exp (-(D.lambda / 2) * ‖z‖ ^ 2)) := by
          rw [pow_add]
          ring

/-- **The window piece converges**: the filter-indexed DCT with the
indicator folded in, the 5c-i majorant as dominator, and the scalar
graded expansion as the pointwise limit. -/
theorem tendsto_integral_window_remainder
    (D : ForwardExpansionDomain N L H)
    {P : EuclidD d → ℝ} (hP_cont : Continuous P)
    (hP_growth : HasPolynomialGrowth P) :
    Tendsto (fun q : ℝ ↦ ∫ z : EuclidD d,
      (mesoscopicSet d q).indicator (fun z ↦
        P z * (Real.exp (-((L (q • z) - L 0) / q ^ 2)) -
          Real.exp (-taylorHomogeneousTerm 2 L z) *
            ∑ j ∈ Finset.range (N + 1),
              correctionCoeffFn L N j z * q ^ j) / q ^ N) z)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨CP, n, hCP0, hCP⟩ := hP_growth
  obtain ⟨C, hC0, hCev⟩ := D.normalized_window_remainder_bound
  have hbase : ∀ z : EuclidD d, (1 : ℝ) ≤ 1 + ‖z‖ :=
    fun z ↦ by linarith [norm_nonneg z]
  have hP2 : ∀ z : EuclidD d, |P z| ≤ 2 * CP * (1 + ‖z‖) ^ n := by
    intro z
    calc |P z| ≤ CP * (1 + ‖z‖ ^ n) := hCP z
      _ ≤ CP * (2 * (1 + ‖z‖) ^ n) := by
          refine mul_le_mul_of_nonneg_left ?_ hCP0
          have h1 : ‖z‖ ^ n ≤ (1 + ‖z‖) ^ n := by
            gcongr
            linarith [norm_nonneg z]
          have h2 : (1 : ℝ) ≤ (1 + ‖z‖) ^ n := one_le_pow₀ (hbase z)
          linarith
      _ = 2 * CP * (1 + ‖z‖) ^ n := by ring
  have hDCT : Tendsto (fun q : ℝ ↦ ∫ z : EuclidD d,
      (mesoscopicSet d q).indicator (fun z ↦
        P z * (Real.exp (-((L (q • z) - L 0) / q ^ 2)) -
          Real.exp (-taylorHomogeneousTerm 2 L z) *
            ∑ j ∈ Finset.range (N + 1),
              correctionCoeffFn L N j z * q ^ j) / q ^ N) z)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ _ : EuclidD d, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z : EuclidD d ↦ 2 * CP * C *
        ((1 + ‖z‖) ^ (n + (N + 2) * (N + 1)) *
          Real.exp (-(D.lambda / 4) * ‖z‖ ^ 2))) ?_ ?_ ?_ ?_
    · -- eventual measurability
      filter_upwards [self_mem_nhdsWithin] with q hq
      refine AEStronglyMeasurable.indicator ?_
        (measurableSet_mesoscopicSet q)
      have hm1 : Measurable fun z : EuclidD d ↦
          Real.exp (-((L (q • z) - L 0) / q ^ 2)) := by
        have hm : Measurable fun z : EuclidD d ↦ L (q • z) :=
          D.measurable_L.comp (measurable_const_smul q)
        exact Real.measurable_exp.comp
          (((hm.sub measurable_const).div_const _).neg)
      have hm2 : Continuous fun z : EuclidD d ↦
          Real.exp (-taylorHomogeneousTerm 2 L z) *
            ∑ j ∈ Finset.range (N + 1),
              correctionCoeffFn L N j z * q ^ j :=
        (Real.continuous_exp.comp
          (taylorHomogeneousTerm_continuous 2 L).neg).mul
          (continuous_finset_sum _ fun j _ ↦
            (continuous_correctionCoeffFn L N j).mul continuous_const)
      exact (((hP_cont.measurable.mul
        (hm1.sub hm2.measurable)).div_const _)).aestronglyMeasurable
    · -- eventual domination
      filter_upwards [hCev, self_mem_nhdsWithin] with q hqev hq0'
      have hq0 : (0 : ℝ) < q := hq0'
      refine Filter.Eventually.of_forall fun z ↦ ?_
      by_cases hmem : z ∈ mesoscopicSet d q
      · rw [Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_div,
          abs_mul, abs_of_pos (pow_pos hq0 N)]
        have hmaj := hqev z hmem
        rw [div_le_iff₀ (pow_pos hq0 N)]
        calc |P z| * |Real.exp (-((L (q • z) - L 0) / q ^ 2)) -
              Real.exp (-taylorHomogeneousTerm 2 L z) *
                ∑ j ∈ Finset.range (N + 1),
                  correctionCoeffFn L N j z * q ^ j|
            ≤ (2 * CP * (1 + ‖z‖) ^ n) *
              (C * (1 + ‖z‖) ^ ((N + 2) * (N + 1)) * q ^ N *
                Real.exp (-(D.lambda / 4) * ‖z‖ ^ 2)) :=
              mul_le_mul (hP2 z) hmaj (abs_nonneg _) (by positivity)
          _ = 2 * CP * C * ((1 + ‖z‖) ^ (n + (N + 2) * (N + 1)) *
                Real.exp (-(D.lambda / 4) * ‖z‖ ^ 2)) * q ^ N := by
              rw [pow_add]
              ring
      · rw [Set.indicator_of_notMem hmem]
        simp only [norm_zero]
        positivity
    · exact (integrable_one_add_norm_pow_mul_gaussian _
        (by linarith [D.lambda_pos])).const_mul _
    · -- pointwise convergence
      refine Filter.Eventually.of_forall fun z ↦ ?_
      have hlittle := exp_graded_expansion
        (fun s ↦ exponentTerm s L z) N (D.tendsto_scaledRem z)
      have hdiv := hlittle.tendsto_div_nhds_zero
      have hg2 : Tendsto (fun q : ℝ ↦
          (P z * Real.exp (-taylorHomogeneousTerm 2 L z)) *
            ((Real.exp (-(∑ s ∈ Finset.Icc 1 N,
                exponentTerm s L z * q ^ s +
                q ^ N * D.scaledRem q z)) -
              ∑ j ∈ Finset.range (N + 1),
                correctionCoeffFn L N j z * q ^ j) / q ^ N))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have := hdiv.const_mul
          (P z * Real.exp (-taylorHomogeneousTerm 2 L z))
        rwa [mul_zero] at this
      refine hg2.congr' ?_
      filter_upwards [eventually_mem_mesoscopicSet z,
        self_mem_nhdsWithin] with q hqmem hq0'
      have hq0 : (0 : ℝ) < q := hq0'
      rw [Set.indicator_of_mem hqmem,
        D.boltzmann_factor_eq hq0 z]
      ring
  simpa using hDCT


end ForwardExpansionDomain

end Laplace.Multi
