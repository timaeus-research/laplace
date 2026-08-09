/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.RateCalculus
import Laplace.Multi.RadialTaylor
import Laplace.Multi.HessianMoments

/-!
# The local rate-sensitive dominated convergence

Stage J5c of the tensor programme: the `HigherLaplaceDomain`
structure (the H4 package extended with `C^k` regularity and a
direct order-`k` Taylor-remainder bound on a fixed ball, per the
shape consult's engineering ruling), the pairwise difference bound
`|L₁ - L₂| ≤ (C₁+C₂)‖y‖^k` on the common ball for matched lower
jets, and the local rate-DCT: the ball-indicator integral of
`P·(e^{-a₁} - e^{-a₂})/q^{k-2}` converges to
`-∫ P·Q·K_H`, where `Q` is the degree-`k` diagonal difference. The
pointwise input is J5a's scalar limit fed by H3b and J4; the
dominator is the secant bound times the rescaled lower bounds.
-/

open Real MeasureTheory Filter Topology Metric

namespace Laplace.Multi

variable {d : ℕ}

/-- **The J5 hypothesis package**: the H4 domain data plus `C^k`
regularity and an order-`k` Taylor remainder bound on a fixed
ball. -/
structure HigherLaplaceDomain (k : ℕ) (L : EuclidD d → ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ)
    extends LocalLaplaceDomain L H where
  contDiff_k : ContDiff ℝ k L
  taylorRadius : ℝ
  taylorRadius_pos : 0 < taylorRadius
  taylorBall_subset : Metric.ball (0 : EuclidD d) taylorRadius ⊆ U
  taylorRemainderConst : ℝ
  taylorRemainderConst_nonneg : 0 ≤ taylorRemainderConst
  taylorRemainder_bound : ∀ y ∈ Metric.ball (0 : EuclidD d) taylorRadius,
    |L y - ∑ j ∈ Finset.range k, taylorHomogeneousTerm j L y| ≤
      taylorRemainderConst * ‖y‖ ^ k

namespace HigherLaplaceDomain

variable {k : ℕ} {L₁ L₂ : EuclidD d → ℝ}
  {H : Matrix (Fin d) (Fin d) ℝ}

/-- Matched lower jets collapse the difference to the two
remainders. -/
theorem pairwise_difference_bound
    (A₁ : HigherLaplaceDomain k L₁ H) (A₂ : HigherLaplaceDomain k L₂ H)
    (hlower : ∀ j < k,
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    {y : EuclidD d} (h₁ : y ∈ Metric.ball (0 : EuclidD d) A₁.taylorRadius)
    (h₂ : y ∈ Metric.ball (0 : EuclidD d) A₂.taylorRadius) :
    |L₁ y - L₂ y| ≤
      (A₁.taylorRemainderConst + A₂.taylorRemainderConst) * ‖y‖ ^ k := by
  have hsum : (∑ j ∈ Finset.range k, taylorHomogeneousTerm j L₁ y) =
      ∑ j ∈ Finset.range k, taylorHomogeneousTerm j L₂ y := by
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    unfold taylorHomogeneousTerm
    rw [hlower j (Finset.mem_range.mp hj)]
  have hb₁ := A₁.taylorRemainder_bound y h₁
  have hb₂ := A₂.taylorRemainder_bound y h₂
  have hsplit : L₁ y - L₂ y =
      (L₁ y - ∑ j ∈ Finset.range k, taylorHomogeneousTerm j L₁ y) -
        (L₂ y - ∑ j ∈ Finset.range k, taylorHomogeneousTerm j L₂ y) := by
    rw [hsum]
    ring
  rw [hsplit]
  calc |(L₁ y - ∑ j ∈ Finset.range k, taylorHomogeneousTerm j L₁ y) -
        (L₂ y - ∑ j ∈ Finset.range k, taylorHomogeneousTerm j L₂ y)|
      ≤ |L₁ y - ∑ j ∈ Finset.range k, taylorHomogeneousTerm j L₁ y| +
        |L₂ y - ∑ j ∈ Finset.range k, taylorHomogeneousTerm j L₂ y| :=
        abs_sub _ _
    _ ≤ (A₁.taylorRemainderConst + A₂.taylorRemainderConst) *
          ‖y‖ ^ k := by nlinarith [pow_nonneg (norm_nonneg y) k]

/-- Matched zeroth jets give equal base values. -/
theorem base_eq_of_lower (hk : 0 < k)
    (hlower : ∀ j < k,
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0) :
    L₁ 0 = L₂ 0 := by
  have h0 := hlower 0 hk
  have h1 := congrFun (congrArg (fun A ↦ A.toFun) h0) (fun _ ↦ 0)
  simpa [iteratedFDeriv_zero_apply] using h1

/-- **The local rate-sensitive dominated convergence** (J5c): on a
common ball inside both domains, the rate-divided exponential
difference integrates to minus the Gaussian pairing with the
degree-`k` diagonal difference. -/
theorem tendsto_local_rate_integral (hk : 2 < k)
    (A₁ : HigherLaplaceDomain k L₁ H) (A₂ : HigherLaplaceDomain k L₂ H)
    (hlower : ∀ j < k,
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ A₁.taylorRadius)
    (hρ₂ : ρ ≤ A₂.taylorRadius)
    {P : EuclidD d → ℝ} (hP_cont : Continuous P)
    (hP_growth : HasPolynomialGrowth P) :
    Tendsto (fun q : ℝ ↦ ∫ x : EuclidD d,
        Set.indicator {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}
          (fun x ↦ P x *
            ((Real.exp (-((L₁ (q • x) - L₁ 0) / q ^ 2)) -
              Real.exp (-((L₂ (q • x) - L₂ 0) / q ^ 2))) / q ^ (k - 2))) x)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-∫ x : EuclidD d,
        P x * (taylorHomogeneousTerm k L₁ x -
          taylorHomogeneousTerm k L₂ x) * quadKernel H x)) := by
  set Q : EuclidD d → ℝ := fun x ↦
    taylorHomogeneousTerm k L₁ x - taylorHomogeneousTerm k L₂ x
    with hQ_def
  set C : ℝ := A₁.taylorRemainderConst + A₂.taylorRemainderConst
    with hC_def
  set c : ℝ := min A₁.c A₂.c with hc_def
  have hc : 0 < c := lt_min A₁.c_pos A₂.c_pos
  have hbase := base_eq_of_lower (by omega) hlower
  -- target as an integral of the pointwise limit
  have htarget : (-∫ x : EuclidD d, P x * Q x * quadKernel H x) =
      ∫ x : EuclidD d, P x * (-(quadKernel H x) * Q x) := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    ring
  rw [htarget]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x : EuclidD d ↦ C * (|P x| * ‖x‖ ^ k *
      Real.exp (-c * ‖x‖ ^ 2))) ?_ ?_ ?_ ?_
  · -- measurability
    filter_upwards with q
    have hset : MeasurableSet
        {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ} :=
      (measurable_const_smul q) measurableSet_ball
    have hm₁ : Measurable fun x : EuclidD d ↦
        Real.exp (-((L₁ (q • x) - L₁ 0) / q ^ 2)) :=
      Real.measurable_exp.comp
        ((((A₁.contDiff_k.continuous.measurable.comp
          (measurable_const_smul q)).sub measurable_const).div_const
            _).neg)
    have hm₂ : Measurable fun x : EuclidD d ↦
        Real.exp (-((L₂ (q • x) - L₂ 0) / q ^ 2)) :=
      Real.measurable_exp.comp
        ((((A₂.contDiff_k.continuous.measurable.comp
          (measurable_const_smul q)).sub measurable_const).div_const
            _).neg)
    exact ((hP_cont.measurable.mul
      (((hm₁.sub hm₂).div_const _))).aestronglyMeasurable).indicator hset
  · -- domination
    filter_upwards [self_mem_nhdsWithin] with q hq
    refine Filter.Eventually.of_forall fun x ↦ ?_
    by_cases hmem : x ∈ {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}
    · rw [Set.indicator_of_mem hmem]
      have hq0 : (0 : ℝ) < q := hq
      have hin : q • x ∈ Metric.ball (0 : EuclidD d) ρ := hmem
      have hin₁ : q • x ∈ Metric.ball (0 : EuclidD d) A₁.taylorRadius :=
        Metric.ball_subset_ball hρ₁ hin
      have hin₂ : q • x ∈ Metric.ball (0 : EuclidD d) A₂.taylorRadius :=
        Metric.ball_subset_ball hρ₂ hin
      have hU₁ : q • x ∈ A₁.U := A₁.taylorBall_subset hin₁
      have hU₂ : q • x ∈ A₂.U := A₂.taylorBall_subset hin₂
      set a₁ : ℝ := (L₁ (q • x) - L₁ 0) / q ^ 2 with ha₁_def
      set a₂ : ℝ := (L₂ (q • x) - L₂ 0) / q ^ 2 with ha₂_def
      have hlow₁ : A₁.c * ‖x‖ ^ 2 ≤ a₁ := A₁.rescaled_lower hq0 hU₁
      have hlow₂ : A₂.c * ‖x‖ ^ 2 ≤ a₂ := A₂.rescaled_lower hq0 hU₂
      have hcx₁ : c * ‖x‖ ^ 2 ≤ a₁ :=
        le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
          (by positivity)) hlow₁
      have hcx₂ : c * ‖x‖ ^ 2 ≤ a₂ :=
        le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
          (by positivity)) hlow₂
      have hmax : max (Real.exp (-a₁)) (Real.exp (-a₂)) ≤
          Real.exp (-(c * ‖x‖ ^ 2)) := by
        rw [max_le_iff]
        exact ⟨Real.exp_le_exp.mpr (by linarith),
          Real.exp_le_exp.mpr (by linarith)⟩
      have hdiff : |a₁ - a₂| ≤ C * q ^ (k - 2) * ‖x‖ ^ k := by
        have hdL : |L₁ (q • x) - L₂ (q • x)| ≤ C * ‖q • x‖ ^ k :=
          pairwise_difference_bound A₁ A₂ hlower hin₁ hin₂
        have hnorm : ‖q • x‖ = q * ‖x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq0]
        have hq2 : (0 : ℝ) < q ^ 2 := by positivity
        have ha : a₁ - a₂ = (L₁ (q • x) - L₂ (q • x)) / q ^ 2 := by
          rw [ha₁_def, ha₂_def, hbase]
          ring
        rw [ha, abs_div, abs_of_pos hq2, div_le_iff₀ hq2]
        calc |L₁ (q • x) - L₂ (q • x)| ≤ C * ‖q • x‖ ^ k := hdL
          _ = C * q ^ k * ‖x‖ ^ k := by
              rw [hnorm, mul_pow]
              ring
          _ = C * q ^ (k - 2) * ‖x‖ ^ k * q ^ 2 := by
              have hkk : k - 2 + 2 = k := by omega
              rw [show q ^ k = q ^ (k - 2) * q ^ 2 by
                rw [← pow_add, hkk]]
              ring
      have hsec := abs_exp_neg_sub_exp_neg_le a₁ a₂
      have hqk2 : (0 : ℝ) < q ^ (k - 2) := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hqk2]
      calc |P x| * (|Real.exp (-a₁) - Real.exp (-a₂)| / q ^ (k - 2))
          ≤ |P x| * ((C * q ^ (k - 2) * ‖x‖ ^ k *
              Real.exp (-(c * ‖x‖ ^ 2))) / q ^ (k - 2)) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            apply div_le_div_of_nonneg_right _ hqk2.le
            calc |Real.exp (-a₁) - Real.exp (-a₂)|
                ≤ |a₁ - a₂| * max (Real.exp (-a₁)) (Real.exp (-a₂)) :=
                  hsec
              _ ≤ (C * q ^ (k - 2) * ‖x‖ ^ k) *
                    Real.exp (-(c * ‖x‖ ^ 2)) := by
                  apply mul_le_mul hdiff hmax (le_max_iff.mpr
                    (Or.inl (Real.exp_pos _).le)) ?_
                  have h₁ := A₁.taylorRemainderConst_nonneg
                  have h₂ := A₂.taylorRemainderConst_nonneg
                  have hC0 : (0:ℝ) ≤ C := by
                    rw [hC_def]
                    linarith
                  exact mul_nonneg (mul_nonneg hC0 (by positivity))
                    (by positivity)
        _ = C * (|P x| * ‖x‖ ^ k * Real.exp (-c * ‖x‖ ^ 2)) := by
            rw [neg_mul]
            field_simp
    · rw [Set.indicator_of_notMem hmem, norm_zero]
      have hC0 : (0:ℝ) ≤ C := by
        rw [hC_def]
        have := A₁.taylorRemainderConst_nonneg
        have := A₂.taylorRemainderConst_nonneg
        linarith
      positivity
  · -- dominator integrability
    refine ((integrable_mul_exp_neg_mul_sq_of_polynomialGrowth hc
      ?_ ?_).const_mul C)
    · exact hP_cont.abs.aestronglyMeasurable.mul
        (continuous_norm.pow k).aestronglyMeasurable
    · obtain ⟨Cp, n, hCp, h⟩ := hP_growth
      have habs : HasPolynomialGrowth (fun x : EuclidD d ↦ |P x|) := by
        refine ⟨Cp, n, hCp, fun x ↦ ?_⟩
        rw [abs_abs]
        exact h x
      exact habs.mul (hasPolynomialGrowth_norm_pow k)
  · -- pointwise limit
    refine Filter.Eventually.of_forall fun x ↦ ?_
    have hev : ∀ᶠ q in 𝓝[>] (0 : ℝ),
        x ∈ {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ} := by
      have hq_small : ∀ᶠ q in 𝓝[>] (0 : ℝ), q < ρ / (‖x‖ + 1) := by
        apply eventually_nhdsWithin_of_eventually_nhds
        exact eventually_lt_nhds (div_pos hρ (by positivity))
      filter_upwards [hq_small, self_mem_nhdsWithin] with q hqρ hq0
      show q • x ∈ Metric.ball (0 : EuclidD d) ρ
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul,
        Real.norm_eq_abs, abs_of_pos hq0]
      calc q * ‖x‖ ≤ q * (‖x‖ + 1) := by
            apply mul_le_mul_of_nonneg_left _ hq0.le
            linarith
        _ < ρ / (‖x‖ + 1) * (‖x‖ + 1) :=
            mul_lt_mul_of_pos_right hqρ (by positivity)
        _ = ρ := by field_simp
    have ha₁lim : Tendsto (fun q : ℝ ↦ (L₁ (q • x) - L₁ 0) / q ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (qform H x / 2)) :=
      A₁.toLocalLaplaceDomain.toLocalQuadraticApprox.rescaled_tendsto x
    have ha₂lim : Tendsto (fun q : ℝ ↦ (L₂ (q • x) - L₂ 0) / q ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (qform H x / 2)) :=
      A₂.toLocalLaplaceDomain.toLocalQuadraticApprox.rescaled_tendsto x
    have hdlim : Tendsto (fun q : ℝ ↦
        ((L₁ (q • x) - L₁ 0) / q ^ 2 -
          (L₂ (q • x) - L₂ 0) / q ^ 2) / q ^ (k - 2))
        (𝓝[>] (0 : ℝ)) (𝓝 (Q x)) := by
      have hJ4 := pairwise_rescaled_loss_tendsto
        A₁.contDiff_k A₂.contDiff_k hlower x
      refine hJ4.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with q hq
      have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hq
      have hkk : 2 + (k - 2) = k := by omega
      rw [hbase]
      rw [show q ^ k = q ^ 2 * q ^ (k - 2) by
        rw [← pow_add, hkk]]
      field_simp
      ring
    have hexp := tendsto_exp_neg_sub_div ha₁lim ha₂lim hdlim
    have hqk : quadKernel H x = Real.exp (-(qform H x / 2)) := by
      unfold quadKernel
      rw [neg_div]
    have hlim : Tendsto (fun q : ℝ ↦ P x *
        ((Real.exp (-((L₁ (q • x) - L₁ 0) / q ^ 2)) -
          Real.exp (-((L₂ (q • x) - L₂ 0) / q ^ 2))) / q ^ (k - 2)))
        (𝓝[>] (0 : ℝ)) (𝓝 (P x * (-(quadKernel H x) * Q x))) := by
      rw [hqk]
      exact hexp.const_mul (P x)
    refine hlim.congr' ?_
    filter_upwards [hev] with q hmem
    rw [Set.indicator_of_mem
      (show x ∈ {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}
        from hmem)]

end HigherLaplaceDomain

end Laplace.Multi
