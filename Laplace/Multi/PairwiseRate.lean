/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.LocalRateDCT

/-!
# The unnormalized pairwise integral theorem

Stage J5d, the shape consult's genuinely load-bearing checkpoint:
for two losses carrying the `HigherLaplaceDomain` package with
matched derivative tensors below order `k`,
`(I₁(P,q) - I₂(P,q))/q^(k-2) → -∫ P·Q·K_H`, where `I_j` are the H4
posterior integrands and `Q` the degree-`k` diagonal difference. The
proof is the consult's three-term decomposition over the common
ball: the local term is J5c's rate-DCT, and each domain tail has
retreating support and vanishes by squeeze against J5b.
-/

open Real MeasureTheory Filter Topology Metric

namespace Laplace.Multi

namespace HigherLaplaceDomain

variable {d : ℕ} {k : ℕ} {L₁ L₂ : EuclidD d → ℝ}
  {H : Matrix (Fin d) (Fin d) ℝ}

/-- Any sub-domain slice of the posterior integrand is integrable at
each positive scale, dominated by the coercive Gaussian. -/
theorem integrable_indicator_slice (A : HigherLaplaceDomain k L₁ H)
    {P : EuclidD d → ℝ} (hP_cont : Continuous P)
    (hP_growth : HasPolynomialGrowth P)
    {q : ℝ} (hq : 0 < q) {S : Set (EuclidD d)}
    (hS_meas : MeasurableSet S)
    (hS_sub : S ⊆ {x : EuclidD d | q • x ∈ A.U}) :
    Integrable (fun x : EuclidD d ↦ Set.indicator S
      (fun x ↦ P x * Real.exp (-((L₁ (q • x) - L₁ 0) / q ^ 2))) x) := by
  have hdom : Integrable (fun x : EuclidD d ↦
      |P x| * Real.exp (-A.c * ‖x‖ ^ 2)) := by
    refine integrable_mul_exp_neg_mul_sq_of_polynomialGrowth A.c_pos
      hP_cont.abs.aestronglyMeasurable ?_
    obtain ⟨C, n, hC, h⟩ := hP_growth
    exact ⟨C, n, hC, fun x ↦ by rw [abs_abs]; exact h x⟩
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun x ↦ ?_)
  · have hm : Measurable fun x : EuclidD d ↦
        Real.exp (-((L₁ (q • x) - L₁ 0) / q ^ 2)) :=
      Real.measurable_exp.comp
        ((((A.contDiff_k.continuous.measurable.comp
          (measurable_const_smul q)).sub measurable_const).div_const
            _).neg)
    exact ((hP_cont.measurable.mul hm).aestronglyMeasurable).indicator
      hS_meas
  · by_cases hmem : x ∈ S
    · rw [Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      have hU : q • x ∈ A.U := hS_sub hmem
      have hlow := A.rescaled_lower hq hU
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact Real.exp_le_exp.mpr (by linarith)
    · rw [Set.indicator_of_notMem hmem, norm_zero]
      positivity

/-- **The retreating domain tail vanishes at every rate** (the J5b
lemma instantiated at the posterior integrand). -/
theorem tendsto_tail_slice (A : HigherLaplaceDomain k L₁ H)
    {P : EuclidD d → ℝ} (hP_cont : Continuous P)
    (hP_growth : HasPolynomialGrowth P)
    {ρ : ℝ} (hρ : 0 < ρ) (r : ℕ) :
    Tendsto (fun q : ℝ ↦ (∫ x : EuclidD d, Set.indicator
        ({x : EuclidD d | q • x ∈ A.U} \
          {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ})
        (fun x ↦ P x * Real.exp (-((L₁ (q • x) - L₁ 0) / q ^ 2))) x) /
        q ^ r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have habs_growth : HasPolynomialGrowth (fun x : EuclidD d ↦ |P x|) := by
    obtain ⟨C, n, hC, h⟩ := hP_growth
    exact ⟨C, n, hC, fun x ↦ by rw [abs_abs]; exact h x⟩
  have hJ5b := tendsto_integral_retreating_tail_div_pow
    (P := fun x : EuclidD d ↦ |P x|)
    hP_cont.abs.aestronglyMeasurable habs_growth hρ A.c_pos r
  refine squeeze_zero_norm' ?_ hJ5b
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq0 : (0 : ℝ) < q := hq
  have hqk : (0 : ℝ) < q ^ r := by positivity
  have hRHS_int : Integrable (fun x : EuclidD d ↦
      Set.indicator {x : EuclidD d | ρ ≤ q * ‖x‖}
        (fun x ↦ |P x| * Real.exp (-A.c * ‖x‖ ^ 2)) x) := by
    have hbase : Integrable (fun x : EuclidD d ↦
        |P x| * Real.exp (-A.c * ‖x‖ ^ 2)) :=
      integrable_mul_exp_neg_mul_sq_of_polynomialGrowth A.c_pos
        hP_cont.abs.aestronglyMeasurable habs_growth
    have hset : MeasurableSet {x : EuclidD d | ρ ≤ q * ‖x‖} := by
      apply measurableSet_le measurable_const
      fun_prop
    exact hbase.indicator hset
  have hb : |∫ x : EuclidD d, Set.indicator
      ({x : EuclidD d | q • x ∈ A.U} \
        {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ})
      (fun x ↦ P x * Real.exp (-((L₁ (q • x) - L₁ 0) / q ^ 2))) x| ≤
      ∫ x : EuclidD d, Set.indicator {x : EuclidD d | ρ ≤ q * ‖x‖}
        (fun x ↦ |P x| * Real.exp (-A.c * ‖x‖ ^ 2)) x := by
    refine le_trans abs_integral_le_integral_abs ?_
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x ↦ abs_nonneg _) hRHS_int
    refine Filter.Eventually.of_forall fun x ↦ ?_
    simp only []
    by_cases hmem : x ∈ ({x : EuclidD d | q • x ∈ A.U} \
        {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ})
    · have htl : x ∈ {x : EuclidD d | ρ ≤ q * ‖x‖} := by
        have hnb := hmem.2
        simp only [Set.mem_setOf_eq, Metric.mem_ball,
          dist_eq_norm, sub_zero, not_lt] at hnb
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq0] at hnb
        exact hnb
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem htl,
        abs_mul, abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hlow := A.rescaled_lower hq0 hmem.1
      exact Real.exp_le_exp.mpr (by linarith)
    · rw [Set.indicator_of_notMem hmem, abs_zero]
      by_cases htl : x ∈ {x : EuclidD d | ρ ≤ q * ‖x‖}
      · rw [Set.indicator_of_mem htl]
        positivity
      · rw [Set.indicator_of_notMem htl]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hqk]
  exact div_le_div_of_nonneg_right hb hqk.le

/-- **The unnormalized pairwise integral theorem** (J5d): the
rate-divided difference of the two posterior integrands converges to
minus the Gaussian pairing with the degree-`k` diagonal
difference. -/
theorem tendsto_pairwise_integral_difference (hk : 2 < k)
    (A₁ : HigherLaplaceDomain k L₁ H) (A₂ : HigherLaplaceDomain k L₂ H)
    (hlower : ∀ j < k,
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    {P : EuclidD d → ℝ} (hP_cont : Continuous P)
    (hP_growth : HasPolynomialGrowth P) :
    Tendsto (fun q : ℝ ↦
        ((∫ x : EuclidD d,
          A₁.toLocalLaplaceDomain.integrand P q x) -
         (∫ x : EuclidD d,
          A₂.toLocalLaplaceDomain.integrand P q x)) / q ^ (k - 2))
      (𝓝[>] (0 : ℝ))
      (𝓝 (-∫ x : EuclidD d,
        P x * (taylorHomogeneousTerm k L₁ x -
          taylorHomogeneousTerm k L₂ x) * quadKernel H x)) := by
  classical
  set ρ : ℝ := min A₁.taylorRadius A₂.taylorRadius with hρ_def
  have hρ : 0 < ρ := lt_min A₁.taylorRadius_pos A₂.taylorRadius_pos
  have hρ₁ : ρ ≤ A₁.taylorRadius := min_le_left _ _
  have hρ₂ : ρ ≤ A₂.taylorRadius := min_le_right _ _
  have hball_meas : ∀ q : ℝ, MeasurableSet
      {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ} :=
    fun q ↦ (measurable_const_smul q) measurableSet_ball
  have hU₁_meas : ∀ q : ℝ, MeasurableSet
      {x : EuclidD d | q • x ∈ A₁.U} :=
    fun q ↦ (measurable_const_smul q) A₁.measurableSet_U
  have hU₂_meas : ∀ q : ℝ, MeasurableSet
      {x : EuclidD d | q • x ∈ A₂.U} :=
    fun q ↦ (measurable_const_smul q) A₂.measurableSet_U
  have hball_sub₁ : ∀ q : ℝ,
      {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ} ⊆
        {x : EuclidD d | q • x ∈ A₁.U} := fun q x hx ↦
    A₁.taylorBall_subset (Metric.ball_subset_ball hρ₁ hx)
  have hball_sub₂ : ∀ q : ℝ,
      {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ} ⊆
        {x : EuclidD d | q • x ∈ A₂.U} := fun q x hx ↦
    A₂.taylorBall_subset (Metric.ball_subset_ball hρ₂ hx)
  have hloc := tendsto_local_rate_integral hk A₁ A₂ hlower hρ hρ₁ hρ₂
    hP_cont hP_growth
  have htail₁ := A₁.tendsto_tail_slice hP_cont hP_growth hρ (k - 2)
  have htail₂ := A₂.tendsto_tail_slice hP_cont hP_growth hρ (k - 2)
  have hcomb := (hloc.add htail₁).sub htail₂
  rw [add_zero, sub_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq0 : (0 : ℝ) < q := hq
  have hloc_int₁ := A₁.integrable_indicator_slice hP_cont hP_growth hq0
    (hball_meas q) (hball_sub₁ q)
  have hloc_int₂ := A₂.integrable_indicator_slice hP_cont hP_growth hq0
    (hball_meas q) (hball_sub₂ q)
  have htail_int₁ := A₁.integrable_indicator_slice hP_cont hP_growth hq0
    ((hU₁_meas q).diff (hball_meas q)) Set.diff_subset
  have htail_int₂ := A₂.integrable_indicator_slice hP_cont hP_growth hq0
    ((hU₂_meas q).diff (hball_meas q)) Set.diff_subset
  have hsplit₁ : ∀ x : EuclidD d,
      A₁.toLocalLaplaceDomain.integrand P q x =
        Set.indicator {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}
          (fun x ↦ P x * Real.exp (-((L₁ (q • x) - L₁ 0) / q ^ 2))) x +
        Set.indicator ({x : EuclidD d | q • x ∈ A₁.U} \
            {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ})
          (fun x ↦ P x * Real.exp (-((L₁ (q • x) - L₁ 0) / q ^ 2))) x := by
    intro x
    unfold LocalLaplaceDomain.integrand
    by_cases hB : x ∈ {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}
    · rw [Set.indicator_of_mem (hball_sub₁ q hB),
        Set.indicator_of_mem hB,
        Set.indicator_of_notMem (fun h ↦ h.2 hB), add_zero]
    · rw [Set.indicator_of_notMem hB, zero_add]
      by_cases h1 : x ∈ {x : EuclidD d | q • x ∈ A₁.U}
      · have hd : x ∈ ({x : EuclidD d | q • x ∈ A₁.U} \
            {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}) :=
          ⟨h1, hB⟩
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem hd]
      · rw [Set.indicator_of_notMem h1,
          Set.indicator_of_notMem (fun h ↦ h1 h.1)]
  have hsplit₂ : ∀ x : EuclidD d,
      A₂.toLocalLaplaceDomain.integrand P q x =
        Set.indicator {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}
          (fun x ↦ P x * Real.exp (-((L₂ (q • x) - L₂ 0) / q ^ 2))) x +
        Set.indicator ({x : EuclidD d | q • x ∈ A₂.U} \
            {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ})
          (fun x ↦ P x * Real.exp (-((L₂ (q • x) - L₂ 0) / q ^ 2))) x := by
    intro x
    unfold LocalLaplaceDomain.integrand
    by_cases hB : x ∈ {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}
    · rw [Set.indicator_of_mem (hball_sub₂ q hB),
        Set.indicator_of_mem hB,
        Set.indicator_of_notMem (fun h ↦ h.2 hB), add_zero]
    · rw [Set.indicator_of_notMem hB, zero_add]
      by_cases h2 : x ∈ {x : EuclidD d | q • x ∈ A₂.U}
      · have hd : x ∈ ({x : EuclidD d | q • x ∈ A₂.U} \
            {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}) :=
          ⟨h2, hB⟩
        rw [Set.indicator_of_mem h2, Set.indicator_of_mem hd]
      · rw [Set.indicator_of_notMem h2,
          Set.indicator_of_notMem (fun h ↦ h2 h.1)]
  have hI₁ : (∫ x : EuclidD d, A₁.toLocalLaplaceDomain.integrand P q x) =
      (∫ x : EuclidD d,
        Set.indicator {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}
          (fun x ↦ P x * Real.exp (-((L₁ (q • x) - L₁ 0) / q ^ 2))) x) +
      ∫ x : EuclidD d,
        Set.indicator ({x : EuclidD d | q • x ∈ A₁.U} \
            {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ})
          (fun x ↦ P x * Real.exp (-((L₁ (q • x) - L₁ 0) / q ^ 2))) x := by
    rw [← integral_add hloc_int₁ htail_int₁]
    exact integral_congr_ae (Filter.Eventually.of_forall hsplit₁)
  have hI₂ : (∫ x : EuclidD d, A₂.toLocalLaplaceDomain.integrand P q x) =
      (∫ x : EuclidD d,
        Set.indicator {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}
          (fun x ↦ P x * Real.exp (-((L₂ (q • x) - L₂ 0) / q ^ 2))) x) +
      ∫ x : EuclidD d,
        Set.indicator ({x : EuclidD d | q • x ∈ A₂.U} \
            {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ})
          (fun x ↦ P x * Real.exp (-((L₂ (q • x) - L₂ 0) / q ^ 2))) x := by
    rw [← integral_add hloc_int₂ htail_int₂]
    exact integral_congr_ae (Filter.Eventually.of_forall hsplit₂)
  have hlocdiff : (∫ x : EuclidD d,
      Set.indicator {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}
        (fun x ↦ P x * Real.exp (-((L₁ (q • x) - L₁ 0) / q ^ 2))) x) -
      (∫ x : EuclidD d,
      Set.indicator {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}
        (fun x ↦ P x * Real.exp (-((L₂ (q • x) - L₂ 0) / q ^ 2))) x) =
      q ^ (k - 2) * ∫ x : EuclidD d,
        Set.indicator {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}
          (fun x ↦ P x *
            ((Real.exp (-((L₁ (q • x) - L₁ 0) / q ^ 2)) -
              Real.exp (-((L₂ (q • x) - L₂ 0) / q ^ 2))) / q ^ (k - 2))) x := by
    rw [← integral_sub hloc_int₁ hloc_int₂, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only []
    by_cases hB : x ∈ {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}
    · rw [Set.indicator_of_mem hB, Set.indicator_of_mem hB,
        Set.indicator_of_mem hB]
      have hqk : (q : ℝ) ^ (k - 2) ≠ 0 := by positivity
      field_simp
    · rw [Set.indicator_of_notMem hB, Set.indicator_of_notMem hB,
        Set.indicator_of_notMem hB]
      norm_num
  have hqk : (q : ℝ) ^ (k - 2) ≠ 0 := by positivity
  set Lv : ℝ := ∫ x : EuclidD d,
    Set.indicator {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}
      (fun x ↦ P x *
        ((Real.exp (-((L₁ (q • x) - L₁ 0) / q ^ 2)) -
          Real.exp (-((L₂ (q • x) - L₂ 0) / q ^ 2))) / q ^ (k - 2))) x
    with hLv_def
  set B₁ : ℝ := ∫ x : EuclidD d,
    Set.indicator {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}
      (fun x ↦ P x * Real.exp (-((L₁ (q • x) - L₁ 0) / q ^ 2))) x
    with hB₁_def
  set B₂ : ℝ := ∫ x : EuclidD d,
    Set.indicator {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ}
      (fun x ↦ P x * Real.exp (-((L₂ (q • x) - L₂ 0) / q ^ 2))) x
    with hB₂_def
  set W₁ : ℝ := ∫ x : EuclidD d,
    Set.indicator ({x : EuclidD d | q • x ∈ A₁.U} \
        {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ})
      (fun x ↦ P x * Real.exp (-((L₁ (q • x) - L₁ 0) / q ^ 2))) x
    with hW₁_def
  set W₂ : ℝ := ∫ x : EuclidD d,
    Set.indicator ({x : EuclidD d | q • x ∈ A₂.U} \
        {x : EuclidD d | q • x ∈ Metric.ball (0 : EuclidD d) ρ})
      (fun x ↦ P x * Real.exp (-((L₂ (q • x) - L₂ 0) / q ^ 2))) x
    with hW₂_def
  rw [hI₁, hI₂, eq_div_iff hqk]
  have hd₁ : W₁ / q ^ (k - 2) * q ^ (k - 2) = W₁ :=
    div_mul_cancel₀ _ hqk
  have hd₂ : W₂ / q ^ (k - 2) * q ^ (k - 2) = W₂ :=
    div_mul_cancel₀ _ hqk
  calc (Lv + W₁ / q ^ (k - 2) - W₂ / q ^ (k - 2)) * q ^ (k - 2)
      = Lv * q ^ (k - 2) + W₁ / q ^ (k - 2) * q ^ (k - 2) -
        W₂ / q ^ (k - 2) * q ^ (k - 2) := by ring
    _ = q ^ (k - 2) * Lv + W₁ - W₂ := by
        rw [hd₁, hd₂]
        ring
    _ = (B₁ - B₂) + W₁ - W₂ := by rw [← hlocdiff]
    _ = B₁ + W₁ - (B₂ + W₂) := by ring

end HigherLaplaceDomain

end Laplace.Multi
