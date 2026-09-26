/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.TiltDensityBounds

/-!
# Quantitative inverse stability of the intrinsic chart

The covariance of the visible statistics under the reference law is coercive on the visible
subspace: there is `λ₀ > 0` with `λ₀ ⟨u,u⟩ ≤ Var_ν⟨u,S⟩` for `u ∈ 𝕍` (`exists_coercive_variance`,
by compactness of the unit sphere and positive definiteness). Combined with the density bounds of
`TiltDensityBounds`, the covariance stays coercive on bounded parameter regions with the explicit
constant `κ_r = e^{−2Br} λ₀` (`variance_familyMeasure_ge_coercive`), and integrating the
derivative of the mean map along a parameter segment gives the **strong monotonicity**

  `κ_r ⟨θ − η, θ − η⟩ ≤ ⟨θ − η, m(η) − m(θ)⟩`   (`dotJ_sub_meanMap_ge`)

for `⟨θ,θ⟩, ⟨η,η⟩ ≤ r²` in `𝕍`, hence the **Lipschitz bound for the inverse chart**

  `κ_r² ⟨θ − η, θ − η⟩ ≤ ⟨m(θ) − m(η), m(θ) − m(η)⟩`   (`sq_dotJ_sub_le_dotJ_meanMap_sub`):

natural coordinates in a ball of radius `r` are recovered from the responses with Lipschitz constant
`κ_r⁻¹`. The image of a parameter ball need not be convex; the statement is about pairs of points
of the ball, not about segments of responses.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Quadratic

variable {J : Type*} [Fintype J]

/-- Expanding the squared norm along a segment. -/
theorem dotJ_segment_eq (a b : J → ℝ) (t : ℝ) :
    dotJ (a + t • (b - a)) (a + t • (b - a)) =
      (1 - t) * dotJ a a + t * dotJ b b - t * (1 - t) * dotJ (b - a) (b - a) := by
  simp only [dotJ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The Euclidean ball `⟨v,v⟩ ≤ r²` is convex. -/
theorem dotJ_segment_le {a b : J → ℝ} {r : ℝ} (ha : dotJ a a ≤ r ^ 2) (hb : dotJ b b ≤ r ^ 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : dotJ (a + t • (b - a)) (a + t • (b - a)) ≤ r ^ 2 := by
  rw [dotJ_segment_eq]
  have h0 : 0 ≤ dotJ (b - a) (b - a) := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  nlinarith [mul_nonneg (mul_nonneg ht0 (sub_nonneg.2 ht1)) h0]

/-- Homogeneity of the squared norm. -/
theorem dotJ_smul_smul (c : ℝ) (a : J → ℝ) : dotJ (c • a) (c • a) = c ^ 2 * dotJ a a := by
  simp only [dotJ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- Cauchy–Schwarz for the pairing, squared form. -/
theorem sq_dotJ_le (a b : J → ℝ) : dotJ a b ^ 2 ≤ dotJ a a * dotJ b b := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have e2 : dotJ a a = ∑ i, a i ^ 2 := Finset.sum_congr rfl fun i _ ↦ (sq _).symm
  have e3 : dotJ b b = ∑ i, b i ^ 2 := Finset.sum_congr rfl fun i _ ↦ (sq _).symm
  rw [e2, e3]
  exact hcs

end Quadratic

section Coercive

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The variance of a visible contrast under the reference law, as the chart quadratic form. -/
theorem lawCov_dirLoss_eq_neg_dotJ_chartDeriv (u : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    lawCov ν (dirLoss S u) (dirLoss S u) =
      -dotJ (u : J → ℝ) (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS 0 u : J → ℝ) := by
  rw [dotJ_chartDeriv, Submodule.coe_zero, priorCov_one_zero, neg_neg]

/-- The variance of a visible contrast is continuous in the contrast. -/
theorem continuous_lawCov_dirLoss :
    Continuous fun u : dirSpan ν (fun _ ↦ (1 : ℝ)) S ↦ lawCov ν (dirLoss S u) (dirLoss S u) := by
  simp_rw [lawCov_dirLoss_eq_neg_dotJ_chartDeriv hS ν]
  refine Continuous.neg ?_
  simp only [dotJ]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  exact ((continuous_apply i).comp continuous_subtype_val).mul
    ((continuous_apply i).comp (continuous_subtype_val.comp
      (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS 0).continuous))

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- Homogeneity of the variance of a contrast. -/
theorem lawCov_dirLoss_smul (c : ℝ) (u : J → ℝ) :
    lawCov ν (dirLoss S (c • u)) (dirLoss S (c • u)) =
      c ^ 2 * lawCov ν (dirLoss S u) (dirLoss S u) := by
  rw [dirLoss_smul]
  unfold lawCov
  simp only [integral_const_mul]
  have : (fun x ↦ c * dirLoss S u x * (c * dirLoss S u x)) =
      fun x ↦ c ^ 2 * (dirLoss S u x * dirLoss S u x) := funext fun x ↦ by ring
  rw [this, integral_const_mul]
  ring

/-- **Coercivity of the reference covariance on the visible subspace**: there is `λ₀ > 0` with
`λ₀ ⟨u,u⟩ ≤ Var_ν⟨u,S⟩` for every `u ∈ 𝕍`. -/
theorem exists_coercive_variance :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ u : dirSpan ν (fun _ ↦ (1 : ℝ)) S,
      lam₀ * dotJ (u : J → ℝ) (u : J → ℝ) ≤ lawCov ν (dirLoss S u) (dirLoss S u) := by
  by_cases hV : ∃ u : dirSpan ν (fun _ ↦ (1 : ℝ)) S, u ≠ 0
  · obtain ⟨u₀, hu₀⟩ := hV
    have : Nontrivial (dirSpan ν (fun _ ↦ (1 : ℝ)) S) := nontrivial_of_ne u₀ 0 hu₀
    -- minimise the ratio over the unit sphere
    have hsph : (Metric.sphere (0 : dirSpan ν (fun _ ↦ (1 : ℝ)) S) 1).Nonempty :=
      NormedSpace.sphere_nonempty.2 zero_le_one
    have hpos : ∀ u : dirSpan ν (fun _ ↦ (1 : ℝ)) S, u ≠ 0 → 0 < dotJ (u : J → ℝ) (u : J → ℝ) := by
      intro u hu
      have h : (u : J → ℝ) ≠ 0 := fun h ↦ hu (Subtype.ext h)
      obtain ⟨i, hi⟩ := Function.ne_iff.1 h
      exact Finset.sum_pos' (fun j _ ↦ mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩
    have hcont : ContinuousOn (fun u : dirSpan ν (fun _ ↦ (1 : ℝ)) S ↦
        lawCov ν (dirLoss S u) (dirLoss S u) / dotJ (u : J → ℝ) (u : J → ℝ))
        (Metric.sphere 0 1) := by
      refine ContinuousOn.div (continuous_lawCov_dirLoss hS ν).continuousOn ?_ fun u hu ↦ ?_
      · simp only [dotJ]
        exact (continuous_finsetSum _ fun i _ ↦
          ((continuous_apply i).comp continuous_subtype_val).mul
            ((continuous_apply i).comp continuous_subtype_val)).continuousOn
      · have hu0 : u ≠ 0 := by
          intro h
          rw [h, mem_sphere_zero_iff_norm, norm_zero] at hu
          exact zero_ne_one hu
        exact (hpos u hu0).ne'
    obtain ⟨u₁, hu₁, hmin⟩ :=
      (isCompact_sphere (0 : dirSpan ν (fun _ ↦ (1 : ℝ)) S) 1).exists_isMinOn hsph hcont
    rw [isMinOn_iff] at hmin
    have hu₁0 : u₁ ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hu₁
      exact zero_ne_one hu₁
    refine ⟨lawCov ν (dirLoss S u₁) (dirLoss S u₁) / dotJ (u₁ : J → ℝ) (u₁ : J → ℝ), ?_, fun u ↦ ?_⟩
    · refine div_pos ?_ (hpos u₁ hu₁0)
      have := priorCov_dirLoss_self_pos measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS 0 u₁.2 (fun h ↦ hu₁0 (Subtype.ext h))
      rwa [priorCov_one_zero] at this
    · by_cases hu : u = 0
      · rw [hu]
        simp [dotJ, lawCov, dirLoss_zero]
      · -- scale `u` to the sphere
        have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
        have hmem : ‖u‖⁻¹ • u ∈ Metric.sphere (0 : dirSpan ν (fun _ ↦ (1 : ℝ)) S) 1 := by
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
        have h := hmin _ hmem
        simp only [Submodule.coe_smul] at h
        rw [lawCov_dirLoss_smul, dotJ_smul_smul,
          show (‖u‖⁻¹ ^ 2 * lawCov ν (dirLoss S u) (dirLoss S u)) /
            (‖u‖⁻¹ ^ 2 * dotJ (u : J → ℝ) (u : J → ℝ)) =
            lawCov ν (dirLoss S u) (dirLoss S u) / dotJ (u : J → ℝ) (u : J → ℝ) by
              field_simp] at h
        rw [le_div_iff₀ (hpos u hu)] at h
        exact h
  · push Not at hV
    refine ⟨1, one_pos, fun u ↦ ?_⟩
    rw [hV u]
    simp [dotJ, lawCov, dirLoss_zero]

end Coercive

section Stability

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {B r : ℝ} (hB0 : 0 ≤ B) (hr0 : 0 ≤ r)
  (hB : ∀ᵐ x ∂ν, dotJ (statPoint S x - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)
    (statPoint S x - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) ≤ B ^ 2)
  {lam₀ : ℝ} (hlam0 : 0 ≤ lam₀) (hlam : ∀ u : dirSpan ν (fun _ ↦ (1 : ℝ)) S,
    lam₀ * dotJ (u : J → ℝ) (u : J → ℝ) ≤ lawCov ν (dirLoss S u) (dirLoss S u))
include hS hB0 hr0 hB hlam0 hlam

omit [Nonempty J] hlam0 in
/-- **Coercivity on a bounded parameter region**: `Var_{P_θ}⟨u,S⟩ ≥ e^{−2Br} λ₀ ⟨u,u⟩` for
`⟨θ,θ⟩ ≤ r²` and `u ∈ 𝕍`. -/
theorem variance_familyMeasure_ge_coercive {θ : J → ℝ} (hθ : dotJ θ θ ≤ r ^ 2)
    (u : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    Real.exp (-(2 * (r * B))) * lam₀ * dotJ (u : J → ℝ) (u : J → ℝ) ≤
      lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ)
        (dirLoss S u) (dirLoss S u) := by
  calc Real.exp (-(2 * (r * B))) * lam₀ * dotJ (u : J → ℝ) (u : J → ℝ)
      ≤ Real.exp (-(2 * (r * B))) * lawCov ν (dirLoss S u) (dirLoss S u) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hlam u) (Real.exp_pos _).le
    _ ≤ _ := lawCov_familyMeasure_ge hS ν hB0 hr0 hB hθ (bdd_dirLoss hS _)

omit [Nonempty J] hB0 hr0 hB hlam0 hlam in
/-- The pairing of a displacement with the mean map along the segment is differentiable, with
derivative minus the variance of the displacement contrast. -/
theorem hasDerivAt_dotJ_meanMap_segment (η θ : J → ℝ) (t : ℝ) :
    HasDerivAt (fun t ↦ dotJ (θ - η)
        (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η + t • (θ - η))))
      (-lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η + t • (θ - η)))
        (dirLoss S (θ - η)) (dirLoss S (θ - η))) t := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hline : HasDerivAt (fun t : ℝ ↦ η + t • (θ - η)) (θ - η) t := by
    have := ((hasDerivAt_id' (x := t)).smul_const (θ - η)).const_add η
    simpa using this
  have hm := (hasStrictFDerivAt_meanMap measurable_const (integrable_const 1) (fun _ ↦ zero_le_one)
    (one_integral_pos ν) measurable_const h0 hS one_pos (η + t • (θ - η))).hasFDerivAt
  have h := (dotCLM (θ - η)).hasFDerivAt.comp_hasDerivAt t (hm.comp_hasDerivAt t hline)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
  · simp only [Function.comp_apply, dotCLM_apply]
    rw [dotJ_comm]
  · simp only [dotCLM_apply]
    rw [dotJ_comm, dotJ_meanMapDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS, priorCov_eq_lawCov_familyMeasure hS ν]

omit [Nonempty J] hlam0 in
/-- **Strong monotonicity of the mean map on bounded parameter regions**:
`κ_r ⟨θ − η, θ − η⟩ ≤ ⟨θ − η, m(η) − m(θ)⟩` with `κ_r = e^{−2Br} λ₀`, for `θ, η ∈ 𝕍` with
`⟨θ,θ⟩, ⟨η,η⟩ ≤ r²`. -/
theorem dotJ_sub_meanMap_ge {θ η : dirSpan ν (fun _ ↦ (1 : ℝ)) S}
    (hθ : dotJ (θ : J → ℝ) (θ : J → ℝ) ≤ r ^ 2) (hη : dotJ (η : J → ℝ) (η : J → ℝ) ≤ r ^ 2) :
    Real.exp (-(2 * (r * B))) * lam₀ *
        dotJ ((θ : J → ℝ) - (η : J → ℝ)) ((θ : J → ℝ) - (η : J → ℝ)) ≤
      dotJ ((θ : J → ℝ) - (η : J → ℝ)) (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η -
        meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) := by
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  -- the variance along the segment, continuous in `t`
  obtain ⟨V, hV⟩ : ∃ V : ℝ → ℝ, V = fun t ↦ lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ))
      (fun _ ↦ (0 : ℝ)) S 1 ((η : J → ℝ) + t • ((θ : J → ℝ) - (η : J → ℝ))))
      (dirLoss S ((θ : J → ℝ) - (η : J → ℝ))) (dirLoss S ((θ : J → ℝ) - (η : J → ℝ))) := ⟨_, rfl⟩
  have hVc : Continuous V := by
    rw [hV]
    have hD := continuous_meanMapDeriv measurable_const (integrable_const 1) (fun _ ↦ zero_le_one)
      (one_integral_pos ν) measurable_const h0 hS one_pos
    have hline : Continuous fun t : ℝ ↦ (η : J → ℝ) + t • ((θ : J → ℝ) - (η : J → ℝ)) := by fun_prop
    have e : (fun t : ℝ ↦ lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        ((η : J → ℝ) + t • ((θ : J → ℝ) - (η : J → ℝ)))) (dirLoss S ((θ : J → ℝ) - (η : J → ℝ)))
        (dirLoss S ((θ : J → ℝ) - (η : J → ℝ)))) = fun t : ℝ ↦ -dotJ ((θ : J → ℝ) - (η : J → ℝ))
        (meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
          ((η : J → ℝ) + t • ((θ : J → ℝ) - (η : J → ℝ))) ((θ : J → ℝ) - (η : J → ℝ))) := by
      funext t
      rw [dotJ_meanMapDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS, priorCov_eq_lawCov_familyMeasure hS ν, neg_neg]
    rw [e]
    refine Continuous.neg ?_
    simp only [dotJ]
    exact continuous_finsetSum _ fun i _ ↦ continuous_const.mul
      ((continuous_apply i).comp ((hD.comp hline).clm_apply continuous_const))
  -- the segment stays in the ball
  have hball : ∀ t ∈ Icc (0 : ℝ) 1,
      dotJ ((η : J → ℝ) + t • ((θ : J → ℝ) - (η : J → ℝ)))
        ((η : J → ℝ) + t • ((θ : J → ℝ) - (η : J → ℝ))) ≤ r ^ 2 :=
    fun t ht ↦ dotJ_segment_le hη hθ ht.1 ht.2
  -- the fundamental theorem of calculus
  have hFTC : dotJ ((θ : J → ℝ) - (η : J → ℝ))
      (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) -
      dotJ ((θ : J → ℝ) - (η : J → ℝ)) (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η) =
      ∫ t in (0 : ℝ)..1, -V t := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t ↦ dotJ ((θ : J → ℝ) - (η : J → ℝ))
        (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
          ((η : J → ℝ) + t • ((θ : J → ℝ) - (η : J → ℝ)))))
      (f' := fun t ↦ -V t) (a := 0) (b := 1)
      (fun t _ ↦ by rw [hV]; exact hasDerivAt_dotJ_meanMap_segment hS ν η θ t)
      (hVc.neg.intervalIntegrable 0 1)
    rw [h]
    simp
  -- the integrand is bounded below by the coercive constant
  have hlow : ∀ t ∈ Icc (0 : ℝ) 1, Real.exp (-(2 * (r * B))) * lam₀ *
      dotJ ((θ : J → ℝ) - (η : J → ℝ)) ((θ : J → ℝ) - (η : J → ℝ)) ≤ V t := by
    intro t ht
    rw [hV]
    have := variance_familyMeasure_ge_coercive hS ν hB0 hr0 hB hlam (hball t ht) (θ - η)
    simpa only [Submodule.coe_sub] using this
  have hint : ∫ t in (0 : ℝ)..1, Real.exp (-(2 * (r * B))) * lam₀ *
      dotJ ((θ : J → ℝ) - (η : J → ℝ)) ((θ : J → ℝ) - (η : J → ℝ)) ≤ ∫ t in (0 : ℝ)..1, V t :=
    intervalIntegral.integral_mono_on zero_le_one (by simp) (hVc.intervalIntegrable 0 1) hlow
  rw [intervalIntegral.integral_const] at hint
  rw [(isLinearMap_dotJ ((θ : J → ℝ) - (η : J → ℝ))).map_sub
    (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η)
    (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ)]
  rw [intervalIntegral.integral_neg] at hFTC
  simp only [sub_zero, one_smul] at hint
  linarith

omit [Nonempty J] in
/-- **The inverse chart is Lipschitz on bounded parameter regions**:
`κ_r² ⟨θ − η, θ − η⟩ ≤ ⟨m(θ) − m(η), m(θ) − m(η)⟩` with `κ_r = e^{−2Br} λ₀`. -/
theorem sq_dotJ_sub_le_dotJ_meanMap_sub {θ η : dirSpan ν (fun _ ↦ (1 : ℝ)) S}
    (hθ : dotJ (θ : J → ℝ) (θ : J → ℝ) ≤ r ^ 2) (hη : dotJ (η : J → ℝ) (η : J → ℝ) ≤ r ^ 2) :
    (Real.exp (-(2 * (r * B))) * lam₀) ^ 2 *
        dotJ ((θ : J → ℝ) - (η : J → ℝ)) ((θ : J → ℝ) - (η : J → ℝ)) ≤
      dotJ (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ -
          meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η)
        (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ -
          meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η) := by
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = Real.exp (-(2 * (r * B))) * lam₀ := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : J → ℝ, d = (θ : J → ℝ) - η := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : J → ℝ, w = meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η -
    meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ := ⟨_, rfl⟩
  have hmono := dotJ_sub_meanMap_ge hS ν hB0 hr0 hB hlam hθ hη
  rw [← hκ, ← hd, ← hw] at hmono
  have hcs := sq_dotJ_le d w
  have hdd : 0 ≤ dotJ d d := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  have hww : dotJ (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ -
      meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η)
      (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ -
        meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η) = dotJ w w := by
    rw [hw, show meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ -
        meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η =
        -(meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η -
          meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) by abel,
      dotJ_neg_left, dotJ_comm, dotJ_neg_left, neg_neg]
  rw [← hκ, ← hd, hww]
  rcases hdd.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  · have hκ0 : 0 ≤ κ := by
      rw [hκ]
      exact mul_nonneg (Real.exp_pos _).le hlam0
    have h1 : (κ * dotJ d d) ^ 2 ≤ dotJ d w ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hκ0 hdd) hmono 2
    have h2 : (κ * dotJ d d) ^ 2 ≤ dotJ d d * dotJ w w := h1.trans hcs
    have h3 : κ ^ 2 * dotJ d d * dotJ d d ≤ dotJ w w * dotJ d d := by nlinarith [h2]
    exact le_of_mul_le_mul_right h3 hpos

end Stability

end Laplace.Multi
