/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherDistance

/-!
# The Fisher metric space, its topology, and the intrinsic Fisher completion

`FisherPoint hS ν` is a wrapper of the direction space `W` carrying the intrinsic Fisher distance
as a `MetricSpace`. The inclusion `W → FisherPoint` is Lipschitz (segment bound) and the projection
`FisherPoint → W` is continuous (the mean is Lipschitz for `d_F` and the inverse mean chart is
continuous), so **the Fisher topology is the usual topology of `W`**. The intrinsic Fisher
completion `FisherCompletion hS ν := UniformSpace.Completion (FisherPoint hS ν)` carries the
Lipschitz extension `meanExt` of the mean map, whose values lie in the closure of the interior
means; and a mean `M` is an extended mean of some completion point iff some Fisher–Cauchy sequence
of parameters has means converging to `M`.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Wrapper

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J]

/-- The direction space carrying the intrinsic Fisher metric (a wrapper type, so that the normed
structure of `W` is not overridden). -/
@[ext]
structure FisherPoint {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) where
  /-- The underlying parameter. -/
  param : dirSpan ν (fun _ ↦ (1 : ℝ)) S

variable {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)

/-- The underlying equivalence with `W`. -/
def FisherPoint.equivW : FisherPoint hS ν ≃ dirSpan ν (fun _ ↦ (1 : ℝ)) S where
  toFun := FisherPoint.param
  invFun := FisherPoint.mk
  left_inv _ := rfl
  right_inv _ := rfl

end Wrapper

section Metric

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]

/-- The direction space. -/
local notation "W" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- **The intrinsic Fisher distance is a metric.** -/
noncomputable instance : MetricSpace (FisherPoint hS ν) where
  dist p q := fisherDist S ν p.param q.param
  dist_self p := fisherDist_self hS ν p.param
  dist_comm _ _ := fisherDist_comm hS ν
  dist_triangle p q r := fisherDist_triangle hS ν p.param q.param r.param
  eq_of_dist_eq_zero h := FisherPoint.ext (eq_of_fisherDist_eq_zero hS ν h)

theorem FisherPoint.dist_eq (p q : FisherPoint hS ν) :
    dist p q = fisherDist S ν p.param q.param := rfl

/-- The inclusion `W → FisherPoint` is Lipschitz (segment bound). -/
theorem lipschitzWith_fisherPoint_mk :
    ∃ K : NNReal, LipschitzWith K (FisherPoint.mk : W → FisherPoint hS ν) := by
  obtain ⟨K, hK0, hK⟩ := exists_fisherNorm_bound hS ν
  refine ⟨K.toNNReal, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  rw [FisherPoint.dist_eq, dist_eq_norm, Real.coe_toNNReal K hK0, norm_sub_rev]
  exact fisherDist_le_mul_norm hS ν hK x y

theorem continuous_fisherPoint_mk : Continuous (FisherPoint.mk : W → FisherPoint hS ν) :=
  (lipschitzWith_fisherPoint_mk hS ν).choose_spec.continuous

/-- **The mean is Lipschitz on the Fisher space.** -/
theorem lipschitzWith_meanMap_param :
    ∃ B : NNReal, LipschitzWith B fun p : FisherPoint hS ν ↦ mean (p.param : J → ℝ) := by
  obtain ⟨B, hB0, hB⟩ := exists_uniform_bound hS
  refine ⟨B.toNNReal, LipschitzWith.of_dist_le_mul fun p q ↦ ?_⟩
  rw [dist_eq_norm, FisherPoint.dist_eq, Real.coe_toNNReal B hB0, fisherDist_comm hS ν]
  exact norm_meanMap_sub_le_fisherDist hS ν hB hB0 q.param p.param

theorem continuous_meanMap_param :
    Continuous fun p : FisherPoint hS ν ↦ mean (p.param : J → ℝ) :=
  (lipschitzWith_meanMap_param hS ν).choose_spec.continuous

/-- The projection to `W` is continuous (through the mean chart and its continuous inverse). -/
theorem continuous_fisherPoint_param :
    Continuous (FisherPoint.param : FisherPoint hS ν → W) := by
  have hc : Continuous fun p : FisherPoint hS ν ↦
      chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
        p.param :=
    Continuous.subtype_mk ((continuous_meanMap_param hS ν).sub continuous_const) fun p ↦
      meanMap_sub_mem_dirSpan measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS _ 0
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  have hc' : ContinuousAt (fun p : FisherPoint hS ν ↦
      chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
        p.param) p := hc.continuousAt
  have h1 := ContinuousAt.comp (f := fun p : FisherPoint hS ν ↦
      chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
        p.param) (x := p)
    (hasStrictFDerivAt_chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS p.param).continuousAt hc'
  refine h1.congr (Filter.Eventually.of_forall fun q ↦ ?_)
  exact chartVInv_chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS q.param

/-- **The Fisher topology is the usual topology of `W`.** -/
noncomputable def FisherPoint.homeomorphW : FisherPoint hS ν ≃ₜ W where
  toEquiv := FisherPoint.equivW hS ν
  continuous_toFun := continuous_fisherPoint_param hS ν
  continuous_invFun := continuous_fisherPoint_mk hS ν

/-- **The intrinsic Fisher completion of the response space.** -/
abbrev FisherCompletion := UniformSpace.Completion (FisherPoint hS ν)

/-- The extended mean map on the completion. -/
noncomputable def meanExt : FisherCompletion hS ν → J → ℝ :=
  UniformSpace.Completion.extension fun p : FisherPoint hS ν ↦ mean (p.param : J → ℝ)

theorem meanExt_coe (p : FisherPoint hS ν) :
    meanExt hS ν (p : FisherCompletion hS ν) = mean (p.param : J → ℝ) :=
  UniformSpace.Completion.extension_coe
    (lipschitzWith_meanMap_param hS ν).choose_spec.uniformContinuous p

theorem lipschitzWith_meanExt : ∃ B : NNReal, LipschitzWith B (meanExt hS ν) :=
  ⟨_, (lipschitzWith_meanMap_param hS ν).choose_spec.completion_extension⟩

theorem continuous_meanExt : Continuous (meanExt hS ν) :=
  UniformSpace.Completion.continuous_extension

/-- Extended means lie in the closure of the interior means. -/
theorem meanExt_mem_closure (x : FisherCompletion hS ν) :
    meanExt hS ν x ∈ closure (Set.range fun θ : W ↦ mean (θ : J → ℝ)) := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_closure.preimage (continuous_meanExt hS ν)) fun p ↦ ?_
  rw [meanExt_coe]
  exact subset_closure ⟨p.param, rfl⟩

/-- **Completion points over a mean are Fisher–Cauchy sequences with that limiting mean.** -/
theorem exists_meanExt_eq_iff (M : J → ℝ) :
    (∃ x : FisherCompletion hS ν, meanExt hS ν x = M) ↔
      ∃ u : ℕ → FisherPoint hS ν, CauchySeq u ∧
        Tendsto (fun n ↦ mean ((u n).param : J → ℝ)) atTop (𝓝 M) := by
  constructor
  · rintro ⟨x, hx⟩
    have hx' : x ∈ closure (Set.range ((↑) : FisherPoint hS ν → FisherCompletion hS ν)) := by
      rw [(UniformSpace.Completion.denseRange_coe).closure_range]
      exact Set.mem_univ x
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 hx'
    choose u hu using hv
    refine ⟨u, ?_, ?_⟩
    · rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq ε hε
      refine ⟨N, fun m hm n hn ↦ ?_⟩
      have := hN m hm n hn
      rwa [← hu m, ← hu n, UniformSpace.Completion.dist_eq] at this
    · have h := ((continuous_meanExt hS ν).tendsto x).comp hlim
      rw [hx] at h
      refine h.congr fun n ↦ ?_
      simp only [Function.comp, ← hu n, meanExt_coe]
  · rintro ⟨u, hu, hlim⟩
    have hc : CauchySeq fun n ↦ ((u n : FisherPoint hS ν) : FisherCompletion hS ν) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu ε hε
      exact ⟨N, fun m hm n hn ↦ by rw [UniformSpace.Completion.dist_eq]; exact hN m hm n hn⟩
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨x, tendsto_nhds_unique ?_ hlim⟩
    have h := ((continuous_meanExt hS ν).tendsto x).comp hx
    refine h.congr fun n ↦ ?_
    simp only [Function.comp, meanExt_coe]

end Metric

end Laplace.Multi
