/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseFaceCalculus
import Laplace.Multi.ResponseGlobalLipschitz

/-!
# Stratified transport of posterior expectations across the moment polytope

The **tangential response field** `u_F(M) := u_F^{A}(M)`, `A = supp q*(M)`, is the regression
direction of the observable `F` relative to the conditioned law `ν_A` at the chart point of `M`
(`tangentField`): a vector of the direction space `W_A` of the minimal face of `M`, defined at every
point of the closed polytope. Every point of the polytope lies in the relative interior of its
minimal face (`mem_intrinsicInterior_carriedResponses_supportSet`), so the facewise interior
calculus applies at every point, and the global Lipschitz bound turns the facewise line derivative
into a derivative along every differentiable path whose velocity is tangent to the current face
(`hasDerivAt_responseObs_path`):
`d/ds E_{R_{M(s)}}[F] = ⟨u_F(M(s)), Ṁ(s)⟩`.
Velocities are automatically tangent wherever the support is locally constant
(`hasDerivAt_mem_vectorSpan_of_supportSet_eventually_eq`). Integrating along a `C¹` journey
`M : [0,1] → conv S(X)` whose velocity is tangent off a countable set of times — for instance a
journey with finitely many face crossings — gives the **stratified transport theorem**
(`stratified_transport`, `stratified_transport_of_locally_constant_support`):
`E_{R_{M(1)}}[F] − E_{R_{M(0)}}[F] = ∫₀¹ ⟨u_F(M(t)), Ṁ(t)⟩ dt`,
the change of a posterior expectation along any journey through the data manifold, from any
starting law to any ending law, is the line integral of the tangential response field, which
switches base law and tangent space at each face crossing.
-/

open MeasureTheory Filter Topology Set Asymptotics

namespace Laplace.Multi

section Chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The chain rule through a Lipschitz map with a line derivative**: a Lipschitz function on a set
composed with a differentiable path is differentiable wherever the function is differentiable along
the tangent line of the path. -/
theorem hasDerivAt_comp_of_lipschitzOnWith_line {g : E → ℝ} {K : Set E} {C : NNReal}
    (hg : LipschitzOnWith C g K) {M : ℝ → E} {v : E} {t : ℝ} (hM : HasDerivAt M v t)
    (hK : ∀ᶠ s in 𝓝 t, M s ∈ K) (hline : ∀ᶠ s in 𝓝 t, M t + (s - t) • v ∈ K) {d : ℝ}
    (hd : HasDerivAt (fun r : ℝ ↦ g (M t + r • v)) d 0) : HasDerivAt (fun s ↦ g (M s)) d t := by
  have h1 : (fun s ↦ g (M s) - g (M t + (s - t) • v)) =o[𝓝 t] fun s ↦ s - t := by
    refine (IsBigO.of_bound (C : ℝ) ?_).trans_isLittleO hM.isLittleO
    filter_upwards [hK, hline] with s hs hs'
    have := hg.dist_le_mul (M s) hs (M t + (s - t) • v) hs'
    rw [Real.dist_eq, dist_eq_norm, sub_add_eq_sub_sub] at this
    rw [Real.norm_eq_abs]
    exact this
  have h2 : HasDerivAt (fun s ↦ g (M t + (s - t) • v)) d t := by
    have := hd.comp_of_eq t ((hasDerivAt_id' (x := t)).sub_const t) (sub_self t).symm
    simpa [Function.comp_def] using this
  refine HasDerivAt.of_isLittleO ((h1.add h2.isLittleO).congr_left fun s ↦ ?_)
  simp only [sub_self, zero_smul, add_zero]
  ring

end Chain

section Field

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν]
include hS

set_option linter.unusedFintypeInType false

open Classical in
/-- **The face regression field**: the regression direction of `F` relative to the conditioned law
`ν_A` at the chart point of `M` (zero when `ν_A` is not a probability law). -/
noncomputable def faceField (A : Set X) (F : X → ℝ) (M : J → ℝ) : J → ℝ :=
  if h : IsProbabilityMeasure (faceMeasure ν A) then
    (haveI := h
     (regressionDir hS (faceMeasure ν A) F (responseTheta measurable_const (integrable_const 1)
       (fun _ ↦ one_pos) (one_integral_pos (faceMeasure ν A)) hS M) : J → ℝ))
  else 0

omit [Fintype X] [MeasurableSingletonClass X] [IsProbabilityMeasure ν] in
theorem faceField_eq (A : Set X) [h : IsProbabilityMeasure (faceMeasure ν A)] (F : X → ℝ)
    (M : J → ℝ) :
    faceField hS ν A F M = (regressionDir hS (faceMeasure ν A) F
      (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos (faceMeasure ν A)) hS M) : J → ℝ) := by
  unfold faceField
  rw [dif_pos h]

/-- **The tangential response field** `u_F(M) = u_F^{supp q*(M)}(M)`: the face regression
direction of `F` on the minimal face of `M`, defined at every point of the closed polytope. -/
noncomputable def tangentField (F : X → ℝ) (M : J → ℝ) : J → ℝ :=
  faceField hS ν (supportSet hS ν M) F M

end Field

section Transport

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x})
include hS hν

set_option linter.unusedFintypeInType false

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

omit [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] hS hν
  [IsProbabilityMeasure ν] in
theorem dotJ_sum_smul (e : J → ℝ) (p : X → ℝ) (f : X → J → ℝ) :
    dotJ e (∑ x, p x • f x) = ∑ x, p x * dotJ e (f x) := by
  simp only [dotJ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- **Every point of the polytope is a relative-interior point of its minimal face.** -/
theorem mem_intrinsicInterior_carriedResponses_supportSet {M : J → ℝ} (hM : M ∈ hull) :
    M ∈ intrinsicInterior ℝ (carriedResponses S (supportSet hS ν M)) := by
  rw [mem_intrinsicInterior_iff_forall_supporting (convex_carriedResponses S _)]
  refine ⟨mem_carriedResponses_supportSet hS ν hν hM, fun e he y hy ↦ ?_⟩
  have hq := qStarVec_mem_stdSimplex_of_mem_hull hS ν hν hM
  have hMq : M = ∑ x, qStarVec hS ν M x • statPoint S x := by
    rw [← vecMoment_eq_sum_smul,
      vecMoment_qStarVec hS ν (genRate_ne_top_of_mem_convexHull hS ν hν hM)]
  have hface : ∀ x ∈ supportSet hS ν M, statPoint S x ∈ carriedResponses S (supportSet hS ν M) := by
    intro x hx
    rw [carriedResponses_eq_convexHull_image]
    exact subset_convexHull ℝ _ ⟨x, hx, rfl⟩
  -- the maximising functional is constant on the atoms of the support
  have hatom : ∀ x ∈ supportSet hS ν M, dotJ e (statPoint S x) = dotJ e M := by
    have hsum : ∑ x, qStarVec hS ν M x * (dotJ e M - dotJ e (statPoint S x)) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq.2, one_mul]
      rw [← dotJ_sum_smul, ← hMq, sub_self]
    have hnn : ∀ x ∈ Finset.univ, 0 ≤ qStarVec hS ν M x * (dotJ e M - dotJ e (statPoint S x)) := by
      intro x _
      by_cases hx : x ∈ supportSet hS ν M
      · exact mul_nonneg (hq.1 x) (sub_nonneg.2 (he _ (hface x hx)))
      · rw [qStarVec_eq_zero_of_notMem hS ν hν hM hx, zero_mul]
    intro x hx
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum x (Finset.mem_univ x)
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 (ne_of_gt hx)
    · linarith
  obtain ⟨b, hb, hbs, rfl⟩ := hy
  rw [vecMoment_eq_sum_smul, dotJ_sum_smul]
  calc ∑ x, b x * dotJ e (statPoint S x) = ∑ x, b x * dotJ e M := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        by_cases hx : x ∈ supportSet hS ν M
        · rw [hatom x hx]
        · rw [hbs x hx, zero_mul, zero_mul]
    _ = dotJ e M := by rw [← Finset.sum_mul, hb.2, one_mul]

omit [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X] [Fintype J] [Nonempty J] hS
  [IsProbabilityMeasure ν] hν in
variable (S) in
/-- The direction space of a face polytope is the direction space of its atoms. -/
theorem vectorSpan_carriedResponses (A : Set X) :
    vectorSpan ℝ (carriedResponses S A) = vectorSpan ℝ (statPoint S '' A) := by
  rw [carriedResponses_eq_convexHull_image, ← direction_affineSpan, affineSpan_convexHull,
    direction_affineSpan]

/-- **Velocities are tangent where the support is locally constant**: if the support of the
response is constant near `t` then the velocity of the path at `t` lies in the direction space of
the current face. -/
theorem hasDerivAt_mem_vectorSpan_of_supportSet_eventually_eq {M : ℝ → J → ℝ} {v : J → ℝ} {t : ℝ}
    (hM : HasDerivAt M v t) (hhull : ∀ᶠ s in 𝓝 t, M s ∈ hull)
    (hconst : ∀ᶠ s in 𝓝 t, supportSet hS ν (M s) = supportSet hS ν (M t)) :
    v ∈ vectorSpan ℝ (statPoint S '' supportSet hS ν (M t)) := by
  have hclosed : IsClosed (vectorSpan ℝ (statPoint S '' supportSet hS ν (M t)) : Set (J → ℝ)) :=
    Submodule.closed_of_finiteDimensional _
  refine hclosed.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.1 hM) ?_
  have hMt : M t ∈ hull := hhull.self_of_nhds
  filter_upwards [(hhull.and hconst).filter_mono nhdsWithin_le_nhds] with s ⟨hs, hs'⟩
  rw [slope_def_module]
  refine Submodule.smul_mem _ _ ?_
  rw [← vectorSpan_carriedResponses S]
  have h1 := mem_carriedResponses_supportSet hS ν hν hs
  rw [hs'] at h1
  simpa [vsub_eq_sub] using vsub_mem_vectorSpan ℝ h1 (mem_carriedResponses_supportSet hS ν hν hMt)

/-- **The derivative of a posterior expectation along a path**: wherever the velocity of a
differentiable path through the polytope is tangent to the current face, the posterior expectation
of `F` along the path has derivative `⟨u_F(M(t)), Ṁ(t)⟩`, the pairing of the velocity with the
tangential response field. -/
theorem hasDerivAt_responseObs_path {F : X → ℝ} (hF : Bdd F) {M : ℝ → J → ℝ} {v : J → ℝ}
    {t : ℝ} (hM : HasDerivAt M v t) (hhull : ∀ᶠ s in 𝓝 t, M s ∈ hull)
    (hv : v ∈ vectorSpan ℝ (statPoint S '' supportSet hS ν (M t))) :
    HasDerivAt (fun s ↦ ∫ x, F x ∂responseProjection hS ν (M s))
      (dotJ (tangentField hS ν F (M t)) v) t := by
  have hMt : M t ∈ hull := hhull.self_of_nhds
  have : IsProbabilityMeasure (faceMeasure ν (supportSet hS ν (M t))) :=
    isProbabilityMeasure_faceMeasure ν (measure_supportSet_ne_zero hS ν hν hMt)
  have hrel := mem_intrinsicInterior_carriedResponses_supportSet hS ν hν hMt
  have hvW : v ∈ dirSpan (faceMeasure ν (supportSet hS ν (M t))) (fun _ ↦ (1 : ℝ)) S := by
    rw [dirSpan_faceMeasure_eq_vectorSpan_image hS ν hν]
    exact hv
  have hline := hasDerivAt_responseObs_face hS ν hν hMt rfl hrel hF ⟨v, hvW⟩
  obtain ⟨C, hC⟩ := lipschitzOnWith_responseObs hS ν hν hF
  -- the tangent line stays in the polytope
  obtain ⟨-, δ, hδ, hball⟩ := mem_intrinsicInterior_iff_exists_ball.1 hrel
  have hsmall : ∀ᶠ s in 𝓝 t, M t + (s - t) • v ∈ hull := by
    have hcont : Tendsto (fun s : ℝ ↦ (s - t) • v) (𝓝 t) (𝓝 0) := by
      have h : Continuous (fun s : ℝ ↦ (s - t) • v) := by fun_prop
      simpa using h.tendsto t
    filter_upwards [hcont.eventually (Metric.ball_mem_nhds (0 : J → ℝ) hδ)] with s hs
    refine carriedResponses_subset_hull (S := S) _ (hball _ ?_ (mem_ball_zero_iff.1 hs))
    rw [direction_affineSpan, vectorSpan_carriedResponses S]
    exact Submodule.smul_mem _ _ hv
  unfold tangentField
  rw [faceField_eq]
  exact hasDerivAt_comp_of_lipschitzOnWith_line hC hM hhull hsmall hline

/-- **STRATIFIED TRANSPORT**: along a `C¹` journey `M : [0,1] → conv S(X)` whose velocity is
tangent to the current face off a countable set of times, the change of a posterior expectation is
the line integral of the tangential response field,
`E_{R_{M(1)}}[F] − E_{R_{M(0)}}[F] = ∫₀¹ ⟨u_F(M(t)), Ṁ(t)⟩ dt`. -/
theorem stratified_transport {F : X → ℝ} (hF : Bdd F) {M V : ℝ → J → ℝ} {B : ℝ}
    (hhull : ∀ t ∈ Icc (0 : ℝ) 1, M t ∈ hull) (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt M (V t) t)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖V t‖ ≤ B) {s : Set ℝ} (hs : s.Countable)
    (htan : ∀ t ∈ Ioo (0 : ℝ) 1 \ s,
      V t ∈ vectorSpan ℝ (statPoint S '' supportSet hS ν (M t))) :
    (∫ x, F x ∂responseProjection hS ν (M 1)) - ∫ x, F x ∂responseProjection hS ν (M 0) =
      ∫ t in (0 : ℝ)..1, dotJ (tangentField hS ν F (M t)) (V t) := by
  set g : ℝ → ℝ := fun t ↦ ∫ x, F x ∂responseProjection hS ν (M t) with hg
  set f' : ℝ → ℝ := fun t ↦ dotJ (tangentField hS ν F (M t)) (V t) with hf'
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨C, hC⟩ := lipschitzOnWith_responseObs hS ν hν hF
  -- the path is Lipschitz, hence so is the expectation along it
  have hMlip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖M y - M x‖ ≤ B * ‖y - x‖ :=
    fun x hx y hy ↦ (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz ↦ (hd z hz).hasDerivWithinAt) hB hx hy
  have hglip : LipschitzOnWith (C * B.toNNReal) g (Icc 0 1) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
    calc dist (g x) (g y) ≤ C * dist (M x) (M y) := hC.dist_le_mul _ (hhull x hx) _ (hhull y hy)
      _ ≤ C * (B * dist x y) := by
          rw [dist_eq_norm, Real.dist_eq, ← Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hMlip y hy x hx) C.2
      _ = ((C * B.toNNReal : NNReal) : ℝ) * dist x y := by
          rw [NNReal.coe_mul, Real.coe_toNNReal B hB0, mul_assoc]
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1 \ s, HasDerivAt g (f' t) t := fun t ht ↦
    hasDerivAt_responseObs_path hS ν hν hF (hd t (Ioo_subset_Icc_self ht.1))
      (Filter.mem_of_superset (Icc_mem_nhds ht.1.1 ht.1.2) hhull) (htan t ht)
  have hbound : ∀ t ∈ Ioo (0 : ℝ) 1 \ s, ‖f' t‖ ≤ C * B := fun t ht ↦ by
    have := (hderiv t ht).le_of_lipschitzOn (Icc_mem_nhds ht.1.1 ht.1.2) hglip
    rw [NNReal.coe_mul, Real.coe_toNNReal B hB0] at this
    exact this
  have hae : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), f' t = deriv g t := by
    have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by
      rw [ae_iff]
      simp
    have h2 : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ s := by
      rw [ae_iff]
      simpa using hs.measure_zero volume
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae h1,
      ae_restrict_of_ae h2] with t ht ht1 hts
    exact ((hderiv t ⟨⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩, hts⟩).deriv).symm
  have hint : IntervalIntegrable f' volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine (Measure.integrableOn_of_bounded (f := deriv g) (M := C * B) measure_Ioc_lt_top.ne
      ?_ ?_).congr_fun_ae (Filter.EventuallyEq.symm hae)
    · exact (measurable_deriv _).aestronglyMeasurable
    · have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by
        rw [ae_iff]
        simp
      have h2 : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ s := by
        rw [ae_iff]
        simpa using hs.measure_zero volume
      filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae h1,
        ae_restrict_of_ae h2, hae] with t ht ht1 hts hft
      rw [← hft]
      exact hbound t ⟨⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩, hts⟩
  exact (integral_eq_of_hasDerivAt_off_countable_of_le g f' zero_le_one hs hglip.continuousOn
    hderiv hint).symm

/-- **Stratified transport for journeys with locally constant support**: if the support of the
response is locally constant off a countable set of times (for instance a journey with finitely
many face crossings), the velocity is automatically tangent and the transport formula holds. -/
theorem stratified_transport_of_locally_constant_support {F : X → ℝ} (hF : Bdd F)
    {M V : ℝ → J → ℝ} {B : ℝ} (hhull : ∀ t ∈ Icc (0 : ℝ) 1, M t ∈ hull)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt M (V t) t) (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖V t‖ ≤ B)
    {s : Set ℝ} (hs : s.Countable)
    (hconst : ∀ t ∈ Ioo (0 : ℝ) 1 \ s, ∀ᶠ u in 𝓝 t, supportSet hS ν (M u) = supportSet hS ν (M t)) :
    (∫ x, F x ∂responseProjection hS ν (M 1)) - ∫ x, F x ∂responseProjection hS ν (M 0) =
      ∫ t in (0 : ℝ)..1, dotJ (tangentField hS ν F (M t)) (V t) :=
  stratified_transport hS ν hν hF hhull hd hB hs fun t ht ↦
    hasDerivAt_mem_vectorSpan_of_supportSet_eventually_eq hS ν hν (hd t (Ioo_subset_Icc_self ht.1))
      (Filter.mem_of_superset (Icc_mem_nhds ht.1.1 ht.1.2) hhull) (hconst t ht)

end Transport

end Laplace.Multi
