/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseRegressionUniformBound
import Laplace.Multi.ResponseObservableTransport
import Laplace.Multi.ResponseBoundaryJourney

/-!
# The global Lipschitz response on the closed polytope

On a finite configuration the posterior expectation `M ↦ E_{R_M} F` of a bounded observable, as a
function of the mean coordinate `M` on the **closed** moment polytope `conv S(X)`, is Lipschitz in
the Euclidean (sup) norm: `|E_{R_N}F − E_{R_M}F| ≤ L_F ‖N − M‖` (`abs_responseObs_sub_le`,
`lipschitzOnWith_responseObs`). The Fisher form degenerates at the boundary and the natural
coordinate escapes to infinity, but the response of every observable stays Lipschitz in mean
coordinates all the way to the boundary.

The interior statement (`abs_integral_familyMeasure_sub_le_of_mem`) integrates the influence
`d/dt E_{θ(M + t e)}F = ⟨u_F(θ_t), e⟩` along the segment between two interior means and uses the
uniform regression bound `Σ_j |u_F(θ)_j| ≤ L_F` of `ResponseRegressionUniformBound`; the closed
statement approximates two polytope points by the interior points of the polytope journeys from the
featureless mean and passes to the limit with the continuity of the entropy projection on the
polytope. Applied to the atom indicators the bound becomes a law-valued Lipschitz estimate
`Σ_x |R_N{x} − R_M{x}| ≤ L ‖N − M‖` (`sum_abs_qStarVec_sub_le`): the entropy projection
`M ↦ R_M` is a Lipschitz section of the mean map over the closed polytope.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Lipschitz

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x})
include hS hν

set_option linter.unusedFintypeInType false

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The featureless mean. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The moment polytope `conv S(X)`. -/
local notation "hull" => convexHull ℝ (range (statPoint S))

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

/-- The regression direction. -/
local notation "uF" => regressionDir hS ν

omit [Fintype X] [MeasurableSingletonClass X] hν in
/-- **The interior Lipschitz bound**: for interior means `M, N` and a uniform bound `L` on
`Σ_j |u_F(θ)_j|`, `|E_{θ(N)}F − E_{θ(M)}F| ≤ L ‖N − M‖`. -/
theorem abs_integral_familyMeasure_sub_le_of_mem {F : X → ℝ} (hF : Bdd F) {L : ℝ}
    (hL : ∀ θ : 𝕍, ∑ j, |(uF F θ : J → ℝ) j| ≤ L) {M N : J → ℝ} (hM : M ∈ Ω) (hN : N ∈ Ω) :
    |(∫ x, F x ∂Pfam (θr N : J → ℝ)) - ∫ x, F x ∂Pfam (θr M : J → ℝ)| ≤ L * ‖N - M‖ := by
  have he : N - M ∈ 𝕍 := sub_mem_dirSpan_of_mem_momentBody' hS ν (intrinsicInterior_subset hM)
    (intrinsicInterior_subset hN)
  set e : 𝕍 := ⟨N - M, he⟩ with he_def
  set θ₀ : 𝕍 := θr M with hθ₀
  have hmean : mean (θ₀ : J → ℝ) = M := meanMap_responseTheta measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS hM
  -- the segment stays interior
  have hdom : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ responseLineDomain S ν θ₀ e := by
    intro t ht
    change mean (θ₀ : J → ℝ) + t • (e : J → ℝ) ∈ Ω
    rw [hmean]
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · rw [h1, one_smul]
      change M + (N - M) ∈ Ω
      rwa [add_sub_cancel]
    · exact mem_intrinsicInterior_segment_of_mem (convex_momentBody S) hM
        (intrinsicInterior_subset hN) ht.1 h1
  -- the derivative of the line observable is the pairing with the regression direction
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (lineObservable hS ν F θ₀ e)
      (dotJ (uF F (responseLine hS ν θ₀ e t) : J → ℝ) (e : J → ℝ)) (Icc 0 1) t := by
    intro t ht
    have h := hasDerivAt_lineObservable hS ν hF θ₀ e (hdom t ht)
    have hval : -lawCov (Pfam (responseLine hS ν θ₀ e t : J → ℝ)) F
        (dirLoss S (responseLineVel hS ν θ₀ e t : J → ℝ)) =
        dotJ (uF F (responseLine hS ν θ₀ e t) : J → ℝ) (e : J → ℝ) := by
      rw [← fisherInner_regressionDir hS ν hF, responseLineVel,
        fisherInner_chartDerivEquiv_symm' hS ν, neg_neg]
    rw [hval] at h
    exact h.hasDerivWithinAt
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖dotJ (uF F (responseLine hS ν θ₀ e t) : J → ℝ) (e : J → ℝ)‖ ≤ L * ‖N - M‖ := by
    intro t _
    rw [Real.norm_eq_abs]
    refine (abs_dotJ_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hL _) (norm_nonneg _)
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1
    (right_mem_Icc.2 zero_le_one)
  rw [sub_zero, mul_one, Real.norm_eq_abs] at hmv
  have h1 : lineObservable hS ν F θ₀ e 1 = ∫ x, F x ∂Pfam (θr N : J → ℝ) := by
    unfold lineObservable responseLine
    rw [hmean]
    change (∫ x, F x ∂Pfam (θr (M + (1 : ℝ) • (N - M)) : J → ℝ)) = _
    rw [one_smul, add_sub_cancel]
  have h0 : lineObservable hS ν F θ₀ e 0 = ∫ x, F x ∂Pfam (θr M : J → ℝ) := by
    unfold lineObservable responseLine
    rw [hmean, zero_smul, add_zero]
  rwa [h1, h0] at hmv

omit [MeasurableSingletonClass X] in
/-- The polytope journey towards any point of the closed polytope converges to it inside the
polytope. -/
theorem tendsto_segment_mem_hull {M : J → ℝ} (hM : M ∈ hull) :
    Tendsto (fun t : ℝ ↦ m₀ + t • (M - m₀)) (𝓝[<] 1) (𝓝[hull] M) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : Tendsto (fun t : ℝ ↦ m₀ + t • (M - m₀)) (𝓝 1) (𝓝 (m₀ + (1 : ℝ) • (M - m₀))) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 1
    rw [one_smul, add_sub_cancel] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with t ht
    exact intrinsicInterior_subset (mem_intrinsicInterior_segment_of_mem (convex_convexHull ℝ _)
      (featureless_mem_polytope hS ν hν) hM ht.1.le ht.2)

omit [MeasurableSingletonClass X] in
/-- The interior points of the polytope journey are interior means. -/
theorem segment_mem_Ω_of_mem_hull {M : J → ℝ} (hM : M ∈ hull) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) : m₀ + t • (M - m₀) ∈ Ω := by
  rw [intrinsicInterior_momentBody_eq_polytope hS ν hν]
  exact mem_intrinsicInterior_segment_of_mem (convex_convexHull ℝ _)
    (featureless_mem_polytope hS ν hν) hM ht0 ht1

/-- The posterior expectation at a point of the closed polytope, as a barycentric sum. -/
theorem integral_responseProjection_eq_sum {M : J → ℝ} (hM : M ∈ hull) (F : X → ℝ) :
    ∫ x, F x ∂responseProjection hS ν M = ∑ x, qStarVec hS ν M x * F x := by
  have hfin := genRate_ne_top_of_mem_convexHull hS ν hν hM
  rw [← vecMeasure_qStarVec hS ν hfin]
  exact integral_vecMeasure (qStarVec_mem_stdSimplex hS ν hfin).1 F

/-- Along the polytope journey the barycentric sums converge. -/
theorem tendsto_sum_qStarVec_segment {M : J → ℝ} (hM : M ∈ hull) (F : X → ℝ) :
    Tendsto (fun t : ℝ ↦ ∑ x, qStarVec hS ν (m₀ + t • (M - m₀)) x * F x) (𝓝[<] 1)
      (𝓝 (∑ x, qStarVec hS ν M x * F x)) := by
  have hq : Tendsto (qStarVec hS ν) (𝓝[hull] M) (𝓝 (qStarVec hS ν M)) :=
    (continuousOn_qStarVec hS ν hν).continuousWithinAt hM
  have h := hq.comp (tendsto_segment_mem_hull hS ν hν hM)
  exact tendsto_finsetSum _ fun x _ ↦
    (((continuous_apply x).tendsto _).comp h).mul_const (F x)

/-- **THE GLOBAL LIPSCHITZ RESPONSE**: on the closed moment polytope, with `L` a uniform bound on
`Σ_j |u_F(θ)_j|`, `|E_{R_N}F − E_{R_M}F| ≤ L ‖N − M‖` for all `M, N ∈ conv S(X)`. -/
theorem abs_responseObs_sub_le {F : X → ℝ} (hF : Bdd F) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ θ : 𝕍, ∑ j, |(uF F θ : J → ℝ) j| ≤ L) {M N : J → ℝ} (hM : M ∈ hull) (hN : N ∈ hull) :
    |(∫ x, F x ∂responseProjection hS ν N) - ∫ x, F x ∂responseProjection hS ν M| ≤
      L * ‖N - M‖ := by
  rw [integral_responseProjection_eq_sum hS ν hν hN, integral_responseProjection_eq_sum hS ν hν hM]
  have hlim : Tendsto (fun t : ℝ ↦ |(∑ x, qStarVec hS ν (m₀ + t • (N - m₀)) x * F x) -
      ∑ x, qStarVec hS ν (m₀ + t • (M - m₀)) x * F x|) (𝓝[<] 1)
      (𝓝 |(∑ x, qStarVec hS ν N x * F x) - ∑ x, qStarVec hS ν M x * F x|) :=
    ((tendsto_sum_qStarVec_segment hS ν hν hN F).sub
      (tendsto_sum_qStarVec_segment hS ν hν hM F)).abs
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with t ht
  have hMt := segment_mem_Ω_of_mem_hull hS ν hν hM ht.1.le ht.2
  have hNt := segment_mem_Ω_of_mem_hull hS ν hν hN ht.1.le ht.2
  have key := abs_integral_familyMeasure_sub_le_of_mem hS ν hF hL hMt hNt
  rw [integral_familyMeasure_eq_sum hS ν, integral_familyMeasure_eq_sum hS ν,
    atomMass_responseTheta_eq_qStarVec hS ν hMt, atomMass_responseTheta_eq_qStarVec hS ν hNt]
    at key
  refine key.trans (mul_le_mul_of_nonneg_left ?_ hL0)
  have e : m₀ + t • (N - m₀) - (m₀ + t • (M - m₀)) = t • (N - M) := by
    simp only [smul_sub]
    abel
  rw [e, norm_smul, Real.norm_of_nonneg ht.1.le]
  exact mul_le_of_le_one_left (norm_nonneg _) ht.2.le

/-- **The posterior expectation of every bounded observable is Lipschitz on the closed
polytope.** -/
theorem exists_lipschitz_responseObs {F : X → ℝ} (hF : Bdd F) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ M ∈ hull, ∀ N ∈ hull,
      |(∫ x, F x ∂responseProjection hS ν N) - ∫ x, F x ∂responseProjection hS ν M| ≤
        L * ‖N - M‖ := by
  obtain ⟨L, hL0, hL⟩ :=
    exists_uniform_sum_abs_regressionDir_bound hS ν (fun x ↦ (hν x).ne') hF
  exact ⟨L, hL0, fun M hM N hN ↦ abs_responseObs_sub_le hS ν hν hF hL0 hL hM hN⟩

/-- The Lipschitz packaging: `M ↦ E_{R_M}F` is `LipschitzOnWith` on the closed polytope. -/
theorem lipschitzOnWith_responseObs {F : X → ℝ} (hF : Bdd F) :
    ∃ K : NNReal,
      LipschitzOnWith K (fun M : J → ℝ ↦ ∫ x, F x ∂responseProjection hS ν M) hull := by
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_responseObs hS ν hν hF
  refine ⟨⟨L, hL0⟩, LipschitzOnWith.of_dist_le_mul fun M hM N hN ↦ ?_⟩
  rw [Real.dist_eq, dist_eq_norm, abs_sub_comm, norm_sub_rev]
  exact hL M hM N hN

/-- **The entropy projection is Lipschitz on the closed polytope**: there is `L` with
`Σ_x |R_N{x} − R_M{x}| ≤ L ‖N − M‖` for all `M, N ∈ conv S(X)`. -/
theorem sum_abs_qStarVec_sub_le :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ M ∈ hull, ∀ N ∈ hull,
      ∑ x, |qStarVec hS ν N x - qStarVec hS ν M x| ≤ L * ‖N - M‖ := by
  classical
  have hind : ∀ x : X, ∃ L : ℝ, 0 ≤ L ∧ ∀ M ∈ hull, ∀ N ∈ hull,
      |qStarVec hS ν N x - qStarVec hS ν M x| ≤ L * ‖N - M‖ := by
    intro x
    obtain ⟨L, hL0, hL⟩ := exists_lipschitz_responseObs hS ν hν
      (bdd_of_fintype fun y ↦ if y = x then (1 : ℝ) else 0)
    refine ⟨L, hL0, fun M hM N hN ↦ ?_⟩
    have h := hL M hM N hN
    rw [integral_responseProjection_eq_sum hS ν hν hN,
      integral_responseProjection_eq_sum hS ν hν hM] at h
    simpa [Finset.sum_ite_eq', mul_ite, mul_one, mul_zero] using h
  choose Lx hLx0 hLx using hind
  refine ⟨∑ x, Lx x, Finset.sum_nonneg fun x _ ↦ hLx0 x, fun M hM N hN ↦ ?_⟩
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun x _ ↦ hLx x M hM N hN

end Lipschitz

end Laplace.Multi
