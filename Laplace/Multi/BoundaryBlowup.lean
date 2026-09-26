/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AtlasSkewness
import Laplace.Multi.BoundaryEscape
import Laplace.Multi.AngularBound
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Universal curvature blow-up at the relative boundary

Let `M` be a response of finite rate on the relative boundary of the moment body, and `M_s` the
straight path from the featureless response `m₀`. A supporting normal `e` at `M` (with
`⟨e, m₀⟩ < ⟨e, M⟩`, since `m₀` is a relative interior point) gives the nonnegative bounded
observable `Y = ⟨e, M⟩ − ⟨e, S⟩`, whose mean under `Q_s = Π(M_s)` is `(1−s)δ`,
`δ = ⟨e, M − m₀⟩ > 0`, so `Var_{Q_s} Y ≤ R(1−s)δ`. Since the first-order transport of `⟨e,S⟩` along
the atlas is the constant `−⟨e, Δ⟩ = −δ`, the covariance Cauchy–Schwarz inequality gives

`κ(s) ≥ δ / (R (1 − s))`  (`atlasCurv_ge_boundary`),

hence `κ(s) → ∞` as `s → 1` (`tendsto_atlasCurv_nhdsLT_one`), the curvature is not integrable on the
whole path (`not_intervalIntegrable_atlasCurv`), and the natural coordinates escape at least
logarithmically, `−⟨θ_s − θ_0, Δ⟩ ≥ (δ/R) log(1/(1−s))` (`neg_dotJ_atlasTheta_ge_log`). The rate
`1/(1−s)` is universal; sharper asymptotics depend on the tail of the law near the face.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section CauchySchwarz

variable {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ]

/-- The covariance as an integral of centred products. -/
theorem lawCov_eq_integral_centred {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) :
    lawCov ρ f g = ∫ x, (f x - ∫ y, f y ∂ρ) * (g x - ∫ y, g y ∂ρ) ∂ρ := by
  have hfi := integrable_of_bdd_prob ρ hf
  have hgi := integrable_of_bdd_prob ρ hg
  have hfg := integrable_of_bdd_prob ρ (hf.mul hg)
  obtain ⟨a, ha⟩ : ∃ a, a = ∫ y, f y ∂ρ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ∫ y, g y ∂ρ := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have e : ∀ x, (f x - a) * (g x - b) = f x * g x - (a * g x + b * f x - a * b) := fun x ↦ by ring
  simp_rw [e]
  have h1 : Integrable (fun x ↦ a * g x + b * f x) ρ := (hgi.const_mul a).add (hfi.const_mul b)
  have h2 : Integrable (fun x ↦ a * g x + b * f x - a * b) ρ := h1.sub (integrable_const _)
  rw [integral_sub hfg h2, integral_sub h1 (integrable_const _),
    integral_add (hgi.const_mul a) (hfi.const_mul b), integral_const_mul, integral_const_mul,
    integral_const, probReal_univ, one_smul, ← ha, ← hb]
  unfold lawCov
  rw [← ha, ← hb]
  ring

/-- **Cauchy–Schwarz for covariances**: `Cov(f,g)² ≤ Var f · Var g`. -/
theorem lawCov_sq_le {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) :
    lawCov ρ f g ^ 2 ≤ lawCov ρ f f * lawCov ρ g g := by
  rw [lawCov_eq_integral_centred ρ hf hg, lawCov_eq_integral_centred ρ hf hf,
    lawCov_eq_integral_centred ρ hg hg]
  have hf' : Bdd fun x ↦ f x - ∫ y, f y ∂ρ := hf.sub (Bdd.const _)
  have hg' : Bdd fun x ↦ g x - ∫ y, g y ∂ρ := hg.sub (Bdd.const _)
  exact integral_mul_sq_le (integrable_of_bdd_prob ρ (hf'.mul hf'))
    (integrable_of_bdd_prob ρ (hg'.mul hg')) (integrable_of_bdd_prob ρ (hf'.mul hg'))

end CauchySchwarz

section Boundary

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤)
  (hbd : M ∉ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hS hfin hbd

/-- **A supporting normal at a relative boundary response**, strictly separating it from the
featureless response. -/
theorem exists_supporting_normal :
    ∃ e : J → ℝ, (∀ y ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S, dotJ e y ≤ dotJ e M) ∧
      dotJ e (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) < dotJ e M := by
  have hM : M ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := mem_momentBody_of_genRate_ne_top hS ν hfin
  have hm0 : meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 ∈
      intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
    rw [← range_meanMap_eq_intrinsicInterior_momentBody measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS]
    exact ⟨0, rfl⟩
  have hbd' := hbd
  rw [mem_intrinsicInterior_iff_forall_supporting (convex_momentBody S)] at hbd'
  obtain ⟨e, he⟩ := not_forall.1 fun h ↦ hbd' ⟨hM, h⟩
  obtain ⟨hsup, hne⟩ := Classical.not_imp.1 he
  obtain ⟨y, hy'⟩ := not_forall.1 hne
  obtain ⟨hy, hne'⟩ := Classical.not_imp.1 hy'
  refine ⟨e, hsup, ?_⟩
  rcases lt_or_eq_of_le (hsup _ (intrinsicInterior_subset hm0)) with h | h
  · exact h
  · exfalso
    have hm0' := (mem_intrinsicInterior_iff_forall_supporting (convex_momentBody S)).1 hm0
    have := hm0'.2 e (fun z hz ↦ (hsup z hz).trans_eq h.symm) y hy
    rw [h] at this
    exact hne' this

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] hfin hbd in
/-- The statistic lies in the moment body almost everywhere. -/
theorem ae_dirLoss_le_of_supporting {e : J → ℝ}
    (hsup : ∀ y ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S, dotJ e y ≤ dotJ e M) :
    ∀ᵐ x ∂ν, dirLoss S e x ≤ dotJ e M := by
  filter_upwards [ae_statPoint_mem_essRange (μ := ν) (π := fun _ ↦ (1 : ℝ)) measurable_const
    (fun _ ↦ one_pos) hS] with x hx
  exact hsup _ (essRange_subset_momentBody S hx)

omit hbd in
/-- **Universal curvature blow-up**: for a supporting normal `e` at `M` with gap
`δ = ⟨e, M − m₀⟩ > 0` and `R ≥ ⟨e, M⟩ − ⟨e, S⟩ ≥ 0`, the atlas curvature satisfies
`κ(s) ≥ δ / (R (1 − s))`. -/
theorem atlasCurv_ge_of_supporting {e : J → ℝ}
    (hsup : ∀ y ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S, dotJ e y ≤ dotJ e M)
    (hlt : dotJ e (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) < dotJ e M)
    {R : ℝ} (hR : ∀ x, dotJ e M - dirLoss S e x ≤ R) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (dotJ e M - dotJ e (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)) / (R * (1 - s)) ≤
      atlasCurv hS ν hfin s := by
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = dotJ e M -
    dotJ e (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := ⟨_, rfl⟩
  rw [← hδ]
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨Q, hQ⟩ : ∃ Q : Measure X, Q = familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
    (atlasTheta hS ν M s) := ⟨_, rfl⟩
  have hQP : IsProbabilityMeasure Q := by
    rw [hQ]
    exact isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS
      (t := 1) _
  have hQν : Q ≪ ν := by
    rw [hQ]
    unfold familyMeasure
    exact withDensity_absolutelyContinuous ν _
  -- the mean of the gap observable under `Q_s` is `(1 − s) δ`
  have hmeanS : (fun i ↦ ∫ x, S i x ∂Q) = atlasPath S ν M s := by
    rw [hQ, mean_familyMeasure_one_zero hS ν, meanMap_atlasTheta hS ν hfin hs0 hs1]
  have hEf : ∫ x, dirLoss S e x ∂Q = dotJ e (atlasPath S ν M s) := by
    rw [← dotJ_integral_eq _ hS e, hmeanS]
  have hEY : dotJ e M - ∫ x, dirLoss S e x ∂Q = (1 - s) * δ := by
    rw [hEf, atlasPath_eq_sub, (isLinearMap_dotJ e).map_sub M, (isLinearMap_dotJ e).map_smul,
      (isLinearMap_dotJ e).map_sub M, hδ, smul_eq_mul]
    ring
  -- the gap observable is nonnegative and bounded by `R` almost everywhere
  have hY0 : ∀ᵐ x ∂Q, 0 ≤ dotJ e M - dirLoss S e x := by
    filter_upwards [hQν.ae_le (ae_dirLoss_le_of_supporting hS ν hsup)] with x hx
    linarith
  have hR0 : 0 < R := by
    have h1 : ∫ x, (dotJ e M - dirLoss S e x) ∂Q ≤ ∫ _x, R ∂Q :=
      integral_mono_ae (integrable_of_bdd_prob Q ((Bdd.const _).sub (bdd_dirLoss hS e)))
        (integrable_const R) (Eventually.of_forall hR)
    rw [integral_sub (integrable_const _) (integrable_of_bdd_prob Q (bdd_dirLoss hS e)),
      integral_const, probReal_univ, one_smul, hEY, integral_const, probReal_univ, one_smul] at h1
    nlinarith
  -- the variance of the gap observable is at most `R (1 − s) δ`
  have hvar : lawCov Q (dirLoss S e) (dirLoss S e) ≤ R * ((1 - s) * δ) := by
    rw [lawCov_self_eq_integral_sq Q (bdd_dirLoss hS e)]
    have hY : Bdd fun x ↦ dotJ e M - dirLoss S e x := (Bdd.const _).sub (bdd_dirLoss hS e)
    have e1 : ∀ x, (dirLoss S e x - ∫ y, dirLoss S e y ∂Q) * (dirLoss S e x - ∫ y, dirLoss S e y ∂Q)
        = (dotJ e M - dirLoss S e x) * (dotJ e M - dirLoss S e x) -
          2 * (dotJ e M - ∫ y, dirLoss S e y ∂Q) * (dotJ e M - dirLoss S e x) +
          (dotJ e M - ∫ y, dirLoss S e y ∂Q) ^ 2 := fun x ↦ by ring
    simp_rw [e1]
    have hi1 := integrable_of_bdd_prob Q (hY.mul hY)
    have hi2 : Integrable (fun x ↦ 2 * (dotJ e M - ∫ y, dirLoss S e y ∂Q) *
        (dotJ e M - dirLoss S e x)) Q := (integrable_of_bdd_prob Q hY).const_mul _
    have hi12 : Integrable (fun x ↦ (dotJ e M - dirLoss S e x) * (dotJ e M - dirLoss S e x) -
        2 * (dotJ e M - ∫ y, dirLoss S e y ∂Q) * (dotJ e M - dirLoss S e x)) Q := hi1.sub hi2
    rw [integral_add hi12 (integrable_const _), integral_sub hi1 hi2, integral_const_mul,
      integral_sub (integrable_const _) (integrable_of_bdd_prob Q (bdd_dirLoss hS e)),
      integral_const, probReal_univ, one_smul, integral_const, probReal_univ, one_smul, hEY]
    have h2 : ∫ x, (dotJ e M - dirLoss S e x) * (dotJ e M - dirLoss S e x) ∂Q ≤
        ∫ x, R * (dotJ e M - dirLoss S e x) ∂Q := by
      refine integral_mono_ae hi1 ((integrable_of_bdd_prob Q hY).const_mul R) ?_
      filter_upwards [hY0] with x hx
      exact mul_le_mul_of_nonneg_right (hR x) hx
    rw [integral_const_mul, integral_sub (integrable_const _)
      (integrable_of_bdd_prob Q (bdd_dirLoss hS e)), integral_const, probReal_univ, one_smul,
      hEY] at h2
    nlinarith
  -- the first-order transport of `⟨e,S⟩` is the constant `−δ`
  have hcov : lawCov Q (dirLoss S e) (dirLoss S (atlasVel hS ν hfin s)) = -δ := by
    rw [hQ, lawCov_dirLoss_atlasVel hS ν hfin s e, (isLinearMap_dotJ e).map_sub M, hδ]
  have hκ : atlasCurv hS ν hfin s =
      lawCov Q (dirLoss S (atlasVel hS ν hfin s)) (dirLoss S (atlasVel hS ν hfin s)) := by
    rw [atlasCurv_eq_priorCov, priorCov_eq_lawCov_familyMeasure hS ν, hQ]
  have hcs := lawCov_sq_le Q (bdd_dirLoss hS e) (bdd_dirLoss hS (atlasVel hS ν hfin s : J → ℝ))
  rw [hcov, ← hκ, neg_sq] at hcs
  have hκ0 : 0 ≤ atlasCurv hS ν hfin s := atlasCurv_nonneg hS ν hfin s
  have h1s : 0 < 1 - s := by linarith
  rw [div_le_iff₀ (by positivity)]
  -- `δ² ≤ Var · κ ≤ R (1−s) δ κ`, so `δ ≤ R (1−s) κ`
  have h3 : δ ^ 2 ≤ R * ((1 - s) * δ) * atlasCurv hS ν hfin s :=
    hcs.trans (mul_le_mul_of_nonneg_right hvar hκ0)
  nlinarith

/-- **Universal curvature blow-up at the boundary**: `∃ δ R > 0, κ(s) ≥ δ / (R (1−s))` on
`[0,1)`. -/
theorem atlasCurv_ge_boundary :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ s, 0 ≤ s → s < 1 →
      δ / (R * (1 - s)) ≤ atlasCurv hS ν hfin s := by
  obtain ⟨e, hsup, hlt⟩ := exists_supporting_normal hS ν hfin hbd
  obtain ⟨-, B, hB⟩ := bdd_dirLoss hS e
  have hR : ∀ x, dotJ e M - dirLoss S e x ≤ |dotJ e M| + B + 1 := fun x ↦ by
    linarith [le_abs_self (dotJ e M), neg_abs_le (dirLoss S e x), hB x]
  refine ⟨_, _, sub_pos.2 hlt, ?_, fun s hs0 hs1 ↦
    atlasCurv_ge_of_supporting hS ν hfin hsup hlt hR hs0 hs1⟩
  have := hB (Classical.arbitrary X)
  linarith [abs_nonneg (dotJ e M), abs_nonneg (dirLoss S e (Classical.arbitrary X))]

/-- **The curvature blows up at the boundary**: `κ(s) → ∞` as `s → 1⁻`. -/
theorem tendsto_atlasCurv_nhdsLT_one :
    Tendsto (atlasCurv hS ν hfin) (𝓝[<] (1 : ℝ)) atTop := by
  obtain ⟨δ, R, hδ, hR, hbound⟩ := atlasCurv_ge_boundary hS ν hfin hbd
  have h1 : Tendsto (fun s : ℝ ↦ 1 - s) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h := (continuous_sub_left (1 : ℝ)).tendsto 1
      rw [sub_self] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_pos.2 (Set.mem_Iio.1 hs)
  have h2 : Tendsto (fun s : ℝ ↦ δ / R * (1 - s)⁻¹) (𝓝[<] (1 : ℝ)) atTop :=
    (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop (div_pos hδ hR)
  refine tendsto_atTop_mono' _ ?_ h2
  have h01 : ∀ᶠ s in 𝓝[<] (1 : ℝ), s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT zero_lt_one
  filter_upwards [h01] with s hs
  have e : δ / R * (1 - s)⁻¹ = δ / (R * (1 - s)) := by rw [← div_eq_mul_inv, div_div]
  rw [e]
  exact hbound s hs.1.le hs.2

/-- **The curvature is not integrable on the whole path**: `∫₀¹ κ = ∞`. -/
theorem not_intervalIntegrable_atlasCurv :
    ¬ IntervalIntegrable (atlasCurv hS ν hfin) volume 0 1 := by
  obtain ⟨δ, R, hδ, hR, hbound⟩ := atlasCurv_ge_boundary hS ν hfin hbd
  intro hint
  have hnot : ¬ IntervalIntegrable (fun s : ℝ ↦ (s - 1)⁻¹) volume 0 1 := by
    rw [intervalIntegrable_sub_inv_iff]
    simp
  refine hnot ?_
  have hint' : IntervalIntegrable (fun s ↦ (δ / R)⁻¹ * atlasCurv hS ν hfin s) volume 0 1 :=
    hint.const_mul _
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hint' ⊢
  refine Integrable.mono' hint' ?_ ?_
  · exact (Measurable.inv (measurable_id.sub measurable_const)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun s hs ↦ ?_
    rcases eq_or_lt_of_le hs.2 with rfl | hs1
    · simp only [sub_self, inv_zero, norm_zero]
      exact mul_nonneg (by positivity) (atlasCurv_nonneg hS ν hfin 1)
    · have hb := hbound s hs.1.le hs1
      have h1s : 0 < 1 - s := by linarith
      rw [Real.norm_eq_abs, abs_of_neg (inv_lt_zero.2 (by linarith : s - 1 < 0)), ← inv_neg,
        neg_sub, inv_div]
      calc (1 - s)⁻¹ = R / δ * (δ / (R * (1 - s))) := by field_simp
        _ ≤ R / δ * atlasCurv hS ν hfin s := mul_le_mul_of_nonneg_left hb (by positivity)

/-- **Logarithmic escape of the natural coordinates**: for `s ∈ [0,1)`,
`−⟨θ_s, Δ⟩ ≥ (δ/R) log(1/(1−s))`. -/
theorem neg_dotJ_atlasTheta_ge_log :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ s, 0 ≤ s → s < 1 →
      δ / R * Real.log (1 / (1 - s)) ≤
        -dotJ (atlasTheta hS ν M s : J → ℝ)
          (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
  obtain ⟨δ, R, hδ, hR, hbound⟩ := atlasCurv_ge_boundary hS ν hfin hbd
  refine ⟨δ, R, hδ, hR, fun s hs0 hs1 ↦ ?_⟩
  rw [neg_dotJ_atlasTheta_eq_integral hS ν hfin hs0 hs1]
  have h1s : 0 < 1 - s := by linarith
  have hlog : ∫ u in (0 : ℝ)..s, δ / R * (1 - u)⁻¹ = δ / R * Real.log (1 / (1 - s)) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left
      (fun x : ℝ ↦ x⁻¹) 1, sub_zero, integral_inv_of_pos h1s one_pos]
  rw [← hlog]
  have hκint : IntervalIntegrable (atlasCurv hS ν hfin) volume 0 s := by
    refine ContinuousOn.intervalIntegrable fun u hu ↦ ?_
    rw [uIcc_of_le hs0] at hu
    exact (continuousAt_atlasCurv hS ν hfin hu.1 (lt_of_le_of_lt hu.2 hs1)).continuousWithinAt
  have hint : IntervalIntegrable (fun u : ℝ ↦ δ / R * (1 - u)⁻¹) volume 0 s := by
    refine ContinuousOn.intervalIntegrable fun u hu ↦ ?_
    rw [uIcc_of_le hs0] at hu
    exact (continuousAt_const.mul ((continuous_sub_left (1 : ℝ)).continuousAt.inv₀
      (by linarith [hu.2]))).continuousWithinAt
  refine intervalIntegral.integral_mono_on hs0 hint hκint fun u hu ↦ ?_
  have e : δ / R * (1 - u)⁻¹ = δ / (R * (1 - u)) := by rw [← div_eq_mul_inv, div_div]
  rw [e]
  exact hbound u hu.1 (lt_of_le_of_lt hu.2 hs1)

end Boundary

end Laplace.Multi
