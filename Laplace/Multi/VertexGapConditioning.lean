/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.VertexGapForward

/-!
# Conditioning is `L¹`-continuous at a law carried by the conditioning set

If probability densities `g_n → f` in `L¹` and `f` is carried by `A` (`∫_A f = 1`), then the
conditioned densities `1_A g_n / ∫_A g_n` converge to `f` in `L¹` as well, with

  `‖1_A g/a − f‖₁ ≤ 2 ‖g − f‖₁`,  `a = ∫_A g`   (`integral_abs_indicator_div_sub_le`).

Applied to the family laws `P_{η_n}` converging to `q_M` (carried by the face fibre `A`), the
face-conditional laws `P_{η_n}(·|A) = ν_F.tilted(−⟨η_n,S⟩)` converge to `q_M` in `L¹`
(`tendsto_integral_abs_faceDens_sub`), so their means converge to `M`
(`tendsto_meanMap_faceMeasure_of_tendsto_meanMap`): the second half of the forward vertex-gap
criterion.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Conditioning

variable {X : Type*} [MeasurableSpace X] (ν : Measure X)

/-- **Conditioning is `L¹`-continuous at a law carried by the conditioning set.** -/
theorem integral_abs_indicator_div_sub_le {f g : X → ℝ} (hf : Integrable f ν) (hg : Integrable g ν)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) {A : Set X} (hA : MeasurableSet A)
    (hfA : ∫ x in A, f x ∂ν = 1) (hfAc : ∫ x in Aᶜ, f x ∂ν = 0) {a : ℝ} (ha : a = ∫ x in A, g x ∂ν)
    (ha0 : 0 < a) :
    ∫ x, |A.indicator g x / a - f x| ∂ν ≤ 2 * ∫ x, |g x - f x| ∂ν := by
  -- pointwise: `|1_A g/a − f| ≤ 1_A g |1/a − 1| + 1_A |g − f| + 1_{Aᶜ} f`
  have hpt : ∀ x, |A.indicator g x / a - f x| ≤
      A.indicator g x * |1 / a - 1| + A.indicator (fun x ↦ |g x - f x|) x + Aᶜ.indicator f x := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_notMem
        (Set.notMem_compl_iff.2 hx), add_zero]
      calc |g x / a - f x| = |g x * (1 / a - 1) + (g x - f x)| := by ring_nf
        _ ≤ |g x * (1 / a - 1)| + |g x - f x| := abs_add_le _ _
        _ = g x * |1 / a - 1| + |g x - f x| := by rw [abs_mul, abs_of_nonneg (hg0 x)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Set.indicator_of_mem
        (Set.mem_compl hx), zero_div, zero_sub, abs_neg, abs_of_nonneg (hf0 x), zero_mul, zero_add,
        zero_add]
  have hint1 : Integrable (fun x ↦ A.indicator g x * |1 / a - 1|) ν :=
    (hg.indicator hA).mul_const _
  have hint2 : Integrable (fun x ↦ A.indicator (fun x ↦ |g x - f x|) x) ν :=
    (hg.sub hf).abs.indicator hA
  have hint3 : Integrable (fun x ↦ Aᶜ.indicator f x) ν := hf.indicator hA.compl
  have hint0 : Integrable (fun x ↦ |A.indicator g x / a - f x|) ν :=
    (((hg.indicator hA).div_const a).sub hf).abs
  calc ∫ x, |A.indicator g x / a - f x| ∂ν
      ≤ ∫ x, (A.indicator g x * |1 / a - 1| + A.indicator (fun x ↦ |g x - f x|) x +
          Aᶜ.indicator f x) ∂ν :=
        integral_mono hint0 ((hint1.add hint2).add hint3) hpt
    _ = |1 / a - 1| * a + (∫ x in A, |g x - f x| ∂ν) + ∫ x in Aᶜ, f x ∂ν := by
        have hint12 : Integrable (fun x ↦ A.indicator g x * |1 / a - 1| +
            A.indicator (fun x ↦ |g x - f x|) x) ν := hint1.add hint2
        rw [integral_add hint12 hint3, integral_add hint1 hint2, integral_mul_const,
          integral_indicator hA, integral_indicator hA, integral_indicator hA.compl, ← ha,
          mul_comm]
    _ = |1 - a| + ∫ x in A, |g x - f x| ∂ν := by
        have e : (1 / a - 1) * a = 1 - a := by field_simp
        rw [hfAc, add_zero, ← e, abs_mul, abs_of_pos ha0]
    _ ≤ (∫ x, |g x - f x| ∂ν) + ∫ x, |g x - f x| ∂ν := by
        refine add_le_add ?_ (setIntegral_le_integral (hg.sub hf).abs
          (Eventually.of_forall fun x ↦ abs_nonneg _))
        rw [ha, ← hfA, ← integral_sub hf.integrableOn hg.integrableOn]
        refine abs_integral_le_integral_abs.trans ?_
        refine (setIntegral_le_integral (hf.sub hg).abs
          (Eventually.of_forall fun x ↦ abs_nonneg _)).trans (le_of_eq ?_)
        exact integral_congr_ae (Eventually.of_forall fun x ↦ by
          beta_reduce
          rw [Pi.sub_apply, abs_sub_comm])
    _ = 2 * ∫ x, |g x - f x| ∂ν := by ring

end Conditioning

section Face

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (u : J → ℝ) (β : ℝ)
include hS

omit [Nonempty X] [Nonempty J] in
/-- The face density is the conditioned family density: `1_A p_η / P_η(A)`. -/
theorem faceDens_eq_indicator_famDens_div (η : J → ℝ) (x : X) :
    faceDens S ν η u β x =
      {x | dirLoss S u x = β}.indicator (famDens S ν η) x /
        ∫ x in {x | dirLoss S u x = β}, famDens S ν η x ∂ν := by
  have hZ := (famZ_pos hS ν η).ne'
  have hint : ∫ x in {x | dirLoss S u x = β}, famDens S ν η x ∂ν =
      faceMass S ν η u β / famZ S ν η := by
    unfold faceMass famDens
    rw [integral_div]
  rw [hint, faceDens]
  by_cases hx : x ∈ {x | dirLoss S u x = β}
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, famDens]
    field_simp
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_div]

omit [Nonempty X] [Nonempty J] in
theorem integral_famDens_faceFibre_pos (hp : 0 < ν.real {x | dirLoss S u x = β}) (η : J → ℝ) :
    0 < ∫ x in {x | dirLoss S u x = β}, famDens S ν η x ∂ν := by
  have hint : ∫ x in {x | dirLoss S u x = β}, famDens S ν η x ∂ν =
      faceMass S ν η u β / famZ S ν η := by
    unfold faceMass famDens
    rw [integral_div]
  rw [hint]
  exact div_pos (faceMass_pos hS ν η u β hp) (famZ_pos hS ν η)

variable (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hpoly hcharged

omit [Nonempty V] in
/-- The projection density of a response on the exposing face is carried by the face fibre. -/
theorem setIntegral_projDens_faceFibre (hV : ∀ v ∈ V, dotJ u v ≤ β) {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (hMβ : dotJ u M = β) :
    (∫ x in {x | dirLoss S u x = β}, projDens hS ν M x ∂ν = 1) ∧
      ∫ x in {x | dirLoss S u x = β}ᶜ, projDens hS ν M x ∂ν = 0 := by
  have hfin := genRate_ne_top_of_mem_convexHull_vertices hS ν V hcharged hM
  have hF := measurableSet_faceFibre hS u β
  have hc : ∫ x in {x | dirLoss S u x = β}ᶜ, projDens hS ν M x ∂ν = 0 := by
    have h := responseProjection_compl_faceFibre_eq_zero hS ν V hpoly hcharged hV hM hMβ
    rw [responseProjection_eq_withDensity_projDens hS ν hfin] at h
    have := measureReal_withDensity_ofReal ν (projDens_nonneg hS ν M) (integrable_projDens hS ν M)
      hF.compl
    rw [measureReal_def, h, ENNReal.toReal_zero] at this
    exact this.symm
  refine ⟨?_, hc⟩
  have htot : ∫ x, projDens hS ν M x ∂ν = 1 := by
    have := integral_eq_one_of_isProbabilityMeasure_withDensity ν (projDens_nonneg hS ν M)
      (integrable_projDens hS ν M) (by
        rw [← responseProjection_eq_withDensity_projDens hS ν hfin]
        exact (responseProjection_spec hS ν hfin).1)
    exact this
  rw [← integral_add_compl₀ hF.nullMeasurableSet (integrable_projDens hS ν M), hc, add_zero] at htot
  exact htot

/-- **The face-conditional family laws converge in `L¹` to the projection** when the means do. -/
theorem tendsto_integral_abs_faceDens_sub (hV : ∀ v ∈ V, dotJ u v ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (hMβ : dotJ u M = β) {η : ℕ → J → ℝ}
    (hlim : Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η n)) atTop
      (𝓝 M)) :
    Tendsto (fun n ↦ ∫ x, |faceDens S ν (η n) u β x - projDens hS ν M x| ∂ν) atTop (𝓝 0) := by
  obtain ⟨hfA, hfAc⟩ := setIntegral_projDens_faceFibre hS ν u β V hpoly hcharged hV hM hMβ
  have hF := measurableSet_faceFibre hS u β
  refine squeeze_zero' (Eventually.of_forall fun n ↦ integral_nonneg fun x ↦ abs_nonneg _)
    (Eventually.of_forall fun n ↦ ?_)
    (by simpa using (tendsto_integral_abs_famDens_sub hS ν V hpoly hcharged hM hlim).const_mul 2)
  have h := integral_abs_indicator_div_sub_le ν (integrable_projDens hS ν M)
    (integrable_famDens hS ν (η n)) (projDens_nonneg hS ν M) (famDens_nonneg hS ν (η n)) hF hfA
    hfAc rfl (integral_famDens_faceFibre_pos hS ν u β hp (η n))
  refine le_trans (le_of_eq ?_) h
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by
    beta_reduce
    rw [faceDens_eq_indicator_famDens_div hS ν u β])

/-- **The face-conditional means converge to `M`** when the means of the family laws do. -/
theorem tendsto_meanMap_faceMeasure_of_tendsto_meanMap (hV : ∀ v ∈ V, dotJ u v ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) (hMβ : dotJ u M = β) {η : ℕ → J → ℝ}
    (hlim : Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η n)) atTop
      (𝓝 M)) :
    Tendsto (fun n ↦ meanMap (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
      (fun _ ↦ (0 : ℝ)) S 1 (η n)) atTop (𝓝 M) := by
  have hfin := genRate_ne_top_of_mem_convexHull_vertices hS ν V hcharged hM
  have hF0 : ν {x | dirLoss S u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have hPF := isProbabilityMeasure_faceMeasure ν hF0
  have hL1 := tendsto_integral_abs_faceDens_sub hS ν u β V hpoly hcharged hV hp hM hMβ hlim
  refine tendsto_pi_nhds.2 fun j ↦ ?_
  obtain ⟨-, B, hB⟩ := hS j
  have hcoord : ∀ n, meanMap (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
      (fun _ ↦ (0 : ℝ)) S 1 (η n) j = ∫ x, S j x * faceDens S ν (η n) u β x ∂ν := fun n ↦ by
    rw [← mean_familyMeasure_one_zero hS (faceMeasure ν {x | dirLoss S u x = β}) (η n)]
    simp only
    rw [familyMeasure_faceMeasure_eq hS ν (η n) u β hp,
      integral_withDensity_ofReal ν (measurable_faceDens hS ν (η n) u β)
        (faceDens_nonneg ν (η n) u β)]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
  have hMj : M j = ∫ x, S j x * projDens hS ν M x ∂ν :=
    (integral_stat_mul_projDens hS ν hfin j).symm
  simp only [hcoord]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _)
    (Eventually.of_forall fun n ↦ ?_) (by simpa using hL1.const_mul B)
  have hbound : ∀ᵐ x ∂ν, ‖S j x‖ ≤ B := Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs]
    exact hB x
  have h1 : Integrable (fun x ↦ S j x * faceDens S ν (η n) u β x) ν :=
    (integrable_faceDens hS ν (η n) u β).bdd_mul (hS j).1.aestronglyMeasurable hbound
  have h2 : Integrable (fun x ↦ S j x * projDens hS ν M x) ν :=
    (integrable_projDens hS ν M).bdd_mul (hS j).1.aestronglyMeasurable hbound
  have h3 : Integrable (fun x ↦ |faceDens S ν (η n) u β x - projDens hS ν M x|) ν :=
    ((integrable_faceDens hS ν (η n) u β).sub (integrable_projDens hS ν M)).abs
  rw [Real.norm_eq_abs, hMj, ← integral_sub h1 h2]
  refine abs_integral_le_integral_abs.trans ?_
  rw [← integral_const_mul]
  refine integral_mono (h1.sub h2).abs (h3.const_mul B) fun x ↦ ?_
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)

end Face

end Laplace.Multi
