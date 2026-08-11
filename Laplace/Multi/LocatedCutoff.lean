/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.TranslationBridge
import Laplace.Multi.CutoffRemoval

/-!
# Located cutoff removal

The centred `superPoly_moment_of_ccData` upgrades compactly-supported
test data to polynomial-growth observables for ONE observable shared
by both packages. For the located composition (two losses with minima
at `p₁` and `p₂`) the coordinate observables differ per side after
centring, so a located analogue is needed. This file proves it: from
superPoly agreement of the PHYSICAL moment families (the
`regionMomentT` of the actual translated losses over the translated
regions, from `TranslationBridge`) over smooth compactly supported
tests in a common actual region `V` containing balls around BOTH
centres, the located moment families of every smooth
polynomial-growth observable agree beyond all orders
(`superPoly_locatedMoment_of_ccData`).

The cutoff is a double bump `χ = 1 - (1 - f₁)(1 - f₂)`: smooth,
`[0,1]`-valued, equal to `1` near each centre, supported in `V`. Each
package's cutoff tail is handled by `posteriorMoment_cutoff_tail` in
its own centred coordinates; the middle term is the data premise
transported by the translation bridge (eventually in `t`, which is
all `SuperPoly` needs).
-/

open Real MeasureTheory Filter Topology Asymptotics Metric
open scoped ContDiff

namespace Laplace

/-- `SuperPoly` transports across eventual equality at `atTop`. -/
theorem SuperPoly.congr {f g : ℝ → ℝ} (hf : SuperPoly f)
    (h : f =ᶠ[atTop] g) : SuperPoly g :=
  fun N ↦ (hf N).congr' h (Filter.EventuallyEq.refl _ _)

end Laplace

namespace Laplace.Multi

variable {d : ℕ}

/-! ## Translation preservation of polynomial growth -/

/-- Polynomial growth is preserved by translation of the argument. -/
theorem HasPolynomialGrowth.comp_const_add {P : EuclidD d → ℝ}
    (hP : HasPolynomialGrowth P) (p : EuclidD d) :
    HasPolynomialGrowth fun y ↦ P (p + y) := by
  obtain ⟨C, n, hC, h⟩ := hP
  refine ⟨C * (1 + 2 ^ n * ‖p‖ ^ n + 2 ^ n), n, by positivity,
    fun y ↦ ?_⟩
  have hpn : (0 : ℝ) ≤ ‖p‖ ^ n := by positivity
  have hyn : (0 : ℝ) ≤ ‖y‖ ^ n := by positivity
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hnorm : ‖p + y‖ ^ n ≤ 2 ^ n * ‖p‖ ^ n + 2 ^ n * ‖y‖ ^ n := by
    have hab : ‖p + y‖ ≤ 2 * max ‖p‖ ‖y‖ := by
      refine (norm_add_le p y).trans ?_
      rcases le_total ‖p‖ ‖y‖ with hle | hle
      · rw [max_eq_right hle]; linarith
      · rw [max_eq_left hle]; linarith
    have hpow : ‖p + y‖ ^ n ≤ (2 * max ‖p‖ ‖y‖) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) hab n
    have hmaxpow : (max ‖p‖ ‖y‖) ^ n ≤ ‖p‖ ^ n + ‖y‖ ^ n := by
      rcases max_cases ‖p‖ ‖y‖ with ⟨hm, _⟩ | ⟨hm, _⟩ <;>
        rw [hm] <;> linarith
    calc ‖p + y‖ ^ n ≤ (2 * max ‖p‖ ‖y‖) ^ n := hpow
      _ = 2 ^ n * (max ‖p‖ ‖y‖) ^ n := by rw [mul_pow]
      _ ≤ 2 ^ n * (‖p‖ ^ n + ‖y‖ ^ n) :=
          mul_le_mul_of_nonneg_left hmaxpow h2n.le
      _ = 2 ^ n * ‖p‖ ^ n + 2 ^ n * ‖y‖ ^ n := by ring
  calc |P (p + y)| ≤ C * (1 + ‖p + y‖ ^ n) := h _
    _ ≤ C * (1 + (2 ^ n * ‖p‖ ^ n + 2 ^ n * ‖y‖ ^ n)) :=
        mul_le_mul_of_nonneg_left (by linarith) hC
    _ ≤ C * (1 + 2 ^ n * ‖p‖ ^ n + 2 ^ n) * (1 + ‖y‖ ^ n) := by
        nlinarith [mul_nonneg hC hpn, mul_nonneg hC hyn,
          mul_nonneg (mul_nonneg hC h2n.le) hpn,
          mul_nonneg (mul_nonneg hC h2n.le) hyn,
          mul_nonneg (mul_nonneg (mul_nonneg hC h2n.le) hpn) hyn]

/-! ## The located cutoff-removal theorem -/

variable {L₁ L₂ : EuclidD d → ℝ}
  {H₁ H₂ : Matrix (Fin d) (Fin d) ℝ}

open LocalLaplaceDomain in
/-- **Located cutoff removal**: superPoly agreement of the physical
moment families of two located losses, over smooth compactly
supported tests in a common actual region containing balls around
both centres, upgrades to superPoly agreement of the located moment
families of every smooth polynomial-growth observable. -/
theorem superPoly_locatedMoment_of_ccData
    (A : LocalLaplaceDomain L₁ H₁) (B : LocalLaplaceDomain L₂ H₂)
    (p₁ p₂ : EuclidD d) {V : Set (EuclidD d)} {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hb₁ : Metric.ball p₁ r₁ ⊆ V) (hb₂ : Metric.ball p₂ r₂ ⊆ V)
    (hdata : ∀ φ : EuclidD d → ℝ, ContDiff ℝ ∞ φ →
      HasCompactSupport φ → tsupport φ ⊆ V →
      Laplace.SuperPoly (fun t : ℝ ↦
        regionMomentT (fun w ↦ L₁ (w - p₁))
          (translatedRegion p₁ A.U) φ t -
        regionMomentT (fun w ↦ L₂ (w - p₂))
          (translatedRegion p₂ B.U) φ t))
    {P : EuclidD d → ℝ} (hP_smooth : ContDiff ℝ ∞ P)
    (hP_growth : HasPolynomialGrowth P) :
    Laplace.SuperPoly (fun t : ℝ ↦
      A.locatedMomentT p₁ P t - B.locatedMomentT p₂ P t) := by
  -- the double bump
  set f₁ : ContDiffBump p₁ :=
    ⟨r₁ / 2, 3 * r₁ / 4, by linarith, by linarith⟩ with hf₁_def
  set f₂ : ContDiffBump p₂ :=
    ⟨r₂ / 2, 3 * r₂ / 4, by linarith, by linarith⟩ with hf₂_def
  set χ : EuclidD d → ℝ :=
    fun w ↦ 1 - (1 - f₁ w) * (1 - f₂ w) with hχ_def
  have hχ_smooth : ContDiff ℝ ∞ χ :=
    contDiff_const.sub ((contDiff_const.sub f₁.contDiff).mul
      (contDiff_const.sub f₂.contDiff))
  have hχ0 : ∀ w, 0 ≤ χ w := by
    intro w
    have ha : 1 - f₁ w ≤ 1 := by linarith [f₁.nonneg' w]
    have hb : 1 - f₂ w ≤ 1 := by linarith [f₂.nonneg' w]
    have hb0 : 0 ≤ 1 - f₂ w := by linarith [f₂.le_one (x := w)]
    have h1 : (1 - f₁ w) * (1 - f₂ w) ≤ 1 * 1 :=
      mul_le_mul ha hb hb0 zero_le_one
    simp only [hχ_def]
    nlinarith
  have hχ1 : ∀ w, χ w ≤ 1 := by
    intro w
    have h1 : 0 ≤ (1 - f₁ w) * (1 - f₂ w) :=
      mul_nonneg (by linarith [f₁.le_one (x := w)])
        (by linarith [f₂.le_one (x := w)])
    simp only [hχ_def]
    linarith
  have hχ_one₁ : ∀ w ∈ Metric.ball p₁ (r₁ / 2), χ w = 1 := by
    intro w hw
    have h1 : f₁ w = 1 :=
      f₁.one_of_mem_closedBall (Metric.ball_subset_closedBall hw)
    simp [hχ_def, h1]
  have hχ_one₂ : ∀ w ∈ Metric.ball p₂ (r₂ / 2), χ w = 1 := by
    intro w hw
    have h2 : f₂ w = 1 :=
      f₂.one_of_mem_closedBall (Metric.ball_subset_closedBall hw)
    simp [hχ_def, h2]
  have hsub : Function.support χ ⊆
      Metric.closedBall p₁ (3 * r₁ / 4) ∪
        Metric.closedBall p₂ (3 * r₂ / 4) := by
    intro w hw
    by_contra hout
    simp only [Set.mem_union, not_or] at hout
    obtain ⟨h1, h2⟩ := hout
    have hf1 : f₁ w = 0 := by
      have hns : w ∉ Function.support f₁ := by
        rw [f₁.support_eq]
        exact fun hmem ↦ h1 (Metric.ball_subset_closedBall hmem)
      simpa [Function.mem_support, not_not] using hns
    have hf2 : f₂ w = 0 := by
      have hns : w ∉ Function.support f₂ := by
        rw [f₂.support_eq]
        exact fun hmem ↦ h2 (Metric.ball_subset_closedBall hmem)
      simpa [Function.mem_support, not_not] using hns
    exact hw (by simp [hχ_def, hf1, hf2])
  have hcb_closed : IsClosed
      (Metric.closedBall p₁ (3 * r₁ / 4) ∪
        Metric.closedBall p₂ (3 * r₂ / 4)) :=
    Metric.isClosed_closedBall.union Metric.isClosed_closedBall
  have hχ_supp : tsupport χ ⊆ V := by
    refine (closure_minimal hsub hcb_closed).trans ?_
    refine Set.union_subset ?_ ?_
    · exact (Metric.closedBall_subset_ball (by linarith)).trans hb₁
    · exact (Metric.closedBall_subset_ball (by linarith)).trans hb₂
  have hχ_cs : HasCompactSupport χ :=
    HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall p₁ (3 * r₁ / 4)).union
        (isCompact_closedBall p₂ (3 * r₂ / 4))) hsub
  -- the data at the cut observable
  have hφ_smooth : ContDiff ℝ ∞ fun w ↦ P w * χ w :=
    hP_smooth.mul hχ_smooth
  have hφ_cs : HasCompactSupport fun w ↦ P w * χ w :=
    hχ_cs.mul_left
  have hφ_supp : tsupport (fun w ↦ P w * χ w) ⊆ V := by
    refine (closure_minimal ?_ (isClosed_tsupport χ)).trans hχ_supp
    intro w hw
    have : χ w ≠ 0 := by
      intro h0
      exact (Function.mem_support.mp hw) (by rw [h0, mul_zero])
    exact subset_closure (Function.mem_support.mpr this)
  have hT2phys := hdata (fun w ↦ P w * χ w) hφ_smooth hφ_cs hφ_supp
  -- convert the physical middle term to located moments
  have hT2 : Laplace.SuperPoly (fun t : ℝ ↦
      A.locatedMomentT p₁ (fun w ↦ P w * χ w) t -
        B.locatedMomentT p₂ (fun w ↦ P w * χ w) t) := by
    refine hT2phys.congr ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [A.regionMomentT_translate_eq_locatedMomentT p₁ _ ht,
      B.regionMomentT_translate_eq_locatedMomentT p₂ _ ht]
  -- per-package cutoff tails, in centred coordinates
  have hT1 : Laplace.SuperPoly (fun t : ℝ ↦
      A.posteriorMomentT (fun y ↦ P (p₁ + y)) t -
        A.posteriorMomentT
          (fun y ↦ P (p₁ + y) * χ (p₁ + y)) t) := by
    refine A.posteriorMoment_cutoff_tail
      (hP_smooth.continuous.comp (continuous_const.add continuous_id))
      (hP_growth.comp_const_add p₁)
      (hχ_smooth.continuous.comp (continuous_const.add continuous_id))
      (fun y ↦ hχ0 _) (fun y ↦ hχ1 _)
      (show (0:ℝ) < r₁ / 2 by linarith) ?_
    intro y hy
    refine hχ_one₁ (p₁ + y) ?_
    rw [Metric.mem_ball, dist_self_add_left] at *
    simpa using hy
  have hT3 : Laplace.SuperPoly (fun t : ℝ ↦
      B.posteriorMomentT (fun y ↦ P (p₂ + y)) t -
        B.posteriorMomentT
          (fun y ↦ P (p₂ + y) * χ (p₂ + y)) t) := by
    refine B.posteriorMoment_cutoff_tail
      (hP_smooth.continuous.comp (continuous_const.add continuous_id))
      (hP_growth.comp_const_add p₂)
      (hχ_smooth.continuous.comp (continuous_const.add continuous_id))
      (fun y ↦ hχ0 _) (fun y ↦ hχ1 _)
      (show (0:ℝ) < r₂ / 2 by linarith) ?_
    intro y hy
    refine hχ_one₂ (p₂ + y) ?_
    rw [Metric.mem_ball, dist_self_add_left] at *
    simpa using hy
  -- telescope
  have hcomb := (hT1.add hT2).sub hT3
  refine hcomb.congr (Filter.Eventually.of_forall fun t ↦ ?_)
  beta_reduce
  unfold LocalLaplaceDomain.locatedMomentT
  beta_reduce
  ring

end Laplace.Multi
