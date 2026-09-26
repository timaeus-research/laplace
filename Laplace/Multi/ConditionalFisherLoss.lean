/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CurvatureSplit

/-!
# The conditional Fisher-loss identity

Along the bridge `D_s = (1 + s(d − 1))ν` with conditional density `a = E_ν[d | σ(S)]`, the
difference of the full-simplex speed `k_d(s)` and the observable-simplex speed `k_a(s)` is an exact
conditional variance:

`k_d(s) − k_a(s) = ∫ (d − a)² / (d_s · a_s²) dν = E_{D_s}[(h_s − E_{D_s}[h_s | σ(S)])²]`,

where `h_s = (d − 1)/d_s` is the mixture score and `E_{D_s}[h_s | σ(S)] = (a − 1)/a_s`. The proof is
the tangent-line identity of the convex kernel `y ↦ y²/(1 + wy)` at the conditional value,
integrated
against the vanishing conditional residual `∫ g(a)(d − a) dν = 0` for bounded `σ(S)`-measurable
`g(a)`. Consequently `k_a ≤ k_d` pointwise, the fibre information `L_s` is a weighted integral of
a nonnegative conditional variance, and a measurable conditional density with the pointwise
bounds always exists.
-/

open MeasureTheory Filter Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Kernel

/-- The slope of the mixture kernel `y ↦ y²/(1 + wy)` at `y = z`. -/
noncomputable def kernelSlope (w z : ℝ) : ℝ := z * (w * z + 2) / (w * z + 1) ^ 2

/-- **Tangent-line identity for the mixture kernel**: the excess of the convex kernel over its
tangent at `z` is the square of the increment weighted by the two denominators. -/
theorem klKernel_sub_tangent {w y z : ℝ} (hy : 0 < 1 + w * (y - 1)) (hz : 0 < 1 + w * (z - 1)) :
    klKernel y w - klKernel z w - kernelSlope w (z - 1) * (y - z) =
      (y - z) ^ 2 / ((1 + w * (y - 1)) * (1 + w * (z - 1)) ^ 2) := by
  unfold klKernel kernelSlope
  have hA : 1 + w * (y - 1) ≠ 0 := hy.ne'
  have hB : 1 + w * (z - 1) ≠ 0 := hz.ne'
  have hB' : (w * (z - 1) + 1) ^ 2 ≠ 0 := pow_ne_zero 2 (by rw [add_comm]; exact hB)
  rw [div_mul_eq_mul_div, div_sub_div _ _ hA hB, div_sub_div _ _ (mul_ne_zero hA hB) hB',
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hA hB) hB') (mul_ne_zero hA (pow_ne_zero 2 hB))]
  ring

theorem abs_kernelSlope_le {w z Z m : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hZ : |z| ≤ Z) (hm : 0 < m)
    (hmz : m ≤ w * z + 1) : |kernelSlope w z| ≤ Z * (Z + 2) / m ^ 2 := by
  unfold kernelSlope
  have hZ0 : 0 ≤ Z := (abs_nonneg z).trans hZ
  rw [abs_div, abs_mul, abs_of_pos (pow_pos (lt_of_lt_of_le hm hmz) 2)]
  have h2 : |w * z + 2| ≤ Z + 2 := by
    calc |w * z + 2| ≤ |w * z| + |2| := abs_add_le _ _
      _ = w * |z| + 2 := by rw [abs_mul, abs_of_nonneg hw0, abs_two]
      _ ≤ Z + 2 := by nlinarith [abs_nonneg z]
  exact div_le_div₀ (by positivity) (mul_le_mul hZ h2 (abs_nonneg _) hZ0) (by positivity)
    (pow_le_pow_left₀ hm.le hmz 2)

end Kernel

section Loss

variable {X : Type*} [MeasurableSpace X] {J : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
  (ν : Measure X) [IsProbabilityMeasure ν]
  {d : X → ℝ} (hd : Measurable d) {c C : ℝ} (hc0 : 0 < c) (hc : ∀ x, c ≤ d x) (hC : ∀ x, d x ≤ C)
  {a : X → ℝ} (ham : Measurable[statSigma S] a) (hac : ∀ x, c ≤ a x) (haC : ∀ x, a x ≤ C)
  (ha : a =ᵐ[ν] ν[d | statSigma S])
include hS hd hc0 hc hC ham hac haC ha

omit hc0 ham hac haC ha in
/-- A `σ(S)`-measurable conditional density with the pointwise bounds of `d` exists. -/
theorem exists_condDens [Nonempty X] :
    ∃ a : X → ℝ, Measurable[statSigma S] a ∧ (∀ x, c ≤ a x) ∧ (∀ x, a x ≤ C) ∧
      a =ᵐ[ν] ν[d | statSigma S] := by
  have hm := statSigma_le hS
  have hdi : Integrable d ν := integrable_of_bounds ν hd hc hC
  have hcC : c ≤ C := (hc (Classical.arbitrary X)).trans (hC (Classical.arbitrary X))
  refine ⟨fun x ↦ max c (min C ((ν[d | statSigma S]) x)), ?_, fun x ↦ le_max_left _ _,
    fun x ↦ max_le hcC (min_le_left _ _), ?_⟩
  · exact measurable_const.max (measurable_const.min stronglyMeasurable_condExp.measurable)
  · have h1 : ν[fun _ ↦ c | statSigma S] ≤ᵐ[ν] ν[d | statSigma S] :=
      condExp_mono (integrable_const c) hdi (Eventually.of_forall hc)
    have h2 : ν[d | statSigma S] ≤ᵐ[ν] ν[fun _ ↦ C | statSigma S] :=
      condExp_mono hdi (integrable_const C) (Eventually.of_forall hC)
    rw [condExp_const hm] at h1 h2
    filter_upwards [h1, h2] with x hx1 hx2
    rw [min_eq_right hx2, max_eq_right hx1]

omit hc0 ham hac haC ha in
/-- The conditional residual against a bounded `σ(S)`-measurable weight vanishes. -/
theorem integral_mul_sub_condDens {g : X → ℝ} (hg : Measurable[statSigma S] g) {K : ℝ}
    (hgK : ∀ x, |g x| ≤ K) {a : X → ℝ} (ham : Measurable[statSigma S] a) (hac : ∀ x, c ≤ a x)
    (haC : ∀ x, a x ≤ C) (ha : a =ᵐ[ν] ν[d | statSigma S]) :
    ∫ x, g x * (d x - a x) ∂ν = 0 := by
  have hm := statSigma_le hS
  have hgm : Measurable g := hg.mono hm le_rfl
  have ham' : Measurable a := ham.mono hm le_rfl
  have hgi : Integrable g ν := by
    refine Integrable.of_bound hgm.aestronglyMeasurable K (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs]
    exact hgK x
  have hdi := integrable_of_bounds ν hd hc hC
  have hai := integrable_of_bounds ν ham' hac haC
  have hgd : Integrable (fun x ↦ g x * d x) ν :=
    hdi.bdd_mul (c := K) hgm.aestronglyMeasurable (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]; exact hgK x)
  have hga : Integrable (fun x ↦ g x * a x) ν :=
    hai.bdd_mul (c := K) hgm.aestronglyMeasurable (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]; exact hgK x)
  have e : (fun x ↦ g x * (d x - a x)) = fun x ↦ g x * d x - g x * a x := by
    funext x
    ring
  rw [e, integral_sub hgd hga, sub_eq_zero]
  have hdB : Bdd d := ⟨hd, max (|c|) (|C|), fun x ↦ by
    rw [abs_le]
    constructor
    · linarith [hc x, neg_abs_le c, le_max_left (|c|) (|C|)]
    · linarith [hC x, le_abs_self C, le_max_right (|c|) (|C|)]⟩
  rw [integral_mul_condExp_statSigma hS ν hdB (hg.stronglyMeasurable) hgK]
  refine integral_congr_ae ?_
  filter_upwards [ha] with x hx
  rw [hx]

/-- **The conditional Fisher-loss identity**: the full-simplex speed exceeds the observable-simplex
speed by the conditional variance of the mixture score,
`k_d(w) − k_a(w) = ∫ (d − a)² / (d_w · a_w²) dν` with `d_w = 1 + w(d−1)`, `a_w = 1 + w(a−1)`. -/
theorem mixSpeed_sub_mixSpeed_condDens {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    mixSpeed ν d w - mixSpeed ν a w =
      ∫ x, (d x - a x) ^ 2 / ((1 + w * (d x - 1)) * (1 + w * (a x - 1)) ^ 2) ∂ν := by
  have hm := statSigma_le hS
  have ham' : Measurable a := ham.mono hm le_rfl
  have hdpos : ∀ x, 0 < 1 + w * (d x - 1) := fun x ↦
    klKernel_denom_pos (lt_of_lt_of_le hc0 (hc x)) hw0 hw1
  have hapos : ∀ x, 0 < 1 + w * (a x - 1) := fun x ↦
    klKernel_denom_pos (lt_of_lt_of_le hc0 (hac x)) hw0 hw1
  have hI : ∀ {r : X → ℝ}, Measurable r → (∀ x, c ≤ r x) → (∀ x, r x ≤ C) →
      Integrable (fun x ↦ klKernel (r x) w) ν := fun {r} hr hcr hCr ↦ by
    refine Integrable.of_bound ?_ ((C + 1) ^ 2 / min 1 c) (Eventually.of_forall fun x ↦ ?_)
    · have h : Measurable fun x ↦ klKernel (r x) w := by
        unfold klKernel
        exact ((hr.sub measurable_const).pow_const 2).div
          (measurable_const.add (measurable_const.mul (hr.sub measurable_const)))
      exact h.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact klKernel_le hc0 hcr hCr w hw0 hw1 x
      · unfold klKernel
        exact div_nonneg (sq_nonneg _) (klKernel_denom_pos (lt_of_lt_of_le hc0 (hcr x)) hw0 hw1).le
  have hslope : ∀ x, |kernelSlope w (a x - 1)| ≤
      (max (|c - 1|) (|C - 1|)) * (max (|c - 1|) (|C - 1|) + 2) / (min 1 c) ^ 2 := fun x ↦ by
    refine abs_kernelSlope_le hw0 hw1 ?_ (lt_min one_pos hc0) ?_
    · rw [abs_le]
      constructor
      · linarith [hac x, neg_abs_le (c - 1), le_max_left (|c - 1|) (|C - 1|)]
      · linarith [haC x, le_abs_self (C - 1), le_max_right (|c - 1|) (|C - 1|)]
    · have := (bridgeDens_bounds hac haC hw0 hw1 x).1
      unfold bridgeDens at this
      linarith
  have hg : Measurable[statSigma S] fun x ↦ kernelSlope w (a x - 1) := by
    unfold kernelSlope
    exact (((ham.sub measurable_const).mul ((measurable_const.mul (ham.sub measurable_const)).add
      measurable_const)).div (((measurable_const.mul (ham.sub measurable_const)).add
      measurable_const).pow_const 2))
  have h0 := integral_mul_sub_condDens hS ν hd hc hC hg hslope ham hac haC ha
  have e : ∀ x, klKernel (d x) w - klKernel (a x) w =
      kernelSlope w (a x - 1) * (d x - a x) +
        (d x - a x) ^ 2 / ((1 + w * (d x - 1)) * (1 + w * (a x - 1)) ^ 2) := fun x ↦ by
    rw [← klKernel_sub_tangent (hdpos x) (hapos x)]
    ring
  have hsub : Integrable (fun x ↦ klKernel (d x) w - klKernel (a x) w) ν :=
    (hI hd hc hC).sub (hI ham' hac haC)
  have hlin : Integrable (fun x ↦ kernelSlope w (a x - 1) * (d x - a x)) ν := by
    refine ((integrable_of_bounds ν hd hc hC).sub (integrable_of_bounds ν ham' hac haC)).bdd_mul
      (c := (max (|c - 1|) (|C - 1|)) * (max (|c - 1|) (|C - 1|) + 2) / (min 1 c) ^ 2)
      (hg.mono hm le_rfl).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs]
    exact hslope x
  have hquad : Integrable
      (fun x ↦ (d x - a x) ^ 2 / ((1 + w * (d x - 1)) * (1 + w * (a x - 1)) ^ 2)) ν := by
    have := hsub.congr (Eventually.of_forall e)
    have h := this.sub hlin
    refine h.congr (Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.sub_apply]
    ring
  unfold mixSpeed
  rw [← integral_sub (hI hd hc hC) (hI ham' hac haC), integral_congr_ae (Eventually.of_forall e),
    integral_add hlin hquad, h0, zero_add]

/-- The observable-simplex speed is bounded by the full-simplex speed. -/
theorem mixSpeed_condDens_le {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    mixSpeed ν a w ≤ mixSpeed ν d w := by
  have h := mixSpeed_sub_mixSpeed_condDens hS ν hd hc0 hc hC ham hac haC ha hw0 hw1
  have hdpos : ∀ x, 0 < 1 + w * (d x - 1) := fun x ↦
    klKernel_denom_pos (lt_of_lt_of_le hc0 (hc x)) hw0 hw1
  have hapos : ∀ x, 0 < 1 + w * (a x - 1) := fun x ↦
    klKernel_denom_pos (lt_of_lt_of_le hc0 (hac x)) hw0 hw1
  have : 0 ≤ mixSpeed ν d w - mixSpeed ν a w := by
    rw [h]
    exact integral_nonneg fun x ↦ div_nonneg (sq_nonneg _)
      (mul_nonneg (hdpos x).le (sq_nonneg _))
  linarith

omit hS ham hac haC ha in
/-- **The fibre information is accumulated conditional variance of the mixture score**:
`L_s = ∫₀ˢ (s − w) ∫ (d − a)²/(d_w a_w²) dν dw`. -/
theorem fibre_eq_integral_condVar {Jf : Type*} {S' : Jf → X → ℝ} (hS' : ∀ j, Bdd (S' j))
    (hnorm : ∫ x, d x ∂ν = 1)
    {a' : X → ℝ} (ham' : Measurable[statSigma S'] a') (hac' : ∀ x, c ≤ a' x) (haC' : ∀ x, a' x ≤ C)
    (ha' : a' =ᵐ[ν] ν[d | statSigma S']) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (klDiv (densLaw ν (bridgeDens d s))
        (statisticLift ν (densLaw ν (bridgeDens d s)) (statPoint S'))).toReal =
      ∫ w in (0 : ℝ)..s, (s - w) *
        ∫ x, (d x - a' x) ^ 2 / ((1 + w * (d x - 1)) * (1 + w * (a' x - 1)) ^ 2) ∂ν := by
  rw [fibre_eq_integral_curvature hS' ν hd hc0 hc hC hnorm (ham'.mono (statSigma_le hS') le_rfl)
    hac' haC' ha' hs0 hs1]
  refine intervalIntegral.integral_congr fun w hw ↦ ?_
  rw [uIcc_of_le hs0] at hw
  rw [mixSpeed_sub_mixSpeed_condDens hS' ν hd hc0 hc hC ham' hac' haC' ha' hw.1 (hw.2.trans hs1)]

end Loss

end Laplace.Multi
