/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.LiftDensity
import Laplace.Multi.InformationDistance

/-!
# The whole decomposition is accumulated curvature

For a data law `D = dν` with bounded positive density, the bridge `D_s = (1 + s(d−1))ν` has
response `M_s` on the atlas path, and with `a` a bounded version of `E_ν[d | σ(S)]`, the lifted
bridge is `(1 + s(a−1))ν`. Writing `k_d(w) = ∫ (d−1)²/(1+w(d−1)) dν` for the full-simplex speed,
`k_a` for the observable speed and `κ` for the atlas curvature,

  `𝓘(M_s) = ∫₀ˢ (s−w) κ(w) dw`, `L_s = ∫₀ˢ (s−w)(k_d(w) − k_a(w)) dw`,
  `R_s = ∫₀ˢ (s−w)(k_a(w) − κ(w)) dw`
                         (`fibre_eq_integral_curvature`, `marginal_eq_integral_curvature`).

The three terms of `KL(D_s‖ν) = 𝓘_s + R_s + L_s` are the three accumulated curvature defects between
the full-simplex path, the observable path and the atlas path: globally reconstruction separates
information, locally it separates scores, and along the bridge the separations accumulate as
curvature.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Bridge

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- The density of the bridge at time `s`. -/
noncomputable def bridgeDens (d : X → ℝ) (s : ℝ) (x : X) : ℝ := 1 + s * (d x - 1)

omit [IsProbabilityMeasure ν] in
theorem klKernel_bridge (r s u : ℝ) :
    klKernel (1 + s * (r - 1)) u = s ^ 2 * klKernel r (u * s) := by
  unfold klKernel
  rw [← mul_div_assoc]
  congr 1 <;> ring

omit [IsProbabilityMeasure ν] in
theorem mixSpeed_bridge (d : X → ℝ) (s u : ℝ) :
    mixSpeed ν (bridgeDens d s) u = s ^ 2 * mixSpeed ν d (u * s) := by
  unfold mixSpeed
  simp_rw [bridgeDens, klKernel_bridge]
  rw [integral_const_mul]

variable {d : X → ℝ} (hd : Measurable d) {c C : ℝ} (hc0 : 0 < c) (hc : ∀ x, c ≤ d x)
  (hC : ∀ x, d x ≤ C)
include hd hc0 hc hC

omit [MeasurableSpace X] hd hc0 in
theorem bridgeDens_bounds {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : X) :
    min 1 c ≤ bridgeDens d s x ∧ bridgeDens d s x ≤ max 1 C := by
  have h1 := hc x
  have h2 := hC x
  unfold bridgeDens
  constructor
  · rcases le_or_gt 1 (d x) with h | h
    · exact (min_le_left _ _).trans (by nlinarith)
    · exact (min_le_right _ _).trans (by nlinarith)
  · rcases le_or_gt 1 (d x) with h | h
    · exact (by nlinarith : 1 + s * (d x - 1) ≤ C).trans (le_max_right _ _)
    · exact (by nlinarith : 1 + s * (d x - 1) ≤ 1).trans (le_max_left _ _)

omit hc0 hc hC in
theorem measurable_bridgeDens (s : ℝ) : Measurable (bridgeDens d s) := by
  unfold bridgeDens
  fun_prop

/-- **The information of the bridge as accumulated full-simplex curvature**:
`KL(D_s ‖ ν) = ∫₀ˢ (s − w) k_d(w) dw`. -/
theorem toReal_klDiv_densLaw_bridge {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (klDiv (densLaw ν (bridgeDens d s)) ν).toReal =
      ∫ w in (0 : ℝ)..s, (s - w) * mixSpeed ν d w := by
  rw [toReal_klDiv_densLaw_eq_integral_mixSpeed ν (measurable_bridgeDens hd s)
    (lt_min one_pos hc0) (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1 x).1)
    (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1 x).2)]
  rcases eq_or_lt_of_le hs0 with rfl | hs
  · simp [mixSpeed_bridge]
  · have e : ∀ u, (1 - u) * mixSpeed ν (bridgeDens d s) u =
        s * ((s - s * u) * mixSpeed ν d (s * u)) := fun u ↦ by
      rw [mixSpeed_bridge, mul_comm u s]
      ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun w ↦ (s - w) * mixSpeed ν d w) hs.ne',
      mul_zero, mul_one, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]

omit hc0 in
/-- A bounded measurable function is integrable. -/
theorem integrable_of_bounds : Integrable d ν := by
  refine Integrable.of_bound hd.aestronglyMeasurable (max (|c|) (|C|))
    (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [hc x, neg_abs_le c, le_max_left (|c|) (|C|)]
  · linarith [hC x, le_abs_self C, le_max_right (|c|) (|C|)]

/-- The bridge law is a probability law. -/
theorem isProbabilityMeasure_densLaw_bridge (hnorm : ∫ x, d x ∂ν = 1) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : IsProbabilityMeasure (densLaw ν (bridgeDens d s)) := by
  refine ⟨?_⟩
  unfold densLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : Integrable (bridgeDens d s) ν :=
    integrable_of_bounds ν (measurable_bridgeDens hd s)
      (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1 x).1)
      (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1 x).2)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x ↦
    (lt_min one_pos hc0).le.trans (bridgeDens_bounds hc hC hs0 hs1 x).1)]
  have hdi := integrable_of_bounds ν hd hc hC
  have h1 : Integrable (fun x ↦ s * (d x - 1)) ν :=
    ((hdi.sub (integrable_const 1)).const_mul s).congr
      (Eventually.of_forall fun x ↦ by simp only [Pi.sub_apply])
  have e : ∫ x, bridgeDens d s x ∂ν = 1 := by
    unfold bridgeDens
    rw [integral_add (integrable_const 1) h1, integral_const, integral_const_mul,
      integral_sub hdi (integrable_const 1), integral_const, hnorm, probReal_univ]
    simp
  rw [e, ENNReal.ofReal_one]

omit [IsProbabilityMeasure ν] hC in
/-- Integrals against a bounded positive density law. -/
theorem integral_densLaw_of_bounds (f : X → ℝ) :
    ∫ x, f x ∂densLaw ν d = ∫ x, d x * f x ∂ν := by
  unfold densLaw
  rw [integral_withDensity_eq_integral_toReal_smul₀ hd.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [ENNReal.toReal_ofReal (hc0.le.trans (hc x)), smul_eq_mul]

/-- The response of the bridge law is the atlas point at time `s`. -/
theorem mean_densLaw_bridge {J : Type*} [Fintype J] {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (fun i ↦ ∫ x, S i x ∂densLaw ν (bridgeDens d s)) =
      atlasPath S ν (fun i ↦ ∫ x, S i x ∂densLaw ν d) s := by
  funext i
  have hSi := integrable_of_bdd_prob ν (hS i)
  have hSd : Integrable (fun x ↦ d x * S i x) ν := by
    refine Integrable.bdd_mul (c := max (|c|) (|C|)) hSi hd.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [hc x, neg_abs_le c, le_max_left (|c|) (|C|)]
    · linarith [hC x, le_abs_self C, le_max_right (|c|) (|C|)]
  have h2 : Integrable (fun x ↦ s * (d x * S i x - S i x)) ν :=
    ((hSd.sub hSi).const_mul s).congr (Eventually.of_forall fun x ↦ by simp only [Pi.sub_apply])
  rw [integral_densLaw_of_bounds ν (measurable_bridgeDens hd s) (lt_min one_pos hc0)
    (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1 x).1) (S i)]
  unfold atlasPath
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    integral_densLaw_of_bounds ν hd hc0 hc (S i), meanMap_zero_eq_mean ν]
  beta_reduce
  have e : (fun x ↦ bridgeDens d s x * S i x) =
      fun x ↦ S i x + s * (d x * S i x - S i x) := by
    funext x
    unfold bridgeDens
    ring
  rw [e, integral_add hSi h2, integral_const_mul, integral_sub hSd hSi]
  ring

omit hd hc0 hc hC in
/-- The information of a bounded positive density law is finite. -/
theorem klDiv_densLaw_ne_top {r : X → ℝ} (hr : Measurable r) {c' : ℝ} (hc0' : 0 < c')
    (hc' : ∀ x, c' ≤ r x) {C' : ℝ} (hC' : ∀ x, r x ≤ C') : klDiv (densLaw ν r) ν ≠ ⊤ := by
  have hfin := isFiniteMeasure_densLaw ν hC'
  unfold densLaw
  rw [klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous ν _)]
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := c') (b := C')).exists_bound_of_continuousOn
    continuous_klFun.continuousOn
  have hae : (fun x ↦ ENNReal.ofReal
      (klFun ((ν.withDensity fun x ↦ ENNReal.ofReal (r x)).rnDeriv ν x).toReal)) =ᵐ[ν]
      fun x ↦ ENNReal.ofReal (klFun (r x)) := by
    filter_upwards [Measure.rnDeriv_withDensity ν hr.ennreal_ofReal] with x hx
    rw [hx, ENNReal.toReal_ofReal (hc0'.le.trans (hc' x))]
  rw [lintegral_congr_ae hae]
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal B) ENNReal.ofReal_ne_top ?_
  calc ∫⁻ x, ENNReal.ofReal (klFun (r x)) ∂ν ≤ ∫⁻ _x, ENNReal.ofReal B ∂ν :=
        lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal
          ((le_abs_self _).trans (hB _ ⟨hc' x, hC' x⟩))
    _ = ENNReal.ofReal B := by simp

omit hc0 hc hC in
/-- The speed `w ↦ k_d(w)` is measurable. -/
theorem measurable_mixSpeed : Measurable (mixSpeed ν d) := by
  have h := (measurable_klKernel_uncurry hd).stronglyMeasurable.integral_prod_right' (ν := ν)
  exact h.measurable

omit hd in
/-- The speed is bounded on `[0,1]`. -/
theorem abs_mixSpeed_le {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    |mixSpeed ν d w| ≤ (C + 1) ^ 2 / min 1 c := by
  unfold mixSpeed
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (integrable_const ((C + 1) ^ 2 / min 1 c))
    (Eventually.of_forall fun x ↦ ?_)).trans ?_
  · have h0 : 0 ≤ klKernel (d x) w := by
      unfold klKernel
      exact div_nonneg (sq_nonneg _) (klKernel_denom_pos (lt_of_lt_of_le hc0 (hc x)) hw0 hw1).le
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact klKernel_le hc0 hc hC w hw0 hw1 x
  · rw [integral_const, probReal_univ, one_smul]

/-- The weighted speed is interval integrable on `[0, s]`. -/
theorem intervalIntegrable_sub_mul_mixSpeed {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IntervalIntegrable (fun w ↦ (s - w) * mixSpeed ν d w) volume 0 s := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs0]
  refine Integrable.of_bound ((measurable_const.sub measurable_id).mul
    (measurable_mixSpeed ν hd)).aestronglyMeasurable ((C + 1) ^ 2 / min 1 c) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun w hw ↦ ?_
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |s - w| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hw.1, hw.2]
  have h2 := abs_mixSpeed_le ν hc0 hc hC hw.1.le (hw.2.trans hs1)
  calc |s - w| * |mixSpeed ν d w| ≤ 1 * ((C + 1) ^ 2 / min 1 c) :=
        mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = (C + 1) ^ 2 / min 1 c := one_mul _

end Bridge

section Split

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {d : X → ℝ} (hd : Measurable d) {c C : ℝ} (hc0 : 0 < c) (hc : ∀ x, c ≤ d x) (hC : ∀ x, d x ≤ C)
  (hnorm : ∫ x, d x ∂ν = 1) {a : X → ℝ} (ham : Measurable a) (hac : ∀ x, c ≤ a x)
  (haC : ∀ x, a x ≤ C) (ha : a =ᵐ[ν] ν[d | statSigma S])
include hS hd hc0 hc hC hnorm ham hac haC ha

omit [Nonempty X] [Fintype J] [Nonempty J] ham hac haC in
/-- **The lift of the bridge is the bridge of the conditional density.** -/
theorem statisticLift_densLaw_bridge {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    statisticLift ν (densLaw ν (bridgeDens d s)) (statPoint S) = densLaw ν (bridgeDens a s) := by
  have hP := isProbabilityMeasure_densLaw_bridge ν hd hc0 hc hC hnorm hs0 hs1
  have hpm := measurable_bridgeDens hd s
  have hpi : Integrable (bridgeDens d s) ν :=
    integrable_of_bounds ν hpm (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1 x).1)
      (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1 x).2)
  have hp0 : 0 ≤ᵐ[ν] bridgeDens d s := Eventually.of_forall fun x ↦ by
    simp only [Pi.zero_apply]
    exact (lt_min one_pos hc0).le.trans (bridgeDens_bounds hc hC hs0 hs1 x).1
  unfold densLaw at hP ⊢
  rw [statisticLift_eq_withDensity_condExp hS ν hpm hpi hp0]
  refine withDensity_congr_ae ?_
  have hm := statSigma_le hS
  have hdi := integrable_of_bounds ν hd hc hC
  have e : bridgeDens d s = (fun _ ↦ (1 - s : ℝ)) + s • d := by
    funext x
    simp only [bridgeDens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  have h1 := condExp_add (m := statSigma S) (integrable_const (1 - s : ℝ)) (hdi.smul s)
  have h2 := condExp_smul (m := statSigma S) (μ := ν) s d
  filter_upwards [h1, h2, ha] with x hx1 hx2 hx3
  rw [hx1, Pi.add_apply, condExp_const hm, hx2, Pi.smul_apply, smul_eq_mul, ← hx3]
  congr 1
  simp only [bridgeDens]
  ring

omit [Nonempty X] [Fintype J] [Nonempty J] in
/-- **The fibre information is accumulated curvature defect between the full-simplex path and
the observable path**: `L_s = ∫₀ˢ (s − w) (k_d(w) − k_a(w)) dw`. -/
theorem fibre_eq_integral_curvature {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (klDiv (densLaw ν (bridgeDens d s))
        (statisticLift ν (densLaw ν (bridgeDens d s)) (statPoint S))).toReal =
      ∫ w in (0 : ℝ)..s, (s - w) * (mixSpeed ν d w - mixSpeed ν a w) := by
  have hP := isProbabilityMeasure_densLaw_bridge ν hd hc0 hc hC hnorm hs0 hs1
  have hDν : densLaw ν (bridgeDens d s) ≪ ν := withDensity_absolutelyContinuous ν _
  have hfin : klDiv (densLaw ν (bridgeDens d s)) ν ≠ ⊤ :=
    klDiv_densLaw_ne_top ν (measurable_bridgeDens hd s) (lt_min one_pos hc0)
      (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1 x).1)
      (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1 x).2)
  have h1 := klDiv_eq_klDiv_statisticLift_add_map ν (densLaw ν (bridgeDens d s)) (statPoint S)
    (measurable_statPoint hS) hDν hfin
  rw [← klDiv_statisticLift_eq_map ν _ (statPoint S) (measurable_statPoint hS) hDν] at h1
  have hne1 : klDiv (densLaw ν (bridgeDens d s))
      (statisticLift ν (densLaw ν (bridgeDens d s)) (statPoint S)) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at h1
    exact hfin h1
  have hne2 : klDiv (statisticLift ν (densLaw ν (bridgeDens d s)) (statPoint S)) ν ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at h1
    exact hfin h1
  have hL : (klDiv (densLaw ν (bridgeDens d s))
      (statisticLift ν (densLaw ν (bridgeDens d s)) (statPoint S))).toReal =
      (klDiv (densLaw ν (bridgeDens d s)) ν).toReal -
        (klDiv (statisticLift ν (densLaw ν (bridgeDens d s)) (statPoint S)) ν).toReal := by
    rw [h1, ENNReal.toReal_add hne1 hne2]
    ring
  rw [hL, statisticLift_densLaw_bridge hS ν hd hc0 hc hC hnorm ha hs0 hs1,
    toReal_klDiv_densLaw_bridge ν hd hc0 hc hC hs0 hs1,
    toReal_klDiv_densLaw_bridge ν ham hc0 hac haC hs0 hs1,
    ← intervalIntegral.integral_sub (intervalIntegrable_sub_mul_mixSpeed ν hd hc0 hc hC hs0 hs1)
      (intervalIntegrable_sub_mul_mixSpeed ν ham hc0 hac haC hs0 hs1)]
  refine intervalIntegral.integral_congr fun w _ ↦ ?_
  ring

/-- **The marginal residual is accumulated curvature defect between the observable path and the
atlas path**: `R_s = ∫₀ˢ (s − w) (k_a(w) − κ(w)) dw`. -/
theorem marginal_eq_integral_curvature {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hfin : genRate ν S (fun i ↦ ∫ x, S i x ∂densLaw ν d) ≠ ⊤) :
    (klDiv ((densLaw ν (bridgeDens d s)).map (statPoint S))
        ((responseProjection hS ν (fun i ↦ ∫ x, S i x ∂densLaw ν (bridgeDens d s))).map
          (statPoint S))).toReal =
      ∫ w in (0 : ℝ)..s, (s - w) * (mixSpeed ν a w - atlasCurv hS ν hfin w) := by
  have hP := isProbabilityMeasure_densLaw_bridge ν hd hc0 hc hC hnorm hs0 hs1.le
  have hDν : densLaw ν (bridgeDens d s) ≪ ν := withDensity_absolutelyContinuous ν _
  have hkl : klDiv (densLaw ν (bridgeDens d s)) ν ≠ ⊤ :=
    klDiv_densLaw_ne_top ν (measurable_bridgeDens hd s) (lt_min one_pos hc0)
      (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1.le x).1)
      (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1.le x).2)
  have hfins : genRate ν S (fun i ↦ ∫ x, S i x ∂densLaw ν (bridgeDens d s)) ≠ ⊤ := fun h ↦
    hkl (klDiv_eq_top_of_genRate_eq_top hS ν _ h)
  obtain ⟨-, -, -, hpyth⟩ := responseProjection_spec hS ν hfins
  have h0 := hpyth (densLaw ν (bridgeDens d s)) hP rfl
  have hsplit := klDiv_responseProjection_eq_statisticLift_add_map' hS ν
    (densLaw ν (bridgeDens d s)) hkl
  have h1 := klDiv_eq_klDiv_statisticLift_add_map ν (densLaw ν (bridgeDens d s)) (statPoint S)
    (measurable_statPoint hS) hDν hkl
  rw [← klDiv_statisticLift_eq_map ν _ (statPoint S) (measurable_statPoint hS) hDν] at h1
  have hne1 : klDiv (densLaw ν (bridgeDens d s))
      (statisticLift ν (densLaw ν (bridgeDens d s)) (statPoint S)) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at h1
    exact hkl h1
  have hne2 : klDiv (statisticLift ν (densLaw ν (bridgeDens d s)) (statPoint S)) ν ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at h1
    exact hkl h1
  have hPne : klDiv (densLaw ν (bridgeDens d s))
      (responseProjection hS ν (fun i ↦ ∫ x, S i x ∂densLaw ν (bridgeDens d s))) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at h0
    exact hkl h0
  have hRne : klDiv ((densLaw ν (bridgeDens d s)).map (statPoint S))
      ((responseProjection hS ν (fun i ↦ ∫ x, S i x ∂densLaw ν (bridgeDens d s))).map
        (statPoint S)) ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hsplit
    exact hPne hsplit
  have e0 := congrArg ENNReal.toReal h0
  rw [ENNReal.toReal_add hPne hfins] at e0
  have e1 := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_add hne1 hne2] at e1
  have esplit := congrArg ENNReal.toReal hsplit
  rw [ENNReal.toReal_add hne1 hRne] at esplit
  have hR : (klDiv ((densLaw ν (bridgeDens d s)).map (statPoint S))
      ((responseProjection hS ν (fun i ↦ ∫ x, S i x ∂densLaw ν (bridgeDens d s))).map
        (statPoint S))).toReal =
      (klDiv (statisticLift ν (densLaw ν (bridgeDens d s)) (statPoint S)) ν).toReal -
        (genRate ν S (fun i ↦ ∫ x, S i x ∂densLaw ν (bridgeDens d s))).toReal := by
    linarith
  have hI : (genRate ν S (fun i ↦ ∫ x, S i x ∂densLaw ν (bridgeDens d s))).toReal =
      ∫ u in (0 : ℝ)..s, (s - u) * atlasCurv hS ν hfin u := by
    rw [mean_densLaw_bridge ν hd hc0 hc hC hS hs0 hs1.le]
    exact genRate_atlasPath_eq_integral hS ν hfin hs0 hs1
  have hκ : IntervalIntegrable (fun u ↦ (s - u) * atlasCurv hS ν hfin u) volume 0 s := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hs0]
    exact (continuousOn_const.sub continuousOn_id).mul fun u hu ↦
      (continuousAt_atlasCurv hS ν hfin hu.1 (lt_of_le_of_lt hu.2 hs1)).continuousWithinAt
  rw [hR, hI, statisticLift_densLaw_bridge hS ν hd hc0 hc hC hnorm ha hs0 hs1.le,
    toReal_klDiv_densLaw_bridge ν ham hc0 hac haC hs0 hs1.le,
    ← intervalIntegral.integral_sub (intervalIntegrable_sub_mul_mixSpeed ν ham hc0 hac haC hs0
      hs1.le) hκ]
  refine intervalIntegral.integral_congr fun w _ ↦ ?_
  ring

end Split

end Laplace.Multi
