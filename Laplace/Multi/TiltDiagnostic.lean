/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.InvisibleQuadratic
import Laplace.Multi.PathEnergy

/-!
# Euler identities for the information along the affine data path

Along the affine data path `D_s = (1 + s(d − 1))ν` from the featureless law to `D = dν`, write
`A(s) = KL(D_s ‖ ν)` (total information), `𝓘(s) = 𝓘(M_s)` (visible information, the rate at the
response `M_s = m₀ + s(M_D − m₀)`) and `R(s) = A(s) − 𝓘(s) = KL(D_s ‖ Q_{M_s})` (invisible
information). Each satisfies an exact **Euler identity** expressing `s f'(s) − f(s)` as a reverse
information:

* `bridge_information_euler`: `s A'(s) − A(s) = KL(ν ‖ D_s)`;
* `atlas_rate_euler`: `s 𝓘'(s) − 𝓘(s) = KL(ν ‖ Q_{M_s})`;
* `invisibleBridge_euler`: `s R'(s) − R(s) = KL(ν ‖ D_s) − KL(ν ‖ Q_{M_s})`;
* `hasDerivAt_invisibleBridge_div`: `d/ds (R(s)/s) = (KL(ν ‖ D_s) − KL(ν ‖ Q_{M_s})) / s²`.

So the invisible information per unit displacement grows exactly when the reverse information of
the data exceeds the reverse information of its reconstruction: the sign of the reverse-KL gap is
the tilt diagnostic. (The invisible information itself need not be monotone: `InvisibleHump`.)
-/

open MeasureTheory Filter Topology Set InformationTheory

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

omit [Nonempty X] [Nonempty J] hS in
/-- `⟨θ, s • v⟩ = s ⟨θ, v⟩`. -/
theorem dotJ_smul_right (θ : J → ℝ) (s : ℝ) (v : J → ℝ) : dotJ θ (s • v) = s * dotJ θ v := by
  simp only [dotJ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **Euler identity for the visible information along the atlas**:
`s 𝓘'(s) − 𝓘(s) = KL(ν ‖ Q_{M_s})`, with `𝓘'(s) = −⟨θ_s, M − m₀⟩`. -/
theorem atlas_rate_euler {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) :
    s * (-dotJ (atlasTheta hS ν M s : J → ℝ) (M - m₀)) -
        (genRate ν S (atlasPath S ν M s)).toReal =
      (klDiv ν (Pfam (atlasTheta hS ν M s : J → ℝ))).toReal := by
  have hrel := atlas_mem_intrinsicInterior hS ν hfin hs0 hs1
  have h := toReal_klDiv_familyMeasure_symm hS ν (atlasTheta hS ν M s)
  have e : meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s) =
      atlasPath S ν M s :=
    meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS hrel
  rw [e, atlasPath_sub, dotJ_smul_right] at h
  have hkl : (klDiv (Pfam (atlasTheta hS ν M s : J → ℝ)) ν).toReal =
      (genRate ν S (atlasPath S ν M s)).toReal := by
    have hfin' := genRate_ne_top_of_mem_intrinsicInterior hS ν hrel
    have h2 := (responseProjection_spec hS ν hfin').2.2.1
    rw [responseProjection_eq_familyMeasure_responseTheta hS ν hrel] at h2
    exact congrArg ENNReal.toReal h2
  rw [hkl] at h
  linarith

section Bridge

variable {d : X → ℝ} (hd : Measurable d) {c C : ℝ} (hc0 : 0 < c) (hc : ∀ x, c ≤ d x)
  (hC : ∀ x, d x ≤ C) (hnorm : ∫ x, d x ∂ν = 1)
include hd hc0 hc hC

omit [Nonempty X] [MeasurableSpace X] [Fintype J] [Nonempty J] hS hd in
/-- The logarithm of the bridge density is bounded on `[0, 1]`. -/
theorem abs_log_bridgeDens_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : X) :
    |Real.log (bridgeDens d s x)| ≤ |Real.log (min 1 c)| + |Real.log (max 1 C)| := by
  have hb := bridgeDens_bounds hc hC hs0 hs1 x
  have hpos : 0 < bridgeDens d s x := lt_of_lt_of_le (lt_min one_pos hc0) hb.1
  have h1 := Real.log_le_log (lt_min one_pos hc0) hb.1
  have h2 := Real.log_le_log hpos hb.2
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log (min 1 c)), abs_nonneg (Real.log (max 1 C))]
  · linarith [le_abs_self (Real.log (max 1 C)), abs_nonneg (Real.log (min 1 c))]

omit [Nonempty X] [Fintype J] [Nonempty J] hS in
/-- The information of the bridge as an integral of `klFun`. -/
theorem toReal_klDiv_bridge_eq_integral_klFun {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (klDiv (densLaw ν (bridgeDens d s)) ν).toReal = ∫ x, klFun (bridgeDens d s x) ∂ν :=
  toReal_klDiv_densLaw ν (measurable_bridgeDens hd s) (lt_min one_pos hc0)
    (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1 x).1) (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1 x).2)

omit [Nonempty X] [Fintype J] [Nonempty J] hS in
/-- The derivative of the total information along the bridge, by differentiation under the
integral: `A'(s) = ∫ (d − 1) log(1 + s(d − 1)) dν`. -/
theorem hasDerivAt_integral_klFun_bridge {s₀ : ℝ} (hs0 : 0 < s₀) (hs1 : s₀ < 1) :
    HasDerivAt (fun s ↦ ∫ x, klFun (bridgeDens d s x) ∂ν)
      (∫ x, (d x - 1) * Real.log (bridgeDens d s₀ x) ∂ν) s₀ := by
  obtain ⟨hm, B, hB⟩ := bdd_sub_one hd hc0 hc hC
  have hr0 : 0 < min s₀ (1 - s₀) := lt_min hs0 (by linarith)
  have hball : ∀ s ∈ Metric.ball s₀ (min s₀ (1 - s₀)), 0 ≤ s ∧ s ≤ 1 := fun s hs ↦ by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    have h1 := min_le_left s₀ (1 - s₀)
    have h2 := min_le_right s₀ (1 - s₀)
    constructor <;> linarith
  have hpos : ∀ s ∈ Metric.ball s₀ (min s₀ (1 - s₀)), ∀ x, 0 < bridgeDens d s x := fun s hs x ↦
    lt_of_lt_of_le (lt_min one_pos hc0)
      (bridgeDens_bounds hc hC (hball s hs).1 (hball s hs).2 x).1
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun s x ↦ klFun (bridgeDens d s x))
    (F' := fun s x ↦ (d x - 1) * Real.log (bridgeDens d s x))
    (bound := fun _ ↦ B * (|Real.log (min 1 c)| + |Real.log (max 1 C)|)) (x₀ := s₀)
    (Metric.ball_mem_nhds s₀ hr0)
    (Eventually.of_forall fun s ↦
      (measurable_klFun.comp (measurable_bridgeDens hd s)).aestronglyMeasurable)
    (integrable_klFun_comp ν (measurable_bridgeDens hd s₀)
      (fun x ↦ (bridgeDens_bounds hc hC hs0.le hs1.le x).1)
      (fun x ↦ (bridgeDens_bounds hc hC hs0.le hs1.le x).2))
    (hm.aestronglyMeasurable.mul
      (Real.measurable_log.comp (measurable_bridgeDens hd s₀)).aestronglyMeasurable)
    (Eventually.of_forall fun x s hs ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hB x) (abs_log_bridgeDens_le hc0 hc hC (hball s hs).1 (hball s hs).2 x)
        (abs_nonneg _) ((abs_nonneg _).trans (hB x)))
    (integrable_const _)
    (Eventually.of_forall fun x s hs ↦ by
      have h := (hasDerivAt_klFun (hpos s hs x).ne').comp s
        (((hasDerivAt_id s).mul_const (d x - 1)).const_add 1)
      refine h.congr_deriv ?_
      simp only [bridgeDens]
      ring)
  exact key.2

omit [Nonempty X] [Fintype J] [Nonempty J] hS in
/-- The total information `A(s) = KL(D_s ‖ ν)` is differentiable on `(0, 1)`. -/
theorem hasDerivAt_klDiv_bridge {s₀ : ℝ} (hs0 : 0 < s₀) (hs1 : s₀ < 1) :
    HasDerivAt (fun s ↦ (klDiv (densLaw ν (bridgeDens d s)) ν).toReal)
      (∫ x, (d x - 1) * Real.log (bridgeDens d s₀ x) ∂ν) s₀ := by
  refine (hasDerivAt_integral_klFun_bridge ν hd hc0 hc hC hs0 hs1).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hs0 hs1] with s hs
  exact toReal_klDiv_bridge_eq_integral_klFun ν hd hc0 hc hC hs.1.le hs.2.le

include hnorm

omit [Nonempty X] [Fintype J] [Nonempty J] hS hnorm in
/-- **Euler identity for the total information**: `s A'(s) − A(s) = KL(ν ‖ D_s)`. -/
theorem bridge_information_euler {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s * (∫ x, (d x - 1) * Real.log (bridgeDens d s x) ∂ν) -
        (klDiv (densLaw ν (bridgeDens d s)) ν).toReal =
      (klDiv ν (densLaw ν (bridgeDens d s))).toReal := by
  obtain ⟨hm, B, hB⟩ := bdd_sub_one hd hc0 hc hC
  have hlog : Bdd fun x ↦ Real.log (bridgeDens d s x) :=
    ⟨Real.measurable_log.comp (measurable_bridgeDens hd s), _,
      abs_log_bridgeDens_le hc0 hc hC hs0 hs1⟩
  have h1 : Integrable (fun x ↦ s * ((d x - 1) * Real.log (bridgeDens d s x))) ν :=
    (integrable_of_bdd_prob ν (Bdd.mul ⟨hm, B, hB⟩ hlog)).const_mul s
  have h2 : Integrable (fun x ↦ klFun (bridgeDens d s x)) ν :=
    integrable_klFun_comp ν (measurable_bridgeDens hd s)
      (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1 x).1)
      (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1 x).2)
  rw [toReal_klDiv_bridge_eq_integral_klFun ν hd hc0 hc hC hs0 hs1,
    toReal_klDiv_densLaw_symm ν (measurable_bridgeDens hd s) (lt_min one_pos hc0)
      (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1 x).1)
      (fun x ↦ (bridgeDens_bounds hc hC hs0 hs1 x).2),
    ← integral_const_mul, ← integral_sub h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [klFun_apply, bridgeDens]
  ring

/-- The data response `M_D = ∫ S dD`. -/
local notation "M_D" => (fun i ↦ ∫ x, S i x ∂densLaw ν d)

/-- **The invisible information is differentiable on `(0, 1)`**, with derivative
`R'(s) = A'(s) − 𝓘'(s)`. -/
theorem hasDerivAt_invisibleBridge {s₀ : ℝ} (hs0 : 0 < s₀) (hs1 : s₀ < 1) :
    HasDerivAt (invisibleBridge hS ν d)
      ((∫ x, (d x - 1) * Real.log (bridgeDens d s₀ x) ∂ν) -
        (-dotJ (atlasTheta hS ν M_D s₀ : J → ℝ) (M_D - m₀))) s₀ := by
  have hfin := genRate_ne_top_of_mem_intrinsicInterior hS ν
    (mean_densLaw_mem_intrinsicInterior hS ν hd hc0 hc hC hnorm)
  have hA := hasDerivAt_klDiv_bridge ν hd hc0 hc hC hs0 hs1
  have hI := hasDerivAt_atlasRate hS ν hfin hs0.le hs1
  refine (hA.sub hI).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hs0 hs1] with s hs
  rw [invisibleBridge_eq hS ν hd hc0 hc hC hnorm hs.1.le hs.2,
    mean_densLaw_bridge ν hd hc0 hc hC hS hs.1.le hs.2.le]
  rfl

/-- **Euler identity for the invisible information**:
`s R'(s) − R(s) = KL(ν ‖ D_s) − KL(ν ‖ Q_{M_s})`. -/
theorem invisibleBridge_euler {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    s * ((∫ x, (d x - 1) * Real.log (bridgeDens d s x) ∂ν) -
        (-dotJ (atlasTheta hS ν M_D s : J → ℝ) (M_D - m₀))) - invisibleBridge hS ν d s =
      (klDiv ν (densLaw ν (bridgeDens d s))).toReal -
        (klDiv ν (Pfam (atlasTheta hS ν M_D s : J → ℝ))).toReal := by
  have hfin := genRate_ne_top_of_mem_intrinsicInterior hS ν
    (mean_densLaw_mem_intrinsicInterior hS ν hd hc0 hc hC hnorm)
  have h1 := bridge_information_euler ν hd hc0 hc hC hs0 hs1.le
  have h2 := atlas_rate_euler hS ν hfin hs0 hs1
  rw [invisibleBridge_eq hS ν hd hc0 hc hC hnorm hs0 hs1,
    mean_densLaw_bridge ν hd hc0 hc hC hS hs0 hs1.le]
  linarith

/-- **The tilt diagnostic**: the invisible information per unit displacement `R(s)/s` has
derivative `(KL(ν ‖ D_s) − KL(ν ‖ Q_{M_s})) / s²` on `(0, 1)`; it increases exactly where the
reverse information of the data exceeds the reverse information of its reconstruction. -/
theorem hasDerivAt_invisibleBridge_div {s₀ : ℝ} (hs0 : 0 < s₀) (hs1 : s₀ < 1) :
    HasDerivAt (fun s ↦ invisibleBridge hS ν d s / s)
      (((klDiv ν (densLaw ν (bridgeDens d s₀))).toReal -
        (klDiv ν (Pfam (atlasTheta hS ν M_D s₀ : J → ℝ))).toReal) / s₀ ^ 2) s₀ := by
  have h := (hasDerivAt_invisibleBridge hS ν hd hc0 hc hC hnorm hs0 hs1).div (hasDerivAt_id s₀)
    hs0.ne'
  refine h.congr_deriv ?_
  rw [← invisibleBridge_euler hS ν hd hc0 hc hC hnorm hs0.le hs1]
  simp only [id_eq, mul_one]
  ring

end Bridge

end Laplace.Multi
