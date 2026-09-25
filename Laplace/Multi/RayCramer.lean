/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.RayChart

/-!
# The Cramér form of the ray: the rate function in the response coordinate

`RayChart` charts the featureless line by `m(u) = ⟨ℓ⟩_u`. Here the chart is inverted on its (open)
image `J = m '' (0,∞)` (`rayInv`, `hasDerivAt_rayInv`: `u'(x) = −1/Var_{u(x)}`) and the Legendre
identity is written as a function of the response coordinate:

* `rayRate ν x = −x u(x) − F(u(x))` is the one-sided Cramér transform of `F = log Z`: it is the
  maximum of `v ↦ −x v − F(v)` over `v > 0` (`rayRate_isMaxOn`), and at `x = m(u)` it is
  `KL(P_u ‖ P_0) − F(0)` (`rayRate_lawMean`, `rayRate_lawMean_eq_lawKL`).
* `I'(x) = −u(x)` and `I''(x) = 1/Var_{u(x)}(ℓ)` (`hasDerivAt_rayRate`, `hasDerivAt_deriv_rayRate`):
  the temperature is minus the slope of the rate function in the chart, and the Fisher speed is its
  curvature.
* `ds² = Var_u du² = I''(m) dm²`: the Fisher length of the ray is the integral of `√I''` in the
  chart (`lawLength_eq_integral_sqrt_curvature`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The inverse of the ray chart on its image (temperature as a function of the response). -/
noncomputable def rayInv (ν : Measure ℝ) : ℝ → ℝ := Function.invFunOn (lawMean ν) (Ioi 0)

/-- The rate function of the ray in the response coordinate, `I(x) = −x u(x) − F(u(x))`. -/
noncomputable def rayRate (ν : Measure ℝ) (x : ℝ) : ℝ :=
  -x * rayInv ν x - lawFree ν (rayInv ν x)

section

variable (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ)
  (hint : ∀ v > 0, ∀ k ≤ 3, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν)
  (hZ : ∀ u > 0, 0 < lawMoment ν 0 u) (hnd : ¬ ∃ c, ∀ᵐ ℓ ∂ν, ℓ = c)
include hpos hint hZ hnd

omit hpos hZ hnd in
theorem hint2 : ∀ v > 0, ∀ k ≤ 2, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν :=
  fun v hv k hk ↦ hint v hv k (by omega)

omit hnd in
theorem continuousOn_lawVar' : ContinuousOn (lawVar ν) (Ioi 0) :=
  continuousOn_lawVar ν hpos hint le_rfl hZ

/-- The inverse chart sends `m(u)` back to `u`. -/
theorem rayInv_lawMean {u : ℝ} (hu : 0 < u) : rayInv ν (lawMean ν u) = u :=
  (lawMean_strictAntiOn ν hpos (hint2 ν hint) hZ hnd).injOn.leftInvOn_invFunOn hu

omit hpos hint hZ hnd in
theorem rayInv_pos {x : ℝ} (hx : x ∈ lawMean ν '' Ioi 0) : 0 < rayInv ν x :=
  Function.invFunOn_mem hx

omit hpos hint hZ hnd in
theorem lawMean_rayInv {x : ℝ} (hx : x ∈ lawMean ν '' Ioi 0) : lawMean ν (rayInv ν x) = x :=
  Function.invFunOn_eq hx

/-- The image of the ray chart is open. -/
theorem isOpen_image_lawMean : IsOpen (lawMean ν '' Ioi 0) := by
  have hanti := lawMean_strictAntiOn ν hpos (hint2 ν hint) hZ hnd
  have hcont := continuousOn_lawMean ν hpos (hint2 ν hint) hZ
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨u, hu, rfl⟩
  have hu : 0 < u := hu
  have h1 : lawMean ν (2 * u) < lawMean ν u :=
    hanti (mem_Ioi.2 hu) (mem_Ioi.2 (by linarith)) (by linarith)
  have h2 : lawMean ν u < lawMean ν (u / 2) :=
    hanti (mem_Ioi.2 (by linarith)) (mem_Ioi.2 hu) (by linarith)
  refine mem_of_superset (Ioo_mem_nhds h1 h2) ?_
  calc Ioo (lawMean ν (2 * u)) (lawMean ν (u / 2)) ⊆ lawMean ν '' Ioo (u / 2) (2 * u) :=
        intermediate_value_Ioo' (by linarith) (hcont.mono fun y hy ↦ by
          simp only [mem_Icc] at hy
          exact mem_Ioi.2 (by linarith))
    _ ⊆ lawMean ν '' Ioi 0 := image_mono fun y hy ↦ mem_Ioi.2 (by linarith [hy.1])

/-- The inverse chart is antitone on the image. -/
theorem rayInv_antitoneOn : AntitoneOn (rayInv ν) (lawMean ν '' Ioi 0) := by
  intro x hx y hy hxy
  by_contra h
  push Not at h
  have := lawMean_strictAntiOn ν hpos (hint2 ν hint) hZ hnd (rayInv_pos ν hx)
    (rayInv_pos ν hy) h
  rw [lawMean_rayInv ν hx, lawMean_rayInv ν hy] at this
  exact absurd this (not_lt.2 hxy)

/-- The inverse chart is continuous at every point of the image. -/
theorem continuousAt_rayInv {x : ℝ} (hx : x ∈ lawMean ν '' Ioi 0) : ContinuousAt (rayInv ν) x := by
  have hT := isOpen_image_lawMean ν hpos hint hZ hnd
  have hmono : MonotoneOn (fun y ↦ -rayInv ν y) (lawMean ν '' Ioi 0) := fun a ha b hb hab ↦
    neg_le_neg (rayInv_antitoneOn ν hpos hint hZ hnd ha hb hab)
  have himg : (fun y ↦ -rayInv ν y) '' (lawMean ν '' Ioi 0) ∈ 𝓝 (-rayInv ν x) := by
    refine mem_of_superset (Iio_mem_nhds (neg_lt_zero.2 (rayInv_pos ν hx))) ?_
    intro z hz
    have hz' : 0 < -z := by simpa using hz
    refine ⟨lawMean ν (-z), ⟨-z, hz', rfl⟩, ?_⟩
    simp only
    rw [rayInv_lawMean ν hpos hint hZ hnd hz', neg_neg]
  have h := (continuousAt_of_monotoneOn_of_image_mem_nhds hmono (hT.mem_nhds hx) himg).neg
  exact h.congr (Filter.Eventually.of_forall fun y ↦ by simp)

/-- **The derivative of the inverse chart**: `u'(x) = −1/Var_{u(x)}(ℓ)`. -/
theorem hasDerivAt_rayInv {x : ℝ} (hx : x ∈ lawMean ν '' Ioi 0) :
    HasDerivAt (rayInv ν) (-(lawVar ν (rayInv ν x)))⁻¹ x := by
  have hu := rayInv_pos ν hx
  obtain ⟨h0, h1, h2⟩ := lawMoments_at ν (hint2 ν hint) hu
  refine HasDerivAt.of_local_left_inverse (continuousAt_rayInv ν hpos hint hZ hnd hx)
    (hasDerivAt_lawMean' ν hpos (hint2 ν hint) hZ hu)
    (neg_ne_zero.2 (lawVar_pos ν hnd (hZ _ hu) h0 h1 h2).ne') ?_
  filter_upwards [(isOpen_image_lawMean ν hpos hint hZ hnd).mem_nhds hx] with y hy
  exact lawMean_rayInv ν hy

/-- The inverse chart is continuous on the image. -/
theorem continuousOn_rayInv : ContinuousOn (rayInv ν) (lawMean ν '' Ioi 0) := fun _ hx ↦
  (continuousAt_rayInv ν hpos hint hZ hnd hx).continuousWithinAt

/-! ### The rate function -/

/-- At `x = m(u)` the rate function is `−u m(u) − F(u)`. -/
theorem rayRate_lawMean {u : ℝ} (hu : 0 < u) :
    rayRate ν (lawMean ν u) = -u * lawMean ν u - lawFree ν u := by
  unfold rayRate
  rw [rayInv_lawMean ν hpos hint hZ hnd hu]
  ring

/-- **The rate function is the KL from the prior**: `I(m(u)) = KL(P_u ‖ P_0) − F(0)`. -/
theorem rayRate_lawMean_eq_lawKL (hZ0 : 0 < lawMoment ν 0 0) {u : ℝ} (hu : 0 < u) :
    rayRate ν (lawMean ν u) = lawKL ν u 0 - lawFree ν 0 := by
  rw [rayRate_lawMean ν hpos hint hZ hnd hu, lawKL_zero_eq_legendre ν hZ hZ0 hu]
  ring

omit hnd in
/-- **The one-sided Cramér transform**: `I(x) = sup_{v>0} (−x v − F(v))`, attained at `v = u(x)`. -/
theorem rayRate_isMaxOn {x : ℝ} (hx : x ∈ lawMean ν '' Ioi 0) :
    IsMaxOn (fun v ↦ -x * v - lawFree ν v) (Ioi 0) (rayInv ν x) := by
  have h := legendre_isMaxOn ν hpos (hint2 ν hint) hZ (rayInv_pos ν hx)
  rwa [lawMean_rayInv ν hx] at h

/-- **`I'(x) = −u(x)`**: the temperature is minus the slope of the rate function. -/
theorem hasDerivAt_rayRate {x : ℝ} (hx : x ∈ lawMean ν '' Ioi 0) :
    HasDerivAt (rayRate ν) (-(rayInv ν x)) x := by
  have hu := rayInv_pos ν hx
  have h1 := hasDerivAt_rayInv ν hpos hint hZ hnd hx
  have h2 := (hasDerivAt_lawFree ν hpos (hint2 ν hint) hZ hu).comp x h1
  have h := ((hasDerivAt_id x).neg.mul h1).sub h2
  refine h.congr_deriv ?_
  rw [lawMean_rayInv ν hx]
  simp only [Pi.neg_apply, id_eq]
  ring

/-- **`I''(x) = 1/Var_{u(x)}(ℓ)`**: the Fisher speed of the ray is the curvature of the rate
function in the response coordinate. -/
theorem hasDerivAt_deriv_rayRate {x : ℝ} (hx : x ∈ lawMean ν '' Ioi 0) :
    HasDerivAt (deriv (rayRate ν)) (1 / lawVar ν (rayInv ν x)) x := by
  have h1 := (hasDerivAt_rayInv ν hpos hint hZ hnd hx).neg
  have e : -(-(lawVar ν (rayInv ν x)))⁻¹ = 1 / lawVar ν (rayInv ν x) := by
    rw [neg_inv, neg_neg, one_div]
  rw [e] at h1
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_image_lawMean ν hpos hint hZ hnd).mem_nhds hx] with y hy
  exact (hasDerivAt_rayRate ν hpos hint hZ hnd hy).deriv

/-- The rate function is convex on the chart image. -/
theorem rayRate_convexOn : ConvexOn ℝ (lawMean ν '' Ioi 0) (rayRate ν) := by
  have hT := isOpen_image_lawMean ν hpos hint hZ hnd
  refine MonotoneOn.convexOn_of_deriv (ordConnected_image_lawMean ν hpos (hint2 ν hint) hZ).convex
    (fun x hx ↦ (hasDerivAt_rayRate ν hpos hint hZ hnd hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ ?_) fun x hx y hy hxy ↦ ?_
  · rw [hT.interior_eq] at hx
    exact (hasDerivAt_rayRate ν hpos hint hZ hnd hx).differentiableAt.differentiableWithinAt
  · rw [hT.interior_eq] at hx hy
    rw [(hasDerivAt_rayRate ν hpos hint hZ hnd hx).deriv,
      (hasDerivAt_rayRate ν hpos hint hZ hnd hy).deriv]
    exact neg_le_neg (rayInv_antitoneOn ν hpos hint hZ hnd hx hy hxy)

/-! ### The Fisher length in the chart -/

/-- **`ds² = Var_u du² = I''(m) dm²`**: the Fisher length of a segment of the ray is the integral of
the square root of the curvature of the rate function over the corresponding response interval. -/
theorem lawLength_eq_integral_sqrt_curvature {u₀ u₁ : ℝ} (hu₀ : 0 < u₀) (hu : u₀ ≤ u₁) :
    ∫ u in u₀..u₁, Real.sqrt (lawVar ν u) =
      ∫ x in lawMean ν u₁..lawMean ν u₀, Real.sqrt (1 / lawVar ν (rayInv ν x)) := by
  have hI : uIcc u₀ u₁ ⊆ Ioi 0 := fun y hy ↦ by
    rw [uIcc_of_le hu] at hy
    exact mem_Ioi.2 (lt_of_lt_of_le hu₀ hy.1)
  have hVar : ∀ u ∈ Ioi (0 : ℝ), 0 < lawVar ν u := fun u hu ↦ by
    obtain ⟨h0, h1, h2⟩ := lawMoments_at ν (hint2 ν hint) hu
    exact lawVar_pos ν hnd (hZ u hu) h0 h1 h2
  have hcv := intervalIntegral.integral_comp_mul_deriv' (a := u₀) (b := u₁) (f := lawMean ν)
    (f' := fun u ↦ -(lawVar ν u)) (g := fun x ↦ Real.sqrt (1 / lawVar ν (rayInv ν x)))
    (fun u hu ↦ hasDerivAt_lawMean' ν hpos (hint2 ν hint) hZ (hI hu))
    ((continuousOn_lawVar' ν hpos hint hZ).neg.mono hI) ?_
  · rw [intervalIntegral.integral_symm (lawMean ν u₀) (lawMean ν u₁), ← hcv,
      ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u hu ↦ ?_
    have hu' := hI hu
    have hV := hVar u hu'
    simp only [Function.comp]
    rw [rayInv_lawMean ν hpos hint hZ hnd hu', one_div, Real.sqrt_inv, mul_neg, neg_neg,
      inv_mul_eq_div, eq_div_iff (Real.sqrt_pos.2 hV).ne', Real.mul_self_sqrt hV.le]
  · have hsub : lawMean ν '' uIcc u₀ u₁ ⊆ lawMean ν '' Ioi 0 := image_mono hI
    refine (Real.continuous_sqrt.comp_continuousOn (ContinuousOn.div continuousOn_const ?_ ?_)).mono
      hsub
    · exact (continuousOn_lawVar' ν hpos hint hZ).comp (continuousOn_rayInv ν hpos hint hZ hnd)
        fun x hx ↦ rayInv_pos ν hx
    · exact fun x hx ↦ (hVar _ (rayInv_pos ν hx)).ne'

end

end Laplace.Multi
