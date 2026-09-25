/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.AffinityKL
import Laplace.Multi.RadialCurvature

/-!
# The ray chart and the Legendre reading of the featureless line

The featureless line `u ↦ P_u ∝ e^{-uℓ} π` runs from the prior (`u = 0`, maximal entropy relative
to `π`) towards the data distribution. This module charts it by the response coordinate
`m(u) = ⟨ℓ⟩_u` and reads the KL divergence from the prior as a Legendre transform of the free
energy `F(u) = log Z(u)`.

* **Variance positivity.** `Var_u(ℓ) = Z(u)⁻¹ ∫ (ℓ − m(u))² e^{-uℓ} dν` (`lawVar_eq_integral_sq`),
  hence `Var_u(ℓ) > 0` as soon as the loss is not a.e. constant under the state density
  (`lawVar_pos`).
* **The ray chart.** `m` is strictly decreasing on `(0, ∞)` (`lawMean_strictAntiOn`), so it is an
  order-reversing bijection onto its image, an interval, and a homeomorphism `(0, ∞) ≃ₜ m '' (0, ∞)`
  (`rayChart`): the response coordinate `⟨ℓ⟩_u` and the temperature determine each other
  continuously along the whole ray.
* **Convexity and the Legendre identity.** `F` is convex on `(0, ∞)` with `F' = −m`
  (`lawFree_convexOn`), and
  `KL(P_u ‖ P_0) = −u m(u) − F(u) + F(0)` (`lawKL_zero_eq_legendre`), where the right-hand side is
  the Legendre transform of `F` at `−m(u)`:
  `−m(u) v − F(v) ≤ −m(u) u − F(u)` for all `v > 0` (`legendre_isMaxOn`). With `Z(0) = 1` this is
  Cramér's rate function of the loss under the prior evaluated at the level `m(u)`: the KL from the
  featureless end of the ray is the large-deviation cost of the response coordinate.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The response coordinate of the featureless line: the tilted mean `m(u) = ⟨ℓ⟩_u = N₁(u)/Z(u)`. -/
noncomputable def lawMean (ν : Measure ℝ) (u : ℝ) : ℝ := lawMoment ν 1 u / lawMoment ν 0 u

/-- The free energy of the featureless line, `F(u) = log Z(u)`. -/
noncomputable def lawFree (ν : Measure ℝ) (u : ℝ) : ℝ := Real.log (lawMoment ν 0 u)

section Variance

variable (ν : Measure ℝ)

/-- `Var_u(ℓ) = Z(u)⁻¹ ∫ (ℓ − m(u))² e^{-uℓ} dν`. -/
theorem lawVar_eq_integral_sq {u : ℝ} (hZ : 0 < lawMoment ν 0 u)
    (h0 : Integrable (fun ℓ ↦ Real.exp (-(u * ℓ))) ν)
    (h1 : Integrable (fun ℓ ↦ ℓ * Real.exp (-(u * ℓ))) ν)
    (h2 : Integrable (fun ℓ ↦ ℓ * ℓ * Real.exp (-(u * ℓ))) ν) :
    lawVar ν u = (∫ ℓ, (ℓ - lawMean ν u) ^ 2 * Real.exp (-(u * ℓ)) ∂ν) / lawMoment ν 0 u := by
  have h := integral_sq_sqrt_speed ν hZ h0 h1 h2
  have e : ∀ ℓ, (-(1 / 2) * (ℓ - lawMoment ν 1 u / lawMoment ν 0 u) *
      Real.sqrt (lawDensity ν u ℓ)) ^ 2 =
      (1 / 4) * ((ℓ - lawMean ν u) ^ 2 * Real.exp (-(u * ℓ)) / lawMoment ν 0 u) := fun ℓ ↦ by
    have hp : 0 ≤ lawDensity ν u ℓ := by unfold lawDensity; positivity
    rw [mul_pow, Real.sq_sqrt hp]
    unfold lawDensity lawMean
    ring
  simp_rw [e] at h
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_div] at h
  linarith

/-- The centred second-moment integrand is integrable (three tilted moments). -/
theorem integrable_sq_sub_mul_exp {u : ℝ} (m : ℝ)
    (h0 : Integrable (fun ℓ ↦ Real.exp (-(u * ℓ))) ν)
    (h1 : Integrable (fun ℓ ↦ ℓ * Real.exp (-(u * ℓ))) ν)
    (h2 : Integrable (fun ℓ ↦ ℓ * ℓ * Real.exp (-(u * ℓ))) ν) :
    Integrable (fun ℓ ↦ (ℓ - m) ^ 2 * Real.exp (-(u * ℓ))) ν := by
  have h := (h2.sub (h1.const_mul (2 * m))).add (h0.const_mul (m ^ 2))
  refine h.congr (Filter.Eventually.of_forall fun ℓ ↦ ?_)
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem lawVar_nonneg {u : ℝ} (hZ : 0 < lawMoment ν 0 u)
    (h0 : Integrable (fun ℓ ↦ Real.exp (-(u * ℓ))) ν)
    (h1 : Integrable (fun ℓ ↦ ℓ * Real.exp (-(u * ℓ))) ν)
    (h2 : Integrable (fun ℓ ↦ ℓ * ℓ * Real.exp (-(u * ℓ))) ν) : 0 ≤ lawVar ν u := by
  rw [lawVar_eq_integral_sq ν hZ h0 h1 h2]
  exact div_nonneg (integral_nonneg fun ℓ ↦ by positivity) hZ.le

/-- **Variance positivity**: if the loss is not a.e. constant under the state density then
`Var_u(ℓ) > 0`. -/
theorem lawVar_pos (hnd : ¬ ∃ c, ∀ᵐ ℓ ∂ν, ℓ = c) {u : ℝ} (hZ : 0 < lawMoment ν 0 u)
    (h0 : Integrable (fun ℓ ↦ Real.exp (-(u * ℓ))) ν)
    (h1 : Integrable (fun ℓ ↦ ℓ * Real.exp (-(u * ℓ))) ν)
    (h2 : Integrable (fun ℓ ↦ ℓ * ℓ * Real.exp (-(u * ℓ))) ν) : 0 < lawVar ν u := by
  rw [lawVar_eq_integral_sq ν hZ h0 h1 h2]
  refine div_pos ?_ hZ
  rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun ℓ ↦ by positivity)
    (integrable_sq_sub_mul_exp ν _ h0 h1 h2)]
  rw [pos_iff_ne_zero]
  intro hsupp
  refine hnd ⟨lawMean ν u, ?_⟩
  rw [ae_iff]
  refine measure_mono_null (fun ℓ hℓ ↦ ?_) hsupp
  simp only [mem_ofPred_eq, Function.mem_support] at hℓ ⊢
  exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hℓ)) (Real.exp_pos _).ne'

end Variance

section Chart

variable (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ)
  (hint : ∀ v > 0, ∀ k ≤ 2, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν)
  (hZ : ∀ u > 0, 0 < lawMoment ν 0 u)
include hpos hint hZ

/-- `m' = −Var` on `(0, ∞)`. -/
theorem hasDerivAt_lawMean' {u : ℝ} (hu : 0 < u) :
    HasDerivAt (lawMean ν) (-(lawVar ν u)) u :=
  hasDerivAt_lawMean ν hpos hint le_rfl hu (hZ u hu)

/-- `F' = −m` on `(0, ∞)`. -/
theorem hasDerivAt_lawFree {u : ℝ} (hu : 0 < u) :
    HasDerivAt (lawFree ν) (-(lawMean ν u)) u :=
  hasDerivAt_lawLogZ ν hpos hint (by norm_num) hu (hZ u hu)

theorem continuousOn_lawMean : ContinuousOn (lawMean ν) (Ioi 0) := fun _ hu ↦
  (hasDerivAt_lawMean' ν hpos hint hZ hu).continuousAt.continuousWithinAt

theorem continuousOn_lawFree : ContinuousOn (lawFree ν) (Ioi 0) := fun _ hu ↦
  (hasDerivAt_lawFree ν hpos hint hZ hu).continuousAt.continuousWithinAt

omit hpos hZ in
/-- The three tilted moments at a fixed `u > 0`, in the shapes the variance lemmas want. -/
theorem lawMoments_at {u : ℝ} (hu : 0 < u) :
    Integrable (fun ℓ ↦ Real.exp (-(u * ℓ))) ν ∧
      Integrable (fun ℓ ↦ ℓ * Real.exp (-(u * ℓ))) ν ∧
      Integrable (fun ℓ ↦ ℓ * ℓ * Real.exp (-(u * ℓ))) ν := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using hint u hu 0 (by norm_num)
  · simpa using hint u hu 1 (by norm_num)
  · have h := hint u hu 2 le_rfl
    refine h.congr (Filter.Eventually.of_forall fun ℓ ↦ ?_)
    simp only; ring

/-- The response coordinate is antitone along the ray. -/
theorem lawMean_antitoneOn : AntitoneOn (lawMean ν) (Ioi 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) (continuousOn_lawMean ν hpos hint hZ)
    (fun u hu ↦ ?_) fun u hu ↦ ?_
  · rw [interior_Ioi] at hu
    exact (hasDerivAt_lawMean' ν hpos hint hZ hu).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi] at hu
    rw [(hasDerivAt_lawMean' ν hpos hint hZ hu).deriv]
    obtain ⟨h0, h1, h2⟩ := lawMoments_at ν hint hu
    linarith [lawVar_nonneg ν (hZ u hu) h0 h1 h2]

/-- **The ray chart is strictly decreasing** when the loss is not a.e. constant. -/
theorem lawMean_strictAntiOn (hnd : ¬ ∃ c, ∀ᵐ ℓ ∂ν, ℓ = c) :
    StrictAntiOn (lawMean ν) (Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) (continuousOn_lawMean ν hpos hint hZ)
    fun u hu ↦ ?_
  rw [interior_Ioi] at hu
  rw [(hasDerivAt_lawMean' ν hpos hint hZ hu).deriv]
  obtain ⟨h0, h1, h2⟩ := lawMoments_at ν hint hu
  linarith [lawVar_pos ν hnd (hZ u hu) h0 h1 h2]

/-- The image of the ray under the chart is an interval. -/
theorem ordConnected_image_lawMean : OrdConnected (lawMean ν '' Ioi 0) :=
  isPreconnected_iff_ordConnected.mp
    (isPreconnected_Ioi.image _ (continuousOn_lawMean ν hpos hint hZ))

/-- **The ray chart**: `u ↦ ⟨ℓ⟩_u` is a homeomorphism from `(0, ∞)` onto its image. -/
theorem exists_rayChart (hnd : ¬ ∃ c, ∀ᵐ ℓ ∂ν, ℓ = c) :
    ∃ e : Ioi (0 : ℝ) ≃ₜ (lawMean ν '' Ioi 0), ∀ u, (e u : ℝ) = lawMean ν u := by
  -- the negated chart is strictly monotone, hence an order isomorphism onto its image
  have hmono : StrictMonoOn (fun u ↦ -lawMean ν u) (Ioi 0) := fun a ha b hb hab ↦
    neg_lt_neg (lawMean_strictAntiOn ν hpos hint hZ hnd ha hb hab)
  have hcont : ContinuousOn (fun u ↦ -lawMean ν u) (Ioi 0) :=
    (continuousOn_lawMean ν hpos hint hZ).neg
  have : OrdConnected ((fun u ↦ -lawMean ν u) '' Ioi 0) :=
    isPreconnected_iff_ordConnected.mp (isPreconnected_Ioi.image _ hcont)
  let e₁ : Ioi (0 : ℝ) ≃ₜ ((fun u ↦ -lawMean ν u) '' Ioi 0) :=
    (StrictMonoOn.orderIso _ _ hmono).toHomeomorph
  -- negate back
  have himg : (Homeomorph.neg ℝ) '' ((fun u ↦ -lawMean ν u) '' Ioi 0) = lawMean ν '' Ioi 0 := by
    rw [Set.image_image]
    exact Set.image_congr fun u _ ↦ by simp
  refine ⟨e₁.trans (((Homeomorph.neg ℝ).image _).trans (Homeomorph.setCongr himg)), fun u ↦ ?_⟩
  change -(-(lawMean ν u)) = lawMean ν u
  exact neg_neg _

end Chart

section Legendre

variable (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ)
  (hint : ∀ v > 0, ∀ k ≤ 2, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν)
  (hZ : ∀ u > 0, 0 < lawMoment ν 0 u)
include hpos hint hZ

/-- **The free energy is convex** along the ray (`F'' = Var ≥ 0`). -/
theorem lawFree_convexOn : ConvexOn ℝ (Ioi 0) (lawFree ν) := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ioi 0) (continuousOn_lawFree ν hpos hint hZ)
    (fun u hu ↦ ?_) fun u hu v hv huv ↦ ?_
  · rw [interior_Ioi] at hu
    exact (hasDerivAt_lawFree ν hpos hint hZ hu).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi] at hu hv
    rw [(hasDerivAt_lawFree ν hpos hint hZ hu).deriv, (hasDerivAt_lawFree ν hpos hint hZ hv).deriv]
    exact neg_le_neg (lawMean_antitoneOn ν hpos hint hZ hu hv huv)

/-- **The tangent inequality**: `F(v) ≥ F(u) − m(u)(v − u)` for `u, v > 0`. -/
theorem lawFree_ge_tangent {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    lawFree ν u - lawMean ν u * (v - u) ≤ lawFree ν v := by
  have hconv := lawFree_convexOn ν hpos hint hZ
  have hd := hasDerivAt_lawFree ν hpos hint hZ hu
  rcases lt_trichotomy u v with huv | rfl | hvu
  · have h := hconv.le_slope_of_hasDerivAt hu hv huv hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    linarith
  · simp
  · have h := hconv.slope_le_of_hasDerivAt hv hu hvu hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    linarith

omit hpos hint in
/-- **The Legendre identity**: `KL(P_u ‖ P_0) = −u m(u) − F(u) + F(0)`. -/
theorem lawKL_zero_eq_legendre (hZ0 : 0 < lawMoment ν 0 0) {u : ℝ} (hu : 0 < u) :
    lawKL ν u 0 = -(lawMean ν u) * u - lawFree ν u + lawFree ν 0 := by
  unfold lawKL lawMean lawFree
  rw [Real.log_div hZ0.ne' (hZ u hu).ne']
  ring

/-- **The Legendre transform is attained at `u`**: `v ↦ −m(u) v − F(v)` is maximal on `(0, ∞)`
at `v = u`, so `KL(P_u ‖ P_0) − F(0) = F*(−m(u)) = sup_v (−m(u) v − F(v))`. -/
theorem legendre_isMaxOn {u : ℝ} (hu : 0 < u) :
    IsMaxOn (fun v ↦ -(lawMean ν u) * v - lawFree ν v) (Ioi 0) u := by
  intro v hv
  have h := lawFree_ge_tangent ν hpos hint hZ hu hv
  simp only [mem_ofPred_eq]
  linarith

/-- The Legendre form of the KL from the prior: for every `v > 0`,
`−m(u) v − F(v) ≤ KL(P_u ‖ P_0) − F(0)`, with equality at `v = u`. -/
theorem lawKL_zero_ge_legendre (hZ0 : 0 < lawMoment ν 0 0) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    -(lawMean ν u) * v - lawFree ν v ≤ lawKL ν u 0 - lawFree ν 0 := by
  rw [lawKL_zero_eq_legendre ν hZ hZ0 hu]
  have := legendre_isMaxOn ν hpos hint hZ hu hv
  simp only [mem_ofPred_eq] at this
  linarith

end Legendre

end Laplace.Multi
