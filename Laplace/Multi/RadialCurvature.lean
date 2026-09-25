/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.Affinity

/-!
# Curvature of the featureless line: `F'' = Var`, the Jensen-gap identity, the square-root speed

For a state density `ν` with tilted moments `N_k(u) = ∫ ℓ^k e^{-uℓ} dν`, differentiation under the
integral gives `N_k' = −N_{k+1}` on `(0, ∞)` (`hasDerivAt_lawMoment`), so with `F = log Z`:

  `F'(u) = −⟨ℓ⟩_u`,  `(⟨ℓ⟩_u)' = −Var_u(ℓ)`,  i.e. `F'' = Var`
  (`hasDerivAt_lawLogZ`, `hasDerivAt_lawMean`).

Two consequences (Astra, round 26, Theorem A):

* **The Jensen-gap identity.** The Bhattacharyya divergence between `P_s` and `P_t` is the midpoint
  Jensen gap of `F`, and integrating `F''` twice, with `m = (s+t)/2`,
  `(F(s) + F(t))/2 − F(m) = ½ (∫_s^m (u − s) Var_u du + ∫_m^t (t − u) Var_u du)`
  (`bhattacharyya_eq_integral_var`): endpoint divergence and path length are two different
  functionals of the same variance profile.
* **The square-root speed.** The square root of the tilted density moves with velocity
  `∂_u √p_u = −½ (ℓ − ⟨ℓ⟩_u) √p_u` (`hasDerivAt_sqrt_lawDensity`), whose squared `L²(ν)`-norm is
  `Var_u(ℓ)/4` (`integral_sq_sqrt_speed`): the Fisher speed of the featureless line is the speed
  of the square-root embedding into the `L²` sphere.
-/

open MeasureTheory Filter Topology Set intervalIntegral

namespace Laplace.Multi

/-- **Differentiation under the integral**: `N_k' = −N_{k+1}` on `(0, ∞)`. -/
theorem hasDerivAt_lawMoment (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ) {K : ℕ}
    (hint : ∀ v > 0, ∀ k ≤ K, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν)
    {k : ℕ} (hk : k + 1 ≤ K) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v ↦ lawMoment ν k v) (-(lawMoment ν (k + 1) u)) u := by
  have hu2 : 0 < u / 2 := by positivity
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun v ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ)))
    (F' := fun v ℓ ↦ -(ℓ ^ (k + 1) * Real.exp (-(v * ℓ))))
    (bound := fun ℓ ↦ ℓ ^ (k + 1) * Real.exp (-(u / 2 * ℓ))) (x₀ := u) (s := Ioi (u / 2))
    (Ioi_mem_nhds (by linarith))
    (Filter.Eventually.of_forall fun v ↦ (by fun_prop : Measurable fun ℓ : ℝ ↦
      ℓ ^ k * Real.exp (-(v * ℓ))).aestronglyMeasurable)
    (hint u hu k (by omega))
    (by fun_prop : Measurable fun ℓ : ℝ ↦ -(ℓ ^ (k + 1) * Real.exp (-(u * ℓ)))).aestronglyMeasurable
    (by
      filter_upwards [hpos] with ℓ hℓ v hv
      have hv : u / 2 < v := hv
      rw [norm_neg, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hℓ,
        Real.abs_exp]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity))
    (hint (u / 2) hu2 (k + 1) hk)
    (Filter.Eventually.of_forall fun ℓ v _ ↦ by
      have hneg : HasDerivAt (fun x : ℝ ↦ -(x * ℓ)) (-ℓ) v := (hasDerivAt_mul_const ℓ).neg
      have he : HasDerivAt (fun x : ℝ ↦ Real.exp (-(x * ℓ))) (Real.exp (-(v * ℓ)) * -ℓ) v :=
        hneg.exp
      refine (he.const_mul (ℓ ^ k)).congr_deriv ?_
      ring)
  refine key.2.congr_deriv ?_
  unfold lawMoment
  rw [MeasureTheory.integral_neg]

/-- `F = log Z` has derivative `−⟨ℓ⟩_u`. -/
theorem hasDerivAt_lawLogZ (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ) {K : ℕ}
    (hint : ∀ v > 0, ∀ k ≤ K, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν) (hK : 1 ≤ K)
    {u : ℝ} (hu : 0 < u) (hZ : 0 < lawMoment ν 0 u) :
    HasDerivAt (fun v ↦ Real.log (lawMoment ν 0 v)) (-(lawMoment ν 1 u / lawMoment ν 0 u)) u := by
  have := (hasDerivAt_lawMoment ν hpos hint (k := 0) hK hu).log hZ.ne'
  refine this.congr_deriv ?_
  ring

/-- The tilted mean `⟨ℓ⟩_u = N₁/Z` has derivative `−Var_u(ℓ)`. -/
theorem hasDerivAt_lawMean (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ) {K : ℕ}
    (hint : ∀ v > 0, ∀ k ≤ K, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν) (hK : 2 ≤ K)
    {u : ℝ} (hu : 0 < u) (hZ : 0 < lawMoment ν 0 u) :
    HasDerivAt (fun v ↦ lawMoment ν 1 v / lawMoment ν 0 v) (-(lawVar ν u)) u := by
  have h1 := hasDerivAt_lawMoment ν hpos hint (k := 1) hK hu
  have h0 := hasDerivAt_lawMoment ν hpos hint (k := 0) (by omega) hu
  have := h1.div h0 hZ.ne'
  refine this.congr_deriv ?_
  unfold lawVar lawExp
  have e2 : (∫ ℓ, ℓ * ℓ * Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 2 u :=
    integral_congr_ae (Filter.Eventually.of_forall fun ℓ ↦ by ring)
  have e1 : (∫ ℓ, ℓ * Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 1 u := by simp [lawMoment]
  have e0 : (∫ ℓ, Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 0 u := by simp [lawMoment]
  rw [e2, e1, e0]
  field_simp
  ring

/-- `lawVar` is continuous on `(0, ∞)` (given three tilted moments). -/
theorem continuousOn_lawVar (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ) {K : ℕ}
    (hint : ∀ v > 0, ∀ k ≤ K, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν) (hK : 3 ≤ K)
    (hZ : ∀ u > 0, 0 < lawMoment ν 0 u) :
    ContinuousOn (fun u ↦ lawVar ν u) (Ioi 0) := by
  have hc : ∀ k, k + 1 ≤ K → ContinuousOn (fun u ↦ lawMoment ν k u) (Ioi 0) := fun k hk u hu ↦
    (hasDerivAt_lawMoment ν hpos hint hk hu).continuousAt.continuousWithinAt
  have e : ∀ u, lawVar ν u = lawMoment ν 2 u / lawMoment ν 0 u -
      (lawMoment ν 1 u / lawMoment ν 0 u) ^ 2 := fun u ↦ by
    unfold lawVar lawExp
    have e2 : (∫ ℓ, ℓ * ℓ * Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 2 u :=
      integral_congr_ae (Filter.Eventually.of_forall fun ℓ ↦ by ring)
    have e1 : (∫ ℓ, ℓ * Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 1 u := by simp [lawMoment]
    have e0 : (∫ ℓ, Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 0 u := by simp [lawMoment]
    rw [e2, e1, e0]
  simp_rw [e]
  exact ((hc 2 hK).div (hc 0 (by omega)) fun u hu ↦ (hZ u hu).ne').sub
    (((hc 1 (by omega)).div (hc 0 (by omega)) fun u hu ↦ (hZ u hu).ne').pow 2)

/-- **The Jensen-gap identity**: for `0 < s < t` and `m = (s+t)/2`,
`(F(s) + F(t))/2 − F(m) = ½ (∫_s^m (u − s) Var_u du + ∫_m^t (t − u) Var_u du)`. -/
theorem bhattacharyya_eq_integral_var (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ) {K : ℕ}
    (hint : ∀ v > 0, ∀ k ≤ K, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν) (hK : 3 ≤ K)
    (hZ : ∀ u > 0, 0 < lawMoment ν 0 u) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    (Real.log (lawMoment ν 0 s) + Real.log (lawMoment ν 0 t)) / 2 -
        Real.log (lawMoment ν 0 ((s + t) / 2)) =
      (1 / 2) * ((∫ u in s..(s + t) / 2, (u - s) * lawVar ν u) +
        ∫ u in (s + t) / 2..t, (t - u) * lawVar ν u) := by
  set m := (s + t) / 2 with hm
  have hsm : s ≤ m := by rw [hm]; linarith
  have hmt : m ≤ t := by rw [hm]; linarith
  have hm0 : 0 < m := by linarith
  -- the mean and its derivative
  have hmean : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt (fun v ↦ lawMoment ν 1 v / lawMoment ν 0 v)
      (-(lawVar ν u)) u := fun u hu ↦ hasDerivAt_lawMean ν hpos hint (by omega) hu (hZ u hu)
  have hF : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt (fun v ↦ Real.log (lawMoment ν 0 v))
      (-(lawMoment ν 1 u / lawMoment ν 0 u)) u := fun u hu ↦
    hasDerivAt_lawLogZ ν hpos hint (by omega) hu (hZ u hu)
  have hVc := continuousOn_lawVar ν hpos hint hK hZ
  have hmeanc : ContinuousOn (fun v ↦ lawMoment ν 1 v / lawMoment ν 0 v) (Ioi 0) :=
    fun u hu ↦ (hmean u hu).continuousAt.continuousWithinAt
  -- left piece via IBP on `(u − s) · (−mean)'`
  have hsub1 : uIcc s m ⊆ Ioi 0 := by
    rw [uIcc_of_le hsm]
    exact fun u hu ↦ lt_of_lt_of_le hs hu.1
  have hsub2 : uIcc m t ⊆ Ioi 0 := by
    rw [uIcc_of_le hmt]
    exact fun u hu ↦ lt_of_lt_of_le hm0 hu.1
  have left : (∫ u in s..m, (u - s) * lawVar ν u) =
      -((m - s) * (lawMoment ν 1 m / lawMoment ν 0 m)) +
        (Real.log (lawMoment ν 0 s) - Real.log (lawMoment ν 0 m)) := by
    -- `∫ (u−s) · Var = −∫ (u−s) · mean'`
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := s) (b := m)
      (u := fun u ↦ u - s) (v := fun v ↦ lawMoment ν 1 v / lawMoment ν 0 v)
      (u' := fun _ ↦ 1) (v' := fun u ↦ -(lawVar ν u))
      (fun u _ ↦ (hasDerivAt_id u).sub_const s) (fun u hu ↦ hmean u (hsub1 hu))
      (continuous_const.intervalIntegrable (μ := volume) s m)
      ((hVc.mono hsub1).neg.intervalIntegrable)
    have hFTC : (∫ u in s..m, lawMoment ν 1 u / lawMoment ν 0 u) =
        -(Real.log (lawMoment ν 0 m) - Real.log (lawMoment ν 0 s)) := by
      have := integral_eq_sub_of_hasDerivAt (f := fun v ↦ Real.log (lawMoment ν 0 v))
        (f' := fun u ↦ -(lawMoment ν 1 u / lawMoment ν 0 u)) (fun u hu ↦ hF u (hsub1 hu))
        (hmeanc.mono hsub1).neg.intervalIntegrable
      rw [intervalIntegral.integral_neg] at this
      linarith
    simp only [sub_self, zero_mul, one_mul, sub_zero] at hibp
    have e : (∫ u in s..m, (u - s) * lawVar ν u) = -∫ u in s..m, (u - s) * -(lawVar ν u) := by
      rw [← intervalIntegral.integral_neg]
      refine integral_congr fun u _ ↦ ?_
      ring
    rw [e, hibp, hFTC]
    ring
  have right : (∫ u in m..t, (t - u) * lawVar ν u) =
      (t - m) * (lawMoment ν 1 m / lawMoment ν 0 m) +
        (Real.log (lawMoment ν 0 t) - Real.log (lawMoment ν 0 m)) := by
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := m) (b := t)
      (u := fun u ↦ t - u) (v := fun v ↦ lawMoment ν 1 v / lawMoment ν 0 v)
      (u' := fun _ ↦ -1) (v' := fun u ↦ -(lawVar ν u))
      (fun u _ ↦ (hasDerivAt_id u).const_sub t) (fun u hu ↦ hmean u (hsub2 hu))
      (continuous_const.intervalIntegrable (μ := volume) m t)
      ((hVc.mono hsub2).neg.intervalIntegrable)
    have hFTC : (∫ u in m..t, -1 * (lawMoment ν 1 u / lawMoment ν 0 u)) =
        Real.log (lawMoment ν 0 t) - Real.log (lawMoment ν 0 m) := by
      have := integral_eq_sub_of_hasDerivAt (f := fun v ↦ Real.log (lawMoment ν 0 v))
        (f' := fun u ↦ -(lawMoment ν 1 u / lawMoment ν 0 u)) (fun u hu ↦ hF u (hsub2 hu))
        (hmeanc.mono hsub2).neg.intervalIntegrable
      rw [← this]
      refine integral_congr fun u _ ↦ ?_
      ring
    have e : (∫ u in m..t, (t - u) * lawVar ν u) = -∫ u in m..t, (t - u) * -(lawVar ν u) := by
      rw [← intervalIntegral.integral_neg]
      refine integral_congr fun u _ ↦ ?_
      ring
    simp only [sub_self, zero_mul, zero_sub] at hibp
    rw [e, hibp, hFTC]
    ring
  rw [left, right, hm]
  ring

/-- **The square-root speed**: `∂_u √p_u(ℓ) = −½ (ℓ − ⟨ℓ⟩_u) √p_u(ℓ)`. -/
theorem hasDerivAt_sqrt_lawDensity (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ) {K : ℕ}
    (hint : ∀ v > 0, ∀ k ≤ K, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν) (hK : 1 ≤ K)
    {u : ℝ} (hu : 0 < u) (hZ : 0 < lawMoment ν 0 u) (ℓ : ℝ) :
    HasDerivAt (fun v ↦ Real.sqrt (lawDensity ν v ℓ))
      (-(1 / 2) * (ℓ - lawMoment ν 1 u / lawMoment ν 0 u) * Real.sqrt (lawDensity ν u ℓ)) u := by
  have hZ' := hasDerivAt_lawMoment ν hpos hint (k := 0) hK hu
  have he : HasDerivAt (fun v : ℝ ↦ Real.exp (-(v * ℓ))) (Real.exp (-(u * ℓ)) * -ℓ) u :=
    (hasDerivAt_mul_const ℓ).neg.exp
  have hp : HasDerivAt (fun v ↦ lawDensity ν v ℓ)
      (-(ℓ - lawMoment ν 1 u / lawMoment ν 0 u) * lawDensity ν u ℓ) u := by
    have := he.div hZ' hZ.ne'
    refine this.congr_deriv ?_
    unfold lawDensity
    field_simp
    ring
  have hpos' : 0 < lawDensity ν u ℓ := by
    unfold lawDensity
    positivity
  have := hp.sqrt hpos'.ne'
  refine this.congr_deriv ?_
  have hsq : Real.sqrt (lawDensity ν u ℓ) ^ 2 = lawDensity ν u ℓ := Real.sq_sqrt hpos'.le
  have hs0 : Real.sqrt (lawDensity ν u ℓ) ≠ 0 := (Real.sqrt_pos.mpr hpos').ne'
  rw [div_eq_iff (by positivity)]
  linear_combination (ℓ - lawMoment ν 1 u / lawMoment ν 0 u) * hsq

/-- **The squared square-root speed is `Var_u(ℓ)/4`**: `∫ (½(ℓ − ⟨ℓ⟩_u))² p_u dν = Var_u/4`. -/
theorem integral_sq_sqrt_speed (ν : Measure ℝ) {u : ℝ} (hZ : 0 < lawMoment ν 0 u)
    (h0 : Integrable (fun ℓ ↦ Real.exp (-(u * ℓ))) ν)
    (h1 : Integrable (fun ℓ ↦ ℓ * Real.exp (-(u * ℓ))) ν)
    (h2 : Integrable (fun ℓ ↦ ℓ * ℓ * Real.exp (-(u * ℓ))) ν) :
    ∫ ℓ, (-(1 / 2) * (ℓ - lawMoment ν 1 u / lawMoment ν 0 u) * Real.sqrt (lawDensity ν u ℓ)) ^ 2 ∂ν
      = lawVar ν u / 4 := by
  set m := lawMoment ν 1 u / lawMoment ν 0 u with hm
  have e : ∀ ℓ, (-(1 / 2) * (ℓ - m) * Real.sqrt (lawDensity ν u ℓ)) ^ 2 =
      (1 / (4 * lawMoment ν 0 u)) * (ℓ * ℓ * Real.exp (-(u * ℓ))) -
        (m / (2 * lawMoment ν 0 u)) * (ℓ * Real.exp (-(u * ℓ))) +
        (m ^ 2 / (4 * lawMoment ν 0 u)) * Real.exp (-(u * ℓ)) := fun ℓ ↦ by
    have hp : 0 ≤ lawDensity ν u ℓ := by unfold lawDensity; positivity
    rw [mul_pow, Real.sq_sqrt hp]
    unfold lawDensity
    field_simp
    ring
  simp_rw [e]
  have I2 : Integrable (fun ℓ ↦ (1 / (4 * lawMoment ν 0 u)) * (ℓ * ℓ * Real.exp (-(u * ℓ)))) ν :=
    h2.const_mul _
  have I1 : Integrable (fun ℓ ↦ (m / (2 * lawMoment ν 0 u)) * (ℓ * Real.exp (-(u * ℓ)))) ν :=
    h1.const_mul _
  have I0 : Integrable (fun ℓ ↦ (m ^ 2 / (4 * lawMoment ν 0 u)) * Real.exp (-(u * ℓ))) ν :=
    h0.const_mul _
  have I21 : Integrable (fun ℓ ↦ (1 / (4 * lawMoment ν 0 u)) * (ℓ * ℓ * Real.exp (-(u * ℓ))) -
      (m / (2 * lawMoment ν 0 u)) * (ℓ * Real.exp (-(u * ℓ)))) ν := I2.sub I1
  rw [integral_add I21 I0, integral_sub I2 I1, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  unfold lawVar lawExp
  have e2 : (∫ ℓ, ℓ * ℓ * Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 2 u :=
    integral_congr_ae (Filter.Eventually.of_forall fun ℓ ↦ by ring)
  have e1 : (∫ ℓ, ℓ * Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 1 u := by simp [lawMoment]
  have e0 : (∫ ℓ, Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 0 u := by simp [lawMoment]
  rw [e2, e1, e0, hm]
  field_simp
  ring

end Laplace.Multi
