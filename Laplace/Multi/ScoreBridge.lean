/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ResponseMap

/-!
# The score-weighted asymptotic bridge

At finite `t` the response of the posterior to a data direction is `−t Cov_{t,a}(φ, D_v L_a)`
(`ResponseMap`); in the singular limit it is `−Cov_{μ̄_a}(φ, S_v)` with the rescaled score `S_v`
(`TermScoreResponse`). Astra's round-21 interface between the two layers is the **four-integral
bridge**: if, for a normalisation `A_t > 0` and (possibly rescaled) observables `φ_t`, the four
normalised integrals

  `A_t ∫ 1 dρ_t → M₀ > 0`,  `A_t ∫ φ_t dρ_t → M_φ`,  `A_t ∫ Q_t dρ_t → M_S`,
  `A_t ∫ φ_t Q_t dρ_t → M_{φS}`,   with `Q_t = t D_v L_a` the physical score,

then `t Cov_{ρ_t}(φ_t, D_v L_a) → M_{φS}/M₀ − (M_φ/M₀)(M_S/M₀)`, the covariance under the
limiting law (`tendsto_scaled_cov_of_four`). This is quotient-limit algebra; all the analysis is
in the four convergences, which the term theorems of the atlas must supply for the score-weighted
observables. The **regular model** `L_a(w) = a w^p` on `(0, ∞)` is the instance where the bridge
is an identity: under `y = t^{1/p} w` the posterior is `t`-independent and the physical score
`t · v w^p` is exactly `v y^p`, so the finite-`t` response of a scaled observable equals the
limiting response for every `t` (`regular_scaled_cov_eq`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-! ### The abstract four-integral bridge -/

/-- The scaled covariance built from the three normalised integrals. -/
theorem tendsto_scaled_cov_of_four {ι : Type*} {l : Filter ι} {A Z N NS NQ : ι → ℝ}
    {M₀ Mφ MS MφS : ℝ} (hM₀ : 0 < M₀) (hZ : Tendsto (fun i ↦ A i * Z i) l (𝓝 M₀))
    (hN : Tendsto (fun i ↦ A i * N i) l (𝓝 Mφ)) (hQ : Tendsto (fun i ↦ A i * NQ i) l (𝓝 MS))
    (hNS : Tendsto (fun i ↦ A i * NS i) l (𝓝 MφS)) :
    Tendsto (fun i ↦ NS i / Z i - N i / Z i * (NQ i / Z i)) l
      (𝓝 (MφS / M₀ - Mφ / M₀ * (MS / M₀))) := by
  have h1 : Tendsto (fun i ↦ A i * NS i / (A i * Z i)) l (𝓝 (MφS / M₀)) := hNS.div hZ hM₀.ne'
  have h2 : Tendsto (fun i ↦ A i * N i / (A i * Z i)) l (𝓝 (Mφ / M₀)) := hN.div hZ hM₀.ne'
  have h3 : Tendsto (fun i ↦ A i * NQ i / (A i * Z i)) l (𝓝 (MS / M₀)) := hQ.div hZ hM₀.ne'
  have := h1.sub (h2.mul h3)
  refine this.congr' ?_
  have hev : ∀ᶠ i in l, A i * Z i ≠ 0 := by
    have := hZ.eventually_ne hM₀.ne'
    exact this
  filter_upwards [hev] with i hi
  have hA : A i ≠ 0 := left_ne_zero_of_mul hi
  have hZi : Z i ≠ 0 := right_ne_zero_of_mul hi
  field_simp

/-- **The four-integral bridge** for a family of Gibbs laws `ρ_t = e^{-tL} π` with physical score
`Q_t = t D_v L` and scaled observables `φ_t`: the finite-`t` response
`−t Cov_{ρ_t}(φ_t, D_vL) = −(⟨φ_t Q_t⟩ − ⟨φ_t⟩⟨Q_t⟩)` converges to minus the covariance of the
limiting law. -/
theorem tendsto_response_of_four {X : Type*} [MeasurableSpace X] {μ : Measure X} {π : X → ℝ}
    {L DL : X → ℝ} {φ : ℝ → X → ℝ} {A : ℝ → ℝ} {M₀ Mφ MS MφS : ℝ} (hM₀ : 0 < M₀)
    (hZ : Tendsto (fun t ↦ A t * priorZ μ π L t) atTop (𝓝 M₀))
    (hN : Tendsto (fun t ↦ A t * ∫ x, φ t x * Real.exp (-(t * L x)) * π x ∂μ) atTop (𝓝 Mφ))
    (hQ : Tendsto (fun t ↦ A t * ∫ x, (t * DL x) * Real.exp (-(t * L x)) * π x ∂μ) atTop (𝓝 MS))
    (hNS : Tendsto (fun t ↦ A t * ∫ x, φ t x * (t * DL x) * Real.exp (-(t * L x)) * π x ∂μ)
      atTop (𝓝 MφS)) :
    Tendsto (fun t ↦ -(t * priorCov μ π L (φ t) DL t)) atTop
      (𝓝 (-(MφS / M₀ - Mφ / M₀ * (MS / M₀)))) := by
  have key := tendsto_scaled_cov_of_four (l := atTop) (A := A) (Z := fun t ↦ priorZ μ π L t)
    (N := fun t ↦ ∫ x, φ t x * Real.exp (-(t * L x)) * π x ∂μ)
    (NS := fun t ↦ ∫ x, φ t x * (t * DL x) * Real.exp (-(t * L x)) * π x ∂μ)
    (NQ := fun t ↦ ∫ x, (t * DL x) * Real.exp (-(t * L x)) * π x ∂μ) hM₀ hZ hN hQ hNS
  refine key.neg.congr' (Filter.Eventually.of_forall fun t ↦ ?_)
  simp only [priorCov, priorExp]
  have e1 : (∫ x, φ t x * (t * DL x) * Real.exp (-(t * L x)) * π x ∂μ) =
      t * ∫ x, (fun x ↦ φ t x * DL x) x * Real.exp (-(t * L x)) * π x ∂μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by ring)
  have e2 : (∫ x, (t * DL x) * Real.exp (-(t * L x)) * π x ∂μ) =
      t * ∫ x, DL x * Real.exp (-(t * L x)) * π x ∂μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by ring)
  rw [e1, e2]
  ring

/-! ### The regular model `L_a(w) = a w^p`: the bridge is an identity -/

/-- The scaled Gibbs numerator of the regular model: `∫₀^∞ g(t^{1/p} w) e^{-t a w^p} dw`. -/
theorem regular_scaled_integral {p a t : ℝ} (hp : 0 < p) (ht : 0 < t) (g : ℝ → ℝ) :
    ∫ w in Ioi (0 : ℝ), g (t ^ (1 / p) * w) * Real.exp (-(t * (a * w ^ p))) =
      t ^ (-(1 / p)) * ∫ y in Ioi (0 : ℝ), g y * Real.exp (-(a * y ^ p)) := by
  have hc : 0 < t ^ (1 / p) := Real.rpow_pos_of_pos ht _
  have key := integral_comp_mul_left_Ioi (fun y ↦ g y * Real.exp (-(a * y ^ p))) (0 : ℝ) hc
  rw [mul_zero, smul_eq_mul, ← Real.rpow_neg ht.le] at key
  rw [← key]
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ ?_
  have hw0 : (0 : ℝ) < w := hw
  congr 2
  rw [Real.mul_rpow hc.le hw0.le, ← Real.rpow_mul ht.le, one_div_mul_cancel hp.ne',
    Real.rpow_one]
  ring

/-- **The regular model bridge is exact**: for a scaled observable `ψ(t^{1/p} w)` and the physical
score `t · v w^p`, the finite-`t` scaled covariance under `e^{-t a w^p}` equals the covariance of
`ψ(y)` and `v y^p` under the limiting law `e^{-a y^p}`, for every `t > 0`. -/
theorem regular_scaled_cov_eq {p a t v : ℝ} (hp : 0 < p) (ht : 0 < t) (ψ : ℝ → ℝ)
    (hZ : (∫ y in Ioi (0 : ℝ), Real.exp (-(a * y ^ p))) ≠ 0) :
    t * priorCov (volume.restrict (Ioi 0)) (fun _ ↦ 1) (fun w ↦ a * w ^ p)
        (fun w ↦ ψ (t ^ (1 / p) * w)) (fun w ↦ v * w ^ p) t =
      priorCov (volume.restrict (Ioi 0)) (fun _ ↦ 1) (fun y ↦ a * y ^ p) ψ
        (fun y ↦ v * y ^ p) 1 := by
  have hc : 0 < t ^ (1 / p) := Real.rpow_pos_of_pos ht _
  have hpow : ∀ w : ℝ, 0 < w → t * (v * w ^ p) = v * (t ^ (1 / p) * w) ^ p := fun w hw ↦ by
    rw [Real.mul_rpow hc.le hw.le, ← Real.rpow_mul ht.le, one_div_mul_cancel hp.ne',
      Real.rpow_one]
    ring
  simp only [priorCov, priorExp, priorZ, mul_one, one_mul]
  -- the four integrals of the scaled model
  have hZ' := regular_scaled_integral (a := a) hp ht (fun _ ↦ (1 : ℝ))
  have hN := regular_scaled_integral (a := a) hp ht ψ
  have hQ := regular_scaled_integral (a := a) hp ht (fun y ↦ v * y ^ p)
  have hNS := regular_scaled_integral (a := a) hp ht (fun y ↦ ψ y * (v * y ^ p))
  simp only [one_mul] at hZ'
  -- rewrite the finite-`t` integrals into scaled form
  have e1 : (∫ w in Ioi (0 : ℝ), Real.exp (-(t * (a * w ^ p)))) =
      t ^ (-(1 / p)) * ∫ y in Ioi (0 : ℝ), Real.exp (-(a * y ^ p)) := hZ'
  have e2 : (∫ w in Ioi (0 : ℝ), ψ (t ^ (1 / p) * w) * Real.exp (-(t * (a * w ^ p)))) =
      t ^ (-(1 / p)) * ∫ y in Ioi (0 : ℝ), ψ y * Real.exp (-(a * y ^ p)) := hN
  have e3 : (∫ w in Ioi (0 : ℝ), v * w ^ p * Real.exp (-(t * (a * w ^ p)))) =
      t ^ (-(1 / p)) * t⁻¹ * ∫ y in Ioi (0 : ℝ), v * y ^ p * Real.exp (-(a * y ^ p)) := by
    rw [show t ^ (-(1 / p)) * t⁻¹ * (∫ y in Ioi (0 : ℝ), v * y ^ p * Real.exp (-(a * y ^ p))) =
      t⁻¹ * (t ^ (-(1 / p)) * ∫ y in Ioi (0 : ℝ), v * y ^ p * Real.exp (-(a * y ^ p))) by ring,
      ← hQ, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ ?_
    have hw0 : (0 : ℝ) < w := hw
    rw [← hpow w hw0]
    field_simp
  have e4 : (∫ w in Ioi (0 : ℝ), ψ (t ^ (1 / p) * w) * (v * w ^ p) *
      Real.exp (-(t * (a * w ^ p)))) =
      t ^ (-(1 / p)) * t⁻¹ * ∫ y in Ioi (0 : ℝ), ψ y * (v * y ^ p) * Real.exp (-(a * y ^ p)) := by
    rw [show t ^ (-(1 / p)) * t⁻¹ *
        (∫ y in Ioi (0 : ℝ), ψ y * (v * y ^ p) * Real.exp (-(a * y ^ p))) =
      t⁻¹ * (t ^ (-(1 / p)) * ∫ y in Ioi (0 : ℝ), ψ y * (v * y ^ p) * Real.exp (-(a * y ^ p)))
      by ring, ← hNS, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ ?_
    have hw0 : (0 : ℝ) < w := hw
    rw [← hpow w hw0]
    field_simp
  rw [e1, e2, e3, e4]
  have hpt : t ^ (-(1 / p)) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  set Z' := ∫ y in Ioi (0 : ℝ), Real.exp (-(a * y ^ p)) with hZ'def
  set N' := ∫ y in Ioi (0 : ℝ), ψ y * Real.exp (-(a * y ^ p)) with hN'def
  set Q' := ∫ y in Ioi (0 : ℝ), v * y ^ p * Real.exp (-(a * y ^ p)) with hQ'def
  set NS' := ∫ y in Ioi (0 : ℝ), ψ y * (v * y ^ p) * Real.exp (-(a * y ^ p)) with hNS'def
  clear_value Z' N' Q' NS'
  field_simp

end Laplace.Multi
