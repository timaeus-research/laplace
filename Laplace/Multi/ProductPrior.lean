/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.StateDensity

/-!
# Product priors: the radial length of a sum of independent losses

For a product prior `π₁ ⊗ π₂` on `X × Y` and a separable loss `L₁(x) + L₂(y)` the featureless-line
posterior factorises, so the radial variance is additive, `Var_u(L₁ + L₂) = Var_u(L₁) + Var_u(L₂)`
(`priorCov_self_prod`), and the radial length `D_t(L) = ∫₀ᵗ √Var_u` obeys the **product-prior
inequality** (Astra round 25 item 6)

  `√(D_t(L₁)² + D_t(L₂)²) ≤ D_t(L₁ + L₂) ≤ D_t(L₁) + D_t(L₂)`

(`sqrt_sq_add_sq_le_radialLength_prod`, `radialLength_prod_le`): the `ℓ²` and `ℓ¹` combinations of
the factor lengths bracket the length of the product, with equality on the left iff the two speed
profiles are proportional and on the right iff one of them vanishes.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-! ### Scalar inequalities -/

/-- `√(x + y) ≤ √x + √y` for all reals (Mathlib's square root vanishes on negatives). -/
theorem sqrt_add_le_sqrt_add_sqrt (x y : ℝ) : Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rcases le_or_gt x 0 with hx | hx
  · rw [Real.sqrt_eq_zero'.mpr hx, zero_add]
    exact Real.sqrt_le_sqrt (by linarith)
  rcases le_or_gt y 0 with hy | hy
  · rw [Real.sqrt_eq_zero'.mpr hy, add_zero]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le, Real.sqrt_nonneg x, Real.sqrt_nonneg y]

/-- Two-dimensional Cauchy–Schwarz in square-root form:
`a √x + b √y ≤ √(a² + b²) √(x + y)` for `x, y ≥ 0`. -/
theorem mul_sqrt_add_mul_sqrt_le (a b : ℝ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    a * Real.sqrt x + b * Real.sqrt y ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (x + y) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  nlinarith [sq_nonneg (a * Real.sqrt y - b * Real.sqrt x), Real.sq_sqrt hx, Real.sq_sqrt hy]

/-! ### Abstract length inequalities -/

/-- `∫₀ᵗ √(V₁ + V₂) ≤ ∫₀ᵗ √V₁ + ∫₀ᵗ √V₂` for continuous variance profiles. -/
theorem integral_sqrt_add_le {V₁ V₂ : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (h₁ : ContinuousOn V₁ (Icc 0 t)) (h₂ : ContinuousOn V₂ (Icc 0 t)) :
    (∫ u in (0 : ℝ)..t, Real.sqrt (V₁ u + V₂ u)) ≤
      (∫ u in (0 : ℝ)..t, Real.sqrt (V₁ u)) + ∫ u in (0 : ℝ)..t, Real.sqrt (V₂ u) := by
  have hI₁ : IntervalIntegrable (fun u ↦ Real.sqrt (V₁ u)) volume 0 t :=
    (Real.continuous_sqrt.comp_continuousOn h₁).intervalIntegrable_of_Icc ht
  have hI₂ : IntervalIntegrable (fun u ↦ Real.sqrt (V₂ u)) volume 0 t :=
    (Real.continuous_sqrt.comp_continuousOn h₂).intervalIntegrable_of_Icc ht
  have hI : IntervalIntegrable (fun u ↦ Real.sqrt (V₁ u + V₂ u)) volume 0 t :=
    (Real.continuous_sqrt.comp_continuousOn (h₁.add h₂)).intervalIntegrable_of_Icc ht
  rw [← intervalIntegral.integral_add hI₁ hI₂]
  exact intervalIntegral.integral_mono_on ht hI (hI₁.add hI₂) fun u _ ↦
    sqrt_add_le_sqrt_add_sqrt _ _

/-- `√((∫₀ᵗ √V₁)² + (∫₀ᵗ √V₂)²) ≤ ∫₀ᵗ √(V₁ + V₂)` for continuous nonnegative variance profiles
(Minkowski for the `ℝ²`-valued speed `(√V₁, √V₂)`, proved by scalar Cauchy–Schwarz). -/
theorem sqrt_sq_add_sq_le_integral_sqrt_add {V₁ V₂ : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (h₁ : ContinuousOn V₁ (Icc 0 t)) (h₂ : ContinuousOn V₂ (Icc 0 t))
    (hn₁ : ∀ u ∈ Icc 0 t, 0 ≤ V₁ u) (hn₂ : ∀ u ∈ Icc 0 t, 0 ≤ V₂ u) :
    Real.sqrt ((∫ u in (0 : ℝ)..t, Real.sqrt (V₁ u)) ^ 2 +
        (∫ u in (0 : ℝ)..t, Real.sqrt (V₂ u)) ^ 2) ≤
      ∫ u in (0 : ℝ)..t, Real.sqrt (V₁ u + V₂ u) := by
  set D₁ := ∫ u in (0 : ℝ)..t, Real.sqrt (V₁ u) with hD₁
  set D₂ := ∫ u in (0 : ℝ)..t, Real.sqrt (V₂ u) with hD₂
  set D := ∫ u in (0 : ℝ)..t, Real.sqrt (V₁ u + V₂ u) with hD
  have hI₁ : IntervalIntegrable (fun u ↦ Real.sqrt (V₁ u)) volume 0 t :=
    (Real.continuous_sqrt.comp_continuousOn h₁).intervalIntegrable_of_Icc ht
  have hI₂ : IntervalIntegrable (fun u ↦ Real.sqrt (V₂ u)) volume 0 t :=
    (Real.continuous_sqrt.comp_continuousOn h₂).intervalIntegrable_of_Icc ht
  have hI : IntervalIntegrable (fun u ↦ Real.sqrt (V₁ u + V₂ u)) volume 0 t :=
    (Real.continuous_sqrt.comp_continuousOn (h₁.add h₂)).intervalIntegrable_of_Icc ht
  have hD0 : 0 ≤ D :=
    intervalIntegral.integral_nonneg ht fun u _ ↦ Real.sqrt_nonneg _
  set S := D₁ ^ 2 + D₂ ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  -- the key inequality `S ≤ √S · D`
  have key : S ≤ Real.sqrt S * D := by
    have e : S = ∫ u in (0 : ℝ)..t, (D₁ * Real.sqrt (V₁ u) + D₂ * Real.sqrt (V₂ u)) := by
      rw [intervalIntegral.integral_add (hI₁.const_mul _) (hI₂.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hS, ← hD₁, ← hD₂]
      ring
    calc S = ∫ u in (0 : ℝ)..t, (D₁ * Real.sqrt (V₁ u) + D₂ * Real.sqrt (V₂ u)) := e
      _ ≤ ∫ u in (0 : ℝ)..t, Real.sqrt S * Real.sqrt (V₁ u + V₂ u) := by
          refine intervalIntegral.integral_mono_on ht ((hI₁.const_mul _).add (hI₂.const_mul _))
            (hI.const_mul _) fun u hu ↦ ?_
          rw [hS]
          exact mul_sqrt_add_mul_sqrt_le D₁ D₂ (hn₁ u hu) (hn₂ u hu)
      _ = Real.sqrt S * D := by rw [intervalIntegral.integral_const_mul]
  rcases eq_or_lt_of_le hS0 with h0 | hpos
  · rw [← h0, Real.sqrt_zero]; exact hD0
  · have hsq : 0 < Real.sqrt S := Real.sqrt_pos.mpr hpos
    have : Real.sqrt S * Real.sqrt S ≤ Real.sqrt S * D := by
      rw [Real.mul_self_sqrt hS0]; exact key
    exact le_of_mul_le_mul_left this hsq

/-! ### Product priors and separable losses -/

theorem mean_ratio_alg {n₁ z₁ n₂ z₂ : ℝ} (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) :
    (n₁ * z₂ + z₁ * n₂) / (z₁ * z₂) = n₁ / z₁ + n₂ / z₂ := by
  field_simp

theorem var_ratio_alg {m₁ n₁ z₁ m₂ n₂ z₂ : ℝ} (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) :
    (m₁ * z₂ + 2 * (n₁ * n₂) + z₁ * m₂) / (z₁ * z₂) -
        (n₁ / z₁ + n₂ / z₂) * (n₁ / z₁ + n₂ / z₂) =
      (m₁ / z₁ - n₁ / z₁ * (n₁ / z₁)) + (m₂ / z₂ - n₂ / z₂ * (n₂ / z₂)) := by
  field_simp
  ring

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ₁ : Measure X} {μ₂ : Measure Y}
  [SFinite μ₁] [SFinite μ₂]

/-- The product prior `π₁(x) π₂(y)`. -/
def prodPrior (π₁ : X → ℝ) (π₂ : Y → ℝ) : X × Y → ℝ := fun p ↦ π₁ p.1 * π₂ p.2

/-- The separable loss `L₁(x) + L₂(y)`. -/
def sumLoss (L₁ : X → ℝ) (L₂ : Y → ℝ) : X × Y → ℝ := fun p ↦ L₁ p.1 + L₂ p.2

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem prod_weight_eq (π₁ L₁ : X → ℝ) (π₂ L₂ : Y → ℝ) (u : ℝ) (p : X × Y) :
    Real.exp (-(u * sumLoss L₁ L₂ p)) * prodPrior π₁ π₂ p =
      (Real.exp (-(u * L₁ p.1)) * π₁ p.1) * (Real.exp (-(u * L₂ p.2)) * π₂ p.2) := by
  unfold sumLoss prodPrior
  rw [show -(u * (L₁ p.1 + L₂ p.2)) = -(u * L₁ p.1) + -(u * L₂ p.2) by ring, Real.exp_add]
  ring

/-- The partition function of a product prior with separable loss factorises. -/
theorem priorZ_prod (π₁ L₁ : X → ℝ) (π₂ L₂ : Y → ℝ) (u : ℝ) :
    priorZ (μ₁.prod μ₂) (prodPrior π₁ π₂) (sumLoss L₁ L₂) u =
      priorZ μ₁ π₁ L₁ u * priorZ μ₂ π₂ L₂ u := by
  unfold priorZ
  simp_rw [prod_weight_eq]
  exact integral_prod_mul (fun x ↦ Real.exp (-(u * L₁ x)) * π₁ x)
    (fun y ↦ Real.exp (-(u * L₂ y)) * π₂ y)

section Moments

variable {π₁ L₁ : X → ℝ} {π₂ L₂ : Y → ℝ} {u : ℝ}
  (hZ₁ : Integrable (fun x ↦ Real.exp (-(u * L₁ x)) * π₁ x) μ₁)
  (hZ₂ : Integrable (fun y ↦ Real.exp (-(u * L₂ y)) * π₂ y) μ₂)
  (hN₁ : Integrable (fun x ↦ L₁ x * Real.exp (-(u * L₁ x)) * π₁ x) μ₁)
  (hN₂ : Integrable (fun y ↦ L₂ y * Real.exp (-(u * L₂ y)) * π₂ y) μ₂)
include hZ₁ hZ₂ hN₁ hN₂

/-- The first-moment numerator of the sum: `∫ (L₁+L₂) e π = N₁ Z₂ + Z₁ N₂`. -/
theorem prod_num_add :
    (∫ p, sumLoss L₁ L₂ p * Real.exp (-(u * sumLoss L₁ L₂ p)) * prodPrior π₁ π₂ p ∂μ₁.prod μ₂) =
      (∫ x, L₁ x * Real.exp (-(u * L₁ x)) * π₁ x ∂μ₁) * (∫ y, Real.exp (-(u * L₂ y)) * π₂ y ∂μ₂) +
      (∫ x, Real.exp (-(u * L₁ x)) * π₁ x ∂μ₁) * ∫ y, L₂ y * Real.exp (-(u * L₂ y)) * π₂ y ∂μ₂ := by
  have e : ∀ p : X × Y, sumLoss L₁ L₂ p * Real.exp (-(u * sumLoss L₁ L₂ p)) * prodPrior π₁ π₂ p =
      (L₁ p.1 * Real.exp (-(u * L₁ p.1)) * π₁ p.1) * (Real.exp (-(u * L₂ p.2)) * π₂ p.2) +
      (Real.exp (-(u * L₁ p.1)) * π₁ p.1) * (L₂ p.2 * Real.exp (-(u * L₂ p.2)) * π₂ p.2) := by
    intro p
    rw [mul_assoc, prod_weight_eq]
    unfold sumLoss
    ring
  simp_rw [e]
  rw [integral_add (hN₁.mul_prod hZ₂) (hZ₁.mul_prod hN₂),
    integral_prod_mul (fun x ↦ L₁ x * Real.exp (-(u * L₁ x)) * π₁ x)
      (fun y ↦ Real.exp (-(u * L₂ y)) * π₂ y),
    integral_prod_mul (fun x ↦ Real.exp (-(u * L₁ x)) * π₁ x)
      (fun y ↦ L₂ y * Real.exp (-(u * L₂ y)) * π₂ y)]

end Moments

section Var

variable {π₁ L₁ : X → ℝ} {π₂ L₂ : Y → ℝ} {u : ℝ}
  (hZ₁ : Integrable (fun x ↦ Real.exp (-(u * L₁ x)) * π₁ x) μ₁)
  (hZ₂ : Integrable (fun y ↦ Real.exp (-(u * L₂ y)) * π₂ y) μ₂)
  (hN₁ : Integrable (fun x ↦ L₁ x * Real.exp (-(u * L₁ x)) * π₁ x) μ₁)
  (hN₂ : Integrable (fun y ↦ L₂ y * Real.exp (-(u * L₂ y)) * π₂ y) μ₂)
  (hM₁ : Integrable (fun x ↦ L₁ x * L₁ x * Real.exp (-(u * L₁ x)) * π₁ x) μ₁)
  (hM₂ : Integrable (fun y ↦ L₂ y * L₂ y * Real.exp (-(u * L₂ y)) * π₂ y) μ₂)
include hZ₁ hZ₂ hN₁ hN₂ hM₁ hM₂

/-- The second-moment numerator of the sum: `∫ (L₁+L₂)² e π = M₁ Z₂ + 2 N₁ N₂ + Z₁ M₂`. -/
theorem prod_num_sq :
    (∫ p, sumLoss L₁ L₂ p * sumLoss L₁ L₂ p * Real.exp (-(u * sumLoss L₁ L₂ p)) *
        prodPrior π₁ π₂ p ∂μ₁.prod μ₂) =
      (∫ x, L₁ x * L₁ x * Real.exp (-(u * L₁ x)) * π₁ x ∂μ₁) *
          (∫ y, Real.exp (-(u * L₂ y)) * π₂ y ∂μ₂) +
      2 * ((∫ x, L₁ x * Real.exp (-(u * L₁ x)) * π₁ x ∂μ₁) *
          ∫ y, L₂ y * Real.exp (-(u * L₂ y)) * π₂ y ∂μ₂) +
      (∫ x, Real.exp (-(u * L₁ x)) * π₁ x ∂μ₁) *
          ∫ y, L₂ y * L₂ y * Real.exp (-(u * L₂ y)) * π₂ y ∂μ₂ := by
  have e : ∀ p : X × Y, sumLoss L₁ L₂ p * sumLoss L₁ L₂ p * Real.exp (-(u * sumLoss L₁ L₂ p)) *
      prodPrior π₁ π₂ p =
      ((L₁ p.1 * L₁ p.1 * Real.exp (-(u * L₁ p.1)) * π₁ p.1) *
          (Real.exp (-(u * L₂ p.2)) * π₂ p.2) +
        2 * ((L₁ p.1 * Real.exp (-(u * L₁ p.1)) * π₁ p.1) *
          (L₂ p.2 * Real.exp (-(u * L₂ p.2)) * π₂ p.2))) +
      (Real.exp (-(u * L₁ p.1)) * π₁ p.1) *
        (L₂ p.2 * L₂ p.2 * Real.exp (-(u * L₂ p.2)) * π₂ p.2) := by
    intro p
    rw [mul_assoc, prod_weight_eq]
    unfold sumLoss
    ring
  simp_rw [e]
  have h12 : Integrable (fun p : X × Y ↦
      (L₁ p.1 * L₁ p.1 * Real.exp (-(u * L₁ p.1)) * π₁ p.1) * (Real.exp (-(u * L₂ p.2)) * π₂ p.2) +
        2 * ((L₁ p.1 * Real.exp (-(u * L₁ p.1)) * π₁ p.1) *
          (L₂ p.2 * Real.exp (-(u * L₂ p.2)) * π₂ p.2))) (μ₁.prod μ₂) :=
    (hM₁.mul_prod hZ₂).add ((hN₁.mul_prod hN₂).const_mul 2)
  rw [integral_add h12 (hZ₁.mul_prod hM₂), integral_add (hM₁.mul_prod hZ₂)
    ((hN₁.mul_prod hN₂).const_mul 2), integral_const_mul,
    integral_prod_mul (fun x ↦ L₁ x * L₁ x * Real.exp (-(u * L₁ x)) * π₁ x)
      (fun y ↦ Real.exp (-(u * L₂ y)) * π₂ y),
    integral_prod_mul (fun x ↦ L₁ x * Real.exp (-(u * L₁ x)) * π₁ x)
      (fun y ↦ L₂ y * Real.exp (-(u * L₂ y)) * π₂ y),
    integral_prod_mul (fun x ↦ Real.exp (-(u * L₁ x)) * π₁ x)
      (fun y ↦ L₂ y * L₂ y * Real.exp (-(u * L₂ y)) * π₂ y)]

omit hM₁ hM₂ in
/-- The posterior mean of the separable loss is the sum of the factor means. -/
theorem priorExp_prod_add (hZ₁0 : priorZ μ₁ π₁ L₁ u ≠ 0) (hZ₂0 : priorZ μ₂ π₂ L₂ u ≠ 0) :
    priorExp (μ₁.prod μ₂) (prodPrior π₁ π₂) (sumLoss L₁ L₂) (sumLoss L₁ L₂) u =
      priorExp μ₁ π₁ L₁ L₁ u + priorExp μ₂ π₂ L₂ L₂ u := by
  unfold priorExp
  rw [priorZ_prod, prod_num_add hZ₁ hZ₂ hN₁ hN₂]
  exact mean_ratio_alg hZ₁0 hZ₂0

/-- **Variance additivity for product priors**: `Var_u(L₁ + L₂) = Var_u(L₁) + Var_u(L₂)`. -/
theorem priorCov_self_prod (hZ₁0 : priorZ μ₁ π₁ L₁ u ≠ 0) (hZ₂0 : priorZ μ₂ π₂ L₂ u ≠ 0) :
    priorCov (μ₁.prod μ₂) (prodPrior π₁ π₂) (sumLoss L₁ L₂) (sumLoss L₁ L₂) (sumLoss L₁ L₂) u =
      priorCov μ₁ π₁ L₁ L₁ L₁ u + priorCov μ₂ π₂ L₂ L₂ L₂ u := by
  unfold priorCov
  rw [priorExp_prod_add hZ₁ hZ₂ hN₁ hN₂ hZ₁0 hZ₂0]
  unfold priorExp
  rw [priorZ_prod, prod_num_sq hZ₁ hZ₂ hN₁ hN₂ hM₁ hM₂]
  exact var_ratio_alg hZ₁0 hZ₂0

end Var

/-! ### The product-prior inequality -/

section Length

variable {π₁ L₁ : X → ℝ} {π₂ L₂ : Y → ℝ} {t : ℝ} (ht : 0 ≤ t)
  (hZ₁ : ∀ u ∈ Icc 0 t, Integrable (fun x ↦ Real.exp (-(u * L₁ x)) * π₁ x) μ₁)
  (hZ₂ : ∀ u ∈ Icc 0 t, Integrable (fun y ↦ Real.exp (-(u * L₂ y)) * π₂ y) μ₂)
  (hN₁ : ∀ u ∈ Icc 0 t, Integrable (fun x ↦ L₁ x * Real.exp (-(u * L₁ x)) * π₁ x) μ₁)
  (hN₂ : ∀ u ∈ Icc 0 t, Integrable (fun y ↦ L₂ y * Real.exp (-(u * L₂ y)) * π₂ y) μ₂)
  (hM₁ : ∀ u ∈ Icc 0 t, Integrable (fun x ↦ L₁ x * L₁ x * Real.exp (-(u * L₁ x)) * π₁ x) μ₁)
  (hM₂ : ∀ u ∈ Icc 0 t, Integrable (fun y ↦ L₂ y * L₂ y * Real.exp (-(u * L₂ y)) * π₂ y) μ₂)
  (hZ₁0 : ∀ u ∈ Icc 0 t, priorZ μ₁ π₁ L₁ u ≠ 0) (hZ₂0 : ∀ u ∈ Icc 0 t, priorZ μ₂ π₂ L₂ u ≠ 0)
  (hV₁ : ContinuousOn (fun u ↦ priorCov μ₁ π₁ L₁ L₁ L₁ u) (Icc 0 t))
  (hV₂ : ContinuousOn (fun u ↦ priorCov μ₂ π₂ L₂ L₂ L₂ u) (Icc 0 t))
include ht hZ₁ hZ₂ hN₁ hN₂ hM₁ hM₂ hZ₁0 hZ₂0 hV₁ hV₂

omit hV₁ hV₂ in
/-- The radial length of the product is `∫₀ᵗ √(V₁ + V₂)`. -/
theorem radialLength_prod_eq :
    radialLength (μ₁.prod μ₂) (prodPrior π₁ π₂) (sumLoss L₁ L₂) t =
      ∫ u in (0 : ℝ)..t, Real.sqrt (priorCov μ₁ π₁ L₁ L₁ L₁ u + priorCov μ₂ π₂ L₂ L₂ L₂ u) := by
  unfold radialLength
  refine intervalIntegral.integral_congr fun u hu ↦ ?_
  rw [uIcc_of_le ht] at hu
  rw [priorCov_self_prod (hZ₁ u hu) (hZ₂ u hu) (hN₁ u hu) (hN₂ u hu) (hM₁ u hu) (hM₂ u hu)
    (hZ₁0 u hu) (hZ₂0 u hu)]

/-- **Product-prior inequality, upper half**: `D_t(L₁ + L₂) ≤ D_t(L₁) + D_t(L₂)`. -/
theorem radialLength_prod_le :
    radialLength (μ₁.prod μ₂) (prodPrior π₁ π₂) (sumLoss L₁ L₂) t ≤
      radialLength μ₁ π₁ L₁ t + radialLength μ₂ π₂ L₂ t := by
  rw [radialLength_prod_eq ht hZ₁ hZ₂ hN₁ hN₂ hM₁ hM₂ hZ₁0 hZ₂0]
  exact integral_sqrt_add_le ht hV₁ hV₂

/-- **Product-prior inequality, lower half**: `√(D_t(L₁)² + D_t(L₂)²) ≤ D_t(L₁ + L₂)`, under
nonnegativity of the factor variances on `[0, t]`. -/
theorem sqrt_sq_add_sq_le_radialLength_prod
    (hn₁ : ∀ u ∈ Icc 0 t, 0 ≤ priorCov μ₁ π₁ L₁ L₁ L₁ u)
    (hn₂ : ∀ u ∈ Icc 0 t, 0 ≤ priorCov μ₂ π₂ L₂ L₂ L₂ u) :
    Real.sqrt (radialLength μ₁ π₁ L₁ t ^ 2 + radialLength μ₂ π₂ L₂ t ^ 2) ≤
      radialLength (μ₁.prod μ₂) (prodPrior π₁ π₂) (sumLoss L₁ L₂) t := by
  rw [radialLength_prod_eq ht hZ₁ hZ₂ hN₁ hN₂ hM₁ hM₂ hZ₁0 hZ₂0]
  exact sqrt_sq_add_sq_le_integral_sqrt_add ht hV₁ hV₂ hn₁ hn₂

end Length

end Laplace.Multi
