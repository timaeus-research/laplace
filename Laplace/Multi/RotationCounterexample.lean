/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.WeightedTemperatureAdapter

/-!
# Radial and quadratic observables do not identify analytic germs

An analytic counterexample to full-expansion identifiability from the natural finite
families. In two variables, with `q(y) = y₀² + y₁²`, the losses

  `L₁ y = q y / 2 + (y₀⁴ + y₁⁴)`,   `L₂ = L₁ ∘ R`,   `R y = ((y₀ + y₁)/√2, (y₀ − y₁)/√2)`

have the same Hessian and different germs at the origin (`L₁ (s, 0) − L₂ (s, 0) = s⁴/2`),
yet on the `R`-invariant localization region `U = {q < 1}` their localized normalized
moments coincide EXACTLY at every temperature for every radial observable `g ∘ q` and for
every monomial of degree `≤ 2`. The mechanism is symmetry: `R` is a measure-preserving
involution preserving `q` and `U`, so `⟨φ⟩_{L₂,t} = ⟨φ ∘ R⟩_{L₁,t}`; the coordinate sign
flip and the swap preserve `L₁` as well, forcing `⟨y₀⟩ = ⟨y₁⟩ = ⟨y₀ y₁⟩ = 0` and
`⟨y₀²⟩ = ⟨y₁²⟩` under `L₁`, which makes `⟨φ ∘ R⟩_{L₁,t} = ⟨φ⟩_{L₁,t}` for every quadratic
monomial. In particular the two-radial-probe rigidity theorem (which is relative to the
Gaussian reference) does not extend to a global identification theorem for `{q, q²}`, nor
does the family of all monomials of degree `≤ 2` identify germs.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

namespace Rotation

/-- The Euclidean quadratic form on `Fin 2 → ℝ`. -/
def qE (y : Fin 2 → ℝ) : ℝ := y 0 ^ 2 + y 1 ^ 2

/-- The reference loss `q/2 + y₀⁴ + y₁⁴`. -/
noncomputable def L₁ (y : Fin 2 → ℝ) : ℝ := qE y / 2 + (y 0 ^ 4 + y 1 ^ 4)

/-- The rotation matrix by `π/4`. -/
noncomputable def rotA : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / Real.sqrt 2, 1 / Real.sqrt 2; 1 / Real.sqrt 2, -(1 / Real.sqrt 2)]

/-- The rotation as a linear map on `Fin 2 → ℝ`. -/
noncomputable def rot : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' rotA

/-- The rotated loss. -/
noncomputable def L₂ (y : Fin 2 → ℝ) : ℝ := L₁ (rot y)

/-- The localization region `{q < 1}`. -/
def U : Set (Fin 2 → ℝ) := {y | qE y < 1}

theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

theorem rot_apply (y : Fin 2 → ℝ) :
    rot y = ![(y 0 + y 1) / Real.sqrt 2, (y 0 - y 1) / Real.sqrt 2] := by
  unfold rot rotA
  rw [Matrix.toLin'_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem rot_zero_apply (y : Fin 2 → ℝ) : rot y 0 = (y 0 + y 1) / Real.sqrt 2 := by
  rw [rot_apply]
  rfl

theorem rot_one_apply (y : Fin 2 → ℝ) : rot y 1 = (y 0 - y 1) / Real.sqrt 2 := by
  rw [rot_apply]
  rfl

theorem rot_rot (y : Fin 2 → ℝ) : rot (rot y) = y := by
  ext i
  fin_cases i
  · change rot (rot y) 0 = y 0
    rw [rot_zero_apply, rot_zero_apply, rot_one_apply, ← add_div, div_div,
      sqrt_two_mul_self]
    ring
  · change rot (rot y) 1 = y 1
    rw [rot_one_apply, rot_zero_apply, rot_one_apply, ← sub_div, div_div,
      sqrt_two_mul_self]
    ring

theorem qE_rot (y : Fin 2 → ℝ) : qE (rot y) = qE y := by
  unfold qE
  rw [rot_zero_apply, rot_one_apply, div_pow, div_pow, sqrt_two_sq]
  ring

theorem det_rot : LinearMap.det rot = -1 := by
  unfold rot rotA
  rw [LinearMap.det_toLin', Matrix.det_fin_two_of, mul_neg, div_mul_div_comm, one_mul,
    sqrt_two_mul_self]
  norm_num

/-! ### Measure-preserving involutions of the plane -/

/-- A linear involution of unit Jacobian preserves every integral. -/
theorem integral_comp_involution (S : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) (hS : ∀ y, S (S y) = y)
    (hdet : |LinearMap.det S| = 1) (f : (Fin 2 → ℝ) → ℝ) :
    ∫ y, f (S y) = ∫ y, f y := by
  have hdet0 : LinearMap.det S ≠ 0 := by
    intro h
    rw [h, abs_zero] at hdet
    exact zero_ne_one hdet
  have hmeas : Measurable S := S.continuous_of_finiteDimensional.measurable
  have hmap : Measure.map S volume = volume := by
    rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet0, abs_inv, hdet, inv_one,
      ENNReal.ofReal_one, one_smul]
  let e : (Fin 2 → ℝ) ≃ᵐ (Fin 2 → ℝ) :=
    { toFun := S
      invFun := S
      left_inv := hS
      right_inv := hS
      measurable_toFun := hmeas
      measurable_invFun := hmeas }
  have hmp : MeasurePreserving e volume volume := ⟨hmeas, hmap⟩
  exact hmp.integral_comp' f

/-- The coordinate sign flip. -/
noncomputable def flip : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' !![-1, 0; 0, 1]

/-- The coordinate swap. -/
noncomputable def swap : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' !![0, 1; 1, 0]

theorem flip_apply (y : Fin 2 → ℝ) : flip y = ![-y 0, y 1] := by
  unfold flip
  rw [Matrix.toLin'_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem swap_apply (y : Fin 2 → ℝ) : swap y = ![y 1, y 0] := by
  unfold swap
  rw [Matrix.toLin'_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem flip_zero_apply (y : Fin 2 → ℝ) : flip y 0 = -y 0 := by
  rw [flip_apply]
  rfl

theorem flip_one_apply (y : Fin 2 → ℝ) : flip y 1 = y 1 := by
  rw [flip_apply]
  rfl

theorem swap_zero_apply (y : Fin 2 → ℝ) : swap y 0 = y 1 := by
  rw [swap_apply]
  rfl

theorem swap_one_apply (y : Fin 2 → ℝ) : swap y 1 = y 0 := by
  rw [swap_apply]
  rfl

theorem flip_flip (y : Fin 2 → ℝ) : flip (flip y) = y := by
  ext i
  fin_cases i
  · change flip (flip y) 0 = y 0
    rw [flip_zero_apply, flip_zero_apply, neg_neg]
  · change flip (flip y) 1 = y 1
    rw [flip_one_apply, flip_one_apply]

theorem swap_swap (y : Fin 2 → ℝ) : swap (swap y) = y := by
  ext i
  fin_cases i
  · change swap (swap y) 0 = y 0
    rw [swap_zero_apply, swap_one_apply]
  · change swap (swap y) 1 = y 1
    rw [swap_one_apply, swap_zero_apply]

theorem det_flip : |LinearMap.det flip| = 1 := by
  unfold flip
  rw [LinearMap.det_toLin', Matrix.det_fin_two_of]
  norm_num

theorem det_swap : |LinearMap.det swap| = 1 := by
  unfold swap
  rw [LinearMap.det_toLin', Matrix.det_fin_two_of]
  norm_num

theorem qE_flip (y : Fin 2 → ℝ) : qE (flip y) = qE y := by
  unfold qE
  rw [flip_zero_apply, flip_one_apply]
  ring

theorem qE_swap (y : Fin 2 → ℝ) : qE (swap y) = qE y := by
  unfold qE
  rw [swap_zero_apply, swap_one_apply]
  ring

theorem L₁_flip (y : Fin 2 → ℝ) : L₁ (flip y) = L₁ y := by
  unfold L₁
  rw [qE_flip, flip_zero_apply, flip_one_apply]
  ring

theorem L₁_swap (y : Fin 2 → ℝ) : L₁ (swap y) = L₁ y := by
  unfold L₁
  rw [qE_swap, swap_zero_apply, swap_one_apply]
  ring

/-! ### Change of variables in the localized moments -/

/-- For a measure-preserving involution preserving the region, the moments of `L ∘ S` are
the moments of `L` at the transported observable. -/
theorem tempMoment_comp (S : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) (hS : ∀ y, S (S y) = y)
    (hdet : |LinearMap.det S| = 1) (hU : ∀ y, S y ∈ U ↔ y ∈ U) (L φ : (Fin 2 → ℝ) → ℝ)
    (t : ℝ) :
    IntWeights.tempMoment U (fun y ↦ L (S y)) φ t =
      IntWeights.tempMoment U L (fun y ↦ φ (S y)) t := by
  unfold IntWeights.tempMoment
  have hnum : (∫ y, U.indicator (fun y ↦ φ y * Real.exp (-(t * L (S y)))) y) =
      ∫ y, U.indicator (fun y ↦ φ (S y) * Real.exp (-(t * L y))) y := by
    rw [← integral_comp_involution S hS hdet
      (fun y ↦ U.indicator (fun y ↦ φ y * Real.exp (-(t * L (S y)))) y)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    beta_reduce
    by_cases hy : y ∈ U
    · rw [Set.indicator_of_mem ((hU y).mpr hy), Set.indicator_of_mem hy, hS]
    · rw [Set.indicator_of_notMem (fun h ↦ hy ((hU y).mp h)), Set.indicator_of_notMem hy]
  have hden : (∫ y, U.indicator (fun y ↦ Real.exp (-(t * L (S y)))) y) =
      ∫ y, U.indicator (fun y ↦ Real.exp (-(t * L y))) y := by
    rw [← integral_comp_involution S hS hdet
      (fun y ↦ U.indicator (fun y ↦ Real.exp (-(t * L (S y)))) y)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    beta_reduce
    by_cases hy : y ∈ U
    · rw [Set.indicator_of_mem ((hU y).mpr hy), Set.indicator_of_mem hy, hS]
    · rw [Set.indicator_of_notMem (fun h ↦ hy ((hU y).mp h)), Set.indicator_of_notMem hy]
  rw [hnum, hden]

theorem rot_mem_U (y : Fin 2 → ℝ) : rot y ∈ U ↔ y ∈ U := by
  change qE (rot y) < 1 ↔ qE y < 1
  rw [qE_rot]

theorem flip_mem_U (y : Fin 2 → ℝ) : flip y ∈ U ↔ y ∈ U := by
  change qE (flip y) < 1 ↔ qE y < 1
  rw [qE_flip]

theorem swap_mem_U (y : Fin 2 → ℝ) : swap y ∈ U ↔ y ∈ U := by
  change qE (swap y) < 1 ↔ qE y < 1
  rw [qE_swap]

/-- The moments of `L₂` are the `L₁`-moments of the rotated observable. -/
theorem tempMoment_L₂ (φ : (Fin 2 → ℝ) → ℝ) (t : ℝ) :
    IntWeights.tempMoment U L₂ φ t = IntWeights.tempMoment U L₁ (fun y ↦ φ (rot y)) t :=
  tempMoment_comp rot rot_rot (by rw [det_rot]; norm_num) rot_mem_U L₁ φ t

/-- Symmetries of `L₁` leave its moments invariant. -/
theorem tempMoment_L₁_flip (φ : (Fin 2 → ℝ) → ℝ) (t : ℝ) :
    IntWeights.tempMoment U L₁ (fun y ↦ φ (flip y)) t = IntWeights.tempMoment U L₁ φ t := by
  rw [← tempMoment_comp flip flip_flip det_flip flip_mem_U L₁ φ t]
  simp only [L₁_flip]

theorem tempMoment_L₁_swap (φ : (Fin 2 → ℝ) → ℝ) (t : ℝ) :
    IntWeights.tempMoment U L₁ (fun y ↦ φ (swap y)) t = IntWeights.tempMoment U L₁ φ t := by
  rw [← tempMoment_comp swap swap_swap det_swap swap_mem_U L₁ φ t]
  simp only [L₁_swap]

/-! ### Linearity of the localized moment in the observable -/

theorem U_subset_closedBall : U ⊆ Metric.closedBall (0 : Fin 2 → ℝ) 1 := by
  intro y hy
  have hq : qE y < 1 := hy
  unfold qE at hq
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  have h0 : ‖y 0‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (y 0), sq_nonneg (y 1), abs_nonneg (y 0)]
  have h1 : ‖y 1‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (y 1), sq_nonneg (y 0), abs_nonneg (y 1)]
  intro i
  fin_cases i
  · exact h0
  · exact h1

theorem continuous_qE : Continuous qE := by
  unfold qE
  fun_prop

theorem measurableSet_U : MeasurableSet U := by
  unfold U
  exact measurableSet_lt continuous_qE.measurable measurable_const

/-- Localized integrands of continuous observables are integrable on the bounded region. -/
theorem integrable_indicator_U {φ L : (Fin 2 → ℝ) → ℝ} (hφ : Continuous φ) (hL : Continuous L)
    (t : ℝ) : Integrable fun y ↦ U.indicator (fun y ↦ φ y * Real.exp (-(t * L y))) y := by
  have hcont : Continuous fun y ↦ φ y * Real.exp (-(t * L y)) := by fun_prop
  rw [integrable_indicator_iff measurableSet_U]
  exact (hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set
    U_subset_closedBall

theorem tempMoment_add {φ ψ L : (Fin 2 → ℝ) → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hL : Continuous L) (t : ℝ) :
    IntWeights.tempMoment U L (fun y ↦ φ y + ψ y) t =
      IntWeights.tempMoment U L φ t + IntWeights.tempMoment U L ψ t := by
  unfold IntWeights.tempMoment
  rw [← add_div]
  congr 1
  rw [← integral_add (integrable_indicator_U hφ hL t) (integrable_indicator_U hψ hL t)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  beta_reduce
  by_cases hy : y ∈ U
  · simp only [Set.indicator_of_mem hy]
    ring
  · simp only [Set.indicator_of_notMem hy, add_zero]

theorem tempMoment_const_mul (c : ℝ) {φ L : (Fin 2 → ℝ) → ℝ} (t : ℝ) :
    IntWeights.tempMoment U L (fun y ↦ c * φ y) t = c * IntWeights.tempMoment U L φ t := by
  unfold IntWeights.tempMoment
  rw [← mul_div_assoc, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  beta_reduce
  by_cases hy : y ∈ U
  · simp only [Set.indicator_of_mem hy]
    ring
  · simp only [Set.indicator_of_notMem hy, mul_zero]

/-! ### The quadratic moments of `L₁` -/

theorem continuous_L₁ : Continuous L₁ := by
  unfold L₁ qE
  fun_prop

theorem moment_coord0_zero (t : ℝ) : IntWeights.tempMoment U L₁ (fun y ↦ y 0) t = 0 := by
  have h := tempMoment_L₁_flip (fun y ↦ y 0) t
  simp only [flip_zero_apply] at h
  have h' := tempMoment_const_mul (-1) (φ := fun y ↦ y 0) (L := L₁) t
  simp only [neg_one_mul] at h'
  linarith

theorem moment_coord1_zero (t : ℝ) : IntWeights.tempMoment U L₁ (fun y ↦ y 1) t = 0 := by
  have h := tempMoment_L₁_swap (fun y ↦ y 1) t
  simp only [swap_one_apply] at h
  rw [← h]
  exact moment_coord0_zero t

theorem moment_cross_zero (t : ℝ) : IntWeights.tempMoment U L₁ (fun y ↦ y 0 * y 1) t = 0 := by
  have h := tempMoment_L₁_flip (fun y ↦ y 0 * y 1) t
  simp only [flip_zero_apply, flip_one_apply] at h
  have h' := tempMoment_const_mul (-1) (φ := fun y ↦ y 0 * y 1) (L := L₁) t
  have hfun : (fun y : Fin 2 → ℝ ↦ -1 * (y 0 * y 1)) = fun y ↦ -y 0 * y 1 := by
    funext y
    ring
  rw [hfun] at h'
  linarith

theorem moment_sq_eq (t : ℝ) :
    IntWeights.tempMoment U L₁ (fun y ↦ y 1 ^ 2) t =
      IntWeights.tempMoment U L₁ (fun y ↦ y 0 ^ 2) t := by
  have h := tempMoment_L₁_swap (fun y ↦ y 0 ^ 2) t
  simp only [swap_zero_apply] at h
  exact h

/-- Linear observables have zero `L₁`-moment. -/
theorem tempMoment_linear (a b t : ℝ) :
    IntWeights.tempMoment U L₁ (fun y ↦ a * y 0 + b * y 1) t = 0 := by
  rw [tempMoment_add (φ := fun y ↦ a * y 0) (ψ := fun y ↦ b * y 1) (by fun_prop) (by fun_prop)
    continuous_L₁, tempMoment_const_mul, tempMoment_const_mul, moment_coord0_zero,
    moment_coord1_zero]
  ring

/-- Quadratic observables have `L₁`-moment equal to the trace times `⟨y₀²⟩`. -/
theorem tempMoment_quadratic (a b c t : ℝ) :
    IntWeights.tempMoment U L₁ (fun y ↦ a * y 0 ^ 2 + b * (y 0 * y 1) + c * y 1 ^ 2) t =
      (a + c) * IntWeights.tempMoment U L₁ (fun y ↦ y 0 ^ 2) t := by
  rw [tempMoment_add (φ := fun y ↦ a * y 0 ^ 2 + b * (y 0 * y 1)) (ψ := fun y ↦ c * y 1 ^ 2)
    (by fun_prop) (by fun_prop) continuous_L₁,
    tempMoment_add (φ := fun y ↦ a * y 0 ^ 2) (ψ := fun y ↦ b * (y 0 * y 1)) (by fun_prop)
    (by fun_prop) continuous_L₁, tempMoment_const_mul, tempMoment_const_mul,
    tempMoment_const_mul, moment_cross_zero, moment_sq_eq]
  ring

/-! ### The counterexample -/

/-- The germs differ: along the first axis `L₁ − L₂ = s⁴/2`. -/
theorem L₁_ne_L₂ : ¬ ∀ᶠ y in 𝓝 (0 : Fin 2 → ℝ), L₁ y = L₂ y := by
  intro h
  obtain ⟨δ, hδ, hy⟩ := Metric.eventually_nhds_iff.mp h
  have hs : 0 < δ / 2 := half_pos hδ
  have hdist : dist (![δ / 2, 0] : Fin 2 → ℝ) 0 < δ := by
    rw [dist_zero_right, pi_norm_lt_iff hδ]
    intro i
    fin_cases i
    · change ‖δ / 2‖ < δ
      rw [Real.norm_eq_abs, abs_of_pos hs]
      linarith
    · change ‖(0 : ℝ)‖ < δ
      rw [norm_zero]
      exact hδ
  have heq := hy hdist
  unfold L₂ L₁ at heq
  rw [qE_rot, rot_zero_apply, rot_one_apply] at heq
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_zero, sub_zero] at heq
  have hkey : (δ / 2) ^ 4 = 2 * ((δ / 2) / Real.sqrt 2) ^ 4 := by linarith
  rw [div_pow (δ / 2) (Real.sqrt 2), show Real.sqrt 2 ^ 4 = 4 by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sqrt_two_sq]; norm_num] at hkey
  have hs4 : 0 < (δ / 2) ^ 4 := by positivity
  linarith

theorem analyticAt_coord (i : Fin 2) : AnalyticAt ℝ (fun y : Fin 2 → ℝ ↦ y i) 0 :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) i).analyticAt 0

theorem analyticAt_L₁ : AnalyticAt ℝ L₁ 0 := by
  unfold L₁ qE
  have h0 := analyticAt_coord 0
  have h1 := analyticAt_coord 1
  have hq : AnalyticAt ℝ (fun y : Fin 2 → ℝ ↦ (y 0 ^ 2 + y 1 ^ 2) / 2) 0 :=
    ((h0.pow 2).add (h1.pow 2)).div_const (c := 2)
  exact hq.add ((h0.pow 4).add (h1.pow 4))

theorem analyticAt_L₂ : AnalyticAt ℝ L₂ 0 := by
  have hrot : AnalyticAt ℝ (fun y : Fin 2 → ℝ ↦ rot y) 0 :=
    (LinearMap.toContinuousLinearMap rot).analyticAt _
  have h : AnalyticAt ℝ L₁ (rot 0) := by
    rw [map_zero]
    exact analyticAt_L₁
  exact h.comp hrot

theorem quad00 (t : ℝ) :
    IntWeights.tempMoment U L₂ (fun y ↦ y 0 * y 0) t =
      IntWeights.tempMoment U L₁ (fun y ↦ y 0 * y 0) t := by
  rw [tempMoment_L₂]
  have hfun : (fun y : Fin 2 → ℝ ↦ rot y 0 * rot y 0) =
      fun y ↦ (1 / 2) * y 0 ^ 2 + 1 * (y 0 * y 1) + (1 / 2) * y 1 ^ 2 := by
    funext y
    rw [rot_zero_apply, div_mul_div_comm, sqrt_two_mul_self]
    ring
  have hfun' : (fun y : Fin 2 → ℝ ↦ y 0 * y 0) =
      fun y ↦ 1 * y 0 ^ 2 + 0 * (y 0 * y 1) + 0 * y 1 ^ 2 := by
    funext y
    ring
  rw [hfun, hfun', tempMoment_quadratic, tempMoment_quadratic]
  ring

theorem quad01 (t : ℝ) :
    IntWeights.tempMoment U L₂ (fun y ↦ y 0 * y 1) t =
      IntWeights.tempMoment U L₁ (fun y ↦ y 0 * y 1) t := by
  rw [tempMoment_L₂]
  have hfun : (fun y : Fin 2 → ℝ ↦ rot y 0 * rot y 1) =
      fun y ↦ (1 / 2) * y 0 ^ 2 + 0 * (y 0 * y 1) + (-(1 / 2)) * y 1 ^ 2 := by
    funext y
    rw [rot_zero_apply, rot_one_apply, div_mul_div_comm, sqrt_two_mul_self]
    ring
  have hfun' : (fun y : Fin 2 → ℝ ↦ y 0 * y 1) =
      fun y ↦ 0 * y 0 ^ 2 + 1 * (y 0 * y 1) + 0 * y 1 ^ 2 := by
    funext y
    ring
  rw [hfun, hfun', tempMoment_quadratic, tempMoment_quadratic]
  ring

theorem quad10 (t : ℝ) :
    IntWeights.tempMoment U L₂ (fun y ↦ y 1 * y 0) t =
      IntWeights.tempMoment U L₁ (fun y ↦ y 1 * y 0) t := by
  rw [tempMoment_L₂]
  have hfun : (fun y : Fin 2 → ℝ ↦ rot y 1 * rot y 0) =
      fun y ↦ (1 / 2) * y 0 ^ 2 + 0 * (y 0 * y 1) + (-(1 / 2)) * y 1 ^ 2 := by
    funext y
    rw [rot_zero_apply, rot_one_apply, div_mul_div_comm, sqrt_two_mul_self]
    ring
  have hfun' : (fun y : Fin 2 → ℝ ↦ y 1 * y 0) =
      fun y ↦ 0 * y 0 ^ 2 + 1 * (y 0 * y 1) + 0 * y 1 ^ 2 := by
    funext y
    ring
  rw [hfun, hfun', tempMoment_quadratic, tempMoment_quadratic]
  ring

theorem quad11 (t : ℝ) :
    IntWeights.tempMoment U L₂ (fun y ↦ y 1 * y 1) t =
      IntWeights.tempMoment U L₁ (fun y ↦ y 1 * y 1) t := by
  rw [tempMoment_L₂]
  have hfun : (fun y : Fin 2 → ℝ ↦ rot y 1 * rot y 1) =
      fun y ↦ (1 / 2) * y 0 ^ 2 + (-1) * (y 0 * y 1) + (1 / 2) * y 1 ^ 2 := by
    funext y
    rw [rot_one_apply, div_mul_div_comm, sqrt_two_mul_self]
    ring
  have hfun' : (fun y : Fin 2 → ℝ ↦ y 1 * y 1) =
      fun y ↦ 0 * y 0 ^ 2 + 0 * (y 0 * y 1) + 1 * y 1 ^ 2 := by
    funext y
    ring
  rw [hfun, hfun', tempMoment_quadratic, tempMoment_quadratic]
  ring

theorem lin0 (t : ℝ) :
    IntWeights.tempMoment U L₂ (fun y ↦ y 0) t = IntWeights.tempMoment U L₁ (fun y ↦ y 0) t := by
  rw [tempMoment_L₂, moment_coord0_zero]
  have hfun : (fun y : Fin 2 → ℝ ↦ rot y 0) =
      fun y ↦ (1 / Real.sqrt 2) * y 0 + (1 / Real.sqrt 2) * y 1 := by
    funext y
    rw [rot_zero_apply]
    ring
  rw [hfun, tempMoment_linear]

theorem lin1 (t : ℝ) :
    IntWeights.tempMoment U L₂ (fun y ↦ y 1) t = IntWeights.tempMoment U L₁ (fun y ↦ y 1) t := by
  rw [tempMoment_L₂, moment_coord1_zero]
  have hfun : (fun y : Fin 2 → ℝ ↦ rot y 1) =
      fun y ↦ (1 / Real.sqrt 2) * y 0 + (-(1 / Real.sqrt 2)) * y 1 := by
    funext y
    rw [rot_one_apply]
    ring
  rw [hfun, tempMoment_linear]

/-- **Radial and quadratic observables do not identify analytic germs.** The analytic losses
`L₁ = q/2 + y₀⁴ + y₁⁴` and `L₂ = L₁ ∘ R` (same Hessian) have different germs at the origin,
yet on `U = {q < 1}` their localized normalized moments agree exactly at every temperature
for every radial observable `g ∘ q`, every coordinate `y_i`, and every quadratic monomial
`y_i y_j`. In particular no family of radial observables (such as `{q, q²}`) and no family of
monomials of degree `≤ 2`, nor their union, is full-expansion sufficient. -/
theorem radial_quadratic_not_identifying :
    AnalyticAt ℝ L₁ 0 ∧ AnalyticAt ℝ L₂ 0 ∧ (¬ ∀ᶠ y in 𝓝 (0 : Fin 2 → ℝ), L₁ y = L₂ y) ∧
    (∀ (g : ℝ → ℝ) (t : ℝ),
      IntWeights.tempMoment U L₂ (fun y ↦ g (qE y)) t =
        IntWeights.tempMoment U L₁ (fun y ↦ g (qE y)) t) ∧
    (∀ (i : Fin 2) (t : ℝ),
      IntWeights.tempMoment U L₂ (fun y ↦ y i) t = IntWeights.tempMoment U L₁ (fun y ↦ y i) t) ∧
    (∀ (i j : Fin 2) (t : ℝ),
      IntWeights.tempMoment U L₂ (fun y ↦ y i * y j) t =
        IntWeights.tempMoment U L₁ (fun y ↦ y i * y j) t) := by
  refine ⟨analyticAt_L₁, analyticAt_L₂, L₁_ne_L₂, ?_, ?_, ?_⟩
  · intro g t
    rw [tempMoment_L₂]
    simp only [qE_rot]
  · intro i t
    fin_cases i
    · exact lin0 t
    · exact lin1 t
  · intro i j t
    fin_cases i <;> fin_cases j
    · exact quad00 t
    · exact quad01 t
    · exact quad10 t
    · exact quad11 t

end Rotation

end Laplace.Multi
