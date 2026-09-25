/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.StateDensity
import Laplace.Multi.WallWindowLength

/-!
# Laws of the radial response length, and the two-sided wall window

Elementary structural properties of the radial response length `D_t(L) = ∫₀ᵗ √Var_u(L) du`
(`radialLength`): invariance under adding a constant to the loss (`radialLength_const_add`), and the
scaling law `D_t(aL + b) = D_{at}(L)` for `a > 0` (`radialLength_smul_add`), which follows from
`⟨φ⟩_{u}^{aL+b} = ⟨φ⟩_{au}^{L}` (`priorExp_smul_add`) and `Var_u(aL + b) = a² Var_{au}(L)`
(`priorCov_self_smul_add`). Together with the two-sided window identity
`ℓ_t(−c₋t^{-σ*}, c₊t^{-σ*}) = ∫_{−c₋}^{c₊} h(c) dc` (`wall_window_length_two_sided`), the exact wall
chart crosses the phase boundary rather than merely approaching it (Astra, round 25, item 6).
-/

open MeasureTheory Filter Topology Set intervalIntegral

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Rescaling the loss rescales the temperature: `⟨φ⟩_u^{aL+b} = ⟨φ⟩_{au}^L`. -/
theorem priorExp_smul_add (π L φ : X → ℝ) (a b u : ℝ) :
    priorExp μ π (fun x ↦ a * L x + b) φ u = priorExp μ π L φ (a * u) := by
  unfold priorExp priorZ
  have e1 : (∫ x, φ x * Real.exp (-(u * (a * L x + b))) * π x ∂μ) =
      Real.exp (-(u * b)) * ∫ x, φ x * Real.exp (-(a * u * L x)) * π x ∂μ := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [show -(u * (a * L x + b)) = -(u * b) + -(a * u * L x) by ring, Real.exp_add]
    ring
  have e2 : (∫ x, Real.exp (-(u * (a * L x + b))) * π x ∂μ) =
      Real.exp (-(u * b)) * ∫ x, Real.exp (-(a * u * L x)) * π x ∂μ := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [show -(u * (a * L x + b)) = -(u * b) + -(a * u * L x) by ring, Real.exp_add]
    ring
  rw [e1, e2, mul_div_mul_left _ _ (Real.exp_pos _).ne']

/-- `Var_u(aL + b) = a² Var_{au}(L)` (given the tilted second moment at `au`). -/
theorem priorCov_self_smul_add {π L : X → ℝ} (a b u : ℝ)
    (hZ : priorZ μ π L (a * u) ≠ 0)
    (h0 : Integrable (fun x ↦ Real.exp (-(a * u * L x)) * π x) μ)
    (h1 : Integrable (fun x ↦ L x * (Real.exp (-(a * u * L x)) * π x)) μ)
    (h2 : Integrable (fun x ↦ L x * L x * (Real.exp (-(a * u * L x)) * π x)) μ) :
    priorCov μ π (fun x ↦ a * L x + b) (fun x ↦ a * L x + b) (fun x ↦ a * L x + b) u =
      a ^ 2 * priorCov μ π L L L (a * u) := by
  unfold priorCov
  rw [priorExp_smul_add, priorExp_smul_add]
  unfold priorExp
  unfold priorZ at hZ ⊢
  have e : ∀ x, (a * L x + b) * (a * L x + b) * Real.exp (-(a * u * L x)) * π x =
      a ^ 2 * (L x * L x * (Real.exp (-(a * u * L x)) * π x)) +
        (2 * a * b) * (L x * (Real.exp (-(a * u * L x)) * π x)) +
        b ^ 2 * (Real.exp (-(a * u * L x)) * π x) := fun x ↦ by ring
  have e' : ∀ x, (a * L x + b) * Real.exp (-(a * u * L x)) * π x =
      a * (L x * (Real.exp (-(a * u * L x)) * π x)) + b * (Real.exp (-(a * u * L x)) * π x) :=
    fun x ↦ by ring
  simp_rw [e, e']
  have I2 : Integrable (fun x ↦ a ^ 2 * (L x * L x * (Real.exp (-(a * u * L x)) * π x))) μ :=
    h2.const_mul _
  have I1 : Integrable (fun x ↦ (2 * a * b) * (L x * (Real.exp (-(a * u * L x)) * π x))) μ :=
    h1.const_mul _
  have I0 : Integrable (fun x ↦ b ^ 2 * (Real.exp (-(a * u * L x)) * π x)) μ := h0.const_mul _
  have I21 : Integrable (fun x ↦ a ^ 2 * (L x * L x * (Real.exp (-(a * u * L x)) * π x)) +
      (2 * a * b) * (L x * (Real.exp (-(a * u * L x)) * π x))) μ := I2.add I1
  have J1 : Integrable (fun x ↦ a * (L x * (Real.exp (-(a * u * L x)) * π x))) μ :=
    h1.const_mul _
  have J0 : Integrable (fun x ↦ b * (Real.exp (-(a * u * L x)) * π x)) μ := h0.const_mul _
  rw [integral_add I21 I0, integral_add I2 I1, integral_add J1 J0,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]
  have eL : (∫ x, L x * (Real.exp (-(a * u * L x)) * π x) ∂μ) =
      ∫ x, L x * Real.exp (-(a * u * L x)) * π x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by ring)
  have eLL : (∫ x, L x * L x * (Real.exp (-(a * u * L x)) * π x) ∂μ) =
      ∫ x, L x * L x * Real.exp (-(a * u * L x)) * π x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by ring)
  rw [eL, eLL]
  set Z := ∫ x, Real.exp (-(a * u * L x)) * π x ∂μ with hZdef
  set N1 := ∫ x, L x * Real.exp (-(a * u * L x)) * π x ∂μ with hN1
  set N2 := ∫ x, L x * L x * Real.exp (-(a * u * L x)) * π x ∂μ with hN2
  clear_value Z N1 N2
  field_simp
  ring

/-- **The scaling law of the radial response length**: `D_t(aL + b) = D_{at}(L)` for `a > 0`. -/
theorem radialLength_smul_add {π L : X → ℝ} {a : ℝ} (ha : 0 < a) (b : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hZ : ∀ v, 0 ≤ v → priorZ μ π L v ≠ 0)
    (h0 : ∀ v, 0 ≤ v → Integrable (fun x ↦ Real.exp (-(v * L x)) * π x) μ)
    (h1 : ∀ v, 0 ≤ v → Integrable (fun x ↦ L x * (Real.exp (-(v * L x)) * π x)) μ)
    (h2 : ∀ v, 0 ≤ v → Integrable (fun x ↦ L x * L x * (Real.exp (-(v * L x)) * π x)) μ) :
    radialLength μ π (fun x ↦ a * L x + b) t = radialLength μ π L (a * t) := by
  unfold radialLength
  have e : ∀ u ∈ uIcc (0 : ℝ) t, Real.sqrt (priorCov μ π (fun x ↦ a * L x + b)
      (fun x ↦ a * L x + b) (fun x ↦ a * L x + b) u) =
      a * Real.sqrt (priorCov μ π L L L (a * u)) := fun u hu ↦ by
    rw [uIcc_of_le ht] at hu
    have hau : 0 ≤ a * u := mul_nonneg ha.le hu.1
    rw [priorCov_self_smul_add a b u (hZ _ hau) (h0 _ hau) (h1 _ hau) (h2 _ hau),
      Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
  rw [integral_congr e, intervalIntegral.integral_const_mul,
    integral_comp_mul_left (f := fun v ↦ Real.sqrt (priorCov μ π L L L v)) ha.ne', mul_zero,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

/-- The radial response length is invariant under adding a constant to the loss. -/
theorem radialLength_const_add {π L : X → ℝ} (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hZ : ∀ v, 0 ≤ v → priorZ μ π L v ≠ 0)
    (h0 : ∀ v, 0 ≤ v → Integrable (fun x ↦ Real.exp (-(v * L x)) * π x) μ)
    (h1 : ∀ v, 0 ≤ v → Integrable (fun x ↦ L x * (Real.exp (-(v * L x)) * π x)) μ)
    (h2 : ∀ v, 0 ≤ v → Integrable (fun x ↦ L x * L x * (Real.exp (-(v * L x)) * π x)) μ) :
    radialLength μ π (fun x ↦ c + L x) t = radialLength μ π L t := by
  have := radialLength_smul_add (μ := μ) (π := π) (L := L) one_pos c ht hZ h0 h1 h2
  rw [one_mul] at this
  rw [← this]
  congr 1
  funext x
  ring

/-- **The two-sided wall window**: the exact window identity across the phase boundary. -/
theorem wall_window_length_two_sided {p q : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) (cm cp : ℝ) :
    ∫ a in (-cm * t ^ (-(1 - q / p)))..(cp * t ^ (-(1 - q / p))),
        Real.sqrt (fisherSpeed (volume.restrict (Ioi 0)) (fun _ ↦ 1) (twoMonoPath p q)
          (twoMonoVel q) t a)
      = ∫ c in (-cm)..cp, Real.sqrt (profilePosterior p q (fun y ↦ y ^ q * y ^ q) c -
          profilePosterior p q (fun y ↦ y ^ q) c ^ 2) :=
  wall_window_length hp ht (-cm) cp

end Laplace.Multi
