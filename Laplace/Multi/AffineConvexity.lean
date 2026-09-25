/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.ResponseMap

/-!
# The log-partition function is convex on the whole affine space of data

For an affine family of losses `L_a = L₀ + ∑ᵢ aᵢ Rᵢ` (`affLoss`; the losses of an affine family of
data distributions) the log-partition function

  `A_t(a) = log Z_t(L_a)`   (`affLogZ`)

is a **convex function on all of `ℝ^k`** (`affLogZ_convexOn`), with directional derivatives
`D_v A_t(a) = −t ⟨R_v⟩_a` (`hasDerivAt_affLogZ_dir`) and second derivatives the response form
`D_v² A_t(a) = g_a(v, v) = t² Var_a(R_v)` (`hasDerivAt_deriv_affLogZ_dir`). Equivalently the free
energy `F_t = −A_t/t` is concave (`affFreeEnergy_concaveOn`) with gradient the mean loss contrasts:
the response map on the data simplex is the gradient map of a concave potential, and the response
form is its (negative) Hessian. Convexity is obtained by restricting to the mixture lines of
`ResponseMap` (`TiltData.mixLogZ_convexOn`) through `affLoss_add_smul`.

This is the exact, global organising object of the response programme (Astra, round 22): the
posterior map `q ↦ ρ_{t,q}` pulls the Fisher–Rao metric back to `Hess_q log Z_t`, a possibly
degenerate Hessian geometry on the data manifold whose nullspace is the constant-loss directions
(`responseForm_self_eq_zero_iff`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The log-partition function on the affine family, `A_t(a) = log Z_t(L₀ + ∑ aᵢ Rᵢ)`. -/
noncomputable def affLogZ (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a : ι → ℝ) :
    ℝ :=
  Real.log (priorZ μ π (affLoss L₀ R a) t)

/-- The free energy on the affine family, `F_t(a) = −A_t(a)/t`. -/
noncomputable def affFreeEnergy (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (a : ι → ℝ) : ℝ :=
  -(1 / t) * affLogZ μ π L₀ R t a

/-- The restriction of the affine family to a line is a mixture line. -/
theorem affLogZ_line (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (a v : ι → ℝ) (s : ℝ) :
    mixLogZ μ π (affLoss L₀ R a) (dirLoss R v) t s = affLogZ μ π L₀ R t (a + s • v) := by
  unfold mixLogZ affLogZ
  rw [affLoss_add_smul]

/-- An affine loss with bounded base and bounded contrasts is bounded. -/
theorem bdd_affLoss {L₀ : X → ℝ} (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
    {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) (a : ι → ℝ) : Bdd (affLoss L₀ R a) := by
  obtain ⟨ham, Ma, hab⟩ := bdd_dirLoss hR a
  refine ⟨hL₀m.add ham, M₀ + Ma, fun x ↦ ?_⟩
  calc |affLoss L₀ R a x| = |L₀ x + dirLoss R a x| := rfl
    _ ≤ |L₀ x| + |dirLoss R a x| := abs_add_le _ _
    _ ≤ M₀ + Ma := add_le_add (hL₀ x) (hab x)

/-- The tilt data of a point of the affine family in a direction `v`. -/
theorem tiltData_aff {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 ≤ π x)
    (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
    {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) (a v : ι → ℝ) (t : ℝ) :
    ∃ M : ℝ, TiltData μ (baseWeight π (affLoss L₀ R a) t) (dirLoss R v) M := by
  obtain ⟨hLm, ML, hLb⟩ := bdd_affLoss hL₀m hL₀ hR a
  obtain ⟨hvm, Mv, hvb⟩ := bdd_dirLoss hR v
  exact ⟨Mv, tiltData_baseWeight_of_bounded μ hπm hπi hπ hπpos hLm hLb hvm hvb t⟩

variable [Nonempty X]

/-- **Convexity of the log-partition function on the affine space of data.** -/
theorem affLogZ_convexOn {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
    (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) (t : ℝ) :
    ConvexOn ℝ univ (affLogZ μ π L₀ R t) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  obtain ⟨M, h⟩ := tiltData_aff hπm hπi hπ hπpos hL₀m hL₀ hR x (y - x) t
  have key := h.mixLogZ_convexOn.2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) ha hb hab
  simp only [affLogZ_line, smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero,
    one_smul, add_sub_cancel] at key
  have hx : a • x + b • y = x + b • (y - x) := by
    rw [show a = 1 - b by linarith]
    module
  rwa [hx]

/-- **Concavity of the free energy on the affine space of data** (`t > 0`). -/
theorem affFreeEnergy_concaveOn {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
    (hπ : ∀ x, 0 ≤ π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
    (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t) :
    ConcaveOn ℝ univ (affFreeEnergy μ π L₀ R t) := by
  have h := ((affLogZ_convexOn hπm hπi hπ hπpos hL₀m hL₀ hR t).neg).smul
    (by positivity : (0 : ℝ) ≤ 1 / t)
  refine h.congr fun a _ ↦ ?_
  simp only [Pi.neg_apply, smul_eq_mul, affFreeEnergy]
  ring

/-- `D_v A_t(a) = −t ⟨R_v⟩_a`: the gradient of the log-partition function is minus `t` times the
mean loss contrast. -/
theorem TiltData.hasDerivAt_affLogZ_dir {π L₀ : X → ℝ} {R : ι → X → ℝ} {a : ι → ℝ} {t M₀ : ℝ}
    (h : TiltData μ (baseWeight π (affLoss L₀ R a) t) (fun _ ↦ 0) M₀) (hR : ∀ i, Bdd (R i))
    (v : ι → ℝ) :
    HasDerivAt (fun ε : ℝ ↦ affLogZ μ π L₀ R t (a + ε • v))
      (-t * priorExp μ π (affLoss L₀ R a) (dirLoss R v) t) 0 := by
  obtain ⟨hvm, Mv, hvb⟩ := bdd_dirLoss hR v
  have key := (h.changeR hvm hvb).hasDerivAt_mixLogZ 0
  simp only [affLogZ_line] at key
  have e : mixExp μ π (affLoss L₀ R a) (dirLoss R v) (dirLoss R v) t 0 =
      priorExp μ π (affLoss L₀ R a) (dirLoss R v) t := by
    unfold mixExp
    congr 1
    funext x
    simp [pathLoss]
  rwa [e] at key

/-- `D_v² A_t(a) = g_a(v, v)`: the Hessian of the log-partition function is the response form. -/
theorem TiltData.hasDerivAt_deriv_affLogZ_dir {π L₀ : X → ℝ} {R : ι → X → ℝ} {a : ι → ℝ}
    {t M₀ : ℝ} (h : TiltData μ (baseWeight π (affLoss L₀ R a) t) (fun _ ↦ 0) M₀)
    (hR : ∀ i, Bdd (R i)) (v : ι → ℝ) :
    HasDerivAt (deriv fun ε : ℝ ↦ affLogZ μ π L₀ R t (a + ε • v))
      (responseForm μ π L₀ R a t v v) 0 := by
  have key := h.hasDerivAt_deriv_mixLogZ_dir hR v
  simp only [affLogZ_line] at key
  exact key

end Laplace.Multi
