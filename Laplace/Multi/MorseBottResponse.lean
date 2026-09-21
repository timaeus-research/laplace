/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.MorseBottNormalForm

/-!
# The response of the Morse–Bott measure to a variation of the truth

Astra's item (C) (`research_truth_variation_v1`): in a one-parameter family `u ↦ H_u(y)` of
transverse Hessian fields (a "resolution-free prototype" of differentiating on a fixed resolved
family), the tangential Morse–Bott density `ρ_u = ∫ K_{H_u(y)} = (2π)^{r/2} det H_u^{-1/2}`
responds by
`∂_u ρ_u = -½ ρ_u · tr(H_u⁻¹ ∂_u H_u)`
(`hasDerivAt_mbDensity_family`, Jacobi's formula obtained from the Gaussian second moments
`∫ xᵢxⱼ K_H = ρ (H⁻¹)ᵢⱼ` rather than from the determinant), and the normalised tangential
expectation `E_{ρ_u}[g] = ∫ g χ ρ_u / ∫ χ ρ_u` by
`d/du E_{ρ_u}[g] = Cov_{ρ_u}(g, S_u)`, `S_u = -½ tr(H_u⁻¹ ∂_u H_u)`
(`hasDerivAt_tanExp_family`). Since the exact Morse–Bott expectations of tangential monomials are
these tangential expectations at every temperature (R7), this is the derivative of the
expectation values themselves along the family (`hasDerivAt_mbExp_tangential_family`).
Hypotheses (`MBFamilyData`): the normal-form data for every `u`, differentiability of `H_u(y)` in
`u` with derivative `H'_u(y)`, continuity of `H'_u` in `y`, and `|xᵀ H'_u(y) x| ≤ B |x|²`.
-/

open Real MeasureTheory Filter Topology
open scoped Matrix

namespace Laplace.Multi

variable {r n : ℕ}

/-! ### The quadratic form is linear in the matrix -/

theorem qform_eq_sum (A : Matrix (Fin r) (Fin r) ℝ) (x : EuclidD r) :
    qform A x = ∑ i, x i * ∑ j, A i j * x j := by
  rw [qform_eq_dotProduct]
  simp only [dotProduct, Matrix.mulVec]

theorem hasDerivAt_qform_param {H : ℝ → Matrix (Fin r) (Fin r) ℝ} {H' : Matrix (Fin r) (Fin r) ℝ}
    {u₀ : ℝ} (hH : HasDerivAt H H' u₀) (x : EuclidD r) :
    HasDerivAt (fun u ↦ qform (H u) x) (qform H' x) u₀ := by
  simp only [qform_eq_sum]
  have hent : ∀ i j, HasDerivAt (fun u ↦ H u i j) (H' i j) u₀ := fun i j ↦
    hasDerivAt_pi.mp (hasDerivAt_pi.mp hH i) j
  have hrow : ∀ i, HasDerivAt (fun u ↦ ∑ j, H u i j * x j) (∑ j, H' i j * x j) u₀ := fun i ↦ by
    have := HasDerivAt.sum (u := Finset.univ) (A := fun j u ↦ H u i j * x j)
      (A' := fun j ↦ H' i j * x j) fun j _ ↦ (hent i j).mul_const (x j)
    have hfun : (fun u ↦ ∑ j, H u i j * x j) = ∑ j, fun u ↦ H u i j * x j := by
      funext u
      simp [Finset.sum_apply]
    rw [hfun]
    exact this
  have := HasDerivAt.sum (u := Finset.univ) (A := fun i u ↦ x i * ∑ j, H u i j * x j)
    (A' := fun i ↦ x i * ∑ j, H' i j * x j) fun i _ ↦ (hrow i).const_mul (x i)
  have hfun : (fun u ↦ ∑ i, x i * ∑ j, H u i j * x j) =
      ∑ i, fun u ↦ x i * ∑ j, H u i j * x j := by
    funext u
    simp [Finset.sum_apply]
  rw [hfun]
  exact this

/-! ### Jacobi via the second moments: `∫ xᵀAx K_H = tr(A H⁻¹) ∫ K_H` -/

theorem integrable_coord_mul_coord_quadKernel {H : Matrix (Fin r) (Fin r) ℝ} (hH : H.PosDef)
    (i j : Fin r) : Integrable fun x : EuclidD r ↦ x i * x j * quadKernel H x := by
  refine (quadKernel_integrable_pow hH 2).mono' (by
    exact (((continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin r ↦ ℝ))).mul
      ((continuous_apply j).comp (PiLp.continuous_ofLp 2 (fun _ : Fin r ↦ ℝ)))).mul
      (quadKernel_continuous H) |>.aestronglyMeasurable) (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (quadKernel_pos _ _)]
  refine mul_le_mul_of_nonneg_right ?_ (quadKernel_pos _ _).le
  rw [abs_mul, sq]
  exact mul_le_mul (euclid_abs_coord_le_norm x i) (euclid_abs_coord_le_norm x j) (abs_nonneg _)
    (norm_nonneg _)

theorem integral_qform_mul_quadKernel_eq_trace (A : Matrix (Fin r) (Fin r) ℝ)
    {H : Matrix (Fin r) (Fin r) ℝ} (hH : H.PosDef) :
    ∫ x : EuclidD r, qform A x * quadKernel H x =
      Matrix.trace (A * H⁻¹) * ∫ x : EuclidD r, quadKernel H x := by
  simp only [qform_eq_sum]
  have hpt : ∀ x : EuclidD r, (∑ i, x i * ∑ j, A i j * x j) * quadKernel H x =
      ∑ i, ∑ j, A i j * (x i * x j * quadKernel H x) := by
    intro x
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  simp only [hpt]
  rw [integral_finsetSum (f := fun i (x : EuclidD r) ↦ ∑ j, A i j * (x i * x j * quadKernel H x)) _
    fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      (integrable_coord_mul_coord_quadKernel hH i j).const_mul _]
  have hin : ∀ i, (∫ x : EuclidD r, ∑ j, A i j * (x i * x j * quadKernel H x)) =
      ∑ j, A i j * (jacInv H * (2 * π) ^ ((r : ℝ) / 2) * H⁻¹ i j) := by
    intro i
    rw [integral_finsetSum (f := fun j (x : EuclidD r) ↦ A i j * (x i * x j * quadKernel H x)) _
      fun j _ ↦ (integrable_coord_mul_coord_quadKernel hH i j).const_mul _]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_const_mul, integral_coord_mul_coord_quadKernel hH]
  simp only [hin, integral_quadKernel hH]
  -- `Σᵢⱼ Aᵢⱼ (H⁻¹)ᵢⱼ = tr(A H⁻¹)` by symmetry of `H⁻¹`
  have hsymm : ∀ i j, H⁻¹ i j = H⁻¹ j i := fun i j ↦ by
    have := hH.isHermitian.inv.apply i j
    simpa using this.symm
  rw [Matrix.trace, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hsymm j i]
  ring

/-! ### The family -/

/-- A one-parameter family of Morse–Bott normal forms: the normal-form data for every `u`, the
`u`-derivative `H'` of the Hessian field, its continuity in `y`, and the bound `|xᵀH'x| ≤ B|x|²`. -/
structure MBFamilyData (H H' : ℝ → EuclidD n → Matrix (Fin r) (Fin r) ℝ) (χ : EuclidD n → ℝ)
    (c B : ℝ) : Prop where
  base : ∀ u, MBData (H u) χ c
  deriv : ∀ u y, HasDerivAt (fun v ↦ H v y) (H' u y) u
  cont' : ∀ u, Continuous (H' u)
  B_nonneg : 0 ≤ B
  qbound : ∀ u y x, |qform (H' u y) x| ≤ B * ‖x‖ ^ 2

/-- The log-derivative of the Morse–Bott density: `S_u(y) = -½ tr(H_u(y)⁻¹ H'_u(y))`. -/
noncomputable def mbScore (H H' : ℝ → EuclidD n → Matrix (Fin r) (Fin r) ℝ) (u : ℝ)
    (y : EuclidD n) : ℝ :=
  -(1 / 2 : ℝ) * Matrix.trace ((H u y)⁻¹ * H' u y)

theorem MBFamilyData.abs_deriv_integrand_le {H H' : ℝ → EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {χ : EuclidD n → ℝ} {c B : ℝ} (h : MBFamilyData H H' χ c B) (u : ℝ) (y : EuclidD n)
    (x : EuclidD r) :
    |-(1 / 2 : ℝ) * qform (H' u y) x * quadKernel (H u y) x| ≤
      1 / 2 * B * (‖x‖ ^ 2 * Real.exp (-(c / 2) * ‖x‖ ^ 2)) := by
  have hB := h.B_nonneg
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    abs_of_pos (quadKernel_pos _ _)]
  have h1 := h.qbound u y x
  have h2 := quadKernel_le_exp_of_ellip ((h.base u).ellip y) x
  calc 1 / 2 * |qform (H' u y) x| * quadKernel (H u y) x
      ≤ 1 / 2 * (B * ‖x‖ ^ 2) * Real.exp (-(c / 2) * ‖x‖ ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (quadKernel_pos _ _).le
          (by positivity)
    _ = 1 / 2 * B * (‖x‖ ^ 2 * Real.exp (-(c / 2) * ‖x‖ ^ 2)) := by ring

/-- **Jacobi's formula for the Morse–Bott density, from the second moments**:
`∂_u ρ_u(y) = -½ tr(H_u⁻¹ H'_u) ρ_u(y)`. -/
theorem MBFamilyData.hasDerivAt_mbDensity {H H' : ℝ → EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {χ : EuclidD n → ℝ} {c B : ℝ} (h : MBFamilyData H H' χ c B) (u₀ : ℝ) (y : EuclidD n) :
    HasDerivAt (fun u ↦ mbDensity (H u) y) (mbScore H H' u₀ y * mbDensity (H u₀) y) u₀ := by
  have hc := (h.base u₀).c_pos
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (EuclidD r))) (F := fun u x ↦ quadKernel (H u y) x)
    (F' := fun u x ↦ -(1 / 2 : ℝ) * qform (H' u y) x * quadKernel (H u y) x)
    (bound := fun x ↦ 1 / 2 * B * (‖x‖ ^ 2 * Real.exp (-(c / 2) * ‖x‖ ^ 2)))
    (x₀ := u₀) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun u ↦ (quadKernel_continuous _).aestronglyMeasurable)
    (quadKernel_integrable ((h.base u₀).posDef y))
    (((continuous_const.mul (qform_continuous _)).mul
      (quadKernel_continuous _)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x u _ ↦ by
      rw [Real.norm_eq_abs]
      exact h.abs_deriv_integrand_le u y x)
    ((integrable_pow_mul_exp_neg_mul_sq (d := r) (half_pos hc) 2).const_mul _)
    (Filter.Eventually.of_forall fun x u _ ↦ ?_)
  · have hval : (∫ x : EuclidD r, -(1 / 2 : ℝ) * qform (H' u₀ y) x * quadKernel (H u₀ y) x) =
        mbScore H H' u₀ y * mbDensity (H u₀) y := by
      have : (fun x : EuclidD r ↦ -(1 / 2 : ℝ) * qform (H' u₀ y) x * quadKernel (H u₀ y) x) =
          fun x ↦ -(1 / 2 : ℝ) * (qform (H' u₀ y) x * quadKernel (H u₀ y) x) := by
        funext x
        ring
      rw [this, integral_const_mul, integral_qform_mul_quadKernel_eq_trace _ ((h.base u₀).posDef y)]
      unfold mbScore mbDensity
      rw [Matrix.trace_mul_comm]
      ring
    rw [hval] at key
    exact key.2
  · -- differentiability of `u ↦ e^{-q_{H_u}(x)/2}`
    have hq := hasDerivAt_qform_param (h.deriv u y) x
    have h1 : HasDerivAt (fun v ↦ -qform (H v y) x / 2) (-qform (H' u y) x / 2) u :=
      hq.neg.div_const 2
    have h2 := h1.exp
    unfold quadKernel
    refine h2.congr_deriv ?_
    ring

/-- Uniform bound on `|∂_u ρ_u(y)|`. -/
theorem MBFamilyData.abs_deriv_mbDensity_le {H H' : ℝ → EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {χ : EuclidD n → ℝ} {c B : ℝ} (h : MBFamilyData H H' χ c B) (u : ℝ) (y : EuclidD n) :
    |mbScore H H' u y * mbDensity (H u) y| ≤
      1 / 2 * B * ∫ x : EuclidD r, ‖x‖ ^ 2 * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
  have hc := (h.base u).c_pos
  have hval : mbScore H H' u y * mbDensity (H u) y =
      ∫ x : EuclidD r, -(1 / 2 : ℝ) * qform (H' u y) x * quadKernel (H u y) x := by
    have : (fun x : EuclidD r ↦ -(1 / 2 : ℝ) * qform (H' u y) x * quadKernel (H u y) x) =
        fun x ↦ -(1 / 2 : ℝ) * (qform (H' u y) x * quadKernel (H u y) x) := by
      funext x
      ring
    rw [this, integral_const_mul, integral_qform_mul_quadKernel_eq_trace _ ((h.base u).posDef y)]
    unfold mbScore mbDensity
    rw [Matrix.trace_mul_comm]
    ring
  rw [hval, ← Real.norm_eq_abs, ← integral_const_mul]
  exact norm_integral_le_of_norm_le
    ((integrable_pow_mul_exp_neg_mul_sq (d := r) (half_pos hc) 2).const_mul _)
    (Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]
      exact h.abs_deriv_integrand_le u y x)

theorem MBFamilyData.continuous_deriv_mbDensity {H H' : ℝ → EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {χ : EuclidD n → ℝ} {c B : ℝ} (h : MBFamilyData H H' χ c B) (u : ℝ) :
    Continuous fun y ↦ mbScore H H' u y * mbDensity (H u) y := by
  have hc := (h.base u).c_pos
  have hval : (fun y ↦ mbScore H H' u y * mbDensity (H u) y) =
      fun y ↦ ∫ x : EuclidD r, -(1 / 2 : ℝ) * qform (H' u y) x * quadKernel (H u y) x := by
    funext y
    have : (fun x : EuclidD r ↦ -(1 / 2 : ℝ) * qform (H' u y) x * quadKernel (H u y) x) =
        fun x ↦ -(1 / 2 : ℝ) * (qform (H' u y) x * quadKernel (H u y) x) := by
      funext x
      ring
    rw [this, integral_const_mul, integral_qform_mul_quadKernel_eq_trace _ ((h.base u).posDef y)]
    unfold mbScore mbDensity
    rw [Matrix.trace_mul_comm]
    ring
  rw [hval]
  refine continuous_of_dominated
    (bound := fun x : EuclidD r ↦ 1 / 2 * B * (‖x‖ ^ 2 * Real.exp (-(c / 2) * ‖x‖ ^ 2)))
    (fun y ↦ ((continuous_const.mul (qform_continuous _)).mul
      (quadKernel_continuous _)).aestronglyMeasurable)
    (fun y ↦ Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]
      exact h.abs_deriv_integrand_le u y x)
    ((integrable_pow_mul_exp_neg_mul_sq (d := r) (half_pos hc) 2).const_mul _)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  have h1 : Continuous fun y ↦ qform (H' u y) x := continuous_qform_in_matrix (h.cont' u) x
  have h2 : Continuous fun y ↦ quadKernel (H u y) x := by
    unfold quadKernel
    exact Real.continuous_exp.comp
      (((continuous_qform_in_matrix (h.base u).cont x).neg).div_const 2)
  exact (continuous_const.mul h1).mul h2

/-! ### The response of the tangential expectation -/

/-- The tangential normalised expectation `E_{ρ}[g] = ∫ g χ ρ / ∫ χ ρ`. -/
noncomputable def tanExp (χ ρ g : EuclidD n → ℝ) : ℝ :=
  (∫ y, g y * (χ y * ρ y)) / ∫ y, χ y * ρ y

/-- `d/du ∫ g χ ρ_u = ∫ g χ (S_u ρ_u)`. -/
theorem MBFamilyData.hasDerivAt_integral_mul_mbDensity
    {H H' : ℝ → EuclidD n → Matrix (Fin r) (Fin r) ℝ} {χ : EuclidD n → ℝ} {c B : ℝ}
    (h : MBFamilyData H H' χ c B) {g : EuclidD n → ℝ} (hg : Continuous g) (u₀ : ℝ) :
    HasDerivAt (fun u ↦ ∫ y, g y * (χ y * mbDensity (H u) y))
      (∫ y, g y * (χ y * (mbScore H H' u₀ y * mbDensity (H u₀) y))) u₀ := by
  have hχc := (h.base u₀).χ_cont
  have hχs := (h.base u₀).χ_supp
  set I₂ : ℝ := ∫ x : EuclidD r, ‖x‖ ^ 2 * Real.exp (-(c / 2) * ‖x‖ ^ 2) with hI₂
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (EuclidD n))) (F := fun u y ↦ g y * (χ y * mbDensity (H u) y))
    (F' := fun u y ↦ g y * (χ y * (mbScore H H' u y * mbDensity (H u) y)))
    (bound := fun y ↦ |g y * χ y| * (1 / 2 * B * I₂))
    (x₀ := u₀) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun u ↦
      (hg.mul (hχc.mul (mbDensity_continuous (h.base u)))).aestronglyMeasurable)
    ((hg.mul (hχc.mul (mbDensity_continuous (h.base u₀)))).integrable_of_hasCompactSupport
      (hχs.mul_right.mul_left))
    ((hg.mul (hχc.mul (h.continuous_deriv_mbDensity u₀))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y u _ ↦ by
      rw [Real.norm_eq_abs, show g y * (χ y * (mbScore H H' u y * mbDensity (H u) y)) =
        (g y * χ y) * (mbScore H H' u y * mbDensity (H u) y) by ring, abs_mul]
      exact mul_le_mul_of_nonneg_left (h.abs_deriv_mbDensity_le u y) (abs_nonneg _))
    (((hg.mul hχc).integrable_of_hasCompactSupport hχs.mul_left).abs.mul_const _)
    (Filter.Eventually.of_forall fun y u _ ↦
      ((h.hasDerivAt_mbDensity u y).const_mul (χ y)).const_mul (g y))
  exact key.2

/-- **The response of the Morse–Bott measure**: `d/du E_{ρ_u}[g] = Cov_{ρ_u}(g, S_u)` with
`S_u = -½ tr(H_u⁻¹ H'_u)`. -/
theorem MBFamilyData.hasDerivAt_tanExp {H H' : ℝ → EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {χ : EuclidD n → ℝ} {c B : ℝ} (h : MBFamilyData H H' χ c B) {g : EuclidD n → ℝ}
    (hg : Continuous g) {y₀ : EuclidD n} (hy₀ : χ y₀ ≠ 0) (u₀ : ℝ) :
    HasDerivAt (fun u ↦ tanExp χ (mbDensity (H u)) g)
      (tanExp χ (mbDensity (H u₀)) (fun y ↦ g y * mbScore H H' u₀ y) -
        tanExp χ (mbDensity (H u₀)) g * tanExp χ (mbDensity (H u₀)) (mbScore H H' u₀)) u₀ := by
  have hN := h.hasDerivAt_integral_mul_mbDensity hg u₀
  have hZ := h.hasDerivAt_integral_mul_mbDensity (g := fun _ ↦ (1 : ℝ)) continuous_const u₀
  simp only [one_mul] at hZ
  have hZpos : 0 < ∫ y, χ y * mbDensity (H u₀) y :=
    integral_cutoff_mul_mbDensity_pos (h.base u₀) hy₀
  have hd := hN.div hZ hZpos.ne'
  unfold tanExp
  refine hd.congr_deriv ?_
  have e1 : (∫ y, g y * (χ y * (mbScore H H' u₀ y * mbDensity (H u₀) y))) =
      ∫ y, g y * mbScore H H' u₀ y * (χ y * mbDensity (H u₀) y) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    ring
  have e2 : (∫ y, χ y * (mbScore H H' u₀ y * mbDensity (H u₀) y)) =
      ∫ y, mbScore H H' u₀ y * (χ y * mbDensity (H u₀) y) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    ring
  rw [e1, e2]
  field_simp

/-- **The response of the expectation values.** In the exact normal form the Morse–Bott
expectation of a tangential monomial is its tangential expectation at every temperature (R7), so
along the family `d/du E_{H_u,t}[yᵛ] = Cov_{ρ_u}(yᵛ, S_u)`. -/
theorem MBFamilyData.hasDerivAt_mbExp_tangential {H H' : ℝ → EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {χ : EuclidD n → ℝ} {c B : ℝ} (h : MBFamilyData H H' χ c B) {y₀ : EuclidD n} (hy₀ : χ y₀ ≠ 0)
    {t : ℝ} (ht : 0 < t) {q : ℕ} (w : Fin q → Fin n) (u₀ : ℝ) :
    HasDerivAt (fun u ↦ mbExp (H u) χ t (fun z ↦ monomialTest w z.2))
      (tanExp χ (mbDensity (H u₀)) (fun y ↦ monomialTest w y * mbScore H H' u₀ y) -
        tanExp χ (mbDensity (H u₀)) (monomialTest w) *
          tanExp χ (mbDensity (H u₀)) (mbScore H H' u₀)) u₀ := by
  have := h.hasDerivAt_tanExp (monomialTest_continuous w) hy₀ u₀
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u ↦ ?_)
  change mbExp (H u) χ t (fun z ↦ monomialTest w z.2) =
    tanExp χ (mbDensity (H u)) (monomialTest w)
  rw [mbExp_tangential (h.base u) ht hy₀ w]
  rfl

end Laplace.Multi
