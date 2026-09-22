/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.SeparableExact
import Laplace.Multi.GaussianMomentsPosDef

/-!
# The rotation law for Gibbs moments

The note writes its anharmonic potential in a rotated frame, `L(w) = ∑ᵢ ℓᵢ(uᵢ)` with
`u = Qᵀ(w − w*)` for a random orthogonal `Q`, and measures the sampled covariance "projected onto
the eigenvectors of `P`", i.e. along the columns of `Q`. This file transports the exact statements
of `SeparableExact` to that frame:

* `affineFrame Q c w = Qᵀ(w − c)`, `abs_det_of_orthogonal`, `integral_comp_affineFrame`: the frame
  change preserves Lebesgue measure (`|det Q| = 1` plus translation invariance);
* `rotated Q c L = L ∘ affineFrame Q c`, `partitionFunction_rotated`, `gibbsExpectation_rotated`,
  `gibbsCov_rotated` (+ `_of_continuous`): `Z`, expectations of `φ ∘ A` and covariances are
  invariant; `gibbsExpectation_rotated_self`: the energy `⟨L⟩` is frame-independent;
* `rotatedAnharmonic` and E2 in the note's frame: the variance along `Q eᵢ` is the one-dimensional
  anharmonic variance (`gibbsCov_rotatedAnharmonic`), so `rotatedAnharmonic_var_second_order`,
  `rotatedAnharmonic_var_relative_rate_note` (`→ a² − 1/2`), `rotatedAnharmonic_mean_asymptotic`
  and `rotatedAnharmonic_energy_asymptotic` (`t⟨L⟩ → d/2`) hold verbatim.
-/

open MeasureTheory Filter Topology Matrix Laplace.OneD

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The frame change preserves Lebesgue measure -/

section Affine

/-- The frame change `A w = Qᵀ (w − c)` of the note (`u = Qᵀ(w − w*)`). -/
def affineFrame (Q : Matrix ι ι ℝ) (c : ι → ℝ) (w : ι → ℝ) : ι → ℝ := Qᵀ *ᵥ (w - c)

omit [DecidableEq ι] in
/-- The `i`-th new coordinate is the projection onto the `i`-th column of `Q`. -/
theorem affineFrame_apply (Q : Matrix ι ι ℝ) (c w : ι → ℝ) (i : ι) :
    affineFrame Q c w i = ∑ j, Q j i * (w j - c j) := by
  simp [affineFrame, mulVec, dotProduct, transpose_apply]

theorem abs_det_of_orthogonal {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) : |Q.det| = 1 := by
  have h : Q.det * Q.det = 1 := by
    have := congrArg Matrix.det hQ
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  rw [← Real.sqrt_sq_eq_abs, sq, h, Real.sqrt_one]

theorem det_transpose_ne_zero_of_orthogonal {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) : Qᵀ.det ≠ 0 := by
  rw [Matrix.det_transpose]
  intro h
  have := abs_det_of_orthogonal hQ
  rw [h, abs_zero] at this
  exact zero_ne_one this

/-- **Change of variables for the frame change**: `∫ g(Qᵀ(w − c)) dw = ∫ g(u) du`. -/
theorem integral_comp_affineFrame {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    (g : (ι → ℝ) → ℝ) (hg : AEStronglyMeasurable g volume) :
    ∫ w, g (affineFrame Q c w) = ∫ u, g u := by
  have h1 : ∫ w, g (affineFrame Q c w) = ∫ w, g (Qᵀ *ᵥ w) :=
    integral_sub_right_eq_self (fun w => g (Qᵀ *ᵥ w)) c
  rw [h1, integral_comp_mulVec Qᵀ (det_transpose_ne_zero_of_orthogonal hQ) g hg,
    Matrix.det_transpose, abs_det_of_orthogonal hQ, one_mul]

end Affine

/-! ### Gibbs moments are frame-independent -/

section Rotated

/-- The potential (or observable) in the rotated frame, `w ↦ L(Qᵀ(w − c))`. -/
def rotated (Q : Matrix ι ι ℝ) (c : ι → ℝ) (L : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  fun w => L (affineFrame Q c w)

theorem partitionFunction_rotated {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    (L : (ι → ℝ) → ℝ) (t : ℝ) (hL : AEStronglyMeasurable (fun u => Real.exp (-(t * L u))) volume) :
    partitionFunction (rotated Q c L) t = partitionFunction L t :=
  integral_comp_affineFrame hQ c (fun u => Real.exp (-(t * L u))) hL

/-- **Expectations are frame-independent**: `⟨φ ∘ A⟩_{L ∘ A} = ⟨φ⟩_L`. -/
theorem gibbsExpectation_rotated {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    (L φ : (ι → ℝ) → ℝ) (t : ℝ)
    (hL : AEStronglyMeasurable (fun u => Real.exp (-(t * L u))) volume)
    (hφ : AEStronglyMeasurable (fun u => φ u * Real.exp (-(t * L u))) volume) :
    gibbsExpectation (rotated Q c L) t (rotated Q c φ) = gibbsExpectation L t φ := by
  unfold gibbsExpectation
  rw [partitionFunction_rotated hQ c L t hL]
  congr 1
  exact integral_comp_affineFrame hQ c (fun u => φ u * Real.exp (-(t * L u))) hφ

/-- **Covariances are frame-independent**: `Cov_{L ∘ A}[φ ∘ A, ψ ∘ A] = Cov_L[φ, ψ]`. -/
theorem gibbsCov_rotated {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    (L φ ψ : (ι → ℝ) → ℝ) (t : ℝ)
    (hL : AEStronglyMeasurable (fun u => Real.exp (-(t * L u))) volume)
    (hφ : AEStronglyMeasurable (fun u => φ u * Real.exp (-(t * L u))) volume)
    (hψ : AEStronglyMeasurable (fun u => ψ u * Real.exp (-(t * L u))) volume)
    (hφψ : AEStronglyMeasurable (fun u => φ u * ψ u * Real.exp (-(t * L u))) volume) :
    gibbsCov (rotated Q c L) t (rotated Q c φ) (rotated Q c ψ) = gibbsCov L t φ ψ := by
  unfold gibbsCov
  rw [gibbsExpectation_rotated hQ c L φ t hL hφ, gibbsExpectation_rotated hQ c L ψ t hL hψ]
  congr 1
  exact gibbsExpectation_rotated hQ c L (fun u => φ u * ψ u) t hL hφψ

theorem gibbsExpectation_rotated_of_continuous {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    {L φ : (ι → ℝ) → ℝ} (hL : Continuous L) (hφ : Continuous φ) (t : ℝ) :
    gibbsExpectation (rotated Q c L) t (rotated Q c φ) = gibbsExpectation L t φ :=
  gibbsExpectation_rotated hQ c L φ t
    (by fun_prop : Continuous fun u => Real.exp (-(t * L u))).aestronglyMeasurable
    (by fun_prop : Continuous fun u => φ u * Real.exp (-(t * L u))).aestronglyMeasurable

theorem gibbsCov_rotated_of_continuous {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    {L φ ψ : (ι → ℝ) → ℝ} (hL : Continuous L) (hφ : Continuous φ) (hψ : Continuous ψ) (t : ℝ) :
    gibbsCov (rotated Q c L) t (rotated Q c φ) (rotated Q c ψ) = gibbsCov L t φ ψ :=
  gibbsCov_rotated hQ c L φ ψ t
    (by fun_prop : Continuous fun u => Real.exp (-(t * L u))).aestronglyMeasurable
    (by fun_prop : Continuous fun u => φ u * Real.exp (-(t * L u))).aestronglyMeasurable
    (by fun_prop : Continuous fun u => ψ u * Real.exp (-(t * L u))).aestronglyMeasurable
    (by fun_prop : Continuous fun u => φ u * ψ u * Real.exp (-(t * L u))).aestronglyMeasurable

/-- **The energy is frame-independent**: `⟨L ∘ A⟩_{L ∘ A} = ⟨L⟩_L`, so the LLC does not depend on
the frame the potential is written in. -/
theorem gibbsExpectation_rotated_self {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    {L : (ι → ℝ) → ℝ} (hL : Continuous L) (t : ℝ) :
    gibbsExpectation (rotated Q c L) t (rotated Q c L) = gibbsExpectation L t L :=
  gibbsExpectation_rotated_of_continuous hQ c hL hL t

/-- **Directional covariances**: the covariance of the new coordinates `(Aw)ᵢ = (Qeᵢ)·(w − c)`
under `L ∘ A` is the covariance of the old coordinates under `L`. -/
theorem gibbsCov_rotated_coord {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    {L : (ι → ℝ) → ℝ} (hL : Continuous L) (t : ℝ) (i j : ι) :
    gibbsCov (rotated Q c L) t (fun w => affineFrame Q c w i) (fun w => affineFrame Q c w j) =
      gibbsCov L t (fun u => u i) (fun u => u j) :=
  gibbsCov_rotated_of_continuous hQ c hL (continuous_apply i) (continuous_apply j) t

theorem gibbsExpectation_rotated_coord {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    {L : (ι → ℝ) → ℝ} (hL : Continuous L) (t : ℝ) (i : ι) :
    gibbsExpectation (rotated Q c L) t (fun w => affineFrame Q c w i) =
      gibbsExpectation L t (fun u => u i) :=
  gibbsExpectation_rotated_of_continuous hQ c hL (continuous_apply i) t

end Rotated

/-! ### E2 in the note's frame -/

section Anharmonic

variable {lam alpha gamma : ι → ℝ}

omit [DecidableEq ι] in
theorem continuous_separableAnharmonic (lam alpha gamma : ι → ℝ) :
    Continuous (separableAnharmonic lam alpha gamma) := by
  simp only [separableAnharmonic]
  refine continuous_finsetSum _ fun i _ => ?_
  unfold anharmonicPotential
  fun_prop

/-- The note's `anharm` potential: `L(w) = ∑ᵢ ℓᵢ(uᵢ)` with `u = Qᵀ(w − c)`. -/
noncomputable def rotatedAnharmonic (Q : Matrix ι ι ℝ) (c : ι → ℝ) (lam alpha gamma : ι → ℝ) :
    (ι → ℝ) → ℝ :=
  rotated Q c (separableAnharmonic lam alpha gamma)

theorem gibbsCov_rotatedAnharmonic_eq {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c : ι → ℝ) (t : ℝ)
    (i j : ι) :
    gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t (fun w => affineFrame Q c w i)
        (fun w => affineFrame Q c w j) =
      gibbsCov (separableAnharmonic lam alpha gamma) t (fun u => u i) (fun u => u j) :=
  gibbsCov_rotated_coord hQ c (continuous_separableAnharmonic lam alpha gamma) t i j

theorem gibbsExpectation_rotatedAnharmonic_eq {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    (t : ℝ) (i : ι) :
    gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) t (fun w => affineFrame Q c w i) =
      gibbsExpectation (separableAnharmonic lam alpha gamma) t (fun u => u i) :=
  gibbsExpectation_rotated_coord hQ c (continuous_separableAnharmonic lam alpha gamma) t i

theorem gibbsExpectation_rotatedAnharmonic_self {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    (t : ℝ) :
    gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) t
        (rotatedAnharmonic Q c lam alpha gamma) =
      gibbsExpectation (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma) :=
  gibbsExpectation_rotated_self hQ c (continuous_separableAnharmonic lam alpha gamma) t

/-- **The exact covariance of the note's `anharm` potential along the columns of `Q`** is diagonal
with the one-dimensional anharmonic variances. -/
theorem gibbsCov_rotatedAnharmonic {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1)
    (c : ι → ℝ) (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ} (ht : 0 < t) (i j : ι) :
    gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t (fun w => affineFrame Q c w i)
        (fun w => affineFrame Q c w j) =
      if i = j then _root_.Laplace.gibbsCov (anharmonicPotential (lam i) (alpha i) (gamma i)) t
        (fun x => x) (fun x => x) else 0 := by
  rw [gibbsCov_rotatedAnharmonic_eq hQ c t i j, gibbsCov_separableAnharmonic hlam hgamma hdisc ht]

/-- E2 in the note's frame, second order: along `Q eᵢ`,
`t²(Var − 1/(λᵢt)) → αᵢ²/λᵢ⁴ − γᵢ/(2λᵢ³)`. -/
theorem rotatedAnharmonic_var_second_order {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (i : ι) :
    Tendsto (fun t : ℝ => t ^ 2 * (gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t
        (fun w => affineFrame Q c w i) (fun w => affineFrame Q c w i) - 1 / (lam i * t))) atTop
      (𝓝 (alpha i ^ 2 / lam i ^ 4 - gamma i / (2 * lam i ^ 3))) := by
  refine (separableAnharmonic_var_second_order hlam hgamma hdisc i).congr'
    (Eventually.of_forall fun t => ?_)
  simp only [gibbsCov_rotatedAnharmonic_eq hQ c t i i]

/-- **E2 in the note's frame**: along every eigenvector `Q eᵢ` the exact relative covariance error
is `(a² − 1/2)/t + o(1/t)`. -/
theorem rotatedAnharmonic_var_relative_rate_note {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    {a : ℝ} (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, gamma i = lam i ^ 2)
    (halpha : ∀ i, alpha i ^ 2 = a ^ 2 * lam i ^ 3) (ha : a ^ 2 < 3) (i : ι) :
    Tendsto (fun t : ℝ => t * (lam i * t * gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t
        (fun w => affineFrame Q c w i) (fun w => affineFrame Q c w i) - 1)) atTop
      (𝓝 (a ^ 2 - 1 / 2)) := by
  refine (separableAnharmonic_var_relative_rate_note hlam hgamma halpha ha i).congr'
    (Eventually.of_forall fun t => ?_)
  simp only [gibbsCov_rotatedAnharmonic_eq hQ c t i i]

/-- E2 in the note's frame, the mean shift along `Q eᵢ`: `t ⟨(Qeᵢ)·(w − c)⟩ → −αᵢ/(2λᵢ²)`. -/
theorem rotatedAnharmonic_mean_asymptotic {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (i : ι) :
    Tendsto (fun t : ℝ => t * gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) t
        (fun w => affineFrame Q c w i)) atTop (𝓝 (-alpha i / (2 * lam i ^ 2))) := by
  refine (separableAnharmonic_mean_asymptotic hlam hgamma hdisc i).congr'
    (Eventually.of_forall fun t => ?_)
  simp only [gibbsExpectation_rotatedAnharmonic_eq hQ c t i]

/-- **E2's LLC in the note's frame**: `t⟨L⟩ → d/2` for the rotated anharmonic potential. -/
theorem rotatedAnharmonic_energy_asymptotic {Q : Matrix ι ι ℝ} (hQ : Qᵀ * Q = 1) (c : ι → ℝ)
    (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) :
    Tendsto (fun t : ℝ => t * gibbsExpectation (rotatedAnharmonic Q c lam alpha gamma) t
        (rotatedAnharmonic Q c lam alpha gamma)) atTop (𝓝 ((Fintype.card ι : ℝ) / 2)) := by
  refine (separableAnharmonic_energy_asymptotic hlam hgamma hdisc).congr'
    (Eventually.of_forall fun t => ?_)
  simp only [gibbsExpectation_rotatedAnharmonic_self hQ c t]

end Anharmonic

end Laplace.Multi
