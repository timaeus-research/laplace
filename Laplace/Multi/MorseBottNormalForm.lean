/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.MomentDeterminacy
import Laplace.Multi.QuadMoments
import Laplace.Multi.RateCalculus
import Laplace.Multi.Dilation
import Laplace.Multi.GaussianStein

/-!
# The Morse–Bott normal form: exact identification of the transverse Hessian field

The first non-isolated case of the germ ↔ expectation-value correspondence. In coordinates
`z = (x, y) ∈ ℝʳ × ℝⁿ` take the exact Morse–Bott normal form
`L(x, y) = ½ xᵀ H(y) x` with `y ↦ H(y)` a continuous, uniformly elliptic field of positive
definite matrices (zero set `W = {x = 0}`), and the tempered sampling weight `χ(y) e^{-tL}` with a
continuous, nonnegative, compactly supported tangential cutoff `χ`. The transverse integrals
are exact Gaussians, so EXACTLY in `t`:

* `E_t[yᵛ] = ∫ yᵛ χ ρ_H / ∫ χ ρ_H` with `ρ_H(y) = ∫ e^{-½xᵀH(y)x} dx` (`mbExp_tangential`) — the
  tangential monomials see the normalised **Morse–Bott density** `χ ρ_H`,
  `ρ_H = (2π)^{r/2} det H^{-1/2}`, independently of the temperature;
* `t · E_t[xᵢxₖ yᵛ] = ∫ yᵛ χ σ_H^{ik} / ∫ χ ρ_H` with
  `σ_H^{ik}(y) = ∫ xᵢxₖ e^{-½xᵀH(y)x} dx = ρ_H (H⁻¹)ᵢₖ` (`mbExp_transverse_second`) — the
  transverse second moments see the conditional covariance.

**Identification** (`mb_identification`): if two such fields `H₁, H₂` give the same normalised
expectations of the tangential monomials and of the transverse second moments `xᵢxₖyᵛ` (all `i, k`,
all tangential words `v`) at ONE temperature `t > 0`, then `H₁ = H₂` on `{χ ≠ 0}`. Proof:
moment determinacy (`MomentDeterminacy`) identifies the continuous compactly supported densities
`χ ρ_j / A_j` and `χ σ_j^{ik} / A_j`, `A_j = ∫ χ ρ_j`; their ratio is `(H_j(y))⁻¹ᵢₖ`
(`normalized_second_moment_quadKernel`), so the inverse Hessian fields agree where `χ ≠ 0`.
Higher transverse moments add nothing: every expectation in this model is a function of `H`.
(Astra consult `gpt_responses/research_morse_bott_normal_form_v1.md`.)
-/

open Real MeasureTheory Filter Topology
open scoped Matrix

namespace Laplace.Multi

variable {r n : ℕ}

/-! ### The model -/

/-- The Morse–Bott normal form `L(x, y) = ½ xᵀ H(y) x`. -/
noncomputable def mbLoss (H : EuclidD n → Matrix (Fin r) (Fin r) ℝ) (z : EuclidD r × EuclidD n) :
    ℝ :=
  qform (H z.2) z.1 / 2

/-- The tempered sampling weight `χ(y) e^{-tL}`. -/
noncomputable def mbWeight (H : EuclidD n → Matrix (Fin r) (Fin r) ℝ) (χ : EuclidD n → ℝ) (t : ℝ)
    (z : EuclidD r × EuclidD n) : ℝ :=
  χ z.2 * Real.exp (-(t * mbLoss H z))

/-- The normalised expectation `∫ φ χ e^{-tL} / ∫ χ e^{-tL}`. -/
noncomputable def mbExp (H : EuclidD n → Matrix (Fin r) (Fin r) ℝ) (χ : EuclidD n → ℝ) (t : ℝ)
    (φ : EuclidD r × EuclidD n → ℝ) : ℝ :=
  (∫ z, φ z * mbWeight H χ t z) / ∫ z, mbWeight H χ t z

/-- The tangential density `ρ_H(y) = ∫ e^{-½ xᵀH(y)x} dx = (2π)^{r/2} det H(y)^{-1/2}`. -/
noncomputable def mbDensity (H : EuclidD n → Matrix (Fin r) (Fin r) ℝ) (y : EuclidD n) : ℝ :=
  ∫ x : EuclidD r, quadKernel (H y) x

/-- The tangential second-moment density `σ_H^{ik}(y) = ∫ xᵢ xₖ e^{-½ xᵀH(y)x} dx`. -/
noncomputable def mbSecond (H : EuclidD n → Matrix (Fin r) (Fin r) ℝ) (i k : Fin r)
    (y : EuclidD n) : ℝ :=
  ∫ x : EuclidD r, x i * x k * quadKernel (H y) x

/-- The hypotheses: a continuous, uniformly elliptic field of positive definite transverse
Hessians and a continuous, nonnegative, compactly supported tangential cutoff. -/
structure MBData (H : EuclidD n → Matrix (Fin r) (Fin r) ℝ) (χ : EuclidD n → ℝ) (c : ℝ) :
    Prop where
  posDef : ∀ y, (H y).PosDef
  cont : Continuous H
  c_pos : 0 < c
  ellip : ∀ y x, c * ‖x‖ ^ 2 ≤ qform (H y) x
  χ_cont : Continuous χ
  χ_supp : HasCompactSupport χ
  χ_nonneg : ∀ y, 0 ≤ χ y

/-! ### Continuity of the quadratic form in the matrix -/

theorem continuous_qform_param {Y : Type*} [TopologicalSpace Y] {H : Y → Matrix (Fin r) (Fin r) ℝ}
    (hH : Continuous H) : Continuous fun p : EuclidD r × Y ↦ qform (H p.2) p.1 := by
  have h : (fun p : EuclidD r × Y ↦ qform (H p.2) p.1) =
      fun p ↦ WithLp.ofLp p.1 ⬝ᵥ (H p.2 *ᵥ WithLp.ofLp p.1) := by
    funext p
    exact qform_eq_dotProduct _ _
  rw [h]
  have hx : Continuous fun p : EuclidD r × Y ↦ WithLp.ofLp p.1 :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin r ↦ ℝ)).comp continuous_fst
  exact hx.dotProduct ((hH.comp continuous_snd).matrix_mulVec hx)

theorem continuous_qform_in_matrix {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ} (hH : Continuous H)
    (x : EuclidD r) : Continuous fun y ↦ qform (H y) x := by
  have h : (fun y ↦ qform (H y) x) = fun y ↦ WithLp.ofLp x ⬝ᵥ (H y *ᵥ WithLp.ofLp x) := by
    funext y
    exact qform_eq_dotProduct _ _
  rw [h]
  exact continuous_const.dotProduct (hH.matrix_mulVec continuous_const)

/-! ### Exact transverse Gaussian integrals -/

theorem exp_neg_mul_qform_eq (H : Matrix (Fin r) (Fin r) ℝ) {t : ℝ} (ht : 0 < t) (x : EuclidD r) :
    Real.exp (-(t * (qform H x / 2))) = quadKernel H (Real.sqrt t • x) := by
  unfold quadKernel
  rw [qform_smul, Real.sq_sqrt ht.le]
  congr 1
  ring

/-- `∫ e^{-t q/2} dx = t^{-r/2} ∫ K_H`. -/
theorem integral_exp_neg_mul_qform (H : Matrix (Fin r) (Fin r) ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ x : EuclidD r, Real.exp (-(t * (qform H x / 2))) =
      (Real.sqrt t)⁻¹ ^ r * ∫ x : EuclidD r, quadKernel H x := by
  have hs : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr ht)
  have h := integral_dilation (fun x : EuclidD r ↦ quadKernel H (Real.sqrt t • x)) hs
  simp only [exp_neg_mul_qform_eq H ht]
  rw [h]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only
  rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr ht).ne', one_smul]

/-- `∫ xᵢ xₖ e^{-t q/2} dx = t^{-r/2} t⁻¹ ∫ xᵢ xₖ K_H`. -/
theorem integral_coord_mul_coord_exp_neg_mul_qform (H : Matrix (Fin r) (Fin r) ℝ) {t : ℝ}
    (ht : 0 < t) (i k : Fin r) :
    ∫ x : EuclidD r, x i * x k * Real.exp (-(t * (qform H x / 2))) =
      (Real.sqrt t)⁻¹ ^ r * t⁻¹ * ∫ x : EuclidD r, x i * x k * quadKernel H x := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hst
  have h := integral_dilation (d := r)
    (fun x ↦ (x i * x k : ℝ) * quadKernel H ((Real.sqrt t • x : EuclidD r))) hs
  simp only [exp_neg_mul_qform_eq H ht]
  rw [h]
  have hsq : (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ = t⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt ht.le]
  rw [mul_assoc]
  congr 1
  rw [← hsq, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [smul_smul, mul_inv_cancel₀ hst.ne', one_smul]
  ring

/-! ### The tangential densities are continuous and positive -/

theorem quadKernel_le_exp_of_ellip {H : Matrix (Fin r) (Fin r) ℝ} {c : ℝ}
    (hell : ∀ x, c * ‖x‖ ^ 2 ≤ qform H x) (x : EuclidD r) :
    quadKernel H x ≤ Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
  unfold quadKernel
  apply Real.exp_le_exp.mpr
  have := hell x
  linarith

theorem mbDensity_pos {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ} {χ : EuclidD n → ℝ} {c : ℝ}
    (h : MBData H χ c) (y : EuclidD n) : 0 < mbDensity H y :=
  integral_quadKernel_pos (h.posDef y)

theorem mbDensity_continuous {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ} {χ : EuclidD n → ℝ} {c : ℝ}
    (h : MBData H χ c) : Continuous (mbDensity H) := by
  unfold mbDensity
  refine continuous_of_dominated (bound := fun x : EuclidD r ↦ Real.exp (-(c / 2) * ‖x‖ ^ 2))
    (fun y ↦ (quadKernel_continuous _).aestronglyMeasurable) (fun y ↦ ?_)
    (integrable_exp_neg_mul_sq_norm (half_pos h.c_pos)) ?_
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [Real.norm_eq_abs, abs_of_pos (quadKernel_pos _ _)]
    exact quadKernel_le_exp_of_ellip (h.ellip y) x
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    unfold quadKernel
    exact Real.continuous_exp.comp (((continuous_qform_in_matrix h.cont x).neg).div_const 2)

theorem mbSecond_continuous {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ} {χ : EuclidD n → ℝ} {c : ℝ}
    (h : MBData H χ c) (i k : Fin r) : Continuous (mbSecond H i k) := by
  unfold mbSecond
  refine continuous_of_dominated
    (bound := fun x : EuclidD r ↦ ‖x‖ ^ 2 * Real.exp (-(c / 2) * ‖x‖ ^ 2))
    (fun y ↦ (((continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin r ↦ ℝ))).mul
      ((continuous_apply k).comp (PiLp.continuous_ofLp 2 (fun _ : Fin r ↦ ℝ)))).mul
      (quadKernel_continuous _) |>.aestronglyMeasurable) (fun y ↦ ?_)
    (integrable_pow_mul_exp_neg_mul_sq (half_pos h.c_pos) 2) ?_
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (quadKernel_pos _ _)]
    have h1 : |x i * x k| ≤ ‖x‖ ^ 2 := by
      rw [abs_mul, sq]
      exact mul_le_mul (euclid_abs_coord_le_norm x i) (euclid_abs_coord_le_norm x k)
        (abs_nonneg _) (norm_nonneg _)
    exact mul_le_mul h1 (quadKernel_le_exp_of_ellip (h.ellip y) x) (quadKernel_pos _ _).le
      (by positivity)
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    unfold quadKernel
    exact continuous_const.mul
      (Real.continuous_exp.comp (((continuous_qform_in_matrix h.cont x).neg).div_const 2))

/-- The normalising constant `A = ∫ χ ρ_H` is positive once `χ` is not identically zero. -/
theorem integral_cutoff_mul_mbDensity_pos {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {χ : EuclidD n → ℝ} {c : ℝ} (h : MBData H χ c) {y₀ : EuclidD n} (hy₀ : χ y₀ ≠ 0) :
    0 < ∫ y, χ y * mbDensity H y := by
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := y₀)
    (h.χ_cont.mul (mbDensity_continuous h)) h.χ_supp.mul_right
    (fun y ↦ mul_nonneg (h.χ_nonneg y) (mbDensity_pos h y).le) ?_
  exact mul_ne_zero hy₀ (mbDensity_pos h y₀).ne'

/-! ### Joint integrability and Fubini -/

/-- The joint integrand `g(x) ψ(y) χ(y) e^{-tL}` is integrable when `g` is continuous with
`|g x| ≤ C ‖x‖^m` and `ψ` is continuous. -/
theorem integrable_mbWeight_mul {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ} {χ : EuclidD n → ℝ}
    {c : ℝ} (h : MBData H χ c) {t : ℝ} (ht : 0 < t) {g : EuclidD r → ℝ} (hg : Continuous g)
    {C : ℝ} {m : ℕ} (hgb : ∀ x, |g x| ≤ C * ‖x‖ ^ m) {ψ : EuclidD n → ℝ} (hψ : Continuous ψ) :
    Integrable fun z : EuclidD r × EuclidD n ↦ g z.1 * ψ z.2 * mbWeight H χ t z := by
  have hc := h.c_pos
  have hprod : Integrable (fun z : EuclidD r × EuclidD n ↦
      (C * (‖z.1‖ ^ m * Real.exp (-(t * c / 2) * ‖z.1‖ ^ 2))) * |ψ z.2 * χ z.2|) := by
    rw [Measure.volume_eq_prod]
    exact ((integrable_pow_mul_exp_neg_mul_sq (by positivity) m).const_mul C).mul_prod
      ((hψ.mul h.χ_cont).integrable_of_hasCompactSupport h.χ_supp.mul_left).abs
  refine hprod.mono' ?_ (Filter.Eventually.of_forall fun z ↦ ?_)
  · unfold mbWeight mbLoss
    exact ((hg.comp continuous_fst).mul (hψ.comp continuous_snd)).mul
      ((h.χ_cont.comp continuous_snd).mul (Real.continuous_exp.comp
        ((continuous_const.mul ((continuous_qform_param h.cont).div_const 2)).neg)))
      |>.aestronglyMeasurable
  · unfold mbWeight mbLoss
    rw [Real.norm_eq_abs]
    have hexp : Real.exp (-(t * (qform (H z.2) z.1 / 2))) ≤
        Real.exp (-(t * c / 2) * ‖z.1‖ ^ 2) := by
      apply Real.exp_le_exp.mpr
      have := h.ellip z.2 z.1
      nlinarith
    calc |g z.1 * ψ z.2 * (χ z.2 * Real.exp (-(t * (qform (H z.2) z.1 / 2))))|
        = |g z.1| * Real.exp (-(t * (qform (H z.2) z.1 / 2))) * |ψ z.2 * χ z.2| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
          ring
      _ ≤ (C * ‖z.1‖ ^ m) * Real.exp (-(t * c / 2) * ‖z.1‖ ^ 2) * |ψ z.2 * χ z.2| := by
          have hCx : 0 ≤ C * ‖z.1‖ ^ m := (abs_nonneg _).trans (hgb z.1)
          exact mul_le_mul (mul_le_mul (hgb z.1) hexp (Real.exp_pos _).le hCx) le_rfl
            (abs_nonneg _) (mul_nonneg hCx (Real.exp_pos _).le)
      _ = C * (‖z.1‖ ^ m * Real.exp (-(t * c / 2) * ‖z.1‖ ^ 2)) * |ψ z.2 * χ z.2| := by ring

/-- Fubini for the model: integrate the transverse variable first. -/
theorem integral_mbWeight_mul_eq {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ} {χ : EuclidD n → ℝ}
    {c : ℝ} (h : MBData H χ c) {t : ℝ} (ht : 0 < t) {g : EuclidD r → ℝ} (hg : Continuous g)
    {C : ℝ} {m : ℕ} (hgb : ∀ x, |g x| ≤ C * ‖x‖ ^ m) {ψ : EuclidD n → ℝ} (hψ : Continuous ψ) :
    ∫ z : EuclidD r × EuclidD n, g z.1 * ψ z.2 * mbWeight H χ t z =
      ∫ y, ψ y * χ y * ∫ x, g x * Real.exp (-(t * (qform (H y) x / 2))) := by
  have hi := integrable_mbWeight_mul h ht hg hgb hψ
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod_symm _ hi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [mbWeight, mbLoss]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only
  ring

/-! ### The two exact formulas -/

theorem abs_one_le (x : EuclidD r) : |(1 : ℝ)| ≤ 1 * ‖x‖ ^ 0 := by simp

theorem abs_coord_mul_coord_le (i k : Fin r) (x : EuclidD r) : |x i * x k| ≤ 1 * ‖x‖ ^ 2 := by
  rw [abs_mul, sq, one_mul]
  exact mul_le_mul (euclid_abs_coord_le_norm x i) (euclid_abs_coord_le_norm x k)
    (abs_nonneg _) (norm_nonneg _)

/-- The partition function: `∫ χ e^{-tL} = t^{-r/2} ∫ χ ρ_H`. -/
theorem integral_mbWeight {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ} {χ : EuclidD n → ℝ} {c : ℝ}
    (h : MBData H χ c) {t : ℝ} (ht : 0 < t) :
    ∫ z, mbWeight H χ t z = (Real.sqrt t)⁻¹ ^ r * ∫ y, χ y * mbDensity H y := by
  have := integral_mbWeight_mul_eq h ht (g := fun _ ↦ (1 : ℝ)) continuous_const (C := 1)
    (m := 0) abs_one_le (ψ := fun _ ↦ (1 : ℝ)) continuous_const
  simp only [one_mul] at this
  rw [this, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only
  rw [integral_exp_neg_mul_qform _ ht]
  unfold mbDensity
  ring

/-- **Tangential monomials see the Morse–Bott density**, independently of `t`:
`E_t[yᵛ] = ∫ yᵛ χ ρ_H / ∫ χ ρ_H`. -/
theorem mbExp_tangential {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ} {χ : EuclidD n → ℝ} {c : ℝ}
    (h : MBData H χ c) {t : ℝ} (ht : 0 < t) {y₀ : EuclidD n} (hy₀ : χ y₀ ≠ 0) {q : ℕ}
    (w : Fin q → Fin n) :
    mbExp H χ t (fun z ↦ monomialTest w z.2) =
      (∫ y, monomialTest w y * (χ y * mbDensity H y)) / ∫ y, χ y * mbDensity H y := by
  unfold mbExp
  have hnum := integral_mbWeight_mul_eq h ht (g := fun _ ↦ (1 : ℝ)) continuous_const (C := 1)
    (m := 0) abs_one_le (monomialTest_continuous w)
  simp only [one_mul] at hnum
  rw [hnum, integral_mbWeight h ht]
  have hA : (∫ y, χ y * mbDensity H y) ≠ 0 := (integral_cutoff_mul_mbDensity_pos h hy₀).ne'
  have hs : (Real.sqrt t)⁻¹ ^ r ≠ 0 := by
    have : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    positivity
  have hnum' : (∫ y, monomialTest w y * χ y * ∫ x : EuclidD r,
      Real.exp (-(t * (qform (H y) x / 2)))) =
      (Real.sqrt t)⁻¹ ^ r * ∫ y, monomialTest w y * (χ y * mbDensity H y) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only
    rw [integral_exp_neg_mul_qform _ ht]
    unfold mbDensity
    ring
  rw [hnum', mul_div_mul_left _ _ hs]

/-- **Transverse second moments see the conditional covariance**:
`E_t[xᵢ xₖ yᵛ] = t⁻¹ ∫ yᵛ χ σ_H^{ik} / ∫ χ ρ_H`. -/
theorem mbExp_transverse_second {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ} {χ : EuclidD n → ℝ}
    {c : ℝ} (h : MBData H χ c) {t : ℝ} (ht : 0 < t) {y₀ : EuclidD n} (hy₀ : χ y₀ ≠ 0)
    (i k : Fin r) {q : ℕ} (w : Fin q → Fin n) :
    mbExp H χ t (fun z ↦ z.1 i * z.1 k * monomialTest w z.2) =
      t⁻¹ * ((∫ y, monomialTest w y * (χ y * mbSecond H i k y)) / ∫ y, χ y * mbDensity H y) := by
  unfold mbExp
  have hnum := integral_mbWeight_mul_eq h ht (g := fun x : EuclidD r ↦ x i * x k)
    (((continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin r ↦ ℝ))).mul
      ((continuous_apply k).comp (PiLp.continuous_ofLp 2 (fun _ : Fin r ↦ ℝ)))) (C := 1) (m := 2)
    (abs_coord_mul_coord_le i k) (monomialTest_continuous w)
  rw [hnum, integral_mbWeight h ht]
  have hA : (∫ y, χ y * mbDensity H y) ≠ 0 := (integral_cutoff_mul_mbDensity_pos h hy₀).ne'
  have hs : (Real.sqrt t)⁻¹ ^ r ≠ 0 := by
    have : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    positivity
  have hnum' : (∫ y, monomialTest w y * χ y * ∫ x : EuclidD r,
      x i * x k * Real.exp (-(t * (qform (H y) x / 2)))) =
      (Real.sqrt t)⁻¹ ^ r * (t⁻¹ * ∫ y, monomialTest w y * (χ y * mbSecond H i k y)) := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only
    rw [integral_coord_mul_coord_exp_neg_mul_qform _ ht]
    unfold mbSecond
    ring
  rw [hnum', mul_div_mul_left _ _ hs, mul_div_assoc]

/-! ### Identification -/

/-- **Identification from the density ratios.** If the normalised tangential densities
`χ ρ_j / A_j` and second-moment densities `χ σ_j^{ik} / A_j` have the same monomial moments, the
Hessian fields agree where `χ ≠ 0`. This is the common core of the exact (`mb_identification`) and
the leading-order (`MorseBottLeading`) identification theorems. -/
theorem mb_identification_of_ratios {H₁ H₂ : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {χ : EuclidD n → ℝ} {c₁ c₂ : ℝ} (h₁ : MBData H₁ χ c₁) (h₂ : MBData H₂ χ c₂)
    {y₀ : EuclidD n} (hy₀ : χ y₀ ≠ 0)
    (hT : ∀ (q : ℕ) (w : Fin q → Fin n),
      (∫ y, monomialTest w y * (χ y * mbDensity H₁ y)) / ∫ y, χ y * mbDensity H₁ y =
        (∫ y, monomialTest w y * (χ y * mbDensity H₂ y)) / ∫ y, χ y * mbDensity H₂ y)
    (hN : ∀ (i k : Fin r) (q : ℕ) (w : Fin q → Fin n),
      (∫ y, monomialTest w y * (χ y * mbSecond H₁ i k y)) / ∫ y, χ y * mbDensity H₁ y =
        (∫ y, monomialTest w y * (χ y * mbSecond H₂ i k y)) / ∫ y, χ y * mbDensity H₂ y) :
    ∀ y, χ y ≠ 0 → H₁ y = H₂ y := by
  set A₁ := ∫ y, χ y * mbDensity H₁ y with hA₁
  set A₂ := ∫ y, χ y * mbDensity H₂ y with hA₂
  have hA₁p : 0 < A₁ := integral_cutoff_mul_mbDensity_pos h₁ hy₀
  have hA₂p : 0 < A₂ := integral_cutoff_mul_mbDensity_pos h₂ hy₀
  -- the tangential densities agree
  have hρ : (fun y ↦ χ y * (mbDensity H₁ y / A₁ - mbDensity H₂ y / A₂)) = 0 := by
    apply eq_zero_of_integral_monomialTest_mul_eq_zero
    · exact h₁.χ_cont.mul (((mbDensity_continuous h₁).div_const _).sub
        ((mbDensity_continuous h₂).div_const _))
    · exact h₁.χ_supp.mul_right
    · intro q w
      have hi₁ : Integrable fun y ↦ monomialTest w y * (χ y * mbDensity H₁ y) :=
        ((monomialTest_continuous w).mul (h₁.χ_cont.mul (mbDensity_continuous h₁)))
          |>.integrable_of_hasCompactSupport (h₁.χ_supp.mul_right.mul_left)
      have hi₂ : Integrable fun y ↦ monomialTest w y * (χ y * mbDensity H₂ y) :=
        ((monomialTest_continuous w).mul (h₂.χ_cont.mul (mbDensity_continuous h₂)))
          |>.integrable_of_hasCompactSupport (h₂.χ_supp.mul_right.mul_left)
      have hfun : (fun y ↦ monomialTest w y * (χ y * (mbDensity H₁ y / A₁ - mbDensity H₂ y / A₂))) =
          fun y ↦ monomialTest w y * (χ y * mbDensity H₁ y) / A₁ -
            monomialTest w y * (χ y * mbDensity H₂ y) / A₂ := by
        funext y
        ring
      rw [hfun, integral_sub (hi₁.div_const _) (hi₂.div_const _), integral_div, integral_div,
        hT q w, sub_self]
  -- the second-moment densities agree
  have hσ : ∀ i k : Fin r,
      (fun y ↦ χ y * (mbSecond H₁ i k y / A₁ - mbSecond H₂ i k y / A₂)) = 0 := by
    intro i k
    apply eq_zero_of_integral_monomialTest_mul_eq_zero
    · exact h₁.χ_cont.mul (((mbSecond_continuous h₁ i k).div_const _).sub
        ((mbSecond_continuous h₂ i k).div_const _))
    · exact h₁.χ_supp.mul_right
    · intro q w
      have hi₁ : Integrable fun y ↦ monomialTest w y * (χ y * mbSecond H₁ i k y) :=
        ((monomialTest_continuous w).mul (h₁.χ_cont.mul (mbSecond_continuous h₁ i k)))
          |>.integrable_of_hasCompactSupport (h₁.χ_supp.mul_right.mul_left)
      have hi₂ : Integrable fun y ↦ monomialTest w y * (χ y * mbSecond H₂ i k y) :=
        ((monomialTest_continuous w).mul (h₂.χ_cont.mul (mbSecond_continuous h₂ i k)))
          |>.integrable_of_hasCompactSupport (h₂.χ_supp.mul_right.mul_left)
      have hfun : (fun y ↦ monomialTest w y * (χ y * (mbSecond H₁ i k y / A₁ -
          mbSecond H₂ i k y / A₂))) =
          fun y ↦ monomialTest w y * (χ y * mbSecond H₁ i k y) / A₁ -
            monomialTest w y * (χ y * mbSecond H₂ i k y) / A₂ := by
        funext y
        ring
      rw [hfun, integral_sub (hi₁.div_const _) (hi₂.div_const _), integral_div, integral_div,
        hN i k q w, sub_self]
  intro y hy
  have hρy : mbDensity H₁ y / A₁ = mbDensity H₂ y / A₂ := by
    have := congrFun hρ y
    simp only [Pi.zero_apply, mul_eq_zero, hy, false_or] at this
    linarith
  have hρ₁ : 0 < mbDensity H₁ y := mbDensity_pos h₁ y
  have hρ₂ : 0 < mbDensity H₂ y := mbDensity_pos h₂ y
  have hinv : (H₁ y)⁻¹ = (H₂ y)⁻¹ := by
    ext i k
    have hσy : mbSecond H₁ i k y / A₁ = mbSecond H₂ i k y / A₂ := by
      have := congrFun (hσ i k) y
      simp only [Pi.zero_apply, mul_eq_zero, hy, false_or] at this
      linarith
    have key : mbSecond H₁ i k y / mbDensity H₁ y = mbSecond H₂ i k y / mbDensity H₂ y := by
      rw [div_eq_div_iff hρ₁.ne' hρ₂.ne']
      rw [div_eq_div_iff hA₁p.ne' hA₂p.ne'] at hρy hσy
      have e : mbSecond H₁ i k y * mbDensity H₂ y * A₁ =
          mbSecond H₂ i k y * mbDensity H₁ y * A₁ := by
        linear_combination mbDensity H₁ y * hσy - mbSecond H₁ i k y * hρy
      exact mul_right_cancel₀ hA₁p.ne' e
    have k₁ := normalized_second_moment_quadKernel (h₁.posDef y) i k
    have k₂ := normalized_second_moment_quadKernel (h₂.posDef y) i k
    unfold mbSecond mbDensity at key
    rw [← k₁, ← k₂, key]
  have hdet₁ : IsUnit (H₁ y).det := isUnit_iff_ne_zero.mpr (h₁.posDef y).det_pos.ne'
  have hdet₂ : IsUnit (H₂ y).det := isUnit_iff_ne_zero.mpr (h₂.posDef y).det_pos.ne'
  rw [← Matrix.nonsing_inv_nonsing_inv (H₁ y) hdet₁, hinv, Matrix.nonsing_inv_nonsing_inv _ hdet₂]

/-- **Exact identification of the transverse Hessian field at one temperature.** If two
Morse–Bott normal forms have the same normalised expectations of all tangential monomials `yᵛ`
and of all transverse second moments `xᵢ xₖ yᵛ` at a single temperature `t > 0`, then their
Hessian fields agree wherever the cutoff is nonzero. -/
theorem mb_identification {H₁ H₂ : EuclidD n → Matrix (Fin r) (Fin r) ℝ} {χ : EuclidD n → ℝ}
    {c₁ c₂ : ℝ} (h₁ : MBData H₁ χ c₁) (h₂ : MBData H₂ χ c₂) {t : ℝ} (ht : 0 < t)
    {y₀ : EuclidD n} (hy₀ : χ y₀ ≠ 0)
    (hT : ∀ (q : ℕ) (w : Fin q → Fin n),
      mbExp H₁ χ t (fun z ↦ monomialTest w z.2) = mbExp H₂ χ t (fun z ↦ monomialTest w z.2))
    (hN : ∀ (i k : Fin r) (q : ℕ) (w : Fin q → Fin n),
      mbExp H₁ χ t (fun z ↦ z.1 i * z.1 k * monomialTest w z.2) =
        mbExp H₂ χ t (fun z ↦ z.1 i * z.1 k * monomialTest w z.2)) :
    ∀ y, χ y ≠ 0 → H₁ y = H₂ y := by
  refine mb_identification_of_ratios h₁ h₂ hy₀ (fun q w ↦ ?_) (fun i k q w ↦ ?_)
  · rw [← mbExp_tangential h₁ ht hy₀ w, ← mbExp_tangential h₂ ht hy₀ w]
    exact hT q w
  · have h := hN i k q w
    rw [mbExp_transverse_second h₁ ht hy₀ i k w, mbExp_transverse_second h₂ ht hy₀ i k w] at h
    exact mul_left_cancel₀ (inv_ne_zero ht.ne') h

/-! ### The free energy: `λ = r/2` and the Morse–Bott volume -/

/-- **Exact free energy of the normal form**: `-log Z_t = (r/2) log t - log ∫ χ ρ_H`, so the
learning coefficient is `r/2` (multiplicity one) and the constant is the log Morse–Bott volume. -/
theorem neg_log_integral_mbWeight {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ} {χ : EuclidD n → ℝ}
    {c : ℝ} (h : MBData H χ c) {t : ℝ} (ht : 0 < t) {y₀ : EuclidD n} (hy₀ : χ y₀ ≠ 0) :
    -Real.log (∫ z, mbWeight H χ t z) =
      (r / 2 : ℝ) * Real.log t - Real.log (∫ y, χ y * mbDensity H y) := by
  rw [integral_mbWeight h ht, Real.log_mul (pow_ne_zero _ (inv_ne_zero (Real.sqrt_pos.mpr ht).ne'))
    (integral_cutoff_mul_mbDensity_pos h hy₀).ne', Real.log_pow, Real.log_inv, Real.log_sqrt ht.le]
  ring

/-! ### The energy observable: `t E_t[L] = r/2` exactly -/

/-- `∫ q e^{-t q/2} dx = t^{-r/2} t⁻¹ ∫ q K_H`. -/
theorem integral_qform_mul_exp_neg_mul_qform (H : Matrix (Fin r) (Fin r) ℝ) {t : ℝ}
    (ht : 0 < t) :
    ∫ x : EuclidD r, qform H x * Real.exp (-(t * (qform H x / 2))) =
      (Real.sqrt t)⁻¹ ^ r * t⁻¹ * ∫ x : EuclidD r, qform H x * quadKernel H x := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hst
  have h := integral_dilation (d := r)
    (fun x ↦ qform H x * quadKernel H ((Real.sqrt t • x : EuclidD r))) hs
  simp only [exp_neg_mul_qform_eq H ht]
  rw [h]
  have hsq : (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ = t⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt ht.le]
  rw [mul_assoc]
  congr 1
  rw [← hsq, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only
  rw [qform_smul, smul_smul, mul_inv_cancel₀ hst.ne', one_smul]
  ring

/-- `s e^{-a s} ≤ 1/(a e)` for `s ≥ 0`, `a > 0`. -/
theorem mul_exp_neg_le {a s : ℝ} (ha : 0 < a) (_hs : 0 ≤ s) :
    s * Real.exp (-(a * s)) ≤ (a * Real.exp 1)⁻¹ := by
  have h := Real.add_one_le_exp (a * s - 1)
  rw [sub_add_cancel, Real.exp_sub] at h
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hpos : 0 < Real.exp (a * s) := Real.exp_pos _
  rw [le_div_iff₀ he] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos,
    show (a * Real.exp 1)⁻¹ * Real.exp (a * s) = Real.exp (a * s) / (a * Real.exp 1) by ring,
    le_div_iff₀ (by positivity)]
  nlinarith [h]

/-- The energy integrand `L χ e^{-tL}` is integrable (bounded by `χ(y) (2/(te)) e^{-tc|x|²/4}`). -/
theorem integrable_mbLoss_mul_mbWeight {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {χ : EuclidD n → ℝ} {c : ℝ} (h : MBData H χ c) {t : ℝ} (ht : 0 < t) :
    Integrable fun z : EuclidD r × EuclidD n ↦ mbLoss H z * mbWeight H χ t z := by
  have hc := h.c_pos
  have hprod : Integrable (fun z : EuclidD r × EuclidD n ↦
      ((t / 4 * Real.exp 1)⁻¹ * Real.exp (-(t * c / 4) * ‖z.1‖ ^ 2)) * |χ z.2|) := by
    rw [Measure.volume_eq_prod]
    exact ((integrable_exp_neg_mul_sq_norm (by positivity)).const_mul _).mul_prod
      (h.χ_cont.integrable_of_hasCompactSupport h.χ_supp).abs
  refine hprod.mono' ?_ (Filter.Eventually.of_forall fun z ↦ ?_)
  · unfold mbWeight mbLoss
    exact (((continuous_qform_param h.cont).div_const 2).mul
      ((h.χ_cont.comp continuous_snd).mul (Real.continuous_exp.comp
        ((continuous_const.mul ((continuous_qform_param h.cont).div_const 2)).neg))))
      |>.aestronglyMeasurable
  · unfold mbWeight mbLoss
    rw [Real.norm_eq_abs]
    set q := qform (H z.2) z.1 with hq
    have hq0 : 0 ≤ q := (mul_nonneg hc.le (sq_nonneg _)).trans (h.ellip z.2 z.1)
    have hsplit : Real.exp (-(t * (q / 2))) =
        Real.exp (-(t / 4 * q)) * Real.exp (-(t / 4 * q)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h1 : q / 2 * Real.exp (-(t / 4 * q)) ≤ (t / 4 * Real.exp 1)⁻¹ := by
      have := mul_exp_neg_le (a := t / 4) (by positivity) hq0
      have hhalf : q / 2 ≤ q := by linarith
      calc q / 2 * Real.exp (-(t / 4 * q)) ≤ q * Real.exp (-(t / 4 * q)) :=
            mul_le_mul_of_nonneg_right hhalf (Real.exp_pos _).le
        _ ≤ (t / 4 * Real.exp 1)⁻¹ := this
    have h2 : Real.exp (-(t / 4 * q)) ≤ Real.exp (-(t * c / 4) * ‖z.1‖ ^ 2) := by
      apply Real.exp_le_exp.mpr
      have := h.ellip z.2 z.1
      rw [← hq] at this
      nlinarith
    calc |q / 2 * (χ z.2 * Real.exp (-(t * (q / 2))))|
        = q / 2 * Real.exp (-(t / 4 * q)) * Real.exp (-(t / 4 * q)) * |χ z.2| := by
          have hq2 : (0 : ℝ) ≤ q / 2 := by positivity
          rw [hsplit]
          simp only [abs_mul, Real.abs_exp, abs_of_nonneg hq2]
          ring
      _ ≤ (t / 4 * Real.exp 1)⁻¹ * Real.exp (-(t * c / 4) * ‖z.1‖ ^ 2) * |χ z.2| := by
          gcongr
      _ = (t / 4 * Real.exp 1)⁻¹ * Real.exp (-(t * c / 4) * ‖z.1‖ ^ 2) * |χ z.2| := rfl

/-- **The energy observable sees the learning coefficient**: `t E_t[L] = r/2` exactly, for every
`t > 0`, whatever the Hessian field `H(y)` (it is the mean of a chi-square with `r` degrees of
freedom divided by `2t`). -/
theorem mul_mbExp_mbLoss {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ} {χ : EuclidD n → ℝ}
    {c : ℝ} (h : MBData H χ c) {t : ℝ} (ht : 0 < t) {y₀ : EuclidD n} (hy₀ : χ y₀ ≠ 0) :
    t * mbExp H χ t (mbLoss H) = (r : ℝ) / 2 := by
  unfold mbExp
  have hi := integrable_mbLoss_mul_mbWeight h ht
  rw [Measure.volume_eq_prod] at hi
  have hnum : (∫ z : EuclidD r × EuclidD n, mbLoss H z * mbWeight H χ t z) =
      (Real.sqrt t)⁻¹ ^ r * t⁻¹ * ((r : ℝ) / 2) * ∫ y, χ y * mbDensity H y := by
    rw [Measure.volume_eq_prod, integral_prod_symm _ hi]
    simp only [mbWeight, mbLoss]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only
    have hinner : (∫ x : EuclidD r, qform (H y) x / 2 *
        (χ y * Real.exp (-(t * (qform (H y) x / 2))))) =
        χ y / 2 * ∫ x : EuclidD r, qform (H y) x * Real.exp (-(t * (qform (H y) x / 2))) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      ring
    rw [hinner, integral_qform_mul_exp_neg_mul_qform _ ht,
      integral_qform_mul_quadKernel (h.posDef y)]
    unfold mbDensity
    ring
  rw [hnum, integral_mbWeight h ht]
  have hA : (∫ y, χ y * mbDensity H y) ≠ 0 := (integral_cutoff_mul_mbDensity_pos h hy₀).ne'
  have hs : (Real.sqrt t)⁻¹ ^ r ≠ 0 := by
    have : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    positivity
  field_simp

end Laplace.Multi
