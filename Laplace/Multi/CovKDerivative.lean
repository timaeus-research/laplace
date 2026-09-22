/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.E2Matrix
import Laplace.Multi.UniqueMinimum

/-!
# eq:covK is minus the temperature derivative

For a `t`-independent probe, `d/dt ⟨ψ⟩_t = −Cov_t[K, ψ]` exactly, since
`⟨ψ⟩_t = ∫ψe^{−tK}/∫e^{−tK}`.
Correspondingly the note's eq:covK is `−∂ₜ` of the first-order prediction
`⟨ψ⟩ ≈ ½ tr(BS) + bᵀ(⟨w⟩ − w*)` built from eq:cov and eq:mean: with `∂ₜS = −SHS` and
`∂ₜ(tT:S) = T:S − tT:(SHS)`, differentiating `½ tr(BS) − ½ bᵀS(tT:S)` produces eq:covK's four
terms one by one. This file records both levels.

* Formula level (`S = (tH)⁻¹`, `H` invertible): `contractT_smul`, `smul_inv_of_isUnit`,
  `firstOrder_eq` (`½ tr(B(sH)⁻¹) + b⬝meanShift s = c/s` with `c = covKConst H T B b`),
  `covKFormula_eq_const_div_sq` (`covKFormula t = c/t²`; the second and fourth terms of eq:covK
  cancel at `γ = 0` because `SHS = S/t`), `hasDerivAt_firstOrder`, `covKFormula_eq_neg_deriv`.
* Exact level, one dimension: for the anharmonic `ℓ` and `k : ℕ`,
  `hasDerivAt_moment_integral` (`d/ds ∫xᵏe^{−sℓ} = −∫ℓxᵏe^{−sℓ}`, by dominated differentiation
  under the integral on `s > t/2`, using `ℓ ≥ 0`), `hasDerivAt_gibbsExpectation_pow`
  (`d/ds ⟨xᵏ⟩_s = −Cov_t[ℓ, xᵏ]` at `s = t`) and `gibbsCov_eq_neg_deriv`.
-/

open Matrix MeasureTheory Filter Topology

namespace Laplace.Multi

open Laplace.OneD (anharmonicPotential)

/-! ### Formula level -/

section Formula

variable {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}

theorem contractT_smul (T : Fin d → Fin d → Fin d → ℝ) (c : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) :
    contractT T (c • S) = c • contractT T S := by
  funext l
  simp only [contractT, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  ring

theorem smul_inv_of_isUnit (hH : IsUnit H.det) {s : ℝ} (hs : s ≠ 0) :
    (s • H)⁻¹ = s⁻¹ • H⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hs, one_smul,
    Matrix.mul_nonsing_inv H hH]

/-- The constant `c = ½ tr(BH⁻¹) − ½ b⬝(H⁻¹(T:H⁻¹))`. -/
noncomputable def covKConst (H : Matrix (Fin d) (Fin d) ℝ) (T : Fin d → Fin d → Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) : ℝ :=
  1 / 2 * (B * H⁻¹).trace - 1 / 2 * (b ⬝ᵥ (H⁻¹ *ᵥ contractT T H⁻¹))

/-- **eq:covK at `γ = 0` is `c/t²`**: the second and fourth terms cancel since `SHS = S/t`. -/
theorem covKFormula_eq_const_div_sq (hH : IsUnit H.det) (T : Fin d → Fin d → Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) {t : ℝ} (ht : t ≠ 0) :
    covKFormula t H T B b = covKConst H T B b / t ^ 2 := by
  rw [covKFormula, covKConst, smul_inv_of_isUnit hH ht]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, Matrix.smul_mulVec,
    Matrix.mulVec_smul, contractT_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Matrix.mul_nonsing_inv H hH, Matrix.nonsing_inv_mul H hH, Matrix.one_mul]
  field_simp
  ring

/-- The first-order prediction `½ tr(BS) + b⬝meanShift` is `c/s`. -/
theorem firstOrder_eq (hH : IsUnit H.det) (T : Fin d → Fin d → Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) {s : ℝ} (hs : s ≠ 0) :
    1 / 2 * (B * (s • H)⁻¹).trace + b ⬝ᵥ meanShift s H T = covKConst H T B b * s⁻¹ := by
  rw [meanShift, covKConst, smul_inv_of_isUnit hH hs]
  simp only [Matrix.mul_smul, Matrix.trace_smul, Matrix.smul_mulVec, Matrix.mulVec_smul,
    contractT_smul, dotProduct_smul, smul_eq_mul]
  field_simp
  ring

/-- **eq:covK is `−∂ₜ` of the first-order eq:cov/eq:mean prediction** (derivative form). -/
theorem hasDerivAt_firstOrder (hH : IsUnit H.det) (T : Fin d → Fin d → Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s => 1 / 2 * (B * (s • H)⁻¹).trace + b ⬝ᵥ meanShift s H T)
      (-covKFormula t H T B b) t := by
  have h : HasDerivAt (fun s : ℝ => covKConst H T B b * s⁻¹)
      (covKConst H T B b * -(t ^ 2)⁻¹) t := (hasDerivAt_inv ht).const_mul _
  have he : (fun s => 1 / 2 * (B * (s • H)⁻¹).trace + b ⬝ᵥ meanShift s H T) =ᶠ[𝓝 t]
      fun s : ℝ => covKConst H T B b * s⁻¹ :=
    (eventually_ne_nhds ht).mono fun s hs => firstOrder_eq hH T B b hs
  rw [covKFormula_eq_const_div_sq hH T B b ht]
  exact (h.congr_of_eventuallyEq he).congr_deriv (by ring)

theorem covKFormula_eq_neg_deriv (hH : IsUnit H.det) (T : Fin d → Fin d → Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) {t : ℝ} (ht : t ≠ 0) :
    covKFormula t H T B b =
      -deriv (fun s => 1 / 2 * (B * (s • H)⁻¹).trace + b ⬝ᵥ meanShift s H T) t := by
  rw [(hasDerivAt_firstOrder hH T B b ht).deriv, neg_neg]

end Formula

/-! ### Exact level: the anharmonic Gibbs measure -/

section Exact

variable {lam alpha gamma : ℝ}

/-- `d/ds ∫ xᵏ e^{−sℓ} = −∫ ℓ xᵏ e^{−sℓ}` at `s = t > 0`, by dominated differentiation on
`s > t/2` with the bound `(λ/2 |x|^{k+2} + |α|/6 |x|^{k+3} + γ/24 |x|^{k+4}) e^{−(t/2)ℓ}`. -/
theorem hasDerivAt_moment_integral (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s : ℝ => ∫ x : ℝ, x ^ k * Real.exp (-(s * anharmonicPotential lam alpha gamma x)))
      (-∫ x : ℝ, anharmonicPotential lam alpha gamma x * x ^ k *
        Real.exp (-(t * anharmonicPotential lam alpha gamma x))) t := by
  have hℓ0 : ∀ x, 0 ≤ anharmonicPotential lam alpha gamma x :=
    fun x => anharmonicPotential_nonneg hgamma hdisc x
  have hcont : Continuous (anharmonicPotential lam alpha gamma) := by
    unfold anharmonicPotential
    fun_prop
  have ht2 : 0 < t / 2 := half_pos ht
  have hbound_int : Integrable fun x : ℝ =>
      (lam / 2 * |x| ^ (k + 2) + |alpha| / 6 * |x| ^ (k + 3) + gamma / 24 * |x| ^ (k + 4)) *
        Real.exp (-(t / 2 * anharmonicPotential lam alpha gamma x)) := by
    have h2 := (Laplace.OneD.integrable_abs_pow_mul_exp_neg_t_anharmonic (k + 2) hlam hgamma hdisc
      ht2).const_mul (lam / 2)
    have h3 := (Laplace.OneD.integrable_abs_pow_mul_exp_neg_t_anharmonic (k + 3) hlam hgamma hdisc
      ht2).const_mul (|alpha| / 6)
    have h4 := (Laplace.OneD.integrable_abs_pow_mul_exp_neg_t_anharmonic (k + 4) hlam hgamma hdisc
      ht2).const_mul (gamma / 24)
    refine ((h2.add h3).add h4).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun s x => x ^ k * Real.exp (-(s * anharmonicPotential lam alpha gamma x)))
    (F' := fun s x => -(anharmonicPotential lam alpha gamma x * x ^ k *
      Real.exp (-(s * anharmonicPotential lam alpha gamma x))))
    (bound := fun x =>
      (lam / 2 * |x| ^ (k + 2) + |alpha| / 6 * |x| ^ (k + 3) + gamma / 24 * |x| ^ (k + 4)) *
        Real.exp (-(t / 2 * anharmonicPotential lam alpha gamma x)))
    (x₀ := t) (s := Set.Ioi (t / 2)) (Ioi_mem_nhds (by linarith))
    (Eventually.of_forall fun s =>
      ((continuous_pow k).mul ((hcont.const_mul s).neg.rexp)).aestronglyMeasurable)
    (integrable_pow_mul_exp_neg_t_anharmonic k hlam hgamma hdisc ht)
    (((hcont.mul (continuous_pow k)).mul ((hcont.const_mul t).neg.rexp)).neg.aestronglyMeasurable)
    (Eventually.of_forall fun x s hs => ?_) hbound_int
    (Eventually.of_forall fun x s _ => ?_)
  · rw [integral_neg] at key
    exact key.2
  · -- the bound
    have hs' : t / 2 ≤ s := (Set.mem_Ioi.mp hs).le
    have hE : Real.exp (-(s * anharmonicPotential lam alpha gamma x)) ≤
        Real.exp (-(t / 2 * anharmonicPotential lam alpha gamma x)) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hs' (hℓ0 x)
      linarith
    have h2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    have h4 : x ^ 4 = |x| ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, h2]
    have h3 : alpha * x ^ 3 ≤ |alpha| * |x| ^ 3 := by
      rw [← abs_pow, ← abs_mul]
      exact le_abs_self _
    have hℓle : anharmonicPotential lam alpha gamma x ≤
        lam / 2 * |x| ^ 2 + |alpha| / 6 * |x| ^ 3 + gamma / 24 * |x| ^ 4 := by
      simp only [anharmonicPotential]
      rw [h2, h4]
      linarith
    have hP : anharmonicPotential lam alpha gamma x * |x| ^ k ≤
        lam / 2 * |x| ^ (k + 2) + |alpha| / 6 * |x| ^ (k + 3) + gamma / 24 * |x| ^ (k + 4) := by
      calc anharmonicPotential lam alpha gamma x * |x| ^ k
          ≤ (lam / 2 * |x| ^ 2 + |alpha| / 6 * |x| ^ 3 + gamma / 24 * |x| ^ 4) * |x| ^ k :=
            mul_le_mul_of_nonneg_right hℓle (pow_nonneg (abs_nonneg x) k)
        _ = _ := by ring
    rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hℓ0 x), abs_pow,
      abs_of_pos (Real.exp_pos _)]
    calc anharmonicPotential lam alpha gamma x * |x| ^ k *
          Real.exp (-(s * anharmonicPotential lam alpha gamma x))
        ≤ anharmonicPotential lam alpha gamma x * |x| ^ k *
          Real.exp (-(t / 2 * anharmonicPotential lam alpha gamma x)) :=
          mul_le_mul_of_nonneg_left hE (mul_nonneg (hℓ0 x) (pow_nonneg (abs_nonneg x) k))
      _ ≤ _ := mul_le_mul_of_nonneg_right hP (Real.exp_pos _).le
  · -- the derivative in `s`
    have h := (((hasDerivAt_id' (x := s)).mul_const
      (anharmonicPotential lam alpha gamma x)).neg.exp).const_mul (x ^ k)
    exact h.congr_deriv (by simp only [Pi.neg_apply]; ring)

/-- **`d/ds ⟨xᵏ⟩_s = −Cov_t[ℓ, xᵏ]`** for the anharmonic Gibbs measure. -/
theorem hasDerivAt_gibbsExpectation_pow (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) s
      (fun x => x ^ k))
      (-_root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
        (anharmonicPotential lam alpha gamma) (fun x => x ^ k)) t := by
  have hN := hasDerivAt_moment_integral hlam hgamma hdisc k ht
  have hZ := hasDerivAt_moment_integral hlam hgamma hdisc 0 ht
  simp only [pow_zero, one_mul, mul_one] at hZ
  have hZpos : 0 < _root_.Laplace.partitionFunction (anharmonicPotential lam alpha gamma) t :=
    partitionFunction_anharmonic_pos hlam hgamma hdisc ht
  have hZne : (∫ x : ℝ, Real.exp (-(t * anharmonicPotential lam alpha gamma x))) ≠ 0 := hZpos.ne'
  have h := hN.div hZ hZne
  refine h.congr_deriv ?_
  simp only [_root_.Laplace.gibbsCov, _root_.Laplace.gibbsExpectation,
    _root_.Laplace.partitionFunction]
  set N := ∫ x : ℝ, x ^ k * Real.exp (-(t * anharmonicPotential lam alpha gamma x)) with hN'
  set Z := ∫ x : ℝ, Real.exp (-(t * anharmonicPotential lam alpha gamma x)) with hZ'
  set LN := ∫ x : ℝ, anharmonicPotential lam alpha gamma x * x ^ k *
    Real.exp (-(t * anharmonicPotential lam alpha gamma x)) with hLN
  set LZ := ∫ x : ℝ, anharmonicPotential lam alpha gamma x *
    Real.exp (-(t * anharmonicPotential lam alpha gamma x)) with hLZ
  clear_value N Z LN LZ
  field_simp
  ring

/-- **The energy–probe covariance is minus the temperature derivative of the moment.** -/
theorem gibbsCov_eq_neg_deriv (hlam : 0 < lam) (hgamma : 0 < gamma)
    (hdisc : alpha ^ 2 < 3 * lam * gamma) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    _root_.Laplace.gibbsCov (anharmonicPotential lam alpha gamma) t
        (anharmonicPotential lam alpha gamma) (fun x => x ^ k) =
      -deriv (fun s => _root_.Laplace.gibbsExpectation (anharmonicPotential lam alpha gamma) s
        (fun x => x ^ k)) t := by
  rw [(hasDerivAt_gibbsExpectation_pow hlam hgamma hdisc k ht).deriv, neg_neg]

end Exact

end Laplace.Multi
