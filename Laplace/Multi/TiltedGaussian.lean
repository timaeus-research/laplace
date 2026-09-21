/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.GaussianWickPosDef

/-!
# The tilted Gaussian and the localised quadratic model (E3)

For a positive definite `P` and a vector `v`, the tilted weight `exp(−½ uᵀPu + v ⬝ᵥ u)` is, after
completing the square, `exp(½ mᵀPm) · e^{−½ (u−m)ᵀP(u−m)}` with `m = P⁻¹v`. Translation invariance
of Lebesgue measure then reduces every expectation under it to a centred Gaussian expectation
(`tiltedExpectation_eq`), giving the mean `m`, the raw second moments `P⁻¹ + mmᵀ`, the covariance
`P⁻¹` and `⟨uᵀHu⟩ = ∑ᵢⱼ Hᵢⱼ(P⁻¹)ᵢⱼ + mᵀHm`.

The localised quadratic model of the sanity note, `exp(−t·½wᵀHw − (γ/2)|w − w₀|²)`, is the tilted
weight with `P = tH + γI` and `v = γw₀` up to a constant (`localisedWeight_eq`). Hence (E3): the
localised covariance is `(tH + γI)⁻¹`, and the LLC estimate is
`t⟨½wᵀHw⟩ = ½ ∑ᵢⱼ (tH)ᵢⱼ((tH+γ)⁻¹)ᵢⱼ + ½ t mᵀHm` with `m = γ(tH+γ)⁻¹w₀`: the localisation belongs
in the effective Hessian, and a mis-centred anchor biases the LLC by `½ t mᵀHm ≥ 0`
(`localised_llc`, `localised_llc_bias_nonneg`); at `γ = 0` the estimate is `d/2`
(`localised_llc_unlocalised`).
-/

open MeasureTheory Matrix

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The tilted weight and the completed square -/

/-- `exp(−½ uᵀPu + v ⬝ᵥ u)`. -/
noncomputable def tiltedWeight (P : Matrix ι ι ℝ) (v u : ι → ℝ) : ℝ :=
  Real.exp (-(1 / 2) * (u ⬝ᵥ P *ᵥ u) + v ⬝ᵥ u)

/-- The mean `m = P⁻¹ v` of the tilted Gaussian. -/
noncomputable def tiltMean (P : Matrix ι ι ℝ) (v : ι → ℝ) : ι → ℝ := P⁻¹ *ᵥ v

noncomputable def tiltedZ (P : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := ∫ u : ι → ℝ, tiltedWeight P v u

noncomputable def tiltedExpectation (P : Matrix ι ι ℝ) (v : ι → ℝ) (φ : (ι → ℝ) → ℝ) : ℝ :=
  (∫ u : ι → ℝ, φ u * tiltedWeight P v u) / tiltedZ P v

theorem mulVec_tiltMean {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ) :
    P *ᵥ tiltMean P v = v := by
  unfold tiltMean
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP.det_pos.ne'),
    Matrix.one_mulVec]

omit [DecidableEq ι] in
theorem dotProduct_mulVec_symm {P : Matrix ι ι ℝ} (hP : P.PosDef) (x y : ι → ℝ) :
    x ⬝ᵥ P *ᵥ y = y ⬝ᵥ P *ᵥ x := by
  have hPt : Pᵀ = P := by
    have := hP.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hPt, dotProduct_comm]

/-- **Completing the square**: `exp(−½uᵀPu + v⬝ᵥu) = exp(½ mᵀPm) · gW(u − m)`. -/
theorem tiltedWeight_eq {P : Matrix ι ι ℝ} (hP : P.PosDef) (v u : ι → ℝ) :
    tiltedWeight P v u =
      Real.exp ((1 / 2) * (tiltMean P v ⬝ᵥ P *ᵥ tiltMean P v)) *
        gaussianWeight (matCLM P) (u - tiltMean P v) := by
  unfold tiltedWeight gaussianWeight
  rw [quadForm_matCLM, ← Real.exp_add]
  congr 1
  have hm := mulVec_tiltMean hP v
  have hsymm := dotProduct_mulVec_symm hP (tiltMean P v) u
  rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hsymm, hm,
    dotProduct_comm v u]
  ring

/-! ### The shift -/

/-- Every tilted integral is a centred Gaussian integral of the shifted integrand. -/
theorem integral_tilted {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ) (f : (ι → ℝ) → ℝ) :
    ∫ u : ι → ℝ, f u * tiltedWeight P v u =
      Real.exp ((1 / 2) * (tiltMean P v ⬝ᵥ P *ᵥ tiltMean P v)) *
        ∫ u : ι → ℝ, f (u + tiltMean P v) * gaussianWeight (matCLM P) u := by
  simp_rw [tiltedWeight_eq hP v, mul_left_comm (f _)]
  rw [integral_const_mul]
  congr 1
  rw [← integral_add_right_eq_self
    (fun u => f u * gaussianWeight (matCLM P) (u - tiltMean P v)) (tiltMean P v)]
  simp only [add_sub_cancel_right]

theorem tiltedZ_eq {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ) :
    tiltedZ P v =
      Real.exp ((1 / 2) * (tiltMean P v ⬝ᵥ P *ᵥ tiltMean P v)) * gaussianZ (matCLM P) := by
  unfold tiltedZ
  have h := integral_tilted hP v (fun _ => (1 : ℝ))
  simpa [gaussianZ] using h

omit [DecidableEq ι] in
theorem tiltedZ_pos {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ) : 0 < tiltedZ P v := by
  classical
  rw [tiltedZ_eq hP v]
  exact mul_pos (Real.exp_pos _) (gaussianZ_matCLM_pos hP)

/-- **The normalised shift**: `⟨φ⟩_tilted = (∫ φ(u + m) gW u) / Z`. -/
theorem tiltedExpectation_eq {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ)
    (φ : (ι → ℝ) → ℝ) :
    tiltedExpectation P v φ =
      (∫ u : ι → ℝ, φ (u + tiltMean P v) * gaussianWeight (matCLM P) u) /
        gaussianZ (matCLM P) := by
  unfold tiltedExpectation
  rw [integral_tilted hP v φ, tiltedZ_eq hP v, mul_div_mul_left _ _ (Real.exp_pos _).ne']

/-! ### Centred Gaussian helpers -/

theorem integrable_coord_mul_gaussianWeight_matCLM' {P : Matrix ι ι ℝ} (hP : P.PosDef) (i : ι) :
    Integrable (fun u : ι → ℝ => u i * gaussianWeight (matCLM P) u) := by
  simpa using integrable_prod_coord_mul_gaussianWeight_matCLM hP (fun _ : Fin 1 => i)

/-- The first moments of the centred Gaussian vanish. -/
theorem integral_coord_mul_gaussianWeight_matCLM_eq_zero {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (i : ι) :
    ∫ u : ι → ℝ, u i * gaussianWeight (matCLM P) u = 0 := by
  simpa using gaussian_stein_prod_coord_matCLM hP (fun k : Fin 0 => Fin.elim0 k) i

theorem integrable_dotProduct_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (w : ι → ℝ) :
    Integrable (fun u : ι → ℝ => (u ⬝ᵥ w) * gaussianWeight (matCLM P) u) := by
  simp_rw [dotProduct, Finset.sum_mul]
  exact integrable_finsetSum _ fun i _ => by
    simp_rw [mul_right_comm _ (w i)]
    exact (integrable_coord_mul_gaussianWeight_matCLM' hP i).mul_const _

theorem integral_dotProduct_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (w : ι → ℝ) :
    ∫ u : ι → ℝ, (u ⬝ᵥ w) * gaussianWeight (matCLM P) u = 0 := by
  simp_rw [dotProduct, Finset.sum_mul, mul_right_comm _ (w _)]
  rw [integral_finsetSum _ fun i _ =>
    (integrable_coord_mul_gaussianWeight_matCLM' hP i).mul_const _]
  simp_rw [integral_mul_const, integral_coord_mul_gaussianWeight_matCLM_eq_zero hP]
  simp

theorem integrable_quadForm_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (H : Matrix ι ι ℝ) :
    Integrable (fun u : ι → ℝ => (u ⬝ᵥ H *ᵥ u) * gaussianWeight (matCLM P) u) := by
  have h : ∀ u : ι → ℝ, (u ⬝ᵥ H *ᵥ u) * gaussianWeight (matCLM P) u =
      ∑ i, ∑ j, H i j * (u i * u j * gaussianWeight (matCLM P) u) := by
    intro u
    simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [h]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_coord_mul_gaussianWeight_matCLM hP i j).const_mul _

/-! ### Moments of the tilted Gaussian -/

/-- `⟨uᵢ⟩ = mᵢ`. -/
theorem tiltedExpectation_coord {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ) (i : ι) :
    tiltedExpectation P v (fun u => u i) = tiltMean P v i := by
  rw [tiltedExpectation_eq hP v]
  simp_rw [Pi.add_apply, add_mul]
  rw [integral_add (integrable_coord_mul_gaussianWeight_matCLM' hP i)
    ((integrable_gaussianWeight_matCLM hP).const_mul _),
    integral_coord_mul_gaussianWeight_matCLM_eq_zero hP, integral_const_mul, zero_add]
  have hZ : ∫ u : ι → ℝ, gaussianWeight (matCLM P) u = gaussianZ (matCLM P) := rfl
  rw [hZ, mul_div_cancel_right₀ _ (gaussianZ_matCLM_pos hP).ne']

/-- `⟨uᵢuⱼ⟩ = (P⁻¹)ᵢⱼ + mᵢmⱼ`. -/
theorem tiltedExpectation_coord_mul {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ) (i j : ι) :
    tiltedExpectation P v (fun u => u i * u j) = P⁻¹ i j + tiltMean P v i * tiltMean P v j := by
  rw [tiltedExpectation_eq hP v]
  set m := tiltMean P v
  have hexp : ∀ u : ι → ℝ, (u + m) i * (u + m) j * gaussianWeight (matCLM P) u =
      u i * u j * gaussianWeight (matCLM P) u + (u ⬝ᵥ (m j • Pi.single i 1 + m i • Pi.single j 1)) *
        gaussianWeight (matCLM P) u + m i * m j * gaussianWeight (matCLM P) u := by
    intro u
    simp only [Pi.add_apply, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_single,
      mul_one]
    ring
  simp_rw [hexp]
  have h1 := integrable_coord_mul_gaussianWeight_matCLM hP i j
  have h2 := integrable_dotProduct_mul_gaussianWeight_matCLM hP
    (m j • Pi.single i 1 + m i • Pi.single j 1)
  have h12 : Integrable (fun u : ι → ℝ => u i * u j * gaussianWeight (matCLM P) u +
      (u ⬝ᵥ (m j • Pi.single i 1 + m i • Pi.single j 1)) * gaussianWeight (matCLM P) u) := h1.add h2
  have h3 : Integrable (fun u : ι → ℝ => m i * m j * gaussianWeight (matCLM P) u) :=
    (integrable_gaussianWeight_matCLM hP).const_mul _
  rw [integral_add h12 h3, integral_add h1 h2, integral_coord_mul_gaussianWeight_matCLM hP,
    integral_dotProduct_mul_gaussianWeight_matCLM hP, integral_const_mul, add_zero]
  have hZ : ∫ u : ι → ℝ, gaussianWeight (matCLM P) u = gaussianZ (matCLM P) := rfl
  rw [hZ, add_div, mul_div_cancel_left₀ _ (gaussianZ_matCLM_pos hP).ne',
    mul_div_cancel_right₀ _ (gaussianZ_matCLM_pos hP).ne']

/-- **The covariance of the tilted Gaussian is `P⁻¹`**. -/
theorem tiltedCov {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ) (i j : ι) :
    tiltedExpectation P v (fun u => u i * u j) -
      tiltedExpectation P v (fun u => u i) * tiltedExpectation P v (fun u => u j) = P⁻¹ i j := by
  rw [tiltedExpectation_coord_mul hP, tiltedExpectation_coord hP, tiltedExpectation_coord hP]
  ring

/-- `⟨uᵀHu⟩ = ∑ᵢⱼ Hᵢⱼ (P⁻¹)ᵢⱼ + mᵀHm`. -/
theorem tiltedExpectation_quadForm {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ)
    (H : Matrix ι ι ℝ) :
    tiltedExpectation P v (fun u => u ⬝ᵥ H *ᵥ u) =
      ∑ i, ∑ j, H i j * P⁻¹ i j + tiltMean P v ⬝ᵥ H *ᵥ tiltMean P v := by
  rw [tiltedExpectation_eq hP v]
  set m := tiltMean P v
  have hexp : ∀ u : ι → ℝ, ((u + m) ⬝ᵥ H *ᵥ (u + m)) * gaussianWeight (matCLM P) u =
      (u ⬝ᵥ H *ᵥ u) * gaussianWeight (matCLM P) u +
        (u ⬝ᵥ (H *ᵥ m + m ᵥ* H)) * gaussianWeight (matCLM P) u +
        (m ⬝ᵥ H *ᵥ m) * gaussianWeight (matCLM P) u := by
    intro u
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_add,
      Matrix.dotProduct_mulVec m H u, dotProduct_comm (m ᵥ* H) u]
    ring
  simp_rw [hexp]
  have h1 := integrable_quadForm_mul_gaussianWeight_matCLM hP H
  have h2 := integrable_dotProduct_mul_gaussianWeight_matCLM hP (H *ᵥ m + m ᵥ* H)
  have h12 : Integrable (fun u : ι → ℝ => (u ⬝ᵥ H *ᵥ u) * gaussianWeight (matCLM P) u +
      (u ⬝ᵥ (H *ᵥ m + m ᵥ* H)) * gaussianWeight (matCLM P) u) := h1.add h2
  have h3 : Integrable (fun u : ι → ℝ => (m ⬝ᵥ H *ᵥ m) * gaussianWeight (matCLM P) u) :=
    (integrable_gaussianWeight_matCLM hP).const_mul _
  rw [integral_add h12 h3, integral_add h1 h2, integral_dotProduct_mul_gaussianWeight_matCLM hP,
    add_zero, integral_const_mul]
  have hq : ∫ u : ι → ℝ, (u ⬝ᵥ H *ᵥ u) * gaussianWeight (matCLM P) u =
      gaussianZ (matCLM P) * ∑ i, ∑ j, H i j * P⁻¹ i j := by
    have h := gaussian_quadForm_integral_posDef hP (matCLM H)
    simp_rw [quadForm_matCLM, hessInvPairing_matCLM] at h
    exact h
  have hZ : ∫ u : ι → ℝ, gaussianWeight (matCLM P) u = gaussianZ (matCLM P) := rfl
  rw [hq, hZ, add_div, mul_div_cancel_left₀ _ (gaussianZ_matCLM_pos hP).ne',
    mul_div_cancel_right₀ _ (gaussianZ_matCLM_pos hP).ne']

omit [DecidableEq ι] in
theorem tiltedExpectation_const_mul (P : Matrix ι ι ℝ) (v : ι → ℝ) (c : ℝ) (φ : (ι → ℝ) → ℝ) :
    tiltedExpectation P v (fun u => c * φ u) = c * tiltedExpectation P v φ := by
  unfold tiltedExpectation
  simp_rw [mul_assoc]
  rw [integral_const_mul, mul_div_assoc]

/-! ### E3: the localised quadratic model -/

omit [Fintype ι] in
/-- The effective precision `tH + γI` is positive definite for `H.PosDef`, `t > 0`, `γ ≥ 0`. -/
theorem effectivePrecision_posDef {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) : (t • H + γ • (1 : Matrix ι ι ℝ)).PosDef :=
  (hH.smul ht).add_posSemidef (Matrix.PosSemidef.one.smul hγ)

/-- **The note's localised target is a tilted Gaussian**:
`exp(−t·½wᵀHw − (γ/2)|w − w₀|²) = exp(−(γ/2)|w₀|²) · tiltedWeight (tH + γI) (γw₀) w`. -/
theorem localisedWeight_eq (H : Matrix ι ι ℝ) (t γ : ℝ) (w₀ w : ι → ℝ) :
    Real.exp (-(t * ((1 / 2) * (w ⬝ᵥ H *ᵥ w))) - γ / 2 * ((w - w₀) ⬝ᵥ (w - w₀))) =
      Real.exp (-(γ / 2) * (w₀ ⬝ᵥ w₀)) *
        tiltedWeight (t • H + γ • (1 : Matrix ι ι ℝ)) (γ • w₀) w := by
  unfold tiltedWeight
  rw [← Real.exp_add]
  congr 1
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul, smul_dotProduct, sub_dotProduct, dotProduct_sub,
    dotProduct_comm w₀ w]
  ring

/-- **E3, the covariance**: under the localised target the covariance of the coordinates is
`(tH + γI)⁻¹`, not `(tH)⁻¹`. -/
theorem localised_cov {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ : ℝ} (ht : 0 < t) (hγ : 0 ≤ γ)
    (w₀ : ι → ℝ) (i j : ι) :
    tiltedExpectation (t • H + γ • 1) (γ • w₀) (fun u => u i * u j) -
      tiltedExpectation (t • H + γ • 1) (γ • w₀) (fun u => u i) *
        tiltedExpectation (t • H + γ • 1) (γ • w₀) (fun u => u j) =
      (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹ i j :=
  tiltedCov (effectivePrecision_posDef hH ht hγ) _ i j

/-- **E3, the LLC**: `t⟨½wᵀHw⟩ = ½ ∑ᵢⱼ (tH)ᵢⱼ((tH+γ)⁻¹)ᵢⱼ + ½ t mᵀHm`, `m = γ(tH+γ)⁻¹w₀`. -/
theorem localised_llc {H : Matrix ι ι ℝ} (hH : H.PosDef) {t γ : ℝ} (ht : 0 < t) (hγ : 0 ≤ γ)
    (w₀ : ι → ℝ) :
    t * tiltedExpectation (t • H + γ • 1) (γ • w₀) (fun u => (1 / 2) * (u ⬝ᵥ H *ᵥ u)) =
      (1 / 2) * ∑ i, ∑ j, (t • H) i j * (t • H + γ • (1 : Matrix ι ι ℝ))⁻¹ i j +
        (t / 2) *
          (tiltMean (t • H + γ • 1) (γ • w₀) ⬝ᵥ H *ᵥ tiltMean (t • H + γ • 1) (γ • w₀)) := by
  have hP := effectivePrecision_posDef hH ht hγ
  rw [tiltedExpectation_const_mul, tiltedExpectation_quadForm hP]
  simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

omit [DecidableEq ι] in
/-- The mis-centring bias `½ t mᵀHm` is nonnegative. -/
theorem localised_llc_bias_nonneg {H : Matrix ι ι ℝ} (hH : H.PosDef) (t : ℝ) (ht : 0 ≤ t)
    (m : ι → ℝ) : 0 ≤ (t / 2) * (m ⬝ᵥ H *ᵥ m) := by
  have := hH.posSemidef.dotProduct_mulVec_nonneg m
  simp only [star_trivial] at this
  positivity

/-- A centred anchor gives no bias: `m = 0` when `w₀ = 0`. -/
theorem tiltMean_zero (P : Matrix ι ι ℝ) (γ : ℝ) : tiltMean P (γ • (0 : ι → ℝ)) = 0 := by
  simp [tiltMean]

/-- With `v = 0` the tilted weight is the centred Gaussian weight. -/
theorem tiltedWeight_zero (P : Matrix ι ι ℝ) (u : ι → ℝ) :
    tiltedWeight P 0 u = gaussianWeight (matCLM P) u := by
  unfold tiltedWeight gaussianWeight
  rw [quadForm_matCLM, zero_dotProduct, add_zero]

omit [DecidableEq ι] in
/-- **Unlocalised**: for the centred Gaussian `e^{−t·½wᵀHw}` the LLC estimate is `d/2`
(the `γ = 0` case of `localised_llc`). -/
theorem localised_llc_unlocalised {H : Matrix ι ι ℝ} (hH : H.PosDef) {t : ℝ} (ht : 0 < t) :
    t * tiltedExpectation (t • H) 0 (fun u => (1 / 2) * (u ⬝ᵥ H *ᵥ u)) = Fintype.card ι / 2 := by
  classical
  have hP : (t • H).PosDef := hH.smul ht
  rw [tiltedExpectation_const_mul, tiltedExpectation_quadForm hP]
  have hm : tiltMean (t • H) 0 = 0 := by simp [tiltMean]
  rw [hm, zero_dotProduct, add_zero]
  have hdet : IsUnit (t • H).det := isUnit_iff_ne_zero.mpr hP.det_pos.ne'
  have hsym : ∀ i j, (t • H)⁻¹ i j = (t • H)⁻¹ j i := fun i j => by
    have := (Matrix.posDef_inv_iff.mpr hP).1.apply i j
    simpa using this.symm
  have hmul : (t • H) * (t • H)⁻¹ = 1 := Matrix.mul_nonsing_inv (t • H) hdet
  have hdiag : ∀ i, ∑ j, H i j * (t • H)⁻¹ i j = t⁻¹ * ((t • H) * (t • H)⁻¹) i i := fun i => by
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsym i j, Matrix.smul_apply, smul_eq_mul]
    field_simp
  rw [Finset.sum_congr rfl fun i _ => hdiag i, ← Finset.mul_sum, hmul]
  simp only [Matrix.one_apply_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp

end Laplace.Multi
