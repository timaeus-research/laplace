/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AnchoredEnergyGap
import Laplace.Sampler.BurnInGammaLaw

/-!
# The anchored Gaussian variance gap: three gaps, one anharmonic coefficient (E3/E2)

The variance of a quadratic form under a tilted Gaussian `N(m, Σ)`, `Σ = P⁻¹`, `m = P⁻¹v`, is
**`Var_{P,v}(uᵀHu) = 2·tr(HΣHΣ) + 4·(Hm)ᵀΣ(Hm)`** (`tiltedVar_quadForm`): the shift `u ↦ u + m`
gives
`(u+m)ᵀH(u+m) = uᵀHu + 2mᵀHu + mᵀHm`, the centred fourth moment is the Wick sum
`E[(uᵀHu)²] = tr(HΣ)² + 2tr(HΣHΣ)` (`integral_quadForm_sq_mul_gaussianWeight_matCLM`, from
`gaussian_fourth_moment_matCLM`), the odd moments vanish by reflection, and the squared mean cancels
the disconnected contraction. For E3's anchored Gaussian (precision `tH + gI`, `aᵢ = (Uᵀv)ᵢ`) this
is
**`t²Var(½uᵀHu) = ½∑ᵢ(tλᵢ/(tλᵢ+g))² + t²∑ᵢλᵢ²aᵢ²/(tλᵢ+g)³`** (`anchoredGaussianVar_eq`), which
expands as
`d/2 + (∑ᵢaᵢ²/λᵢ − g∑ᵢ1/λᵢ)/t + O(t⁻²)` with the explicit constant `∑ᵢ(3g²/2 + 3gaᵢ²)/λᵢ²`
(`anchoredGaussianVar_rate2`). Against the landed second-order localised variance
`t²Var_loc(L∘A) = d/2 + 2∑ᵢe₁ᵢ/t + O(t⁻²)` (`localisedVar_energy_order2`) this gives
**`t²Var_loc(L∘A) − t²Var_anch(½uᵀHu) = 2C₁′/t + O(t⁻²)`** (`localisedVar_anchoredGap`) with the
same
`C₁′ = ∑ᵢ(e₁ᵢ + g/(2λᵢ) − aᵢ²/(2λᵢ)) = ∑ᵢ(e₀ᵢ − aᵢαᵢ/(2λᵢ²))` as the transform gap
(`AnchoredGaussianGap`) and
the energy gap (`AnchoredEnergyGap`): mean `C₁′/t`, variance `2C₁′/t`, transform
`−sC₁′/((1+s)^{d/2+1}t)` —
three gaps, one coefficient, each proved from its own landed expansion (no differentiation of a
remainder).
-/

open Matrix Filter Topology MeasureTheory Laplace.Multi

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Symmetry helpers -/

theorem inv_apply_symm {P : Matrix ι ι ℝ} (hP : P.PosDef) (i j : ι) : P⁻¹ i j = P⁻¹ j i := by
  have h := hP.inv.1.apply i j
  simpa using h.symm

omit [Fintype ι] [DecidableEq ι] in
theorem apply_symm_of_isHermitian {H : Matrix ι ι ℝ} (hH : H.IsHermitian) (i j : ι) :
    H i j = H j i := by
  have h := hH.apply i j
  simpa using h.symm

omit [Fintype ι] [DecidableEq ι] in
theorem transpose_eq_of_isHermitian {H : Matrix ι ι ℝ} (hH : H.IsHermitian) : Hᵀ = H := by
  have h := hH.eq
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

omit [DecidableEq ι] in
/-- `xᵀHy = yᵀHx` for symmetric `H`. -/
theorem dotProduct_mulVec_symm_of_isHermitian {H : Matrix ι ι ℝ} (hH : H.IsHermitian)
    (x y : ι → ℝ) : x ⬝ᵥ H *ᵥ y = y ⬝ᵥ H *ᵥ x := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, transpose_eq_of_isHermitian hH,
    dotProduct_comm]

omit [DecidableEq ι] in
theorem dotProduct_mulVec_eq_sum (H : Matrix ι ι ℝ) (x y : ι → ℝ) :
    x ⬝ᵥ H *ᵥ y = ∑ a, ∑ b, H a b * (x a * y b) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-! ### Polynomial expansions of the integrands -/

omit [DecidableEq ι] in
theorem quadForm_sq_mul_eq_sum (H : Matrix ι ι ℝ) (u : ι → ℝ) (G : ℝ) :
    (u ⬝ᵥ H *ᵥ u) ^ 2 * G = ∑ a, ∑ c, ∑ b, ∑ d, H a b * H c d * (u a * u b * u c * u d * G) := by
  rw [dotProduct_mulVec_eq_sum, sq, Finset.sum_mul_sum]
  simp only [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring

omit [DecidableEq ι] in
theorem dotProduct_sq_mul_eq_sum (w u : ι → ℝ) (G : ℝ) :
    (u ⬝ᵥ w) ^ 2 * G = ∑ a, ∑ b, w a * w b * (u a * u b * G) := by
  simp only [dotProduct, sq, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

omit [DecidableEq ι] in
theorem quadForm_mul_dotProduct_mul_eq_sum (H : Matrix ι ι ℝ) (w u : ι → ℝ) (G : ℝ) :
    (u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ w) * G = ∑ a, ∑ c, ∑ b, H a b * w c * (u a * u b * u c * G) := by
  rw [dotProduct_mulVec_eq_sum]
  simp only [dotProduct]
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun b _ => by ring

/-! ### Integrability -/

theorem integrable_three_coord_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (a b c : ι) : Integrable (fun u : ι → ℝ => u a * u b * u c * gaussianWeight (matCLM P) u) := by
  simpa [Fin.prod_univ_three] using integrable_prod_coord_mul_gaussianWeight_matCLM hP ![a, b, c]

theorem integrable_quadForm_sq_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (H : Matrix ι ι ℝ) : Integrable (fun u : ι → ℝ => (u ⬝ᵥ H *ᵥ u) ^ 2 * gaussianWeight (matCLM P)
        u) := by
  simp_rw [quadForm_sq_mul_eq_sum]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun c _ =>
    integrable_finsetSum _ fun b _ => integrable_finsetSum _ fun d _ =>
      ((laplaceCov4MomentHypotheses_matCLM hP).int_4moment a b c d).const_mul _

theorem integrable_dotProduct_sq_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (w : ι → ℝ) : Integrable (fun u : ι → ℝ => (u ⬝ᵥ w) ^ 2 * gaussianWeight (matCLM P) u) := by
  simp_rw [dotProduct_sq_mul_eq_sum]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (integrable_coord_mul_gaussianWeight_matCLM hP a b).const_mul _

theorem integrable_quadForm_mul_dotProduct_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ}
    (hP : P.PosDef) (H : Matrix ι ι ℝ) (w : ι → ℝ) :
    Integrable (fun u : ι → ℝ => (u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ w) * gaussianWeight (matCLM P) u) := by
  simp_rw [quadForm_mul_dotProduct_mul_eq_sum]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun c _ =>
    integrable_finsetSum _ fun b _ =>
      (integrable_three_coord_mul_gaussianWeight_matCLM hP a b c).const_mul _


/-! ### The centred Gaussian moments of the quadratic and linear forms -/

/-- **Wick for the squared quadratic form**: `∫(uᵀHu)² gw = Z·(tr(HΣ)² + 2·tr(HΣHΣ))`, `Σ = P⁻¹`. -/
theorem integral_quadForm_sq_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    {H : Matrix ι ι ℝ} (hH : H.IsHermitian) :
    ∫ u : ι → ℝ, (u ⬝ᵥ H *ᵥ u) ^ 2 * gaussianWeight (matCLM P) u =
      gaussianZ (matCLM P) * ((∑ i, ∑ j, H i j * P⁻¹ i j) ^ 2 +
        2 * ∑ a, ∑ c, (H * P⁻¹) a c * (H * P⁻¹) c a) := by
  have hI : ∀ a b c d : ι, Integrable (fun u : ι → ℝ =>
      H a b * H c d * (u a * u b * u c * u d * gaussianWeight (matCLM P) u)) :=
    fun a b c d => ((laplaceCov4MomentHypotheses_matCLM hP).int_4moment a b c d).const_mul _
  simp_rw [quadForm_sq_mul_eq_sum]
  have key : ∫ u : ι → ℝ, ∑ a, ∑ c, ∑ b, ∑ d,
      H a b * H c d * (u a * u b * u c * u d * gaussianWeight (matCLM P) u) =
      ∑ a, ∑ c, ∑ b, ∑ d, H a b * H c d * (gaussianZ (matCLM P) *
        (P⁻¹ a d * P⁻¹ b c + P⁻¹ b d * P⁻¹ a c + P⁻¹ c d * P⁻¹ a b)) := by
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun c _ =>
      integrable_finsetSum _ fun b _ => integrable_finsetSum _ fun d _ => hI a b c d]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ =>
      integrable_finsetSum _ fun d _ => hI a b c d]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_finsetSum _ fun b _ => integrable_finsetSum _ fun d _ => hI a b c d]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finsetSum _ fun d _ => hI a b c d]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [integral_const_mul, gaussian_fourth_moment_matCLM hP]
  rw [key]
  have hsym := inv_apply_symm hP
  have hHs := apply_symm_of_isHermitian hH
  have h3 : ∑ a, ∑ c, ∑ b, ∑ d, H a b * H c d * (P⁻¹ c d * P⁻¹ a b) =
      (∑ i, ∑ j, H i j * P⁻¹ i j) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    simp only [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring
  have h1 : ∑ a, ∑ c, ∑ b, ∑ d, H a b * H c d * (P⁻¹ a d * P⁻¹ b c) =
      ∑ a, ∑ c, (H * P⁻¹) a c * (H * P⁻¹) c a := by
    simp only [Matrix.mul_apply, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by rw [hsym d a]; ring
  have h2 : ∑ a, ∑ c, ∑ b, ∑ d, H a b * H c d * (P⁻¹ b d * P⁻¹ a c) =
      ∑ a, ∑ c, (H * P⁻¹) a c * (H * P⁻¹) c a := by
    rw [← h1]
    refine Finset.sum_congr rfl fun a _ => ?_
    calc ∑ c, ∑ b, ∑ d, H a b * H c d * (P⁻¹ b d * P⁻¹ a c)
        = ∑ c, ∑ b, ∑ d, H a b * H d c * (P⁻¹ a c * P⁻¹ b d) :=
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun d _ => by rw [hHs c d]; ring
      _ = ∑ b, ∑ c, ∑ d, H a b * H d c * (P⁻¹ a c * P⁻¹ b d) := Finset.sum_comm
      _ = ∑ b, ∑ d, ∑ c, H a b * H d c * (P⁻¹ a c * P⁻¹ b d) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ d, ∑ b, ∑ c, H a b * H d c * (P⁻¹ a c * P⁻¹ b d) := Finset.sum_comm
  have hsplit : ∀ a c b d : ι, H a b * H c d * (gaussianZ (matCLM P) *
      (P⁻¹ a d * P⁻¹ b c + P⁻¹ b d * P⁻¹ a c + P⁻¹ c d * P⁻¹ a b)) =
      gaussianZ (matCLM P) * (H a b * H c d * (P⁻¹ a d * P⁻¹ b c)) +
        gaussianZ (matCLM P) * (H a b * H c d * (P⁻¹ b d * P⁻¹ a c)) +
        gaussianZ (matCLM P) * (H a b * H c d * (P⁻¹ c d * P⁻¹ a b)) := fun a c b d => by ring
  simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, h2, h3]
  ring

/-- `∫(uᵀw)² gw = Z·wᵀΣw`. -/
theorem integral_dotProduct_sq_mul_gaussianWeight_matCLM {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (w : ι → ℝ) :
    ∫ u : ι → ℝ, (u ⬝ᵥ w) ^ 2 * gaussianWeight (matCLM P) u =
      gaussianZ (matCLM P) * (w ⬝ᵥ P⁻¹ *ᵥ w) := by
  simp_rw [dotProduct_sq_mul_eq_sum]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (integrable_coord_mul_gaussianWeight_matCLM hP a b).const_mul _,
    dotProduct_mulVec_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (integrable_coord_mul_gaussianWeight_matCLM hP a b).const_mul
      _,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, integral_coord_mul_gaussianWeight_matCLM hP]
  ring

/-- The cubic moment `∫(uᵀHu)(uᵀw) gw` vanishes by reflection. -/
theorem integral_quadForm_mul_dotProduct_mul_gaussianWeight_matCLM (P H : Matrix ι ι ℝ)
    (w : ι → ℝ) :
    ∫ u : ι → ℝ, (u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ w) * gaussianWeight (matCLM P) u = 0 :=
  integral_odd_mul_gaussian_eq_zero (matCLM P) _ fun u => by
    simp only [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
    ring

/-- **The variance of a quadratic form under a tilted Gaussian**:
`Var_{P,v}(uᵀHu) = 2·tr(HΣHΣ) + 4·(Hm)ᵀΣ(Hm)`, `Σ = P⁻¹`, `m = P⁻¹v`. -/
theorem tiltedVar_quadForm {P : Matrix ι ι ℝ} (hP : P.PosDef) (v : ι → ℝ) {H : Matrix ι ι ℝ}
    (hH : H.IsHermitian) :
    tiltedExpectation P v (fun u => (u ⬝ᵥ H *ᵥ u) ^ 2) -
      (tiltedExpectation P v (fun u => u ⬝ᵥ H *ᵥ u)) ^ 2 =
      2 * ∑ a, ∑ c, (H * P⁻¹) a c * (H * P⁻¹) c a +
        4 * ((H *ᵥ tiltMean P v) ⬝ᵥ P⁻¹ *ᵥ (H *ᵥ tiltMean P v)) := by
  rw [tiltedExpectation_quadForm hP, tiltedExpectation_eq hP v]
  set m := tiltMean P v with hm
  have hZ0 : gaussianZ (matCLM P) ≠ 0 := (gaussianZ_matCLM_pos hP).ne'
  have hlin : ∀ u : ι → ℝ, (u + m) ⬝ᵥ H *ᵥ (u + m) =
      u ⬝ᵥ H *ᵥ u + 2 * (u ⬝ᵥ (H *ᵥ m)) + m ⬝ᵥ H *ᵥ m := by
    intro u
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
      dotProduct_mulVec_symm_of_isHermitian hH m u]
    ring
  have hexp : ∀ u : ι → ℝ, ((u + m) ⬝ᵥ H *ᵥ (u + m)) ^ 2 * gaussianWeight (matCLM P) u =
      ((u ⬝ᵥ H *ᵥ u) ^ 2 * gaussianWeight (matCLM P) u +
        4 * ((u ⬝ᵥ (H *ᵥ m)) ^ 2 * gaussianWeight (matCLM P) u)) +
      ((4 * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u) +
        (2 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ H *ᵥ u) * gaussianWeight (matCLM P) u)) +
        ((4 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u) +
          (m ⬝ᵥ H *ᵥ m) ^ 2 * gaussianWeight (matCLM P) u)) := by
    intro u
    rw [hlin]
    ring
  simp_rw [hexp]
  have I1 := integrable_quadForm_sq_mul_gaussianWeight_matCLM hP H
  have I2 := (integrable_dotProduct_sq_mul_gaussianWeight_matCLM hP (H *ᵥ m)).const_mul (4 : ℝ)
  have I3 := (integrable_quadForm_mul_dotProduct_mul_gaussianWeight_matCLM hP H
    (H *ᵥ m)).const_mul (4 : ℝ)
  have I4 := (integrable_quadForm_mul_gaussianWeight_matCLM hP H).const_mul (2 * (m ⬝ᵥ H *ᵥ m))
  have I5 := (integrable_dotProduct_mul_gaussianWeight_matCLM hP (H *ᵥ m)).const_mul
    (4 * (m ⬝ᵥ H *ᵥ m))
  have I6 := (integrable_gaussianWeight_matCLM hP).const_mul ((m ⬝ᵥ H *ᵥ m) ^ 2)
  have hq : ∫ u : ι → ℝ, (u ⬝ᵥ H *ᵥ u) * gaussianWeight (matCLM P) u =
      gaussianZ (matCLM P) * ∑ i, ∑ j, H i j * P⁻¹ i j := by
    have h := gaussian_quadForm_integral_posDef hP (matCLM H)
    simp_rw [quadForm_matCLM, hessInvPairing_matCLM] at h
    exact h
  have hZ : ∫ u : ι → ℝ, gaussianWeight (matCLM P) u = gaussianZ (matCLM P) := rfl
  have I12 : Integrable (fun u : ι → ℝ => (u ⬝ᵥ H *ᵥ u) ^ 2 * gaussianWeight (matCLM P) u +
      4 * ((u ⬝ᵥ (H *ᵥ m)) ^ 2 * gaussianWeight (matCLM P) u)) := I1.add I2
  have I34 : Integrable (fun u : ι → ℝ =>
      4 * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u) +
        (2 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ H *ᵥ u) * gaussianWeight (matCLM P) u)) := I3.add I4
  have I56 : Integrable (fun u : ι → ℝ =>
      (4 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u) +
        (m ⬝ᵥ H *ᵥ m) ^ 2 * gaussianWeight (matCLM P) u) := I5.add I6
  have I3456 : Integrable (fun u : ι → ℝ =>
      (4 * ((u ⬝ᵥ H *ᵥ u) * (u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u) +
        (2 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ H *ᵥ u) * gaussianWeight (matCLM P) u)) +
      ((4 * (m ⬝ᵥ H *ᵥ m)) * ((u ⬝ᵥ (H *ᵥ m)) * gaussianWeight (matCLM P) u) +
        (m ⬝ᵥ H *ᵥ m) ^ 2 * gaussianWeight (matCLM P) u)) := I34.add I56
  rw [integral_add I12 I3456, integral_add I1 I2, integral_add I34 I56, integral_add I3 I4,
    integral_add I5 I6]
  simp only [integral_const_mul]
  rw [integral_quadForm_sq_mul_gaussianWeight_matCLM hP hH,
    integral_dotProduct_sq_mul_gaussianWeight_matCLM hP,
    integral_quadForm_mul_dotProduct_mul_gaussianWeight_matCLM,
    integral_dotProduct_mul_gaussianWeight_matCLM hP, hq, hZ]
  field_simp
  ring


/-! ### E3's anchored Gaussian variance in the eigenbasis -/

/-- `H(tH+gI)⁻¹ = U diag(λᵢ/(tλᵢ+g)) Uᵀ`. -/
theorem mul_inv_localisedPrecision_eq_conj {H : Matrix ι ι ℝ} (hH : H.PosDef) {t g : ℝ}
    (ht : 0 < t) (hg : 0 ≤ g) :
    H * (t • H + g • (1 : Matrix ι ι ℝ))⁻¹ = orthoOf hH.1 *
      diagonal (fun i => hH.1.eigenvalues i / (t * hH.1.eigenvalues i + g)) * (orthoOf hH.1)ᵀ := by
  have hd : (fun i => hH.1.eigenvalues i * (1 / (t * hH.1.eigenvalues i + g))) =
      fun i => hH.1.eigenvalues i / (t * hH.1.eigenvalues i + g) := by
    funext i
    ring
  rw [inv_localisedPrecision_eq_conj hH ht hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    mul_orthoOf_eq hH.1, Matrix.mul_assoc (orthoOf hH.1), Matrix.diagonal_mul_diagonal, hd]

/-- `tr((H(tH+gI)⁻¹)²) = ∑ᵢ(λᵢ/(tλᵢ+g))²`. -/
theorem trace_sq_mul_inv_localisedPrecision {H : Matrix ι ι ℝ} (hH : H.PosDef) {t g : ℝ}
    (ht : 0 < t) (hg : 0 ≤ g) :
    ∑ a, ∑ c, (H * (t • H + g • (1 : Matrix ι ι ℝ))⁻¹) a c *
        (H * (t • H + g • (1 : Matrix ι ι ℝ))⁻¹) c a =
      ∑ i, (hH.1.eigenvalues i / (t * hH.1.eigenvalues i + g)) ^ 2 := by
  have e : ∑ a, ∑ c, (H * (t • H + g • (1 : Matrix ι ι ℝ))⁻¹) a c *
      (H * (t • H + g • (1 : Matrix ι ι ℝ))⁻¹) c a =
      Matrix.trace ((H * (t • H + g • (1 : Matrix ι ι ℝ))⁻¹) *
        (H * (t • H + g • (1 : Matrix ι ι ℝ))⁻¹)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [e, mul_inv_localisedPrecision_eq_conj hH ht hg, Laplace.Sampler.conj_mul_conj hH.1,
      Matrix.trace_mul_cycle,
    orthoOf_transpose_mul hH.1, Matrix.one_mul, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `(Hm)ᵀ(tH+gI)⁻¹(Hm) = ∑ᵢ λᵢ²aᵢ²/(tλᵢ+g)³` for the anchored mean `m = (tH+gI)⁻¹v`, `aᵢ =
(Uᵀv)ᵢ`. -/
theorem anchoredMean_energy_localised {H : Matrix ι ι ℝ} (hH : H.PosDef) {t g : ℝ} (ht : 0 < t)
    (hg : 0 ≤ g) (v : ι → ℝ) :
    (H *ᵥ tiltMean (t • H + g • (1 : Matrix ι ι ℝ)) v) ⬝ᵥ (t • H + g • (1 : Matrix ι ι ℝ))⁻¹ *ᵥ
        (H *ᵥ tiltMean (t • H + g • (1 : Matrix ι ι ℝ)) v) =
      ∑ i, hH.1.eigenvalues i ^ 2 * ((orthoOf hH.1)ᵀ *ᵥ v) i ^ 2 / (t * hH.1.eigenvalues i + g) ^ 3
          := by
  have hHm : H *ᵥ tiltMean (t • H + g • (1 : Matrix ι ι ℝ)) v = orthoOf hH.1 *ᵥ
      (diagonal (fun i => hH.1.eigenvalues i / (t * hH.1.eigenvalues i + g)) *ᵥ
        ((orthoOf hH.1)ᵀ *ᵥ v)) := by
    unfold tiltMean
    rw [Matrix.mulVec_mulVec, mul_inv_localisedPrecision_eq_conj hH ht hg, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
  rw [hHm, inv_localisedPrecision_eq_conj hH ht hg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec _ (orthoOf hH.1)ᵀ (orthoOf hH.1), orthoOf_transpose_mul hH.1,
    Matrix.one_mulVec, dotProduct_orthoOf_mulVec hH.1]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [div_eq_mul_inv, ← inv_pow]
  ring

/-- **E3's anchored Gaussian variance of the scaled quadratic energy**:
`t²·Var_{tH+gI,v}(½uᵀHu) = ½∑ᵢ(tλᵢ/(tλᵢ+g))² + t²∑ᵢλᵢ²aᵢ²/(tλᵢ+g)³`, `aᵢ = (Uᵀv)ᵢ`. -/
theorem anchoredGaussianVar_eq {H : Matrix ι ι ℝ} (hH : H.PosDef) {t g : ℝ} (ht : 0 < t)
    (hg : 0 ≤ g) (v : ι → ℝ) :
    t ^ 2 * (tiltedExpectation (t • H + g • (1 : Matrix ι ι ℝ)) v
        (fun u => ((1 / 2) * (u ⬝ᵥ H *ᵥ u)) ^ 2) -
      (tiltedExpectation (t • H + g • (1 : Matrix ι ι ℝ)) v (fun u => (1 / 2) * (u ⬝ᵥ H *ᵥ u))) ^
          2) =
      1 / 2 * ∑ i, (t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + g)) ^ 2 +
        t ^ 2 * ∑ i, hH.1.eigenvalues i ^ 2 * ((orthoOf hH.1)ᵀ *ᵥ v) i ^ 2 /
          (t * hH.1.eigenvalues i + g) ^ 3 := by
  have hP := effectivePrecision_posDef hH ht hg
  have e1 : (fun u : ι → ℝ => ((1 / 2 : ℝ) * (u ⬝ᵥ H *ᵥ u)) ^ 2) =
      fun u => (1 / 4 : ℝ) * (u ⬝ᵥ H *ᵥ u) ^ 2 := by
    funext u
    ring
  rw [e1, tiltedExpectation_const_mul, tiltedExpectation_const_mul]
  have hvar := tiltedVar_quadForm hP v hH.1
  rw [trace_sq_mul_inv_localisedPrecision hH ht hg,
    anchoredMean_energy_localised hH ht hg v] at hvar
  have e2 : ∑ i, (t * hH.1.eigenvalues i / (t * hH.1.eigenvalues i + g)) ^ 2 =
      t ^ 2 * ∑ i, (hH.1.eigenvalues i / (t * hH.1.eigenvalues i + g)) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e2]
  linear_combination (t ^ 2 / 4) * hvar

end Laplace.Sampler

namespace Laplace.Multi

/-! ### The anchored variance's finite-temperature correction (E2 frame data) -/

/-- `0 ≤ ½(u/(u+g))² − ½ + g/u ≤ 3g²/(2u²)`. -/
theorem central_var_term_bound {u g : ℝ} (hu : 0 < u) (hg : 0 ≤ g) :
    |1 / 2 * (u / (u + g)) ^ 2 - 1 / 2 + g / u| ≤ 3 / 2 * g ^ 2 / u ^ 2 := by
  have hug : 0 < u + g := by positivity
  have e : 1 / 2 * (u / (u + g)) ^ 2 - 1 / 2 + g / u =
      g ^ 2 * (3 * u + 2 * g) / (2 * u * (u + g) ^ 2) := by
    field_simp
    ring
  rw [e, abs_of_nonneg (by positivity)]
  have e2 : 3 / 2 * g ^ 2 / u ^ 2 - g ^ 2 * (3 * u + 2 * g) / (2 * u * (u + g) ^ 2) =
      g ^ 2 * (4 * u * g + 3 * g ^ 2) / (2 * u ^ 2 * (u + g) ^ 2) := by
    field_simp
    ring
  have : 0 ≤ g ^ 2 * (4 * u * g + 3 * g ^ 2) / (2 * u ^ 2 * (u + g) ^ 2) := by positivity
  linarith

/-- `|t²λ²a²/(tλ+g)³ − a²/(λt)| ≤ 3ga²/(λ²t²)`. -/
theorem noncentral_var_term_bound {t lam g a : ℝ} (ht : 0 < t) (hl : 0 < lam) (hg : 0 ≤ g) :
    |t ^ 2 * lam ^ 2 * a ^ 2 / (t * lam + g) ^ 3 - a ^ 2 / (lam * t)| ≤
      3 * g * a ^ 2 / (lam ^ 2 * t ^ 2) := by
  have hu : 0 < t * lam := by positivity
  have hug : 0 < t * lam + g := by positivity
  have e : t ^ 2 * lam ^ 2 * a ^ 2 / (t * lam + g) ^ 3 - a ^ 2 / (lam * t) =
      -(a ^ 2 * g * (3 * (t * lam) ^ 2 + 3 * (t * lam) * g + g ^ 2) /
        ((t * lam) * (t * lam + g) ^ 3)) := by
    field_simp
    ring
  rw [e, abs_neg, abs_of_nonneg (by positivity)]
  have e2 : 3 * g * a ^ 2 / (lam ^ 2 * t ^ 2) -
      a ^ 2 * g * (3 * (t * lam) ^ 2 + 3 * (t * lam) * g + g ^ 2) / ((t * lam) * (t * lam + g) ^ 3)
          =
      a ^ 2 * g * (6 * (t * lam) ^ 2 * g + 8 * (t * lam) * g ^ 2 + 3 * g ^ 3) /
        ((t * lam) ^ 2 * (t * lam + g) ^ 3) := by
    field_simp
    ring
  have : 0 ≤ a ^ 2 * g * (6 * (t * lam) ^ 2 * g + 8 * (t * lam) * g ^ 2 + 3 * g ^ 3) /
      ((t * lam) ^ 2 * (t * lam + g) ^ 3) := by positivity
  linarith

/-- **The anchored Gaussian variance's correction**:
`½∑ᵢ(tλᵢ/(tλᵢ+g))² + t²∑ᵢλᵢ²aᵢ²/(tλᵢ+g)³ = d/2 + (∑ᵢaᵢ²/λᵢ − g∑ᵢ1/λᵢ)/t + O(t⁻²)`, explicit
constant,
every `t > 0`. -/
theorem anchoredGaussianVar_rate2 {d : ℕ} {lam : Fin d → ℝ} {g : ℝ} (hlam : ∀ i, 0 < lam i)
    (hg : 0 ≤ g) (a : Fin d → ℝ) {t : ℝ} (ht : 0 < t) :
      |(1 / 2 * ∑ i, (t * lam i / (t * lam i + g)) ^ 2 + t ^ 2 * ∑ i, lam i ^ 2 * a i ^ 2 / (t * lam
        i + g) ^ 3) - (d : ℝ) / 2 - (∑ i, a i ^ 2 / lam i - ∑ i, g / lam i) / t| ≤ (∑ i, (3 / 2 * g
        ^ 2 + 3 * g * a i ^ 2) / lam i ^ 2) / t ^ 2 := by
  have key : ∀ i, 1 / 2 * (t * lam i / (t * lam i + g)) ^ 2 +
      t ^ 2 * (lam i ^ 2 * a i ^ 2 / (t * lam i + g) ^ 3) - 1 / 2 - (a i ^ 2 / lam i - g / lam i) /
          t =
      (1 / 2 * (t * lam i / (t * lam i + g)) ^ 2 - 1 / 2 + g / (t * lam i)) +
        (t ^ 2 * lam i ^ 2 * a i ^ 2 / (t * lam i + g) ^ 3 - a i ^ 2 / (lam i * t)) := fun i => by
    ring
  have hb : ∀ i, |(1 / 2 * (t * lam i / (t * lam i + g)) ^ 2 - 1 / 2 + g / (t * lam i)) +
      (t ^ 2 * lam i ^ 2 * a i ^ 2 / (t * lam i + g) ^ 3 - a i ^ 2 / (lam i * t))| ≤
      (3 / 2 * g ^ 2 + 3 * g * a i ^ 2) / lam i ^ 2 / t ^ 2 := fun i => by
    have hl := hlam i
    have hu : 0 < t * lam i := by positivity
    calc _ ≤ |1 / 2 * (t * lam i / (t * lam i + g)) ^ 2 - 1 / 2 + g / (t * lam i)| +
          |t ^ 2 * lam i ^ 2 * a i ^ 2 / (t * lam i + g) ^ 3 - a i ^ 2 / (lam i * t)| := abs_add_le
              _ _
      _ ≤ 3 / 2 * g ^ 2 / (t * lam i) ^ 2 + 3 * g * a i ^ 2 / (lam i ^ 2 * t ^ 2) :=
          add_le_add (central_var_term_bound hu hg) (noncentral_var_term_bound ht hl hg)
      _ = (3 / 2 * g ^ 2 + 3 * g * a i ^ 2) / lam i ^ 2 / t ^ 2 := by
          field_simp
  have hd : (d : ℝ) / 2 = ∑ _i : Fin d, (1 / 2 : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have e : (1 / 2 * ∑ i, (t * lam i / (t * lam i + g)) ^ 2 + t ^ 2 * ∑ i, lam i ^ 2 * a i ^ 2 / (t *
      lam i + g) ^ 3) - (d : ℝ) / 2 - (∑ i, a i ^ 2 / lam i - ∑ i, g / lam i) / t = ∑ i, (1 / 2 * (t
      * lam i / (t * lam i + g)) ^ 2 + t ^ 2 * (lam i ^ 2 * a i ^ 2 / (t * lam i + g) ^ 3) - 1 / 2 -
      (a i ^ 2 / lam i - g / lam i) / t) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum,
      sub_div, hd]
  rw [e]
  calc _ ≤ ∑ i, |1 / 2 * (t * lam i / (t * lam i + g)) ^ 2 +
        t ^ 2 * (lam i ^ 2 * a i ^ 2 / (t * lam i + g) ^ 3) - 1 / 2 -
          (a i ^ 2 / lam i - g / lam i) / t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (3 / 2 * g ^ 2 + 3 * g * a i ^ 2) / lam i ^ 2 / t ^ 2 :=
        Finset.sum_le_sum fun i _ => by rw [key i]; exact hb i
    _ = _ := by rw [Finset.sum_div]

section Multi

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g : ℝ}
variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- **The anchored variance gap is governed by `2C₁′`**:
`t²Var_loc(L∘A) − (½∑ᵢ(tλᵢ/(tλᵢ+g))² + t²∑ᵢλᵢ²aᵢ²/(tλᵢ+g)³) = 2C₁′/t + O(t⁻²)`, `aᵢ = g·u₀ᵢ`,
`C₁′ = ∑ᵢ(e₁ᵢ + g/(2λᵢ) − aᵢ²/(2λᵢ))` — the coefficient of the transform and energy gaps. -/
theorem localisedVar_anchoredGap (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (rotatedAnharmonic
        Q c lam alpha gamma) (rotatedAnharmonic Q c lam alpha gamma) - (1 / 2 * ∑ i, (t * lam i / (t
        * lam i + g)) ^ 2 + t ^ 2 * ∑ i, lam i ^ 2 * (g * affineFrame Q c w₀ i) ^ 2 / (t * lam i +
        g) ^ 3) - 2 * (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) +
        g / (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / t| ≤ K / t ^ 2 := by
  obtain ⟨K₁, T₁, hK₁, hT₁, h₁⟩ :=
    localisedVar_energy_order2 (hlam := hlam) (hgamma := hgamma) (hdisc := hdisc) hQ c w₀ hg
  refine ⟨K₁ + ∑ i, (3 / 2 * g ^ 2 + 3 * g * (g * affineFrame Q c w₀ i) ^ 2) / lam i ^ 2, T₁, ?_,
    hT₁, fun {t} ht => ?_⟩
  · have : 0 ≤ ∑ i, (3 / 2 * g ^ 2 + 3 * g * (g * affineFrame Q c w₀ i) ^ 2) / lam i ^ 2 :=
      Finset.sum_nonneg fun i _ => by
        have := hlam i
        positivity
    linarith
  have ht0 : 0 < t := by linarith
  have e₁ := h₁ ht
  have e₂ := anchoredGaussianVar_rate2 hlam hg (fun i => g * affineFrame Q c w₀ i) ht0
  have hC : 2 * (∑ i, energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) - (∑ i,
      (g * affineFrame Q c w₀ i) ^ 2 / lam i - ∑ i, g / lam i) = 2 * (∑ i, (energyLocCoeff1 (lam i)
      (alpha i) (gamma i) g (affineFrame Q c w₀ i) + g / (2 * lam i) - (g * affineFrame Q c w₀ i) ^
      2 / (2 * lam i))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (hlam i).ne'
    field_simp
    ring
  have e : t ^ 2 * gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t
      (rotatedAnharmonic Q c lam alpha gamma) (rotatedAnharmonic Q c lam alpha gamma) - (1 / 2 * ∑
      i, (t * lam i / (t * lam i + g)) ^ 2 + t ^ 2 * ∑ i, lam i ^ 2 * (g * affineFrame Q c w₀ i) ^ 2
      / (t * lam i + g) ^ 3) - 2 * (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame
      Q c w₀ i) + g / (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / t = (t ^ 2 *
      gibbsCov (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (rotatedAnharmonic Q c lam
      alpha gamma) (rotatedAnharmonic Q c lam alpha gamma) - (d : ℝ) / 2 - 2 * (∑ i, energyLocCoeff1
      (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)) / t) - ((1 / 2 * ∑ i, (t * lam i / (t *
      lam i + g)) ^ 2 + t ^ 2 * ∑ i, lam i ^ 2 * (g * affineFrame Q c w₀ i) ^ 2 / (t * lam i + g) ^
      3) - (d : ℝ) / 2 - (∑ i, (g * affineFrame Q c w₀ i) ^ 2 / lam i - ∑ i, g / lam i) / t) := by
    rw [← hC]
    ring
  rw [e]
  calc _ ≤ |_| + |_| := abs_sub _ _
    _ ≤ K₁ / t ^ 2 + (∑ i, (3 / 2 * g ^ 2 + 3 * g * (g * affineFrame Q c w₀ i) ^ 2) / lam i ^ 2) /
        t ^ 2 := add_le_add e₁ e₂
    _ = _ := by ring

end Multi

end Laplace.Multi
