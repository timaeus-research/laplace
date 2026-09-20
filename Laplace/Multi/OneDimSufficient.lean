/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.SufficientFamilies
import Laplace.OneD.GaussianMoments

/-!
# In one dimension, `x²` and `x³` suffice at every degree

The observation operator of a family `S` on the degree-`k` homogeneous
polynomials is injective iff `S` recovers the degree-`k` Taylor tensor at the
leading rate (`SufficientFamilies`). In dimension one `H_k = ℝ·x^k`, so a
family is sufficient at degree `k` iff some member has nonzero Gaussian
covariance with `x^k`. Under `γ = N(0, h⁻¹)`,

  `Cov_γ[x², x^{2j}] = h^{-(j+1)} · 2j · (2j-1)‼ > 0`   (`j ≥ 1`),
  `Cov_γ[x³, x^{2j+1}] = h^{-(j+2)} · (2j+3)‼ > 0`,

from the moments `E[x^{2j}] = (2j-1)‼ h^{-j}` and `E[x^{odd}] = 0`. Hence the
two-element family `{x², x³}` is sufficient at every degree `k ≥ 1`
(`family_two_three_injective`, and the kernel form
`pairingMap_two_three_ker_eq_bot` feeding
`iteratedFDeriv_recovery_of_pairingMap_ker_eq_bot`). This is the
one-dimensional counterpart of the finite-family obstruction in `d ≥ 2`.
-/

open MeasureTheory Set Filter Real
open scoped Nat

namespace Laplace.Multi

/-! ### The one-dimensional bridge -/

/-- Integrals over `EuclidD 1` of functions of the single coordinate. -/
theorem integral_euclidD_one (f : ℝ → ℝ) : ∫ x : EuclidD 1, f (x 0) = ∫ s : ℝ, f s := by
  rw [← (PiLp.volume_preserving_toLp (Fin 1)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding (fun x : EuclidD 1 ↦ f (x 0)),
    ← (volume_preserving_funUnique (Fin 1) ℝ).integral_comp' (fun s : ℝ ↦ f s)]
  rfl

/-- The quadratic form of a `1 × 1` matrix. -/
theorem qform_fin_one (H : Matrix (Fin 1) (Fin 1) ℝ) (x : EuclidD 1) :
    qform H x = H 0 0 * (x 0) ^ 2 := by
  rw [qform_eq_dotProduct]
  simp [Matrix.mulVec, dotProduct]
  ring

/-- Coordinate moments against the `1 × 1` Gaussian kernel, unnormalized. -/
theorem integral_pow_mul_quadKernel_fin_one (H : Matrix (Fin 1) (Fin 1) ℝ) (n : ℕ) :
    ∫ x : EuclidD 1, (x 0) ^ n * quadKernel H x =
      ∫ s : ℝ, s ^ n * Real.exp (-(H 0 0 * s ^ 2) / 2) := by
  have h := integral_euclidD_one (fun s : ℝ ↦ s ^ n * Real.exp (-(H 0 0 * s ^ 2) / 2))
  refine Eq.trans ?_ h
  congr 1
  funext x
  simp only [quadKernel, qform_fin_one]

/-- Odd moments of the rescaled Gaussian vanish. -/
theorem integral_pow_odd_mul_exp_neg_t_sq_half (k : ℕ) (t : ℝ) :
    ∫ s : ℝ, s ^ (2 * k + 1) * Real.exp (-(t * s ^ 2) / 2) = 0 := by
  set f : ℝ → ℝ := fun s ↦ s ^ (2 * k + 1) * Real.exp (-(t * s ^ 2) / 2) with hf
  have hodd : ∀ s : ℝ, f (-s) = -(f s) := by
    intro s
    simp only [hf]
    rw [Odd.neg_pow ⟨k, rfl⟩, neg_sq, neg_mul]
  have heq : (∫ s, f s) = -(∫ s, f s) := by
    conv_lhs => rw [← integral_neg_eq_self f volume]
    rw [show (fun s ↦ f (-s)) = fun s ↦ -(f s) from funext hodd, integral_neg]
  exact self_eq_neg.mp heq

/-! ### Normalized moments -/

/-- The `1 × 1` positive-definite entry is positive. -/
theorem posDef_fin_one_pos {H : Matrix (Fin 1) (Fin 1) ℝ} (hH : H.PosDef) : 0 < H 0 0 := by
  have h := hH.det_pos
  rwa [Matrix.det_fin_one] at h

/-- Even normalized moments: `E_γ[x^{2j}] = (2j-1)‼ h^{-j}`. -/
theorem gaussianExpectation_pow_even_fin_one {H : Matrix (Fin 1) (Fin 1) ℝ} (hH : H.PosDef)
    (j : ℕ) :
    gaussianExpectation H (fun x : EuclidD 1 ↦ (x 0) ^ (2 * j)) =
      ((2 * j - 1)‼ : ℝ) * ((H 0 0)⁻¹) ^ j := by
  have hh := posDef_fin_one_pos hH
  unfold gaussianExpectation
  have h0 : ∫ x : EuclidD 1, quadKernel H x =
      ∫ x : EuclidD 1, (x 0) ^ (2 * 0) * quadKernel H x := by
    congr 1
    funext x
    simp
  rw [h0, integral_pow_mul_quadKernel_fin_one, integral_pow_mul_quadKernel_fin_one,
    Laplace.OneD.integral_pow_mul_exp_neg_t_sq_half j hh,
    Laplace.OneD.integral_pow_mul_exp_neg_t_sq_half 0 hh]
  have hsq : (0 : ℝ) < Real.sqrt (2 * π) := by positivity
  have hp0 : 0 < H 0 0 ^ (-((0 : ℕ) + 1 / 2 : ℝ)) := Real.rpow_pos_of_pos hh _
  have hratio : H 0 0 ^ (-((j : ℝ) + 1 / 2)) =
      H 0 0 ^ (-((0 : ℕ) + 1 / 2 : ℝ)) * ((H 0 0)⁻¹) ^ j := by
    rw [← Real.rpow_natCast (H 0 0)⁻¹ j, Real.inv_rpow hh.le, ← Real.rpow_neg hh.le,
      ← Real.rpow_add hh]
    congr 1
    push_cast
    ring
  have h0f : ((2 * 0 - 1)‼ : ℝ) = 1 := by norm_num [Nat.doubleFactorial]
  rw [hratio, h0f]
  field_simp

/-- Odd normalized moments vanish. -/
theorem gaussianExpectation_pow_odd_fin_one (H : Matrix (Fin 1) (Fin 1) ℝ) (j : ℕ) :
    gaussianExpectation H (fun x : EuclidD 1 ↦ (x 0) ^ (2 * j + 1)) = 0 := by
  unfold gaussianExpectation
  rw [integral_pow_mul_quadKernel_fin_one, integral_pow_odd_mul_exp_neg_t_sq_half, zero_div]

/-- Covariance of two coordinate powers as a moment difference. -/
theorem gaussianCovariance_pow_pow_fin_one (H : Matrix (Fin 1) (Fin 1) ℝ) (a b : ℕ) :
    gaussianCovariance H (fun x : EuclidD 1 ↦ (x 0) ^ a) (fun x ↦ (x 0) ^ b) =
      gaussianExpectation H (fun x : EuclidD 1 ↦ (x 0) ^ (a + b)) -
        gaussianExpectation H (fun x : EuclidD 1 ↦ (x 0) ^ a) *
          gaussianExpectation H (fun x : EuclidD 1 ↦ (x 0) ^ b) := by
  unfold gaussianCovariance
  congr 2
  funext x
  rw [pow_add]

/-- `Cov_γ[x², x^{2j}] > 0` for `j ≥ 1`. -/
theorem gaussianCovariance_sq_pow_even_pos {H : Matrix (Fin 1) (Fin 1) ℝ} (hH : H.PosDef)
    {j : ℕ} (hj : 1 ≤ j) :
    0 < gaussianCovariance H (fun x : EuclidD 1 ↦ (x 0) ^ 2) (fun x ↦ (x 0) ^ (2 * j)) := by
  have hh := posDef_fin_one_pos hH
  rw [gaussianCovariance_pow_pow_fin_one, show 2 + 2 * j = 2 * (j + 1) by ring,
    show (2 : ℕ) = 2 * 1 by norm_num, gaussianExpectation_pow_even_fin_one hH,
    gaussianExpectation_pow_even_fin_one hH, gaussianExpectation_pow_even_fin_one hH]
  have hinv : 0 < (H 0 0)⁻¹ := inv_pos.mpr hh
  have hpow : 0 < ((H 0 0)⁻¹) ^ j := pow_pos hinv j
  -- `(2j+1)‼ = (2j+1) (2j-1)‼`
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hdf : ((2 * (i + 1 + 1) - 1)‼ : ℝ) = (2 * i + 3) * ((2 * (i + 1) - 1)‼ : ℝ) := by
    rw [show 2 * (i + 1 + 1) - 1 = (2 * i + 1) + 2 by omega, Nat.doubleFactorial_add_two,
      show 2 * (i + 1) - 1 = 2 * i + 1 by omega]
    push_cast
    ring
  have h1f : ((2 * 1 - 1)‼ : ℝ) = 1 := by norm_num [Nat.doubleFactorial]
  rw [hdf, h1f, one_mul, pow_one]
  have hdf0 : (0 : ℝ) < ((2 * (i + 1) - 1)‼ : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hA : 0 < ((2 * (i + 1) - 1)‼ : ℝ) * ((H 0 0)⁻¹) ^ (i + 1 + 1) := by positivity
  have key : (2 * (i : ℝ) + 3) * ((2 * (i + 1) - 1)‼ : ℝ) * ((H 0 0)⁻¹) ^ (i + 1 + 1) -
      (H 0 0)⁻¹ * (((2 * (i + 1) - 1)‼ : ℝ) * ((H 0 0)⁻¹) ^ (i + 1)) =
      (2 * (i : ℝ) + 2) * (((2 * (i + 1) - 1)‼ : ℝ) * ((H 0 0)⁻¹) ^ (i + 1 + 1)) := by ring
  nlinarith [key, hA]

/-- `Cov_γ[x³, x^{2j+1}] > 0`. -/
theorem gaussianCovariance_cube_pow_odd_pos {H : Matrix (Fin 1) (Fin 1) ℝ} (hH : H.PosDef)
    (j : ℕ) :
    0 < gaussianCovariance H (fun x : EuclidD 1 ↦ (x 0) ^ 3) (fun x ↦ (x 0) ^ (2 * j + 1)) := by
  have hh := posDef_fin_one_pos hH
  rw [gaussianCovariance_pow_pow_fin_one, show 3 + (2 * j + 1) = 2 * (j + 2) by ring,
    show (3 : ℕ) = 2 * 1 + 1 by norm_num, gaussianExpectation_pow_even_fin_one hH,
    gaussianExpectation_pow_odd_fin_one, zero_mul, sub_zero]
  have hinv : 0 < (H 0 0)⁻¹ := inv_pos.mpr hh
  have hdf0 : (0 : ℝ) < ((2 * (j + 2) - 1)‼ : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
  positivity

/-! ### The degree-`k` homogeneous polynomials in one variable -/

/-- Every monomial word in one variable is `x^k`. -/
theorem monomialTest_fin_one {k : ℕ} (m : Fin k → Fin 1) :
    monomialTest m = fun x : EuclidD 1 ↦ (x 0) ^ k := by
  funext x
  unfold monomialTest
  have : ∀ j : Fin k, x (m j) = x 0 := fun j ↦ by rw [Subsingleton.elim (m j) 0]
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `H_k = ℝ · x^k` in one variable. -/
theorem mem_homogPolySpan_one_iff {k : ℕ} {Q : EuclidD 1 → ℝ} :
    Q ∈ homogPolySpan 1 k ↔ ∃ c : ℝ, Q = fun x ↦ c * (x 0) ^ k := by
  unfold homogPolySpan
  rw [Set.range_unique, monomialTest_fin_one, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by funext x; simp⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by funext x; simp⟩

/-- **`{x², x³}` is sufficient at every degree `k ≥ 1` in one dimension**: a
degree-`k` homogeneous polynomial with vanishing covariance against both `x²`
and `x³` is zero. -/
theorem family_two_three_injective {H : Matrix (Fin 1) (Fin 1) ℝ} (hH : H.PosDef)
    {k : ℕ} (hk : 0 < k) {Q : EuclidD 1 → ℝ} (hQ : Q ∈ homogPolySpan 1 k)
    (h2 : gaussianCovariance H (fun x : EuclidD 1 ↦ (x 0) ^ 2) Q = 0)
    (h3 : gaussianCovariance H (fun x : EuclidD 1 ↦ (x 0) ^ 3) Q = 0) : Q = 0 := by
  obtain ⟨c, rfl⟩ := mem_homogPolySpan_one_iff.mp hQ
  have hsmul : (fun x : EuclidD 1 ↦ c * (x 0) ^ k) = c • fun x : EuclidD 1 ↦ (x 0) ^ k := by
    funext x
    simp
  rw [hsmul, gaussianCovariance_const_smul_right] at h2 h3
  suffices hc : c = 0 by rw [hsmul, hc, zero_smul]
  rcases Nat.even_or_odd' k with ⟨j, hj | hj⟩
  · subst hj
    have hj1 : 1 ≤ j := by omega
    exact (mul_eq_zero.mp h2).resolve_right (gaussianCovariance_sq_pow_even_pos hH hj1).ne'
  · subst hj
    exact (mul_eq_zero.mp h3).resolve_right (gaussianCovariance_cube_pow_odd_pos hH j).ne'

/-- The family `{x², x³}` as monomial words, for the pairing map. -/
def twoThreeFamily : Fin 2 → EuclidD 1 → ℝ :=
  ![monomialTest (fun _ : Fin 2 ↦ (0 : Fin 1)), monomialTest (fun _ : Fin 3 ↦ (0 : Fin 1))]

theorem twoThreeFamily_continuous (i : Fin 2) : Continuous (twoThreeFamily i) := by
  fin_cases i <;> exact monomialTest_continuous _

theorem twoThreeFamily_hasPolynomialGrowth (i : Fin 2) :
    HasPolynomialGrowth (twoThreeFamily i) := by
  fin_cases i <;> exact monomialTest_hasPolynomialGrowth _

/-- **Kernel form**: the observation operator of `{x², x³}` is injective on
`H_k` for every `k ≥ 1`, ready for `iteratedFDeriv_recovery_of_pairingMap_ker_eq_bot`. -/
theorem pairingMap_two_three_ker_eq_bot {H : Matrix (Fin 1) (Fin 1) ℝ} (hH : H.PosDef)
    {k : ℕ} (hk : 0 < k) :
    LinearMap.ker (pairingMap (k := k) hH twoThreeFamily twoThreeFamily_continuous
      twoThreeFamily_hasPolynomialGrowth) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro Q hQ
  have h2 : gaussianCovariance H (twoThreeFamily 0) Q = 0 := congrFun hQ 0
  have h3 : gaussianCovariance H (twoThreeFamily 1) Q = 0 := congrFun hQ 1
  simp only [twoThreeFamily, Matrix.cons_val_zero, Matrix.cons_val_one,
    monomialTest_fin_one] at h2 h3
  exact Subtype.ext (family_two_three_injective hH hk Q.2 h2 h3)

end Laplace.Multi
