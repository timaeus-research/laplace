/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.OneDimSufficient
import Laplace.Multi.MonomialTests

/-!
# In one dimension, the two rescaled tests `u` and `u²` recover the whole Taylor series

The positive counterpart of `CyclicBlindness`: in `d = 1` a fixed two-element family of rescaled
tests identifies every derivative tensor at a nondegenerate minimum. Under `γ = N(0, h⁻¹)`,
`Cov_γ[x, x^{2j+1}] = E[x^{2j+2}] > 0` and `Cov_γ[x², x^{2j}] > 0` (`OneDimSufficient`), so the
observation operator of `{x, x²}` is injective on `H_k = ℝ·x^k` for every `k ≥ 1`
(`family_one_two_injective`, `pairingMap_one_two_ker_eq_bot`). The family-generic all-orders
wrapper (`smooth_jet_recovery_of_family_rates`, strong induction on the degree feeding
`iteratedFDeriv_recovery_of_pairingMap_ker_eq_bot`) then gives the headline
(`oneDim_two_tests_recover_jet`): if two certified one-dimensional losses with the same jet to
order `2` have rescaled moments at `u` and `u²` that agree on a right neighbourhood of `q = 0`,
at every degree, then all their derivative tensors at the origin agree. The mechanism is the
triangular one: the first unknown coefficient `a_k x^k` enters `E_t[φ(√t x)]` through
`-a_k Cov_γ(φ(U), U^k)` (`tendsto_pairwise_normalized_moment_difference`), nonzero for `φ = U`
when `k` is odd and `φ = U²` when `k` is even.
-/

open MeasureTheory Set Filter Real Asymptotics
open scoped Nat Topology

namespace Laplace.Multi

/-! ### `Cov_γ[x, x^{2j+1}] > 0` -/

theorem gaussianCovariance_one_pow_odd_pos {H : Matrix (Fin 1) (Fin 1) ℝ} (hH : H.PosDef)
    (j : ℕ) :
    0 < gaussianCovariance H (fun x : EuclidD 1 ↦ (x 0) ^ 1) (fun x ↦ (x 0) ^ (2 * j + 1)) := by
  have hh := posDef_fin_one_pos hH
  have h1 : gaussianExpectation H (fun x : EuclidD 1 ↦ (x 0) ^ 1) = 0 := by
    simpa using gaussianExpectation_pow_odd_fin_one H 0
  rw [gaussianCovariance_pow_pow_fin_one, show 1 + (2 * j + 1) = 2 * (j + 1) by ring,
    gaussianExpectation_pow_even_fin_one hH, h1, zero_mul, sub_zero]
  have hinv : 0 < (H 0 0)⁻¹ := inv_pos.mpr hh
  have hdf0 : (0 : ℝ) < ((2 * (j + 1) - 1)‼ : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
  positivity

/-- **`{x, x²}` is sufficient at every degree `k ≥ 1` in one dimension.** -/
theorem family_one_two_injective {H : Matrix (Fin 1) (Fin 1) ℝ} (hH : H.PosDef)
    {k : ℕ} (hk : 0 < k) {Q : EuclidD 1 → ℝ} (hQ : Q ∈ homogPolySpan 1 k)
    (h1 : gaussianCovariance H (fun x : EuclidD 1 ↦ (x 0) ^ 1) Q = 0)
    (h2 : gaussianCovariance H (fun x : EuclidD 1 ↦ (x 0) ^ 2) Q = 0) : Q = 0 := by
  obtain ⟨c, rfl⟩ := mem_homogPolySpan_one_iff.mp hQ
  have hsmul : (fun x : EuclidD 1 ↦ c * (x 0) ^ k) = c • fun x : EuclidD 1 ↦ (x 0) ^ k := by
    funext x
    simp
  rw [hsmul, gaussianCovariance_const_smul_right] at h1 h2
  suffices hc : c = 0 by rw [hsmul, hc, zero_smul]
  rcases Nat.even_or_odd' k with ⟨j, hj | hj⟩
  · subst hj
    have hj1 : 1 ≤ j := by omega
    exact (mul_eq_zero.mp h2).resolve_right (gaussianCovariance_sq_pow_even_pos hH hj1).ne'
  · subst hj
    exact (mul_eq_zero.mp h1).resolve_right (gaussianCovariance_one_pow_odd_pos hH j).ne'

/-- The family `{x, x²}` as monomial words. -/
def oneTwoFamily : Fin 2 → EuclidD 1 → ℝ :=
  ![monomialTest (fun _ : Fin 1 ↦ (0 : Fin 1)), monomialTest (fun _ : Fin 2 ↦ (0 : Fin 1))]

theorem oneTwoFamily_continuous (i : Fin 2) : Continuous (oneTwoFamily i) := by
  fin_cases i <;> exact monomialTest_continuous _

theorem oneTwoFamily_hasPolynomialGrowth (i : Fin 2) : HasPolynomialGrowth (oneTwoFamily i) := by
  fin_cases i <;> exact monomialTest_hasPolynomialGrowth _

theorem pairingMap_one_two_ker_eq_bot {H : Matrix (Fin 1) (Fin 1) ℝ} (hH : H.PosDef)
    {k : ℕ} (hk : 0 < k) :
    LinearMap.ker (pairingMap (k := k) hH oneTwoFamily oneTwoFamily_continuous
      oneTwoFamily_hasPolynomialGrowth) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro Q hQ
  have h1 : gaussianCovariance H (oneTwoFamily 0) Q = 0 := congrFun hQ 0
  have h2 : gaussianCovariance H (oneTwoFamily 1) Q = 0 := congrFun hQ 1
  simp only [oneTwoFamily, Matrix.cons_val_zero, Matrix.cons_val_one,
    monomialTest_fin_one] at h1 h2
  exact Subtype.ext (family_one_two_injective hH hk Q.2 h1 h2)

/-! ### Family-generic all-orders recovery -/

namespace HigherLaplaceDomain

variable {d : ℕ} {L₁ L₂ : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- Rescaled moments that agree near `q = 0` give `o(q^(k-2))` data. -/
theorem isLittleO_of_eventuallyEq {k : ℕ} (A₁ : HigherLaplaceDomain k L₁ H)
    (A₂ : HigherLaplaceDomain k L₂ H) {P : EuclidD d → ℝ}
    (h : ∀ᶠ q in 𝓝[>] (0 : ℝ), A₁.rescaledMoment P q = A₂.rescaledMoment P q) :
    (fun q : ℝ ↦ A₁.rescaledMoment P q - A₂.rescaledMoment P q)
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (k - 2) := by
  refine (isLittleO_zero _ _).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [h] with q hq
  simp [hq]

/-- **All-orders recovery from a family whose observation operator is injective at every
degree.** Strong induction on the degree through
`iteratedFDeriv_recovery_of_pairingMap_ker_eq_bot`. -/
theorem smooth_jet_recovery_of_family_rates
    (A : ∀ k, 2 < k → HigherLaplaceDomain k L₁ H)
    (B : ∀ k, 2 < k → HigherLaplaceDomain k L₂ H)
    (hbase : ∀ j < 3, iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    (hsymm₁ : ∀ k, 2 < k → (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (hsymm₂ : ∀ k, 2 < k → (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    {ι : Type*} (F : ι → EuclidD d → ℝ)
    (hFc : ∀ i, Continuous (F i)) (hFg : ∀ i, HasPolynomialGrowth (F i))
    (hker : ∀ k (h2 : 2 < k),
      LinearMap.ker (pairingMap (k := k) (A k h2).hH_posDef F hFc hFg) = ⊥)
    (hdata : ∀ k (h2 : 2 < k), ∀ i,
      (fun q : ℝ ↦ (A k h2).rescaledMoment (F i) q - (B k h2).rescaledMoment (F i) q)
        =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (k - 2)) :
    ∀ j, iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj3 : j < 3
    · exact hbase j hj3
    · have h2j : 2 < j := by omega
      exact iteratedFDeriv_recovery_of_pairingMap_ker_eq_bot h2j (A j h2j) (B j h2j)
        (fun i hi ↦ ih i hi) (hsymm₁ j h2j) (hsymm₂ j h2j) F hFc hFg (hker j h2j)
        (hdata j h2j)

end HigherLaplaceDomain

/-! ### Headline -/

open HigherLaplaceDomain in
/-- **In one dimension the two rescaled tests `u`, `u²` recover the whole jet.** For certified
one-dimensional losses with the same jet to order `2` whose rescaled moments at `x` and `x²`
agree near `q = 0` at every degree, every derivative tensor at the origin agrees. -/
theorem oneDim_two_tests_recover_jet {L₁ L₂ : EuclidD 1 → ℝ} {H : Matrix (Fin 1) (Fin 1) ℝ}
    (A : ∀ k, 2 < k → HigherLaplaceDomain k L₁ H)
    (B : ∀ k, 2 < k → HigherLaplaceDomain k L₂ H)
    (hbase : ∀ j < 3, iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    (hsymm₁ : ∀ k, 2 < k → (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (hsymm₂ : ∀ k, 2 < k → (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    (hdata : ∀ k (h2 : 2 < k), ∀ i : Fin 2, ∀ᶠ q in 𝓝[>] (0 : ℝ),
      (A k h2).rescaledMoment (oneTwoFamily i) q = (B k h2).rescaledMoment (oneTwoFamily i) q) :
    ∀ j, iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0 :=
  smooth_jet_recovery_of_family_rates A B hbase hsymm₁ hsymm₂ oneTwoFamily
    oneTwoFamily_continuous oneTwoFamily_hasPolynomialGrowth
    (fun k h2 ↦ pairingMap_one_two_ker_eq_bot (A k h2).hH_posDef (by omega))
    (fun k h2 i ↦ isLittleO_of_eventuallyEq (A k h2) (B k h2) (hdata k h2 i))

end Laplace.Multi
