/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.SufficientFamilies

/-!
# The `H`-uniform spanning criterion for sufficient families

`SufficientFamilies` characterises a sufficient family of observables at
degree `k` by injectivity of the observation operator
`Q ↦ (Cov_γ[φ_i, Q])_i` on the degree-`k` homogeneous polynomials, a
condition that depends on the Hessian `H` through `γ = N(0, H⁻¹)`. Here
is the `H`-uniform sufficient condition: if every monomial word of degree
`k` is a finite linear combination of the `φ_i` plus a constant, *as a
function*, then the observation operator is injective for every positive
definite `H` (`family_injective_of_span`). The proof is linearity of the
Gaussian covariance in the first slot together with `Cov_γ[c, Q] = 0` for
constants, reducing to the monomial family's injectivity.

The consult's warning stands: it is the functions, not their `k`-jets,
that must span.
-/

open Asymptotics Filter MeasureTheory

namespace Laplace.Multi

variable {d k : ℕ}

/-- The Gaussian expectation of a constant is the constant. -/
theorem gaussianExpectation_const {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (c : ℝ) :
    gaussianExpectation H (fun _ ↦ c) = c := by
  unfold gaussianExpectation
  rw [integral_const_mul, mul_div_assoc, div_self (integral_quadKernel_pos hH).ne', mul_one]

/-- Constants are uncorrelated with everything. -/
theorem gaussianCovariance_const_left {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (c : ℝ) (Q : EuclidD d → ℝ) :
    gaussianCovariance H (fun _ ↦ c) Q = 0 := by
  unfold gaussianCovariance
  rw [gaussianExpectation_const hH, gaussianExpectation_const_mul]
  ring

/-- Finite combinations of continuous polynomially growing observables are
continuous with polynomial growth. -/
theorem continuous_finset_combo {ι : Type*} (φ : ι → EuclidD d → ℝ)
    (hφc : ∀ i, Continuous (φ i)) (c : ι → ℝ) (s : Finset ι) :
    Continuous fun x ↦ ∑ i ∈ s, c i * φ i x :=
  continuous_finsetSum s fun i _ ↦ (continuous_const (y := c i)).mul (hφc i)

theorem hasPolynomialGrowth_finset_combo {ι : Type*} (φ : ι → EuclidD d → ℝ)
    (hφg : ∀ i, HasPolynomialGrowth (φ i)) (c : ι → ℝ) (s : Finset ι) :
    HasPolynomialGrowth fun x ↦ ∑ i ∈ s, c i * φ i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, le_rfl, fun x ↦ by simp⟩
  | insert b s hb ih =>
    have h1 : HasPolynomialGrowth (c b • φ b) := (hφg b).const_smul (c b)
    have h2 := h1.add ih
    refine ⟨h2.choose, h2.choose_spec.choose, h2.choose_spec.choose_spec.1, fun x ↦ ?_⟩
    have := h2.choose_spec.choose_spec.2 x
    simpa [Finset.sum_insert hb, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this

/-- Linearity of the covariance in the first slot over a finite combination
of continuous polynomially growing observables. -/
theorem gaussianCovariance_finset_sum_left {ι : Type*} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) (φ : ι → EuclidD d → ℝ)
    (hφc : ∀ i, Continuous (φ i)) (hφg : ∀ i, HasPolynomialGrowth (φ i))
    (c : ι → ℝ) (s : Finset ι) {Q : EuclidD d → ℝ}
    (hQc : Continuous Q) (hQg : HasPolynomialGrowth Q) :
    gaussianCovariance H (fun x ↦ ∑ i ∈ s, c i * φ i x) Q =
      ∑ i ∈ s, c i * gaussianCovariance H (φ i) Q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [gaussianCovariance_comm]
    rw [show (fun _ : EuclidD d ↦ (0 : ℝ)) = (0 : ℝ) • Q by funext x; simp,
      gaussianCovariance_const_smul_right, zero_mul]
  | insert a s ha ih =>
    have hsc := continuous_finset_combo φ hφc c s
    have hsg := hasPolynomialGrowth_finset_combo φ hφg c s
    have hfun : (fun x ↦ ∑ i ∈ insert a s, c i * φ i x) =
        (c a • φ a) + fun x ↦ ∑ i ∈ s, c i * φ i x := by
      funext x
      simp [Finset.sum_insert ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_insert ha, hfun, gaussianCovariance_comm, gaussianCovariance_add_right hH
      hQc hQg ((hφc a).const_smul (c a)) ((hφg a).const_smul (c a)) hsc hsg,
      gaussianCovariance_const_smul_right, gaussianCovariance_comm Q (φ a),
      gaussianCovariance_comm Q (fun x ↦ ∑ i ∈ s, c i * φ i x), ih]

/-- **The `H`-uniform spanning criterion.** If every degree-`k` monomial word
is a finite combination of the `φ_i` plus a constant, as a function, then
the family's observation operator is injective on the degree-`k`
homogeneous polynomials for every positive definite `H`. -/
theorem family_injective_of_span {ι : Type*} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) (hk : 0 < k) (φ : ι → EuclidD d → ℝ)
    (hφc : ∀ i, Continuous (φ i)) (hφg : ∀ i, HasPolynomialGrowth (φ i))
    (hspan : ∀ m : Fin k → Fin d, ∃ (s : Finset ι) (c : ι → ℝ) (c₀ : ℝ),
      monomialTest m = fun x ↦ (∑ i ∈ s, c i * φ i x) + c₀) :
    ∀ Q ∈ homogPolySpan d k,
      (∀ i, gaussianCovariance H (φ i) Q = 0) → Q = 0 := by
  intro Q hQ hpair
  refine monomialTest_family_injective hH hk Q hQ fun m ↦ ?_
  obtain ⟨s, c, c₀, hm⟩ := hspan m
  have hQc := homogPolySpan_continuous hQ
  have hQg := homogPolySpan_hasPolynomialGrowth hQ
  have hsc := continuous_finset_combo φ hφc c s
  have hsg := hasPolynomialGrowth_finset_combo φ hφg c s
  rw [hm]
  have hfun : (fun x ↦ (∑ i ∈ s, c i * φ i x) + c₀) =
      (fun x ↦ ∑ i ∈ s, c i * φ i x) + fun _ ↦ c₀ := by
    funext x
    simp [Pi.add_apply]
  rw [hfun, gaussianCovariance_comm, gaussianCovariance_add_right hH hQc hQg hsc hsg
    continuous_const ⟨|c₀|, 0, abs_nonneg _, fun x ↦ by
      simp only [pow_zero]; linarith [abs_nonneg c₀]⟩, gaussianCovariance_comm Q,
    gaussianCovariance_finset_sum_left hH φ hφc hφg c s hQc hQg, gaussianCovariance_comm Q,
    gaussianCovariance_const_left hH]
  simp [hpair]

end Laplace.Multi
