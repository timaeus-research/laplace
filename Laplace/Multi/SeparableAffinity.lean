/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.SeparableRecovery

/-!
# Even multi-index moments and the exponent-affinity law

The multi-index layer of the separable degenerate programme (germbij
§7.4(b)): the normalized moment of an even monomial observable
`∏ i, w i ^ (2 j i)` against a separable weighted-monomial potential
is a product of one-dimensional moments, hence an exact power law
\[ \langle w^{2j} \rangle_t = C(k, a, j)\, t^{-\sum_i j_i / k_i}, \]
whose exponent is linear in the multi-index with zero intercept: the
note's normalized exponent-affinity `ℓ(α) = ∑ α_i q_i` with weights
`q_i = 1/(2 k_i)`, exact rather than asymptotic for this class.
-/

open Real MeasureTheory Filter

namespace Laplace

namespace OneD

/-- The general even moment of the scaled monomial potential is an
exact power law: `⟨x^(2j)⟩_{a·L_k, t} = ((2k)!/a)^(j/k) · Γratio ·
t^(-j/k)`. -/
theorem evenMoment_smul_kthPotential
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {a t : ℝ} (ha : 0 < a)
    (ht : 0 < t) :
    gibbsExpectation (fun x ↦ a * kthPotential k x) t
        (fun x ↦ x ^ (2 * j)) =
      (((Nat.factorial (2 * k) : ℝ) / a) ^ ((j : ℝ) / (k : ℝ)) *
          (Real.Gamma ((2 * j + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
            Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)))) *
        t ^ (-(j : ℝ) / (k : ℝ)) := by
  rw [gibbsExpectation_smul_kthPotential]
  have hta : 0 < t * a := mul_pos ht ha
  rw [gibbsExpectation_kthPotential_even hk j hta]
  have hsplit : ((Nat.factorial (2 * k) : ℝ) / (t * a)) ^
      ((j : ℝ) / (k : ℝ)) =
      ((Nat.factorial (2 * k) : ℝ) / a) ^ ((j : ℝ) / (k : ℝ)) *
        t ^ (-(j : ℝ) / (k : ℝ)) := by
    have h1 : (Nat.factorial (2 * k) : ℝ) / (t * a) =
        ((Nat.factorial (2 * k) : ℝ) / a) * t⁻¹ := by
      rw [mul_comm t a, ← div_div, div_eq_mul_inv]
    have hinv : t⁻¹ = t ^ (-1 : ℝ) := by
      rw [Real.rpow_neg ht.le, Real.rpow_one]
    rw [h1, Real.mul_rpow (by positivity) (by positivity), hinv,
      ← Real.rpow_mul ht.le]
    rw [show (-1 : ℝ) * ((j : ℝ) / (k : ℝ)) =
      -(j : ℝ) / (k : ℝ) by ring]
  rw [hsplit]
  ring

/-- The general even-moment power-law coefficient is positive. -/
theorem evenMoment_coeff_pos {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {a : ℝ}
    (ha : 0 < a) :
    0 < ((Nat.factorial (2 * k) : ℝ) / a) ^ ((j : ℝ) / (k : ℝ)) *
      (Real.Gamma ((2 * j + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
        Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ))) := by
  have hfac : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have h2k : (0 : ℝ) < ((2 * k : ℕ) : ℝ) := by
    have : (0 : ℕ) < 2 * k := by omega
    exact_mod_cast this
  have hΓ₁ : 0 < Real.Gamma ((2 * j + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hΓ₂ : 0 < Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hrpow : 0 < ((Nat.factorial (2 * k) : ℝ) / a) ^
      ((j : ℝ) / (k : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  positivity

end OneD

namespace Multi

variable {ι : Type*} [Fintype ι]

/-- The even monomial observable `w ↦ ∏ i, w i ^ (2 j i)`. -/
def evenMonomial (j : ι → ℕ) : (ι → ℝ) → ℝ :=
  fun w ↦ ∏ i, (w i) ^ (2 * j i)

/-- The unnormalized even-monomial moment of a separable potential
factorizes into one-dimensional even moments. -/
theorem evenMonomial_integral_separableMonomial (a : ι → ℝ)
    (k j : ι → ℕ) (t : ℝ) :
    ∫ w : ι → ℝ, evenMonomial j w *
        Real.exp (-(t * separableMonomial a k w)) =
      ∏ i, ∫ x : ℝ, x ^ (2 * j i) *
        Real.exp (-(t * (a i * OneD.kthPotential (k i) x))) := by
  have hpt : ∀ w : ι → ℝ, evenMonomial j w *
      Real.exp (-(t * separableMonomial a k w)) =
      ∏ i, (w i) ^ (2 * j i) *
        Real.exp (-(t * (a i * OneD.kthPotential (k i) (w i)))) := by
    intro w
    rw [exp_separableMonomial a k t w, evenMonomial,
      Finset.prod_mul_distrib]
  calc ∫ w : ι → ℝ, evenMonomial j w *
        Real.exp (-(t * separableMonomial a k w))
      = ∫ w : ι → ℝ, ∏ i, (w i) ^ (2 * j i) *
          Real.exp (-(t * (a i * OneD.kthPotential (k i) (w i)))) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∏ i, ∫ x : ℝ, x ^ (2 * j i) *
          Real.exp (-(t * (a i * OneD.kthPotential (k i) x))) :=
        integral_fintype_prod_volume_eq_prod
          (f := fun i x ↦ x ^ (2 * j i) *
            Real.exp (-(t * (a i * OneD.kthPotential (k i) x))))

/-- **Normalized product form**: the Gibbs expectation of an even
monomial against a separable potential is the product of the
one-dimensional normalized moments (all spectator cancellations at
once; the identity is field algebra, needing no positivity). -/
theorem gibbsExpectation_evenMonomial_separableMonomial
    (a : ι → ℝ) (k j : ι → ℕ) (t : ℝ) :
    gibbsExpectation (separableMonomial a k) t (evenMonomial j) =
      ∏ i, _root_.Laplace.gibbsExpectation
        (fun x ↦ a i * OneD.kthPotential (k i) x) t
        (fun x ↦ x ^ (2 * j i)) := by
  unfold gibbsExpectation _root_.Laplace.gibbsExpectation
    _root_.Laplace.partitionFunction
  rw [evenMonomial_integral_separableMonomial,
    partitionFunction_separableMonomial, ← Finset.prod_div_distrib]
  rfl

/-- **Exact exponent affinity** (germbij §7.4(b), normalized form):
the even multi-index moment is an exact power law whose exponent
`∑ i, j i / k i = ∑ i, (2 j i) q i` is linear in the multi-index
with zero intercept, where `q i = 1/(2 k i)` are the anisotropic
weights. -/
theorem gibbsExpectation_evenMonomial_powerLaw
    {a : ι → ℝ} {k : ι → ℕ} (ha : ∀ i, 0 < a i) (hk : ∀ i, 1 ≤ k i)
    (j : ι → ℕ) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation (separableMonomial a k) t (evenMonomial j) =
      (∏ i, ((Nat.factorial (2 * k i) : ℝ) / a i) ^
          ((j i : ℝ) / (k i : ℝ)) *
        (Real.Gamma ((2 * j i + 1 : ℝ) / ((2 * k i : ℕ) : ℝ)) /
          Real.Gamma ((1 : ℝ) / ((2 * k i : ℕ) : ℝ)))) *
        t ^ (-∑ i, (j i : ℝ) / (k i : ℝ)) := by
  rw [gibbsExpectation_evenMonomial_separableMonomial]
  have hterm : ∀ i : ι, _root_.Laplace.gibbsExpectation
      (fun x ↦ a i * OneD.kthPotential (k i) x) t
      (fun x ↦ x ^ (2 * j i)) =
      (((Nat.factorial (2 * k i) : ℝ) / a i) ^
          ((j i : ℝ) / (k i : ℝ)) *
        (Real.Gamma ((2 * j i + 1 : ℝ) / ((2 * k i : ℕ) : ℝ)) /
          Real.Gamma ((1 : ℝ) / ((2 * k i : ℕ) : ℝ)))) *
        t ^ (-(j i : ℝ) / (k i : ℝ)) := fun i ↦
    OneD.evenMoment_smul_kthPotential (hk i) (j i) (ha i) ht
  rw [Finset.prod_congr rfl fun i _ ↦ hterm i,
    Finset.prod_mul_distrib]
  congr 1
  rw [← Real.rpow_sum_of_pos ht _ Finset.univ]
  congr 1
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ neg_div _ _

/-- The affinity coefficient is positive (so the exponent is
observable: the moment functions are genuine positive power laws). -/
theorem evenMonomial_powerLaw_coeff_pos
    {a : ι → ℝ} {k : ι → ℕ} (ha : ∀ i, 0 < a i) (hk : ∀ i, 1 ≤ k i)
    (j : ι → ℕ) :
    0 < ∏ i, ((Nat.factorial (2 * k i) : ℝ) / a i) ^
        ((j i : ℝ) / (k i : ℝ)) *
      (Real.Gamma ((2 * j i + 1 : ℝ) / ((2 * k i : ℕ) : ℝ)) /
        Real.Gamma ((1 : ℝ) / ((2 * k i : ℕ) : ℝ))) :=
  Finset.prod_pos fun i _ ↦
    OneD.evenMoment_coeff_pos (hk i) (j i) (ha i)

end Multi

end Laplace
