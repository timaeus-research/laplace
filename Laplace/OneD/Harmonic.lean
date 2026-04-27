import Laplace.Gibbs
import Laplace.OneD.GaussianMoments

/-!
# The harmonic 1D Gibbs measure

For the harmonic potential `L(x) = (λ/2) x²` with `λ > 0`, this file proves the
explicit forms of the partition function and the moments under the Gibbs
measure `exp(-t · L(x)) dx`:

* `partitionFunction_harmonic : Z_λ(t) = √(2π / (λ t))`,
* `gibbsExpectation_harmonic_pow_even : ⟨x^(2k)⟩_t = (2k-1)‼ / (λ t)^k`,
* `gibbsExpectation_harmonic_pow_odd : ⟨x^(2k+1)⟩_t = 0`.

These are the leading-order Laplace formulas. They follow directly from the
Gaussian moment lemmas in `OneD.GaussianMoments` by setting the inverse
covariance to `λ t`.
-/

open Real MeasureTheory Set
open scoped Nat

namespace Laplace.OneD

/-- The 1D harmonic potential `L(x) = (λ/2) x²`. -/
noncomputable def harmonicPotential (lam : ℝ) : ℝ → ℝ := fun x => lam / 2 * x ^ 2

/-- Helper: rewrite the harmonic Gibbs integrand to the rescaled-Gaussian form. -/
private lemma harmonic_integrand_eq (lam t : ℝ) (phi : ℝ → ℝ) :
    (fun x : ℝ => phi x * Real.exp (-(t * harmonicPotential lam x))) =
      (fun x : ℝ => phi x * Real.exp (-((lam * t) * x ^ 2) / 2)) := by
  ext x
  unfold harmonicPotential
  congr 1; congr 1; ring

/-- Numerator integral for an even power under the harmonic Gibbs measure. -/
theorem harmonic_int_pow_even
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (k : ℕ) :
    ∫ x : ℝ, x ^ (2 * k) * Real.exp (-(t * harmonicPotential lam x)) =
      ((2 * k - 1)‼ : ℝ) * Real.sqrt (2 * π) * (lam * t) ^ (-((k : ℝ) + 1/2)) := by
  rw [harmonic_integrand_eq]
  exact integral_pow_mul_exp_neg_t_sq_half k (mul_pos hlam ht)

/-- Numerator integral for an odd power under the harmonic Gibbs measure
    vanishes. -/
theorem harmonic_int_pow_odd
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (k : ℕ) :
    ∫ x : ℝ, x ^ (2 * k + 1) * Real.exp (-(t * harmonicPotential lam x)) = 0 := by
  rw [harmonic_integrand_eq]
  -- Reduce to standard odd moment by rescaling `x = u / √(λt)`.
  set b := lam * t with hb
  have hbpos : 0 < b := mul_pos hlam ht
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hbpos
  have : (∫ x : ℝ, (x * Real.sqrt b) ^ (2 * k + 1) *
            Real.exp (-(b * (x * Real.sqrt b) ^ 2) / 2)) =
      (Real.sqrt b)⁻¹ * ∫ y : ℝ, y ^ (2 * k + 1) * Real.exp (-(b * y ^ 2) / 2) := by
    have := MeasureTheory.Measure.integral_comp_mul_right
      (fun y : ℝ => y ^ (2 * k + 1) * Real.exp (-(b * y ^ 2) / 2)) (Real.sqrt b)
    rw [abs_of_pos (inv_pos.mpr hsb), smul_eq_mul] at this
    exact this
  -- The substitution gives the desired vanishing — but the simpler approach is
  -- to use the `integral_neg_eq_self` symmetry directly on the rescaled integrand.
  -- We use that approach instead.
  clear this
  set f : ℝ → ℝ := fun x => x ^ (2 * k + 1) * Real.exp (-(b * x ^ 2) / 2) with hf
  have hodd : ∀ x : ℝ, f (-x) = -(f x) := by
    intro x
    simp only [hf]
    rw [Odd.neg_pow ⟨k, rfl⟩, neg_sq]
    ring
  have heq : (∫ x, f x) = -(∫ x, f x) := by
    conv_lhs => rw [← integral_neg_eq_self f volume]
    rw [show (fun x => f (-x)) = (fun x => -(f x)) from funext hodd]
    rw [integral_neg]
  linarith

/-- For `λ, t > 0`, the partition function of the harmonic Gibbs measure is
`Z_λ(t) = √(2π / (λ t))`. -/
theorem partitionFunction_harmonic {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    Laplace.partitionFunction (harmonicPotential lam) t =
      Real.sqrt (2 * π / (lam * t)) := by
  -- `Z = ∫ exp(-t L(x)) = ∫ x^0 · exp(-t L(x))`, then apply `harmonic_int_pow_even` at k=0.
  unfold Laplace.partitionFunction
  rw [show (fun x : ℝ => Real.exp (-(t * harmonicPotential lam x))) =
        (fun x : ℝ => x ^ (2 * 0) * Real.exp (-(t * harmonicPotential lam x))) from by
        ext x; simp]
  rw [harmonic_int_pow_even hlam ht 0]
  -- Goal: `(2*0-1)‼ * √(2π) * (λt)^(-(0 + 1/2)) = √(2π/(λt))`.
  -- `(2*0-1)‼ = 0‼ = 1`.
  simp only [Nat.doubleFactorial, Nat.cast_one, one_mul, Nat.cast_zero, zero_add]
  -- Goal: `√(2π) * (λt)^(-(1/2)) = √(2π/(λt))`.
  rw [show (2 * π / (lam * t) : ℝ) = (2 * π) * (lam * t)⁻¹ by ring,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π)]
  -- Goal: `√(2π) * (λt)^(-(1/2)) = √(2π) * √((λt)⁻¹)`.
  congr 1
  -- Goal: `(λt)^(-(1/2)) = √((λt)⁻¹)`.
  rw [Real.sqrt_eq_rpow,
      show ((lam * t : ℝ)⁻¹ : ℝ) = (lam * t : ℝ) ^ (-1 : ℝ) from
        (Real.rpow_neg_one (lam * t)).symm,
      ← Real.rpow_mul (mul_pos hlam ht).le]
  congr 1
  ring

/-- For `λ, t > 0`, the harmonic Gibbs expectation of `x^(2k)` is
`⟨x^(2k)⟩_t = (2k-1)‼ / (λ t)^k`. -/
theorem gibbsExpectation_harmonic_pow_even
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (k : ℕ) :
    Laplace.gibbsExpectation (harmonicPotential lam) t (fun x => x ^ (2 * k)) =
      ((2 * k - 1)‼ : ℝ) / (lam * t) ^ k := by
  have hlamt : 0 < lam * t := mul_pos hlam ht
  unfold Laplace.gibbsExpectation
  rw [harmonic_int_pow_even hlam ht k, partitionFunction_harmonic hlam ht]
  -- Goal: `((2k-1)‼ * √(2π) * (λt)^(-(↑k + 1/2))) / √(2π/(λt)) = (2k-1)‼ / (λt)^k`.
  -- Rewrite √(2π/(λt)) = √(2π) * (λt)^(-1/2):
  rw [show (2 * π / (lam * t) : ℝ) = (2 * π) * (lam * t)⁻¹ by ring,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π),
      show Real.sqrt ((lam * t : ℝ)⁻¹) = (lam * t : ℝ) ^ (-(1/2 : ℝ)) by
        rw [Real.sqrt_eq_rpow,
            show ((lam * t : ℝ)⁻¹ : ℝ) = (lam * t : ℝ) ^ (-1 : ℝ) from
              (Real.rpow_neg_one _).symm,
            ← Real.rpow_mul hlamt.le]
        congr 1; ring]
  -- Cancel √(2π) and combine powers of (λt).
  have h2pi_ne : Real.sqrt (2 * π) ≠ 0 := by positivity
  rw [show ∀ a b c d : ℝ, (a * b * c) / (b * d) = a * c * (b / b) / d by intros; ring,
      div_self h2pi_ne, mul_one]
  -- Goal: `((2k-1)‼ * (λt)^(-(↑k + 1/2))) / (λt)^(-(1/2)) = (2k-1)‼ / (λt)^k`.
  -- Regroup with `mul_div_assoc`, then combine the two rpow factors.
  rw [mul_div_assoc, ← Real.rpow_sub hlamt,
      show -((k : ℝ) + 1/2) - -(1/2 : ℝ) = -((k : ℝ)) by ring,
      Real.rpow_neg hlamt.le,
      show ((lam * t : ℝ) ^ ((k : ℝ))) = (lam * t : ℝ) ^ k from rpow_natCast _ k]
  ring

/-- For `λ, t > 0`, the harmonic Gibbs expectation of any odd power vanishes. -/
theorem gibbsExpectation_harmonic_pow_odd
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (k : ℕ) :
    Laplace.gibbsExpectation (harmonicPotential lam) t (fun x => x ^ (2 * k + 1)) = 0 := by
  unfold Laplace.gibbsExpectation
  rw [harmonic_int_pow_odd hlam ht k, zero_div]

/-- **Harmonic case of the primer's anharmonic covariance formula**: for the
    purely harmonic potential `L(x) = (λ/2)x²`,

  `Cov_t[x², x] = 0`.

This is consistent with the primer's `Cov_t[x², x] = -2α/(λ³ t²) + o(t⁻²)`
specialized to `α = 0`. The vanishing follows because both `⟨x⟩_t` and `⟨x³⟩_t`
are odd-power expectations, hence zero by symmetry. -/
theorem gibbsCov_harmonic_sq_id_zero
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    Laplace.gibbsCov (harmonicPotential lam) t (fun x => x ^ 2) (fun x => x) = 0 := by
  unfold Laplace.gibbsCov
  -- ⟨x²·x⟩_t - ⟨x²⟩_t · ⟨x⟩_t.
  -- The first term: x²·x = x³ = x^(2·1+1), so the expectation vanishes.
  rw [show (fun x : ℝ => x ^ 2 * x) = (fun x : ℝ => x ^ (2 * 1 + 1)) from by
        ext x; ring]
  rw [gibbsExpectation_harmonic_pow_odd hlam ht 1]
  -- The second term: ⟨x⟩_t = ⟨x^(2·0+1)⟩_t = 0.
  rw [show (fun x : ℝ => x) = (fun x : ℝ => x ^ (2 * 0 + 1)) from by
        ext x; ring]
  rw [gibbsExpectation_harmonic_pow_odd hlam ht 0]
  ring

end Laplace.OneD
