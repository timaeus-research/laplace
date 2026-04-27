import Laplace.OneD.TailBound
import Laplace.OneD.Harmonic

/-!
# Harmonic Laplace localisation

We package the tail bounds in `Laplace.OneD.TailBound` into "localisation"
lemmas: for the harmonic potential `L_λ(x) = (λ/2)x²` and any `δ > 0`, the
contribution to `∫ x^n · exp(-t L_λ(x)) dx` from outside `(-δ, δ)` is
exponentially small in `t`.

Specifically, for the integrals we need in Stage 2 (the anharmonic
covariance formula `Cov_t[x², x] = -2α/(λ³t²) + o(t⁻²)`), we provide:

* `harmonic_tail_zeroth_Ioi`: the tail of the partition-function integrand.
* `harmonic_tail_first_Ioi`: the tail of `x · exp(-t L_λ(x))`.
* `harmonic_tail_second_Ioi`: the tail of `x² · exp(-t L_λ(x))`.

Each bound has the form `≤ C(δ, λ, t) · exp(-(λ t) δ² / 2)`, with
`C(δ, λ, t)` a polynomial in `1/(λ t)`. This is `o(t^{-N})` for every `N`.
-/

open Real MeasureTheory Set
open scoped Nat

namespace Laplace.OneD

/-- **Zeroth-moment tail** under the harmonic Gibbs measure: for `λ, t, δ > 0`,

  `∫_{Ioi δ} exp(-t L_λ(x)) dx ≤ exp(-(λ t) δ² / 2) / ((λ t) δ)`. -/
theorem harmonic_tail_zeroth_Ioi {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t)
    {delta : ℝ} (hδ : 0 < delta) :
    ∫ x in Ioi delta, Real.exp (-(t * harmonicPotential lam x)) ≤
      Real.exp (-((lam * t) * delta ^ 2) / 2) / ((lam * t) * delta) := by
  -- Rewrite the integrand `exp(-(t · (λ/2)x²))` as `exp(-(λt) x² / 2)`.
  have hint_eq : ∫ x in Ioi delta, Real.exp (-(t * harmonicPotential lam x)) =
      ∫ x in Ioi delta, Real.exp (-((lam * t) * x ^ 2) / 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    unfold harmonicPotential
    congr 1; ring
  rw [hint_eq]
  exact gaussian_tail_bound_rescaled_Ioi hδ (mul_pos hlam ht)

/-- **First-moment tail** under the harmonic Gibbs measure: for `λ, t > 0`
and any `δ`,

  `∫_{Ioi δ} x · exp(-t L_λ(x)) dx = exp(-(λ t) δ² / 2) / (λ t)`. -/
theorem harmonic_tail_first_Ioi {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t)
    (delta : ℝ) :
    ∫ x in Ioi delta, x * Real.exp (-(t * harmonicPotential lam x)) =
      Real.exp (-((lam * t) * delta ^ 2) / 2) / (lam * t) := by
  have hint_eq : ∫ x in Ioi delta, x * Real.exp (-(t * harmonicPotential lam x)) =
      ∫ x in Ioi delta, x * Real.exp (-((lam * t) * x ^ 2) / 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    unfold harmonicPotential
    congr 1; congr 1; ring
  rw [hint_eq]
  exact integral_Ioi_id_mul_exp_neg_b_sq_half (mul_pos hlam ht) delta

/-- **Second-moment tail** under the harmonic Gibbs measure: for `λ, t, δ > 0`,

  `∫_{Ioi δ} x² · exp(-t L_λ(x)) dx
    ≤ δ · exp(-(λ t) δ² / 2) / (λ t)
        + exp(-(λ t) δ² / 2) / (δ · (λ t)²)`.

The two terms come from the boundary contribution and the integrated tail
in the second-moment closed form. -/
theorem harmonic_tail_second_Ioi {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t)
    {delta : ℝ} (hδ : 0 < delta) :
    ∫ x in Ioi delta, x ^ 2 * Real.exp (-(t * harmonicPotential lam x)) ≤
      delta * Real.exp (-((lam * t) * delta ^ 2) / 2) / (lam * t)
        + Real.exp (-((lam * t) * delta ^ 2) / 2) / (delta * (lam * t) ^ 2) := by
  have hlamt : 0 < lam * t := mul_pos hlam ht
  have hint_eq : ∫ x in Ioi delta, x ^ 2 * Real.exp (-(t * harmonicPotential lam x)) =
      ∫ x in Ioi delta, x ^ 2 * Real.exp (-((lam * t) * x ^ 2) / 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    unfold harmonicPotential
    congr 1; congr 1; ring
  rw [hint_eq, integral_Ioi_sq_mul_exp_neg_b_sq_half hlamt delta]
  -- Goal: δ · exp(-(λt)δ²/2)/(λt) + (1/(λt)) · ∫_{Ioi δ} exp(-(λt)x²/2)
  --     ≤ δ · exp(-(λt)δ²/2)/(λt) + exp(-(λt)δ²/2)/(δ · (λt)²)
  have htail := gaussian_tail_bound_rescaled_Ioi hδ hlamt
  -- htail : ∫_{Ioi δ} exp(-(λt)x²/2) ≤ exp(-(λt)δ²/2)/((λt) · δ)
  have h1 : (1 / (lam * t)) * ∫ x in Ioi delta, Real.exp (-((lam * t) * x ^ 2) / 2) ≤
      (1 / (lam * t)) * (Real.exp (-((lam * t) * delta ^ 2) / 2) / ((lam * t) * delta)) := by
    apply mul_le_mul_of_nonneg_left htail
    apply div_nonneg (by norm_num) hlamt.le
  -- Now bound the right side and clean up the algebra.
  calc delta * Real.exp (-((lam * t) * delta ^ 2) / 2) / (lam * t)
        + 1 / (lam * t) * ∫ x in Ioi delta, Real.exp (-((lam * t) * x ^ 2) / 2)
      ≤ delta * Real.exp (-((lam * t) * delta ^ 2) / 2) / (lam * t)
          + (1 / (lam * t))
            * (Real.exp (-((lam * t) * delta ^ 2) / 2) / ((lam * t) * delta)) := by
          linarith
    _ = delta * Real.exp (-((lam * t) * delta ^ 2) / 2) / (lam * t)
          + Real.exp (-((lam * t) * delta ^ 2) / 2) / (delta * (lam * t) ^ 2) := by
          have hδ_ne : delta ≠ 0 := hδ.ne'
          have hlamt_ne : (lam * t : ℝ) ≠ 0 := hlamt.ne'
          field_simp

/-! ## Two-sided localisation -/

/-- Even-function symmetry on the half-lines for the harmonic Gibbs integrand. -/
private lemma harmonic_integrand_even (lam t : ℝ) (n : ℕ) (M : ℝ) :
    ∫ x in Iio (-M), x ^ (2 * n) * Real.exp (-(t * harmonicPotential lam x)) =
      ∫ x in Ioi M, x ^ (2 * n) * Real.exp (-(t * harmonicPotential lam x)) := by
  -- Substitute `x ↦ -x`: maps `Iio (-M)` to `Ioi M`. The integrand is even.
  rw [← integral_Iic_eq_integral_Iio]
  have hsub := integral_comp_neg_Iic (-M)
    (fun y : ℝ => y ^ (2 * n) * Real.exp (-(t * harmonicPotential lam y)))
  rw [show (-(-M) : ℝ) = M from neg_neg M] at hsub
  rw [show (fun x : ℝ =>
        (-x) ^ (2 * n) * Real.exp (-(t * harmonicPotential lam (-x)))) =
        (fun x : ℝ =>
        x ^ (2 * n) * Real.exp (-(t * harmonicPotential lam x))) from by
        ext x
        congr 1
        · rw [show (-x) ^ (2 * n) = ((-1) ^ (2 * n)) * x ^ (2 * n) from by
                rw [neg_eq_neg_one_mul, mul_pow]]
          rw [pow_mul, neg_one_sq]; ring
        · congr 1; congr 1
          unfold harmonicPotential
          rw [show (-x : ℝ) ^ 2 = x ^ 2 from neg_pow_two x]] at hsub
  exact hsub

/-- **Zeroth-moment two-sided tail** under the harmonic Gibbs measure: for `λ, t, δ > 0`,

  `∫_{|x| > δ} exp(-t L_λ(x)) dx ≤ 2 · exp(-(λ t) δ² / 2) / ((λ t) δ)`. -/
theorem harmonic_tail_zeroth_compl {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t)
    {delta : ℝ} (hδ : 0 < delta) :
    (∫ x in Iio (-delta), Real.exp (-(t * harmonicPotential lam x))) +
        ∫ x in Ioi delta, Real.exp (-(t * harmonicPotential lam x)) ≤
      2 * Real.exp (-((lam * t) * delta ^ 2) / 2) / ((lam * t) * delta) := by
  have hsymm := harmonic_integrand_even lam t 0 delta
  simp only [Nat.mul_zero, pow_zero, one_mul] at hsymm
  rw [hsymm]
  rw [show (∫ x in Ioi delta, Real.exp (-(t * harmonicPotential lam x))) +
        ∫ x in Ioi delta, Real.exp (-(t * harmonicPotential lam x)) =
      2 * ∫ x in Ioi delta, Real.exp (-(t * harmonicPotential lam x)) by ring]
  rw [show (2 * Real.exp (-((lam * t) * delta ^ 2) / 2) / ((lam * t) * delta) : ℝ) =
        2 * (Real.exp (-((lam * t) * delta ^ 2) / 2) / ((lam * t) * delta)) by ring]
  exact mul_le_mul_of_nonneg_left
    (harmonic_tail_zeroth_Ioi hlam ht hδ) (by norm_num)

/-- **Second-moment two-sided tail** under the harmonic Gibbs measure: for `λ, t, δ > 0`,

  `∫_{|x| > δ} x² · exp(-t L_λ(x)) dx
    ≤ 2 (δ / (λ t) + 1 / (δ · (λ t)²)) · exp(-(λ t) δ² / 2)`. -/
theorem harmonic_tail_second_compl {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t)
    {delta : ℝ} (hδ : 0 < delta) :
    (∫ x in Iio (-delta), x ^ 2 * Real.exp (-(t * harmonicPotential lam x))) +
        ∫ x in Ioi delta, x ^ 2 * Real.exp (-(t * harmonicPotential lam x)) ≤
      2 * (delta * Real.exp (-((lam * t) * delta ^ 2) / 2) / (lam * t)
        + Real.exp (-((lam * t) * delta ^ 2) / 2) / (delta * (lam * t) ^ 2)) := by
  have hsymm := harmonic_integrand_even lam t 1 delta
  simp only [Nat.mul_one] at hsymm
  rw [hsymm]
  rw [show (∫ x in Ioi delta, x ^ 2 * Real.exp (-(t * harmonicPotential lam x))) +
        ∫ x in Ioi delta, x ^ 2 * Real.exp (-(t * harmonicPotential lam x)) =
      2 * ∫ x in Ioi delta, x ^ 2 * Real.exp (-(t * harmonicPotential lam x)) by ring]
  exact mul_le_mul_of_nonneg_left
    (harmonic_tail_second_Ioi hlam ht hδ) (by norm_num)

end Laplace.OneD
