import Laplace.Gibbs
import Laplace.OneD.MonomialPotential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Pure quartic 1D Gibbs moments

For the centred quartic potential `L(x) = x^4 / 24`, this file establishes
exact closed forms for the partition function and even/odd moments of the 1D
Gibbs measure `exp(-t · L(x)) dx`, and the covariance of affine observables.

This is the first step into a genuinely degenerate posterior: `L''(0) = 0`,
so the Hessian-based Laplace machinery from the rest of this repository
does not apply. Instead, the substitution `u = (t/24)^{1/4} · x` reduces
every moment integral exactly to a `Γ`-function value.

## Headline results

* `quartic_partition` :
  `∫ exp(-(t · x^4/24)) dx = (1/2) · (24/t)^{1/4} · Γ(1/4)`.
* `quartic_moment_even` :
  `∫ x^{2n} · exp(-(t · x^4/24)) dx = (1/2) · (24/t)^{(2n+1)/4} · Γ((2n+1)/4)`.
* `quartic_moment_odd` :
  `∫ x^{2n+1} · exp(-(t · x^4/24)) dx = 0`.
* `quartic_expected_value_even` :
  `⟨x^{2n}⟩_t = (24/t)^{n/2} · Γ((2n+1)/4) / Γ(1/4)`.
* `quartic_expected_value_odd` :
  `⟨x^{2n+1}⟩_t = 0`.
* `quartic_cov_affine` :
  `Cov_t[a x + c, b x + d] = a b · √(24/t) · Γ(3/4) / Γ(1/4)`.

## Strategy

Apply `integral_rpow_mul_exp_neg_mul_rpow` with `p = 4`, `b = t/24`,
`q = 2n` to get
`∫ x in Ioi 0, x^{2n} · exp(-(t/24) · x^4) = (t/24)^{-(2n+1)/4} · (1/4) · Γ((2n+1)/4)`,
then double by `integral_comp_abs` for the full-line integral. Odd moments
vanish by `integral_comp_neg`. The expected values and covariance follow
algebraically.
-/

open Real MeasureTheory Set

namespace Laplace.OneD

/-- The 1D pure quartic potential `L(x) = x^4 / 24`. -/
noncomputable def quarticPotential : ℝ → ℝ := fun x => x ^ 4 / 24

@[simp] lemma quarticPotential_apply (x : ℝ) :
    quarticPotential x = x ^ 4 / 24 := rfl

/-- The quartic potential is the `k = 2` specialisation of the generic
even-monomial template. -/
lemma quarticPotential_eq_kthPotential :
    quarticPotential = kthPotential 2 := by
  funext x; simp [quarticPotential, kthPotential]; norm_num

/-! ## Integrability -/

/-- Polynomial-times-quartic-Gibbs integrability.
$k = 2$ specialisation of `kth_integrable_pow`. -/
theorem quartic_integrable_pow (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-(t * x ^ 4 / 24))) := by
  have h := kth_integrable_pow (k := 2) (by norm_num) n ht
  convert h using 4 <;> norm_num

/-- Polynomial-times-quartic-Gibbs integrability, in `quarticPotential` form.
$k = 2$ specialisation of `kth_integrable_pow_pot`. -/
theorem quartic_integrable_pow_pot (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-(t * quarticPotential x))) := by
  rw [quarticPotential_eq_kthPotential]
  exact kth_integrable_pow_pot (k := 2) (by norm_num) n ht

/-! ## Half-line moment integrals -/

/-- Half-line moment integral against the pure-quartic Gibbs weight.
$k = 2$ specialisation of `integral_pow_mul_exp_neg_kth_Ioi`. -/
theorem integral_pow_mul_exp_neg_quartic_Ioi (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), x ^ (2 * n) * exp (-(t * x ^ 4 / 24)) =
      (1/4) * (24/t) ^ ((2 * n + 1 : ℝ) / 4) * Real.Gamma ((2 * n + 1 : ℝ) / 4) := by
  have h := integral_pow_mul_exp_neg_kth_Ioi (k := 2) (by norm_num) n ht
  convert h using 3

/-! ## Full-line moment integrals -/

/-- Even moment of the pure-quartic Gibbs weight on the full real line.
$k = 2$ specialisation of `kth_moment_even`. -/
theorem quartic_moment_even (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, x ^ (2 * n) * exp (-(t * x ^ 4 / 24)) =
      (1/2) * (24/t) ^ ((2 * n + 1 : ℝ) / 4) * Real.Gamma ((2 * n + 1 : ℝ) / 4) := by
  have h := kth_moment_even (k := 2) (by norm_num) n ht
  convert h using 3

/-- Odd moment of the pure-quartic Gibbs weight on the full real line vanishes
by symmetry. $k = 2$ specialisation of `kth_moment_odd`. -/
theorem quartic_moment_odd (n : ℕ) (t : ℝ) :
    ∫ x : ℝ, x ^ (2 * n + 1) * exp (-(t * x ^ 4 / 24)) = 0 := by
  have h := kth_moment_odd 2 n t
  convert h using 3

/-- The partition function for the pure-quartic potential.
$k = 2$ specialisation of `partitionFunction_kthPotential` via the
`quarticPotential = kthPotential 2` bridge. -/
theorem quartic_partition {t : ℝ} (ht : 0 < t) :
    partitionFunction quarticPotential t =
      (1/2) * (24/t) ^ ((1 : ℝ) / 4) * Real.Gamma ((1 : ℝ) / 4) := by
  rw [quarticPotential_eq_kthPotential]
  have h := partitionFunction_kthPotential (k := 2) (by norm_num) ht
  convert h using 3

/-- The partition function for the pure-quartic potential is positive.
$k = 2$ specialisation of `partitionFunction_kthPotential_pos`. -/
theorem quartic_partition_pos {t : ℝ} (ht : 0 < t) :
    0 < partitionFunction quarticPotential t := by
  rw [quarticPotential_eq_kthPotential]
  exact partitionFunction_kthPotential_pos (k := 2) (by norm_num) ht

/-! ## Expected values -/

/-- Even-power expected value against the pure-quartic Gibbs measure.
$k = 2$ specialisation of `gibbsExpectation_kthPotential_even`. -/
theorem quartic_expected_value_even (n : ℕ) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation quarticPotential t (fun x => x ^ (2 * n)) =
      (24/t) ^ ((n : ℝ) / 2) * Real.Gamma ((2 * n + 1 : ℝ) / 4) / Real.Gamma ((1 : ℝ) / 4) := by
  rw [quarticPotential_eq_kthPotential]
  have h := gibbsExpectation_kthPotential_even (k := 2) (by norm_num) n ht
  convert h using 3

/-- Odd-power expected value against the pure-quartic Gibbs measure vanishes by
symmetry. $k = 2$ specialisation of `gibbsExpectation_kthPotential_odd`. -/
theorem quartic_expected_value_odd (n : ℕ) (t : ℝ) :
    gibbsExpectation quarticPotential t (fun x => x ^ (2 * n + 1)) = 0 := by
  rw [quarticPotential_eq_kthPotential]
  exact gibbsExpectation_kthPotential_odd 2 n t

/-- Specialisation of `quartic_expected_value_even` to `n = 1`:
`⟨x^2⟩_t = √(24/t) · Γ(3/4) / Γ(1/4)`. -/
theorem quartic_expected_value_sq {t : ℝ} (ht : 0 < t) :
    gibbsExpectation quarticPotential t (fun x => x ^ 2) =
      Real.sqrt (24 / t) * Real.Gamma ((3 : ℝ) / 4) / Real.Gamma ((1 : ℝ) / 4) := by
  have h := quartic_expected_value_even 1 ht
  -- Normalise casts and arithmetic
  push_cast at h
  rw [show ((2 * 1 + 1 : ℝ) / 4) = ((3 : ℝ) / 4) from by norm_num,
      ← Real.sqrt_eq_rpow] at h
  -- LHS uses `x^(2*1)`, defEq to `x^2`
  exact h

/-- Specialisation of `quartic_expected_value_odd` to `n = 0`:
`⟨x⟩_t = 0`. -/
theorem quartic_expected_value_lin (t : ℝ) :
    gibbsExpectation quarticPotential t (fun x => x) = 0 := by
  have h := quartic_expected_value_odd 0 t
  simpa using h

/-! ## Covariance of affine observables -/

/-- Covariance of two affine observables against the pure-quartic Gibbs measure.
For `t > 0` and any `a b c d : ℝ`,
`Cov_t[a x + c, b x + d] = a b · √(24/t) · Γ(3/4) / Γ(1/4)`.

This is the headline degenerate-case analogue of
`gibbsCov_first_order_rate_sharp`: the covariance decays as `t^{-1/2}` (rather
than the nondegenerate `t^{-1}`), and the leading coefficient is given by an
explicit ratio of Γ-values. -/
theorem quartic_cov_affine {t : ℝ} (ht : 0 < t) (a b c d : ℝ) :
    gibbsCov quarticPotential t (fun x => a * x + c) (fun x => b * x + d) =
      a * b * Real.sqrt (24 / t) * Real.Gamma ((3 : ℝ) / 4) / Real.Gamma ((1 : ℝ) / 4) := by
  have hZpos := quartic_partition_pos ht
  have hZne : partitionFunction quarticPotential t ≠ 0 := ne_of_gt hZpos
  -- Integrability of `1, x, x²` against the Gibbs weight.
  have hI0 : Integrable (fun x : ℝ => Real.exp (-(t * quarticPotential x))) := by
    have h := quartic_integrable_pow_pot 0 ht
    have heq : (fun x : ℝ => x ^ 0 * Real.exp (-(t * quarticPotential x))) =
               (fun x : ℝ => Real.exp (-(t * quarticPotential x))) := by ext; simp
    rwa [heq] at h
  have hI1 : Integrable (fun x : ℝ => x * Real.exp (-(t * quarticPotential x))) := by
    have h := quartic_integrable_pow_pot 1 ht
    have heq : (fun x : ℝ => x ^ 1 * Real.exp (-(t * quarticPotential x))) =
               (fun x : ℝ => x * Real.exp (-(t * quarticPotential x))) := by
      ext; rw [pow_one]
    rwa [heq] at h
  have hI2 := quartic_integrable_pow_pot 2 ht
  -- Linearity for affine combinations: ⟨px + q⟩_t = p ⟨x⟩_t + q.
  have hphi_aff : ∀ p q : ℝ,
      gibbsExpectation quarticPotential t (fun x => p * x + q) =
        p * gibbsExpectation quarticPotential t (fun x => x) + q := by
    intro p q
    unfold gibbsExpectation
    rw [show (fun x : ℝ => (p * x + q) * Real.exp (-(t * quarticPotential x))) =
           (fun x : ℝ => p * (x * Real.exp (-(t * quarticPotential x))) +
                     q * Real.exp (-(t * quarticPotential x))) from by funext x; ring]
    rw [MeasureTheory.integral_add (hI1.const_mul p) (hI0.const_mul q)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hZdef : (∫ x : ℝ, Real.exp (-(t * quarticPotential x))) =
                 partitionFunction quarticPotential t := rfl
    rw [hZdef]
    field_simp
  -- Quadratic expansion: ⟨(ax+c)(bx+d)⟩_t = ab⟨x²⟩_t + (ad+bc)⟨x⟩_t + cd.
  have hphipsi :
      gibbsExpectation quarticPotential t (fun x => (a * x + c) * (b * x + d)) =
        a * b * gibbsExpectation quarticPotential t (fun x => x ^ 2) +
        (a * d + b * c) * gibbsExpectation quarticPotential t (fun x => x) +
        c * d := by
    unfold gibbsExpectation
    rw [show (fun x : ℝ =>
              (a * x + c) * (b * x + d) * Real.exp (-(t * quarticPotential x))) =
           (fun x : ℝ =>
              (a * b) * (x ^ 2 * Real.exp (-(t * quarticPotential x))) +
              (a * d + b * c) * (x * Real.exp (-(t * quarticPotential x))) +
              (c * d) * Real.exp (-(t * quarticPotential x))) from by funext x; ring]
    -- Pi.add workaround (see laplace `CLAUDE.md`): build a *single-lambda*
    -- integrability witness so the integral_add pattern unifies under beta.
    have hI12 : Integrable
        (fun x : ℝ =>
            a * b * (x ^ 2 * Real.exp (-(t * quarticPotential x))) +
            (a * d + b * c) * (x * Real.exp (-(t * quarticPotential x))))
        volume := (hI2.const_mul (a * b)).add (hI1.const_mul (a * d + b * c))
    rw [MeasureTheory.integral_add hI12 (hI0.const_mul (c * d))]
    rw [MeasureTheory.integral_add (hI2.const_mul (a * b))
          (hI1.const_mul (a * d + b * c))]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
    have hZdef : (∫ x : ℝ, Real.exp (-(t * quarticPotential x))) =
                 partitionFunction quarticPotential t := rfl
    rw [hZdef]
    field_simp
  -- Combine: Cov = ⟨φψ⟩ - ⟨φ⟩⟨ψ⟩ = (ab⟨x²⟩ + cd) - cd = ab⟨x²⟩.
  unfold gibbsCov
  rw [hphipsi, hphi_aff a c, hphi_aff b d,
      quartic_expected_value_lin t, quartic_expected_value_sq ht]
  ring

end Laplace.OneD
