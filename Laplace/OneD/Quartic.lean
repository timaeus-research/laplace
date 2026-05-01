import Laplace.Gibbs
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

/-! ## Integrability -/

/-- Polynomial-times-quartic-Gibbs integrability. For `n : ℕ` and `t > 0`,
`x^n · exp(-(t · x^4 / 24))` is Lebesgue integrable on `ℝ`.

Proof: Gaussian comparison via the square-completion identity
`t·x^4/24 − x² = (t·x² − 12)²/(24t) − 6/t ≥ −6/t`, which gives
`exp(−t·x^4/24) ≤ exp(6/t)·exp(−x²)`. The dominator is integrable by
Mathlib's `integrable_rpow_mul_exp_neg_mul_sq`. -/
theorem quartic_integrable_pow (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-(t * x ^ 4 / 24))) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => x ^ n * Real.exp (-(t * x ^ 4 / 24))) volume :=
    (by fun_prop : Continuous _).aestronglyMeasurable
  have hns : (-1 : ℝ) < (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hdom_raw : Integrable
      (fun x : ℝ => x ^ ((n : ℕ) : ℝ) * Real.exp (-(1 : ℝ) * x ^ 2)) volume :=
    integrable_rpow_mul_exp_neg_mul_sq (by norm_num) hns
  have hdom : Integrable (fun x : ℝ => x ^ n * Real.exp (-(x ^ 2))) volume := by
    have heq : (fun x : ℝ => x ^ ((n : ℕ) : ℝ) * Real.exp (-(1 : ℝ) * x ^ 2)) =
               (fun x : ℝ => x ^ n * Real.exp (-(x ^ 2))) := by
      ext x
      rw [Real.rpow_natCast]
      congr 2
      ring
    rwa [heq] at hdom_raw
  have hbound : ∀ x : ℝ,
      Real.exp (-(t * x ^ 4 / 24)) ≤ Real.exp (6 / t) * Real.exp (-(x ^ 2)) := by
    intro x
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq : (0 : ℝ) ≤ (t * x ^ 2 - 12) ^ 2 := sq_nonneg _
    have h24t : (0 : ℝ) < 24 * t := by positivity
    have key : t * x ^ 4 / 24 - x ^ 2 = (t * x ^ 2 - 12) ^ 2 / (24 * t) - 6 / t := by
      field_simp
      ring
    have hdiv : (0 : ℝ) ≤ (t * x ^ 2 - 12) ^ 2 / (24 * t) := div_nonneg hsq h24t.le
    linarith
  have habs : ∀ x : ℝ,
      ‖x ^ n * Real.exp (-(t * x ^ 4 / 24))‖ ≤
        ‖Real.exp (6 / t) * (x ^ n * Real.exp (-(x ^ 2)))‖ := by
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _),
        abs_of_pos (Real.exp_pos _), abs_pow]
    have hxn : (0 : ℝ) ≤ |x| ^ n := pow_nonneg (abs_nonneg _) n
    nlinarith [hbound x, Real.exp_pos (-(x ^ 2))]
  exact (hdom.const_mul (Real.exp (6 / t))).mono hmeas
    (Filter.Eventually.of_forall habs)

/-- Polynomial-times-quartic-Gibbs integrability, in `quarticPotential` form. -/
theorem quartic_integrable_pow_pot (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-(t * quarticPotential x))) := by
  have h := quartic_integrable_pow n ht
  have heq : (fun x : ℝ => x ^ n * Real.exp (-(t * x ^ 4 / 24))) =
             (fun x : ℝ => x ^ n * Real.exp (-(t * quarticPotential x))) := by
    ext x
    rw [quarticPotential_apply]
    congr 2
    ring
  rwa [heq] at h

/-! ## Half-line moment integrals -/

/-- Half-line moment integral against the pure-quartic Gibbs weight. For `n : ℕ`
and `t > 0`,
`∫ x in Ioi 0, x^{2n} · exp(-(t · x^4 / 24)) dx
  = (1/4) · (24/t)^{(2n+1)/4} · Γ((2n+1)/4)`.

Direct application of Mathlib's `integral_rpow_mul_exp_neg_mul_rpow` with
`p = 4`, `q = 2n`, `b = t/24`. -/
theorem integral_pow_mul_exp_neg_quartic_Ioi (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), x ^ (2 * n) * exp (-(t * x ^ 4 / 24)) =
      (1/4) * (24/t) ^ ((2 * n + 1 : ℝ) / 4) * Real.Gamma ((2 * n + 1 : ℝ) / 4) := by
  have ht24 : (0 : ℝ) < t / 24 := by positivity
  have hq : (-1 : ℝ) < 2 * (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  -- Master lemma: ∫ x^q * exp(-b * x^p) = b^(-(q+1)/p) * (1/p) * Γ((q+1)/p)
  have key := integral_rpow_mul_exp_neg_mul_rpow
    (p := 4) (q := 2 * (n : ℝ)) (b := t / 24)
    (by norm_num) hq ht24
  -- Massage our integrand to rpow form (matching the master lemma)
  have hLHS : (∫ x in Ioi (0 : ℝ), x ^ (2 * n) * exp (-(t * x ^ 4 / 24))) =
      ∫ x in Ioi (0 : ℝ), x ^ (2 * (n : ℝ)) * exp (-(t / 24) * x ^ (4 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [mem_Ioi] at hx
    have h2n : x ^ (2 * (n : ℝ)) = x ^ (2 * n) := by
      rw [show (2 * (n : ℝ) : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring,
          rpow_natCast]
    have h4 : x ^ (4 : ℝ) = x ^ (4 : ℕ) := by
      rw [show ((4 : ℝ) : ℝ) = ((4 : ℕ) : ℝ) by norm_num, rpow_natCast]
    rw [h2n, h4]
    congr 2
    ring
  rw [hLHS, key]
  -- Reduce exponent (2n+1)/4 to canonical form
  have hg : (2 * (n : ℝ) + 1) / 4 = (2 * n + 1 : ℝ) / 4 := by ring
  have hgneg : -(2 * (n : ℝ) + 1) / 4 = -((2 * n + 1 : ℝ) / 4) := by ring
  rw [hg, hgneg]
  -- Convert (t/24)^(-(2n+1)/4) to (24/t)^((2n+1)/4)
  have hinv : (t / 24 : ℝ) ^ (-((2 * n + 1 : ℝ) / 4)) =
      (24 / t : ℝ) ^ ((2 * n + 1 : ℝ) / 4) := by
    rw [show (24 / t : ℝ) = (t / 24)⁻¹ by
          field_simp]
    rw [inv_rpow ht24.le, ← rpow_neg ht24.le]
  rw [hinv]
  ring

/-! ## Full-line moment integrals -/

/-- Even moment of the pure-quartic Gibbs weight on the full real line.
For `n : ℕ` and `t > 0`,
`∫ x : ℝ, x^{2n} · exp(-(t · x^4 / 24)) dx
  = (1/2) · (24/t)^{(2n+1)/4} · Γ((2n+1)/4)`. -/
theorem quartic_moment_even (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, x ^ (2 * n) * exp (-(t * x ^ 4 / 24)) =
      (1/2) * (24/t) ^ ((2 * n + 1 : ℝ) / 4) * Real.Gamma ((2 * n + 1 : ℝ) / 4) := by
  -- Step 1: rewrite the integrand in `|x|`-form (integrand is even).
  have heven : (∫ x : ℝ, x ^ (2 * n) * exp (-(t * x ^ 4 / 24))) =
      ∫ x : ℝ, |x| ^ (2 * n) * exp (-(t * |x| ^ 4 / 24)) := by
    congr 1
    ext x
    rw [show x ^ (2 * n) = |x| ^ (2 * n) from by
          rw [pow_mul x 2 n, ← sq_abs x, ← pow_mul],
        show x ^ 4 = |x| ^ 4 from by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul x 2 2, ← sq_abs x, ← pow_mul]]
  rw [heven]
  -- Step 2: `integral_comp_abs` gives 2 × half-line integral.
  rw [integral_comp_abs (f := fun y => y ^ (2 * n) * exp (-(t * y ^ 4 / 24)))]
  -- Step 3: substitute the half-line value.
  rw [integral_pow_mul_exp_neg_quartic_Ioi n ht]
  ring

/-- Odd moment of the pure-quartic Gibbs weight on the full real line vanishes
by symmetry. For `n : ℕ` and any `t : ℝ`,
`∫ x : ℝ, x^{2n+1} · exp(-(t · x^4 / 24)) dx = 0`. -/
theorem quartic_moment_odd (n : ℕ) (t : ℝ) :
    ∫ x : ℝ, x ^ (2 * n + 1) * exp (-(t * x ^ 4 / 24)) = 0 := by
  set f : ℝ → ℝ := fun x => x ^ (2 * n + 1) * exp (-(t * x ^ 4 / 24)) with hf
  have hodd : ∀ x : ℝ, f (-x) = -(f x) := by
    intro x
    simp only [hf]
    rw [Odd.neg_pow ⟨n, rfl⟩, show ((-x) : ℝ) ^ 4 = x ^ 4 from by ring]
    ring
  have heq : (∫ x, f x) = -(∫ x, f x) := by
    conv_lhs => rw [← integral_neg_eq_self f volume]
    rw [show (fun x => f (-x)) = (fun x => -(f x)) from funext hodd]
    rw [integral_neg]
  linarith

/-- The partition function for the pure-quartic potential.
For `t > 0`,
`Z_t = ∫ exp(-(t · x^4 / 24)) dx = (1/2) · (24/t)^{1/4} · Γ(1/4)`. -/
theorem quartic_partition {t : ℝ} (ht : 0 < t) :
    partitionFunction quarticPotential t =
      (1/2) * (24/t) ^ ((1 : ℝ) / 4) * Real.Gamma ((1 : ℝ) / 4) := by
  unfold partitionFunction
  have step : (∫ x : ℝ, exp (-(t * quarticPotential x))) =
              (∫ x : ℝ, x ^ (2 * 0) * exp (-(t * x ^ 4 / 24))) := by
    congr 1
    ext x
    rw [Nat.mul_zero, pow_zero, one_mul, quarticPotential_apply]
    congr 1
    ring
  rw [step, quartic_moment_even 0 ht]
  norm_num

/-- The partition function for the pure-quartic potential is positive. -/
theorem quartic_partition_pos {t : ℝ} (ht : 0 < t) :
    0 < partitionFunction quarticPotential t := by
  rw [quartic_partition ht]
  have h24t : (0 : ℝ) < 24 / t := by positivity
  have hpow : 0 < (24 / t : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos h24t _
  have hg : 0 < Real.Gamma ((1 : ℝ) / 4) := Real.Gamma_pos_of_pos (by norm_num)
  positivity

/-! ## Expected values -/

/-- Even-power expected value against the pure-quartic Gibbs measure.
For `n : ℕ` and `t > 0`,
`⟨x^{2n}⟩_t = (24/t)^{n/2} · Γ((2n+1)/4) / Γ(1/4)`. -/
theorem quartic_expected_value_even (n : ℕ) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation quarticPotential t (fun x => x ^ (2 * n)) =
      (24/t) ^ ((n : ℝ) / 2) * Real.Gamma ((2 * n + 1 : ℝ) / 4) / Real.Gamma ((1 : ℝ) / 4) := by
  unfold gibbsExpectation
  have hnum : (∫ x : ℝ, x ^ (2 * n) * exp (-(t * quarticPotential x))) =
              (∫ x : ℝ, x ^ (2 * n) * exp (-(t * x ^ 4 / 24))) := by
    congr 1
    ext x
    rw [quarticPotential_apply]
    congr 2
    ring
  rw [hnum, quartic_moment_even n ht, quartic_partition ht]
  have h24 : (0 : ℝ) < 24 / t := by positivity
  have hg : Real.Gamma ((1 : ℝ) / 4) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by norm_num))
  have h24pow : (24 / t : ℝ) ^ ((1 : ℝ) / 4) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos h24 _)
  -- Split (2n+1)/4 = n/2 + 1/4 to expose the cancelling factor (24/t)^(1/4).
  rw [show ((2 * n + 1 : ℝ) / 4) = ((n : ℝ) / 2) + ((1 : ℝ) / 4) from by ring,
      Real.rpow_add h24 _ _]
  field_simp

/-- Odd-power expected value against the pure-quartic Gibbs measure vanishes by
symmetry. For any `n : ℕ` and any `t : ℝ`, `⟨x^{2n+1}⟩_t = 0`. (The hypothesis
`0 < t` is unnecessary because the moment is zero by parity at the integral
level — the partition function never enters.) -/
theorem quartic_expected_value_odd (n : ℕ) (t : ℝ) :
    gibbsExpectation quarticPotential t (fun x => x ^ (2 * n + 1)) = 0 := by
  unfold gibbsExpectation
  have hnum : (∫ x : ℝ, x ^ (2 * n + 1) * exp (-(t * quarticPotential x))) = 0 := by
    have heq : (∫ x : ℝ, x ^ (2 * n + 1) * exp (-(t * quarticPotential x))) =
               (∫ x : ℝ, x ^ (2 * n + 1) * exp (-(t * x ^ 4 / 24))) := by
      congr 1
      ext x
      rw [quarticPotential_apply]
      congr 2
      ring
    rw [heq, quartic_moment_odd n t]
  rw [hnum, zero_div]

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
