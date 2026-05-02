import Laplace.Gibbs
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Pure sextic 1D Gibbs moments

For the centred sextic potential `L(x) = x^6 / 720`, this file establishes
exact closed forms for the partition function and even/odd moments of the 1D
Gibbs measure `exp(-t · L(x)) dx`, and the covariance of affine observables.

Like the quartic case, this is a genuinely degenerate posterior: `L''(0) = 0`,
so the Hessian-based Laplace machinery from the rest of this repository does
not apply. The substitution `u = (t/720)^{1/6} · x` reduces every moment
integral exactly to a `Γ`-function value, with rate `t^{-1/3}` (compared
to the quartic's `t^{-1/2}` and the harmonic's `t^{-1}`).

## Headline results

* `sextic_partition` :
  `∫ exp(-(t · x^6/720)) dx = (1/3) · (720/t)^{1/6} · Γ(1/6)`.
* `sextic_moment_even` :
  `∫ x^{2n} · exp(-(t · x^6/720)) dx = (1/3) · (720/t)^{(2n+1)/6} · Γ((2n+1)/6)`.
* `sextic_moment_odd` :
  `∫ x^{2n+1} · exp(-(t · x^6/720)) dx = 0`.
* `sextic_expected_value_even` :
  `⟨x^{2n}⟩_t = (720/t)^{n/3} · Γ((2n+1)/6) / Γ(1/6)`.
* `sextic_expected_value_odd` :
  `⟨x^{2n+1}⟩_t = 0`.
* `sextic_cov_affine` :
  `Cov_t[a x + c, b x + d] = a b · (720/t)^{1/3} · Γ(1/2) / Γ(1/6)`.

## Strategy

The atomic kernel is the half-line moment `integral_pow_mul_exp_neg_sextic_Ioi`,
stated for *arbitrary* `m : ℕ` (not just `2n`). It applies
`integral_rpow_mul_exp_neg_mul_rpow` with `p = 6`, `b = t/720`, `q = m` to get
`∫ x in Ioi 0, x^m · exp(-(t/720) · x^6) = (1/6) · (720/t)^{(m+1)/6} · Γ((m+1)/6)`.
Even full-line moments use `integral_comp_abs` to double; odd moments vanish
by parity (`(-x)^6 = x^6`).

Integrability uses the slick polynomial bound `x^2 ≤ 1 + x^6` (proved
piecewise: trivial on `|x| ≤ 1`; for `|x| ≥ 1`, multiply through by `x^4 ≥ 1`).
This gives `t · x^6 / 720 ≥ (t/720) · x^2 - t/720`, hence
`exp(-t·x^6/720) ≤ exp(t/720) · exp(-(t/720)·x^2)` against a Gaussian dominator.
-/

open Real MeasureTheory Set

namespace Laplace.OneD

/-- The 1D pure sextic potential `L(x) = x^6 / 720`. -/
noncomputable def sexticPotential : ℝ → ℝ := fun x => x ^ 6 / 720

@[simp] lemma sexticPotential_apply (x : ℝ) :
    sexticPotential x = x ^ 6 / 720 := rfl

/-! ## Integrability -/

/-- The polynomial bound `x^2 ≤ 1 + x^6`, proved piecewise. -/
private lemma sq_le_one_add_pow_six (x : ℝ) : x ^ 2 ≤ 1 + x ^ 6 := by
  rcases le_total (x ^ 2) 1 with hx | hx
  · -- `|x| ≤ 1`: `x² ≤ 1 ≤ 1 + x^6`
    have h6 : (0 : ℝ) ≤ x ^ 6 := by positivity
    linarith
  · -- `|x| ≥ 1`: `x^4 ≥ 1`, hence `x² ≤ x^6 ≤ 1 + x^6`
    have h4 : (1 : ℝ) ≤ x ^ 4 := by nlinarith [sq_nonneg x]
    have h26 : x ^ 2 ≤ x ^ 6 := by
      have hsq : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
      have h6eq : x ^ 6 = x ^ 2 * x ^ 4 := by ring
      nlinarith
    linarith

/-- Polynomial-times-sextic-Gibbs integrability. For `n : ℕ` and `t > 0`,
`x^n · exp(-(t · x^6 / 720))` is Lebesgue integrable on `ℝ`.

Proof: Gaussian comparison via `x² ≤ 1 + x^6`, which gives
`t·x^6/720 ≥ (t/720)·x² - t/720`, hence
`exp(-t·x^6/720) ≤ exp(t/720)·exp(-(t/720)·x²)`. The dominator is integrable
by Mathlib's `integrable_rpow_mul_exp_neg_mul_sq` with `b = t/720`. -/
theorem sextic_integrable_pow (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-(t * x ^ 6 / 720))) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => x ^ n * Real.exp (-(t * x ^ 6 / 720))) volume :=
    (by fun_prop : Continuous _).aestronglyMeasurable
  have ht720 : (0 : ℝ) < t / 720 := by positivity
  have hns : (-1 : ℝ) < (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hdom_raw : Integrable
      (fun x : ℝ => x ^ ((n : ℕ) : ℝ) * Real.exp (-(t / 720) * x ^ 2)) volume :=
    integrable_rpow_mul_exp_neg_mul_sq ht720 hns
  have hdom : Integrable
      (fun x : ℝ => x ^ n * Real.exp (-((t / 720) * x ^ 2))) volume := by
    have heq : (fun x : ℝ => x ^ ((n : ℕ) : ℝ) * Real.exp (-(t / 720) * x ^ 2)) =
               (fun x : ℝ => x ^ n * Real.exp (-((t / 720) * x ^ 2))) := by
      ext x
      rw [Real.rpow_natCast]
      congr 2
      ring
    rwa [heq] at hdom_raw
  have hbound : ∀ x : ℝ,
      Real.exp (-(t * x ^ 6 / 720)) ≤
        Real.exp (t / 720) * Real.exp (-((t / 720) * x ^ 2)) := by
    intro x
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hkey : x ^ 2 ≤ 1 + x ^ 6 := sq_le_one_add_pow_six x
    have hprod : (0 : ℝ) ≤ (t / 720) * (1 + x ^ 6 - x ^ 2) :=
      mul_nonneg ht720.le (by linarith)
    nlinarith
  have habs : ∀ x : ℝ,
      ‖x ^ n * Real.exp (-(t * x ^ 6 / 720))‖ ≤
        ‖Real.exp (t / 720) * (x ^ n * Real.exp (-((t / 720) * x ^ 2)))‖ := by
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _),
        abs_of_pos (Real.exp_pos _), abs_pow]
    have hxn : (0 : ℝ) ≤ |x| ^ n := pow_nonneg (abs_nonneg _) n
    nlinarith [hbound x, Real.exp_pos (-((t / 720) * x ^ 2))]
  exact (hdom.const_mul (Real.exp (t / 720))).mono hmeas
    (Filter.Eventually.of_forall habs)

/-- Polynomial-times-sextic-Gibbs integrability, in `sexticPotential` form. -/
theorem sextic_integrable_pow_pot (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-(t * sexticPotential x))) := by
  have h := sextic_integrable_pow n ht
  have heq : (fun x : ℝ => x ^ n * Real.exp (-(t * x ^ 6 / 720))) =
             (fun x : ℝ => x ^ n * Real.exp (-(t * sexticPotential x))) := by
    ext x
    rw [sexticPotential_apply]
    congr 2
    ring
  rwa [heq] at h

/-! ## Half-line moment integrals -/

/-- Half-line moment integral against the pure-sextic Gibbs weight. For `m : ℕ`
and `t > 0`,
`∫ x in Ioi 0, x^m · exp(-(t · x^6 / 720)) dx
  = (1/6) · (720/t)^{(m+1)/6} · Γ((m+1)/6)`.

Direct application of Mathlib's `integral_rpow_mul_exp_neg_mul_rpow` with
`p = 6`, `q = m`, `b = t/720`. Stated for arbitrary `m` (not only `2n`) so that
both even and odd full-line moment formulas can be derived from it. -/
theorem integral_pow_mul_exp_neg_sextic_Ioi (m : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), x ^ m * exp (-(t * x ^ 6 / 720)) =
      (1/6) * (720/t) ^ ((m + 1 : ℝ) / 6) * Real.Gamma ((m + 1 : ℝ) / 6) := by
  have ht720 : (0 : ℝ) < t / 720 := by positivity
  have hq : (-1 : ℝ) < (m : ℝ) := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  -- Master lemma: ∫ x^q * exp(-b * x^p) = b^(-(q+1)/p) * (1/p) * Γ((q+1)/p)
  have key := integral_rpow_mul_exp_neg_mul_rpow
    (p := 6) (q := (m : ℝ)) (b := t / 720)
    (by norm_num) hq ht720
  -- Massage our integrand to rpow form (matching the master lemma)
  have hLHS : (∫ x in Ioi (0 : ℝ), x ^ m * exp (-(t * x ^ 6 / 720))) =
      ∫ x in Ioi (0 : ℝ), x ^ ((m : ℝ)) * exp (-(t / 720) * x ^ (6 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [mem_Ioi] at hx
    have hm : x ^ ((m : ℝ)) = x ^ m := by rw [rpow_natCast]
    have h6 : x ^ (6 : ℝ) = x ^ (6 : ℕ) := by
      rw [show ((6 : ℝ) : ℝ) = ((6 : ℕ) : ℝ) by norm_num, rpow_natCast]
    rw [hm, h6]
    congr 2
    ring
  rw [hLHS, key]
  -- Convert (t/720)^(-(m+1)/6) to (720/t)^((m+1)/6)
  have hg : ((m : ℝ) + 1) / 6 = ((m + 1 : ℝ)) / 6 := by ring
  have hgneg : -((m : ℝ) + 1) / 6 = -(((m + 1 : ℝ)) / 6) := by ring
  rw [hg, hgneg]
  have hinv : (t / 720 : ℝ) ^ (-(((m + 1 : ℝ)) / 6)) =
      (720 / t : ℝ) ^ (((m + 1 : ℝ)) / 6) := by
    rw [show (720 / t : ℝ) = (t / 720)⁻¹ by field_simp]
    rw [inv_rpow ht720.le, ← rpow_neg ht720.le]
  rw [hinv]
  ring

/-! ## Full-line moment integrals -/

/-- Even moment of the pure-sextic Gibbs weight on the full real line.
For `n : ℕ` and `t > 0`,
`∫ x : ℝ, x^{2n} · exp(-(t · x^6 / 720)) dx
  = (1/3) · (720/t)^{(2n+1)/6} · Γ((2n+1)/6)`. -/
theorem sextic_moment_even (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, x ^ (2 * n) * exp (-(t * x ^ 6 / 720)) =
      (1/3) * (720/t) ^ ((2 * n + 1 : ℝ) / 6) * Real.Gamma ((2 * n + 1 : ℝ) / 6) := by
  -- Step 1: rewrite the integrand in `|x|`-form (integrand is even).
  have heven : (∫ x : ℝ, x ^ (2 * n) * exp (-(t * x ^ 6 / 720))) =
      ∫ x : ℝ, |x| ^ (2 * n) * exp (-(t * |x| ^ 6 / 720)) := by
    congr 1
    ext x
    rw [show x ^ (2 * n) = |x| ^ (2 * n) from by
          rw [pow_mul x 2 n, ← sq_abs x, ← pow_mul],
        show x ^ 6 = |x| ^ 6 from by
          rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul x 2 3, ← sq_abs x, ← pow_mul]]
  rw [heven]
  -- Step 2: `integral_comp_abs` gives 2 × half-line integral.
  rw [integral_comp_abs (f := fun y => y ^ (2 * n) * exp (-(t * y ^ 6 / 720)))]
  -- Step 3: substitute the half-line value (B+ form, instantiated at m := 2*n).
  rw [integral_pow_mul_exp_neg_sextic_Ioi (2 * n) ht]
  -- Reconcile (2n + 1) cast and 2 · (1/6) = 1/3.
  have hcast : (((2 * n : ℕ) : ℝ) + 1) / 6 = (2 * n + 1 : ℝ) / 6 := by push_cast; ring
  rw [hcast]
  ring

/-- Odd moment of the pure-sextic Gibbs weight on the full real line vanishes
by symmetry. For `n : ℕ` and any `t : ℝ`,
`∫ x : ℝ, x^{2n+1} · exp(-(t · x^6 / 720)) dx = 0`. -/
theorem sextic_moment_odd (n : ℕ) (t : ℝ) :
    ∫ x : ℝ, x ^ (2 * n + 1) * exp (-(t * x ^ 6 / 720)) = 0 := by
  set f : ℝ → ℝ := fun x => x ^ (2 * n + 1) * exp (-(t * x ^ 6 / 720)) with hf
  have hodd : ∀ x : ℝ, f (-x) = -(f x) := by
    intro x
    simp only [hf]
    rw [Odd.neg_pow ⟨n, rfl⟩, show ((-x) : ℝ) ^ 6 = x ^ 6 from by ring]
    ring
  have heq : (∫ x, f x) = -(∫ x, f x) := by
    conv_lhs => rw [← integral_neg_eq_self f volume]
    rw [show (fun x => f (-x)) = (fun x => -(f x)) from funext hodd]
    rw [integral_neg]
  linarith

/-- The partition function for the pure-sextic potential.
For `t > 0`,
`Z_t = ∫ exp(-(t · x^6 / 720)) dx = (1/3) · (720/t)^{1/6} · Γ(1/6)`. -/
theorem sextic_partition {t : ℝ} (ht : 0 < t) :
    partitionFunction sexticPotential t =
      (1/3) * (720/t) ^ ((1 : ℝ) / 6) * Real.Gamma ((1 : ℝ) / 6) := by
  unfold partitionFunction
  have step : (∫ x : ℝ, exp (-(t * sexticPotential x))) =
              (∫ x : ℝ, x ^ (2 * 0) * exp (-(t * x ^ 6 / 720))) := by
    congr 1
    ext x
    rw [Nat.mul_zero, pow_zero, one_mul, sexticPotential_apply]
    congr 1
    ring
  rw [step, sextic_moment_even 0 ht]
  norm_num

/-- The partition function for the pure-sextic potential is positive. -/
theorem sextic_partition_pos {t : ℝ} (ht : 0 < t) :
    0 < partitionFunction sexticPotential t := by
  rw [sextic_partition ht]
  have h720t : (0 : ℝ) < 720 / t := by positivity
  have hpow : 0 < (720 / t : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos h720t _
  have hg : 0 < Real.Gamma ((1 : ℝ) / 6) := Real.Gamma_pos_of_pos (by norm_num)
  positivity

/-! ## Expected values -/

/-- Even-power expected value against the pure-sextic Gibbs measure.
For `n : ℕ` and `t > 0`,
`⟨x^{2n}⟩_t = (720/t)^{n/3} · Γ((2n+1)/6) / Γ(1/6)`. -/
theorem sextic_expected_value_even (n : ℕ) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation sexticPotential t (fun x => x ^ (2 * n)) =
      (720/t) ^ ((n : ℝ) / 3) * Real.Gamma ((2 * n + 1 : ℝ) / 6) / Real.Gamma ((1 : ℝ) / 6) := by
  unfold gibbsExpectation
  have hnum : (∫ x : ℝ, x ^ (2 * n) * exp (-(t * sexticPotential x))) =
              (∫ x : ℝ, x ^ (2 * n) * exp (-(t * x ^ 6 / 720))) := by
    congr 1
    ext x
    rw [sexticPotential_apply]
    congr 2
    ring
  rw [hnum, sextic_moment_even n ht, sextic_partition ht]
  have h720 : (0 : ℝ) < 720 / t := by positivity
  have hg : Real.Gamma ((1 : ℝ) / 6) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by norm_num))
  have h720pow : (720 / t : ℝ) ^ ((1 : ℝ) / 6) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos h720 _)
  -- Split (2n+1)/6 = n/3 + 1/6 to expose the cancelling factor (720/t)^(1/6).
  rw [show ((2 * n + 1 : ℝ) / 6) = ((n : ℝ) / 3) + ((1 : ℝ) / 6) from by ring,
      Real.rpow_add h720 _ _]
  field_simp

/-- Odd-power expected value against the pure-sextic Gibbs measure vanishes by
symmetry. For any `n : ℕ` and any `t : ℝ`, `⟨x^{2n+1}⟩_t = 0`. -/
theorem sextic_expected_value_odd (n : ℕ) (t : ℝ) :
    gibbsExpectation sexticPotential t (fun x => x ^ (2 * n + 1)) = 0 := by
  unfold gibbsExpectation
  have hnum : (∫ x : ℝ, x ^ (2 * n + 1) * exp (-(t * sexticPotential x))) = 0 := by
    have heq : (∫ x : ℝ, x ^ (2 * n + 1) * exp (-(t * sexticPotential x))) =
               (∫ x : ℝ, x ^ (2 * n + 1) * exp (-(t * x ^ 6 / 720))) := by
      congr 1
      ext x
      rw [sexticPotential_apply]
      congr 2
      ring
    rw [heq, sextic_moment_odd n t]
  rw [hnum, zero_div]

/-- Specialisation of `sextic_expected_value_even` to `n = 1`:
`⟨x^2⟩_t = (720/t)^{1/3} · Γ(1/2) / Γ(1/6) = √π · (720/t)^{1/3} / Γ(1/6)`. -/
theorem sextic_expected_value_sq {t : ℝ} (ht : 0 < t) :
    gibbsExpectation sexticPotential t (fun x => x ^ 2) =
      (720/t) ^ ((1 : ℝ) / 3) * Real.Gamma ((1 : ℝ) / 2) / Real.Gamma ((1 : ℝ) / 6) := by
  have h := sextic_expected_value_even 1 ht
  push_cast at h
  rw [show ((2 * 1 + 1 : ℝ) / 6) = ((1 : ℝ) / 2) from by norm_num,
      show ((1 : ℝ) / 3) = ((1 : ℝ) / 3) from rfl] at h
  -- LHS uses `x^(2*1)`, defEq to `x^2`
  exact h

/-- Specialisation of `sextic_expected_value_odd` to `n = 0`:
`⟨x⟩_t = 0`. -/
theorem sextic_expected_value_lin (t : ℝ) :
    gibbsExpectation sexticPotential t (fun x => x) = 0 := by
  have h := sextic_expected_value_odd 0 t
  simpa using h

/-! ## Covariance of affine observables -/

/-- Covariance of two affine observables against the pure-sextic Gibbs measure.
For `t > 0` and any `a b c d : ℝ`,
`Cov_t[a x + c, b x + d] = a b · (720/t)^{1/3} · Γ(1/2) / Γ(1/6)`.

This is the headline degenerate-case analogue of `quartic_cov_affine`: the
covariance decays as `t^{-1/3}` (rather than the quartic's `t^{-1/2}` or the
nondegenerate `t^{-1}`), and the leading coefficient is given by an explicit
ratio of Γ-values. Note `Γ(1/2) = √π`. -/
theorem sextic_cov_affine {t : ℝ} (ht : 0 < t) (a b c d : ℝ) :
    gibbsCov sexticPotential t (fun x => a * x + c) (fun x => b * x + d) =
      a * b * (720 / t) ^ ((1 : ℝ) / 3) * Real.Gamma ((1 : ℝ) / 2) /
        Real.Gamma ((1 : ℝ) / 6) := by
  have hZpos := sextic_partition_pos ht
  have hZne : partitionFunction sexticPotential t ≠ 0 := ne_of_gt hZpos
  -- Integrability of `1, x, x²` against the Gibbs weight.
  have hI0 : Integrable (fun x : ℝ => Real.exp (-(t * sexticPotential x))) := by
    have h := sextic_integrable_pow_pot 0 ht
    have heq : (fun x : ℝ => x ^ 0 * Real.exp (-(t * sexticPotential x))) =
               (fun x : ℝ => Real.exp (-(t * sexticPotential x))) := by ext; simp
    rwa [heq] at h
  have hI1 : Integrable (fun x : ℝ => x * Real.exp (-(t * sexticPotential x))) := by
    have h := sextic_integrable_pow_pot 1 ht
    have heq : (fun x : ℝ => x ^ 1 * Real.exp (-(t * sexticPotential x))) =
               (fun x : ℝ => x * Real.exp (-(t * sexticPotential x))) := by
      ext; rw [pow_one]
    rwa [heq] at h
  have hI2 := sextic_integrable_pow_pot 2 ht
  -- Linearity for affine combinations: ⟨px + q⟩_t = p ⟨x⟩_t + q.
  have hphi_aff : ∀ p q : ℝ,
      gibbsExpectation sexticPotential t (fun x => p * x + q) =
        p * gibbsExpectation sexticPotential t (fun x => x) + q := by
    intro p q
    unfold gibbsExpectation
    rw [show (fun x : ℝ => (p * x + q) * Real.exp (-(t * sexticPotential x))) =
           (fun x : ℝ => p * (x * Real.exp (-(t * sexticPotential x))) +
                     q * Real.exp (-(t * sexticPotential x))) from by funext x; ring]
    rw [MeasureTheory.integral_add (hI1.const_mul p) (hI0.const_mul q)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hZdef : (∫ x : ℝ, Real.exp (-(t * sexticPotential x))) =
                 partitionFunction sexticPotential t := rfl
    rw [hZdef]
    field_simp
  -- Quadratic expansion: ⟨(ax+c)(bx+d)⟩_t = ab⟨x²⟩_t + (ad+bc)⟨x⟩_t + cd.
  have hphipsi :
      gibbsExpectation sexticPotential t (fun x => (a * x + c) * (b * x + d)) =
        a * b * gibbsExpectation sexticPotential t (fun x => x ^ 2) +
        (a * d + b * c) * gibbsExpectation sexticPotential t (fun x => x) +
        c * d := by
    unfold gibbsExpectation
    rw [show (fun x : ℝ =>
              (a * x + c) * (b * x + d) * Real.exp (-(t * sexticPotential x))) =
           (fun x : ℝ =>
              (a * b) * (x ^ 2 * Real.exp (-(t * sexticPotential x))) +
              (a * d + b * c) * (x * Real.exp (-(t * sexticPotential x))) +
              (c * d) * Real.exp (-(t * sexticPotential x))) from by funext x; ring]
    -- Pi.add workaround (see laplace `CLAUDE.md`): build a *single-lambda*
    -- integrability witness so the integral_add pattern unifies under beta.
    have hI12 : Integrable
        (fun x : ℝ =>
            a * b * (x ^ 2 * Real.exp (-(t * sexticPotential x))) +
            (a * d + b * c) * (x * Real.exp (-(t * sexticPotential x))))
        volume := (hI2.const_mul (a * b)).add (hI1.const_mul (a * d + b * c))
    rw [MeasureTheory.integral_add hI12 (hI0.const_mul (c * d))]
    rw [MeasureTheory.integral_add (hI2.const_mul (a * b))
          (hI1.const_mul (a * d + b * c))]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
    have hZdef : (∫ x : ℝ, Real.exp (-(t * sexticPotential x))) =
                 partitionFunction sexticPotential t := rfl
    rw [hZdef]
    field_simp
  -- Combine: Cov = ⟨φψ⟩ - ⟨φ⟩⟨ψ⟩ = (ab⟨x²⟩ + cd) - cd = ab⟨x²⟩.
  unfold gibbsCov
  rw [hphipsi, hphi_aff a c, hphi_aff b d,
      sextic_expected_value_lin t, sextic_expected_value_sq ht]
  ring

end Laplace.OneD
