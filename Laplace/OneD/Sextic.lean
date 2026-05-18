import Laplace.Gibbs
import Laplace.OneD.MonomialPotential
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

/-- The sextic potential is the `k = 3` specialisation of the generic
even-monomial template. -/
lemma sexticPotential_eq_kthPotential :
    sexticPotential = kthPotential 3 := by
  funext x; simp [sexticPotential, kthPotential]; norm_num

/-! ## Integrability -/

/-- Polynomial-times-sextic-Gibbs integrability.
$k = 3$ specialisation of `kth_integrable_pow`. -/
theorem sextic_integrable_pow (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-(t * x ^ 6 / 720))) := by
  have h := kth_integrable_pow (k := 3) (by norm_num) n ht
  convert h using 4 <;> norm_num

/-- Polynomial-times-sextic-Gibbs integrability, in `sexticPotential` form.
$k = 3$ specialisation of `kth_integrable_pow_pot`. -/
theorem sextic_integrable_pow_pot (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-(t * sexticPotential x))) := by
  rw [sexticPotential_eq_kthPotential]
  exact kth_integrable_pow_pot (k := 3) (by norm_num) n ht

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
$k = 3$ specialisation of `kth_moment_even`. -/
theorem sextic_moment_even (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, x ^ (2 * n) * exp (-(t * x ^ 6 / 720)) =
      (1/3) * (720/t) ^ ((2 * n + 1 : ℝ) / 6) * Real.Gamma ((2 * n + 1 : ℝ) / 6) := by
  have h := kth_moment_even (k := 3) (by norm_num) n ht
  convert h using 3

/-- Odd moment of the pure-sextic Gibbs weight on the full real line vanishes
by symmetry. $k = 3$ specialisation of `kth_moment_odd`. -/
theorem sextic_moment_odd (n : ℕ) (t : ℝ) :
    ∫ x : ℝ, x ^ (2 * n + 1) * exp (-(t * x ^ 6 / 720)) = 0 := by
  have h := kth_moment_odd 3 n t
  convert h using 3

/-- The partition function for the pure-sextic potential.
$k = 3$ specialisation of `partitionFunction_kthPotential`. -/
theorem sextic_partition {t : ℝ} (ht : 0 < t) :
    partitionFunction sexticPotential t =
      (1/3) * (720/t) ^ ((1 : ℝ) / 6) * Real.Gamma ((1 : ℝ) / 6) := by
  rw [sexticPotential_eq_kthPotential]
  have h := partitionFunction_kthPotential (k := 3) (by norm_num) ht
  convert h using 3

/-- The partition function for the pure-sextic potential is positive.
$k = 3$ specialisation of `partitionFunction_kthPotential_pos`. -/
theorem sextic_partition_pos {t : ℝ} (ht : 0 < t) :
    0 < partitionFunction sexticPotential t := by
  rw [sexticPotential_eq_kthPotential]
  exact partitionFunction_kthPotential_pos (k := 3) (by norm_num) ht

/-! ## Expected values -/

/-- Even-power expected value against the pure-sextic Gibbs measure.
$k = 3$ specialisation of `gibbsExpectation_kthPotential_even`. -/
theorem sextic_expected_value_even (n : ℕ) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation sexticPotential t (fun x => x ^ (2 * n)) =
      (720/t) ^ ((n : ℝ) / 3) * Real.Gamma ((2 * n + 1 : ℝ) / 6) / Real.Gamma ((1 : ℝ) / 6) := by
  rw [sexticPotential_eq_kthPotential]
  have h := gibbsExpectation_kthPotential_even (k := 3) (by norm_num) n ht
  convert h using 3

/-- Odd-power expected value against the pure-sextic Gibbs measure vanishes by
symmetry. $k = 3$ specialisation of `gibbsExpectation_kthPotential_odd`. -/
theorem sextic_expected_value_odd (n : ℕ) (t : ℝ) :
    gibbsExpectation sexticPotential t (fun x => x ^ (2 * n + 1)) = 0 := by
  rw [sexticPotential_eq_kthPotential]
  exact gibbsExpectation_kthPotential_odd 3 n t

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
