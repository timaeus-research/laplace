import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Threepoint.CrossSusceptibility

/-!
# Concrete `GibbsRegularity` instance for the harmonic potential

For the 1D harmonic potential `L(x) = (λ/2)x²` with the linear
perturbation `A(x) = x` on `ℝ` against Lebesgue measure (with `λ, t > 0`),
this file proves
  `Threepoint.GibbsRegularity (volume) ((λ/2)·) (id) t`.

The instance unlocks threepoint's *derivative* theorems --- the FDT
(`Threepoint.gibbsExp_deriv_eq_neg_t_cov`), the cross-susceptibility
identity (`gibbsCov_deriv_eq_neg_t_kappa3`), and the flow equation ---
for the harmonic case, transforming them from parameterised lemmas
(conditional on a hypothesis bundle) into theorems about the harmonic
Gibbs measure proper. The kappa3-harmonic tide (Tide 5) and the
anharmonic-κ₃ tide (Tide 9) both deliberately sidestepped
`GibbsRegularity` because their targets lived at `h = 0`; this tide
provides the substrate those derivative theorems need.

## Strategy

Rather than apply a dominated-convergence theorem
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), we prove the
*closed form* of the partition function for all `h`:
\[
  Z(h) := \int e^{-(t\,((\lambda/2) x^2 + h\,x))}\,dx
        = e^{t h^2/(2\lambda)} \sqrt{2\pi/(\lambda t)}.
\]
This is via square completion plus translation invariance of Lebesgue
measure plus `integral_gaussian`, and from this all three
`GibbsRegularity` fields are ordinary calculus.

## Headline

* `Threepoint.harmonic_id_gibbsRegularity`:
    For `λ, t > 0`,
    `Threepoint.GibbsRegularity (volume) (fun x => (λ/2)·x²) (fun x => x) t`.

## Helpers (user-facing)

* `harmonic_linear_partition_eq`: closed form of `Z(h)` for all `h`.
* `harmonic_partition_pos`: `0 < Z(0)` for `λ, t > 0`.
* `harmonic_integral_x_exp_neg_eq_zero`: `∫ x · exp(-(tλ/2)x²) dx = 0`
  by parity. (The pointwise derivative of `Z` at `h = 0` equals
  `∫ (-t·x) · exp(-(tλ/2)x²) dx = 0`.)

## Tide-step provenance

Tide step 10 (Candidate C3 from the 6 May candidates survey),
formalised on `tide/harmonic-gibbsregularity` in laplace, branched off
`main` (commit `8f330ce`). See
`sri/projects/patterning/tide-log/2026-05-06-tide-harmonic-gibbsregularity.md`.
-/

open MeasureTheory Real Filter Topology

namespace Laplace.OneD

/-! ## Closed-form partition function -/

/-- Square-completion identity:
`(λ/2) x² + h x = (λ/2) (x + h/λ)² - h²/(2λ)`. -/
private lemma harmonic_square_completion (lam h x : ℝ) (hlam : lam ≠ 0) :
    (lam / 2) * x ^ 2 + h * x
      = (lam / 2) * (x + h / lam) ^ 2 - h ^ 2 / (2 * lam) := by
  field_simp
  ring

/-- Pointwise rewrite of the perturbed Boltzmann factor. -/
private lemma exp_neg_t_harmonic_linear_eq (lam t h x : ℝ) (hlam : lam ≠ 0) :
    Real.exp (-(t * ((lam / 2) * x ^ 2 + h * x)))
      = Real.exp (t * h ^ 2 / (2 * lam))
        * Real.exp (-(t * ((lam / 2) * (x + h / lam) ^ 2))) := by
  rw [harmonic_square_completion lam h x hlam]
  rw [show -(t * ((lam / 2) * (x + h / lam) ^ 2 - h ^ 2 / (2 * lam)))
        = t * h ^ 2 / (2 * lam) + (-(t * ((lam / 2) * (x + h / lam) ^ 2)))
        from by ring]
  rw [Real.exp_add]

/-- **Closed form of the harmonic + linear-perturbation partition function.**

For `λ, t > 0` and any `h ∈ ℝ`,
`∫ exp(-(t · ((λ/2) x² + h x))) dx = exp(t h² / (2λ)) · √(2π/(λt))`. -/
theorem harmonic_linear_partition_eq
    {lam t h : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    (∫ x : ℝ, Real.exp (-(t * ((lam / 2) * x ^ 2 + h * x))))
      = Real.exp (t * h ^ 2 / (2 * lam))
          * Real.sqrt (2 * Real.pi / (lam * t)) := by
  have hlam_ne : lam ≠ 0 := hlam.ne'
  -- Pointwise rewrite: integrand factors as constant * shifted Gaussian.
  have h_integrand_eq :
      (fun x : ℝ => Real.exp (-(t * ((lam / 2) * x ^ 2 + h * x))))
        = fun x : ℝ => Real.exp (t * h ^ 2 / (2 * lam))
            * Real.exp (-(t * ((lam / 2) * (x + h / lam) ^ 2))) := by
    funext x
    exact exp_neg_t_harmonic_linear_eq lam t h x hlam_ne
  rw [show (∫ x : ℝ, Real.exp (-(t * ((lam / 2) * x ^ 2 + h * x))))
        = ∫ x : ℝ, Real.exp (t * h ^ 2 / (2 * lam))
            * Real.exp (-(t * ((lam / 2) * (x + h / lam) ^ 2))) from by
      rw [h_integrand_eq]]
  -- Pull the constant out of the integral.
  rw [integral_const_mul]
  -- Translation invariance: ∫ exp(-(tλ/2)·(x + h/λ)²) = ∫ exp(-(tλ/2)·y²).
  have h_translate :
      (∫ x : ℝ, Real.exp (-(t * ((lam / 2) * (x + h / lam) ^ 2))))
        = ∫ y : ℝ, Real.exp (-(t * ((lam / 2) * y ^ 2))) :=
    integral_add_right_eq_self
      (fun y : ℝ => Real.exp (-(t * ((lam / 2) * y ^ 2)))) (h / lam)
  rw [h_translate]
  -- Bridge to integral_gaussian: -(t · ((λ/2) · y²)) = -(tλ/2) · y².
  have h_eq : (fun y : ℝ => Real.exp (-(t * ((lam / 2) * y ^ 2))))
      = (fun y : ℝ => Real.exp (-(t * lam / 2) * y ^ 2)) := by
    funext y; ring_nf
  rw [h_eq]
  -- ∫ exp(-b · y²) = √(π/b) with b = tλ/2.
  rw [integral_gaussian (t * lam / 2)]
  -- √(π / (tλ/2)) = √(2π/(λt)).
  congr 1
  field_simp

/-! ## Specialisations at `h = 0` -/

/-- The unperturbed harmonic partition function:
`∫ exp(-(tλ/2) x²) dx = √(2π/(λt))` for `λ, t > 0`. -/
theorem harmonic_partition_eq
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    (∫ x : ℝ, Real.exp (-(t * ((lam / 2) * x ^ 2))))
      = Real.sqrt (2 * Real.pi / (lam * t)) := by
  have h := harmonic_linear_partition_eq (h := 0) hlam ht
  -- LHS of h has `(lam/2) * x^2 + 0 * x`; rewrite by integrand congruence.
  have h_lhs : (∫ x : ℝ, Real.exp (-(t * ((lam / 2) * x ^ 2 + 0 * x))))
      = (∫ x : ℝ, Real.exp (-(t * ((lam / 2) * x ^ 2)))) := by
    congr 1
    funext x
    ring_nf
  rw [h_lhs] at h
  -- RHS of h has `Real.exp (t * 0^2 / (2 * lam)) * √(...)`; simplify.
  have h_rhs : Real.exp (t * (0 : ℝ) ^ 2 / (2 * lam))
      * Real.sqrt (2 * Real.pi / (lam * t))
      = Real.sqrt (2 * Real.pi / (lam * t)) := by
    rw [show t * (0 : ℝ) ^ 2 / (2 * lam) = 0 from by ring, Real.exp_zero]
    ring
  rw [h_rhs] at h
  exact h

/-- Strict positivity of the unperturbed harmonic partition. -/
theorem harmonic_partition_pos
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    0 < (∫ x : ℝ, Real.exp (-(t * ((lam / 2) * x ^ 2)))) := by
  rw [harmonic_partition_eq hlam ht]
  apply Real.sqrt_pos.mpr
  positivity

/-! ## Parity: odd-moment vanishing -/

/-- Generic helper: for an odd integrable function on `ℝ`, the integral is
zero. (Mirrors `Threepoint.integral_eq_zero_of_odd` from the harmonic
κ₃ tide.) -/
private lemma integral_eq_zero_of_odd
    (f : ℝ → ℝ) (hodd : ∀ x, f (-x) = -(f x)) :
    (∫ x : ℝ, f x) = 0 := by
  have heq : (∫ x : ℝ, f x) = -(∫ x : ℝ, f x) := by
    conv_lhs => rw [← MeasureTheory.integral_neg_eq_self f volume]
    rw [show (fun x : ℝ => f (-x)) = (fun x : ℝ => -(f x)) from funext hodd]
    rw [MeasureTheory.integral_neg]
  linarith

/-- The first Gaussian moment vanishes:
`∫ (-t · x) · exp(-(tλ/2) x²) dx = 0`. This is the right-hand side of
`partition_hasDerivAt` at `h = 0`. -/
theorem harmonic_integral_neg_t_x_exp_neg_eq_zero
    (lam t : ℝ) :
    (∫ x : ℝ, (-t * x) * Real.exp (-(t * ((lam / 2) * x ^ 2)))) = 0 := by
  apply integral_eq_zero_of_odd
  intro x
  have hsq : (-x) ^ 2 = x ^ 2 := by ring
  rw [hsq]
  ring

/-! ## Differentiability of `Z(h)` at `h = 0` -/

/-- The closed form of `Z(h)` is differentiable in `h` everywhere; at
`h = 0` the derivative is zero. -/
private theorem closed_form_hasDerivAt_zero
    (lam t : ℝ) :
    HasDerivAt
      (fun h : ℝ => Real.exp (t * h ^ 2 / (2 * lam))
          * Real.sqrt (2 * Real.pi / (lam * t)))
      0 0 := by
  -- Goal: derivative at 0 of `exp(g(h)) · C` where `g(h) = t·h²/(2λ)`,
  -- `C = √(2π/(λt))`. `g'(0) = 0`, so the whole derivative is 0.
  -- Step 1: g'(0) = 0.
  have h_g : HasDerivAt (fun h : ℝ => t * h ^ 2 / (2 * lam)) 0 0 := by
    have hpow : HasDerivAt (fun h : ℝ => h ^ 2)
        ((2 : ℕ) * (0 : ℝ) ^ ((2 : ℕ) - 1)) 0 := hasDerivAt_pow 2 (0 : ℝ)
    have h_t : HasDerivAt (fun h : ℝ => t * h ^ 2)
        (t * ((2 : ℕ) * (0 : ℝ) ^ ((2 : ℕ) - 1))) 0 := hpow.const_mul t
    have h_div : HasDerivAt (fun h : ℝ => t * h ^ 2 / (2 * lam))
        (t * ((2 : ℕ) * (0 : ℝ) ^ ((2 : ℕ) - 1)) / (2 * lam)) 0 :=
      h_t.div_const (2 * lam)
    have h_zero : t * ((2 : ℕ) * (0 : ℝ) ^ ((2 : ℕ) - 1)) / (2 * lam) = 0 := by
      norm_num
    rw [h_zero] at h_div
    exact h_div
  -- Step 2: exp ∘ g at 0; use HasDerivAt.exp.
  have h_exp : HasDerivAt
      (fun h : ℝ => Real.exp (t * h ^ 2 / (2 * lam)))
      (Real.exp (t * (0 : ℝ) ^ 2 / (2 * lam)) * 0) 0 := h_g.exp
  have h_simp : Real.exp (t * (0 : ℝ) ^ 2 / (2 * lam)) * 0 = 0 := by ring
  rw [h_simp] at h_exp
  -- Step 3: multiply by the constant √(2π/(λt)).
  have h_const := h_exp.mul_const (Real.sqrt (2 * Real.pi / (lam * t)))
  have h_simp2 : (0 : ℝ) * Real.sqrt (2 * Real.pi / (lam * t)) = 0 := by ring
  rw [h_simp2] at h_const
  exact h_const

/-! ## The `GibbsRegularity` instance -/

/-- **Concrete `GibbsRegularity` for the harmonic + linear-perturbation case.**

For the 1D harmonic potential `L(x) = (λ/2) x²` with the linear
perturbation `A(x) = x` on `ℝ` against Lebesgue measure (`λ, t > 0`),
all three regularity fields hold. The proof routes through the
closed-form partition function (`harmonic_linear_partition_eq`) and
ordinary calculus on the closed form. -/
theorem _root_.Threepoint.harmonic_id_gibbsRegularity
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    Threepoint.GibbsRegularity (volume : Measure ℝ)
      (fun x : ℝ => lam / 2 * x ^ 2)
      (fun x : ℝ => x) t where
  partition_pos := harmonic_partition_pos hlam ht
  partition_h_zero := by
    -- ∫ exp(-(t·((λ/2)x² + 0·x))) = ∫ exp(-(t·(λ/2)x²)).
    congr 1
    funext x
    ring_nf
  partition_hasDerivAt := by
    -- Goal: HasDerivAt (fun h => ∫ exp(-(t·((λ/2)x² + h·x)))) (target) 0
    -- target := ∫ (-t · x) · exp(-(t·(λ/2)x²)) = 0 (by parity).
    -- Approach: show the integrand-as-function-of-h equals
    -- exp(t·h²/(2λ)) · √(2π/(λt)) (closed form), differentiate.
    have h_eq : (fun h : ℝ =>
            ∫ x : ℝ, Real.exp (-(t * ((lam / 2) * x ^ 2 + h * x))))
        = (fun h : ℝ => Real.exp (t * h ^ 2 / (2 * lam))
            * Real.sqrt (2 * Real.pi / (lam * t))) := by
      funext h
      exact harmonic_linear_partition_eq hlam ht
    rw [h_eq]
    -- Derivative of the closed form at 0 is 0.
    have h_deriv : HasDerivAt
        (fun h : ℝ => Real.exp (t * h ^ 2 / (2 * lam))
            * Real.sqrt (2 * Real.pi / (lam * t)))
        0 0 := closed_form_hasDerivAt_zero lam t
    -- The target value `∫ (-t · x) · exp(-(t·(λ/2)x²))` also equals 0 by parity.
    have h_tgt :
        (∫ x : ℝ, (-t * x) * Real.exp (-(t * ((lam / 2) * x ^ 2)))) = 0 :=
      harmonic_integral_neg_t_x_exp_neg_eq_zero lam t
    rw [h_tgt]
    exact h_deriv

end Laplace.OneD
