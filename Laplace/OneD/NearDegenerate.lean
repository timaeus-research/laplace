import Laplace.Gibbs
import Laplace.OneD.Anharmonic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Near-degenerate scaling identity

This file proves the universal-scaling formula identified in the
near-degenerate-crossover note (`sri/projects/automation/log/2026-05-01-near-
degenerate-crossover.md`):

For the **near-degenerate** potential `L^{nd}_ε(x) = (ε/2) x² + x⁴/24` and the
**universal potential** `V(y) = y²/2 + y⁴/24`, the substitution `x = √ε · y`
takes `t · L^{nd}_ε(x)` to `ε² t · V(y)` exactly. This forces every Gibbs
moment of the near-degenerate posterior to factor through the universal
posterior at the *effective inverse temperature* `T = ε² t`:

  `⟨x^{2n}⟩_{μ_t}^{L^{nd}_ε} = ε^n · ⟨y^{2n}⟩_{μ_T}^{V}`.

Below the crossover scale `t ≪ 1/ε²` (i.e. `T ≪ 1`), the universal moment is
governed by the pure-quartic core (`Laplace.OneD.Quartic`). Above the
crossover (`T ≫ 1`), it tracks the standard Laplace asymptotics. The scaling
identity holds *exactly* for every ε, t > 0, with no remainder.

## Headline

* `near_degenerate_expected_value_scaling`:
    `⟨x^{2n}⟩_{L^{nd}_ε, t} = ε^n · ⟨y^{2n}⟩_{V, ε²t}` for `ε, t > 0`, `n : ℕ`.

## Internal lemmas (in dependency order)

* `nearDegeneratePotential_sqrt_eps_apply`: `L^{nd}_ε(√ε · y) = ε² · V(y)` (the
  algebraic core of the substitution).
* `near_degenerate_integral_substitution`: for any `f : ℝ → ℝ` and `ε > 0`,
    `∫ x, f x · exp(-(t · L^{nd}_ε(x))) = √ε · ∫ y, f(√ε y) · exp(-(ε²t · V(y)))`.
  (Mathlib's `integral_comp_mul_right` plus a pointwise rewrite.)
* `partitionFunction_near_degenerate`: `Z_{L^{nd}_ε}(t) = √ε · Z_V(ε²t)`.
* `gibbsExpectation_near_degenerate`: `gibbs-expectation` transport for any `f`.

## Tide-step provenance

Tide step 3, formalised on `tide/universal-scaling` (branched off
`tide/2d-semi-degenerate`). See
`sri/projects/automation/log/2026-05-01-tide-universal-scaling.md`.
-/

open Real MeasureTheory

namespace Laplace.OneD

/-! ## Aliases -/

/-- The 1D near-degenerate potential `L^{nd}_ε(x) = (ε/2) x² + x⁴/24`. This is
the anharmonic potential with cubic coefficient `α = 0` and quartic
coefficient `γ = 1`. -/
noncomputable abbrev nearDegeneratePotential (eps : ℝ) : ℝ → ℝ :=
  anharmonicPotential eps 0 1

/-- The universal scaling potential `V(y) = y²/2 + y⁴/24`. Equal to
`nearDegeneratePotential 1`. -/
noncomputable abbrev universalPotential : ℝ → ℝ := nearDegeneratePotential 1

@[simp] lemma nearDegeneratePotential_apply (eps x : ℝ) :
    nearDegeneratePotential eps x = eps / 2 * x ^ 2 + x ^ 4 / 24 := by
  unfold nearDegeneratePotential anharmonicPotential
  ring

@[simp] lemma universalPotential_apply (y : ℝ) :
    universalPotential y = y ^ 2 / 2 + y ^ 4 / 24 := by
  unfold universalPotential nearDegeneratePotential anharmonicPotential
  ring

/-! ## Algebraic substitution identity -/

/-- The algebraic core of the universal scaling: substituting `x = √ε · y`
into `L^{nd}_ε` produces `ε² V(y)` exactly. -/
lemma nearDegeneratePotential_sqrt_eps_apply (eps : ℝ) (heps : 0 ≤ eps) (y : ℝ) :
    nearDegeneratePotential eps (Real.sqrt eps * y) =
      eps ^ 2 * universalPotential y := by
  rw [nearDegeneratePotential_apply, universalPotential_apply]
  -- Use (√ε)² = ε and (√ε)⁴ = ε² to expand and simplify.
  have hsq : Real.sqrt eps ^ 2 = eps := Real.sq_sqrt heps
  have h2 : (Real.sqrt eps * y) ^ 2 = eps * y ^ 2 := by
    rw [mul_pow, hsq]
  have h4 : (Real.sqrt eps * y) ^ 4 = eps ^ 2 * y ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2]
    ring
  rw [h2, h4]
  ring

/-! ## Substitution lemma -/

/-- **General substitution lemma (Candidate D).** For `ε > 0`, any function
`f : ℝ → ℝ`, and `t : ℝ`,
  `∫ x, f(x) · exp(-(t · L^{nd}_ε(x))) dx
     = √ε · ∫ y, f(√ε · y) · exp(-(ε² t · V(y))) dy`.

This is the unnormalised universal-scaling identity at the integral level. The
proof composes Mathlib's `MeasureTheory.Measure.integral_comp_mul_right` with
the algebraic identity `L^{nd}_ε(√ε y) = ε² V(y)`. -/
theorem near_degenerate_integral_substitution
    (f : ℝ → ℝ) {eps : ℝ} (heps : 0 < eps) (t : ℝ) :
    (∫ x : ℝ, f x * Real.exp (-(t * nearDegeneratePotential eps x))) =
      Real.sqrt eps *
        ∫ y : ℝ, f (Real.sqrt eps * y) *
          Real.exp (-(eps ^ 2 * t * universalPotential y)) := by
  -- Mathlib's `integral_comp_mul_right` says `∫ x, g(x · a) = |a⁻¹| • ∫ y, g y`.
  -- Apply it with `a = √ε` and `g(x) = f(x) · exp(-(t · L^{nd}_ε(x)))`.
  have hsqrt_pos : 0 < Real.sqrt eps := Real.sqrt_pos.mpr heps
  have hsqrt_ne : Real.sqrt eps ≠ 0 := ne_of_gt hsqrt_pos
  have hkey :=
    MeasureTheory.Measure.integral_comp_mul_right
      (fun x : ℝ => f x * Real.exp (-(t * nearDegeneratePotential eps x)))
      (Real.sqrt eps)
  -- `hkey` : `∫ x, (f * exp(...))(x · √ε) = |√ε⁻¹| • ∫ y, f y · exp(-(t L y))`.
  -- We want the *opposite* direction; rearrange.
  rw [abs_of_pos (inv_pos.mpr hsqrt_pos), smul_eq_mul] at hkey
  -- hkey : ∫ x, f(x · √ε) · exp(-(t · L^{nd}_ε(x · √ε))) =
  --          (√ε)⁻¹ * ∫ y, f y · exp(-(t · L^{nd}_ε(y))).
  -- Solve for the RHS:
  have hkey' :
      (∫ y : ℝ, f y * Real.exp (-(t * nearDegeneratePotential eps y))) =
        Real.sqrt eps *
          ∫ x : ℝ, f (x * Real.sqrt eps) *
            Real.exp (-(t * nearDegeneratePotential eps (x * Real.sqrt eps))) := by
    have := hkey
    field_simp at this
    linarith
  rw [hkey']
  -- Replace the integrand with the universal form via the algebraic identity.
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [show x * Real.sqrt eps = Real.sqrt eps * x from mul_comm _ _]
  rw [nearDegeneratePotential_sqrt_eps_apply eps heps.le]
  ring_nf

/-! ## Partition-function corollary -/

/-- **Partition-function scaling (Candidate B).** For `ε > 0` and `t : ℝ`,
`Z_{L^{nd}_ε}(t) = √ε · Z_V(ε² t)`. -/
theorem partitionFunction_near_degenerate {eps : ℝ} (heps : 0 < eps) (t : ℝ) :
    Laplace.partitionFunction (nearDegeneratePotential eps) t =
      Real.sqrt eps *
        Laplace.partitionFunction universalPotential (eps ^ 2 * t) := by
  unfold Laplace.partitionFunction
  -- Apply the substitution lemma at f ≡ 1.
  have h := near_degenerate_integral_substitution (fun _ => (1 : ℝ)) heps t
  simp only [one_mul] at h
  exact h

/-! ## Gibbs-expectation transport -/

/-- **Gibbs-expectation transport (Candidate E).** For `ε > 0`, `t > 0`, and
any `f : ℝ → ℝ`,
  `⟨f⟩_{L^{nd}_ε, t} = ⟨y ↦ f(√ε y)⟩_{V, ε² t}`.

Both sides are normalised by the respective partition functions; the `√ε`
prefactors of D and B cancel. -/
theorem gibbsExpectation_near_degenerate
    (f : ℝ → ℝ) {eps t : ℝ} (heps : 0 < eps) (_ht : 0 < t) :
    Laplace.gibbsExpectation (nearDegeneratePotential eps) t f =
      Laplace.gibbsExpectation universalPotential (eps ^ 2 * t)
        (fun y => f (Real.sqrt eps * y)) := by
  unfold Laplace.gibbsExpectation
  rw [near_degenerate_integral_substitution f heps t,
      partitionFunction_near_degenerate heps t]
  -- Goal: (√ε · NUM') / (√ε · DEN') = NUM' / DEN', i.e. cancel √ε.
  have hsqrt_ne : Real.sqrt eps ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr heps)
  rw [mul_div_mul_left _ _ hsqrt_ne]

/-! ## Headline: monomial scaling -/

/-- **Universal scaling identity for monomial moments (Candidate A).** For
`ε > 0`, `t > 0`, and `n : ℕ`,
  `⟨x^{2n}⟩_{L^{nd}_ε, t} = ε^n · ⟨y^{2n}⟩_{V, ε² t}`.

The factor of `ε^n` comes from `(√ε)^{2n} = ε^n` after pulling the constant
out of the universal-potential integral. -/
theorem near_degenerate_expected_value_scaling
    (n : ℕ) {eps t : ℝ} (heps : 0 < eps) (ht : 0 < t) :
    Laplace.gibbsExpectation (nearDegeneratePotential eps) t
        (fun x => x ^ (2 * n)) =
      eps ^ n *
        Laplace.gibbsExpectation universalPotential (eps ^ 2 * t)
          (fun y => y ^ (2 * n)) := by
  -- Step 1: transport via E to the universal potential.
  rw [gibbsExpectation_near_degenerate _ heps ht]
  -- Goal: ⟨y ↦ (√ε · y)^{2n}⟩_{V, T} = ε^n · ⟨y ↦ y^{2n}⟩_{V, T}.
  -- Step 2: pull (√ε)^{2n} = ε^n out of the integrand.
  have hsqrt_pow : Real.sqrt eps ^ (2 * n) = eps ^ n := by
    rw [pow_mul, Real.sq_sqrt heps.le]
  -- Rewrite (√ε · y)^{2n} = ε^n · y^{2n}.
  have hpow : ∀ y : ℝ, (Real.sqrt eps * y) ^ (2 * n) = eps ^ n * y ^ (2 * n) := by
    intro y
    rw [mul_pow, hsqrt_pow]
  unfold Laplace.gibbsExpectation
  rw [show (fun y : ℝ => (Real.sqrt eps * y) ^ (2 * n) *
            Real.exp (-(eps ^ 2 * t * universalPotential y))) =
          (fun y : ℝ => eps ^ n * (y ^ (2 * n) *
            Real.exp (-(eps ^ 2 * t * universalPotential y)))) from by
    funext y; rw [hpow]; ring]
  rw [MeasureTheory.integral_const_mul]
  ring

end Laplace.OneD
