import Laplace.OneD.Harmonic
import Laplace.OneD.Localisation

/-!
# The 1D anharmonic potential

Setup for the primer's `lem:laplace_cov2` (1D specialisation):

  For `L(x) = (λ/2) x² + (α/6) x³ + (γ/24) x⁴` with `λ > 0`, `γ > 0`, `α ∈ ℝ`,
  and the Gibbs measure `exp(-t L(x)) dx`, we want

    `Cov_t[x², x] = -2α/(λ³ t²) + o(t⁻²)`  as `t → ∞`.

This file defines the potential and establishes its basic shape:
* `anharmonicPotential lam alpha gamma`: the cubic-plus-quartic form.
* `anharmonic_eq_harmonic_add_perturbation`: split into harmonic + perturbation.
* `anharmonicPerturbation`: the `(α/6) x³ + (γ/24) x⁴` piece.
* Algebraic facts about the perturbation at `0` (vanishing through second order).

The asymptotic theorem itself is left as future work.
-/

open Real

namespace Laplace.OneD

/-- The 1D anharmonic potential `L(x) = (λ/2)x² + (α/6)x³ + (γ/24)x⁴`. -/
noncomputable def anharmonicPotential (lam alpha gamma : ℝ) : ℝ → ℝ :=
  fun x => lam / 2 * x ^ 2 + alpha / 6 * x ^ 3 + gamma / 24 * x ^ 4

/-- The cubic + quartic perturbation `g(x) = (α/6)x³ + (γ/24)x⁴`. -/
noncomputable def anharmonicPerturbation (alpha gamma : ℝ) : ℝ → ℝ :=
  fun x => alpha / 6 * x ^ 3 + gamma / 24 * x ^ 4

/-- The anharmonic potential decomposes as `L_λ + g_{α,γ}`. -/
lemma anharmonicPotential_eq_harmonic_add_perturbation
    (lam alpha gamma : ℝ) (x : ℝ) :
    anharmonicPotential lam alpha gamma x =
      harmonicPotential lam x + anharmonicPerturbation alpha gamma x := by
  unfold anharmonicPotential harmonicPotential anharmonicPerturbation
  ring

/-- Functional form of the decomposition. -/
lemma anharmonicPotential_eq_add (lam alpha gamma : ℝ) :
    anharmonicPotential lam alpha gamma =
      fun x => harmonicPotential lam x + anharmonicPerturbation alpha gamma x := by
  ext x
  exact anharmonicPotential_eq_harmonic_add_perturbation lam alpha gamma x

/-- The perturbation vanishes at the origin. -/
lemma anharmonicPerturbation_zero (alpha gamma : ℝ) :
    anharmonicPerturbation alpha gamma 0 = 0 := by
  unfold anharmonicPerturbation; ring

/-- The perturbation is `O(x³)` near the origin: explicitly,
`g(x) = x³ · (α/6 + γ/24 · x)`. -/
lemma anharmonicPerturbation_factor (alpha gamma x : ℝ) :
    anharmonicPerturbation alpha gamma x =
      x ^ 3 * (alpha / 6 + gamma / 24 * x) := by
  unfold anharmonicPerturbation; ring

/-- Splitting the Gibbs Boltzmann factor: `exp(-t L) = exp(-t L_harm) · exp(-t g)`. -/
lemma exp_neg_t_anharmonic_eq_mul (lam alpha gamma t x : ℝ) :
    Real.exp (-(t * anharmonicPotential lam alpha gamma x)) =
      Real.exp (-(t * harmonicPotential lam x)) *
        Real.exp (-(t * anharmonicPerturbation alpha gamma x)) := by
  rw [anharmonicPotential_eq_harmonic_add_perturbation]
  rw [show -(t * (harmonicPotential lam x + anharmonicPerturbation alpha gamma x)) =
        -(t * harmonicPotential lam x) + -(t * anharmonicPerturbation alpha gamma x) by
        ring]
  exact Real.exp_add _ _

/-! ## Coercivity

For the anharmonic potential to admit a Laplace asymptotic, we need
`L(x) ≥ c · x²` globally for some `c > 0`. This is what makes `0` a strict
global minimum of `L` (not just a local one) and provides the Gaussian decay
that controls the integrals.

Writing `L(x) = x² · Q(x)` with `Q(x) = (γ/24) x² + (α/6) x + (λ/2)`, the
minimum value of the quadratic `Q` is `(3λγ - α²)/(6γ)`. Hence the
**discriminant condition** `α² < 3λγ` (with `λ, γ > 0`) is sufficient for
strict global coercivity.
-/

/-- The factored form: `L(x) = x² · Q(x)` where `Q` is a degree-2 polynomial. -/
lemma anharmonicPotential_factor (lam alpha gamma x : ℝ) :
    anharmonicPotential lam alpha gamma x =
      x ^ 2 * (gamma / 24 * x ^ 2 + alpha / 6 * x + lam / 2) := by
  unfold anharmonicPotential; ring

/-- The minimum value of the quadratic `Q(x) = (γ/24) x² + (α/6) x + (λ/2)`
is `(3λγ - α²) / (6γ)`, attained at `x = -2α/γ`. -/
lemma anharmonic_quadratic_min (lam alpha gamma x : ℝ) (hgamma : 0 < gamma) :
    (3 * lam * gamma - alpha ^ 2) / (6 * gamma) ≤
      gamma / 24 * x ^ 2 + alpha / 6 * x + lam / 2 := by
  -- Complete the square: γ/24 · (x + 2α/γ)² + (3λγ - α²)/(6γ)
  --                    = γ/24 · x² + (α/6) x + (λ/2)  -- after expansion.
  have key : gamma / 24 * x ^ 2 + alpha / 6 * x + lam / 2 -
              (3 * lam * gamma - alpha ^ 2) / (6 * gamma) =
              gamma / 24 * (x + 2 * alpha / gamma) ^ 2 := by
    have hg_ne : gamma ≠ 0 := hgamma.ne'
    field_simp
    ring
  -- Both sides are non-negative (the RHS as a square times γ/24 > 0).
  have hsq : 0 ≤ gamma / 24 * (x + 2 * alpha / gamma) ^ 2 := by positivity
  linarith

/-- **Anharmonic coercivity (discriminant form)**:
under the discriminant condition `α² < 3λγ` (with `λ, γ > 0`),
the quadratic factor is bounded below by a positive constant
`c = (3λγ - α²) / (6γ)`. -/
lemma anharmonic_quadratic_lower_bound (lam alpha gamma : ℝ)
    (_hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ c > 0, ∀ x : ℝ, c ≤ gamma / 24 * x ^ 2 + alpha / 6 * x + lam / 2 := by
  refine ⟨(3 * lam * gamma - alpha ^ 2) / (6 * gamma), ?_, ?_⟩
  · -- c > 0 since numerator > 0 (by hdisc) and denominator > 0.
    apply div_pos
    · linarith
    · linarith
  · intro x
    exact anharmonic_quadratic_min lam alpha gamma x hgamma

/-- **Anharmonic coercivity**: under `α² < 3λγ`, the anharmonic potential
satisfies `L(x) ≥ c · x²` globally for `c = (3λγ - α²) / (6γ) > 0`. -/
theorem anharmonic_coercive (lam alpha gamma : ℝ)
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ c > 0, ∀ x : ℝ, c * x ^ 2 ≤ anharmonicPotential lam alpha gamma x := by
  obtain ⟨c, hc_pos, hQ⟩ :=
    anharmonic_quadratic_lower_bound lam alpha gamma hlam hgamma hdisc
  refine ⟨c, hc_pos, fun x => ?_⟩
  rw [anharmonicPotential_factor]
  -- Goal: c · x² ≤ x² · Q(x).
  have hx : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  rw [show (x ^ 2 * (gamma / 24 * x ^ 2 + alpha / 6 * x + lam / 2) : ℝ) =
        (gamma / 24 * x ^ 2 + alpha / 6 * x + lam / 2) * x ^ 2 by ring]
  rw [show (c * x ^ 2 : ℝ) = c * x ^ 2 from rfl]
  exact mul_le_mul_of_nonneg_right (hQ x) hx

end Laplace.OneD
