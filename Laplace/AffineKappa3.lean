import Laplace.Gibbs
import Threepoint.CrossSusceptibility
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Factored $\kappa_3$ identity for affine observables (potential-agnostic)

For any 1D Gibbs measure with potential $L$ at temperature $t$ (with
appropriate integrability and a non-zero partition function), and any
constants $a_1, a_2, a_3, b_1, b_2, b_3 \in \mathbb{R}$, the third
joint cumulant of three shifted-affine observables factors as
$$
  \kappa_3(\mu, L,\;a_2 x + b_2,\;t,\;a_1 x + b_1,\;a_3 x + b_3)
  \;=\; a_1 a_2 a_3 \cdot \kappa_3(\mu, L,\;x,\;t,\;x,\;x).
$$
This is the natural cumulant content: constants drop by translation
invariance, scalings factor by trilinearity. The C1 (harmonic-affine
$\kappa_3$ vanishing) and G2/G2+ (anharmonic-affine $\kappa_3$
asymptotic) tides become 5-line specialisations of this identity.

## Headline results

* `threepoint_gibbsExp_volume_zero_eq` — the Threepoint→Laplace bridge
  at $h = 0$ on the volume measure. Lifted from C1's / G2's private.
* `kappa3_volume_unfold` — `Threepoint.kappa3` at the volume measure
  unfolded into 5 `Laplace.gibbsExpectation` terms. Lifted from G2's
  private.
* `gibbsExpectation_affine` — `⟨a x + b⟩_t = a · ⟨x⟩_t + b`, given
  $Z \neq 0$ and integrability of the linear and constant pieces.
* `kappa3_volume_shifted_affine_eq_smul` — the headline identity.

## Strategy

The headline proof is direct: unfold both sides via
`kappa3_volume_unfold`, then for each of the seven `gibbsExpectation`
terms appearing in the unfold (φAB, φA, φB, AB, φ, A, B), expand the
integrand into a cubic polynomial in $x$ via `funext + ring` and
reduce via the I2 algebra (`gibbsExpectation_smul`,
`gibbsExpectation_add`, `gibbsExpectation_const`) to a linear
combination of the four moments $m_0 = 1$, $m_1$, $m_2$, $m_3$.
Final `ring` collects.

The cubic expansion is factored into a private helper
`gibbsExp_cubic_eq` that handles the `⟨a x³ + b x² + c x + d⟩`
decomposition once.
-/

namespace Laplace

open MeasureTheory

/-! ## Bridge: `Threepoint.gibbsExp` at $h = 0$ ↔ `Laplace.gibbsExpectation` -/

/-- For any potential `L`, perturbation direction `A`, observable `φ`, and
temperature `t`, `Threepoint.gibbsExp` against the Lebesgue measure with no
perturbation (`h = 0`) reduces to `Laplace.gibbsExpectation L t φ`.
This is the bridge between the perturbed-Gibbs API of the Threepoint
package and the unperturbed-Gibbs API of Laplace. -/
theorem threepoint_gibbsExp_volume_zero_eq
    (L A φ : ℝ → ℝ) (t : ℝ) :
    Threepoint.gibbsExp (volume : Measure ℝ) L A t 0 φ
      = Laplace.gibbsExpectation L t φ := by
  unfold Threepoint.gibbsExp Laplace.gibbsExpectation Laplace.partitionFunction
  simp only [zero_mul, add_zero]

/-! ## Unfold `Threepoint.kappa3` into Laplace expectations -/

/-- `Threepoint.kappa3` against the Lebesgue measure unfolds into a
sum of five `Laplace.gibbsExpectation` terms (independent of the
perturbation direction `A`, since at `h = 0` it doesn't enter the
integrand). -/
theorem kappa3_volume_unfold
    (L A φ B : ℝ → ℝ) (t : ℝ) :
    Threepoint.kappa3 (volume : Measure ℝ) L A t φ B
      = Laplace.gibbsExpectation L t (fun x : ℝ => φ x * A x * B x)
        - Laplace.gibbsExpectation L t (fun x : ℝ => φ x * A x)
          * Laplace.gibbsExpectation L t B
        - Laplace.gibbsExpectation L t (fun x : ℝ => φ x * B x)
          * Laplace.gibbsExpectation L t A
        - Laplace.gibbsExpectation L t (fun x : ℝ => A x * B x)
          * Laplace.gibbsExpectation L t φ
        + 2 * Laplace.gibbsExpectation L t φ
            * Laplace.gibbsExpectation L t A
            * Laplace.gibbsExpectation L t B := by
  unfold Threepoint.kappa3
  rw [threepoint_gibbsExp_volume_zero_eq, threepoint_gibbsExp_volume_zero_eq,
      threepoint_gibbsExp_volume_zero_eq, threepoint_gibbsExp_volume_zero_eq,
      threepoint_gibbsExp_volume_zero_eq, threepoint_gibbsExp_volume_zero_eq,
      threepoint_gibbsExp_volume_zero_eq]

/-! ## Affine-of-id Gibbs expectation -/

/-- Gibbs expectation of an affine observable in `id`:
`⟨a x + b⟩_t = a · ⟨x⟩_t + b`, provided `Z(t) ≠ 0` (so the constant
evaluates as itself) and integrability of the linear and constant
pieces (so the additive split via `gibbsExpectation_add` applies). -/
theorem gibbsExpectation_affine
    (L : ℝ → ℝ) (t : ℝ) (a b : ℝ)
    (hZ : partitionFunction L t ≠ 0)
    (h_int_x : Integrable (fun x : ℝ => x * Real.exp (-(t * L x))))
    (h_int_1 : Integrable (fun x : ℝ => Real.exp (-(t * L x)))) :
    gibbsExpectation L t (fun x : ℝ => a * x + b)
      = a * gibbsExpectation L t (fun x : ℝ => x) + b := by
  -- Recast the integrand `(a · x + b)` as `(fun x => a * x) x + (fun _ => b) x`.
  have h_int_a_x : Integrable (fun x : ℝ => (a * x) * Real.exp (-(t * L x))) := by
    have heq : (fun x : ℝ => (a * x) * Real.exp (-(t * L x)))
        = fun x : ℝ => a * (x * Real.exp (-(t * L x))) := by
      funext x; ring
    rw [heq]; exact h_int_x.const_mul a
  have h_int_b : Integrable (fun x : ℝ => b * Real.exp (-(t * L x))) :=
    h_int_1.const_mul b
  rw [show (fun x : ℝ => a * x + b)
        = fun x : ℝ => (fun y : ℝ => a * y) x + (fun _ : ℝ => b) x from rfl]
  rw [gibbsExpectation_add L t (fun y => a * y) (fun _ => b) h_int_a_x h_int_b]
  rw [gibbsExpectation_smul L t a (fun y => y), gibbsExpectation_const L t b hZ]

/-! ## Cubic-polynomial Gibbs expectation -/

/-- Gibbs expectation of a degree-3 polynomial in `x`:
`⟨a₃ x³ + a₂ x² + a₁ x + a₀⟩_t = a₃ m₃ + a₂ m₂ + a₁ m₁ + a₀`
where `mₖ := gibbsExpectation L t (fun x => xᵏ)`, given `Z ≠ 0` and
integrability of `xⁿ · exp(-tL)` for `n ∈ {0, 1, 2, 3}`. -/
private theorem gibbsExp_cubic_eq
    (L : ℝ → ℝ) (t : ℝ) (a₃ a₂ a₁ a₀ : ℝ)
    (hZ : partitionFunction L t ≠ 0)
    (h_int_1 : Integrable (fun x : ℝ => Real.exp (-(t * L x))))
    (h_int_x : Integrable (fun x : ℝ => x * Real.exp (-(t * L x))))
    (h_int_x2 : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-(t * L x))))
    (h_int_x3 : Integrable (fun x : ℝ => x ^ 3 * Real.exp (-(t * L x)))) :
    gibbsExpectation L t (fun x : ℝ => a₃ * x ^ 3 + a₂ * x ^ 2 + a₁ * x + a₀)
      = a₃ * gibbsExpectation L t (fun x : ℝ => x ^ 3)
        + a₂ * gibbsExpectation L t (fun x : ℝ => x ^ 2)
        + a₁ * gibbsExpectation L t (fun x : ℝ => x)
        + a₀ := by
  -- Integrability of each scalar-multiplied piece.
  have h_int_a3x3 : Integrable
      (fun x : ℝ => (a₃ * x ^ 3) * Real.exp (-(t * L x))) := by
    have heq : (fun x : ℝ => (a₃ * x ^ 3) * Real.exp (-(t * L x)))
        = fun x : ℝ => a₃ * (x ^ 3 * Real.exp (-(t * L x))) := by
      funext x; ring
    rw [heq]; exact h_int_x3.const_mul a₃
  have h_int_a2x2 : Integrable
      (fun x : ℝ => (a₂ * x ^ 2) * Real.exp (-(t * L x))) := by
    have heq : (fun x : ℝ => (a₂ * x ^ 2) * Real.exp (-(t * L x)))
        = fun x : ℝ => a₂ * (x ^ 2 * Real.exp (-(t * L x))) := by
      funext x; ring
    rw [heq]; exact h_int_x2.const_mul a₂
  have h_int_a1x : Integrable
      (fun x : ℝ => (a₁ * x) * Real.exp (-(t * L x))) := by
    have heq : (fun x : ℝ => (a₁ * x) * Real.exp (-(t * L x)))
        = fun x : ℝ => a₁ * (x * Real.exp (-(t * L x))) := by
      funext x; ring
    rw [heq]; exact h_int_x.const_mul a₁
  have h_int_a0 : Integrable (fun x : ℝ => a₀ * Real.exp (-(t * L x))) :=
    h_int_1.const_mul a₀
  -- Integrability of cumulative tails.
  have h_int_a3a2 : Integrable
      (fun x : ℝ => ((a₃ * x ^ 3) + (a₂ * x ^ 2)) * Real.exp (-(t * L x))) := by
    have heq : (fun x : ℝ => ((a₃ * x ^ 3) + (a₂ * x ^ 2)) * Real.exp (-(t * L x)))
        = fun x : ℝ => (a₃ * x ^ 3) * Real.exp (-(t * L x))
                       + (a₂ * x ^ 2) * Real.exp (-(t * L x)) := by
      funext x; ring
    rw [heq]; exact h_int_a3x3.add h_int_a2x2
  have h_int_a3a2a1 : Integrable
      (fun x : ℝ => ((a₃ * x ^ 3) + (a₂ * x ^ 2) + (a₁ * x)) * Real.exp (-(t * L x))) := by
    have heq : (fun x : ℝ => ((a₃ * x ^ 3) + (a₂ * x ^ 2) + (a₁ * x))
                  * Real.exp (-(t * L x)))
        = fun x : ℝ => ((a₃ * x ^ 3) + (a₂ * x ^ 2)) * Real.exp (-(t * L x))
                       + (a₁ * x) * Real.exp (-(t * L x)) := by
      funext x; ring
    rw [heq]; exact h_int_a3a2.add h_int_a1x
  -- Split via gibbsExpectation_add three times.
  rw [show (fun x : ℝ => a₃ * x ^ 3 + a₂ * x ^ 2 + a₁ * x + a₀)
        = (fun x : ℝ => (fun y : ℝ => a₃ * y ^ 3 + a₂ * y ^ 2 + a₁ * y) x
                        + (fun _ : ℝ => a₀) x) from rfl]
  rw [gibbsExpectation_add L t
        (fun y => a₃ * y ^ 3 + a₂ * y ^ 2 + a₁ * y) (fun _ => a₀)
        h_int_a3a2a1 h_int_a0]
  rw [show (fun y : ℝ => a₃ * y ^ 3 + a₂ * y ^ 2 + a₁ * y)
        = fun y : ℝ => (fun z : ℝ => a₃ * z ^ 3 + a₂ * z ^ 2) y
                       + (fun z : ℝ => a₁ * z) y from rfl]
  rw [gibbsExpectation_add L t
        (fun z => a₃ * z ^ 3 + a₂ * z ^ 2) (fun z => a₁ * z)
        h_int_a3a2 h_int_a1x]
  rw [show (fun z : ℝ => a₃ * z ^ 3 + a₂ * z ^ 2)
        = fun z : ℝ => (fun w : ℝ => a₃ * w ^ 3) z
                       + (fun w : ℝ => a₂ * w ^ 2) z from rfl]
  rw [gibbsExpectation_add L t
        (fun w => a₃ * w ^ 3) (fun w => a₂ * w ^ 2)
        h_int_a3x3 h_int_a2x2]
  rw [gibbsExpectation_smul L t a₃ (fun w => w ^ 3),
      gibbsExpectation_smul L t a₂ (fun w => w ^ 2),
      gibbsExpectation_smul L t a₁ (fun y => y),
      gibbsExpectation_const L t a₀ hZ]

/-! ## The headline factored identity -/

/-- **Factored $\kappa_3$ identity for shifted-affine observables
(potential-agnostic).**

For any 1D Gibbs measure with potential `L` at temperature `t`, with
$Z(t) \neq 0$ and integrability of $x^n \cdot \exp(-tL)$ for
$n \in \{0, 1, 2, 3\}$, and any constants
$a_1, a_2, a_3, b_1, b_2, b_3 \in \mathbb{R}$:
$$
  \kappa_3(\mu_{\mathrm{vol}}, L,\;a_2 x + b_2,\;t,\;a_1 x + b_1,\;a_3 x + b_3)
  \;=\; a_1 a_2 a_3 \cdot \kappa_3(\mu_{\mathrm{vol}}, L,\;x,\;t,\;x,\;x).
$$
The constants $b_i$ drop by translation invariance of cumulants; the
multipliers $a_i$ pull through by trilinearity.

The C1 vanishing for the harmonic case and the G2/G2+ asymptotic for
the anharmonic case become 5-line specialisations: combine this
identity with the potential-specific value of the $\kappa_3(x, x, x)$
right-hand side. -/
theorem kappa3_volume_shifted_affine_eq_smul
    (L : ℝ → ℝ) {t : ℝ}
    (hZ : partitionFunction L t ≠ 0)
    (h_int_1 : Integrable (fun x : ℝ => Real.exp (-(t * L x))))
    (h_int_x : Integrable (fun x : ℝ => x * Real.exp (-(t * L x))))
    (h_int_x2 : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-(t * L x))))
    (h_int_x3 : Integrable (fun x : ℝ => x ^ 3 * Real.exp (-(t * L x))))
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) :
    Threepoint.kappa3 (volume : Measure ℝ) L
        (fun x : ℝ => a₂ * x + b₂) t
        (fun x : ℝ => a₁ * x + b₁) (fun x : ℝ => a₃ * x + b₃)
      = a₁ * a₂ * a₃ * Threepoint.kappa3 (volume : Measure ℝ) L
          (fun x : ℝ => x) t (fun x : ℝ => x) (fun x : ℝ => x) := by
  -- Unfold both sides via `kappa3_volume_unfold`.
  rw [kappa3_volume_unfold, kappa3_volume_unfold]
  -- For each of the 7 integrand terms, expand the polynomial product
  -- into `a₃ x³ + a₂ x² + a₁ x + a₀` form, then apply `gibbsExp_cubic_eq`.
  -- Define moment shorthands.
  set m₁ : ℝ := gibbsExpectation L t (fun x : ℝ => x)
  set m₂ : ℝ := gibbsExpectation L t (fun x : ℝ => x ^ 2) with hm2
  set m₃ : ℝ := gibbsExpectation L t (fun x : ℝ => x ^ 3) with hm3
  -- Term: ⟨(a₁x+b₁)(a₂x+b₂)(a₃x+b₃)⟩.
  have h_φAB : gibbsExpectation L t
        (fun x : ℝ => (a₁ * x + b₁) * (a₂ * x + b₂) * (a₃ * x + b₃))
      = (a₁ * a₂ * a₃) * m₃
        + (a₁ * a₂ * b₃ + a₁ * b₂ * a₃ + b₁ * a₂ * a₃) * m₂
        + (a₁ * b₂ * b₃ + b₁ * a₂ * b₃ + b₁ * b₂ * a₃) * m₁
        + b₁ * b₂ * b₃ := by
    have heq : (fun x : ℝ => (a₁ * x + b₁) * (a₂ * x + b₂) * (a₃ * x + b₃))
        = fun x : ℝ => (a₁ * a₂ * a₃) * x ^ 3
            + (a₁ * a₂ * b₃ + a₁ * b₂ * a₃ + b₁ * a₂ * a₃) * x ^ 2
            + (a₁ * b₂ * b₃ + b₁ * a₂ * b₃ + b₁ * b₂ * a₃) * x
            + b₁ * b₂ * b₃ := by funext x; ring
    rw [heq]
    exact gibbsExp_cubic_eq L t (a₁ * a₂ * a₃)
      (a₁ * a₂ * b₃ + a₁ * b₂ * a₃ + b₁ * a₂ * a₃)
      (a₁ * b₂ * b₃ + b₁ * a₂ * b₃ + b₁ * b₂ * a₃)
      (b₁ * b₂ * b₃) hZ h_int_1 h_int_x h_int_x2 h_int_x3
  -- Term: ⟨(a₁x+b₁)(a₂x+b₂)⟩ — quadratic, expressed as cubic with leading 0.
  have h_φA : gibbsExpectation L t
        (fun x : ℝ => (a₁ * x + b₁) * (a₂ * x + b₂))
      = (a₁ * a₂) * m₂ + (a₁ * b₂ + b₁ * a₂) * m₁ + b₁ * b₂ := by
    have heq : (fun x : ℝ => (a₁ * x + b₁) * (a₂ * x + b₂))
        = fun x : ℝ => 0 * x ^ 3 + (a₁ * a₂) * x ^ 2
            + (a₁ * b₂ + b₁ * a₂) * x + b₁ * b₂ := by funext x; ring
    rw [heq]
    rw [gibbsExp_cubic_eq L t 0 (a₁ * a₂) (a₁ * b₂ + b₁ * a₂) (b₁ * b₂)
        hZ h_int_1 h_int_x h_int_x2 h_int_x3]
    ring
  -- Term: ⟨(a₁x+b₁)(a₃x+b₃)⟩.
  have h_φB : gibbsExpectation L t
        (fun x : ℝ => (a₁ * x + b₁) * (a₃ * x + b₃))
      = (a₁ * a₃) * m₂ + (a₁ * b₃ + b₁ * a₃) * m₁ + b₁ * b₃ := by
    have heq : (fun x : ℝ => (a₁ * x + b₁) * (a₃ * x + b₃))
        = fun x : ℝ => 0 * x ^ 3 + (a₁ * a₃) * x ^ 2
            + (a₁ * b₃ + b₁ * a₃) * x + b₁ * b₃ := by funext x; ring
    rw [heq]
    rw [gibbsExp_cubic_eq L t 0 (a₁ * a₃) (a₁ * b₃ + b₁ * a₃) (b₁ * b₃)
        hZ h_int_1 h_int_x h_int_x2 h_int_x3]
    ring
  -- Term: ⟨(a₂x+b₂)(a₃x+b₃)⟩.
  have h_AB : gibbsExpectation L t
        (fun x : ℝ => (a₂ * x + b₂) * (a₃ * x + b₃))
      = (a₂ * a₃) * m₂ + (a₂ * b₃ + b₂ * a₃) * m₁ + b₂ * b₃ := by
    have heq : (fun x : ℝ => (a₂ * x + b₂) * (a₃ * x + b₃))
        = fun x : ℝ => 0 * x ^ 3 + (a₂ * a₃) * x ^ 2
            + (a₂ * b₃ + b₂ * a₃) * x + b₂ * b₃ := by funext x; ring
    rw [heq]
    rw [gibbsExp_cubic_eq L t 0 (a₂ * a₃) (a₂ * b₃ + b₂ * a₃) (b₂ * b₃)
        hZ h_int_1 h_int_x h_int_x2 h_int_x3]
    ring
  -- Linear terms: ⟨a_i x + b_i⟩.
  have h_φ : gibbsExpectation L t (fun x : ℝ => a₁ * x + b₁)
      = a₁ * m₁ + b₁ :=
    gibbsExpectation_affine L t a₁ b₁ hZ h_int_x h_int_1
  have h_A : gibbsExpectation L t (fun x : ℝ => a₂ * x + b₂)
      = a₂ * m₁ + b₂ :=
    gibbsExpectation_affine L t a₂ b₂ hZ h_int_x h_int_1
  have h_B : gibbsExpectation L t (fun x : ℝ => a₃ * x + b₃)
      = a₃ * m₁ + b₃ :=
    gibbsExpectation_affine L t a₃ b₃ hZ h_int_x h_int_1
  -- RHS: ⟨x · x · x⟩, ⟨x · x⟩, ⟨x · x⟩, ⟨x · x⟩, ⟨x⟩, ⟨x⟩, ⟨x⟩.
  have h_xxx : gibbsExpectation L t (fun x : ℝ => x * x * x) = m₃ := by
    have heq : (fun x : ℝ => x * x * x) = fun x : ℝ => x ^ 3 := by
      funext x; ring
    rw [heq, hm3]
  have h_xx_left : gibbsExpectation L t (fun x : ℝ => x * x) = m₂ := by
    have heq : (fun x : ℝ => x * x) = fun x : ℝ => x ^ 2 := by
      funext x; ring
    rw [heq, hm2]
  -- Substitute and ring.
  rw [h_φAB, h_φA, h_φB, h_AB, h_φ, h_A, h_B, h_xxx, h_xx_left]
  ring

end Laplace
