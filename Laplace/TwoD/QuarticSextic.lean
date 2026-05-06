import Laplace.Gibbs
import Laplace.OneD.Quartic
import Laplace.OneD.Sextic
import Laplace.TwoD.Basic
import Laplace.TwoD.AddSeparable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod

/-!
# 2D quartic-sextic Gibbs covariance

This file extends the seabed's degenerate-case excursions (1D pure quartic
and 1D sextic) to the doubly-degenerate 2D potential

  `L(x, y) = x⁴/24 + y⁶/720`

in which both directions are degenerate (`L_xx(0) = L_yy(0) = 0`) but with
different orders of vanishing — quartic in `x` (rate `t^{-1/2}`) and sextic
in `y` (rate `t^{-1/3}`). The Gibbs density factorises as
`exp(−tL(x,y)) = exp(−tx⁴/24) · exp(−ty⁶/720)`, so the 2D measure is the
product of the 1D quartic and 1D sextic Gibbs measures.

The headline result is `cov_affine_quarticSextic`: for affine observables
`φ(x,y) = a₁ x + a₂ y + c`, `ψ(x,y) = b₁ x + b₂ y + d`, and `t > 0`,
$$
  \mathrm{Cov}_t[\varphi, \psi]
  = a_1 b_1 \cdot \sqrt{24/t} \cdot \Gamma(3/4)/\Gamma(1/4)
    + a_2 b_2 \cdot (720/t)^{1/3} \cdot \Gamma(1/2)/\Gamma(1/6).
$$
The two contributions decay at *different* rates: the quartic side at
`t^{-1/2}` and the sextic side at `t^{-1/3}`. There is no `t^{-5/6}`
cross term — under separable Gibbs, the mixed covariances vanish exactly
(`Laplace.TwoD.gibbsCov_addSeparable_fst_snd_eq_zero` from Tide 12).

## Architecture

Built directly on the AddSeparable abstraction (Tide 12) and the cleanup
refactor (Tide 13). The new infrastructure here is just:
* a fresh `quarticSexticPotential : ℝ × ℝ → ℝ`,
* a `[simp]` bridge identifying it with `addSeparable quarticPotential sexticPotential`,
* its Boltzmann factor decomposition (corollary of the bridge),
* partition function and mixed-monomial moment factorisations (one-line
  applications of the AddSeparable lemmas),
* moment-table lemmas (`gibbsExpectation_fst`, `_snd`, `_fst_mul_snd`,
  `_fst_sq`, `_snd_sq`),
* the headline `cov_affine_quarticSextic`.

Atom integrability comes via `integrable_separable_addSeparable` (Tide 14)
applied at `Laplace.OneD.quartic_integrable_pow_pot` and
`Laplace.OneD.sextic_integrable_pow_pot`.

## Tide-step provenance

Tide 14 (combined: integrability promotion + A4 mixed-power moments + A2
quartic-sextic), `tide/quartic-sextic` chained off `tide/twod-cleanup`. See
`sri/projects/primer/tide-log/2026-05-06-tide-quartic-sextic.md`.
-/

open Real MeasureTheory Set

namespace Laplace.TwoD

/-! ## The quartic-sextic potential -/

/-- The 2D quartic-sextic potential `L(x, y) = x⁴/24 + y⁶/720`. -/
noncomputable def quarticSexticPotential : ℝ × ℝ → ℝ :=
  fun z => z.1 ^ 4 / 24 + z.2 ^ 6 / 720

@[simp] lemma quarticSexticPotential_apply (z : ℝ × ℝ) :
    quarticSexticPotential z = z.1 ^ 4 / 24 + z.2 ^ 6 / 720 := rfl

/-! ## Bridge to the additively-separable abstraction -/

/-- The quartic-sextic 2D potential is an additively-separable potential
with `U = quartic` and `V = sextic`. -/
@[simp] lemma quarticSexticPotential_eq_addSeparable :
    quarticSexticPotential =
      addSeparable Laplace.OneD.quarticPotential Laplace.OneD.sexticPotential := by
  funext z
  simp only [quarticSexticPotential_apply, addSeparable_apply,
    Laplace.OneD.quarticPotential_apply, Laplace.OneD.sexticPotential_apply]

/-- The Boltzmann factor for `L(x,y) = x⁴/24 + y⁶/720` factorises as a product
of a quartic factor in `x` and a sextic factor in `y`. Corollary of
`exp_neg_t_addSeparable_eq_mul` via the bridge. -/
lemma exp_neg_t_quarticSextic_eq_mul (t : ℝ) (z : ℝ × ℝ) :
    Real.exp (-(t * quarticSexticPotential z)) =
      Real.exp (-(t * Laplace.OneD.quarticPotential z.1)) *
      Real.exp (-(t * Laplace.OneD.sexticPotential z.2)) := by
  rw [quarticSexticPotential_eq_addSeparable]
  exact exp_neg_t_addSeparable_eq_mul _ _ t z

/-! ## Partition function factorisation -/

/-- The 2D partition function factorises into the product of the 1D quartic
and 1D sextic partition functions. -/
theorem partitionFunction_factor (t : ℝ) :
    partitionFunction quarticSexticPotential t =
      Laplace.partitionFunction Laplace.OneD.quarticPotential t *
      Laplace.partitionFunction Laplace.OneD.sexticPotential t := by
  rw [quarticSexticPotential_eq_addSeparable]
  exact partitionFunction_addSeparable_factor _ _ _

/-- Closed form for the partition function:
`Z_2D(t) = (1/2)(24/t)^{1/4} Γ(1/4) · (1/3)(720/t)^{1/6} Γ(1/6)`. -/
theorem partitionFunction_closed_form {t : ℝ} (ht : 0 < t) :
    partitionFunction quarticSexticPotential t =
      ((1/2) * (24/t) ^ ((1 : ℝ)/4) * Real.Gamma ((1 : ℝ)/4)) *
      ((1/3) * (720/t) ^ ((1 : ℝ)/6) * Real.Gamma ((1 : ℝ)/6)) := by
  rw [partitionFunction_factor, Laplace.OneD.quartic_partition ht,
      Laplace.OneD.sextic_partition ht]

/-- Positivity of the 2D partition function. -/
theorem partitionFunction_pos {t : ℝ} (ht : 0 < t) :
    0 < partitionFunction quarticSexticPotential t := by
  rw [partitionFunction_factor]
  exact mul_pos (Laplace.OneD.quartic_partition_pos ht)
    (Laplace.OneD.sextic_partition_pos ht)

/-! ## Mixed-monomial moment factorisation -/

/-- The 2D moment integral of a separable monomial `z.1^m · z.2^n` against
the quartic-sextic Gibbs weight factorises into the product of 1D moment
integrals. Application of `integral_separable_addSeparable` at
`f = fun x ↦ x^m`, `g = fun y ↦ y^n` via the bridge. -/
theorem integral_pow_pow_factor (t : ℝ) (m n : ℕ) :
    (∫ z : ℝ × ℝ, z.1 ^ m * z.2 ^ n *
        Real.exp (-(t * quarticSexticPotential z))) =
      (∫ x : ℝ, x ^ m * Real.exp (-(t * Laplace.OneD.quarticPotential x))) *
      (∫ y : ℝ, y ^ n * Real.exp (-(t * Laplace.OneD.sexticPotential y))) := by
  simp only [quarticSexticPotential_eq_addSeparable]
  exact integral_separable_addSeparable _ _ _ (fun x => x ^ m) (fun y => y ^ n)

/-! ## Specialised moments needed for affine covariance -/

/-- `⟨1⟩_t = 1` (with `Z_t > 0`). -/
lemma gibbsExpectation_one {t : ℝ} (ht : 0 < t) :
    gibbsExpectation quarticSexticPotential t (fun _ => 1) = 1 := by
  unfold gibbsExpectation
  have hZ : partitionFunction quarticSexticPotential t ≠ 0 :=
    ne_of_gt (partitionFunction_pos ht)
  simp only [one_mul]
  exact div_self hZ

/-- The first coordinate has zero mean: `⟨z.1⟩_t = 0`. -/
theorem gibbsExpectation_fst {t : ℝ} (_ht : 0 < t) :
    gibbsExpectation quarticSexticPotential t (fun z => z.1) = 0 := by
  unfold gibbsExpectation
  have hnum :
      (∫ z : ℝ × ℝ, z.1 * Real.exp (-(t * quarticSexticPotential z))) = 0 := by
    have h := integral_pow_pow_factor t 1 0
    simp only [pow_one, pow_zero, one_mul, mul_one] at h
    rw [h]
    have hquartic_zero :
        (∫ x : ℝ, x * Real.exp (-(t * Laplace.OneD.quarticPotential x))) = 0 := by
      have heq : (fun x : ℝ => x * Real.exp (-(t * Laplace.OneD.quarticPotential x))) =
                 (fun x : ℝ => x ^ (2 * 0 + 1) * Real.exp (-(t * x ^ 4 / 24))) := by
        ext x
        rw [Laplace.OneD.quarticPotential_apply,
            show (2 * 0 + 1 : ℕ) = 1 from rfl, pow_one]
        congr 2
        ring
      rw [heq, Laplace.OneD.quartic_moment_odd 0 t]
    rw [hquartic_zero, zero_mul]
  rw [hnum, zero_div]

/-- The second coordinate has zero mean: `⟨z.2⟩_t = 0`. -/
theorem gibbsExpectation_snd {t : ℝ} (_ht : 0 < t) :
    gibbsExpectation quarticSexticPotential t (fun z => z.2) = 0 := by
  unfold gibbsExpectation
  have hnum :
      (∫ z : ℝ × ℝ, z.2 * Real.exp (-(t * quarticSexticPotential z))) = 0 := by
    have h := integral_pow_pow_factor t 0 1
    simp only [pow_zero, pow_one, one_mul] at h
    rw [h]
    have hsextic_zero :
        (∫ y : ℝ, y * Real.exp (-(t * Laplace.OneD.sexticPotential y))) = 0 := by
      have heq : (fun y : ℝ => y * Real.exp (-(t * Laplace.OneD.sexticPotential y))) =
                 (fun y : ℝ => y ^ (2 * 0 + 1) * Real.exp (-(t * y ^ 6 / 720))) := by
        ext y
        rw [Laplace.OneD.sexticPotential_apply,
            show (2 * 0 + 1 : ℕ) = 1 from rfl, pow_one]
        congr 2
        ring
      rw [heq, Laplace.OneD.sextic_moment_odd 0 t]
    rw [hsextic_zero, mul_zero]
  rw [hnum, zero_div]

/-- `⟨z.1 · z.2⟩_t = 0` (mixed first moment vanishes by independence + parity). -/
theorem gibbsExpectation_fst_mul_snd {t : ℝ} (_ht : 0 < t) :
    gibbsExpectation quarticSexticPotential t (fun z => z.1 * z.2) = 0 := by
  unfold gibbsExpectation
  have hnum :
      (∫ z : ℝ × ℝ, z.1 * z.2 *
          Real.exp (-(t * quarticSexticPotential z))) = 0 := by
    have h := integral_pow_pow_factor t 1 1
    simp only [pow_one] at h
    rw [h]
    have hsextic_zero :
        (∫ y : ℝ, y * Real.exp (-(t * Laplace.OneD.sexticPotential y))) = 0 := by
      have heq : (fun y : ℝ => y * Real.exp (-(t * Laplace.OneD.sexticPotential y))) =
                 (fun y : ℝ => y ^ (2 * 0 + 1) * Real.exp (-(t * y ^ 6 / 720))) := by
        ext y
        rw [Laplace.OneD.sexticPotential_apply,
            show (2 * 0 + 1 : ℕ) = 1 from rfl, pow_one]
        congr 2
        ring
      rw [heq, Laplace.OneD.sextic_moment_odd 0 t]
    rw [hsextic_zero, mul_zero]
  rw [hnum, zero_div]

/-- `⟨z.1²⟩_t = √(24/t) · Γ(3/4) / Γ(1/4)` (quartic-direction second moment). -/
theorem gibbsExpectation_fst_sq {t : ℝ} (ht : 0 < t) :
    gibbsExpectation quarticSexticPotential t (fun z => z.1 ^ 2) =
      Real.sqrt (24 / t) * Real.Gamma ((3 : ℝ) / 4) / Real.Gamma ((1 : ℝ) / 4) := by
  unfold gibbsExpectation
  have h := integral_pow_pow_factor t 2 0
  simp only [pow_zero, one_mul, mul_one] at h
  rw [h, partitionFunction_factor]
  have hZs_pos := Laplace.OneD.sextic_partition_pos ht
  have hZs_ne : Laplace.partitionFunction Laplace.OneD.sexticPotential t ≠ 0 :=
    ne_of_gt hZs_pos
  -- Convert the sextic 1D integral to the literal `Laplace.partitionFunction` symbol.
  rw [show (∫ y : ℝ, Real.exp (-(t * Laplace.OneD.sexticPotential y))) =
        Laplace.partitionFunction Laplace.OneD.sexticPotential t from rfl]
  -- Cancel Z_sextic from numerator and denominator: (a · c) / (b · c) = a / b.
  rw [mul_div_mul_right _ _ hZs_ne]
  -- Goal: (∫ x² · exp(-tQ_quartic)) / Z_quartic = sqrt(24/t)·Γ(3/4)/Γ(1/4).
  exact Laplace.OneD.quartic_expected_value_sq ht

/-- `⟨z.2²⟩_t = (720/t)^{1/3} · Γ(1/2) / Γ(1/6)` (sextic-direction second moment). -/
theorem gibbsExpectation_snd_sq {t : ℝ} (ht : 0 < t) :
    gibbsExpectation quarticSexticPotential t (fun z => z.2 ^ 2) =
      (720/t) ^ ((1 : ℝ) / 3) * Real.Gamma ((1 : ℝ) / 2) / Real.Gamma ((1 : ℝ) / 6) := by
  unfold gibbsExpectation
  have h := integral_pow_pow_factor t 0 2
  simp only [pow_zero, one_mul] at h
  rw [h, partitionFunction_factor]
  have hZq_pos := Laplace.OneD.quartic_partition_pos ht
  have hZq_ne : Laplace.partitionFunction Laplace.OneD.quarticPotential t ≠ 0 :=
    ne_of_gt hZq_pos
  -- Convert the quartic 1D integral to the literal `Laplace.partitionFunction` symbol.
  rw [show (∫ x : ℝ, Real.exp (-(t * Laplace.OneD.quarticPotential x))) =
        Laplace.partitionFunction Laplace.OneD.quarticPotential t from rfl]
  -- Cancel Z_quartic from numerator and denominator: (c · a) / (c · b) = a / b.
  rw [mul_div_mul_left _ _ hZq_ne]
  -- Goal: (∫ y² · exp(-tQ_sextic)) / Z_sextic = sextic_expected_value_sq.
  exact Laplace.OneD.sextic_expected_value_sq ht

/-! ## Headline theorem: affine covariance -/

/-- **Affine covariance against the 2D quartic-sextic Gibbs measure.**
For `L(x, y) = x⁴/24 + y⁶/720` with `t > 0` and affine observables
`φ(x,y) = a₁ x + a₂ y + c`, `ψ(x,y) = b₁ x + b₂ y + d`,

  `Cov_t[φ, ψ] = a₁ b₁ · √(24/t) · Γ(3/4)/Γ(1/4)
                 + a₂ b₂ · (720/t)^{1/3} · Γ(1/2)/Γ(1/6)`.

Both contributions decay, but at different rates: the quartic direction at
`t^{-1/2}` and the sextic direction at `t^{-1/3}`. The constants `c, d` drop
out (covariance is shift-invariant in each argument). The cross terms
`a₁ b₂` and `a₂ b₁` vanish by `gibbsCov_addSeparable_fst_snd_eq_zero` (or
equivalently because both 1D potentials have parity-vanishing means and
the joint mixed moment factorises). -/
theorem cov_affine_quarticSextic {t : ℝ} (ht : 0 < t)
    (a₁ a₂ b₁ b₂ c d : ℝ) :
    gibbsCov quarticSexticPotential t
        (fun z : ℝ × ℝ => a₁ * z.1 + a₂ * z.2 + c)
        (fun z : ℝ × ℝ => b₁ * z.1 + b₂ * z.2 + d) =
      a₁ * b₁ * Real.sqrt (24 / t) * Real.Gamma ((3 : ℝ) / 4) / Real.Gamma ((1 : ℝ) / 4) +
      a₂ * b₂ * (720/t) ^ ((1 : ℝ) / 3) * Real.Gamma ((1 : ℝ) / 2) / Real.Gamma ((1 : ℝ) / 6) := by
  have hZpos := partitionFunction_pos ht
  have hZne : partitionFunction quarticSexticPotential t ≠ 0 := ne_of_gt hZpos
  -- 2D atom integrabilities via the generic helper from AddSeparable.
  have hI00 : Integrable
      (fun z : ℝ × ℝ => z.1 ^ 0 * z.2 ^ 0 *
        Real.exp (-(t * quarticSexticPotential z))) := by
    simp only [quarticSexticPotential_eq_addSeparable]
    exact integrable_separable_addSeparable
      (f := fun x => x ^ 0) (g := fun y => y ^ 0)
      (Laplace.OneD.quartic_integrable_pow_pot 0 ht)
      (Laplace.OneD.sextic_integrable_pow_pot 0 ht)
  have hI10 : Integrable
      (fun z : ℝ × ℝ => z.1 ^ 1 * z.2 ^ 0 *
        Real.exp (-(t * quarticSexticPotential z))) := by
    simp only [quarticSexticPotential_eq_addSeparable]
    exact integrable_separable_addSeparable
      (f := fun x => x ^ 1) (g := fun y => y ^ 0)
      (Laplace.OneD.quartic_integrable_pow_pot 1 ht)
      (Laplace.OneD.sextic_integrable_pow_pot 0 ht)
  have hI01 : Integrable
      (fun z : ℝ × ℝ => z.1 ^ 0 * z.2 ^ 1 *
        Real.exp (-(t * quarticSexticPotential z))) := by
    simp only [quarticSexticPotential_eq_addSeparable]
    exact integrable_separable_addSeparable
      (f := fun x => x ^ 0) (g := fun y => y ^ 1)
      (Laplace.OneD.quartic_integrable_pow_pot 0 ht)
      (Laplace.OneD.sextic_integrable_pow_pot 1 ht)
  have hI20 : Integrable
      (fun z : ℝ × ℝ => z.1 ^ 2 * z.2 ^ 0 *
        Real.exp (-(t * quarticSexticPotential z))) := by
    simp only [quarticSexticPotential_eq_addSeparable]
    exact integrable_separable_addSeparable
      (f := fun x => x ^ 2) (g := fun y => y ^ 0)
      (Laplace.OneD.quartic_integrable_pow_pot 2 ht)
      (Laplace.OneD.sextic_integrable_pow_pot 0 ht)
  have hI02 : Integrable
      (fun z : ℝ × ℝ => z.1 ^ 0 * z.2 ^ 2 *
        Real.exp (-(t * quarticSexticPotential z))) := by
    simp only [quarticSexticPotential_eq_addSeparable]
    exact integrable_separable_addSeparable
      (f := fun x => x ^ 0) (g := fun y => y ^ 2)
      (Laplace.OneD.quartic_integrable_pow_pot 0 ht)
      (Laplace.OneD.sextic_integrable_pow_pot 2 ht)
  have hI11 : Integrable
      (fun z : ℝ × ℝ => z.1 ^ 1 * z.2 ^ 1 *
        Real.exp (-(t * quarticSexticPotential z))) := by
    simp only [quarticSexticPotential_eq_addSeparable]
    exact integrable_separable_addSeparable
      (f := fun x => x ^ 1) (g := fun y => y ^ 1)
      (Laplace.OneD.quartic_integrable_pow_pot 1 ht)
      (Laplace.OneD.sextic_integrable_pow_pot 1 ht)
  -- Strip the trivial `z.1^0 * z.2^0 = 1` factors so each is in canonical form.
  have hI00' : Integrable
      (fun z : ℝ × ℝ => Real.exp (-(t * quarticSexticPotential z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 0 * z.2 ^ 0 * Real.exp (-(t * quarticSexticPotential z))) =
               (fun z : ℝ × ℝ => Real.exp (-(t * quarticSexticPotential z))) := by
      ext; simp
    rwa [heq] at hI00
  have hI10' : Integrable
      (fun z : ℝ × ℝ => z.1 * Real.exp (-(t * quarticSexticPotential z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 1 * z.2 ^ 0 * Real.exp (-(t * quarticSexticPotential z))) =
               (fun z : ℝ × ℝ => z.1 * Real.exp (-(t * quarticSexticPotential z))) := by
      ext; simp
    rwa [heq] at hI10
  have hI01' : Integrable
      (fun z : ℝ × ℝ => z.2 * Real.exp (-(t * quarticSexticPotential z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 0 * z.2 ^ 1 * Real.exp (-(t * quarticSexticPotential z))) =
               (fun z : ℝ × ℝ => z.2 * Real.exp (-(t * quarticSexticPotential z))) := by
      ext; simp
    rwa [heq] at hI01
  have hI20' : Integrable
      (fun z : ℝ × ℝ => z.1 ^ 2 * Real.exp (-(t * quarticSexticPotential z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 2 * z.2 ^ 0 * Real.exp (-(t * quarticSexticPotential z))) =
               (fun z : ℝ × ℝ => z.1 ^ 2 * Real.exp (-(t * quarticSexticPotential z))) := by
      ext; simp
    rwa [heq] at hI20
  have hI02' : Integrable
      (fun z : ℝ × ℝ => z.2 ^ 2 * Real.exp (-(t * quarticSexticPotential z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 0 * z.2 ^ 2 * Real.exp (-(t * quarticSexticPotential z))) =
               (fun z : ℝ × ℝ => z.2 ^ 2 * Real.exp (-(t * quarticSexticPotential z))) := by
      ext; simp
    rwa [heq] at hI02
  have hI11' : Integrable
      (fun z : ℝ × ℝ => z.1 * z.2 * Real.exp (-(t * quarticSexticPotential z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 1 * z.2 ^ 1 * Real.exp (-(t * quarticSexticPotential z))) =
               (fun z : ℝ × ℝ => z.1 * z.2 * Real.exp (-(t * quarticSexticPotential z))) := by
      ext; simp
    rwa [heq] at hI11
  -- Linearity for affine observables: ⟨p₁ z.1 + p₂ z.2 + q⟩ = q (since means vanish).
  have hphi_aff : ∀ p₁ p₂ q : ℝ,
      gibbsExpectation quarticSexticPotential t
          (fun z => p₁ * z.1 + p₂ * z.2 + q) = q := by
    intro p₁ p₂ q
    unfold gibbsExpectation
    rw [show (fun z : ℝ × ℝ =>
              (p₁ * z.1 + p₂ * z.2 + q) *
              Real.exp (-(t * quarticSexticPotential z))) =
          (fun z : ℝ × ℝ =>
              p₁ * (z.1 * Real.exp (-(t * quarticSexticPotential z))) +
              p₂ * (z.2 * Real.exp (-(t * quarticSexticPotential z))) +
              q * Real.exp (-(t * quarticSexticPotential z))) from by
        funext z; ring]
    have h12 : Integrable (fun z : ℝ × ℝ =>
                p₁ * (z.1 * Real.exp (-(t * quarticSexticPotential z))) +
                p₂ * (z.2 * Real.exp (-(t * quarticSexticPotential z)))) :=
      (hI10'.const_mul p₁).add (hI01'.const_mul p₂)
    rw [MeasureTheory.integral_add h12 (hI00'.const_mul q)]
    rw [MeasureTheory.integral_add (hI10'.const_mul p₁) (hI01'.const_mul p₂)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
    have hMx : (∫ z : ℝ × ℝ, z.1 * Real.exp (-(t * quarticSexticPotential z))) = 0 := by
      have := gibbsExpectation_fst ht
      unfold gibbsExpectation at this
      exact (div_eq_zero_iff.mp this).resolve_right hZne
    have hMy : (∫ z : ℝ × ℝ, z.2 * Real.exp (-(t * quarticSexticPotential z))) = 0 := by
      have := gibbsExpectation_snd ht
      unfold gibbsExpectation at this
      exact (div_eq_zero_iff.mp this).resolve_right hZne
    rw [hMx, hMy,
        show (∫ z : ℝ × ℝ, Real.exp (-(t * quarticSexticPotential z))) =
          partitionFunction quarticSexticPotential t from rfl]
    field_simp
    ring
  have hphi : gibbsExpectation quarticSexticPotential t
      (fun z => a₁ * z.1 + a₂ * z.2 + c) = c := hphi_aff a₁ a₂ c
  have hpsi : gibbsExpectation quarticSexticPotential t
      (fun z => b₁ * z.1 + b₂ * z.2 + d) = d := hphi_aff b₁ b₂ d
  -- Quadratic expansion (6 terms in the product).
  have hphipsi :
      gibbsExpectation quarticSexticPotential t
          (fun z => (a₁ * z.1 + a₂ * z.2 + c) * (b₁ * z.1 + b₂ * z.2 + d)) =
        a₁ * b₁ * gibbsExpectation quarticSexticPotential t (fun z => z.1 ^ 2) +
        a₂ * b₂ * gibbsExpectation quarticSexticPotential t (fun z => z.2 ^ 2) +
        c * d := by
    unfold gibbsExpectation
    rw [show (fun z : ℝ × ℝ =>
              (a₁ * z.1 + a₂ * z.2 + c) * (b₁ * z.1 + b₂ * z.2 + d) *
              Real.exp (-(t * quarticSexticPotential z))) =
          (fun z : ℝ × ℝ =>
              (a₁ * b₁) * (z.1 ^ 2 * Real.exp (-(t * quarticSexticPotential z))) +
              (a₁ * b₂ + a₂ * b₁) * (z.1 * z.2 * Real.exp (-(t * quarticSexticPotential z))) +
              (a₂ * b₂) * (z.2 ^ 2 * Real.exp (-(t * quarticSexticPotential z))) +
              (a₁ * d + b₁ * c) * (z.1 * Real.exp (-(t * quarticSexticPotential z))) +
              (a₂ * d + b₂ * c) * (z.2 * Real.exp (-(t * quarticSexticPotential z))) +
              (c * d) * Real.exp (-(t * quarticSexticPotential z))) from by
        funext z; ring]
    have h12 : Integrable (fun z : ℝ × ℝ =>
        (a₁ * b₁) * (z.1 ^ 2 * Real.exp (-(t * quarticSexticPotential z))) +
        (a₁ * b₂ + a₂ * b₁) *
          (z.1 * z.2 * Real.exp (-(t * quarticSexticPotential z)))) :=
      (hI20'.const_mul _).add (hI11'.const_mul _)
    have h123 : Integrable (fun z : ℝ × ℝ =>
        (a₁ * b₁) * (z.1 ^ 2 * Real.exp (-(t * quarticSexticPotential z))) +
        (a₁ * b₂ + a₂ * b₁) *
          (z.1 * z.2 * Real.exp (-(t * quarticSexticPotential z))) +
        (a₂ * b₂) * (z.2 ^ 2 * Real.exp (-(t * quarticSexticPotential z)))) :=
      h12.add (hI02'.const_mul _)
    have h1234 : Integrable (fun z : ℝ × ℝ =>
        (a₁ * b₁) * (z.1 ^ 2 * Real.exp (-(t * quarticSexticPotential z))) +
        (a₁ * b₂ + a₂ * b₁) *
          (z.1 * z.2 * Real.exp (-(t * quarticSexticPotential z))) +
        (a₂ * b₂) * (z.2 ^ 2 * Real.exp (-(t * quarticSexticPotential z))) +
        (a₁ * d + b₁ * c) *
          (z.1 * Real.exp (-(t * quarticSexticPotential z)))) :=
      h123.add (hI10'.const_mul _)
    have h12345 : Integrable (fun z : ℝ × ℝ =>
        (a₁ * b₁) * (z.1 ^ 2 * Real.exp (-(t * quarticSexticPotential z))) +
        (a₁ * b₂ + a₂ * b₁) *
          (z.1 * z.2 * Real.exp (-(t * quarticSexticPotential z))) +
        (a₂ * b₂) * (z.2 ^ 2 * Real.exp (-(t * quarticSexticPotential z))) +
        (a₁ * d + b₁ * c) *
          (z.1 * Real.exp (-(t * quarticSexticPotential z))) +
        (a₂ * d + b₂ * c) *
          (z.2 * Real.exp (-(t * quarticSexticPotential z)))) :=
      h1234.add (hI01'.const_mul _)
    rw [MeasureTheory.integral_add h12345 (hI00'.const_mul _)]
    rw [MeasureTheory.integral_add h1234 (hI01'.const_mul _)]
    rw [MeasureTheory.integral_add h123 (hI10'.const_mul _)]
    rw [MeasureTheory.integral_add h12 (hI02'.const_mul _)]
    rw [MeasureTheory.integral_add (hI20'.const_mul _) (hI11'.const_mul _)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hMx : (∫ z : ℝ × ℝ, z.1 * Real.exp (-(t * quarticSexticPotential z))) = 0 := by
      have := gibbsExpectation_fst ht
      unfold gibbsExpectation at this
      exact (div_eq_zero_iff.mp this).resolve_right hZne
    have hMy : (∫ z : ℝ × ℝ, z.2 * Real.exp (-(t * quarticSexticPotential z))) = 0 := by
      have := gibbsExpectation_snd ht
      unfold gibbsExpectation at this
      exact (div_eq_zero_iff.mp this).resolve_right hZne
    have hMxy : (∫ z : ℝ × ℝ, z.1 * z.2 *
                  Real.exp (-(t * quarticSexticPotential z))) = 0 := by
      have := gibbsExpectation_fst_mul_snd ht
      unfold gibbsExpectation at this
      exact (div_eq_zero_iff.mp this).resolve_right hZne
    rw [hMx, hMy, hMxy]
    rw [show (∫ z : ℝ × ℝ, Real.exp (-(t * quarticSexticPotential z))) =
          partitionFunction quarticSexticPotential t from rfl]
    field_simp
    ring
  -- Combine.
  unfold gibbsCov
  rw [hphipsi, hphi, hpsi,
      gibbsExpectation_fst_sq ht,
      gibbsExpectation_snd_sq ht]
  ring

end Laplace.TwoD
