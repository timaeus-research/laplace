import Laplace.Gibbs
import Laplace.OneD.Quartic
import Laplace.OneD.Harmonic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod

/-!
# 2D semi-degenerate Gibbs covariance

This file extends the seabed's degenerate-case excursion (1D pure quartic,
`Laplace/OneD/Quartic.lean`) to a 2D potential

  `L(x, y) = (λ/2)·y² + x⁴/24`     (`λ > 0`)

which combines a degenerate quartic direction (in `x`, where `L_xx(0) = 0`)
with a nondegenerate quadratic direction (in `y`, where `L_yy(0) = λ`).
The Gibbs density factorises as
`exp(−tL(x,y)) = exp(−tx⁴/24) · exp(−tλy²/2)`, so the 2D measure is the
product of the 1D quartic Gibbs in `x` and the 1D harmonic Gibbs in `y`.

The headline result is `cov_affine_semiDegenerate`: for affine
observables `φ(x,y) = a₁x + a₂y + c`, `ψ(x,y) = b₁x + b₂y + d`,
$$
  Cov_t[φ, ψ] = a₁ b₁ \cdot \sqrt{24/t} \cdot Γ(3/4)/Γ(1/4) + a₂ b₂ / (λ t).
$$
The `t^{-1/2}` term comes from the degenerate `x`-direction; the `t^{-1}`
term comes from the nondegenerate `y`-direction.

## Architecture

We define thin 2D wrappers `partitionFunction`, `gibbsExpectation`, and
`gibbsCov` mirroring the 1D `Laplace.Gibbs` setup but with `L : ℝ × ℝ → ℝ`.
The integration is against the canonical product measure on `ℝ × ℝ`
(`(volume : Measure (ℝ × ℝ)) = volume.prod volume`).

The factorisation lemmas use Mathlib's `MeasureTheory.integral_prod_mul`,
which is unconditional (returns the product of integrals; if the function
is not integrable both sides are 0 by convention).

## Tide-step provenance

Tide step 2, formalised on `tide/2d-semi-degenerate` (branched off
`tide/quartic-moments`). See
`sri/projects/automation/log/2026-05-01-tide-2d-semi-degenerate-cov.md`.
-/

open Real MeasureTheory Set

namespace Laplace.TwoD

/-! ## Thin 2D Gibbs wrappers -/

/-- Partition function of the 2D Gibbs measure `exp(-t · L(z)) dz` on `ℝ × ℝ`. -/
noncomputable def partitionFunction (L : ℝ × ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ z : ℝ × ℝ, Real.exp (-(t * L z))

/-- Gibbs expectation `⟨φ⟩_t = (1/Z(t)) · ∫ φ(z) exp(-t L(z)) dz`. -/
noncomputable def gibbsExpectation (L : ℝ × ℝ → ℝ) (t : ℝ) (φ : ℝ × ℝ → ℝ) : ℝ :=
  (∫ z : ℝ × ℝ, φ z * Real.exp (-(t * L z))) / partitionFunction L t

/-- Gibbs covariance `Cov_t[φ, ψ] = ⟨φψ⟩_t − ⟨φ⟩_t ⟨ψ⟩_t`. -/
noncomputable def gibbsCov
    (L : ℝ × ℝ → ℝ) (t : ℝ) (φ ψ : ℝ × ℝ → ℝ) : ℝ :=
  gibbsExpectation L t (fun z => φ z * ψ z)
    - gibbsExpectation L t φ * gibbsExpectation L t ψ

/-! ## The semi-degenerate potential -/

/-- The 2D semi-degenerate potential `L(x, y) = (λ/2) · y² + x⁴/24`. -/
noncomputable def semiDegeneratePotential (lam : ℝ) : ℝ × ℝ → ℝ :=
  fun z => lam / 2 * z.2 ^ 2 + z.1 ^ 4 / 24

@[simp] lemma semiDegeneratePotential_apply (lam : ℝ) (z : ℝ × ℝ) :
    semiDegeneratePotential lam z = lam / 2 * z.2 ^ 2 + z.1 ^ 4 / 24 := rfl

/-! ## Bridge to the additively-separable abstraction -/

/-- The semi-degenerate potential is an additively-separable potential
with `U = quartic` and `V = harmonic`. -/
@[simp] lemma semiDegeneratePotential_eq_addSeparable (lam : ℝ) :
    semiDegeneratePotential lam =
      addSeparable Laplace.OneD.quarticPotential
        (Laplace.OneD.harmonicPotential lam) := by
  funext z
  simp only [semiDegeneratePotential_apply, addSeparable_apply,
    Laplace.OneD.quarticPotential_apply]
  unfold Laplace.OneD.harmonicPotential
  ring

/-! ## Boltzmann factor decomposition -/

/-- The Boltzmann factor for `L(x,y) = (λ/2)y² + x⁴/24` factorises as a
product of a quartic factor in `x` and a harmonic factor in `y`. Corollary
of `exp_neg_t_addSeparable_eq_mul` via the bridge above. -/
lemma exp_neg_t_semiDegenerate_eq_mul (lam t : ℝ) (z : ℝ × ℝ) :
    Real.exp (-(t * semiDegeneratePotential lam z)) =
      Real.exp (-(t * Laplace.OneD.quarticPotential z.1)) *
      Real.exp (-(t * Laplace.OneD.harmonicPotential lam z.2)) := by
  rw [semiDegeneratePotential_eq_addSeparable]
  exact exp_neg_t_addSeparable_eq_mul _ _ t z

/-! ## Partition function factorisation -/

/-- The 2D partition function factorises into the product of the 1D
quartic and 1D harmonic partition functions. Application of
`partitionFunction_addSeparable_factor` via the bridge. -/
theorem partitionFunction_factor (lam t : ℝ) :
    partitionFunction (semiDegeneratePotential lam) t =
      Laplace.partitionFunction Laplace.OneD.quarticPotential t *
      Laplace.partitionFunction (Laplace.OneD.harmonicPotential lam) t := by
  rw [semiDegeneratePotential_eq_addSeparable]
  exact partitionFunction_addSeparable_factor _ _ _

/-- Closed form for the partition function: `Z_2D(t) = (1/2)·(24/t)^{1/4}·Γ(1/4)·√(2π/(λt))`. -/
theorem partitionFunction_closed_form {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    partitionFunction (semiDegeneratePotential lam) t =
      ((1/2) * (24/t) ^ ((1 : ℝ)/4) * Real.Gamma ((1 : ℝ)/4)) *
      Real.sqrt (2 * π / (lam * t)) := by
  rw [partitionFunction_factor, Laplace.OneD.quartic_partition ht,
      Laplace.OneD.partitionFunction_harmonic hlam ht]

/-- Positivity of the 2D partition function. -/
theorem partitionFunction_pos {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    0 < partitionFunction (semiDegeneratePotential lam) t := by
  rw [partitionFunction_factor]
  exact mul_pos (Laplace.OneD.quartic_partition_pos ht)
    (by rw [Laplace.OneD.partitionFunction_harmonic hlam ht]; positivity)

/-! ## Mixed-monomial moment factorisation -/

/-- The 2D moment integral of a separable monomial `z.1^m · z.2^n` against
the semi-degenerate Gibbs weight factorises into the product of 1D
moment integrals. Application of `integral_separable_addSeparable` at
`f = fun x ↦ x^m`, `g = fun y ↦ y^n` via the bridge. -/
theorem integral_pow_pow_factor (lam t : ℝ) (m n : ℕ) :
    (∫ z : ℝ × ℝ, z.1 ^ m * z.2 ^ n *
        Real.exp (-(t * semiDegeneratePotential lam z))) =
      (∫ x : ℝ, x ^ m * Real.exp (-(t * Laplace.OneD.quarticPotential x))) *
      (∫ y : ℝ, y ^ n * Real.exp (-(t * Laplace.OneD.harmonicPotential lam y))) := by
  simp only [semiDegeneratePotential_eq_addSeparable]
  exact integral_separable_addSeparable _ _ _ (fun x => x ^ m) (fun y => y ^ n)

/-! ## Specialised moments needed for affine covariance -/

/-- `⟨1⟩_t = 1` (with `Z_t > 0`). Trivial special case for completeness. -/
lemma gibbsExpectation_one {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    gibbsExpectation (semiDegeneratePotential lam) t (fun _ => 1) = 1 := by
  unfold gibbsExpectation
  have hZ : partitionFunction (semiDegeneratePotential lam) t ≠ 0 :=
    ne_of_gt (partitionFunction_pos hlam ht)
  simp only [one_mul]
  exact div_self hZ

/-- The first coordinate has zero mean: `⟨z.1⟩_t = 0`. (Positivity hypotheses retained
for API consistency with the other moment lemmas; the proof goes through by parity
alone and does not actually use them.) -/
theorem gibbsExpectation_fst {lam t : ℝ} (_hlam : 0 < lam) (_ht : 0 < t) :
    gibbsExpectation (semiDegeneratePotential lam) t (fun z => z.1) = 0 := by
  unfold gibbsExpectation
  -- Numerator: ∫ z.1 · exp(-tL) = (∫ x exp(-tQ_quartic)) · (∫ exp(-tQ_harmonic)) = 0 · _ = 0
  have hnum :
      (∫ z : ℝ × ℝ, z.1 * Real.exp (-(t * semiDegeneratePotential lam z))) = 0 := by
    have h := integral_pow_pow_factor lam t 1 0
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
theorem gibbsExpectation_snd {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    gibbsExpectation (semiDegeneratePotential lam) t (fun z => z.2) = 0 := by
  unfold gibbsExpectation
  have hnum :
      (∫ z : ℝ × ℝ, z.2 * Real.exp (-(t * semiDegeneratePotential lam z))) = 0 := by
    have h := integral_pow_pow_factor lam t 0 1
    simp only [pow_zero, pow_one, one_mul] at h
    rw [h]
    -- The harmonic side: ∫ y · exp(-(t · harmonicPotential lam y)) = 0 by parity (k=0 odd case).
    have hharm_zero :
        (∫ y : ℝ, y * Real.exp (-(t * Laplace.OneD.harmonicPotential lam y))) = 0 := by
      have h2 := Laplace.OneD.harmonic_int_pow_odd hlam ht 0
      simpa using h2
    rw [hharm_zero, mul_zero]
  rw [hnum, zero_div]

/-- `⟨z.1 · z.2⟩_t = 0` (mixed first moment vanishes by independence + parity). -/
theorem gibbsExpectation_fst_mul_snd {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    gibbsExpectation (semiDegeneratePotential lam) t (fun z => z.1 * z.2) = 0 := by
  unfold gibbsExpectation
  have hnum :
      (∫ z : ℝ × ℝ, z.1 * z.2 *
          Real.exp (-(t * semiDegeneratePotential lam z))) = 0 := by
    have h := integral_pow_pow_factor lam t 1 1
    simp only [pow_one] at h
    rw [h]
    -- Either factor vanishes by parity; pick the harmonic side.
    have hharm_zero :
        (∫ y : ℝ, y * Real.exp (-(t * Laplace.OneD.harmonicPotential lam y))) = 0 := by
      have h2 := Laplace.OneD.harmonic_int_pow_odd hlam ht 0
      simpa using h2
    rw [hharm_zero, mul_zero]
  rw [hnum, zero_div]

/-- `⟨z.1²⟩_t = √(24/t) · Γ(3/4) / Γ(1/4)` (degenerate-direction second moment). -/
theorem gibbsExpectation_fst_sq {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    gibbsExpectation (semiDegeneratePotential lam) t (fun z => z.1 ^ 2) =
      Real.sqrt (24 / t) * Real.Gamma ((3 : ℝ) / 4) / Real.Gamma ((1 : ℝ) / 4) := by
  unfold gibbsExpectation
  have h := integral_pow_pow_factor lam t 2 0
  simp only [pow_zero, one_mul, mul_one] at h
  rw [h, partitionFunction_factor]
  have hZh_pos : 0 < Laplace.partitionFunction (Laplace.OneD.harmonicPotential lam) t := by
    rw [Laplace.OneD.partitionFunction_harmonic hlam ht]; positivity
  have hZh_ne : Laplace.partitionFunction (Laplace.OneD.harmonicPotential lam) t ≠ 0 :=
    ne_of_gt hZh_pos
  -- Convert the harmonic 1D integral to the literal `Laplace.partitionFunction` symbol so the
  -- `mul_div_mul_right` cancellation matches syntactically (it would otherwise be defEq only).
  rw [show (∫ y : ℝ, Real.exp (-(t * Laplace.OneD.harmonicPotential lam y))) =
        Laplace.partitionFunction (Laplace.OneD.harmonicPotential lam) t from rfl]
  -- Cancel Z_harmonic from numerator and denominator: (a · c) / (b · c) = a / b.
  rw [mul_div_mul_right _ _ hZh_ne]
  -- Goal: (∫ x² · exp(-tQ_quartic)) / Z_quartic = sqrt(24/t)·Γ(3/4)/Γ(1/4).
  -- The 1D quartic expected_value_sq lemma is precisely this, after unfolding gibbsExpectation.
  exact Laplace.OneD.quartic_expected_value_sq ht

/-- `⟨z.2²⟩_t = 1/(λ t)` (nondegenerate-direction second moment). -/
theorem gibbsExpectation_snd_sq {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    gibbsExpectation (semiDegeneratePotential lam) t (fun z => z.2 ^ 2) =
      1 / (lam * t) := by
  unfold gibbsExpectation
  have h := integral_pow_pow_factor lam t 0 2
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
  -- Goal: (∫ y² · exp(-tQ_harm)) / Z_harm = 1/(λt).
  -- Apply the 1D harmonic moment lemma at k = 1.
  have h2 := Laplace.OneD.gibbsExpectation_harmonic_pow_even hlam ht 1
  unfold Laplace.gibbsExpectation at h2
  -- h2 : (∫ y^(2*1) · exp(-tQ_harm)) / Z_harm = ((2*1-1)!! : ℝ) / (λt)^1
  -- (2*1 = 2 by reduction; (2-1)!! = 1!! = 1; (λt)^1 = λt.)
  convert h2 using 2
  · simp [Nat.doubleFactorial]
  · exact (pow_one _).symm

/-! ## Integrability lemmas (1D and 2D atoms) -/

/-- 1D harmonic integrability: `y^n · exp(-(t · harmonicPotential lam y))` is integrable
on ℝ for any `n : ℕ`, `lam > 0`, `t > 0`. Uses Mathlib's
`integrable_rpow_mul_exp_neg_mul_sq` after converting `y^n` (npow) to `y^(n:ℝ)` (rpow) and
matching the `(b/2) · y^2` shape. -/
private theorem harmonic_integrable_pow (n : ℕ) {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    Integrable
      (fun y : ℝ => y ^ n * Real.exp (-(t * Laplace.OneD.harmonicPotential lam y))) := by
  have hns : (-1 : ℝ) < (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  have hb : 0 < t * lam / 2 := by positivity
  have hraw : Integrable
      (fun y : ℝ => y ^ ((n : ℕ) : ℝ) * Real.exp (-(t * lam / 2) * y ^ 2)) volume :=
    integrable_rpow_mul_exp_neg_mul_sq hb hns
  have heq : (fun y : ℝ => y ^ ((n : ℕ) : ℝ) * Real.exp (-(t * lam / 2) * y ^ 2)) =
             (fun y : ℝ => y ^ n * Real.exp (-(t * Laplace.OneD.harmonicPotential lam y))) := by
    ext y
    rw [Real.rpow_natCast]
    unfold Laplace.OneD.harmonicPotential
    congr 2
    ring
  rwa [heq] at hraw

/-- 2D atom integrability: `z.1^m · z.2^n · exp(-(t · semiDegeneratePotential lam z))`
on `ℝ × ℝ`. -/
private theorem semiDegenerate_integrable_pow_pow (m n : ℕ) {lam t : ℝ}
    (hlam : 0 < lam) (ht : 0 < t) :
    Integrable
      (fun z : ℝ × ℝ =>
        z.1 ^ m * z.2 ^ n *
        Real.exp (-(t * semiDegeneratePotential lam z))) := by
  have hq := Laplace.OneD.quartic_integrable_pow_pot m ht
  have hh := harmonic_integrable_pow n hlam ht
  -- Factor the integrand into (x part) * (y part) and apply Integrable.mul_prod.
  have hprod := hq.mul_prod (g := fun y : ℝ => y ^ n *
      Real.exp (-(t * Laplace.OneD.harmonicPotential lam y))) hh
  have heq : (fun z : ℝ × ℝ =>
              (z.1 ^ m * Real.exp (-(t * Laplace.OneD.quarticPotential z.1))) *
              (z.2 ^ n * Real.exp (-(t * Laplace.OneD.harmonicPotential lam z.2)))) =
             (fun z : ℝ × ℝ =>
              z.1 ^ m * z.2 ^ n *
              Real.exp (-(t * semiDegeneratePotential lam z))) := by
    ext z
    rw [exp_neg_t_semiDegenerate_eq_mul]
    ring
  rwa [heq] at hprod

/-! ## Headline theorem: affine covariance -/

/-- **Affine covariance against the 2D semi-degenerate Gibbs measure.**
For `L(x, y) = (λ/2)y² + x⁴/24` with `λ > 0`, `t > 0`, and affine observables
`φ(x,y) = a₁ x + a₂ y + c`, `ψ(x,y) = b₁ x + b₂ y + d`,
$$
  \mathrm{Cov}_t[\varphi, \psi] = a_1 b_1 \cdot \sqrt{24/t} \cdot \Gamma(3/4)/\Gamma(1/4)
                                + a_2 b_2 / (\lambda t).
$$
The `t^{-1/2}` term is contributed by the degenerate quartic direction, the `t^{-1}` term
by the nondegenerate quadratic direction. The constants `c, d` drop out (covariance is
shift-invariant in each argument). -/
theorem cov_affine_semiDegenerate {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t)
    (a₁ a₂ b₁ b₂ c d : ℝ) :
    gibbsCov (semiDegeneratePotential lam) t
        (fun z : ℝ × ℝ => a₁ * z.1 + a₂ * z.2 + c)
        (fun z : ℝ × ℝ => b₁ * z.1 + b₂ * z.2 + d) =
      a₁ * b₁ * Real.sqrt (24 / t) * Real.Gamma ((3 : ℝ) / 4) / Real.Gamma ((1 : ℝ) / 4) +
      a₂ * b₂ / (lam * t) := by
  have hZpos := partitionFunction_pos hlam ht
  have hZne : partitionFunction (semiDegeneratePotential lam) t ≠ 0 := ne_of_gt hZpos
  -- 2D atom integrabilities
  have hI00 := semiDegenerate_integrable_pow_pow 0 0 hlam ht
  have hI10 := semiDegenerate_integrable_pow_pow 1 0 hlam ht
  have hI01 := semiDegenerate_integrable_pow_pow 0 1 hlam ht
  have hI20 := semiDegenerate_integrable_pow_pow 2 0 hlam ht
  have hI02 := semiDegenerate_integrable_pow_pow 0 2 hlam ht
  have hI11 := semiDegenerate_integrable_pow_pow 1 1 hlam ht
  -- Strip the trivial `z.1^0 * z.2^0 = 1` factors so each is in canonical form.
  have hI00' : Integrable
      (fun z : ℝ × ℝ => Real.exp (-(t * semiDegeneratePotential lam z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 0 * z.2 ^ 0 * Real.exp (-(t * semiDegeneratePotential lam z))) =
               (fun z : ℝ × ℝ => Real.exp (-(t * semiDegeneratePotential lam z))) := by
      ext; simp
    rwa [heq] at hI00
  have hI10' : Integrable
      (fun z : ℝ × ℝ => z.1 * Real.exp (-(t * semiDegeneratePotential lam z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 1 * z.2 ^ 0 * Real.exp (-(t * semiDegeneratePotential lam z))) =
               (fun z : ℝ × ℝ => z.1 * Real.exp (-(t * semiDegeneratePotential lam z))) := by
      ext; simp
    rwa [heq] at hI10
  have hI01' : Integrable
      (fun z : ℝ × ℝ => z.2 * Real.exp (-(t * semiDegeneratePotential lam z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 0 * z.2 ^ 1 * Real.exp (-(t * semiDegeneratePotential lam z))) =
               (fun z : ℝ × ℝ => z.2 * Real.exp (-(t * semiDegeneratePotential lam z))) := by
      ext; simp
    rwa [heq] at hI01
  have hI20' : Integrable
      (fun z : ℝ × ℝ => z.1 ^ 2 * Real.exp (-(t * semiDegeneratePotential lam z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 2 * z.2 ^ 0 * Real.exp (-(t * semiDegeneratePotential lam z))) =
               (fun z : ℝ × ℝ => z.1 ^ 2 * Real.exp (-(t * semiDegeneratePotential lam z))) := by
      ext; simp
    rwa [heq] at hI20
  have hI02' : Integrable
      (fun z : ℝ × ℝ => z.2 ^ 2 * Real.exp (-(t * semiDegeneratePotential lam z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 0 * z.2 ^ 2 * Real.exp (-(t * semiDegeneratePotential lam z))) =
               (fun z : ℝ × ℝ => z.2 ^ 2 * Real.exp (-(t * semiDegeneratePotential lam z))) := by
      ext; simp
    rwa [heq] at hI02
  have hI11' : Integrable
      (fun z : ℝ × ℝ => z.1 * z.2 * Real.exp (-(t * semiDegeneratePotential lam z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 1 * z.2 ^ 1 * Real.exp (-(t * semiDegeneratePotential lam z))) =
               (fun z : ℝ × ℝ => z.1 * z.2 * Real.exp (-(t * semiDegeneratePotential lam z))) := by
      ext; simp
    rwa [heq] at hI11
  -- Linearity for affine observables: ⟨p₁ z.1 + p₂ z.2 + q⟩ = q (since means vanish).
  have hphi_aff : ∀ p₁ p₂ q : ℝ,
      gibbsExpectation (semiDegeneratePotential lam) t
          (fun z => p₁ * z.1 + p₂ * z.2 + q) = q := by
    intro p₁ p₂ q
    unfold gibbsExpectation
    rw [show (fun z : ℝ × ℝ =>
              (p₁ * z.1 + p₂ * z.2 + q) *
              Real.exp (-(t * semiDegeneratePotential lam z))) =
          (fun z : ℝ × ℝ =>
              p₁ * (z.1 * Real.exp (-(t * semiDegeneratePotential lam z))) +
              p₂ * (z.2 * Real.exp (-(t * semiDegeneratePotential lam z))) +
              q * Real.exp (-(t * semiDegeneratePotential lam z))) from by
        funext z; ring]
    have h12 : Integrable (fun z : ℝ × ℝ =>
                p₁ * (z.1 * Real.exp (-(t * semiDegeneratePotential lam z))) +
                p₂ * (z.2 * Real.exp (-(t * semiDegeneratePotential lam z)))) :=
      (hI10'.const_mul p₁).add (hI01'.const_mul p₂)
    rw [MeasureTheory.integral_add h12 (hI00'.const_mul q)]
    rw [MeasureTheory.integral_add (hI10'.const_mul p₁) (hI01'.const_mul p₂)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
    -- Goal: (p₁ · M_x + p₂ · M_y + q · Z) / Z = q. Use M_x = M_y = 0 (numerator-of-zero-mean).
    have hMx : (∫ z : ℝ × ℝ, z.1 * Real.exp (-(t * semiDegeneratePotential lam z))) = 0 := by
      have := gibbsExpectation_fst hlam ht
      unfold gibbsExpectation at this
      exact (div_eq_zero_iff.mp this).resolve_right hZne
    have hMy : (∫ z : ℝ × ℝ, z.2 * Real.exp (-(t * semiDegeneratePotential lam z))) = 0 := by
      have := gibbsExpectation_snd hlam ht
      unfold gibbsExpectation at this
      exact (div_eq_zero_iff.mp this).resolve_right hZne
    rw [hMx, hMy,
        show (∫ z : ℝ × ℝ, Real.exp (-(t * semiDegeneratePotential lam z))) =
          partitionFunction (semiDegeneratePotential lam) t from rfl]
    field_simp
    ring
  -- ⟨φ⟩ = c, ⟨ψ⟩ = d
  have hphi : gibbsExpectation (semiDegeneratePotential lam) t
      (fun z => a₁ * z.1 + a₂ * z.2 + c) = c := hphi_aff a₁ a₂ c
  have hpsi : gibbsExpectation (semiDegeneratePotential lam) t
      (fun z => b₁ * z.1 + b₂ * z.2 + d) = d := hphi_aff b₁ b₂ d
  -- Quadratic expansion: ⟨φψ⟩ = a₁b₁ ⟨z.1²⟩ + (a₁b₂+a₂b₁) ⟨z.1z.2⟩ + a₂b₂ ⟨z.2²⟩
  --                              + (a₁d+b₁c) ⟨z.1⟩ + (a₂d+b₂c) ⟨z.2⟩ + cd
  have hphipsi :
      gibbsExpectation (semiDegeneratePotential lam) t
          (fun z => (a₁ * z.1 + a₂ * z.2 + c) * (b₁ * z.1 + b₂ * z.2 + d)) =
        a₁ * b₁ * gibbsExpectation (semiDegeneratePotential lam) t (fun z => z.1 ^ 2) +
        a₂ * b₂ * gibbsExpectation (semiDegeneratePotential lam) t (fun z => z.2 ^ 2) +
        c * d := by
    unfold gibbsExpectation
    rw [show (fun z : ℝ × ℝ =>
              (a₁ * z.1 + a₂ * z.2 + c) * (b₁ * z.1 + b₂ * z.2 + d) *
              Real.exp (-(t * semiDegeneratePotential lam z))) =
          (fun z : ℝ × ℝ =>
              (a₁ * b₁) * (z.1 ^ 2 * Real.exp (-(t * semiDegeneratePotential lam z))) +
              (a₁ * b₂ + a₂ * b₁) * (z.1 * z.2 * Real.exp (-(t * semiDegeneratePotential lam z))) +
              (a₂ * b₂) * (z.2 ^ 2 * Real.exp (-(t * semiDegeneratePotential lam z))) +
              (a₁ * d + b₁ * c) * (z.1 * Real.exp (-(t * semiDegeneratePotential lam z))) +
              (a₂ * d + b₂ * c) * (z.2 * Real.exp (-(t * semiDegeneratePotential lam z))) +
              (c * d) * Real.exp (-(t * semiDegeneratePotential lam z))) from by
        funext z; ring]
    -- Integrate the 6-term sum via repeated integral_add.
    have h12 : Integrable (fun z : ℝ × ℝ =>
        (a₁ * b₁) * (z.1 ^ 2 * Real.exp (-(t * semiDegeneratePotential lam z))) +
        (a₁ * b₂ + a₂ * b₁) *
          (z.1 * z.2 * Real.exp (-(t * semiDegeneratePotential lam z)))) :=
      (hI20'.const_mul _).add (hI11'.const_mul _)
    have h123 : Integrable (fun z : ℝ × ℝ =>
        (a₁ * b₁) * (z.1 ^ 2 * Real.exp (-(t * semiDegeneratePotential lam z))) +
        (a₁ * b₂ + a₂ * b₁) *
          (z.1 * z.2 * Real.exp (-(t * semiDegeneratePotential lam z))) +
        (a₂ * b₂) * (z.2 ^ 2 * Real.exp (-(t * semiDegeneratePotential lam z)))) :=
      h12.add (hI02'.const_mul _)
    have h1234 : Integrable (fun z : ℝ × ℝ =>
        (a₁ * b₁) * (z.1 ^ 2 * Real.exp (-(t * semiDegeneratePotential lam z))) +
        (a₁ * b₂ + a₂ * b₁) *
          (z.1 * z.2 * Real.exp (-(t * semiDegeneratePotential lam z))) +
        (a₂ * b₂) * (z.2 ^ 2 * Real.exp (-(t * semiDegeneratePotential lam z))) +
        (a₁ * d + b₁ * c) *
          (z.1 * Real.exp (-(t * semiDegeneratePotential lam z)))) :=
      h123.add (hI10'.const_mul _)
    have h12345 : Integrable (fun z : ℝ × ℝ =>
        (a₁ * b₁) * (z.1 ^ 2 * Real.exp (-(t * semiDegeneratePotential lam z))) +
        (a₁ * b₂ + a₂ * b₁) *
          (z.1 * z.2 * Real.exp (-(t * semiDegeneratePotential lam z))) +
        (a₂ * b₂) * (z.2 ^ 2 * Real.exp (-(t * semiDegeneratePotential lam z))) +
        (a₁ * d + b₁ * c) *
          (z.1 * Real.exp (-(t * semiDegeneratePotential lam z))) +
        (a₂ * d + b₂ * c) *
          (z.2 * Real.exp (-(t * semiDegeneratePotential lam z)))) :=
      h1234.add (hI01'.const_mul _)
    rw [MeasureTheory.integral_add h12345 (hI00'.const_mul _)]
    rw [MeasureTheory.integral_add h1234 (hI01'.const_mul _)]
    rw [MeasureTheory.integral_add h123 (hI10'.const_mul _)]
    rw [MeasureTheory.integral_add h12 (hI02'.const_mul _)]
    rw [MeasureTheory.integral_add (hI20'.const_mul _) (hI11'.const_mul _)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    -- Now everything is in terms of M_xx, M_xy, M_yy, M_x, M_y, Z.
    -- M_x = M_y = M_xy = 0 (extract from gibbsExpectation_fst, _snd, _fst_mul_snd).
    have hMx : (∫ z : ℝ × ℝ, z.1 * Real.exp (-(t * semiDegeneratePotential lam z))) = 0 := by
      have := gibbsExpectation_fst hlam ht
      unfold gibbsExpectation at this
      exact (div_eq_zero_iff.mp this).resolve_right hZne
    have hMy : (∫ z : ℝ × ℝ, z.2 * Real.exp (-(t * semiDegeneratePotential lam z))) = 0 := by
      have := gibbsExpectation_snd hlam ht
      unfold gibbsExpectation at this
      exact (div_eq_zero_iff.mp this).resolve_right hZne
    have hMxy : (∫ z : ℝ × ℝ, z.1 * z.2 *
                  Real.exp (-(t * semiDegeneratePotential lam z))) = 0 := by
      have := gibbsExpectation_fst_mul_snd hlam ht
      unfold gibbsExpectation at this
      exact (div_eq_zero_iff.mp this).resolve_right hZne
    rw [hMx, hMy, hMxy]
    rw [show (∫ z : ℝ × ℝ, Real.exp (-(t * semiDegeneratePotential lam z))) =
          partitionFunction (semiDegeneratePotential lam) t from rfl]
    -- LHS: (a₁b₁ M_xx + 0 + a₂b₂ M_yy + 0 + 0 + cd Z) / Z
    -- RHS: a₁b₁ ⟨z.1²⟩ + a₂b₂ ⟨z.2²⟩ + cd
    -- ⟨z.j²⟩ = M_jj / Z.
    field_simp
    ring
  -- Combine: Cov = ⟨φψ⟩ - ⟨φ⟩⟨ψ⟩ = (a₁b₁⟨z.1²⟩ + a₂b₂⟨z.2²⟩ + cd) - cd
  unfold gibbsCov
  rw [hphipsi, hphi, hpsi,
      gibbsExpectation_fst_sq hlam ht,
      gibbsExpectation_snd_sq hlam ht]
  ring

end Laplace.TwoD
