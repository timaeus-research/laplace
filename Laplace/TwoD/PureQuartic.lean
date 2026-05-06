import Laplace.Gibbs
import Laplace.OneD.Quartic
import Laplace.TwoD.SemiDegenerate
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod

/-!
# 2D pure-quartic Gibbs covariance

This file extends the seabed's degenerate-case excursion (1D pure quartic,
`Laplace/OneD/Quartic.lean`) and the semi-degenerate 2D excursion
(`Laplace/TwoD/SemiDegenerate.lean`) to the doubly-degenerate 2D potential

  `L(x, y) = x⁴/24 + y⁴/24`

in which both directions are degenerate (`L_xx(0) = L_yy(0) = 0`). The Gibbs
density factorises as `exp(−tL(x,y)) = exp(−tx⁴/24) · exp(−ty⁴/24)`, so the
2D measure is the product of two copies of the 1D quartic Gibbs measure.

The headline result is `cov_affine_pureQuartic`: for affine observables
`φ(x,y) = a₁ x + a₂ y + c`, `ψ(x,y) = b₁ x + b₂ y + d`, and `t > 0`,
$$
  \mathrm{Cov}_t[\varphi, \psi] = (a_1 b_1 + a_2 b_2) \cdot \sqrt{24/t}
                                  \cdot \Gamma(3/4)/\Gamma(1/4).
$$
Both contributions decay at the same single rate `t^{-1/2}` (both directions
degenerate). With `a₂ = b₂ = 0` this specialises to
`Laplace.OneD.quartic_cov_affine`; with one observable the constant function it
reproduces the (vanishing) variance of a constant.

## Architecture

We reuse the potential-agnostic 2D Gibbs wrappers
`Laplace.TwoD.partitionFunction / gibbsExpectation / gibbsCov` already defined
in `Laplace/TwoD/SemiDegenerate.lean`. The only new infrastructure is:
* a fresh `pureQuarticPotential : ℝ × ℝ → ℝ`,
* its Boltzmann factor decomposition,
* partition function and mixed-monomial moment factorisations,
* atom integrability via `Integrable.mul_prod` of two
  `Laplace.OneD.quartic_integrable_pow_pot` witnesses.

The y-direction integrability is now `Laplace.OneD.quartic_integrable_pow_pot`
directly — no analog of `SemiDegenerate.lean`'s private `harmonic_integrable_pow`
is needed.

## Tide-step provenance

Tide step (5th excursion in this seabed), formalised on `tide/2d-pure-quartic`
(branched off `main` at commit `44a6001`). See
`sri/projects/automation/log/2026-05-02-tide-2d-pure-quartic.md`.
-/

open Real MeasureTheory Set

namespace Laplace.TwoD.PureQuartic

/-! ## The pure-quartic 2D potential -/

/-- The 2D pure-quartic potential `L(x, y) = x⁴/24 + y⁴/24`. -/
noncomputable def pureQuarticPotential : ℝ × ℝ → ℝ :=
  fun z => z.1 ^ 4 / 24 + z.2 ^ 4 / 24

@[simp] lemma pureQuarticPotential_apply (z : ℝ × ℝ) :
    pureQuarticPotential z = z.1 ^ 4 / 24 + z.2 ^ 4 / 24 := rfl

/-! ## Boltzmann factor decomposition -/

/-! ## Bridge to the additively-separable abstraction -/

/-- The pure-quartic 2D potential is an additively-separable potential
with both marginals equal to the 1D quartic. -/
@[simp] lemma pureQuarticPotential_eq_addSeparable :
    pureQuarticPotential =
      addSeparable Laplace.OneD.quarticPotential Laplace.OneD.quarticPotential := by
  funext z
  simp only [pureQuarticPotential_apply, addSeparable_apply,
    Laplace.OneD.quarticPotential_apply]

/-- The Boltzmann factor for `L(x,y) = x⁴/24 + y⁴/24` factorises as a product
of quartic factors in `x` and `y`. Corollary of `exp_neg_t_addSeparable_eq_mul`
via the bridge above. -/
lemma exp_neg_t_pureQuartic_eq_mul (t : ℝ) (z : ℝ × ℝ) :
    Real.exp (-(t * pureQuarticPotential z)) =
      Real.exp (-(t * Laplace.OneD.quarticPotential z.1)) *
      Real.exp (-(t * Laplace.OneD.quarticPotential z.2)) := by
  rw [pureQuarticPotential_eq_addSeparable]
  exact exp_neg_t_addSeparable_eq_mul _ _ t z

/-! ## Partition function factorisation -/

/-- The 2D partition function factorises into the square of the 1D quartic
partition function. Application of `partitionFunction_addSeparable_factor`
via the bridge. -/
theorem partitionFunction_factor (t : ℝ) :
    partitionFunction pureQuarticPotential t =
      Laplace.partitionFunction Laplace.OneD.quarticPotential t *
      Laplace.partitionFunction Laplace.OneD.quarticPotential t := by
  rw [pureQuarticPotential_eq_addSeparable]
  exact partitionFunction_addSeparable_factor _ _ _

/-- Closed form for the partition function:
`Z_2D(t) = ((1/2) · (24/t)^{1/4} · Γ(1/4))²`. -/
theorem partitionFunction_closed_form {t : ℝ} (ht : 0 < t) :
    partitionFunction pureQuarticPotential t =
      ((1/2) * (24/t) ^ ((1 : ℝ)/4) * Real.Gamma ((1 : ℝ)/4)) *
      ((1/2) * (24/t) ^ ((1 : ℝ)/4) * Real.Gamma ((1 : ℝ)/4)) := by
  rw [partitionFunction_factor, Laplace.OneD.quartic_partition ht]

/-- Positivity of the 2D partition function. -/
theorem partitionFunction_pos {t : ℝ} (ht : 0 < t) :
    0 < partitionFunction pureQuarticPotential t := by
  rw [partitionFunction_factor]
  exact mul_pos (Laplace.OneD.quartic_partition_pos ht)
    (Laplace.OneD.quartic_partition_pos ht)

/-! ## Mixed-monomial moment factorisation -/

/-- The 2D moment integral of a separable monomial `z.1^m · z.2^n` against
the pure-quartic Gibbs weight factorises into the product of 1D moment
integrals. Application of `integral_separable_addSeparable` at
`f = fun x ↦ x^m`, `g = fun y ↦ y^n` via the bridge. -/
theorem integral_pow_pow_factor (t : ℝ) (m n : ℕ) :
    (∫ z : ℝ × ℝ, z.1 ^ m * z.2 ^ n *
        Real.exp (-(t * pureQuarticPotential z))) =
      (∫ x : ℝ, x ^ m * Real.exp (-(t * Laplace.OneD.quarticPotential x))) *
      (∫ y : ℝ, y ^ n * Real.exp (-(t * Laplace.OneD.quarticPotential y))) := by
  simp only [pureQuarticPotential_eq_addSeparable]
  exact integral_separable_addSeparable _ _ _ (fun x => x ^ m) (fun y => y ^ n)

/-! ## Specialised moments needed for affine covariance -/

/-- `⟨1⟩_t = 1`. -/
lemma gibbsExpectation_one {t : ℝ} (ht : 0 < t) :
    gibbsExpectation pureQuarticPotential t (fun _ => 1) = 1 := by
  unfold gibbsExpectation
  have hZ : partitionFunction pureQuarticPotential t ≠ 0 :=
    ne_of_gt (partitionFunction_pos ht)
  simp only [one_mul]
  exact div_self hZ

/-- The first coordinate has zero mean: `⟨z.1⟩_t = 0`. (The positivity
hypothesis is retained for API consistency; the proof goes through by parity
alone.) -/
theorem gibbsExpectation_fst {t : ℝ} (_ht : 0 < t) :
    gibbsExpectation pureQuarticPotential t (fun z => z.1) = 0 := by
  unfold gibbsExpectation
  have hnum :
      (∫ z : ℝ × ℝ, z.1 * Real.exp (-(t * pureQuarticPotential z))) = 0 := by
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
    gibbsExpectation pureQuarticPotential t (fun z => z.2) = 0 := by
  unfold gibbsExpectation
  have hnum :
      (∫ z : ℝ × ℝ, z.2 * Real.exp (-(t * pureQuarticPotential z))) = 0 := by
    have h := integral_pow_pow_factor t 0 1
    simp only [pow_zero, pow_one, one_mul] at h
    rw [h]
    have hquartic_zero :
        (∫ y : ℝ, y * Real.exp (-(t * Laplace.OneD.quarticPotential y))) = 0 := by
      have heq : (fun y : ℝ => y * Real.exp (-(t * Laplace.OneD.quarticPotential y))) =
                 (fun y : ℝ => y ^ (2 * 0 + 1) * Real.exp (-(t * y ^ 4 / 24))) := by
        ext y
        rw [Laplace.OneD.quarticPotential_apply,
            show (2 * 0 + 1 : ℕ) = 1 from rfl, pow_one]
        congr 2
        ring
      rw [heq, Laplace.OneD.quartic_moment_odd 0 t]
    rw [hquartic_zero, mul_zero]
  rw [hnum, zero_div]

/-- `⟨z.1 · z.2⟩_t = 0` (mixed first moment vanishes by parity in either
factor). -/
theorem gibbsExpectation_fst_mul_snd {t : ℝ} (_ht : 0 < t) :
    gibbsExpectation pureQuarticPotential t (fun z => z.1 * z.2) = 0 := by
  unfold gibbsExpectation
  have hnum :
      (∫ z : ℝ × ℝ, z.1 * z.2 *
          Real.exp (-(t * pureQuarticPotential z))) = 0 := by
    have h := integral_pow_pow_factor t 1 1
    simp only [pow_one] at h
    rw [h]
    -- Either factor vanishes by parity; pick the y-side.
    have hquartic_zero :
        (∫ y : ℝ, y * Real.exp (-(t * Laplace.OneD.quarticPotential y))) = 0 := by
      have heq : (fun y : ℝ => y * Real.exp (-(t * Laplace.OneD.quarticPotential y))) =
                 (fun y : ℝ => y ^ (2 * 0 + 1) * Real.exp (-(t * y ^ 4 / 24))) := by
        ext y
        rw [Laplace.OneD.quarticPotential_apply,
            show (2 * 0 + 1 : ℕ) = 1 from rfl, pow_one]
        congr 2
        ring
      rw [heq, Laplace.OneD.quartic_moment_odd 0 t]
    rw [hquartic_zero, mul_zero]
  rw [hnum, zero_div]

/-- `⟨z.1²⟩_t = √(24/t) · Γ(3/4) / Γ(1/4)` (first-direction degenerate
second moment). -/
theorem gibbsExpectation_fst_sq {t : ℝ} (ht : 0 < t) :
    gibbsExpectation pureQuarticPotential t (fun z => z.1 ^ 2) =
      Real.sqrt (24 / t) * Real.Gamma ((3 : ℝ) / 4) / Real.Gamma ((1 : ℝ) / 4) := by
  unfold gibbsExpectation
  have h := integral_pow_pow_factor t 2 0
  simp only [pow_zero, one_mul, mul_one] at h
  rw [h, partitionFunction_factor]
  have hZq_pos := Laplace.OneD.quartic_partition_pos ht
  have hZq_ne : Laplace.partitionFunction Laplace.OneD.quarticPotential t ≠ 0 :=
    ne_of_gt hZq_pos
  -- Convert the bare y-integral to the literal `Laplace.partitionFunction` symbol so
  -- the `mul_div_mul_right` cancellation matches syntactically.
  rw [show (∫ y : ℝ, Real.exp (-(t * Laplace.OneD.quarticPotential y))) =
        Laplace.partitionFunction Laplace.OneD.quarticPotential t from rfl]
  -- Cancel Z_quartic from numerator and denominator: (a · c) / (b · c) = a / b.
  rw [mul_div_mul_right _ _ hZq_ne]
  -- Goal: (∫ x² · exp(-tQ_quartic)) / Z_quartic = ⟨x²⟩_quartic.
  exact Laplace.OneD.quartic_expected_value_sq ht

/-- `⟨z.2²⟩_t = √(24/t) · Γ(3/4) / Γ(1/4)` (second-direction degenerate
second moment). -/
theorem gibbsExpectation_snd_sq {t : ℝ} (ht : 0 < t) :
    gibbsExpectation pureQuarticPotential t (fun z => z.2 ^ 2) =
      Real.sqrt (24 / t) * Real.Gamma ((3 : ℝ) / 4) / Real.Gamma ((1 : ℝ) / 4) := by
  unfold gibbsExpectation
  have h := integral_pow_pow_factor t 0 2
  simp only [pow_zero, one_mul] at h
  rw [h, partitionFunction_factor]
  have hZq_pos := Laplace.OneD.quartic_partition_pos ht
  have hZq_ne : Laplace.partitionFunction Laplace.OneD.quarticPotential t ≠ 0 :=
    ne_of_gt hZq_pos
  rw [show (∫ x : ℝ, Real.exp (-(t * Laplace.OneD.quarticPotential x))) =
        Laplace.partitionFunction Laplace.OneD.quarticPotential t from rfl]
  -- Cancel Z_quartic from numerator and denominator: (c · a) / (c · b) = a / b.
  rw [mul_div_mul_left _ _ hZq_ne]
  exact Laplace.OneD.quartic_expected_value_sq ht

/-! ## Integrability lemmas -/

/-- 2D atom integrability: `z.1^m · z.2^n · exp(-(t · pureQuarticPotential z))`
on `ℝ × ℝ`. -/
private theorem pureQuartic_integrable_pow_pow (m n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable
      (fun z : ℝ × ℝ =>
        z.1 ^ m * z.2 ^ n *
        Real.exp (-(t * pureQuarticPotential z))) := by
  have hq1 := Laplace.OneD.quartic_integrable_pow_pot m ht
  have hq2 := Laplace.OneD.quartic_integrable_pow_pot n ht
  -- Factor the integrand into (x part) * (y part) and apply Integrable.mul_prod.
  have hprod := hq1.mul_prod (g := fun y : ℝ => y ^ n *
      Real.exp (-(t * Laplace.OneD.quarticPotential y))) hq2
  have heq : (fun z : ℝ × ℝ =>
              (z.1 ^ m * Real.exp (-(t * Laplace.OneD.quarticPotential z.1))) *
              (z.2 ^ n * Real.exp (-(t * Laplace.OneD.quarticPotential z.2)))) =
             (fun z : ℝ × ℝ =>
              z.1 ^ m * z.2 ^ n *
              Real.exp (-(t * pureQuarticPotential z))) := by
    ext z
    rw [exp_neg_t_pureQuartic_eq_mul]
    ring
  rwa [heq] at hprod

/-! ## Headline theorem: affine covariance -/

/-- **Affine covariance against the 2D pure-quartic Gibbs measure.**
For `L(x, y) = x⁴/24 + y⁴/24`, `t > 0`, and affine observables
`φ(x,y) = a₁ x + a₂ y + c`, `ψ(x,y) = b₁ x + b₂ y + d`,
$$
  \mathrm{Cov}_t[\varphi, \psi] = (a_1 b_1 + a_2 b_2)
                                  \cdot \sqrt{24/t}
                                  \cdot \Gamma(3/4)/\Gamma(1/4).
$$
Both directions are degenerate, so both contributions decay at the single rate
`t^{-1/2}`. The constants `c, d` drop out (covariance is shift-invariant in
each argument). This is the doubly-degenerate analog of
`cov_affine_semiDegenerate`. -/
theorem cov_affine_pureQuartic {t : ℝ} (ht : 0 < t)
    (a₁ a₂ b₁ b₂ c d : ℝ) :
    gibbsCov pureQuarticPotential t
        (fun z : ℝ × ℝ => a₁ * z.1 + a₂ * z.2 + c)
        (fun z : ℝ × ℝ => b₁ * z.1 + b₂ * z.2 + d) =
      (a₁ * b₁ + a₂ * b₂) * Real.sqrt (24 / t) *
        Real.Gamma ((3 : ℝ) / 4) / Real.Gamma ((1 : ℝ) / 4) := by
  have hZpos := partitionFunction_pos ht
  have hZne : partitionFunction pureQuarticPotential t ≠ 0 := ne_of_gt hZpos
  -- 2D atom integrabilities
  have hI00 := pureQuartic_integrable_pow_pow 0 0 ht
  have hI10 := pureQuartic_integrable_pow_pow 1 0 ht
  have hI01 := pureQuartic_integrable_pow_pow 0 1 ht
  have hI20 := pureQuartic_integrable_pow_pow 2 0 ht
  have hI02 := pureQuartic_integrable_pow_pow 0 2 ht
  have hI11 := pureQuartic_integrable_pow_pow 1 1 ht
  -- Strip the trivial `z.1^0 * z.2^0 = 1` factors so each is in canonical form.
  have hI00' : Integrable
      (fun z : ℝ × ℝ => Real.exp (-(t * pureQuarticPotential z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 0 * z.2 ^ 0 * Real.exp (-(t * pureQuarticPotential z))) =
               (fun z : ℝ × ℝ => Real.exp (-(t * pureQuarticPotential z))) := by
      ext; simp
    rwa [heq] at hI00
  have hI10' : Integrable
      (fun z : ℝ × ℝ => z.1 * Real.exp (-(t * pureQuarticPotential z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 1 * z.2 ^ 0 * Real.exp (-(t * pureQuarticPotential z))) =
               (fun z : ℝ × ℝ => z.1 * Real.exp (-(t * pureQuarticPotential z))) := by
      ext; simp
    rwa [heq] at hI10
  have hI01' : Integrable
      (fun z : ℝ × ℝ => z.2 * Real.exp (-(t * pureQuarticPotential z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 0 * z.2 ^ 1 * Real.exp (-(t * pureQuarticPotential z))) =
               (fun z : ℝ × ℝ => z.2 * Real.exp (-(t * pureQuarticPotential z))) := by
      ext; simp
    rwa [heq] at hI01
  have hI20' : Integrable
      (fun z : ℝ × ℝ => z.1 ^ 2 * Real.exp (-(t * pureQuarticPotential z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 2 * z.2 ^ 0 * Real.exp (-(t * pureQuarticPotential z))) =
               (fun z : ℝ × ℝ => z.1 ^ 2 * Real.exp (-(t * pureQuarticPotential z))) := by
      ext; simp
    rwa [heq] at hI20
  have hI02' : Integrable
      (fun z : ℝ × ℝ => z.2 ^ 2 * Real.exp (-(t * pureQuarticPotential z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 0 * z.2 ^ 2 * Real.exp (-(t * pureQuarticPotential z))) =
               (fun z : ℝ × ℝ => z.2 ^ 2 * Real.exp (-(t * pureQuarticPotential z))) := by
      ext; simp
    rwa [heq] at hI02
  have hI11' : Integrable
      (fun z : ℝ × ℝ => z.1 * z.2 * Real.exp (-(t * pureQuarticPotential z))) := by
    have heq : (fun z : ℝ × ℝ =>
                z.1 ^ 1 * z.2 ^ 1 * Real.exp (-(t * pureQuarticPotential z))) =
               (fun z : ℝ × ℝ => z.1 * z.2 * Real.exp (-(t * pureQuarticPotential z))) := by
      ext; simp
    rwa [heq] at hI11
  -- Linearity for affine observables: ⟨p₁ z.1 + p₂ z.2 + q⟩ = q (since means vanish).
  have hphi_aff : ∀ p₁ p₂ q : ℝ,
      gibbsExpectation pureQuarticPotential t
          (fun z => p₁ * z.1 + p₂ * z.2 + q) = q := by
    intro p₁ p₂ q
    unfold gibbsExpectation
    rw [show (fun z : ℝ × ℝ =>
              (p₁ * z.1 + p₂ * z.2 + q) *
              Real.exp (-(t * pureQuarticPotential z))) =
          (fun z : ℝ × ℝ =>
              p₁ * (z.1 * Real.exp (-(t * pureQuarticPotential z))) +
              p₂ * (z.2 * Real.exp (-(t * pureQuarticPotential z))) +
              q * Real.exp (-(t * pureQuarticPotential z))) from by
        funext z; ring]
    have h12 : Integrable (fun z : ℝ × ℝ =>
                p₁ * (z.1 * Real.exp (-(t * pureQuarticPotential z))) +
                p₂ * (z.2 * Real.exp (-(t * pureQuarticPotential z)))) :=
      (hI10'.const_mul p₁).add (hI01'.const_mul p₂)
    rw [MeasureTheory.integral_add h12 (hI00'.const_mul q)]
    rw [MeasureTheory.integral_add (hI10'.const_mul p₁) (hI01'.const_mul p₂)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
    have hMx : (∫ z : ℝ × ℝ, z.1 * Real.exp (-(t * pureQuarticPotential z))) = 0 := by
      have := gibbsExpectation_fst (t := t) ht
      unfold gibbsExpectation at this
      exact (div_eq_zero_iff.mp this).resolve_right hZne
    have hMy : (∫ z : ℝ × ℝ, z.2 * Real.exp (-(t * pureQuarticPotential z))) = 0 := by
      have := gibbsExpectation_snd (t := t) ht
      unfold gibbsExpectation at this
      exact (div_eq_zero_iff.mp this).resolve_right hZne
    rw [hMx, hMy,
        show (∫ z : ℝ × ℝ, Real.exp (-(t * pureQuarticPotential z))) =
          partitionFunction pureQuarticPotential t from rfl]
    field_simp
    ring
  have hphi : gibbsExpectation pureQuarticPotential t
      (fun z => a₁ * z.1 + a₂ * z.2 + c) = c := hphi_aff a₁ a₂ c
  have hpsi : gibbsExpectation pureQuarticPotential t
      (fun z => b₁ * z.1 + b₂ * z.2 + d) = d := hphi_aff b₁ b₂ d
  -- Quadratic expansion: ⟨φψ⟩ = a₁b₁ ⟨z.1²⟩ + (a₁b₂+a₂b₁) ⟨z.1z.2⟩ + a₂b₂ ⟨z.2²⟩
  --                              + (a₁d+b₁c) ⟨z.1⟩ + (a₂d+b₂c) ⟨z.2⟩ + cd
  have hphipsi :
      gibbsExpectation pureQuarticPotential t
          (fun z => (a₁ * z.1 + a₂ * z.2 + c) * (b₁ * z.1 + b₂ * z.2 + d)) =
        a₁ * b₁ * gibbsExpectation pureQuarticPotential t (fun z => z.1 ^ 2) +
        a₂ * b₂ * gibbsExpectation pureQuarticPotential t (fun z => z.2 ^ 2) +
        c * d := by
    unfold gibbsExpectation
    rw [show (fun z : ℝ × ℝ =>
              (a₁ * z.1 + a₂ * z.2 + c) * (b₁ * z.1 + b₂ * z.2 + d) *
              Real.exp (-(t * pureQuarticPotential z))) =
          (fun z : ℝ × ℝ =>
              (a₁ * b₁) * (z.1 ^ 2 * Real.exp (-(t * pureQuarticPotential z))) +
              (a₁ * b₂ + a₂ * b₁) * (z.1 * z.2 * Real.exp (-(t * pureQuarticPotential z))) +
              (a₂ * b₂) * (z.2 ^ 2 * Real.exp (-(t * pureQuarticPotential z))) +
              (a₁ * d + b₁ * c) * (z.1 * Real.exp (-(t * pureQuarticPotential z))) +
              (a₂ * d + b₂ * c) * (z.2 * Real.exp (-(t * pureQuarticPotential z))) +
              (c * d) * Real.exp (-(t * pureQuarticPotential z))) from by
        funext z; ring]
    -- Integrate the 6-term sum via repeated integral_add.
    have h12 : Integrable (fun z : ℝ × ℝ =>
        (a₁ * b₁) * (z.1 ^ 2 * Real.exp (-(t * pureQuarticPotential z))) +
        (a₁ * b₂ + a₂ * b₁) *
          (z.1 * z.2 * Real.exp (-(t * pureQuarticPotential z)))) :=
      (hI20'.const_mul _).add (hI11'.const_mul _)
    have h123 : Integrable (fun z : ℝ × ℝ =>
        (a₁ * b₁) * (z.1 ^ 2 * Real.exp (-(t * pureQuarticPotential z))) +
        (a₁ * b₂ + a₂ * b₁) *
          (z.1 * z.2 * Real.exp (-(t * pureQuarticPotential z))) +
        (a₂ * b₂) * (z.2 ^ 2 * Real.exp (-(t * pureQuarticPotential z)))) :=
      h12.add (hI02'.const_mul _)
    have h1234 : Integrable (fun z : ℝ × ℝ =>
        (a₁ * b₁) * (z.1 ^ 2 * Real.exp (-(t * pureQuarticPotential z))) +
        (a₁ * b₂ + a₂ * b₁) *
          (z.1 * z.2 * Real.exp (-(t * pureQuarticPotential z))) +
        (a₂ * b₂) * (z.2 ^ 2 * Real.exp (-(t * pureQuarticPotential z))) +
        (a₁ * d + b₁ * c) *
          (z.1 * Real.exp (-(t * pureQuarticPotential z)))) :=
      h123.add (hI10'.const_mul _)
    have h12345 : Integrable (fun z : ℝ × ℝ =>
        (a₁ * b₁) * (z.1 ^ 2 * Real.exp (-(t * pureQuarticPotential z))) +
        (a₁ * b₂ + a₂ * b₁) *
          (z.1 * z.2 * Real.exp (-(t * pureQuarticPotential z))) +
        (a₂ * b₂) * (z.2 ^ 2 * Real.exp (-(t * pureQuarticPotential z))) +
        (a₁ * d + b₁ * c) *
          (z.1 * Real.exp (-(t * pureQuarticPotential z))) +
        (a₂ * d + b₂ * c) *
          (z.2 * Real.exp (-(t * pureQuarticPotential z)))) :=
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
    have hMx : (∫ z : ℝ × ℝ, z.1 * Real.exp (-(t * pureQuarticPotential z))) = 0 := by
      have := gibbsExpectation_fst (t := t) ht
      unfold gibbsExpectation at this
      exact (div_eq_zero_iff.mp this).resolve_right hZne
    have hMy : (∫ z : ℝ × ℝ, z.2 * Real.exp (-(t * pureQuarticPotential z))) = 0 := by
      have := gibbsExpectation_snd (t := t) ht
      unfold gibbsExpectation at this
      exact (div_eq_zero_iff.mp this).resolve_right hZne
    have hMxy : (∫ z : ℝ × ℝ, z.1 * z.2 *
                  Real.exp (-(t * pureQuarticPotential z))) = 0 := by
      have := gibbsExpectation_fst_mul_snd (t := t) ht
      unfold gibbsExpectation at this
      exact (div_eq_zero_iff.mp this).resolve_right hZne
    rw [hMx, hMy, hMxy]
    rw [show (∫ z : ℝ × ℝ, Real.exp (-(t * pureQuarticPotential z))) =
          partitionFunction pureQuarticPotential t from rfl]
    field_simp
    ring
  -- Combine: Cov = ⟨φψ⟩ - ⟨φ⟩⟨ψ⟩ = (a₁b₁⟨z.1²⟩ + a₂b₂⟨z.2²⟩ + cd) - cd
  unfold gibbsCov
  rw [hphipsi, hphi, hpsi,
      gibbsExpectation_fst_sq ht,
      gibbsExpectation_snd_sq ht]
  ring

end Laplace.TwoD.PureQuartic
