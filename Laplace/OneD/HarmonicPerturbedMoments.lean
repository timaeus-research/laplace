import Laplace.OneD.HarmonicCovGlobalConstancy
import Laplace.OneD.IntegralRemainder

/-!
# Perturbed harmonic-Gibbs moments `⟨xᵏ⟩_h` for k = 3, 4

For the harmonic Gibbs measure
`μ_t,h(x) ∝ exp(-t((λ/2)x² + h·x))` on ℝ against Lebesgue with
`λ, t > 0`, this file extends I4's k = 1, 2 closed forms to k = 3, 4:

  `⟨x³⟩_h = -3h/(λ²t) - h³/λ³`,
  `⟨x⁴⟩_h = 3/(λ²t²) + 6h²/(λ³t) + h⁴/λ⁴`.

The decisive observation (per GPT-5.5 Pro at the O1 deliberation): the
normalised perturbed Gibbs law is exactly `N(-h/λ, 1/(λt))`, so the
closed forms are the raw Gaussian moments
`E[X^k] = sum_{j} binom(k,j) μ^(k-j) σ^j · (j-1)!!`
substituted at `μ = -h/λ`, `σ² = 1/(λt)`.

The Lean proof routes through a **public Gibbs-expectation transport
lemma**, `gibbsExp_harmonic_h_eq_unperturbed_shift`, which captures the
underlying fact (perturbed law = unperturbed law shifted by `-h/λ`)
in a form independent of the choice of observable. This realises I4's
retrospective Follow-up §5: *"Promote
`integral_with_perturbation_eq_shifted` on second use"* — the transport
lemma is the natural Gibbs-expectation-level lift.

## Public API

* `gibbsExp_harmonic_h_eq_unperturbed_shift`:
    `⟨f(x)⟩_h = ⟨f(y - h/λ)⟩_0`.
* `gibbsExp_h_cube_harmonic_eq`:
    `⟨x³⟩_h = -3h/(λ²t) - h³/λ³`.
* `gibbsExp_h_quartic_harmonic_eq`:
    `⟨x⁴⟩_h = 3/(λ²t²) + 6h²/(λ³t) + h⁴/λ⁴`.

## Tide-step provenance

Tide step O1 (perturbed-moments-harmonic), formalised on
`tide/perturbed-moments-harmonic` in laplace, branched off post-merge
`main` (commit `47e3426`). See
`sri/projects/primer/tide-log/2026-05-07-tide-perturbed-moments-harmonic.md`.
-/

open MeasureTheory
open scoped Nat

namespace Laplace.OneD

/-! ## Re-derived helpers from I4 (the originals are `private`) -/

/-- Generic shift identity for any `f`: shift the integrand `f(x)`
against `exp(-(t·L_h))` to an integrand `f(y - h/λ)` against
`exp(-(t·L_0))`, modulo the constant `exp(t·h²/(2λ))`. (Re-derived
locally; the I4 version is `private`.) -/
private lemma integral_shifted'
    {lam t : ℝ} (hlam : 0 < lam) (h : ℝ) (f : ℝ → ℝ) :
    (∫ x : ℝ, f x * Real.exp (-(t * (lam / 2 * x ^ 2 + h * x))))
      = Real.exp (t * h ^ 2 / (2 * lam)) *
          (∫ y : ℝ, f (y - h / lam) *
            Real.exp (-(t * (lam / 2 * y ^ 2)))) := by
  have hkey : ∀ x : ℝ,
      Real.exp (-(t * (lam / 2 * x ^ 2 + h * x))) =
      Real.exp (t * h ^ 2 / (2 * lam)) *
        Real.exp (-(t * (lam / 2 * (x + h / lam) ^ 2))) := by
    intro x
    have hlam_ne : lam ≠ 0 := ne_of_gt hlam
    have hadd : -(t * (lam / 2 * x ^ 2 + h * x)) =
        t * h ^ 2 / (2 * lam) + (-(t * (lam / 2 * (x + h / lam) ^ 2))) := by
      have : lam / 2 * x ^ 2 + h * x =
          lam / 2 * (x + h / lam) ^ 2 - h ^ 2 / (2 * lam) := by
        field_simp; ring
      rw [this]; ring
    rw [hadd, Real.exp_add]
  have heq : (fun x : ℝ => f x * Real.exp (-(t * (lam / 2 * x ^ 2 + h * x))))
      = (fun x : ℝ => Real.exp (t * h ^ 2 / (2 * lam)) *
          (f x * Real.exp (-(t * (lam / 2 * (x + h / lam) ^ 2))))) := by
    funext x; rw [hkey]; ring
  rw [heq, integral_const_mul]
  congr 1
  set c : ℝ := h / lam
  have hreshape : (fun x : ℝ => f x *
      Real.exp (-(t * (lam / 2 * (x + c) ^ 2)))) =
      (fun x : ℝ =>
        (fun y : ℝ => f (y - c) *
          Real.exp (-(t * (lam / 2 * y ^ 2)))) (x + c)) := by
    funext x
    have hxc : x + c - c = x := by ring
    change f x * _ = f (x + c - c) * _
    rw [hxc]
  rw [hreshape]
  exact integral_add_right_eq_self
    (fun y : ℝ => f (y - c) * Real.exp (-(t * (lam / 2 * y ^ 2)))) c

/-! ## Integrability witnesses for `y^k · exp(-(t·(λ/2)·y²))`, k = 0..4 -/

private lemma integrable_gauss_pow' {lam t : ℝ}
    (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    Integrable (fun y : ℝ => y ^ n *
        Real.exp (-(t * (lam / 2 * y ^ 2)))) volume := by
  have hb : 0 < lam * t / 2 := by positivity
  have h := integrable_pow_mul_exp_neg_mul_sq hb n
  -- h : Integrable (fun x : ℝ => x ^ n * exp(-(lam*t/2) * x^2))
  have heq : (fun x : ℝ => x ^ n * Real.exp (-(lam * t / 2 * x ^ 2)))
      = (fun y : ℝ => y ^ n * Real.exp (-(t * (lam / 2 * y ^ 2)))) := by
    funext y; congr 2; ring
  rw [heq] at h
  exact h

/-! ## Closed forms for the unperturbed Gaussian integrals at `(λ/2)·²` -/

/-- `∫ exp(-(t·(λ/2)·y²)) dy = √(2π/(λt))`. -/
private lemma int_pow_zero {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    (∫ y : ℝ, Real.exp (-(t * (lam / 2 * y ^ 2))))
      = Real.sqrt (2 * Real.pi / (lam * t)) := by
  have := partitionFunction_harmonic hlam ht
  unfold Laplace.partitionFunction harmonicPotential at this
  exact this

/-- `∫ y · exp(-(t·(λ/2)·y²)) dy = 0`. -/
private lemma int_pow_one {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    (∫ y : ℝ, y * Real.exp (-(t * (lam / 2 * y ^ 2)))) = 0 := by
  have h := harmonic_int_pow_odd hlam ht 0
  unfold harmonicPotential at h
  simpa using h

/-- `∫ y² · exp(-(t·(λ/2)·y²)) dy = (1/(λt)) · √(2π/(λt))`. -/
private lemma int_pow_two {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    (∫ y : ℝ, y ^ 2 * Real.exp (-(t * (lam / 2 * y ^ 2))))
      = (1 / (lam * t)) * Real.sqrt (2 * Real.pi / (lam * t)) := by
  have h := harmonic_int_pow_even hlam ht 1
  unfold harmonicPotential at h
  -- (2 * 1 - 1)‼ = 1‼ = 1; cast normalisation.
  have hdf : (((2 * 1 - 1 : ℕ)‼ : ℝ)) = 1 := by
    change (((1 : ℕ) : ℝ)) = 1
    exact Nat.cast_one
  rw [hdf, Nat.cast_one, show (2 * 1 : ℕ) = 2 from rfl] at h
  rw [h]
  -- Goal: 1 * √(2π) * (λt)^(-(1+1/2)) = (1/(λt)) * √(2π/(λt)).
  have hlamt : 0 < lam * t := mul_pos hlam ht
  rw [show (2 * Real.pi / (lam * t) : ℝ) = (2 * Real.pi) * (lam * t)⁻¹ by ring,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
      show Real.sqrt ((lam * t : ℝ)⁻¹) = (lam * t : ℝ) ^ (-(1 / 2 : ℝ)) by
        rw [Real.sqrt_eq_rpow,
            show ((lam * t : ℝ)⁻¹ : ℝ) = (lam * t : ℝ) ^ (-1 : ℝ) from
              (Real.rpow_neg_one _).symm,
            ← Real.rpow_mul hlamt.le]
        congr 1; ring]
  rw [show (1 / (lam * t) : ℝ) = (lam * t : ℝ) ^ (-1 : ℝ) by
        rw [Real.rpow_neg_one]; ring]
  rw [show (lam * t : ℝ) ^ (-((1 : ℝ) + 1 / 2)) =
        (lam * t : ℝ) ^ ((-1 : ℝ) + (-(1 / 2 : ℝ))) from by
        congr 1; ring]
  rw [Real.rpow_add hlamt]
  ring

/-- `∫ y³ · exp(-(t·(λ/2)·y²)) dy = 0`. -/
private lemma int_pow_three {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    (∫ y : ℝ, y ^ 3 * Real.exp (-(t * (lam / 2 * y ^ 2)))) = 0 := by
  have h := harmonic_int_pow_odd hlam ht 1
  unfold harmonicPotential at h
  -- 2*1+1 = 3.
  rw [show (2 * 1 + 1 : ℕ) = 3 from rfl] at h
  exact h

/-- `∫ y⁴ · exp(-(t·(λ/2)·y²)) dy = 3/(λt)² · √(2π/(λt))`.

Routes through `harmonic_int_pow_even` at `k = 2`: `(2·2-1)!! = 3!! = 3`,
and exponent algebra `(λt)^(-(2 + 1/2)) = (1/(λt)²) · (λt)^(-(1/2))`. -/
private lemma int_pow_four {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    (∫ y : ℝ, y ^ 4 * Real.exp (-(t * (lam / 2 * y ^ 2))))
      = 3 / ((lam * t) ^ 2) * Real.sqrt (2 * Real.pi / (lam * t)) := by
  have h := harmonic_int_pow_even hlam ht 2
  unfold harmonicPotential at h
  -- (2 * 2 - 1)‼ = 3‼ = 3; cast normalisation `((2 : ℕ) : ℝ) = 2`.
  have hdf : (((2 * 2 - 1 : ℕ)‼ : ℝ)) = 3 := by
    change (((3 : ℕ)‼ : ℝ)) = 3
    have : (3 : ℕ)‼ = 3 := by decide
    rw [this]; norm_num
  have hcast2 : ((2 : ℕ) : ℝ) = 2 := by norm_cast
  rw [hdf, hcast2, show (2 * 2 : ℕ) = 4 from rfl] at h
  rw [h]
  -- Goal: 3 * √(2π) * (λt)^(-(2 + 1/2)) = 3/(λt)² · √(2π/(λt))
  have hlamt : 0 < lam * t := mul_pos hlam ht
  rw [show (2 * Real.pi / (lam * t) : ℝ) = (2 * Real.pi) * (lam * t)⁻¹ by ring,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
      show Real.sqrt ((lam * t : ℝ)⁻¹) = (lam * t : ℝ) ^ (-(1 / 2 : ℝ)) by
        rw [Real.sqrt_eq_rpow,
            show ((lam * t : ℝ)⁻¹ : ℝ) = (lam * t : ℝ) ^ (-1 : ℝ) from
              (Real.rpow_neg_one _).symm,
            ← Real.rpow_mul hlamt.le]
        congr 1; ring]
  -- Now: 3 * √(2π) * (λt)^(-(2+1/2)) = 3/(λt)² · √(2π) · (λt)^(-1/2)
  -- Convert (λt)² to (λt)^(2:ℝ).
  rw [show ((lam * t) ^ 2 : ℝ) = (lam * t : ℝ) ^ (2 : ℝ) by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast, Real.rpow_natCast]]
  -- Combine RHS: 3/(λt)^(2:ℝ) · √(2π) · (λt)^(-1/2) = 3 * √(2π) * (λt)^(-2) * (λt)^(-1/2)
  rw [show (3 / (lam * t : ℝ) ^ (2 : ℝ)) = 3 * (lam * t : ℝ) ^ (-(2 : ℝ)) by
        rw [Real.rpow_neg hlamt.le 2]; field_simp]
  -- Combine exponents: (λt)^(-2) · (λt)^(-1/2) = (λt)^(-(2+1/2)).
  have hcombine : (lam * t : ℝ) ^ (-((2 : ℝ) + 1 / 2))
      = (lam * t : ℝ) ^ (-(2 : ℝ)) * (lam * t : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hlamt]; congr 1; ring
  rw [hcombine]; ring

/-! ## Public Gibbs-expectation transport lemma

The decisive abstraction: at the level of normalised expectations, the
perturbed harmonic Gibbs law is the unperturbed Gaussian shifted by
`-h/λ`. The `exp(t h²/(2λ))` factor that the integral-level shift
identity carries cancels in the ratio defining `gibbsExp`. -/

/-- **Transport lemma.** For the harmonic potential
`L(x) = (λ/2)x²` and perturbation direction `A(x) = x`, the perturbed
Gibbs expectation of `f(x)` at parameter `h` equals the *unperturbed*
Gibbs expectation of the shifted observable `f(y - h/λ)`.

Equivalently, the normalised perturbed law is `N(-h/λ, 1/(λt))`. -/
theorem gibbsExp_harmonic_h_eq_unperturbed_shift
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (h : ℝ) (f : ℝ → ℝ) :
    Threepoint.gibbsExp (volume : Measure ℝ)
        (fun x : ℝ => lam / 2 * x ^ 2)
        (fun x : ℝ => x) t h f
      = Threepoint.gibbsExp (volume : Measure ℝ)
        (fun x : ℝ => lam / 2 * x ^ 2)
        (fun x : ℝ => x) t 0
        (fun y : ℝ => f (y - h / lam)) := by
  unfold Threepoint.gibbsExp
  -- LHS: (∫ f(x) · exp(-t(λ/2 x² + h·x))) / (∫ exp(-t(λ/2 x² + h·x)))
  -- RHS: (∫ f(y - h/λ) · exp(-t(λ/2 y²))) / (∫ exp(-t(λ/2 y²)))   [since 0·x = 0]
  -- Apply integral_shifted' to both numerator and denominator on LHS.
  -- The exp(t h²/(2λ)) factor appears in both and cancels.
  have hexp_ne : Real.exp (t * h ^ 2 / (2 * lam)) ≠ 0 := Real.exp_ne_zero _
  have hZ0_pos : 0 < Real.sqrt (2 * Real.pi / (lam * t)) := by
    apply Real.sqrt_pos.mpr; positivity
  have hZ0_ne : (∫ y : ℝ, Real.exp (-(t * (lam / 2 * y ^ 2)))) ≠ 0 := by
    rw [int_pow_zero hlam ht]; exact hZ0_pos.ne'
  -- Reduce LHS denominator.
  have hLHS_den :
      (∫ w : ℝ, Real.exp (-(t * (lam / 2 * w ^ 2 + h * w))))
        = Real.exp (t * h ^ 2 / (2 * lam)) *
          (∫ y : ℝ, Real.exp (-(t * (lam / 2 * y ^ 2)))) := by
    have h1 : (fun x : ℝ => Real.exp (-(t * (lam / 2 * x ^ 2 + h * x))))
        = (fun x : ℝ => (fun (_ : ℝ) => (1 : ℝ)) x *
            Real.exp (-(t * (lam / 2 * x ^ 2 + h * x)))) := by
      funext x; ring
    rw [h1, integral_shifted' hlam h (fun (_ : ℝ) => (1 : ℝ))]
    simp only [one_mul]
  -- Reduce LHS numerator.
  have hLHS_num :
      (∫ w : ℝ, f w * Real.exp (-(t * (lam / 2 * w ^ 2 + h * w))))
        = Real.exp (t * h ^ 2 / (2 * lam)) *
          (∫ y : ℝ, f (y - h / lam) *
            Real.exp (-(t * (lam / 2 * y ^ 2)))) :=
    integral_shifted' hlam h f
  -- Reduce RHS denominator.
  have hRHS_den :
      (∫ w : ℝ, Real.exp (-(t * (lam / 2 * w ^ 2 + 0 * w))))
        = (∫ y : ℝ, Real.exp (-(t * (lam / 2 * y ^ 2)))) := by
    apply integral_congr_ae
    filter_upwards with y
    congr 2; ring
  -- Reduce RHS numerator.
  have hRHS_num :
      (∫ w : ℝ, f (w - h / lam) *
            Real.exp (-(t * (lam / 2 * w ^ 2 + 0 * w))))
        = (∫ y : ℝ, f (y - h / lam) *
            Real.exp (-(t * (lam / 2 * y ^ 2)))) := by
    apply integral_congr_ae
    filter_upwards with y
    congr 2; congr 2; ring
  change (∫ w : ℝ, f w * Real.exp (-(t * (lam / 2 * w ^ 2 + h * w)))) /
       (∫ w : ℝ, Real.exp (-(t * (lam / 2 * w ^ 2 + h * w))))
       = (∫ w : ℝ, f (w - h / lam) *
            Real.exp (-(t * (lam / 2 * w ^ 2 + 0 * w)))) /
         (∫ w : ℝ, Real.exp (-(t * (lam / 2 * w ^ 2 + 0 * w))))
  rw [hLHS_num, hLHS_den, hRHS_num, hRHS_den]
  -- Now: (E · A) / (E · Z₀) = A / Z₀ where E = exp(t h²/(2λ)).
  field_simp

/-! ## The cubic moment -/

/-- **Cubic moment of the perturbed harmonic Gibbs measure.**

`⟨x³⟩_h = -3h/(λ²t) - h³/λ³`.

By the transport lemma, `⟨x³⟩_h = ⟨(y - h/λ)³⟩_0`. Expand
`(y - h/λ)³ = y³ - 3(h/λ)y² + 3(h/λ)²y - (h/λ)³`. Use Tide 10's
moments: `⟨y³⟩_0 = 0`, `⟨y²⟩_0 = 1/(λt)`, `⟨y⟩_0 = 0`, `⟨1⟩_0 = 1`.
Conclude `-3(h/λ)/(λt) - (h/λ)³ = -3h/(λ²t) - h³/λ³`. -/
theorem gibbsExp_h_cube_harmonic_eq
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (h : ℝ) :
    Threepoint.gibbsExp (volume : Measure ℝ)
        (fun x : ℝ => lam / 2 * x ^ 2)
        (fun x : ℝ => x) t h
        (fun x : ℝ => x ^ 3)
      = -3 * h / (lam ^ 2 * t) - h ^ 3 / lam ^ 3 := by
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have ht_ne : t ≠ 0 := ne_of_gt ht
  -- Transport: ⟨x³⟩_h = ⟨(y - h/λ)³⟩_0.
  rw [gibbsExp_harmonic_h_eq_unperturbed_shift hlam ht h (fun x : ℝ => x ^ 3)]
  -- Compute ⟨(y - h/λ)³⟩_0 via direct integral form. Set up integrability
  -- for each polynomial term of (y - α)³ = y³ - 3α y² + 3α² y - α³,
  -- where α := h / lam.
  set α : ℝ := h / lam with hα
  have hZ0 := int_pow_zero hlam ht
  have h0 := integrable_gauss_pow' hlam ht 0
  have h1 := integrable_gauss_pow' hlam ht 1
  have h2 := integrable_gauss_pow' hlam ht 2
  have h3 := integrable_gauss_pow' hlam ht 3
  -- Massage h0..h3 into the convenient `y^k * exp(...)` form.
  have h0' : Integrable
      (fun y : ℝ => Real.exp (-(t * (lam / 2 * y ^ 2)))) volume := by
    simpa using h0
  have h1' : Integrable
      (fun y : ℝ => y * Real.exp (-(t * (lam / 2 * y ^ 2)))) volume := by
    have := h1
    simpa [pow_one] using this
  -- Numerator: ∫ (y - α)³ · exp(-(t·(λ/2)·y²)) dy.
  -- Expand pointwise via funext + ring, then split integrals.
  have hnum_pt : (fun y : ℝ => (y - α) ^ 3 *
        Real.exp (-(t * (lam / 2 * y ^ 2)))) =
      (fun y : ℝ => y ^ 3 * Real.exp (-(t * (lam / 2 * y ^ 2)))
        - 3 * α * (y ^ 2 * Real.exp (-(t * (lam / 2 * y ^ 2))))
        + 3 * α ^ 2 * (y * Real.exp (-(t * (lam / 2 * y ^ 2))))
        - α ^ 3 * Real.exp (-(t * (lam / 2 * y ^ 2)))) := by
    funext y; ring
  have hint_3α_y2 : Integrable
      (fun y : ℝ => 3 * α *
        (y ^ 2 * Real.exp (-(t * (lam / 2 * y ^ 2))))) volume :=
    h2.const_mul (3 * α)
  have hint_3α2_y : Integrable
      (fun y : ℝ => 3 * α ^ 2 *
        (y * Real.exp (-(t * (lam / 2 * y ^ 2))))) volume :=
    h1'.const_mul (3 * α ^ 2)
  have hint_α3 : Integrable
      (fun y : ℝ => α ^ 3 * Real.exp (-(t * (lam / 2 * y ^ 2))))
      volume :=
    h0'.const_mul (α ^ 3)
  -- Numerator value. Build single-lambda integrability witnesses to avoid
  -- the `Pi.add`/lambda mismatch in `integral_add`.
  have hint_left : Integrable
      (fun y : ℝ => y ^ 3 * Real.exp (-(t * (lam / 2 * y ^ 2)))
        - 3 * α * (y ^ 2 * Real.exp (-(t * (lam / 2 * y ^ 2)))))
      volume := h3.sub hint_3α_y2
  have hint_right : Integrable
      (fun y : ℝ => 3 * α ^ 2 * (y * Real.exp (-(t * (lam / 2 * y ^ 2))))
        - α ^ 3 * Real.exp (-(t * (lam / 2 * y ^ 2))))
      volume := hint_3α2_y.sub hint_α3
  have hnum :
      (∫ y : ℝ, (y - α) ^ 3 * Real.exp (-(t * (lam / 2 * y ^ 2))))
        = -3 * α * ((1 / (lam * t)) *
            Real.sqrt (2 * Real.pi / (lam * t)))
          - α ^ 3 * Real.sqrt (2 * Real.pi / (lam * t)) := by
    rw [hnum_pt]
    rw [show (fun y : ℝ => y ^ 3 * Real.exp (-(t * (lam / 2 * y ^ 2)))
              - 3 * α * (y ^ 2 * Real.exp (-(t * (lam / 2 * y ^ 2))))
              + 3 * α ^ 2 * (y * Real.exp (-(t * (lam / 2 * y ^ 2))))
              - α ^ 3 * Real.exp (-(t * (lam / 2 * y ^ 2))))
            = (fun y : ℝ =>
                (y ^ 3 * Real.exp (-(t * (lam / 2 * y ^ 2)))
                  - 3 * α * (y ^ 2 * Real.exp (-(t * (lam / 2 * y ^ 2)))))
                + (3 * α ^ 2 * (y * Real.exp (-(t * (lam / 2 * y ^ 2))))
                  - α ^ 3 * Real.exp (-(t * (lam / 2 * y ^ 2))))) by
        funext y; ring]
    rw [integral_add hint_left hint_right,
        integral_sub h3 hint_3α_y2,
        integral_sub hint_3α2_y hint_α3,
        integral_const_mul, integral_const_mul, integral_const_mul,
        int_pow_three hlam ht, int_pow_two hlam ht,
        int_pow_one hlam ht, int_pow_zero hlam ht]
    ring
  -- Combine with denominator.
  unfold Threepoint.gibbsExp
  change (∫ y : ℝ, (y - α) ^ 3 *
        Real.exp (-(t * (lam / 2 * y ^ 2 + 0 * y)))) /
      (∫ y : ℝ, Real.exp (-(t * (lam / 2 * y ^ 2 + 0 * y))))
      = -3 * h / (lam ^ 2 * t) - h ^ 3 / lam ^ 3
  -- Reduce 0 * y to 0 in both integrals.
  have hreduce_num : (fun y : ℝ => (y - α) ^ 3 *
        Real.exp (-(t * (lam / 2 * y ^ 2 + 0 * y)))) =
      (fun y : ℝ => (y - α) ^ 3 *
        Real.exp (-(t * (lam / 2 * y ^ 2)))) := by
    funext y; congr 2; ring
  have hreduce_den : (fun y : ℝ =>
      Real.exp (-(t * (lam / 2 * y ^ 2 + 0 * y)))) =
      (fun y : ℝ => Real.exp (-(t * (lam / 2 * y ^ 2)))) := by
    funext y; congr 2; ring
  rw [hreduce_num, hreduce_den, hnum, hZ0]
  -- α := h/lam, expand and simplify.
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi / (lam * t)) := by
    apply Real.sqrt_pos.mpr; positivity
  have hsqrt_ne : Real.sqrt (2 * Real.pi / (lam * t)) ≠ 0 := hsqrt_pos.ne'
  rw [hα]
  field_simp

/-! ## The quartic moment -/

/-- **Quartic moment of the perturbed harmonic Gibbs measure.**

`⟨x⁴⟩_h = 3/(λ²t²) + 6h²/(λ³t) + h⁴/λ⁴`.

By the transport lemma, `⟨x⁴⟩_h = ⟨(y - h/λ)⁴⟩_0`. Expand and use
Tide 10's moments: `⟨y⁴⟩_0 = 3/(λt)²`, `⟨y²⟩_0 = 1/(λt)`, odd moments
`= 0`. -/
theorem gibbsExp_h_quartic_harmonic_eq
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (h : ℝ) :
    Threepoint.gibbsExp (volume : Measure ℝ)
        (fun x : ℝ => lam / 2 * x ^ 2)
        (fun x : ℝ => x) t h
        (fun x : ℝ => x ^ 4)
      = 3 / (lam ^ 2 * t ^ 2) + 6 * h ^ 2 / (lam ^ 3 * t)
        + h ^ 4 / lam ^ 4 := by
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have ht_ne : t ≠ 0 := ne_of_gt ht
  rw [gibbsExp_harmonic_h_eq_unperturbed_shift hlam ht h (fun x : ℝ => x ^ 4)]
  set α : ℝ := h / lam with hα
  have hZ0 := int_pow_zero hlam ht
  have h0 := integrable_gauss_pow' hlam ht 0
  have h1 := integrable_gauss_pow' hlam ht 1
  have h2 := integrable_gauss_pow' hlam ht 2
  have h3 := integrable_gauss_pow' hlam ht 3
  have h4 := integrable_gauss_pow' hlam ht 4
  have h0' : Integrable
      (fun y : ℝ => Real.exp (-(t * (lam / 2 * y ^ 2)))) volume := by
    simpa using h0
  have h1' : Integrable
      (fun y : ℝ => y * Real.exp (-(t * (lam / 2 * y ^ 2)))) volume := by
    simpa [pow_one] using h1
  -- Pointwise: (y - α)⁴ · g(y)
  --   = y⁴ g - 4α y³ g + 6α² y² g - 4α³ y g + α⁴ g.
  have hnum_pt : (fun y : ℝ => (y - α) ^ 4 *
        Real.exp (-(t * (lam / 2 * y ^ 2)))) =
      (fun y : ℝ => y ^ 4 * Real.exp (-(t * (lam / 2 * y ^ 2)))
        - 4 * α * (y ^ 3 * Real.exp (-(t * (lam / 2 * y ^ 2))))
        + 6 * α ^ 2 * (y ^ 2 * Real.exp (-(t * (lam / 2 * y ^ 2))))
        - 4 * α ^ 3 * (y * Real.exp (-(t * (lam / 2 * y ^ 2))))
        + α ^ 4 * Real.exp (-(t * (lam / 2 * y ^ 2)))) := by
    funext y; ring
  -- Integrability of constant-mul scaled summands.
  have hint_4α_y3 : Integrable
      (fun y : ℝ => 4 * α *
        (y ^ 3 * Real.exp (-(t * (lam / 2 * y ^ 2))))) volume :=
    h3.const_mul (4 * α)
  have hint_6α2_y2 : Integrable
      (fun y : ℝ => 6 * α ^ 2 *
        (y ^ 2 * Real.exp (-(t * (lam / 2 * y ^ 2))))) volume :=
    h2.const_mul (6 * α ^ 2)
  have hint_4α3_y : Integrable
      (fun y : ℝ => 4 * α ^ 3 *
        (y * Real.exp (-(t * (lam / 2 * y ^ 2))))) volume :=
    h1'.const_mul (4 * α ^ 3)
  have hint_α4 : Integrable
      (fun y : ℝ => α ^ 4 * Real.exp (-(t * (lam / 2 * y ^ 2))))
      volume :=
    h0'.const_mul (α ^ 4)
  -- Numerator value. Build single-lambda integrability witnesses.
  have hint_AB : Integrable
      (fun y : ℝ => y ^ 4 * Real.exp (-(t * (lam / 2 * y ^ 2)))
        - 4 * α * (y ^ 3 * Real.exp (-(t * (lam / 2 * y ^ 2)))))
      volume := h4.sub hint_4α_y3
  have hint_CD : Integrable
      (fun y : ℝ => 6 * α ^ 2 * (y ^ 2 * Real.exp (-(t * (lam / 2 * y ^ 2))))
        - 4 * α ^ 3 * (y * Real.exp (-(t * (lam / 2 * y ^ 2)))))
      volume := hint_6α2_y2.sub hint_4α3_y
  have hint_ABCD : Integrable
      (fun y : ℝ => (y ^ 4 * Real.exp (-(t * (lam / 2 * y ^ 2)))
        - 4 * α * (y ^ 3 * Real.exp (-(t * (lam / 2 * y ^ 2)))))
        + (6 * α ^ 2 * (y ^ 2 * Real.exp (-(t * (lam / 2 * y ^ 2))))
          - 4 * α ^ 3 * (y * Real.exp (-(t * (lam / 2 * y ^ 2))))))
      volume := hint_AB.add hint_CD
  have hnum :
      (∫ y : ℝ, (y - α) ^ 4 * Real.exp (-(t * (lam / 2 * y ^ 2))))
        = 3 / ((lam * t) ^ 2) * Real.sqrt (2 * Real.pi / (lam * t))
          + 6 * α ^ 2 * ((1 / (lam * t)) *
              Real.sqrt (2 * Real.pi / (lam * t)))
          + α ^ 4 * Real.sqrt (2 * Real.pi / (lam * t)) := by
    rw [hnum_pt]
    rw [show (fun y : ℝ => y ^ 4 * Real.exp (-(t * (lam / 2 * y ^ 2)))
              - 4 * α * (y ^ 3 * Real.exp (-(t * (lam / 2 * y ^ 2))))
              + 6 * α ^ 2 * (y ^ 2 * Real.exp (-(t * (lam / 2 * y ^ 2))))
              - 4 * α ^ 3 * (y * Real.exp (-(t * (lam / 2 * y ^ 2))))
              + α ^ 4 * Real.exp (-(t * (lam / 2 * y ^ 2))))
            = (fun y : ℝ =>
                ((y ^ 4 * Real.exp (-(t * (lam / 2 * y ^ 2)))
                  - 4 * α * (y ^ 3 * Real.exp (-(t * (lam / 2 * y ^ 2)))))
                  + (6 * α ^ 2 * (y ^ 2 * Real.exp (-(t * (lam / 2 * y ^ 2))))
                    - 4 * α ^ 3 * (y * Real.exp (-(t * (lam / 2 * y ^ 2))))))
                + α ^ 4 * Real.exp (-(t * (lam / 2 * y ^ 2)))) by
        funext y; ring]
    rw [integral_add hint_ABCD hint_α4,
        integral_add hint_AB hint_CD,
        integral_sub h4 hint_4α_y3,
        integral_sub hint_6α2_y2 hint_4α3_y,
        integral_const_mul, integral_const_mul,
        integral_const_mul, integral_const_mul,
        int_pow_four hlam ht, int_pow_three hlam ht,
        int_pow_two hlam ht, int_pow_one hlam ht,
        int_pow_zero hlam ht]
    ring
  -- Combine with denominator.
  unfold Threepoint.gibbsExp
  change (∫ y : ℝ, (y - α) ^ 4 *
        Real.exp (-(t * (lam / 2 * y ^ 2 + 0 * y)))) /
      (∫ y : ℝ, Real.exp (-(t * (lam / 2 * y ^ 2 + 0 * y))))
      = 3 / (lam ^ 2 * t ^ 2) + 6 * h ^ 2 / (lam ^ 3 * t)
        + h ^ 4 / lam ^ 4
  have hreduce_num : (fun y : ℝ => (y - α) ^ 4 *
        Real.exp (-(t * (lam / 2 * y ^ 2 + 0 * y)))) =
      (fun y : ℝ => (y - α) ^ 4 *
        Real.exp (-(t * (lam / 2 * y ^ 2)))) := by
    funext y; congr 2; ring
  have hreduce_den : (fun y : ℝ =>
      Real.exp (-(t * (lam / 2 * y ^ 2 + 0 * y)))) =
      (fun y : ℝ => Real.exp (-(t * (lam / 2 * y ^ 2)))) := by
    funext y; congr 2; ring
  rw [hreduce_num, hreduce_den, hnum, hZ0]
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi / (lam * t)) := by
    apply Real.sqrt_pos.mpr; positivity
  have hsqrt_ne : Real.sqrt (2 * Real.pi / (lam * t)) ≠ 0 := hsqrt_pos.ne'
  rw [hα]
  field_simp

end Laplace.OneD
