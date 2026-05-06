import Laplace.OneD.Harmonic
import Threepoint.CrossSusceptibility

/-!
# Global constancy of the harmonic Gibbs covariance

For the harmonic Gibbs measure `μ_t,h(x) ∝ exp(-t((λ/2)x² + h·x))` on
ℝ against Lebesgue, with `λ, t > 0`, this file proves the
**global** identity

  `gibbsCov_h(x, x) = 1/(λ t)`        for all `h ∈ ℝ`.

The Tide 13 capstone (`HarmonicCrossSuscDeriv.lean`) proved only that
the *derivative* in `h` vanishes at `h = 0`. By a square-completion
argument the perturbed Gibbs measure factors as a translate of the
unperturbed Gaussian, so its variance is independent of `h` outright.

The proof is a closed-form evaluation of three perturbed integrals
(`∫ exp(-tL_h)`, `∫ x exp(-tL_h)`, `∫ x² exp(-tL_h)`), each obtained by
translation-invariance of Lebesgue (`integral_add_right_eq_self`) plus
the closed-form unperturbed integrals from
`Laplace.OneD.Harmonic` (Tide 10). No `GibbsObservable` hypotheses are
needed.

## Public API

* `partitionFunction_h_harmonic`:
    `∫ exp(-(t·((λ/2)x² + h·x))) dx = exp(t·h²/(2λ)) · √(2π/(λt))`.
* `gibbsExp_h_id_harmonic_eq`:
    `⟨x⟩_h = -h/λ` (the centroid shift).
* `gibbsExp_h_sq_harmonic_eq`:
    `⟨x²⟩_h = 1/(λt) + h²/λ²`.
* `gibbsCov_h_id_id_harmonic_eq`:
    `Cov_h(x, x) = 1/(λt)`, globally in `h`.

## Tide-step provenance

Tide step I4, formalised on `tide/global-constancy-harmonic-cov` in
laplace, branched off `main` (commit `141997c`). See
`sri/projects/primer/tide-log/2026-05-07-tide-global-constancy-harmonic-cov.md`.
-/

open Real MeasureTheory
open scoped Nat

namespace Laplace.OneD

/-! ## Square-completion identity -/

/-- The pointwise square-completion identity at the heart of the
file: `(λ/2)x² + h·x = (λ/2)(x + h/λ)² - h²/(2λ)`. -/
private lemma harmonic_h_square_completion
    {lam : ℝ} (hlam : 0 < lam) (h x : ℝ) :
    lam / 2 * x ^ 2 + h * x =
      lam / 2 * (x + h / lam) ^ 2 - h ^ 2 / (2 * lam) := by
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  field_simp
  ring

/-- The exponentiated form of `harmonic_h_square_completion`: factor
out the `h`-dependent constant. -/
private lemma harmonic_h_exp_factor
    {lam t : ℝ} (hlam : 0 < lam) (h x : ℝ) :
    Real.exp (-(t * (lam / 2 * x ^ 2 + h * x))) =
      Real.exp (t * h ^ 2 / (2 * lam)) *
        Real.exp (-(t * (lam / 2 * (x + h / lam) ^ 2))) := by
  have hkey : -(t * (lam / 2 * x ^ 2 + h * x)) =
      t * h ^ 2 / (2 * lam) + (-(t * (lam / 2 * (x + h / lam) ^ 2))) := by
    rw [harmonic_h_square_completion hlam]
    ring
  rw [hkey, Real.exp_add]

/-! ## Translation-shifted integrals -/

/-- Generic shift identity for any `f`: shift the integrand `f(x)`
against `exp(-(t·L_h))` to an integrand `f(y - h/λ)` against
`exp(-(t·L_0))`, modulo the constant `exp(t·h²/(2λ))`. -/
private lemma integral_with_perturbation_eq_shifted
    {lam t : ℝ} (hlam : 0 < lam) (h : ℝ) (f : ℝ → ℝ) :
    (∫ x : ℝ, f x * Real.exp (-(t * (lam / 2 * x ^ 2 + h * x))))
      = Real.exp (t * h ^ 2 / (2 * lam)) *
          (∫ y : ℝ, f (y - h / lam) *
            Real.exp (-(t * (lam / 2 * y ^ 2)))) := by
  have heq : (fun x : ℝ => f x * Real.exp (-(t * (lam / 2 * x ^ 2 + h * x))))
      = (fun x : ℝ => Real.exp (t * h ^ 2 / (2 * lam)) *
          (f x * Real.exp (-(t * (lam / 2 * (x + h / lam) ^ 2))))) := by
    funext x
    rw [harmonic_h_exp_factor hlam h x]
    ring
  rw [heq, integral_const_mul]
  congr 1
  set c : ℝ := h / lam with hc
  -- We need: ∫ f(x) · exp(-(t·(λ/2)·(x + c)²)) dx
  --        = ∫ f(y - c) · exp(-(t·(λ/2)·y²)) dy.
  -- Apply `integral_add_right_eq_self` with
  --   F(y) := f(y - c) * exp(-(t·(λ/2)·y²)),
  -- giving ∫ F(x + c) dx = ∫ F(y) dy. Note F(x + c) = f(x) · exp(-(t·(λ/2)·(x+c)²))
  -- because (x + c) - c = x.
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

/-! ## Integrability witnesses for the unperturbed Gaussian moments -/

/-- `Integrable (fun y => exp(-(t·(λ/2)·y²)))`, the base unperturbed
integrand. -/
private lemma integrable_harmonic_gauss
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    Integrable (fun y : ℝ => Real.exp (-(t * (lam / 2 * y ^ 2)))) volume := by
  have hb : 0 < lam * t / 2 := by positivity
  have h := integrable_exp_neg_mul_sq hb
  -- h : Integrable (fun x : ℝ => exp(-(lam*t/2) * x^2))
  have heq : (fun x : ℝ => Real.exp (-(lam * t / 2) * x ^ 2))
      = (fun y : ℝ => Real.exp (-(t * (lam / 2 * y ^ 2)))) := by
    funext y
    congr 1
    ring
  rw [heq] at h
  exact h

/-- `Integrable (fun y => y · exp(-(t·(λ/2)·y²)))`, the first-moment
integrand. -/
private lemma integrable_harmonic_gauss_id
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    Integrable
      (fun y : ℝ => y * Real.exp (-(t * (lam / 2 * y ^ 2)))) volume := by
  have hb : 0 < lam * t / 2 := by positivity
  have h := integrable_mul_exp_neg_mul_sq hb
  -- h : Integrable (fun x : ℝ => x * exp(-(lam*t/2) * x^2))
  have heq : (fun x : ℝ => x * Real.exp (-(lam * t / 2) * x ^ 2))
      = (fun y : ℝ => y * Real.exp (-(t * (lam / 2 * y ^ 2)))) := by
    funext y
    congr 1
    congr 1
    ring
  rw [heq] at h
  exact h

/-- `Integrable (fun y => y · y · exp(-(t·(λ/2)·y²)))`, the
second-moment integrand. -/
private lemma integrable_harmonic_gauss_sq
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    Integrable
      (fun y : ℝ => y * y * Real.exp (-(t * (lam / 2 * y ^ 2)))) volume := by
  have hb : 0 < lam * t / 2 := by positivity
  have hs : (-1 : ℝ) < (2 : ℝ) := by norm_num
  have h := integrable_rpow_mul_exp_neg_mul_sq hb hs
  -- h : Integrable (fun x : ℝ => x ^ (2 : ℝ) * exp(-(lam*t/2) * x^2))
  have heq : (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-(lam * t / 2) * x ^ 2))
      = (fun y : ℝ => y * y * Real.exp (-(t * (lam / 2 * y ^ 2)))) := by
    funext y
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast, Real.rpow_natCast]
    rw [show y ^ (2 : ℕ) = y * y from sq y]
    congr 1
    congr 1
    ring
  rw [heq] at h
  exact h

/-! ## Closed forms for the three unperturbed harmonic integrals at `(λ/2)·²` -/

/-- Bridge: `partitionFunction_harmonic` re-expressed without the
`harmonicPotential`/`Laplace.partitionFunction` wrappers. -/
private lemma harmonic_int_zero_pow
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    (∫ y : ℝ, Real.exp (-(t * (lam / 2 * y ^ 2))))
      = Real.sqrt (2 * Real.pi / (lam * t)) := by
  have := partitionFunction_harmonic hlam ht
  unfold Laplace.partitionFunction harmonicPotential at this
  exact this

/-- Bridge: `harmonic_int_pow_odd` at k=0, in the `(λ/2)·²` form. -/
private lemma harmonic_int_first_pow
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    (∫ y : ℝ, y * Real.exp (-(t * (lam / 2 * y ^ 2)))) = 0 := by
  have h := harmonic_int_pow_odd hlam ht 0
  -- h : ∫ x, x^(2*0+1) * exp(-(t * harmonicPotential lam x)) = 0
  -- i.e. ∫ x, x * exp(-(t * (lam/2 * x^2))) = 0 after simp
  unfold harmonicPotential at h
  simpa using h

/-- Closed-form for the second-moment integral: directly extracts
`∫ y² · exp(-(t·(λ/2)·y²)) = (1/(λt)) · √(2π/(λt))`.

The manipulation chains `harmonic_int_pow_even` (k=1) with the
algebraic identity `√(2π) · (λt)^{-(1+1/2)} = (1/(λt)) · √(2π/(λt))`. -/
private lemma harmonic_int_second_pow_simplified
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    (∫ y : ℝ, y * y * Real.exp (-(t * (lam / 2 * y ^ 2))))
      = (1 / (lam * t)) * Real.sqrt (2 * Real.pi / (lam * t)) := by
  have h := harmonic_int_pow_even hlam ht 1
  unfold harmonicPotential at h
  -- Convert x^(2*1) = x*x.
  have hr : (fun x : ℝ => x ^ (2 * 1) *
              Real.exp (-(t * (lam / 2 * x ^ 2)))) =
            (fun x : ℝ => x * x *
              Real.exp (-(t * (lam / 2 * x ^ 2)))) := by
    funext x
    rw [show (2 * 1 : ℕ) = 2 from rfl, sq]
  rw [hr] at h
  -- Reduce `((2*1-1 : ℕ)‼ : ℝ) = 1` and `((1 : ℕ) : ℝ) = (1 : ℝ)`.
  have hdf : (((2 * 1 - 1 : ℕ)‼ : ℝ)) = 1 := by
    change (((1 : ℕ) : ℝ)) = 1   -- 2*1-1 = 1, then 1‼ = 1, both definitional.
    exact Nat.cast_one
  rw [hdf, Nat.cast_one] at h
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

/-! ## The four public theorems -/

/-- **Closed form of the perturbed harmonic partition function.**

`∫ exp(-(t·((λ/2)x² + h·x))) dx = exp(t·h²/(2λ)) · √(2π/(λt))`.

By square completion, the perturbed Boltzmann factor is the
unperturbed one translated by `-h/λ`, modulo a multiplicative constant
`exp(t·h²/(2λ))`. Translation-invariance of Lebesgue then reduces the
integral to `partitionFunction_harmonic` (Tide 10). -/
theorem partitionFunction_h_harmonic
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (h : ℝ) :
    (∫ x : ℝ, Real.exp (-(t * (lam / 2 * x ^ 2 + h * x))))
      = Real.exp (t * h ^ 2 / (2 * lam)) *
          Real.sqrt (2 * Real.pi / (lam * t)) := by
  -- Apply the shift lemma with `f := 1`. Bridge: rewrite `exp(...)` as `1 * exp(...)`.
  have hrewrite : (fun x : ℝ => Real.exp (-(t * (lam / 2 * x ^ 2 + h * x))))
      = (fun x : ℝ =>
          (fun (_ : ℝ) => (1 : ℝ)) x *
          Real.exp (-(t * (lam / 2 * x ^ 2 + h * x)))) := by
    funext x; ring
  rw [hrewrite,
      integral_with_perturbation_eq_shifted hlam h
        (fun (_ : ℝ) => (1 : ℝ))]
  simp only [one_mul]
  rw [harmonic_int_zero_pow hlam ht]

/-- **Centroid of the perturbed harmonic Gibbs measure.**

`⟨x⟩_h = -h/λ` for all `h`.

The square-completion shift sends the centre of mass from `0` (in the
unperturbed Gibbs) to `-h/λ` (in the perturbed Gibbs). -/
theorem gibbsExp_h_id_harmonic_eq
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (h : ℝ) :
    Threepoint.gibbsExp (volume : Measure ℝ)
        (fun x : ℝ => lam / 2 * x ^ 2)
        (fun x : ℝ => x) t h
        (fun x : ℝ => x)
      = -h / lam := by
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have hZpos : 0 < Real.sqrt (2 * Real.pi / (lam * t)) := by
    apply Real.sqrt_pos.mpr; positivity
  have hgauss := integrable_harmonic_gauss hlam ht
  have hgauss_y := integrable_harmonic_gauss_id hlam ht
  -- Numerator: ∫ x · exp(-(t·L_h(x))) dx via the shift lemma.
  have hnum : (∫ x : ℝ, x * Real.exp (-(t * (lam / 2 * x ^ 2 + h * x))))
      = -(h / lam) * (Real.exp (t * h ^ 2 / (2 * lam)) *
          Real.sqrt (2 * Real.pi / (lam * t))) := by
    rw [integral_with_perturbation_eq_shifted hlam h (fun x : ℝ => x)]
    -- Goal: exp(...) * ∫ (y - h/λ) · g(y) dy = -(h/λ) * (exp(...) · √(...))
    -- Pointwise: (y - c) · g(y) = y · g(y) - c · g(y).
    have hint_const : Integrable
        (fun y : ℝ => (h / lam) * Real.exp (-(t * (lam / 2 * y ^ 2)))) volume :=
      hgauss.const_mul (h / lam)
    have hsplit_eq : (∫ y : ℝ, (y - h / lam) *
          Real.exp (-(t * (lam / 2 * y ^ 2))))
        = (∫ y : ℝ, y * Real.exp (-(t * (lam / 2 * y ^ 2))))
          - (∫ y : ℝ, (h / lam) * Real.exp (-(t * (lam / 2 * y ^ 2)))) := by
      rw [← integral_sub hgauss_y hint_const]
      apply integral_congr_ae
      filter_upwards with y
      ring
    rw [hsplit_eq, integral_const_mul,
        harmonic_int_first_pow hlam ht, harmonic_int_zero_pow hlam ht]
    ring
  -- Denominator: partitionFunction_h_harmonic.
  have hden := partitionFunction_h_harmonic hlam ht h
  have hden_ne : (∫ x : ℝ, Real.exp (-(t * (lam / 2 * x ^ 2 + h * x)))) ≠ 0 := by
    rw [hden]; positivity
  -- Combine into gibbsExp.
  unfold Threepoint.gibbsExp
  change (∫ w : ℝ, w * Real.exp (-(t * (lam / 2 * w ^ 2 + h * w)))) /
       (∫ w : ℝ, Real.exp (-(t * (lam / 2 * w ^ 2 + h * w))))
       = -h / lam
  rw [hnum, hden]
  have hcommon_ne : Real.exp (t * h ^ 2 / (2 * lam)) *
      Real.sqrt (2 * Real.pi / (lam * t)) ≠ 0 := by positivity
  field_simp

/-- **Second moment of the perturbed harmonic Gibbs measure.**

`⟨x²⟩_h = 1/(λt) + h²/λ²`. -/
theorem gibbsExp_h_sq_harmonic_eq
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (h : ℝ) :
    Threepoint.gibbsExp (volume : Measure ℝ)
        (fun x : ℝ => lam / 2 * x ^ 2)
        (fun x : ℝ => x) t h
        (fun x : ℝ => x * x)
      = 1 / (lam * t) + h ^ 2 / lam ^ 2 := by
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have hZpos : 0 < Real.sqrt (2 * Real.pi / (lam * t)) := by
    apply Real.sqrt_pos.mpr; positivity
  have hgauss := integrable_harmonic_gauss hlam ht
  have hgauss_y := integrable_harmonic_gauss_id hlam ht
  have hgauss_y2 := integrable_harmonic_gauss_sq hlam ht
  -- Numerator: ∫ x² · exp(-(t·L_h(x))) dx.
  -- Via shift lemma: = exp(...) · ∫ (y - c)² · g(y) dy
  --                = exp(...) · [⟨y²⟩₀_int - 2c·⟨y⟩₀_int + c²·⟨1⟩₀_int]
  --                = exp(...) · [(1/(λt))·Z₀ - 0 + c²·Z₀]
  --                = exp(...) · Z₀ · (1/(λt) + c²)
  have hnum : (∫ x : ℝ, x * x *
      Real.exp (-(t * (lam / 2 * x ^ 2 + h * x))))
      = (1 / (lam * t) + h ^ 2 / lam ^ 2) *
          (Real.exp (t * h ^ 2 / (2 * lam)) *
            Real.sqrt (2 * Real.pi / (lam * t))) := by
    rw [integral_with_perturbation_eq_shifted hlam h (fun x : ℝ => x * x)]
    -- Pointwise (y - c) · (y - c) · g(y)
    --   = y² · g(y) - 2c·y·g(y) + c²·g(y).
    have hint_yg2 : Integrable
        (fun y : ℝ => 2 * (h / lam) * (y * Real.exp (-(t * (lam / 2 * y ^ 2)))))
        volume :=
      hgauss_y.const_mul (2 * (h / lam))
    have hint_c2g : Integrable
        (fun y : ℝ => (h / lam) ^ 2 * Real.exp (-(t * (lam / 2 * y ^ 2))))
        volume :=
      hgauss.const_mul ((h / lam) ^ 2)
    have hint_diff : Integrable
        (fun y : ℝ => y * y * Real.exp (-(t * (lam / 2 * y ^ 2)))
          - 2 * (h / lam) *
            (y * Real.exp (-(t * (lam / 2 * y ^ 2))))) volume :=
      hgauss_y2.sub hint_yg2
    have hsplit_eq : (∫ y : ℝ, (y - h / lam) * (y - h / lam) *
          Real.exp (-(t * (lam / 2 * y ^ 2))))
        = (∫ y : ℝ, y * y * Real.exp (-(t * (lam / 2 * y ^ 2))))
          - (∫ y : ℝ, 2 * (h / lam) *
              (y * Real.exp (-(t * (lam / 2 * y ^ 2)))))
          + (∫ y : ℝ, (h / lam) ^ 2 *
              Real.exp (-(t * (lam / 2 * y ^ 2)))) := by
      rw [← integral_sub hgauss_y2 hint_yg2,
          ← integral_add hint_diff hint_c2g]
      apply integral_congr_ae
      filter_upwards with y
      ring
    rw [hsplit_eq,
        integral_const_mul, integral_const_mul,
        harmonic_int_second_pow_simplified hlam ht,
        harmonic_int_first_pow hlam ht,
        harmonic_int_zero_pow hlam ht]
    ring
  -- Denominator.
  have hden := partitionFunction_h_harmonic hlam ht h
  have hden_ne : (∫ x : ℝ, Real.exp (-(t * (lam / 2 * x ^ 2 + h * x)))) ≠ 0 := by
    rw [hden]; positivity
  -- Combine.
  unfold Threepoint.gibbsExp
  change (∫ w : ℝ, w * w * Real.exp (-(t * (lam / 2 * w ^ 2 + h * w)))) /
       (∫ w : ℝ, Real.exp (-(t * (lam / 2 * w ^ 2 + h * w))))
       = 1 / (lam * t) + h ^ 2 / lam ^ 2
  rw [hnum, hden]
  have hcommon_ne : Real.exp (t * h ^ 2 / (2 * lam)) *
      Real.sqrt (2 * Real.pi / (lam * t)) ≠ 0 := by positivity
  field_simp

/-- **Global constancy of the harmonic Gibbs covariance.**

For all `h ∈ ℝ`,

  `Cov_h(x, x) = 1/(λ t)`.

This strengthens Tide 13's `cov_h_id_id_deriv_harmonic_eq_zero` (which
established only zero *derivative* at `h = 0` via the κ₃ route) to the
*global* statement that the covariance is constant in `h`. The proof
proceeds without any `GibbsObservable` hypotheses by direct
closed-form evaluation, using square-completion + translation
invariance of Lebesgue. -/
theorem gibbsCov_h_id_id_harmonic_eq
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (h : ℝ) :
    Threepoint.gibbsCov (volume : Measure ℝ)
        (fun x : ℝ => lam / 2 * x ^ 2)
        (fun x : ℝ => x) t h
        (fun x : ℝ => x) (fun x : ℝ => x)
      = 1 / (lam * t) := by
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  unfold Threepoint.gibbsCov
  -- The product integrand `(fun w => x w * x w)` reduces to `(fun w => w * w)` by β.
  change Threepoint.gibbsExp (volume : Measure ℝ)
        (fun x : ℝ => lam / 2 * x ^ 2)
        (fun x : ℝ => x) t h
        (fun w : ℝ => w * w)
       - Threepoint.gibbsExp (volume : Measure ℝ)
          (fun x : ℝ => lam / 2 * x ^ 2)
          (fun x : ℝ => x) t h
          (fun x : ℝ => x) *
        Threepoint.gibbsExp (volume : Measure ℝ)
          (fun x : ℝ => lam / 2 * x ^ 2)
          (fun x : ℝ => x) t h
          (fun x : ℝ => x)
       = 1 / (lam * t)
  rw [gibbsExp_h_sq_harmonic_eq hlam ht h, gibbsExp_h_id_harmonic_eq hlam ht h]
  field_simp
  ring

end Laplace.OneD
