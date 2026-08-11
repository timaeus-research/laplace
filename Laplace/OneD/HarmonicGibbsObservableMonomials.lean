import Laplace.OneD.HarmonicGibbsRegularity
import Threepoint.CrossSusceptibility

/-!
# `Threepoint.GibbsObservable` instances for harmonic monomials

Concrete `Threepoint.GibbsObservable` instances for the
harmonic potential `L(x) = (λ/2) x²` with linear perturbation
`A(x) = x` and monomial observables `(fun x => x^k)` for `k : ℕ`. This
makes Tide 13's `cov_h_id_id_deriv_harmonic_eq_zero` unconditional on
the `GibbsObservable` hypotheses for the canonical `x, x², x³`
observables.

## Strategy

After the GPT-5.5 Pro deliberation, the chosen route is **dominated
differentiation under the integral sign** (not the closed-form
binomial-expansion route): apply
`MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le` with
a Gaussian-domination bound
\[
  |x^k \cdot e^{-(t\,((\lambda/2)x^2 + h\,x))}|
    \;\le\; C \cdot |x|^k \cdot e^{-(t\lambda/4)\,x^2}
\]
valid for `|h| ≤ 1` (Young's inequality:
`|hx| ≤ (λ/4)x² + h²/λ` absorbs the linear perturbation into the
quadratic decay). Integrability of the dominator falls out from
Mathlib's `integrable_rpow_mul_exp_neg_mul_sq`
(`Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`).

The dominated-differentiation route is cleaner than the closed-form
route here because (i) it is generic in `k : ℕ` at no extra cost,
(ii) it avoids needing a central-Gaussian-moment library (M₂, M₄, …)
that Mathlib v4.29.0 doesn't ship in the form we need, and (iii) the
integrability infrastructure is already in Mathlib.

## Status

This file provides the headline generic-`k` instance
and its `x, x², x³` specialisations, built on a small ladder of
foundational lemmas.

- `harmonic_perturbed_numerator_zero_eq` (and its `_pow` form): the
  `h = 0` reduction of the perturbed monomial numerator. Discharges
  the first conjunct of `Threepoint.GibbsObservable` for any monomial
  observable.
- The analytic core (`abs_mul_le_quarter_lambda_sq_add` Young bound,
  `dominator_integrable_pow`, `harmonic_perturbed_integrand_pow_bound`,
  `harmonic_perturbed_integrand_pow_hasDerivAt`) feeds the dominated
  differentiation.
- The headline `Threepoint.harmonic_id_gibbsObservable_pow` builds the
  full `GibbsObservable` instance for every monomial observable
  `x ↦ x^k`, and `Threepoint.harmonic_id_gibbsObservable_id`,
  `_mul_self`, `_mul_mul_self` are the `k = 1, 2, 3` (`x, x², x³`)
  specialisations that make Tide 13's
  `cov_h_id_id_deriv_harmonic_eq_zero` unconditional on those
  canonical observables.

## Tide-step provenance

Tide step (G4 from the 7 May candidates survey),
`tide/harmonic-gibbsobservable-monomials` branch, off laplace `main`
at `f21a9cc`. Tide log:
`sri/projects/patterning/tide-log/2026-05-07-tide-harmonic-gibbsobservable-monomials.md`.
-/

open MeasureTheory

namespace Laplace.OneD

/-! ## The `h = 0` identity for monomial-numerator integrals

`Threepoint.GibbsObservable μ L A t φ` is a conjunction; the first
conjunct asks that the numerator
`∫ φ(w) · exp(-(t · (L(w) + 0 · A(w)))) ∂μ` reduces to
`∫ φ(w) · exp(-(t · L(w))) ∂μ`. For the harmonic + linear setup
`(L, A) = ((λ/2)·², id)` with monomial `φ(x) = x^k`, this is a
`simp [zero_mul, add_zero]`-style reduction. The lemma below does the
reduction once for any observable; it is independent of the choice of
`φ` and even of `k`. -/

/-- For the harmonic potential `(λ/2)·x²` with linear perturbation
`A(x) = x`, the perturbed numerator at `h = 0` reduces to the
unperturbed integral. Independent of the observable `φ`. -/
theorem harmonic_perturbed_numerator_zero_eq
    (lam t : ℝ) (φ : ℝ → ℝ) :
    (∫ w : ℝ, φ w * Real.exp (-(t * ((lam / 2) * w ^ 2 + 0 * w))))
      = (∫ w : ℝ, φ w * Real.exp (-(t * ((lam / 2) * w ^ 2)))) := by
  congr 1
  funext w
  ring_nf

/-- Specialisation to monomial observables. Matches the first conjunct
of `Threepoint.GibbsObservable` for `(volume, harmonic, id)` at
`φ(x) = x^k`. -/
theorem harmonic_perturbed_numerator_zero_eq_pow
    (lam t : ℝ) (k : ℕ) :
    (∫ w : ℝ, w ^ k * Real.exp (-(t * ((lam / 2) * w ^ 2 + 0 * w))))
      = (∫ w : ℝ, w ^ k * Real.exp (-(t * ((lam / 2) * w ^ 2)))) :=
  harmonic_perturbed_numerator_zero_eq lam t (fun w => w ^ k)

/-! ## Analytic core: Young inequality + dominator -/

/-- Young's inequality with weight `λ/2`. For `lam > 0`,
`|h · x| ≤ (lam/4) · x² + h² / lam`. -/
lemma abs_mul_le_quarter_lambda_sq_add (lam : ℝ) (hlam : 0 < lam)
    (h x : ℝ) :
    |h * x| ≤ (lam / 4) * x ^ 2 + h ^ 2 / lam := by
  have h4lam : (0 : ℝ) < 4 * lam := by linarith
  refine abs_le.mpr ⟨?_, ?_⟩
  · -- -((lam/4) · x² + h²/lam) ≤ h · x.
    -- Equivalent (×4·lam) to (lam·x + 2·h)² ≥ 0.
    have hsq : 0 ≤ lam ^ 2 * x ^ 2 + 4 * lam * h * x + 4 * h ^ 2 := by
      have := sq_nonneg (lam * x + 2 * h); nlinarith [this]
    have step : ((lam / 4) * x ^ 2 + h ^ 2 / lam) - (-(h * x))
              = (lam ^ 2 * x ^ 2 + 4 * lam * h * x + 4 * h ^ 2) / (4 * lam) := by
      field_simp; ring
    have hge : 0 ≤ ((lam / 4) * x ^ 2 + h ^ 2 / lam) - (-(h * x)) := by
      rw [step]; exact div_nonneg hsq h4lam.le
    linarith
  · -- h · x ≤ (lam/4) · x² + h²/lam.
    -- Equivalent (×4·lam) to (lam·x − 2·h)² ≥ 0.
    have hsq : 0 ≤ lam ^ 2 * x ^ 2 - 4 * lam * h * x + 4 * h ^ 2 := by
      have := sq_nonneg (lam * x - 2 * h); nlinarith [this]
    have step : ((lam / 4) * x ^ 2 + h ^ 2 / lam) - (h * x)
              = (lam ^ 2 * x ^ 2 - 4 * lam * h * x + 4 * h ^ 2) / (4 * lam) := by
      field_simp; ring
    have hge : 0 ≤ ((lam / 4) * x ^ 2 + h ^ 2 / lam) - (h * x) := by
      rw [step]; exact div_nonneg hsq h4lam.le
    linarith

/-- Integrability of the dominator `|x|^k · exp(-c · x²)` for `c > 0`,
`k : ℕ`. Routed through `integrable_rpow_mul_exp_neg_mul_sq` after
casting `k : ℕ` to `(k : ℝ)`, then matching `|x|^k · exp(...)` against
`‖x^k · exp(...)‖` via `Real.norm_eq_abs` and `abs_pow`. -/
lemma dominator_integrable_pow {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k * Real.exp (-c * x ^ 2)) := by
  have h_xk : Integrable (fun x : ℝ => x ^ k * Real.exp (-c * x ^ 2)) := by
    have hk : (-1 : ℝ) < (k : ℝ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith
    have h := integrable_rpow_mul_exp_neg_mul_sq hc (s := (k : ℝ)) hk
    have heq : (fun x : ℝ => x ^ ((k : ℕ) : ℝ) * Real.exp (-c * x ^ 2))
        = (fun x : ℝ => x ^ k * Real.exp (-c * x ^ 2)) := by
      funext x; rw [Real.rpow_natCast]
    rwa [heq] at h
  have h_norm := h_xk.norm
  refine h_norm.congr (Filter.Eventually.of_forall fun x => ?_)
  change ‖x ^ k * Real.exp (-c * x ^ 2)‖ = |x| ^ k * Real.exp (-c * x ^ 2)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, Real.abs_exp]

/-- Pointwise domination bound for the perturbed integrand. For `lam > 0`,
`t > 0`, `|h| ≤ 1`, and any `k : ℕ`,
`‖x^k · exp(-(t · ((lam/2) · x² + h · x)))‖
  ≤ exp(t/lam) · |x|^k · exp(-(t·lam/4) · x²)`.
The Gaussian-shaped `bound(x)` for the dominated-differentiation
invocation. -/
lemma harmonic_perturbed_integrand_pow_bound
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t)
    (k : ℕ) {h : ℝ} (hh : |h| ≤ 1) (x : ℝ) :
    ‖x ^ k * Real.exp (-(t * ((lam / 2) * x ^ 2 + h * x)))‖
      ≤ Real.exp (t / lam) * |x| ^ k *
          Real.exp (-(t * lam / 4) * x ^ 2) := by
  -- Step 1: Young + monotonicity of exp give
  --   exp(-(t · ((lam/2) · x² + h · x)))
  --     ≤ exp(t · h² / lam) · exp(-(t·lam/4) · x²).
  have h_young : -(h * x) ≤ (lam / 4) * x ^ 2 + h ^ 2 / lam := by
    have := abs_mul_le_quarter_lambda_sq_add lam hlam h x
    have h_neg : -(h * x) ≤ |h * x| := neg_le_abs _
    linarith
  have h_lower : (lam / 4) * x ^ 2 - h ^ 2 / lam
                  ≤ (lam / 2) * x ^ 2 + h * x := by linarith
  have h_exp_arg :
      -(t * ((lam / 2) * x ^ 2 + h * x))
        ≤ -(t * lam / 4) * x ^ 2 + t * h ^ 2 / lam := by
    have ht_le : t * ((lam / 4) * x ^ 2 - h ^ 2 / lam)
        ≤ t * ((lam / 2) * x ^ 2 + h * x) :=
      mul_le_mul_of_nonneg_left h_lower ht.le
    have step :
        -(t * ((lam / 4) * x ^ 2 - h ^ 2 / lam))
          = -(t * lam / 4) * x ^ 2 + t * h ^ 2 / lam := by ring
    linarith
  have h_exp_le :
      Real.exp (-(t * ((lam / 2) * x ^ 2 + h * x)))
        ≤ Real.exp (-(t * lam / 4) * x ^ 2 + t * h ^ 2 / lam) :=
    Real.exp_le_exp.mpr h_exp_arg
  -- Step 2: For |h| ≤ 1, t·h²/lam ≤ t/lam.
  have h_sq_le : h ^ 2 ≤ 1 := by
    have hh' := sq_abs h
    have := pow_le_pow_left₀ (abs_nonneg h) hh 2
    nlinarith
  have h_coef_le : t * h ^ 2 / lam ≤ t / lam := by
    have h_num : t * h ^ 2 ≤ t * 1 :=
      mul_le_mul_of_nonneg_left h_sq_le ht.le
    have h_num' : t * h ^ 2 ≤ t := by linarith
    exact (div_le_div_iff_of_pos_right hlam).mpr h_num'
  -- Step 3: Combine the two bounds.
  have h_exp_split :
      Real.exp (-(t * lam / 4) * x ^ 2 + t * h ^ 2 / lam)
        = Real.exp (t * h ^ 2 / lam) *
          Real.exp (-(t * lam / 4) * x ^ 2) := by
    rw [add_comm, Real.exp_add]
  have h_exp_coef :
      Real.exp (t * h ^ 2 / lam) ≤ Real.exp (t / lam) :=
    Real.exp_le_exp.mpr h_coef_le
  -- Step 4: Reshape ‖x^k · exp(...)‖ = |x|^k · exp(...) and finish.
  have h_xk_nn : 0 ≤ |x| ^ k := pow_nonneg (abs_nonneg _) k
  rw [Real.norm_eq_abs, abs_mul, abs_pow, Real.abs_exp]
  calc |x| ^ k * Real.exp (-(t * ((lam / 2) * x ^ 2 + h * x)))
      ≤ |x| ^ k * Real.exp (-(t * lam / 4) * x ^ 2 + t * h ^ 2 / lam) := by
          exact mul_le_mul_of_nonneg_left h_exp_le h_xk_nn
    _ = |x| ^ k * (Real.exp (t * h ^ 2 / lam) *
                   Real.exp (-(t * lam / 4) * x ^ 2)) := by
          rw [h_exp_split]
    _ ≤ |x| ^ k * (Real.exp (t / lam) *
                   Real.exp (-(t * lam / 4) * x ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ h_xk_nn
          exact mul_le_mul_of_nonneg_right h_exp_coef (Real.exp_pos _).le
    _ = Real.exp (t / lam) * |x| ^ k *
          Real.exp (-(t * lam / 4) * x ^ 2) := by ring

/-! ## Pointwise differentiability of the perturbed numerator integrand

For each fixed `x`, the function
`h ↦ x^k · exp(-(t · ((lam/2) · x² + h · x)))` is `C^∞`. The derivative
in `h` is the pointwise product
`x^k · (-(t · x)) · exp(-(t · ((lam/2) · x² + h · x)))`
which we expose in the form needed by `Threepoint.GibbsObservable`. -/

/-- Pointwise derivative in `h` of the perturbed monomial numerator
integrand. -/
lemma harmonic_perturbed_integrand_pow_hasDerivAt
    (lam t : ℝ) (k : ℕ) (h x : ℝ) :
    HasDerivAt
      (fun h : ℝ => x ^ k * Real.exp (-(t * ((lam / 2) * x ^ 2 + h * x))))
      (x ^ k * (-(t * x) *
        Real.exp (-(t * ((lam / 2) * x ^ 2 + h * x))))) h := by
  -- Build via the chain: affine in h ↦ const_mul t ↦ neg ↦ exp ↦ const_mul x^k.
  have h_id : HasDerivAt (fun h : ℝ => h * x) x h := by
    have := (hasDerivAt_id h).mul_const x
    simpa using this
  have h_aff : HasDerivAt (fun h : ℝ => (lam / 2) * x ^ 2 + h * x) x h := by
    have h_const : HasDerivAt (fun _ : ℝ => (lam / 2) * x ^ 2) 0 h :=
      hasDerivAt_const h ((lam / 2) * x ^ 2)
    have hsum : HasDerivAt
        (fun y : ℝ => (lam / 2) * x ^ 2 + y * x) (0 + x) h := h_const.add h_id
    have hzero : (0 : ℝ) + x = x := zero_add x
    rwa [hzero] at hsum
  have h_scale : HasDerivAt
      (fun h : ℝ => t * ((lam / 2) * x ^ 2 + h * x)) (t * x) h :=
    h_aff.const_mul t
  have h_neg : HasDerivAt
      (fun h : ℝ => -(t * ((lam / 2) * x ^ 2 + h * x))) (-(t * x)) h :=
    h_scale.neg
  have h_exp := h_neg.exp
  -- h_exp : HasDerivAt (fun h => exp(-(t·...))) (exp(-(t·...)) · (-(t·x))) h.
  have h_total := h_exp.const_mul (x ^ k)
  -- h_total has derivative `x^k · (exp(-(t·...)) · (-(t·x)))`; reshape to match.
  convert h_total using 1
  ring

/-! ## The `GibbsObservable` instance for monomial observables -/

/-- **Concrete `Threepoint.GibbsObservable` for the harmonic + linear
perturbation case at monomial observables.** For `lam > 0`, `t > 0`,
`k : ℕ`,
`Threepoint.GibbsObservable volume ((λ/2)·²) id t (·^k)` holds.
This makes `Tide 13`'s `cov_h_id_id_deriv_harmonic_eq_zero` unconditional
on the `GibbsObservable` hypotheses for the canonical monomials
`x, x², x³`.

The first conjunct is the `h = 0` reduction
(`harmonic_perturbed_numerator_zero_eq_pow`); the second is the
`HasDerivAt` of the perturbed numerator at `h = 0`, proved by
dominated differentiation under the integral via
`MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le` with
the Gaussian-shaped dominator from
`harmonic_perturbed_integrand_pow_bound` (at index `k+1`, applied to
the derivative integrand). -/
theorem _root_.Threepoint.harmonic_id_gibbsObservable_pow
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) (k : ℕ) :
    Threepoint.GibbsObservable (volume : Measure ℝ)
      (fun x : ℝ => lam / 2 * x ^ 2)
      (fun x : ℝ => x) t (fun x : ℝ => x ^ k) := by
  refine ⟨?_, ?_⟩
  · -- First conjunct: h = 0 numerator identity.
    -- Note: GibbsObservable uses `L w + 0 * A w` with our `L = (λ/2)·²` and `A = id`,
    -- which expands to `(λ/2)·x² + 0 · x = (λ/2)·x²`. Match against our primitive.
    exact harmonic_perturbed_numerator_zero_eq_pow lam t k
  · -- Second conjunct: HasDerivAt of the perturbed numerator at h = 0.
    -- Apply `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with:
    --   - F h x = x^k · exp(-(t · ((lam/2)·x² + h·x)))
    --   - F' h x = x^k · (-(t·x)) · exp(-(t · ((lam/2)·x² + h·x)))
    --   - bound x = exp(t/lam) · t · |x|^(k+1) · exp(-(t·lam/4)·x²) (≥ ‖F' h x‖ for |h| ≤ 1).
    have hball : Metric.ball (0 : ℝ) 1 ∈ nhds (0 : ℝ) :=
      Metric.ball_mem_nhds _ one_pos
    -- Integrability of F at h = 0.
    have hF_int : Integrable
        (fun x : ℝ => x ^ k * Real.exp (-(t * ((lam / 2) * x ^ 2 + 0 * x)))) := by
      have : (fun x : ℝ => x ^ k * Real.exp (-(t * ((lam / 2) * x ^ 2 + 0 * x))))
           = (fun x : ℝ => x ^ k * Real.exp (-(t * ((lam / 2) * x ^ 2)))) := by
        funext x; ring_nf
      rw [this]
      -- Reduce to integrability of `x^k · exp(-(c · x²))` for `c = t · lam / 2`.
      have htl : 0 < t * lam / 2 := by positivity
      have hk : (-1 : ℝ) < (k : ℝ) := by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith
      have h_rpow := integrable_rpow_mul_exp_neg_mul_sq htl (s := (k : ℝ)) hk
      have heq : (fun x : ℝ => x ^ ((k : ℕ) : ℝ) * Real.exp (-(t * lam / 2) * x ^ 2))
          = (fun x : ℝ => x ^ k * Real.exp (-(t * ((lam / 2) * x ^ 2)))) := by
        funext x
        rw [Real.rpow_natCast]
        congr 2; ring
      rwa [heq] at h_rpow
    -- AE strong measurability of F (continuous in x).
    have hF_meas : ∀ᶠ h in nhds (0 : ℝ),
        AEStronglyMeasurable
          (fun x : ℝ => x ^ k * Real.exp (-(t * ((lam / 2) * x ^ 2 + h * x))))
          (volume : Measure ℝ) := by
      refine Filter.Eventually.of_forall fun h => ?_
      refine Continuous.aestronglyMeasurable ?_
      fun_prop
    -- AE strong measurability of F' at h = 0.
    have hF'_meas : AEStronglyMeasurable
        (fun x : ℝ => x ^ k *
          (-(t * x) * Real.exp (-(t * ((lam / 2) * x ^ 2 + 0 * x)))))
        (volume : Measure ℝ) := by
      refine Continuous.aestronglyMeasurable ?_
      fun_prop
    -- The dominator: bound x = t · exp(t/lam) · |x|^(k+1) · exp(-(t·lam/4)·x²).
    set bound : ℝ → ℝ :=
      fun x => t * (Real.exp (t / lam) * |x| ^ (k + 1) *
        Real.exp (-(t * lam / 4) * x ^ 2)) with hbound_def
    -- Integrability of the dominator.
    have h_bound_int : Integrable bound := by
      have htl4 : (0 : ℝ) < t * lam / 4 := by positivity
      have h_dom := dominator_integrable_pow htl4 (k + 1)
      have h_const := h_dom.const_mul (Real.exp (t / lam))
      have h_total := h_const.const_mul t
      have heq : (fun x : ℝ => t * (Real.exp (t / lam) *
            (|x| ^ (k + 1) * Real.exp (-(t * lam / 4) * x ^ 2))))
            = bound := by
        funext x; rw [hbound_def]; ring
      rw [← heq]; exact h_total
    -- The bound on F' h x: |F' h x| ≤ bound x for |h| ≤ 1.
    have h_F'_bound : ∀ᵐ x : ℝ ∂volume, ∀ h ∈ Metric.ball (0 : ℝ) 1,
        ‖x ^ k * (-(t * x) *
            Real.exp (-(t * ((lam / 2) * x ^ 2 + h * x))))‖ ≤ bound x := by
      refine Filter.Eventually.of_forall fun x h hx => ?_
      have hh_lt : |h| < 1 := by
        rw [Metric.mem_ball, dist_zero_right] at hx
        simpa using hx
      have hh_le : |h| ≤ 1 := hh_lt.le
      -- Rewrite x^k · (-(t·x)) · exp(...) as (-t) · x^(k+1) · exp(...).
      have h_rewrite :
          x ^ k * (-(t * x) *
              Real.exp (-(t * ((lam / 2) * x ^ 2 + h * x))))
            = (-t) * (x ^ (k + 1) *
              Real.exp (-(t * ((lam / 2) * x ^ 2 + h * x)))) := by
        rw [pow_succ]; ring
      rw [h_rewrite, norm_mul, Real.norm_eq_abs, abs_neg, abs_of_pos ht]
      have h_inner :=
        harmonic_perturbed_integrand_pow_bound hlam ht (k + 1) hh_le x
      -- h_inner : ‖x^(k+1) · exp(-(t·...))‖ ≤ exp(t/lam) · |x|^(k+1) · exp(-(t·lam/4)·x²).
      have hbound_x :
          bound x = t * (Real.exp (t / lam) * |x| ^ (k + 1) *
            Real.exp (-(t * lam / 4) * x ^ 2)) := rfl
      rw [hbound_x]
      exact mul_le_mul_of_nonneg_left h_inner ht.le
    -- Pointwise HasDerivAt for each x and each h ∈ ball 0 1.
    have h_diff : ∀ᵐ x : ℝ ∂volume, ∀ h ∈ Metric.ball (0 : ℝ) 1,
        HasDerivAt (fun h : ℝ =>
            x ^ k * Real.exp (-(t * ((lam / 2) * x ^ 2 + h * x))))
          (x ^ k * (-(t * x) *
            Real.exp (-(t * ((lam / 2) * x ^ 2 + h * x))))) h := by
      refine Filter.Eventually.of_forall fun x h _ => ?_
      exact harmonic_perturbed_integrand_pow_hasDerivAt lam t k h x
    -- Apply the dominated-differentiation theorem.
    have h_total :=
      hasDerivAt_integral_of_dominated_loc_of_deriv_le hball hF_meas hF_int
        hF'_meas h_F'_bound h_bound_int h_diff
    -- h_total.2 has the form
    --   HasDerivAt (fun n ↦ ∫ a, a^k · exp(-(t·((λ/2)·a² + n·a)))) (...) 0
    -- with derivative integral evaluated at the perturbed integrand at h=0.
    -- The expected GibbsObservable shape has the unperturbed exp form
    -- (no `+ 0·a` inside). Simplify the derivative integrand by `0·a = 0` then `+0`.
    have h_d := h_total.2
    have h_eq_deriv :
        (∫ a : ℝ, a ^ k *
            (-(t * a) * Real.exp (-(t * ((lam / 2) * a ^ 2 + 0 * a))))
              ∂(volume : Measure ℝ))
          = (∫ w : ℝ, w ^ k *
              ((-t * w) * Real.exp (-(t * ((lam / 2) * w ^ 2))))
                ∂(volume : Measure ℝ)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with a
      ring_nf
    rw [h_eq_deriv] at h_d
    exact h_d

/-! ## Multiplicative-form wrappers

`Threepoint.harmonic_id_gibbsObservable_pow` produces
`GibbsObservable ... (fun x => x^k)` for any `k : ℕ`. Tide 13's
`cov_h_id_id_deriv_harmonic_eq_zero` consumes the same content but
in multiplicative form (`x`, `x*x`, `x*x*x`) at the slot pair
`(φ, ψ) = (id, id)`. The functions are propositionally equal but
not definitionally equal; we transport along function-extensional
equality via `funext; ring`.

These three wrappers, together with the headline
`cov_h_id_id_deriv_harmonic_eq_zero_unconditional` in
`HarmonicCrossSuscDeriv.lean`, complete the U2 discharge tide:
Tide 13's conditional theorem becomes unconditional. -/

/-- `GibbsObservable` for `fun x => x` (the linear monomial in
multiplicative form). G4's `pow` instance at `k = 1` rewritten
via `funext; ring`. -/
theorem _root_.Threepoint.harmonic_id_gibbsObservable_id
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    Threepoint.GibbsObservable (volume : Measure ℝ)
      (fun x : ℝ => lam / 2 * x ^ 2)
      (fun x : ℝ => x) t (fun x : ℝ => x) := by
  have h := Threepoint.harmonic_id_gibbsObservable_pow hlam ht 1
  have heq : (fun x : ℝ => x ^ 1) = (fun x : ℝ => x) := by
    funext x; ring
  rwa [heq] at h

/-- `GibbsObservable` for `fun x => x * x` (the quadratic monomial in
multiplicative form). G4's `pow` instance at `k = 2` rewritten via
`funext; ring`. -/
theorem _root_.Threepoint.harmonic_id_gibbsObservable_mul_self
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    Threepoint.GibbsObservable (volume : Measure ℝ)
      (fun x : ℝ => lam / 2 * x ^ 2)
      (fun x : ℝ => x) t (fun x : ℝ => x * x) := by
  have h := Threepoint.harmonic_id_gibbsObservable_pow hlam ht 2
  have heq : (fun x : ℝ => x ^ 2) = (fun x : ℝ => x * x) := by
    funext x; ring
  rwa [heq] at h

/-- `GibbsObservable` for `fun x => x * x * x` (the cubic monomial in
multiplicative form). G4's `pow` instance at `k = 3` rewritten via
`funext; ring`. -/
theorem _root_.Threepoint.harmonic_id_gibbsObservable_mul_mul_self
    {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    Threepoint.GibbsObservable (volume : Measure ℝ)
      (fun x : ℝ => lam / 2 * x ^ 2)
      (fun x : ℝ => x) t (fun x : ℝ => x * x * x) := by
  have h := Threepoint.harmonic_id_gibbsObservable_pow hlam ht 3
  have heq : (fun x : ℝ => x ^ 3) = (fun x : ℝ => x * x * x) := by
    funext x; ring
  rwa [heq] at h

end Laplace.OneD
