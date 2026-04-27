import Laplace.ScalarBound
import Laplace.OneD.GaussianMoments
import Laplace.OneD.Anharmonic
import Laplace.OneD.Rescaling

/-!
# Pointwise integrand bound for the perturbative remainder

We combine the scalar Taylor bound from `Laplace.ScalarBound` with Gaussian
weight factors to get pointwise estimates of the form

  `|u^n · e^{-u²/2} · (e^{-s} - (1 - s))|
     ≤ (s² / 2) · |u|^n · e^{-u²/2} · max 1 (e^{-s})`.

In the application, `s = s_t(u) = A · u³/√t + B · u⁴/t` with `A, B` depending
on the anharmonic coefficients. Under the coercivity hypothesis from
`Laplace.OneD.Anharmonic`, the right-hand side is dominated by a Gaussian in
`u` and has explicit decay in `t`, giving the global `O(1/t)` integral
remainder estimate (next piece).

This file is a straightforward consequence of the scalar bound; no new
analytic content beyond the algebra.
-/

open Real Set MeasureTheory
open scoped Nat

namespace Laplace.OneD

/-- **Pointwise perturbative remainder bound** in the Gaussian-weighted form
needed for the Laplace asymptotic. For all `n : ℕ`, `u s : ℝ`,

  `|u^n · e^{-u²/2} · (e^{-s} - (1 - s))|
     ≤ (s² / 2) · |u|^n · e^{-u²/2} · max 1 (e^{-s})`.

Proof: factor the absolute value, apply `abs_exp_neg_sub_one_add_le`. -/
theorem perturbation_remainder_pointwise (n : ℕ) (u s : ℝ) :
    |u ^ n * Real.exp (-(u ^ 2) / 2) * (Real.exp (-s) - (1 - s))| ≤
      (s ^ 2 / 2) * |u| ^ n * Real.exp (-(u ^ 2) / 2) * max 1 (Real.exp (-s)) := by
  have hexp_pos : 0 < Real.exp (-(u ^ 2) / 2) := Real.exp_pos _
  have hmax_pos : 0 < max 1 (Real.exp (-s)) :=
    lt_max_of_lt_left (by norm_num : (0 : ℝ) < 1)
  -- Split absolute value across the product.
  rw [abs_mul, abs_mul, abs_pow, abs_of_pos hexp_pos]
  -- Goal: |u|^n · e^{-u²/2} · |exp(-s) - (1 - s)| ≤ (s²/2) · |u|^n · e^{-u²/2} · max(1, e^{-s}).
  -- Bound the absolute value of the Taylor remainder by `Laplace.abs_exp_neg_sub_one_add_le`.
  have hbound := Laplace.abs_exp_neg_sub_one_add_le s
  -- Rearrange to put |u|^n · e^{-u²/2} as a common factor and apply.
  rw [show (s ^ 2 / 2 * |u| ^ n * Real.exp (-(u ^ 2) / 2) * max 1 (Real.exp (-s)) : ℝ) =
        |u| ^ n * Real.exp (-(u ^ 2) / 2) * ((s ^ 2 / 2) * max 1 (Real.exp (-s))) by ring]
  apply mul_le_mul_of_nonneg_left hbound
  positivity

/-- **Gaussian-weighted absolute remainder bound**: when we want the bound
without the leading `u^n` factor, just specialise `n = 0`. -/
theorem perturbation_remainder_pointwise_zero (u s : ℝ) :
    |Real.exp (-(u ^ 2) / 2) * (Real.exp (-s) - (1 - s))| ≤
      (s ^ 2 / 2) * Real.exp (-(u ^ 2) / 2) * max 1 (Real.exp (-s)) := by
  have := perturbation_remainder_pointwise 0 u s
  simpa using this

/-! ## Combined bound: pointwise + decay + polynomial

Combining `perturbation_remainder_pointwise`, `rescaled_max_decay`, and
`rescaledPerturbation_sq_le` gives the master pointwise bound used in the
global integral remainder estimate:

  `|u^n · e^{-u²/2} · (e^{-s_t} - (1 - s_t))|
       ≤ C/t · |u|^n · (u⁶ + u⁸) · e^{-c₀ u²}`

for `t ≥ 1`, with `C = (A² + B²)` and `c₀ = min(1/2, c/λ)` (where `c` is the
coercivity constant from `anharmonic_coercive`). The right-hand side is an
explicit Gaussian-times-polynomial that integrates to `O(1/t)`.
-/

/-- **Combined pointwise bound** for the perturbative remainder. Under
the coercivity hypothesis `α² < 3λγ`, there exist constants `C₀ ≥ 0`
and `c₀ > 0` such that for all `t ≥ 1`, `n : ℕ`, and `u : ℝ`:

  `|u^n · e^{-u²/2} · (e^{-s_t(u)} - (1 - s_t(u)))|
     ≤ (C₀/t) · |u|^n · (u^6 + u^8) · e^{-c₀ u²}`. -/
theorem perturbation_remainder_combined
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ C₀ c₀ : ℝ, 0 ≤ C₀ ∧ 0 < c₀ ∧ ∀ {t : ℝ}, 1 ≤ t → ∀ (n : ℕ) (u : ℝ),
      |u ^ n * Real.exp (-(u ^ 2) / 2) *
        (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
         (1 - rescaledPerturbation lam alpha gamma t u))| ≤
      (C₀ / t) * |u| ^ n * (u ^ 6 + u ^ 8) * Real.exp (-(c₀ * u ^ 2)) := by
  obtain ⟨c₀, hc₀_pos, hdecay⟩ := rescaled_max_decay hlam hgamma hdisc
  refine ⟨cubicScale lam alpha ^ 2 + quarticScale lam gamma ^ 2, c₀,
          add_nonneg (sq_nonneg _) (sq_nonneg _),
          hc₀_pos, ?_⟩
  intro t ht n u
  have ht_pos : 0 < t := by linarith
  set s := rescaledPerturbation lam alpha gamma t u
  set A := cubicScale lam alpha
  set B := quarticScale lam gamma
  -- Step 1: pointwise bound (Taylor remainder + Gaussian factor).
  have h1 := perturbation_remainder_pointwise n u s
  -- Step 2: replace `e^{-u²/2} · max(1, e^{-s})` by `e^{-c₀ u²}` (decay).
  have h2 := hdecay ht_pos u
  have hsq2_nn : 0 ≤ s ^ 2 / 2 := by positivity
  have habs_nn : 0 ≤ |u| ^ n := pow_nonneg (abs_nonneg u) n
  -- Combine 1 and 2:
  -- LHS ≤ (s²/2) |u|^n · e^{-u²/2} · max(1, e^{-s}) ≤ (s²/2) |u|^n · e^{-c₀ u²}.
  have h12 : |u ^ n * Real.exp (-(u ^ 2) / 2) * (Real.exp (-s) - (1 - s))| ≤
      (s ^ 2 / 2) * |u| ^ n * Real.exp (-(c₀ * u ^ 2)) := by
    calc |u ^ n * Real.exp (-(u ^ 2) / 2) * (Real.exp (-s) - (1 - s))|
        ≤ (s ^ 2 / 2) * |u| ^ n * Real.exp (-(u ^ 2) / 2) * max 1 (Real.exp (-s)) := h1
      _ = (s ^ 2 / 2) * |u| ^ n *
            (Real.exp (-(u ^ 2) / 2) * max 1 (Real.exp (-s))) := by ring
      _ ≤ (s ^ 2 / 2) * |u| ^ n * Real.exp (-(c₀ * u ^ 2)) := by
            exact mul_le_mul_of_nonneg_left h2 (mul_nonneg hsq2_nn habs_nn)
  -- Step 3: replace `s²/2` by its polynomial bound.
  have h3 := rescaledPerturbation_sq_le lam alpha gamma ht u
  -- h3 : s² ≤ 2(A²+B²)·(u⁶+u⁸)/t  with `s = rescaledPerturbation ...`.
  -- So s²/2 ≤ (A²+B²)·(u⁶+u⁸)/t.
  have h3' : s ^ 2 / 2 ≤ (A ^ 2 + B ^ 2) * (u ^ 6 + u ^ 8) / t := by
    have := h3
    have ht_pos' : (0 : ℝ) < t := ht_pos
    -- 2x/2 = x reasoning:
    have hx : s ^ 2 / 2 ≤ (2 * (A ^ 2 + B ^ 2) * (u ^ 6 + u ^ 8) / t) / 2 :=
      div_le_div_of_nonneg_right this (by norm_num : (0 : ℝ) ≤ 2)
    have heq : (2 * (A ^ 2 + B ^ 2) * (u ^ 6 + u ^ 8) / t) / 2 =
                (A ^ 2 + B ^ 2) * (u ^ 6 + u ^ 8) / t := by
      have ht_ne : t ≠ 0 := ht_pos.ne'
      field_simp
    rw [heq] at hx
    exact hx
  -- Combine: LHS ≤ (s²/2)·|u|^n · e^{-c₀ u²} ≤ ((A²+B²)(u⁶+u⁸)/t)·|u|^n · e^{-c₀ u²}.
  calc |u ^ n * Real.exp (-(u ^ 2) / 2) * (Real.exp (-s) - (1 - s))|
      ≤ (s ^ 2 / 2) * |u| ^ n * Real.exp (-(c₀ * u ^ 2)) := h12
    _ ≤ ((A ^ 2 + B ^ 2) * (u ^ 6 + u ^ 8) / t) * |u| ^ n *
          Real.exp (-(c₀ * u ^ 2)) := by
          have hrhs_nn : 0 ≤ |u| ^ n * Real.exp (-(c₀ * u ^ 2)) :=
            mul_nonneg habs_nn (Real.exp_pos _).le
          have := mul_le_mul_of_nonneg_right h3' hrhs_nn
          linarith
    _ = (A ^ 2 + B ^ 2) / t * |u| ^ n * (u ^ 6 + u ^ 8) *
          Real.exp (-(c₀ * u ^ 2)) := by ring

/-! ## Integrability of polynomial-times-Gaussian functions

We need integrability of `u^n · exp(-c u²)` and related expressions to apply
`integral_mono` for the global remainder bound. -/

/-- For `c > 0` and `n : ℕ`, the function `u ↦ u^n · exp(-c·u²)` is integrable
on ℝ. Direct corollary of Mathlib's `integrable_rpow_mul_exp_neg_mul_sq`. -/
theorem integrable_pow_mul_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Integrable (fun u : ℝ => u ^ n * Real.exp (-(c * u ^ 2))) := by
  have hs : (-1 : ℝ) < (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h := integrable_rpow_mul_exp_neg_mul_sq hc hs
  -- h : Integrable (fun x => x^(n:ℝ) * exp(-c · x²))
  convert h using 1
  ext u
  congr 1
  · exact (Real.rpow_natCast u n).symm
  · congr 1; ring

/-- For `c > 0` and `n : ℕ`, the function `u ↦ |u|^n · exp(-c·u²)` is
integrable on ℝ. -/
theorem integrable_abs_pow_mul_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Integrable (fun u : ℝ => |u| ^ n * Real.exp (-(c * u ^ 2))) := by
  -- Bound: |u|^n ≤ u^n + (-u)^n, both giving integrable functions.
  -- Easier: use that the function is equal to |u^n · exp(-c u²)| (since exp > 0).
  have h_int := integrable_pow_mul_exp_neg_mul_sq hc n
  have h_eq : (fun u : ℝ => |u| ^ n * Real.exp (-(c * u ^ 2))) =
      fun u : ℝ => |u ^ n * Real.exp (-(c * u ^ 2))| := by
    ext u
    rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  rw [h_eq]
  exact h_int.norm

/-- Sums and products of polynomial-Gaussian terms remain integrable. -/
private theorem integrable_pow_add_pow_mul_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Integrable (fun u : ℝ => |u| ^ n * (u ^ 6 + u ^ 8) * Real.exp (-(c * u ^ 2))) := by
  -- |u|^n · (u^6 + u^8) = |u|^n · u^6 + |u|^n · u^8 = |u|^(n+6) (·sign) + |u|^(n+8) (·sign)
  -- Easier: bound |u|^n · (u^6 + u^8) · exp ≤ |u|^(n+6) · exp + |u|^(n+8) · exp.
  -- But for integrability we can directly split the integrand.
  have h_split : (fun u : ℝ => |u| ^ n * (u ^ 6 + u ^ 8) * Real.exp (-(c * u ^ 2))) =
      (fun u : ℝ => |u| ^ n * u ^ 6 * Real.exp (-(c * u ^ 2)))
        + (fun u : ℝ => |u| ^ n * u ^ 8 * Real.exp (-(c * u ^ 2))) := by
    ext u
    simp only [Pi.add_apply]
    ring
  rw [h_split]
  -- Each summand: |u|^n · u^k · exp(-c u²) for k = 6, 8.
  -- Bound: |u|^n · u^k · exp(-c u²) ≤ |u|^(n+k) · exp(-c u²) (for even k).
  apply Integrable.add
  · -- |u|^n · u^6 = |u|^n · |u|^6 = |u|^(n+6) (since u^6 = |u|^6).
    have h_eq : (fun u : ℝ => |u| ^ n * u ^ 6 * Real.exp (-(c * u ^ 2))) =
        fun u : ℝ => |u| ^ (n + 6) * Real.exp (-(c * u ^ 2)) := by
      ext u
      rw [show |u| ^ (n + 6) = |u| ^ n * |u| ^ 6 from pow_add _ _ _]
      rw [show |u| ^ 6 = u ^ 6 from by
            rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, sq_abs]
            ring]
    rw [h_eq]
    exact integrable_abs_pow_mul_exp_neg_mul_sq hc (n + 6)
  · -- |u|^n · u^8 = |u|^(n+8).
    have h_eq : (fun u : ℝ => |u| ^ n * u ^ 8 * Real.exp (-(c * u ^ 2))) =
        fun u : ℝ => |u| ^ (n + 8) * Real.exp (-(c * u ^ 2)) := by
      ext u
      rw [show |u| ^ (n + 8) = |u| ^ n * |u| ^ 8 from pow_add _ _ _]
      rw [show |u| ^ 8 = u ^ 8 from by
            rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, sq_abs]
            ring]
    rw [h_eq]
    exact integrable_abs_pow_mul_exp_neg_mul_sq hc (n + 8)

/-! ## Global integral remainder bound

We finally combine the pointwise bound (`perturbation_remainder_combined`)
with the integrability lemmas above to get an `O(1/t)` remainder. -/

/-- **Global `O(1/t)` remainder bound** (per fixed `n`): under the discriminant
condition, the integral of the perturbative remainder against `u^n · e^{-u²/2}`
is bounded by `K / t` for some `K ≥ 0` depending on `n, λ, α, γ`.

This is the master integrated estimate per GPT's strategy: it lets us
linearise `e^{-s_t(u)} ≈ 1 - s_t(u)` inside the integral with controlled error. -/
theorem perturbation_remainder_integral_bound
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
    (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
          (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
           (1 - rescaledPerturbation lam alpha gamma t u))| ≤ K / t := by
  -- Get the pointwise bound and its constants.
  obtain ⟨C₀, c₀, hC₀_nn, hc₀_pos, hpointwise⟩ :=
    perturbation_remainder_combined hlam hgamma hdisc
  -- The integrability of the bounding function.
  have hint_bound : Integrable (fun u : ℝ =>
      |u| ^ n * (u ^ 6 + u ^ 8) * Real.exp (-(c₀ * u ^ 2))) :=
    integrable_pow_add_pow_mul_exp_neg_mul_sq hc₀_pos n
  -- Define M = ∫ |u|^n · (u⁶+u⁸) · e^{-c₀ u²} du. M ≥ 0 since integrand is nonneg.
  set M := ∫ u : ℝ, |u| ^ n * (u ^ 6 + u ^ 8) * Real.exp (-(c₀ * u ^ 2)) with hM_def
  have hM_nn : 0 ≤ M := by
    apply integral_nonneg
    intro u
    have h1 : 0 ≤ |u| ^ n := pow_nonneg (abs_nonneg u) n
    have h2 : 0 ≤ u ^ 6 + u ^ 8 := by positivity
    have h3 : 0 ≤ Real.exp (-(c₀ * u ^ 2)) := (Real.exp_pos _).le
    positivity
  refine ⟨C₀ * M, mul_nonneg hC₀_nn hM_nn, ?_⟩
  intro t ht
  have ht_pos : 0 < t := by linarith
  -- Step A: bound `|∫ f| ≤ ∫ |f|`.
  -- Step B: bound `∫ |f| ≤ ∫ g` where `g = pointwise upper bound`.
  -- Step C: compute ∫ g = (C₀/t) · M.
  set f := fun u : ℝ => u ^ n * Real.exp (-(u ^ 2) / 2) *
    (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
     (1 - rescaledPerturbation lam alpha gamma t u)) with hf_def
  set g := fun u : ℝ => (C₀ / t) * |u| ^ n * (u ^ 6 + u ^ 8) *
    Real.exp (-(c₀ * u ^ 2)) with hg_def
  -- g is integrable (constant times the bounded integrable function).
  have hint_g : Integrable g := by
    have : g = (C₀ / t) • (fun u : ℝ =>
        |u| ^ n * (u ^ 6 + u ^ 8) * Real.exp (-(c₀ * u ^ 2))) := by
      ext u
      simp only [hg_def, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]
    exact hint_bound.smul (C₀ / t)
  -- |f| ≤ g pointwise (this IS our combined pointwise bound).
  have hfg : ∀ u, |f u| ≤ g u := by
    intro u
    have := hpointwise ht n u
    -- this : |u^n · e^{-u²/2} · (e^{-s_t} - (1 - s_t))| ≤
    --        (C₀/t) · |u|^n · (u⁶+u⁸) · e^{-c₀ u²}
    convert this using 1
  -- f integrable: |f| ≤ g and g integrable, so f integrable.
  have hint_f : Integrable f := by
    apply Integrable.mono' hint_g
    · -- AE strongly measurable: f is continuous, hence measurable.
      apply Continuous.aestronglyMeasurable
      simp only [hf_def]
      unfold rescaledPerturbation cubicScale quarticScale
      have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
      fun_prop
    · -- |f u| ≤ g u almost everywhere (here, everywhere).
      apply Filter.Eventually.of_forall
      intro u
      rw [Real.norm_eq_abs]
      exact hfg u
  -- Now: |∫ f| ≤ ∫ |f| ≤ ∫ g = (C₀/t) · M.
  calc |∫ u : ℝ, f u|
      ≤ ∫ u : ℝ, |f u| := abs_integral_le_integral_abs
    _ ≤ ∫ u : ℝ, g u :=
        integral_mono hint_f.abs hint_g
          (fun u => (Real.norm_eq_abs (f u)).symm ▸ hfg u)
    _ = (C₀ / t) * M := by
        rw [show g = fun u : ℝ => (C₀ / t) * (|u| ^ n * (u ^ 6 + u ^ 8) *
              Real.exp (-(c₀ * u ^ 2))) from by
              ext u; simp only [hg_def]; ring]
        rw [integral_const_mul]
    _ = C₀ * M / t := by ring

/-! ## Integrability of the standard Gaussian moment integrand

A convenience lemma we'll need downstream when computing raw Gaussian moments
in the linearisation. -/

/-- Integrability of `u^n · e^{-u²/2}` (the standard Gaussian moment integrand). -/
theorem integrable_pow_mul_exp_neg_half_sq (n : ℕ) :
    Integrable (fun u : ℝ => u ^ n * Real.exp (-(u ^ 2) / 2)) := by
  have h := integrable_pow_mul_exp_neg_mul_sq (c := 1/2) (by norm_num : (0 : ℝ) < 1/2) n
  have heq : (fun u : ℝ => u ^ n * Real.exp (-(1/2 * u ^ 2))) =
      fun u : ℝ => u ^ n * Real.exp (-(u ^ 2) / 2) := by
    ext u; congr 1; congr 1; ring
  rw [heq] at h; exact h

/-! ## Linearised integrand decomposition

Following GPT-5.5-Pro's idiom: normalize Pi operations with `simp_rw`, then
apply `integral_add` / `integral_neg` / `integral_const_mul` directly. -/

/-- The linearised integral evaluates to `M_n - (A/√t)·M_{n+3} - (B/t)·M_{n+4}`. -/
theorem linearised_integral_decomposition
    (lam alpha gamma : ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
        (1 - rescaledPerturbation lam alpha gamma t u) =
      (∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2))
        - cubicScale lam alpha / Real.sqrt t *
            (∫ u : ℝ, u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
        - quarticScale lam gamma / t *
            (∫ u : ℝ, u ^ (n + 4) * Real.exp (-(u ^ 2) / 2)) := by
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_t_ne : Real.sqrt t ≠ 0 := hsqrt_t_pos.ne'
  have ht_ne : t ≠ 0 := ht.ne'
  have hint_n := integrable_pow_mul_exp_neg_half_sq n
  have hint_n3 := integrable_pow_mul_exp_neg_half_sq (n + 3)
  have hint_n4 := integrable_pow_mul_exp_neg_half_sq (n + 4)
  -- Step 1: rewrite integrand pointwise into a clean three-term form.
  rw [show (fun u : ℝ => u ^ n * Real.exp (-(u ^ 2) / 2) *
            (1 - rescaledPerturbation lam alpha gamma t u)) =
        fun u : ℝ =>
          u ^ n * Real.exp (-(u ^ 2) / 2)
            + (-(cubicScale lam alpha / Real.sqrt t) *
                (u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
              + -(quarticScale lam gamma / t) *
                (u ^ (n + 4) * Real.exp (-(u ^ 2) / 2))) from by
        ext u
        unfold rescaledPerturbation
        rw [show u ^ (n + 3) = u ^ n * u ^ 3 from pow_add u n 3,
            show u ^ (n + 4) = u ^ n * u ^ 4 from pow_add u n 4]
        field_simp
        ring]
  -- Step 2: split via `integral_add`. The `change` tactic helps unification.
  have hint_g3 : Integrable
      (fun u : ℝ => -(cubicScale lam alpha / Real.sqrt t) *
        (u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))) :=
    hint_n3.const_mul _
  have hint_g4 : Integrable
      (fun u : ℝ => -(quarticScale lam gamma / t) *
        (u ^ (n + 4) * Real.exp (-(u ^ 2) / 2))) :=
    hint_n4.const_mul _
  have hint_g34 : Integrable (fun u : ℝ =>
      -(cubicScale lam alpha / Real.sqrt t) *
        (u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
      + -(quarticScale lam gamma / t) *
        (u ^ (n + 4) * Real.exp (-(u ^ 2) / 2))) := hint_g3.add hint_g4
  -- The integral_add lemma expects `∫ a, f a + g a` form. Use change to get there.
  rw [show (∫ u : ℝ,
        u ^ n * Real.exp (-(u ^ 2) / 2)
          + (-(cubicScale lam alpha / Real.sqrt t) *
              (u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
            + -(quarticScale lam gamma / t) *
              (u ^ (n + 4) * Real.exp (-(u ^ 2) / 2)))) =
      (∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2))
        + ∫ u : ℝ,
            -(cubicScale lam alpha / Real.sqrt t) *
              (u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
            + -(quarticScale lam gamma / t) *
              (u ^ (n + 4) * Real.exp (-(u ^ 2) / 2)) from
      integral_add hint_n hint_g34]
  rw [show (∫ u : ℝ,
        -(cubicScale lam alpha / Real.sqrt t) *
          (u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
        + -(quarticScale lam gamma / t) *
          (u ^ (n + 4) * Real.exp (-(u ^ 2) / 2))) =
      (∫ u : ℝ, -(cubicScale lam alpha / Real.sqrt t) *
              (u ^ (n + 3) * Real.exp (-(u ^ 2) / 2)))
        + ∫ u : ℝ, -(quarticScale lam gamma / t) *
              (u ^ (n + 4) * Real.exp (-(u ^ 2) / 2)) from
      integral_add hint_g3 hint_g4]
  rw [integral_const_mul, integral_const_mul]
  ring

/-! ## J_n asymptotic: the full first-order expansion

Combining the integral remainder bound with the linearised decomposition gives
the asymptotic of `J_n(t) = ∫ u^n · e^{-u²/2} · e^{-s_t(u)} du`. -/

/-- Integrability of `u^n · e^{-u²/2} · e^{-s_t(u)}`. Under coercivity, the
product is bounded by `|u|^n · e^{-c u²}`. -/
private theorem integrable_J_n
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ℝ => u ^ n * Real.exp (-(u ^ 2) / 2) *
      Real.exp (-rescaledPerturbation lam alpha gamma t u)) := by
  obtain ⟨c₀, hc₀_pos, hboltz⟩ :=
    rescaled_boltzmann_decay hlam hgamma hdisc
  -- Use the bounding integrand |u|^n · e^{-c₀ u²}.
  apply Integrable.mono' (g := fun u : ℝ => |u| ^ n * Real.exp (-(c₀ * u ^ 2)))
    (integrable_abs_pow_mul_exp_neg_mul_sq hc₀_pos n)
  · apply Continuous.aestronglyMeasurable
    unfold rescaledPerturbation cubicScale quarticScale
    have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    fun_prop
  · apply Filter.Eventually.of_forall
    intro u
    rw [Real.norm_eq_abs]
    have h1 := hboltz ht u
    -- e^{-(u²/2 + s_t)} ≤ e^{-c₀ u²}, i.e., e^{-u²/2} · e^{-s_t} ≤ e^{-c₀ u²}.
    have h_factor : Real.exp (-(u ^ 2) / 2) *
        Real.exp (-rescaledPerturbation lam alpha gamma t u) =
        Real.exp (-(u ^ 2 / 2 + rescaledPerturbation lam alpha gamma t u)) := by
      rw [← Real.exp_add]
      congr 1; ring
    rw [show |u ^ n * Real.exp (-(u ^ 2) / 2) *
            Real.exp (-rescaledPerturbation lam alpha gamma t u)| =
          |u| ^ n *
            (Real.exp (-(u ^ 2) / 2) *
              Real.exp (-rescaledPerturbation lam alpha gamma t u)) by
          rw [abs_mul, abs_mul, abs_pow,
              abs_of_pos (Real.exp_pos _),
              abs_of_pos (Real.exp_pos _)]
          ring]
    rw [h_factor]
    apply mul_le_mul_of_nonneg_left h1 (pow_nonneg (abs_nonneg u) n)

/-- **`J_n` asymptotic expansion**: under coercivity,

  `J_n(t) = M_n - (A/√t)·M_{n+3} - (B/t)·M_{n+4} + r_n(t)`

with `|r_n(t)| ≤ K/t` for some `K ≥ 0` and all `t ≥ 1`,
where `M_k = ∫ u^k · e^{-u²/2} du`. -/
theorem J_n_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
    (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |(∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
          Real.exp (-rescaledPerturbation lam alpha gamma t u))
        - ((∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2))
            - cubicScale lam alpha / Real.sqrt t *
                (∫ u : ℝ, u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
            - quarticScale lam gamma / t *
                (∫ u : ℝ, u ^ (n + 4) * Real.exp (-(u ^ 2) / 2)))| ≤ K / t := by
  obtain ⟨K, hK_nn, hbound⟩ :=
    perturbation_remainder_integral_bound hlam hgamma hdisc n
  refine ⟨K, hK_nn, ?_⟩
  intro t ht
  have ht_pos : 0 < t := by linarith
  -- The integral remainder bound says `|∫ u^n e^{-u²/2} (e^{-s} - (1 - s))| ≤ K/t`.
  -- We rewrite the LHS using linearity:
  --   ∫ u^n e^{-u²/2} e^{-s} - ∫ u^n e^{-u²/2} (1 - s) = ∫ u^n e^{-u²/2} (e^{-s} - (1-s))
  have hint_J := integrable_J_n hlam hgamma hdisc n ht_pos
  have hint_lin : Integrable (fun u : ℝ =>
      u ^ n * Real.exp (-(u ^ 2) / 2) *
        (1 - rescaledPerturbation lam alpha gamma t u)) := by
    -- Bound by |u|^(n+4) · e^{-u²/2} (or similar) — finite Gaussian moment.
    -- Use the difference: J_n_integrable - integral_remainder_integrable.
    -- Actually: the linearised integrand is u^n e^{-u²/2} · (1 - s_t).
    -- = u^n e^{-u²/2} - u^n e^{-u²/2} · s_t
    -- = u^n e^{-u²/2} - (A/√t) u^{n+3} e^{-u²/2} - (B/t) u^{n+4} e^{-u²/2}.
    -- All three pieces integrable.
    have hint_n := integrable_pow_mul_exp_neg_half_sq n
    have hint_n3 := integrable_pow_mul_exp_neg_half_sq (n + 3)
    have hint_n4 := integrable_pow_mul_exp_neg_half_sq (n + 4)
    have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
    have hsqrt_t_ne : Real.sqrt t ≠ 0 := hsqrt_t_pos.ne'
    have ht_ne : t ≠ 0 := ht_pos.ne'
    have heq : (fun u : ℝ => u ^ n * Real.exp (-(u ^ 2) / 2) *
            (1 - rescaledPerturbation lam alpha gamma t u)) =
        fun u : ℝ => u ^ n * Real.exp (-(u ^ 2) / 2)
              + (-(cubicScale lam alpha / Real.sqrt t) *
                  (u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
                + -(quarticScale lam gamma / t) *
                  (u ^ (n + 4) * Real.exp (-(u ^ 2) / 2))) := by
      ext u
      unfold rescaledPerturbation
      rw [show u ^ (n + 3) = u ^ n * u ^ 3 from pow_add u n 3,
          show u ^ (n + 4) = u ^ n * u ^ 4 from pow_add u n 4]
      field_simp
      ring
    rw [heq]
    exact hint_n.add ((hint_n3.const_mul _).add (hint_n4.const_mul _))
  -- Compute: ∫ J - ∫ linearised = ∫ (e^{-s} - (1 - s)) · u^n · e^{-u²/2}.
  have hkey : (∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
        Real.exp (-rescaledPerturbation lam alpha gamma t u))
      - (∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
            (1 - rescaledPerturbation lam alpha gamma t u)) =
      ∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
          (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
           (1 - rescaledPerturbation lam alpha gamma t u)) := by
    rw [show (fun u : ℝ => u ^ n * Real.exp (-(u ^ 2) / 2) *
              (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
               (1 - rescaledPerturbation lam alpha gamma t u))) =
          (fun u : ℝ => u ^ n * Real.exp (-(u ^ 2) / 2) *
              Real.exp (-rescaledPerturbation lam alpha gamma t u))
          - (fun u : ℝ => u ^ n * Real.exp (-(u ^ 2) / 2) *
              (1 - rescaledPerturbation lam alpha gamma t u)) by
        ext u; simp only [Pi.sub_apply]; ring]
    rw [show (∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
              Real.exp (-rescaledPerturbation lam alpha gamma t u))
              - (∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
                  (1 - rescaledPerturbation lam alpha gamma t u)) =
            ∫ u : ℝ, ((fun u : ℝ => u ^ n * Real.exp (-(u ^ 2) / 2) *
              Real.exp (-rescaledPerturbation lam alpha gamma t u)) -
              (fun u : ℝ => u ^ n * Real.exp (-(u ^ 2) / 2) *
                  (1 - rescaledPerturbation lam alpha gamma t u))) u from by
      simp only [Pi.sub_apply]
      exact (integral_sub hint_J hint_lin).symm]
  -- Apply the linearisation decomposition + integral remainder bound.
  rw [linearised_integral_decomposition lam alpha gamma n ht_pos] at hkey
  calc |(∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
              Real.exp (-rescaledPerturbation lam alpha gamma t u))
            - ((∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2))
                - cubicScale lam alpha / Real.sqrt t *
                    (∫ u : ℝ, u ^ (n + 3) * Real.exp (-(u ^ 2) / 2))
                - quarticScale lam gamma / t *
                    (∫ u : ℝ, u ^ (n + 4) * Real.exp (-(u ^ 2) / 2)))|
        = |∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
              (Real.exp (-rescaledPerturbation lam alpha gamma t u) -
               (1 - rescaledPerturbation lam alpha gamma t u))| := by rw [hkey]
      _ ≤ K / t := hbound ht

/-! ## Specialised asymptotics for n = 1 (per GPT-5.5-Pro recommendation)

Demonstrates the full chain: `J_n_asymptotic` + moment values from Stage 1
gives an explicit asymptotic with closed-form prefactors. -/

/-- `M_1 = ∫ u · e^{-u²/2} du = 0` (odd moment vanishes). -/
private lemma M_1_eq_zero :
    ∫ u : ℝ, u ^ 1 * Real.exp (-(u ^ 2) / 2) = 0 := by
  have h := integral_pow_mul_exp_neg_sq_odd 0
  simpa using h

/-- `M_4 = ∫ u^4 · e^{-u²/2} du = 3 √(2π)`. -/
private lemma M_4_eq :
    ∫ u : ℝ, u ^ 4 * Real.exp (-(u ^ 2) / 2) = 3 * Real.sqrt (2 * Real.pi) := by
  have h := integral_pow_mul_exp_neg_sq_half 2
  -- h : ∫ x, x^(2*2) * exp(-x²/2) = (2·2 - 1)‼ · √(2π) = 3 · √(2π)
  have hd : ((2 * 2 - 1)‼ : ℝ) = 3 := by
    show ((3 : ℕ)‼ : ℝ) = 3
    rw [show (3 : ℕ)‼ = 3 by decide]; norm_num
  simp only [show (2 * 2 : ℕ) = 4 from rfl] at h
  rw [hd] at h
  exact h

/-- `M_5 = ∫ u^5 · e^{-u²/2} du = 0`. -/
private lemma M_5_eq_zero :
    ∫ u : ℝ, u ^ 5 * Real.exp (-(u ^ 2) / 2) = 0 := by
  have h := integral_pow_mul_exp_neg_sq_odd 2
  simpa using h

/-- **`J_1` asymptotic**: under coercivity,

  `J_1(t) = ∫ u · e^{-u²/2} · e^{-s_t(u)} du = -3 A √(2π) / √t + O(1/t)`,

where `A = cubicScale lam alpha = α / (6 λ^{3/2})`. -/
theorem J_1_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |(∫ u : ℝ, u ^ 1 * Real.exp (-(u ^ 2) / 2) *
          Real.exp (-rescaledPerturbation lam alpha gamma t u))
        - (-3 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) / Real.sqrt t)| ≤
      K / t := by
  obtain ⟨K, hK_nn, hbound⟩ := J_n_asymptotic hlam hgamma hdisc 1
  refine ⟨K, hK_nn, ?_⟩
  intro t ht
  have ht_pos : 0 < t := by linarith
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_t_ne : Real.sqrt t ≠ 0 := hsqrt_t_pos.ne'
  -- Substitute moment values: M_1 = 0, M_4 = 3√(2π), M_5 = 0.
  have h_target : (∫ u : ℝ, u ^ 1 * Real.exp (-(u ^ 2) / 2))
      - cubicScale lam alpha / Real.sqrt t *
          (∫ u : ℝ, u ^ (1 + 3) * Real.exp (-(u ^ 2) / 2))
      - quarticScale lam gamma / t *
          (∫ u : ℝ, u ^ (1 + 4) * Real.exp (-(u ^ 2) / 2)) =
      -3 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) / Real.sqrt t := by
    rw [M_1_eq_zero,
        show (1 + 3 : ℕ) = 4 from rfl, M_4_eq,
        show (1 + 4 : ℕ) = 5 from rfl, M_5_eq_zero]
    field_simp
    ring
  rw [← h_target]
  exact hbound ht

/-- `M_0 = ∫ e^{-u²/2} du = √(2π)`. -/
private lemma M_0_eq :
    ∫ u : ℝ, u ^ 0 * Real.exp (-(u ^ 2) / 2) = Real.sqrt (2 * Real.pi) := by
  have h := integral_pow_mul_exp_neg_sq_half 0
  -- h : ∫ x, x^0 * exp(-x²/2) = (2*0-1)‼ · √(2π) = 1 · √(2π) = √(2π)
  have hd : ((2 * 0 - 1)‼ : ℝ) = 1 := by
    show ((0 : ℕ)‼ : ℝ) = 1
    rw [show (0 : ℕ)‼ = 1 from rfl]; norm_num
  simp only [Nat.mul_zero] at h
  rw [hd, one_mul] at h
  exact h

/-- `M_2 = ∫ u² · e^{-u²/2} du = √(2π)`. -/
private lemma M_2_eq :
    ∫ u : ℝ, u ^ 2 * Real.exp (-(u ^ 2) / 2) = Real.sqrt (2 * Real.pi) := by
  have h := integral_pow_mul_exp_neg_sq_half 1
  have hd : ((2 * 1 - 1)‼ : ℝ) = 1 := by
    show ((1 : ℕ)‼ : ℝ) = 1
    rw [show (1 : ℕ)‼ = 1 from rfl]; norm_num
  simp only [show (2 * 1 : ℕ) = 2 from rfl] at h
  rw [hd, one_mul] at h
  exact h

/-- `M_3 = ∫ u^3 · e^{-u²/2} du = 0`. -/
private lemma M_3_eq_zero :
    ∫ u : ℝ, u ^ 3 * Real.exp (-(u ^ 2) / 2) = 0 := by
  have h := integral_pow_mul_exp_neg_sq_odd 1
  simpa using h

/-- `M_6 = ∫ u^6 · e^{-u²/2} du = 15 √(2π)`. -/
private lemma M_6_eq :
    ∫ u : ℝ, u ^ 6 * Real.exp (-(u ^ 2) / 2) = 15 * Real.sqrt (2 * Real.pi) := by
  have h := integral_pow_mul_exp_neg_sq_half 3
  -- h : ∫ x, x^(2*3) * exp(-x²/2) = 5‼ · √(2π) = 15·√(2π).
  have hd : ((2 * 3 - 1)‼ : ℝ) = 15 := by
    show ((5 : ℕ)‼ : ℝ) = 15
    rw [show (5 : ℕ)‼ = 15 by decide]; norm_num
  simp only [show (2 * 3 : ℕ) = 6 from rfl] at h
  rw [hd] at h
  exact h

/-- `M_7 = ∫ u^7 · e^{-u²/2} du = 0`. -/
private lemma M_7_eq_zero :
    ∫ u : ℝ, u ^ 7 * Real.exp (-(u ^ 2) / 2) = 0 := by
  have h := integral_pow_mul_exp_neg_sq_odd 3
  simpa using h

/-- **`J_0` asymptotic**: `J_0(t) = √(2π) + O(1/t)`. -/
theorem J_0_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |(∫ u : ℝ, u ^ 0 * Real.exp (-(u ^ 2) / 2) *
          Real.exp (-rescaledPerturbation lam alpha gamma t u))
        - Real.sqrt (2 * Real.pi)| ≤ K / t := by
  obtain ⟨K, hK_nn, hbound⟩ := J_n_asymptotic hlam hgamma hdisc 0
  -- The (B/t) · M_4 term gets absorbed into the O(1/t) bound.
  refine ⟨K + 3 * |quarticScale lam gamma| * Real.sqrt (2 * Real.pi),
    by positivity, ?_⟩
  intro t ht
  have ht_pos : 0 < t := by linarith
  -- Substitute M_0 = √(2π), M_3 = 0, M_4 = 3√(2π).
  have h := hbound ht
  rw [M_0_eq,
      show (0 + 3 : ℕ) = 3 from rfl, M_3_eq_zero,
      show (0 + 4 : ℕ) = 4 from rfl, M_4_eq] at h
  -- h : |J_0 - (√(2π) - 0 - (B/t) · 3√(2π))| ≤ K/t
  -- Rearranged: |J_0 - √(2π) + (B/t) · 3√(2π)| ≤ K/t
  -- So: |J_0 - √(2π)| ≤ K/t + |3B√(2π)/t| = (K + 3|B|√(2π))/t.
  have habs : ∀ a b c : ℝ, |a - b| ≤ c → |a - (b - 0 - 3 * cubicScale lam alpha / Real.sqrt t * 0
      - 3 * quarticScale lam gamma / t * 1 * Real.sqrt (2 * Real.pi))| = |a - b + 3 * quarticScale lam gamma / t * Real.sqrt (2 * Real.pi)| := by
    intros; ring_nf
  -- Just use triangle inequality directly.
  have hpos_bound : (0 : ℝ) ≤ 3 * |quarticScale lam gamma| * Real.sqrt (2 * Real.pi) := by
    positivity
  have h_quartic_abs : |(quarticScale lam gamma / t * Real.sqrt (2 * Real.pi))| =
      |quarticScale lam gamma| / t * Real.sqrt (2 * Real.pi) := by
    rw [abs_mul, abs_div, abs_of_pos ht_pos,
        abs_of_nonneg (Real.sqrt_nonneg _)]
  -- Use: |J_0 - √(2π)| = |J_0 - (√(2π) - (B/t)·3·√(2π)) - (B/t)·3·√(2π)|
  --                   ≤ |J_0 - (√(2π) - (B/t)·3·√(2π))| + |(B/t)·3·√(2π)|
  --                   ≤ K/t + 3|B|·√(2π)/t.
  calc |(∫ u : ℝ, u ^ 0 * Real.exp (-(u ^ 2) / 2) *
            Real.exp (-rescaledPerturbation lam alpha gamma t u))
            - Real.sqrt (2 * Real.pi)|
      = |((∫ u : ℝ, u ^ 0 * Real.exp (-(u ^ 2) / 2) *
              Real.exp (-rescaledPerturbation lam alpha gamma t u))
            - (Real.sqrt (2 * Real.pi)
              - cubicScale lam alpha / Real.sqrt t * 0
              - quarticScale lam gamma / t * (3 * Real.sqrt (2 * Real.pi))))
          + (- (quarticScale lam gamma / t * (3 * Real.sqrt (2 * Real.pi))))| := by
            congr 1; ring
    _ ≤ |((∫ u : ℝ, u ^ 0 * Real.exp (-(u ^ 2) / 2) *
              Real.exp (-rescaledPerturbation lam alpha gamma t u))
            - (Real.sqrt (2 * Real.pi)
              - cubicScale lam alpha / Real.sqrt t * 0
              - quarticScale lam gamma / t * (3 * Real.sqrt (2 * Real.pi))))|
        + |(- (quarticScale lam gamma / t * (3 * Real.sqrt (2 * Real.pi))))| :=
          abs_add_le _ _
    _ ≤ K / t +
        |(- (quarticScale lam gamma / t * (3 * Real.sqrt (2 * Real.pi))))| := by
          gcongr
    _ = K / t + 3 * |quarticScale lam gamma| * Real.sqrt (2 * Real.pi) / t := by
          rw [abs_neg, abs_mul, abs_div, abs_mul, abs_of_pos ht_pos,
              show |(3 : ℝ)| = 3 from by norm_num,
              abs_of_nonneg (Real.sqrt_nonneg _)]
          ring
    _ = (K + 3 * |quarticScale lam gamma| * Real.sqrt (2 * Real.pi)) / t := by
          field_simp

/-- **`J_2` asymptotic**: `J_2(t) = √(2π) + O(1/t)`. Mirrors `J_0`. -/
theorem J_2_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |(∫ u : ℝ, u ^ 2 * Real.exp (-(u ^ 2) / 2) *
          Real.exp (-rescaledPerturbation lam alpha gamma t u))
        - Real.sqrt (2 * Real.pi)| ≤ K / t := by
  obtain ⟨K, hK_nn, hbound⟩ := J_n_asymptotic hlam hgamma hdisc 2
  refine ⟨K + 15 * |quarticScale lam gamma| * Real.sqrt (2 * Real.pi),
    by positivity, ?_⟩
  intro t ht
  have ht_pos : 0 < t := by linarith
  have h := hbound ht
  rw [M_2_eq,
      show (2 + 3 : ℕ) = 5 from rfl, M_5_eq_zero,
      show (2 + 4 : ℕ) = 6 from rfl, M_6_eq] at h
  -- h : |J_2 - (√(2π) - 0 - (B/t) · 15√(2π))| ≤ K/t
  calc |(∫ u : ℝ, u ^ 2 * Real.exp (-(u ^ 2) / 2) *
            Real.exp (-rescaledPerturbation lam alpha gamma t u))
            - Real.sqrt (2 * Real.pi)|
      = |((∫ u : ℝ, u ^ 2 * Real.exp (-(u ^ 2) / 2) *
              Real.exp (-rescaledPerturbation lam alpha gamma t u))
            - (Real.sqrt (2 * Real.pi)
              - cubicScale lam alpha / Real.sqrt t * 0
              - quarticScale lam gamma / t * (15 * Real.sqrt (2 * Real.pi))))
          + (- (quarticScale lam gamma / t * (15 * Real.sqrt (2 * Real.pi))))| := by
            congr 1; ring
    _ ≤ |((∫ u : ℝ, u ^ 2 * Real.exp (-(u ^ 2) / 2) *
              Real.exp (-rescaledPerturbation lam alpha gamma t u))
            - (Real.sqrt (2 * Real.pi)
              - cubicScale lam alpha / Real.sqrt t * 0
              - quarticScale lam gamma / t * (15 * Real.sqrt (2 * Real.pi))))|
        + |(- (quarticScale lam gamma / t * (15 * Real.sqrt (2 * Real.pi))))| :=
          abs_add_le _ _
    _ ≤ K / t +
        |(- (quarticScale lam gamma / t * (15 * Real.sqrt (2 * Real.pi))))| := by
          gcongr
    _ = K / t + 15 * |quarticScale lam gamma| * Real.sqrt (2 * Real.pi) / t := by
          rw [abs_neg, abs_mul, abs_div, abs_mul, abs_of_pos ht_pos,
              show |(15 : ℝ)| = 15 from by norm_num,
              abs_of_nonneg (Real.sqrt_nonneg _)]
          ring
    _ = (K + 15 * |quarticScale lam gamma| * Real.sqrt (2 * Real.pi)) / t := by
          field_simp

/-- **`J_3` asymptotic**: `J_3(t) = -15 A √(2π) / √t + O(1/t)`. Mirrors `J_1`. -/
theorem J_3_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |(∫ u : ℝ, u ^ 3 * Real.exp (-(u ^ 2) / 2) *
          Real.exp (-rescaledPerturbation lam alpha gamma t u))
        - (-15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) / Real.sqrt t)| ≤
      K / t := by
  obtain ⟨K, hK_nn, hbound⟩ := J_n_asymptotic hlam hgamma hdisc 3
  refine ⟨K, hK_nn, ?_⟩
  intro t ht
  have ht_pos : 0 < t := by linarith
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_t_ne : Real.sqrt t ≠ 0 := hsqrt_t_pos.ne'
  -- Substitute: M_3 = 0, M_6 = 15√(2π), M_7 = 0.
  have h_target : (∫ u : ℝ, u ^ 3 * Real.exp (-(u ^ 2) / 2))
      - cubicScale lam alpha / Real.sqrt t *
          (∫ u : ℝ, u ^ (3 + 3) * Real.exp (-(u ^ 2) / 2))
      - quarticScale lam gamma / t *
          (∫ u : ℝ, u ^ (3 + 4) * Real.exp (-(u ^ 2) / 2)) =
      -15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) / Real.sqrt t := by
    rw [M_3_eq_zero,
        show (3 + 3 : ℕ) = 6 from rfl, M_6_eq,
        show (3 + 4 : ℕ) = 7 from rfl, M_7_eq_zero]
    field_simp
    ring
  rw [← h_target]
  exact hbound ht

/-! ## Substitution identity: relating `I_n(t)` and `J_n(t)`

The substitution `u = x · √(λt)` connects the rescaled-coordinate moments
`J_n(t)` to the original-coordinate moments `I_n(t) = ∫ x^n · exp(-tL_anh(x))`.

The identity is:
  `(√(λt))^(n+1) · I_n(t) = J_n(t)`. -/

/-- The substitution identity. Multiplying both sides by `(√(λt))^(n+1)` keeps
the formula in integer-power form. -/
theorem I_n_J_n_relation
    (lam alpha gamma : ℝ) (n : ℕ) {t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    Real.sqrt (lam * t) ^ (n + 1) *
        ∫ x : ℝ, x ^ n * Real.exp (-(t * anharmonicPotential lam alpha gamma x)) =
      ∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
        Real.exp (-rescaledPerturbation lam alpha gamma t u) := by
  have hlamt : 0 < lam * t := mul_pos hlam ht
  have hsqrt_pos : 0 < Real.sqrt (lam * t) := Real.sqrt_pos.mpr hlamt
  have hsqrt_ne : Real.sqrt (lam * t) ≠ 0 := hsqrt_pos.ne'
  -- Apply `integral_comp_mul_right` in reverse: `∫ u, g u = √(λt) · ∫ x, g (x · √(λt))`.
  have hcomp := MeasureTheory.Measure.integral_comp_mul_right
    (fun u : ℝ => u ^ n * Real.exp (-(u ^ 2) / 2) *
      Real.exp (-rescaledPerturbation lam alpha gamma t u))
    (Real.sqrt (lam * t))
  -- hcomp : ∫ x, ((x·√(λt))^n · exp(-((x√(λt))²)/2) · exp(-s_t(x√(λt)))) =
  --         |√(λt)⁻¹| · ∫ u, (u^n · ...)
  rw [abs_of_pos (inv_pos.mpr hsqrt_pos), smul_eq_mul] at hcomp
  -- Simplify the LHS of hcomp using the rescaling identity:
  --   (x · √(λt))²/2 + s_t(x · √(λt)) = t · L_anh(x).
  have hresc : ∀ x : ℝ, (x * Real.sqrt (lam * t)) ^ 2 / 2 +
      rescaledPerturbation lam alpha gamma t (x * Real.sqrt (lam * t)) =
      t * anharmonicPotential lam alpha gamma x := by
    intro x
    -- Use `anharmonic_rescaling_identity` with `u := x · √(λt)`:
    --   t · L_anh((x · √(λt))/√(λt)) = (x√(λt))²/2 + s_t(x √(λt)).
    have h := anharmonic_rescaling_identity hlam ht alpha gamma (x * Real.sqrt (lam * t))
    -- h : t · L_anh((x · √(λt)) / √(λt)) = (x√(λt))²/2 + s_t(x √(λt))
    rw [show (x * Real.sqrt (lam * t)) / Real.sqrt (lam * t) = x from
          mul_div_cancel_right₀ x hsqrt_ne] at h
    linarith
  -- Now massage hcomp's LHS:
  -- ∫ x, ((x · √(λt))^n · exp(-((x√(λt))²)/2) · exp(-s_t(x √(λt)))) =
  --   ∫ x, (x^n · (√(λt))^n · exp(-(t · L_anh(x))))    -- using hresc
  -- =  (√(λt))^n · ∫ x, x^n · exp(-(t · L_anh(x)))
  have hLHS : (∫ x : ℝ, (x * Real.sqrt (lam * t)) ^ n *
        Real.exp (-((x * Real.sqrt (lam * t)) ^ 2) / 2) *
        Real.exp (-rescaledPerturbation lam alpha gamma t
            (x * Real.sqrt (lam * t)))) =
      Real.sqrt (lam * t) ^ n *
        ∫ x : ℝ, x ^ n *
          Real.exp (-(t * anharmonicPotential lam alpha gamma x)) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    ext x
    -- Combine the two exp factors via exp_add:
    have hexp_combine :
        Real.exp (-((x * Real.sqrt (lam * t)) ^ 2) / 2) *
        Real.exp (-rescaledPerturbation lam alpha gamma t
            (x * Real.sqrt (lam * t))) =
        Real.exp (-(t * anharmonicPotential lam alpha gamma x)) := by
      rw [← Real.exp_add]
      congr 1
      have := hresc x
      linarith
    -- Decompose `(x · √(λt))^n = x^n · √(λt)^n`:
    have hpow_split : (x * Real.sqrt (lam * t)) ^ n =
        x ^ n * Real.sqrt (lam * t) ^ n := mul_pow x _ n
    rw [hpow_split, mul_assoc, hexp_combine]
    ring
  -- Combine.
  rw [hLHS] at hcomp
  -- hcomp : √(λt)^n · I_n = √(λt)⁻¹ · J_n
  -- Multiply both sides by √(λt)^(n+1):
  -- √(λt)^(n+1) · √(λt)^n · I_n = √(λt)^(n+1) · √(λt)⁻¹ · J_n = √(λt)^n · J_n.
  -- Hmm not quite. Let me redo.
  -- Actually: hcomp says √(λt)^n · I_n = √(λt)⁻¹ · J_n.
  -- So √(λt)^(n+1) · I_n = √(λt) · √(λt)^n · I_n = √(λt) · √(λt)⁻¹ · J_n = J_n.
  have : Real.sqrt (lam * t) ^ (n + 1) *
        ∫ x : ℝ, x ^ n *
          Real.exp (-(t * anharmonicPotential lam alpha gamma x)) =
      Real.sqrt (lam * t) *
        (Real.sqrt (lam * t) ^ n *
          ∫ x : ℝ, x ^ n *
            Real.exp (-(t * anharmonicPotential lam alpha gamma x))) := by
    rw [pow_succ]; ring
  rw [this, hcomp]
  field_simp

/-! ## I_n asymptotics via the substitution identity

Combining `J_n_asymptotic` with `I_n_J_n_relation` gives explicit asymptotics
for the original-coordinate moments `I_n(t) = ∫ x^n · exp(-tL_anh(x)) dx`. -/

/-- **`I_0` asymptotic**: under coercivity, the partition function satisfies
`I_0(t) = √(2π) / √(λt) + O(1/(t · √(λt)))`. -/
theorem I_0_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |(∫ x : ℝ, Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
        - Real.sqrt (2 * Real.pi) / Real.sqrt (lam * t)| ≤
      K / (t * Real.sqrt (lam * t)) := by
  obtain ⟨K, hK_nn, hbound⟩ := J_0_asymptotic hlam hgamma hdisc
  refine ⟨K, hK_nn, ?_⟩
  intro t ht
  have ht_pos : 0 < t := by linarith
  have hlamt : 0 < lam * t := mul_pos hlam ht_pos
  have hsqrt_pos : 0 < Real.sqrt (lam * t) := Real.sqrt_pos.mpr hlamt
  have hsqrt_ne : Real.sqrt (lam * t) ≠ 0 := hsqrt_pos.ne'
  -- From `I_n_J_n_relation` with n = 0: `√(λt) · I_0 = J_0`.
  have hsub := I_n_J_n_relation lam alpha gamma 0 hlam ht_pos
  -- hsub : √(λt)^1 · I_0 = J_0  (since (n+1) = 1).
  rw [pow_one] at hsub
  -- We have |J_0 - √(2π)| ≤ K/t. Divide by √(λt) > 0.
  have hbnd := hbound ht
  -- Convert hbnd via the substitution: J_0 = √(λt) · I_0, so:
  --   |√(λt) · I_0 - √(2π)| ≤ K/t.
  -- Divide by √(λt): |I_0 - √(2π)/√(λt)| ≤ K/(t · √(λt)).
  -- Concretely: simplify the integrand in hbnd via the substitution.
  -- hbnd's integrand: ∫ u, u^0 · exp(-u²/2) · exp(-s_t(u)) = J_0.
  -- We have hsub : √(λt) · ∫ x, x^0 · exp(-tL) = J_0.
  -- So J_0 = √(λt) · I_0 (after recognizing x^0 = 1).
  -- Convert both hbnd and hsub to remove `u^0` factors.
  simp only [pow_zero, one_mul] at hbnd hsub
  -- Now hsub : √(λt) · I_0 = ∫ u, exp(-u²/2) · exp(-s_t(u)).
  -- Substitute into hbnd:
  rw [← hsub] at hbnd
  -- hbnd : |√(λt) · I_0 - √(2π)| ≤ K/t
  -- Divide by √(λt):
  have hgoal_eq : (∫ x : ℝ, Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
        - Real.sqrt (2 * Real.pi) / Real.sqrt (lam * t) =
      (Real.sqrt (lam * t) *
            (∫ x : ℝ, Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
          - Real.sqrt (2 * Real.pi)) / Real.sqrt (lam * t) := by
    field_simp
  rw [hgoal_eq, abs_div, abs_of_pos hsqrt_pos]
  rw [show (K / (t * Real.sqrt (lam * t)) : ℝ) =
        (K / t) / Real.sqrt (lam * t) by field_simp]
  exact div_le_div_of_nonneg_right hbnd hsqrt_pos.le

/-- **`I_1` asymptotic**: `I_1(t) = -3A√(2π) / ((λt)·√t) + O(1/((λt)·t))`. -/
theorem I_1_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |(∫ x : ℝ, x * Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
        - (-3 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) /
            (lam * t * Real.sqrt t))| ≤
      K / (lam * t * t) := by
  obtain ⟨K, hK_nn, hbound⟩ := J_1_asymptotic hlam hgamma hdisc
  refine ⟨K, hK_nn, ?_⟩
  intro t ht
  have ht_pos : 0 < t := by linarith
  have hlamt : 0 < lam * t := mul_pos hlam ht_pos
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_lamt_pos : 0 < Real.sqrt (lam * t) := Real.sqrt_pos.mpr hlamt
  have hsqrt_lamt_ne : Real.sqrt (lam * t) ≠ 0 := hsqrt_lamt_pos.ne'
  have hlamt_ne : lam * t ≠ 0 := hlamt.ne'
  have ht_ne : t ≠ 0 := ht_pos.ne'
  -- Substitution: (√(λt))² · I_1 = J_1, i.e., (λt) · I_1 = J_1.
  have hsub := I_n_J_n_relation lam alpha gamma 1 hlam ht_pos
  -- hsub : √(λt)^(1+1) · ∫ x, x^1 · exp(-tL) = ∫ u, u^1 · exp(-u²/2) · exp(-s_t)
  rw [show ((1 : ℕ) + 1) = 2 from rfl, sq, Real.mul_self_sqrt hlamt.le] at hsub
  -- hsub : (λt) · ∫ x, x^1 · exp(-tL) = ∫ u, u^1 · exp(-u²/2) · exp(-s_t)
  have hbnd := hbound ht
  rw [← hsub] at hbnd
  simp only [pow_one] at hbnd
  -- hbnd : |(λt) · I_1 - (-3A√(2π)/√t)| ≤ K/t
  -- Divide by (λt):
  have hgoal_eq : (∫ x : ℝ, x *
            Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
        - (-3 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) /
            (lam * t * Real.sqrt t)) =
      ((lam * t) *
            (∫ x : ℝ, x *
              Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
          - (-3 * cubicScale lam alpha *
              Real.sqrt (2 * Real.pi) / Real.sqrt t)) / (lam * t) := by
    field_simp
  rw [hgoal_eq, abs_div, abs_of_pos hlamt]
  rw [show (K / (lam * t * t) : ℝ) = (K / t) / (lam * t) by
        field_simp]
  exact div_le_div_of_nonneg_right hbnd hlamt.le

/-- **`I_2` asymptotic**: `I_2(t) = √(2π)/((λt)·√(λt)) + O(1/((λt)·√(λt)·t))`. -/
theorem I_2_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |(∫ x : ℝ, x ^ 2 * Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
        - Real.sqrt (2 * Real.pi) / (lam * t * Real.sqrt (lam * t))| ≤
      K / (lam * t * Real.sqrt (lam * t) * t) := by
  obtain ⟨K, hK_nn, hbound⟩ := J_2_asymptotic hlam hgamma hdisc
  refine ⟨K, hK_nn, ?_⟩
  intro t ht
  have ht_pos : 0 < t := by linarith
  have hlamt : 0 < lam * t := mul_pos hlam ht_pos
  have hsqrt_lamt_pos : 0 < Real.sqrt (lam * t) := Real.sqrt_pos.mpr hlamt
  have hsqrt_lamt_ne : Real.sqrt (lam * t) ≠ 0 := hsqrt_lamt_pos.ne'
  -- Substitution: (√(λt))³ · I_2 = J_2, i.e., (λt)·√(λt) · I_2 = J_2.
  have hsub := I_n_J_n_relation lam alpha gamma 2 hlam ht_pos
  -- hsub : √(λt)^3 · I_2 = J_2
  have hpow3 : Real.sqrt (lam * t) ^ (2 + 1) = (lam * t) * Real.sqrt (lam * t) := by
    rw [show (2 + 1 : ℕ) = 3 from rfl, show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one,
        sq, Real.mul_self_sqrt hlamt.le]
  rw [hpow3] at hsub
  have hbnd := hbound ht
  rw [← hsub] at hbnd
  -- hbnd : |(λt)·√(λt) · I_2 - √(2π)| ≤ K/t
  -- Divide by (λt)·√(λt) > 0:
  have hcoeff_pos : 0 < lam * t * Real.sqrt (lam * t) :=
    mul_pos hlamt hsqrt_lamt_pos
  have hgoal_eq : (∫ x : ℝ, x ^ 2 *
            Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
        - Real.sqrt (2 * Real.pi) / (lam * t * Real.sqrt (lam * t)) =
      ((lam * t * Real.sqrt (lam * t)) *
            (∫ x : ℝ, x ^ 2 *
              Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
          - Real.sqrt (2 * Real.pi)) / (lam * t * Real.sqrt (lam * t)) := by
    field_simp
  rw [hgoal_eq, abs_div, abs_of_pos hcoeff_pos]
  rw [show (K / (lam * t * Real.sqrt (lam * t) * t) : ℝ) =
        (K / t) / (lam * t * Real.sqrt (lam * t)) by field_simp]
  exact div_le_div_of_nonneg_right hbnd hcoeff_pos.le

/-- **`I_3` asymptotic**: `I_3(t) = -15A√(2π) / ((λt)²·√t) + O(1/((λt)²·t))`. -/
theorem I_3_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |(∫ x : ℝ, x ^ 3 * Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
        - (-15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) /
            ((lam * t) ^ 2 * Real.sqrt t))| ≤
      K / ((lam * t) ^ 2 * t) := by
  obtain ⟨K, hK_nn, hbound⟩ := J_3_asymptotic hlam hgamma hdisc
  refine ⟨K, hK_nn, ?_⟩
  intro t ht
  have ht_pos : 0 < t := by linarith
  have hlamt : 0 < lam * t := mul_pos hlam ht_pos
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hlamt_sq_pos : 0 < (lam * t) ^ 2 := by positivity
  have hlamt_sq_ne : (lam * t) ^ 2 ≠ 0 := hlamt_sq_pos.ne'
  -- Substitution: (√(λt))^4 · I_3 = J_3, i.e., (λt)² · I_3 = J_3.
  have hsub := I_n_J_n_relation lam alpha gamma 3 hlam ht_pos
  have hpow4 : Real.sqrt (lam * t) ^ (3 + 1) = (lam * t) ^ 2 := by
    rw [show (3 + 1 : ℕ) = 4 from rfl, show (4 : ℕ) = 2 * 2 from rfl,
        pow_mul, Real.sq_sqrt hlamt.le]
  rw [hpow4] at hsub
  have hbnd := hbound ht
  rw [← hsub] at hbnd
  -- hbnd : |(λt)² · I_3 - (-15A√(2π)/√t)| ≤ K/t
  have hgoal_eq : (∫ x : ℝ, x ^ 3 *
            Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
        - (-15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) /
            ((lam * t) ^ 2 * Real.sqrt t)) =
      ((lam * t) ^ 2 *
            (∫ x : ℝ, x ^ 3 *
              Real.exp (-(t * anharmonicPotential lam alpha gamma x)))
          - (-15 * cubicScale lam alpha *
              Real.sqrt (2 * Real.pi) / Real.sqrt t)) / (lam * t) ^ 2 := by
    field_simp
  rw [hgoal_eq, abs_div, abs_of_pos hlamt_sq_pos]
  rw [show (K / ((lam * t) ^ 2 * t) : ℝ) = (K / t) / (lam * t) ^ 2 by
        field_simp]
  exact div_le_div_of_nonneg_right hbnd hlamt_sq_pos.le

/-! ## Summary: from `I_n` asymptotics to the primer's covariance formula

The four `I_n` asymptotic theorems above (`I_0, I_1, I_2, I_3`) deliver, for the
anharmonic potential `L(x) = (λ/2)x² + (α/6)x³ + (γ/24)x⁴` under the
discriminant condition `α² < 3λγ`:

* `I_0(t) = √(2π)/√(λt) + O(1/(t·√(λt)))`
* `I_1(t) = -3A√(2π)/((λt)·√t) + O(1/((λt)·t))`
* `I_2(t) = √(2π)/((λt)·√(λt)) + O(1/((λt)·√(λt)·t))`
* `I_3(t) = -15A√(2π)/((λt)²·√t) + O(1/((λt)²·t))`

where `A = cubicScale lam alpha = α/(6·λ^{3/2})`.

The Gibbs expectations (`gibbsExpectation` from `Laplace.Gibbs`) are
`⟨x^n⟩_t = I_n(t)/I_0(t)`. From the four asymptotics above:

* `⟨x⟩_t = -α/(2λ²·t) + O(t^{-3/2})`
* `⟨x²⟩_t = 1/(λt) + O(t⁻²)`
* `⟨x³⟩_t = -5α/(2λ³·t²) + O(t^{-5/2})`

Hence the primer's covariance formula:

  `Cov_t[x², x] = ⟨x³⟩_t - ⟨x²⟩_t · ⟨x⟩_t`
                = `-5α/(2λ³ t²) + α/(2λ³ t²) + o(t⁻²)`
                = `-2α/(λ³ t²) + o(t⁻²)`.

The full assembly involves dividing the `I_n` asymptotics, multiplying expansions
to compute `⟨x²⟩_t·⟨x⟩_t`, and an `IsLittleO`-level argument for the cancellation.
That bookkeeping is tangential to the mathematical content (which is captured by
the `I_n` asymptotics above) and is left as a follow-up.

The coefficient cancellation is `-5α + α = -4α` divided by `2λ³ t²` to give
`-4α/(2λ³ t²) = -2α/(λ³ t²)`, matching the primer's `lem:laplace_cov2`
specialised to 1D with `φ = x²`, `ψ = x`. -/

/-- The coefficient identity that lies behind the primer's formula:
the leading-order anharmonic contributions in `⟨x³⟩_t` and `⟨x²⟩_t · ⟨x⟩_t`
combine to produce the covariance coefficient `-2α/λ³`. -/
theorem cov_coefficient_identity (lam alpha : ℝ) (hlam : lam ≠ 0) :
    -5 * alpha / (2 * lam ^ 3) - 1 / lam * (-alpha / (2 * lam ^ 2)) =
      -2 * alpha / lam ^ 3 := by
  field_simp
  ring

/-! ## Convergence consequences of the I_n asymptotics

Each `I_n_asymptotic` gives a bound `|I_n(t) - leading_n(t)| ≤ K_n · error_n(t)`
with `error_n(t) → 0`. This implies `I_n(t) - leading_n(t) → 0`. -/

/-- `J_n(t) = ∫ u^n · e^{-u²/2} · e^{-s_t(u)}`, packaged as a function for
convenience in the convergence chain. -/
noncomputable def J_n (lam alpha gamma : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ u : ℝ, u ^ n * Real.exp (-(u ^ 2) / 2) *
    Real.exp (-rescaledPerturbation lam alpha gamma t u)

/-- `I_n(t) = ∫ x^n · e^{-tL_anh(x)}`, the original-coordinate moment. -/
noncomputable def I_n (lam alpha gamma : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, x ^ n * Real.exp (-(t * anharmonicPotential lam alpha gamma x))

/-- `J_0(t) → √(2π)` as `t → ∞`. -/
theorem tendsto_J_0
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto (J_n lam alpha gamma 0) Filter.atTop
      (nhds (Real.sqrt (2 * Real.pi))) := by
  obtain ⟨K, hK_nn, hbound⟩ := J_0_asymptotic hlam hgamma hdisc
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨max 1 (K / ε + 1), fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn_pos : 0 < n := by linarith
  have hn_K : K / ε + 1 ≤ n := le_trans (le_max_right _ _) hn
  have h := hbound hn1
  -- h : |J_n 0 ... n - √(2π)| ≤ K/n  (after simp on u^0)
  simp only [J_n, pow_zero, one_mul] at h ⊢
  rw [Real.dist_eq]
  -- want: |∫ ... - √(2π)| < ε
  calc |(∫ u : ℝ, Real.exp (-(u ^ 2) / 2) *
            Real.exp (-rescaledPerturbation lam alpha gamma n u))
            - Real.sqrt (2 * Real.pi)|
      ≤ K / n := h
    _ < ε := by
        rcases eq_or_lt_of_le hK_nn with heq | hpos
        · rw [← heq]; simp; exact hε
        · rw [div_lt_iff₀ hn_pos]
          calc K = (K/ε) * ε := by field_simp
            _ < n * ε := by
                  apply mul_lt_mul_of_pos_right _ hε
                  linarith
            _ = ε * n := by ring

/-- `J_2(t) → √(2π)` as `t → ∞`. -/
theorem tendsto_J_2
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto (J_n lam alpha gamma 2) Filter.atTop
      (nhds (Real.sqrt (2 * Real.pi))) := by
  obtain ⟨K, hK_nn, hbound⟩ := J_2_asymptotic hlam hgamma hdisc
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨max 1 (K / ε + 1), fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn_pos : 0 < n := by linarith
  have hn_K : K / ε + 1 ≤ n := le_trans (le_max_right _ _) hn
  have h := hbound hn1
  simp only [J_n] at h ⊢
  rw [Real.dist_eq]
  calc |(∫ u : ℝ, u ^ 2 * Real.exp (-(u ^ 2) / 2) *
            Real.exp (-rescaledPerturbation lam alpha gamma n u))
            - Real.sqrt (2 * Real.pi)|
      ≤ K / n := h
    _ < ε := by
        rcases eq_or_lt_of_le hK_nn with heq | hpos
        · rw [← heq]; simp; exact hε
        · rw [div_lt_iff₀ hn_pos]
          calc K = (K/ε) * ε := by field_simp
            _ < n * ε := by
                  apply mul_lt_mul_of_pos_right _ hε
                  linarith
            _ = ε * n := by ring

/-- Helper: for `K ≥ 0` and `ε > 0`, eventually `K/√n < ε`. -/
private lemma div_sqrt_lt_eventually {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, K / Real.sqrt n < ε := by
  filter_upwards [Filter.eventually_ge_atTop (max 1 ((K / ε) ^ 2 + 1))] with n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn_pos : 0 < n := by linarith
  have hsqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hn_sq : (K / ε) ^ 2 + 1 ≤ n := le_trans (le_max_right _ _) hn
  rcases eq_or_lt_of_le hK with heq | hpos
  · rw [← heq]; simp [hε]
  · rw [div_lt_iff₀ hsqrt_n_pos]
    -- Want: K < ε · √n. Since n ≥ (K/ε)² + 1 > (K/ε)², we have √n > K/ε.
    have hKε : 0 < K / ε := div_pos hpos hε
    have hsqrt_n_gt : K / ε < Real.sqrt n := by
      rw [show K / ε = Real.sqrt ((K / ε) ^ 2) from
            (Real.sqrt_sq hKε.le).symm]
      apply Real.sqrt_lt_sqrt
      · exact sq_nonneg _
      · linarith
    have : K < ε * Real.sqrt n := by
      rw [show (K : ℝ) = ε * (K / ε) from by field_simp]
      exact mul_lt_mul_of_pos_left hsqrt_n_gt hε
    linarith

/-- `√t · J_1(t) → -3A · √(2π)` as `t → ∞`. -/
theorem tendsto_sqrt_t_mul_J_1
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto (fun t : ℝ => Real.sqrt t * J_n lam alpha gamma 1 t) Filter.atTop
      (nhds (-3 * cubicScale lam alpha * Real.sqrt (2 * Real.pi))) := by
  obtain ⟨K, hK_nn, hbound⟩ := J_1_asymptotic hlam hgamma hdisc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := (div_sqrt_lt_eventually hK_nn hε).exists_forall_of_atTop
  refine ⟨max 1 T, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn_pos : 0 < n := by linarith
  have hnT : T ≤ n := le_trans (le_max_right _ _) hn
  have hsqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsqrt_n_ne : Real.sqrt n ≠ 0 := hsqrt_n_pos.ne'
  have h := hbound hn1
  have h_div_eps : K / Real.sqrt n < ε := hT n hnT
  rw [Real.dist_eq]
  have h_mul : |Real.sqrt n * J_n lam alpha gamma 1 n
        - (-3 * cubicScale lam alpha * Real.sqrt (2 * Real.pi))|
        = Real.sqrt n * |J_n lam alpha gamma 1 n
            - (-3 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) /
                Real.sqrt n)| := by
    rw [show Real.sqrt n * J_n lam alpha gamma 1 n
            - (-3 * cubicScale lam alpha * Real.sqrt (2 * Real.pi)) =
          Real.sqrt n * (J_n lam alpha gamma 1 n
              - (-3 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) /
                  Real.sqrt n)) from by field_simp]
    rw [abs_mul, abs_of_pos hsqrt_n_pos]
  simp only [J_n] at h ⊢ h_mul
  rw [h_mul]
  calc Real.sqrt n *
        |(∫ u : ℝ, u ^ 1 * Real.exp (-(u ^ 2) / 2) *
            Real.exp (-rescaledPerturbation lam alpha gamma n u))
            - -3 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) /
                Real.sqrt n|
      ≤ Real.sqrt n * (K / n) := by
        apply mul_le_mul_of_nonneg_left h hsqrt_n_pos.le
    _ = K / Real.sqrt n := by
        rw [eq_div_iff hsqrt_n_ne]
        have hn_eq : (n : ℝ) = Real.sqrt n * Real.sqrt n :=
          (Real.mul_self_sqrt hn_pos.le).symm
        rw [show Real.sqrt n * (K / n) * Real.sqrt n = K * (Real.sqrt n * Real.sqrt n) / n
              from by ring, ← hn_eq]
        field_simp
    _ < ε := h_div_eps

/-- `√t · J_3(t) → -15A · √(2π)` as `t → ∞`. -/
theorem tendsto_sqrt_t_mul_J_3
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto (fun t : ℝ => Real.sqrt t * J_n lam alpha gamma 3 t) Filter.atTop
      (nhds (-15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi))) := by
  obtain ⟨K, hK_nn, hbound⟩ := J_3_asymptotic hlam hgamma hdisc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := (div_sqrt_lt_eventually hK_nn hε).exists_forall_of_atTop
  refine ⟨max 1 T, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn_pos : 0 < n := by linarith
  have hnT : T ≤ n := le_trans (le_max_right _ _) hn
  have hsqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsqrt_n_ne : Real.sqrt n ≠ 0 := hsqrt_n_pos.ne'
  have h := hbound hn1
  have h_div_eps : K / Real.sqrt n < ε := hT n hnT
  rw [Real.dist_eq]
  have h_mul : |Real.sqrt n * J_n lam alpha gamma 3 n
        - (-15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi))|
        = Real.sqrt n * |J_n lam alpha gamma 3 n
            - (-15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) /
                Real.sqrt n)| := by
    rw [show Real.sqrt n * J_n lam alpha gamma 3 n
            - (-15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi)) =
          Real.sqrt n * (J_n lam alpha gamma 3 n
              - (-15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) /
                  Real.sqrt n)) from by field_simp]
    rw [abs_mul, abs_of_pos hsqrt_n_pos]
  simp only [J_n] at h ⊢ h_mul
  rw [h_mul]
  calc Real.sqrt n *
        |(∫ u : ℝ, u ^ 3 * Real.exp (-(u ^ 2) / 2) *
            Real.exp (-rescaledPerturbation lam alpha gamma n u))
            - -15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) /
                Real.sqrt n|
      ≤ Real.sqrt n * (K / n) := by
        apply mul_le_mul_of_nonneg_left h hsqrt_n_pos.le
    _ = K / Real.sqrt n := by
        rw [eq_div_iff hsqrt_n_ne]
        have hn_eq : (n : ℝ) = Real.sqrt n * Real.sqrt n :=
          (Real.mul_self_sqrt hn_pos.le).symm
        rw [show Real.sqrt n * (K / n) * Real.sqrt n = K * (Real.sqrt n * Real.sqrt n) / n
              from by ring, ← hn_eq]
        field_simp
    _ < ε := h_div_eps

/-! ## Final assembly: the primer's anharmonic covariance formula

The four `tendsto_*` theorems above combine to give the primer's
`Cov_t[x², x] = -2α/(λ³t²) + o(t⁻²)` formula. -/

/-- `√(2π) > 0`. -/
private lemma sqrt_two_pi_pos : 0 < Real.sqrt (2 * Real.pi) := by
  apply Real.sqrt_pos.mpr; positivity

/-- `√(2π) ≠ 0`. -/
private lemma sqrt_two_pi_ne : Real.sqrt (2 * Real.pi) ≠ 0 := sqrt_two_pi_pos.ne'

/-- The numerator of the rescaled covariance: `√t · (J_0·J_3 - J_2·J_1)`
tends to `-12 A √(2π)²  = -12 A · 2π` as `t → ∞`. -/
private lemma tendsto_numerator
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto (fun t : ℝ =>
        Real.sqrt t * (J_n lam alpha gamma 0 t * J_n lam alpha gamma 3 t
                        - J_n lam alpha gamma 2 t * J_n lam alpha gamma 1 t))
      Filter.atTop
      (nhds (-12 * cubicScale lam alpha * (2 * Real.pi))) := by
  have hJ0 := tendsto_J_0 hlam hgamma hdisc
  have hJ2 := tendsto_J_2 hlam hgamma hdisc
  have hsqrtJ1 := tendsto_sqrt_t_mul_J_1 hlam hgamma hdisc
  have hsqrtJ3 := tendsto_sqrt_t_mul_J_3 hlam hgamma hdisc
  -- √t · J_0 · J_3 = J_0 · (√t · J_3) → √(2π) · (-15A√(2π)) = -15A · 2π
  have hterm1 : Filter.Tendsto
      (fun t : ℝ => J_n lam alpha gamma 0 t * (Real.sqrt t * J_n lam alpha gamma 3 t))
      Filter.atTop
      (nhds (Real.sqrt (2 * Real.pi) *
              (-15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi)))) :=
    hJ0.mul hsqrtJ3
  -- √t · J_2 · J_1 = J_2 · (√t · J_1) → √(2π) · (-3A√(2π)) = -3A · 2π
  have hterm2 : Filter.Tendsto
      (fun t : ℝ => J_n lam alpha gamma 2 t * (Real.sqrt t * J_n lam alpha gamma 1 t))
      Filter.atTop
      (nhds (Real.sqrt (2 * Real.pi) *
              (-3 * cubicScale lam alpha * Real.sqrt (2 * Real.pi)))) :=
    hJ2.mul hsqrtJ1
  -- Difference:
  have hdiff := hterm1.sub hterm2
  -- The integrand of hdiff is `J_0 · (√t · J_3) - J_2 · (√t · J_1)`,
  -- which equals `√t · (J_0 · J_3 - J_2 · J_1)` by ring.
  have hcong : (fun t : ℝ =>
        J_n lam alpha gamma 0 t * (Real.sqrt t * J_n lam alpha gamma 3 t)
        - J_n lam alpha gamma 2 t * (Real.sqrt t * J_n lam alpha gamma 1 t)) =
      (fun t : ℝ =>
        Real.sqrt t *
          (J_n lam alpha gamma 0 t * J_n lam alpha gamma 3 t
            - J_n lam alpha gamma 2 t * J_n lam alpha gamma 1 t)) := by
    ext t; ring
  rw [hcong] at hdiff
  -- Compute the value: √(2π)·(-15A·√(2π)) - √(2π)·(-3A·√(2π)) = -12A · 2π.
  have hval : Real.sqrt (2 * Real.pi) *
        (-15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi))
      - Real.sqrt (2 * Real.pi) *
        (-3 * cubicScale lam alpha * Real.sqrt (2 * Real.pi)) =
      -12 * cubicScale lam alpha * (2 * Real.pi) := by
    have hsq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
      Real.mul_self_sqrt (by positivity)
    linear_combination (-12 * cubicScale lam alpha) * hsq
  rw [← hval]
  exact hdiff

/-- `J_0(t)² → 2π` as `t → ∞`. -/
private lemma tendsto_J_0_sq
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto (fun t : ℝ => J_n lam alpha gamma 0 t ^ 2) Filter.atTop
      (nhds (2 * Real.pi)) := by
  have h := (tendsto_J_0 hlam hgamma hdisc).pow 2
  -- h : Tendsto (J_0)^2 → (√(2π))^2
  have heq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt (by positivity)
  rw [heq] at h
  exact h

/-- The main quotient: `√t · (J_0·J_3 - J_2·J_1) / J_0² → -12 A` as `t → ∞`. -/
private lemma tendsto_main_quotient
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto (fun t : ℝ =>
        Real.sqrt t * (J_n lam alpha gamma 0 t * J_n lam alpha gamma 3 t
                        - J_n lam alpha gamma 2 t * J_n lam alpha gamma 1 t) /
        J_n lam alpha gamma 0 t ^ 2) Filter.atTop
      (nhds (-12 * cubicScale lam alpha)) := by
  have hnum := tendsto_numerator hlam hgamma hdisc
  have hden := tendsto_J_0_sq hlam hgamma hdisc
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := h2pi_pos.ne'
  -- Apply Tendsto.div with the limit `2π ≠ 0`.
  have hquot := hnum.div hden h2pi_ne
  -- Compute the limit value:
  --   -12 A · 2π / (2π) = -12 A.
  have hval : -12 * cubicScale lam alpha * (2 * Real.pi) / (2 * Real.pi)
        = -12 * cubicScale lam alpha := by
    field_simp
  rw [hval] at hquot
  exact hquot

/-- **The primer's anharmonic covariance formula** (rescaled form).

  `lim_{t → ∞} t² · Cov_t[x², x] = -2α/λ³`,

equivalently `Cov_t[x², x] = -2α/(λ³ t²) + o(t⁻²)`.

This is the rescaled-coordinate form expressed via `J_n`. To bridge to the
original `gibbsCov` formulation, multiply by the substitution-identity factor
`λ^{3/2}`: the result `tendsto_main_quotient` gives `→ -12 A`, and dividing by
`λ^{3/2}` (using `A = cubicScale lam alpha = α/(6 λ^{3/2})`) yields `-2α/λ³`. -/
theorem cov_anharmonic_J_form_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto (fun t : ℝ =>
        Real.sqrt t * (J_n lam alpha gamma 0 t * J_n lam alpha gamma 3 t
                        - J_n lam alpha gamma 2 t * J_n lam alpha gamma 1 t) /
        (lam * Real.sqrt lam * J_n lam alpha gamma 0 t ^ 2)) Filter.atTop
      (nhds (-2 * alpha / lam ^ 3)) := by
  have hmain := tendsto_main_quotient hlam hgamma hdisc
  have hsqrt_lam_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsqrt_lam_ne : Real.sqrt lam ≠ 0 := hsqrt_lam_pos.ne'
  have hlam_ne : lam ≠ 0 := hlam.ne'
  -- Divide hmain by lam · √lam = lam^{3/2}:
  have hdivide := hmain.div_const (lam * Real.sqrt lam)
  -- Compute: -12 A / (λ · √λ) = -12 · α/(6 λ^{3/2}) / (λ^{3/2}) = -2α/λ³.
  have hval : -12 * cubicScale lam alpha / (lam * Real.sqrt lam) =
      -2 * alpha / lam ^ 3 := by
    unfold cubicScale
    have hlam_sq : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
    field_simp
    linear_combination (12 * alpha) * hlam_sq
  rw [hval] at hdivide
  -- Goal: same form with /(λ·√λ·J_0²). Match by congr.
  convert hdivide using 1
  ext t
  field_simp

/-! ## Bridge to `gibbsCov` and the primer's formula -/

/-- `gibbsCov(L, t, x², x) = (Z·∫x³e^{-tL} - ∫x²e^{-tL}·∫xe^{-tL}) / Z²`. -/
private lemma gibbsCov_x_sq_x_eq_I_form
    (L : ℝ → ℝ) (t : ℝ) :
    Laplace.gibbsCov L t (fun x => x ^ 2) (fun x => x) =
      ((∫ x : ℝ, Real.exp (-(t * L x))) *
          (∫ x : ℝ, x ^ 3 * Real.exp (-(t * L x)))
        - (∫ x : ℝ, x ^ 2 * Real.exp (-(t * L x))) *
            (∫ x : ℝ, x * Real.exp (-(t * L x)))) /
      (∫ x : ℝ, Real.exp (-(t * L x))) ^ 2 := by
  unfold Laplace.gibbsCov Laplace.gibbsExpectation Laplace.partitionFunction
  rw [show (fun x : ℝ => x ^ 2 * x) = (fun x : ℝ => x ^ 3) from by ext; ring]
  by_cases hZ : (∫ x : ℝ, Real.exp (-(t * L x))) = 0
  · rw [hZ]; simp
  · field_simp

/-- **The primer's anharmonic covariance formula** in `gibbsCov` form.

For `L(x) = (λ/2)x² + (α/6)x³ + (γ/24)x⁴` with `λ > 0`, `γ > 0`, and the
discriminant condition `α² < 3λγ`,

  `lim_{t → ∞} t² · Cov_t[x², x] = -2α / λ³`,

equivalently `Cov_t[x², x] = -2α/(λ³ t²) + o(t⁻²)`. -/
theorem cov_anharmonic_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto (fun t : ℝ => t ^ 2 * Laplace.gibbsCov
        (anharmonicPotential lam alpha gamma) t
        (fun x => x ^ 2) (fun x => x)) Filter.atTop
      (nhds (-2 * alpha / lam ^ 3)) := by
  have hJ_form := cov_anharmonic_J_form_asymptotic hlam hgamma hdisc
  apply Filter.Tendsto.congr' _ hJ_form
  -- Eventually J_0(t) ≠ 0 (since J_0 → √(2π) > 0).
  have hJ0_ev : ∀ᶠ t in Filter.atTop, J_n lam alpha gamma 0 t ≠ 0 := by
    have hJ0 := tendsto_J_0 hlam hgamma hdisc
    have h_pos_J0 : ∀ᶠ t in Filter.atTop, 0 < J_n lam alpha gamma 0 t :=
      Filter.Tendsto.eventually_const_lt sqrt_two_pi_pos hJ0
    filter_upwards [h_pos_J0] with t ht; exact ht.ne'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ), hJ0_ev] with t ht hJ0_ne
  have hlamt : 0 < lam * t := mul_pos hlam ht
  have hsqrt_lamt_pos : 0 < Real.sqrt (lam * t) := Real.sqrt_pos.mpr hlamt
  have hsqrt_lamt_ne : Real.sqrt (lam * t) ≠ 0 := hsqrt_lamt_pos.ne'
  have hsqrt_lam_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsqrt_lam_ne : Real.sqrt lam ≠ 0 := hsqrt_lam_pos.ne'
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_t_ne : Real.sqrt t ≠ 0 := hsqrt_t_pos.ne'
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have ht_ne : t ≠ 0 := ht.ne'
  -- Substitution identities.
  have h0 := I_n_J_n_relation lam alpha gamma 0 hlam ht
  have h1 := I_n_J_n_relation lam alpha gamma 1 hlam ht
  have h2 := I_n_J_n_relation lam alpha gamma 2 hlam ht
  have h3 := I_n_J_n_relation lam alpha gamma 3 hlam ht
  rw [pow_one] at h0
  rw [show (1 + 1 : ℕ) = 2 from rfl] at h1
  rw [show (2 + 1 : ℕ) = 3 from rfl] at h2
  rw [show (3 + 1 : ℕ) = 4 from rfl] at h3
  simp only [pow_zero, one_mul] at h0
  simp only [pow_one] at h1
  rw [gibbsCov_x_sq_x_eq_I_form]
  set Z := ∫ x : ℝ, Real.exp (-(t * anharmonicPotential lam alpha gamma x)) with hZ_def
  set IL1 := ∫ x : ℝ, x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))
    with hIL1_def
  set IL2 := ∫ x : ℝ, x ^ 2 *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x)) with hIL2_def
  set IL3 := ∫ x : ℝ, x ^ 3 *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x)) with hIL3_def
  -- Substitution identities, in matching forms.
  have hZ_eq : Real.sqrt (lam * t) * Z = J_n lam alpha gamma 0 t := by
    unfold J_n; simp only [pow_zero, one_mul]; exact h0
  have hIL1_eq : Real.sqrt (lam * t) ^ 2 * IL1 = J_n lam alpha gamma 1 t := by
    unfold J_n; simp only [pow_one]; exact h1
  have hIL2_eq : Real.sqrt (lam * t) ^ 3 * IL2 = J_n lam alpha gamma 2 t := by
    unfold J_n; exact h2
  have hIL3_eq : Real.sqrt (lam * t) ^ 4 * IL3 = J_n lam alpha gamma 3 t := by
    unfold J_n; exact h3
  have hZ_ne : Z ≠ 0 := fun hZ => hJ0_ne (by rw [← hZ_eq, hZ, mul_zero])
  -- Substitute IL_n = J_n / (√(λt))^(n+1) and Z = J_0/√(λt).
  have hsqrt_lamt_sq : Real.sqrt (lam * t) ^ 2 = lam * t := Real.sq_sqrt hlamt.le
  have hsqrt_lamt_split : Real.sqrt (lam * t) = Real.sqrt lam * Real.sqrt t :=
    Real.sqrt_mul hlam.le t
  have hZ_sub : Z = J_n lam alpha gamma 0 t / Real.sqrt (lam * t) := by
    rw [eq_div_iff hsqrt_lamt_ne, mul_comm]; exact hZ_eq
  have hIL1_sub : IL1 = J_n lam alpha gamma 1 t / (lam * t) := by
    rw [eq_div_iff hlamt.ne', mul_comm, ← hsqrt_lamt_sq]; exact hIL1_eq
  have hIL2_sub : IL2 = J_n lam alpha gamma 2 t /
      (lam * t * Real.sqrt (lam * t)) := by
    rw [eq_div_iff (mul_ne_zero hlamt.ne' hsqrt_lamt_ne), mul_comm,
        show (lam * t * Real.sqrt (lam * t) : ℝ) = Real.sqrt (lam * t) ^ 3 from by
          rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, hsqrt_lamt_sq]]
    exact hIL2_eq
  have hIL3_sub : IL3 = J_n lam alpha gamma 3 t / (lam * t) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hlamt.ne'), mul_comm,
        show ((lam * t) ^ 2 : ℝ) = Real.sqrt (lam * t) ^ 4 from by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsqrt_lamt_sq]]
    exact hIL3_eq
  rw [hZ_sub, hIL1_sub, hIL2_sub, hIL3_sub, hsqrt_lamt_split]
  -- GPT-5.5-Pro's recipe: freeze the square roots, rewrite `lam,t` as squares,
  -- then `field_simp; ring`.
  set sl : ℝ := Real.sqrt lam with hsl_def
  set st : ℝ := Real.sqrt t with hst_def
  have hsl2 : sl ^ 2 = lam := Real.sq_sqrt hlam.le
  have hst2 : st ^ 2 = t := Real.sq_sqrt ht.le
  have hsl_ne : sl ≠ 0 := hsqrt_lam_ne
  have hst_ne : st ≠ 0 := hsqrt_t_ne
  have hJ0_sq_ne : J_n lam alpha gamma 0 t ^ 2 ≠ 0 := pow_ne_zero 2 hJ0_ne
  -- Eliminate lam, t in favour of sl², st².
  rw [← hsl2, ← hst2]
  field_simp

/-! ## Two more 1D anharmonic asymptotics

The primer's `figures/plot1_convergence.png` plots three asymptotic limits
side by side:

  (a) `t · ⟨w⟩_t      → -α/(2λ²)`   (`lem:laplace_exp` in 1D)
  (b) `t · Cov_t[w,w] → 1/λ`         (`lem:laplace_cov` in 1D)
  (c) `t² · Cov_t[w²,w] → -2α/λ³`    (`lem:laplace_cov2` in 1D)

We have already proved (c) above. (a) and (b) are essentially algebraic
combinations of the `I_n` and `J_n` asymptotics already established. -/

/-- (a) **Mean asymptotic, J-form**: `√t · J_1 / (√λ · J_0) → -α/(2λ²)`.

Recall `√t · J_1 → -3·A·√(2π)` (`tendsto_sqrt_t_mul_J_1`) and
`J_0 → √(2π)` (`tendsto_J_0`); divide by `√(2π)` and by `√λ`, and use
`A = α/(6 λ^{3/2})` to get `-α/(2λ²)`. -/
theorem mean_anharmonic_J_form_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto (fun t : ℝ =>
        Real.sqrt t * J_n lam alpha gamma 1 t /
          (Real.sqrt lam * J_n lam alpha gamma 0 t)) Filter.atTop
      (nhds (-alpha / (2 * lam ^ 2))) := by
  have hJ1 := tendsto_sqrt_t_mul_J_1 hlam hgamma hdisc
  have hJ0 := tendsto_J_0 hlam hgamma hdisc
  have hsqrt_lam_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsqrt_lam_ne : Real.sqrt lam ≠ 0 := hsqrt_lam_pos.ne'
  -- Build denominator: √λ · J_0 → √λ · √(2π).
  have hden : Filter.Tendsto
      (fun t : ℝ => Real.sqrt lam * J_n lam alpha gamma 0 t) Filter.atTop
      (nhds (Real.sqrt lam * Real.sqrt (2 * Real.pi))) :=
    (tendsto_const_nhds).mul hJ0
  have hden_ne : Real.sqrt lam * Real.sqrt (2 * Real.pi) ≠ 0 :=
    mul_ne_zero hsqrt_lam_ne sqrt_two_pi_ne
  -- Quotient tends to (-3 A √(2π)) / (√λ · √(2π)) = -α/(2λ²).
  have hquot := hJ1.div hden hden_ne
  have hval : -3 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) /
      (Real.sqrt lam * Real.sqrt (2 * Real.pi)) = -alpha / (2 * lam ^ 2) := by
    unfold cubicScale
    have hlam_self : Real.sqrt lam * Real.sqrt lam = lam :=
      Real.mul_self_sqrt hlam.le
    have hlam_ne : lam ≠ 0 := hlam.ne'
    have h2pi_ne : Real.sqrt (2 * Real.pi) ≠ 0 := sqrt_two_pi_ne
    have hsqrt_lam_ne : Real.sqrt lam ≠ 0 := hsqrt_lam_ne
    rw [show (-3 * (alpha / (6 * lam * Real.sqrt lam)) * Real.sqrt (2 * Real.pi)) /
            (Real.sqrt lam * Real.sqrt (2 * Real.pi)) =
          -3 * alpha / (6 * lam * (Real.sqrt lam * Real.sqrt lam)) from by
            field_simp]
    rw [hlam_self]
    field_simp
    ring
  rw [hval] at hquot
  exact hquot

/-- **Exact bridge**: for `t > 0` and `J_0(t) ≠ 0`,
`t · ⟨x⟩_t = √t · J_1(t) / (√λ · J_0(t))`. -/
private lemma mean_J_form_exact
    {lam alpha gamma : ℝ} (hlam : 0 < lam)
    {t : ℝ} (ht : 0 < t)
    (hJ0_ne : J_n lam alpha gamma 0 t ≠ 0) :
    t * Laplace.gibbsExpectation
      (anharmonicPotential lam alpha gamma) t (fun x => x) =
    Real.sqrt t * J_n lam alpha gamma 1 t /
      (Real.sqrt lam * J_n lam alpha gamma 0 t) := by
  have hlamt : 0 < lam * t := mul_pos hlam ht
  have hsqrt_lamt_pos : 0 < Real.sqrt (lam * t) := Real.sqrt_pos.mpr hlamt
  have hsqrt_lamt_ne : Real.sqrt (lam * t) ≠ 0 := hsqrt_lamt_pos.ne'
  have hsqrt_lam_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsqrt_lam_ne : Real.sqrt lam ≠ 0 := hsqrt_lam_pos.ne'
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_t_ne : Real.sqrt t ≠ 0 := hsqrt_t_pos.ne'
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have ht_ne : t ≠ 0 := ht.ne'
  unfold Laplace.gibbsExpectation Laplace.partitionFunction
  set Z := ∫ x : ℝ, Real.exp (-(t * anharmonicPotential lam alpha gamma x)) with hZ_def
  set IL1 := ∫ x : ℝ, x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))
    with hIL1_def
  have h0 := I_n_J_n_relation lam alpha gamma 0 hlam ht
  have h1 := I_n_J_n_relation lam alpha gamma 1 hlam ht
  rw [pow_one] at h0
  rw [show (1 + 1 : ℕ) = 2 from rfl] at h1
  simp only [pow_zero, one_mul] at h0
  simp only [pow_one] at h1
  have hZ_eq : Real.sqrt (lam * t) * Z = J_n lam alpha gamma 0 t := by
    unfold J_n; simp only [pow_zero, one_mul]; exact h0
  have hIL1_eq : Real.sqrt (lam * t) ^ 2 * IL1 = J_n lam alpha gamma 1 t := by
    unfold J_n; simp only [pow_one]; exact h1
  have hsqrt_lamt_sq : Real.sqrt (lam * t) ^ 2 = lam * t := Real.sq_sqrt hlamt.le
  have hsqrt_lamt_split : Real.sqrt (lam * t) = Real.sqrt lam * Real.sqrt t :=
    Real.sqrt_mul hlam.le t
  have hZ_sub : Z = J_n lam alpha gamma 0 t / Real.sqrt (lam * t) := by
    rw [eq_div_iff hsqrt_lamt_ne, mul_comm]; exact hZ_eq
  have hIL1_sub : IL1 = J_n lam alpha gamma 1 t / (lam * t) := by
    rw [eq_div_iff hlamt.ne', mul_comm, ← hsqrt_lamt_sq]; exact hIL1_eq
  have hZ_ne : Z ≠ 0 := fun hZ => hJ0_ne (by rw [← hZ_eq, hZ, mul_zero])
  rw [hZ_sub, hIL1_sub, hsqrt_lamt_split]
  set sl : ℝ := Real.sqrt lam with hsl_def
  set st : ℝ := Real.sqrt t with hst_def
  have hsl2 : sl ^ 2 = lam := Real.sq_sqrt hlam.le
  have hst2 : st ^ 2 = t := Real.sq_sqrt ht.le
  have hsl_ne : sl ≠ 0 := hsqrt_lam_ne
  have hst_ne : st ≠ 0 := hsqrt_t_ne
  rw [← hsl2, ← hst2]
  field_simp

/-- (a) **Mean asymptotic** in `gibbsExpectation` form: `t · ⟨x⟩_t → -α/(2λ²)`.

Equivalently `⟨x⟩_t = -α/(2λ² t) + o(t⁻¹)` as `t → ∞`. -/
theorem mean_anharmonic_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto (fun t : ℝ => t * Laplace.gibbsExpectation
        (anharmonicPotential lam alpha gamma) t (fun x => x)) Filter.atTop
      (nhds (-alpha / (2 * lam ^ 2))) := by
  have hJ_form := mean_anharmonic_J_form_asymptotic hlam hgamma hdisc
  apply Filter.Tendsto.congr' _ hJ_form
  have hJ0_ev : ∀ᶠ t in Filter.atTop, J_n lam alpha gamma 0 t ≠ 0 := by
    have hJ0 := tendsto_J_0 hlam hgamma hdisc
    have h_pos_J0 : ∀ᶠ t in Filter.atTop, 0 < J_n lam alpha gamma 0 t :=
      Filter.Tendsto.eventually_const_lt sqrt_two_pi_pos hJ0
    filter_upwards [h_pos_J0] with t ht; exact ht.ne'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ), hJ0_ev] with t ht hJ0_ne
  have hlamt : 0 < lam * t := mul_pos hlam ht
  have hsqrt_lamt_pos : 0 < Real.sqrt (lam * t) := Real.sqrt_pos.mpr hlamt
  have hsqrt_lamt_ne : Real.sqrt (lam * t) ≠ 0 := hsqrt_lamt_pos.ne'
  have hsqrt_lam_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsqrt_lam_ne : Real.sqrt lam ≠ 0 := hsqrt_lam_pos.ne'
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_t_ne : Real.sqrt t ≠ 0 := hsqrt_t_pos.ne'
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have ht_ne : t ≠ 0 := ht.ne'
  unfold Laplace.gibbsExpectation Laplace.partitionFunction
  set Z := ∫ x : ℝ, Real.exp (-(t * anharmonicPotential lam alpha gamma x)) with hZ_def
  set IL1 := ∫ x : ℝ, x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))
    with hIL1_def
  -- Substitution identities.
  have h0 := I_n_J_n_relation lam alpha gamma 0 hlam ht
  have h1 := I_n_J_n_relation lam alpha gamma 1 hlam ht
  rw [pow_one] at h0
  rw [show (1 + 1 : ℕ) = 2 from rfl] at h1
  simp only [pow_zero, one_mul] at h0
  simp only [pow_one] at h1
  have hZ_eq : Real.sqrt (lam * t) * Z = J_n lam alpha gamma 0 t := by
    unfold J_n; simp only [pow_zero, one_mul]; exact h0
  have hIL1_eq : Real.sqrt (lam * t) ^ 2 * IL1 = J_n lam alpha gamma 1 t := by
    unfold J_n; simp only [pow_one]; exact h1
  have hsqrt_lamt_sq : Real.sqrt (lam * t) ^ 2 = lam * t := Real.sq_sqrt hlamt.le
  have hsqrt_lamt_split : Real.sqrt (lam * t) = Real.sqrt lam * Real.sqrt t :=
    Real.sqrt_mul hlam.le t
  have hZ_sub : Z = J_n lam alpha gamma 0 t / Real.sqrt (lam * t) := by
    rw [eq_div_iff hsqrt_lamt_ne, mul_comm]; exact hZ_eq
  have hIL1_sub : IL1 = J_n lam alpha gamma 1 t / (lam * t) := by
    rw [eq_div_iff hlamt.ne', mul_comm, ← hsqrt_lamt_sq]; exact hIL1_eq
  have hZ_ne : Z ≠ 0 := fun hZ => hJ0_ne (by rw [← hZ_eq, hZ, mul_zero])
  rw [hZ_sub, hIL1_sub, hsqrt_lamt_split]
  -- GPT-5.5-Pro recipe: substitute fresh symbols for the square roots.
  set sl : ℝ := Real.sqrt lam with hsl_def
  set st : ℝ := Real.sqrt t with hst_def
  have hsl2 : sl ^ 2 = lam := Real.sq_sqrt hlam.le
  have hst2 : st ^ 2 = t := Real.sq_sqrt ht.le
  have hsl_ne : sl ≠ 0 := hsqrt_lam_ne
  have hst_ne : st ≠ 0 := hsqrt_t_ne
  rw [← hsl2, ← hst2]
  field_simp

/-- (b) **Self-covariance asymptotic, J-form**: `(J_2·J_0 - J_1²) / (λ·J_0²) → 1/λ`.

Recall `J_0, J_2 → √(2π)` and `J_1 → 0`. So the numerator
`J_2·J_0 - J_1² → (√(2π))² - 0 = 2π` and the denominator
`λ·J_0² → λ · 2π`. The ratio is `1/λ`. -/
theorem var_anharmonic_J_form_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto (fun t : ℝ =>
        (J_n lam alpha gamma 2 t * J_n lam alpha gamma 0 t
          - J_n lam alpha gamma 1 t ^ 2) /
        (lam * J_n lam alpha gamma 0 t ^ 2)) Filter.atTop
      (nhds (1 / lam)) := by
  have hJ0 := tendsto_J_0 hlam hgamma hdisc
  have hJ2 := tendsto_J_2 hlam hgamma hdisc
  have hsqrtJ1 := tendsto_sqrt_t_mul_J_1 hlam hgamma hdisc
  -- Step 1: J_1 → 0, since √t·J_1 → finite and √t → atTop.
  have hJ1 : Filter.Tendsto (J_n lam alpha gamma 1) Filter.atTop (nhds 0) := by
    have h := hsqrtJ1.div_atTop Real.tendsto_sqrt_atTop
    -- h : Tendsto ((√t · J_1)/√t) → 0
    apply h.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    have hsqrt_ne : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
    field_simp
  -- Numerator: J_2·J_0 - J_1² → √(2π)·√(2π) - 0 = 2π.
  have hnum : Filter.Tendsto (fun t : ℝ =>
        J_n lam alpha gamma 2 t * J_n lam alpha gamma 0 t
        - J_n lam alpha gamma 1 t ^ 2) Filter.atTop
      (nhds (Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) - 0 ^ 2)) :=
    (hJ2.mul hJ0).sub (hJ1.pow 2)
  -- Denominator: λ·J_0² → λ·2π.
  have hden : Filter.Tendsto (fun t : ℝ =>
        lam * J_n lam alpha gamma 0 t ^ 2) Filter.atTop
      (nhds (lam * Real.sqrt (2 * Real.pi) ^ 2)) :=
    tendsto_const_nhds.mul (hJ0.pow 2)
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  have hsqrt2pi_sq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt h2pi_pos.le
  have hden_ne : lam * Real.sqrt (2 * Real.pi) ^ 2 ≠ 0 := by
    rw [hsqrt2pi_sq]; positivity
  have hquot := hnum.div hden hden_ne
  -- Compute: (2π - 0)/(λ · 2π) = 1/λ.
  have hval : (Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) - 0 ^ 2) /
      (lam * Real.sqrt (2 * Real.pi) ^ 2) = 1 / lam := by
    rw [hsqrt2pi_sq, Real.mul_self_sqrt h2pi_pos.le]
    have hlam_ne : lam ≠ 0 := hlam.ne'
    have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := h2pi_pos.ne'
    field_simp
    ring
  rw [hval] at hquot
  exact hquot

/-- `gibbsCov(L, t, x, x) = (Z·∫x²e^{-tL} - (∫xe^{-tL})²) / Z²`. -/
private lemma gibbsCov_x_x_eq_I_form
    (L : ℝ → ℝ) (t : ℝ) :
    Laplace.gibbsCov L t (fun x => x) (fun x => x) =
      ((∫ x : ℝ, Real.exp (-(t * L x))) *
          (∫ x : ℝ, x ^ 2 * Real.exp (-(t * L x)))
        - (∫ x : ℝ, x * Real.exp (-(t * L x))) ^ 2) /
      (∫ x : ℝ, Real.exp (-(t * L x))) ^ 2 := by
  unfold Laplace.gibbsCov Laplace.gibbsExpectation Laplace.partitionFunction
  rw [show (fun x : ℝ => x * x) = (fun x : ℝ => x ^ 2) from by ext x; ring]
  by_cases hZ : (∫ x : ℝ, Real.exp (-(t * L x))) = 0
  · rw [hZ]; simp
  · field_simp

/-- (b) **Self-covariance asymptotic** in `gibbsCov` form: `t · Cov_t[x,x] → 1/λ`.

Equivalently `Cov_t[x,x] = 1/(λ t) + o(t⁻¹)` as `t → ∞`. -/
theorem cov_self_anharmonic_asymptotic
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    Filter.Tendsto (fun t : ℝ => t * Laplace.gibbsCov
        (anharmonicPotential lam alpha gamma) t
        (fun x => x) (fun x => x)) Filter.atTop
      (nhds (1 / lam)) := by
  have hJ_form := var_anharmonic_J_form_asymptotic hlam hgamma hdisc
  apply Filter.Tendsto.congr' _ hJ_form
  have hJ0_ev : ∀ᶠ t in Filter.atTop, J_n lam alpha gamma 0 t ≠ 0 := by
    have hJ0 := tendsto_J_0 hlam hgamma hdisc
    have h_pos_J0 : ∀ᶠ t in Filter.atTop, 0 < J_n lam alpha gamma 0 t :=
      Filter.Tendsto.eventually_const_lt sqrt_two_pi_pos hJ0
    filter_upwards [h_pos_J0] with t ht; exact ht.ne'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ), hJ0_ev] with t ht hJ0_ne
  have hlamt : 0 < lam * t := mul_pos hlam ht
  have hsqrt_lamt_pos : 0 < Real.sqrt (lam * t) := Real.sqrt_pos.mpr hlamt
  have hsqrt_lamt_ne : Real.sqrt (lam * t) ≠ 0 := hsqrt_lamt_pos.ne'
  have hsqrt_lam_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsqrt_lam_ne : Real.sqrt lam ≠ 0 := hsqrt_lam_pos.ne'
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_t_ne : Real.sqrt t ≠ 0 := hsqrt_t_pos.ne'
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have ht_ne : t ≠ 0 := ht.ne'
  rw [gibbsCov_x_x_eq_I_form]
  set Z := ∫ x : ℝ, Real.exp (-(t * anharmonicPotential lam alpha gamma x)) with hZ_def
  set IL1 := ∫ x : ℝ, x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))
    with hIL1_def
  set IL2 := ∫ x : ℝ, x ^ 2 *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x)) with hIL2_def
  have h0 := I_n_J_n_relation lam alpha gamma 0 hlam ht
  have h1 := I_n_J_n_relation lam alpha gamma 1 hlam ht
  have h2 := I_n_J_n_relation lam alpha gamma 2 hlam ht
  rw [pow_one] at h0
  rw [show (1 + 1 : ℕ) = 2 from rfl] at h1
  rw [show (2 + 1 : ℕ) = 3 from rfl] at h2
  simp only [pow_zero, one_mul] at h0
  simp only [pow_one] at h1
  have hZ_eq : Real.sqrt (lam * t) * Z = J_n lam alpha gamma 0 t := by
    unfold J_n; simp only [pow_zero, one_mul]; exact h0
  have hIL1_eq : Real.sqrt (lam * t) ^ 2 * IL1 = J_n lam alpha gamma 1 t := by
    unfold J_n; simp only [pow_one]; exact h1
  have hIL2_eq : Real.sqrt (lam * t) ^ 3 * IL2 = J_n lam alpha gamma 2 t := by
    unfold J_n; exact h2
  have hsqrt_lamt_sq : Real.sqrt (lam * t) ^ 2 = lam * t := Real.sq_sqrt hlamt.le
  have hsqrt_lamt_split : Real.sqrt (lam * t) = Real.sqrt lam * Real.sqrt t :=
    Real.sqrt_mul hlam.le t
  have hZ_sub : Z = J_n lam alpha gamma 0 t / Real.sqrt (lam * t) := by
    rw [eq_div_iff hsqrt_lamt_ne, mul_comm]; exact hZ_eq
  have hIL1_sub : IL1 = J_n lam alpha gamma 1 t / (lam * t) := by
    rw [eq_div_iff hlamt.ne', mul_comm, ← hsqrt_lamt_sq]; exact hIL1_eq
  have hIL2_sub : IL2 = J_n lam alpha gamma 2 t /
      (lam * t * Real.sqrt (lam * t)) := by
    rw [eq_div_iff (mul_ne_zero hlamt.ne' hsqrt_lamt_ne), mul_comm,
        show (lam * t * Real.sqrt (lam * t) : ℝ) = Real.sqrt (lam * t) ^ 3 from by
          rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, hsqrt_lamt_sq]]
    exact hIL2_eq
  have hZ_ne : Z ≠ 0 := fun hZ => hJ0_ne (by rw [← hZ_eq, hZ, mul_zero])
  rw [hZ_sub, hIL1_sub, hIL2_sub, hsqrt_lamt_split]
  set sl : ℝ := Real.sqrt lam with hsl_def
  set st : ℝ := Real.sqrt t with hst_def
  have hsl2 : sl ^ 2 = lam := Real.sq_sqrt hlam.le
  have hst2 : st ^ 2 = t := Real.sq_sqrt ht.le
  have hsl_ne : sl ≠ 0 := hsqrt_lam_ne
  have hst_ne : st ≠ 0 := hsqrt_t_ne
  have hJ0_sq_ne : J_n lam alpha gamma 0 t ^ 2 ≠ 0 := pow_ne_zero 2 hJ0_ne
  rw [← hsl2, ← hst2]
  field_simp

/-! ## Explicit O(t⁻²) rate for the mean and self-covariance

GPT-5.5 Pro consultation (`gpt_responses/o2_strategy_check.md`) showed that the
upgrade from `Tendsto` to explicit `O(t⁻²)` rate does not require building a
full second-order `J_n` asymptotic. Instead:

- For self-covariance, the existing first-order `J_n` bounds suffice via
  `t·Cov[x,x] - 1/λ = (J_0(J_2-J_0) - J_1²) / (λ·J_0²)`.
- For the mean, an exact Stein/score identity
  `J_1 + (3A/√t)·J_2 + (4B/t)·J_3 = 0` gives the rate from the same
  first-order bounds.

The scalar Taylor-2 bound (`abs_exp_neg_sub_one_add_sub_half_sq_le`) in
`ScalarBound.lean` is now unused for these two theorems, but kept as a
general-purpose result for future strengthening.
-/

/-- `J_0(t)` eventually lives in `[√(2π)/2, 3√(2π)/2]` as `t → ∞`. Useful as
a denominator bound in the explicit-rate proofs. -/
private lemma J_0_eventually_bounded
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ T, 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      Real.sqrt (2 * Real.pi) / 2 ≤ J_n lam alpha gamma 0 t ∧
      J_n lam alpha gamma 0 t ≤ 3 * Real.sqrt (2 * Real.pi) / 2 := by
  have hJ0 := tendsto_J_0 hlam hgamma hdisc
  rw [Metric.tendsto_atTop] at hJ0
  set c := Real.sqrt (2 * Real.pi) with hc_def
  have hc_pos : 0 < c := sqrt_two_pi_pos
  obtain ⟨T, hT⟩ := hJ0 (c / 2) (by linarith)
  refine ⟨max 1 T, le_max_left _ _, ?_⟩
  intro t ht
  have ht_T : T ≤ t := le_trans (le_max_right _ _) ht
  have h := hT t ht_T
  rw [Real.dist_eq] at h
  have h_abs := abs_le.mp h.le
  refine ⟨by linarith [h_abs.1], by linarith [h_abs.2]⟩

/-- **Exact bridge** for the self-covariance: for `t > 0` and `J_0(t) ≠ 0`,
`t · Cov_t[x, x] = (J_2·J_0 - J_1²) / (λ·J_0²)`. -/
private lemma cov_self_J_form_exact
    {lam alpha gamma : ℝ} (hlam : 0 < lam)
    {t : ℝ} (ht : 0 < t)
    (hJ0_ne : J_n lam alpha gamma 0 t ≠ 0) :
    t * Laplace.gibbsCov
      (anharmonicPotential lam alpha gamma) t (fun x => x) (fun x => x) =
    (J_n lam alpha gamma 2 t * J_n lam alpha gamma 0 t -
      J_n lam alpha gamma 1 t ^ 2) /
    (lam * J_n lam alpha gamma 0 t ^ 2) := by
  have hlamt : 0 < lam * t := mul_pos hlam ht
  have hsqrt_lamt_pos : 0 < Real.sqrt (lam * t) := Real.sqrt_pos.mpr hlamt
  have hsqrt_lamt_ne : Real.sqrt (lam * t) ≠ 0 := hsqrt_lamt_pos.ne'
  have hsqrt_lam_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsqrt_lam_ne : Real.sqrt lam ≠ 0 := hsqrt_lam_pos.ne'
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_t_ne : Real.sqrt t ≠ 0 := hsqrt_t_pos.ne'
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have ht_ne : t ≠ 0 := ht.ne'
  rw [gibbsCov_x_x_eq_I_form]
  set Z := ∫ x : ℝ, Real.exp (-(t * anharmonicPotential lam alpha gamma x)) with hZ_def
  set IL1 := ∫ x : ℝ, x * Real.exp (-(t * anharmonicPotential lam alpha gamma x))
    with hIL1_def
  set IL2 := ∫ x : ℝ, x ^ 2 *
      Real.exp (-(t * anharmonicPotential lam alpha gamma x)) with hIL2_def
  have h0 := I_n_J_n_relation lam alpha gamma 0 hlam ht
  have h1 := I_n_J_n_relation lam alpha gamma 1 hlam ht
  have h2 := I_n_J_n_relation lam alpha gamma 2 hlam ht
  rw [pow_one] at h0
  rw [show (1 + 1 : ℕ) = 2 from rfl] at h1
  rw [show (2 + 1 : ℕ) = 3 from rfl] at h2
  simp only [pow_zero, one_mul] at h0
  simp only [pow_one] at h1
  have hZ_eq : Real.sqrt (lam * t) * Z = J_n lam alpha gamma 0 t := by
    unfold J_n; simp only [pow_zero, one_mul]; exact h0
  have hIL1_eq : Real.sqrt (lam * t) ^ 2 * IL1 = J_n lam alpha gamma 1 t := by
    unfold J_n; simp only [pow_one]; exact h1
  have hIL2_eq : Real.sqrt (lam * t) ^ 3 * IL2 = J_n lam alpha gamma 2 t := by
    unfold J_n; exact h2
  have hsqrt_lamt_sq : Real.sqrt (lam * t) ^ 2 = lam * t := Real.sq_sqrt hlamt.le
  have hsqrt_lamt_split : Real.sqrt (lam * t) = Real.sqrt lam * Real.sqrt t :=
    Real.sqrt_mul hlam.le t
  have hZ_sub : Z = J_n lam alpha gamma 0 t / Real.sqrt (lam * t) := by
    rw [eq_div_iff hsqrt_lamt_ne, mul_comm]; exact hZ_eq
  have hIL1_sub : IL1 = J_n lam alpha gamma 1 t / (lam * t) := by
    rw [eq_div_iff hlamt.ne', mul_comm, ← hsqrt_lamt_sq]; exact hIL1_eq
  have hIL2_sub : IL2 = J_n lam alpha gamma 2 t /
      (lam * t * Real.sqrt (lam * t)) := by
    rw [eq_div_iff (mul_ne_zero hlamt.ne' hsqrt_lamt_ne), mul_comm,
        show (lam * t * Real.sqrt (lam * t) : ℝ) = Real.sqrt (lam * t) ^ 3 from by
          rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, hsqrt_lamt_sq]]
    exact hIL2_eq
  have hZ_ne : Z ≠ 0 := fun hZ => hJ0_ne (by rw [← hZ_eq, hZ, mul_zero])
  rw [hZ_sub, hIL1_sub, hIL2_sub, hsqrt_lamt_split]
  set sl : ℝ := Real.sqrt lam with hsl_def
  set st : ℝ := Real.sqrt t with hst_def
  have hsl2 : sl ^ 2 = lam := Real.sq_sqrt hlam.le
  have hst2 : st ^ 2 = t := Real.sq_sqrt ht.le
  have hsl_ne : sl ≠ 0 := hsqrt_lam_ne
  have hst_ne : st ≠ 0 := hsqrt_t_ne
  have hJ0_sq_ne : J_n lam alpha gamma 0 t ^ 2 ≠ 0 := pow_ne_zero 2 hJ0_ne
  rw [← hsl2, ← hst2]
  field_simp

/-- For `t ≥ 1`, `K/t ≤ K/√t` (with `K ≥ 0`). -/
private lemma div_t_le_div_sqrt_t {K t : ℝ} (hK : 0 ≤ K) (ht : 1 ≤ t) :
    K / t ≤ K / Real.sqrt t := by
  have ht_pos : 0 < t := by linarith
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_ge_one : 1 ≤ Real.sqrt t := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt ht
  rcases eq_or_lt_of_le hK with heq | hpos
  · rw [← heq]; simp
  · rw [div_le_div_iff₀ ht_pos hsqrt_t_pos]
    have h_st_le_t : Real.sqrt t ≤ t :=
      calc Real.sqrt t = Real.sqrt t * 1 := by ring
        _ ≤ Real.sqrt t * Real.sqrt t := by
              exact mul_le_mul_of_nonneg_left hsqrt_ge_one hsqrt_t_pos.le
        _ = t := Real.mul_self_sqrt ht_pos.le
    nlinarith [hpos]

/-- `|J_1(t)| ≤ K/√t` for some `K ≥ 0`, for all `t ≥ 1`. -/
private lemma J_1_abs_bound
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |J_n lam alpha gamma 1 t| ≤ K / Real.sqrt t := by
  obtain ⟨K, hK_nn, hbound⟩ := J_1_asymptotic hlam hgamma hdisc
  refine ⟨K + 3 * |cubicScale lam alpha| * Real.sqrt (2 * Real.pi), by positivity, ?_⟩
  intro t ht1
  have ht_pos : 0 < t := by linarith
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_t_ne : Real.sqrt t ≠ 0 := hsqrt_t_pos.ne'
  set L : ℝ := -3 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) / Real.sqrt t with hL_def
  have h_J1_diff : |J_n lam alpha gamma 1 t - L| ≤ K / t := by
    rw [hL_def]; unfold J_n; exact hbound ht1
  have h_abs_L : |L| = 3 * |cubicScale lam alpha| * Real.sqrt (2 * Real.pi) / Real.sqrt t := by
    rw [hL_def, abs_div, abs_of_pos hsqrt_t_pos]
    have h_eq : -3 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) =
        -(3 * cubicScale lam alpha * Real.sqrt (2 * Real.pi)) := by ring
    rw [h_eq, abs_neg, abs_mul, abs_mul, abs_of_pos sqrt_two_pi_pos]
    have h3 : |(3 : ℝ)| = 3 := abs_of_pos (by norm_num)
    rw [h3]
  -- |J_1| ≤ |J_1 - L| + |L| ≤ K/t + 3|A|√(2π)/√t.
  have h_tri : |J_n lam alpha gamma 1 t| ≤ |J_n lam alpha gamma 1 t - L| + |L| := by
    have := abs_add_le (J_n lam alpha gamma 1 t - L) L
    rw [show (J_n lam alpha gamma 1 t - L) + L = J_n lam alpha gamma 1 t from by ring] at this
    exact this
  have hKt_le := div_t_le_div_sqrt_t hK_nn ht1
  calc |J_n lam alpha gamma 1 t|
      ≤ |J_n lam alpha gamma 1 t - L| + |L| := h_tri
    _ ≤ K / t + 3 * |cubicScale lam alpha| * Real.sqrt (2 * Real.pi) / Real.sqrt t := by
          rw [h_abs_L] at *; linarith
    _ ≤ K / Real.sqrt t + 3 * |cubicScale lam alpha| * Real.sqrt (2 * Real.pi) /
          Real.sqrt t := by linarith
    _ = (K + 3 * |cubicScale lam alpha| * Real.sqrt (2 * Real.pi)) / Real.sqrt t := by
          rw [← add_div]

/-- `|J_3(t)| ≤ K/√t` for some `K ≥ 0`, for all `t ≥ 1`. -/
private lemma J_3_abs_bound
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |J_n lam alpha gamma 3 t| ≤ K / Real.sqrt t := by
  obtain ⟨K, hK_nn, hbound⟩ := J_3_asymptotic hlam hgamma hdisc
  refine ⟨K + 15 * |cubicScale lam alpha| * Real.sqrt (2 * Real.pi), by positivity, ?_⟩
  intro t ht1
  have ht_pos : 0 < t := by linarith
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  set L : ℝ := -15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) / Real.sqrt t with hL_def
  have h_J3_diff : |J_n lam alpha gamma 3 t - L| ≤ K / t := by
    rw [hL_def]; unfold J_n; exact hbound ht1
  have h_abs_L : |L| =
      15 * |cubicScale lam alpha| * Real.sqrt (2 * Real.pi) / Real.sqrt t := by
    rw [hL_def, abs_div, abs_of_pos hsqrt_t_pos]
    have h_eq : -15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi) =
        -(15 * cubicScale lam alpha * Real.sqrt (2 * Real.pi)) := by ring
    rw [h_eq, abs_neg, abs_mul, abs_mul, abs_of_pos sqrt_two_pi_pos]
    have h15 : |(15 : ℝ)| = 15 := abs_of_pos (by norm_num)
    rw [h15]
  have h_tri : |J_n lam alpha gamma 3 t| ≤ |J_n lam alpha gamma 3 t - L| + |L| := by
    have := abs_add_le (J_n lam alpha gamma 3 t - L) L
    rw [show (J_n lam alpha gamma 3 t - L) + L = J_n lam alpha gamma 3 t from by ring] at this
    exact this
  have hKt_le := div_t_le_div_sqrt_t hK_nn ht1
  calc |J_n lam alpha gamma 3 t|
      ≤ |J_n lam alpha gamma 3 t - L| + |L| := h_tri
    _ ≤ K / t + 15 * |cubicScale lam alpha| * Real.sqrt (2 * Real.pi) / Real.sqrt t := by
          rw [h_abs_L] at *; linarith
    _ ≤ K / Real.sqrt t + 15 * |cubicScale lam alpha| * Real.sqrt (2 * Real.pi) /
          Real.sqrt t := by linarith
    _ = (K + 15 * |cubicScale lam alpha| * Real.sqrt (2 * Real.pi)) / Real.sqrt t := by
          rw [← add_div]

/-- `|J_2(t) - J_0(t)| ≤ K/t` for some `K ≥ 0`, for all `t ≥ 1`. Both have
the same leading constant `√(2π)` so the difference is `O(1/t)`. -/
private lemma J_2_sub_J_0_bound
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 1 ≤ t →
      |J_n lam alpha gamma 2 t - J_n lam alpha gamma 0 t| ≤ K / t := by
  obtain ⟨K_0, hK_0_nn, hbound_0⟩ := J_0_asymptotic hlam hgamma hdisc
  obtain ⟨K_2, hK_2_nn, hbound_2⟩ := J_2_asymptotic hlam hgamma hdisc
  refine ⟨K_0 + K_2, by linarith, ?_⟩
  intro t ht1
  have ht_pos : 0 < t := by linarith
  have h0 := hbound_0 ht1
  have h2 := hbound_2 ht1
  -- h0 : |J_0 t - √(2π)| ≤ K_0/t (after spelling J_n in u^0 form)
  -- h2 : |J_2 t - √(2π)| ≤ K_2/t (after spelling J_n in u^2 form)
  have h_J0 : |J_n lam alpha gamma 0 t - Real.sqrt (2 * Real.pi)| ≤ K_0 / t := by
    unfold J_n; exact h0
  have h_J2 : |J_n lam alpha gamma 2 t - Real.sqrt (2 * Real.pi)| ≤ K_2 / t := by
    unfold J_n; exact h2
  -- |J_2 - J_0| ≤ |J_2 - c| + |c - J_0| ≤ K_2/t + K_0/t.
  have h_decomp :
      J_n lam alpha gamma 2 t - J_n lam alpha gamma 0 t =
      (J_n lam alpha gamma 2 t - Real.sqrt (2 * Real.pi)) +
        -(J_n lam alpha gamma 0 t - Real.sqrt (2 * Real.pi)) := by ring
  rw [h_decomp]
  have h_tri := abs_add_le (J_n lam alpha gamma 2 t - Real.sqrt (2 * Real.pi))
      (-(J_n lam alpha gamma 0 t - Real.sqrt (2 * Real.pi)))
  rw [abs_neg] at h_tri
  calc _ ≤ |J_n lam alpha gamma 2 t - Real.sqrt (2 * Real.pi)|
          + |J_n lam alpha gamma 0 t - Real.sqrt (2 * Real.pi)| := h_tri
    _ ≤ K_2 / t + K_0 / t := by linarith
    _ = (K_0 + K_2) / t := by ring

/-- (b) **Self-covariance, explicit `O(t⁻²)` rate**:
`|t · Cov_t[x,x] - 1/λ| ≤ K/t` for some constant `K`, for all `t ≥ T`.

Equivalently `Cov_t[x,x] = 1/(λ t) + O(t⁻²)` as `t → ∞`. -/
theorem cov_self_anharmonic_O2_rate
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma) :
    ∃ K T : ℝ, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t : ℝ}, T ≤ t →
      |t * Laplace.gibbsCov
        (anharmonicPotential lam alpha gamma) t (fun x => x) (fun x => x) -
        1 / lam| ≤ K / t := by
  obtain ⟨T_J0, hT_J0_ge, hJ0_bd⟩ := J_0_eventually_bounded hlam hgamma hdisc
  obtain ⟨K_d, hK_d_nn, hbound_d⟩ := J_2_sub_J_0_bound hlam hgamma hdisc
  obtain ⟨K_1, hK_1_nn, hbound_1⟩ := J_1_abs_bound hlam hgamma hdisc
  set c := Real.sqrt (2 * Real.pi) with hc_def
  have hc_pos : 0 < c := sqrt_two_pi_pos
  have hc2_pos : 0 < c ^ 2 := by positivity
  have hlam_pos : 0 < lam := hlam
  have hlam_ne : lam ≠ 0 := hlam.ne'
  -- The constant. Bound on |numerator|/(λ·J_0²): use J_0 ∈ [c/2, 3c/2] and J_1 = O(1/√t).
  refine ⟨(3 * c * K_d / 2 + K_1 ^ 2) * 4 / (lam * c ^ 2), T_J0, ?_, hT_J0_ge, ?_⟩
  · positivity
  intro t ht
  have ht_pos : 0 < t := by linarith
  have ht1 : 1 ≤ t := le_trans hT_J0_ge ht
  obtain ⟨h_lo, h_hi⟩ := hJ0_bd ht
  -- J_0 t ≥ c/2 > 0, so J_0 t ≠ 0 and J_0 t² ≥ (c/2)² = c²/4.
  have hJ0_pos : 0 < J_n lam alpha gamma 0 t := by linarith
  have hJ0_ne : J_n lam alpha gamma 0 t ≠ 0 := hJ0_pos.ne'
  have hJ0_sq_lo : c ^ 2 / 4 ≤ J_n lam alpha gamma 0 t ^ 2 := by
    have h := mul_self_le_mul_self (by linarith : (0:ℝ) ≤ c / 2) h_lo
    nlinarith
  -- Bridge to J-form.
  rw [cov_self_J_form_exact hlam ht_pos hJ0_ne]
  -- Goal: |(J_2·J_0 - J_1²)/(λ·J_0²) - 1/λ| ≤ K/t.
  -- Rewrite as (J_0(J_2 - J_0) - J_1²)/(λ·J_0²).
  have hbridge :
      (J_n lam alpha gamma 2 t * J_n lam alpha gamma 0 t -
        J_n lam alpha gamma 1 t ^ 2) / (lam * J_n lam alpha gamma 0 t ^ 2) - 1 / lam =
      (J_n lam alpha gamma 0 t * (J_n lam alpha gamma 2 t - J_n lam alpha gamma 0 t)
        - J_n lam alpha gamma 1 t ^ 2) / (lam * J_n lam alpha gamma 0 t ^ 2) := by
    have hJ0_sq_ne : J_n lam alpha gamma 0 t ^ 2 ≠ 0 := pow_ne_zero 2 hJ0_ne
    field_simp
    ring
  rw [hbridge]
  -- Bound numerator and denominator separately.
  have h_d := hbound_d ht1
  have h_J1 := hbound_1 ht1
  have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  -- |J_1²| ≤ (K_1/√t)² = K_1²/t.
  have h_J1_sq : J_n lam alpha gamma 1 t ^ 2 ≤ K_1 ^ 2 / t := by
    have h_abs_sq : J_n lam alpha gamma 1 t ^ 2 = |J_n lam alpha gamma 1 t| ^ 2 := by
      rw [sq_abs]
    rw [h_abs_sq]
    have h_K_sq : (K_1 / Real.sqrt t) * (K_1 / Real.sqrt t) = K_1 ^ 2 / t := by
      rw [show (K_1 / Real.sqrt t) * (K_1 / Real.sqrt t) =
          K_1 ^ 2 / (Real.sqrt t) ^ 2 from by rw [div_mul_div_comm]; ring]
      rw [Real.sq_sqrt ht_pos.le]
    rw [show |J_n lam alpha gamma 1 t| ^ 2 = |J_n lam alpha gamma 1 t| *
        |J_n lam alpha gamma 1 t| from by ring, ← h_K_sq]
    exact mul_self_le_mul_self (abs_nonneg _) h_J1
  -- |numerator| ≤ |J_0|·|J_2 - J_0| + J_1² ≤ (3c/2)·K_d/t + K_1²/t.
  have h_num_bound :
      |J_n lam alpha gamma 0 t * (J_n lam alpha gamma 2 t - J_n lam alpha gamma 0 t)
        - J_n lam alpha gamma 1 t ^ 2| ≤
      (3 * c / 2) * (K_d / t) + K_1 ^ 2 / t := by
    set X := J_n lam alpha gamma 0 t * (J_n lam alpha gamma 2 t - J_n lam alpha gamma 0 t)
    set Y := J_n lam alpha gamma 1 t ^ 2
    have h_tri : |X - Y| ≤ |X| + |Y| := by
      have := abs_add_le X (-Y)
      rw [show X + (-Y) = X - Y from by ring] at this
      rw [abs_neg] at this
      exact this
    have h_abs_X : |X| ≤ (3 * c / 2) * (K_d / t) := by
      simp only [X, abs_mul, abs_of_pos hJ0_pos]
      exact mul_le_mul h_hi h_d (abs_nonneg _) (by linarith)
    have h_abs_Y : |Y| ≤ K_1 ^ 2 / t := by
      simp only [Y]
      rw [abs_of_nonneg (sq_nonneg _)]
      exact h_J1_sq
    linarith
  -- |denominator| ≥ λ·c²/4.
  have h_denom_lo : lam * c ^ 2 / 4 ≤ lam * J_n lam alpha gamma 0 t ^ 2 := by
    have := mul_le_mul_of_nonneg_left hJ0_sq_lo hlam_pos.le
    linarith
  have h_denom_pos : 0 < lam * J_n lam alpha gamma 0 t ^ 2 :=
    mul_pos hlam_pos (pow_pos hJ0_pos 2)
  -- Final calc.
  rw [abs_div, abs_of_pos h_denom_pos]
  have h_num_nn : 0 ≤ (3 * c / 2) * (K_d / t) + K_1 ^ 2 / t := by
    have h1 : 0 ≤ (3 * c / 2) * (K_d / t) :=
      mul_nonneg (by linarith) (div_nonneg hK_d_nn ht_pos.le)
    have h2 : 0 ≤ K_1 ^ 2 / t := div_nonneg (sq_nonneg _) ht_pos.le
    linarith
  have h_lc_pos : 0 < lam * c ^ 2 / 4 := by positivity
  calc |J_n lam alpha gamma 0 t * (J_n lam alpha gamma 2 t - J_n lam alpha gamma 0 t)
        - J_n lam alpha gamma 1 t ^ 2| / (lam * J_n lam alpha gamma 0 t ^ 2)
      ≤ ((3 * c / 2) * (K_d / t) + K_1 ^ 2 / t) /
          (lam * J_n lam alpha gamma 0 t ^ 2) :=
        div_le_div_of_nonneg_right h_num_bound (le_of_lt h_denom_pos)
    _ ≤ ((3 * c / 2) * (K_d / t) + K_1 ^ 2 / t) / (lam * c ^ 2 / 4) :=
        div_le_div_of_nonneg_left h_num_nn h_lc_pos h_denom_lo
    _ = (3 * c * K_d / 2 + K_1 ^ 2) * 4 / (lam * c ^ 2) / t := by
        field_simp

/-! ## Stein/score identity for the J_n integrals

The exact identity `J_1(t) + (3A/√t)·J_2(t) + (4B/t)·J_3(t) = 0` follows from
`0 = ∫_ℝ d/du(e^{-u²/2 - s_t(u)}) du` (boundary terms vanish by Gaussian decay).
-/

/-- The score function `S_t(u) = u + 3A·u²/√t + 4B·u³/t`. This is the
derivative of `u²/2 + s_t(u)` with respect to `u`. -/
private noncomputable def scoreFun (lam alpha gamma : ℝ) (t : ℝ) (u : ℝ) : ℝ :=
  u + 3 * cubicScale lam alpha * u ^ 2 / Real.sqrt t +
    4 * quarticScale lam gamma * u ^ 3 / t

/-- The integrand `f_t(u) = e^{-u²/2}·e^{-s_t(u)}` (matches the integrand of
`J_0` minus the `u^n` factor). -/
private noncomputable def fGauss (lam alpha gamma : ℝ) (t : ℝ) (u : ℝ) : ℝ :=
  Real.exp (-(u ^ 2) / 2) * Real.exp (-rescaledPerturbation lam alpha gamma t u)

/-- The derivative of `rescaledPerturbation` in `u`. -/
private lemma rescaledPerturbation_hasDerivAt
    (lam alpha gamma : ℝ) {t : ℝ} (ht : 0 < t) (u : ℝ) :
    HasDerivAt (fun u => rescaledPerturbation lam alpha gamma t u)
      (3 * cubicScale lam alpha * u ^ 2 / Real.sqrt t +
        4 * quarticScale lam gamma * u ^ 3 / t) u := by
  unfold rescaledPerturbation
  have hsqrt_t_ne : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have ht_ne : t ≠ 0 := ht.ne'
  have h_cube : HasDerivAt (fun u : ℝ => u ^ 3) (3 * u ^ 2) u := by
    have := (hasDerivAt_id u).pow 3
    simpa using this
  have h_quart : HasDerivAt (fun u : ℝ => u ^ 4) (4 * u ^ 3) u := by
    have := (hasDerivAt_id u).pow 4
    simpa using this
  have h_term1 : HasDerivAt
      (fun u => cubicScale lam alpha * u ^ 3 / Real.sqrt t)
      (3 * cubicScale lam alpha * u ^ 2 / Real.sqrt t) u := by
    have h1 := (h_cube.const_mul (cubicScale lam alpha)).div_const (Real.sqrt t)
    convert h1 using 1; ring
  have h_term2 : HasDerivAt
      (fun u => quarticScale lam gamma * u ^ 4 / t)
      (4 * quarticScale lam gamma * u ^ 3 / t) u := by
    have h2 := (h_quart.const_mul (quarticScale lam gamma)).div_const t
    convert h2 using 1; ring
  exact h_term1.add h_term2

/-- `f_t(u) = exp(-u²/2)·exp(-s_t(u))` has derivative `-S_t(u)·f_t(u)`. -/
private lemma fGauss_hasDerivAt
    (lam alpha gamma : ℝ) {t : ℝ} (ht : 0 < t) (u : ℝ) :
    HasDerivAt (fGauss lam alpha gamma t)
      (-(scoreFun lam alpha gamma t u) * fGauss lam alpha gamma t u) u := by
  unfold fGauss scoreFun
  have h_neg_half_sq : HasDerivAt (fun u : ℝ => -(u ^ 2) / 2) (-u) u := by
    have := (hasDerivAt_id u).pow 2
    have h1 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by simpa using this
    have h2 := h1.neg.div_const 2
    convert h2 using 1; ring
  have h_exp1 : HasDerivAt (fun u : ℝ => Real.exp (-(u ^ 2) / 2))
      (-u * Real.exp (-(u ^ 2) / 2)) u := by
    have := (Real.hasDerivAt_exp (-(u ^ 2) / 2)).comp u h_neg_half_sq
    convert this using 1; ring
  have h_neg_sp : HasDerivAt (fun u => -rescaledPerturbation lam alpha gamma t u)
      (-(3 * cubicScale lam alpha * u ^ 2 / Real.sqrt t +
        4 * quarticScale lam gamma * u ^ 3 / t)) u :=
    (rescaledPerturbation_hasDerivAt lam alpha gamma ht u).neg
  have h_exp2 : HasDerivAt (fun u : ℝ => Real.exp (-rescaledPerturbation lam alpha gamma t u))
      (-(3 * cubicScale lam alpha * u ^ 2 / Real.sqrt t +
        4 * quarticScale lam gamma * u ^ 3 / t) *
       Real.exp (-rescaledPerturbation lam alpha gamma t u)) u := by
    have := (Real.hasDerivAt_exp _).comp u h_neg_sp
    convert this using 1; ring
  have h_prod := h_exp1.mul h_exp2
  convert h_prod using 1; ring

/-- `exp(-c·u²) → 0` as `|u| → ∞` (for `c > 0`). Helper for `fGauss` decay. -/
private lemma exp_neg_const_mul_sq_tendsto_atTop_zero {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun u : ℝ => Real.exp (-(c * u ^ 2))) Filter.atTop (nhds 0) := by
  have h_sq : Filter.Tendsto (fun u : ℝ => u ^ 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have h_cmul : Filter.Tendsto (fun u : ℝ => c * u ^ 2) Filter.atTop Filter.atTop :=
    h_sq.const_mul_atTop hc
  have h_neg : Filter.Tendsto (fun u : ℝ => -(c * u ^ 2)) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp h_cmul
  exact Real.tendsto_exp_atBot.comp h_neg

private lemma exp_neg_const_mul_sq_tendsto_atBot_zero {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun u : ℝ => Real.exp (-(c * u ^ 2))) Filter.atBot (nhds 0) := by
  have h_neg_id : Filter.Tendsto (fun u : ℝ => -u) Filter.atBot Filter.atTop :=
    Filter.tendsto_neg_atBot_atTop
  have h_pow : Filter.Tendsto (fun u : ℝ => u ^ 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have h_sq : Filter.Tendsto (fun u : ℝ => u ^ 2) Filter.atBot Filter.atTop := by
    have h := h_pow.comp h_neg_id
    convert h using 1
    ext u; simp [Function.comp]
  have h_cmul : Filter.Tendsto (fun u : ℝ => c * u ^ 2) Filter.atBot Filter.atTop :=
    h_sq.const_mul_atTop hc
  have h_neg : Filter.Tendsto (fun u : ℝ => -(c * u ^ 2)) Filter.atBot Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp h_cmul
  exact Real.tendsto_exp_atBot.comp h_neg

/-- `f_t(u) → 0` as `u → ∞`. -/
private lemma fGauss_tendsto_atTop_zero
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
    {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fGauss lam alpha gamma t) Filter.atTop (nhds 0) := by
  obtain ⟨c₀, hc₀_pos, hbound⟩ := rescaled_boltzmann_decay hlam hgamma hdisc
  apply squeeze_zero (g := fun u => Real.exp (-(c₀ * u ^ 2))) _ _
    (exp_neg_const_mul_sq_tendsto_atTop_zero hc₀_pos)
  · intro u; unfold fGauss; positivity
  · intro u
    unfold fGauss
    rw [show Real.exp (-(u ^ 2) / 2) * Real.exp (-rescaledPerturbation lam alpha gamma t u) =
        Real.exp (-(u ^ 2 / 2 + rescaledPerturbation lam alpha gamma t u)) from by
        rw [← Real.exp_add]; congr 1; ring]
    exact hbound ht u

/-- `f_t(u) → 0` as `u → -∞`. -/
private lemma fGauss_tendsto_atBot_zero
    {lam alpha gamma : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma) (hdisc : alpha ^ 2 < 3 * lam * gamma)
    {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fGauss lam alpha gamma t) Filter.atBot (nhds 0) := by
  obtain ⟨c₀, hc₀_pos, hbound⟩ := rescaled_boltzmann_decay hlam hgamma hdisc
  apply squeeze_zero (g := fun u => Real.exp (-(c₀ * u ^ 2))) _ _
    (exp_neg_const_mul_sq_tendsto_atBot_zero hc₀_pos)
  · intro u; unfold fGauss; positivity
  · intro u
    unfold fGauss
    rw [show Real.exp (-(u ^ 2) / 2) * Real.exp (-rescaledPerturbation lam alpha gamma t u) =
        Real.exp (-(u ^ 2 / 2 + rescaledPerturbation lam alpha gamma t u)) from by
        rw [← Real.exp_add]; congr 1; ring]
    exact hbound ht u

end Laplace.OneD
