/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.MorseBottNormalForm

/-!
# Morse–Bott in adapted coordinates: leading-order identification with a transverse remainder

The exact normal form of `MorseBottNormalForm` is relaxed to
`L(x, y) = ½ xᵀ H(y) x + R(x, y)`, `|R(x, y)| ≤ C |x|³` on a transverse window `|x| ≤ δ`
(`MBGenData`), with a transverse cutoff `χ₁` supported in that window and equal to `1` at `0`,
and the tangential cutoff `χ₂` as before. The exact formulas of the normal form become `t → ∞`
limits: after the substitution `x = u/√t`,
`(√t)^{r+k} ∫ g(x) ψ(y) χ₁χ₂ e^{-tL} = ∫ ψ χ₂ ∫ g(u) χ₁(u/√t) e^{-½uᵀH(y)u - tR(u/√t, y)} du dy`
and the inner integrand is dominated by `|g(u)| e^{-c|u|²/4}` uniformly in `y` and `t` (the
remainder eats at most half the Gaussian decay on the window, since `Cδ ≤ c/4`), so two dominated
convergence theorems give (`tendsto_sqrt_pow_mul_integral`)
`(√t)^{r+k} ∫ g ψ χ₁χ₂ e^{-tL} → ∫ ψ χ₂ ∫ g(u) e^{-½uᵀH(y)u} du dy`.
Hence (`tendsto_mbgExp_tangential`, `tendsto_mul_mbgExp_transverse_second`)
`E_t[yᵛ] → ∫ yᵛ χ₂ ρ_H / ∫ χ₂ ρ_H` and `t E_t[xᵢxₖ yᵛ] → ∫ yᵛ χ₂ σ_H^{ik} / ∫ χ₂ ρ_H`:
the leading order of the tangential monomials is the normalised Morse–Bott density and the
leading order of the rescaled transverse second moments is the conditional covariance `H(y)⁻¹`,
whatever the remainder. **Identification** (`mbg_identification`): if two such losses have
eventually equal normalised expectations of all tangential monomials and all transverse second
moments, their Hessian fields agree on `{χ₂ ≠ 0}` (via `mb_identification_of_ratios`). This is the
parameter-uniform Gaussian leading order of Astra's plan, in adapted coordinates.
-/

open Real MeasureTheory Filter Topology
open scoped Matrix

namespace Laplace.Multi

variable {r n : ℕ}

/-! ### The model -/

/-- `L(x, y) = ½ xᵀ H(y) x + R(x, y)`. -/
noncomputable def mbgLoss (H : EuclidD n → Matrix (Fin r) (Fin r) ℝ)
    (R : EuclidD r → EuclidD n → ℝ) (z : EuclidD r × EuclidD n) : ℝ :=
  qform (H z.2) z.1 / 2 + R z.1 z.2

/-- The weight `χ₁(x) χ₂(y) e^{-tL}`. -/
noncomputable def mbgWeight (H : EuclidD n → Matrix (Fin r) (Fin r) ℝ)
    (R : EuclidD r → EuclidD n → ℝ) (χ₁ : EuclidD r → ℝ) (χ₂ : EuclidD n → ℝ) (t : ℝ)
    (z : EuclidD r × EuclidD n) : ℝ :=
  χ₁ z.1 * χ₂ z.2 * Real.exp (-(t * mbgLoss H R z))

/-- The normalised expectation. -/
noncomputable def mbgExp (H : EuclidD n → Matrix (Fin r) (Fin r) ℝ)
    (R : EuclidD r → EuclidD n → ℝ) (χ₁ : EuclidD r → ℝ) (χ₂ : EuclidD n → ℝ) (t : ℝ)
    (φ : EuclidD r × EuclidD n → ℝ) : ℝ :=
  (∫ z, φ z * mbgWeight H R χ₁ χ₂ t z) / ∫ z, mbgWeight H R χ₁ χ₂ t z

/-- Hypotheses: the normal-form data for `(H, χ₂)`, a jointly continuous remainder bounded by
`C|x|³` on the window `|x| ≤ δ` with `Cδ ≤ c/4`, and a continuous transverse cutoff `χ₁` with
`|χ₁| ≤ 1`, `χ₁(0) = 1`, supported in the window. -/
structure MBGenData (H : EuclidD n → Matrix (Fin r) (Fin r) ℝ) (R : EuclidD r → EuclidD n → ℝ)
    (χ₁ : EuclidD r → ℝ) (χ₂ : EuclidD n → ℝ) (c C δ : ℝ) : Prop where
  base : MBData H χ₂ c
  R_cont : Continuous fun z : EuclidD r × EuclidD n ↦ R z.1 z.2
  R_bound : ∀ x y, ‖x‖ ≤ δ → |R x y| ≤ C * ‖x‖ ^ 3
  C_nonneg : 0 ≤ C
  δ_pos : 0 < δ
  Cδ : C * δ ≤ c / 4
  χ₁_cont : Continuous χ₁
  χ₁_supp : ∀ x, δ < ‖x‖ → χ₁ x = 0
  χ₁_zero : χ₁ 0 = 1
  χ₁_le : ∀ x, |χ₁ x| ≤ 1

/-- The rescaled inner integrand and integral: `∫ g(u) χ₁(u/√t) e^{-½uᵀH(y)u - tR(u/√t, y)} du`. -/
noncomputable def innerScaled (H : EuclidD n → Matrix (Fin r) (Fin r) ℝ)
    (R : EuclidD r → EuclidD n → ℝ) (χ₁ : EuclidD r → ℝ) (g : EuclidD r → ℝ) (t : ℝ)
    (y : EuclidD n) : ℝ :=
  ∫ u : EuclidD r, g u * χ₁ ((Real.sqrt t)⁻¹ • u) *
    Real.exp (-(qform (H y) u / 2 + t * R ((Real.sqrt t)⁻¹ • u) y))

/-! ### The uniform domination -/

theorem sqrt_inv_sq {t : ℝ} (ht : 0 < t) : ((Real.sqrt t)⁻¹) ^ 2 = t⁻¹ := by
  rw [inv_pow, Real.sq_sqrt ht.le]

/-- On the window, `|tR(u/√t, y)| ≤ (c/4)|u|²`; off the window the cutoff vanishes. -/
theorem abs_cutoff_mul_exp_le {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {t : ℝ} (ht : 0 < t) (u : EuclidD r) (y : EuclidD n) :
    |χ₁ ((Real.sqrt t)⁻¹ • u) *
      Real.exp (-(qform (H y) u / 2 + t * R ((Real.sqrt t)⁻¹ • u) y))| ≤
      Real.exp (-(c / 4) * ‖u‖ ^ 2) := by
  set q : ℝ := (Real.sqrt t)⁻¹ with hq
  have hqpos : 0 < q := inv_pos.mpr (Real.sqrt_pos.mpr ht)
  have hq2 : t * q ^ 2 = 1 := by
    rw [hq, sqrt_inv_sq ht, mul_inv_cancel₀ ht.ne']
  have hnorm : ‖q • u‖ = q * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hqpos]
  by_cases hwin : ‖q • u‖ ≤ δ
  · have hR := h.R_bound (q • u) y hwin
    have hell := h.base.ellip y u
    have hc := h.base.c_pos
    -- `t |R| ≤ C q |u|³ = C (q|u|) |u|² ≤ C δ |u|² ≤ (c/4)|u|²`
    have hRt : t * |R (q • u) y| ≤ c / 4 * ‖u‖ ^ 2 := by
      calc t * |R (q • u) y| ≤ t * (C * ‖q • u‖ ^ 3) := by gcongr
        _ = C * (q * ‖u‖) * ‖u‖ ^ 2 * (t * q ^ 2) := by rw [hnorm]; ring
        _ = C * (q * ‖u‖) * ‖u‖ ^ 2 := by rw [hq2, mul_one]
        _ ≤ C * δ * ‖u‖ ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by rwa [← hnorm]) h.C_nonneg) (by positivity)
        _ ≤ c / 4 * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right h.Cδ (by positivity)
    have hexp : Real.exp (-(qform (H y) u / 2 + t * R (q • u) y)) ≤
        Real.exp (-(c / 4) * ‖u‖ ^ 2) := by
      apply Real.exp_le_exp.mpr
      have h1 : -(t * |R (q • u) y|) ≤ t * R (q • u) y := by
        have := neg_abs_le (R (q • u) y)
        nlinarith
      nlinarith
    calc |χ₁ (q • u) * Real.exp (-(qform (H y) u / 2 + t * R (q • u) y))|
        = |χ₁ (q • u)| * Real.exp (-(qform (H y) u / 2 + t * R (q • u) y)) := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ 1 * Real.exp (-(c / 4) * ‖u‖ ^ 2) :=
          mul_le_mul (h.χ₁_le _) hexp (Real.exp_pos _).le zero_le_one
      _ = Real.exp (-(c / 4) * ‖u‖ ^ 2) := one_mul _
  · push Not at hwin
    rw [h.χ₁_supp _ hwin, zero_mul, abs_zero]
    exact (Real.exp_pos _).le

/-! ### Pointwise convergence -/

theorem tendsto_sqrt_atTop' : Tendsto Real.sqrt atTop atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun b ↦ ⟨b ^ 2, fun t ht ↦ ?_⟩
  calc b ≤ |b| := le_abs_self b
    _ = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
    _ ≤ Real.sqrt t := Real.sqrt_le_sqrt ht

theorem tendsto_sqrt_inv : Tendsto (fun t : ℝ ↦ (Real.sqrt t)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop'

theorem tendsto_cutoff_scaled {χ₁ : EuclidD r → ℝ} (hc : Continuous χ₁) (h0 : χ₁ 0 = 1)
    (u : EuclidD r) : Tendsto (fun t : ℝ ↦ χ₁ ((Real.sqrt t)⁻¹ • u)) atTop (𝓝 1) := by
  have h' : Tendsto (fun t : ℝ ↦ (Real.sqrt t)⁻¹ • u) atTop (𝓝 0) := by
    simpa using tendsto_sqrt_inv.smul_const u
  have h := (hc.tendsto 0).comp h'
  rw [h0] at h
  exact h

theorem tendsto_mul_remainder_scaled {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) (u : EuclidD r) (y : EuclidD n) :
    Tendsto (fun t : ℝ ↦ t * R ((Real.sqrt t)⁻¹ • u) y) atTop (𝓝 0) := by
  have hδ := h.δ_pos
  have hbound : Tendsto (fun t : ℝ ↦ C * ‖u‖ ^ 3 * (Real.sqrt t)⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_sqrt_inv.const_mul (C * ‖u‖ ^ 3)
  refine squeeze_zero_norm' ?_ hbound
  have hsmall : ∀ᶠ t : ℝ in atTop, (Real.sqrt t)⁻¹ < δ / (‖u‖ + 1) :=
    tendsto_sqrt_inv (Iio_mem_nhds (by positivity))
  filter_upwards [hsmall, eventually_gt_atTop 0] with t hlt ht
  set q : ℝ := (Real.sqrt t)⁻¹ with hq
  have hqpos : 0 < q := inv_pos.mpr (Real.sqrt_pos.mpr ht)
  have hq2 : t * q ^ 2 = 1 := by
    rw [hq, sqrt_inv_sq ht, mul_inv_cancel₀ ht.ne']
  have hnorm : ‖q • u‖ = q * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hqpos]
  have hwin : ‖q • u‖ ≤ δ := by
    rw [hnorm]
    have h1 : q * (‖u‖ + 1) < δ := by
      rwa [lt_div_iff₀ (by positivity)] at hlt
    nlinarith [norm_nonneg u]
  have hR := h.R_bound (q • u) y hwin
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos ht]
  calc t * |R (q • u) y| ≤ t * (C * ‖q • u‖ ^ 3) := by gcongr
    _ = C * ‖u‖ ^ 3 * q * (t * q ^ 2) := by rw [hnorm]; ring
    _ = C * ‖u‖ ^ 3 * q := by rw [hq2, mul_one]

theorem tendsto_scaled_integrand {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) (g : EuclidD r → ℝ) (u : EuclidD r) (y : EuclidD n) :
    Tendsto (fun t : ℝ ↦ g u * χ₁ ((Real.sqrt t)⁻¹ • u) *
        Real.exp (-(qform (H y) u / 2 + t * R ((Real.sqrt t)⁻¹ • u) y))) atTop
      (𝓝 (g u * quadKernel (H y) u)) := by
  have h1 := tendsto_cutoff_scaled h.χ₁_cont h.χ₁_zero u
  have h2 : Tendsto (fun t : ℝ ↦ Real.exp (-(qform (H y) u / 2 + t * R ((Real.sqrt t)⁻¹ • u) y)))
      atTop (𝓝 (Real.exp (-(qform (H y) u / 2 + 0)))) :=
    (Real.continuous_exp.tendsto _).comp
      ((tendsto_const_nhds.add (tendsto_mul_remainder_scaled h u y)).neg)
  have h3 := (tendsto_const_nhds (x := g u)).mul h1 |>.mul h2
  rw [mul_one, add_zero] at h3
  unfold quadKernel
  rw [neg_div]
  exact h3

/-! ### The inner limit -/

theorem continuous_scaled_integrand_u {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {g : EuclidD r → ℝ} (hg : Continuous g) (t : ℝ)
    (y : EuclidD n) :
    Continuous fun u : EuclidD r ↦ g u * χ₁ ((Real.sqrt t)⁻¹ • u) *
      Real.exp (-(qform (H y) u / 2 + t * R ((Real.sqrt t)⁻¹ • u) y)) := by
  have hR : Continuous fun u : EuclidD r ↦ R ((Real.sqrt t)⁻¹ • u) y := by
    have := h.R_cont.comp (show Continuous (fun u : EuclidD r ↦ ((Real.sqrt t)⁻¹ • u, y)) by
      fun_prop)
    exact this
  have hχ : Continuous fun u : EuclidD r ↦ χ₁ ((Real.sqrt t)⁻¹ • u) :=
    h.χ₁_cont.comp (continuous_const_smul _)
  have hexp : Continuous fun u : EuclidD r ↦
      Real.exp (-(qform (H y) u / 2 + t * R ((Real.sqrt t)⁻¹ • u) y)) :=
    Real.continuous_exp.comp
      ((((qform_continuous (H y)).div_const 2).add (continuous_const.mul hR)).neg)
  exact (hg.mul hχ).mul hexp

theorem continuous_scaled_integrand_y {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) (g : EuclidD r → ℝ) (t : ℝ) (u : EuclidD r) :
    Continuous fun y : EuclidD n ↦ g u * χ₁ ((Real.sqrt t)⁻¹ • u) *
      Real.exp (-(qform (H y) u / 2 + t * R ((Real.sqrt t)⁻¹ • u) y)) := by
  have hR : Continuous fun y : EuclidD n ↦ R ((Real.sqrt t)⁻¹ • u) y := by
    have := h.R_cont.comp (show Continuous (fun y : EuclidD n ↦ ((Real.sqrt t)⁻¹ • u, y)) by
      fun_prop)
    exact this
  have hq := continuous_qform_in_matrix h.base.cont u
  fun_prop

/-- The dominating function `Cg |u|^k e^{-c|u|²/4}` is integrable. -/
theorem integrable_bound {c Cg : ℝ} (hc : 0 < c) (k : ℕ) :
    Integrable fun u : EuclidD r ↦ Cg * ‖u‖ ^ k * Real.exp (-(c / 4) * ‖u‖ ^ 2) := by
  have := (integrable_pow_mul_exp_neg_mul_sq (d := r) (by positivity : (0 : ℝ) < c / 4) k).const_mul
    Cg
  simpa [mul_assoc] using this

theorem abs_scaled_integrand_le {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {g : EuclidD r → ℝ} {Cg : ℝ} {k : ℕ}
    (hgb : ∀ u, |g u| ≤ Cg * ‖u‖ ^ k) {t : ℝ} (ht : 0 < t) (u : EuclidD r) (y : EuclidD n) :
    |g u * χ₁ ((Real.sqrt t)⁻¹ • u) *
      Real.exp (-(qform (H y) u / 2 + t * R ((Real.sqrt t)⁻¹ • u) y))| ≤
      Cg * ‖u‖ ^ k * Real.exp (-(c / 4) * ‖u‖ ^ 2) := by
  rw [mul_assoc, abs_mul]
  exact mul_le_mul (hgb u) (abs_cutoff_mul_exp_le h ht u y) (abs_nonneg _)
    ((abs_nonneg _).trans (hgb u))

/-- **Inner dominated convergence**: `innerScaled g t y → ∫ g(u) K_{H(y)}(u) du`. -/
theorem tendsto_innerScaled {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {g : EuclidD r → ℝ} (hg : Continuous g) {Cg : ℝ} {k : ℕ}
    (hgb : ∀ u, |g u| ≤ Cg * ‖u‖ ^ k) (y : EuclidD n) :
    Tendsto (fun t ↦ innerScaled H R χ₁ g t y) atTop
      (𝓝 (∫ u : EuclidD r, g u * quadKernel (H y) u)) := by
  unfold innerScaled
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u ↦ Cg * ‖u‖ ^ k * Real.exp (-(c / 4) * ‖u‖ ^ 2))
    (Filter.Eventually.of_forall fun t ↦
      (continuous_scaled_integrand_u h hg t y).aestronglyMeasurable)
    ?_ (integrable_bound h.base.c_pos k)
    (Filter.Eventually.of_forall fun u ↦ tendsto_scaled_integrand h g u y)
  filter_upwards [eventually_gt_atTop 0] with t ht
  exact Filter.Eventually.of_forall fun u ↦ by
    rw [Real.norm_eq_abs]
    exact abs_scaled_integrand_le h hgb ht u y

theorem continuous_innerScaled {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {g : EuclidD r → ℝ} (hg : Continuous g) {Cg : ℝ} {k : ℕ}
    (hgb : ∀ u, |g u| ≤ Cg * ‖u‖ ^ k) {t : ℝ} (ht : 0 < t) :
    Continuous (innerScaled H R χ₁ g t) := by
  unfold innerScaled
  refine continuous_of_dominated (bound := fun u ↦ Cg * ‖u‖ ^ k * Real.exp (-(c / 4) * ‖u‖ ^ 2))
    (fun y ↦ (continuous_scaled_integrand_u h hg t y).aestronglyMeasurable) (fun y ↦ ?_)
    (integrable_bound h.base.c_pos k)
    (Filter.Eventually.of_forall fun u ↦ continuous_scaled_integrand_y h g t u)
  exact Filter.Eventually.of_forall fun u ↦ by
    rw [Real.norm_eq_abs]
    exact abs_scaled_integrand_le h hgb ht u y

theorem abs_innerScaled_le {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {g : EuclidD r → ℝ} {Cg : ℝ} {k : ℕ}
    (hgb : ∀ u, |g u| ≤ Cg * ‖u‖ ^ k) {t : ℝ} (ht : 0 < t) (y : EuclidD n) :
    |innerScaled H R χ₁ g t y| ≤
      ∫ u : EuclidD r, Cg * ‖u‖ ^ k * Real.exp (-(c / 4) * ‖u‖ ^ 2) := by
  unfold innerScaled
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le (integrable_bound h.base.c_pos k)
    (Filter.Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs]
      exact abs_scaled_integrand_le h hgb ht u y)

/-! ### The dilation identity and Fubini -/

/-- `(√t)^{r+k} ∫ g χ₁ e^{-tL(·, y)} = innerScaled g t y` for `g` homogeneous of degree `k`. -/
theorem sqrt_pow_mul_integral_eq_innerScaled {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {g : EuclidD r → ℝ} {k : ℕ}
    (hgh : ∀ (a : ℝ) (u : EuclidD r), g (a • u) = a ^ k * g u) {t : ℝ} (ht : 0 < t)
    (y : EuclidD n) :
    Real.sqrt t ^ (r + k) *
      ∫ x : EuclidD r, g x * χ₁ x * Real.exp (-(t * (qform (H y) x / 2 + R x y))) =
      innerScaled H R χ₁ g t y := by
  set q : ℝ := (Real.sqrt t)⁻¹ with hq
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hqpos : 0 < q := inv_pos.mpr hst
  have hq2 : t * q ^ 2 = 1 := by
    rw [hq, sqrt_inv_sq ht, mul_inv_cancel₀ ht.ne']
  have hdil := integral_dilation (d := r)
    (fun x ↦ g x * χ₁ x * Real.exp (-(t * (qform (H y) x / 2 + R x y)))) hqpos
  rw [hdil]
  unfold innerScaled
  have hpt : ∀ u : EuclidD r,
      g (q • u) * χ₁ (q • u) * Real.exp (-(t * (qform (H y) (q • u) / 2 + R (q • u) y))) =
        q ^ k * (g u * χ₁ (q • u) * Real.exp (-(qform (H y) u / 2 + t * R (q • u) y))) := by
    intro u
    rw [hgh, qform_smul]
    have : t * (q ^ 2 * qform (H y) u / 2 + R (q • u) y) =
        qform (H y) u / 2 + t * R (q • u) y := by
      have : t * q ^ 2 * qform (H y) u = qform (H y) u := by rw [hq2, one_mul]
      linear_combination (1 / 2 : ℝ) * this
    rw [this]
    ring
  simp only [hpt]
  rw [integral_const_mul, ← hq]
  have hone : Real.sqrt t ^ (r + k) * (q ^ r * q ^ k) = 1 := by
    rw [← pow_add, ← mul_pow, hq, mul_inv_cancel₀ hst.ne', one_pow]
  set I := ∫ u : EuclidD r, g u * χ₁ (q • u) * Real.exp (-(qform (H y) u / 2 + t * R (q • u) y))
    with hI
  calc Real.sqrt t ^ (r + k) * (q ^ r * (q ^ k * I))
      = Real.sqrt t ^ (r + k) * (q ^ r * q ^ k) * I := by ring
    _ = I := by rw [hone, one_mul]

/-- Joint continuity of the integrand. -/
theorem continuous_mbg_integrand {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {g : EuclidD r → ℝ} (hg : Continuous g)
    {ψ : EuclidD n → ℝ} (hψ : Continuous ψ) (t : ℝ) :
    Continuous fun z : EuclidD r × EuclidD n ↦ g z.1 * ψ z.2 * mbgWeight H R χ₁ χ₂ t z := by
  unfold mbgWeight mbgLoss
  exact ((hg.comp continuous_fst).mul (hψ.comp continuous_snd)).mul
    (((h.χ₁_cont.comp continuous_fst).mul (h.base.χ_cont.comp continuous_snd)).mul
      (Real.continuous_exp.comp (continuous_const.mul
        (((continuous_qform_param h.base.cont).div_const 2).add h.R_cont)).neg))

/-- The weight has compact support: `closedBall 0 δ ×ˢ tsupport χ₂`. -/
theorem hasCompactSupport_mbg_integrand {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) (g : EuclidD r → ℝ) (ψ : EuclidD n → ℝ) (t : ℝ) :
    HasCompactSupport fun z : EuclidD r × EuclidD n ↦ g z.1 * ψ z.2 * mbgWeight H R χ₁ χ₂ t z := by
  have hK : IsCompact ((Metric.closedBall (0 : EuclidD r) δ) ×ˢ tsupport χ₂) :=
    (isCompact_closedBall _ _).prod h.base.χ_supp
  refine IsCompact.of_isClosed_subset hK (isClosed_tsupport _) ?_
  refine closure_minimal ?_ (Metric.isClosed_closedBall.prod (isClosed_tsupport _))
  intro z hz
  rw [Function.mem_support] at hz
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hcon
    push Not at hcon
    apply hz
    simp [mbgWeight, h.χ₁_supp _ hcon]
  · by_contra hcon
    apply hz
    simp [mbgWeight, image_eq_zero_of_notMem_tsupport hcon]

theorem integrable_mbg_integrand {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {g : EuclidD r → ℝ} (hg : Continuous g)
    {ψ : EuclidD n → ℝ} (hψ : Continuous ψ) (t : ℝ) :
    Integrable fun z : EuclidD r × EuclidD n ↦ g z.1 * ψ z.2 * mbgWeight H R χ₁ χ₂ t z :=
  (continuous_mbg_integrand h hg hψ t).integrable_of_hasCompactSupport
    (hasCompactSupport_mbg_integrand h g ψ t)

/-- Fubini: the transverse integral first. -/
theorem integral_mbg_eq {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {g : EuclidD r → ℝ} (hg : Continuous g)
    {ψ : EuclidD n → ℝ} (hψ : Continuous ψ) (t : ℝ) :
    ∫ z : EuclidD r × EuclidD n, g z.1 * ψ z.2 * mbgWeight H R χ₁ χ₂ t z =
      ∫ y, ψ y * χ₂ y *
        ∫ x : EuclidD r, g x * χ₁ x * Real.exp (-(t * (qform (H y) x / 2 + R x y))) := by
  have hi := integrable_mbg_integrand h hg hψ t
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod_symm _ hi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [mbgWeight, mbgLoss]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only
  ring

/-! ### The leading-order limit -/

/-- **Parameter-uniform Gaussian leading order**:
`(√t)^{r+k} ∫ g ψ χ₁χ₂ e^{-tL} → ∫ ψ χ₂ ∫ g K_{H(y)}`. -/
theorem tendsto_sqrt_pow_mul_integral {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {g : EuclidD r → ℝ} (hg : Continuous g) {Cg : ℝ} {k : ℕ}
    (hgb : ∀ u, |g u| ≤ Cg * ‖u‖ ^ k) (hgh : ∀ (a : ℝ) (u : EuclidD r), g (a • u) = a ^ k * g u)
    {ψ : EuclidD n → ℝ} (hψ : Continuous ψ) :
    Tendsto (fun t ↦ Real.sqrt t ^ (r + k) *
        ∫ z : EuclidD r × EuclidD n, g z.1 * ψ z.2 * mbgWeight H R χ₁ χ₂ t z) atTop
      (𝓝 (∫ y, ψ y * χ₂ y * ∫ u : EuclidD r, g u * quadKernel (H y) u)) := by
  -- rewrite as the outer integral of the inner scaled integral
  have hrew : ∀ᶠ t : ℝ in atTop, Real.sqrt t ^ (r + k) *
      (∫ z : EuclidD r × EuclidD n, g z.1 * ψ z.2 * mbgWeight H R χ₁ χ₂ t z) =
      ∫ y, ψ y * χ₂ y * innerScaled H R χ₁ g t y := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [integral_mbg_eq h hg hψ t, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only
    rw [← sqrt_pow_mul_integral_eq_innerScaled hgh ht y]
    ring
  refine Tendsto.congr' (hrew.mono fun t ht ↦ ht.symm) ?_
  set M : ℝ := ∫ u : EuclidD r, Cg * ‖u‖ ^ k * Real.exp (-(c / 4) * ‖u‖ ^ 2) with hM
  have hψχ : Integrable fun y ↦ |ψ y * χ₂ y| * M :=
    (((hψ.mul h.base.χ_cont).integrable_of_hasCompactSupport h.base.χ_supp.mul_left).abs).mul_const
      M
  refine tendsto_integral_filter_of_dominated_convergence (fun y ↦ |ψ y * χ₂ y| * M) ?_ ?_ hψχ
    (Filter.Eventually.of_forall fun y ↦ ?_)
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact ((hψ.mul h.base.χ_cont).mul (continuous_innerScaled h hg hgb ht)).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop 0] with t ht
    refine Filter.Eventually.of_forall fun y ↦ ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_innerScaled_le h hgb ht y) (abs_nonneg _)
  · exact tendsto_const_nhds.mul (tendsto_innerScaled h hg hgb y)

/-! ### The leading order of the normalised expectations -/

theorem one_hom (a : ℝ) (u : EuclidD r) : (fun _ : EuclidD r ↦ (1 : ℝ)) (a • u) =
    a ^ 0 * (fun _ : EuclidD r ↦ (1 : ℝ)) u := by simp

theorem coord_mul_coord_hom (i k : Fin r) (a : ℝ) (u : EuclidD r) :
    (fun x : EuclidD r ↦ x i * x k) (a • u) = a ^ 2 * (fun x : EuclidD r ↦ x i * x k) u := by
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

/-- The partition function: `(√t)^r Z_t → ∫ χ₂ ρ_H`. -/
theorem tendsto_sqrt_pow_mul_partition {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) :
    Tendsto (fun t ↦ Real.sqrt t ^ r * ∫ z, mbgWeight H R χ₁ χ₂ t z) atTop
      (𝓝 (∫ y, χ₂ y * mbDensity H y)) := by
  have := tendsto_sqrt_pow_mul_integral h (g := fun _ ↦ (1 : ℝ)) continuous_const (Cg := 1)
    (k := 0) abs_one_le one_hom (ψ := fun _ ↦ (1 : ℝ)) continuous_const
  simpa [mbDensity] using this

/-- **Leading order of the tangential monomials**: `E_t[yᵛ] → ∫ yᵛ χ₂ ρ_H / ∫ χ₂ ρ_H`. -/
theorem tendsto_mbgExp_tangential {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {y₀ : EuclidD n} (hy₀ : χ₂ y₀ ≠ 0) {q : ℕ}
    (w : Fin q → Fin n) :
    Tendsto (fun t ↦ mbgExp H R χ₁ χ₂ t (fun z ↦ monomialTest w z.2)) atTop
      (𝓝 ((∫ y, monomialTest w y * (χ₂ y * mbDensity H y)) / ∫ y, χ₂ y * mbDensity H y)) := by
  have hnum := tendsto_sqrt_pow_mul_integral h (g := fun _ ↦ (1 : ℝ)) continuous_const (Cg := 1)
    (k := 0) abs_one_le one_hom (monomialTest_continuous w)
  have hden := tendsto_sqrt_pow_mul_partition h
  have hA : (∫ y, χ₂ y * mbDensity H y) ≠ 0 :=
    (integral_cutoff_mul_mbDensity_pos h.base hy₀).ne'
  simp only [add_zero, one_mul] at hnum
  have hlim := hnum.div hden hA
  have heq : (∫ y, monomialTest w y * χ₂ y * ∫ u : EuclidD r, quadKernel (H y) u) =
      ∫ y, monomialTest w y * (χ₂ y * mbDensity H y) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [mbDensity]
    ring
  rw [heq] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hne : Real.sqrt t ^ r ≠ 0 := pow_ne_zero _ (Real.sqrt_pos.mpr ht).ne'
  simp only [mbgExp, Pi.div_apply]
  rw [mul_div_mul_left _ _ hne]

/-- **Leading order of the rescaled transverse second moments**:
`t E_t[xᵢ xₖ yᵛ] → ∫ yᵛ χ₂ σ_H^{ik} / ∫ χ₂ ρ_H`, i.e. the conditional covariance `H(y)⁻¹`. -/
theorem tendsto_mul_mbgExp_transverse_second {H : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ} {c C δ : ℝ}
    (h : MBGenData H R χ₁ χ₂ c C δ) {y₀ : EuclidD n} (hy₀ : χ₂ y₀ ≠ 0) (i k : Fin r) {q : ℕ}
    (w : Fin q → Fin n) :
    Tendsto (fun t ↦ t * mbgExp H R χ₁ χ₂ t (fun z ↦ z.1 i * z.1 k * monomialTest w z.2)) atTop
      (𝓝 ((∫ y, monomialTest w y * (χ₂ y * mbSecond H i k y)) / ∫ y, χ₂ y * mbDensity H y)) := by
  have hnum := tendsto_sqrt_pow_mul_integral h (g := fun x : EuclidD r ↦ x i * x k)
    (((continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin r ↦ ℝ))).mul
      ((continuous_apply k).comp (PiLp.continuous_ofLp 2 (fun _ : Fin r ↦ ℝ)))) (Cg := 1)
    (k := 2) (abs_coord_mul_coord_le i k) (coord_mul_coord_hom i k) (monomialTest_continuous w)
  have hden := tendsto_sqrt_pow_mul_partition h
  have hA : (∫ y, χ₂ y * mbDensity H y) ≠ 0 :=
    (integral_cutoff_mul_mbDensity_pos h.base hy₀).ne'
  have hlim := hnum.div hden hA
  have heq : (∫ y, monomialTest w y * χ₂ y * ∫ u : EuclidD r, u i * u k * quadKernel (H y) u) =
      ∫ y, monomialTest w y * (χ₂ y * mbSecond H i k y) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [mbSecond]
    ring
  rw [heq] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hne : Real.sqrt t ^ r ≠ 0 := pow_ne_zero _ (Real.sqrt_pos.mpr ht).ne'
  simp only [mbgExp, Pi.div_apply]
  rw [pow_add, Real.sq_sqrt ht.le, mul_assoc, mul_div_mul_left _ _ hne, mul_div_assoc]

/-- **Leading-order identification of the transverse Hessian field.** If two Morse–Bott losses
in adapted coordinates (with arbitrary `O(|x|³)` transverse remainders) have eventually equal
normalised expectations of all tangential monomials and of all transverse second moments, then
their Hessian fields agree wherever the tangential cutoff is nonzero. -/
theorem mbg_identification {H₁ H₂ : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R₁ R₂ : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ}
    {c₁ C₁ δ₁ c₂ C₂ δ₂ : ℝ} (h₁ : MBGenData H₁ R₁ χ₁ χ₂ c₁ C₁ δ₁)
    (h₂ : MBGenData H₂ R₂ χ₁ χ₂ c₂ C₂ δ₂) {y₀ : EuclidD n} (hy₀ : χ₂ y₀ ≠ 0)
    (hT : ∀ (q : ℕ) (w : Fin q → Fin n), ∀ᶠ t in atTop,
      mbgExp H₁ R₁ χ₁ χ₂ t (fun z ↦ monomialTest w z.2) =
        mbgExp H₂ R₂ χ₁ χ₂ t (fun z ↦ monomialTest w z.2))
    (hN : ∀ (i k : Fin r) (q : ℕ) (w : Fin q → Fin n), ∀ᶠ t in atTop,
      mbgExp H₁ R₁ χ₁ χ₂ t (fun z ↦ z.1 i * z.1 k * monomialTest w z.2) =
        mbgExp H₂ R₂ χ₁ χ₂ t (fun z ↦ z.1 i * z.1 k * monomialTest w z.2)) :
    ∀ y, χ₂ y ≠ 0 → H₁ y = H₂ y := by
  refine mb_identification_of_ratios h₁.base h₂.base hy₀ (fun q w ↦ ?_) (fun i k q w ↦ ?_)
  · exact tendsto_nhds_unique (tendsto_mbgExp_tangential h₁ hy₀ w)
      ((tendsto_mbgExp_tangential h₂ hy₀ w).congr' ((hT q w).mono fun t ht ↦ ht.symm))
  · exact tendsto_nhds_unique (tendsto_mul_mbgExp_transverse_second h₁ hy₀ i k w)
      ((tendsto_mul_mbgExp_transverse_second h₂ hy₀ i k w).congr'
        ((hN i k q w).mono fun t ht ↦ by simp only; rw [ht]))

end Laplace.Multi
