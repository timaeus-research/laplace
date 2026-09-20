/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# Finite sufficient statistics for Gibbs measures

Two Gibbs densities `p₁ ∝ e^{-E₁}`, `p₂ ∝ e^{-E₂}` on a measure space whose
expectations of the energy difference `D = E₂ - E₁` agree have `D` almost
everywhere constant (`energy_sub_ae_const_of_gibbsExpectation_eq`). The proof is
the equality case of the monotonicity of the logarithm: `(log p₁ - log p₂)(p₁ - p₂)
≥ 0` pointwise, `log p₁ - log p₂ = D + log(Z₂/Z₁)`, and the integral of the
product vanishes because both densities integrate to `1` and the `D`-moments
agree; so the product vanishes a.e., which forces `p₁ = p₂` a.e. No relative
entropy and no finiteness of the reference measure is needed.

For an exponential family `E_a = ∑ᵢ aᵢ fᵢ` this is finite-dimensional
identifiability: equal Gibbs moments of the finitely many `fᵢ` force `E_a - E_b`
to be a.e. constant (`energy_sub_ae_const_of_moments_eq`). Read with `fᵢ` the
monomials of weighted degree one for fixed positive weights: the normalized
Gibbs moments of those monomials determine a positive weighted-homogeneous
polynomial up to an additive constant, which the value at `0` removes. This is
the finite-sufficient-statistics endpoint of the germbij note's constructive
recovery, bypassing the coarea formula.
-/

open MeasureTheory Set Filter Real

namespace Laplace

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Monotonicity of the logarithm in product form: `(log x - log y)(x - y) ≥ 0`. -/
theorem log_sub_log_mul_sub_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ (Real.log x - Real.log y) * (x - y) := by
  rcases le_total x y with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (Real.log_le_log hx h))
      (sub_nonpos.mpr h)
  · exact mul_nonneg (sub_nonneg.mpr (Real.log_le_log hy h)) (sub_nonneg.mpr h)

/-- Equality case: `(log x - log y)(x - y) = 0` forces `x = y`. -/
theorem eq_of_log_sub_log_mul_sub_eq_zero {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : (Real.log x - Real.log y) * (x - y) = 0) : x = y := by
  rcases mul_eq_zero.mp h with h | h
  · exact Real.log_injOn_pos hx hy (sub_eq_zero.mp h)
  · exact sub_eq_zero.mp h

/-- **Gibbs measures with equal expectation of the energy difference have a.e.
constant energy difference.** With `Zⱼ = ∫ e^{-Eⱼ} dμ > 0` and the moments
`∫ (E₂ - E₁) e^{-Eⱼ} dμ / Zⱼ` equal for `j = 1, 2`, there is `c` with
`E₂ - E₁ = c` a.e. -/
theorem energy_sub_ae_const_of_gibbsExpectation_eq {E₁ E₂ : X → ℝ}
    (hZ₁ : Integrable (fun x ↦ Real.exp (-E₁ x)) μ)
    (hZ₂ : Integrable (fun x ↦ Real.exp (-E₂ x)) μ)
    (hZ₁pos : 0 < ∫ x, Real.exp (-E₁ x) ∂μ) (hZ₂pos : 0 < ∫ x, Real.exp (-E₂ x) ∂μ)
    (hD₁ : Integrable (fun x ↦ (E₂ x - E₁ x) * Real.exp (-E₁ x)) μ)
    (hD₂ : Integrable (fun x ↦ (E₂ x - E₁ x) * Real.exp (-E₂ x)) μ)
    (hmom : (∫ x, (E₂ x - E₁ x) * Real.exp (-E₁ x) ∂μ) / (∫ x, Real.exp (-E₁ x) ∂μ) =
      (∫ x, (E₂ x - E₁ x) * Real.exp (-E₂ x) ∂μ) / (∫ x, Real.exp (-E₂ x) ∂μ)) :
    ∃ c : ℝ, (fun x ↦ E₂ x - E₁ x) =ᵐ[μ] fun _ ↦ c := by
  set Z₁ : ℝ := ∫ x, Real.exp (-E₁ x) ∂μ with hZ₁_def
  set Z₂ : ℝ := ∫ x, Real.exp (-E₂ x) ∂μ with hZ₂_def
  set A₁ : ℝ := ∫ x, (E₂ x - E₁ x) * Real.exp (-E₁ x) ∂μ with hA₁_def
  set A₂ : ℝ := ∫ x, (E₂ x - E₁ x) * Real.exp (-E₂ x) ∂μ with hA₂_def
  set c₀ : ℝ := Real.log Z₂ - Real.log Z₁ with hc₀_def
  -- the two densities and the log-ratio identity
  set p₁ : X → ℝ := fun x ↦ Real.exp (-E₁ x) / Z₁ with hp₁_def
  set p₂ : X → ℝ := fun x ↦ Real.exp (-E₂ x) / Z₂ with hp₂_def
  have hp₁pos : ∀ x, 0 < p₁ x := fun x ↦ div_pos (Real.exp_pos _) hZ₁pos
  have hp₂pos : ∀ x, 0 < p₂ x := fun x ↦ div_pos (Real.exp_pos _) hZ₂pos
  have hlog : ∀ x, Real.log (p₁ x) - Real.log (p₂ x) = (E₂ x - E₁ x) + c₀ := by
    intro x
    simp only [hp₁_def, hp₂_def, hc₀_def]
    rw [Real.log_div (Real.exp_pos _).ne' hZ₁pos.ne', Real.log_div (Real.exp_pos _).ne' hZ₂pos.ne',
      Real.log_exp, Real.log_exp]
    ring
  -- the nonnegative integrand
  set g : X → ℝ := fun x ↦ ((E₂ x - E₁ x) + c₀) * (p₁ x - p₂ x) with hg_def
  have hg0 : ∀ x, 0 ≤ g x := fun x ↦ by
    simp only [hg_def]
    rw [← hlog x]
    exact log_sub_log_mul_sub_nonneg (hp₁pos x) (hp₂pos x)
  -- its expansion into integrable pieces
  have hexp : g = fun x ↦ ((E₂ x - E₁ x) * Real.exp (-E₁ x)) * Z₁⁻¹ -
      ((E₂ x - E₁ x) * Real.exp (-E₂ x)) * Z₂⁻¹ +
      (c₀ * (Real.exp (-E₁ x) * Z₁⁻¹) - c₀ * (Real.exp (-E₂ x) * Z₂⁻¹)) := by
    funext x
    simp only [hg_def, hp₁_def, hp₂_def]
    field_simp
  have hI1 : Integrable (fun x ↦ ((E₂ x - E₁ x) * Real.exp (-E₁ x)) * Z₁⁻¹ -
      ((E₂ x - E₁ x) * Real.exp (-E₂ x)) * Z₂⁻¹) μ := (hD₁.mul_const _).sub (hD₂.mul_const _)
  have hI2 : Integrable (fun x ↦ c₀ * (Real.exp (-E₁ x) * Z₁⁻¹) -
      c₀ * (Real.exp (-E₂ x) * Z₂⁻¹)) μ :=
    ((hZ₁.mul_const _).const_mul c₀).sub ((hZ₂.mul_const _).const_mul c₀)
  have hint : Integrable g μ := by
    rw [hexp]
    exact hI1.add hI2
  -- its integral vanishes
  have hval : ∫ x, g x ∂μ = 0 := by
    rw [hexp]
    beta_reduce
    rw [integral_add hI1 hI2, integral_sub (hD₁.mul_const _) (hD₂.mul_const _),
      integral_sub ((hZ₁.mul_const _).const_mul c₀) ((hZ₂.mul_const _).const_mul c₀),
      integral_mul_const, integral_mul_const, integral_const_mul, integral_const_mul,
      integral_mul_const, integral_mul_const]
    have h1 : Z₁ * Z₁⁻¹ = 1 := mul_inv_cancel₀ hZ₁pos.ne'
    have h2 : Z₂ * Z₂⁻¹ = 1 := mul_inv_cancel₀ hZ₂pos.ne'
    have hm : A₁ * Z₁⁻¹ = A₂ * Z₂⁻¹ := by
      rw [← div_eq_mul_inv, ← div_eq_mul_inv]
      exact hmom
    simp only [← hZ₁_def, ← hZ₂_def, ← hA₁_def, ← hA₂_def] at h1 h2 hm ⊢
    rw [h1, h2, hm]
    ring
  -- hence the integrand vanishes a.e.
  have hzero : g =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hg0) hint).mp hval
  refine ⟨-c₀, ?_⟩
  filter_upwards [hzero] with x hx
  have hx' : ((E₂ x - E₁ x) + c₀) * (p₁ x - p₂ x) = 0 := hx
  rw [← hlog x] at hx'
  have hpe : p₁ x = p₂ x := eq_of_log_sub_log_mul_sub_eq_zero (hp₁pos x) (hp₂pos x) hx'
  have := hlog x
  rw [hpe, sub_self] at this
  linarith

/-! ### Exponential families -/

variable {ι : Type*} [Fintype ι]

/-- The energy `∑ᵢ aᵢ fᵢ` of an exponential family. -/
def energy (f : ι → X → ℝ) (a : ι → ℝ) (x : X) : ℝ := ∑ i, a i * f i x

/-- **Finite sufficient statistics.** If the Gibbs measures of `E_a = ∑ aᵢ fᵢ` and
`E_b = ∑ bᵢ fᵢ` have the same normalized moments `∫ fᵢ e^{-E} / ∫ e^{-E}` for every
`i`, then `E_b - E_a` is a.e. constant. -/
theorem energy_sub_ae_const_of_moments_eq (f : ι → X → ℝ) (a b : ι → ℝ)
    (hZa : Integrable (fun x ↦ Real.exp (-energy f a x)) μ)
    (hZb : Integrable (fun x ↦ Real.exp (-energy f b x)) μ)
    (hZapos : 0 < ∫ x, Real.exp (-energy f a x) ∂μ)
    (hZbpos : 0 < ∫ x, Real.exp (-energy f b x) ∂μ)
    (hfa : ∀ i, Integrable (fun x ↦ f i x * Real.exp (-energy f a x)) μ)
    (hfb : ∀ i, Integrable (fun x ↦ f i x * Real.exp (-energy f b x)) μ)
    (hmom : ∀ i, (∫ x, f i x * Real.exp (-energy f a x) ∂μ) / (∫ x, Real.exp (-energy f a x) ∂μ) =
      (∫ x, f i x * Real.exp (-energy f b x) ∂μ) / (∫ x, Real.exp (-energy f b x) ∂μ)) :
    ∃ c : ℝ, (fun x ↦ energy f b x - energy f a x) =ᵐ[μ] fun _ ↦ c := by
  -- the energy difference is the finite combination `∑ (bᵢ - aᵢ) fᵢ`
  have hD : ∀ x, energy f b x - energy f a x = ∑ i, (b i - a i) * f i x := by
    intro x
    simp only [energy, ← Finset.sum_sub_distrib]
    congr 1
    funext i
    ring
  have hDa : Integrable (fun x ↦ (energy f b x - energy f a x) * Real.exp (-energy f a x)) μ := by
    have : (fun x ↦ (energy f b x - energy f a x) * Real.exp (-energy f a x)) =
        fun x ↦ ∑ i, (b i - a i) * (f i x * Real.exp (-energy f a x)) := by
      funext x
      rw [hD, Finset.sum_mul]
      congr 1
      funext i
      ring
    rw [this]
    exact integrable_finsetSum _ fun i _ ↦ (hfa i).const_mul _
  have hDb : Integrable (fun x ↦ (energy f b x - energy f a x) * Real.exp (-energy f b x)) μ := by
    have : (fun x ↦ (energy f b x - energy f a x) * Real.exp (-energy f b x)) =
        fun x ↦ ∑ i, (b i - a i) * (f i x * Real.exp (-energy f b x)) := by
      funext x
      rw [hD, Finset.sum_mul]
      congr 1
      funext i
      ring
    rw [this]
    exact integrable_finsetSum _ fun i _ ↦ (hfb i).const_mul _
  -- equal moments of the difference, by linearity
  have hlin : ∀ (E : X → ℝ), (∀ i, Integrable (fun x ↦ f i x * Real.exp (-E x)) μ) →
      ∫ x, (energy f b x - energy f a x) * Real.exp (-E x) ∂μ =
        ∑ i, (b i - a i) * ∫ x, f i x * Real.exp (-E x) ∂μ := by
    intro E hE
    have h1 : (fun x ↦ (energy f b x - energy f a x) * Real.exp (-E x)) =
        fun x ↦ ∑ i, (b i - a i) * (f i x * Real.exp (-E x)) := by
      funext x
      rw [hD, Finset.sum_mul]
      congr 1
      funext i
      ring
    rw [h1, integral_finsetSum _ fun i _ ↦ (hE i).const_mul _]
    congr 1
    funext i
    rw [integral_const_mul]
  have hmomD : (∫ x, (energy f b x - energy f a x) * Real.exp (-energy f a x) ∂μ) /
      (∫ x, Real.exp (-energy f a x) ∂μ) =
      (∫ x, (energy f b x - energy f a x) * Real.exp (-energy f b x) ∂μ) /
      (∫ x, Real.exp (-energy f b x) ∂μ) := by
    rw [hlin _ hfa, hlin _ hfb, Finset.sum_div, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_div_assoc, mul_div_assoc, hmom i]
  exact energy_sub_ae_const_of_gibbsExpectation_eq μ hZa hZb hZapos hZbpos hDa hDb hmomD

end Laplace
