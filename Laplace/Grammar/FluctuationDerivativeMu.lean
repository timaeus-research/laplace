/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.FluctuationDerivative
import Laplace.Grammar.FamilyCoeffSeries

/-!
# The derivative dictionary in the spectral parameter (Stage 5e)

Unit 255 (Taylor-tree programme; Astra #29 candidate B, conclusion; review v22 follow-ups). The
logarithmic moments are spectral derivatives of the fluctuation function: for `β > 0`, `μ > 0`,
```
∂_μ fluctMoment β a p μ i = − fluctMoment β a p μ (i+1),
fluctMoment β a p μ i = (−1)^i ∂_μ^i S_{μ+p/2}(a),            S_ν(a) = ∫₀^∞ t^{ν-1} e^{-βt+β√t a}
    dt,
β^p fluctMoment β a p μ i = (−∂_μ)^i ∂_a^p S_μ(a)                 (the paper's dictionary),
```
(`hasDerivAt_fluctMoment_mu`, `fluctMoment_eq_iteratedDeriv_mu`, `fluctMoment_eq_mixed_deriv`), by
differentiation under the integral with the two-sided domination
`t^{ν-1} ≤ t^{μ/2-1} + t^{3μ/2-1}` on `|ν − μ| < μ/2`; the sign `(−∂_μ)^i ↔ (−log t)^i` is exact.
    Also
the shift identity `fluctMoment β a p ν 0 = S_{ν+p/2}(a)` (`fluctMoment_zero_eq_shift`) and the
identification of the family coefficients with the paper's series for **every** real `μ`
(`familySpectralCoeff_eq_series'`; both sides vanish off `Λ(h,k)`). No `sorry` and no additional
`axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology

namespace Laplace.Grammar

open MonoRep CoeffFamily

/-! ### Pointwise derivative in the exponent -/

theorem hasDerivAt_rpow_exponent {t : ℝ} (ht : 0 < t) (μ : ℝ) :
    HasDerivAt (fun μ => t ^ (μ - 1)) (Real.log t * t ^ (μ - 1)) μ := by
  have h : HasDerivAt (fun μ => Real.log t * (μ - 1)) (Real.log t) μ := by
    simpa using ((hasDerivAt_id μ).sub_const 1).const_mul (Real.log t)
  have := h.exp
  have hfun : (fun μ => Real.exp (Real.log t * (μ - 1))) = fun μ => t ^ (μ - 1) := by
    funext μ; rw [Real.rpow_def_of_pos ht]
  rw [hfun] at this
  convert this using 1
  rw [Real.rpow_def_of_pos ht]; ring

theorem hasDerivAt_fluctIntegrand_mu (β : ℝ) (p : ℕ) (i : ℕ) (a : ℝ) {t : ℝ} (ht : 0 < t) (μ : ℝ) :
    HasDerivAt (fun μ => fluctIntegrand β p μ i a t) (-(fluctIntegrand β p μ (i + 1) a t)) μ := by
  have := ((hasDerivAt_rpow_exponent ht μ).mul_const ((-Real.log t) ^ i)).mul_const
    (phaseKernel β a p t)
  unfold fluctIntegrand
  refine this.congr_deriv ?_
  rw [pow_succ]; ring

/-! ### Two-sided domination near `μ` -/

theorem rpow_sub_one_le_two_sided {t : ℝ} (ht : 0 < t) {μ ν : ℝ} (_hμ : 0 < μ)
    (hν : ν ∈ Metric.ball μ (μ / 2)) :
    t ^ (ν - 1) ≤ t ^ (μ / 2 - 1) + t ^ (3 * μ / 2 - 1) := by
  have hb := Metric.mem_ball.1 hν
  rw [Real.dist_eq, abs_sub_lt_iff] at hb
  have h1 : 0 ≤ t ^ (μ / 2 - 1) := Real.rpow_nonneg ht.le _
  have h2 : 0 ≤ t ^ (3 * μ / 2 - 1) := Real.rpow_nonneg ht.le _
  rcases le_or_gt t 1 with ht1 | ht1
  · calc t ^ (ν - 1) ≤ t ^ (μ / 2 - 1) :=
          Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
      _ ≤ _ := by linarith
  · calc t ^ (ν - 1) ≤ t ^ (3 * μ / 2 - 1) :=
          Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
      _ ≤ _ := by linarith

theorem abs_deriv_fluctIntegrand_mu_le (β : ℝ) (p : ℕ) (i : ℕ) (a : ℝ) {t : ℝ} (ht : 0 < t)
    {μ ν : ℝ} (hμ : 0 < μ) (hν : ν ∈ Metric.ball μ (μ / 2)) :
    ‖-(fluctIntegrand β p ν (i + 1) a t)‖ ≤
      logMajorant β a (μ / 2) (i + 1) p t + logMajorant β a (3 * μ / 2) (i + 1) p t := by
  rw [norm_neg, Real.norm_eq_abs]
  unfold fluctIntegrand logMajorant
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _),
    abs_of_nonneg (phaseKernel_nonneg _ _ _ _), abs_pow, abs_neg]
  have hlog : |Real.log t| ^ (i + 1) ≤ (1 + |Real.log t|) ^ (i + 1) :=
    pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg (Real.log t)]) _
  have hg := phaseKernel_nonneg β a p t
  have hL : 0 ≤ (1 + |Real.log t|) ^ (i + 1) := by positivity
  calc t ^ (ν - 1) * |Real.log t| ^ (i + 1) * phaseKernel β a p t
      ≤ (t ^ (μ / 2 - 1) + t ^ (3 * μ / 2 - 1)) * (1 + |Real.log t|) ^ (i + 1) * phaseKernel β a
          p t :=
        mul_le_mul_of_nonneg_right (mul_le_mul (rpow_sub_one_le_two_sided ht hμ hν) hlog
          (by positivity) (by positivity)) hg
    _ = _ := by ring

theorem continuous_fluctIntegrand_mu (β : ℝ) (p : ℕ) (μ : ℝ) (i : ℕ) (a : ℝ) :
    ContinuousOn (fun t => fluctIntegrand β p μ i a t) (Ioi 0) :=
  continuous_fluctIntegrand_a β p μ i a

/-- **`∂_μ fluctMoment = − fluctMoment` at the next log order.** -/
theorem hasDerivAt_fluctMoment_mu (β : ℝ) (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (i : ℕ)
    (a : ℝ) :
    HasDerivAt (fun ν => fluctMoment β a p ν i) (-(fluctMoment β a p μ (i + 1))) μ := by
  have hμ2 : 0 < μ / 2 := by positivity
  have hμ3 : 0 < 3 * μ / 2 := by positivity
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun ν t => fluctIntegrand β p ν i a t)
    (F' := fun ν t => -(fluctIntegrand β p ν (i + 1) a t))
    (bound := fun t => logMajorant β a (μ / 2) (i + 1) p t + logMajorant β a (3 * μ / 2) (i + 1)
        p t)
    (x₀ := μ) (Metric.ball_mem_nhds μ hμ2)
    (Eventually.of_forall fun ν =>
      ((continuous_fluctIntegrand_mu β p ν i a).aestronglyMeasurable measurableSet_Ioi))
    (integrableOn_fluct β a hβ p hμ i)
    ((continuous_fluctIntegrand_mu β p μ (i + 1) a).neg.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ν hν =>
      abs_deriv_fluctIntegrand_mu_le β p i a (mem_Ioi.1 ht) hμ hν)
    ((integrableOn_logMajorant β a (μ / 2) hβ hμ2 (i + 1) p).add
      (integrableOn_logMajorant β a (3 * μ / 2) hβ hμ3 (i + 1) p))
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ν _ =>
      hasDerivAt_fluctIntegrand_mu β p i a (mem_Ioi.1 ht) ν)
  have hval : ∫ t in Ioi (0 : ℝ), -(fluctIntegrand β p μ (i + 1) a t) =
      -(fluctMoment β a p μ (i + 1)) := by
    unfold fluctMoment; rw [integral_neg]; rfl
  rw [hval] at key
  exact key.2

/-- **Iterated spectral derivatives**: on `μ > 0`,
`∂_μ^i fluctMoment(·, q) = (−1)^i fluctMoment(·, i+q)`. -/
theorem iteratedDeriv_fluctMoment_mu (β : ℝ) (hβ : 0 < β) (p : ℕ) (a : ℝ) :
    ∀ i q : ℕ, ∀ {μ : ℝ}, 0 < μ →
      iteratedDeriv i (fun ν => fluctMoment β a p ν q) μ = (-1) ^ i * fluctMoment β a p μ (i + q)
  | 0, q, μ, _ => by simp
  | i + 1, q, μ, hμ => by
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv i (fun ν => fluctMoment β a p ν q) =ᶠ[𝓝 μ]
        fun ν => (-1) ^ i * fluctMoment β a p ν (i + q) := by
      filter_upwards [Ioi_mem_nhds hμ] with ν hν
      exact iteratedDeriv_fluctMoment_mu β hβ p a i q (mem_Ioi.1 hν)
    rw [hev.deriv_eq, ((hasDerivAt_fluctMoment_mu β hβ p hμ (i + q) a).const_mul ((-1 : ℝ) ^
        i)).deriv,
      show i + 1 + q = i + q + 1 by ring, pow_succ]
    ring

/-- Iterated spectral derivatives of a constant multiple. -/
theorem iteratedDeriv_const_mul_fluctMoment_mu (β : ℝ) (hβ : 0 < β) (p : ℕ) (a C : ℝ) :
    ∀ i q : ℕ, ∀ {μ : ℝ}, 0 < μ →
      iteratedDeriv i (fun ν => C * fluctMoment β a p ν q) μ =
        C * ((-1) ^ i * fluctMoment β a p μ (i + q))
  | 0, q, μ, _ => by simp
  | i + 1, q, μ, hμ => by
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv i (fun ν => C * fluctMoment β a p ν q) =ᶠ[𝓝 μ]
        fun ν => C * ((-1) ^ i * fluctMoment β a p ν (i + q)) := by
      filter_upwards [Ioi_mem_nhds hμ] with ν hν
      exact iteratedDeriv_const_mul_fluctMoment_mu β hβ p a C i q (mem_Ioi.1 hν)
    rw [hev.deriv_eq, (((hasDerivAt_fluctMoment_mu β hβ p hμ (i + q) a).const_mul
      ((-1 : ℝ) ^ i)).const_mul C).deriv, show i + 1 + q = i + q + 1 by ring, pow_succ]
    ring

/-- The shift identity `fluctMoment β a p ν 0 = S_{ν+p/2}(a)`. -/
theorem fluctMoment_zero_eq_shift (β a : ℝ) (p : ℕ) (ν : ℝ) :
    fluctMoment β a p ν 0 = fluctuationFn β (ν + p / 2) a := by
  unfold fluctuationFn fluctMoment phaseKernel
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := mem_Ioi.1 ht
  simp only [pow_zero, one_mul, mul_one]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le,
    show ν + (p : ℝ) / 2 - 1 = (ν - 1) + 1 / 2 * p by ring, Real.rpow_add ht0]
  ring

/-- **The spectral dictionary**: `fluctMoment β a p μ i = (−1)^i ∂_ν^i S_{ν+p/2}(a)|_{ν=μ}`. -/
theorem fluctMoment_eq_iteratedDeriv_mu (β : ℝ) (hβ : 0 < β) (p : ℕ) (a : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (i : ℕ) :
    fluctMoment β a p μ i = (-1) ^ i * iteratedDeriv i (fun ν => fluctuationFn β (ν + p / 2) a) μ
        := by
  have hfun : (fun ν => fluctuationFn β (ν + p / 2) a) = fun ν => fluctMoment β a p ν 0 :=
    funext fun ν => (fluctMoment_zero_eq_shift β a p ν).symm
  rw [hfun, iteratedDeriv_fluctMoment_mu β hβ p a i 0 hμ, add_zero, ← mul_assoc, ← mul_pow]
  simp

/-- **The paper's mixed dictionary**: `β^p fluctMoment β a p μ i = (−∂_μ)^i ∂_a^p S_μ(a)`, i.e.
`(−1)^i ∂_ν^i (∂_a^p S_ν(a))|_{ν=μ}` for `μ > 0`. -/
theorem fluctMoment_eq_mixed_deriv (β : ℝ) (hβ : 0 < β) (p : ℕ) (a : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (i : ℕ) :
    β ^ p * fluctMoment β a p μ i =
      (-1) ^ i * iteratedDeriv i (fun ν => iteratedDeriv p (fluctuationFn β ν) a) μ := by
  have hev : (fun ν => iteratedDeriv p (fluctuationFn β ν) a) =ᶠ[𝓝 μ]
      fun ν => β ^ p * fluctMoment β a p ν 0 := by
    filter_upwards [Ioi_mem_nhds hμ] with ν hν
    exact iteratedDeriv_fluctuationFn β hβ (mem_Ioi.1 hν) p a
  rw [hev.iteratedDeriv_eq, iteratedDeriv_const_mul_fluctMoment_mu β hβ p a (β ^ p) i 0 hμ,
      add_zero,
    show (-1 : ℝ) ^ i * (β ^ p * ((-1) ^ i * fluctMoment β a p μ i)) =
      β ^ p * fluctMoment β a p μ i * ((-1) ^ i * (-1) ^ i) by ring,
    ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]

/-! ### Identification of the coefficient series at every `μ` -/

theorem kernelS_eq_zero_of_not_candidate (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) {μ : ℝ}
    (hμ : ¬ candidateExp h k μ) (j : ℕ) (γ : Fin (n + 1) → ℕ) : kernelS n h k β a p μ j γ = 0 := by
  unfold kernelS
  exact Finset.sum_eq_zero fun q _ => by rw [coeffAt_monoWeights_eq_zero n h k γ hμ q]; ring

theorem familyCoeffSeries_eq_zero_of_not_candidate (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cξ cη : CoeffFamily (n + 1)) {μ : ℝ} (hμ : ¬ candidateExp h k μ) (j : ℕ) :
    familyCoeffSeries n h k β cξ cη μ j = 0 := by
  unfold familyCoeffSeries familyCoeffTerm kernelFunctional
  simp_rw [kernelS_eq_zero_of_not_candidate n h k β _ _ hμ j, mul_zero, tsum_zero]
  simp

/-- **Identification for every real `μ`**: `A_{μ,j}(cξ,cη) = familyCoeffSeries` (both vanish off
`Λ(h,k)`). -/
theorem familySpectralCoeff_eq_series' (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) (μ : ℝ)
    (j : ℕ) :
    familySpectralCoeff n h k β cξ cη μ j = familyCoeffSeries n h k β cξ cη μ j := by
  by_cases hc : candidateExp h k μ
  · exact familySpectralCoeff_eq_series n h k hk β hβ hξ hη (candidateExp_pos hk hc) j
  · rw [familySpectralCoeff_eq_zero_of_not_candidate n h k hk β hβ hξ hη hc j,
      familyCoeffSeries_eq_zero_of_not_candidate n h k β cξ cη hc j]

end Laplace.Grammar
