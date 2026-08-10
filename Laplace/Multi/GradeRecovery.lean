/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.GradeComparison

/-!
# Grade recovery

Stages C and D of the semi-quasi-homogeneous recovery plan, reaching
the scoping consult's designated endpoint for class (c). Stage C is
covariance injectivity: a continuous observable with vanishing
self-covariance under a positive reference density is almost
everywhere its mean, hence (by continuity against the open-positive
volume) constant, and a vanishing value at the origin kills the
constant; for finite combinations of nonconstant monomials the
covariances against the support monomials suffice. Stage D composes
this with the one-grade difference limit: if the normalized moment
differences of two families vanish at the grade rate for every
support monomial, while the difference limits equal the negative
covariances, uniqueness of limits forces every covariance to zero
and the grade difference to vanish identically.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

theorem mvMonomial_continuous (α : ι → ℕ) :
    Continuous (mvMonomial (ι := ι) α) :=
  continuous_finset_prod _ fun i _ ↦ (continuous_apply i).pow _

/-- A nonzero multi-index's monomial vanishes at the origin. -/
theorem mvMonomial_zero_eq_zero {α : ι → ℕ} (hα : α ≠ 0) :
    mvMonomial (ι := ι) α 0 = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hα (funext hall)
  unfold mvMonomial
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [Pi.zero_apply, zero_pow hi]

/-- Expectation linearity over a finite monomial combination against
a fixed second factor. -/
theorem expectationUnder_combo_mul
    (P B : (ι → ℝ) → ℝ) (S : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ)
    (hint : ∀ α ∈ S, Integrable (fun w : ι → ℝ ↦
      mvMonomial α w * B w * Real.exp (-P w))) :
    expectationUnder volume P
        (fun w ↦ (∑ α ∈ S, c α * mvMonomial α w) * B w) =
      ∑ α ∈ S, c α * expectationUnder volume P
        (fun w ↦ mvMonomial α w * B w) := by
  unfold expectationUnder
  beta_reduce
  have hnum : ∫ w : ι → ℝ, (∑ α ∈ S, c α * mvMonomial α w) * B w *
      Real.exp (-P w) =
      ∑ α ∈ S, c α * ∫ w : ι → ℝ,
        mvMonomial α w * B w * Real.exp (-P w) := by
    calc ∫ w : ι → ℝ, (∑ α ∈ S, c α * mvMonomial α w) * B w *
          Real.exp (-P w)
        = ∫ w : ι → ℝ, ∑ α ∈ S,
            c α * (mvMonomial α w * B w * Real.exp (-P w)) := by
          refine MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall fun w ↦ ?_)
          beta_reduce
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun α _ ↦ ?_
          ring
      _ = ∑ α ∈ S, c α * ∫ w : ι → ℝ,
            mvMonomial α w * B w * Real.exp (-P w) := by
          rw [MeasureTheory.integral_finset_sum _ fun α hα ↦
            (hint α hα).const_mul (c α)]
          refine Finset.sum_congr rfl fun α _ ↦ ?_
          rw [MeasureTheory.integral_const_mul]
  rw [hnum, Finset.sum_div]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [mul_div_assoc]

/-- Covariance bilinearity in the first argument over a finite
monomial combination. -/
theorem covarianceUnder_combo_left
    (P B : (ι → ℝ) → ℝ) (S : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ)
    (hintB : ∀ α ∈ S, Integrable (fun w : ι → ℝ ↦
      mvMonomial α w * B w * Real.exp (-P w)))
    (hint1 : ∀ α ∈ S, Integrable (fun w : ι → ℝ ↦
      mvMonomial α w * Real.exp (-P w))) :
    covarianceUnder volume P
        (fun w ↦ ∑ α ∈ S, c α * mvMonomial α w) B =
      ∑ α ∈ S, c α * covarianceUnder volume P (mvMonomial α) B := by
  unfold covarianceUnder
  have h1 := expectationUnder_combo_mul P B S c hintB
  have h2 : expectationUnder volume P
      (fun w ↦ ∑ α ∈ S, c α * mvMonomial α w) =
      ∑ α ∈ S, c α * expectationUnder volume P (mvMonomial α) := by
    have := expectationUnder_combo_mul P (fun _ ↦ (1 : ℝ)) S c
      (by simpa [mul_one] using hint1)
    simpa [mul_one] using this
  rw [h1, h2, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  ring

/-- **Stage C core**: a continuous observable with vanishing
self-covariance under a positive reference density, and vanishing
value at the origin, is identically zero. -/
theorem eq_zero_of_covariance_self_zero
    {Q P : (ι → ℝ) → ℝ} (hQcont : Continuous Q)
    (he : Integrable (fun w : ι → ℝ ↦ Real.exp (-P w)))
    (hQe : Integrable (fun w : ι → ℝ ↦ Q w * Real.exp (-P w)))
    (hQQe : Integrable (fun w : ι → ℝ ↦ Q w * Q w * Real.exp (-P w)))
    (hZpos : 0 < ∫ w : ι → ℝ, Real.exp (-P w))
    (hcov : covarianceUnder volume P Q Q = 0)
    (hQ0 : Q 0 = 0) :
    ∀ w, Q w = 0 := by
  set Z : ℝ := ∫ w : ι → ℝ, Real.exp (-P w) with hZ_def
  set m : ℝ := (∫ w : ι → ℝ, Q w * Real.exp (-P w)) / Z with hm_def
  have hZne : Z ≠ 0 := hZpos.ne'
  -- the variance integral vanishes
  have hintvar : Integrable (fun w : ι → ℝ ↦
      (Q w - m) ^ 2 * Real.exp (-P w)) := by
    have h1 : Integrable (fun w : ι → ℝ ↦
        Q w * Q w * Real.exp (-P w) -
          2 * m * (Q w * Real.exp (-P w)) +
          m ^ 2 * Real.exp (-P w)) :=
      (hQQe.sub ((hQe.const_mul (2 * m)))).add (he.const_mul (m ^ 2))
    refine h1.congr (Filter.Eventually.of_forall fun w ↦ ?_)
    beta_reduce
    ring
  have hvar : ∫ w : ι → ℝ, (Q w - m) ^ 2 * Real.exp (-P w) = 0 := by
    have hexpand : ∫ w : ι → ℝ, (Q w - m) ^ 2 * Real.exp (-P w) =
        (∫ w : ι → ℝ, Q w * Q w * Real.exp (-P w)) -
          2 * m * (∫ w : ι → ℝ, Q w * Real.exp (-P w)) +
          m ^ 2 * Z := by
      rw [hZ_def]
      rw [show (fun w : ι → ℝ ↦ (Q w - m) ^ 2 * Real.exp (-P w)) =
          fun w : ι → ℝ ↦
            Q w * Q w * Real.exp (-P w) -
              2 * m * (Q w * Real.exp (-P w)) +
              m ^ 2 * Real.exp (-P w) from funext fun w ↦ by ring]
      have h12 : Integrable (fun w : ι → ℝ ↦
          Q w * Q w * Real.exp (-P w) -
            2 * m * (Q w * Real.exp (-P w))) volume :=
        hQQe.sub (hQe.const_mul (2 * m))
      rw [MeasureTheory.integral_add h12 (he.const_mul (m ^ 2)),
        MeasureTheory.integral_sub hQQe (hQe.const_mul (2 * m)),
        MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
    rw [hexpand]
    have hcov' : (∫ w : ι → ℝ, Q w * Q w * Real.exp (-P w)) / Z -
        ((∫ w : ι → ℝ, Q w * Real.exp (-P w)) / Z) *
          ((∫ w : ι → ℝ, Q w * Real.exp (-P w)) / Z) = 0 := by
      have := hcov
      unfold covarianceUnder expectationUnder at this
      rw [← hZ_def] at this
      exact this
    rw [hm_def]
    field_simp at hcov' ⊢
    nlinarith [hcov']
  -- almost-everywhere constancy
  have hae : (fun w : ι → ℝ ↦ (Q w - m) ^ 2 * Real.exp (-P w))
      =ᵐ[volume] 0 := by
    rw [← MeasureTheory.integral_eq_zero_iff_of_nonneg
      (fun w ↦ by positivity) hintvar]
    exact hvar
  have haeQ : Q =ᵐ[volume] fun _ ↦ m := by
    refine hae.mono fun w hw ↦ ?_
    have hw' : (Q w - m) ^ 2 * Real.exp (-P w) = 0 := hw
    have hsq : (Q w - m) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hw' with h | h
      · exact h
      · exact absurd h (Real.exp_pos _).ne'
    have := pow_eq_zero_iff (n := 2) (by omega) |>.mp hsq
    have hQw : Q w = m := by linarith [sub_eq_zero.mp this]
    exact hQw
  -- everywhere constancy, and the constant is zero
  have hQeq : Q = fun _ ↦ m :=
    (Continuous.ae_eq_iff_eq volume hQcont continuous_const).mp haeQ
  have hm0 : m = 0 := by
    rw [← hQ0, hQeq]
  intro w
  rw [hQeq, hm0]

/-- **Stage C**: a finite combination of nonconstant monomials whose
covariances against its support monomials all vanish is identically
zero. -/
theorem monomialCombo_eq_zero_of_covariance_monomials_zero
    (P : (ι → ℝ) → ℝ) (S : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ)
    (hS0 : ∀ α ∈ S, α ≠ 0)
    (he : Integrable (fun w : ι → ℝ ↦ Real.exp (-P w)))
    (hint_m : ∀ α ∈ S, Integrable (fun w : ι → ℝ ↦
      mvMonomial α w * Real.exp (-P w)))
    (hint_pair : ∀ α ∈ S, Integrable (fun w : ι → ℝ ↦
      mvMonomial α w * (∑ β ∈ S, c β * mvMonomial β w) *
        Real.exp (-P w)))
    (hZpos : 0 < ∫ w : ι → ℝ, Real.exp (-P w))
    (hcov : ∀ α ∈ S, covarianceUnder volume P (mvMonomial α)
      (fun w ↦ ∑ β ∈ S, c β * mvMonomial β w) = 0) :
    ∀ w, ∑ β ∈ S, c β * mvMonomial β w = 0 := by
  set Qc : (ι → ℝ) → ℝ := fun w ↦ ∑ β ∈ S, c β * mvMonomial β w
    with hQc_def
  have hQcont : Continuous Qc :=
    continuous_finset_sum _ fun β _ ↦
      continuous_const.mul (mvMonomial_continuous β)
  have hQe : Integrable (fun w : ι → ℝ ↦ Qc w * Real.exp (-P w)) := by
    have h1 : Integrable (fun w : ι → ℝ ↦ ∑ β ∈ S,
        c β * (mvMonomial β w * Real.exp (-P w))) :=
      integrable_finset_sum _ fun β hβ ↦
        (hint_m β hβ).const_mul (c β)
    refine h1.congr (Filter.Eventually.of_forall fun w ↦ ?_)
    beta_reduce
    rw [hQc_def, Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ ↦ ?_
    ring
  have hQQe : Integrable (fun w : ι → ℝ ↦
      Qc w * Qc w * Real.exp (-P w)) := by
    have h1 : Integrable (fun w : ι → ℝ ↦ ∑ α ∈ S,
        c α * (mvMonomial α w * Qc w * Real.exp (-P w))) :=
      integrable_finset_sum _ fun α hα ↦
        (hint_pair α hα).const_mul (c α)
    refine h1.congr (Filter.Eventually.of_forall fun w ↦ ?_)
    beta_reduce
    rw [show Qc w * Qc w = (∑ α ∈ S, c α * mvMonomial α w) * Qc w
      from by rw [hQc_def]]
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    ring
  have hcovQQ : covarianceUnder volume P Qc Qc = 0 := by
    rw [hQc_def]
    rw [covarianceUnder_combo_left P Qc S c hint_pair hint_m]
    refine Finset.sum_eq_zero fun α hα ↦ ?_
    rw [hcov α hα, mul_zero]
  have hQ0 : Qc 0 = 0 := by
    rw [hQc_def]
    refine Finset.sum_eq_zero fun β hβ ↦ ?_
    rw [mvMonomial_zero_eq_zero (hS0 β hβ), mul_zero]
  exact eq_zero_of_covariance_self_zero hQcont he hQe hQQe hZpos
    hcovQQ hQ0

/-- **Stage D**: if for every support monomial the normalized
difference quotients of two families tend both to the negative
covariance (the one-grade difference limit, discharged by callers
under its hypothesis package) and to zero (the matching-rates
assumption), the grade difference vanishes identically. -/
theorem grade_eq_of_normalized_rates
    (P : (ι → ℝ) → ℝ) (V₁ V₂ : ℝ → (ι → ℝ) → ℝ) (ρ : ℕ)
    (S : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ)
    (hS0 : ∀ α ∈ S, α ≠ 0)
    (he : Integrable (fun w : ι → ℝ ↦ Real.exp (-P w)))
    (hint_m : ∀ α ∈ S, Integrable (fun w : ι → ℝ ↦
      mvMonomial α w * Real.exp (-P w)))
    (hint_pair : ∀ α ∈ S, Integrable (fun w : ι → ℝ ↦
      mvMonomial α w * (∑ β ∈ S, c β * mvMonomial β w) *
        Real.exp (-P w)))
    (hZpos : 0 < ∫ w : ι → ℝ, Real.exp (-P w))
    (hlim : ∀ α ∈ S, Tendsto (fun h : ℝ ↦
      ((∫ w : ι → ℝ, mvMonomial α w *
          Real.exp (-(P w + V₂ h w))) /
          (∫ w : ι → ℝ, Real.exp (-(P w + V₂ h w))) -
        (∫ w : ι → ℝ, mvMonomial α w *
          Real.exp (-(P w + V₁ h w))) /
          ∫ w : ι → ℝ, Real.exp (-(P w + V₁ h w))) / h ^ ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-covarianceUnder volume P (mvMonomial α)
        (fun w ↦ ∑ β ∈ S, c β * mvMonomial β w))))
    (hrate : ∀ α ∈ S, Tendsto (fun h : ℝ ↦
      ((∫ w : ι → ℝ, mvMonomial α w *
          Real.exp (-(P w + V₂ h w))) /
          (∫ w : ι → ℝ, Real.exp (-(P w + V₂ h w))) -
        (∫ w : ι → ℝ, mvMonomial α w *
          Real.exp (-(P w + V₁ h w))) /
          ∫ w : ι → ℝ, Real.exp (-(P w + V₁ h w))) / h ^ ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ w, ∑ β ∈ S, c β * mvMonomial β w = 0 := by
  refine monomialCombo_eq_zero_of_covariance_monomials_zero P S c
    hS0 he hint_m hint_pair hZpos fun α hα ↦ ?_
  have huniq := tendsto_nhds_unique (hlim α hα) (hrate α hα)
  linarith [huniq]

end Laplace.Multi
