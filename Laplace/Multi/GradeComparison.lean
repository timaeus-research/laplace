/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.QhMomentRecovery

/-!
# The one-grade difference limit

Stage B of the semi-quasi-homogeneous recovery plan (the scoping
consult's "best reusable recovery target"): for two Gibbs families
sharing a reference density `e^{-P}` (any `P` — no Gaussian
structure) and differing by corrections `V₁, V₂` that vanish
pointwise and whose difference carries the rate `h^ρ` toward `Q`, the
normalized moments separate at exactly that rate:
`(M₂(h) - M₁(h))/h^ρ → -Cov_P(A, Q)`.
The pointwise engine avoids dividing by the correction (the `W = 0`
fibers are painless): `|e^{-W} - 1 + W| ≤ W²` squeezes
`(e^{-W}-1)/h^ρ + W/h^ρ` to zero against `|W/h^ρ|·|W|`. The pairwise
formulation means products of lower-grade corrections never appear:
once all lower grades agree they cancel in the difference.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The normalized expectation under the reference density `e^{-P}`. -/
noncomputable def expectationUnder (μ : Measure X) (P A : X → ℝ) : ℝ :=
  (∫ x, A x * Real.exp (-P x) ∂μ) / ∫ x, Real.exp (-P x) ∂μ

/-- The covariance under the reference density `e^{-P}`. -/
noncomputable def covarianceUnder (μ : Measure X) (P A Q : X → ℝ) : ℝ :=
  expectationUnder μ P (fun x ↦ A x * Q x) -
    expectationUnder μ P A * expectationUnder μ P Q

/-- **The pointwise engine**: if `W → 0` at rate `h^ρ` toward `Qx`,
then `(e^{-W} - 1)/h^ρ → -Qx`. -/
theorem tendsto_exp_neg_sub_one_div_pow {W : ℝ → ℝ} {ρ : ℕ} {Qx : ℝ}
    (hW0 : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hWq : Tendsto (fun h : ℝ ↦ W h / h ^ ρ) (𝓝[>] (0 : ℝ)) (𝓝 Qx)) :
    Tendsto (fun h : ℝ ↦ (Real.exp (-W h) - 1) / h ^ ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 (-Qx)) := by
  have hrem : Tendsto
      (fun h : ℝ ↦ (Real.exp (-W h) - 1 + W h) / h ^ ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hg : Tendsto (fun h : ℝ ↦ |W h / h ^ ρ| * |W h|)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h1 := hWq.abs.mul hW0.abs
      rwa [abs_zero, mul_zero] at h1
    refine squeeze_zero_norm' ?_ hg
    have hW1 : ∀ᶠ h in 𝓝[>] (0 : ℝ), |W h| ≤ 1 := by
      have := hW0.abs
      rw [abs_zero] at this
      exact this.eventually_le_const one_pos
    filter_upwards [hW1, self_mem_nhdsWithin] with h hWh hh0'
    have hh0 : (0 : ℝ) < h := hh0'
    have hnum : |Real.exp (-W h) - 1 + W h| ≤ W h ^ 2 := by
      have heq : Real.exp (-W h) - 1 + W h =
          Real.exp (-W h) - 1 - -W h := by ring
      rw [heq]
      calc |Real.exp (-W h) - 1 - -W h| ≤ (-W h) ^ 2 :=
            Real.abs_exp_sub_one_sub_id_le (by rwa [abs_neg])
        _ = W h ^ 2 := by ring
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hh0 ρ)]
    calc |Real.exp (-W h) - 1 + W h| / h ^ ρ
        ≤ W h ^ 2 / h ^ ρ := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = |W h / h ^ ρ| * |W h| := by
          rw [abs_div, abs_of_pos (pow_pos hh0 ρ), ← sq_abs (W h), sq]
          ring
  have hsum := hWq.neg.add hrem
  rw [add_zero] at hsum
  refine hsum.congr fun h ↦ ?_
  ring

omit [MeasurableSpace X] in
/-- The pointwise difference-quotient limit for the full integrand. -/
theorem tendsto_pointwise_difference_div_pow (A P : X → ℝ)
    {V₁ V₂ : ℝ → X → ℝ} {ρ : ℕ} {Q : X → ℝ} (x : X)
    (hV₁ : Tendsto (fun h : ℝ ↦ V₁ h x) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hV₂ : Tendsto (fun h : ℝ ↦ V₂ h x) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hdiff : Tendsto (fun h : ℝ ↦ (V₂ h x - V₁ h x) / h ^ ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 (Q x))) :
    Tendsto (fun h : ℝ ↦ A x *
        (Real.exp (-(P x + V₂ h x)) - Real.exp (-(P x + V₁ h x))) /
        h ^ ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(A x * Q x * Real.exp (-P x)))) := by
  have hW0 : Tendsto (fun h : ℝ ↦ V₂ h x - V₁ h x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := hV₂.sub hV₁
    rwa [sub_zero] at this
  have hcore := tendsto_exp_neg_sub_one_div_pow hW0 hdiff
  have hexpV₁ : Tendsto (fun h : ℝ ↦ Real.exp (-V₁ h x))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hneg : Tendsto (fun h : ℝ ↦ -V₁ h x) (𝓝[>] (0 : ℝ))
        (𝓝 0) := by
      have := hV₁.neg
      rwa [neg_zero] at this
    have := (Real.continuous_exp.tendsto (0 : ℝ)).comp hneg
    simpa using this
  have hprod := (hcore.mul hexpV₁).const_mul
    (A x * Real.exp (-P x))
  rw [mul_one, show A x * Real.exp (-P x) * -Q x =
    -(A x * Q x * Real.exp (-P x)) from by ring] at hprod
  refine hprod.congr fun h ↦ ?_
  have hfactor : Real.exp (-(P x + V₂ h x)) -
      Real.exp (-(P x + V₁ h x)) =
      Real.exp (-P x) * Real.exp (-V₁ h x) *
        (Real.exp (-(V₂ h x - V₁ h x)) - 1) := by
    rw [show -(P x + V₂ h x) =
        -P x + -V₁ h x + -(V₂ h x - V₁ h x) from by ring,
      show -(P x + V₁ h x) = -P x + -V₁ h x from by ring,
      Real.exp_add, Real.exp_add]
    ring
  rw [hfactor]
  ring

/-- **The unnormalized one-grade difference limit** (dominated
convergence). -/
theorem tendsto_integral_exp_difference_div_pow
    (A P : X → ℝ) (V₁ V₂ : ℝ → X → ℝ) (ρ : ℕ) (Q : X → ℝ)
    (hmeas : ∀ᶠ h in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun x ↦
      A x * (Real.exp (-(P x + V₂ h x)) -
        Real.exp (-(P x + V₁ h x))) / h ^ ρ) μ)
    (hV₁ : ∀ᵐ x ∂μ, Tendsto (fun h : ℝ ↦ V₁ h x)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hV₂ : ∀ᵐ x ∂μ, Tendsto (fun h : ℝ ↦ V₂ h x)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hdiff : ∀ᵐ x ∂μ, Tendsto (fun h : ℝ ↦
      (V₂ h x - V₁ h x) / h ^ ρ) (𝓝[>] (0 : ℝ)) (𝓝 (Q x)))
    {G : X → ℝ} (hG : Integrable G μ)
    (hdom : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂μ,
      ‖A x * (Real.exp (-(P x + V₂ h x)) -
        Real.exp (-(P x + V₁ h x))) / h ^ ρ‖ ≤ G x)
    (hint₁ : ∀ᶠ h in 𝓝[>] (0 : ℝ), Integrable
      (fun x ↦ A x * Real.exp (-(P x + V₁ h x))) μ)
    (hint₂ : ∀ᶠ h in 𝓝[>] (0 : ℝ), Integrable
      (fun x ↦ A x * Real.exp (-(P x + V₂ h x))) μ) :
    Tendsto (fun h : ℝ ↦
      ((∫ x, A x * Real.exp (-(P x + V₂ h x)) ∂μ) -
        ∫ x, A x * Real.exp (-(P x + V₁ h x)) ∂μ) / h ^ ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-∫ x, A x * Q x * Real.exp (-P x) ∂μ)) := by
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun h : ℝ ↦ A x *
      (Real.exp (-(P x + V₂ h x)) - Real.exp (-(P x + V₁ h x))) /
      h ^ ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(A x * Q x * Real.exp (-P x)))) := by
    filter_upwards [hV₁, hV₂, hdiff] with x h1 h2 h3
    exact tendsto_pointwise_difference_div_pow A P x h1 h2 h3
  have hDCT : Tendsto (fun h : ℝ ↦ ∫ x, A x *
      (Real.exp (-(P x + V₂ h x)) - Real.exp (-(P x + V₁ h x))) /
      h ^ ρ ∂μ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, -(A x * Q x * Real.exp (-P x)) ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence G hmeas hdom
      hG hlim
  rw [MeasureTheory.integral_neg] at hDCT
  refine hDCT.congr' ?_
  filter_upwards [hint₁, hint₂] with h h1 h2
  rw [MeasureTheory.integral_div]
  congr 1
  rw [← MeasureTheory.integral_sub h2 h1]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  ring

/-- **The normalized one-grade difference limit**: the moments of the
two families separate at exactly the grade rate, with the covariance
under the reference density as the coefficient. -/
theorem tendsto_normalized_difference_div_pow
    (A P : X → ℝ) (V₁ V₂ : ℝ → X → ℝ) (ρ : ℕ) (Q : X → ℝ)
    -- inputs for the observable numerator
    (hmeasA : ∀ᶠ h in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun x ↦
      A x * (Real.exp (-(P x + V₂ h x)) -
        Real.exp (-(P x + V₁ h x))) / h ^ ρ) μ)
    {GA : X → ℝ} (hGA : Integrable GA μ)
    (hdomA : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂μ,
      ‖A x * (Real.exp (-(P x + V₂ h x)) -
        Real.exp (-(P x + V₁ h x))) / h ^ ρ‖ ≤ GA x)
    (hintA₁ : ∀ᶠ h in 𝓝[>] (0 : ℝ), Integrable
      (fun x ↦ A x * Real.exp (-(P x + V₁ h x))) μ)
    (hintA₂ : ∀ᶠ h in 𝓝[>] (0 : ℝ), Integrable
      (fun x ↦ A x * Real.exp (-(P x + V₂ h x))) μ)
    -- inputs for the partition denominator
    (hmeas1 : ∀ᶠ h in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun x ↦
      (1 : ℝ) * (Real.exp (-(P x + V₂ h x)) -
        Real.exp (-(P x + V₁ h x))) / h ^ ρ) μ)
    {G1 : X → ℝ} (hG1 : Integrable G1 μ)
    (hdom1 : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂μ,
      ‖(1 : ℝ) * (Real.exp (-(P x + V₂ h x)) -
        Real.exp (-(P x + V₁ h x))) / h ^ ρ‖ ≤ G1 x)
    (hint1₁ : ∀ᶠ h in 𝓝[>] (0 : ℝ), Integrable
      (fun x ↦ (1 : ℝ) * Real.exp (-(P x + V₁ h x))) μ)
    (hint1₂ : ∀ᶠ h in 𝓝[>] (0 : ℝ), Integrable
      (fun x ↦ (1 : ℝ) * Real.exp (-(P x + V₂ h x))) μ)
    -- the corrections
    (hV₁ : ∀ᵐ x ∂μ, Tendsto (fun h : ℝ ↦ V₁ h x)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hV₂ : ∀ᵐ x ∂μ, Tendsto (fun h : ℝ ↦ V₂ h x)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hdiff : ∀ᵐ x ∂μ, Tendsto (fun h : ℝ ↦
      (V₂ h x - V₁ h x) / h ^ ρ) (𝓝[>] (0 : ℝ)) (𝓝 (Q x)))
    -- convergence of the base family and positivity of the partition
    (hNlim : Tendsto (fun h : ℝ ↦
      ∫ x, A x * Real.exp (-(P x + V₁ h x)) ∂μ) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, A x * Real.exp (-P x) ∂μ)))
    (hZ₁lim : Tendsto (fun h : ℝ ↦
      ∫ x, Real.exp (-(P x + V₁ h x)) ∂μ) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, Real.exp (-P x) ∂μ)))
    (hZ₂lim : Tendsto (fun h : ℝ ↦
      ∫ x, Real.exp (-(P x + V₂ h x)) ∂μ) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, Real.exp (-P x) ∂μ)))
    (hZpos : 0 < ∫ x, Real.exp (-P x) ∂μ) :
    Tendsto (fun h : ℝ ↦
      ((∫ x, A x * Real.exp (-(P x + V₂ h x)) ∂μ) /
          (∫ x, Real.exp (-(P x + V₂ h x)) ∂μ) -
        (∫ x, A x * Real.exp (-(P x + V₁ h x)) ∂μ) /
          ∫ x, Real.exp (-(P x + V₁ h x)) ∂μ) / h ^ ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 (-covarianceUnder μ P A Q)) := by
  set Z0 : ℝ := ∫ x, Real.exp (-P x) ∂μ with hZ0_def
  -- the two rate limits from the unnormalized theorem
  have hrateA := tendsto_integral_exp_difference_div_pow A P V₁ V₂ ρ Q
    hmeasA hV₁ hV₂ hdiff hGA hdomA hintA₁ hintA₂
  have hrate1 := tendsto_integral_exp_difference_div_pow
    (fun _ ↦ (1 : ℝ)) P V₁ V₂ ρ Q
    hmeas1 hV₁ hV₂ hdiff hG1 hdom1 hint1₁ hint1₂
  simp only [one_mul] at hrate1
  -- eventual lower bound on the partitions
  have hZ₁low : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      Z0 / 2 ≤ ∫ x, Real.exp (-(P x + V₁ h x)) ∂μ :=
    hZ₁lim.eventually_const_le (half_lt_self hZpos)
  have hZ₂low : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      Z0 / 2 ≤ ∫ x, Real.exp (-(P x + V₂ h x)) ∂μ :=
    hZ₂lim.eventually_const_le (half_lt_self hZpos)
  -- the limit of the assembled right-hand side
  have hRHS : Tendsto (fun h : ℝ ↦
      (((∫ x, A x * Real.exp (-(P x + V₂ h x)) ∂μ) -
          ∫ x, A x * Real.exp (-(P x + V₁ h x)) ∂μ) / h ^ ρ) /
        (∫ x, Real.exp (-(P x + V₂ h x)) ∂μ) -
      ((∫ x, A x * Real.exp (-(P x + V₁ h x)) ∂μ) /
          (∫ x, Real.exp (-(P x + V₁ h x)) ∂μ)) *
        ((((∫ x, Real.exp (-(P x + V₂ h x)) ∂μ) -
            ∫ x, Real.exp (-(P x + V₁ h x)) ∂μ) / h ^ ρ) /
          ∫ x, Real.exp (-(P x + V₂ h x)) ∂μ))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((-∫ x, A x * Q x * Real.exp (-P x) ∂μ) / Z0 -
        ((∫ x, A x * Real.exp (-P x) ∂μ) / Z0) *
          ((-∫ x, Q x * Real.exp (-P x) ∂μ) / Z0))) := by
    have hQ1 : Tendsto (fun h : ℝ ↦
        (((∫ x, A x * Real.exp (-(P x + V₂ h x)) ∂μ) -
          ∫ x, A x * Real.exp (-(P x + V₁ h x)) ∂μ) / h ^ ρ) /
        ∫ x, Real.exp (-(P x + V₂ h x)) ∂μ) (𝓝[>] (0 : ℝ))
        (𝓝 ((-∫ x, A x * Q x * Real.exp (-P x) ∂μ) / Z0)) :=
      hrateA.div hZ₂lim hZpos.ne'
    have hQ2 : Tendsto (fun h : ℝ ↦
        (∫ x, A x * Real.exp (-(P x + V₁ h x)) ∂μ) /
          ∫ x, Real.exp (-(P x + V₁ h x)) ∂μ) (𝓝[>] (0 : ℝ))
        (𝓝 ((∫ x, A x * Real.exp (-P x) ∂μ) / Z0)) :=
      hNlim.div hZ₁lim hZpos.ne'
    have hQ3 : Tendsto (fun h : ℝ ↦
        (((∫ x, Real.exp (-(P x + V₂ h x)) ∂μ) -
          ∫ x, Real.exp (-(P x + V₁ h x)) ∂μ) / h ^ ρ) /
        ∫ x, Real.exp (-(P x + V₂ h x)) ∂μ) (𝓝[>] (0 : ℝ))
        (𝓝 ((-∫ x, Q x * Real.exp (-P x) ∂μ) / Z0)) :=
      hrate1.div hZ₂lim hZpos.ne'
    exact hQ1.sub (hQ2.mul hQ3)
  -- rewrite the limit value as the covariance
  have hval : (-∫ x, A x * Q x * Real.exp (-P x) ∂μ) / Z0 -
      ((∫ x, A x * Real.exp (-P x) ∂μ) / Z0) *
        ((-∫ x, Q x * Real.exp (-P x) ∂μ) / Z0) =
      -covarianceUnder μ P A Q := by
    unfold covarianceUnder expectationUnder
    rw [hZ0_def]
    ring
  rw [hval] at hRHS
  -- transfer along the eventual quotient-rate identity
  refine hRHS.congr' ?_
  filter_upwards [hZ₁low, hZ₂low, self_mem_nhdsWithin]
    with h h1 h2 hh0'
  have hh0 : (0 : ℝ) < h := hh0'
  have hZ0half : (0 : ℝ) < Z0 / 2 := by linarith
  have hZ₁ne : (∫ x, Real.exp (-(P x + V₁ h x)) ∂μ) ≠ 0 :=
    (lt_of_lt_of_le hZ0half h1).ne'
  have hZ₂ne : (∫ x, Real.exp (-(P x + V₂ h x)) ∂μ) ≠ 0 :=
    (lt_of_lt_of_le hZ0half h2).ne'
  have hhρ : (h : ℝ) ^ ρ ≠ 0 := (pow_pos hh0 ρ).ne'
  field_simp
  ring

end Laplace.Multi
