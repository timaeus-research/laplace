/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The fluctuation function (grammar paper §4)

Watanabe's *fluctuation function* (greybook, Definition 5.8), the building block
of the `Z_n[φ]` asymptotic expansion in *Expectations and the exceptional
divisor* (§4, `eq:fluctuation`):

  `S_λ(a) = ∫₀^∞ t^{λ-1} e^{-β t + β a √t} dt`,   `β, λ > 0`.

This module opens the §4 formalisation with the definition, its integrability
for every `a ∈ ℝ` (AM–GM domination `a√t ≤ t/2 + a²/2` against a Gamma
integrand), and the base value `S_λ(0) = β^{-λ} Γ(λ)`.

`lam` denotes the RLCT `λ` (`λ` is reserved syntax in Lean).
-/

open Real MeasureTheory

namespace Laplace.Grammar

/-- The **fluctuation function** `S_λ(a) = ∫₀^∞ t^{λ-1} e^{-β t + β a √t} dt`
(grammar §4 `eq:fluctuation`; Watanabe, Definition 5.8). -/
noncomputable def fluctuation (β lam a : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t)

/-- The fluctuation integrand is integrable on `(0, ∞)` for every `a` (with
`β, λ > 0`): the AM–GM bound `a√t ≤ t/2 + a²/2` gives
`e^{-βt + βa√t} ≤ e^{βa²/2} · e^{-(β/2)t}`, and the majorant
`t^{λ-1} e^{-(β/2)t}` is Gamma-integrable. -/
theorem fluctuation_integrableOn (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    IntegrableOn
      (fun t => t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t))
      (Set.Ioi (0 : ℝ)) := by
  -- Majorant: `exp(βa²/2) · (t^(λ-1) · exp(-(β/2)·t))`, Gamma-integrable at `p = 1`.
  have hmaj : IntegrableOn
      (fun t : ℝ => Real.exp (β * a ^ 2 / 2) *
        (t ^ (lam - 1) * Real.exp (-(β / 2) * t ^ (1 : ℝ)))) (Set.Ioi (0 : ℝ)) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos (by linarith)).const_mul _
  refine Integrable.mono' hmaj ?_ ?_
  · -- `AEStronglyMeasurable` of the integrand: continuous on `(0, ∞)`.
    apply ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    apply ContinuousOn.mul
    · exact continuousOn_id.rpow_const
        (fun t ht => Or.inl (ne_of_gt (Set.mem_Ioi.mp ht)))
    · exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
  · -- Pointwise domination via AM–GM `a√t ≤ t/2 + a²/2`.
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have ht0 : (0 : ℝ) < t := Set.mem_Ioi.mp ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _),
      abs_of_pos (Real.exp_pos _), Real.rpow_one,
      show Real.exp (β * a ^ 2 / 2) * (t ^ (lam - 1) * Real.exp (-(β / 2) * t))
        = t ^ (lam - 1) * (Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 2) * t)) by ring,
      ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht0.le _)
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (Real.sqrt t - a), Real.sq_sqrt ht0.le, hβ]

/-- Base value `S_λ(0) = β^{-λ} Γ(λ)` (grammar §4, remark after `eq:fluctuation`). -/
theorem fluctuation_zero (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) :
    fluctuation β lam 0 = β ^ (-lam) * Real.Gamma lam := by
  have h : fluctuation β lam 0
      = ∫ t in Set.Ioi (0 : ℝ), t ^ (lam - 1) * Real.exp (-β * t ^ (1 : ℝ)) := by
    unfold fluctuation
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [mul_zero, zero_mul, add_zero, Real.rpow_one]
  rw [h, integral_rpow_mul_exp_neg_mul_rpow one_pos (by linarith) hβ,
    show -(lam - 1 + 1) / 1 = -lam by ring, show (lam - 1 + 1) / 1 = lam by ring]
  simp

/-- Property (i): `S'_λ(a) = β · S_{λ+1/2}(a)` (grammar §4 `lem:fluctuation_properties`).
Differentiate under the integral: the `a`-derivative of the phase `-βt + βa√t` is `β√t`, and
`t^{λ-1}·√t = t^{(λ+1/2)-1}`, so the derivative integral is `β · S_{λ+1/2}`. -/
theorem hasDerivAt_fluctuation (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    HasDerivAt (fun a => fluctuation β lam a) (β * fluctuation β (lam + 1 / 2) a) a := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  let F : ℝ → ℝ → ℝ := fun b t => t ^ (lam - 1) * Real.exp (-β * t + β * b * Real.sqrt t)
  let G : ℝ → ℝ → ℝ := fun b t =>
    t ^ ((lam + 1 / 2) - 1) * Real.exp (-β * t + β * b * Real.sqrt t)
  let D : ℝ → ℝ → ℝ := fun b t => β * G b t
  have hFi : ∀ b, Integrable (F b) μ := fun b => fluctuation_integrableOn β lam hβ hlam b
  have hDi : ∀ b, Integrable (D b) μ := fun b =>
    (fluctuation_integrableOn β (lam + 1 / 2) hβ (by linarith) b).const_mul β
  -- Pointwise derivative in the parameter `b`, normalised to the shifted integrand `D`.
  have hpoint : ∀ t, 0 < t → ∀ b, HasDerivAt (fun b => F b t) (D b t) b := by
    intro t ht b
    have hphase : HasDerivAt (fun b : ℝ => -β * t + β * b * Real.sqrt t) (β * Real.sqrt t) b := by
      simpa using ((((hasDerivAt_id b).const_mul β).mul_const (Real.sqrt t)).const_add (-β * t))
    have hpow : t ^ (lam - 1) * Real.sqrt t = t ^ (lam + 1 / 2 - 1) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]; congr 1; ring
    have hraw := (hphase.exp).const_mul (t ^ (lam - 1))
    have hval : t ^ (lam - 1) * (Real.exp (-β * t + β * b * Real.sqrt t) * (β * Real.sqrt t))
        = D b t := by
      change _ = β * (t ^ (lam + 1 / 2 - 1) * Real.exp (-β * t + β * b * Real.sqrt t))
      rw [← hpow]; ring
    rwa [hval] at hraw
  have hpos : ∀ᵐ t ∂μ, 0 < t := ae_restrict_mem measurableSet_Ioi
  have hFmeas : ∀ᶠ b in nhds a, AEStronglyMeasurable (F b) μ :=
    Filter.Eventually.of_forall fun b => (hFi b).aestronglyMeasurable
  -- Uniform domination on `ball a 1`: the derivative integrand increases in `b`.
  have hbound : ∀ᵐ t ∂μ, ∀ b ∈ Metric.ball a 1, ‖D b t‖ ≤ D (a + 1) t := by
    filter_upwards [hpos] with t ht b hb
    have hb' : b ≤ a + 1 := by
      have habs : |b - a| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hb
      have := (abs_lt.mp habs).2; linarith
    have hphase : -β * t + β * b * Real.sqrt t ≤ -β * t + β * (a + 1) * Real.sqrt t := by
      have hmul : β * b * Real.sqrt t ≤ β * (a + 1) * Real.sqrt t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb' hβ.le) (Real.sqrt_nonneg t)
      linarith
    have hexp := Real.exp_le_exp.mpr hphase
    have hDnn : 0 ≤ D b t := by
      change 0 ≤ β * (t ^ (lam + 1 / 2 - 1) * Real.exp (-β * t + β * b * Real.sqrt t))
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hDnn]
    change β * (t ^ (lam + 1 / 2 - 1) * Real.exp (-β * t + β * b * Real.sqrt t))
      ≤ β * (t ^ (lam + 1 / 2 - 1) * Real.exp (-β * t + β * (a + 1) * Real.sqrt t))
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg ht.le _)) hβ.le
  have hdiff : ∀ᵐ t ∂μ, ∀ b ∈ Metric.ball a 1, HasDerivAt (fun b => F b t) (D b t) b := by
    filter_upwards [hpos] with t ht b _
    exact hpoint t ht b
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := D)
    (x₀ := a) (bound := D (a + 1)) (s := Metric.ball a 1)
    (Metric.ball_mem_nhds a one_pos) hFmeas (hFi a)
    (hDi a).aestronglyMeasurable hbound (hDi (a + 1)) hdiff
  have h2 := h.2
  have hkey : (∫ t, D a t ∂μ) = β * fluctuation β (lam + 1 / 2) a := integral_const_mul β (G a)
  rw [hkey] at h2
  exact h2

/-- Property (i) in `deriv` form. -/
theorem deriv_fluctuation (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    deriv (fun a => fluctuation β lam a) a = β * fluctuation β (lam + 1 / 2) a :=
  (hasDerivAt_fluctuation β lam hβ hlam a).deriv

/-- Property (ii): `S''_λ(a) = β² · S_{λ+1}(a)` (grammar §4 `lem:fluctuation_properties`),
obtained by applying (i) at `λ` and again at `λ + 1/2`. -/
theorem hasDerivAt_deriv_fluctuation (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    HasDerivAt (fun a => β * fluctuation β (lam + 1 / 2) a)
      (β ^ 2 * fluctuation β (lam + 1) a) a := by
  have h := (hasDerivAt_fluctuation β (lam + 1 / 2) hβ (by linarith) a).const_mul β
  rw [show lam + 1 / 2 + 1 / 2 = lam + 1 by ring,
    show β * (β * fluctuation β (lam + 1) a) = β ^ 2 * fluctuation β (lam + 1) a by ring] at h
  exact h

/-- The integration-by-parts recurrence (grammar §4 `eq:fluctuation_recurrence`):
`S_{λ+1}(a) = (a/2)·S_{λ+1/2}(a) + (λ/β)·S_λ(a)`, from `∫₀^∞ d/dt[t^λ e^{phase}] = 0`. -/
theorem fluctuation_recurrence (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    fluctuation β (lam + 1) a
      = (a / 2) * fluctuation β (lam + 1 / 2) a + (lam / β) * fluctuation β lam a := by
  set e : ℝ → ℝ := fun t => Real.exp (-β * t + β * a * Real.sqrt t) with he_def
  -- `g t = t^λ e^{phase}`; its derivative `D` decomposed with exponents matching `fluctuation`.
  let g : ℝ → ℝ := fun t => t ^ lam * e t
  let D : ℝ → ℝ := fun t =>
    lam * (t ^ (lam - 1) * e t) - β * (t ^ (lam + 1 - 1) * e t)
      + (β * a / 2) * (t ^ (lam + 1 / 2 - 1) * e t)
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt g (D t) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hpow : HasDerivAt (fun t : ℝ => t ^ lam) (lam * t ^ (lam - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht0.ne')
    have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt t)) t := Real.hasDerivAt_sqrt ht0.ne'
    have h1 : HasDerivAt (fun t : ℝ => -β * t) (-β) t := by
      simpa using (hasDerivAt_id t).const_mul (-β)
    have h2 : HasDerivAt (fun t : ℝ => β * a * Real.sqrt t) (β * a * (1 / (2 * Real.sqrt t))) t :=
      hsqrt.const_mul (β * a)
    have hph : HasDerivAt (fun t : ℝ => -β * t + β * a * Real.sqrt t)
        (-β + β * a * (1 / (2 * Real.sqrt t))) t := h1.add h2
    have he : HasDerivAt e (e t * (-β + β * a * (1 / (2 * Real.sqrt t)))) t := hph.exp
    have hg := hpow.mul he
    have hsq : Real.sqrt t = t ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow t
    have hA : t ^ (lam + 1 - 1) = t ^ lam := by rw [show lam + 1 - 1 = lam by ring]
    have hII : t ^ (lam + 1 / 2 - 1) = t ^ lam * (Real.sqrt t)⁻¹ := by
      rw [hsq, ← Real.rpow_neg ht0.le, ← Real.rpow_add ht0]; congr 1; ring
    have hval : lam * t ^ (lam - 1) * e t
        + t ^ lam * (e t * (-β + β * a * (1 / (2 * Real.sqrt t)))) = D t := by
      change _ = lam * (t ^ (lam - 1) * e t) - β * (t ^ (lam + 1 - 1) * e t)
        + β * a / 2 * (t ^ (lam + 1 / 2 - 1) * e t)
      rw [hA, hII]; ring
    exact hval ▸ hg
  -- Boundary continuity at 0: `g 0 = 0` for `λ > 0`.
  have hcont : ContinuousWithinAt g (Set.Ici 0) 0 := by
    have hce : Continuous e := by rw [he_def]; fun_prop
    have hcp : ContinuousWithinAt (fun t : ℝ => t ^ lam) (Set.Ici 0) 0 :=
      (continuousAt_rpow_const 0 lam (Or.inr hlam.le)).continuousWithinAt
    exact hcp.mul hce.continuousWithinAt
  -- `t^λ e^{phase} → 0` at `atTop` (super-polynomial decay of the phase).
  have htop : Filter.Tendsto g Filter.atTop (nhds 0) := by
    have hmaj : Filter.Tendsto (fun t : ℝ => Real.exp (β * a ^ 2 / 2) * (t ^ lam *
        Real.exp (-(β / 2) * t))) Filter.atTop (nhds 0) := by
      have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero lam (β / 2) (by linarith)).const_mul
        (Real.exp (β * a ^ 2 / 2))
      simpa using this
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht0
      exact mul_nonneg (Real.rpow_nonneg ht0.le lam) (by rw [he_def]; exact (Real.exp_pos _).le)
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht0
      have hexp : Real.exp (-β * t + β * a * Real.sqrt t)
          ≤ Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 2) * t) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg (Real.sqrt t - a), Real.sq_sqrt ht0.le]
      calc g t = t ^ lam * e t := rfl
        _ ≤ Real.exp (β * a ^ 2 / 2) * (t ^ lam * Real.exp (-(β / 2) * t)) := by
            rw [he_def]; nlinarith [Real.rpow_nonneg ht0.le lam, hexp, Real.exp_pos
              (-β * t + β * a * Real.sqrt t)]
  have hDint : IntegrableOn D (Set.Ioi 0) := by
    have h0 := fluctuation_integrableOn β lam hβ hlam a
    have h1 := fluctuation_integrableOn β (lam + 1) hβ (by linarith) a
    have hh := fluctuation_integrableOn β (lam + 1 / 2) hβ (by linarith) a
    exact ((h0.const_mul lam).sub (h1.const_mul β)).add (hh.const_mul (β * a / 2))
  have hg0 : g 0 = 0 := by
    simp only [g, Real.zero_rpow hlam.ne', zero_mul]
  have hFTC : (∫ t in Set.Ioi (0 : ℝ), D t) = 0 := by
    have := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hDint htop
    rwa [hg0, sub_zero] at this
  -- Decompose the integral into the three fluctuation values.
  have hsplit : (∫ t in Set.Ioi (0 : ℝ), D t)
      = lam * fluctuation β lam a - β * fluctuation β (lam + 1) a
        + (β * a / 2) * fluctuation β (lam + 1 / 2) a := by
    have h0 : IntegrableOn (fun t => t ^ (lam - 1) * e t) (Set.Ioi 0) := by
      rw [he_def]; exact fluctuation_integrableOn β lam hβ hlam a
    have h1 : IntegrableOn (fun t => t ^ (lam + 1 - 1) * e t) (Set.Ioi 0) := by
      rw [he_def]; exact fluctuation_integrableOn β (lam + 1) hβ (by linarith) a
    have hh : IntegrableOn (fun t => t ^ (lam + 1 / 2 - 1) * e t) (Set.Ioi 0) := by
      rw [he_def]; exact fluctuation_integrableOn β (lam + 1 / 2) hβ (by linarith) a
    have hDe : D = fun t => lam * (t ^ (lam - 1) * e t) - β * (t ^ (lam + 1 - 1) * e t)
        + β * a / 2 * (t ^ (lam + 1 / 2 - 1) * e t) := rfl
    have ia : IntegrableOn (fun t => lam * (t ^ (lam - 1) * e t)
        - β * (t ^ (lam + 1 - 1) * e t)) (Set.Ioi 0) := (h0.const_mul lam).sub (h1.const_mul β)
    have ib : IntegrableOn (fun t => β * a / 2 * (t ^ (lam + 1 / 2 - 1) * e t)) (Set.Ioi 0) :=
      hh.const_mul (β * a / 2)
    rw [hDe, integral_add ia ib, integral_sub (h0.const_mul lam) (h1.const_mul β),
      integral_const_mul, integral_const_mul, integral_const_mul]
    rfl
  rw [hFTC] at hsplit
  have hβ' : β ≠ 0 := hβ.ne'
  field_simp at hsplit ⊢
  linarith [hsplit]

/-- Property (iii) (grammar §4 `lem:fluctuation_properties`): the second-order ODE
`S''_λ = (aβ/2)·S'_λ + λβ·S_λ`, i.e. `β²S_{λ+1} = (aβ/2)(βS_{λ+1/2}) + λβ S_λ`. -/
theorem fluctuation_ode (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    β ^ 2 * fluctuation β (lam + 1) a
      = (a * β / 2) * (β * fluctuation β (lam + 1 / 2) a) + lam * β * fluctuation β lam a := by
  rw [fluctuation_recurrence β lam hβ hlam a]
  field_simp

end Laplace.Grammar
