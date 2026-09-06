/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LogInsertions

/-!
# The log-insertion ODE (grammar §4 `prop:LogODE`)

Writing `g_k(a) = ∂_λ^k S_λ(a) = ∫₀^∞ (log t)^k t^{ν-1} e^{-βt+βa√t} dt` (at order `ν`, via
`iteratedDeriv_fluctuation_order`), the Weber ODE differentiated `k` times in the order gives

  `g_k''(a) - (βa/2) g_k'(a) - νβ g_k(a) = kβ g_{k-1}(a)`.

We prove this directly for the integral `gLog`, from an `a`-derivative ladder
`∂_a gLog(ν,k) = β gLog(ν+½,k)` and a log-weighted integration-by-parts recurrence (the same
improper FTC as `fluctuation_recurrence`, with the extra `k(log t)^{k-1}` term produced by
differentiating the log weight).
-/

open Real MeasureTheory

namespace Laplace.Grammar

/-- The log-weighted fluctuation integral `g_k(a) = ∫₀^∞ (log t)^k t^{ν-1} e^{-βt+βa√t} dt`; equals
`∂_λ^k S_λ(a)` at order `ν` by `iteratedDeriv_fluctuation_order`. -/
noncomputable def gLog (β a ν : ℝ) (k : ℕ) : ℝ :=
  ∫ t in Set.Ioi 0, (Real.log t) ^ k * t ^ (ν - 1) * Real.exp (-β * t + β * a * Real.sqrt t)

/-- Signed integrand of `gLog` is integrable (norm dominated by the `|log|^k`-weighted
integrand). -/
theorem gLog_integrable (β a ν : ℝ) (k : ℕ) (hβ : 0 < β) (hν : 0 < ν) :
    IntegrableOn (fun t => (Real.log t) ^ k * t ^ (ν - 1) * Real.exp (-β * t + β * a * Real.sqrt t))
      (Set.Ioi 0) := by
  refine (log_pow_fluctuation_integrableOn β ν a k hβ hν).mono' ?_ ?_
  · exact (by fun_prop : Measurable (fun t => (Real.log t) ^ k * t ^ (ν - 1)
      * Real.exp (-β * t + β * a * Real.sqrt t))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
      abs_of_pos (Real.rpow_pos_of_pos ht _), abs_of_pos (Real.exp_pos _)]

/-- **`a`-derivative ladder** for the log-weighted integral: `∂_a gLog(ν,k) = β gLog(ν+½,k)`. -/
theorem hasDerivAt_gLog (β ν : ℝ) (k : ℕ) (hβ : 0 < β) (hν : 0 < ν) (a : ℝ) :
    HasDerivAt (fun a => gLog β a ν k) (β * gLog β a (ν + 1 / 2) k) a := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  let F : ℝ → ℝ → ℝ := fun b t =>
    (Real.log t) ^ k * t ^ (ν - 1) * Real.exp (-β * t + β * b * Real.sqrt t)
  let D : ℝ → ℝ → ℝ := fun b t =>
    β * ((Real.log t) ^ k * t ^ (ν + 1 / 2 - 1) * Real.exp (-β * t + β * b * Real.sqrt t))
  have hFi : ∀ b, Integrable (F b) μ := fun b => gLog_integrable β b ν k hβ hν
  have hpoint : ∀ t, 0 < t → ∀ b, HasDerivAt (fun b => F b t) (D b t) b := by
    intro t ht b
    have hphase : HasDerivAt (fun b : ℝ => -β * t + β * b * Real.sqrt t) (β * Real.sqrt t) b := by
      simpa using ((((hasDerivAt_id b).const_mul β).mul_const (Real.sqrt t)).const_add (-β * t))
    have hpow : t ^ (ν - 1) * Real.sqrt t = t ^ (ν + 1 / 2 - 1) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]; congr 1; ring
    have hraw := (hphase.exp).const_mul ((Real.log t) ^ k * t ^ (ν - 1))
    have hval : (Real.log t) ^ k * t ^ (ν - 1)
        * (Real.exp (-β * t + β * b * Real.sqrt t) * (β * Real.sqrt t)) = D b t := by
      change _ = β * ((Real.log t) ^ k * t ^ (ν + 1 / 2 - 1)
        * Real.exp (-β * t + β * b * Real.sqrt t))
      rw [← hpow]; ring
    rwa [hval] at hraw
  have hpos : ∀ᵐ t ∂μ, 0 < t := ae_restrict_mem measurableSet_Ioi
  have hFmeas : ∀ᶠ b in nhds a, AEStronglyMeasurable (F b) μ :=
    Filter.Eventually.of_forall fun b => (hFi b).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μ, ∀ b ∈ Metric.ball a 1,
      ‖D b t‖ ≤ β * (|Real.log t| ^ k * t ^ (ν + 1 / 2 - 1)
        * Real.exp (-β * t + β * (a + 1) * Real.sqrt t)) := by
    filter_upwards [hpos] with t ht b hb
    have ht0 : (0 : ℝ) < t := ht
    have hb' : b ≤ a + 1 := by
      have habs : |b - a| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hb
      have := (abs_lt.mp habs).2; linarith
    have hexp : Real.exp (-β * t + β * b * Real.sqrt t)
        ≤ Real.exp (-β * t + β * (a + 1) * Real.sqrt t) := by
      apply Real.exp_le_exp.mpr
      have : β * b * Real.sqrt t ≤ β * (a + 1) * Real.sqrt t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb' hβ.le) (Real.sqrt_nonneg t)
      linarith
    rw [Real.norm_eq_abs,
      show D b t = β * ((Real.log t) ^ k * t ^ (ν + 1 / 2 - 1)
        * Real.exp (-β * t + β * b * Real.sqrt t)) from rfl,
      abs_mul, abs_of_pos hβ, abs_mul, abs_mul, abs_pow,
      abs_of_pos (Real.rpow_pos_of_pos ht0 _), abs_of_pos (Real.exp_pos _)]
    gcongr
  have hDaux : Integrable (fun t => β * (|Real.log t| ^ k * t ^ (ν + 1 / 2 - 1)
      * Real.exp (-β * t + β * (a + 1) * Real.sqrt t))) μ :=
    (log_pow_fluctuation_integrableOn β (ν + 1 / 2) (a + 1) k hβ (by linarith)).const_mul β
  have hdiff : ∀ᵐ t ∂μ, ∀ b ∈ Metric.ball a 1, HasDerivAt (fun b => F b t) (D b t) b := by
    filter_upwards [hpos] with t ht b _
    exact hpoint t ht b
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := D)
    (x₀ := a) (bound := fun t => β * (|Real.log t| ^ k * t ^ (ν + 1 / 2 - 1)
      * Real.exp (-β * t + β * (a + 1) * Real.sqrt t))) (s := Metric.ball a 1)
    (Metric.ball_mem_nhds a one_pos) hFmeas (hFi a)
    ((by fun_prop : Measurable (fun t => β * ((Real.log t) ^ k * t ^ (ν + 1 / 2 - 1)
      * Real.exp (-β * t + β * a * Real.sqrt t)))).aestronglyMeasurable) hbound hDaux hdiff
  have h2 := h.2
  have hkey : (∫ t, D a t ∂μ) = β * gLog β a (ν + 1 / 2) k := by
    rw [gLog]; exact integral_const_mul β _
  rw [hkey] at h2
  exact h2

/-- **Log-weighted recurrence** (grammar §4, from `∫₀^∞ ∂_t[t^ν (log t)^k e^{-βt+βa√t}] dt = 0`):
`β gLog(ν+1,k) = (βa/2) gLog(ν+½,k) + ν gLog(ν,k) + k gLog(ν,k-1)`. -/
theorem gLog_recurrence (β a ν : ℝ) (k : ℕ) (hβ : 0 < β) (hν : 0 < ν) :
    β * gLog β a (ν + 1) k
      = (β * a / 2) * gLog β a (ν + 1 / 2) k + ν * gLog β a ν k
        + (k : ℝ) * gLog β a ν (k - 1) := by
  set e : ℝ → ℝ := fun t => Real.exp (-β * t + β * a * Real.sqrt t) with he_def
  let g : ℝ → ℝ := fun t => t ^ ν * (Real.log t) ^ k * e t
  let D : ℝ → ℝ := fun t =>
    ν * ((Real.log t) ^ k * t ^ (ν - 1) * e t)
      + (k : ℝ) * ((Real.log t) ^ (k - 1) * t ^ (ν - 1) * e t)
      - β * ((Real.log t) ^ k * t ^ (ν + 1 - 1) * e t)
      + (β * a / 2) * ((Real.log t) ^ k * t ^ (ν + 1 / 2 - 1) * e t)
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt g (D t) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hpow : HasDerivAt (fun t : ℝ => t ^ ν) (ν * t ^ (ν - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht0.ne')
    have hlogk : HasDerivAt (fun t : ℝ => (Real.log t) ^ k)
        ((k : ℝ) * (Real.log t) ^ (k - 1) * t⁻¹) t :=
      (Real.hasDerivAt_log ht0.ne').pow k
    have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt t)) t := Real.hasDerivAt_sqrt ht0.ne'
    have hph : HasDerivAt (fun t : ℝ => -β * t + β * a * Real.sqrt t)
        (-β + β * a * (1 / (2 * Real.sqrt t))) t := by
      have h1 : HasDerivAt (fun t : ℝ => -β * t) (-β) t := by
        simpa using (hasDerivAt_id t).const_mul (-β)
      exact h1.add (hsqrt.const_mul (β * a))
    have he : HasDerivAt e (e t * (-β + β * a * (1 / (2 * Real.sqrt t)))) t := hph.exp
    have hg := ((hpow.mul hlogk).mul he)
    have hsq : Real.sqrt t = t ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow t
    have hA : t ^ (ν + 1 - 1) = t ^ ν := by rw [show ν + 1 - 1 = ν by ring]
    have hB : t ^ ν * t⁻¹ = t ^ (ν - 1) := by
      rw [show (t⁻¹ : ℝ) = t ^ (-1 : ℝ) by rw [Real.rpow_neg ht0.le, Real.rpow_one],
        ← Real.rpow_add ht0, show ν + -1 = ν - 1 by ring]
    have hII : t ^ ν * (1 / (2 * Real.sqrt t)) = (1 / 2) * t ^ (ν + 1 / 2 - 1) := by
      have h : t ^ ν * (Real.sqrt t)⁻¹ = t ^ (ν + 1 / 2 - 1) := by
        rw [hsq, ← Real.rpow_neg ht0.le, ← Real.rpow_add ht0]; congr 1; ring
      rw [show t ^ ν * (1 / (2 * Real.sqrt t)) = (1 / 2) * (t ^ ν * (Real.sqrt t)⁻¹) by ring, h]
    have hval : (ν * t ^ (ν - 1) * (Real.log t) ^ k
          + t ^ ν * ((k : ℝ) * (Real.log t) ^ (k - 1) * t⁻¹)) * e t
        + t ^ ν * (Real.log t) ^ k * (e t * (-β + β * a * (1 / (2 * Real.sqrt t)))) = D t := by
      change _ = ν * ((Real.log t) ^ k * t ^ (ν - 1) * e t)
        + (k : ℝ) * ((Real.log t) ^ (k - 1) * t ^ (ν - 1) * e t)
        - β * ((Real.log t) ^ k * t ^ (ν + 1 - 1) * e t)
        + (β * a / 2) * ((Real.log t) ^ k * t ^ (ν + 1 / 2 - 1) * e t)
      rw [hA]
      rw [show t ^ ν * ((k : ℝ) * (Real.log t) ^ (k - 1) * t⁻¹)
          = (k : ℝ) * (Real.log t) ^ (k - 1) * (t ^ ν * t⁻¹) by ring, hB]
      rw [show t ^ ν * (Real.log t) ^ k * (e t * (-β + β * a * (1 / (2 * Real.sqrt t))))
          = -β * ((Real.log t) ^ k * t ^ ν * e t)
            + β * a * ((Real.log t) ^ k * (t ^ ν * (1 / (2 * Real.sqrt t))) * e t) by ring, hII]
      ring
    exact hval ▸ hg
  have hg0 : g 0 = 0 := by simp only [g, Real.zero_rpow hν.ne', zero_mul]
  set bnd : ℝ → ℝ := fun t => Real.exp (β * a ^ 2 / 2) * (↑k / (ν / 2)) ^ k
    * (t ^ (3 * ν / 2) + t ^ (ν / 2)) * Real.exp (-(β / 2) * t) with hbnd_def
  have hbnd00 : bnd 0 = 0 := by
    simp only [bnd, Real.zero_rpow (by positivity : (3 * ν / 2 : ℝ) ≠ 0),
      Real.zero_rpow (by positivity : (ν / 2 : ℝ) ≠ 0)]; ring
  have hgbnd : ∀ t : ℝ, 0 ≤ t → ‖g t‖ ≤ bnd t := by
    intro t ht
    rcases eq_or_lt_of_le ht with h0 | ht0
    · rw [← h0, hg0, hbnd00, norm_zero]
    · have hlog := abs_log_pow_le t (ν / 2) k ht0 (by positivity)
      have hamgm : β * a * Real.sqrt t ≤ β / 2 * t + β / 2 * a ^ 2 := by
        nlinarith [sq_nonneg (Real.sqrt t - a), Real.sq_sqrt ht0.le, Real.sqrt_nonneg t]
      have hexp : e t ≤ Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 2) * t) := by
        rw [he_def, ← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [hamgm]
      have hr1 : t ^ (ν / 2) * t ^ ν = t ^ (3 * ν / 2) := by
        rw [← Real.rpow_add ht0]; congr 1; ring
      have hr2 : t ^ (-(ν / 2)) * t ^ ν = t ^ (ν / 2) := by
        rw [← Real.rpow_add ht0]; congr 1; ring
      have hepos : (0 : ℝ) < e t := by rw [he_def]; exact Real.exp_pos _
      rw [Real.norm_eq_abs,
        show g t = (Real.log t) ^ k * (t ^ ν * e t) by simp only [g]; ring,
        abs_mul, abs_pow, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _), abs_of_pos hepos]
      calc |Real.log t| ^ k * (t ^ ν * e t)
          ≤ ((↑k / (ν / 2)) ^ k * (t ^ (ν / 2) + t ^ (-(ν / 2)))) * (t ^ ν
              * (Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 2) * t))) := by gcongr
        _ = bnd t := by
              rw [hbnd_def]
              linear_combination
                (Real.exp (β * a ^ 2 / 2) * (↑k / (ν / 2)) ^ k * Real.exp (-(β / 2) * t)) * hr1
                + (Real.exp (β * a ^ 2 / 2) * (↑k / (ν / 2)) ^ k * Real.exp (-(β / 2) * t)) * hr2
  have hbndeq : bnd = fun t => (Real.exp (β * a ^ 2 / 2) * (↑k / (ν / 2)) ^ k)
      * (t ^ (3 * ν / 2) * Real.exp (-(β / 2) * t) + t ^ (ν / 2) * Real.exp (-(β / 2) * t)) := by
    funext t; simp only [hbnd_def]; ring
  have hbndT : Filter.Tendsto bnd Filter.atTop (nhds 0) := by
    rw [hbndeq]
    have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 * ν / 2) (β / 2) (by linarith)
    have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (ν / 2) (β / 2) (by linarith)
    simpa using (h1.add h2).const_mul (Real.exp (β * a ^ 2 / 2) * (↑k / (ν / 2)) ^ k)
  have hbnd0 : Filter.Tendsto bnd (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by
    have hc : ContinuousWithinAt bnd (Set.Ici 0) 0 := by
      apply ContinuousWithinAt.mul _ (Real.continuous_exp.comp (by fun_prop)).continuousWithinAt
      apply ContinuousWithinAt.mul continuousWithinAt_const
      exact
        ((continuousAt_rpow_const 0 (3 * ν / 2) (Or.inr (by positivity))).continuousWithinAt).add
          ((continuousAt_rpow_const 0 (ν / 2) (Or.inr (by positivity))).continuousWithinAt)
    have := hc.tendsto
    rwa [hbnd00] at this
  have hcont : ContinuousWithinAt g (Set.Ici 0) 0 := by
    rw [ContinuousWithinAt, hg0]
    refine squeeze_zero_norm' ?_ hbnd0
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hgbnd t ht
  have htop : Filter.Tendsto g Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hbndT
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact hgbnd t ht
  have hDint : IntegrableOn D (Set.Ioi 0) := by
    have I1 := gLog_integrable β a ν k hβ hν
    have I2 := gLog_integrable β a ν (k - 1) hβ hν
    have I3 := gLog_integrable β a (ν + 1) k hβ (by linarith)
    have I4 := gLog_integrable β a (ν + 1 / 2) k hβ (by linarith)
    exact (((I1.const_mul ν).add (I2.const_mul (k : ℝ))).sub (I3.const_mul β)).add
      (I4.const_mul (β * a / 2))
  have hFTC : (∫ t in Set.Ioi (0 : ℝ), D t) = 0 := by
    have := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hDint htop
    rwa [hg0, sub_zero] at this
  have hsplit : (∫ t in Set.Ioi (0 : ℝ), D t)
      = ν * gLog β a ν k + (k : ℝ) * gLog β a ν (k - 1) - β * gLog β a (ν + 1) k
        + (β * a / 2) * gLog β a (ν + 1 / 2) k := by
    have I1 := gLog_integrable β a ν k hβ hν
    have I2 := gLog_integrable β a ν (k - 1) hβ hν
    have I3 := gLog_integrable β a (ν + 1) k hβ (by linarith)
    have I4 := gLog_integrable β a (ν + 1 / 2) k hβ (by linarith)
    have hDe : D = fun t =>
        ν * ((Real.log t) ^ k * t ^ (ν - 1) * Real.exp (-β * t + β * a * Real.sqrt t))
        + (k : ℝ) * ((Real.log t) ^ (k - 1) * t ^ (ν - 1) * Real.exp (-β * t + β * a * Real.sqrt t))
        - β * ((Real.log t) ^ k * t ^ (ν + 1 - 1) * Real.exp (-β * t + β * a * Real.sqrt t))
        + (β * a / 2) * ((Real.log t) ^ k * t ^ (ν + 1 / 2 - 1)
          * Real.exp (-β * t + β * a * Real.sqrt t)) := rfl
    have h12 : IntegrableOn (fun t => ν * ((Real.log t) ^ k * t ^ (ν - 1)
          * Real.exp (-β * t + β * a * Real.sqrt t))
        + (k : ℝ) * ((Real.log t) ^ (k - 1) * t ^ (ν - 1)
          * Real.exp (-β * t + β * a * Real.sqrt t))) (Set.Ioi 0) :=
      (I1.const_mul ν).add (I2.const_mul (k : ℝ))
    have h123 : IntegrableOn (fun t => (ν * ((Real.log t) ^ k * t ^ (ν - 1)
          * Real.exp (-β * t + β * a * Real.sqrt t))
        + (k : ℝ) * ((Real.log t) ^ (k - 1) * t ^ (ν - 1)
          * Real.exp (-β * t + β * a * Real.sqrt t)))
        - β * ((Real.log t) ^ k * t ^ (ν + 1 - 1)
          * Real.exp (-β * t + β * a * Real.sqrt t))) (Set.Ioi 0) :=
      h12.sub (I3.const_mul β)
    rw [hDe, integral_add h123 (I4.const_mul (β * a / 2)), integral_sub h12 (I3.const_mul β),
      integral_add (I1.const_mul ν) (I2.const_mul (k : ℝ)),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
    rfl
  rw [hFTC] at hsplit
  have hβ' : β ≠ 0 := hβ.ne'
  linarith [hsplit]

/-- **The log-insertion ODE** (grammar §4 `prop:LogODE`): the log-weighted fluctuation integral
`g_k(a) = gLog β a ν k = ∂_λ^k S_λ(a)` satisfies
`g_k''(a) - (βa/2) g_k'(a) - νβ g_k(a) = kβ g_{k-1}(a)`. -/
theorem gLog_ode (β a ν : ℝ) (k : ℕ) (hβ : 0 < β) (hν : 0 < ν) :
    deriv (deriv (fun a => gLog β a ν k)) a - (β * a / 2) * deriv (fun a => gLog β a ν k) a
      - ν * β * gLog β a ν k = (k : ℝ) * β * gLog β a ν (k - 1) := by
  have hd1 : deriv (fun a => gLog β a ν k) = fun a => β * gLog β a (ν + 1 / 2) k :=
    funext fun a => (hasDerivAt_gLog β ν k hβ hν a).deriv
  have hd2 : deriv (deriv (fun a => gLog β a ν k)) a = β * (β * gLog β a (ν + 1) k) := by
    rw [hd1]
    have : HasDerivAt (fun a => β * gLog β a (ν + 1 / 2) k)
        (β * (β * gLog β a (ν + 1 / 2 + 1 / 2) k)) a :=
      (hasDerivAt_gLog β (ν + 1 / 2) k hβ (by linarith) a).const_mul β
    rw [show ν + 1 / 2 + 1 / 2 = ν + 1 by ring] at this
    exact this.deriv
  rw [hd2, hd1]
  have hrec := gLog_recurrence β a ν k hβ hν
  nlinarith [hrec]

end Laplace.Grammar
