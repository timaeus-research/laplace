/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.Fluctuation

/-!
# The log-insertion generating function (grammar §4 `lem:log_generating`)

Summing the log-shift operator against `z^p/p!` gives the generating function

  `∑_{p≥0} (z^p/p!) ∫₀^∞ t^{ν-1}(c-log t)^p e^{-βt+βa√t} dt = e^{zc} S_{ν-z}(a)`,

i.e. `∑ (z^p/p!)(c-∂_ν)^p S_ν = e^{zc} S_{ν-z}` (Taylor's theorem in the order: `e^{-z∂_ν}S_ν
= S_{ν-z}`). We prove it for `|z| < ν` by interchanging the exponential series with the integral
(`hasSum_integral_of_dominated_convergence`), dominated by `e^{|z||c-log t|} t^{ν-1} e^{-βt+βa√t}`.
-/

open Real MeasureTheory

namespace Laplace.Grammar

/-- `e^{|z||log t|} ≤ t^{|z|} + t^{-|z|}` for `t > 0`. -/
private theorem exp_absz_abs_log_le (z t : ℝ) (ht : 0 < t) :
    Real.exp (|z| * |Real.log t|) ≤ t ^ |z| + t ^ (-|z|) := by
  rcases le_or_gt 1 t with h1 | h1
  · rw [abs_of_nonneg (Real.log_nonneg h1),
      show |z| * Real.log t = Real.log t * |z| by ring, Real.exp_mul, Real.exp_log ht]
    have : (0 : ℝ) ≤ t ^ (-|z|) := (Real.rpow_pos_of_pos ht _).le; linarith
  · rw [abs_of_neg (Real.log_neg ht h1),
      show |z| * -Real.log t = Real.log t * -|z| by ring, Real.exp_mul, Real.exp_log ht]
    have : (0 : ℝ) ≤ t ^ |z| := (Real.rpow_pos_of_pos ht _).le; linarith

/-- **The log-insertion generating function** (grammar §4 `lem:log_generating`), for `|z| < ν`:
`∑_{p} (z^p/p!) ∫₀^∞ t^{ν-1}(c-log t)^p e^{-βt+βa√t} dt = e^{zc} S_{ν-z}(a)`. The `p`-th integral is
`(c-∂_ν)^p S_ν` (by `fluctuation_log_shift`), so this is
`∑ (z^p/p!)(c-∂_ν)^p S_ν = e^{zc} S_{ν-z}`. -/
theorem fluctuation_log_generating (β a c z ν : ℝ) (hβ : 0 < β) (hz : |z| < ν) :
    HasSum (fun p : ℕ => (z ^ p / p.factorial)
        * ∫ t in Set.Ioi 0,
            (c - Real.log t) ^ p * t ^ (ν - 1) * Real.exp (-β * t + β * a * Real.sqrt t))
      (Real.exp (z * c) * fluctuation β (ν - z) a) := by
  set μ : Measure ℝ := volume.restrict (Set.Ioi 0) with hμ
  set e : ℝ → ℝ := fun t => Real.exp (-β * t + β * a * Real.sqrt t) with he
  have hνpos : 0 < ν := lt_of_le_of_lt (abs_nonneg z) hz
  -- integrand family and its dominating bound
  let F : ℕ → ℝ → ℝ := fun p t => z ^ p / p.factorial * (c - Real.log t) ^ p * t ^ (ν - 1) * e t
  let bound : ℕ → ℝ → ℝ := fun p t =>
    (|z| * |c - Real.log t|) ^ p / p.factorial * (t ^ (ν - 1) * e t)
  let f : ℝ → ℝ := fun t => Real.exp (z * (c - Real.log t)) * t ^ (ν - 1) * e t
  -- measurability
  have hF_meas : ∀ p, AEStronglyMeasurable (F p) μ := fun p =>
    (by fun_prop : Measurable (fun t => z ^ p / p.factorial * (c - Real.log t) ^ p * t ^ (ν - 1)
      * Real.exp (-β * t + β * a * Real.sqrt t))).aestronglyMeasurable
  have hpos : ∀ᵐ t ∂μ, 0 < t := ae_restrict_mem measurableSet_Ioi
  -- pointwise norm bound (equality)
  have h_bound : ∀ p, ∀ᵐ t ∂μ, ‖F p t‖ ≤ bound p t := by
    intro p
    filter_upwards [hpos] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hepos : (0 : ℝ) < e t := by rw [he]; exact Real.exp_pos _
    have hFval : F p t = z ^ p / p.factorial * (c - Real.log t) ^ p * t ^ (ν - 1) * e t := rfl
    have hbval : bound p t
        = (|z| * |c - Real.log t|) ^ p / p.factorial * (t ^ (ν - 1) * e t) := rfl
    rw [hFval, hbval, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_div, abs_pow, abs_pow,
      Nat.abs_cast, abs_of_pos (Real.rpow_pos_of_pos ht0 _), abs_of_pos hepos, mul_pow]
    apply le_of_eq; ring
  -- summability of the bound
  have h_summable : ∀ᵐ t ∂μ, Summable (fun p => bound p t) := by
    filter_upwards with t
    exact (Real.summable_pow_div_factorial (|z| * |c - Real.log t|)).mul_right _
  -- the summed bound equals the dominating function
  have htsum : ∀ t : ℝ, (∑' p, bound p t)
      = Real.exp (|z| * |c - Real.log t|) * (t ^ (ν - 1) * e t) := by
    intro t
    have hbval : (fun p => bound p t)
        = fun p => (|z| * |c - Real.log t|) ^ p / p.factorial * (t ^ (ν - 1) * e t) := rfl
    rw [hbval, tsum_mul_right]
    congr 1
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (|z| * |c - Real.log t|)).tsum_eq
  have hmaj : IntegrableOn (fun t => Real.exp (|z| * |c|) *
      (t ^ (ν - 1 + |z|) * e t + t ^ (ν - 1 - |z|) * e t)) (Set.Ioi 0) := by
    have i1 : IntegrableOn (fun t => t ^ (ν - 1 + |z|) * e t) (Set.Ioi 0) := by
      rw [he, show ν - 1 + |z| = (ν + |z|) - 1 by ring]
      exact fluctuation_integrableOn β (ν + |z|) hβ (by positivity) a
    have i2 : IntegrableOn (fun t => t ^ (ν - 1 - |z|) * e t) (Set.Ioi 0) := by
      rw [he, show ν - 1 - |z| = (ν - |z|) - 1 by ring]
      exact fluctuation_integrableOn β (ν - |z|) hβ (by linarith [abs_nonneg z]) a
    exact (i1.add i2).const_mul (Real.exp (|z| * |c|))
  have bound_integrable : Integrable (fun t => ∑' p, bound p t) μ := by
    refine Integrable.congr ?_ (Filter.Eventually.of_forall (fun t => (htsum t).symm))
    refine hmaj.mono' ?_ ?_
    · exact (by rw [he]; fun_prop : Measurable fun t =>
        Real.exp (|z| * |c - Real.log t|) * (t ^ (ν - 1) * e t)).aestronglyMeasurable
    · filter_upwards [hpos] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hepos : (0 : ℝ) < e t := by rw [he]; exact Real.exp_pos _
      have hexpbnd : Real.exp (|z| * |c - Real.log t|)
          ≤ Real.exp (|z| * |c|) * (t ^ |z| + t ^ (-|z|)) := by
        calc Real.exp (|z| * |c - Real.log t|)
            ≤ Real.exp (|z| * (|c| + |Real.log t|)) := by
              apply Real.exp_le_exp.mpr
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg z)
              rw [sub_eq_add_neg, ← abs_neg (Real.log t)]
              exact abs_add_le c _
          _ = Real.exp (|z| * |c|) * Real.exp (|z| * |Real.log t|) := by
              rw [← Real.exp_add]; congr 1; ring
          _ ≤ Real.exp (|z| * |c|) * (t ^ |z| + t ^ (-|z|)) :=
              mul_le_mul_of_nonneg_left (exp_absz_abs_log_le z t ht0) (Real.exp_pos _).le
      have hrw1 : t ^ |z| * t ^ (ν - 1) = t ^ (ν - 1 + |z|) := by
        rw [← Real.rpow_add ht0]; congr 1; ring
      have hrw2 : t ^ (-|z|) * t ^ (ν - 1) = t ^ (ν - 1 - |z|) := by
        rw [← Real.rpow_add ht0]; congr 1; ring
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc Real.exp (|z| * |c - Real.log t|) * (t ^ (ν - 1) * e t)
          ≤ Real.exp (|z| * |c|) * (t ^ |z| + t ^ (-|z|)) * (t ^ (ν - 1) * e t) := by
            gcongr
        _ = Real.exp (|z| * |c|) * (t ^ (ν - 1 + |z|) * e t + t ^ (ν - 1 - |z|) * e t) := by
            rw [← hrw1, ← hrw2]; ring
  -- pointwise exponential series
  have h_lim : ∀ᵐ t ∂μ, HasSum (fun p => F p t) (f t) := by
    filter_upwards with t
    have hexp : HasSum (fun p => (z * (c - Real.log t)) ^ p / p.factorial)
        (Real.exp (z * (c - Real.log t))) := by
      rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
    have hfun : (fun p => F p t)
        = fun p => (z * (c - Real.log t)) ^ p / p.factorial * (t ^ (ν - 1) * e t) := by
      funext p
      show z ^ p / p.factorial * (c - Real.log t) ^ p * t ^ (ν - 1) * e t
        = (z * (c - Real.log t)) ^ p / p.factorial * (t ^ (ν - 1) * e t)
      rw [mul_pow]; ring
    have hval : f t = Real.exp (z * (c - Real.log t)) * (t ^ (ν - 1) * e t) := by
      show Real.exp (z * (c - Real.log t)) * t ^ (ν - 1) * e t
        = Real.exp (z * (c - Real.log t)) * (t ^ (ν - 1) * e t)
      ring
    rw [hfun, hval]
    exact hexp.mul_right _
  have hmain := hasSum_integral_of_dominated_convergence (μ := μ) (F := F) (f := f)
    bound hF_meas h_bound h_summable bound_integrable h_lim
  -- identify ∫ F p and ∫ f
  have hFint : ∀ p, (∫ t, F p t ∂μ)
      = z ^ p / p.factorial * ∫ t in Set.Ioi 0,
          (c - Real.log t) ^ p * t ^ (ν - 1) * Real.exp (-β * t + β * a * Real.sqrt t) := by
    intro p
    rw [hμ, show (fun t => F p t)
        = fun t => z ^ p / p.factorial
          * ((c - Real.log t) ^ p * t ^ (ν - 1) * Real.exp (-β * t + β * a * Real.sqrt t)) from by
          funext t
          show z ^ p / p.factorial * (c - Real.log t) ^ p * t ^ (ν - 1) * e t = _
          rw [he]; ring, integral_const_mul]
  have hfint : (∫ t, f t ∂μ) = Real.exp (z * c) * fluctuation β (ν - z) a := by
    have hstep : (∫ t in Set.Ioi 0, f t)
        = ∫ t in Set.Ioi 0, Real.exp (z * c)
            * (t ^ (ν - z - 1) * Real.exp (-β * t + β * a * Real.sqrt t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : (0 : ℝ) < t := ht
      have hcomb : t ^ (-z) * t ^ (ν - 1) = t ^ (ν - z - 1) := by
        rw [← Real.rpow_add ht0]; congr 1; ring
      show Real.exp (z * (c - Real.log t)) * t ^ (ν - 1) * e t
        = Real.exp (z * c) * (t ^ (ν - z - 1) * Real.exp (-β * t + β * a * Real.sqrt t))
      rw [he]
      simp only []
      rw [show z * (c - Real.log t) = z * c + -z * Real.log t by ring, Real.exp_add,
        show Real.exp (-z * Real.log t) = t ^ (-z) by rw [Real.rpow_def_of_pos ht0]; congr 1; ring,
        ← hcomb]
      ring
    rw [hμ, hstep, integral_const_mul]
    rfl
  rw [hfint] at hmain
  exact hmain.congr_fun (fun p => (hFint p).symm)

end Laplace.Grammar
