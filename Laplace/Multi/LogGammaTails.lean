/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib

/-!
# Truncated Gamma and log-Gamma integrals

The building blocks of the multiplicity law: the truncated integrals

  `Γ_j(u) = ∫₀ᵘ s^j e^{-s} ds`,   `Λ_j(u) = ∫₀ᵘ s^j e^{-s} log s ds`

(`gammaTrunc`, `logGammaTrunc`), their limits `j!` and `Λ_j(∞)` (`logGammaFull`), the tail bounds
`|Γ_j(u) − j!| ≤ (j+2)!/u²`, `|Λ_j(u) − Λ_j(∞)| ≤ (j+3)!/u²` for `u ≥ 1` (obtained by inserting the
factor `(s/u)² ≥ 1` on the tail — no exponential asymptotics needed), and the integration-by-parts
recursion `Λ_{j+1}(∞) = (j+1) Λ_j(∞) + j!` (`logGammaFull_succ`), the only special-function identity
the multiplicity law needs (Astra, round 25).
-/

open MeasureTheory Filter Topology Set intervalIntegral

namespace Laplace.Multi

/-- `Γ_j(u) = ∫₀ᵘ s^j e^{-s} ds`. -/
noncomputable def gammaTrunc (j : ℕ) (u : ℝ) : ℝ := ∫ s in (0 : ℝ)..u, s ^ j * Real.exp (-s)

/-- `Λ_j(u) = ∫₀ᵘ s^j e^{-s} log s ds`. -/
noncomputable def logGammaTrunc (j : ℕ) (u : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..u, s ^ j * Real.exp (-s) * Real.log s

/-- `Λ_j(∞) = ∫₀^∞ s^j e^{-s} log s ds`. -/
noncomputable def logGammaFull (j : ℕ) : ℝ := ∫ s in Ioi (0 : ℝ), s ^ j * Real.exp (-s) * Real.log s

/-- `s^j e^{-s}` is integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_exp_neg_Ioi (j : ℕ) :
    IntegrableOn (fun s : ℝ ↦ s ^ j * Real.exp (-s)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (j : ℝ) + 1) (by positivity)
  refine h.congr_fun (fun s hs ↦ ?_) measurableSet_Ioi
  simp only [add_sub_cancel_right, Real.rpow_natCast]
  ring

/-- `∫₀^∞ s^j e^{-s} ds = j!`. -/
theorem integral_pow_mul_exp_neg_Ioi (j : ℕ) :
    ∫ s in Ioi (0 : ℝ), s ^ j * Real.exp (-s) = (j.factorial : ℝ) := by
  have h := Real.Gamma_eq_integral (s := (j : ℝ) + 1) (by positivity)
  rw [Real.Gamma_nat_eq_factorial] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ ↦ ?_
  simp only [add_sub_cancel_right, Real.rpow_natCast]
  ring

/-- `log` is integrable on `(0, 1]`. -/
theorem integrableOn_log_Ioc_zero_one : IntegrableOn Real.log (Ioc (0 : ℝ) 1) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp intervalIntegrable_log'

/-- `s^j e^{-s} log s` is integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_exp_neg_mul_log_Ioi (j : ℕ) :
    IntegrableOn (fun s : ℝ ↦ s ^ j * Real.exp (-s) * Real.log s) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · refine integrableOn_log_Ioc_zero_one.abs.mono' (by fun_prop : Measurable
      fun s : ℝ ↦ s ^ j * Real.exp (-s) * Real.log s).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs ↦ ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hs.1.le _), Real.abs_exp]
    have h1 : s ^ j ≤ 1 := pow_le_one₀ hs.1.le hs.2
    have h2 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hs.1])
    calc s ^ j * Real.exp (-s) * |Real.log s| ≤ 1 * 1 * |Real.log s| := by
          gcongr
      _ = |Real.log s| := by ring
  · refine ((integrableOn_pow_mul_exp_neg_Ioi (j + 1)).mono_set (Ioi_subset_Ioi zero_le_one)).mono'
      (by fun_prop : Measurable fun s : ℝ ↦ s ^ j * Real.exp (-s) * Real.log s).aestronglyMeasurable
      ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs ↦ ?_)
    have hs1 : 1 < s := hs
    have hs0 : 0 < s := lt_trans zero_lt_one hs1
    simp only [Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hs0.le _), Real.abs_exp,
      abs_of_nonneg (Real.log_nonneg hs1.le), pow_succ]
    have := Real.log_le_sub_one_of_pos hs0
    calc s ^ j * Real.exp (-s) * Real.log s ≤ s ^ j * Real.exp (-s) * s := by
          gcongr
          linarith
      _ = s ^ j * s * Real.exp (-s) := by ring

/-- **Tail bound**: `∫_u^∞ s^j e^{-s} ≤ (j+2)!/u²` for `u ≥ 1`. -/
theorem gammaTail_le (j : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    ∫ s in Ioi u, s ^ j * Real.exp (-s) ≤ ((j + 2).factorial : ℝ) / u ^ 2 := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hI : IntegrableOn (fun s : ℝ ↦ s ^ j * Real.exp (-s)) (Ioi u) :=
    (integrableOn_pow_mul_exp_neg_Ioi j).mono_set (Ioi_subset_Ioi hu0.le)
  have hI2 : IntegrableOn (fun s : ℝ ↦ s ^ (j + 2) * Real.exp (-s) / u ^ 2) (Ioi u) :=
    ((integrableOn_pow_mul_exp_neg_Ioi (j + 2)).mono_set (Ioi_subset_Ioi hu0.le)).div_const _
  calc ∫ s in Ioi u, s ^ j * Real.exp (-s)
      ≤ ∫ s in Ioi u, s ^ (j + 2) * Real.exp (-s) / u ^ 2 := by
        refine setIntegral_mono_on hI hI2 measurableSet_Ioi fun s hs ↦ ?_
        have hs : u < s := hs
        rw [le_div_iff₀ (by positivity), pow_add]
        have : u ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hu0.le hs.le 2
        have hs0 : 0 < s := lt_trans hu0 hs
        calc s ^ j * Real.exp (-s) * u ^ 2 ≤ s ^ j * Real.exp (-s) * s ^ 2 :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = s ^ j * s ^ 2 * Real.exp (-s) := by ring
    _ = (∫ s in Ioi u, s ^ (j + 2) * Real.exp (-s)) / u ^ 2 := integral_div _ _
    _ ≤ (∫ s in Ioi 0, s ^ (j + 2) * Real.exp (-s)) / u ^ 2 := by
        have hmono : (∫ s in Ioi u, s ^ (j + 2) * Real.exp (-s)) ≤
            ∫ s in Ioi 0, s ^ (j + 2) * Real.exp (-s) := by
          refine setIntegral_mono_set (integrableOn_pow_mul_exp_neg_Ioi (j + 2)) ?_
            (Filter.Eventually.of_forall (Ioi_subset_Ioi hu0.le))
          refine (ae_restrict_iff' measurableSet_Ioi).mpr
            (Filter.Eventually.of_forall fun s hs ↦ ?_)
          have : 0 < s := hs
          positivity
        exact div_le_div_of_nonneg_right hmono (by positivity)
    _ = ((j + 2).factorial : ℝ) / u ^ 2 := by rw [integral_pow_mul_exp_neg_Ioi]

/-- The tail integrals are nonnegative. -/
theorem gammaTail_nonneg (j : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ ∫ s in Ioi u, s ^ j * Real.exp (-s) :=
  setIntegral_nonneg measurableSet_Ioi fun s hs ↦ by
    have : 0 < s := lt_of_le_of_lt hu hs
    positivity

/-- **Log tail bound**: `|∫_u^∞ s^j e^{-s} log s| ≤ (j+3)!/u²` for `u ≥ 1`. -/
theorem logGammaTail_abs_le (j : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    |∫ s in Ioi u, s ^ j * Real.exp (-s) * Real.log s| ≤ ((j + 3).factorial : ℝ) / u ^ 2 := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hI : IntegrableOn (fun s : ℝ ↦ s ^ j * Real.exp (-s) * Real.log s) (Ioi u) :=
    (integrableOn_pow_mul_exp_neg_mul_log_Ioi j).mono_set (Ioi_subset_Ioi hu0.le)
  have hI1 : IntegrableOn (fun s : ℝ ↦ s ^ (j + 1) * Real.exp (-s)) (Ioi u) :=
    (integrableOn_pow_mul_exp_neg_Ioi (j + 1)).mono_set (Ioi_subset_Ioi hu0.le)
  calc |∫ s in Ioi u, s ^ j * Real.exp (-s) * Real.log s|
      ≤ ∫ s in Ioi u, |s ^ j * Real.exp (-s) * Real.log s| := by
        have := norm_integral_le_integral_norm (μ := volume.restrict (Ioi u))
          (fun s : ℝ ↦ s ^ j * Real.exp (-s) * Real.log s)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∫ s in Ioi u, s ^ (j + 1) * Real.exp (-s) := by
        refine setIntegral_mono_on hI.abs hI1 measurableSet_Ioi fun s hs ↦ ?_
        have hs : u < s := hs
        have hs1 : 1 < s := lt_of_le_of_lt hu hs
        have hs0 : 0 < s := lt_trans zero_lt_one hs1
        rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hs0.le _), Real.abs_exp,
          abs_of_nonneg (Real.log_nonneg hs1.le), pow_succ]
        have := Real.log_le_sub_one_of_pos hs0
        calc s ^ j * Real.exp (-s) * Real.log s ≤ s ^ j * Real.exp (-s) * s := by
              gcongr
              linarith
          _ = s ^ j * s * Real.exp (-s) := by ring
    _ ≤ ((j + 1 + 2).factorial : ℝ) / u ^ 2 := gammaTail_le (j + 1) hu
    _ = ((j + 3).factorial : ℝ) / u ^ 2 := by norm_num

/-- `Γ_j(u) = j! − ∫_u^∞ s^j e^{-s}` for `u ≥ 0`. -/
theorem gammaTrunc_eq (j : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    gammaTrunc j u = (j.factorial : ℝ) - ∫ s in Ioi u, s ^ j * Real.exp (-s) := by
  rw [← integral_pow_mul_exp_neg_Ioi, ← Ioc_union_Ioi_eq_Ioi hu,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((integrableOn_pow_mul_exp_neg_Ioi j).mono_set Ioc_subset_Ioi_self)
      ((integrableOn_pow_mul_exp_neg_Ioi j).mono_set (Ioi_subset_Ioi hu)),
    gammaTrunc, integral_of_le hu]
  ring

/-- `Λ_j(u) = Λ_j(∞) − ∫_u^∞ s^j e^{-s} log s` for `u ≥ 0`. -/
theorem logGammaTrunc_eq (j : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    logGammaTrunc j u = logGammaFull j - ∫ s in Ioi u, s ^ j * Real.exp (-s) * Real.log s := by
  rw [logGammaFull, ← Ioc_union_Ioi_eq_Ioi hu,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((integrableOn_pow_mul_exp_neg_mul_log_Ioi j).mono_set Ioc_subset_Ioi_self)
      ((integrableOn_pow_mul_exp_neg_mul_log_Ioi j).mono_set (Ioi_subset_Ioi hu)),
    logGammaTrunc, integral_of_le hu]
  ring

/-- `|Γ_j(u) − j!| ≤ (j+2)!/u²` for `u ≥ 1`. -/
theorem abs_gammaTrunc_sub_le (j : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    |gammaTrunc j u - (j.factorial : ℝ)| ≤ ((j + 2).factorial : ℝ) / u ^ 2 := by
  rw [gammaTrunc_eq j (zero_le_one.trans hu), sub_sub_cancel_left, abs_neg,
    abs_of_nonneg (gammaTail_nonneg j u (zero_le_one.trans hu))]
  exact gammaTail_le j hu

/-- `|Λ_j(u) − Λ_j(∞)| ≤ (j+3)!/u²` for `u ≥ 1`. -/
theorem abs_logGammaTrunc_sub_le (j : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    |logGammaTrunc j u - logGammaFull j| ≤ ((j + 3).factorial : ℝ) / u ^ 2 := by
  rw [logGammaTrunc_eq j (zero_le_one.trans hu), sub_sub_cancel_left, abs_neg]
  exact logGammaTail_abs_le j hu

/-- `s^{j+1} e^{-s} log s → 0` as `s → 0⁺`. -/
theorem tendsto_pow_mul_exp_neg_mul_log_nhdsGT_zero (j : ℕ) :
    Tendsto (fun s : ℝ ↦ Real.log s * (s ^ (j + 1) * Real.exp (-s))) (𝓝[>] 0) (𝓝 0) := by
  have h1 := tendsto_log_mul_rpow_nhdsGT_zero (r := (j : ℝ) + 1) (by positivity)
  have h2 : Tendsto (fun s : ℝ ↦ Real.exp (-s)) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun s : ℝ ↦ Real.exp (-s)) (𝓝 0) (𝓝 (Real.exp (-0))) :=
      (Real.continuous_exp.comp continuous_neg).tendsto 0
    rw [neg_zero, Real.exp_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have := h1.mul h2
  rw [zero_mul] at this
  refine this.congr fun s ↦ ?_
  rw [← Real.rpow_natCast, Nat.cast_succ]
  ring

/-- `s^{j+1} e^{-s} log s → 0` as `s → ∞`. -/
theorem tendsto_pow_mul_exp_neg_mul_log_atTop (j : ℕ) :
    Tendsto (fun s : ℝ ↦ Real.log s * (s ^ (j + 1) * Real.exp (-s))) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (j + 2))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.log_nonneg hs),
    abs_of_nonneg (pow_nonneg hs0.le _), Real.abs_exp]
  have := Real.log_le_sub_one_of_pos hs0
  calc Real.log s * (s ^ (j + 1) * Real.exp (-s)) ≤ s * (s ^ (j + 1) * Real.exp (-s)) := by
        gcongr
        linarith
    _ = s ^ (j + 2) * Real.exp (-s) := by ring

/-- **The integration-by-parts recursion** `Λ_{j+1}(∞) = (j+1) Λ_j(∞) + j!`. -/
theorem logGammaFull_succ (j : ℕ) :
    logGammaFull (j + 1) = ((j : ℝ) + 1) * logGammaFull j + (j.factorial : ℝ) := by
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun s : ℝ ↦ s ^ (j + 1) * Real.exp (-s))
      ((((j : ℝ) + 1) * x ^ j - x ^ (j + 1)) * Real.exp (-x)) x := fun x _ ↦ by
    have := (hasDerivAt_pow (j + 1) x).mul (hasDerivAt_neg x).exp
    refine this.congr_deriv ?_
    simp only [Nat.cast_succ, Nat.add_sub_cancel]
    ring
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt Real.log x⁻¹ x := fun x hx ↦
    Real.hasDerivAt_log (ne_of_gt hx)
  have huv' : IntegrableOn (Real.log * fun x : ℝ ↦
      ((((j : ℝ) + 1) * x ^ j - x ^ (j + 1)) * Real.exp (-x))) (Ioi 0) := by
    have h : IntegrableOn (fun x : ℝ ↦ ((j : ℝ) + 1) * (x ^ j * Real.exp (-x) * Real.log x) -
        x ^ (j + 1) * Real.exp (-x) * Real.log x) (Ioi 0) :=
      ((integrableOn_pow_mul_exp_neg_mul_log_Ioi j).const_mul ((j : ℝ) + 1)).sub
        (integrableOn_pow_mul_exp_neg_mul_log_Ioi (j + 1))
    refine h.congr_fun (fun x _ ↦ ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]
    ring
  have hu'v : IntegrableOn ((fun x : ℝ ↦ x⁻¹) * fun x : ℝ ↦ x ^ (j + 1) * Real.exp (-x))
      (Ioi 0) := by
    refine (integrableOn_pow_mul_exp_neg_Ioi j).congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
    have hx : 0 < x := hx
    simp only [Pi.mul_apply, pow_succ]
    field_simp
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v
    (tendsto_pow_mul_exp_neg_mul_log_nhdsGT_zero j) (tendsto_pow_mul_exp_neg_mul_log_atTop j)
  -- rewrite the two sides
  have e1 : (∫ x in Ioi (0 : ℝ), Real.log x * ((((j : ℝ) + 1) * x ^ j - x ^ (j + 1)) *
      Real.exp (-x))) = ((j : ℝ) + 1) * logGammaFull j - logGammaFull (j + 1) := by
    unfold logGammaFull
    rw [← MeasureTheory.integral_const_mul, ← integral_sub
      ((integrableOn_pow_mul_exp_neg_mul_log_Ioi j).const_mul _)
      (integrableOn_pow_mul_exp_neg_mul_log_Ioi (j + 1))]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
    ring
  have e2 : (∫ x in Ioi (0 : ℝ), x⁻¹ * (x ^ (j + 1) * Real.exp (-x))) = (j.factorial : ℝ) := by
    rw [← integral_pow_mul_exp_neg_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    have hx : 0 < x := hx
    simp only [pow_succ]
    field_simp
  rw [e1, e2] at key
  linarith

end Laplace.Multi
