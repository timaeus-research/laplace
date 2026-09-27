/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DataDissipation
import Laplace.Multi.AtomicIntervalDistortion

/-!
# The Fisher length of a binary data path

For an indicator data direction `h = 1_A` with `p₀ = ν(A) ∈ (0, 1)` the data path
`ρ_t = ν.tilted (t h)` only reweights the two conditional laws on `A` and `Aᶜ`: its mean
`m_t = ρ_t(A)` solves the logistic equation `m' = m(1 − m)` and its Fisher speed is
`√(m_t(1 − m_t))`. Since `(d/dt)(−2 arccos √m_t) = √(m_t(1 − m_t))`, the total Fisher length of
the data path is

  `∫₀^∞ √Var_{ρ_t} h dt = 2 arccos √p₀ < π`
  (`integral_Ioi_sqrt_var_indicator`, `two_arccos_sqrt_lt_pi`).

On the atomic interval of `AtomicIntervalDistortion` the data path therefore has finite length
`2 arccos √(1/2)` while its response path has infinite length: no constant bounds the response
length by the data length.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Binary

variable {X : Type*} [MeasurableSpace X] [Nonempty X] (ν : Measure X) [IsProbabilityMeasure ν]
  {A : Set X} (hA : MeasurableSet A)
include hA

/-- The indicator of `A` as a real function. -/
local notation "𝟙A" => (A.indicator fun _ ↦ (1 : ℝ))

omit [Nonempty X] [IsProbabilityMeasure ν] in
theorem bdd_indicator : Bdd 𝟙A :=
  ⟨measurable_const.indicator hA, 1, fun x ↦ by
    by_cases hx : x ∈ A <;> simp [hx]⟩

omit [MeasurableSpace X] [Nonempty X] [IsProbabilityMeasure ν] hA in
theorem indicator_mul_self (x : X) : 𝟙A x * 𝟙A x = 𝟙A x := by
  by_cases hx : x ∈ A <;> simp [hx]

omit [MeasurableSpace X] [Nonempty X] [IsProbabilityMeasure ν] hA in
theorem indicator_le_one (x : X) : 𝟙A x ≤ 1 := by
  by_cases hx : x ∈ A <;> simp [hx]

omit [MeasurableSpace X] [Nonempty X] [IsProbabilityMeasure ν] hA in
theorem exp_mul_indicator (t : ℝ) (x : X) : exp (t * 𝟙A x) = 1 + (exp t - 1) * 𝟙A x := by
  by_cases hx : x ∈ A <;> simp [hx]

omit [MeasurableSpace X] [Nonempty X] [IsProbabilityMeasure ν] hA in
theorem exp_mul_indicator_mul (t : ℝ) (x : X) :
    exp (t * 𝟙A x) * 𝟙A x = exp t * 𝟙A x := by
  by_cases hx : x ∈ A <;> simp [hx]

variable (A) in
/-- The mean of the indicator along the binary data path. -/
noncomputable def binMean (t : ℝ) : ℝ := ∫ x, 𝟙A x ∂ν.tilted (fun x ↦ t * 𝟙A x)

omit [Nonempty X] [IsProbabilityMeasure ν] in
theorem integral_indicator_one' : ∫ x, 𝟙A x ∂ν = ν.real A := by
  rw [integral_indicator hA]
  simp

omit [Nonempty X] in
/-- The explicit logistic curve `m_t = p₀ e^t / (1 + (e^t − 1) p₀)`. -/
theorem binMean_eq (t : ℝ) :
    binMean ν A t = exp t * ν.real A / (1 + (exp t - 1) * ν.real A) := by
  have hint : Integrable 𝟙A ν := integrable_of_bdd_prob ν (bdd_indicator hA)
  rw [binMean, integral_tilted]
  have e1 : ∀ x, (exp (t * 𝟙A x) / ∫ y, exp (t * 𝟙A y) ∂ν) • 𝟙A x =
      exp t * 𝟙A x / ∫ y, exp (t * 𝟙A y) ∂ν := fun x ↦ by
    rw [smul_eq_mul, div_mul_eq_mul_div, exp_mul_indicator_mul]
  have e2 : ∫ y, exp (t * 𝟙A y) ∂ν = 1 + (exp t - 1) * ν.real A := by
    simp_rw [exp_mul_indicator]
    rw [integral_add (integrable_const _) (hint.const_mul _), integral_const_mul,
      integral_indicator_one' ν hA]
    simp
  simp_rw [e1]
  rw [integral_div, integral_const_mul, integral_indicator_one' ν hA, e2]

variable (hp0 : 0 < ν.real A) (hp1 : ν.real A < 1)
include hp0 hp1

omit [Nonempty X] in
theorem binMean_pos (t : ℝ) : 0 < binMean ν A t := by
  rw [binMean_eq ν hA]
  have : 0 < 1 + (exp t - 1) * ν.real A := by nlinarith [exp_pos t]
  positivity

omit [Nonempty X] in
theorem binMean_lt_one (t : ℝ) : binMean ν A t < 1 := by
  rw [binMean_eq ν hA, div_lt_one (by nlinarith [exp_pos t])]
  nlinarith [exp_pos t]

omit hp0 hp1 in
/-- The logistic equation `m' = m(1 − m)`. -/
theorem hasDerivAt_binMean (t : ℝ) :
    HasDerivAt (binMean ν A) (binMean ν A t * (1 - binMean ν A t)) t := by
  have h := hasDerivAt_integral_tilted ν (bdd_indicator hA) (bdd_indicator hA) t
  refine h.congr_deriv ?_
  simp_rw [indicator_mul_self]
  rw [binMean]
  ring

omit [Nonempty X] [IsProbabilityMeasure ν] hA hp0 hp1 in
/-- The Fisher speed of the binary data path is `√(m_t(1 − m_t))`. -/
theorem lawCov_indicator_dataPath (t : ℝ) :
    lawCov (ν.tilted fun x ↦ t * 𝟙A x) 𝟙A 𝟙A = binMean ν A t * (1 - binMean ν A t) := by
  rw [lawCov]
  simp_rw [indicator_mul_self]
  rw [binMean]
  ring

/-- **The arccos primitive**: `(d/dt)(−2 arccos √m_t) = √(m_t(1 − m_t))`. -/
theorem hasDerivAt_neg_two_arccos_sqrt_binMean (t : ℝ) :
    HasDerivAt (fun s ↦ -2 * arccos √(binMean ν A s))
      (√(binMean ν A t * (1 - binMean ν A t))) t := by
  have hm0 := binMean_pos ν hA hp0 hp1 t
  have hm1 := binMean_lt_one ν hA hp0 hp1 t
  have hs0 : 0 < √(binMean ν A t) := Real.sqrt_pos.2 hm0
  have hs1 : √(binMean ν A t) < 1 := by
    rw [Real.sqrt_lt' one_pos, one_pow]
    exact hm1
  have h1 := (Real.hasDerivAt_sqrt hm0.ne').comp t (hasDerivAt_binMean ν hA t)
  have h2 := (Real.hasDerivAt_arccos (by linarith) hs1.ne).comp t h1
  refine (h2.const_mul (-2)).congr_deriv ?_
  have ha : √(binMean ν A t) ^ 2 = binMean ν A t := Real.sq_sqrt hm0.le
  have hb0 : 0 < √(1 - binMean ν A t) := Real.sqrt_pos.2 (by linarith)
  have hb : √(1 - binMean ν A t) ^ 2 = 1 - binMean ν A t := Real.sq_sqrt (by linarith)
  rw [ha, Real.sqrt_mul hm0.le]
  have key : binMean ν A t * (1 - binMean ν A t) =
      (√(binMean ν A t) * √(1 - binMean ν A t)) * (√(binMean ν A t) * √(1 - binMean ν A t)) := by
    rw [mul_mul_mul_comm, Real.mul_self_sqrt hm0.le, Real.mul_self_sqrt (by linarith)]
  rw [key]
  field_simp

omit hp0 hp1 in
theorem continuous_sqrt_var_indicator :
    Continuous fun t ↦ √(binMean ν A t * (1 - binMean ν A t)) := by
  have hc : Continuous (binMean ν A) :=
    continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_binMean ν hA t).continuousAt
  exact (hc.mul (continuous_const.sub hc)).sqrt

omit [Nonempty X] hp0 hp1 in
theorem binMean_zero : binMean ν A 0 = ν.real A := by
  rw [binMean_eq ν hA]
  simp

/-- **The length of a window of the binary data path**:
`∫₀^T √Var_{ρ_t} h dt = 2 arccos √p₀ − 2 arccos √m_T`. -/
theorem intervalIntegral_sqrt_var_indicator (T : ℝ) :
    ∫ t in (0 : ℝ)..T, √(lawCov (ν.tilted fun x ↦ t * 𝟙A x) 𝟙A 𝟙A) =
      2 * arccos √(ν.real A) - 2 * arccos √(binMean ν A T) := by
  simp_rw [lawCov_indicator_dataPath (ν := ν)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hasDerivAt_neg_two_arccos_sqrt_binMean ν hA hp0 hp1 s)
    ((continuous_sqrt_var_indicator ν hA).intervalIntegrable _ _), binMean_zero ν hA]
  ring

omit [Nonempty X] in
theorem tendsto_binMean_one : Tendsto (binMean ν A) atTop (𝓝 1) := by
  have e : binMean ν A = fun t ↦ ν.real A / (exp (-t) * (1 - ν.real A) + ν.real A) := by
    funext t
    rw [binMean_eq ν hA, Real.exp_neg]
    have h1 : 0 < 1 + (exp t - 1) * ν.real A := by nlinarith [exp_pos t]
    have h2 : 0 < (exp t)⁻¹ * (1 - ν.real A) + ν.real A := by
      have := inv_pos.2 (exp_pos t)
      nlinarith
    field_simp
    ring
  rw [e]
  have h : Tendsto (fun t ↦ exp (-t) * (1 - ν.real A) + ν.real A) atTop
      (𝓝 (0 * (1 - ν.real A) + ν.real A)) :=
    (tendsto_exp_neg_atTop_nhds_zero.mul_const _).add_const _
  have := (tendsto_const_nhds (x := ν.real A)).div h (by simpa using hp0.ne')
  rw [zero_mul, zero_add, div_self hp0.ne'] at this
  exact this

/-- **The total Fisher length of the binary data path is `2 arccos √p₀`** (as a limit). -/
theorem tendsto_intervalIntegral_sqrt_var_indicator :
    Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, √(lawCov (ν.tilted fun x ↦ t * 𝟙A x) 𝟙A 𝟙A)) atTop
      (𝓝 (2 * arccos √(ν.real A))) := by
  simp_rw [intervalIntegral_sqrt_var_indicator ν hA hp0 hp1]
  have h : Tendsto (fun T ↦ 2 * arccos √(binMean ν A T)) atTop (𝓝 (2 * arccos √1)) :=
    ((continuous_arccos.tendsto _).comp
      ((Real.continuous_sqrt.tendsto _).comp (tendsto_binMean_one ν hA hp0 hp1))).const_mul 2
  rw [Real.sqrt_one, arccos_one, mul_zero] at h
  simpa using (tendsto_const_nhds (x := 2 * arccos √(ν.real A))).sub h

theorem integrableOn_sqrt_var_indicator :
    IntegrableOn (fun t ↦ √(lawCov (ν.tilted fun x ↦ t * 𝟙A x) 𝟙A 𝟙A)) (Ioi (0 : ℝ)) := by
  have hc : Continuous fun t ↦ √(lawCov (ν.tilted fun x ↦ t * 𝟙A x) 𝟙A 𝟙A) := by
    simp_rw [lawCov_indicator_dataPath (ν := ν)]
    exact continuous_sqrt_var_indicator ν hA
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (2 * arccos √(ν.real A)) 0 (b := id)
    (l := atTop) (fun T ↦ hc.integrableOn_Ioc) tendsto_id ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  simp only [id_eq]
  calc ∫ t in (0 : ℝ)..T, ‖√(lawCov (ν.tilted fun x ↦ t * 𝟙A x) 𝟙A 𝟙A)‖
      = ∫ t in (0 : ℝ)..T, √(lawCov (ν.tilted fun x ↦ t * 𝟙A x) 𝟙A 𝟙A) :=
        intervalIntegral.integral_congr fun t _ ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ = 2 * arccos √(ν.real A) - 2 * arccos √(binMean ν A T) :=
        intervalIntegral_sqrt_var_indicator ν hA hp0 hp1 T
    _ ≤ 2 * arccos √(ν.real A) := by linarith [arccos_nonneg √(binMean ν A T)]

/-- **The Fisher length of the binary data path**: `∫₀^∞ √Var_{ρ_t} h dt = 2 arccos √p₀`. -/
theorem integral_Ioi_sqrt_var_indicator :
    ∫ t in Ioi (0 : ℝ), √(lawCov (ν.tilted fun x ↦ t * 𝟙A x) 𝟙A 𝟙A) = 2 * arccos √(ν.real A) :=
  tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_sqrt_var_indicator ν hA hp0 hp1)
      (tendsto_id (α := ℝ)))
    (tendsto_intervalIntegral_sqrt_var_indicator ν hA hp0 hp1)

omit [Nonempty X] [IsProbabilityMeasure ν] hA hp1 in
/-- The binary data length is below `π`. -/
theorem two_arccos_sqrt_lt_pi : 2 * arccos √(ν.real A) < π := by
  have := arccos_lt_pi_div_two.2 (Real.sqrt_pos.2 hp0)
  linarith

end Binary

namespace AtomicInterval

theorem hA_eq_indicator : hA = ({0} : Set ℕ).indicator fun _ ↦ (1 : ℝ) := by
  funext k
  simp [hA, Set.indicator_apply]

/-- **Finite data length on the atomic interval**: `L_data = 2 arccos √(1/2) < π`, while the
response length is infinite (`tendsto_responseLength_atTop`). -/
theorem integral_Ioi_sqrt_var_hA :
    ∫ t in Ioi (0 : ℝ), √(lawCov (νA.tilted fun x ↦ t * hA x) hA hA) = 2 * arccos √(1 / 2) := by
  rw [hA_eq_indicator, integral_Ioi_sqrt_var_indicator νA (measurableSet_singleton 0)
    (by rw [νA_real_singleton]; exact atomW_pos 0)
    (by rw [νA_real_singleton]; norm_num [atomW]), νA_real_singleton]
  rfl

theorem dataLength_lt_pi :
    ∫ t in Ioi (0 : ℝ), √(lawCov (νA.tilted fun x ↦ t * hA x) hA hA) < π := by
  rw [integral_Ioi_sqrt_var_hA]
  have := two_arccos_sqrt_lt_pi νA (A := ({0} : Set ℕ))
    (by rw [νA_real_singleton]; exact atomW_pos 0)
  rwa [νA_real_singleton] at this

end AtomicInterval

end Laplace.Multi
