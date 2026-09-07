/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MonomialPhaseTail

/-!
# Positive log moments and the Tonelli majorant for the phase series (Stage 3d)

Unit 234 (Taylor-tree programme; Astra #27, Gate B). Define the **log majorant**
`logMajorant β b ν r p t = t^{ν-1} (1+|log t|)^r (√t)^p e^{-βt+βb√t}` and the **positive log
moment**
`phaseLogMoment β b ν r p = ∫₀^∞ logMajorant`. For `β > 0`, `ν > 0` the majorant is integrable on
`(0,∞)` for every real `b` and every `r, p` (`integrableOn_logMajorant`: on `(0,1]` the binomial
expansion of `(1 - log t)^r` reduces it to the basis terms of unit 225 times a bounded factor; on
`(1,∞)` the bound `1 + log t ≤ t` and the exponential domination of unit 229 apply). The **Tonelli
identity** for the phase series is
```
∑_{p} (βB)^p/p! · phaseLogMoment β b ν r p = phaseLogMoment β (b+B) ν r 0      (B ≥ 0),
```
with the series absolutely convergent (`summable_phaseLogMoment_series`,
`tsum_phaseLogMoment_series`):
pointwise `∑_p (βB√t)^p/p! = e^{βB√t}` folds the phase order into the exponent, and
`hasSum_integral_of_summable_integral_norm` interchanges sum and integral once the partial sums are
dominated by the folded majorant. This is the single abstraction that makes the phase-order sums of
Stage 3 absolutely convergent with **no smallness assumption on `B`**. No `sorry` and no additional
`axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology

namespace Laplace.Grammar

/-- The log majorant `t^{ν-1} (1+|log t|)^r (√t)^p e^{-βt+βb√t}`. -/
noncomputable def logMajorant (β b ν : ℝ) (r p : ℕ) (t : ℝ) : ℝ :=
  t ^ (ν - 1) * (1 + |Real.log t|) ^ r * phaseKernel β b p t

/-- The positive log moment `∫₀^∞ logMajorant`. -/
noncomputable def phaseLogMoment (β b ν : ℝ) (r p : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), logMajorant β b ν r p t

theorem logMajorant_nonneg (β b ν : ℝ) (r p : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ logMajorant β b ν r p t :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg ht _) (pow_nonneg (by positivity) _))
    (phaseKernel_nonneg β b p t)

theorem continuousOn_logMajorant (β b ν : ℝ) (r p : ℕ) :
    ContinuousOn (logMajorant β b ν r p) (Ioi 0) :=
  ((continuousOn_id.rpow_const fun _ ht => Or.inl (ne_of_gt ht)).mul
    ((continuousOn_const.add (Real.continuousOn_log.mono fun _ ht => ne_of_gt ht).abs).pow r)).mul
    (continuous_phaseKernel β b p).continuousOn

theorem measurable_logMajorant (β b ν : ℝ) (r p : ℕ) : Measurable (logMajorant β b ν r p) := by
  unfold logMajorant
  exact ((measurable_id.pow_const _).mul
    ((measurable_const.add Real.measurable_log.abs).pow_const r)).mul
    (continuous_phaseKernel β b p).measurable

/-! ### Integrability on `(0,1]` -/

/-- On `(0,1]`, `(1+|log t|)^r = ∑ C(r,i) (-log t)^i`. -/
theorem one_add_abs_log_pow {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (r : ℕ) :
    (1 + |Real.log t|) ^ r = ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * (-Real.log t) ^ i := by
  rw [abs_of_nonpos (Real.log_nonpos ht.1.le ht.2), add_comm, add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one]
  ring

theorem integrableOn_logMajorant_Ioc (β b ν : ℝ) (hν : 0 < ν) (r p : ℕ) :
    IntegrableOn (logMajorant β b ν r p) (Ioc 0 1) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_phaseKernel β b p).continuousOn
  have hterm : ∀ i : ℕ, IntegrableOn (fun t => (r.choose i : ℝ) * powLogBasis ν i t *
      phaseKernel β b p t) (Ioc 0 1) := fun i => by
    have h1 : IntegrableOn (fun t => phaseKernel β b p t * ((r.choose i : ℝ) * powLogBasis ν i t))
        (Ioc 0 1) :=
      ((integrableOn_powLogBasis ν hν i).const_mul _).bdd_mul (c := C)
        (continuous_phaseKernel β b p).aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => hC t ⟨ht.1.le, ht.2⟩)
    refine h1.congr_fun (fun t _ => ?_) measurableSet_Ioc
    beta_reduce
    ring
  have hsum : IntegrableOn (fun t => ∑ i ∈ Finset.range (r + 1),
      (r.choose i : ℝ) * powLogBasis ν i t * phaseKernel β b p t) (Ioc 0 1) :=
    integrable_finsetSum _ fun i _ => hterm i
  refine hsum.congr_fun (fun t ht => ?_) measurableSet_Ioc
  beta_reduce
  unfold logMajorant powLogBasis
  rw [one_add_abs_log_pow ht r, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### Exponential domination on `(1,∞)` -/

/-- For `t ≥ 1`: `logMajorant ≤ C e^{-βt/4}` with `C = e^{βb²/2} m! (4/β)^m`, `m = ⌈ν⌉ + r + p`. -/
theorem logMajorant_le (β b ν : ℝ) (hβ : 0 < β) (r p : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    logMajorant β b ν r p t ≤ tailConst β b p ν r * Real.exp (-(β * t / 4)) := by
  have ht0 : 0 < t := by linarith
  have hlog : (1 + |Real.log t|) ^ r ≤ t ^ r := by
    rw [abs_of_nonneg (Real.log_nonneg ht)]
    exact pow_le_pow_left₀ (by linarith [Real.log_nonneg ht])
      (by linarith [Real.log_le_sub_one_of_pos ht0]) r
  have hsqrt : Real.sqrt t ^ p ≤ t ^ p :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) ((Real.sqrt_le_left ht0.le).2 (by nlinarith)) p
  have hrpow : t ^ (ν - 1) ≤ t ^ (⌈ν⌉₊ : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ht (by linarith [Nat.le_ceil ν])
  set m : ℕ := ⌈ν⌉₊ + r + p with hm
  have hpowm : t ^ (⌈ν⌉₊ : ℕ) * t ^ r * t ^ p = t ^ m := by rw [hm, pow_add, pow_add]
  have hexp : t ^ m ≤ (m.factorial : ℝ) * (4 / β) ^ m * Real.exp (β * t / 4) := by
    have h := Real.pow_div_factorial_le_exp (β * t / 4) (by positivity) m
    rw [div_le_iff₀ (by positivity)] at h
    calc t ^ m = (β * t / 4) ^ m * (4 / β) ^ m := by
          rw [← mul_pow]; congr 1; field_simp
      _ ≤ Real.exp (β * t / 4) * (m.factorial : ℝ) * (4 / β) ^ m :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by ring
  have hker := phaseKernel_le β b hβ p ht0.le
  unfold logMajorant tailConst
  calc t ^ (ν - 1) * (1 + |Real.log t|) ^ r * phaseKernel β b p t
      ≤ t ^ (⌈ν⌉₊ : ℕ) * t ^ r *
          (t ^ p * (Real.exp (β * b ^ 2 / 2) * Real.exp (-(β * t / 2)))) := by
        refine mul_le_mul (mul_le_mul hrpow hlog (by positivity) (by positivity))
          (hker.trans (mul_le_mul_of_nonneg_right hsqrt (by positivity)))
          (phaseKernel_nonneg β b p t) (by positivity)
    _ = Real.exp (β * b ^ 2 / 2) * (t ^ m * Real.exp (-(β * t / 2))) := by rw [← hpowm]; ring
    _ ≤ Real.exp (β * b ^ 2 / 2) * (((m.factorial : ℝ) * (4 / β) ^ m * Real.exp (β * t / 4)) *
          Real.exp (-(β * t / 2))) := by gcongr
    _ = Real.exp (β * b ^ 2 / 2) * (m.factorial : ℝ) * (4 / β) ^ m * Real.exp (-(β * t / 4)) := by
        rw [mul_assoc ((m.factorial : ℝ) * (4 / β) ^ m), ← Real.exp_add,
          show β * t / 4 + -(β * t / 2) = -(β * t / 4) by ring]
        ring

theorem integrableOn_logMajorant_Ioi_one (β b ν : ℝ) (hβ : 0 < β) (r p : ℕ) :
    IntegrableOn (logMajorant β b ν r p) (Ioi 1) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 1 (by positivity : 0 < β / 4)).const_mul
    (tailConst β b p ν r)) ((continuousOn_logMajorant β b ν r p).mono
      (Ioi_subset_Ioi zero_le_one) |>.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  have ht1 : 1 < t := mem_Ioi.1 ht
  rw [Real.norm_eq_abs, abs_of_nonneg (logMajorant_nonneg β b ν r p (by linarith)),
    show -(β / 4) * t = -(β * t / 4) by ring]
  exact logMajorant_le β b ν hβ r p ht1.le

/-- **Integrability of the log majorant on `(0,∞)`** (Gate B: any real `b`, any `r, p`). -/
theorem integrableOn_logMajorant (β b ν : ℝ) (hβ : 0 < β) (hν : 0 < ν) (r p : ℕ) :
    IntegrableOn (logMajorant β b ν r p) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact (integrableOn_logMajorant_Ioc β b ν hν r p).union
    (integrableOn_logMajorant_Ioi_one β b ν hβ r p)

theorem phaseLogMoment_nonneg (β b ν : ℝ) (r p : ℕ) : 0 ≤ phaseLogMoment β b ν r p :=
  setIntegral_nonneg measurableSet_Ioi fun _ ht => logMajorant_nonneg β b ν r p (mem_Ioi.1 ht).le

/-! ### The phase series folds into the exponent -/

/-- `∑_p (βB)^p/p! (√t)^p = e^{βB√t}` (the exponential series). -/
theorem tsum_phase_series (β B t : ℝ) :
    ∑' p : ℕ, (β * B) ^ p / (p.factorial : ℝ) * Real.sqrt t ^ p =
      Real.exp (β * B * Real.sqrt t) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  simp only
  refine tsum_congr fun p => ?_
  rw [mul_pow]
  ring

theorem summable_phase_series (β B t : ℝ) :
    Summable fun p : ℕ => (β * B) ^ p / (p.factorial : ℝ) * Real.sqrt t ^ p := by
  have := Real.summable_pow_div_factorial (β * B * Real.sqrt t)
  refine this.congr fun p => ?_
  rw [mul_pow]
  ring

/-- Pointwise: `∑_p (βB)^p/p! · logMajorant β b ν r p t = logMajorant β (b+B) ν r 0 t`. -/
theorem tsum_logMajorant_series (β b B ν : ℝ) (r : ℕ) (t : ℝ) :
    ∑' p : ℕ, (β * B) ^ p / (p.factorial : ℝ) * logMajorant β b ν r p t =
      logMajorant β (b + B) ν r 0 t := by
  have hs := (summable_phase_series β B t).mul_right
    (t ^ (ν - 1) * (1 + |Real.log t|) ^ r * Real.exp (-(β * t) + β * Real.sqrt t * b))
  have hpt : ∀ p : ℕ, (β * B) ^ p / (p.factorial : ℝ) * logMajorant β b ν r p t =
      (β * B) ^ p / (p.factorial : ℝ) * Real.sqrt t ^ p *
        (t ^ (ν - 1) * (1 + |Real.log t|) ^ r * Real.exp (-(β * t) + β * Real.sqrt t * b)) := by
    intro p
    unfold logMajorant phaseKernel
    ring
  simp_rw [hpt]
  rw [tsum_mul_right, tsum_phase_series]
  unfold logMajorant phaseKernel
  rw [pow_zero, one_mul,
    show ∀ X A Y : ℝ, Real.exp X * (A * Real.exp Y) = A * (Real.exp X * Real.exp Y) from
      fun X A Y => by ring, ← Real.exp_add]
  congr 2
  ring

theorem summable_logMajorant_series (β b B ν : ℝ) (r : ℕ) (t : ℝ) :
    Summable fun p : ℕ => (β * B) ^ p / (p.factorial : ℝ) * logMajorant β b ν r p t := by
  have hs := (summable_phase_series β B t).mul_right
    (t ^ (ν - 1) * (1 + |Real.log t|) ^ r * Real.exp (-(β * t) + β * Real.sqrt t * b))
  refine hs.congr fun p => ?_
  unfold logMajorant phaseKernel
  ring

/-- Partial sums of the phase series are dominated by the folded majorant (`B ≥ 0`, `t > 0`). -/
theorem sum_range_logMajorant_le (β b B ν : ℝ) (hB : 0 ≤ B) (hβ : 0 ≤ β) (r : ℕ) {t : ℝ}
    (ht : 0 < t) (P : ℕ) :
    ∑ p ∈ Finset.range P, (β * B) ^ p / (p.factorial : ℝ) * logMajorant β b ν r p t ≤
      logMajorant β (b + B) ν r 0 t := by
  rw [← tsum_logMajorant_series β b B ν r t]
  exact (summable_logMajorant_series β b B ν r t).sum_le_tsum _
    (fun p _ => mul_nonneg (by positivity) (logMajorant_nonneg β b ν r p ht.le))

/-! ### The Tonelli majorant: integrate the folded series -/

theorem integrableOn_phase_series_term (β b B ν : ℝ) (hβ : 0 < β) (hν : 0 < ν) (r p : ℕ) :
    IntegrableOn (fun t => (β * B) ^ p / (p.factorial : ℝ) * logMajorant β b ν r p t) (Ioi 0) :=
  (integrableOn_logMajorant β b ν hβ hν r p).const_mul _

/-- Partial sums of the phase-moment series are bounded by the folded log moment. -/
theorem sum_range_phaseLogMoment_le (β b B ν : ℝ) (hβ : 0 < β) (hν : 0 < ν) (hB : 0 ≤ B) (r : ℕ)
    (P : ℕ) :
    ∑ p ∈ Finset.range P, (β * B) ^ p / (p.factorial : ℝ) * phaseLogMoment β b ν r p ≤
      phaseLogMoment β (b + B) ν r 0 := by
  unfold phaseLogMoment
  have h1 : ∑ p ∈ Finset.range P, (β * B) ^ p / (p.factorial : ℝ) *
      ∫ t in Ioi (0 : ℝ), logMajorant β b ν r p t =
      ∫ t in Ioi (0 : ℝ), ∑ p ∈ Finset.range P,
        (β * B) ^ p / (p.factorial : ℝ) * logMajorant β b ν r p t := by
    rw [integral_finsetSum _ fun p _ => integrableOn_phase_series_term β b B ν hβ hν r p]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_const_mul]
  rw [h1]
  refine setIntegral_mono_on (integrable_finsetSum _ fun p _ =>
    integrableOn_phase_series_term β b B ν hβ hν r p)
    (integrableOn_logMajorant β (b + B) ν hβ hν r 0) measurableSet_Ioi fun t ht => ?_
  exact sum_range_logMajorant_le β b B ν hB hβ.le r (mem_Ioi.1 ht) P

/-- **Absolute convergence of the phase-moment series** (Gate B). -/
theorem summable_phaseLogMoment_series (β b B ν : ℝ) (hβ : 0 < β) (hν : 0 < ν) (hB : 0 ≤ B)
    (r : ℕ) :
    Summable fun p : ℕ => (β * B) ^ p / (p.factorial : ℝ) * phaseLogMoment β b ν r p :=
  summable_of_sum_range_le (fun p => mul_nonneg (by positivity) (phaseLogMoment_nonneg β b ν r p))
    (sum_range_phaseLogMoment_le β b B ν hβ hν hB r)

/-- **Tonelli identity for the phase series**:
`∑_p (βB)^p/p! · M_{ν,r,p}(b) = M_{ν,r,0}(b+B)` for `β > 0`, `ν > 0`, `B ≥ 0`. -/
theorem tsum_phaseLogMoment_series (β b B ν : ℝ) (hβ : 0 < β) (hν : 0 < ν) (hB : 0 ≤ B) (r : ℕ) :
    ∑' p : ℕ, (β * B) ^ p / (p.factorial : ℝ) * phaseLogMoment β b ν r p =
      phaseLogMoment β (b + B) ν r 0 := by
  unfold phaseLogMoment
  have hnorm : Summable fun p : ℕ => ∫ t in Ioi (0 : ℝ),
      ‖(β * B) ^ p / (p.factorial : ℝ) * logMajorant β b ν r p t‖ := by
    refine (summable_phaseLogMoment_series β b B ν hβ hν hB r).congr fun p => ?_
    unfold phaseLogMoment
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (by positivity) (logMajorant_nonneg β b ν r p (mem_Ioi.1 ht).le))]
  have hsum := hasSum_integral_of_summable_integral_norm
    (fun p => integrableOn_phase_series_term β b B ν hβ hν r p) hnorm
  have h1 : ∀ p : ℕ, ∫ t in Ioi (0 : ℝ), (β * B) ^ p / (p.factorial : ℝ) * logMajorant β b ν r p t =
      (β * B) ^ p / (p.factorial : ℝ) * ∫ t in Ioi (0 : ℝ), logMajorant β b ν r p t :=
    fun p => integral_const_mul _ _
  simp_rw [h1] at hsum
  rw [hsum.tsum_eq]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => tsum_logMajorant_series β b B ν r t

end Laplace.Grammar
