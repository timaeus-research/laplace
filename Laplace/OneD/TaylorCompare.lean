/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.TaylorPackage

/-!
# Admissible potentials and the local Taylor comparison

Stage C3 of the smooth-germ programme, first installment: the
admissibility package. An `AdmissiblePotential` is continuous,
vanishes at `0`, has a global quadratic lower envelope and a local
quadratic upper envelope. These give the two workhorse order bounds:
the partition function is at least `C₀·q` (`admissible_partition_lower`
— restrict to `|x| ≤ q·δ`, where `t·K ≤ κ·δ²` by the scaling relation
`t·q² = 1`, so the integrand is bounded below by a constant on an
interval of length `2qδ`), and every signed moment is at most
`C_s·q^(s+1)` in absolute value (`admissible_moment_upper` — envelope
domination plus the exact scaling of stage C2).
-/

open Real MeasureTheory Filter Topology

namespace Laplace.OneD

open Laplace

/-- The admissibility package for a global potential: continuity, a
normalized minimum, a global quadratic lower envelope, and a local
quadratic upper envelope. -/
structure AdmissiblePotential (K : ℝ → ℝ) (ρ κ δ : ℝ) : Prop where
  cont : Continuous K
  zero : K 0 = 0
  lower : ∀ x, ρ * x ^ 2 ≤ K x
  upper_near : ∀ x, |x| ≤ δ → K x ≤ κ * x ^ 2
  rho_pos : 0 < ρ
  kappa_pos : 0 < κ
  delta_pos : 0 < δ

/-- Every polynomial moment of an admissible Gibbs weight is
integrable. -/
theorem AdmissiblePotential.integrable_pow
    {K : ℝ → ℝ} {ρ κ δ : ℝ} (h : AdmissiblePotential K ρ κ δ)
    (s : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ ↦ x ^ s * Real.exp (-(t * K x))) := by
  have hdom := integrable_abs_pow_mul_exp_neg_kth (k := 1)
    le_rfl s (ρ := t * ρ) (mul_pos ht h.rho_pos)
  have hdom' : Integrable (fun x : ℝ ↦
      |x| ^ s * Real.exp (-(t * ρ * x ^ 2))) := by
    refine hdom.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    norm_num
  refine hdom'.mono' ?_ (Filter.Eventually.of_forall fun x ↦ ?_)
  · exact ((continuous_pow s).mul (Real.continuous_exp.comp
      (h.cont.const_smul t).neg)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (h.lower x) ht.le
    linarith

/-- **The partition lower bound** (re-scoped C2.4): under the scaling
relation `t·q² = 1` with `0 < q ≤ 1`, the admissible partition
function is at least `C₀·q` with `C₀ = 2δ·e^(-κδ²)`. -/
theorem AdmissiblePotential.partition_lower
    {K : ℝ → ℝ} {ρ κ δ : ℝ} (h : AdmissiblePotential K ρ κ δ)
    {t q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hqt : t * q ^ 2 = 1) :
    2 * δ * Real.exp (-(κ * δ ^ 2)) * q ≤
      ∫ x : ℝ, Real.exp (-(t * K x)) := by
  have ht : 0 < t := by nlinarith [sq_nonneg q]
  have hint : Integrable (fun x : ℝ ↦ Real.exp (-(t * K x))) := by
    have hi := h.integrable_pow 0 ht
    exact hi.congr (Filter.Eventually.of_forall fun x ↦ by simp)
  have hset : MeasurableSet (Set.Icc (-(q * δ)) (q * δ)) :=
    measurableSet_Icc
  -- Pointwise: on |x| ≤ q·δ the exponent is at most κ·δ².
  have hpt : ∀ x ∈ Set.Icc (-(q * δ)) (q * δ),
      Real.exp (-(κ * δ ^ 2)) ≤ Real.exp (-(t * K x)) := by
    intro x hx
    apply Real.exp_le_exp.mpr
    have hxd : |x| ≤ q * δ := abs_le.mpr ⟨hx.1, hx.2⟩
    have hxδ : |x| ≤ δ := le_trans hxd (by nlinarith [h.delta_pos])
    have hK : K x ≤ κ * x ^ 2 := h.upper_near x hxδ
    have hx2 : x ^ 2 ≤ (q * δ) ^ 2 := by
      rw [← sq_abs x]
      exact pow_le_pow_left₀ (abs_nonneg x) hxd 2
    have hchain : t * K x ≤ κ * δ ^ 2 := by
      have h1 : t * K x ≤ t * (κ * x ^ 2) :=
        mul_le_mul_of_nonneg_left hK ht.le
      have h2 : t * (κ * x ^ 2) ≤ t * (κ * (q * δ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ ht.le
        exact mul_le_mul_of_nonneg_left hx2 h.kappa_pos.le
      have h3 : t * (κ * (q * δ) ^ 2) = κ * δ ^ 2 := by
        have : t * (κ * (q * δ) ^ 2) = κ * δ ^ 2 * (t * q ^ 2) := by
          ring
        rw [this, hqt, mul_one]
      linarith
    linarith
  have hle := setIntegral_ge_of_const_le hset
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hpt
    hint.integrableOn
  rw [smul_eq_mul] at hle
  have hvol : volume.real (Set.Icc (-(q * δ)) (q * δ)) =
      2 * (q * δ) := by
    rw [measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal
        (by nlinarith [h.delta_pos] : (0:ℝ) ≤ q * δ - -(q * δ))]
    ring
  rw [hvol] at hle
  calc 2 * δ * Real.exp (-(κ * δ ^ 2)) * q
      = 2 * (q * δ) * Real.exp (-(κ * δ ^ 2)) := by ring
    _ ≤ ∫ x in Set.Icc (-(q * δ)) (q * δ),
          Real.exp (-(t * K x)) := hle
    _ ≤ ∫ x : ℝ, Real.exp (-(t * K x)) :=
        setIntegral_le_integral hint
          (Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le)

/-- **The moment upper bound**: under the scaling relation, every
signed admissible moment is at most `C_s·q^(s+1)` in absolute value,
with `C_s` the reference absolute moment of the envelope Gaussian. -/
theorem AdmissiblePotential.moment_upper
    {K : ℝ → ℝ} {ρ κ δ : ℝ} (h : AdmissiblePotential K ρ κ δ)
    (s : ℕ) {t q : ℝ} (hq : 0 < q) (hqt : t * q ^ 2 = 1) :
    |∫ x : ℝ, x ^ s * Real.exp (-(t * K x))| ≤
      (∫ y : ℝ, |y| ^ s * Real.exp (-(ρ * y ^ 2))) * q ^ (s + 1) := by
  have ht : 0 < t := by nlinarith [sq_nonneg q]
  have habs_int : Integrable (fun x : ℝ ↦
      |x| ^ s * Real.exp (-(t * (ρ * x ^ 2)))) := by
    have hi := integrable_abs_pow_mul_exp_neg_kth (k := 1)
      le_rfl s (ρ := t * ρ) (mul_pos ht h.rho_pos)
    refine hi.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [mul_assoc]
  calc |∫ x : ℝ, x ^ s * Real.exp (-(t * K x))|
      ≤ ∫ x : ℝ, |x ^ s * Real.exp (-(t * K x))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x : ℝ, |x| ^ s * Real.exp (-(t * (ρ * x ^ 2))) := by
        apply integral_mono (h.integrable_pow s ht).abs habs_int
        intro x
        simp only [abs_mul, abs_pow, Real.abs_exp]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left (h.lower x) ht.le
        linarith
    _ = q ^ (s + 1) * ∫ y : ℝ, |y| ^ s * Real.exp (-(ρ * y ^ 2)) :=
        abs_moment_scaling s hq hqt
    _ = (∫ y : ℝ, |y| ^ s * Real.exp (-(ρ * y ^ 2))) * q ^ (s + 1) := by
        ring

/-- The scaled outer tail vanishes: `e^(-(c/q))/q^n → 0` as `q → 0⁺`
(exponential beats every power after the substitution `u = 1/q`). -/
theorem exp_neg_div_tendsto_zero {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Tendsto (fun q : ℝ ↦ Real.exp (-(c / q)) / q ^ n) (𝓝[>] 0)
      (𝓝 0) := by
  have hbase : Tendsto (fun v : ℝ ↦ v ^ n * Real.exp (-v))
      atTop (𝓝 0) := tendsto_pow_mul_exp_neg_atTop_nhds_zero n
  have hscale : Tendsto (fun u : ℝ ↦ c * u) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc tendsto_id
  have hcomp : Tendsto (fun u : ℝ ↦ (c * u) ^ n * Real.exp (-(c * u)))
      atTop (𝓝 0) := hbase.comp hscale
  have hconst : Tendsto (fun u : ℝ ↦
      (1 / c ^ n) * ((c * u) ^ n * Real.exp (-(c * u))))
      atTop (𝓝 ((1 / c ^ n) * 0)) := hcomp.const_mul _
  rw [mul_zero] at hconst
  have hu : Tendsto (fun u : ℝ ↦ u ^ n * Real.exp (-(c * u)))
      atTop (𝓝 0) := by
    refine hconst.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [mul_pow]
    field_simp
  have hinv : Tendsto (fun q : ℝ ↦ q⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero
  have := hu.comp hinv
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq0 : (0 : ℝ) < q := hq
  simp only [Function.comp_apply]
  rw [div_eq_mul_inv (Real.exp _), inv_pow, ← inv_pow]
  rw [show -(c * q⁻¹) = -(c / q) by field_simp]
  ring

set_option maxHeartbeats 3200000 in
-- The assembled epsilon-of-room proof combines ~10 integral
-- manipulations in one calc; this exceeds the default heartbeat
-- budget in `isDefEq` (see CLAUDE.md).
/-- **The local Taylor comparison, unnormalized** (stage C3 main):
for admissible potentials whose difference is `o(|x|^D)` at `0` in
epsilon-radius form, the moment difference is `o(q^(s+D-1))` along
`q → 0⁺`. Split at `|x| = √q`: inside, the secant bound and the jet
hypothesis (keeping the power `|x|^D` inside the Gaussian integral);
outside, two applications of the envelope tail bound with the
`e^(-c/q)` prefactor. -/
theorem admissible_moment_difference_littleO
    {K₁ K₂ : ℝ → ℝ} {ρ₁ κ₁ δ₁ ρ₂ κ₂ δ₂ : ℝ} {D : ℕ} (hD : 2 ≤ D)
    (h1 : AdmissiblePotential K₁ ρ₁ κ₁ δ₁)
    (h2 : AdmissiblePotential K₂ ρ₂ κ₂ δ₂)
    (hjet : ∀ ε : ℝ, 0 < ε → ∃ δ' : ℝ, 0 < δ' ∧ ∀ x : ℝ, |x| ≤ δ' →
      |K₁ x - K₂ x| ≤ ε * |x| ^ D)
    (s : ℕ) :
    Tendsto (fun q : ℝ ↦
      ((∫ x : ℝ, x ^ s * Real.exp (-((q ^ 2)⁻¹ * K₁ x))) -
        ∫ x : ℝ, x ^ s * Real.exp (-((q ^ 2)⁻¹ * K₂ x))) /
        q ^ (s + D - 1))
      (𝓝[>] 0) (𝓝 0) := by
  have hρ1 := h1.rho_pos
  have hρ2 := h2.rho_pos
  set ρ : ℝ := min ρ₁ ρ₂ with hρ_def
  have hρ : 0 < ρ := lt_min hρ1 hρ2
  set C : ℝ := ∫ y : ℝ, |y| ^ (s + D) * Real.exp (-(ρ * y ^ 2))
    with hC_def
  have hC0 : 0 ≤ C :=
    integral_nonneg fun y ↦ by positivity
  set CT₁ : ℝ := ∫ y : ℝ, |y| ^ s * Real.exp (-(ρ₁ / 2 * y ^ 2))
    with hCT₁_def
  set CT₂ : ℝ := ∫ y : ℝ, |y| ^ s * Real.exp (-(ρ₂ / 2 * y ^ 2))
    with hCT₂_def
  have hCT₁0 : 0 ≤ CT₁ := integral_nonneg fun y ↦ by positivity
  have hCT₂0 : 0 ≤ CT₂ := integral_nonneg fun y ↦ by positivity
  -- The two outer bound functions tend to zero.
  have houter₁ : Tendsto (fun q : ℝ ↦
      CT₁ * (Real.exp (-(ρ₁ / 2 / q)) / q ^ (D - 2))) (𝓝[>] 0)
      (𝓝 0) := by
    have := (exp_neg_div_tendsto_zero
      (by positivity : (0:ℝ) < ρ₁ / 2) (D - 2)).const_mul CT₁
    rwa [mul_zero] at this
  have houter₂ : Tendsto (fun q : ℝ ↦
      CT₂ * (Real.exp (-(ρ₂ / 2 / q)) / q ^ (D - 2))) (𝓝[>] 0)
      (𝓝 0) := by
    have := (exp_neg_div_tendsto_zero
      (by positivity : (0:ℝ) < ρ₂ / 2) (D - 2)).const_mul CT₂
    rwa [mul_zero] at this
  rw [Metric.tendsto_nhds]
  intro η hη
  set M : ℝ := max C 1 with hM_def
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  set εj : ℝ := η / (4 * M) with hεj_def
  have hεj : 0 < εj := by positivity
  obtain ⟨δ', hδ', hjet_loc⟩ := hjet εj hεj
  have hout₁ := (Metric.tendsto_nhds.mp houter₁) (η / 4)
    (by positivity)
  have hout₂ := (Metric.tendsto_nhds.mp houter₂) (η / 4)
    (by positivity)
  filter_upwards [Ioc_mem_nhdsGT
      (lt_min (lt_min one_pos (by positivity : (0:ℝ) < δ' ^ 2))
        (by positivity : (0:ℝ) < 1)), hout₁, hout₂,
    self_mem_nhdsWithin] with q hq ho₁ ho₂ hqpos
  obtain ⟨hq0, hqle⟩ := hq
  have hq1 : q ≤ 1 := le_trans hqle (le_trans (min_le_left _ _)
    (min_le_left _ _))
  have hqδ : q ≤ δ' ^ 2 := le_trans hqle (le_trans (min_le_left _ _)
    (min_le_right _ _))
  set t : ℝ := (q ^ 2)⁻¹ with ht_def
  have ht : 0 < t := by positivity
  have hqt : t * q ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
  have hr0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hrδ : Real.sqrt q ≤ δ' := by
    calc Real.sqrt q ≤ Real.sqrt (δ' ^ 2) := Real.sqrt_le_sqrt hqδ
      _ = δ' := Real.sqrt_sq hδ'.le
  -- The integrand difference and the region split.
  set S : Set ℝ := {x : ℝ | Real.sqrt q ≤ |x|} with hS_def
  have hSmeas : MeasurableSet S :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  have hint₁ := h1.integrable_pow s ht
  have hint₂ := h2.integrable_pow s ht
  have hf_int : Integrable (fun x : ℝ ↦
      x ^ s * Real.exp (-(t * K₁ x)) -
        x ^ s * Real.exp (-(t * K₂ x))) := hint₁.sub hint₂
  -- Tail part: bounded via the two envelope tails.
  have htail₁ := tail_integral_le hρ1 ht hr0.le h1.lower h1.cont s
  have htail₂ := tail_integral_le hρ2 ht hr0.le h2.lower h2.cont s
  have hhalf₁ : (∫ x : ℝ, |x| ^ s *
      Real.exp (-(t / 2 * (ρ₁ * x ^ 2)))) = q ^ (s + 1) * CT₁ := by
    have hs := abs_moment_scaling (a := ρ₁ / 2) (t := t) (q := q)
      s hq0 hqt
    rw [show (fun x : ℝ ↦ |x| ^ s *
        Real.exp (-(t * (ρ₁ / 2 * x ^ 2)))) = fun x : ℝ ↦ |x| ^ s *
        Real.exp (-(t / 2 * (ρ₁ * x ^ 2))) from funext fun x ↦ by
      rw [show t * (ρ₁ / 2 * x ^ 2) = t / 2 * (ρ₁ * x ^ 2) by ring]]
      at hs
    rw [hs, hCT₁_def]
  have hhalf₂ : (∫ x : ℝ, |x| ^ s *
      Real.exp (-(t / 2 * (ρ₂ * x ^ 2)))) = q ^ (s + 1) * CT₂ := by
    have hs := abs_moment_scaling (a := ρ₂ / 2) (t := t) (q := q)
      s hq0 hqt
    rw [show (fun x : ℝ ↦ |x| ^ s *
        Real.exp (-(t * (ρ₂ / 2 * x ^ 2)))) = fun x : ℝ ↦ |x| ^ s *
        Real.exp (-(t / 2 * (ρ₂ * x ^ 2))) from funext fun x ↦ by
      rw [show t * (ρ₂ / 2 * x ^ 2) = t / 2 * (ρ₂ * x ^ 2) by ring]]
      at hs
    rw [hs, hCT₂_def]
  have hpref₁ : Real.exp (-(t / 2 * (ρ₁ * Real.sqrt q ^ 2))) =
      Real.exp (-(ρ₁ / 2 / q)) := by
    congr 1
    rw [Real.sq_sqrt hq0.le, ht_def]
    field_simp
  have hpref₂ : Real.exp (-(t / 2 * (ρ₂ * Real.sqrt q ^ 2))) =
      Real.exp (-(ρ₂ / 2 / q)) := by
    congr 1
    rw [Real.sq_sqrt hq0.le, ht_def]
    field_simp
  -- q-power arithmetic.
  have hqpow : q ^ (s + 1) = q ^ (s + D - 1) / q ^ (D - 2) := by
    rw [eq_div_iff (by positivity : (q : ℝ) ^ (D - 2) ≠ 0), ← pow_add]
    congr 1
    omega
  -- Tail bounds in scaled form.
  have htail₁' : (∫ x in S, |x| ^ s * Real.exp (-(t * K₁ x))) ≤
      CT₁ * (Real.exp (-(ρ₁ / 2 / q)) / q ^ (D - 2)) *
        q ^ (s + D - 1) := by
    calc (∫ x in S, |x| ^ s * Real.exp (-(t * K₁ x)))
        ≤ Real.exp (-(t / 2 * (ρ₁ * Real.sqrt q ^ 2))) *
          ∫ x : ℝ, |x| ^ s * Real.exp (-(t / 2 * (ρ₁ * x ^ 2))) :=
          htail₁
      _ = Real.exp (-(ρ₁ / 2 / q)) * (q ^ (s + 1) * CT₁) := by
          rw [hpref₁, hhalf₁]
      _ = CT₁ * (Real.exp (-(ρ₁ / 2 / q)) / q ^ (D - 2)) *
          q ^ (s + D - 1) := by
          rw [hqpow]
          have hd2 : (0:ℝ) < q ^ (D - 2) := by positivity
          field_simp
  have htail₂' : (∫ x in S, |x| ^ s * Real.exp (-(t * K₂ x))) ≤
      CT₂ * (Real.exp (-(ρ₂ / 2 / q)) / q ^ (D - 2)) *
        q ^ (s + D - 1) := by
    calc (∫ x in S, |x| ^ s * Real.exp (-(t * K₂ x)))
        ≤ Real.exp (-(t / 2 * (ρ₂ * Real.sqrt q ^ 2))) *
          ∫ x : ℝ, |x| ^ s * Real.exp (-(t / 2 * (ρ₂ * x ^ 2))) :=
          htail₂
      _ = Real.exp (-(ρ₂ / 2 / q)) * (q ^ (s + 1) * CT₂) := by
          rw [hpref₂, hhalf₂]
      _ = CT₂ * (Real.exp (-(ρ₂ / 2 / q)) / q ^ (D - 2)) *
          q ^ (s + D - 1) := by
          rw [hqpow]
          have hd2 : (0:ℝ) < q ^ (D - 2) := by positivity
          field_simp
  -- Absolute-value forms of the two Gibbs integrands.
  have habs₁ : Integrable (fun x : ℝ ↦
      |x| ^ s * Real.exp (-(t * K₁ x))) :=
    hint₁.abs.congr (Filter.Eventually.of_forall fun x ↦ by
      simp [abs_mul, abs_pow, Real.abs_exp])
  have habs₂ : Integrable (fun x : ℝ ↦
      |x| ^ s * Real.exp (-(t * K₂ x))) :=
    hint₂.abs.congr (Filter.Eventually.of_forall fun x ↦ by
      simp [abs_mul, abs_pow, Real.abs_exp])
  -- Tail part of the difference.
  have htail_abs : |∫ x in S, (x ^ s * Real.exp (-(t * K₁ x)) -
      x ^ s * Real.exp (-(t * K₂ x)))| ≤
      (∫ x in S, |x| ^ s * Real.exp (-(t * K₁ x))) +
        ∫ x in S, |x| ^ s * Real.exp (-(t * K₂ x)) := by
    calc |∫ x in S, (x ^ s * Real.exp (-(t * K₁ x)) -
          x ^ s * Real.exp (-(t * K₂ x)))|
        ≤ ∫ x in S, |x ^ s * Real.exp (-(t * K₁ x)) -
            x ^ s * Real.exp (-(t * K₂ x))| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x in S, (|x| ^ s * Real.exp (-(t * K₁ x)) +
            |x| ^ s * Real.exp (-(t * K₂ x))) := by
          apply setIntegral_mono_on hf_int.abs.integrableOn
            (habs₁.add habs₂).integrableOn hSmeas
          intro x _
          calc |x ^ s * Real.exp (-(t * K₁ x)) -
                x ^ s * Real.exp (-(t * K₂ x))|
              ≤ |x ^ s * Real.exp (-(t * K₁ x))| +
                |x ^ s * Real.exp (-(t * K₂ x))| := abs_sub _ _
            _ = |x| ^ s * Real.exp (-(t * K₁ x)) +
                |x| ^ s * Real.exp (-(t * K₂ x)) := by
                rw [abs_mul, abs_pow, Real.abs_exp,
                  abs_mul, abs_pow, Real.abs_exp]
      _ = (∫ x in S, |x| ^ s * Real.exp (-(t * K₁ x))) +
            ∫ x in S, |x| ^ s * Real.exp (-(t * K₂ x)) :=
          integral_add habs₁.integrableOn habs₂.integrableOn
  -- Inner part of the difference.
  have hmaj : Integrable (fun x : ℝ ↦ εj * t *
      (|x| ^ (s + D) * Real.exp (-(t * (ρ * x ^ 2))))) := by
    have hi := integrable_abs_pow_mul_exp_neg_kth (k := 1)
      le_rfl (s + D) (ρ := t * ρ) (mul_pos ht hρ)
    exact (hi.congr (Filter.Eventually.of_forall fun x ↦ by
      simp only [mul_assoc])).const_mul _
  have hinner_abs : |∫ x in Sᶜ, (x ^ s * Real.exp (-(t * K₁ x)) -
      x ^ s * Real.exp (-(t * K₂ x)))| ≤
      εj * C * q ^ (s + D - 1) := by
    have hpt_inner : ∀ x ∈ Sᶜ,
        |x ^ s * Real.exp (-(t * K₁ x)) -
          x ^ s * Real.exp (-(t * K₂ x))| ≤
        εj * t * (|x| ^ (s + D) * Real.exp (-(t * (ρ * x ^ 2)))) := by
      intro x hx
      have hxr : |x| < Real.sqrt q := by
        have := hx
        simp only [hS_def, Set.mem_compl_iff, Set.mem_setOf_eq,
          not_le] at this
        exact this
      have hxδ : |x| ≤ δ' := le_trans hxr.le hrδ
      have hsec := exp_secant_le (t * K₁ x) (t * K₂ x)
      have hmax : max (Real.exp (-(t * K₁ x)))
          (Real.exp (-(t * K₂ x))) ≤
          Real.exp (-(t * (ρ * x ^ 2))) := by
        apply max_le
        · apply Real.exp_le_exp.mpr
          have hl : ρ * x ^ 2 ≤ K₁ x := le_trans
            (mul_le_mul_of_nonneg_right (min_le_left _ _)
              (sq_nonneg x)) (h1.lower x)
          nlinarith
        · apply Real.exp_le_exp.mpr
          have hl : ρ * x ^ 2 ≤ K₂ x := le_trans
            (mul_le_mul_of_nonneg_right (min_le_right _ _)
              (sq_nonneg x)) (h2.lower x)
          nlinarith
      have hjetx := hjet_loc x hxδ
      calc |x ^ s * Real.exp (-(t * K₁ x)) -
            x ^ s * Real.exp (-(t * K₂ x))|
          = |x| ^ s * |Real.exp (-(t * K₁ x)) -
              Real.exp (-(t * K₂ x))| := by
            rw [show x ^ s * Real.exp (-(t * K₁ x)) -
                x ^ s * Real.exp (-(t * K₂ x)) =
                x ^ s * (Real.exp (-(t * K₁ x)) -
                  Real.exp (-(t * K₂ x))) by ring,
              abs_mul, abs_pow]
        _ ≤ |x| ^ s * (|t * K₁ x - t * K₂ x| *
              max (Real.exp (-(t * K₁ x)))
                (Real.exp (-(t * K₂ x)))) :=
            mul_le_mul_of_nonneg_left hsec (by positivity)
        _ ≤ |x| ^ s * ((t * (εj * |x| ^ D)) *
              Real.exp (-(t * (ρ * x ^ 2)))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul _ hmax
              (le_trans (Real.exp_pos _).le (le_max_left _ _))
              (by positivity)
            rw [show t * K₁ x - t * K₂ x = t * (K₁ x - K₂ x) by ring,
              abs_mul, abs_of_pos ht]
            exact mul_le_mul_of_nonneg_left hjetx ht.le
        _ = εj * t * (|x| ^ (s + D) *
              Real.exp (-(t * (ρ * x ^ 2)))) := by
            rw [pow_add]
            ring
    calc |∫ x in Sᶜ, (x ^ s * Real.exp (-(t * K₁ x)) -
          x ^ s * Real.exp (-(t * K₂ x)))|
        ≤ ∫ x in Sᶜ, |x ^ s * Real.exp (-(t * K₁ x)) -
            x ^ s * Real.exp (-(t * K₂ x))| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x in Sᶜ, εj * t * (|x| ^ (s + D) *
            Real.exp (-(t * (ρ * x ^ 2)))) :=
          setIntegral_mono_on hf_int.abs.integrableOn
            hmaj.integrableOn hSmeas.compl hpt_inner
      _ ≤ ∫ x : ℝ, εj * t * (|x| ^ (s + D) *
            Real.exp (-(t * (ρ * x ^ 2)))) :=
          setIntegral_le_integral hmaj
            (Filter.Eventually.of_forall fun x ↦ by positivity)
      _ = εj * t * (q ^ (s + D + 1) * C) := by
          rw [integral_const_mul,
            abs_moment_scaling (a := ρ) (s + D) hq0 hqt, hC_def]
      _ = εj * C * q ^ (s + D - 1) := by
          rw [ht_def, show s + D + 1 = (s + D - 1) + 2 by omega,
            pow_add]
          field_simp
  -- Decomposition and assembly.
  have hsplit : (∫ x : ℝ, x ^ s * Real.exp (-(t * K₁ x))) -
      (∫ x : ℝ, x ^ s * Real.exp (-(t * K₂ x))) =
      (∫ x in S, (x ^ s * Real.exp (-(t * K₁ x)) -
        x ^ s * Real.exp (-(t * K₂ x)))) +
      ∫ x in Sᶜ, (x ^ s * Real.exp (-(t * K₁ x)) -
        x ^ s * Real.exp (-(t * K₂ x))) := by
    rw [← integral_sub hint₁ hint₂]
    exact (integral_add_compl hSmeas hf_int).symm
  rw [Real.dist_eq, sub_zero]
  have hqp : (0 : ℝ) < q ^ (s + D - 1) := by positivity
  rw [abs_div, abs_of_pos hqp, div_lt_iff₀ hqp]
  -- Convert the two outer smallness facts.
  rw [Real.dist_eq, sub_zero] at ho₁ ho₂
  have hb₁ : CT₁ * (Real.exp (-(ρ₁ / 2 / q)) / q ^ (D - 2)) < η / 4 :=
    lt_of_abs_lt ho₁
  have hb₂ : CT₂ * (Real.exp (-(ρ₂ / 2 / q)) / q ^ (D - 2)) < η / 4 :=
    lt_of_abs_lt ho₂
  have hεC : εj * C ≤ η / 4 := by
    rw [hεj_def]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity)
      (by norm_num : (0:ℝ) < 4)]
    have hCM : C ≤ M := le_max_left _ _
    nlinarith
  calc |(∫ x : ℝ, x ^ s * Real.exp (-(t * K₁ x))) -
        ∫ x : ℝ, x ^ s * Real.exp (-(t * K₂ x))|
      = |(∫ x in S, (x ^ s * Real.exp (-(t * K₁ x)) -
          x ^ s * Real.exp (-(t * K₂ x)))) +
        ∫ x in Sᶜ, (x ^ s * Real.exp (-(t * K₁ x)) -
          x ^ s * Real.exp (-(t * K₂ x)))| := by rw [hsplit]
    _ ≤ |∫ x in S, (x ^ s * Real.exp (-(t * K₁ x)) -
          x ^ s * Real.exp (-(t * K₂ x)))| +
        |∫ x in Sᶜ, (x ^ s * Real.exp (-(t * K₁ x)) -
          x ^ s * Real.exp (-(t * K₂ x)))| := abs_add_le _ _
    _ ≤ ((∫ x in S, |x| ^ s * Real.exp (-(t * K₁ x))) +
          ∫ x in S, |x| ^ s * Real.exp (-(t * K₂ x))) +
        εj * C * q ^ (s + D - 1) := add_le_add htail_abs hinner_abs
    _ ≤ (CT₁ * (Real.exp (-(ρ₁ / 2 / q)) / q ^ (D - 2)) *
          q ^ (s + D - 1) +
        CT₂ * (Real.exp (-(ρ₂ / 2 / q)) / q ^ (D - 2)) *
          q ^ (s + D - 1)) +
        εj * C * q ^ (s + D - 1) := by
        have := add_le_add htail₁' htail₂'
        linarith
    _ < η * q ^ (s + D - 1) := by nlinarith [hqp, hb₁, hb₂, hεC,
        mul_le_mul_of_nonneg_right hεC hqp.le]

set_option maxHeartbeats 1600000 in
-- Quotient bookkeeping over four integral atoms exceeds the default
-- heartbeat budget in `isDefEq` (see CLAUDE.md).
/-- **The local Taylor comparison, normalized** (stage C3 quotient):
under the same hypotheses, the difference of normalized moments is
`o(q^(s+D-2))`. Decompose
`F₁ - F₂ = (A₁ - A₂)/Z₁ + A₂(Z₂ - Z₁)/(Z₁Z₂)` and squeeze against
the unnormalized limits using `Z ≥ C₀q` and `|A| ≤ Cq^(s+1)`. -/
theorem admissible_normalized_difference_littleO
    {K₁ K₂ : ℝ → ℝ} {ρ₁ κ₁ δ₁ ρ₂ κ₂ δ₂ : ℝ} {D : ℕ} (hD : 2 ≤ D)
    (h1 : AdmissiblePotential K₁ ρ₁ κ₁ δ₁)
    (h2 : AdmissiblePotential K₂ ρ₂ κ₂ δ₂)
    (hjet : ∀ ε : ℝ, 0 < ε → ∃ δ' : ℝ, 0 < δ' ∧ ∀ x : ℝ, |x| ≤ δ' →
      |K₁ x - K₂ x| ≤ ε * |x| ^ D)
    (s : ℕ) :
    Tendsto (fun q : ℝ ↦
      ((∫ x : ℝ, x ^ s * Real.exp (-((q ^ 2)⁻¹ * K₁ x))) /
          (∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * K₁ x))) -
        (∫ x : ℝ, x ^ s * Real.exp (-((q ^ 2)⁻¹ * K₂ x))) /
          (∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * K₂ x)))) /
        q ^ (s + D - 2))
      (𝓝[>] 0) (𝓝 0) := by
  set C₀₁ : ℝ := 2 * δ₁ * Real.exp (-(κ₁ * δ₁ ^ 2)) with hC₀₁_def
  set C₀₂ : ℝ := 2 * δ₂ * Real.exp (-(κ₂ * δ₂ ^ 2)) with hC₀₂_def
  have hC₀₁ : 0 < C₀₁ := by
    have := h1.delta_pos
    positivity
  have hC₀₂ : 0 < C₀₂ := by
    have := h2.delta_pos
    positivity
  set C₂ : ℝ := ∫ y : ℝ, |y| ^ s * Real.exp (-(ρ₂ * y ^ 2))
    with hC₂_def
  have hC₂0 : 0 ≤ C₂ := integral_nonneg fun y ↦ by positivity
  -- The two unnormalized limits (s and 0), in |·| form.
  have hmain_s := (admissible_moment_difference_littleO hD h1 h2
    hjet s).abs
  rw [abs_zero] at hmain_s
  have hmain_0 : Tendsto (fun q : ℝ ↦
      |((∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * K₁ x))) -
        ∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * K₂ x))) / q ^ (D - 1)|)
      (𝓝[>] 0) (𝓝 0) := by
    have h := (admissible_moment_difference_littleO hD h1 h2
      hjet 0).abs
    rw [abs_zero] at h
    have heq : (fun q : ℝ ↦
        |((∫ x : ℝ, x ^ 0 * Real.exp (-((q ^ 2)⁻¹ * K₁ x))) -
          ∫ x : ℝ, x ^ 0 * Real.exp (-((q ^ 2)⁻¹ * K₂ x))) /
          q ^ (0 + D - 1)|) = fun q : ℝ ↦
        |((∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * K₁ x))) -
          ∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * K₂ x))) / q ^ (D - 1)| := by
      funext q
      have e₁ : (∫ x : ℝ, x ^ 0 * Real.exp (-((q ^ 2)⁻¹ * K₁ x))) =
          ∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * K₁ x)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by simp)
      have e₂ : (∫ x : ℝ, x ^ 0 * Real.exp (-((q ^ 2)⁻¹ * K₂ x))) =
          ∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * K₂ x)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by simp)
      rw [e₁, e₂, show (0 : ℕ) + D - 1 = D - 1 by omega]
    rwa [heq] at h
  -- The squeeze bound function.
  have hbound : Tendsto (fun q : ℝ ↦
      (1 / C₀₁) * |((∫ x : ℝ, x ^ s * Real.exp (-((q ^ 2)⁻¹ * K₁ x))) -
          ∫ x : ℝ, x ^ s * Real.exp (-((q ^ 2)⁻¹ * K₂ x))) /
          q ^ (s + D - 1)| +
        (C₂ / (C₀₁ * C₀₂)) *
          |((∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * K₁ x))) -
            ∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * K₂ x))) / q ^ (D - 1)|)
      (𝓝[>] 0) (𝓝 0) := by
    have := (hmain_s.const_mul (1 / C₀₁)).add
      (hmain_0.const_mul (C₂ / (C₀₁ * C₀₂)))
    simpa using this
  apply squeeze_zero_norm' _ hbound
  filter_upwards [Ioc_mem_nhdsGT one_pos, self_mem_nhdsWithin]
    with q hq _
  obtain ⟨hq0, hq1⟩ := hq
  set t : ℝ := (q ^ 2)⁻¹ with ht_def
  have ht : 0 < t := by positivity
  have hqt : t * q ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
  set A₁ : ℝ := ∫ x : ℝ, x ^ s * Real.exp (-(t * K₁ x)) with hA₁_def
  set A₂ : ℝ := ∫ x : ℝ, x ^ s * Real.exp (-(t * K₂ x)) with hA₂_def
  set Z₁ : ℝ := ∫ x : ℝ, Real.exp (-(t * K₁ x)) with hZ₁_def
  set Z₂ : ℝ := ∫ x : ℝ, Real.exp (-(t * K₂ x)) with hZ₂_def
  have hZ₁l : C₀₁ * q ≤ Z₁ := h1.partition_lower hq0 hq1 hqt
  have hZ₂l : C₀₂ * q ≤ Z₂ := h2.partition_lower hq0 hq1 hqt
  have hZ₁p : 0 < Z₁ := lt_of_lt_of_le (by positivity) hZ₁l
  have hZ₂p : 0 < Z₂ := lt_of_lt_of_le (by positivity) hZ₂l
  have hA₂u : |A₂| ≤ C₂ * q ^ (s + 1) := h2.moment_upper s hq0 hqt
  -- The decomposition and the elementary bound.
  have hdecomp : A₁ / Z₁ - A₂ / Z₂ =
      (A₁ - A₂) / Z₁ + A₂ * (Z₂ - Z₁) / (Z₁ * Z₂) := by
    field_simp
    ring
  have hqp : (0 : ℝ) < q ^ (s + D - 2) := by positivity
  rw [Real.norm_eq_abs]
  have habs_decomp : |A₁ / Z₁ - A₂ / Z₂| ≤
      |A₁ - A₂| / Z₁ + |A₂| * |Z₂ - Z₁| / (Z₁ * Z₂) := by
    rw [hdecomp]
    calc |(A₁ - A₂) / Z₁ + A₂ * (Z₂ - Z₁) / (Z₁ * Z₂)|
        ≤ |(A₁ - A₂) / Z₁| + |A₂ * (Z₂ - Z₁) / (Z₁ * Z₂)| :=
          abs_add_le _ _
      _ = |A₁ - A₂| / Z₁ + |A₂| * |Z₂ - Z₁| / (Z₁ * Z₂) := by
          rw [abs_div, abs_of_pos hZ₁p, abs_div, abs_mul,
            abs_of_pos (mul_pos hZ₁p hZ₂p)]
  have hden₁ : C₀₁ * q ^ (s + D - 1) ≤ Z₁ * q ^ (s + D - 2) := by
    calc C₀₁ * q ^ (s + D - 1) = C₀₁ * q * q ^ (s + D - 2) := by
          rw [show s + D - 1 = (s + D - 2) + 1 by omega, pow_succ]
          ring
      _ ≤ Z₁ * q ^ (s + D - 2) :=
          mul_le_mul_of_nonneg_right hZ₁l (by positivity)
  have ht1 : |A₁ - A₂| / Z₁ / q ^ (s + D - 2) ≤
      1 / C₀₁ * (|A₁ - A₂| / q ^ (s + D - 1)) := by
    calc |A₁ - A₂| / Z₁ / q ^ (s + D - 2)
        = |A₁ - A₂| / (Z₁ * q ^ (s + D - 2)) := by rw [div_div]
      _ ≤ |A₁ - A₂| / (C₀₁ * q ^ (s + D - 1)) := by
          gcongr
      _ = 1 / C₀₁ * (|A₁ - A₂| / q ^ (s + D - 1)) := by
          field_simp
  have ht2 : |A₂| * |Z₂ - Z₁| / (Z₁ * Z₂) / q ^ (s + D - 2) ≤
      C₂ / (C₀₁ * C₀₂) * (|Z₁ - Z₂| / q ^ (D - 1)) := by
    rw [abs_sub_comm Z₂ Z₁, div_div]
    have hnum : |A₂| * |Z₁ - Z₂| ≤
        C₂ * q ^ (s + 1) * |Z₁ - Z₂| :=
      mul_le_mul_of_nonneg_right hA₂u (abs_nonneg _)
    have hden : C₀₁ * C₀₂ * q ^ (s + D) ≤
        Z₁ * Z₂ * q ^ (s + D - 2) := by
      have hexp2 : s + D = 2 + (s + D - 2) := by omega
      have hq2 : C₀₁ * C₀₂ * q ^ (s + D) =
          C₀₁ * q * (C₀₂ * q) * q ^ (s + D - 2) := by
        nth_rewrite 1 [hexp2]
        rw [pow_add]
        ring
      rw [hq2]
      have hZZ : C₀₁ * q * (C₀₂ * q) ≤ Z₁ * Z₂ :=
        mul_le_mul hZ₁l hZ₂l (by positivity) hZ₁p.le
      exact mul_le_mul_of_nonneg_right hZZ (by positivity)
    calc |A₂| * |Z₁ - Z₂| / (Z₁ * Z₂ * q ^ (s + D - 2))
        ≤ C₂ * q ^ (s + 1) * |Z₁ - Z₂| /
          (C₀₁ * C₀₂ * q ^ (s + D)) := by
          apply div_le_div₀ (mul_nonneg (mul_nonneg hC₂0
            (by positivity)) (abs_nonneg _)) hnum (by positivity) hden
      _ = C₂ / (C₀₁ * C₀₂) * (|Z₁ - Z₂| / q ^ (D - 1)) := by
          have hexp3 : s + D = (s + 1) + (D - 1) := by omega
          nth_rewrite 1 [hexp3]
          rw [pow_add, div_mul_div_comm,
            div_eq_div_iff (by positivity) (by positivity)]
          ring
  calc |(A₁ / Z₁ - A₂ / Z₂) / q ^ (s + D - 2)|
      = |A₁ / Z₁ - A₂ / Z₂| / q ^ (s + D - 2) := by
        rw [abs_div, abs_of_pos hqp]
    _ ≤ (|A₁ - A₂| / Z₁ + |A₂| * |Z₂ - Z₁| / (Z₁ * Z₂)) /
        q ^ (s + D - 2) := by
        apply div_le_div_of_nonneg_right habs_decomp hqp.le
    _ = |A₁ - A₂| / Z₁ / q ^ (s + D - 2) +
        |A₂| * |Z₂ - Z₁| / (Z₁ * Z₂) / q ^ (s + D - 2) := by
        rw [add_div]
    _ ≤ 1 / C₀₁ * (|A₁ - A₂| / q ^ (s + D - 1)) +
        C₂ / (C₀₁ * C₀₂) * (|Z₁ - Z₂| / q ^ (D - 1)) :=
        add_le_add ht1 ht2
    _ = 1 / C₀₁ * |(A₁ - A₂) / q ^ (s + D - 1)| +
        C₂ / (C₀₁ * C₀₂) * |(Z₁ - Z₂) / q ^ (D - 1)| := by
        rw [abs_div, abs_of_pos
            (by positivity : (0:ℝ) < q ^ (s + D - 1)),
          abs_div, abs_of_pos
            (by positivity : (0:ℝ) < q ^ (D - 1))]

end Laplace.OneD
