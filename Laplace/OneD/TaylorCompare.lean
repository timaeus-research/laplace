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

end Laplace.OneD
