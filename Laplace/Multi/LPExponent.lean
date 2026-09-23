/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib

/-!
# The exponent along a ray: several loss variables and several truth variables

Item E of the relative push-forward programme (germbij_slop S14) in full generality for positive
monomials. Loss variables `x ∈ (0,1)^ι` with density `∏ x_i^{h_i}`, monomials
`c_ν ∏_i x_i^{A_{νi}} ∏_j s_j^{B_{νj}}` indexed by `ν : κ`, truths `s_j = t^{-γ_j}`. Given a
primal–dual pair for the linear programme
`λ = min { ∑ (h_i+1) a_i : a ≥ 0, A a + B γ ≥ 1 } = max { ∑ y_ν (1 − B_ν·γ) : y ≥ 0, Aᵀ y ≤ h + 1 }`
(`LPData`), the free energy exponent along the ray is `λ` (`LPData.tendsto_lpExponent`). The lower
bound is the primal box `x_i ≤ t^{-a_i}` on which every term of `tF` is `O(1)`; the upper bound is
the dual certificate through `y log u ≤ u − y + y log y`, which gives
`e^{-tF} ≤ K t^{-(1-δ)λ} ∏ x_i^{-e_i}` with `e_i = (1-δ) ∑_ν y_ν A_{νi} < h_i + 1`, so no partition
of the cube is needed. Strong duality itself is not formalised: the theorem takes the optimal pair as
data, and weak duality (`LPData.duality`) certifies optimality.
-/

open Real MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-! ### One-dimensional cutoff powers -/

/-- `y^r` on `(0, ρ)`, `0` elsewhere. -/
noncomputable def cutPow (ρ r : ℝ) (y : ℝ) : ℝ := (Ioo (0 : ℝ) ρ).indicator (fun y ↦ y ^ r) y

theorem cutPow_of_mem {ρ r y : ℝ} (hy : y ∈ Ioo (0 : ℝ) ρ) : cutPow ρ r y = y ^ r :=
  indicator_of_mem hy _

theorem cutPow_of_notMem {ρ r y : ℝ} (hy : y ∉ Ioo (0 : ℝ) ρ) : cutPow ρ r y = 0 :=
  indicator_of_notMem hy _

theorem cutPow_nonneg (ρ r y : ℝ) : 0 ≤ cutPow ρ r y := by
  unfold cutPow
  by_cases hy : y ∈ Ioo (0 : ℝ) ρ
  · rw [indicator_of_mem hy]; exact Real.rpow_nonneg hy.1.le _
  · rw [indicator_of_notMem hy]

theorem measurable_cutPow (ρ r : ℝ) : Measurable (cutPow ρ r) :=
  (measurable_id.pow_const r).indicator measurableSet_Ioo

theorem integrable_cutPow {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : -1 < r) : Integrable (cutPow ρ r) := by
  unfold cutPow
  rw [integrable_indicator_iff measurableSet_Ioo]
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hρ).mp (intervalIntegral.intervalIntegrable_rpow' hr)

theorem integral_cutPow {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : -1 < r) :
    ∫ y, cutPow ρ r y = ρ ^ (r + 1) / (r + 1) := by
  unfold cutPow
  rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hρ, integral_rpow (Or.inl hr),
    Real.zero_rpow (by linarith), sub_zero]

theorem cutPow_le_cutPow {ρ ρ' r y : ℝ} (h : ρ ≤ ρ') : cutPow ρ r y ≤ cutPow ρ' r y := by
  by_cases hy : y ∈ Ioo (0 : ℝ) ρ
  · rw [cutPow_of_mem hy, cutPow_of_mem (Ioo_subset_Ioo le_rfl h hy)]
  · rw [cutPow_of_notMem hy]; exact cutPow_nonneg _ _ _

/-! ### The LP data -/

variable {ι κ m : Type*} [Fintype ι] [Fintype κ] [Fintype m]

/-- The truth exponent of monomial `ν` along the ray: `B_ν · γ`. -/
noncomputable def truthExp (B : κ → m → ℝ) (γ : m → ℝ) (ν : κ) : ℝ := ∑ j, B ν j * γ j

/-- The positive-monomial loss along the ray `s_j = t^{-γ_j}`. -/
noncomputable def lpLoss (c : κ → ℝ) (A : κ → ι → ℝ) (B : κ → m → ℝ) (γ : m → ℝ) (t : ℝ)
    (x : ι → ℝ) : ℝ :=
  ∑ ν, c ν * (∏ i, x i ^ (A ν i)) * t ^ (-truthExp B γ ν)

/-- The cube density `∏ x_i^{h_i}` on `(0,1)^ι`. -/
noncomputable def cubeDensity (h : ι → ℝ) (x : ι → ℝ) : ℝ := ∏ i, cutPow 1 (h i) (x i)

/-- The partition function. -/
noncomputable def lpZ (c : κ → ℝ) (A : κ → ι → ℝ) (B : κ → m → ℝ) (γ : m → ℝ) (h : ι → ℝ)
    (t : ℝ) : ℝ :=
  ∫ x, cubeDensity h x * Real.exp (-(t * lpLoss c A B γ t x))

/-- The primal value `∑ (h_i + 1) a_i`. -/
noncomputable def lpValue (h a : ι → ℝ) : ℝ := ∑ i, (h i + 1) * a i

/-- An optimal primal–dual pair for the exponent LP. -/
structure LPData (c : κ → ℝ) (A : κ → ι → ℝ) (B : κ → m → ℝ) (γ : m → ℝ) (h a : ι → ℝ)
    (y : κ → ℝ) : Prop where
  hc : ∀ ν, 0 < c ν
  hA : ∀ ν i, 0 ≤ A ν i
  hβ : ∀ ν, 0 ≤ truthExp B γ ν
  hh : ∀ i, 0 ≤ h i
  ha : ∀ i, 0 ≤ a i
  hy : ∀ ν, 0 ≤ y ν
  primal : ∀ ν, 1 ≤ ∑ i, A ν i * a i + truthExp B γ ν
  dual : ∀ i, ∑ ν, y ν * A ν i ≤ h i + 1
  duality : lpValue h a = ∑ ν, y ν * (1 - truthExp B γ ν)

namespace LPData

variable {c : κ → ℝ} {A : κ → ι → ℝ} {B : κ → m → ℝ} {γ : m → ℝ} {h a : ι → ℝ} {y : κ → ℝ}
  (hd : LPData c A B γ h a y)
include hd

omit hd in
theorem measurable_cubeDensity : Measurable (cubeDensity h) :=
  Finset.measurable_prod _ fun i _ ↦ (measurable_cutPow 1 (h i)).comp (measurable_pi_apply i)

omit hd in
theorem measurable_lpLoss (t : ℝ) : Measurable (lpLoss c A B γ t) :=
  Finset.measurable_sum _ fun _ _ ↦ ((Finset.measurable_prod _ fun i _ ↦
    (measurable_pi_apply i).pow_const _).const_mul _).mul_const _

omit hd in
theorem cubeDensity_nonneg (x : ι → ℝ) : 0 ≤ cubeDensity h x :=
  Finset.prod_nonneg fun _ _ ↦ cutPow_nonneg _ _ _

omit hd in
/-- The cube density vanishes off the open cube. -/
theorem cubeDensity_eq_zero {x : ι → ℝ} (hx : ¬ ∀ i, x i ∈ Ioo (0 : ℝ) 1) : cubeDensity h x = 0 := by
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) (cutPow_of_notMem hi)

omit hd in
theorem cubeDensity_of_mem {x : ι → ℝ} (hx : ∀ i, x i ∈ Ioo (0 : ℝ) 1) :
    cubeDensity h x = ∏ i, x i ^ (h i) :=
  Finset.prod_congr rfl fun i _ ↦ cutPow_of_mem (hx i)

theorem integrable_cubeDensity : Integrable (cubeDensity h) := by
  unfold cubeDensity
  rw [volume_pi]
  exact Integrable.fintype_prod (f := fun i y ↦ cutPow 1 (h i) y)
    fun i ↦ integrable_cutPow zero_le_one (by linarith [hd.hh i])

theorem lpLoss_nonneg {t : ℝ} (ht : 0 < t) {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ lpLoss c A B γ t x :=
  Finset.sum_nonneg fun ν _ ↦ mul_nonneg (mul_nonneg (hd.hc ν).le
    (Finset.prod_nonneg fun i _ ↦ Real.rpow_nonneg (hx i) _)) (Real.rpow_pos_of_pos ht _).le

/-- The integrand is dominated by the cube density. -/
theorem integrable_integrand {t : ℝ} (ht : 0 < t) :
    Integrable fun x ↦ cubeDensity h x * Real.exp (-(t * lpLoss c A B γ t x)) := by
  refine hd.integrable_cubeDensity.mono' ?_ (Filter.Eventually.of_forall fun x ↦ ?_)
  · exact ((measurable_cubeDensity (h := h)).mul
      ((measurable_lpLoss (c := c) (A := A) (B := B) (γ := γ) t).const_mul t |>.neg.exp)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (cubeDensity_nonneg x) (Real.exp_pos _).le)]
    by_cases hx : ∀ i, x i ∈ Ioo (0 : ℝ) 1
    · exact mul_le_of_le_one_right (cubeDensity_nonneg x) (Real.exp_le_one_iff.mpr (by
        have := hd.lpLoss_nonneg ht fun i ↦ (hx i).1.le
        nlinarith))
    · rw [cubeDensity_eq_zero hx, zero_mul]

/-! ### Lower bound: the primal box -/

/-- On the primal box `x_i ≤ t^{-a_i}`, each term of `tF` is at most its coefficient. -/
theorem mul_term_le {t : ℝ} (ht : 1 ≤ t) {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hxr : ∀ i, x i ≤ t ^ (-a i)) (ν : κ) :
    t * (c ν * (∏ i, x i ^ (A ν i)) * t ^ (-truthExp B γ ν)) ≤ c ν := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have h1 : ∏ i, x i ^ (A ν i) ≤ ∏ i, (t ^ (-a i)) ^ (A ν i) :=
    Finset.prod_le_prod (fun i _ ↦ Real.rpow_nonneg (hx i) _)
      fun i _ ↦ Real.rpow_le_rpow (hx i) (hxr i) (hd.hA ν i)
  have h2 : ∏ i, (t ^ (-a i)) ^ (A ν i) = t ^ (-(∑ i, A ν i * a i)) := by
    rw [← Finset.sum_neg_distrib, Real.rpow_sum_of_pos ht0]
    exact Finset.prod_congr rfl fun i _ ↦ by rw [← Real.rpow_mul ht0.le]; ring_nf
  have h3 : t * (t ^ (-(∑ i, A ν i * a i)) * t ^ (-truthExp B γ ν)) =
      t ^ (1 - ∑ i, A ν i * a i - truthExp B γ ν) := by
    rw [← Real.rpow_add ht0]
    have := Real.rpow_add ht0 1 (-(∑ i, A ν i * a i) + -truthExp B γ ν)
    rw [Real.rpow_one] at this
    rw [← this]
    ring_nf
  have h4 : t ^ (1 - ∑ i, A ν i * a i - truthExp B γ ν) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith [hd.primal ν])
  calc t * (c ν * (∏ i, x i ^ (A ν i)) * t ^ (-truthExp B γ ν))
      ≤ t * (c ν * (∏ i, (t ^ (-a i)) ^ (A ν i)) * t ^ (-truthExp B γ ν)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1 (hd.hc ν).le) (Real.rpow_pos_of_pos ht0 _).le) ht0.le
    _ = c ν * (t * (t ^ (-(∑ i, A ν i * a i)) * t ^ (-truthExp B γ ν))) := by rw [h2]; ring
    _ ≤ c ν * 1 := by rw [h3]; exact mul_le_mul_of_nonneg_left h4 (hd.hc ν).le
    _ = c ν := mul_one _

theorem mul_lpLoss_le {t : ℝ} (ht : 1 ≤ t) {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hxr : ∀ i, x i ≤ t ^ (-a i)) : t * lpLoss c A B γ t x ≤ ∑ ν, c ν := by
  unfold lpLoss
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun ν _ ↦ hd.mul_term_le ht hx hxr ν

/-- **Lower bound.** `Z ≥ e^{-C} t^{-λ} ∏ 1/(h_i+1)`. -/
theorem lpZ_ge {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-∑ ν, c ν) * t ^ (-lpValue h a) * ∏ i, 1 / (h i + 1) ≤ lpZ c A B γ h t := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  set r : ι → ℝ := fun i ↦ t ^ (-a i) with hr
  have hr0 : ∀ i, 0 < r i := fun i ↦ Real.rpow_pos_of_pos ht0 _
  have hr1 : ∀ i, r i ≤ 1 := fun i ↦
    Real.rpow_le_one_of_one_le_of_nonpos ht (neg_nonpos.mpr (hd.ha i))
  -- the minorant
  set G : (ι → ℝ) → ℝ := fun x ↦ Real.exp (-∑ ν, c ν) * ∏ i, cutPow (r i) (h i) (x i) with hG
  have hGint : Integrable G := by
    rw [hG]
    refine Integrable.const_mul ?_ _
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun i y ↦ cutPow (r i) (h i) y)
      fun i ↦ integrable_cutPow (hr0 i).le (by linarith [hd.hh i])
  have hGval : ∫ x, G x = Real.exp (-∑ ν, c ν) * t ^ (-lpValue h a) * ∏ i, 1 / (h i + 1) := by
    rw [hG, integral_const_mul, volume_pi,
      integral_fintype_prod_eq_prod (fun i y ↦ cutPow (r i) (h i) y)]
    have : ∀ i, ∫ y, cutPow (r i) (h i) y = t ^ (-(a i * (h i + 1))) * (1 / (h i + 1)) := by
      intro i
      rw [integral_cutPow (hr0 i).le (by linarith [hd.hh i]), hr]
      simp only
      rw [← Real.rpow_mul ht0.le, div_eq_mul_one_div]
      ring_nf
    simp only [this]
    have hsum : ∑ i, -(a i * (h i + 1)) = -lpValue h a := by
      unfold lpValue
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos ht0, hsum]
    ring
  rw [← hGval]
  refine integral_mono hGint (hd.integrable_integrand ht0) fun x ↦ ?_
  simp only [hG]
  by_cases hx : ∀ i, x i ∈ Ioo 0 (r i)
  · have hx1 : ∀ i, x i ∈ Ioo (0 : ℝ) 1 := fun i ↦ ⟨(hx i).1, lt_of_lt_of_le (hx i).2 (hr1 i)⟩
    have e1 : ∏ i, cutPow (r i) (h i) (x i) = cubeDensity h x := by
      rw [cubeDensity_of_mem hx1]
      exact Finset.prod_congr rfl fun i _ ↦ cutPow_of_mem (hx i)
    rw [e1, mul_comm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (cubeDensity_nonneg x)
    have := hd.mul_lpLoss_le ht (fun i ↦ (hx1 i).1.le) (fun i ↦ (hx i).2.le)
    linarith
  · push Not at hx
    obtain ⟨i, hi⟩ := hx
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (cutPow_of_notMem hi), mul_zero]
    exact mul_nonneg (cubeDensity_nonneg x) (Real.exp_pos _).le

/-! ### Upper bound: the dual certificate -/

omit hd in
/-- `y log u ≤ u − y + y log y` for `u > 0`, `y ≥ 0`. -/
theorem mul_log_le {u y : ℝ} (hu : 0 < u) (hy : 0 ≤ y) :
    y * Real.log u ≤ u - y + y * Real.log y := by
  rcases hy.lt_or_eq with hy | hy
  · have := Real.log_le_sub_one_of_pos (div_pos hu hy)
    rw [Real.log_div hu.ne' hy.ne'] at this
    have h2 := mul_le_mul_of_nonneg_left this hy.le
    have e : y * (u / y - 1) = u - y := by field_simp
    rw [e, mul_sub] at h2
    linarith
  · subst hy; simp; exact hu.le

/-- The dual weights rescaled by `1 − δ`, their total, and the induced fibre exponents. -/
noncomputable def dualExp (A : κ → ι → ℝ) (y : κ → ℝ) (δ : ℝ) (i : ι) : ℝ :=
  ∑ ν, (1 - δ) * y ν * A ν i

theorem dualExp_lt {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (i : ι) : dualExp A y δ i < h i + 1 := by
  unfold dualExp
  have := hd.dual i
  have hh := hd.hh i
  calc ∑ ν, (1 - δ) * y ν * A ν i = (1 - δ) * ∑ ν, y ν * A ν i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ν _ ↦ by ring
    _ ≤ (1 - δ) * (h i + 1) := mul_le_mul_of_nonneg_left this (by linarith)
    _ < h i + 1 := by nlinarith

theorem dualExp_nonneg (δ : ℝ) (hδ1 : δ ≤ 1) (i : ι) : 0 ≤ dualExp A y δ i :=
  Finset.sum_nonneg fun ν _ ↦ mul_nonneg (mul_nonneg (by linarith) (hd.hy ν)) (hd.hA ν i)

/-- The log-domain constant of the dual bound. -/
noncomputable def dualLogK (c y : κ → ℝ) (δ : ℝ) : ℝ :=
  ∑ ν, ((1 - δ) * y ν * Real.log ((1 - δ) * y ν) -
    (1 - δ) * y ν * Real.log (y ν / (∑ ν', y ν') * c ν)) - ∑ ν, (1 - δ) * y ν

/-- **The dual bound, in the log domain.** On the open cube, for `t ≥ 1`,
`(1−δ) λ log t + ∑ e_i log x_i ≤ tF + log K`. -/
theorem dual_log_bound {δ : ℝ} (hδ1 : δ ≤ 1) (hY : 0 < ∑ ν, y ν) {t : ℝ} (ht : 1 ≤ t)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Ioo (0 : ℝ) 1) :
    (1 - δ) * lpValue h a * Real.log t + ∑ i, dualExp A y δ i * Real.log (x i) ≤
      t * lpLoss c A B γ t x + dualLogK c y δ := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  set Y := ∑ ν, y ν with hYdef
  set p : κ → ℝ := fun ν ↦ y ν / Y with hp
  have hp0 : ∀ ν, 0 ≤ p ν := fun ν ↦ div_nonneg (hd.hy ν) hY.le
  have hpsum : ∑ ν, p ν = 1 := by
    rw [hp]; simp only; rw [← Finset.sum_div, div_self hY.ne']
  -- the monomials
  set Fν : κ → ℝ := fun ν ↦ c ν * (∏ i, x i ^ (A ν i)) * t ^ (-truthExp B γ ν) with hFν
  have hFpos : ∀ ν, 0 < Fν ν := fun ν ↦ mul_pos (mul_pos (hd.hc ν)
    (Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos (hx i).1 _)) (Real.rpow_pos_of_pos ht0 _)
  have hF : lpLoss c A B γ t x = ∑ ν, Fν ν := rfl
  have hFle : ∀ ν, Fν ν ≤ lpLoss c A B γ t x := fun ν ↦
    Finset.single_le_sum (f := Fν) (fun ν _ ↦ (hFpos ν).le) (Finset.mem_univ ν)
  -- log of a monomial
  have hlogF : ∀ ν, Real.log (Fν ν) = Real.log (c ν) + ∑ i, A ν i * Real.log (x i) -
      truthExp B γ ν * Real.log t := by
    intro ν
    simp only [hFν]
    rw [Real.log_mul (mul_pos (hd.hc ν) (Finset.prod_pos fun i _ ↦
      Real.rpow_pos_of_pos (hx i).1 _)).ne' (Real.rpow_pos_of_pos ht0 _).ne',
      Real.log_mul (hd.hc ν).ne' (Finset.prod_pos fun i _ ↦
      Real.rpow_pos_of_pos (hx i).1 _).ne', Real.log_prod (fun i _ ↦
      (Real.rpow_pos_of_pos (hx i).1 _).ne'), Real.log_rpow ht0]
    simp only [Real.log_rpow (hx _).1]
    ring
  -- the key inequality per monomial with `u = p_ν t F_ν`, `y' = (1−δ) y_ν`
  have hkey : ∀ ν, (1 - δ) * y ν * Real.log (p ν * (t * Fν ν)) ≤
      p ν * (t * Fν ν) - (1 - δ) * y ν + (1 - δ) * y ν * Real.log ((1 - δ) * y ν) := by
    intro ν
    by_cases hyν : y ν = 0
    · simp only [hp, hyν, zero_div, zero_mul, mul_zero, sub_zero, add_zero, le_refl]
    · have hpν : 0 < p ν := div_pos (lt_of_le_of_ne (hd.hy ν) (Ne.symm hyν)) hY
      exact mul_log_le (mul_pos hpν (mul_pos ht0 (hFpos ν))) (mul_nonneg (by linarith) (hd.hy ν))
  -- expand the logs where `y_ν ≠ 0`
  have hexp : ∀ ν, (1 - δ) * y ν * Real.log (p ν * (t * Fν ν)) =
      (1 - δ) * y ν * (Real.log (p ν * c ν) + (1 - truthExp B γ ν) * Real.log t +
        ∑ i, A ν i * Real.log (x i)) := by
    intro ν
    by_cases hyν : y ν = 0
    · simp only [hyν, mul_zero, zero_mul]
    · have hpν : 0 < p ν := div_pos (lt_of_le_of_ne (hd.hy ν) (Ne.symm hyν)) hY
      congr 1
      rw [Real.log_mul hpν.ne' (mul_pos ht0 (hFpos ν)).ne', Real.log_mul ht0.ne' (hFpos ν).ne',
        hlogF ν, Real.log_mul hpν.ne' (hd.hc ν).ne']
      ring
  have hsum := Finset.sum_le_sum fun ν (_ : ν ∈ Finset.univ) ↦ hkey ν
  simp only [hexp] at hsum
  -- `∑ p_ν t F_ν ≤ t F`
  have hconv : ∑ ν, p ν * (t * Fν ν) ≤ t * lpLoss c A B γ t x := by
    calc ∑ ν, p ν * (t * Fν ν) ≤ ∑ ν, p ν * (t * lpLoss c A B γ t x) :=
          Finset.sum_le_sum fun ν _ ↦ mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hFle ν) ht0.le) (hp0 ν)
      _ = t * lpLoss c A B γ t x := by rw [← Finset.sum_mul, hpsum, one_mul]
  -- the left-hand side of `hsum` rearranged
  have hlhs : ∑ ν, (1 - δ) * y ν * (Real.log (p ν * c ν) + (1 - truthExp B γ ν) * Real.log t +
      ∑ i, A ν i * Real.log (x i)) =
      ∑ ν, (1 - δ) * y ν * Real.log (p ν * c ν) + (1 - δ) * lpValue h a * Real.log t +
        ∑ i, dualExp A y δ i * Real.log (x i) := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · congr 1
      rw [hd.duality, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun ν _ ↦ by ring
    · unfold dualExp
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun ν _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hlhs] at hsum
  have hrhs : ∑ ν, (p ν * (t * Fν ν) - (1 - δ) * y ν + (1 - δ) * y ν * Real.log ((1 - δ) * y ν)) =
      ∑ ν, p ν * (t * Fν ν) - ∑ ν, (1 - δ) * y ν +
        ∑ ν, (1 - δ) * y ν * Real.log ((1 - δ) * y ν) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [hrhs] at hsum
  unfold dualLogK
  rw [Finset.sum_sub_distrib]
  simp only [hp] at hsum ⊢
  linarith

/-- **The dual bound, exponentiated.** On the open cube `e^{-tF} ≤ K t^{-(1−δ)λ} ∏ x_i^{-e_i}`. -/
theorem exp_neg_le {δ : ℝ} (hδ1 : δ ≤ 1) (hY : 0 < ∑ ν, y ν) {t : ℝ} (ht : 1 ≤ t)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Ioo (0 : ℝ) 1) :
    Real.exp (-(t * lpLoss c A B γ t x)) ≤
      Real.exp (dualLogK c y δ) * t ^ (-((1 - δ) * lpValue h a)) *
        ∏ i, x i ^ (-dualExp A y δ i) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hb := hd.dual_log_bound hδ1 hY ht hx
  rw [Real.rpow_def_of_pos ht0, ← Real.exp_add]
  have e : ∏ i, x i ^ (-dualExp A y δ i) = Real.exp (∑ i, -(dualExp A y δ i * Real.log (x i))) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ ↦ by
      rw [Real.rpow_def_of_pos (hx i).1]; ring_nf
  rw [e, ← Real.exp_add, Real.exp_le_exp, Finset.sum_neg_distrib]
  linarith

/-- **Upper bound.** For `0 < δ < 1` and `t ≥ 1`, `Z ≤ K t^{-(1−δ)λ} ∏ 1/(h_i − e_i + 1)`. -/
theorem lpZ_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hY : 0 < ∑ ν, y ν) {t : ℝ} (ht : 1 ≤ t) :
    lpZ c A B γ h t ≤ Real.exp (dualLogK c y δ) * t ^ (-((1 - δ) * lpValue h a)) *
      ∏ i, 1 / (h i - dualExp A y δ i + 1) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have he : ∀ i, -1 < h i - dualExp A y δ i := fun i ↦ by linarith [hd.dualExp_lt hδ hδ1 i]
  set K := Real.exp (dualLogK c y δ) * t ^ (-((1 - δ) * lpValue h a)) with hK
  have hK0 : 0 ≤ K := by positivity
  set G : (ι → ℝ) → ℝ := fun x ↦ K * ∏ i, cutPow 1 (h i - dualExp A y δ i) (x i) with hG
  have hGint : Integrable G := by
    rw [hG]
    refine Integrable.const_mul ?_ _
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun i z ↦ cutPow 1 (h i - dualExp A y δ i) z)
      fun i ↦ integrable_cutPow zero_le_one (he i)
  have hGval : ∫ x, G x = K * ∏ i, 1 / (h i - dualExp A y δ i + 1) := by
    rw [hG, integral_const_mul, volume_pi,
      integral_fintype_prod_eq_prod (fun i z ↦ cutPow 1 (h i - dualExp A y δ i) z)]
    congr 1
    exact Finset.prod_congr rfl fun i _ ↦ by
      rw [integral_cutPow zero_le_one (he i), Real.one_rpow]
  rw [← hGval]
  refine integral_mono (hd.integrable_integrand ht0) hGint fun x ↦ ?_
  simp only [hG]
  by_cases hx : ∀ i, x i ∈ Ioo (0 : ℝ) 1
  · rw [cubeDensity_of_mem hx]
    have hb := hd.exp_neg_le hδ1.le hY ht hx
    calc (∏ i, x i ^ (h i)) * Real.exp (-(t * lpLoss c A B γ t x))
        ≤ (∏ i, x i ^ (h i)) * (K * ∏ i, x i ^ (-dualExp A y δ i)) :=
          mul_le_mul_of_nonneg_left hb (Finset.prod_nonneg fun i _ ↦ Real.rpow_nonneg (hx i).1.le _)
      _ = K * ∏ i, cutPow 1 (h i - dualExp A y δ i) (x i) := by
          rw [mul_left_comm, ← Finset.prod_mul_distrib]
          congr 1
          exact Finset.prod_congr rfl fun i _ ↦ by
            rw [cutPow_of_mem (hx i), ← Real.rpow_add (hx i).1]; ring_nf
  · rw [cubeDensity_eq_zero hx, zero_mul]
    exact mul_nonneg hK0 (Finset.prod_nonneg fun i _ ↦ cutPow_nonneg _ _ _)

/-- The trivial upper bound `Z ≤ ∏ 1/(h_i+1)`. -/
theorem lpZ_le_const {t : ℝ} (ht : 0 < t) : lpZ c A B γ h t ≤ ∏ i, 1 / (h i + 1) := by
  have hval : ∫ x, cubeDensity h x = ∏ i, 1 / (h i + 1) := by
    unfold cubeDensity
    rw [volume_pi, integral_fintype_prod_eq_prod (fun i y ↦ cutPow 1 (h i) y)]
    exact Finset.prod_congr rfl fun i _ ↦ by
      rw [integral_cutPow zero_le_one (by linarith [hd.hh i]), Real.one_rpow]
  rw [← hval]
  refine integral_mono (hd.integrable_integrand ht) hd.integrable_cubeDensity fun x ↦ ?_
  by_cases hx : ∀ i, x i ∈ Ioo (0 : ℝ) 1
  · exact mul_le_of_le_one_right (cubeDensity_nonneg x) (Real.exp_le_one_iff.mpr (by
      have := hd.lpLoss_nonneg ht fun i ↦ (hx i).1.le
      nlinarith))
  · rw [cubeDensity_eq_zero hx, zero_mul]

theorem lpZ_pos {t : ℝ} (ht : 1 ≤ t) : 0 < lpZ c A B γ h t :=
  lt_of_lt_of_le (by
    have := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos ht) (-lpValue h a)
    have : 0 < ∏ i, 1 / (h i + 1) := Finset.prod_pos fun i _ ↦ by have := hd.hh i; positivity
    positivity) (hd.lpZ_ge ht)

theorem lpValue_nonneg : 0 ≤ lpValue h a :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg (by linarith [hd.hh i]) (hd.ha i)

/-- **The exponent along a ray, several variables.** `-log Z / log t → λ`. -/
theorem tendsto_lpExponent :
    Tendsto (fun t ↦ -Real.log (lpZ c A B γ h t) / Real.log t) atTop (𝓝 (lpValue h a)) := by
  set L := lpValue h a with hL
  have hL0 : 0 ≤ L := hd.lpValue_nonneg
  have hP : 0 < ∏ i, 1 / (h i + 1) := Finset.prod_pos fun i _ ↦ by have := hd.hh i; positivity
  set C := ∑ ν, c ν with hC
  -- upper envelope from the lower bound on `Z`
  have hup : ∀ᶠ t in atTop, -Real.log (lpZ c A B γ h t) / Real.log t ≤
      L + (C - Real.log (∏ i, 1 / (h i + 1))) / Real.log t := by
    filter_upwards [eventually_gt_atTop 1] with t ht
    have ht0 : 0 < t := one_pos.trans ht
    have hlt : 0 < Real.log t := Real.log_pos ht
    have hZ := hd.lpZ_ge ht.le
    have hpos : 0 < Real.exp (-C) * t ^ (-L) * ∏ i, 1 / (h i + 1) := by
      have := Real.rpow_pos_of_pos ht0 (-L); positivity
    have hlog := Real.log_le_log hpos hZ
    rw [Real.log_mul (by have := Real.rpow_pos_of_pos ht0 (-L); positivity) hP.ne',
      Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos ht0 _).ne', Real.log_exp,
      Real.log_rpow ht0] at hlog
    rw [div_le_iff₀ hlt]
    have e : (L + (C - Real.log (∏ i, 1 / (h i + 1))) / Real.log t) * Real.log t =
        L * Real.log t + (C - Real.log (∏ i, 1 / (h i + 1))) := by field_simp
    rw [e]
    nlinarith [hlog]
  -- lower envelope
  have hlow : ∀ ε > 0, ∀ᶠ t in atTop, L - ε ≤ -Real.log (lpZ c A B γ h t) / Real.log t := by
    intro ε hε
    by_cases hY : ∑ ν, y ν = 0
    · -- all dual weights vanish: `L = 0`
      have hL0' : L = 0 := by
        rw [hL, hd.duality]
        exact Finset.sum_eq_zero fun ν _ ↦ by
          rw [(Finset.sum_eq_zero_iff_of_nonneg fun ν _ ↦ hd.hy ν).mp hY ν (Finset.mem_univ ν),
            zero_mul]
      have hP1 : ∏ i, 1 / (h i + 1) ≤ 1 :=
        Finset.prod_le_one (fun i _ ↦ by have := hd.hh i; positivity)
          fun i _ ↦ div_le_one_of_le₀ (by linarith [hd.hh i]) (by linarith [hd.hh i])
      have hlogP : Real.log (∏ i, 1 / (h i + 1)) ≤ 0 := Real.log_nonpos hP.le hP1
      filter_upwards [eventually_gt_atTop 1] with t ht
      have hlt : 0 < Real.log t := Real.log_pos ht
      have hZpos := hd.lpZ_pos ht.le
      have hZ1 := hd.lpZ_le_const (one_pos.trans ht)
      have hlog := Real.log_le_log hZpos hZ1
      rw [hL0', zero_sub, le_div_iff₀ hlt]
      nlinarith
    · have hYpos : 0 < ∑ ν, y ν := lt_of_le_of_ne (Finset.sum_nonneg fun ν _ ↦ hd.hy ν) (Ne.symm hY)
      -- choose `δ` with `δ L ≤ ε/2`
      set δ : ℝ := min (1 / 2) (ε / (2 * (L + 1))) with hδdef
      have hδ0 : 0 < δ := lt_min one_half_pos (by positivity)
      have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) one_half_lt_one
      have hδL : δ * L ≤ ε / 2 := by
        have h1 : δ ≤ ε / (2 * (L + 1)) := min_le_right _ _
        calc δ * L ≤ ε / (2 * (L + 1)) * L := mul_le_mul_of_nonneg_right h1 hL0
          _ ≤ ε / (2 * (L + 1)) * (L + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = ε / 2 := by field_simp
      set K := Real.exp (dualLogK c y δ) * ∏ i, 1 / (h i - dualExp A y δ i + 1) with hK
      have hK0 : 0 < K := by
        have : 0 < ∏ i, 1 / (h i - dualExp A y δ i + 1) := Finset.prod_pos fun i _ ↦ by
          have := hd.dualExp_lt hδ0 hδ1 i; have := hd.hh i
          exact div_pos one_pos (by linarith)
        positivity
      have hdiv : Tendsto (fun t : ℝ ↦ Real.log K / Real.log t) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
      filter_upwards [eventually_gt_atTop 1, hdiv.eventually (eventually_le_nhds (half_pos hε))]
        with t ht hl
      have ht0 : 0 < t := one_pos.trans ht
      have hlt : 0 < Real.log t := Real.log_pos ht
      have hZle := hd.lpZ_le hδ0 hδ1 hYpos ht.le
      have hZle' : lpZ c A B γ h t ≤ K * t ^ (-((1 - δ) * L)) := by
        rw [hK]; linarith [show Real.exp (dualLogK c y δ) * t ^ (-((1 - δ) * lpValue h a)) *
          ∏ i, 1 / (h i - dualExp A y δ i + 1) = Real.exp (dualLogK c y δ) *
          (∏ i, 1 / (h i - dualExp A y δ i + 1)) * t ^ (-((1 - δ) * L)) by ring]
      have hZpos := hd.lpZ_pos ht.le
      have hlog := Real.log_le_log hZpos hZle'
      rw [Real.log_mul hK0.ne' (Real.rpow_pos_of_pos ht0 _).ne', Real.log_rpow ht0] at hlog
      rw [le_div_iff₀ hlt]
      rw [div_le_iff₀ hlt] at hl
      nlinarith
  refine tendsto_order.2 ⟨fun a' ha' ↦ ?_, fun a' ha' ↦ ?_⟩
  · have hε : 0 < (L - a') / 2 := by linarith
    filter_upwards [hlow _ hε] with t ht
    linarith
  · have h0 : Tendsto (fun t : ℝ ↦ (C - Real.log (∏ i, 1 / (h i + 1))) / Real.log t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    filter_upwards [hup, h0.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < a' - L))]
      with t ht hlt
    linarith

end LPData

end Laplace.Multi
