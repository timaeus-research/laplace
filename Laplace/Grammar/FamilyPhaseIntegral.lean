/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CoeffFamily

/-!
# The standard integral for coefficient-family data (Stage 4d)

Unit 244 (Taylor-tree programme, Stage 4; Astra #28 §2.4 (I)). For absolutely summable coefficient
families `cξ, cη` the standard integral
```
Z(N) = ∫_{(0,1]^d} evalF cη u · u^h · exp(-βN u^{2k} + β√N u^k evalF cξ u) du
```
(`familyPhaseIntegral`) is the limit, at every fixed `N ≥ 0`, of the polynomial standard integrals of
the box truncations (`tendsto_polyPhaseIntegral_truncList`): the truncations converge uniformly on
the cube (unit 243) and the integrands are dominated by the constant
`mass cη · e^{β√N mass cξ}` on the finite-measure box. No `sorry` and no additional `axiom`
declarations.
-/

open MeasureTheory Set Real Filter Topology

namespace Laplace.Grammar

open MonoRep CoeffFamily

/-- The standard integral for coefficient-family data. -/
noncomputable def familyPhaseIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (cξ cη : CoeffFamily (n + 1)) : ℝ :=
  ∫ u in unitBox (n + 1), evalF cη u * (∏ i, u i ^ h i) *
    Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * evalF cξ u)

/-- Pointwise convergence of the truncations on the closed cube. -/
theorem tendsto_eval_truncList {d : ℕ} {c : CoeffFamily d} (hc : AbsSummable c) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) :
    Tendsto (fun m => eval (truncList c m) u) atTop (𝓝 (evalF c u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) (tailMass_tendsto_zero hc)
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact abs_evalF_sub_truncList_le hc m hu

/-- **The polynomial standard integrals of the truncations converge to the family integral**
(fixed `N ≥ 0`, `β ≥ 0`). -/
theorem tendsto_polyPhaseIntegral_truncList (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 ≤ β)
    {N : ℝ} (hN : 0 ≤ N) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) :
    Tendsto (fun m => polyPhaseIntegral n h k β N (truncList cξ m) (truncList cη m)) atTop
      (𝓝 (familyPhaseIntegral n h k β N cξ cη)) := by
  unfold polyPhaseIntegral familyPhaseIntegral
  set C : ℝ := mass cη * Real.exp (β * Real.sqrt N * mass cξ) with hC
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun m => Continuous.aestronglyMeasurable ?_
    exact ((continuous_eval _).mul
      (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _)).mul
      (Real.continuous_exp.comp ((continuous_const.mul
        (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _)).neg.add
        ((continuous_const.mul (continuous_const.mul
          (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _))).mul
          (continuous_eval _))))
  · refine Eventually.of_forall fun m => ae_restrict_of_forall_mem (measurableSet_unitBox _)
      fun u hu => ?_
    have hu' : u ∈ closedCube (n + 1) := unitBox_subset_closedCube _ hu
    have hτ := prod_pow_mem_Icc (fun i => 2 * k i) hu
    have hh := prod_pow_mem_Icc h hu
    have hK := prod_pow_mem_Icc k hu
    have h1 : |eval (truncList cη m) u| ≤ mass cη :=
      (abs_eval_le_l1 _ hu').trans (l1_truncList_le_mass hη m)
    have h2 : |eval (truncList cξ m) u| ≤ mass cξ :=
      (abs_eval_le_l1 _ hu').trans (l1_truncList_le_mass hξ m)
    have hexp : Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) +
        β * (Real.sqrt N * ∏ i, u i ^ k i) * eval (truncList cξ m) u) ≤
        Real.exp (β * Real.sqrt N * mass cξ) := by
      refine Real.exp_le_exp.2 ?_
      have hs : 0 ≤ β * (Real.sqrt N * ∏ i, u i ^ k i) := by
        have := Real.sqrt_nonneg N; have := hK.1; positivity
      have hprod : β * (Real.sqrt N * ∏ i, u i ^ k i) ≤ β * Real.sqrt N :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (Real.sqrt_nonneg N) hK.2) hβ
      have ha : β * (Real.sqrt N * ∏ i, u i ^ k i) * eval (truncList cξ m) u ≤
          β * Real.sqrt N * mass cξ := by
        calc β * (Real.sqrt N * ∏ i, u i ^ k i) * eval (truncList cξ m) u
            ≤ β * (Real.sqrt N * ∏ i, u i ^ k i) * mass cξ :=
              mul_le_mul_of_nonneg_left ((le_abs_self _).trans h2) hs
          _ ≤ β * Real.sqrt N * mass cξ := mul_le_mul_of_nonneg_right hprod (mass_nonneg cξ)
      have : 0 ≤ β * N * ∏ i, u i ^ (2 * k i) := by have := hτ.1; positivity
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hh.1, abs_of_nonneg (Real.exp_nonneg _),
      hC]
    calc |eval (truncList cη m) u| * (∏ i, u i ^ h i) * Real.exp _
        ≤ mass cη * 1 * Real.exp (β * Real.sqrt N * mass cξ) :=
          mul_le_mul (mul_le_mul h1 hh.2 hh.1 (mass_nonneg cη)) hexp (Real.exp_nonneg _)
            (by have := mass_nonneg cη; positivity)
      _ = _ := by ring
  · exact integrableOn_const (volume_unitBox_lt_top (n + 1)).ne
  · refine ae_restrict_of_forall_mem (measurableSet_unitBox _) fun u hu => ?_
    have hu' : u ∈ closedCube (n + 1) := unitBox_subset_closedCube _ hu
    exact ((tendsto_eval_truncList hη hu').mul tendsto_const_nhds).mul
      (Real.continuous_exp.continuousAt.tendsto.comp (tendsto_const_nhds.add
        (tendsto_const_nhds.mul (tendsto_eval_truncList hξ hu'))))

end Laplace.Grammar
