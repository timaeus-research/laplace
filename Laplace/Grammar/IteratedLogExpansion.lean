/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LogSquaredSecondOrder

/-!
# Complete polynomial-in-`log` expansions of the iterated primitives (grammar §4.2)

Units 41–42 identified the constants below `log n` (`d = 2`) and `(log n)²` (`d = 3`). Here the
transfer step "polynomial in `log x` plus `O(1/x)` ↦ the same shape one degree higher" is proved
once for the iterated logarithmic primitives `H_m = iterLogPrim m`:

  `H_m(L) = ∑_{i ≤ m} c_{m,i} log^i L + θ_m(L)`,  `|θ_m(L)| ≤ M/L`  (`L ≥ 1`),

with explicit recursively defined coefficients `c_{m,i}` (`iterLogCoeff`): `c_{0,0} = A`,
`c_{m+1,i+1} = c_{m,i}/(i+1)`, and the new constant `c_{m+1,0} = ∫₀¹ H_m/x + ∫₁^∞ θ_m/x`. The top
coefficient is `c_{m,m} = A/m!`. Consequently every all-equal chart integral of unit 39 has a
complete expansion `Z_d(n) = n^{-1/2} P_d(log n) + O(n^{-1})`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- The expansion coefficients of the iterated logarithmic primitives. -/
noncomputable def iterLogCoeff (β a : ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => quadMass β a
  | 0, _ + 1 => 0
  | m + 1, 0 => (∫ x in Ioc (0 : ℝ) 1, iterLogPrim β a m x / x)
      + ∫ x in Ioi (1 : ℝ), (iterLogPrim β a m x
          - ∑ i ∈ Finset.range (m + 1), iterLogCoeff β a m i * Real.log x ^ i) / x
  | m + 1, i + 1 => iterLogCoeff β a m i / ((i : ℝ) + 1)

/-- The remainder `θ_m(x) = H_m(x) − ∑_{i ≤ m} c_{m,i} log^i x`. -/
noncomputable def iterLogRem (β a : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  iterLogPrim β a m x - ∑ i ∈ Finset.range (m + 1), iterLogCoeff β a m i * Real.log x ^ i

theorem iterLogCoeff_zero_zero (β a : ℝ) : iterLogCoeff β a 0 0 = quadMass β a := rfl

theorem iterLogCoeff_succ_zero (β a : ℝ) (m : ℕ) :
    iterLogCoeff β a (m + 1) 0 = (∫ x in Ioc (0 : ℝ) 1, iterLogPrim β a m x / x)
      + ∫ x in Ioi (1 : ℝ), iterLogRem β a m x / x := rfl

theorem iterLogCoeff_succ_succ (β a : ℝ) (m i : ℕ) :
    iterLogCoeff β a (m + 1) (i + 1) = iterLogCoeff β a m i / ((i : ℝ) + 1) := rfl

/-- `c_{m,m} = A / m!`. -/
theorem iterLogCoeff_top (β a : ℝ) (m : ℕ) :
    iterLogCoeff β a m m = quadMass β a / (m.factorial : ℝ) := by
  induction m with
  | zero => simp [iterLogCoeff_zero_zero]
  | succ m ih =>
    rw [iterLogCoeff_succ_succ, ih, Nat.factorial_succ]
    push_cast
    have h1 : (m.factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((m : ℝ) + 1) ≠ 0 := by positivity
    field_simp

theorem iterLogRem_zero (β a x : ℝ) : iterLogRem β a 0 x = quadPrimitive β a x - quadMass β a := by
  simp [iterLogRem, iterLogCoeff_zero_zero, iterLogPrim_zero]

theorem iterLogRem_div_continuousOn (β a : ℝ) (hβ : 0 < β) (m : ℕ) :
    ContinuousOn (fun x => iterLogRem β a m x / x) (Ioi 1) := by
  have hne : ∀ x ∈ Ioi (1 : ℝ), x ≠ 0 := fun x hx => (zero_lt_one.trans hx).ne'
  refine ContinuousOn.div ?_ continuousOn_id hne
  refine (iterLogPrim_continuous β a hβ m).continuousOn.sub ?_
  refine continuousOn_finsetSum _ fun i _ => ?_
  exact continuousOn_const.mul ((Real.continuousOn_log.mono hne).pow i)

theorem iterLogRem_div_bounds (β a : ℝ) (m : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (hb : |iterLogRem β a m x| ≤ quadMoment β a / x) :
    |iterLogRem β a m x / x| ≤ quadMoment β a * x ^ (-2 : ℝ) := by
  have hx0 : (0 : ℝ) < x := one_pos.trans_le hx
  rw [abs_div, abs_of_pos hx0, Real.rpow_neg hx0.le, Real.rpow_two, div_le_iff₀ hx0]
  calc |iterLogRem β a m x| ≤ quadMoment β a / x := hb
    _ = quadMoment β a * (x ^ 2)⁻¹ * x := by field_simp

theorem iterLogRem_div_integrableOn (β a : ℝ) (hβ : 0 < β) (m : ℕ) (c : ℝ) (hc : 1 ≤ c)
    (hb : ∀ L, 1 ≤ L → |iterLogRem β a m L| ≤ quadMoment β a / L) :
    IntegrableOn (fun x => iterLogRem β a m x / x) (Ioi c) := by
  have hc0 : (0 : ℝ) < c := one_pos.trans_le hc
  refine Integrable.mono' (g := fun x => quadMoment β a * x ^ (-2 : ℝ))
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hc0).const_mul _)
    (((iterLogRem_div_continuousOn β a hβ m).mono (Ioi_subset_Ioi hc)).aestronglyMeasurable
      measurableSet_Ioi) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun x hx => ?_
  have hx1 : (1 : ℝ) ≤ x := hc.trans (le_of_lt hx)
  rw [Real.norm_eq_abs]
  exact iterLogRem_div_bounds β a m x hx1 (hb x hx1)

theorem iterLogRem_tail_abs_le (β a : ℝ) (m : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hb : ∀ L, 1 ≤ L → |iterLogRem β a m L| ≤ quadMoment β a / L) :
    |∫ x in Ioi L, iterLogRem β a m x / x| ≤ quadMoment β a / L := by
  have hL0 : (0 : ℝ) < L := one_pos.trans_le hL
  have hint : (∫ x in Ioi L, quadMoment β a * x ^ (-2 : ℝ)) = quadMoment β a / L := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hL0]
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg hL0.le, Real.rpow_one]
    field_simp
  rw [← hint, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt (by norm_num) hL0).const_mul _)
    ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun x hx => ?_
  have hx1 : (1 : ℝ) ≤ x := hL.trans (le_of_lt hx)
  rw [Real.norm_eq_abs]
  exact iterLogRem_div_bounds β a m x hx1 (hb x hx1)

theorem integrableOn_log_pow_div_Ioc (i : ℕ) (L : ℝ) :
    IntegrableOn (fun x : ℝ => Real.log x ^ i / x) (Ioc 1 L) := by
  have : ContinuousOn (fun x : ℝ => Real.log x ^ i / x) (Icc 1 L) :=
    ((Real.continuousOn_log.mono fun x hx => (lt_of_lt_of_le one_pos hx.1).ne').pow i).div
      continuousOn_id fun x hx => (lt_of_lt_of_le one_pos hx.1).ne'
  exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- **The transfer step**: for `L ≥ 1`, `θ_{m+1}(L) = −∫_L^∞ θ_m(x)/x dx`. -/
theorem iterLogRem_succ_eq (β a : ℝ) (hβ : 0 < β) (m : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hb : ∀ L, 1 ≤ L → |iterLogRem β a m L| ≤ quadMoment β a / L) :
    iterLogRem β a (m + 1) L = -∫ x in Ioi L, iterLogRem β a m x / x := by
  have hL0 : (0 : ℝ) < L := one_pos.trans_le hL
  have hint : IntegrableOn (fun x => iterLogPrim β a m x / x) (Ioc 0 L) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL0.le).1
      (iterLogPrim_div_intervalIntegrable β a hβ m 0 L)
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioc 1 L) :=
    Set.disjoint_left.2 fun x h1 h2 => (not_lt.2 h1.2) h2.1
  have hsplit := setIntegral_union hdisj measurableSet_Ioc (hint.mono_set (Ioc_subset_Ioc_right hL))
    (hint.mono_set (Ioc_subset_Ioc_left zero_le_one))
    (f := fun x => iterLogPrim β a m x / x)
  rw [Ioc_union_Ioc_eq_Ioc zero_le_one hL] at hsplit
  have hθint := iterLogRem_div_integrableOn β a hβ m 1 le_rfl hb
  have hθsplit := setIntegral_union (Ioc_disjoint_Ioi (le_refl L)) measurableSet_Ioi
    (hθint.mono_set Ioc_subset_Ioi_self) (hθint.mono_set (Ioi_subset_Ioi hL))
    (f := fun x => iterLogRem β a m x / x)
  rw [Ioc_union_Ioi_eq_Ioi hL] at hθsplit
  have hpt : ∀ x ∈ Ioc (1 : ℝ) L, iterLogPrim β a m x / x
      = (∑ i ∈ Finset.range (m + 1), iterLogCoeff β a m i * (Real.log x ^ i / x))
        + iterLogRem β a m x / x := by
    intro x _
    rw [iterLogRem, sub_div, Finset.sum_div]
    simp_rw [mul_div_assoc]
    ring
  have hpoly : IntegrableOn
      (fun x : ℝ => ∑ i ∈ Finset.range (m + 1), iterLogCoeff β a m i * (Real.log x ^ i / x))
      (Ioc 1 L) := by
    refine integrable_finsetSum _ fun i _ => ?_
    exact (integrableOn_log_pow_div_Ioc i L).const_mul _
  have hθ' : IntegrableOn (fun x => iterLogRem β a m x / x) (Ioc 1 L) :=
    hθint.mono_set Ioc_subset_Ioi_self
  have hpolyval : (∫ x in Ioc (1 : ℝ) L,
      ∑ i ∈ Finset.range (m + 1), iterLogCoeff β a m i * (Real.log x ^ i / x))
      = ∑ i ∈ Finset.range (m + 1),
          iterLogCoeff β a m i * (Real.log L ^ (i + 1) / ((i : ℝ) + 1)) := by
    rw [integral_finsetSum _ fun i _ => (integrableOn_log_pow_div_Ioc i L).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le hL,
      integral_log_pow_div i L hL]
  have hmid : (∫ x in Ioc (1 : ℝ) L, iterLogPrim β a m x / x)
      = (∑ i ∈ Finset.range (m + 1),
          iterLogCoeff β a m i * (Real.log L ^ (i + 1) / ((i : ℝ) + 1)))
        + ∫ x in Ioc (1 : ℝ) L, iterLogRem β a m x / x := by
    rw [setIntegral_congr_fun measurableSet_Ioc hpt, MeasureTheory.integral_add hpoly hθ', hpolyval]
  have hsum : ∑ i ∈ Finset.range (m + 1 + 1), iterLogCoeff β a (m + 1) i * Real.log L ^ i
      = iterLogCoeff β a (m + 1) 0
        + ∑ i ∈ Finset.range (m + 1),
            iterLogCoeff β a m i * (Real.log L ^ (i + 1) / ((i : ℝ) + 1)) := by
    rw [Finset.sum_range_succ', pow_zero, mul_one, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iterLogCoeff_succ_succ]; ring
  rw [iterLogRem, iterLogPrim_succ, intervalIntegral.integral_of_le hL0.le, hsplit, hmid, hsum,
    iterLogCoeff_succ_zero, hθsplit]
  ring

/-- **Uniform remainder bound**: `|θ_m(L)| ≤ M/L` for all `m` and `L ≥ 1`. -/
theorem iterLogRem_abs_le (β a : ℝ) (hβ : 0 < β) (m : ℕ) :
    ∀ L, 1 ≤ L → |iterLogRem β a m L| ≤ quadMoment β a / L := by
  induction m with
  | zero =>
    intro L hL
    have hL0 : (0 : ℝ) < L := one_pos.trans_le hL
    rw [iterLogRem_zero, abs_sub_comm,
      abs_of_nonneg (quadMass_sub_primitive_nonneg β a L hβ hL0.le)]
    exact quadMass_sub_primitive_le β a L hβ hL0
  | succ m ih =>
    intro L hL
    rw [iterLogRem_succ_eq β a hβ m L hL ih, abs_neg]
    exact iterLogRem_tail_abs_le β a m L hL ih

/-- **Complete expansion of `H_m`**: `|H_m(L) − ∑_{i ≤ m} c_{m,i} log^i L| ≤ M/L` for `L ≥ 1`. -/
theorem iterLogPrim_expansion (β a : ℝ) (hβ : 0 < β) (m : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    |iterLogPrim β a m L - ∑ i ∈ Finset.range (m + 1), iterLogCoeff β a m i * Real.log L ^ i|
      ≤ quadMoment β a / L :=
  iterLogRem_abs_le β a hβ m L hL

/-- The polynomial coefficient of `Z_{k+2}` as a function of `n`. -/
noncomputable def iterChartCoeff (β a b : ℝ) (k : ℕ) (n : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 2),
    iterLogCoeff β a (k + 1) i * (Real.log n / 2 + ((k : ℝ) + 2) * Real.log b) ^ i

/-- **Complete expansion of the all-equal chart integral**:
`Z_{k+2}(n) = n^{-1/2} ∑_{i ≤ k+1} c_{k+1,i} (log n / 2 + (k+2) log b)^i + O(n^{-1})`. -/
theorem iterChart_expansion_isBigO (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) (k : ℕ) :
    (fun n : ℝ => iterChart β a b (k + 2) (Real.sqrt n)
        - n ^ (-(1 / 2 : ℝ)) * iterChartCoeff β a b k n)
      =O[atTop] fun n : ℝ => n⁻¹ := by
  apply IsBigO.of_bound (quadMoment β a / b ^ (k + 2))
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / b ^ (2 * (k + 2)))]
    with n hn hnb
  have hn0 : (0 : ℝ) < n := by linarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hL : 1 ≤ Real.sqrt n * b ^ (k + 2) := by
    have h1 : (1 / b ^ (k + 2)) ^ 2 ≤ n := by
      rw [div_pow, one_pow, ← pow_mul, mul_comm]; exact hnb
    have h2 : 1 / b ^ (k + 2) ≤ Real.sqrt n := by
      rw [Real.le_sqrt (by positivity) hn0.le]; exact h1
    calc (1 : ℝ) = 1 / b ^ (k + 2) * b ^ (k + 2) := by field_simp
      _ ≤ Real.sqrt n * b ^ (k + 2) := by gcongr
  have hlogL : Real.log (Real.sqrt n * b ^ (k + 2))
      = Real.log n / 2 + ((k : ℝ) + 2) * Real.log b := by
    rw [Real.log_mul hsn.ne' (by positivity), Real.log_sqrt hn0.le, Real.log_pow]
    push_cast; ring
  have hθ := iterLogPrim_expansion β a hβ (k + 1) _ hL
  rw [hlogL] at hθ
  have hpow : n ^ (-(1 / 2 : ℝ)) = (Real.sqrt n)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hn0.le]
  have heq : iterChart β a b (k + 2) (Real.sqrt n) - n ^ (-(1 / 2 : ℝ)) * iterChartCoeff β a b k n
      = (Real.sqrt n)⁻¹ * (iterLogPrim β a (k + 1) (Real.sqrt n * b ^ (k + 2))
          - iterChartCoeff β a b k n) := by
    rw [hpow, iterChart_succ_eq β a b (k + 1) _ hsn hb]; ring
  rw [heq, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn0), abs_mul,
    abs_of_pos (inv_pos.2 hsn)]
  calc (Real.sqrt n)⁻¹ * |iterLogPrim β a (k + 1) (Real.sqrt n * b ^ (k + 2))
        - iterChartCoeff β a b k n|
      ≤ (Real.sqrt n)⁻¹ * (quadMoment β a / (Real.sqrt n * b ^ (k + 2))) := by
        gcongr
        exact hθ
    _ = quadMoment β a / b ^ (k + 2) * ((Real.sqrt n)⁻¹ * (1 / Real.sqrt n)) := by
        field_simp
    _ = quadMoment β a / b ^ (k + 2) * n⁻¹ := by
        rw [one_div, ← mul_inv, Real.mul_self_sqrt hn0.le]

end Laplace.Grammar
