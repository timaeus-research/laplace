/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TwoDGeneralSecondOrder

/-!
# Iterated "divide and integrate" primitives of a general base (grammar §4.2)

Unit 43 proved the complete polynomial-in-`log` expansion of the iterated primitives
`H_{m+1}(x) = ∫₀^x H_m(t)/t dt` of the quadratic primitive `F₀`. The mechanism only uses four facts
about the base `G = H₀`: measurability, `0 ≤ G ≤ A`, `G(x) ≤ C x^δ` near `0` (`δ > 0`), and the tail
`|G(L) − A| ≤ M/L` for `L ≥ 1`. Here the construction is carried out for an arbitrary base
satisfying these (`LogBase`), with all integrals over `Ioc`, and instantiated for the weighted
primitives `F_γ` (`γ > −1`): `A = A_γ`, `M = A_{γ+1}`, `C = E/(γ+1)`, `δ = γ+1`. The result is

  `|H^G_m(L) − ∑_{i ≤ m} c_{m,i} log^i L| ≤ M/L`  (`L ≥ 1`),  `c_{m,m} = A/m!`,

with the same recursive coefficients as unit 43. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter

namespace Laplace.Grammar

/-- Iterated "divide by `t` and integrate over `(0, x]`" primitives of a base function. -/
noncomputable def iterDivPrim (G : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => G
  | m + 1 => fun x => ∫ t in Ioc (0 : ℝ) x, iterDivPrim G m t / t

theorem iterDivPrim_zero (G : ℝ → ℝ) : iterDivPrim G 0 = G := rfl

theorem iterDivPrim_succ (G : ℝ → ℝ) (m : ℕ) (x : ℝ) :
    iterDivPrim G (m + 1) x = ∫ t in Ioc (0 : ℝ) x, iterDivPrim G m t / t := rfl

/-- Hypotheses on a base function under which the iterated expansion goes through. -/
structure LogBase (G : ℝ → ℝ) (A M C δ : ℝ) : Prop where
  measurable : Measurable G
  nonneg : ∀ x, 0 ≤ G x
  le_mass : ∀ x, G x ≤ A
  le_pow : ∀ x, 0 < x → x ≤ 1 → G x ≤ C * x ^ δ
  δ_pos : 0 < δ
  tail : ∀ L, 1 ≤ L → |G L - A| ≤ M / L

theorem integrableOn_rpow_sub_one_Ioc (δ : ℝ) (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => t ^ (δ - 1)) (Ioc 0 1) :=
  (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < δ - 1) (a := 0) (b := 1)).1

theorem integral_Ioc_rpow_sub_one (δ x : ℝ) (hδ : 0 < δ) (hx : 0 ≤ x) :
    (∫ t in Ioc (0 : ℝ) x, t ^ (δ - 1)) = x ^ δ / δ := by
  rw [← intervalIntegral.integral_of_le hx, integral_rpow (Or.inl (by linarith)), sub_add_cancel,
    Real.zero_rpow hδ.ne', sub_zero]

/-- A nonnegative measurable `H` with `H ≤ C' t^δ` near `0` and bounded on `(1, L]` has `H/t`
integrable on `(0, L]`. -/
theorem div_integrableOn_of_bounds {H : ℝ → ℝ} {C' δ K L : ℝ} (hδ : 0 < δ) (hmeas : Measurable H)
    (hnn : ∀ x, 0 ≤ H x) (hpow : ∀ x, 0 < x → x ≤ 1 → H x ≤ C' * x ^ δ)
    (hbdd : ∀ x, 1 < x → x ≤ L → H x ≤ K) :
    IntegrableOn (fun t => H t / t) (Ioc 0 L) := by
  have hmeas' : Measurable (fun t => H t / t) := hmeas.div measurable_id
  have h1 : IntegrableOn (fun t => H t / t) (Ioc 0 1) := by
    refine Integrable.mono' (g := fun t => C' * t ^ (δ - 1))
      ((integrableOn_rpow_sub_one_Ioc δ hδ).const_mul _) hmeas'.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hnn t) ht.1.le), div_le_iff₀ ht.1]
    calc H t ≤ C' * t ^ δ := hpow t ht.1 ht.2
      _ = C' * t ^ (δ - 1) * t := by
          rw [mul_assoc, ← Real.rpow_add_one ht.1.ne', sub_add_cancel]
  have h2 : IntegrableOn (fun t => H t / t) (Ioc 1 L) := by
    refine Integrable.mono' (g := fun _ => K) (integrableOn_const measure_Ioc_lt_top.ne)
      hmeas'.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht0 : (0 : ℝ) < t := one_pos.trans ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hnn t) ht0.le)]
    exact (div_le_self (hnn t) ht.1.le).trans (hbdd t ht.1 ht.2)
  rcases le_or_gt L 1 with hL | hL
  · exact h1.mono_set (Ioc_subset_Ioc_right hL)
  · have := h1.union h2
    rwa [Ioc_union_Ioc_eq_Ioc zero_le_one hL.le] at this

/-- Per-level properties of the iterated primitives: measurable, nonnegative, `≤ (C/δ^m) x^δ` near
`0`, and `H_m/t` integrable on every `(0, L]`. -/
theorem iterDivPrim_props {G : ℝ → ℝ} {A M C δ : ℝ} (hG : LogBase G A M C δ) (m : ℕ) :
    Measurable (iterDivPrim G m) ∧ (∀ x, 0 ≤ iterDivPrim G m x)
      ∧ (∀ x, 0 < x → x ≤ 1 → iterDivPrim G m x ≤ C / δ ^ m * x ^ δ)
      ∧ (∀ L, IntegrableOn (fun t => iterDivPrim G m t / t) (Ioc 0 L)) := by
  have hδ := hG.δ_pos
  induction m with
  | zero =>
    have hpow : ∀ x, 0 < x → x ≤ 1 → iterDivPrim G 0 x ≤ C / δ ^ 0 * x ^ δ := by
      intro x hx hx1
      rw [iterDivPrim_zero, pow_zero, div_one]
      exact hG.le_pow x hx hx1
    exact ⟨hG.measurable, hG.nonneg, hpow, fun L =>
      div_integrableOn_of_bounds hδ hG.measurable hG.nonneg hpow fun x _ _ => hG.le_mass x⟩
  | succ m ih =>
    obtain ⟨hmeas, hnn, hpow, hint⟩ := ih
    have hnn' : ∀ x, 0 ≤ iterDivPrim G (m + 1) x := fun x =>
      setIntegral_nonneg measurableSet_Ioc fun t ht => div_nonneg (hnn t) ht.1.le
    have hmono : Monotone (iterDivPrim G (m + 1)) := by
      intro x y hxy
      refine setIntegral_mono_set (hint y) ?_
        (Filter.Eventually.of_forall fun z hz => Ioc_subset_Ioc_right hxy hz)
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall fun t ht => div_nonneg (hnn t) ht.1.le
    have hmeas' : Measurable (iterDivPrim G (m + 1)) := hmono.measurable
    have hpow' : ∀ x, 0 < x → x ≤ 1 → iterDivPrim G (m + 1) x ≤ C / δ ^ (m + 1) * x ^ δ := by
      intro x hx hx1
      rw [iterDivPrim_succ]
      calc (∫ t in Ioc (0 : ℝ) x, iterDivPrim G m t / t)
          ≤ ∫ t in Ioc (0 : ℝ) x, C / δ ^ m * t ^ (δ - 1) := by
            refine setIntegral_mono_on (hint x)
              (((integrableOn_rpow_sub_one_Ioc δ hδ).mono_set
                (Ioc_subset_Ioc_right hx1)).const_mul _)
              measurableSet_Ioc fun t ht => ?_
            rw [div_le_iff₀ ht.1]
            calc iterDivPrim G m t ≤ C / δ ^ m * t ^ δ := hpow t ht.1 (ht.2.trans hx1)
              _ = C / δ ^ m * t ^ (δ - 1) * t := by
                  rw [mul_assoc, ← Real.rpow_add_one ht.1.ne', sub_add_cancel]
        _ = C / δ ^ (m + 1) * x ^ δ := by
            rw [MeasureTheory.integral_const_mul, integral_Ioc_rpow_sub_one δ x hδ hx.le, pow_succ]
            field_simp
    exact ⟨hmeas', hnn', hpow', fun L =>
      div_integrableOn_of_bounds hδ hmeas' hnn' hpow' fun x _ hxL => hmono hxL⟩

/-- The expansion coefficients of the iterated primitives of a base with mass `A`. -/
noncomputable def divCoeff (G : ℝ → ℝ) (A : ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => A
  | 0, _ + 1 => 0
  | m + 1, 0 => (∫ x in Ioc (0 : ℝ) 1, iterDivPrim G m x / x)
      + ∫ x in Ioi (1 : ℝ), (iterDivPrim G m x
          - ∑ i ∈ Finset.range (m + 1), divCoeff G A m i * Real.log x ^ i) / x
  | m + 1, i + 1 => divCoeff G A m i / ((i : ℝ) + 1)

/-- The remainder `θ_m(x) = H_m(x) − ∑_{i ≤ m} c_{m,i} log^i x`. -/
noncomputable def divRem (G : ℝ → ℝ) (A : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  iterDivPrim G m x - ∑ i ∈ Finset.range (m + 1), divCoeff G A m i * Real.log x ^ i

theorem divCoeff_zero_zero (G : ℝ → ℝ) (A : ℝ) : divCoeff G A 0 0 = A := rfl

theorem divCoeff_succ_zero (G : ℝ → ℝ) (A : ℝ) (m : ℕ) :
    divCoeff G A (m + 1) 0 = (∫ x in Ioc (0 : ℝ) 1, iterDivPrim G m x / x)
      + ∫ x in Ioi (1 : ℝ), divRem G A m x / x := rfl

theorem divCoeff_succ_succ (G : ℝ → ℝ) (A : ℝ) (m i : ℕ) :
    divCoeff G A (m + 1) (i + 1) = divCoeff G A m i / ((i : ℝ) + 1) := rfl

/-- `c_{m,m} = A / m!`. -/
theorem divCoeff_top (G : ℝ → ℝ) (A : ℝ) (m : ℕ) :
    divCoeff G A m m = A / (m.factorial : ℝ) := by
  induction m with
  | zero => simp [divCoeff_zero_zero]
  | succ m ih =>
    rw [divCoeff_succ_succ, ih, Nat.factorial_succ]
    push_cast
    have h1 : (m.factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((m : ℝ) + 1) ≠ 0 := by positivity
    field_simp

theorem divRem_zero (G : ℝ → ℝ) (A x : ℝ) : divRem G A 0 x = G x - A := by
  simp [divRem, divCoeff_zero_zero, iterDivPrim_zero]

theorem divRem_div_measurable {G : ℝ → ℝ} {A M C δ : ℝ} (hG : LogBase G A M C δ) (m : ℕ) :
    Measurable (fun x => divRem G A m x / x) := by
  refine Measurable.div ?_ measurable_id
  refine (iterDivPrim_props hG m).1.sub ?_
  refine Finset.measurable_sum _ fun i _ => ?_
  exact measurable_const.mul (Real.measurable_log.pow_const i)

theorem divRem_div_bounds (G : ℝ → ℝ) (A M : ℝ) (m : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (hb : |divRem G A m x| ≤ M / x) :
    |divRem G A m x / x| ≤ M * x ^ (-2 : ℝ) := by
  have hx0 : (0 : ℝ) < x := one_pos.trans_le hx
  rw [abs_div, abs_of_pos hx0, Real.rpow_neg hx0.le, Real.rpow_two, div_le_iff₀ hx0]
  calc |divRem G A m x| ≤ M / x := hb
    _ = M * (x ^ 2)⁻¹ * x := by field_simp

theorem divRem_div_integrableOn {G : ℝ → ℝ} {A M C δ : ℝ} (hG : LogBase G A M C δ) (m : ℕ)
    (c : ℝ) (hc : 1 ≤ c) (hb : ∀ L, 1 ≤ L → |divRem G A m L| ≤ M / L) :
    IntegrableOn (fun x => divRem G A m x / x) (Ioi c) := by
  have hc0 : (0 : ℝ) < c := one_pos.trans_le hc
  refine Integrable.mono' (g := fun x => M * x ^ (-2 : ℝ))
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hc0).const_mul _)
    (divRem_div_measurable hG m).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun x hx => ?_
  have hx1 : (1 : ℝ) ≤ x := hc.trans (le_of_lt hx)
  rw [Real.norm_eq_abs]
  exact divRem_div_bounds G A M m x hx1 (hb x hx1)

theorem divRem_tail_abs_le (G : ℝ → ℝ) (A M : ℝ) (m : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hb : ∀ L, 1 ≤ L → |divRem G A m L| ≤ M / L) :
    |∫ x in Ioi L, divRem G A m x / x| ≤ M / L := by
  have hL0 : (0 : ℝ) < L := one_pos.trans_le hL
  have hint : (∫ x in Ioi L, M * x ^ (-2 : ℝ)) = M / L := by
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
  exact divRem_div_bounds G A M m x hx1 (hb x hx1)

/-- **The transfer step**: for `L ≥ 1`, `θ_{m+1}(L) = −∫_L^∞ θ_m(x)/x dx`. -/
theorem divRem_succ_eq {G : ℝ → ℝ} {A M C δ : ℝ} (hG : LogBase G A M C δ) (m : ℕ) (L : ℝ)
    (hL : 1 ≤ L) (hb : ∀ L, 1 ≤ L → |divRem G A m L| ≤ M / L) :
    divRem G A (m + 1) L = -∫ x in Ioi L, divRem G A m x / x := by
  have hint : IntegrableOn (fun x => iterDivPrim G m x / x) (Ioc 0 L) :=
    (iterDivPrim_props hG m).2.2.2 L
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioc 1 L) :=
    Set.disjoint_left.2 fun x h1 h2 => (not_lt.2 h1.2) h2.1
  have hsplit := setIntegral_union hdisj measurableSet_Ioc (hint.mono_set (Ioc_subset_Ioc_right hL))
    (hint.mono_set (Ioc_subset_Ioc_left zero_le_one))
    (f := fun x => iterDivPrim G m x / x)
  rw [Ioc_union_Ioc_eq_Ioc zero_le_one hL] at hsplit
  have hθint := divRem_div_integrableOn hG m 1 le_rfl hb
  have hθsplit := setIntegral_union (Ioc_disjoint_Ioi (le_refl L)) measurableSet_Ioi
    (hθint.mono_set Ioc_subset_Ioi_self) (hθint.mono_set (Ioi_subset_Ioi hL))
    (f := fun x => divRem G A m x / x)
  rw [Ioc_union_Ioi_eq_Ioi hL] at hθsplit
  have hpt : ∀ x ∈ Ioc (1 : ℝ) L, iterDivPrim G m x / x
      = (∑ i ∈ Finset.range (m + 1), divCoeff G A m i * (Real.log x ^ i / x))
        + divRem G A m x / x := by
    intro x _
    rw [divRem, sub_div, Finset.sum_div]
    simp_rw [mul_div_assoc]
    ring
  have hpoly : IntegrableOn
      (fun x : ℝ => ∑ i ∈ Finset.range (m + 1), divCoeff G A m i * (Real.log x ^ i / x))
      (Ioc 1 L) := by
    refine integrable_finsetSum _ fun i _ => ?_
    exact (integrableOn_log_pow_div_Ioc i L).const_mul _
  have hθ' : IntegrableOn (fun x => divRem G A m x / x) (Ioc 1 L) :=
    hθint.mono_set Ioc_subset_Ioi_self
  have hpolyval : (∫ x in Ioc (1 : ℝ) L,
      ∑ i ∈ Finset.range (m + 1), divCoeff G A m i * (Real.log x ^ i / x))
      = ∑ i ∈ Finset.range (m + 1),
          divCoeff G A m i * (Real.log L ^ (i + 1) / ((i : ℝ) + 1)) := by
    rw [integral_finsetSum _ fun i _ => (integrableOn_log_pow_div_Ioc i L).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le hL,
      integral_log_pow_div i L hL]
  have hmid : (∫ x in Ioc (1 : ℝ) L, iterDivPrim G m x / x)
      = (∑ i ∈ Finset.range (m + 1),
          divCoeff G A m i * (Real.log L ^ (i + 1) / ((i : ℝ) + 1)))
        + ∫ x in Ioc (1 : ℝ) L, divRem G A m x / x := by
    rw [setIntegral_congr_fun measurableSet_Ioc hpt, MeasureTheory.integral_add hpoly hθ', hpolyval]
  have hsum : ∑ i ∈ Finset.range (m + 1 + 1), divCoeff G A (m + 1) i * Real.log L ^ i
      = divCoeff G A (m + 1) 0
        + ∑ i ∈ Finset.range (m + 1),
            divCoeff G A m i * (Real.log L ^ (i + 1) / ((i : ℝ) + 1)) := by
    rw [Finset.sum_range_succ', pow_zero, mul_one, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [divCoeff_succ_succ]; ring
  rw [divRem, iterDivPrim_succ, hsplit, hmid, hsum, divCoeff_succ_zero, hθsplit]
  ring

/-- **Uniform remainder bound**: `|θ_m(L)| ≤ M/L` for all `m` and `L ≥ 1`. -/
theorem divRem_abs_le {G : ℝ → ℝ} {A M C δ : ℝ} (hG : LogBase G A M C δ) (m : ℕ) :
    ∀ L, 1 ≤ L → |divRem G A m L| ≤ M / L := by
  induction m with
  | zero =>
    intro L hL
    rw [divRem_zero]
    exact hG.tail L hL
  | succ m ih =>
    intro L hL
    rw [divRem_succ_eq hG m L hL ih, abs_neg]
    exact divRem_tail_abs_le G A M m L hL ih

/-- **Complete expansion for a general base**:
`|H_m(L) − ∑_{i ≤ m} c_{m,i} log^i L| ≤ M/L` for `L ≥ 1`. -/
theorem iterDivPrim_expansion {G : ℝ → ℝ} {A M C δ : ℝ} (hG : LogBase G A M C δ) (m : ℕ) (L : ℝ)
    (hL : 1 ≤ L) :
    |iterDivPrim G m L - ∑ i ∈ Finset.range (m + 1), divCoeff G A m i * Real.log L ^ i| ≤ M / L :=
  divRem_abs_le hG m L hL

/-- The weighted primitive `F_γ` is an admissible base with `A = A_γ`, `M = A_{γ+1}`,
`C = E/(γ+1)`, `δ = γ+1`. -/
theorem weightedPrimitive_logBase (β a γ : ℝ) (hβ : 0 < β) (hγ : -1 < γ) :
    LogBase (weightedPrimitive β a γ) (weightedMass β a γ) (weightedMass β a (γ + 1))
      (Real.exp (β * a ^ 2 / 2) / (γ + 1)) (γ + 1) where
  measurable := weightedPrimitive_measurable β a γ hβ hγ
  nonneg := weightedPrimitive_nonneg β a γ
  le_mass := by
    intro x
    rcases le_or_gt 0 x with hx | hx
    · exact weightedPrimitive_le_mass β a γ x hβ hγ hx
    · rw [weightedPrimitive, Ioc_eq_empty (not_lt.2 hx.le), Measure.restrict_empty,
        integral_zero_measure]
      exact (weightedMass_pos β a γ hβ hγ).le
  le_pow := by
    intro x hx _
    calc weightedPrimitive β a γ x ≤ Real.exp (β * a ^ 2 / 2) * x ^ (γ + 1) / (γ + 1) :=
          weightedPrimitive_le β a γ x hβ hγ hx.le
      _ = Real.exp (β * a ^ 2 / 2) / (γ + 1) * x ^ (γ + 1) := by ring
  δ_pos := by linarith
  tail := by
    intro L hL
    have hL0 : (0 : ℝ) < L := one_pos.trans_le hL
    rw [abs_sub_comm, abs_of_nonneg (weightedMass_sub_primitive_nonneg β a γ L hβ hγ hL0.le)]
    exact weightedMass_sub_primitive_le β a γ L hβ hγ hL0

/-- **Complete expansion of the iterated weighted primitives**. -/
theorem iterWeightedPrim_expansion (β a γ : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (m : ℕ) (L : ℝ)
    (hL : 1 ≤ L) :
    |iterDivPrim (weightedPrimitive β a γ) m L
        - ∑ i ∈ Finset.range (m + 1),
            divCoeff (weightedPrimitive β a γ) (weightedMass β a γ) m i * Real.log L ^ i|
      ≤ weightedMass β a (γ + 1) / L :=
  iterDivPrim_expansion (weightedPrimitive_logBase β a γ hβ hγ) m L hL

end Laplace.Grammar
