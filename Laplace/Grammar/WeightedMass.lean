/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.WeightedPrimitive

/-!
# Weighted masses and the weighted logarithmic primitive (grammar §4.2)

Infrastructure for the asymptotics of the general `(k, h)` reduction of unit 44. For `γ > −1`:

* `A_γ = ∫₀^∞ t^γ f(t) dt = S_{(γ+1)/2}(a)/2` (`weightedMass_eq`), positive and finite;
* `F_γ` is monotone (hence measurable), `0 ≤ F_γ(x) ≤ min(A_γ, E x^{γ+1}/(γ+1))`;
* the tail `A_γ − F_γ(x) = ∫_x^∞ t^γ f ≤ A_{γ+1}/x`;
* the weighted logarithmic primitive `∫₀^L F_γ(x)/x dx` satisfies
  `A_γ log L − A_{γ+1} ≤ · ≤ A_γ log L + E/(γ+1)²` for `L ≥ 1`.

Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter

namespace Laplace.Grammar

/-- `A_γ = ∫₀^∞ t^γ f(t) dt`. -/
noncomputable def weightedMass (β a γ : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), t ^ γ * quadKernel β a t

/-- The pointwise form of the substitution `s = x²` in the fluctuation integral. -/
theorem weighted_subst_pt (β a γ x : ℝ) (hx : 0 < x) :
    ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) • ((x ^ (2 : ℝ)) ^ ((γ + 1) / 2 - 1)
        * Real.exp (-β * x ^ (2 : ℝ) + β * a * Real.sqrt (x ^ (2 : ℝ))))
      = 2 * (x ^ γ * quadKernel β a x) := by
  have h1 : (x ^ (2 : ℝ)) ^ ((γ + 1) / 2 - 1) = x ^ (γ - 1) := by
    rw [← Real.rpow_mul hx.le]
    congr 1
    ring
  rw [smul_eq_mul, h1, Real.rpow_two, Real.sqrt_sq hx.le, show (2 : ℝ) - 1 = 1 by norm_num,
    Real.rpow_one, Real.rpow_sub_one hx.ne', quadKernel]
  field_simp

/-- `A_γ = S_{(γ+1)/2}(a)/2`. -/
theorem weightedMass_eq (β a γ : ℝ) :
    weightedMass β a γ = 1 / 2 * fluctuation β ((γ + 1) / 2) a := by
  have hsub := integral_comp_rpow_Ioi_of_pos
    (g := fun s => s ^ ((γ + 1) / 2 - 1) * Real.exp (-β * s + β * a * Real.sqrt s))
    (two_pos : (0 : ℝ) < 2)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => weighted_subst_pt β a γ x hx),
    MeasureTheory.integral_const_mul] at hsub
  rw [weightedMass, fluctuation, ← hsub]
  ring

theorem weightedKernel_integrableOn (β a γ : ℝ) (hβ : 0 < β) (hγ : -1 < γ) :
    IntegrableOn (fun t => t ^ γ * quadKernel β a t) (Ioi 0) := by
  have hlam : 0 < (γ + 1) / 2 := by linarith
  have h := (integrableOn_Ioi_comp_rpow_iff
    (fun s => s ^ ((γ + 1) / 2 - 1) * Real.exp (-β * s + β * a * Real.sqrt s))
    (two_ne_zero : (2 : ℝ) ≠ 0)).2 (fluctuation_integrableOn β ((γ + 1) / 2) hβ hlam a)
  have h' : IntegrableOn (fun x : ℝ => 1 / 2 * ((|(2 : ℝ)| * x ^ ((2 : ℝ) - 1))
      • ((x ^ (2 : ℝ)) ^ ((γ + 1) / 2 - 1)
        * Real.exp (-β * x ^ (2 : ℝ) + β * a * Real.sqrt (x ^ (2 : ℝ)))))) (Ioi 0) :=
    h.const_mul _
  refine h'.congr_fun (fun x hx => ?_) measurableSet_Ioi
  beta_reduce
  rw [abs_two, weighted_subst_pt β a γ x hx]
  ring

theorem weightedMass_pos (β a γ : ℝ) (hβ : 0 < β) (hγ : -1 < γ) : 0 < weightedMass β a γ := by
  rw [weightedMass_eq]
  have := fluctuation_pos β ((γ + 1) / 2) a hβ (by linarith)
  positivity

theorem weightedPrimitive_nonneg (β a γ x : ℝ) : 0 ≤ weightedPrimitive β a γ x :=
  setIntegral_nonneg measurableSet_Ioc fun t ht =>
    mul_nonneg (Real.rpow_nonneg ht.1.le γ) (quadKernel_pos β a t).le

theorem weightedPrimitive_mono (β a γ : ℝ) (hβ : 0 < β) (hγ : -1 < γ) :
    Monotone (weightedPrimitive β a γ) := by
  intro x y hxy
  refine setIntegral_mono_set
    ((weightedKernel_integrableOn β a γ hβ hγ).mono_set Ioc_subset_Ioi_self) ?_
    (Filter.Eventually.of_forall fun z hz => Ioc_subset_Ioc_right hxy hz)
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
  exact Filter.Eventually.of_forall fun t ht =>
    mul_nonneg (Real.rpow_nonneg ht.1.le γ) (quadKernel_pos β a t).le

theorem weightedPrimitive_measurable (β a γ : ℝ) (hβ : 0 < β) (hγ : -1 < γ) :
    Measurable (weightedPrimitive β a γ) :=
  (weightedPrimitive_mono β a γ hβ hγ).measurable

/-- `A_γ − F_γ(x) = ∫_x^∞ t^γ f(t) dt`. -/
theorem weightedMass_sub_primitive (β a γ x : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (hx : 0 ≤ x) :
    weightedMass β a γ - weightedPrimitive β a γ x = ∫ t in Ioi x, t ^ γ * quadKernel β a t := by
  have hint := weightedKernel_integrableOn β a γ hβ hγ
  have hsplit := setIntegral_union (Ioc_disjoint_Ioi (le_refl x)) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hx))
  rw [Ioc_union_Ioi_eq_Ioi hx] at hsplit
  rw [weightedMass, weightedPrimitive, hsplit]
  ring

theorem weightedMass_sub_primitive_nonneg (β a γ x : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (hx : 0 ≤ x) :
    0 ≤ weightedMass β a γ - weightedPrimitive β a γ x := by
  rw [weightedMass_sub_primitive β a γ x hβ hγ hx]
  exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (Real.rpow_nonneg (hx.trans_lt ht).le γ) (quadKernel_pos β a t).le

theorem weightedPrimitive_le_mass (β a γ x : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (hx : 0 ≤ x) :
    weightedPrimitive β a γ x ≤ weightedMass β a γ := by
  linarith [weightedMass_sub_primitive_nonneg β a γ x hβ hγ hx]

/-- **Tail bound**: `A_γ − F_γ(x) ≤ A_{γ+1}/x`. -/
theorem weightedMass_sub_primitive_le (β a γ x : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (hx : 0 < x) :
    weightedMass β a γ - weightedPrimitive β a γ x ≤ weightedMass β a (γ + 1) / x := by
  rw [weightedMass_sub_primitive β a γ x hβ hγ hx.le, le_div_iff₀ hx]
  have hint := weightedKernel_integrableOn β a γ hβ hγ
  have hint1 := weightedKernel_integrableOn β a (γ + 1) hβ (by linarith)
  calc (∫ t in Ioi x, t ^ γ * quadKernel β a t) * x
      = ∫ t in Ioi x, t ^ γ * quadKernel β a t * x := (MeasureTheory.integral_mul_const x _).symm
    _ ≤ ∫ t in Ioi x, t ^ (γ + 1) * quadKernel β a t := by
        refine setIntegral_mono_on ((hint.mono_set (Ioi_subset_Ioi hx.le)).mul_const x)
          (hint1.mono_set (Ioi_subset_Ioi hx.le)) measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := hx.trans ht
        rw [Real.rpow_add ht0, Real.rpow_one]
        calc t ^ γ * quadKernel β a t * x ≤ t ^ γ * quadKernel β a t * t :=
              mul_le_mul_of_nonneg_left (le_of_lt ht)
                (mul_nonneg (Real.rpow_nonneg ht0.le γ) (quadKernel_pos β a t).le)
          _ = t ^ γ * t * quadKernel β a t := by ring
    _ ≤ weightedMass β a (γ + 1) := by
        refine setIntegral_mono_set hint1 ?_
          (Filter.Eventually.of_forall fun z hz => Ioi_subset_Ioi hx.le hz)
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
        exact Filter.Eventually.of_forall fun t ht =>
          mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (quadKernel_pos β a t).le

/-- `F_γ(x) ≤ E x^{γ+1}/(γ+1)`. -/
theorem weightedPrimitive_le (β a γ x : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (hx : 0 ≤ x) :
    weightedPrimitive β a γ x ≤ Real.exp (β * a ^ 2 / 2) * x ^ (γ + 1) / (γ + 1) := by
  have hγ1 : γ + 1 ≠ 0 := by linarith
  rw [weightedPrimitive, ← intervalIntegral.integral_of_le hx]
  calc (∫ t in (0 : ℝ)..x, t ^ γ * quadKernel β a t)
      ≤ ∫ t in (0 : ℝ)..x, t ^ γ * Real.exp (β * a ^ 2 / 2) := by
        refine intervalIntegral.integral_mono_on hx
          ((intervalIntegral.intervalIntegrable_rpow' hγ).mul_continuousOn
            (quadKernel_continuous β a).continuousOn)
          ((intervalIntegral.intervalIntegrable_rpow' hγ).mul_const _) fun t ht => ?_
        exact mul_le_mul_of_nonneg_left (quadKernel_le_const β a t hβ) (Real.rpow_nonneg ht.1 γ)
    _ = Real.exp (β * a ^ 2 / 2) * x ^ (γ + 1) / (γ + 1) := by
        rw [intervalIntegral.integral_mul_const, integral_rpow (Or.inl hγ), Real.zero_rpow hγ1]
        ring

theorem weightedPrimitive_div_le (β a γ x : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (hx : 0 < x) :
    weightedPrimitive β a γ x / x ≤ Real.exp (β * a ^ 2 / 2) / (γ + 1) * x ^ γ := by
  rw [div_le_iff₀ hx]
  calc weightedPrimitive β a γ x ≤ Real.exp (β * a ^ 2 / 2) * x ^ (γ + 1) / (γ + 1) :=
        weightedPrimitive_le β a γ x hβ hγ hx.le
    _ = Real.exp (β * a ^ 2 / 2) / (γ + 1) * x ^ γ * x := by
        rw [Real.rpow_add hx, Real.rpow_one]; ring

theorem weightedPrimitive_div_integrableOn (β a γ L : ℝ) (hβ : 0 < β) (hγ : -1 < γ) :
    IntegrableOn (fun x => weightedPrimitive β a γ x / x) (Ioc 0 L) := by
  refine Integrable.mono' (g := fun x => Real.exp (β * a ^ 2 / 2) / (γ + 1) * x ^ γ)
    ((intervalIntegral.intervalIntegrable_rpow' hγ (a := 0) (b := L)).1.const_mul _)
    ((weightedPrimitive_measurable β a γ hβ hγ).div measurable_id).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall fun x hx => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (weightedPrimitive_nonneg β a γ x) hx.1.le)]
  exact weightedPrimitive_div_le β a γ x hβ hγ hx.1

/-- The weighted logarithmic primitive `∫₀^L F_γ(x)/x dx`. -/
noncomputable def weightedLogPrimitive (β a γ L : ℝ) : ℝ :=
  ∫ x in Ioc (0 : ℝ) L, weightedPrimitive β a γ x / x

theorem integrableOn_inv_Ioc_one (L : ℝ) : IntegrableOn (fun x : ℝ => x⁻¹) (Ioc 1 L) := by
  have : ContinuousOn (fun x : ℝ => x⁻¹) (Icc 1 L) :=
    continuousOn_inv₀.mono fun x hx => (lt_of_lt_of_le one_pos hx.1).ne'
  exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem integrableOn_inv_sq_Ioc_one (L : ℝ) :
    IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) (Ioc 1 L) := by
  have : ContinuousOn (fun x : ℝ => (x ^ 2)⁻¹) (Icc 1 L) :=
    (continuousOn_pow 2).inv₀ fun x hx => pow_ne_zero 2 (lt_of_lt_of_le one_pos hx.1).ne'
  exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- Split of the weighted logarithmic primitive at `x = 1`. -/
theorem weightedLogPrimitive_split (β a γ L : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (hL : 1 ≤ L) :
    weightedLogPrimitive β a γ L - weightedMass β a γ * Real.log L
      = (∫ x in Ioc (0 : ℝ) 1, weightedPrimitive β a γ x / x)
        - ∫ x in Ioc (1 : ℝ) L, (weightedMass β a γ - weightedPrimitive β a γ x) / x := by
  have hint := weightedPrimitive_div_integrableOn β a γ L hβ hγ
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioc 1 L) :=
    Set.disjoint_left.2 fun x h1 h2 => (not_lt.2 h1.2) h2.1
  have hsplit := setIntegral_union hdisj measurableSet_Ioc (hint.mono_set (Ioc_subset_Ioc_right hL))
    (hint.mono_set (Ioc_subset_Ioc_left zero_le_one))
    (f := fun x => weightedPrimitive β a γ x / x)
  rw [Ioc_union_Ioc_eq_Ioc zero_le_one hL] at hsplit
  have hA : IntegrableOn (fun x : ℝ => weightedMass β a γ * x⁻¹) (Ioc 1 L) :=
    (integrableOn_inv_Ioc_one L).const_mul _
  have hF : IntegrableOn (fun x : ℝ => weightedPrimitive β a γ x / x) (Ioc 1 L) :=
    hint.mono_set (Ioc_subset_Ioc_left zero_le_one)
  have hpt : ∀ x ∈ Ioc (1 : ℝ) L, (weightedMass β a γ - weightedPrimitive β a γ x) / x
      = weightedMass β a γ * x⁻¹ - weightedPrimitive β a γ x / x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := one_pos.trans hx.1
    field_simp
  rw [weightedLogPrimitive, hsplit, setIntegral_congr_fun measurableSet_Ioc hpt,
    MeasureTheory.integral_sub hA hF, MeasureTheory.integral_const_mul, integral_Ioc_inv L hL]
  ring

/-- **Weighted logarithmic squeeze**: for `L ≥ 1`,
`A_γ log L − A_{γ+1} ≤ ∫₀^L F_γ/x ≤ A_γ log L + E/(γ+1)²`. -/
theorem weightedLogPrimitive_bounds (β a γ L : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (hL : 1 ≤ L) :
    weightedMass β a γ * Real.log L - weightedMass β a (γ + 1) ≤ weightedLogPrimitive β a γ L ∧
      weightedLogPrimitive β a γ L
        ≤ weightedMass β a γ * Real.log L + Real.exp (β * a ^ 2 / 2) / (γ + 1) ^ 2 := by
  have hγ1 : 0 < γ + 1 := by linarith
  have hsplit := weightedLogPrimitive_split β a γ L hβ hγ hL
  have hint := weightedPrimitive_div_integrableOn β a γ L hβ hγ
  have hE0 : 0 < Real.exp (β * a ^ 2 / 2) := Real.exp_pos _
  -- the piece on (0, 1]
  have h1_nonneg : 0 ≤ ∫ x in Ioc (0 : ℝ) 1, weightedPrimitive β a γ x / x :=
    setIntegral_nonneg measurableSet_Ioc fun x hx =>
      div_nonneg (weightedPrimitive_nonneg β a γ x) hx.1.le
  have h1_le : (∫ x in Ioc (0 : ℝ) 1, weightedPrimitive β a γ x / x)
      ≤ Real.exp (β * a ^ 2 / 2) / (γ + 1) ^ 2 := by
    calc (∫ x in Ioc (0 : ℝ) 1, weightedPrimitive β a γ x / x)
        ≤ ∫ x in Ioc (0 : ℝ) 1, Real.exp (β * a ^ 2 / 2) / (γ + 1) * x ^ γ :=
          setIntegral_mono_on (hint.mono_set (Ioc_subset_Ioc_right hL))
            ((intervalIntegral.intervalIntegrable_rpow' hγ (a := 0) (b := 1)).1.const_mul _)
            measurableSet_Ioc
            fun x hx => weightedPrimitive_div_le β a γ x hβ hγ hx.1
      _ = Real.exp (β * a ^ 2 / 2) / (γ + 1) ^ 2 := by
          rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
            integral_rpow (Or.inl hγ), Real.one_rpow, Real.zero_rpow hγ1.ne', sub_zero]
          field_simp
  -- the piece on (1, L]
  have h2_nonneg : 0 ≤ ∫ x in Ioc (1 : ℝ) L, (weightedMass β a γ - weightedPrimitive β a γ x) / x :=
    setIntegral_nonneg measurableSet_Ioc fun x hx =>
      div_nonneg (weightedMass_sub_primitive_nonneg β a γ x hβ hγ (zero_le_one.trans hx.1.le))
        (zero_le_one.trans hx.1.le)
  have h2_le : (∫ x in Ioc (1 : ℝ) L, (weightedMass β a γ - weightedPrimitive β a γ x) / x)
      ≤ weightedMass β a (γ + 1) := by
    have hA1 : 0 ≤ weightedMass β a (γ + 1) := (weightedMass_pos β a (γ + 1) hβ (by linarith)).le
    have hdiff_int : IntegrableOn
        (fun x : ℝ => (weightedMass β a γ - weightedPrimitive β a γ x) / x) (Ioc 1 L) := by
      have hA : IntegrableOn (fun x : ℝ => weightedMass β a γ * x⁻¹) (Ioc 1 L) :=
        (integrableOn_inv_Ioc_one L).const_mul _
      have h3 : IntegrableOn
          (fun x : ℝ => weightedMass β a γ * x⁻¹ - weightedPrimitive β a γ x / x) (Ioc 1 L) :=
        hA.sub (hint.mono_set (Ioc_subset_Ioc_left zero_le_one))
      refine h3.congr_fun (fun x hx => ?_) measurableSet_Ioc
      have hx0 : (0 : ℝ) < x := one_pos.trans hx.1
      beta_reduce
      field_simp
    calc (∫ x in Ioc (1 : ℝ) L, (weightedMass β a γ - weightedPrimitive β a γ x) / x)
        ≤ ∫ x in Ioc (1 : ℝ) L, weightedMass β a (γ + 1) * (x ^ 2)⁻¹ := by
          refine setIntegral_mono_on hdiff_int ((integrableOn_inv_sq_Ioc_one L).const_mul _)
            measurableSet_Ioc fun x hx => ?_
          have hx0 : (0 : ℝ) < x := one_pos.trans hx.1
          rw [div_le_iff₀ hx0]
          calc weightedMass β a γ - weightedPrimitive β a γ x ≤ weightedMass β a (γ + 1) / x :=
                weightedMass_sub_primitive_le β a γ x hβ hγ hx0
            _ = weightedMass β a (γ + 1) * (x ^ 2)⁻¹ * x := by field_simp
      _ = weightedMass β a (γ + 1) * (1 - L⁻¹) := by
          rw [MeasureTheory.integral_const_mul, integral_Ioc_inv_sq L hL]
      _ ≤ weightedMass β a (γ + 1) := by
          have : 0 ≤ L⁻¹ := inv_nonneg.2 (zero_le_one.trans hL)
          nlinarith
  constructor <;> linarith

end Laplace.Grammar
