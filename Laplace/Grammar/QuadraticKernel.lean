/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LeadingContinuous

/-!
# The quadratic kernel, its primitive, and the logarithmic primitive (grammar §4.2, `d = 2` prep)

For the first multivariate standard integral (`d = 2`, `k = (1,1)`, `h = (0,0)`) the inner integral
reduces to the primitive `F(x) = ∫₀^x f`, `f(s) = e^{-βs² + βas}`, and the outer integral to the
*logarithmic primitive* `H(L) = ∫₀^L F(x)/x dx`. The `log n` of the two-dimensional asymptotic comes
from `H(L) ≈ A log L`, `A = ∫₀^∞ f = S_{1/2}(a)/2`, made precise here by the uniform squeeze

  `A log L - M ≤ H(L) ≤ A log L + E`   for `L ≥ 1`,   `M = ∫₀^∞ s f(s) ds`,   `E = e^{βa²/2}`.

Everything is one-dimensional and elementary: Gaussian domination, `0 ≤ F(x) ≤ E x`,
`0 ≤ A - F(x) ≤ M/x`, and the two interval integrals `∫₁^L dx/x = log L`, `∫₁^L dx/x² ≤ 1`.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set

namespace Laplace.Grammar

/-- The quadratic kernel `f(s) = e^{-βs² + βas}`. -/
noncomputable def quadKernel (β a s : ℝ) : ℝ := Real.exp (-β * s ^ 2 + β * a * s)

/-- Its primitive `F(x) = ∫₀^x f`. -/
noncomputable def quadPrimitive (β a x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, quadKernel β a s

/-- The total mass `A = ∫₀^∞ f`. -/
noncomputable def quadMass (β a : ℝ) : ℝ := ∫ s in Ioi (0 : ℝ), quadKernel β a s

/-- The first moment `M = ∫₀^∞ s f(s) ds`. -/
noncomputable def quadMoment (β a : ℝ) : ℝ := ∫ s in Ioi (0 : ℝ), s * quadKernel β a s

/-- The logarithmic primitive `H(L) = ∫₀^L F(x)/x dx`. -/
noncomputable def logPrimitive (β a L : ℝ) : ℝ := ∫ x in Ioc (0 : ℝ) L, quadPrimitive β a x / x

theorem quadKernel_pos (β a s : ℝ) : 0 < quadKernel β a s := Real.exp_pos _

theorem quadKernel_continuous (β a : ℝ) : Continuous (quadKernel β a) := by
  unfold quadKernel; fun_prop

/-- Gaussian domination `f(s) ≤ e^{βa²/2} e^{-(β/2)s²}`. -/
theorem quadKernel_le (β a s : ℝ) (hβ : 0 < β) :
    quadKernel β a s ≤ Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 2) * s ^ 2) := by
  unfold quadKernel
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith [mul_nonneg hβ.le (sq_nonneg (s - a))]

theorem quadKernel_le_const (β a s : ℝ) (hβ : 0 < β) :
    quadKernel β a s ≤ Real.exp (β * a ^ 2 / 2) := by
  calc quadKernel β a s ≤ Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 2) * s ^ 2) :=
        quadKernel_le β a s hβ
    _ ≤ Real.exp (β * a ^ 2 / 2) * 1 := by
        gcongr
        exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg s])
    _ = _ := mul_one _

/-- The standard integrand at `n = 1`, `k = 1` is the quadratic kernel times `u^h`. -/
private theorem standardIntegrand_one_eq (β a : ℝ) (h : ℕ) (u : ℝ) :
    u ^ h * Real.exp (-β * 1 * u ^ (2 * 1) + β * Real.sqrt 1 * u ^ 1 * a)
      = u ^ h * quadKernel β a u := by
  unfold quadKernel
  simp only [Real.sqrt_one, pow_one, mul_one]
  congr 2; ring

theorem quadKernel_integrableOn (β a : ℝ) (hβ : 0 < β) :
    IntegrableOn (quadKernel β a) (Ioi 0) := by
  have := standardIntegrand_integrableOn β 1 a 0 1 hβ one_pos one_pos
  refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
  beta_reduce; rw [standardIntegrand_one_eq]; simp

theorem quadMoment_integrand_integrableOn (β a : ℝ) (hβ : 0 < β) :
    IntegrableOn (fun s => s * quadKernel β a s) (Ioi 0) := by
  have := standardIntegrand_integrableOn β 1 a 1 1 hβ one_pos one_pos
  refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
  beta_reduce; rw [standardIntegrand_one_eq]; simp

/-- `A = S_{1/2}(a)/2`. -/
theorem quadMass_eq (β a : ℝ) :
    quadMass β a = (1 / 2 : ℝ) * fluctuation β (1 / 2) a := by
  have h := standardIntegral1D_eq_fluctuation β 1 a 0 1 one_pos one_pos
  have hcongr : (∫ u in Ioi (0 : ℝ),
      u ^ 0 * Real.exp (-β * 1 * u ^ (2 * 1) + β * Real.sqrt 1 * u ^ 1 * a)) = quadMass β a := by
    unfold quadMass
    exact setIntegral_congr_fun measurableSet_Ioi fun u _ => by
      rw [standardIntegrand_one_eq]; simp
  rw [hcongr] at h
  rw [h]; norm_num

theorem quadMass_pos (β a : ℝ) (hβ : 0 < β) : 0 < quadMass β a := by
  rw [quadMass_eq β a]
  have := fluctuation_pos β (1 / 2) a hβ (by norm_num)
  positivity

/-- `M = S_1(a)/2`. -/
theorem quadMoment_eq (β a : ℝ) :
    quadMoment β a = (1 / 2 : ℝ) * fluctuation β 1 a := by
  have h := standardIntegral1D_eq_fluctuation β 1 a 1 1 one_pos one_pos
  have hcongr : (∫ u in Ioi (0 : ℝ),
      u ^ 1 * Real.exp (-β * 1 * u ^ (2 * 1) + β * Real.sqrt 1 * u ^ 1 * a)) = quadMoment β a := by
    unfold quadMoment
    exact setIntegral_congr_fun measurableSet_Ioi fun u _ => by
      rw [standardIntegrand_one_eq]; simp
  rw [hcongr] at h
  rw [h]; norm_num

theorem quadMoment_nonneg (β a : ℝ) : 0 ≤ quadMoment β a :=
  setIntegral_nonneg measurableSet_Ioi fun s hs =>
    mul_nonneg (le_of_lt hs) (quadKernel_pos β a s).le

theorem quadPrimitive_continuous (β a : ℝ) : Continuous (quadPrimitive β a) :=
  intervalIntegral.continuous_primitive
    (fun c d => (quadKernel_continuous β a).intervalIntegrable c d) 0

theorem quadPrimitive_nonneg (β a x : ℝ) (hx : 0 ≤ x) : 0 ≤ quadPrimitive β a x :=
  intervalIntegral.integral_nonneg hx fun s _ => (quadKernel_pos β a s).le

/-- `F(x) ≤ E x` for `x ≥ 0`. -/
theorem quadPrimitive_le (β a x : ℝ) (hβ : 0 < β) (hx : 0 ≤ x) :
    quadPrimitive β a x ≤ Real.exp (β * a ^ 2 / 2) * x := by
  unfold quadPrimitive
  calc (∫ s in (0 : ℝ)..x, quadKernel β a s)
      ≤ ∫ _ in (0 : ℝ)..x, Real.exp (β * a ^ 2 / 2) :=
        intervalIntegral.integral_mono_on hx ((quadKernel_continuous β a).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _) fun s _ => quadKernel_le_const β a s hβ
    _ = Real.exp (β * a ^ 2 / 2) * x := by rw [intervalIntegral.integral_const]; simp [mul_comm]

/-- `A - F(x) = ∫_x^∞ f` for `x ≥ 0`. -/
theorem quadMass_sub_primitive (β a x : ℝ) (hβ : 0 < β) (hx : 0 ≤ x) :
    quadMass β a - quadPrimitive β a x = ∫ s in Ioi x, quadKernel β a s := by
  have hint := quadKernel_integrableOn β a hβ
  have hsplit := setIntegral_union (Ioc_disjoint_Ioi (le_refl x)) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hx))
  rw [Ioc_union_Ioi_eq_Ioi hx] at hsplit
  rw [quadMass, quadPrimitive, intervalIntegral.integral_of_le hx, hsplit]; ring

theorem quadMass_sub_primitive_nonneg (β a x : ℝ) (hβ : 0 < β) (hx : 0 ≤ x) :
    0 ≤ quadMass β a - quadPrimitive β a x := by
  rw [quadMass_sub_primitive β a x hβ hx]
  exact setIntegral_nonneg measurableSet_Ioi fun s _ => (quadKernel_pos β a s).le

/-- `A - F(x) ≤ M/x` for `x > 0`. -/
theorem quadMass_sub_primitive_le (β a x : ℝ) (hβ : 0 < β) (hx : 0 < x) :
    quadMass β a - quadPrimitive β a x ≤ quadMoment β a / x := by
  rw [le_div_iff₀ hx, quadMass_sub_primitive β a x hβ hx.le]
  have hint := quadKernel_integrableOn β a hβ
  have hmint := quadMoment_integrand_integrableOn β a hβ
  calc (∫ s in Ioi x, quadKernel β a s) * x = ∫ s in Ioi x, x * quadKernel β a s := by
        rw [MeasureTheory.integral_const_mul]; ring
    _ ≤ ∫ s in Ioi x, s * quadKernel β a s :=
        setIntegral_mono_on ((hint.mono_set (Ioi_subset_Ioi hx.le)).const_mul x)
          (hmint.mono_set (Ioi_subset_Ioi hx.le)) measurableSet_Ioi fun s hs =>
          mul_le_mul_of_nonneg_right (le_of_lt hs) (quadKernel_pos β a s).le
    _ ≤ ∫ s in Ioi 0, s * quadKernel β a s := by
        apply setIntegral_mono_set hmint
        · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
          exact Filter.Eventually.of_forall fun s hs =>
            mul_nonneg (le_of_lt hs) (quadKernel_pos β a s).le
        · exact (Ioi_subset_Ioi hx.le).eventuallyLE
    _ = quadMoment β a := rfl

/-- `F(x)/x` is bounded by `E` on `(0, L]`, hence integrable there. -/
theorem quadPrimitive_div_integrableOn (β a L : ℝ) (hβ : 0 < β) :
    IntegrableOn (fun x => quadPrimitive β a x / x) (Ioc 0 L) := by
  refine Integrable.mono' (g := fun _ => Real.exp (β * a ^ 2 / 2))
    (integrableOn_const measure_Ioc_lt_top.ne) ?_ ?_
  · exact ((quadPrimitive_continuous β a).measurable.div measurable_id).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (quadPrimitive_nonneg β a x hx0.le) hx0.le),
      div_le_iff₀ hx0]
    exact quadPrimitive_le β a x hβ hx0.le

/-- `x⁻¹` is integrable on `(1, L]` (bounded by `1`). -/
private theorem inv_integrableOn_Ioc_one (L : ℝ) :
    IntegrableOn (fun x : ℝ => x⁻¹) (Ioc (1 : ℝ) L) := by
  refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrableOn_const measure_Ioc_lt_top.ne)
    measurable_inv.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall fun x hx => ?_
  have hx1 : (1 : ℝ) < x := hx.1
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (zero_lt_one.trans hx1))]
  exact inv_le_one_of_one_le₀ hx1.le

/-- `(x²)⁻¹` is integrable on `(1, L]` (bounded by `1`). -/
private theorem inv_sq_integrableOn_Ioc_one (L : ℝ) :
    IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) (Ioc (1 : ℝ) L) := by
  refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrableOn_const measure_Ioc_lt_top.ne)
    ((measurable_id.pow_const 2).inv).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall fun x hx => ?_
  have hx1 : (1 : ℝ) < x := hx.1
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (by positivity))]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hx1.le)

/-- Splitting `H(L) - A log L` at `x = 1`. -/
theorem logPrimitive_split (β a L : ℝ) (hβ : 0 < β) (hL : 1 ≤ L) :
    logPrimitive β a L - quadMass β a * Real.log L
      = (∫ x in Ioc (0 : ℝ) 1, quadPrimitive β a x / x)
        - ∫ x in Ioc (1 : ℝ) L, (quadMass β a - quadPrimitive β a x) / x := by
  have hint := quadPrimitive_div_integrableOn β a L hβ
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioc 1 L) :=
    Set.disjoint_left.2 fun x h1 h2 => (not_lt.2 h1.2) h2.1
  have hsplit := setIntegral_union hdisj measurableSet_Ioc (hint.mono_set (Ioc_subset_Ioc_right hL))
    (hint.mono_set (Ioc_subset_Ioc_left zero_le_one))
  rw [Ioc_union_Ioc_eq_Ioc zero_le_one hL] at hsplit
  have hinv : IntegrableOn (fun x : ℝ => quadMass β a / x) (Ioc 1 L) := by
    have h2 : IntegrableOn (fun x : ℝ => quadMass β a * x⁻¹) (Ioc 1 L) :=
      (inv_integrableOn_Ioc_one L).const_mul _
    refine h2.congr_fun (fun x _ => ?_) measurableSet_Ioc
    simp [div_eq_mul_inv]
  have hlog : (∫ x in Ioc (1 : ℝ) L, quadMass β a / x) = quadMass β a * Real.log L := by
    rw [← intervalIntegral.integral_of_le hL]
    have : (∫ x in (1 : ℝ)..L, quadMass β a / x) = quadMass β a * ∫ x in (1 : ℝ)..L, 1 / x := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; ring
    rw [this, integral_one_div_of_pos one_pos (lt_of_lt_of_le one_pos hL), div_one]
  have hsub : (∫ x in Ioc (1 : ℝ) L, (quadMass β a - quadPrimitive β a x) / x)
      = (∫ x in Ioc (1 : ℝ) L, quadMass β a / x)
        - ∫ x in Ioc (1 : ℝ) L, quadPrimitive β a x / x := by
    rw [← MeasureTheory.integral_sub hinv (hint.mono_set (Ioc_subset_Ioc_left zero_le_one))]
    exact setIntegral_congr_fun measurableSet_Ioc fun x _ => by ring
  rw [logPrimitive, hsplit, hsub, hlog]; ring

/-- `∫₁^L dx/x² = 1 - 1/L`. -/
theorem integral_Ioc_inv_sq (L : ℝ) (hL : 1 ≤ L) :
    (∫ x in Ioc (1 : ℝ) L, (x ^ 2)⁻¹) = 1 - L⁻¹ := by
  rw [← intervalIntegral.integral_of_le hL]
  have h0 : (0 : ℝ) ∉ Set.uIcc 1 L := by
    rw [Set.uIcc_of_le hL]; intro h; linarith [h.1]
  have := integral_zpow (a := (1 : ℝ)) (b := L) (n := -2) (Or.inr ⟨by norm_num, h0⟩)
  have hfun : (fun x : ℝ => (x ^ 2)⁻¹) = fun x : ℝ => x ^ (-2 : ℤ) := by
    funext x; rw [zpow_neg, zpow_two, sq]
  rw [hfun, this]
  norm_num
  ring

/-- **The uniform squeeze** `A log L - M ≤ H(L) ≤ A log L + E` for `L ≥ 1`. -/
theorem logPrimitive_bounds (β a L : ℝ) (hβ : 0 < β) (hL : 1 ≤ L) :
    quadMass β a * Real.log L - quadMoment β a ≤ logPrimitive β a L ∧
      logPrimitive β a L ≤ quadMass β a * Real.log L + Real.exp (β * a ^ 2 / 2) := by
  have hsplit := logPrimitive_split β a L hβ hL
  have hint := quadPrimitive_div_integrableOn β a L hβ
  -- the piece on (0,1]
  have h1_nonneg : 0 ≤ ∫ x in Ioc (0 : ℝ) 1, quadPrimitive β a x / x :=
    setIntegral_nonneg measurableSet_Ioc fun x hx =>
      div_nonneg (quadPrimitive_nonneg β a x hx.1.le) hx.1.le
  have h1_le : (∫ x in Ioc (0 : ℝ) 1, quadPrimitive β a x / x) ≤ Real.exp (β * a ^ 2 / 2) := by
    calc (∫ x in Ioc (0 : ℝ) 1, quadPrimitive β a x / x)
        ≤ ∫ _ in Ioc (0 : ℝ) 1, Real.exp (β * a ^ 2 / 2) :=
          setIntegral_mono_on (hint.mono_set (Ioc_subset_Ioc_right hL))
            (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc fun x hx => by
              rw [div_le_iff₀ hx.1]; exact quadPrimitive_le β a x hβ hx.1.le
      _ = Real.exp (β * a ^ 2 / 2) := by
          rw [setIntegral_const]; simp [Measure.real, Real.volume_Ioc]
  -- the piece on (1, L]
  have h2_nonneg : 0 ≤ ∫ x in Ioc (1 : ℝ) L, (quadMass β a - quadPrimitive β a x) / x :=
    setIntegral_nonneg measurableSet_Ioc fun x hx =>
      div_nonneg (quadMass_sub_primitive_nonneg β a x hβ (zero_le_one.trans hx.1.le))
        (zero_le_one.trans hx.1.le)
  have h2_le : (∫ x in Ioc (1 : ℝ) L, (quadMass β a - quadPrimitive β a x) / x)
      ≤ quadMoment β a := by
    have hsq : IntegrableOn (fun x : ℝ => quadMoment β a * (x ^ 2)⁻¹) (Ioc 1 L) :=
      (inv_sq_integrableOn_Ioc_one L).const_mul _
    have hdiff_int : IntegrableOn (fun x : ℝ => (quadMass β a - quadPrimitive β a x) / x)
        (Ioc 1 L) := by
      have hinv : IntegrableOn (fun x : ℝ => quadMass β a / x) (Ioc 1 L) := by
        have h2 : IntegrableOn (fun x : ℝ => quadMass β a * x⁻¹) (Ioc 1 L) :=
          (inv_integrableOn_Ioc_one L).const_mul _
        refine h2.congr_fun (fun x _ => ?_) measurableSet_Ioc
        simp [div_eq_mul_inv]
      have h3 : IntegrableOn (fun x : ℝ => quadMass β a / x - quadPrimitive β a x / x) (Ioc 1 L) :=
        hinv.sub (hint.mono_set (Ioc_subset_Ioc_left zero_le_one))
      refine h3.congr_fun (fun x _ => ?_) measurableSet_Ioc
      beta_reduce; ring
    have hpt : ∀ x ∈ Ioc (1 : ℝ) L,
        (quadMass β a - quadPrimitive β a x) / x ≤ quadMoment β a * (x ^ 2)⁻¹ := by
      intro x hx
      have hx0 : (0 : ℝ) < x := one_pos.trans hx.1
      rw [div_le_iff₀ hx0]
      calc quadMass β a - quadPrimitive β a x ≤ quadMoment β a / x :=
            quadMass_sub_primitive_le β a x hβ hx0
        _ = quadMoment β a * (x ^ 2)⁻¹ * x := by field_simp
    calc (∫ x in Ioc (1 : ℝ) L, (quadMass β a - quadPrimitive β a x) / x)
        ≤ ∫ x in Ioc (1 : ℝ) L, quadMoment β a * (x ^ 2)⁻¹ :=
          setIntegral_mono_on hdiff_int hsq measurableSet_Ioc hpt
      _ = quadMoment β a * (1 - L⁻¹) := by
          rw [MeasureTheory.integral_const_mul, integral_Ioc_inv_sq L hL]
      _ ≤ quadMoment β a := by
          have := quadMoment_nonneg β a
          have hLinv : 0 ≤ L⁻¹ := inv_nonneg.2 (zero_le_one.trans hL)
          nlinarith
  constructor <;> linarith

end Laplace.Grammar
