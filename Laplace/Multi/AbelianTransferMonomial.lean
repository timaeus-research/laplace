/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.AbelianTransferSquare

/-!
# Two-variable monomials: exponent and multiplicity

For `K_{a,b}(x, y) = x^{2a} y^{2b}` on the unit square the sublevel volume is

  `vol{K_{a,b} ≤ ε} = ∫₀¹ min(1, (ε/x^{2a})^{1/(2b)}) dx`

(`sublevelMass_monomialLoss_eq`), and elementary bounds on this integral give
the real log canonical threshold and multiplicity of the monomial:

* `a ≠ b`: `vol{K ≤ ε} = Θ(ε^{1/(2 max(a,b))})`, hence
  `∫ e^{-t K_{a,b}} = Θ(t^{-1/(2 max(a,b))})` (`boltzmannMass_monomialLoss_transfer`);
* `a = b`: the reparametrisation `{(xy)^{2a} ≤ ε} = {(xy)² ≤ ε^{1/a}}` reduces
  to the square instance and gives `Θ(t^{-1/(2a)} log t)`
  (`boltzmannMass_monomialLoss_diag_transfer`).

So the exponent is the minimum of the coordinate weights `1/(2a), 1/(2b)` and
the logarithm appears exactly when the minimum is attained twice — the
two-variable case of the monomial rule of singular learning theory, proved
with no resolution of singularities.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Laplace

/-- The monomial loss `x^{2a} y^{2b}`. -/
def monomialLoss (a b : ℕ) : ℝ × ℝ → ℝ := fun p ↦ p.1 ^ (2 * a) * p.2 ^ (2 * b)

theorem monomialLoss_nonneg (a b : ℕ) (p : ℝ × ℝ) : 0 ≤ monomialLoss a b p :=
  mul_nonneg (Even.pow_nonneg (even_two_mul a) _) (Even.pow_nonneg (even_two_mul b) _)

theorem measurable_monomialLoss (a b : ℕ) : Measurable (monomialLoss a b) := by
  unfold monomialLoss
  fun_prop

/-- `y^n ≤ q ↔ y ≤ q^{1/n}` for `y, q ≥ 0`, `n ≠ 0`. -/
theorem pow_le_iff_le_rpow_inv {y q : ℝ} (hy : 0 ≤ y) (hq : 0 ≤ q) {n : ℕ} (hn : n ≠ 0) :
    y ^ n ≤ q ↔ y ≤ q ^ ((n : ℝ)⁻¹) := by
  have h := Real.rpow_inv_natCast_pow hq hn
  constructor
  · intro hle
    have : y ^ n ≤ (q ^ ((n : ℝ)⁻¹)) ^ n := by rwa [h]
    exact (pow_le_pow_iff_left₀ hy (Real.rpow_nonneg hq _) hn).mp this
  · intro hle
    have := pow_le_pow_left₀ hy hle n
    rwa [h] at this

/-- The section over `x ∈ (0, 1]` of the monomial sublevel set on the square. -/
theorem section_sublevel_monomialLoss {a b : ℕ} (hb : 0 < b) {ε x : ℝ} (hε : 0 ≤ ε)
    (hx : x ∈ Ioc (0 : ℝ) 1) :
    Prod.mk x ⁻¹' ({p : ℝ × ℝ | monomialLoss a b p ≤ ε} ∩ unitSquare) =
      Icc 0 (min 1 ((ε / x ^ (2 * a)) ^ (((2 * b : ℕ) : ℝ)⁻¹))) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hxa : 0 < x ^ (2 * a) := pow_pos hx0 _
  have hn : 2 * b ≠ 0 := by omega
  ext y
  simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, unitSquare, mem_prod, mem_Icc,
    le_min_iff, monomialLoss]
  constructor
  · rintro ⟨hle, ⟨-, -⟩, hy0, hy1⟩
    refine ⟨hy0, hy1, ?_⟩
    rw [← pow_le_iff_le_rpow_inv hy0 (div_nonneg hε hxa.le) hn, le_div_iff₀ hxa]
    linarith
  · rintro ⟨hy0, hy1, hle⟩
    refine ⟨?_, ⟨hx0.le, hx1⟩, hy0, hy1⟩
    rw [← pow_le_iff_le_rpow_inv hy0 (div_nonneg hε hxa.le) hn, le_div_iff₀ hxa] at hle
    linarith

/-- **Sublevel mass of the monomial** as a one-dimensional integral. -/
theorem sublevelMass_monomialLoss_eq {a b : ℕ} (hb : 0 < b) {ε : ℝ} (hε : 0 ≤ ε) :
    sublevelMass (volume.restrict unitSquare) (monomialLoss a b) ε =
      ∫ x in Ioc (0 : ℝ) 1, min 1 ((ε / x ^ (2 * a)) ^ (((2 * b : ℕ) : ℝ)⁻¹)) := by
  set T : Set (ℝ × ℝ) := {p | monomialLoss a b p ≤ ε} with hT_def
  have hTm : MeasurableSet T := measurableSet_le (measurable_monomialLoss a b) measurable_const
  unfold sublevelMass
  rw [measureReal_def, Measure.restrict_apply hTm, Measure.volume_eq_prod ℝ ℝ,
    Measure.prod_apply (hTm.inter measurableSet_unitSquare)]
  set s : ℝ → ℝ := fun x ↦ min 1 ((ε / x ^ (2 * a)) ^ (((2 * b : ℕ) : ℝ)⁻¹)) with hs_def
  have hae : (fun x ↦ volume (Prod.mk x ⁻¹' (T ∩ unitSquare))) =ᵐ[volume]
      (Ioc (0 : ℝ) 1).indicator fun x ↦ ENNReal.ofReal (s x) := by
    have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with x hx0
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem hx, section_sublevel_monomialLoss hb hε hx, Real.volume_Icc, sub_zero]
    · rw [indicator_of_notMem hx]
      have hempty : Prod.mk x ⁻¹' (T ∩ unitSquare) = ∅ := by
        ext y
        simp only [mem_preimage, mem_inter_iff, unitSquare, mem_prod, mem_Icc,
          mem_empty_iff_false, iff_false]
        rintro ⟨-, ⟨hx0', hx1⟩, -⟩
        exact hx ⟨lt_of_le_of_ne hx0' (Ne.symm hx0), hx1⟩
      rw [hempty, measure_empty]
  rw [lintegral_congr_ae hae, lintegral_indicator measurableSet_Ioc]
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hsm : Measurable s := by
    simp only [hs_def]
    fun_prop
  have hs0 : ∀ x, 0 ≤ s x := fun x ↦ by
    simp only [hs_def]
    exact le_min zero_le_one
      (Real.rpow_nonneg (div_nonneg hε (Even.pow_nonneg (even_two_mul a) x)) _)
  have hint : IntegrableOn s (Ioc (0 : ℝ) 1) := by
    refine Integrable.of_bound hsm.aestronglyMeasurable 1 (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hs0 x)]
    exact min_le_left _ _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hs0),
    ENNReal.toReal_ofReal (integral_nonneg hs0)]

/-! ### Bounds on the one-dimensional integral -/

section Bounds

variable {a b : ℕ} {ε : ℝ}

/-- On `(0, ε^{1/(2a)}]` the integrand is `1`. -/
theorem one_le_monomial_section (ha : 0 < a) (hε : 0 < ε) {x : ℝ} (hx0 : 0 < x)
    (hx : x ≤ ε ^ (((2 * a : ℕ) : ℝ)⁻¹)) :
    1 ≤ (ε / x ^ (2 * a)) ^ (((2 * b : ℕ) : ℝ)⁻¹) := by
  have hxa : 0 < x ^ (2 * a) := pow_pos hx0 _
  have h1 : x ^ (2 * a) ≤ ε := (pow_le_iff_le_rpow_inv hx0.le hε.le (by omega)).mpr hx
  exact Real.one_le_rpow ((one_le_div hxa).mpr h1) (by positivity)

/-- On `(0, 1]` the integrand is at least `ε^{1/(2b)}`. -/
theorem rpow_le_monomial_section (hε : 0 < ε) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ε ^ (((2 * b : ℕ) : ℝ)⁻¹) ≤ (ε / x ^ (2 * a)) ^ (((2 * b : ℕ) : ℝ)⁻¹) := by
  have hxa : 0 < x ^ (2 * a) := pow_pos hx0 _
  refine Real.rpow_le_rpow hε.le ?_ (by positivity)
  rw [le_div_iff₀ hxa]
  exact mul_le_of_le_one_right hε.le (pow_le_one₀ hx0.le hx1)

/-- The integrand as `c x^{-a/b}`. -/
theorem monomial_section_eq (hb : 0 < b) (hε : 0 < ε) {x : ℝ} (hx0 : 0 < x) :
    (ε / x ^ (2 * a)) ^ (((2 * b : ℕ) : ℝ)⁻¹) =
      ε ^ (((2 * b : ℕ) : ℝ)⁻¹) * x ^ (-((a : ℝ) / b)) := by
  have hxa : 0 ≤ x ^ (2 * a) := (pow_pos hx0 _).le
  rw [Real.div_rpow hε.le hxa, ← Real.rpow_natCast x (2 * a), ← Real.rpow_mul hx0.le,
    div_eq_mul_inv, ← Real.rpow_neg hx0.le]
  congr 2
  have : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  push_cast
  field_simp

/-- The integrand is nonnegative and bounded by `1`. -/
theorem monomial_integrand_bounds (hε : 0 ≤ ε) (x : ℝ) :
    0 ≤ min 1 ((ε / x ^ (2 * a)) ^ (((2 * b : ℕ) : ℝ)⁻¹)) ∧
      min 1 ((ε / x ^ (2 * a)) ^ (((2 * b : ℕ) : ℝ)⁻¹)) ≤ 1 :=
  ⟨le_min zero_le_one
    (Real.rpow_nonneg (div_nonneg hε (Even.pow_nonneg (even_two_mul a) x)) _), min_le_left _ _⟩

theorem monomial_integrand_integrableOn (hε : 0 ≤ ε) {u v : ℝ} :
    IntegrableOn (fun x ↦ min 1 ((ε / x ^ (2 * a)) ^ (((2 * b : ℕ) : ℝ)⁻¹))) (Ioc u v) := by
  have : IsFiniteMeasure (volume.restrict (Ioc u v)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  refine Integrable.of_bound (Measurable.aestronglyMeasurable (by fun_prop)) 1
    (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (monomial_integrand_bounds hε x).1]
  exact (monomial_integrand_bounds hε x).2

/-- **Lower bound I**: the integral is at least `ε^{1/(2a)}`. -/
theorem monomial_integral_ge_left (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε ^ (((2 * a : ℕ) : ℝ)⁻¹) ≤
      ∫ x in Ioc (0 : ℝ) 1, min 1 ((ε / x ^ (2 * a)) ^ (((2 * b : ℕ) : ℝ)⁻¹)) := by
  set x₀ : ℝ := ε ^ (((2 * a : ℕ) : ℝ)⁻¹) with hx₀_def
  have hx₀0 : 0 < x₀ := Real.rpow_pos_of_pos hε _
  have hx₀1 : x₀ ≤ 1 := Real.rpow_le_one hε.le hε1 (by positivity)
  have hmono := setIntegral_mono_set (μ := volume) (monomial_integrand_integrableOn (a := a)
    (b := b) hε.le (u := 0) (v := 1))
    (Eventually.of_forall fun x ↦ (monomial_integrand_bounds hε.le x).1)
    (Ioc_subset_Ioc_right hx₀1).eventuallyLE
  refine le_trans ?_ hmono
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) x₀)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hconst := setIntegral_mono_on (integrable_const (1 : ℝ))
    (monomial_integrand_integrableOn hε.le) measurableSet_Ioc fun x hx ↦
      le_min le_rfl (one_le_monomial_section (b := b) ha hε hx.1 hx.2)
  rw [setIntegral_const, Real.volume_real_Ioc_of_le hx₀0.le, sub_zero, smul_eq_mul,
    mul_one] at hconst
  exact hconst

/-- **Lower bound II**: the integral is at least `ε^{1/(2b)} (1 - ε^{1/(2a)})`. -/
theorem monomial_integral_ge_right (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε ^ (((2 * b : ℕ) : ℝ)⁻¹) * (1 - ε ^ (((2 * a : ℕ) : ℝ)⁻¹)) ≤
      ∫ x in Ioc (0 : ℝ) 1, min 1 ((ε / x ^ (2 * a)) ^ (((2 * b : ℕ) : ℝ)⁻¹)) := by
  set x₀ : ℝ := ε ^ (((2 * a : ℕ) : ℝ)⁻¹) with hx₀_def
  set c : ℝ := ε ^ (((2 * b : ℕ) : ℝ)⁻¹) with hc_def
  have hx₀0 : 0 < x₀ := Real.rpow_pos_of_pos hε _
  have hx₀1 : x₀ ≤ 1 := Real.rpow_le_one hε.le hε1 (by positivity)
  have hc1 : c ≤ 1 := Real.rpow_le_one hε.le hε1 (by positivity)
  have hmono := setIntegral_mono_set (μ := volume) (monomial_integrand_integrableOn (a := a)
    (b := b) hε.le (u := 0) (v := 1))
    (Eventually.of_forall fun x ↦ (monomial_integrand_bounds hε.le x).1)
    (Ioc_subset_Ioc_left hx₀0.le).eventuallyLE
  refine le_trans ?_ hmono
  have : IsFiniteMeasure (volume.restrict (Ioc x₀ 1)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hconst := setIntegral_mono_on (integrable_const c)
    (monomial_integrand_integrableOn hε.le) measurableSet_Ioc fun x hx ↦
      le_min hc1 (rpow_le_monomial_section (a := a) hε (hx₀0.trans hx.1) hx.2)
  rw [setIntegral_const, Real.volume_real_Ioc_of_le hx₀1, smul_eq_mul] at hconst
  linarith

/-- **Upper bound**: the integral is at most `x₀ + c ∫_{x₀}^1 x^{-a/b} dx`. -/
theorem monomial_integral_le (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x in Ioc (0 : ℝ) 1, min 1 ((ε / x ^ (2 * a)) ^ (((2 * b : ℕ) : ℝ)⁻¹))) ≤
      ε ^ (((2 * a : ℕ) : ℝ)⁻¹) + ε ^ (((2 * b : ℕ) : ℝ)⁻¹) *
        ∫ x in ε ^ (((2 * a : ℕ) : ℝ)⁻¹)..1, x ^ (-((a : ℝ) / b)) := by
  set x₀ : ℝ := ε ^ (((2 * a : ℕ) : ℝ)⁻¹) with hx₀_def
  set c : ℝ := ε ^ (((2 * b : ℕ) : ℝ)⁻¹) with hc_def
  have hx₀0 : 0 < x₀ := Real.rpow_pos_of_pos hε _
  have hx₀1 : x₀ ≤ 1 := Real.rpow_le_one hε.le hε1 (by positivity)
  set f : ℝ → ℝ := fun x ↦ min 1 ((ε / x ^ (2 * a)) ^ (((2 * b : ℕ) : ℝ)⁻¹)) with hf_def
  have hsplit : ∫ x in Ioc (0 : ℝ) 1, f x =
      (∫ x in Ioc (0 : ℝ) x₀, f x) + ∫ x in Ioc x₀ 1, f x := by
    have hdisj : Disjoint (Ioc (0 : ℝ) x₀) (Ioc x₀ 1) :=
      Set.disjoint_left.mpr fun x hx hx' ↦ (not_lt.mpr hx.2) hx'.1
    rw [← setIntegral_union hdisj measurableSet_Ioc
      (monomial_integrand_integrableOn hε.le) (monomial_integrand_integrableOn hε.le),
      Ioc_union_Ioc_eq_Ioc hx₀0.le hx₀1]
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) x₀)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  -- first piece: `f ≤ 1`
  have h1 : ∫ x in Ioc (0 : ℝ) x₀, f x ≤ x₀ := by
    have := setIntegral_mono_on
      (monomial_integrand_integrableOn (a := a) (b := b) hε.le (u := 0) (v := x₀))
      (integrable_const (1 : ℝ)) measurableSet_Ioc
      fun x _ ↦ (monomial_integrand_bounds (a := a) (b := b) hε.le x).2
    rwa [setIntegral_const, Real.volume_real_Ioc_of_le hx₀0.le, sub_zero, smul_eq_mul,
      mul_one] at this
  -- second piece: `f ≤ c x^{-a/b}`
  have hcont : ContinuousOn (fun x : ℝ ↦ x ^ (-((a : ℝ) / b))) (Icc x₀ 1) := by
    refine ContinuousOn.rpow_const continuousOn_id fun x hx ↦ Or.inl ?_
    exact (hx₀0.trans_le hx.1).ne'
  have hint2 : IntegrableOn (fun x : ℝ ↦ c * x ^ (-((a : ℝ) / b))) (Ioc x₀ 1) :=
    ((hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self).const_mul c
  have h2 : ∫ x in Ioc x₀ 1, f x ≤ c * ∫ x in x₀..1, x ^ (-((a : ℝ) / b)) := by
    rw [intervalIntegral.integral_of_le hx₀1, ← integral_const_mul]
    refine setIntegral_mono_on (monomial_integrand_integrableOn hε.le) hint2 measurableSet_Ioc
      fun x hx ↦ ?_
    have hx0 : 0 < x := hx₀0.trans hx.1
    simp only [hf_def]
    rw [← monomial_section_eq hb hε hx0]
    exact min_le_right _ _
  simp only [hf_def] at hsplit h1 h2 ⊢
  rw [hsplit]
  linarith

end Bounds

/-! ### The transfer theorems -/

/-- **Off-diagonal monomials**: for `a ≠ b`,
`∫_{[0,1]²} e^{-t x^{2a} y^{2b}} = Θ(t^{-1/(2 max(a,b))})`. -/
theorem boltzmannMass_monomialLoss_transfer {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ t : ℝ in atTop,
      C₁ * t ^ (-(((2 * max a b : ℕ) : ℝ)⁻¹)) ≤
          boltzmannMass (volume.restrict unitSquare) (monomialLoss a b) t ∧
      boltzmannMass (volume.restrict unitSquare) (monomialLoss a b) t ≤
          C₂ * t ^ (-(((2 * max a b : ℕ) : ℝ)⁻¹)) := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  set r : ℝ := (a : ℝ) / b with hr_def
  have hr0 : 0 < r := by positivity
  -- the threshold `ε₀ = (1/2)^{2a}` keeps `x₀ ≤ 1/2`
  set ε₀ : ℝ := (1 / 2 : ℝ) ^ (2 * a) with hε₀_def
  have hε₀ : 0 < ε₀ := by positivity
  have hε₀1 : ε₀ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hx₀half : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ε ^ (((2 * a : ℕ) : ℝ)⁻¹) ≤ 1 / 2 := by
    intro ε hε hεle
    calc ε ^ (((2 * a : ℕ) : ℝ)⁻¹) ≤ ε₀ ^ (((2 * a : ℕ) : ℝ)⁻¹) :=
          Real.rpow_le_rpow hε.le hεle (by positivity)
      _ = 1 / 2 := Real.pow_rpow_inv_natCast (by norm_num) (by omega)
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · -- `a < b`: exponent `1/(2b)`, `r < 1`
    have hmax : max a b = b := max_eq_right hlt.le
    have hr1 : r < 1 := by
      rw [hr_def, div_lt_one (by positivity)]
      exact_mod_cast hlt
    rw [hmax]
    have hexp : ((2 * b : ℕ) : ℝ)⁻¹ ≤ ((2 * a : ℕ) : ℝ)⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact_mod_cast Nat.mul_le_mul_left 2 hlt.le
    have hc₂ : 0 < 1 + 1 / (1 - r) := by
      have : 0 < 1 - r := by linarith
      positivity
    refine boltzmannMass_power_transfer _ _ (measurable_monomialLoss a b) (monomialLoss_nonneg a b)
      (lam := ((2 * b : ℕ) : ℝ)⁻¹) (ε₀ := ε₀) (c₁ := 1 / 2) (c₂ := 1 + 1 / (1 - r))
      (by positivity) hε₀ (by norm_num) hc₂ (fun ε hε hεle ↦ ?_) (fun ε hε hεle ↦ ?_)
    · have hε1 : ε ≤ 1 := hεle.trans hε₀1
      rw [sublevelMass_monomialLoss_eq hb hε.le]
      have h := monomial_integral_ge_right (a := a) (b := b) ha hε hε1
      have hx := hx₀half ε hε hεle
      have hc0 : 0 ≤ ε ^ (((2 * b : ℕ) : ℝ)⁻¹) := Real.rpow_nonneg hε.le _
      nlinarith
    · have hε1 : ε ≤ 1 := hεle.trans hε₀1
      rw [sublevelMass_monomialLoss_eq hb hε.le]
      have h := monomial_integral_le (a := a) (b := b) ha hb hε hε1
      set x₀ : ℝ := ε ^ (((2 * a : ℕ) : ℝ)⁻¹) with hx₀_def
      set c : ℝ := ε ^ (((2 * b : ℕ) : ℝ)⁻¹) with hc_def
      have hx₀0 : 0 < x₀ := Real.rpow_pos_of_pos hε _
      have hx₀1 : x₀ ≤ 1 := Real.rpow_le_one hε.le hε1 (by positivity)
      have hx₀c : x₀ ≤ c := Real.rpow_le_rpow_of_exponent_ge hε hε1 hexp
      have hc0 : 0 ≤ c := Real.rpow_nonneg hε.le _
      have hI : ∫ x in x₀..1, x ^ (-r) = (1 - x₀ ^ (1 - r)) / (1 - r) := by
        rw [integral_rpow (Or.inr ⟨by linarith, ?_⟩), Real.one_rpow,
          show -r + 1 = 1 - r by ring]
        rw [Set.uIcc_of_le hx₀1]
        exact fun h0 ↦ (lt_irrefl _ (hx₀0.trans_le h0.1)).elim
      have hIle : ∫ x in x₀..1, x ^ (-r) ≤ 1 / (1 - r) := by
        rw [hI]
        have : 0 < 1 - r := by linarith
        exact div_le_div_of_nonneg_right (by linarith [Real.rpow_nonneg hx₀0.le (1 - r)]) this.le
      calc ∫ x in Ioc (0 : ℝ) 1, min 1 ((ε / x ^ (2 * a)) ^ (((2 * b : ℕ) : ℝ)⁻¹))
          ≤ x₀ + c * ∫ x in x₀..1, x ^ (-r) := h
        _ ≤ c + c * (1 / (1 - r)) := by gcongr
        _ = (1 + 1 / (1 - r)) * c := by ring
  · -- `b < a`: exponent `1/(2a)`, `r > 1`
    have hmax : max a b = a := max_eq_left hlt.le
    have hr1 : 1 < r := by
      rw [hr_def, one_lt_div (by positivity)]
      exact_mod_cast hlt
    rw [hmax]
    have hexp : ((2 * a : ℕ) : ℝ)⁻¹ ≤ ((2 * b : ℕ) : ℝ)⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact_mod_cast Nat.mul_le_mul_left 2 hlt.le
    have hc₂ : 0 < 1 + 1 / (r - 1) := by
      have : 0 < r - 1 := by linarith
      positivity
    refine boltzmannMass_power_transfer _ _ (measurable_monomialLoss a b) (monomialLoss_nonneg a b)
      (lam := ((2 * a : ℕ) : ℝ)⁻¹) (ε₀ := ε₀) (c₁ := 1) (c₂ := 1 + 1 / (r - 1))
      (by positivity) hε₀ one_pos hc₂ (fun ε hε hεle ↦ ?_) (fun ε hε hεle ↦ ?_)
    · have hε1 : ε ≤ 1 := hεle.trans hε₀1
      rw [sublevelMass_monomialLoss_eq hb hε.le, one_mul]
      exact monomial_integral_ge_left ha hε hε1
    · have hε1 : ε ≤ 1 := hεle.trans hε₀1
      rw [sublevelMass_monomialLoss_eq hb hε.le]
      have h := monomial_integral_le (a := a) (b := b) ha hb hε hε1
      set x₀ : ℝ := ε ^ (((2 * a : ℕ) : ℝ)⁻¹) with hx₀_def
      set c : ℝ := ε ^ (((2 * b : ℕ) : ℝ)⁻¹) with hc_def
      have hx₀0 : 0 < x₀ := Real.rpow_pos_of_pos hε _
      have hx₀1 : x₀ ≤ 1 := Real.rpow_le_one hε.le hε1 (by positivity)
      have hc0 : 0 ≤ c := Real.rpow_nonneg hε.le _
      have hr1' : 0 < r - 1 := by linarith
      have hI : ∫ x in x₀..1, x ^ (-r) = (x₀ ^ (1 - r) - 1) / (r - 1) := by
        rw [integral_rpow (Or.inr ⟨by linarith, ?_⟩), Real.one_rpow,
          show -r + 1 = 1 - r by ring, ← neg_div_neg_eq, neg_sub, neg_sub]
        rw [Set.uIcc_of_le hx₀1]
        exact fun h0 ↦ (lt_irrefl _ (hx₀0.trans_le h0.1)).elim
      -- `c x₀^{1-r} = x₀`
      have hkey : c * x₀ ^ (1 - r) = x₀ := by
        simp only [hc_def, hx₀_def]
        rw [← Real.rpow_mul hε.le, ← Real.rpow_add hε]
        congr 1
        rw [hr_def]
        push_cast
        field_simp
        ring
      have hIle : c * ∫ x in x₀..1, x ^ (-r) ≤ x₀ * (1 / (r - 1)) := by
        rw [hI, mul_div_assoc', div_le_iff₀ hr1', mul_sub, hkey]
        have : 0 ≤ c := hc0
        calc x₀ - c * 1 ≤ x₀ := by linarith
          _ = x₀ * (1 / (r - 1)) * (r - 1) := by field_simp
      calc ∫ x in Ioc (0 : ℝ) 1, min 1 ((ε / x ^ (2 * a)) ^ (((2 * b : ℕ) : ℝ)⁻¹))
          ≤ x₀ + c * ∫ x in x₀..1, x ^ (-r) := h
        _ ≤ x₀ + x₀ * (1 / (r - 1)) := by linarith
        _ = (1 + 1 / (r - 1)) * x₀ := by ring

/-- The diagonal monomial `(xy)^{2a}` is the square loss composed with a power. -/
theorem monomialLoss_diag (a : ℕ) (p : ℝ × ℝ) :
    monomialLoss a a p = ((p.1 * p.2) ^ 2) ^ a := by
  unfold monomialLoss
  rw [← mul_pow, ← pow_mul, mul_comm 2 a]

/-- **Diagonal monomials**: `∫_{[0,1]²} e^{-t (xy)^{2a}} = Θ(t^{-1/(2a)} log t)`. -/
theorem boltzmannMass_monomialLoss_diag_transfer {a : ℕ} (ha : 0 < a) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ t : ℝ in atTop,
      C₁ * t ^ (-(((2 * a : ℕ) : ℝ)⁻¹)) * Real.log t ≤
          boltzmannMass (volume.restrict unitSquare) (monomialLoss a a) t ∧
      boltzmannMass (volume.restrict unitSquare) (monomialLoss a a) t ≤
          C₂ * t ^ (-(((2 * a : ℕ) : ℝ)⁻¹)) * Real.log t := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  -- reparametrisation of the sublevel mass
  have hsub : ∀ ε : ℝ, 0 ≤ ε →
      sublevelMass (volume.restrict unitSquare) (monomialLoss a a) ε =
        sublevelMass (volume.restrict unitSquare) (fun p : ℝ × ℝ ↦ (p.1 * p.2) ^ 2)
          (ε ^ ((a : ℝ)⁻¹)) := by
    intro ε hε
    unfold sublevelMass
    congr 2
    ext p
    simp only [monomialLoss_diag]
    exact pow_le_iff_le_rpow_inv (sq_nonneg _) hε ha.ne'
  have hε₀ : (0 : ℝ) < Real.exp (-(2 * a)) := Real.exp_pos _
  have hε₀1 : Real.exp (-(2 * a)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hbounds : ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-(2 * a)) →
      1 / (2 * a) * ε ^ (((2 * a : ℕ) : ℝ)⁻¹) * (Real.log ε⁻¹) ^ 1 ≤
          sublevelMass (volume.restrict unitSquare) (monomialLoss a a) ε ∧
      sublevelMass (volume.restrict unitSquare) (monomialLoss a a) ε ≤
          1 / a * ε ^ (((2 * a : ℕ) : ℝ)⁻¹) * (Real.log ε⁻¹) ^ 1 := by
    intro ε hε hεle
    have hε1 : ε ≤ 1 := hεle.trans hε₀1.le
    have hu : 0 < ε ^ ((a : ℝ)⁻¹) := Real.rpow_pos_of_pos hε _
    have hu1 : ε ^ ((a : ℝ)⁻¹) ≤ 1 := Real.rpow_le_one hε.le hε1 (by positivity)
    rw [hsub ε hε.le, sublevelMass_sq_mul_sq hu hu1, Real.log_inv, pow_one,
      Real.sqrt_eq_rpow, ← Real.rpow_mul hε.le, Real.log_rpow hε]
    have hexp : (a : ℝ)⁻¹ * (1 / 2) = ((2 * a : ℕ) : ℝ)⁻¹ := by
      push_cast
      field_simp
    rw [hexp]
    set s : ℝ := ε ^ (((2 * a : ℕ) : ℝ)⁻¹) with hs_def
    set q : ℝ := ((2 * a : ℕ) : ℝ)⁻¹ with hq_def
    have hs : 0 ≤ s := Real.rpow_nonneg hε.le _
    have hq : 0 < q := by positivity
    have hq' : (1 : ℝ) / (2 * a) = q := by
      rw [hq_def]
      push_cast
      ring
    have hq2 : (1 : ℝ) / a = 2 * q := by
      rw [hq_def]
      push_cast
      field_simp
    have hL : 2 * (a : ℝ) ≤ -Real.log ε := by
      have := Real.log_le_log hε hεle
      rw [Real.log_exp] at this
      linarith
    have hL0 : 0 ≤ -Real.log ε := by linarith
    have hqL : 1 ≤ q * -Real.log ε := by
      calc (1 : ℝ) = q * (2 * a) := by
            rw [hq_def]
            push_cast
            field_simp
        _ ≤ q * -Real.log ε := mul_le_mul_of_nonneg_left hL hq.le
    constructor
    · rw [hq']
      nlinarith [mul_nonneg hs (mul_nonneg hq.le hL0)]
    · rw [hq2]
      nlinarith [mul_nonneg hs (sub_nonneg.mpr hqL)]
  obtain ⟨C₁, C₂, hC₁, hC₂, h⟩ := boltzmannMass_log_transfer (volume.restrict unitSquare)
    (monomialLoss a a) (measurable_monomialLoss a a) (monomialLoss_nonneg a a) 1
    (by positivity) hε₀ hε₀1 (by positivity) (by positivity)
    (fun ε hε hεle ↦ (hbounds ε hε hεle).1) (fun ε hε hεle ↦ (hbounds ε hε hεle).2)
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  filter_upwards [h] with t ht
  simpa [pow_one] using ht

end Laplace
