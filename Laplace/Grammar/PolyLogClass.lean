/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.GeneralTower

/-!
# The polylog-bounded class and its closure under power steps (grammar §4.2)

To analyse the general tower of unit 55 for exponent vectors sorted in non-increasing order, the
levels stay in the class of functions `G` that are measurable, nonnegative, `≤ C₀ y^δ` on `(0,1]`,
and `≤ C₁ (1 + log y)^j` on `[1, ∞)` (`PolyLogBounded G C₀ δ C₁ j`). This unit proves:

* the base level `F_{q-1}` is in the class with `j = 0`;
* a logarithmic step (`powStep (-1)`) raises `j` by one;
* a convergent step (`powStep t`, `t < -1`) lands in the class with `j = 0` (bounded);

together with the integrability, monotonicity and measurability facts needed for both. The key tool
for absorbing logarithms is `(1 + log x)^j ≤ (1 + 1/ε)^j x^{jε}` for `x ≥ 1`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter

namespace Laplace.Grammar

/-- Polylog-bounded functions: `0 ≤ G ≤ C₀ y^δ` on `(0,1]` and `G ≤ C₁ (1 + log y)^j` on `[1,∞)`. -/
structure PolyLogBounded (G : ℝ → ℝ) (C₀ δ C₁ : ℝ) (j : ℕ) : Prop where
  measurable : Measurable G
  nonneg : ∀ y, 0 ≤ G y
  δ_pos : 0 < δ
  le_pow : ∀ y, 0 < y → y ≤ 1 → G y ≤ C₀ * y ^ δ
  le_log : ∀ y, 1 ≤ y → G y ≤ C₁ * (1 + Real.log y) ^ j

/-- `(1 + log x)^j ≤ (1 + 1/ε)^j x^{jε}` for `x ≥ 1`, `ε > 0`. -/
theorem one_add_log_pow_le_rpow (j : ℕ) (ε x : ℝ) (hε : 0 < ε) (hx : 1 ≤ x) :
    (1 + Real.log x) ^ j ≤ (1 + 1 / ε) ^ j * x ^ ((j : ℝ) * ε) := by
  have hx0 : (0 : ℝ) < x := one_pos.trans_le hx
  have h1 : (1 : ℝ) ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have hlog : 1 + Real.log x ≤ (1 + 1 / ε) * x ^ ε := by
    have := Real.log_le_rpow_div hx0.le hε
    calc 1 + Real.log x ≤ x ^ ε + x ^ ε / ε := by linarith
      _ = (1 + 1 / ε) * x ^ ε := by ring
  have hnn : 0 ≤ 1 + Real.log x := by linarith [Real.log_nonneg hx]
  calc (1 + Real.log x) ^ j ≤ ((1 + 1 / ε) * x ^ ε) ^ j := pow_le_pow_left₀ hnn hlog j
    _ = (1 + 1 / ε) ^ j * x ^ ((j : ℝ) * ε) := by
        rw [mul_pow, ← Real.rpow_natCast (x ^ ε) j, ← Real.rpow_mul hx0.le, mul_comm ε]

/-- On `[1, L]`, `x^t ≤ L^t + 1`. -/
theorem rpow_le_rpow_add_one (t x L : ℝ) (hx : 1 ≤ x) (hxL : x ≤ L) : x ^ t ≤ L ^ t + 1 := by
  have hx0 : (0 : ℝ) < x := one_pos.trans_le hx
  have hL0 : (0 : ℝ) ≤ L := hx0.le.trans hxL
  rcases le_or_gt 0 t with ht | ht
  · have := Real.rpow_le_rpow hx0.le hxL ht
    linarith
  · have := Real.rpow_le_one_of_one_le_of_nonpos hx ht.le
    have : 0 ≤ L ^ t := Real.rpow_nonneg hL0 t
    linarith

/-- `(1 + log x)^j / x` is integrable on `(1, L]`. -/
theorem integrableOn_one_add_log_pow_div_Ioc (j : ℕ) (L : ℝ) :
    IntegrableOn (fun x : ℝ => (1 + Real.log x) ^ j / x) (Ioc 1 L) := by
  have : ContinuousOn (fun x : ℝ => (1 + Real.log x) ^ j / x) (Icc 1 L) :=
    ((continuousOn_const.add (Real.continuousOn_log.mono fun x hx =>
      (lt_of_lt_of_le one_pos hx.1).ne')).pow j).div continuousOn_id
      fun x hx => (lt_of_lt_of_le one_pos hx.1).ne'
  exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self


namespace PolyLogBounded

variable {G : ℝ → ℝ} {C₀ δ C₁ : ℝ} {j : ℕ}

theorem C₀_nonneg (hG : PolyLogBounded G C₀ δ C₁ j) : 0 ≤ C₀ := by
  have := hG.le_pow 1 one_pos le_rfl
  rw [Real.one_rpow, mul_one] at this
  exact (hG.nonneg 1).trans this

theorem C₁_nonneg (hG : PolyLogBounded G C₀ δ C₁ j) : 0 ≤ C₁ := by
  have := hG.le_log 1 le_rfl
  rw [Real.log_one, add_zero, one_pow, mul_one] at this
  exact (hG.nonneg 1).trans this

/-- `x^t G(x)` is integrable on `(0, L]` whenever `t + δ > -1`. -/
theorem integrableOn_rpow_mul (hG : PolyLogBounded G C₀ δ C₁ j) (t : ℝ) (ht : -1 < t + δ) (L : ℝ) :
    IntegrableOn (fun x => x ^ t * G x) (Ioc 0 L) := by
  have hmeas : Measurable (fun x => x ^ t * G x) := (measurable_id.pow_const t).mul hG.measurable
  have h1 : IntegrableOn (fun x => x ^ t * G x) (Ioc 0 1) := by
    refine Integrable.mono' (g := fun x => C₀ * x ^ (t + δ))
      ((intervalIntegral.intervalIntegrable_rpow' ht (a := 0) (b := 1)).1.const_mul _)
      hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (hG.nonneg x)),
      Real.rpow_add hx0]
    calc x ^ t * G x ≤ x ^ t * (C₀ * x ^ δ) :=
          mul_le_mul_of_nonneg_left (hG.le_pow x hx0 hx.2) (Real.rpow_nonneg hx0.le _)
      _ = C₀ * (x ^ t * x ^ δ) := by ring
  have h2 : IntegrableOn (fun x => x ^ t * G x) (Ioc 1 L) := by
    refine Integrable.mono' (g := fun _ => (L ^ t + 1) * (C₁ * (1 + Real.log L) ^ j))
      (integrableOn_const measure_Ioc_lt_top.ne) hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx1 : (1 : ℝ) ≤ x := hx.1.le
    have hx0 : (0 : ℝ) < x := one_pos.trans_le hx1
    have hlogx : 0 ≤ 1 + Real.log x := by linarith [Real.log_nonneg hx1]
    have hlog : (1 + Real.log x) ^ j ≤ (1 + Real.log L) ^ j :=
      pow_le_pow_left₀ hlogx (by linarith [Real.log_le_log hx0 hx.2]) j
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (hG.nonneg x))]
    calc x ^ t * G x ≤ (L ^ t + 1) * (C₁ * (1 + Real.log x) ^ j) :=
          mul_le_mul (rpow_le_rpow_add_one t x L hx1 hx.2) (hG.le_log x hx1) (hG.nonneg x)
            (by linarith [Real.rpow_nonneg (hx0.le.trans hx.2) t])
      _ ≤ (L ^ t + 1) * (C₁ * (1 + Real.log L) ^ j) := by
          gcongr
          · linarith [Real.rpow_nonneg (hx0.le.trans hx.2) t]
          · exact hG.C₁_nonneg
  rcases le_or_gt L 1 with hL | hL
  · exact h1.mono_set (Ioc_subset_Ioc_right hL)
  · have := h1.union h2
    rwa [Ioc_union_Ioc_eq_Ioc zero_le_one hL.le] at this

theorem powStep_nonneg (hG : PolyLogBounded G C₀ δ C₁ j) (t y : ℝ) : 0 ≤ powStep t G y :=
  setIntegral_nonneg measurableSet_Ioc fun x hx =>
    mul_nonneg (Real.rpow_nonneg hx.1.le _) (hG.nonneg x)

theorem powStep_mono (hG : PolyLogBounded G C₀ δ C₁ j) (t : ℝ) (ht : -1 < t + δ) :
    Monotone (powStep t G) := by
  intro x y hxy
  refine setIntegral_mono_set (hG.integrableOn_rpow_mul t ht y) ?_
    (Filter.Eventually.of_forall fun z hz => Ioc_subset_Ioc_right hxy hz)
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
  exact Filter.Eventually.of_forall fun z hz =>
    mul_nonneg (Real.rpow_nonneg hz.1.le _) (hG.nonneg z)

theorem powStep_measurable (hG : PolyLogBounded G C₀ δ C₁ j) (t : ℝ) (ht : -1 < t + δ) :
    Measurable (powStep t G) :=
  (hG.powStep_mono t ht).measurable

/-- Near `0`: `powStep t G (y) ≤ C₀/(t+δ+1) · y^{t+δ+1}` for `0 < y ≤ 1`. -/
theorem powStep_le_pow (hG : PolyLogBounded G C₀ δ C₁ j) (t : ℝ) (ht : -1 < t + δ) (y : ℝ)
    (hy0 : 0 < y) (hy1 : y ≤ 1) :
    powStep t G y ≤ C₀ / (t + δ + 1) * y ^ (t + δ + 1) := by
  have hpos : 0 < t + δ + 1 := by linarith
  calc powStep t G y ≤ ∫ x in Ioc (0 : ℝ) y, C₀ * x ^ (t + δ) := by
        refine setIntegral_mono_on (hG.integrableOn_rpow_mul t ht y)
          (((intervalIntegral.intervalIntegrable_rpow' ht (a := 0) (b := y)).1).const_mul _)
          measurableSet_Ioc fun x hx => ?_
        have hx0 : 0 < x := hx.1
        rw [Real.rpow_add hx0]
        calc x ^ t * G x ≤ x ^ t * (C₀ * x ^ δ) :=
              mul_le_mul_of_nonneg_left (hG.le_pow x hx0 (hx.2.trans hy1))
                (Real.rpow_nonneg hx0.le _)
          _ = C₀ * (x ^ t * x ^ δ) := by ring
    _ = C₀ / (t + δ + 1) * y ^ (t + δ + 1) := by
        rw [MeasureTheory.integral_const_mul, show t + δ = (t + δ + 1) - 1 by ring,
          integral_Ioc_rpow_sub_one _ y hpos hy0.le]
        ring

/-- The logarithmic step raises the log-degree by one. -/
theorem powStep_neg_one (hG : PolyLogBounded G C₀ δ C₁ j) :
    PolyLogBounded (powStep (-1) G) (C₀ / δ) δ (C₀ / δ + C₁ / ((j : ℝ) + 1)) (j + 1) where
  measurable := hG.powStep_measurable (-1) (by linarith [hG.δ_pos])
  nonneg := hG.powStep_nonneg (-1)
  δ_pos := hG.δ_pos
  le_pow := by
    intro y hy0 hy1
    have := hG.powStep_le_pow (-1) (by linarith [hG.δ_pos]) y hy0 hy1
    rwa [show -1 + δ + 1 = δ by ring] at this
  le_log := by
    intro y hy
    have hδ := hG.δ_pos
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hint := hG.integrableOn_rpow_mul (-1) (by linarith) y
    have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioc 1 y) :=
      Set.disjoint_left.2 fun x h1 h2 => (not_lt.2 h1.2) h2.1
    have hsplit := setIntegral_union hdisj measurableSet_Ioc
      (hint.mono_set (Ioc_subset_Ioc_right hy)) (hint.mono_set (Ioc_subset_Ioc_left zero_le_one))
      (f := fun x => x ^ (-1 : ℝ) * G x)
    rw [Ioc_union_Ioc_eq_Ioc zero_le_one hy] at hsplit
    have h1 : (∫ x in Ioc (0 : ℝ) 1, x ^ (-1 : ℝ) * G x) ≤ C₀ / δ := by
      have := hG.powStep_le_pow (-1) (by linarith) 1 one_pos le_rfl
      rwa [Real.one_rpow, mul_one, show -1 + δ + 1 = δ by ring, powStep] at this
    have h2 : (∫ x in Ioc (1 : ℝ) y, x ^ (-1 : ℝ) * G x)
        ≤ C₁ / ((j : ℝ) + 1) * (1 + Real.log y) ^ (j + 1) := by
      calc (∫ x in Ioc (1 : ℝ) y, x ^ (-1 : ℝ) * G x)
          ≤ ∫ x in Ioc (1 : ℝ) y, C₁ * ((1 + Real.log x) ^ j / x) := by
            refine setIntegral_mono_on (hint.mono_set (Ioc_subset_Ioc_left zero_le_one))
              ((integrableOn_one_add_log_pow_div_Ioc j y).const_mul _) measurableSet_Ioc
              fun x hx => ?_
            have hx0 : (0 : ℝ) < x := one_pos.trans hx.1
            rw [Real.rpow_neg hx0.le, Real.rpow_one]
            calc x⁻¹ * G x ≤ x⁻¹ * (C₁ * (1 + Real.log x) ^ j) :=
                  mul_le_mul_of_nonneg_left (hG.le_log x hx.1.le) (inv_nonneg.2 hx0.le)
              _ = C₁ * ((1 + Real.log x) ^ j / x) := by ring
        _ = C₁ * (((1 + Real.log y) ^ (j + 1) - 1) / ((j : ℝ) + 1)) := by
            rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le hy,
              integral_one_add_log_pow_div j y hy]
        _ ≤ C₁ / ((j : ℝ) + 1) * (1 + Real.log y) ^ (j + 1) := by
            have hC₁ := hG.C₁_nonneg
            rw [show C₁ / ((j : ℝ) + 1) * (1 + Real.log y) ^ (j + 1)
              = C₁ * ((1 + Real.log y) ^ (j + 1) / ((j : ℝ) + 1)) by ring]
            exact mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right (by linarith) hj.le) hC₁
    have hge : (1 : ℝ) ≤ (1 + Real.log y) ^ (j + 1) :=
      one_le_pow₀ (by linarith [Real.log_nonneg hy])
    have hC₀ : 0 ≤ C₀ / δ := div_nonneg hG.C₀_nonneg hδ.le
    calc powStep (-1) G y = (∫ x in Ioc (0 : ℝ) 1, x ^ (-1 : ℝ) * G x)
          + ∫ x in Ioc (1 : ℝ) y, x ^ (-1 : ℝ) * G x := by rw [powStep, hsplit]
      _ ≤ C₀ / δ * (1 + Real.log y) ^ (j + 1)
          + C₁ / ((j : ℝ) + 1) * (1 + Real.log y) ^ (j + 1) := by
          gcongr
          calc (∫ x in Ioc (0 : ℝ) 1, x ^ (-1 : ℝ) * G x) ≤ C₀ / δ := h1
            _ = C₀ / δ * 1 := (mul_one _).symm
            _ ≤ C₀ / δ * (1 + Real.log y) ^ (j + 1) := by gcongr
      _ = (C₀ / δ + C₁ / ((j : ℝ) + 1)) * (1 + Real.log y) ^ (j + 1) := by ring

end PolyLogBounded

namespace PolyLogBounded

variable {G : ℝ → ℝ} {C₀ δ C₁ : ℝ} {j : ℕ}

/-- The absorption exponent `ε = (−t−1)/(2(j+1))` used to trade logarithms for powers. -/
noncomputable def absorbEps (t : ℝ) (j : ℕ) : ℝ := (-t - 1) / (2 * ((j : ℝ) + 1))

theorem absorbEps_pos (t : ℝ) (j : ℕ) (ht : t < -1) : 0 < absorbEps t j := by
  unfold absorbEps
  have : 0 < -t - 1 := by linarith
  positivity

/-- For `t < -1` and `x ≥ 1`: `x^t G(x) ≤ C₁ (1 + 1/ε)^j x^{(t−1)/2}`. -/
theorem rpow_mul_le_of_lt (hG : PolyLogBounded G C₀ δ C₁ j) (t : ℝ) (ht : t < -1) (x : ℝ)
    (hx : 1 ≤ x) :
    x ^ t * G x ≤ C₁ * (1 + 1 / absorbEps t j) ^ j * x ^ ((t - 1) / 2) := by
  have hx0 : (0 : ℝ) < x := one_pos.trans_le hx
  have hε := absorbEps_pos t j ht
  have hlog := one_add_log_pow_le_rpow j (absorbEps t j) x hε hx
  have hexp : t + (j : ℝ) * absorbEps t j ≤ (t - 1) / 2 := by
    unfold absorbEps
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have h0 : 0 < -t - 1 := by linarith
    have : (j : ℝ) * ((-t - 1) / (2 * ((j : ℝ) + 1))) ≤ (-t - 1) / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
      nlinarith [mul_nonneg hj h0.le]
    linarith
  calc x ^ t * G x ≤ x ^ t * (C₁ * (1 + Real.log x) ^ j) :=
        mul_le_mul_of_nonneg_left (hG.le_log x hx) (Real.rpow_nonneg hx0.le _)
    _ ≤ x ^ t * (C₁ * ((1 + 1 / absorbEps t j) ^ j * x ^ ((j : ℝ) * absorbEps t j))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog hG.C₁_nonneg)
          (Real.rpow_nonneg hx0.le _)
    _ = C₁ * (1 + 1 / absorbEps t j) ^ j * x ^ (t + (j : ℝ) * absorbEps t j) := by
        rw [Real.rpow_add hx0]; ring
    _ ≤ C₁ * (1 + 1 / absorbEps t j) ^ j * x ^ ((t - 1) / 2) := by
        have hε' : 0 ≤ 1 + 1 / absorbEps t j := by have := hε; positivity
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hexp)
          (mul_nonneg hG.C₁_nonneg (pow_nonneg hε' j))

/-- For `t < -1` the integrand `x^t G(x)` is integrable on all of `(0, ∞)`. -/
theorem integrableOn_rpow_mul_Ioi (hG : PolyLogBounded G C₀ δ C₁ j) (t : ℝ) (ht : t < -1)
    (ht' : -1 < t + δ) :
    IntegrableOn (fun x => x ^ t * G x) (Ioi 0) := by
  have hmeas : Measurable (fun x => x ^ t * G x) := (measurable_id.pow_const t).mul hG.measurable
  have h1 := hG.integrableOn_rpow_mul t ht' 1
  have h2 : IntegrableOn (fun x => x ^ t * G x) (Ioi 1) := by
    refine Integrable.mono' (g := fun x => C₁ * (1 + 1 / absorbEps t j) ^ j * x ^ ((t - 1) / 2))
      ((integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _)
      hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hx1) _)
      (hG.nonneg x))]
    exact hG.rpow_mul_le_of_lt t ht x hx1
  have := h1.union h2
  rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at this

/-- The limit of a convergent power step. -/
noncomputable def powLimit (t : ℝ) (G : ℝ → ℝ) : ℝ := ∫ x in Ioi (0 : ℝ), x ^ t * G x

theorem powLimit_sub_powStep (hG : PolyLogBounded G C₀ δ C₁ j) (t : ℝ) (ht : t < -1)
    (ht' : -1 < t + δ) (y : ℝ) (hy : 0 ≤ y) :
    powLimit t G - powStep t G y = ∫ x in Ioi y, x ^ t * G x := by
  have hint := hG.integrableOn_rpow_mul_Ioi t ht ht'
  have hsplit := setIntegral_union (Ioc_disjoint_Ioi (le_refl y)) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hy))
  rw [Ioc_union_Ioi_eq_Ioi hy] at hsplit
  rw [powLimit, powStep, hsplit]
  ring

theorem powStep_le_powLimit (hG : PolyLogBounded G C₀ δ C₁ j) (t : ℝ) (ht : t < -1)
    (ht' : -1 < t + δ) (y : ℝ) :
    powStep t G y ≤ powLimit t G := by
  rcases le_or_gt 0 y with hy | hy
  · have h := hG.powLimit_sub_powStep t ht ht' y hy
    have h0 : 0 ≤ ∫ x in Ioi y, x ^ t * G x := setIntegral_nonneg measurableSet_Ioi fun x hx =>
      mul_nonneg (Real.rpow_nonneg (hy.trans_lt hx).le _) (hG.nonneg x)
    linarith
  · rw [powStep, Ioc_eq_empty (not_lt.2 hy.le), Measure.restrict_empty, integral_zero_measure]
    exact setIntegral_nonneg measurableSet_Ioi fun x hx =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (hG.nonneg x)

/-- Tail of a convergent step: `powLimit − powStep t G (y) ≤ M y^{-(−t−1)/2}` for `y ≥ 1`. -/
theorem powLimit_sub_powStep_le (hG : PolyLogBounded G C₀ δ C₁ j) (t : ℝ) (ht : t < -1)
    (ht' : -1 < t + δ) (y : ℝ) (hy : 1 ≤ y) :
    powLimit t G - powStep t G y
      ≤ C₁ * (1 + 1 / absorbEps t j) ^ j * (2 / (-t - 1)) * y ^ (-((-t - 1) / 2)) := by
  have hy0 : (0 : ℝ) < y := one_pos.trans_le hy
  have hint := hG.integrableOn_rpow_mul_Ioi t ht ht'
  rw [hG.powLimit_sub_powStep t ht ht' y hy0.le]
  have hval : (∫ x in Ioi y, C₁ * (1 + 1 / absorbEps t j) ^ j * x ^ ((t - 1) / 2))
      = C₁ * (1 + 1 / absorbEps t j) ^ j * (2 / (-t - 1)) * y ^ (-((-t - 1) / 2)) := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hy0,
      show (t - 1) / 2 + 1 = -((-t - 1) / 2) by ring]
    have : -t - 1 ≠ 0 := by linarith
    field_simp
  rw [← hval]
  refine setIntegral_mono_on (hint.mono_set (Ioi_subset_Ioi hy0.le))
    ((integrableOn_Ioi_rpow_of_lt (by linarith) hy0).const_mul _) measurableSet_Ioi fun x hx => ?_
  exact hG.rpow_mul_le_of_lt t ht x (hy.trans (le_of_lt hx))

/-- A convergent step lands in the class with `j = 0` (bounded by its limit). -/
theorem powStep_of_lt (hG : PolyLogBounded G C₀ δ C₁ j) (t : ℝ) (ht : t < -1) (ht' : -1 < t + δ) :
    PolyLogBounded (powStep t G) (C₀ / (t + δ + 1)) (t + δ + 1) (powLimit t G) 0 where
  measurable := hG.powStep_measurable t ht'
  nonneg := hG.powStep_nonneg t
  δ_pos := by linarith
  le_pow := fun y hy0 hy1 => hG.powStep_le_pow t ht' y hy0 hy1
  le_log := fun y _ => by
    rw [pow_zero, mul_one]
    exact hG.powStep_le_powLimit t ht ht' y

theorem powStep_pos (hG : PolyLogBounded G C₀ δ C₁ j) (hpos : ∀ x, 0 < x → 0 < G x) (t : ℝ)
    (ht' : -1 < t + δ) (y : ℝ) (hy : 0 < y) : 0 < powStep t G y := by
  rw [powStep, setIntegral_pos_iff_support_of_nonneg_ae ?_ (hG.integrableOn_rpow_mul t ht' y)]
  · have hsub : Ioc (0 : ℝ) y ⊆ Function.support (fun x : ℝ => x ^ t * G x) ∩ Ioc 0 y := by
      intro x hx
      refine ⟨?_, hx⟩
      rw [Function.mem_support]
      exact (mul_pos (Real.rpow_pos_of_pos hx.1 t) (hpos x hx.1)).ne'
    calc (0 : ENNReal) < volume (Ioc (0 : ℝ) y) := by
          rw [Real.volume_Ioc, sub_zero]; exact ENNReal.ofReal_pos.2 hy
      _ ≤ _ := measure_mono hsub
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun x hx =>
      mul_nonneg (Real.rpow_nonneg hx.1.le _) (hG.nonneg x)

theorem powLimit_pos (hG : PolyLogBounded G C₀ δ C₁ j) (hpos : ∀ x, 0 < x → 0 < G x) (t : ℝ)
    (ht : t < -1) (ht' : -1 < t + δ) : 0 < powLimit t G := by
  have h := hG.powStep_pos hpos t ht' 1 one_pos
  exact h.trans_le (hG.powStep_le_powLimit t ht ht' 1)

/-- **A convergent step is an admissible base** with mass `powLimit`, tail rate `(−t−1)/2`. -/
theorem logBase_powStep_of_lt (hG : PolyLogBounded G C₀ δ C₁ j) (t : ℝ) (ht : t < -1)
    (ht' : -1 < t + δ) :
    LogBase (powStep t G) (powLimit t G) (C₁ * (1 + 1 / absorbEps t j) ^ j * (2 / (-t - 1)))
      (C₀ / (t + δ + 1)) (t + δ + 1) ((-t - 1) / 2) where
  measurable := hG.powStep_measurable t ht'
  nonneg := hG.powStep_nonneg t
  le_mass := fun y => hG.powStep_le_powLimit t ht ht' y
  le_pow := fun y hy0 hy1 => hG.powStep_le_pow t ht' y hy0 hy1
  δ_pos := by linarith
  ε_pos := by linarith
  tail := by
    intro L hL
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hG.powStep_le_powLimit t ht ht' L])]
    exact hG.powLimit_sub_powStep_le t ht ht' L hL

end PolyLogBounded

/-- The base level `F_{q−1}` is polylog-bounded with `j = 0`. -/
theorem weightedPrimitive_polyLog (β a q : ℝ) (hβ : 0 < β) (hq : 0 < q) :
    PolyLogBounded (weightedPrimitive β a (q - 1)) (Real.exp (β * a ^ 2 / 2) / q) q
      (weightedMass β a (q - 1)) 0 where
  measurable := weightedPrimitive_measurable β a (q - 1) hβ (by linarith)
  nonneg := weightedPrimitive_nonneg β a (q - 1)
  δ_pos := hq
  le_pow := by
    intro y hy0 _
    have := weightedPrimitive_le β a (q - 1) y hβ (by linarith) hy0.le
    rw [show q - 1 + 1 = q by ring] at this
    exact this.trans (le_of_eq (by ring))
  le_log := fun y hy => by
    rw [pow_zero, mul_one]
    exact weightedPrimitive_le_mass β a (q - 1) y hβ (by linarith) (zero_le_one.trans hy)

end Laplace.Grammar
