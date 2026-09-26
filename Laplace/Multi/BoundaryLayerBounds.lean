/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PolytopeFaceCut

/-!
# Boundary-layer calculus

For a nonnegative slack `g` and a nonnegative integrable weight `w`, the **layer mass**
`H(r) = ∫_{0 < g < r} w` and the **tilt mass** `B_t = ∫_{g > 0} w e^{−t g}` are related by the
Laplace transform `B_t = t ∫₀^∞ e^{−t r} H(r) dr` (`tiltMass_eq_laplace_layerMass`, Tonelli), and
by the elementary bound `H(r) ≤ e^{t r} B_t` (`layerMass_le_exp_mul_tiltMass`). Consequently a
polynomial boundary layer `H(r) ≤ K r^α` on `(0, r₀]` gives the polynomial tilt decay
`B_t ≤ K Γ(α+1) t^{−α} + W e^{−t r₀}` (`tiltMass_le_of_layerMass_le`), and conversely a decay
`B_t ≤ C t^{−α}` for `t ≥ t₀` gives `H(r) ≤ e C r^α` for `r ≤ 1/t₀` (`layerMass_le_of_tiltMass_le`):
the growth exponent of the layer and the decay exponent of the tilt coincide.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Exp

/-- The derivative of `−e^{−t r}`. -/
theorem hasDerivAt_neg_exp_neg_mul (t r : ℝ) :
    HasDerivAt (fun r ↦ -Real.exp (-(t * r))) (t * Real.exp (-(t * r))) r := by
  have h1 : HasDerivAt (fun r ↦ -(t * r)) (-t) r := by
    have h := (hasDerivAt_id r).const_mul (-t)
    simp only [id_eq, mul_one, neg_mul] at h
    exact h
  have h2 : HasDerivAt (fun r ↦ -Real.exp (-(t * r))) (-(Real.exp (-(t * r)) * -t)) r := h1.exp.neg
  exact h2.congr_deriv (by ring)

theorem tendsto_neg_exp_neg_mul {t : ℝ} (ht : 0 < t) :
    Tendsto (fun r ↦ -Real.exp (-(t * r))) atTop (𝓝 0) := by
  have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ht)).neg
  rw [neg_zero] at h
  exact h

/-- `∫_a^∞ t e^{−t r} dr = e^{−t a}` for `t > 0`. -/
theorem integral_Ioi_mul_exp_neg_mul {t : ℝ} (ht : 0 < t) (a : ℝ) :
    ∫ r in Ioi a, t * Real.exp (-(t * r)) = Real.exp (-(t * a)) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    (hasDerivAt_neg_exp_neg_mul t a).continuousAt.continuousWithinAt
    (fun r _ ↦ hasDerivAt_neg_exp_neg_mul t r)
    (fun r _ ↦ (mul_pos ht (Real.exp_pos (-(t * r)))).le) (tendsto_neg_exp_neg_mul ht)
  rw [h, zero_sub, neg_neg]

theorem integrableOn_Ioi_mul_exp_neg_mul {t : ℝ} (ht : 0 < t) (a : ℝ) :
    IntegrableOn (fun r ↦ t * Real.exp (-(t * r))) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg (hasDerivAt_neg_exp_neg_mul t a).continuousAt.continuousWithinAt
    (fun r _ ↦ hasDerivAt_neg_exp_neg_mul t r)
    (fun r _ ↦ (mul_pos ht (Real.exp_pos (-(t * r)))).le) (tendsto_neg_exp_neg_mul ht)

theorem integrableOn_Ioi_exp_neg_mul {t : ℝ} (ht : 0 < t) (a : ℝ) :
    IntegrableOn (fun r ↦ Real.exp (-(t * r))) (Ioi a) := by
  have h : IntegrableOn (fun r ↦ t⁻¹ * (t * Real.exp (-(t * r)))) (Ioi a) :=
    (integrableOn_Ioi_mul_exp_neg_mul ht a).const_mul t⁻¹
  refine h.congr_fun (fun r _ ↦ ?_) measurableSet_Ioi
  change t⁻¹ * (t * Real.exp (-(t * r))) = _
  rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]

end Exp

section Layer

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (w g : X → ℝ)

/-- The boundary-layer mass `H(r) = ∫_{0 < g < r} w`. -/
noncomputable def layerMass (r : ℝ) : ℝ := ∫ x in {x | 0 < g x ∧ g x < r}, w x ∂ν

/-- The tilt mass `B_t = ∫_{g > 0} w e^{−t g}`. -/
noncomputable def tiltMass (t : ℝ) : ℝ := ∫ x in {x | 0 < g x}, w x * Real.exp (-(t * g x)) ∂ν

/-- The total mass off the face, `W = ∫_{g > 0} w`. -/
noncomputable def offMass : ℝ := ∫ x in {x | 0 < g x}, w x ∂ν

variable {w g} (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hwi : Integrable w ν) (hg : Measurable g)
  (hg0 : ∀ x, 0 ≤ g x)
include hw hw0 hwi hg hg0

omit hw hw0 hwi hg0 in
theorem measurableSet_layer (r : ℝ) : MeasurableSet {x | 0 < g x ∧ g x < r} :=
  (measurableSet_lt measurable_const hg).inter (measurableSet_lt hg measurable_const)

omit hw hw0 hwi hg0 in
theorem measurableSet_slackPos : MeasurableSet {x | 0 < g x} :=
  measurableSet_lt measurable_const hg

omit [IsFiniteMeasure ν] hw hwi hg hg0 in
theorem layerMass_nonneg (r : ℝ) : 0 ≤ layerMass ν w g r :=
  setIntegral_nonneg_of_ae_restrict (Eventually.of_forall hw0)

omit [IsFiniteMeasure ν] hw hg hg0 in
theorem layerMass_mono : Monotone (layerMass ν w g) := fun r r' hrr' ↦ by
  have hsub : {x | 0 < g x ∧ g x < r} ⊆ {x | 0 < g x ∧ g x < r'} :=
    fun x hx ↦ ⟨hx.1, hx.2.trans_le hrr'⟩
  exact setIntegral_mono_set hwi.integrableOn (Eventually.of_forall hw0) hsub.eventuallyLE

omit [IsFiniteMeasure ν] hw hg hg0 in
theorem layerMass_le_offMass (r : ℝ) : layerMass ν w g r ≤ offMass ν w g := by
  have hsub : {x | 0 < g x ∧ g x < r} ⊆ {x | 0 < g x} := fun x hx ↦ hx.1
  exact setIntegral_mono_set hwi.integrableOn (Eventually.of_forall hw0) hsub.eventuallyLE

omit [IsFiniteMeasure ν] hw hw0 in
theorem integrable_tilt {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x ↦ w x * Real.exp (-(t * g x))) ν := by
  have hm : Measurable (fun x ↦ Real.exp (-(t * g x))) :=
    Real.measurable_exp.comp (hg.const_mul t).neg
  have h := hwi.bdd_mul (c := 1) hm.aestronglyMeasurable
    (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, Real.abs_exp]
      exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ht (hg0 x))))
  exact h.congr (Eventually.of_forall fun x ↦ mul_comm _ _)

omit [IsFiniteMeasure ν] hw hwi hg hg0 in
theorem tiltMass_nonneg (t : ℝ) : 0 ≤ tiltMass ν w g t :=
  setIntegral_nonneg_of_ae_restrict
    (Eventually.of_forall fun x ↦ mul_nonneg (hw0 x) (Real.exp_pos _).le)

omit [IsFiniteMeasure ν] hw in
/-- **The layer bound** `H(r) ≤ e^{t r} B_t` for `t ≥ 0`. -/
theorem layerMass_le_exp_mul_tiltMass {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    layerMass ν w g r ≤ Real.exp (t * r) * tiltMass ν w g t := by
  unfold layerMass tiltMass
  rw [← integral_const_mul]
  have hI : Integrable (fun x ↦ Real.exp (t * r) * (w x * Real.exp (-(t * g x)))) ν :=
    (integrable_tilt ν hwi hg hg0 ht).const_mul _
  have hpt : ∀ x, g x < r → w x ≤ Real.exp (t * r) * (w x * Real.exp (-(t * g x))) := fun x hx ↦ by
    rw [show Real.exp (t * r) * (w x * Real.exp (-(t * g x))) =
        w x * (Real.exp (t * r) * Real.exp (-(t * g x))) by ring, ← Real.exp_add]
    exact le_mul_of_one_le_right (hw0 x)
      (Real.one_le_exp_iff.2 (by nlinarith [mul_nonneg ht (sub_nonneg.2 hx.le)]))
  calc ∫ x in {x | 0 < g x ∧ g x < r}, w x ∂ν ≤
        ∫ x in {x | 0 < g x ∧ g x < r}, Real.exp (t * r) * (w x * Real.exp (-(t * g x))) ∂ν :=
        setIntegral_mono_on hwi.integrableOn hI.integrableOn (measurableSet_layer hg r)
          fun x hx ↦ hpt x hx.2
    _ ≤ ∫ x in {x | 0 < g x}, Real.exp (t * r) * (w x * Real.exp (-(t * g x))) ∂ν := by
        have hsub : {x | 0 < g x ∧ g x < r} ⊆ {x | 0 < g x} := fun x hx ↦ hx.1
        exact setIntegral_mono_set hI.integrableOn (Eventually.of_forall fun x ↦
          mul_nonneg (Real.exp_pos _).le (mul_nonneg (hw0 x) (Real.exp_pos _).le))
          hsub.eventuallyLE

/-- **The Laplace-transform identity** `B_t = t ∫₀^∞ e^{−t r} H(r) dr` (Tonelli). -/
theorem tiltMass_eq_laplace_layerMass {t : ℝ} (ht : 0 < t) :
    tiltMass ν w g t = t * ∫ r in Ioi 0, Real.exp (-(t * r)) * layerMass ν w g r := by
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun r ↦ t * Real.exp (-(t * r)) := ⟨_, rfl⟩
  have hFm : Measurable F := hF ▸ measurable_const.mul (Real.measurable_exp.comp
    (measurable_id.const_mul t).neg)
  have hF0 : ∀ r, 0 ≤ F r := fun r ↦ hF ▸ (mul_pos ht (Real.exp_pos _)).le
  have hFi : IntegrableOn F (Ioi 0) := hF ▸ integrableOn_Ioi_mul_exp_neg_mul ht 0
  -- the exponential as a tail integral of `F`
  have hexp : ∀ x, Real.exp (-(t * g x)) = ∫ r in Ioi 0, (Ioi (g x)).indicator F r := fun x ↦ by
    rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.2 (Ioi_subset_Ioi (hg0 x)), hF, integral_Ioi_mul_exp_neg_mul ht]
  have hpos := measurableSet_slackPos hg
  -- Tonelli
  have hint : Integrable (Function.uncurry fun x r ↦ w x * (Ioi (g x)).indicator F r)
      ((ν.restrict {x | 0 < g x}).prod (volume.restrict (Ioi 0))) := by
    have hprod : Integrable (fun p : X × ℝ ↦ w p.1 * F p.2)
        ((ν.restrict {x | 0 < g x}).prod (volume.restrict (Ioi 0))) :=
      Integrable.mul_prod hwi.integrableOn hFi
    have hmeas : Measurable (Function.uncurry fun x r ↦ w x * (Ioi (g x)).indicator F r) := by
      have e : (Function.uncurry fun x r ↦ w x * (Ioi (g x)).indicator F r) =
          fun p : X × ℝ ↦ w p.1 * {p : X × ℝ | g p.1 < p.2}.indicator (fun p ↦ F p.2) p := by
        funext p
        simp only [Function.uncurry_def, Set.indicator_apply, mem_Ioi, mem_ofPred_eq]
      rw [e]
      exact (hw.comp measurable_fst).mul ((hFm.comp measurable_snd).indicator
        (measurableSet_lt (hg.comp measurable_fst) measurable_snd))
    refine hprod.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun p ↦ ?_)
    simp only [Function.uncurry_def, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (hw0 p.1) (Set.indicator_nonneg (fun r _ ↦ hF0 r) _))]
    exact mul_le_mul_of_nonneg_left (Set.indicator_le_self' (fun r _ ↦ hF0 r) _) (hw0 p.1)
  unfold tiltMass
  have h1 : ∫ x in {x | 0 < g x}, w x * Real.exp (-(t * g x)) ∂ν =
      ∫ x in {x | 0 < g x}, (∫ r in Ioi 0, w x * (Ioi (g x)).indicator F r) ∂ν :=
    setIntegral_congr_fun hpos fun x _ ↦ by rw [hexp x, ← integral_const_mul]
  rw [h1, integral_integral_swap hint]
  have h2 : ∀ r ∈ Ioi (0 : ℝ), ∫ x in {x | 0 < g x}, w x * (Ioi (g x)).indicator F r ∂ν =
      F r * layerMass ν w g r := fun r _ ↦ by
    have e : ∀ x, w x * (Ioi (g x)).indicator F r = F r * ({x | g x < r}.indicator w x) :=
      fun x ↦ by
        by_cases hx : g x < r
        · rw [Set.indicator_of_mem (mem_Ioi.2 hx), Set.indicator_of_mem (s := {x | g x < r}) hx]
          ring
        · rw [Set.indicator_of_notMem (fun h ↦ hx (mem_Ioi.1 h)),
            Set.indicator_of_notMem (s := {x | g x < r}) hx, mul_zero, mul_zero]
    simp_rw [e]
    rw [integral_const_mul, integral_indicator (measurableSet_lt hg measurable_const),
      Measure.restrict_restrict (measurableSet_lt hg measurable_const)]
    unfold layerMass
    have hsets : {x | g x < r} ∩ {x | 0 < g x} = {x | 0 < g x ∧ g x < r} := by
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact and_comm
    rw [hsets]
  rw [setIntegral_congr_fun measurableSet_Ioi h2, hF]
  simp only [mul_assoc]
  rw [integral_const_mul]

omit [IsFiniteMeasure ν] hw hg hg0 in
theorem integrableOn_exp_mul_layerMass {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun r ↦ Real.exp (-(t * r)) * layerMass ν w g r) (Ioi 0) := by
  refine ((integrableOn_Ioi_exp_neg_mul ht 0).mul_const (offMass ν w g)).mono'
    ((Real.measurable_exp.comp (measurable_id.const_mul t).neg).mul
      (layerMass_mono ν hw0 hwi).measurable).aestronglyMeasurable
    (Eventually.of_forall fun r ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (layerMass_nonneg ν hw0 r))]
  exact mul_le_mul_of_nonneg_left (layerMass_le_offMass ν hw0 hwi r) (Real.exp_pos _).le

/-- **Polynomial boundary layers give polynomial tilt decay**: if `H(r) ≤ K r^α` on `(0, r₀]`, then
`B_t ≤ K Γ(α+1) t^{−α} + W e^{−t r₀}` for every `t > 0`. -/
theorem tiltMass_le_of_layerMass_le {α K r₀ : ℝ} (hα : 0 ≤ α) (hK : 0 ≤ K) (hr₀ : 0 < r₀)
    (hH : ∀ r, 0 < r → r ≤ r₀ → layerMass ν w g r ≤ K * r ^ α) {t : ℝ} (ht : 0 < t) :
    tiltMass ν w g t ≤
      K * Real.Gamma (α + 1) * t ^ (-α) + offMass ν w g * Real.exp (-(t * r₀)) := by
  rw [tiltMass_eq_laplace_layerMass ν hw hw0 hwi hg hg0 ht]
  have hI := integrableOn_exp_mul_layerMass ν (g := g) hw0 hwi ht
  have hsplit : ∫ r in Ioi 0, Real.exp (-(t * r)) * layerMass ν w g r =
      (∫ r in Ioc 0 r₀, Real.exp (-(t * r)) * layerMass ν w g r) +
        ∫ r in Ioi r₀, Real.exp (-(t * r)) * layerMass ν w g r := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi hr₀.le)),
      Ioc_union_Ioi_eq_Ioi hr₀.le]
  -- the polynomial piece
  have hG : ∫ r in Ioi 0, r ^ α * Real.exp (-(t * r)) = (1 / t) ^ (α + 1) * Real.Gamma (α + 1) := by
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0 < α + 1) ht
    rwa [add_sub_cancel_right] at this
  have hGi : IntegrableOn (fun r ↦ r ^ α * Real.exp (-(t * r))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < α) one_pos ht
    refine this.congr_fun (fun r _ ↦ ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
  have hGiK : IntegrableOn (fun r ↦ K * (r ^ α * Real.exp (-(t * r)))) (Ioi 0) := hGi.const_mul K
  have h1 : ∫ r in Ioc 0 r₀, Real.exp (-(t * r)) * layerMass ν w g r ≤
      K * ((1 / t) ^ (α + 1) * Real.Gamma (α + 1)) := by
    rw [← hG, ← integral_const_mul]
    calc ∫ r in Ioc 0 r₀, Real.exp (-(t * r)) * layerMass ν w g r ≤
          ∫ r in Ioc 0 r₀, K * (r ^ α * Real.exp (-(t * r))) :=
          setIntegral_mono_on (hI.mono_set Ioc_subset_Ioi_self)
            (hGiK.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc fun r hr ↦ by
              rw [show K * (r ^ α * Real.exp (-(t * r))) =
                Real.exp (-(t * r)) * (K * r ^ α) by ring]
              exact mul_le_mul_of_nonneg_left (hH r hr.1 hr.2) (Real.exp_pos _).le
      _ ≤ ∫ r in Ioi 0, K * (r ^ α * Real.exp (-(t * r))) :=
          setIntegral_mono_set hGiK ((ae_restrict_iff' measurableSet_Ioi).2
            (Eventually.of_forall fun r hr ↦ mul_nonneg hK
              (mul_nonneg (Real.rpow_nonneg (le_of_lt hr) α) (Real.exp_pos _).le)))
            Ioc_subset_Ioi_self.eventuallyLE
  -- the tail piece
  have h2 : ∫ r in Ioi r₀, Real.exp (-(t * r)) * layerMass ν w g r ≤
      offMass ν w g * (Real.exp (-(t * r₀)) / t) := by
    have hE : ∫ r in Ioi r₀, Real.exp (-(t * r)) = Real.exp (-(t * r₀)) / t := by
      have := integral_Ioi_mul_exp_neg_mul ht r₀
      rw [integral_const_mul] at this
      rw [← this]
      field_simp
    calc ∫ r in Ioi r₀, Real.exp (-(t * r)) * layerMass ν w g r ≤
          ∫ r in Ioi r₀, Real.exp (-(t * r)) * offMass ν w g :=
          setIntegral_mono_on (hI.mono_set (Ioi_subset_Ioi hr₀.le))
            ((integrableOn_Ioi_exp_neg_mul ht r₀).mul_const _) measurableSet_Ioi fun r _ ↦
              mul_le_mul_of_nonneg_left (layerMass_le_offMass ν hw0 hwi r) (Real.exp_pos _).le
      _ = offMass ν w g * (Real.exp (-(t * r₀)) / t) := by rw [integral_mul_const, hE, mul_comm]
  have hpow : t * (1 / t) ^ (α + 1) = t ^ (-α) := by
    rw [one_div, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
    calc t * t ^ (-(α + 1)) = t ^ (1 : ℝ) * t ^ (-(α + 1)) := by rw [Real.rpow_one]
      _ = t ^ (1 + -(α + 1)) := (Real.rpow_add ht _ _).symm
      _ = t ^ (-α) := by congr 1; ring
  rw [hsplit]
  calc t * ((∫ r in Ioc 0 r₀, Real.exp (-(t * r)) * layerMass ν w g r) +
        ∫ r in Ioi r₀, Real.exp (-(t * r)) * layerMass ν w g r) ≤
      t * (K * ((1 / t) ^ (α + 1) * Real.Gamma (α + 1)) +
        offMass ν w g * (Real.exp (-(t * r₀)) / t)) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) ht.le
    _ = K * Real.Gamma (α + 1) * t ^ (-α) + offMass ν w g * Real.exp (-(t * r₀)) := by
        rw [mul_add, show t * (K * ((1 / t) ^ (α + 1) * Real.Gamma (α + 1))) =
          K * Real.Gamma (α + 1) * (t * (1 / t) ^ (α + 1)) by ring, hpow,
          show t * (offMass ν w g * (Real.exp (-(t * r₀)) / t)) =
            offMass ν w g * Real.exp (-(t * r₀)) by field_simp]

omit [IsFiniteMeasure ν] hw in
/-- **Polynomial tilt decay gives a polynomial boundary layer**: if `B_t ≤ C t^{−α}` for `t ≥ t₀`,
then `H(r) ≤ e C r^α` for `0 < r ≤ 1/t₀`. -/
theorem layerMass_le_of_tiltMass_le {α C t₀ : ℝ} (ht₀ : 0 < t₀)
    (hB : ∀ t, t₀ ≤ t → tiltMass ν w g t ≤ C * t ^ (-α)) {r : ℝ} (hr : 0 < r)
    (hrt : r ≤ 1 / t₀) : layerMass ν w g r ≤ Real.exp 1 * C * r ^ α := by
  have ht : t₀ ≤ 1 / r := by
    rw [le_div_iff₀ hr]
    calc t₀ * r ≤ t₀ * (1 / t₀) := mul_le_mul_of_nonneg_left hrt ht₀.le
      _ = 1 := by field_simp
  calc layerMass ν w g r ≤ Real.exp (1 / r * r) * tiltMass ν w g (1 / r) :=
        layerMass_le_exp_mul_tiltMass ν hw0 hwi hg hg0 (by positivity) r
    _ ≤ Real.exp 1 * (C * (1 / r) ^ (-α)) := by
        rw [one_div_mul_cancel hr.ne']
        exact mul_le_mul_of_nonneg_left (hB _ ht) (Real.exp_pos _).le
    _ = Real.exp 1 * C * r ^ α := by
        rw [one_div, Real.inv_rpow hr.le, Real.rpow_neg hr.le, inv_inv]
        ring

end Layer

section Ray

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (θ u : J → ℝ) (β : ℝ)
include hS

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
variable (S) in
/-- The nonnegative slack of the exposing functional. -/
noncomputable def raySlack (x : X) : ℝ := max 0 (β - dirLoss S u x)

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem measurable_raySlack : Measurable (raySlack S u β) :=
  measurable_const.max ((bdd_dirLoss hS u).1.const_sub β)

omit [MeasurableSpace X] [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem raySlack_nonneg (x : X) : 0 ≤ raySlack S u β x := le_max_left _ _

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The off-face mass of the natural ray is the tilt mass of the slack. -/
theorem offFaceMass_eq_tiltMass (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β) (t : ℝ) :
    offFaceMass S ν θ u β t = tiltMass ν (famWeight S θ) (raySlack S u β) t := by
  unfold offFaceMass tiltMass
  have hset : {x | dirLoss S u x = β}ᶜ =ᵐ[ν] {x | 0 < raySlack S u β x} := by
    refine Filter.eventuallyEq_set.2 ?_
    filter_upwards [hβ] with x hx
    change ¬dirLoss S u x = β ↔ 0 < max 0 (β - dirLoss S u x)
    rw [lt_max_iff, sub_pos]
    simp only [lt_self_iff_false, false_or]
    exact ⟨fun h ↦ lt_of_le_of_ne hx h, fun h ↦ h.ne⟩
  refine (setIntegral_congr_set hset).trans ?_
  refine setIntegral_congr_fun (measurableSet_lt measurable_const (measurable_raySlack hS u β))
    fun x hx ↦ ?_
  have hx' : 0 < β - dirLoss S u x := by
    have hx0 : 0 < max 0 (β - dirLoss S u x) := hx
    have := lt_max_iff.1 hx0
    simpa using this
  simp only [raySlack, max_eq_right hx'.le]

omit [Nonempty X] [Nonempty J] in
/-- **Polynomial boundary layers give polynomial total-variation rates along natural rays**:
if `H(r) ≤ K r^α` on `(0, r₀]`, then `‖p_{θ−tu} − p_F‖₁ ≤ (2/A)(K Γ(α+1) t^{−α} + W e^{−t r₀})`. -/
theorem integral_abs_famDens_ray_sub_faceDens_le (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) {α K r₀ : ℝ} (hα : 0 ≤ α) (hK : 0 ≤ K)
    (hr₀ : 0 < r₀)
    (hH : ∀ r, 0 < r → r ≤ r₀ → layerMass ν (famWeight S θ) (raySlack S u β) r ≤ K * r ^ α)
    {t : ℝ} (ht : 0 < t) :
    ∫ x, |famDens S ν (θ - t • u) x - faceDens S ν θ u β x| ∂ν ≤
      2 / faceMass S ν θ u β * (K * Real.Gamma (α + 1) * t ^ (-α) +
        offMass ν (famWeight S θ) (raySlack S u β) * Real.exp (-(t * r₀))) := by
  have hA := faceMass_pos hS ν θ u β hp
  have hB := offFaceMass_nonneg hS ν θ u β t
  have hmw : Measurable (famWeight S θ) := Real.measurable_exp.comp (bdd_dirLoss hS θ).1.neg
  have hbound := tiltMass_le_of_layerMass_le ν hmw (fun x ↦ (famWeight_pos θ x).le)
    (integrable_famWeight hS ν θ) (measurable_raySlack hS u β) (raySlack_nonneg u β) hα hK hr₀ hH ht
  rw [← offFaceMass_eq_tiltMass hS ν θ u β hβ] at hbound
  rw [integral_abs_famDens_ray_sub_faceDens hS ν θ u β hp]
  calc 2 * offFaceMass S ν θ u β t / (faceMass S ν θ u β + offFaceMass S ν θ u β t) ≤
        2 * offFaceMass S ν θ u β t / faceMass S ν θ u β :=
        div_le_div_of_nonneg_left (by linarith) hA (by linarith)
    _ = 2 / faceMass S ν θ u β * offFaceMass S ν θ u β t := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)

end Ray

end Laplace.Multi
