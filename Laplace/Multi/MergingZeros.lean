/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.WallCrossover

/-!
# The merging-zeros wall `x²(x − s)²`

The second kind of wall in one dimension: two zeros of the loss, at `0` and at `s`, merge as
`s → 0`.
Off the wall each is Morse (type `1/2`); at the wall the loss is `x⁴` (type `1/4`). With flat prior
the energy statistic collapses EXACTLY onto the combined variable `σ = s t^{1/4}`
(`mergeEnergy_eq_mergeCross`), the same variable as for the degenerating-unit wall
`x²(x² + s²)`, as germbij_slop S10's zoo found. Translating by `σ/2` puts the family in the
symmetric double-well form `(w² − a)²`, `a = σ²/4` (`mergeCross_eq_doubleWell`), whose value at
the wall is `1/4`
(`doubleWell_zero`). The limit `1/2` as `a → ∞` (two separated Gaussians) is
`tendsto_doubleWell_atTop`, by evenness, the substitution `w = √a + y/(2√a)` on the half line and
dominated convergence; the crossover is non-monotone in between (numerics, S10).
-/

open Real MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The merging-zeros loss `x²(x − s)²`. -/
noncomputable def mergeLoss (s x : ℝ) : ℝ := x ^ 2 * (x - s) ^ 2

/-- Its energy statistic with flat prior. -/
noncomputable def mergeEnergy (s t : ℝ) : ℝ :=
  t * ((∫ x, mergeLoss s x * Real.exp (-(t * mergeLoss s x))) /
    ∫ x, Real.exp (-(t * mergeLoss s x)))

/-- The crossover function `E_σ[u²(u − σ)²]` under `e^{-u²(u−σ)²}`. -/
noncomputable def mergeCross (σ : ℝ) : ℝ :=
  (∫ u, mergeLoss σ u * Real.exp (-mergeLoss σ u)) / ∫ u, Real.exp (-mergeLoss σ u)

/-- The double-well energy `E_a[(w² − a)²]` under `e^{-(w² − a)²}`. -/
noncomputable def doubleWell (a : ℝ) : ℝ :=
  (∫ w, (w ^ 2 - a) ^ 2 * Real.exp (-(w ^ 2 - a) ^ 2)) / ∫ w, Real.exp (-(w ^ 2 - a) ^ 2)

/-- **Exact collapse**: `t E_{s,t}[x²(x−s)²] = mergeCross (s t^{1/4})`. -/
theorem mergeEnergy_eq_mergeCross (s : ℝ) {t : ℝ} (ht : 0 < t) :
    mergeEnergy s t = mergeCross (s * t ^ ((1 : ℝ) / 4)) := by
  set c : ℝ := t ^ (-(1 / 4 : ℝ)) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos ht _
  have hc4 : t * c ^ 4 = 1 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    push_cast
    rw [show -(1 / 4 : ℝ) * 4 = -1 by norm_num, Real.rpow_neg_one, mul_inv_cancel₀ ht.ne']
  have hcq : t ^ ((1 : ℝ) / 4) * c = 1 := by
    rw [hc, ← Real.rpow_add ht]
    norm_num
  have hpt : ∀ u : ℝ, t * mergeLoss s (c * u) = mergeLoss (s * t ^ ((1 : ℝ) / 4)) u := by
    intro u
    unfold mergeLoss
    have : c * u - s = c * (u - s * t ^ ((1 : ℝ) / 4)) := by
      have : c * (s * t ^ ((1 : ℝ) / 4)) = s := by
        rw [mul_comm s, ← mul_assoc, mul_comm c, hcq, one_mul]
      rw [mul_sub, this]
    rw [this, mul_pow, mul_pow]
    have : t * (c ^ 2 * u ^ 2 * (c ^ 2 * (u - s * t ^ ((1 : ℝ) / 4)) ^ 2)) =
        (t * c ^ 4) * (u ^ 2 * (u - s * t ^ ((1 : ℝ) / 4)) ^ 2) := by ring
    rw [this, hc4, one_mul]
  have hn := Measure.integral_comp_mul_left
    (fun x : ℝ ↦ t * mergeLoss s x * Real.exp (-(t * mergeLoss s x))) c
  have hd := Measure.integral_comp_mul_left (fun x : ℝ ↦ Real.exp (-(t * mergeLoss s x))) c
  rw [abs_inv, abs_of_pos hcpos, smul_eq_mul] at hn hd
  simp only [hpt] at hn hd
  unfold mergeEnergy mergeCross
  rw [mul_div_assoc', ← integral_const_mul]
  have e0 : (fun x : ℝ ↦ t * (mergeLoss s x * Real.exp (-(t * mergeLoss s x)))) =
      fun x ↦ t * mergeLoss s x * Real.exp (-(t * mergeLoss s x)) := by
    funext x
    ring
  rw [e0]
  have hn' : (∫ x, t * mergeLoss s x * Real.exp (-(t * mergeLoss s x))) = c * ∫ u,
      mergeLoss (s * t ^ ((1 : ℝ) / 4)) u * Real.exp (-mergeLoss (s * t ^ ((1 : ℝ) / 4)) u) := by
    rw [hn, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
  have hd' : (∫ x, Real.exp (-(t * mergeLoss s x))) =
      c * ∫ u, Real.exp (-mergeLoss (s * t ^ ((1 : ℝ) / 4)) u) := by
    rw [hd, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
  rw [hn', hd', mul_div_mul_left _ _ hcpos.ne']

/-- `u²(u − σ)² = (w² − σ²/4)²` with `w = u − σ/2`. -/
theorem mergeLoss_eq_doubleWell (σ u : ℝ) :
    mergeLoss σ u = ((u - σ / 2) ^ 2 - σ ^ 2 / 4) ^ 2 := by
  unfold mergeLoss
  ring

/-- **Symmetric form**: `mergeCross σ = doubleWell (σ²/4)`. -/
theorem mergeCross_eq_doubleWell (σ : ℝ) : mergeCross σ = doubleWell (σ ^ 2 / 4) := by
  unfold mergeCross doubleWell
  have hn := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun w : ℝ ↦ (w ^ 2 - σ ^ 2 / 4) ^ 2 * Real.exp (-(w ^ 2 - σ ^ 2 / 4) ^ 2)) (σ / 2)
  have hd := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun w : ℝ ↦ Real.exp (-(w ^ 2 - σ ^ 2 / 4) ^ 2)) (σ / 2)
  simp only [mergeLoss_eq_doubleWell]
  rw [← hn, ← hd]

/-- **At the wall** the double-well energy is `1/4`. -/
theorem doubleWell_zero : doubleWell 0 = 1 / 4 := by
  have h := agmom_shift_div 2 (by norm_num) 0
  unfold agmom at h
  unfold doubleWell
  simp only [sub_zero]
  have e1 : (fun w : ℝ ↦ (w ^ 2) ^ 2 * Real.exp (-(w ^ 2) ^ 2)) =
      fun w ↦ |w| ^ (0 + 2 * 2) * Real.exp (-w ^ (2 * 2)) := by
    funext w
    rw [zero_add, abs_pow_even, ← pow_mul]
  have e0 : (fun w : ℝ ↦ Real.exp (-(w ^ 2) ^ 2)) = fun w ↦ |w| ^ 0 * Real.exp (-w ^ (2 * 2)) := by
    funext w
    rw [pow_zero, one_mul, ← pow_mul]
  rw [e1, e0, h]
  norm_num

/-! ### The separated-wells limit `doubleWell a → 1/2` -/

/-- `q_a(z) = z + z²/4a`: the well `(w² − a)²` in the coordinate `w = √a + z/(2√a)`. -/
noncomputable def dwq (a z : ℝ) : ℝ := z + z ^ 2 / (4 * a)

theorem dwq_sq_ge {a z : ℝ} (ha : 0 < a) (hz : -(2 * a) < z) : z ^ 2 / 4 ≤ dwq a z ^ 2 := by
  unfold dwq
  rcases le_or_gt 0 z with hz0 | hz0
  · have : z ≤ z + z ^ 2 / (4 * a) := by
      have : 0 ≤ z ^ 2 / (4 * a) := by positivity
      linarith
    nlinarith [sq_nonneg z]
  · -- `z + z²/4a = z (1 + z/4a)` with `1/2 < 1 + z/4a < 1`
    have hq : z + z ^ 2 / (4 * a) = z * (1 + z / (4 * a)) := by
      field_simp
    have h1 : 1 / 2 < 1 + z / (4 * a) := by
      rw [show (1 : ℝ) / 2 = 1 + (-(1 / 2) : ℝ) by norm_num]
      gcongr
      rw [lt_div_iff₀ (by positivity)]
      linarith
    have h2 : 1 + z / (4 * a) < 1 := by
      have : z / (4 * a) < 0 := div_neg_of_neg_of_pos hz0 (by positivity)
      linarith
    rw [hq, mul_pow]
    have hf : (1 / 2 : ℝ) ^ 2 ≤ (1 + z / (4 * a)) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) h1.le 2
    have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
    calc z ^ 2 / 4 = z ^ 2 * (1 / 2 : ℝ) ^ 2 := by ring
      _ ≤ z ^ 2 * (1 + z / (4 * a)) ^ 2 := mul_le_mul_of_nonneg_left hf hz2

theorem abs_dwq_le {a z : ℝ} (ha : 1 ≤ a) : |dwq a z| ≤ |z| + z ^ 2 / 4 := by
  unfold dwq
  refine (abs_add_le _ _).trans ?_
  have h1 : |z ^ 2 / (4 * a)| = z ^ 2 / (4 * a) := abs_of_nonneg (by positivity)
  rw [h1]
  have : z ^ 2 / (4 * a) ≤ z ^ 2 / 4 := by
    apply div_le_div_of_nonneg_left (sq_nonneg z) (by norm_num)
    linarith
  linarith

theorem tendsto_dwq (z : ℝ) : Tendsto (fun a ↦ dwq a z) atTop (𝓝 z) := by
  have h4 : Tendsto (fun a : ℝ ↦ 4 * a) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have := (tendsto_const_nhds (x := z ^ 2)).div_atTop h4
  have h := this.const_add z
  rw [add_zero] at h
  exact h

/-- The half-line form of the double-well energy. -/
theorem doubleWell_eq_halfLine {a : ℝ} (ha : 0 < a) :
    doubleWell a =
      (∫ z, (Ioi (-(2 * a))).indicator (fun z ↦ dwq a z ^ 2 * Real.exp (-dwq a z ^ 2)) z) /
        ∫ z, (Ioi (-(2 * a))).indicator (fun z ↦ Real.exp (-dwq a z ^ 2)) z := by
  set r : ℝ := Real.sqrt a with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr ha
  have hr2 : r ^ 2 = a := Real.sq_sqrt ha.le
  set c : ℝ := 1 / (2 * r) with hc
  have hcpos : 0 < c := by positivity
  -- the substituted well
  have hq : ∀ z : ℝ, ((c * z + r) ^ 2 - a) ^ 2 = dwq a z ^ 2 := by
    intro z
    congr 1
    unfold dwq
    rw [hc, ← hr2]
    field_simp
    ring
  -- the domain: `c z + r > 0 ↔ z > -2a`
  have hdom : ∀ z : ℝ, (0 < c * z + r ↔ -(2 * a) < z) := by
    intro z
    rw [hc, ← hr2]
    constructor
    · intro h
      have : 0 < (1 / (2 * r) * z + r) * (2 * r) := mul_pos h (by positivity)
      field_simp at this
      nlinarith
    · intro h
      have : 0 < (1 / (2 * r) * z + r) * (2 * r) := by
        field_simp
        nlinarith
      exact pos_of_mul_pos_left this (by positivity)
  -- evenness and substitution for an even integrand shape `F (w² − a)`
  have key : ∀ F : ℝ → ℝ, (∫ w, F ((w ^ 2 - a) ^ 2)) =
      2 * c * ∫ z, (Ioi (-(2 * a))).indicator (fun z ↦ F (dwq a z ^ 2)) z := by
    intro F
    have heven : (fun w : ℝ ↦ F ((w ^ 2 - a) ^ 2)) = fun w ↦ (fun v ↦ F ((v ^ 2 - a) ^ 2)) |w| := by
      funext w
      simp only [sq_abs]
    rw [heven, integral_comp_abs (f := fun v ↦ F ((v ^ 2 - a) ^ 2)),
      ← integral_indicator measurableSet_Ioi]
    set G : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (fun v ↦ F ((v ^ 2 - a) ^ 2)) with hG
    have hsub : (∫ v, G v) = c * ∫ z, G (c * z + r) := by
      have h1 := Measure.integral_comp_mul_left (fun y ↦ G (y + r)) c
      have h2 := integral_add_right_eq_self (μ := (volume : Measure ℝ)) G r
      rw [abs_inv, abs_of_pos hcpos, smul_eq_mul] at h1
      rw [h2] at h1
      rw [h1, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
    have hpt : ∀ z, G (c * z + r) = (Ioi (-(2 * a))).indicator (fun z ↦ F (dwq a z ^ 2)) z := by
      intro z
      simp only [hG]
      by_cases hz : -(2 * a) < z
      · rw [Set.indicator_of_mem (show c * z + r ∈ Ioi 0 from (hdom z).mpr hz),
          Set.indicator_of_mem (show z ∈ Ioi (-(2 * a)) from hz), hq]
      · rw [Set.indicator_of_notMem (show c * z + r ∉ Ioi 0 from fun h ↦ hz ((hdom z).mp h)),
          Set.indicator_of_notMem (show z ∉ Ioi (-(2 * a)) from hz)]
    rw [hsub]
    simp only [hpt]
    ring
  unfold doubleWell
  rw [key (fun y ↦ y * Real.exp (-y)), key (fun y ↦ Real.exp (-y)),
    mul_div_mul_left _ _ (by positivity : (2 * c : ℝ) ≠ 0)]

/-- **Separated wells**: `doubleWell a → 1/2` as `a → ∞`. -/
theorem tendsto_doubleWell_atTop : Tendsto doubleWell atTop (𝓝 (1 / 2)) := by
  -- the Gaussian limit ratio
  have hlim : (∫ z : ℝ, z ^ 2 * Real.exp (-(z ^ 2))) / (∫ z : ℝ, Real.exp (-(z ^ 2))) = 1 / 2 := by
    have h := gmom_two_k_div_zero 1 le_rfl
    unfold gmom at h
    norm_num at h ⊢
    exact h
  -- integrable dominating functions
  have hG : ∀ j : ℕ, Integrable fun z : ℝ ↦ |z| ^ j * Real.exp (-(1 / 4 * z ^ (2 * 1))) :=
    fun j ↦ integrable_abs_pow_mul_exp_neg_mul_pow (by norm_num) 1 le_rfl j
  have hdomN : Integrable fun z : ℝ ↦
      (|z| + z ^ 2 / 4) ^ 2 * Real.exp (-(1 / 4 * z ^ (2 * 1))) := by
    refine (((hG 2).add ((hG 3).const_mul (1 / 2))).add ((hG 4).const_mul (1 / 16))).congr
      (Filter.Eventually.of_forall fun z ↦ ?_)
    simp only [Pi.add_apply]
    rw [← sq_abs z]
    ring
  have hdomD : Integrable fun z : ℝ ↦ Real.exp (-(1 / 4 * z ^ (2 * 1))) := by
    have := hG 0
    simpa using this
  -- pointwise limits
  have hptN : ∀ z : ℝ, Tendsto (fun a ↦ (Ioi (-(2 * a))).indicator
      (fun z ↦ dwq a z ^ 2 * Real.exp (-dwq a z ^ 2)) z) atTop
      (𝓝 (z ^ 2 * Real.exp (-(z ^ 2)))) := by
    intro z
    have h := ((tendsto_dwq z).pow 2).mul
      ((Real.continuous_exp.tendsto _).comp ((tendsto_dwq z).pow 2).neg)
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (max 1 |z|)] with a ha
    have hz : -(2 * a) < z := by
      have h1 : 1 ≤ a := le_of_max_le_left ha
      have h2 : |z| ≤ a := le_of_max_le_right ha
      have := neg_abs_le z
      linarith
    simp only [Function.comp]
    rw [Set.indicator_of_mem (show z ∈ Ioi (-(2 * a)) from hz)]
  have hptD : ∀ z : ℝ, Tendsto (fun a ↦ (Ioi (-(2 * a))).indicator
      (fun z ↦ Real.exp (-dwq a z ^ 2)) z) atTop (𝓝 (Real.exp (-(z ^ 2)))) := by
    intro z
    have h := (Real.continuous_exp.tendsto _).comp ((tendsto_dwq z).pow 2).neg
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (max 1 |z|)] with a ha
    have hz : -(2 * a) < z := by
      have h1 : 1 ≤ a := le_of_max_le_left ha
      have h2 : |z| ≤ a := le_of_max_le_right ha
      have := neg_abs_le z
      linarith
    simp only [Function.comp]
    rw [Set.indicator_of_mem (show z ∈ Ioi (-(2 * a)) from hz)]
  -- the bounds, for `a ≥ 1`
  have hbN : ∀ a : ℝ, 1 ≤ a → ∀ z : ℝ,
      ‖(Ioi (-(2 * a))).indicator (fun z ↦ dwq a z ^ 2 * Real.exp (-dwq a z ^ 2)) z‖ ≤
        (|z| + z ^ 2 / 4) ^ 2 * Real.exp (-(1 / 4 * z ^ (2 * 1))) := by
    intro a ha z
    have ha0 : 0 < a := by linarith
    have hq4 : 1 / 4 * z ^ (2 * 1) = z ^ 2 / 4 := by ring
    rw [Real.norm_eq_abs, hq4]
    by_cases hz : -(2 * a) < z
    · rw [Set.indicator_of_mem (show z ∈ Ioi (-(2 * a)) from hz),
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
      have hq2 : dwq a z ^ 2 ≤ (|z| + z ^ 2 / 4) ^ 2 := by
        rw [← sq_abs (dwq a z)]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_dwq_le ha) 2
      have hexp : Real.exp (-dwq a z ^ 2) ≤ Real.exp (-(z ^ 2 / 4)) :=
        Real.exp_le_exp.mpr (by linarith [dwq_sq_ge ha0 hz])
      exact mul_le_mul hq2 hexp (Real.exp_pos _).le (by positivity)
    · rw [Set.indicator_of_notMem (show z ∉ Ioi (-(2 * a)) from hz), abs_zero]
      positivity
  have hbD : ∀ a : ℝ, 1 ≤ a → ∀ z : ℝ,
      ‖(Ioi (-(2 * a))).indicator (fun z ↦ Real.exp (-dwq a z ^ 2)) z‖ ≤
        Real.exp (-(1 / 4 * z ^ (2 * 1))) := by
    intro a ha z
    have ha0 : 0 < a := by linarith
    have hq4 : 1 / 4 * z ^ (2 * 1) = z ^ 2 / 4 := by ring
    rw [Real.norm_eq_abs, hq4]
    by_cases hz : -(2 * a) < z
    · rw [Set.indicator_of_mem (show z ∈ Ioi (-(2 * a)) from hz), Real.abs_exp]
      exact Real.exp_le_exp.mpr (by linarith [dwq_sq_ge ha0 hz])
    · rw [Set.indicator_of_notMem (show z ∉ Ioi (-(2 * a)) from hz), abs_zero]
      positivity
  have hmeasN : ∀ a : ℝ, AEStronglyMeasurable (fun z ↦ (Ioi (-(2 * a))).indicator
      (fun z ↦ dwq a z ^ 2 * Real.exp (-dwq a z ^ 2)) z) volume := fun a ↦
    ((by unfold dwq; fun_prop : Continuous fun z ↦ dwq a z ^ 2 * Real.exp (-dwq a z ^ 2))
      |>.aestronglyMeasurable).indicator measurableSet_Ioi
  have hmeasD : ∀ a : ℝ, AEStronglyMeasurable (fun z ↦ (Ioi (-(2 * a))).indicator
      (fun z ↦ Real.exp (-dwq a z ^ 2)) z) volume := fun a ↦
    ((by unfold dwq; fun_prop : Continuous fun z ↦ Real.exp (-dwq a z ^ 2))
      |>.aestronglyMeasurable).indicator measurableSet_Ioi
  have hnum : Tendsto (fun a ↦ ∫ z, (Ioi (-(2 * a))).indicator
      (fun z ↦ dwq a z ^ 2 * Real.exp (-dwq a z ^ 2)) z) atTop
      (𝓝 (∫ z : ℝ, z ^ 2 * Real.exp (-(z ^ 2)))) := by
    refine tendsto_integral_filter_of_dominated_convergence _
      (Filter.Eventually.of_forall hmeasN) ?_ hdomN (Filter.Eventually.of_forall hptN)
    filter_upwards [eventually_ge_atTop 1] with a ha
    exact Filter.Eventually.of_forall (hbN a ha)
  have hden : Tendsto (fun a ↦ ∫ z, (Ioi (-(2 * a))).indicator
      (fun z ↦ Real.exp (-dwq a z ^ 2)) z) atTop (𝓝 (∫ z : ℝ, Real.exp (-(z ^ 2)))) := by
    refine tendsto_integral_filter_of_dominated_convergence _
      (Filter.Eventually.of_forall hmeasD) ?_ hdomD (Filter.Eventually.of_forall hptD)
    filter_upwards [eventually_ge_atTop 1] with a ha
    exact Filter.Eventually.of_forall (hbD a ha)
  have hden0 : (∫ z : ℝ, Real.exp (-(z ^ 2))) ≠ 0 := by
    have hG0 := integrable_pow_mul_exp_neg_mul_pow one_pos 1 le_rfl 0
    simp only [mul_one, one_mul, pow_zero] at hG0
    refine ((integral_pos_iff_support_of_nonneg (fun z ↦ (Real.exp_pos _).le) hG0).mpr ?_).ne'
    have : Function.support (fun z : ℝ ↦ Real.exp (-(z ^ 2))) = Set.univ := by
      ext z
      simp [(Real.exp_pos _).ne']
    rw [this]
    simp
  have := hnum.div hden hden0
  rw [hlim] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with a ha
  simp only [Pi.div_apply]
  rw [doubleWell_eq_halfLine ha]

/-- **The merging-zeros crossover**: `mergeCross σ → 1/2` as `σ → ∞`. -/
theorem tendsto_mergeCross_atTop : Tendsto mergeCross atTop (𝓝 (1 / 2)) := by
  have h4 : Tendsto (fun σ : ℝ ↦ σ ^ 2 / 4) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).atTop_div_const (by norm_num)
  have := tendsto_doubleWell_atTop.comp h4
  refine this.congr' (Filter.Eventually.of_forall fun σ ↦ ?_)
  simp only [Function.comp]
  exact (mergeCross_eq_doubleWell σ).symm

theorem mergeCross_zero : mergeCross 0 = 1 / 4 := by
  rw [mergeCross_eq_doubleWell]
  norm_num
  exact doubleWell_zero

end Laplace.Multi
