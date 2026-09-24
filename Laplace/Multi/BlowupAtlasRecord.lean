/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BlowupSectorRecord

/-!
# The two-chart blow-up atlas of the plane

The two blow-up charts `(x, y) ↦ (x, xy)` (chart `A`) and `(x, y) ↦ (xy, y)` (chart `B`,
`BlowupSectorRecord`) of the plane, for the loss `F = z₀² + z₁²` and the truth coordinate `z₀`,
over the unit box `L' = {|z₀| ≤ 1, |z₁| ≤ 1}`, glued by the continuous partition of unity
`ω_A = clamp((4z₀² − z₁²)/(z₀² + z₁²))`, `ω_B = 1 − ω_A` (`ω_A` vanishes for `|z₁| ≥ 2|z₀|`,
`ω_B` for `|z₁| < |z₀|`). The pullbacks of the weights to the charts are continuous —
`ω_A(x, xy) = clamp((4 − y²)/(1 + y²))`, `ω_B(xy, y) = 1 − clamp((4x² − 1)/(x² + 1))` — which is
the point of the blow-up: the discontinuity of the angular weights at the origin is resolved. The
transport identity `∫_{L'} Ψ = ∫ Ψ(x, xy) ω_A |x| + ∫ Ψ(xy, y) ω_B |y|` (`at_transport`) is the
sum of the two changes of variables, each off a null line. Chart `A` has the pure truth monomial
`q = (1, 0)`, chart `B` the mixed one `q = (1, 1)`.
-/

open Real MeasureTheory Set
open scoped ENNReal Matrix

namespace Laplace.Multi.BlowupAtlas

open Laplace.Multi.ToyWall Laplace.Multi.BlowupSector

/-! ### The box and the partition of unity -/

/-- The unit box. -/
def atL' : Set (Fin 2 → ℝ) := {z | |z 0| ≤ 1 ∧ |z 1| ≤ 1}

theorem isClosed_atL' : IsClosed atL' := by
  unfold atL'
  rw [Set.ofPred_and]
  exact (isClosed_le (by fun_prop) continuous_const).inter
    (isClosed_le (by fun_prop) continuous_const)

theorem measurableSet_atL' : MeasurableSet atL' := isClosed_atL'.measurableSet

theorem bsL'_subset_atL' : bsL' ⊆ atL' := fun _ hz ↦ ⟨hz.1.trans hz.2, hz.2⟩

/-- Clamping to `[0, 1]`. -/
noncomputable def clamp (s : ℝ) : ℝ := min 1 (max 0 s)

theorem clamp_nonneg (s : ℝ) : 0 ≤ clamp s := le_min zero_le_one (le_max_left _ _)

theorem clamp_le_one (s : ℝ) : clamp s ≤ 1 := min_le_left _ _

theorem continuous_clamp : Continuous clamp :=
  continuous_const.min (continuous_const.max continuous_id)

theorem clamp_of_nonpos {s : ℝ} (hs : s ≤ 0) : clamp s = 0 := by
  unfold clamp
  rw [max_eq_left hs, min_eq_right zero_le_one]

theorem clamp_of_one_le {s : ℝ} (hs : 1 ≤ s) : clamp s = 1 := by
  unfold clamp
  rw [max_eq_right (zero_le_one.trans hs), min_eq_left hs]

/-- The weight of chart `A`. -/
noncomputable def wA (z : Fin 2 → ℝ) : ℝ := clamp ((4 * z 0 ^ 2 - z 1 ^ 2) / (z 0 ^ 2 + z 1 ^ 2))

/-- The weight of chart `B`. -/
noncomputable def wB (z : Fin 2 → ℝ) : ℝ := 1 - wA z

theorem wA_nonneg (z : Fin 2 → ℝ) : 0 ≤ wA z := clamp_nonneg _

theorem wA_le_one (z : Fin 2 → ℝ) : wA z ≤ 1 := clamp_le_one _

theorem wB_nonneg (z : Fin 2 → ℝ) : 0 ≤ wB z := by unfold wB; linarith [wA_le_one z]

theorem wA_add_wB (z : Fin 2 → ℝ) : wA z + wB z = 1 := by unfold wB; ring

theorem measurable_wA : Measurable wA :=
  continuous_clamp.measurable.comp (Measurable.div (by fun_prop) (by fun_prop))

theorem measurable_wB : Measurable wB := measurable_const.sub measurable_wA

theorem wA_eq_zero {z : Fin 2 → ℝ} (h : 2 * |z 0| ≤ |z 1|) : wA z = 0 := by
  unfold wA
  refine clamp_of_nonpos (div_nonpos_iff.mpr (Or.inr ⟨?_, by positivity⟩))
  have h2 : (2 * |z 0|) ^ 2 ≤ |z 1| ^ 2 := pow_le_pow_left₀ (by positivity) h 2
  rw [mul_pow, sq_abs, sq_abs] at h2
  linarith

theorem wB_eq_zero {z : Fin 2 → ℝ} (h : |z 1| < |z 0|) : wB z = 0 := by
  unfold wB wA
  have h0 : 0 < |z 0| := (abs_nonneg _).trans_lt h
  have h2 : |z 1| ^ 2 ≤ |z 0| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h.le 2
  rw [sq_abs, sq_abs] at h2
  have hpos : 0 < z 0 ^ 2 + z 1 ^ 2 := by
    have : 0 < z 0 ^ 2 := by rw [← sq_abs]; positivity
    positivity
  rw [clamp_of_one_le ((one_le_div hpos).mpr (by linarith)), sub_self]

/-- The pullback of `ω_A` to chart `A`. -/
noncomputable def gA (y : ℝ) : ℝ := clamp ((4 - y ^ 2) / (1 + y ^ 2))

/-- The pullback of `ω_B` to chart `B`. -/
noncomputable def hB (x : ℝ) : ℝ := 1 - clamp ((4 * x ^ 2 - 1) / (x ^ 2 + 1))

theorem continuous_gA : Continuous gA :=
  continuous_clamp.comp (Continuous.div (by fun_prop) (by fun_prop) fun y ↦ by positivity)

theorem continuous_hB : Continuous hB :=
  continuous_const.sub
    (continuous_clamp.comp (Continuous.div (by fun_prop) (by fun_prop) fun x ↦ by positivity))

theorem gA_nonneg (y : ℝ) : 0 ≤ gA y := clamp_nonneg _

theorem gA_le_one (y : ℝ) : gA y ≤ 1 := clamp_le_one _

theorem hB_nonneg (x : ℝ) : 0 ≤ hB x := by
  unfold hB; linarith [clamp_le_one ((4 * x ^ 2 - 1) / (x ^ 2 + 1))]

theorem hB_le_one (x : ℝ) : hB x ≤ 1 := by
  unfold hB; linarith [clamp_nonneg ((4 * x ^ 2 - 1) / (x ^ 2 + 1))]

theorem gA_zero : gA 0 = 1 := by
  unfold gA
  norm_num [clamp]

theorem hB_zero : hB 0 = 1 := by
  unfold hB
  norm_num [clamp]

theorem gA_eq_zero {y : ℝ} (hy : 2 ≤ |y|) : gA y = 0 := by
  unfold gA
  refine clamp_of_nonpos (div_nonpos_iff.mpr (Or.inr ⟨?_, by positivity⟩))
  have h2 : (2 : ℝ) ^ 2 ≤ |y| ^ 2 := pow_le_pow_left₀ (by norm_num) hy 2
  rw [sq_abs] at h2
  linarith

theorem hB_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : hB x = 0 := by
  unfold hB
  have h2 : (1 : ℝ) ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ (by norm_num) hx 2
  rw [sq_abs] at h2
  rw [clamp_of_one_le ((one_le_div (by positivity)).mpr (by linarith)), sub_self]

theorem wA_repA (u : Fin 2 → ℝ) (hu : u 0 ≠ 0) : wA ![u 0, u 0 * u 1] = gA (u 1) := by
  unfold wA gA
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have h : u 0 ^ 2 ≠ 0 := pow_ne_zero 2 hu
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

theorem wB_bsRep (u : Fin 2 → ℝ) (hu : u 1 ≠ 0) : wB (bsRep u) = hB (u 0) := by
  unfold wB wA hB
  congr 2
  rw [bsRep_zero, bsRep_one]
  have h : u 1 ^ 2 ≠ 0 := pow_ne_zero 2 hu
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-! ### Chart `A`: `(x, y) ↦ (x, xy)` -/

/-- The first blow-up chart. -/
noncomputable def repA (u : Fin 2 → ℝ) : Fin 2 → ℝ := ![u 0, u 0 * u 1]

theorem repA_zero (u : Fin 2 → ℝ) : repA u 0 = u 0 := rfl

theorem repA_one (u : Fin 2 → ℝ) : repA u 1 = u 0 * u 1 := rfl

theorem continuous_repA : Continuous repA := by
  refine continuous_pi fun j ↦ ?_
  revert j
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · simp only [repA_zero]
    fun_prop
  · simp only [repA_one]
    fun_prop

/-- The cutoff of chart `A`: `1` on the ball of radius `2`, vanishing off the ball of radius
`4`. -/
noncomputable def cutA (u : Fin 2 → ℝ) : ℝ := toyDens ((4 : ℝ)⁻¹ • u)

theorem cutA_nonneg (u : Fin 2 → ℝ) : 0 ≤ cutA u := toyDens_nonneg _

theorem cutA_le_one (u : Fin 2 → ℝ) : cutA u ≤ 1 := toyDens_le_one _

theorem continuous_cutA : Continuous cutA := continuous_toyDens.comp (continuous_const_smul _)

theorem norm_quarter_smul (u : Fin 2 → ℝ) : ‖(4 : ℝ)⁻¹ • u‖ = 4⁻¹ * ‖u‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by norm_num : (0 : ℝ) < 4)]

theorem cutA_eq_one {u : Fin 2 → ℝ} (hu : ‖u‖ ≤ 2) : cutA u = 1 :=
  toyDens_eq_one (by rw [norm_quarter_smul]; linarith)

theorem cutA_supp {u : Fin 2 → ℝ} (hu : cutA u ≠ 0) : ‖u‖ < 4 := by
  have := toyDens_supp hu
  rw [norm_quarter_smul] at this
  linarith

/-- The density of chart `A`: `ω_A(x, xy) |x|` with the cutoff. -/
noncomputable def densA (u : Fin 2 → ℝ) : ℝ := gA (u 1) * |u 0| * cutA u

theorem continuous_densA : Continuous densA :=
  ((continuous_gA.comp (continuous_apply 1)).mul (continuous_apply 0).abs).mul continuous_cutA

theorem densA_nonneg (u : Fin 2 → ℝ) : 0 ≤ densA u :=
  mul_nonneg (mul_nonneg (gA_nonneg _) (abs_nonneg _)) (cutA_nonneg u)

/-- The density of chart `B` in the atlas: `ω_B(xy, y) |y|` with the cutoff. -/
noncomputable def densB (u : Fin 2 → ℝ) : ℝ := hB (u 0) * bsDens u

theorem continuous_densB : Continuous densB :=
  (continuous_hB.comp (continuous_apply 0)).mul continuous_bsDens

theorem densB_nonneg (u : Fin 2 → ℝ) : 0 ≤ densB u :=
  mul_nonneg (hB_nonneg _) (mul_nonneg (abs_nonneg _) (bsCut_nonneg u))

/-- The domain of chart `A` off the exceptional line. -/
def TA : Set (Fin 2 → ℝ) := {u | |u 0| ≤ 1 ∧ |u 1| ≤ 2 ∧ |u 0 * u 1| ≤ 1 ∧ u 0 ≠ 0}

theorem measurableSet_TA : MeasurableSet TA := by
  unfold TA
  rw [Set.ofPred_and, Set.ofPred_and, Set.ofPred_and]
  exact (measurableSet_le (by fun_prop) measurable_const).inter
    ((measurableSet_le (by fun_prop) measurable_const).inter
      ((measurableSet_le (by fun_prop) measurable_const).inter
        (isOpen_ne_fun (continuous_apply 0) continuous_const).measurableSet))

/-- The Fréchet derivative of chart `A`. -/
noncomputable def derivA (u : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' !![(1 : ℝ), 0; u 1, u 0])

theorem derivA_apply (u v : Fin 2 → ℝ) : derivA u v = ![v 0, u 1 * v 0 + u 0 * v 1] := by
  unfold derivA
  rw [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]
  funext j
  revert j
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem hasFDerivAt_repA (u : Fin 2 → ℝ) : HasFDerivAt repA (derivA u) u := by
  refine hasFDerivAt_pi'.mpr ?_
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · refine ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) u).congr_fderiv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x ↦ ?_)
    · ext v
      simp [derivA_apply]
    · simp [repA_zero]
  · have h := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) u).mul
      (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) u)
    refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ ?_)
    · ext v
      simp [derivA_apply]
      ring
    · simp [repA_one]

theorem det_derivA (u : Fin 2 → ℝ) : (derivA u).det = u 0 := by
  rw [ContinuousLinearMap.det, derivA, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin',
    Matrix.det_fin_two_of]
  ring

theorem injOn_repA : InjOn repA TA := by
  intro u hu v hv h
  have h0 : u 0 = v 0 := by
    have := congrFun h 0
    simpa [repA_zero] using this
  have h1 : u 0 * u 1 = v 0 * v 1 := by
    have := congrFun h 1
    simpa [repA_one] using this
  rw [← h0] at h1
  have hu0 : u 0 ≠ 0 := hu.2.2.2
  funext j
  revert j
  refine Fin.forall_fin_two.mpr ⟨h0, ?_⟩
  exact mul_left_cancel₀ hu0 h1

theorem image_repA : repA '' TA = (atL' ∩ {z | |z 1| ≤ 2 * |z 0|}) ∩ {z | z 0 ≠ 0} := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨⟨hu.1, hu.2.2.1⟩, ?_⟩, hu.2.2.2⟩
    change |u 0 * u 1| ≤ 2 * |u 0|
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hu.2.1 (abs_nonneg _)
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, hz⟩
    have hz0 : z 0 ≠ 0 := hz
    have h2' : |z 1| ≤ 2 * |z 0| := h2
    have habs : 0 < |z 0| := abs_pos.mpr hz0
    refine ⟨![z 0, z 1 / z 0], ?_, ?_⟩
    · change |(![z 0, z 1 / z 0] : Fin 2 → ℝ) 0| ≤ 1 ∧ |(![z 0, z 1 / z 0] : Fin 2 → ℝ) 1| ≤ 2 ∧
        |(![z 0, z 1 / z 0] : Fin 2 → ℝ) 0 * (![z 0, z 1 / z 0] : Fin 2 → ℝ) 1| ≤ 1 ∧
        (![z 0, z 1 / z 0] : Fin 2 → ℝ) 0 ≠ 0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_div]
      refine ⟨h0, ?_, ?_, hz0⟩
      · rw [div_le_iff₀ habs]
        exact h2'
      · rw [mul_div_cancel₀ _ hz0]
        exact h1
    · funext j
      revert j
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · rw [repA_zero]
        simp
      · rw [repA_one]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        exact mul_div_cancel₀ _ hz0

theorem volume_line0 : volume {z : Fin 2 → ℝ | z 0 = 0} = 0 := by
  have e : {z : Fin 2 → ℝ | z 0 = 0} =
      (LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0) : Set (Fin 2 → ℝ)) := by
    ext z
    simp [LinearMap.mem_ker]
  rw [e]
  refine Measure.addHaar_submodule volume _ fun h ↦ ?_
  rw [Submodule.eq_top_iff'] at h
  have := h (Pi.single 0 1)
  simp [LinearMap.mem_ker] at this

theorem norm_le_two_of_mem_TA {u : Fin 2 → ℝ} (hu : u ∈ TA) : ‖u‖ ≤ 2 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · rw [Real.norm_eq_abs]; exact hu.1.trans (by norm_num)
  · rw [Real.norm_eq_abs]; exact hu.2.1

theorem TA_subset_domA {u : Fin 2 → ℝ} (hu : u ∈ TA) :
    u ∈ Metric.closedBall (0 : Fin 2 → ℝ) 4 ∩ repA ⁻¹' atL' := by
  refine ⟨mem_closedBall_zero_iff.mpr ((norm_le_two_of_mem_TA hu).trans (by norm_num)), ?_⟩
  change |repA u 0| ≤ 1 ∧ |repA u 1| ≤ 1
  rw [repA_zero, repA_one]
  exact ⟨hu.1, hu.2.2.1⟩

/-- **The transport identity of chart `A`** for the weight `ω_A`. -/
theorem transportA (Ψ : (Fin 2 → ℝ) → ℝ≥0∞) :
    ∫⁻ z in atL', Ψ z * ENNReal.ofReal (wA z) =
      ∫⁻ u in Metric.closedBall (0 : Fin 2 → ℝ) 4 ∩ repA ⁻¹' atL',
        Ψ (repA u) * ENNReal.ofReal (densA u) := by
  have hdom : MeasurableSet (Metric.closedBall (0 : Fin 2 → ℝ) 4 ∩ repA ⁻¹' atL') :=
    Metric.isClosed_closedBall.measurableSet.inter
      (measurableSet_atL'.preimage continuous_repA.measurable)
  have hS : MeasurableSet ((atL' ∩ {z : Fin 2 → ℝ | |z 1| ≤ 2 * |z 0|}) ∩ {z | z 0 ≠ 0}) :=
    (measurableSet_atL'.inter (measurableSet_le (by fun_prop) (by fun_prop))).inter
      (isOpen_ne_fun (continuous_apply 0) continuous_const).measurableSet
  -- restrict to the image of `TA`
  have h1 : ∫⁻ z in atL', Ψ z * ENNReal.ofReal (wA z) =
      ∫⁻ z in (atL' ∩ {z : Fin 2 → ℝ | |z 1| ≤ 2 * |z 0|}) ∩ {z | z 0 ≠ 0},
        Ψ z * ENNReal.ofReal (wA z) := by
    rw [← lintegral_indicator measurableSet_atL', ← lintegral_indicator hS]
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ z, z ∉ {z : Fin 2 → ℝ | z 0 = 0} := compl_mem_ae_iff.mpr volume_line0
    filter_upwards [hae] with z hz
    by_cases hL : z ∈ atL'
    · rw [Set.indicator_of_mem hL]
      by_cases hsec : |z 1| ≤ 2 * |z 0|
      · have hmem : z ∈ (atL' ∩ {z : Fin 2 → ℝ | |z 1| ≤ 2 * |z 0|}) ∩ {z | z 0 ≠ 0} :=
          ⟨⟨hL, hsec⟩, hz⟩
        rw [Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem (fun h ↦ hsec h.1.2), wA_eq_zero (le_of_lt (not_le.mp hsec)),
          ENNReal.ofReal_zero, mul_zero]
    · rw [Set.indicator_of_notMem hL, Set.indicator_of_notMem (fun h ↦ hL h.1.1)]
  rw [h1, ← image_repA, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_TA
    (fun u _ ↦ (hasFDerivAt_repA u).hasFDerivWithinAt) injOn_repA, ← lintegral_indicator
    measurableSet_TA, ← lintegral_indicator hdom]
  refine lintegral_congr fun u ↦ ?_
  by_cases hu : u ∈ TA
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (TA_subset_domA hu), det_derivA, densA,
      cutA_eq_one (norm_le_two_of_mem_TA hu), mul_one]
    have hw : wA (repA u) = gA (u 1) := wA_repA u hu.2.2.2
    rw [hw, mul_comm (ENNReal.ofReal |u 0|), mul_assoc, ← ENNReal.ofReal_mul (gA_nonneg _)]
  · rw [Set.indicator_of_notMem hu]
    by_cases hd : u ∈ Metric.closedBall (0 : Fin 2 → ℝ) 4 ∩ repA ⁻¹' atL'
    · rw [Set.indicator_of_mem hd]
      have hL : |repA u 0| ≤ 1 ∧ |repA u 1| ≤ 1 := hd.2
      rw [repA_zero, repA_one] at hL
      have h0 : u 0 = 0 ∨ 2 < |u 1| := by
        by_contra h
        push Not at h
        exact hu ⟨hL.1, h.2, hL.2, h.1⟩
      rcases h0 with h0 | h0
      · simp [densA, h0]
      · simp [densA, gA_eq_zero h0.le]
    · rw [Set.indicator_of_notMem hd]

/-- **The transport identity of chart `B`** for the weight `ω_B`, from the sector identity. -/
theorem transportB (Ψ : (Fin 2 → ℝ) → ℝ≥0∞) :
    ∫⁻ z in atL', Ψ z * ENNReal.ofReal (wB z) =
      ∫⁻ u in Metric.closedBall (0 : Fin 2 → ℝ) 2 ∩ bsRep ⁻¹' atL',
        Ψ (bsRep u) * ENNReal.ofReal (densB u) := by
  have hdom : MeasurableSet (Metric.closedBall (0 : Fin 2 → ℝ) 2 ∩ bsRep ⁻¹' atL') :=
    Metric.isClosed_closedBall.measurableSet.inter
      (measurableSet_atL'.preimage continuous_bsRep.measurable)
  have hdom' : MeasurableSet (Metric.closedBall (0 : Fin 2 → ℝ) 2 ∩ bsRep ⁻¹' bsL') :=
    Metric.isClosed_closedBall.measurableSet.inter
      (measurableSet_bsL'.preimage continuous_bsRep.measurable)
  -- restrict to the sector
  have h1 : ∫⁻ z in atL', Ψ z * ENNReal.ofReal (wB z) =
      ∫⁻ z in bsL', Ψ z * ENNReal.ofReal (wB z) := by
    rw [← lintegral_indicator measurableSet_atL', ← lintegral_indicator measurableSet_bsL']
    refine lintegral_congr fun z ↦ ?_
    by_cases hL : z ∈ atL'
    · rw [Set.indicator_of_mem hL]
      by_cases hb : z ∈ bsL'
      · rw [Set.indicator_of_mem hb]
      · rw [Set.indicator_of_notMem hb]
        have : |z 1| < |z 0| := by
          by_contra h
          exact hb ⟨not_lt.mp h, hL.2⟩
        rw [wB_eq_zero this, ENNReal.ofReal_zero, mul_zero]
    · rw [Set.indicator_of_notMem hL, Set.indicator_of_notMem (fun h ↦ hL (bsL'_subset_atL' h))]
  rw [h1, bs_transport (fun z ↦ Ψ z * ENNReal.ofReal (wB z)), ← lintegral_indicator hdom',
    ← lintegral_indicator hdom]
  refine lintegral_congr fun u ↦ ?_
  by_cases hu1 : u 1 = 0
  · have hz : bsDens u = 0 := by simp [bsDens, hu1]
    have hz' : densB u = 0 := by simp [densB, hz]
    by_cases hd : u ∈ Metric.closedBall (0 : Fin 2 → ℝ) 2 ∩ bsRep ⁻¹' bsL'
    · rw [Set.indicator_of_mem hd, hz, ENNReal.ofReal_zero, mul_zero]
      by_cases hd' : u ∈ Metric.closedBall (0 : Fin 2 → ℝ) 2 ∩ bsRep ⁻¹' atL'
      · rw [Set.indicator_of_mem hd', hz', ENNReal.ofReal_zero, mul_zero]
      · rw [Set.indicator_of_notMem hd']
    · rw [Set.indicator_of_notMem hd]
      by_cases hd' : u ∈ Metric.closedBall (0 : Fin 2 → ℝ) 2 ∩ bsRep ⁻¹' atL'
      · rw [Set.indicator_of_mem hd', hz', ENNReal.ofReal_zero, mul_zero]
      · rw [Set.indicator_of_notMem hd']
  · have hw : wB (bsRep u) = hB (u 0) := wB_bsRep u hu1
    by_cases hd : u ∈ Metric.closedBall (0 : Fin 2 → ℝ) 2 ∩ bsRep ⁻¹' bsL'
    · have hd' : u ∈ Metric.closedBall (0 : Fin 2 → ℝ) 2 ∩ bsRep ⁻¹' atL' :=
        ⟨hd.1, bsL'_subset_atL' hd.2⟩
      rw [Set.indicator_of_mem hd, Set.indicator_of_mem hd', hw, densB, mul_assoc,
        ← ENNReal.ofReal_mul (hB_nonneg _)]
    · rw [Set.indicator_of_notMem hd]
      by_cases hd' : u ∈ Metric.closedBall (0 : Fin 2 → ℝ) 2 ∩ bsRep ⁻¹' atL'
      · rw [Set.indicator_of_mem hd']
        have hL : |bsRep u 0| ≤ 1 ∧ |bsRep u 1| ≤ 1 := hd'.2
        rw [bsRep_zero, bsRep_one] at hL
        have hnot : ¬ (|u 0 * u 1| ≤ |u 1|) := by
          intro h
          exact hd ⟨hd'.1, show |bsRep u 0| ≤ |bsRep u 1| ∧ |bsRep u 1| ≤ 1 from
            ⟨by rw [bsRep_zero, bsRep_one]; exact h, by rw [bsRep_one]; exact hL.2⟩⟩
        have h1 : 1 ≤ |u 0| := by
          by_contra h
          push Not at h
          exact hnot (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) h.le)
        simp [densB, hB_eq_zero h1]
      · rw [Set.indicator_of_notMem hd']

/-- **The transport identity of the atlas.** -/
theorem at_transport (Ψ : (Fin 2 → ℝ) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ z in atL', Ψ z =
      (∫⁻ u in Metric.closedBall (0 : Fin 2 → ℝ) 4 ∩ repA ⁻¹' atL',
        Ψ (repA u) * ENNReal.ofReal (densA u)) +
      ∫⁻ u in Metric.closedBall (0 : Fin 2 → ℝ) 2 ∩ bsRep ⁻¹' atL',
        Ψ (bsRep u) * ENNReal.ofReal (densB u) := by
  have hm : Measurable fun z ↦ Ψ z * ENNReal.ofReal (wA z) :=
    hΨ.mul (ENNReal.measurable_ofReal.comp measurable_wA)
  rw [← transportA Ψ, ← transportB Ψ, ← lintegral_add_left hm]
  refine setLIntegral_congr_fun measurableSet_atL' fun z _ ↦ ?_
  rw [← mul_add, ← ENNReal.ofReal_add (wA_nonneg z) (wB_nonneg z), wA_add_wB, ENNReal.ofReal_one,
    mul_one]

/-! ### The record -/

theorem truthA (u : Fin 2 → ℝ) : repA u 0 = truthMono 1 ![1, 0] u := by
  simp [truthMono, repA_zero, Fin.prod_univ_two]

theorem truthB (u : Fin 2 → ℝ) : bsRep u 0 = truthMono 1 ![1, 1] u := by
  simp [truthMono, bsRep_zero, Fin.prod_univ_two]

/-- The wall data of the two-chart blow-up atlas over the unit box. -/
noncomputable def atData : WallChartsData 1 0 atL' where
  ι := Fin 2
  rep := ![repA, bsRep]
  rep_cont := Fin.forall_fin_two.mpr ⟨continuous_repA, continuous_bsRep⟩
  ρ := ![4, 2]
  ρ_pos := Fin.forall_fin_two.mpr ⟨by norm_num, by norm_num⟩
  dom := fun i ↦ Metric.closedBall (0 : Fin 2 → ℝ) (![4, 2] i) ∩ (![repA, bsRep] i) ⁻¹' atL'
  dom_eq := fun _ ↦ rfl
  dom_meas := Fin.forall_fin_two.mpr
    ⟨Metric.isClosed_closedBall.measurableSet.inter
      (measurableSet_atL'.preimage continuous_repA.measurable),
     Metric.isClosed_closedBall.measurableSet.inter
      (measurableSet_atL'.preimage continuous_bsRep.measurable)⟩
  dens := ![densA, densB]
  dens_cont := Fin.forall_fin_two.mpr ⟨continuous_densA, continuous_densB⟩
  dens_nonneg := Fin.forall_fin_two.mpr ⟨densA_nonneg, densB_nonneg⟩
  dens_supp := Fin.forall_fin_two.mpr
    ⟨fun u hu ↦ mem_ball_zero_iff.mpr (cutA_supp (right_ne_zero_of_mul hu)),
     fun u hu ↦ mem_ball_zero_iff.mpr
      (bsCut_supp (right_ne_zero_of_mul (right_ne_zero_of_mul hu)))⟩
  S := fun _ ↦ 1
  S_ne := fun _ ↦ one_ne_zero
  q := ![![1, 0], ![1, 1]]
  k := ![0, 1]
  q_pos := Fin.forall_fin_two.mpr ⟨by simp, by simp⟩
  truth := Fin.forall_fin_two.mpr ⟨fun u _ ↦ truthA u, fun u _ ↦ truthB u⟩
  transport := fun Ψ hΨ ↦ by
    rw [Fin.sum_univ_two]
    exact at_transport Ψ hΨ

theorem atData_rep_zero (u : Fin 2 → ℝ) : atData.rep (0 : Fin 2) u = repA u := rfl
theorem atData_rep_one (u : Fin 2 → ℝ) : atData.rep (1 : Fin 2) u = bsRep u := rfl
theorem atData_dens_zero (u : Fin 2 → ℝ) : atData.dens (0 : Fin 2) u = densA u := rfl
theorem atData_dens_one (u : Fin 2 → ℝ) : atData.dens (1 : Fin 2) u = densB u := rfl

/-- The index of chart `A`. -/
def iA : atData.ι := (0 : Fin 2)

/-- The index of chart `B`. -/
def iB : atData.ι := (1 : Fin 2)

instance : DecidableEq atData.ι := inferInstanceAs (DecidableEq (Fin 2))

theorem iB_ne_iA : iB ≠ iA := by decide

theorem forall_index {P : atData.ι → Prop} : (∀ i, P i) ↔ P iA ∧ P iB :=
  Fin.forall_fin_two

theorem atData_rep_iA (u : Fin 2 → ℝ) : atData.rep iA u = repA u := rfl
theorem atData_rep_iB (u : Fin 2 → ℝ) : atData.rep iB u = bsRep u := rfl
theorem atData_dens_iA (u : Fin 2 → ℝ) : atData.dens iA u = densA u := rfl
theorem atData_dens_iB (u : Fin 2 → ℝ) : atData.dens iB u = densB u := rfl
theorem atData_ρ_iA : atData.ρ iA = 4 := rfl
theorem atData_ρ_iB : atData.ρ iB = 2 := rfl
theorem atData_S (i : atData.ι) : atData.S i = 1 := rfl
theorem atData_q_iA : atData.q iA = ![1, 0] := rfl
theorem atData_q_iB : atData.q iB = ![1, 1] := rfl
theorem atData_k_iA : atData.k iA = 0 := rfl
theorem atData_k_iB : atData.k iB = 1 := rfl

/-- The phase data of the atlas: `F ∘ rep_A = (1 + y²) x²` with density `ω_A |x|`,
`F ∘ rep_B = (1 + x²) y²` with density `ω_B |y|`. -/
noncomputable def atPhase : atData.Phase bsF where
  kF := ![![2, 0], ![0, 2]]
  hJ := ![![1, 0], ![0, 1]]
  a := ![fun u ↦ 1 + u 1 ^ 2, fun u ↦ 1 + u 0 ^ 2]
  b := fun _ _ ↦ 1
  wt := ![fun u ↦ gA (u 1) * cutA u, fun u ↦ hB (u 0) * bsCut u]
  a_cont := Fin.forall_fin_two.mpr
    ⟨show Continuous fun u : Fin 2 → ℝ ↦ 1 + u 1 ^ 2 by fun_prop,
     show Continuous fun u : Fin 2 → ℝ ↦ 1 + u 0 ^ 2 by fun_prop⟩
  b_cont := fun _ ↦ continuous_const
  wt_cont := Fin.forall_fin_two.mpr
    ⟨(continuous_gA.comp (continuous_apply 1)).mul continuous_cutA,
     (continuous_hB.comp (continuous_apply 0)).mul continuous_bsCut⟩
  wt_nonneg := Fin.forall_fin_two.mpr
    ⟨fun u ↦ mul_nonneg (gA_nonneg _) (cutA_nonneg u),
     fun u ↦ mul_nonneg (hB_nonneg _) (bsCut_nonneg u)⟩
  wt_le_one := Fin.forall_fin_two.mpr
    ⟨fun u ↦ mul_le_one₀ (gA_le_one _) (cutA_nonneg u) (cutA_le_one u),
     fun u ↦ mul_le_one₀ (hB_le_one _) (bsCut_nonneg u) (bsCut_le_one u)⟩
  ma := fun _ ↦ 1
  Ma := ![17, 5]
  mb := fun _ ↦ 1
  Mb := fun _ ↦ 1
  ma_pos := fun _ ↦ one_pos
  mb_pos := fun _ ↦ one_pos
  a_bounds := Fin.forall_fin_two.mpr ⟨fun u hu ↦ by
      have h1 : |u 1| ≤ 4 := by
        have := norm_le_pi_norm u 1
        rw [Real.norm_eq_abs] at this
        exact this.trans (mem_closedBall_zero_iff.mp hu : ‖u‖ ≤ 4)
      have h2 : u 1 ^ 2 ≤ 16 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg (u 1)]
      simp only [Matrix.cons_val_zero]
      constructor
      · rw [abs_of_nonneg (by positivity)]
        nlinarith [sq_nonneg (u 1)]
      · rw [abs_of_nonneg (by positivity)]
        linarith,
    fun u hu ↦ by
      have h1 : |u 0| ≤ 2 := by
        have := norm_le_pi_norm u 0
        rw [Real.norm_eq_abs] at this
        exact this.trans (mem_closedBall_zero_iff.mp hu : ‖u‖ ≤ 2)
      have h2 : u 0 ^ 2 ≤ 4 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg (u 0)]
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
      constructor
      · rw [abs_of_nonneg (by positivity)]
        nlinarith [sq_nonneg (u 0)]
      · rw [abs_of_nonneg (by positivity)]
        linarith⟩
  b_bounds := fun _ _ _ ↦ by simp
  phase := Fin.forall_fin_two.mpr ⟨fun u _ ↦ by
      simp only [atData_rep_zero, Matrix.cons_val_zero, bsF, repA_zero, repA_one,
        Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.succ_zero_eq_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, pow_zero, mul_one]
      ring,
    fun u _ ↦ by
      simp only [atData_rep_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, bsF, bsRep_zero,
        bsRep_one, Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.succ_zero_eq_one,
        Matrix.cons_val_zero, pow_zero, one_mul, mul_one]
      ring⟩
  dens_eq := Fin.forall_fin_two.mpr ⟨fun u _ ↦ by
      simp only [atData_dens_zero, Matrix.cons_val_zero, densA, Fin.prod_univ_succ,
        Fin.prod_univ_zero, Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        pow_zero, pow_one, mul_one, one_mul]
      ring,
    fun u _ ↦ by
      simp only [atData_dens_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, densB, bsDens,
        Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.succ_zero_eq_one, Matrix.cons_val_zero,
        pow_zero, pow_one, one_mul, mul_one]
      ring⟩

end Laplace.Multi.BlowupAtlas
