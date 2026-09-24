/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ToyWallRecord

/-!
# A blow-up chart with a mixed truth monomial

The second blow-up chart `(x, y) ↦ (xy, y)` of the plane, for the loss `F = z₀² + z₁²` and the
truth coordinate `z₀`, over the sector `L' = {|z₀| ≤ |z₁| ≤ 1}`. In the chart the loss is
`y² (1 + x²)` and the truth coordinate is the *mixed* monomial `x y`, so the truth exponent is
`q = (1, 1)` and the transverse exponent `Q = 1` is nonzero — the case of the cut variable that the
identity chart of `ToyWallRecord` cannot exercise. The chart covers the sector minus the null line
`z₁ = 0`, so a single chart with weight `1` on the unit box suffices; the transport identity is the
change of variables `∫_{L'} Ψ = ∫ Ψ(xy, y) |y| dx dy` (`bs_transport`, from Mathlib's
`lintegral_image_eq_lintegral_abs_det_fderiv_mul`).

Constants of the chart: `q_k = 1` (solving for `y`), `Q = 1`, `k_F = (0, 2)`, `h_J = (0, 1)`,
`a = 1 + x²`, `b = 1`.
-/

open Real MeasureTheory Set
open scoped ENNReal Matrix

namespace Laplace.Multi.BlowupSector

open Laplace.Multi.ToyWall

/-- The loss `z₀² + z₁²`. -/
noncomputable def bsF (z : Fin 2 → ℝ) : ℝ := z 0 ^ 2 + z 1 ^ 2

/-- The blow-up chart `(x, y) ↦ (xy, y)`. -/
noncomputable def bsRep (u : Fin 2 → ℝ) : Fin 2 → ℝ := ![u 0 * u 1, u 1]

theorem bsRep_zero (u : Fin 2 → ℝ) : bsRep u 0 = u 0 * u 1 := rfl

theorem bsRep_one (u : Fin 2 → ℝ) : bsRep u 1 = u 1 := rfl

theorem continuous_bsRep : Continuous bsRep := by
  refine continuous_pi fun j ↦ ?_
  revert j
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · simp only [bsRep_zero]
    fun_prop
  · simp only [bsRep_one]
    fun_prop

/-- The sector `|z₀| ≤ |z₁| ≤ 1`. -/
def bsL' : Set (Fin 2 → ℝ) := {z | |z 0| ≤ |z 1| ∧ |z 1| ≤ 1}

theorem isClosed_bsL' : IsClosed bsL' := by
  unfold bsL'
  rw [Set.ofPred_and]
  exact (isClosed_le (by fun_prop) (by fun_prop)).inter (isClosed_le (by fun_prop) continuous_const)

theorem measurableSet_bsL' : MeasurableSet bsL' := isClosed_bsL'.measurableSet

/-- The cutoff: `1` on the unit ball, vanishing off the ball of radius `2`. -/
noncomputable def bsCut (u : Fin 2 → ℝ) : ℝ := toyDens ((2 : ℝ)⁻¹ • u)

theorem bsCut_nonneg (u : Fin 2 → ℝ) : 0 ≤ bsCut u := toyDens_nonneg _

theorem bsCut_le_one (u : Fin 2 → ℝ) : bsCut u ≤ 1 := toyDens_le_one _

theorem continuous_bsCut : Continuous bsCut :=
  continuous_toyDens.comp (continuous_const_smul _)

theorem norm_half_smul (u : Fin 2 → ℝ) : ‖(2 : ℝ)⁻¹ • u‖ = 2⁻¹ * ‖u‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_two]

theorem bsCut_eq_one {u : Fin 2 → ℝ} (hu : ‖u‖ ≤ 1) : bsCut u = 1 :=
  toyDens_eq_one (by rw [norm_half_smul]; linarith)

theorem bsCut_supp {u : Fin 2 → ℝ} (hu : bsCut u ≠ 0) : ‖u‖ < 2 := by
  have := toyDens_supp hu
  rw [norm_half_smul] at this
  linarith

/-- The chart density `|y|` times the cutoff. -/
noncomputable def bsDens (u : Fin 2 → ℝ) : ℝ := |u 1| * bsCut u

theorem continuous_bsDens : Continuous bsDens :=
  ((continuous_apply 1).abs).mul continuous_bsCut

/-! ### The change of variables -/

/-- The chart domain off the exceptional line: `|x| ≤ 1`, `0 < |y| ≤ 1`. -/
def bsT : Set (Fin 2 → ℝ) := {u | |u 0| ≤ 1 ∧ |u 1| ≤ 1 ∧ u 1 ≠ 0}

theorem measurableSet_bsT : MeasurableSet bsT := by
  unfold bsT
  rw [Set.ofPred_and, Set.ofPred_and]
  exact (measurableSet_le (by fun_prop) measurable_const).inter
    ((measurableSet_le (by fun_prop) measurable_const).inter
      (isOpen_ne_fun (continuous_apply 1) continuous_const).measurableSet)

/-- The Jacobian matrix of the chart. -/
noncomputable def bsJac (u : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![u 1, u 0; 0, 1]

/-- The Fréchet derivative of the chart. -/
noncomputable def bsDeriv (u : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (bsJac u))

theorem bsDeriv_apply (u v : Fin 2 → ℝ) :
    bsDeriv u v = ![u 1 * v 0 + u 0 * v 1, v 1] := by
  unfold bsDeriv bsJac
  rw [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]
  funext j
  revert j
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem hasFDerivAt_bsRep (u : Fin 2 → ℝ) : HasFDerivAt bsRep (bsDeriv u) u := by
  refine hasFDerivAt_pi'.mpr ?_
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · have h := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) u).mul
      (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) u)
    refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ ?_)
    · ext v
      simp [bsDeriv_apply]
      ring
    · simp [bsRep_zero]
  · refine ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) u).congr_fderiv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x ↦ ?_)
    · ext v
      simp [bsDeriv_apply]
    · simp [bsRep_one]

theorem det_bsDeriv (u : Fin 2 → ℝ) : (bsDeriv u).det = u 1 := by
  rw [ContinuousLinearMap.det, bsDeriv, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin',
    bsJac, Matrix.det_fin_two_of]
  ring

theorem bs_injOn : InjOn bsRep bsT := by
  intro u hu v hv h
  have h1 : u 1 = v 1 := by
    have := congrFun h 1
    simpa [bsRep_one] using this
  have h0 : u 0 * u 1 = v 0 * v 1 := by
    have := congrFun h 0
    simpa [bsRep_zero] using this
  rw [← h1] at h0
  have hu1 : u 1 ≠ 0 := hu.2.2
  funext j
  revert j
  refine Fin.forall_fin_two.mpr ⟨?_, h1⟩
  exact mul_right_cancel₀ hu1 h0

theorem bs_image : bsRep '' bsT = bsL' ∩ {z | z 1 ≠ 0} := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨?_, hu.2.1⟩, hu.2.2⟩
    rw [bsRep_zero, bsRep_one, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hu.1
  · rintro ⟨⟨h0, h1⟩, hz⟩
    have hz1 : z 1 ≠ 0 := hz
    refine ⟨![z 0 / z 1, z 1], ⟨?_, ?_, ?_⟩, ?_⟩
    · simp only [Matrix.cons_val_zero, abs_div]
      exact div_le_one_of_le₀ h0 (abs_nonneg _)
    · simpa using h1
    · simpa using hz1
    · funext j
      revert j
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · rw [bsRep_zero]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        exact div_mul_cancel₀ _ hz1
      · rw [bsRep_one]
        simp

theorem volume_line : volume {z : Fin 2 → ℝ | z 1 = 0} = 0 := by
  have e : {z : Fin 2 → ℝ | z 1 = 0} =
      (LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1) : Set (Fin 2 → ℝ)) := by
    ext z
    simp [LinearMap.mem_ker]
  rw [e]
  refine Measure.addHaar_submodule volume _ fun h ↦ ?_
  rw [Submodule.eq_top_iff'] at h
  have := h (Pi.single 1 1)
  simp [LinearMap.mem_ker] at this

theorem norm_le_one_of_mem_bsT {u : Fin 2 → ℝ} (hu : u ∈ bsT) : ‖u‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · rw [Real.norm_eq_abs]; exact hu.1
  · rw [Real.norm_eq_abs]; exact hu.2.1

theorem bsT_subset_dom {u : Fin 2 → ℝ} (hu : u ∈ bsT) :
    u ∈ Metric.closedBall (0 : Fin 2 → ℝ) 2 ∩ bsRep ⁻¹' bsL' := by
  refine ⟨mem_closedBall_zero_iff.mpr ((norm_le_one_of_mem_bsT hu).trans (by norm_num)), ?_⟩
  change |bsRep u 0| ≤ |bsRep u 1| ∧ |bsRep u 1| ≤ 1
  rw [bsRep_zero, bsRep_one, abs_mul]
  exact ⟨mul_le_of_le_one_left (abs_nonneg _) hu.1, hu.2.1⟩

theorem mem_bsT_of_mem_dom {u : Fin 2 → ℝ}
    (hd : u ∈ Metric.closedBall (0 : Fin 2 → ℝ) 2 ∩ bsRep ⁻¹' bsL') (hu1 : u 1 ≠ 0) : u ∈ bsT := by
  have h : |bsRep u 0| ≤ |bsRep u 1| ∧ |bsRep u 1| ≤ 1 := hd.2
  rw [bsRep_zero, bsRep_one, abs_mul] at h
  refine ⟨?_, h.2, hu1⟩
  have hpos : 0 < |u 1| := abs_pos.mpr hu1
  exact le_of_mul_le_mul_right (by linarith [h.1]) hpos

/-- **The transport identity of the blow-up chart**: `∫_{L'} Ψ = ∫ Ψ(xy, y) |y| dx dy`. -/
theorem bs_transport (Ψ : (Fin 2 → ℝ) → ℝ≥0∞) :
    ∫⁻ z in bsL', Ψ z =
      ∫⁻ u in Metric.closedBall (0 : Fin 2 → ℝ) 2 ∩ bsRep ⁻¹' bsL',
        Ψ (bsRep u) * ENNReal.ofReal (bsDens u) := by
  have hdom : MeasurableSet (Metric.closedBall (0 : Fin 2 → ℝ) 2 ∩ bsRep ⁻¹' bsL') :=
    Metric.isClosed_closedBall.measurableSet.inter
      (measurableSet_bsL'.preimage continuous_bsRep.measurable)
  have h1 : ∫⁻ z in bsL', Ψ z = ∫⁻ z in bsL' ∩ {z | z 1 ≠ 0}, Ψ z := by
    refine setLIntegral_congr ?_
    have hae : ∀ᵐ z, z ∉ {z : Fin 2 → ℝ | z 1 = 0} := compl_mem_ae_iff.mpr volume_line
    filter_upwards [hae] with z hz
    rw [eq_iff_iff]
    exact ⟨fun h ↦ ⟨h, hz⟩, fun h ↦ h.1⟩
  rw [h1, ← bs_image, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_bsT
    (fun u _ ↦ (hasFDerivAt_bsRep u).hasFDerivWithinAt) bs_injOn Ψ, ← lintegral_indicator
    measurableSet_bsT, ← lintegral_indicator hdom]
  refine lintegral_congr fun u ↦ ?_
  by_cases hu : u ∈ bsT
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (bsT_subset_dom hu), det_bsDeriv, bsDens,
      bsCut_eq_one (norm_le_one_of_mem_bsT hu), mul_one, mul_comm]
  · rw [Set.indicator_of_notMem hu]
    by_cases hd : u ∈ Metric.closedBall (0 : Fin 2 → ℝ) 2 ∩ bsRep ⁻¹' bsL'
    · rw [Set.indicator_of_mem hd]
      have h0 : u 1 = 0 := by
        by_contra h
        exact hu (mem_bsT_of_mem_dom hd h)
      simp [bsDens, h0]
    · rw [Set.indicator_of_notMem hd]

/-! ### The record -/

/-- The wall data of the blow-up chart over the sector. -/
noncomputable def bsData : WallChartsData 1 0 bsL' where
  ι := Unit
  rep := fun _ ↦ bsRep
  rep_cont := fun _ ↦ continuous_bsRep
  ρ := fun _ ↦ 2
  ρ_pos := fun _ ↦ two_pos
  dom := fun _ ↦ Metric.closedBall (0 : Fin 2 → ℝ) 2 ∩ bsRep ⁻¹' bsL'
  dom_eq := fun _ ↦ rfl
  dom_meas := fun _ ↦ Metric.isClosed_closedBall.measurableSet.inter
    (measurableSet_bsL'.preimage continuous_bsRep.measurable)
  dens := fun _ ↦ bsDens
  dens_cont := fun _ ↦ continuous_bsDens
  dens_nonneg := fun _ u ↦ mul_nonneg (abs_nonneg _) (bsCut_nonneg u)
  dens_supp := fun _ u hu ↦ mem_ball_zero_iff.mpr (bsCut_supp (right_ne_zero_of_mul hu))
  S := fun _ ↦ 1
  S_ne := fun _ ↦ one_ne_zero
  q := fun _ ↦ ![1, 1]
  k := fun _ ↦ 1
  q_pos := fun _ ↦ by simp
  truth := fun _ u _ ↦ by
    simp [truthMono, bsRep_zero, Fin.prod_univ_two]
  transport := fun Ψ _ ↦ by
    rw [Fintype.sum_unique]
    exact bs_transport Ψ

theorem bsData_rep (i : bsData.ι) (u : Fin 2 → ℝ) : bsData.rep i u = bsRep u := rfl
theorem bsData_dens (i : bsData.ι) (u : Fin 2 → ℝ) : bsData.dens i u = bsDens u := rfl
theorem bsData_ρ (i : bsData.ι) : bsData.ρ i = 2 := rfl
theorem bsData_S (i : bsData.ι) : bsData.S i = 1 := rfl
theorem bsData_q (i : bsData.ι) : bsData.q i = ![1, 1] := rfl
theorem bsData_k (i : bsData.ι) : bsData.k i = 1 := rfl

/-- The phase data of the blow-up chart: `F ∘ rep = (1 + x²) y²`, density `|y|`. -/
noncomputable def bsPhase : bsData.Phase bsF where
  kF := fun _ ↦ ![0, 2]
  hJ := fun _ ↦ ![0, 1]
  a := fun _ u ↦ 1 + u 0 ^ 2
  b := fun _ _ ↦ 1
  wt := fun _ ↦ bsCut
  a_cont := fun _ ↦ by fun_prop
  b_cont := fun _ ↦ continuous_const
  wt_cont := fun _ ↦ continuous_bsCut
  wt_nonneg := fun _ ↦ bsCut_nonneg
  wt_le_one := fun _ ↦ bsCut_le_one
  ma := fun _ ↦ 1
  Ma := fun _ ↦ 5
  mb := fun _ ↦ 1
  Mb := fun _ ↦ 1
  ma_pos := fun _ ↦ one_pos
  mb_pos := fun _ ↦ one_pos
  a_bounds := fun _ u hu ↦ by
    have h1 : |u 0| ≤ 2 := by
      have := norm_le_pi_norm u 0
      rw [Real.norm_eq_abs] at this
      exact this.trans (mem_closedBall_zero_iff.mp hu)
    have h2 : u 0 ^ 2 ≤ 4 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (u 0)]
    constructor
    · rw [abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg (u 0)]
    · rw [abs_of_nonneg (by positivity)]
      linarith
  b_bounds := fun _ _ _ ↦ by simp
  phase := fun _ u _ ↦ by
    simp only [bsData_rep, bsF, bsRep_zero, bsRep_one, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Fin.succ_zero_eq_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      mul_one, pow_zero, one_mul]
    ring
  dens_eq := fun _ u _ ↦ by
    simp only [bsData_dens, bsDens, Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.succ_zero_eq_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, pow_zero, pow_one,
      one_mul, mul_one]
    ring

end Laplace.Multi.BlowupSector
