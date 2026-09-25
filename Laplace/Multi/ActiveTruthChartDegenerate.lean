/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthDegenerateGeneral
import Laplace.Multi.ActiveTruthLPChart

/-!
# The chart wrapper of the boundary regime

Astra round 13, item 3 (the chart wrapper; the `j = 0` labelling is absorbed by the splitting
`e`). For an active-truth chart whose second fibre constraint vanishes identically, the normalised
model kernel converges to the integral of the observable against the **degenerate active-truth
measure** (`activeTruthDegMeasure`): the density
`C · (wt |b|)(P(v)) e^{-βs-ηh} e^{-c₀ |a(P(v))| e^{-s}} 1_{h > h₀} 1_{(M⁻¹v)_1 > 0}` on the
transverse plane, `C = A ρ^{∑(r+1)} vol(F')/|det M|`, pushed forward along the surface
`v ↦ rep(P(v))`, `P(v) = bridgePt(survPt(z(v))) u(v)` through the box: the surviving coordinate
`z(v)` sits at the box coordinate `e(inr 1)`, the truth coordinate is `u(v)`, the other
coordinates are at the wall (`degPt`). This is the two-dimensional surface of the boundary
regime, against the one-dimensional truth segment of the nondegenerate regime
(`activeTruthMeasure`).
`tendsto_modelKernelOf_activeTruth_degenerate` is the wrapper and
`TermData.activeTruthDegenerate` the term.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

namespace WallChartsData.Phase

variable {m k : ℕ} {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)} {D : WallChartsData m ℓ L'}
  {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F) {i : D.ι} {ε : Fin m → Bool} {b : Bool}
  {σ γ β η : ℝ} {φ : (Fin (m + 1) → ℝ) → ℝ}

/-- The point of the model box with the surviving coordinate `e (inr 1)` equal to `z` and the
other coordinates at the wall. -/
noncomputable def survPt (e : Fin k ⊕ Fin 2 ≃ Fin m) (z : ℝ) : Fin m → ℝ :=
  fun j ↦ Function.update (0 : Fin k ⊕ Fin 2 → ℝ) (Sum.inr 1) z (e.symm j)

theorem continuous_survPt (e : Fin k ⊕ Fin 2 ≃ Fin m) : Continuous (survPt e) :=
  (continuous_reindex e).comp (continuous_const.update (Sum.inr 1) continuous_id)

theorem abs_survPt_lt (e : Fin k ⊕ Fin 2 ≃ Fin m) {ρ z : ℝ} (hz : z ∈ Ioo 0 ρ) (j : Fin m) :
    |survPt e z j| < ρ := by
  unfold survPt
  by_cases h : e.symm j = Sum.inr 1
  · rw [h, Function.update_self, abs_of_pos hz.1]
    exact hz.2
  · rw [Function.update_of_ne h, Pi.zero_apply, abs_zero]
    exact hz.1.trans hz.2

/-- The reindexed update is the surviving-coordinate point. -/
theorem reindex_update_zero (e : Fin k ⊕ Fin 2 ≃ Fin m) (z : ℝ) :
    (fun j ↦ Function.update (0 : Fin k ⊕ Fin 2 → ℝ) (Sum.inr 1) z (e.symm j)) = survPt e z :=
  rfl

/-- The surface point of the boundary regime over the transverse point `v`. -/
noncomputable def degPt (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ : ℝ)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) (v : Fin 2 → ℝ) : Fin (m + 1) → ℝ :=
  D.bridgePt i ε b (survPt e (survCoord (D.ρ i) (P.kappa i ∘ e) (D.Qexp i ∘ e) v))
    (truthOf (D.ρ i) (D.constD i σ) (D.q i (D.k i)) (D.Qexp i ∘ e) (v 1))

theorem continuous_degPt (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ : ℝ)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) : Continuous (P.degPt i ε b σ e) :=
  (D.continuous_bridgePt i ε b).comp
    (((continuous_survPt e).comp (continuous_survCoord _ _ _)).prodMk
      ((continuous_truthOf _ _ _ _).comp (continuous_apply 1)))

/-- The transverse set of the boundary regime: `h > h₀` and `(M⁻¹v)_1 > 0`. -/
def degSet (i : D.ι) (σ : ℝ) (e : Fin k ⊕ Fin 2 ≃ Fin m) : Set (Fin 2 → ℝ) :=
  {v | -(D.q i (D.k i) * log (D.ρ i / D.constD i σ) +
    (∑ j, (D.Qexp i ∘ e) j) * log (D.ρ i)) < v 1} ∩
    {v | 0 < fibreB (P.kappa i ∘ e) (D.Qexp i ∘ e) v 1}

theorem measurableSet_degSet (i : D.ι) (σ : ℝ) (e : Fin k ⊕ Fin 2 ≃ Fin m) :
    MeasurableSet (P.degSet i σ e) :=
  (measurableSet_lt measurable_const (measurable_pi_apply 1)).inter
    (measurableSet_lt measurable_const (continuous_fibreB _ _ 1).measurable)

/-- On the transverse set the surface point lies in the open box of the chart. -/
theorem degPt_mem_ball (i : D.ι) (ε : Fin m → Bool) (b : Bool) (hσ : σ ≠ 0)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) {v : Fin 2 → ℝ} (hv : v ∈ P.degSet i σ e) :
    P.degPt i ε b σ e v ∈ Metric.ball (0 : Fin (m + 1) → ℝ) (D.ρ i) := by
  have hρ := D.ρ_pos i
  have hq : (0 : ℝ) < D.q i (D.k i) := Nat.cast_pos.mpr (D.q_pos i)
  have hDpos : 0 < D.constD i σ := Real.rpow_pos_of_pos (abs_pos.mpr hσ) _
  have hu := truthOf_mem_Ioo hρ hDpos hq (D.Qexp i ∘ e) hv.1
  have hz := survCoord_mem_Ioo hρ (κ := P.kappa i ∘ e) (Q := D.Qexp i ∘ e) hv.2
  exact D.bridgePt_mem_ball_of_abs_lt i ε b hρ (abs_survPt_lt e hz)
    (by rw [abs_of_pos hu.1]; exact hu.2)

/-- The density of the boundary regime on the transverse plane (without the constant). -/
noncomputable def activeTruthDegDensity (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ β η : ℝ)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) (v : Fin 2 → ℝ) : ℝ :=
  (P.degSet i σ e).indicator (fun v ↦
    P.wt i (P.degPt i ε b σ e v) * |P.b i (P.degPt i ε b σ e v)| *
      exp (-(β * v 0 + η * v 1 + 0)) *
      exp (-(P.constB i σ * D.ρ i ^ (∑ j, (P.kappa i ∘ e) j) * |P.a i (P.degPt i ε b σ e v)| *
        exp (-v 0)))) v

/-- The constant of the boundary regime: `A ρ^{∑(r+1)} vol(F')/|det M|`. -/
noncomputable def degConst (i : D.ι) (σ γ : ℝ) (e : Fin k ⊕ Fin 2 ≃ Fin m) : ℝ :=
  P.constA i σ * D.ρ i ^ (∑ j, ((P.rExp i ∘ e) j + 1)) *
    |(transMat (P.kappa i ∘ e) (D.Qexp i ∘ e)).det|⁻¹ *
    (volume (facePolytope (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ)).toReal

theorem degConst_nonneg (i : D.ι) (σ γ : ℝ) (e : Fin k ⊕ Fin 2 ≃ Fin m) :
    0 ≤ P.degConst i σ γ e :=
  mul_nonneg (mul_nonneg (mul_nonneg (P.constA_nonneg (i := i) (σ := σ))
    (Real.rpow_nonneg (D.ρ_pos i).le _)) (inv_nonneg.mpr (abs_nonneg _))) ENNReal.toReal_nonneg

/-- **The degenerate active-truth measure**: the density pushed forward along the surface
`v ↦ degPt v`. -/
noncomputable def activeTruthDegMeasure (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ β η : ℝ)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) : Measure (Fin (m + 1) → ℝ) :=
  (volume.withDensity fun v ↦ ENNReal.ofReal (P.degConst i σ γ e *
    P.activeTruthDegDensity i ε b σ β η e v)).map (fun v ↦ D.rep i (P.degPt i ε b σ e v))

theorem measurable_activeTruthDegDensity (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ β η : ℝ)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) : Measurable (P.activeTruthDegDensity i ε b σ β η e) := by
  unfold activeTruthDegDensity
  have hpt := P.continuous_degPt i ε b σ e
  refine Measurable.indicator ?_ (P.measurableSet_degSet i σ e)
  refine (((((P.wt_cont i).comp hpt).mul (continuous_abs.comp ((P.b_cont i).comp hpt))).mul
    (Real.continuous_exp.comp (by fun_prop))).mul (Real.continuous_exp.comp ?_)).measurable
  exact (((continuous_const.mul (continuous_abs.comp ((P.a_cont i).comp hpt))).mul
    (Real.continuous_exp.comp (continuous_apply 0).neg)).neg)

theorem activeTruthDegDensity_nonneg (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ β η : ℝ)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) (v : Fin 2 → ℝ) : 0 ≤ P.activeTruthDegDensity i ε b σ β η e v := by
  unfold activeTruthDegDensity
  refine Set.indicator_nonneg (fun v _ ↦ ?_) v
  exact mul_nonneg (mul_nonneg (mul_nonneg (P.wt_nonneg i _) (abs_nonneg _)) (exp_pos _).le)
    (exp_pos _).le

/-- The density is dominated by `M_b` times the constant-unit transverse weight at `c₀ m_a`. -/
theorem ofReal_activeTruthDegDensity_le (i : D.ι) (ε : Fin m → Bool) (b : Bool) (hσ : σ ≠ 0)
    (β η : ℝ) (e : Fin k ⊕ Fin 2 ≃ Fin m) (v : Fin 2 → ℝ) :
    ENNReal.ofReal (P.activeTruthDegDensity i ε b σ β η e v) ≤
      ENNReal.ofReal (P.Mb i) * vWeight β η 0
        (P.constB i σ * D.ρ i ^ (∑ j, (P.kappa i ∘ e) j) * P.ma i)
        (-(D.q i (D.k i) * log (D.ρ i / D.constD i σ) + (∑ j, (D.Qexp i ∘ e) j) * log (D.ρ i)))
        v := by
  unfold activeTruthDegDensity vWeight
  by_cases hv : v ∈ P.degSet i σ e
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (show v 1 ∈ Ioi _ from hv.1), one_mul,
      ← ENNReal.ofReal_mul P.Mb_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    have hball := P.degPt_mem_ball i ε b hσ e hv
    have hcb := Metric.ball_subset_closedBall hball
    have hb := (P.b_bounds i _ hcb).2
    have ha := (P.a_bounds i _ hcb).1
    have hc : 0 < P.constB i σ * D.ρ i ^ (∑ j, (P.kappa i ∘ e) j) :=
      mul_pos (P.constB_pos hσ) (Real.rpow_pos_of_pos (D.ρ_pos i) _)
    have hwb : P.wt i (P.degPt i ε b σ e v) * |P.b i (P.degPt i ε b σ e v)| ≤ P.Mb i := by
      calc P.wt i (P.degPt i ε b σ e v) * |P.b i (P.degPt i ε b σ e v)| ≤ 1 * P.Mb i :=
            mul_le_mul (P.wt_le_one i _) hb (abs_nonneg _) zero_le_one
        _ = P.Mb i := one_mul _
    have hE : 0 ≤ exp (-(β * v 0 + η * v 1 + 0)) := (exp_pos _).le
    have h3 : exp (-(P.constB i σ * D.ρ i ^ (∑ j, (P.kappa i ∘ e) j) *
        |P.a i (P.degPt i ε b σ e v)| * exp (-v 0))) ≤
        exp (-(P.constB i σ * D.ρ i ^ (∑ j, (P.kappa i ∘ e) j) * P.ma i * exp (-v 0))) := by
      rw [Real.exp_le_exp, neg_le_neg_iff]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha hc.le) (exp_pos _).le
    calc P.wt i (P.degPt i ε b σ e v) * |P.b i (P.degPt i ε b σ e v)| *
          exp (-(β * v 0 + η * v 1 + 0)) *
          exp (-(P.constB i σ * D.ρ i ^ (∑ j, (P.kappa i ∘ e) j) *
            |P.a i (P.degPt i ε b σ e v)| * exp (-v 0)))
        ≤ P.Mb i * exp (-(β * v 0 + η * v 1 + 0)) *
          exp (-(P.constB i σ * D.ρ i ^ (∑ j, (P.kappa i ∘ e) j) * P.ma i * exp (-v 0))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hwb hE) h3 (exp_pos _).le
            (mul_nonneg P.Mb_nonneg hE)
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hv, ENNReal.ofReal_zero]
    exact zero_le

theorem isFiniteMeasure_activeTruthDegMeasure (i : D.ι) (ε : Fin m → Bool) (b : Bool)
    (hσ : σ ≠ 0) (γ : ℝ) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) (e : Fin k ⊕ Fin 2 ≃ Fin m) :
    IsFiniteMeasure (P.activeTruthDegMeasure i ε b σ γ β η e) := by
  unfold activeTruthDegMeasure
  have hc : 0 < P.constB i σ * D.ρ i ^ (∑ j, (P.kappa i ∘ e) j) * P.ma i :=
    mul_pos (mul_pos (P.constB_pos hσ) (Real.rpow_pos_of_pos (D.ρ_pos i) _)) (P.ma_pos i)
  set h₀ := -(D.q i (D.k i) * log (D.ρ i / D.constD i σ) +
    (∑ j, (D.Qexp i ∘ e) j) * log (D.ρ i)) with hh₀
  set c₁ := P.constB i σ * D.ρ i ^ (∑ j, (P.kappa i ∘ e) j) * P.ma i with hc₁
  have hfin : ∫⁻ v, ENNReal.ofReal (P.degConst i σ γ e *
      P.activeTruthDegDensity i ε b σ β η e v) < ⊤ := by
    calc ∫⁻ v, ENNReal.ofReal (P.degConst i σ γ e * P.activeTruthDegDensity i ε b σ β η e v)
        = ENNReal.ofReal (P.degConst i σ γ e) *
          ∫⁻ v, ENNReal.ofReal (P.activeTruthDegDensity i ε b σ β η e v) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact lintegral_congr fun v ↦ ENNReal.ofReal_mul (P.degConst_nonneg i σ γ e)
      _ ≤ ENNReal.ofReal (P.degConst i σ γ e) *
          ∫⁻ v, ENNReal.ofReal (P.Mb i) * vWeight β η 0 c₁ h₀ v :=
          mul_le_mul_of_nonneg_left (lintegral_mono fun v ↦
            P.ofReal_activeTruthDegDensity_le i ε b hσ β η e v) zero_le
      _ = ENNReal.ofReal (P.degConst i σ γ e) *
          (ENNReal.ofReal (P.Mb i) * ∫⁻ v, vWeight β η 0 c₁ h₀ v) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ < ⊤ := by
          rw [lintegral_vWeight_zero hβ hη hc]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have := isFiniteMeasure_withDensity hfin.ne
  infer_instance

theorem integral_activeTruthDegMeasure (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ β η : ℝ)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) (hφm : Measurable φ) :
    ∫ x, φ x ∂(P.activeTruthDegMeasure i ε b σ γ β η e) =
      ∫ v, φ (D.rep i (P.degPt i ε b σ e v)) *
        (P.degConst i σ γ e * P.activeTruthDegDensity i ε b σ β η e v) := by
  unfold activeTruthDegMeasure
  have hm : Measurable fun v ↦ ENNReal.ofReal (P.degConst i σ γ e *
      P.activeTruthDegDensity i ε b σ β η e v) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (P.measurable_activeTruthDegDensity i ε b σ β η e))
  have hmap : Measurable fun v : Fin 2 → ℝ ↦ D.rep i (P.degPt i ε b σ e v) :=
    (D.rep_cont i).measurable.comp (P.continuous_degPt i ε b σ e).measurable
  rw [integral_map hmap.aemeasurable hφm.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ hm.aemeasurable
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (mul_nonneg (P.degConst_nonneg i σ γ e)
    (P.activeTruthDegDensity_nonneg i ε b σ β η e v)), mul_comm]

/-- The transverse weight of the partial traces of the chart is the observable times the density. -/
theorem vWeightTD_chart_eq (i : D.ι) (ε : Fin m → Bool) (b : Bool) (hσ : σ ≠ 0) (β η : ℝ)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) (hφL : ∀ z, φ z ≠ 0 → z ∈ L') (v : Fin 2 → ℝ) :
    vWeightTD (D.ρ i) (D.constD i σ) (D.q i (D.k i)) (P.kappa i ∘ e) (D.Qexp i ∘ e) β η
      (P.constB i σ * D.ρ i ^ (∑ j, (P.kappa i ∘ e) j))
      (-(D.q i (D.k i) * log (D.ρ i / D.constD i σ) + (∑ j, (D.Qexp i ∘ e) j) * log (D.ρ i)))
      (fun z u ↦ P.weightFn i φ ε b (survPt e z) u) (fun z u ↦ P.unitFn i ε b (survPt e z) u) v =
      ENNReal.ofReal (φ (D.rep i (P.degPt i ε b σ e v)) *
        P.activeTruthDegDensity i ε b σ β η e v) := by
  unfold vWeightTD activeTruthDegDensity
  by_cases hv : v ∈ P.degSet i σ e
  · rw [Set.indicator_of_mem (show v 1 ∈ Ioi _ from hv.1),
      Set.indicator_of_mem (show fibreB (P.kappa i ∘ e) (D.Qexp i ∘ e) v 1 ∈ Ioi 0 from hv.2),
      Set.indicator_of_mem hv, one_mul, one_mul]
    have hcb := Metric.ball_subset_closedBall (P.degPt_mem_ball i ε b hσ e hv)
    congr 1
    beta_reduce
    rw [P.weightFn_eq_of_mem_closedBall hφL hcb]
    unfold unitFn degPt
    ring
  · rw [Set.indicator_of_notMem hv, mul_zero, ENNReal.ofReal_zero]
    rcases not_and_or.mp hv with h | h
    · rw [Set.indicator_of_notMem (show v 1 ∉ Ioi _ from h), zero_mul, zero_mul]
    · rw [Set.indicator_of_notMem
        (show fibreB (P.kappa i ∘ e) (D.Qexp i ∘ e) v 1 ∉ Ioi 0 from h), mul_zero, zero_mul]

/-- **The chart term of the boundary regime**: the normalised model kernel of an active-truth chart
with an identically vanishing second fibre constraint converges to the integral of the observable
against the degenerate active-truth measure. -/
theorem tendsto_modelKernelOf_activeTruth_degenerate (e : Fin k ⊕ Fin 2 ≃ Fin m) (hσ : σ ≠ 0)
    (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ P.phaseExp i γ) (hκ : ∀ j, 0 < P.kappa i j)
    (hΔ : (transMat (P.kappa i ∘ e) (D.Qexp i ∘ e)).det ≠ 0)
    (hc₀ : fibreCoef (P.kappa i ∘ e) (D.Qexp i ∘ e) 0 ≠ 0 ∨
      fibreA (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ 0 ≠ 0)
    (hdeg : fibreCoef (P.kappa i ∘ e) (D.Qexp i ∘ e) 1 = 0 ∧
      fibreA (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ 1 = 0)
    (hr : ∀ j, P.rExp i (e j) + 1 = β * P.kappa i (e j) - η * D.Qexp i (e j))
    (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ)
    (hφL : ∀ z, φ z ≠ 0 → z ∈ L') :
    Tendsto (fun t ↦ t ^ (γ * P.pExp i + (β * P.phaseExp i γ - η * γ)) / log t ^ k *
        P.modelKernelOf i φ ε b t γ σ) atTop
      (𝓝 (∫ x, φ x ∂(P.activeTruthDegMeasure i ε b σ γ β η e))) := by
  have hρ := D.ρ_pos i
  have hq : (0 : ℝ) < D.q i (D.k i) := Nat.cast_pos.mpr (D.q_pos i)
  have hDpos : 0 < D.constD i σ := Real.rpow_pos_of_pos (abs_pos.mpr hσ) _
  have hB := P.constB_pos (i := i) hσ
  set We : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ :=
    fun y v ↦ P.weightFn i φ ε b (fun j ↦ y (e.symm j)) v with hWe
  set ae' : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ :=
    fun y v ↦ max (P.unitFn i ε b (fun j ↦ y (e.symm j)) v) (P.ma i) with hae
  -- the reindexed kernel with the unit modified off the domain
  have hK : ∀ᶠ t in atTop, P.modelKernelOf i φ ε b t γ σ =
      modelKernel (D.ρ i) (P.constA i σ) (P.constB i σ) (D.constD i σ) γ (P.pExp i)
        (D.q i (D.k i)) (P.phaseExp i γ) (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e)
        We ae' t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    unfold modelKernelOf
    rw [modelKernel_reindex e]
    refine modelKernel_congr_unit fun x hx ↦ ?_
    rw [hae]
    simp only
    symm
    refine max_eq_left (P.ma_le_unitFn_of_mem_ball ?_)
    have hx0 : ∀ j, 0 < x j := fun j ↦ ((Set.mem_univ_pi.mp hx.1) j).1
    have hcut : cutVar (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i ∘ e) t x < D.ρ i := hx.2
    have hcut0 : 0 ≤ cutVar (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i ∘ e) t x := by
      unfold cutVar
      exact mul_nonneg (mul_nonneg hDpos.le (Real.rpow_nonneg ht.le _))
        (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hx0 j).le _)
    exact (D.bridgePt_mem_ball_iff i ε b hρ (fun j ↦ hx0 _) hcut0).mpr
      ⟨fun j ↦ ((Set.mem_univ_pi.mp hx.1) _).2, hcut⟩
  -- the partial traces
  have hmap : ∀ z u : ℝ, Tendsto (fun y : Fin k ⊕ Fin 2 → ℝ ↦
      ((fun j ↦ Function.update y (Sum.inr 1) z (e.symm j)), u)) (𝓝 0) (𝓝 (survPt e z, u)) :=
    fun z u ↦ (((continuous_reindex e).comp (continuous_id.update (Sum.inr 1) continuous_const)
      ).tendsto 0).prodMk_nhds tendsto_const_nhds
  have hball : ∀ z ∈ Ioo (0 : ℝ) (D.ρ i), ∀ u ∈ Ioo (0 : ℝ) (D.ρ i),
      D.bridgePt i ε b (survPt e z) u ∈ Metric.ball (0 : Fin (m + 1) → ℝ) (D.ρ i) :=
    fun z hz u hu ↦ D.bridgePt_mem_ball_of_abs_lt i ε b hρ (abs_survPt_lt e hz)
      (by rw [abs_of_pos hu.1]; exact hu.2)
  have hWtr : ∀ z ∈ Ioo (0 : ℝ) (D.ρ i), ∀ u ∈ Ioo (0 : ℝ) (D.ρ i),
      Tendsto (fun y ↦ We (Function.update y (Sum.inr 1) z) u)
        (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) (D.ρ i)] 0)
        (𝓝 (P.weightFn i φ ε b (survPt e z) u)) := fun z hz u hu ↦
    (((P.continuousAt_weightFn hφc hφL (hball z hz u hu)).tendsto.comp
      (hmap z u))).mono_left nhdsWithin_le_nhds
  have hatr : ∀ z ∈ Ioo (0 : ℝ) (D.ρ i), ∀ u ∈ Ioo (0 : ℝ) (D.ρ i),
      Tendsto (fun y ↦ ae' (Function.update y (Sum.inr 1) z) u)
        (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) (D.ρ i)] 0)
        (𝓝 (P.unitFn i ε b (survPt e z) u)) := fun z hz u hu ↦ by
    have h1 : Tendsto (fun y ↦ ae' (Function.update y (Sum.inr 1) z) u) (𝓝 0)
        (𝓝 (max (P.unitFn i ε b (survPt e z) u) (P.ma i))) :=
      ((P.continuousAt_unitFn (i := i) (ε := ε) (b := b) (survPt e z, u)).tendsto.comp
        (hmap z u)).max (tendsto_const_nhds (x := P.ma i))
    rw [max_eq_left (P.ma_le_unitFn_of_mem_ball (hball z hz u hu))] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hgen := tendsto_modelKernel_general_degenerate (k := k) (ρ := D.ρ i) (A := P.constA i σ)
    (B := P.constB i σ) (D := D.constD i σ) (γ := γ) (p := P.pExp i) (q := D.q i (D.k i))
    (δ := P.phaseExp i γ) (β := β) (η := η) (Q := D.Qexp i ∘ e) (κ := P.kappa i ∘ e)
    (r := P.rExp i ∘ e) (W := We) (a := ae') (Wstar := Mφ * P.Mb i) (amin := P.ma i)
    (Wtr := fun z u ↦ P.weightFn i φ ε b (survPt e z) u)
    (atr := fun z u ↦ P.unitFn i ε b (survPt e z) u)
    hρ hDpos hq hB hβ hη hδ (fun j ↦ hκ _) hΔ hc₀ hdeg (fun j ↦ hr j) (P.ma_pos i)
    ((P.measurable_weightFn hφc.measurable).comp
      (((continuous_reindex e).measurable.comp measurable_fst).prodMk measurable_snd))
    ((P.measurable_unitFn.comp
      (((continuous_reindex e).measurable.comp measurable_fst).prodMk measurable_snd)).max
      measurable_const)
    (fun x u ↦ ⟨P.weightFn_nonneg hφ _ _, (le_abs_self _).trans (P.abs_weightFn_le hφ hMφ _ _)⟩)
    (fun _ _ ↦ le_max_right _ _)
    ((P.measurable_weightFn hφc.measurable).comp
      (((continuous_survPt e).measurable.comp measurable_fst).prodMk measurable_snd))
    (P.measurable_unitFn.comp
      (((continuous_survPt e).measurable.comp measurable_fst).prodMk measurable_snd))
    (fun z _ u _ ↦ ⟨P.weightFn_nonneg hφ _ _,
      (le_abs_self _).trans (P.abs_weightFn_le hφ hMφ _ _)⟩)
    (fun z hz u hu ↦ P.ma_le_unitFn_of_mem_ball (hball z hz u hu)) hWtr hatr
  -- the limit value is the integral against the degenerate active-truth measure
  have hval : ∫ x, φ x ∂(P.activeTruthDegMeasure i ε b σ γ β η e) =
      P.constA i σ * D.ρ i ^ (∑ j, ((P.rExp i ∘ e) j + 1)) *
        |(transMat (P.kappa i ∘ e) (D.Qexp i ∘ e)).det|⁻¹ *
        (∫⁻ v : Fin 2 → ℝ, vWeightTD (D.ρ i) (D.constD i σ) (D.q i (D.k i)) (P.kappa i ∘ e)
          (D.Qexp i ∘ e) β η (P.constB i σ * D.ρ i ^ (∑ j, (P.kappa i ∘ e) j))
          (-(D.q i (D.k i) * log (D.ρ i / D.constD i σ) +
            (∑ j, (D.Qexp i ∘ e) j) * log (D.ρ i)))
          (fun z u ↦ P.weightFn i φ ε b (survPt e z) u)
          (fun z u ↦ P.unitFn i ε b (survPt e z) u) v).toReal *
        (volume (facePolytope (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ)).toReal := by
    rw [P.integral_activeTruthDegMeasure i ε b σ γ β η e hφc.measurable]
    have hnn : ∀ v, 0 ≤ φ (D.rep i (P.degPt i ε b σ e v)) *
        P.activeTruthDegDensity i ε b σ β η e v :=
      fun v ↦ mul_nonneg (hφ _) (P.activeTruthDegDensity_nonneg i ε b σ β η e v)
    have hmeas : Measurable fun v ↦ φ (D.rep i (P.degPt i ε b σ e v)) *
        P.activeTruthDegDensity i ε b σ β η e v :=
      (hφc.measurable.comp ((D.rep_cont i).comp (P.continuous_degPt i ε b σ e)).measurable).mul
        (P.measurable_activeTruthDegDensity i ε b σ β η e)
    have e1 : ∫ v, φ (D.rep i (P.degPt i ε b σ e v)) *
        (P.degConst i σ γ e * P.activeTruthDegDensity i ε b σ β η e v) =
        P.degConst i σ γ e * ∫ v, φ (D.rep i (P.degPt i ε b σ e v)) *
          P.activeTruthDegDensity i ε b σ β η e v := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun v ↦ by ring)
    rw [e1, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hmeas.aestronglyMeasurable]
    simp_rw [P.vWeightTD_chart_eq i ε b hσ β η e hφL]
    unfold degConst
    ring
  rw [hval]
  refine hgen.congr' ?_
  filter_upwards [hK] with t ht
  rw [ht]

open scoped Classical in
/-- **The boundary-regime term**: `(γp + βδ − ηγ, k, activeTruthDegMeasure)`. -/
noncomputable def TermData.activeTruthDegenerate (e : Fin k ⊕ Fin 2 ≃ Fin m) (hσ : σ ≠ 0)
    {p : WallChartsData.Phase.TermIdx D} (hadm : D.admissible p.1 p.2.1 p.2.2 σ) (hβ : 0 < β)
    (hη : 0 < η) (hδ : 0 ≤ P.phaseExp p.1 γ) (hκ : ∀ j, 0 < P.kappa p.1 j)
    (hΔ : (transMat (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e)).det ≠ 0)
    (hc₀ : fibreCoef (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e) 0 ≠ 0 ∨
      fibreA (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e) (P.phaseExp p.1 γ) γ 0 ≠ 0)
    (hdeg : fibreCoef (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e) 1 = 0 ∧
      fibreA (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e) (P.phaseExp p.1 γ) γ 1 = 0)
    (hr : ∀ j, P.rExp p.1 (e j) + 1 = β * P.kappa p.1 (e j) - η * D.Qexp p.1 (e j)) :
    P.TermData σ γ p where
  lam := γ * P.pExp p.1 + (β * P.phaseExp p.1 γ - η * γ)
  kk := k
  μ := P.activeTruthDegMeasure p.1 p.2.1 p.2.2 σ γ β η e
  finite := P.isFiniteMeasure_activeTruthDegMeasure p.1 p.2.1 p.2.2 hσ γ hβ hη e
  tendsto := fun φ hφc hφ ⟨M, hM⟩ hφL ↦ by
    have h := P.tendsto_modelKernelOf_activeTruth_degenerate (ε := p.2.1) (b := p.2.2) e hσ hβ hη
      hδ hκ hΔ hc₀ hdeg hr hφc hφ hM hφL
    refine h.congr' (Eventually.of_forall fun t ↦ ?_)
    unfold termKernel
    simp only [if_pos hadm]

end WallChartsData.Phase

end Laplace.Multi
