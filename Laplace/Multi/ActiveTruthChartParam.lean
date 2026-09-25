/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthGeneralParam
import Laplace.Multi.ActiveTruthChart
import Laplace.Multi.WallLogTermParam

/-!
# The chart-level active-truth term along a moving parameter

The active-truth term of a chart with `σ(t) → σ₀ ≠ 0`: the chart constants `A, B, D` are
continuous in `σ` (`tendsto_constA/B/D`), the chart weight and unit do not depend on `σ`, and the
general-unit moving theorem (`tendsto_modelKernel_general_param`, via the time change) gives the
active-truth measure at `σ₀` (`tendsto_modelKernelOf_activeTruth_param`,
`tendsto_termKernel_activeTruth_param`). This is the parameter-stability statement for the
active-truth term, the analogue of `tendsto_termKernel_tied_param` for the tied term.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

namespace TruthChartsData.Phase

variable {m k : ℕ} {L' : Set (Fin (m + 1) → ℝ)} {T : (Fin (m + 1) → ℝ) → ℝ}
  {D : TruthChartsData m T L'}
  {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F) {i : D.ι} {ε : Fin m → Bool} {b : Bool}
  {σ : ℝ → ℝ} {σ₀ γ β η : ℝ} {φ : (Fin (m + 1) → ℝ) → ℝ}

/-- **The active-truth chart term along a moving parameter** `σ(t) → σ₀ ≠ 0`. -/
theorem tendsto_modelKernelOf_activeTruth_param (e : Fin k ⊕ Fin 2 ≃ Fin m)
    (hσ : Tendsto σ atTop (𝓝 σ₀)) (hσ₀ : σ₀ ≠ 0) (hγ : 0 < γ) (hβ : 0 < β) (hη : 0 < η)
    (hδ : 0 ≤ P.phaseExp i γ) (hκ : ∀ j, 0 < P.kappa i j)
    (hΔ : (transMat (P.kappa i ∘ e) (D.Qexp i ∘ e)).det ≠ 0)
    (hc₀ : fibreCoef (P.kappa i ∘ e) (D.Qexp i ∘ e) 0 ≠ 0 ∨
      fibreA (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ 0 ≠ 0)
    (hc₁ : fibreCoef (P.kappa i ∘ e) (D.Qexp i ∘ e) 1 ≠ 0 ∨
      fibreA (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ 1 ≠ 0)
    (hr : ∀ j, P.rExp i (e j) + 1 = β * P.kappa i (e j) - η * D.Qexp i (e j))
    (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ)
    (hφL : ∀ z, φ z ≠ 0 → z ∈ L') :
    Tendsto (fun t ↦ t ^ (γ * P.pExp i + (β * P.phaseExp i γ - η * γ)) / log t ^ k *
        P.modelKernelOf i φ ε b t γ (σ t)) atTop
      (𝓝 (∫ x, φ x ∂(P.activeTruthMeasure i ε b σ₀ γ β η e))) := by
  have hρ := D.ρ_pos i
  have hq : (0 : ℝ) < D.q i (D.k i) := Nat.cast_pos.mpr (D.q_pos i)
  have hD₀ : 0 < D.constD i σ₀ := Real.rpow_pos_of_pos (abs_pos.mpr hσ₀) _
  have hB₀ := P.constB_pos (i := i) hσ₀
  have hσne : ∀ᶠ t in atTop, σ t ≠ 0 := hσ.eventually_ne hσ₀
  set We : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ :=
    fun y v ↦ P.weightFn i φ ε b (fun j ↦ y (e.symm j)) v with hWe
  set ae' : (Fin k ⊕ Fin 2 → ℝ) → ℝ → ℝ :=
    fun y v ↦ max (P.unitFn i ε b (fun j ↦ y (e.symm j)) v) (P.ma i) with hae
  -- the reindexed kernel with the unit modified off the domain, along the parameter
  have hK : ∀ᶠ t in atTop, P.modelKernelOf i φ ε b t γ (σ t) =
      modelKernel (D.ρ i) (P.constA i (σ t)) (P.constB i (σ t)) (D.constD i (σ t)) γ (P.pExp i)
        (D.q i (D.k i)) (P.phaseExp i γ) (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e)
        We ae' t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hσne] with t ht hσt
    have hDpos : 0 < D.constD i (σ t) := Real.rpow_pos_of_pos (abs_pos.mpr hσt) _
    unfold modelKernelOf
    rw [modelKernel_reindex e]
    refine modelKernel_congr_unit fun x hx ↦ ?_
    rw [hae]
    simp only
    symm
    refine max_eq_left (P.ma_le_unitFn_of_mem_ball ?_)
    have hx0 : ∀ j, 0 < x j := fun j ↦ ((Set.mem_univ_pi.mp hx.1) j).1
    have hcut : cutVar (D.constD i (σ t)) γ (D.q i (D.k i)) (D.Qexp i ∘ e) t x < D.ρ i := hx.2
    have hcut0 : 0 ≤ cutVar (D.constD i (σ t)) γ (D.q i (D.k i)) (D.Qexp i ∘ e) t x := by
      unfold cutVar
      exact mul_nonneg (mul_nonneg hDpos.le (Real.rpow_nonneg ht.le _))
        (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hx0 j).le _)
    exact (D.bridgePt_mem_ball_iff i ε b hρ (fun j ↦ hx0 _) hcut0).mpr
      ⟨fun j ↦ ((Set.mem_univ_pi.mp hx.1) _).2, hcut⟩
  -- the traces
  have hmap : ∀ u : ℝ, Tendsto (fun x : Fin k ⊕ Fin 2 → ℝ ↦ ((fun j ↦ x (e.symm j)), u)) (𝓝 0)
      (𝓝 ((0 : Fin m → ℝ), u)) := fun u ↦
    ((continuous_reindex e).tendsto 0).prodMk_nhds tendsto_const_nhds
  have hWtr : ∀ u ∈ Ioo (0 : ℝ) (D.ρ i), Tendsto (fun x ↦ We x u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) (D.ρ i)] 0)
      (𝓝 (P.weightFn i φ ε b 0 u)) := fun u hu ↦
    (((P.continuousAt_weightFn hφc hφL (truthPt_mem_ball (D := D) i ε b hu)).tendsto.comp
      (hmap u))).mono_left nhdsWithin_le_nhds
  have hatr : ∀ u ∈ Ioo (0 : ℝ) (D.ρ i), Tendsto (fun x ↦ ae' x u)
      (𝓝[Set.pi univ fun _ : Fin k ⊕ Fin 2 ↦ Ioo (0 : ℝ) (D.ρ i)] 0)
      (𝓝 (P.unitFn i ε b 0 u)) := fun u hu ↦ by
    have h1 : Tendsto (fun x ↦ ae' x u) (𝓝 0) (𝓝 (max (P.unitFn i ε b 0 u) (P.ma i))) :=
      ((P.continuousAt_unitFn (i := i) (ε := ε) (b := b) (0, u)).tendsto.comp
        (hmap u)).max (tendsto_const_nhds (x := P.ma i))
    rw [max_eq_left (P.ma_le_unitFn_of_mem_ball (truthPt_mem_ball (D := D) i ε b hu))] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hgen := tendsto_modelKernel_general_param (k := k) (ρ := D.ρ i)
    (A := fun t ↦ P.constA i (σ t)) (B := fun t ↦ P.constB i (σ t))
    (D := fun t ↦ D.constD i (σ t)) (A₀ := P.constA i σ₀) (B₀ := P.constB i σ₀)
    (D₀ := D.constD i σ₀) (γ := γ) (p := P.pExp i) (q := D.q i (D.k i)) (δ := P.phaseExp i γ)
    (β := β) (η := η) (Q := D.Qexp i ∘ e) (κ := P.kappa i ∘ e) (r := P.rExp i ∘ e) (W := We)
    (a := ae') (Wstar := Mφ * P.Mb i) (amin := P.ma i)
    (Wtr := fun u ↦ P.weightFn i φ ε b 0 u) (atr := fun u ↦ P.unitFn i ε b 0 u)
    hρ hq hγ hβ hη hδ (fun j ↦ hκ _) hΔ hc₀ hc₁ (fun j ↦ hr j) (P.ma_pos i)
    ((P.measurable_weightFn hφc.measurable).comp
      (((continuous_reindex e).measurable.comp measurable_fst).prodMk measurable_snd))
    ((P.measurable_unitFn.comp
      (((continuous_reindex e).measurable.comp measurable_fst).prodMk measurable_snd)).max
      measurable_const)
    (fun x u ↦ ⟨P.weightFn_nonneg hφ _ _, (le_abs_self _).trans (P.abs_weightFn_le hφ hMφ _ _)⟩)
    (fun _ _ ↦ le_max_right _ _)
    ((P.measurable_weightFn hφc.measurable).comp (measurable_const.prodMk measurable_id))
    (P.measurable_unitFn.comp (measurable_const.prodMk measurable_id))
    (fun u _ ↦ ⟨P.weightFn_nonneg hφ _ _, (le_abs_self _).trans (P.abs_weightFn_le hφ hMφ _ _)⟩)
    (fun u hu ↦ P.ma_le_unitFn_of_mem_ball (truthPt_mem_ball (D := D) i ε b hu)) hWtr hatr
    (P.tendsto_constA hσ hσ₀) (P.tendsto_constB hσ hσ₀) hB₀ (D.tendsto_constD hσ hσ₀) hD₀
  -- the limit value is the integral against the active-truth measure at `σ₀`
  have hval : ∫ x, φ x ∂(P.activeTruthMeasure i ε b σ₀ γ β η e) =
      P.constA i σ₀ * Gamma β * P.constB i σ₀ ^ (-β) * (D.q i (D.k i) : ℝ) *
        D.constD i σ₀ ^ (-((D.q i (D.k i) : ℝ) * η)) *
        (volume (facePolytope (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ)).toReal /
        |(transMat (P.kappa i ∘ e) (D.Qexp i ∘ e)).det| *
        ∫ u in Ioo (0 : ℝ) (D.ρ i), u ^ ((D.q i (D.k i) : ℝ) * η - 1) *
          (P.weightFn i φ ε b 0 u * P.unitFn i ε b 0 u ^ (-β)) := by
    rw [P.integral_activeTruthMeasure i ε b σ₀ γ η hβ e hφc.measurable]
    unfold activeTruthDensity
    simp_rw [← Set.indicator_mul_right _ (fun u ↦ φ (D.rep i (D.bridgePt i ε b 0 u)))]
    rw [integral_indicator measurableSet_Ioo, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu ↦ ?_
    have hcb : D.bridgePt i ε b 0 u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i) :=
      Metric.ball_subset_closedBall (truthPt_mem_ball (D := D) i ε b hu)
    rw [P.weightFn_eq_of_mem_closedBall hφL hcb]
    unfold activeTruthDensityFn faceConst unitFn
    ring
  rw [hval]
  refine hgen.congr' ?_
  filter_upwards [hK] with t ht
  rw [ht]

open scoped Classical in
/-- **The active-truth term along a moving parameter**: an admissible (at `σ₀`) branch. -/
theorem tendsto_termKernel_activeTruth_param (e : Fin k ⊕ Fin 2 ≃ Fin m)
    (hσ : Tendsto σ atTop (𝓝 σ₀)) (hσ₀ : σ₀ ≠ 0) (hγ : 0 < γ)
    {p : TruthChartsData.Phase.TermIdx D} (hadm : D.admissible p.1 p.2.1 p.2.2 σ₀) (hβ : 0 < β)
    (hη : 0 < η) (hδ : 0 ≤ P.phaseExp p.1 γ) (hκ : ∀ j, 0 < P.kappa p.1 j)
    (hΔ : (transMat (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e)).det ≠ 0)
    (hc₀ : fibreCoef (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e) 0 ≠ 0 ∨
      fibreA (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e) (P.phaseExp p.1 γ) γ 0 ≠ 0)
    (hc₁ : fibreCoef (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e) 1 ≠ 0 ∨
      fibreA (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e) (P.phaseExp p.1 γ) γ 1 ≠ 0)
    (hr : ∀ j, P.rExp p.1 (e j) + 1 = β * P.kappa p.1 (e j) - η * D.Qexp p.1 (e j))
    (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ)
    (hφL : ∀ z, φ z ≠ 0 → z ∈ L') :
    Tendsto (fun t ↦ t ^ (γ * P.pExp p.1 + (β * P.phaseExp p.1 γ - η * γ)) / log t ^ k *
        P.termKernel φ (σ t) γ p t) atTop
      (𝓝 (∫ x, φ x ∂(P.activeTruthMeasure p.1 p.2.1 p.2.2 σ₀ γ β η e))) := by
  have h := P.tendsto_modelKernelOf_activeTruth_param (ε := p.2.1) (b := p.2.2) e hσ hσ₀ hγ hβ hη
    hδ hκ hΔ hc₀ hc₁ hr hφc hφ hMφ hφL
  refine h.congr' ?_
  filter_upwards [D.admissible_eventually_iff (i := p.1) (ε := p.2.1) (b := p.2.2) hσ hσ₀] with t ht
  unfold termKernel
  rw [if_pos (ht.mpr hadm)]

end TruthChartsData.Phase

end Laplace.Multi
