/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthChartDegenerate

/-!
# Nonvanishing of the degenerate active-truth measure

Astra round 13, item 4: a limit theorem allowing a zero coefficient is not a theorem about the
leading order. The degenerate active-truth measure charges every open set meeting its surface
`v ↦ rep(degPt v)` at a transverse point `v₀` of the set `{h > h₀, (M⁻¹v)_1 > 0}` where the weight
`wt |b|` is positive (`activeTruthDegMeasure_pos_of_open`), for a positive face polytope; in
particular it is nonzero (`activeTruthDegMeasure_ne_zero`), and it gives no mass to a set the
surface misses (`activeTruthDegMeasure_eq_zero_of_disjoint`), the ingredients of the
support-separated distinguishability of `ActiveTruthDistinguish.lean` for this regime.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

namespace TruthChartsData.Phase

variable {m k : ℕ} {L' : Set (Fin (m + 1) → ℝ)} {T : (Fin (m + 1) → ℝ) → ℝ}
  {D : TruthChartsData m T L'}
  {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F) {σ γ β η : ℝ}

theorem isOpen_degSet (i : D.ι) (σ : ℝ) (e : Fin k ⊕ Fin 2 ≃ Fin m) :
    IsOpen (P.degSet i σ e) :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter
    (isOpen_lt continuous_const (continuous_fibreB _ _ 1))

theorem degConst_pos (i : D.ι) (hσ : σ ≠ 0) (γ : ℝ) (e : Fin k ⊕ Fin 2 ≃ Fin m)
    (hΔ : (transMat (P.kappa i ∘ e) (D.Qexp i ∘ e)).det ≠ 0) (hκ : ∀ j, 0 < P.kappa i j)
    (hvol : 0 < volume (facePolytope (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ)) :
    0 < P.degConst i σ γ e := by
  unfold degConst
  have hF := volume_facePolytope_ne_top hΔ (fun j ↦ hκ _) (P.phaseExp i γ) γ
  exact mul_pos (mul_pos (mul_pos (P.constA_pos (i := i) hσ)
    (Real.rpow_pos_of_pos (D.ρ_pos i) _)) (inv_pos.mpr (abs_pos.mpr hΔ)))
    (ENNReal.toReal_pos hvol.ne' hF)

/-- The degenerate measure of a measurable set is the weighted volume of its preimage under the
surface map. -/
theorem activeTruthDegMeasure_apply (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ β η : ℝ)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) {O : Set (Fin (m + 1) → ℝ)} (hO : MeasurableSet O) :
    P.activeTruthDegMeasure i ε b σ γ β η e O =
      ∫⁻ v in (fun v : Fin 2 → ℝ ↦ D.rep i (P.degPt i ε b σ e v)) ⁻¹' O,
        ENNReal.ofReal (P.degConst i σ γ e * P.activeTruthDegDensity i ε b σ β η e v) := by
  unfold activeTruthDegMeasure
  have hmap : Measurable fun v : Fin 2 → ℝ ↦ D.rep i (P.degPt i ε b σ e v) :=
    (D.rep_cont i).measurable.comp (P.continuous_degPt i ε b σ e).measurable
  rw [Measure.map_apply hmap hO, withDensity_apply _ (hmap hO)]

/-- **The degenerate active-truth measure charges every open set meeting its surface** at a
transverse point of positive weight. -/
theorem activeTruthDegMeasure_pos_of_open (i : D.ι) (ε : Fin m → Bool) (b : Bool) (hσ : σ ≠ 0)
    (γ β η : ℝ) (e : Fin k ⊕ Fin 2 ≃ Fin m)
    (hΔ : (transMat (P.kappa i ∘ e) (D.Qexp i ∘ e)).det ≠ 0) (hκ : ∀ j, 0 < P.kappa i j)
    (hvol : 0 < volume (facePolytope (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ))
    {v₀ : Fin 2 → ℝ} (hv₀ : v₀ ∈ P.degSet i σ e)
    (hpos : 0 < P.wt i (P.degPt i ε b σ e v₀) * |P.b i (P.degPt i ε b σ e v₀)|)
    {O : Set (Fin (m + 1) → ℝ)} (hO : IsOpen O) (hmem : D.rep i (P.degPt i ε b σ e v₀) ∈ O) :
    0 < P.activeTruthDegMeasure i ε b σ γ β η e O := by
  have hm : Measurable fun v ↦ ENNReal.ofReal (P.degConst i σ γ e *
      P.activeTruthDegDensity i ε b σ β η e v) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (P.measurable_activeTruthDegDensity i ε b σ β η e))
  rw [P.activeTruthDegMeasure_apply i ε b σ γ β η e hO.measurableSet, setLIntegral_pos_iff hm]
  have hpt := P.continuous_degPt i ε b σ e
  have hg : Continuous fun v ↦ P.wt i (P.degPt i ε b σ e v) * |P.b i (P.degPt i ε b σ e v)| :=
    ((P.wt_cont i).comp hpt).mul (continuous_abs.comp ((P.b_cont i).comp hpt))
  have hU : IsOpen {v | 0 < P.wt i (P.degPt i ε b σ e v) * |P.b i (P.degPt i ε b σ e v)|} :=
    isOpen_lt continuous_const hg
  have hpre : IsOpen ((fun v : Fin 2 → ℝ ↦ D.rep i (P.degPt i ε b σ e v)) ⁻¹' O) :=
    hO.preimage ((D.rep_cont i).comp hpt)
  refine lt_of_lt_of_le (((hU.inter (P.isOpen_degSet i σ e)).inter hpre).measure_pos volume
    ⟨v₀, ⟨hpos, hv₀⟩, hmem⟩) (measure_mono fun v hv ↦ ?_)
  obtain ⟨⟨hv1, hv2⟩, hv3⟩ := hv
  have hv1' : 0 < P.wt i (P.degPt i ε b σ e v) * |P.b i (P.degPt i ε b σ e v)| := hv1
  refine ⟨?_, hv3⟩
  simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  refine mul_pos (P.degConst_pos i hσ γ e hΔ hκ hvol) ?_
  unfold activeTruthDegDensity
  rw [Set.indicator_of_mem hv2]
  exact mul_pos (mul_pos hv1' (exp_pos _)) (exp_pos _)

/-- **Nonvanishing of the degenerate active-truth measure.** -/
theorem activeTruthDegMeasure_ne_zero (i : D.ι) (ε : Fin m → Bool) (b : Bool) (hσ : σ ≠ 0)
    (γ β η : ℝ) (e : Fin k ⊕ Fin 2 ≃ Fin m)
    (hΔ : (transMat (P.kappa i ∘ e) (D.Qexp i ∘ e)).det ≠ 0) (hκ : ∀ j, 0 < P.kappa i j)
    (hvol : 0 < volume (facePolytope (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ))
    {v₀ : Fin 2 → ℝ} (hv₀ : v₀ ∈ P.degSet i σ e)
    (hpos : 0 < P.wt i (P.degPt i ε b σ e v₀) * |P.b i (P.degPt i ε b σ e v₀)|) :
    P.activeTruthDegMeasure i ε b σ γ β η e ≠ 0 := by
  intro h0
  have := P.activeTruthDegMeasure_pos_of_open i ε b hσ γ β η e hΔ hκ hvol hv₀ hpos isOpen_univ
    (mem_univ _)
  rw [h0] at this
  simp at this

/-- **The degenerate active-truth measure gives no mass to a set the surface misses.** -/
theorem activeTruthDegMeasure_eq_zero_of_disjoint (i : D.ι) (ε : Fin m → Bool) (b : Bool)
    (σ γ β η : ℝ) (e : Fin k ⊕ Fin 2 ≃ Fin m) {O : Set (Fin (m + 1) → ℝ)} (hO : MeasurableSet O)
    (hdisj : ∀ v ∈ P.degSet i σ e, D.rep i (P.degPt i ε b σ e v) ∉ O) :
    P.activeTruthDegMeasure i ε b σ γ β η e O = 0 := by
  rw [P.activeTruthDegMeasure_apply i ε b σ γ β η e hO]
  have hmap : Measurable fun v : Fin 2 → ℝ ↦ D.rep i (P.degPt i ε b σ e v) :=
    (D.rep_cont i).measurable.comp (P.continuous_degPt i ε b σ e).measurable
  refine (setLIntegral_congr_fun (hmap hO) (g := fun _ ↦ 0) fun v hv ↦ ?_).trans lintegral_zero
  have hv' : v ∉ P.degSet i σ e := fun h ↦ hdisj v h hv
  unfold activeTruthDegDensity
  rw [Set.indicator_of_notMem hv', mul_zero, ENNReal.ofReal_zero]

end TruthChartsData.Phase

end Laplace.Multi
