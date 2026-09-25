/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.CoefficientResponse
import Laplace.Multi.ActiveTruthTraceTheorem

/-!
# The mixture-weight response of the active-truth trace regime

The active-truth trace theorem (`tendsto_modelKernel_trace`) gives the leading constant of a chart
kernel in the trace regime as

  `A Γ(β) B^{-β} q D^{-qη} vol(F)/|det M| · ∫_0^ρ u^{qη-1} w(u) a(u)^{-β} du`,

with `a` the unit of the phase along the truth segment. When the loss is a mixture
`L_a = ∑ aᵢ fᵢ` of populations with a common resolution, the unit is affine in the mixture weight,
`a(u) = U_a(u) = ∑ aᵢ hᵢ(u)`, and the constant is exactly the face coefficient of
`CoefficientResponse` for the face measure `u^{qη-1} du` on `(0, ρ)`:

  `∫_0^ρ u^{qη-1} w U_a^{-β} du = faceCoef (traceFaceMeasure ρ (qη − 1)) w h β a`
  (`trace_integral_eq_faceCoef`).

Consequently the leading constant of the trace regime is differentiable in the mixture weight,
with the explicit differential `−β C₀ ∫_0^ρ u^{qη-1} w U_a^{-β-1} R_v du`
(`hasDerivAt_traceConstant`), and the limiting posterior on the truth segment obeys the
**singular fluctuation–response identity** `d/dε ⟨w⟩_{a+εv} = −β Cov_{ν_a}(w, R_v / U_a)`
(`hasDerivAt_tracePosterior`) — the first instance of the coefficient-response calculus on an
actual term of the atlas.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The face measure of the truth segment: `u^e du` on `(0, ρ)`. -/
noncomputable def traceFaceMeasure (ρ e : ℝ) : Measure ℝ :=
  (volume.restrict (Ioo (0 : ℝ) ρ)).withDensity fun u ↦ ENNReal.ofReal (u ^ e)

theorem integrableOn_rpow_Ioo {ρ e : ℝ} (hρ : 0 < ρ) (he : -1 < e) :
    IntegrableOn (fun u : ℝ ↦ u ^ e) (Ioo 0 ρ) := by
  have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ρ) he)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hρ.le] at this
  exact this.mono_set Ioo_subset_Ioc_self

theorem isFiniteMeasure_traceFaceMeasure {ρ e : ℝ} (hρ : 0 < ρ) (he : -1 < e) :
    IsFiniteMeasure (traceFaceMeasure ρ e) := by
  unfold traceFaceMeasure
  exact isFiniteMeasure_withDensity_ofReal (integrableOn_rpow_Ioo hρ he).hasFiniteIntegral

theorem measurable_ofReal_rpow (e : ℝ) : Measurable fun u : ℝ ↦ ENNReal.ofReal (u ^ e) :=
  ENNReal.measurable_ofReal.comp (measurable_id.pow_const e)

/-- An integral against the face measure is the weighted integral on `(0, ρ)`. -/
theorem integral_traceFaceMeasure {ρ e : ℝ} (g : ℝ → ℝ) :
    ∫ u, g u ∂(traceFaceMeasure ρ e) = ∫ u in Ioo (0 : ℝ) ρ, u ^ e * g u := by
  unfold traceFaceMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀ (f := fun u ↦ ENNReal.ofReal (u ^ e))
    (measurable_ofReal_rpow e).aemeasurable
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) g]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu ↦ ?_
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hu.1.le e)]

/-- The face measure of the truth segment has positive total mass. -/
theorem traceFaceMeasure_univ_pos {ρ e : ℝ} (hρ : 0 < ρ) : 0 < traceFaceMeasure ρ e univ := by
  unfold traceFaceMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_pos_iff_support (measurable_ofReal_rpow e), Measure.restrict_apply' measurableSet_Ioo]
  have hsub : Ioo (0 : ℝ) ρ ⊆ Function.support fun u : ℝ ↦ ENNReal.ofReal (u ^ e) := fun u hu ↦ by
    rw [Function.mem_support]
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hu.1 e)).ne'
  rw [Set.inter_eq_right.mpr hsub, Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (by linarith)

theorem integrable_traceFaceMeasure_of_bounded {ρ e : ℝ} (hρ : 0 < ρ) (he : -1 < e) {w : ℝ → ℝ}
    (hwm : Measurable w) {W : ℝ} (hwb : ∀ u, |w u| ≤ W) : Integrable w (traceFaceMeasure ρ e) := by
  have := isFiniteMeasure_traceFaceMeasure hρ he
  exact (integrable_const W).mono' hwm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u ↦ by rw [Real.norm_eq_abs]; exact hwb u)

variable {ι : Type*} [Fintype ι]

theorem measurable_faceUnit_of {h : ι → ℝ → ℝ} (hhm : ∀ i, Measurable (h i)) (a : ι → ℝ) :
    Measurable (faceUnit h a) :=
  Finset.measurable_sum Finset.univ fun i _ ↦ (hhm i).const_mul (a i)

/-- **The trace integral is a face coefficient**: `∫_0^ρ u^e w U_a^{-β} = μ_a(w)` for the face
measure `u^e du`. -/
theorem trace_integral_eq_faceCoef {ρ e β : ℝ} {h : ι → ℝ → ℝ} (w : ℝ → ℝ) (a : ι → ℝ) :
    ∫ u in Ioo (0 : ℝ) ρ, u ^ e * (w u * faceUnit h a u ^ (-β)) =
      faceCoef (traceFaceMeasure ρ e) w h β a := by
  unfold faceCoef
  rw [integral_traceFaceMeasure]

/-- The face data of the truth segment for an affine unit bounded below. -/
theorem faceData_trace {ρ e : ℝ} (hρ : 0 < ρ) (he : -1 < e) {h : ι → ℝ → ℝ}
    (hhm : ∀ i, Measurable (h i)) {Mh : ℝ} (hhb : ∀ i u, |h i u| ≤ Mh) {a : ι → ℝ} {c : ℝ}
    (hc : 0 < c) (hU : ∀ u, c ≤ faceUnit h a u) : FaceData (traceFaceMeasure ρ e) h a c Mh where
  finite := isFiniteMeasure_traceFaceMeasure hρ he
  h_meas := hhm
  h_bound := hhb
  c_pos := hc
  unit_ge := hU

/-- The normaliser `μ_a(1) = ∫ U_a^{-β}` on the truth segment is positive. -/
theorem faceCoef_one_trace_pos {ρ e β : ℝ} (hρ : 0 < ρ) (he : -1 < e) (hβ : 0 ≤ β)
    {h : ι → ℝ → ℝ} (hhm : ∀ i, Measurable (h i)) {a : ι → ℝ} {c : ℝ} (hc : 0 < c)
    (hU : ∀ u, c ≤ faceUnit h a u) :
    0 < faceCoef (traceFaceMeasure ρ e) (fun _ ↦ 1) h β a := by
  have := isFiniteMeasure_traceFaceMeasure hρ he
  unfold faceCoef
  simp only [one_mul]
  have hpos : ∀ u, 0 < faceUnit h a u ^ (-β) := fun u ↦
    Real.rpow_pos_of_pos (hc.trans_le (hU u)) _
  have hint : Integrable (fun u ↦ faceUnit h a u ^ (-β)) (traceFaceMeasure ρ e) :=
    integrable_traceFaceMeasure_of_bounded hρ he ((measurable_faceUnit_of hhm a).pow_const _)
      (W := c ^ (-β)) fun u ↦ by
        rw [abs_of_pos (hpos u)]
        exact rpow_le_rpow_of_le_of_nonpos hc (hU u) (neg_nonpos.mpr hβ)
  rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun u ↦ (hpos u).le)
    hint]
  have hsupp : Function.support (fun u ↦ faceUnit h a u ^ (-β)) = univ :=
    Set.eq_univ_iff_forall.mpr fun u ↦ (hpos u).ne'
  rw [hsupp]
  exact traceFaceMeasure_univ_pos hρ

/-- **The leading constant of the trace regime for a mixture is a face coefficient.** -/
theorem tendsto_modelKernel_trace_mixture {k : ℕ} {ρ A B D γ p q δ β η : ℝ}
    {Q κ r : Fin k ⊕ Fin 2 → ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hB : 0 < B) (hβ : 0 < β)
    (hη : 0 < η) (hδ : 0 ≤ δ) (hκ : ∀ i, 0 < κ i) (hΔ : (transMat κ Q).det ≠ 0)
    (hc₀ : fibreCoef κ Q 0 ≠ 0 ∨ fibreA κ Q δ γ 0 ≠ 0)
    (hc₁ : fibreCoef κ Q 1 ≠ 0 ∨ fibreA κ Q δ γ 1 ≠ 0)
    (hr : ∀ i, r i + 1 = β * κ i - η * Q i) {w : ℝ → ℝ} {Wstar : ℝ} (hwm : Measurable w)
    (hw : ∀ u ∈ Ioo (0 : ℝ) ρ, 0 ≤ w u ∧ w u ≤ Wstar) {h : ι → ℝ → ℝ}
    (hhm : ∀ i, Measurable (h i)) {a : ι → ℝ} {amin : ℝ} (hamin : 0 < amin)
    (hU : ∀ u, amin ≤ faceUnit h a u) :
    Tendsto (fun t ↦ t ^ (γ * p + (β * δ - η * γ)) / Real.log t ^ k *
        modelKernel ρ A B D γ p q δ Q κ r (fun _ u ↦ w u) (fun _ u ↦ faceUnit h a u) t) atTop
      (𝓝 (A * Real.Gamma β * B ^ (-β) * q * D ^ (-(q * η)) *
        (volume (facePolytope κ Q δ γ)).toReal / |(transMat κ Q).det| *
        faceCoef (traceFaceMeasure ρ (q * η - 1)) w h β a)) := by
  have := tendsto_modelKernel_trace (A := A) (p := p) hρ hD hq hB hβ hη hδ hκ hΔ hc₀ hc₁ hr hamin
    hwm (measurable_faceUnit_of hhm a) hw (fun u _ ↦ hU u)
  rwa [trace_integral_eq_faceCoef] at this

/-- **The leading constant of the trace regime is differentiable in the mixture weight**, with
differential `−β C₀ ∫_0^ρ u^e w U_a^{-β-1} R_v du`. -/
theorem hasDerivAt_traceConstant [Nonempty ι] {ρ e β C₀ : ℝ} (hρ : 0 < ρ) (he : -1 < e)
    (hβ : 0 ≤ β) {h : ι → ℝ → ℝ} (hhm : ∀ i, Measurable (h i)) {Mh : ℝ}
    (hhb : ∀ i u, |h i u| ≤ Mh) {a : ι → ℝ} {c : ℝ} (hc : 0 < c) (hU : ∀ u, c ≤ faceUnit h a u)
    {w : ℝ → ℝ} (hwm : Measurable w) {W : ℝ} (hwb : ∀ u, |w u| ≤ W) (v : ι → ℝ) :
    HasDerivAt (fun ε : ℝ ↦ C₀ * faceCoef (traceFaceMeasure ρ e) w h β (a + ε • v))
      (C₀ * (-β * ∫ u, w u * faceUnit h a u ^ (-β - 1) * faceUnit h v u
        ∂(traceFaceMeasure ρ e))) 0 :=
  ((faceData_trace hρ he hhm hhb hc hU).hasDerivAt_faceCoef
    (integrable_traceFaceMeasure_of_bounded hρ he hwm hwb) hβ v).const_mul C₀

/-- **The singular fluctuation–response identity on the truth segment**: the limiting posterior
`w ↦ μ_a(w)/μ_a(1)` of the trace regime has differential `−β Cov_{ν_a}(w, R_v / U_a)` in the
mixture weight. -/
theorem hasDerivAt_tracePosterior [Nonempty ι] {ρ e β : ℝ} (hρ : 0 < ρ) (he : -1 < e)
    (hβ : 0 ≤ β) {h : ι → ℝ → ℝ} (hhm : ∀ i, Measurable (h i)) {Mh : ℝ}
    (hhb : ∀ i u, |h i u| ≤ Mh) {a : ι → ℝ} {c : ℝ} (hc : 0 < c) (hU : ∀ u, c ≤ faceUnit h a u)
    {w : ℝ → ℝ} (hwm : Measurable w) {W : ℝ} (hwb : ∀ u, |w u| ≤ W) (v : ι → ℝ) :
    HasDerivAt (fun ε : ℝ ↦ facePosterior (traceFaceMeasure ρ e) w h β (a + ε • v))
      (-β * faceCov (traceFaceMeasure ρ e) w (fun u ↦ faceUnit h v u / faceUnit h a u) h β a)
      0 :=
  (faceData_trace hρ he hhm hhb hc hU).hasDerivAt_facePosterior
    (integrable_traceFaceMeasure_of_bounded hρ he hwm hwb) hβ v
    (faceCoef_one_trace_pos hρ he hβ hhm hc hU).ne'

end Laplace.Multi
