/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ExpectationValuesKnow
import Laplace.Multi.ActiveTruthLPChart

/-!
# Support-separated distinguishability of active-truth faces

Two certified phases whose leading measures are separated by an open set — one charges an open
`O ⊆ L'`, the other gives it no mass — have distinguishable leading expectations: some continuous
nonnegative bounded observable supported in `L'` has fibre ratios whose difference does not tend
to `0` (`exists_observable_of_separated`, through `normalise_restrict_eq_iff_forall_tendsto`:
equal normalised leading measures would give equal masses to `O`). For active-truth faces the
separation is read off the truth segments: the active-truth measure of a chart charges every open
set meeting its truth segment at a point of positive weight (`activeTruthMeasure_pos_of_open`)
and gives no mass to a set the truth segment misses (`activeTruthMeasure_eq_zero_of_disjoint`);
the leading measure of a certificate dominates the measure of each of its leading terms
(`le_leadingMeasure_of_leading`). `exists_observable_of_activeTruth_separated` assembles these:
a leading active-truth term of the first phase whose truth segment meets an open `O ⊆ L'` with
positive weight, against a second phase whose leading measure vanishes on `O`.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

/-- Equal normalised restrictions give proportional masses: a set charged by the first measure
and null for the second separates them. -/
theorem normalise_restrict_ne_of_separated {X : Type*} [MeasurableSpace X] {μ₁ μ₂ : Measure X}
    {L' O : Set X} (hO : MeasurableSet O) (hfin : μ₁ L' ≠ ⊤) (h₁ : 0 < μ₁ (O ∩ L'))
    (h₂ : μ₂ (O ∩ L') = 0) :
    normaliseMeasure (μ₁.restrict L') ≠ normaliseMeasure (μ₂.restrict L') := by
  intro h
  have := congrArg (fun ν : Measure X ↦ ν O) h
  simp only [normaliseMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
    Measure.restrict_apply hO, smul_eq_mul, h₂, mul_zero] at this
  exact (mul_ne_zero (ENNReal.inv_ne_zero.mpr hfin) h₁.ne') this

namespace TruthChartsData.Phase.TermMeasureCertificate

variable {m : ℕ} {L' : Set (Fin (m + 1) → ℝ)}
  {T : (Fin (m + 1) → ℝ) → ℝ} {D₁ D₂ : TruthChartsData m T L'} {F₁ F₂ : (Fin (m + 1) → ℝ) → ℝ}
  {P₁ : D₁.Phase F₁} {P₂ : D₂.Phase F₂} {σ₁ γ₁ σ₂ γ₂ : ℝ}
  (C₁ : P₁.TermMeasureCertificate σ₁ γ₁) (C₂ : P₂.TermMeasureCertificate σ₂ γ₂)

/-- The leading measure dominates the measure of each leading term. -/
theorem le_leadingMeasure_of_leading {T : (Fin (m + 1) → ℝ) → ℝ}
    {D : TruthChartsData m T L'} {F : (Fin (m + 1) → ℝ) → ℝ}
    {P : D.Phase F} {σ γ : ℝ} (C : P.TermMeasureCertificate σ γ) {p : TermIdx D}
    (hlam : C.lam p = C.lam₀) (hk : C.kk p = C.k₀) (s : Set (Fin (m + 1) → ℝ)) :
    C.μ p s ≤ C.leadingMeasure s := by
  classical
  unfold leadingMeasure lexMeasure
  rw [Measure.finsetSum_apply]
  exact Finset.single_le_sum (f := fun q ↦ C.μ q s) (fun _ _ ↦ zero_le)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hlam, hk⟩)

/-- **Support-separated distinguishability.** If the leading measure of the first phase charges an
open `O ⊆ L'` that is null for the leading measure of the second, some observable supported in
`L'` has fibre ratios whose difference does not tend to `0`. -/
theorem exists_observable_of_separated (hL' : IsOpen L')
    (hS₁ : ∀ i, |D₁.S i| = 1) (hF₁ : ∀ z, 0 ≤ F₁ z) (hFm₁ : Measurable F₁) (hσ₁ : σ₁ ≠ 0)
    (hS₂ : ∀ i, |D₂.S i| = 1) (hF₂ : ∀ z, 0 ≤ F₂ z) (hFm₂ : Measurable F₂) (hσ₂ : σ₂ ≠ 0)
    {χ : (Fin (m + 1) → ℝ) → ℝ} (hχc : Continuous χ) (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ}
    (hMχ : ∀ z, χ z ≤ Mχ) (hχL : ∀ z, χ z ≠ 0 → z ∈ L')
    (hpos₁ : 0 < ∫ z, χ z ∂C₁.leadingMeasure) (hpos₂ : 0 < ∫ z, χ z ∂C₂.leadingMeasure)
    {O : Set (Fin (m + 1) → ℝ)} (hO : MeasurableSet O) (h₁ : 0 < C₁.leadingMeasure (O ∩ L'))
    (h₂ : C₂.leadingMeasure (O ∩ L') = 0) :
    ∃ ψ : (Fin (m + 1) → ℝ) → ℝ, Continuous ψ ∧ (∀ z, 0 ≤ ψ z) ∧ (∃ M, ∀ z, ψ z ≤ M) ∧
      (∀ z, ψ z ≠ 0 → z ∈ L') ∧
      ¬ Tendsto (fun t ↦ D₁.fibreRatio F₁ ψ χ σ₁ γ₁ t - D₂.fibreRatio F₂ ψ χ σ₂ γ₂ t) atTop
        (𝓝 0) := by
  by_contra hcon
  have hall : ∀ ψ : (Fin (m + 1) → ℝ) → ℝ, Continuous ψ → (∀ z, 0 ≤ ψ z) →
      (∃ M, ∀ z, ψ z ≤ M) → (∀ z, ψ z ≠ 0 → z ∈ L') →
      Tendsto (fun t ↦ D₁.fibreRatio F₁ ψ χ σ₁ γ₁ t - D₂.fibreRatio F₂ ψ χ σ₂ γ₂ t) atTop
        (𝓝 0) := fun ψ hψc hψ hM hψL =>
    of_not_not fun hn => hcon ⟨ψ, hψc, hψ, hM, hψL, hn⟩
  have hnorm := (C₁.normalise_restrict_eq_iff_forall_tendsto C₂ hL' hS₁ hF₁ hFm₁ hσ₁ hS₂ hF₂
    hFm₂ hσ₂ hχc hχ hMχ hχL hpos₁ hpos₂).mpr hall
  exact normalise_restrict_ne_of_separated hO (measure_ne_top _ _) h₁ h₂ hnorm

end TruthChartsData.Phase.TermMeasureCertificate

namespace TruthChartsData.Phase

variable {m k : ℕ} {L' : Set (Fin (m + 1) → ℝ)} {T : (Fin (m + 1) → ℝ) → ℝ}
  {D : TruthChartsData m T L'}
  {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F) {σ γ β η : ℝ}

/-- The truth segment of a chart, as a map `(0, ρ) → ℝ^{m+1}` extended to `ℝ`. -/
theorem continuous_truthSegment (i : D.ι) (ε : Fin m → Bool) (b : Bool) :
    Continuous fun u : ℝ ↦ D.rep i (D.bridgePt i ε b 0 u) :=
  (D.rep_cont i).comp (continuous_truthPt (D := D) i ε b)

/-- The active-truth measure of a measurable set is the weighted volume of its preimage under
the truth segment. -/
theorem activeTruthMeasure_apply (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ β η : ℝ)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) {O : Set (Fin (m + 1) → ℝ)} (hO : MeasurableSet O) :
    P.activeTruthMeasure i ε b σ γ β η e O =
      ∫⁻ u in (fun u : ℝ ↦ D.rep i (D.bridgePt i ε b 0 u)) ⁻¹' O,
        ENNReal.ofReal (P.activeTruthDensity i ε b σ γ β η e u) := by
  unfold activeTruthMeasure
  rw [Measure.map_apply (continuous_truthSegment (D := D) i ε b).measurable hO,
    withDensity_apply _ ((continuous_truthSegment (D := D) i ε b).measurable hO)]

/-- **The active-truth measure charges every open set meeting the truth segment** at a point of
positive weight. -/
theorem activeTruthMeasure_pos_of_open (i : D.ι) (ε : Fin m → Bool) (b : Bool) (hσ : σ ≠ 0)
    (hβ : 0 < β) (e : Fin k ⊕ Fin 2 ≃ Fin m) (hκ : ∀ j, 0 < P.kappa i j)
    (hΔ : (transMat (P.kappa i ∘ e) (D.Qexp i ∘ e)).det ≠ 0)
    (hvol : 0 < volume (facePolytope (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ))
    {u₀ : ℝ} (hu₀ : u₀ ∈ Ioo (0 : ℝ) (D.ρ i))
    (hpos : 0 < P.wt i (D.bridgePt i ε b 0 u₀) * |P.b i (D.bridgePt i ε b 0 u₀)|)
    {O : Set (Fin (m + 1) → ℝ)} (hO : IsOpen O) (hmem : D.rep i (D.bridgePt i ε b 0 u₀) ∈ O) :
    0 < P.activeTruthMeasure i ε b σ γ β η e O := by
  have hm : Measurable fun u ↦ ENNReal.ofReal (P.activeTruthDensity i ε b σ γ β η e u) :=
    ENNReal.measurable_ofReal.comp (P.measurable_activeTruthDensity i ε b σ γ β η e)
  rw [P.activeTruthMeasure_apply i ε b σ γ β η e hO.measurableSet, setLIntegral_pos_iff hm]
  have hpt := continuous_truthPt (D := D) i ε b
  have hg : Continuous fun u ↦ P.wt i (D.bridgePt i ε b 0 u) * |P.b i (D.bridgePt i ε b 0 u)| :=
    ((P.wt_cont i).comp hpt).mul (continuous_abs.comp ((P.b_cont i).comp hpt))
  have hU : IsOpen {u | 0 < P.wt i (D.bridgePt i ε b 0 u) * |P.b i (D.bridgePt i ε b 0 u)|} :=
    isOpen_lt continuous_const hg
  have hpre : IsOpen ((fun u : ℝ ↦ D.rep i (D.bridgePt i ε b 0 u)) ⁻¹' O) :=
    hO.preimage (continuous_truthSegment (D := D) i ε b)
  refine lt_of_lt_of_le (((hU.inter isOpen_Ioo).inter hpre).measure_pos volume
    ⟨u₀, ⟨hpos, hu₀⟩, hmem⟩) (measure_mono fun u hu ↦ ?_)
  obtain ⟨⟨hu1, hu2⟩, hu3⟩ := hu
  have hu1' : 0 < P.wt i (D.bridgePt i ε b 0 u) * |P.b i (D.bridgePt i ε b 0 u)| := hu1
  refine ⟨?_, hu3⟩
  simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  unfold activeTruthDensity
  rw [Set.indicator_of_mem hu2]
  unfold activeTruthDensityFn
  have hA := P.constA_pos (i := i) hσ
  have hΓ := Real.Gamma_pos_of_pos hβ
  have hB : 0 < P.constB i σ ^ (-β) := Real.rpow_pos_of_pos (P.constB_pos hσ) _
  have hq : (0 : ℝ) < D.q i (D.k i) := Nat.cast_pos.mpr (D.q_pos i)
  have hD : 0 < D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (abs_pos.mpr hσ) _) _
  have hF := P.faceConst_pos i γ e hκ hΔ hvol
  have hu : 0 < u ^ ((D.q i (D.k i) : ℝ) * η - 1) := Real.rpow_pos_of_pos hu2.1 _
  have ha : 0 < |P.a i (D.bridgePt i ε b 0 u)| ^ (-β) :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le (P.ma_pos i)
      (P.ma_le_unitFn_of_mem_ball (truthPt_mem_ball (D := D) i ε b hu2))) _
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hA hΓ) hB) hq) hD) hF)
    (mul_pos hu (mul_pos hu1' ha))

/-- **The active-truth measure gives no mass to a set the truth segment misses.** -/
theorem activeTruthMeasure_eq_zero_of_disjoint (i : D.ι) (ε : Fin m → Bool) (b : Bool)
    (σ γ β η : ℝ) (e : Fin k ⊕ Fin 2 ≃ Fin m) {O : Set (Fin (m + 1) → ℝ)} (hO : MeasurableSet O)
    (hdisj : ∀ u ∈ Ioo (0 : ℝ) (D.ρ i), D.rep i (D.bridgePt i ε b 0 u) ∉ O) :
    P.activeTruthMeasure i ε b σ γ β η e O = 0 := by
  rw [P.activeTruthMeasure_apply i ε b σ γ β η e hO]
  refine (setLIntegral_congr_fun ((continuous_truthSegment (D := D) i ε b).measurable hO)
    (g := fun _ ↦ 0) fun u hu ↦ ?_).trans lintegral_zero
  have hu' : u ∉ Ioo (0 : ℝ) (D.ρ i) := fun h ↦ hdisj u h hu
  unfold activeTruthDensity
  rw [Set.indicator_of_notMem hu', ENNReal.ofReal_zero]

end TruthChartsData.Phase

namespace TruthChartsData.Phase.TermMeasureCertificate

variable {m k : ℕ} {L' : Set (Fin (m + 1) → ℝ)}
  {T : (Fin (m + 1) → ℝ) → ℝ} {D₁ D₂ : TruthChartsData m T L'} {F₁ F₂ : (Fin (m + 1) → ℝ) → ℝ}
  {P₁ : D₁.Phase F₁} {P₂ : D₂.Phase F₂} {σ₁ γ₁ σ₂ γ₂ β η : ℝ}
  (C₁ : P₁.TermMeasureCertificate σ₁ γ₁) (C₂ : P₂.TermMeasureCertificate σ₂ γ₂)

/-- **Distinguishability of active-truth faces.** A leading term of the first phase whose
coefficient measure is the active-truth measure of a chart, with a truth-segment point of
positive weight inside an open `O ⊆ L'` null for the leading measure of the second phase, gives an
observable supported in `L'` whose fibre ratios are not asymptotically equal. -/
theorem exists_observable_of_activeTruth_separated (hL' : IsOpen L')
    (hS₁ : ∀ i, |D₁.S i| = 1) (hF₁ : ∀ z, 0 ≤ F₁ z) (hFm₁ : Measurable F₁) (hσ₁ : σ₁ ≠ 0)
    (hS₂ : ∀ i, |D₂.S i| = 1) (hF₂ : ∀ z, 0 ≤ F₂ z) (hFm₂ : Measurable F₂) (hσ₂ : σ₂ ≠ 0)
    {χ : (Fin (m + 1) → ℝ) → ℝ} (hχc : Continuous χ) (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ}
    (hMχ : ∀ z, χ z ≤ Mχ) (hχL : ∀ z, χ z ≠ 0 → z ∈ L')
    (hpos₁ : 0 < ∫ z, χ z ∂C₁.leadingMeasure) (hpos₂ : 0 < ∫ z, χ z ∂C₂.leadingMeasure)
    {p : TermIdx D₁} (hlam : C₁.lam p = C₁.lam₀) (hk : C₁.kk p = C₁.k₀)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) (hμ : C₁.μ p = P₁.activeTruthMeasure p.1 p.2.1 p.2.2 σ₁ γ₁ β η e)
    (hβ : 0 < β) (hκ : ∀ j, 0 < P₁.kappa p.1 j)
    (hΔ : (transMat (P₁.kappa p.1 ∘ e) (D₁.Qexp p.1 ∘ e)).det ≠ 0)
    (hvol : 0 < volume (facePolytope (P₁.kappa p.1 ∘ e) (D₁.Qexp p.1 ∘ e) (P₁.phaseExp p.1 γ₁)
      γ₁))
    {u₀ : ℝ} (hu₀ : u₀ ∈ Ioo (0 : ℝ) (D₁.ρ p.1))
    (hpos : 0 < P₁.wt p.1 (D₁.bridgePt p.1 p.2.1 p.2.2 0 u₀) *
      |P₁.b p.1 (D₁.bridgePt p.1 p.2.1 p.2.2 0 u₀)|)
    {O : Set (Fin (m + 1) → ℝ)} (hO : IsOpen O) (hOL : O ⊆ L')
    (hmem : D₁.rep p.1 (D₁.bridgePt p.1 p.2.1 p.2.2 0 u₀) ∈ O) (h₂ : C₂.leadingMeasure O = 0) :
    ∃ ψ : (Fin (m + 1) → ℝ) → ℝ, Continuous ψ ∧ (∀ z, 0 ≤ ψ z) ∧ (∃ M, ∀ z, ψ z ≤ M) ∧
      (∀ z, ψ z ≠ 0 → z ∈ L') ∧
      ¬ Tendsto (fun t ↦ D₁.fibreRatio F₁ ψ χ σ₁ γ₁ t - D₂.fibreRatio F₂ ψ χ σ₂ γ₂ t) atTop
        (𝓝 0) := by
  have hOL' : O ∩ L' = O := inter_eq_left.mpr hOL
  refine C₁.exists_observable_of_separated C₂ hL' hS₁ hF₁ hFm₁ hσ₁ hS₂ hF₂ hFm₂ hσ₂ hχc hχ hMχ
    hχL hpos₁ hpos₂ hO.measurableSet ?_ (by rw [hOL']; exact h₂)
  rw [hOL']
  refine lt_of_lt_of_le ?_ (C₁.le_leadingMeasure_of_leading hlam hk O)
  rw [hμ]
  exact P₁.activeTruthMeasure_pos_of_open p.1 p.2.1 p.2.2 hσ₁ hβ e hκ hΔ hvol hu₀ hpos hO hmem

end TruthChartsData.Phase.TermMeasureCertificate

end Laplace.Multi
