/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.MixedTruthExport

/-!
# Pointwise chart-independence of the fibre kernel

The push-forward identity determines the total fibre kernel of a chart system only almost
everywhere in the truth value `s`, while the expectation theorems evaluate it along a sequence
`s = σ t^{-γ}`. Astra (round 17) separated the two tasks: *identification* (two chart expressions
represent the same push-forward measure) and *version selection* (continuity upgrades a.e.
equality to pointwise equality). This file supplies the version-selection layer:

* `eqOn_of_ae_eq_restrict_of_continuousOn`: continuous versions of an a.e.-specified function
  agree on an open set (`ℝ≥0∞`-valued; only Hausdorffness is used);
* `totalKernel_eq_of_truthCutoff`: **the cutoff route to pointwise chart-independence** — for two
  chart systems `D₁, D₂` for the same truth `T` over regions `L₁, L₂`, a bounded continuous
  observable `θ` (no support condition) and a truth cutoff `χ` with `χ(s₀) = 1` such that the
  truth-localised observable `θ · χ(T)` is supported in `L₁ ∩ L₂`, the two kernels agree AT `s₀`:
  the a.e. identity for the localised observable, continuity of both localised kernels at `s₀`,
  and the cutoff factor `χ(s₀) = 1` (`totalKernel_mul_comp_truth`);
* `totalKernel_eq_of_thin`: the same with the standard cutoff `truthCutoff ε`, for
  `0 < |s₀| ≤ ε/2` and `θ` supported in `L₁ ∩ L₂` on the thin region `{|T| < ε}`.

The support of the localised observable inside the common region is the genuine geometric
hypothesis: two regions containing a neighbourhood of the same wall point have different kernels
in general (for `T = xy` and `θ = 1` on `(-R, R)²` the kernel is `2 log(R²/|s|)`, so the
difference of two such kernels is the nonzero constant `4 log(R₂/R₁)`); the kernel is region-,
not chart-, dependent, and pointwise agreement is exactly agreement of the localised
push-forward measures with a continuous version.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace Laplace.Multi

/-- Continuous versions of an a.e.-specified function agree on an open set. -/
theorem eqOn_of_ae_eq_restrict_of_continuousOn {U : Set ℝ} (hU : IsOpen U) {K₁ K₂ : ℝ → ℝ≥0∞}
    (h₁ : ContinuousOn K₁ U) (h₂ : ContinuousOn K₂ U) (hae : K₁ =ᵐ[volume.restrict U] K₂) :
    Set.EqOn K₁ K₂ U := by
  intro s₀ hs₀
  by_contra hne
  have hpair : Tendsto (fun s ↦ (K₁ s, K₂ s)) (𝓝 s₀) (𝓝 (K₁ s₀, K₂ s₀)) :=
    (h₁.continuousAt (hU.mem_nhds hs₀)).prodMk_nhds (h₂.continuousAt (hU.mem_nhds hs₀))
  have hmem : (diagonal ℝ≥0∞)ᶜ ∈ 𝓝 (K₁ s₀, K₂ s₀) :=
    isClosed_diagonal.isOpen_compl.mem_nhds (by simpa [mem_diagonal_iff] using hne)
  have hopen : ∀ᶠ s in 𝓝 s₀, K₁ s ≠ K₂ s := by
    filter_upwards [hpair.eventually hmem] with s hs
    simpa [mem_diagonal_iff] using hs
  have hN : {s | K₁ s ≠ K₂ s} ∩ U ∈ 𝓝 s₀ := inter_mem hopen (hU.mem_nhds hs₀)
  have hpos : 0 < volume ({s | K₁ s ≠ K₂ s} ∩ U) :=
    Measure.measure_pos_of_mem_nhds (μ := volume) hN
  have hzero : (volume.restrict U) {s | K₁ s ≠ K₂ s} = 0 := ae_iff.mp hae
  rw [Measure.restrict_apply' hU.measurableSet] at hzero
  exact hpos.ne' hzero

variable {m : ℕ}

/-- **Pointwise chart-independence through a truth cutoff.** -/
theorem totalKernel_eq_of_truthCutoff {T : (Fin (m + 1) → ℝ) → ℝ} {L₁ L₂ : Set (Fin (m + 1) → ℝ)}
    (D₁ : TruthChartsData m T L₁) (D₂ : TruthChartsData m T L₂) (hT : Continuous T)
    (hL₁ : MeasurableSet L₁) (hL₂ : MeasurableSet L₂) {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞}
    (hθc : Continuous θ) {M : ℝ≥0∞} (hM : M ≠ ∞) (hθM : ∀ z, θ z ≤ M) {χ : ℝ → ℝ}
    (hχc : Continuous χ) (hχ1 : ∀ s, χ s ≤ 1)
    (hsupp : ∀ z, θ z ≠ 0 → χ (T z) ≠ 0 → z ∈ L₁ ∩ L₂) {s₀ : ℝ} (hs₀ : s₀ ≠ 0)
    (hχs : χ s₀ = 1) : D₁.totalKernel θ s₀ = D₂.totalKernel θ s₀ := by
  set θε : (Fin (m + 1) → ℝ) → ℝ≥0∞ := fun z ↦ θ z * ENNReal.ofReal (χ (T z)) with hθε
  have hθεc : Continuous θε := by
    refine continuous_iff_continuousAt.2 fun z ↦ ?_
    exact ENNReal.Tendsto.mul (hθc.tendsto z) (Or.inr ENNReal.ofReal_ne_top)
      ((ENNReal.continuous_ofReal.comp (hχc.comp hT)).tendsto z)
      (Or.inr (ne_top_of_le_ne_top hM (hθM z)))
  have hθεb : ∀ z, θε z ≤ M := fun z ↦ by
    refine (mul_le_of_le_one_right zero_le ?_).trans (hθM z)
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (hχ1 _)
  have hθεL : ∀ z, θε z ≠ 0 → z ∈ L₁ ∩ L₂ := fun z hz ↦ by
    have h1 : θ z ≠ 0 := fun h ↦ hz (by simp only [hθε, h, zero_mul])
    have h2 : χ (T z) ≠ 0 := fun h ↦ hz (by simp only [hθε, h, ENNReal.ofReal_zero, mul_zero])
    exact hsupp z h1 h2
  have hae := TruthChartsData.totalKernel_ae_eq_of_support D₁ D₂ hT.measurable hL₁ hL₂
    hθεc.measurable hθεL
  have heq : D₁.totalKernel θε s₀ = D₂.totalKernel θε s₀ :=
    eq_of_ae_eq_of_continuousAt hae
      (D₁.continuousAt_totalKernel hθεc hM hθεb (fun z hz ↦ (hθεL z hz).1) hs₀)
      (D₂.continuousAt_totalKernel hθεc hM hθεb (fun z hz ↦ (hθεL z hz).2) hs₀)
  have hcut : ∀ {L : Set (Fin (m + 1) → ℝ)} (D : TruthChartsData m T L),
      D.totalKernel θε s₀ = D.totalKernel θ s₀ := fun D ↦ by
    rw [hθε, TruthChartsData.totalKernel_mul_comp_truth D θ (fun s ↦ ENNReal.ofReal (χ s))
      ENNReal.ofReal_ne_top, hχs, ENNReal.ofReal_one, one_mul]
  rwa [hcut, hcut] at heq

/-- **Pointwise chart-independence on the thin region.** With the standard cutoff, two chart
systems whose regions both contain the part of the support of `θ` inside `{|T| < ε}` have the
same kernel at every `s₀` with `0 < |s₀| ≤ ε/2`. -/
theorem totalKernel_eq_of_thin {T : (Fin (m + 1) → ℝ) → ℝ} {L₁ L₂ : Set (Fin (m + 1) → ℝ)}
    (D₁ : TruthChartsData m T L₁) (D₂ : TruthChartsData m T L₂) (hT : Continuous T)
    (hL₁ : MeasurableSet L₁) (hL₂ : MeasurableSet L₂) {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞}
    (hθc : Continuous θ) {M : ℝ≥0∞} (hM : M ≠ ∞) (hθM : ∀ z, θ z ≤ M) {ε : ℝ} (hε : 0 < ε)
    (hsupp : ∀ z, θ z ≠ 0 → |T z| < ε → z ∈ L₁ ∩ L₂) {s₀ : ℝ} (hs₀ : s₀ ≠ 0)
    (hs₀ε : |s₀| ≤ ε / 2) : D₁.totalKernel θ s₀ = D₂.totalKernel θ s₀ :=
  totalKernel_eq_of_truthCutoff D₁ D₂ hT hL₁ hL₂ hθc hM hθM (continuous_truthCutoff ε)
    (truthCutoff_le_one ε)
    (fun z h1 h2 ↦ hsupp z h1 (abs_lt_of_truthCutoff_ne_zero hε h2)) hs₀
    (truthCutoff_eq_one hε hs₀ε)

/-- The kernels agree on the whole punctured window `0 < |s| ≤ ε/2`. -/
theorem totalKernel_eqOn_of_thin {T : (Fin (m + 1) → ℝ) → ℝ} {L₁ L₂ : Set (Fin (m + 1) → ℝ)}
    (D₁ : TruthChartsData m T L₁) (D₂ : TruthChartsData m T L₂) (hT : Continuous T)
    (hL₁ : MeasurableSet L₁) (hL₂ : MeasurableSet L₂) {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞}
    (hθc : Continuous θ) {M : ℝ≥0∞} (hM : M ≠ ∞) (hθM : ∀ z, θ z ≤ M) {ε : ℝ} (hε : 0 < ε)
    (hsupp : ∀ z, θ z ≠ 0 → |T z| < ε → z ∈ L₁ ∩ L₂) :
    Set.EqOn (D₁.totalKernel θ) (D₂.totalKernel θ) {s | s ≠ 0 ∧ |s| ≤ ε / 2} := fun _ hs ↦
  totalKernel_eq_of_thin D₁ D₂ hT hL₁ hL₂ hθc hM hθM hε hsupp hs.1 hs.2

end Laplace.Multi
