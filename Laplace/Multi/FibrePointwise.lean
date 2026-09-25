/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FibreContinuity

/-!
# The pointwise fibre identity off the wall

For a continuous bounded `θ ≥ 0` supported in the region `L' = {z | z ℓ ∈ B, z' ∈ A}` (read through
the coordinate splitting at `ℓ`) and inside a ball, the chart integrands of a `WallChartsData` are
continuous, bounded and supported in the open boxes (`chartFun_eq`, `continuous_chartFun`), so the
total fibre kernel is continuous at every `s ≠ 0` (`continuousAt_totalKernel`); the ambient fibre
integral `s ↦ ∫⁻_{z' ∈ A} θ(z', s)` is continuous everywhere (`continuous_ambientFibre`). Two
continuous functions that agree almost everywhere on an open set agree on it, so the fibre identity
holds at EVERY `s ∈ interior B`, `s ≠ 0` (`WallChartsData.fibre_eqOn`, `fibre_eq`): the ambient
fibre integral over the physical parameters at truth `s` is the sum of the chart kernels.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

variable {m : ℕ}

/-- The ambient fibre integral `s ↦ ∫⁻_{z' ∈ A} θ(insertNth ℓ s z')` is continuous, for continuous
bounded `θ` vanishing outside a ball. -/
theorem continuous_ambientFibre (ℓ : Fin (m + 1)) (A : Set (Fin m → ℝ))
    {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hθc : Continuous θ) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hθM : ∀ z, θ z ≤ M) {R : ℝ} (hθR : ∀ z, θ z ≠ 0 → ‖z‖ < R) :
    Continuous fun s ↦ ∫⁻ z' in A, θ (ℓ.insertNth s z') := by
  refine continuous_iff_continuousAt.mpr fun s₀ ↦ ?_
  have hins : ∀ z', Continuous fun s ↦ θ (ℓ.insertNth s z') := fun z' ↦
    hθc.comp (Continuous.finInsertNth (A := fun _ : Fin (m + 1) ↦ ℝ) ℓ (f := id)
      (g := fun _ ↦ z') continuous_id continuous_const)
  have hmeas : ∀ s, Measurable fun z' : Fin m → ℝ ↦ θ (ℓ.insertNth s z') := fun s ↦
    (hθc.comp (Continuous.finInsertNth (A := fun _ : Fin (m + 1) ↦ ℝ) ℓ (f := fun _ ↦ s)
      (g := id) continuous_const continuous_id)).measurable
  refine tendsto_lintegral_filter_of_dominated_convergence
    ((Metric.closedBall (0 : Fin m → ℝ) R).indicator (fun _ ↦ M))
    (Eventually.of_forall fun s ↦ hmeas s) (Eventually.of_forall fun s ↦ ?_) ?_
    (Eventually.of_forall fun z' ↦ (hins z').continuousAt)
  · refine Eventually.of_forall fun z' ↦ ?_
    by_cases h0 : θ (ℓ.insertNth s z') = 0
    · rw [h0]; exact zero_le
    · have hz : ‖z'‖ ≤ R := by
        refine le_of_lt (lt_of_le_of_lt ?_ (hθR _ h0))
        rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
        intro j
        have := norm_le_pi_norm (ℓ.insertNth s z' : Fin (m + 1) → ℝ) (ℓ.succAbove j)
        rwa [Fin.insertNth_apply_succAbove] at this
      rw [indicator_of_mem (mem_closedBall_zero_iff.mpr hz)]
      exact hθM _
  · rw [lintegral_indicator_const measurableSet_closedBall]
    exact ENNReal.mul_ne_top hM measure_closedBall_lt_top.ne

namespace TruthChartsData

variable {T : (Fin (m + 1) → ℝ) → ℝ} {L' : Set (Fin (m + 1) → ℝ)} (D : TruthChartsData m T L')

/-- For `θ` supported in `L'`, the chart integrand is `θ ∘ rep · dens` without the indicator. -/
theorem chartFun_eq {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hθL : ∀ z, θ z ≠ 0 → z ∈ L') (i : D.ι) :
    D.chartFun θ i = fun u ↦ θ (D.rep i u) * ENNReal.ofReal (D.dens i u) := by
  funext u
  unfold TruthChartsData.chartFun
  by_cases hu : u ∈ D.dom i
  · rw [indicator_of_mem hu]
  · rw [indicator_of_notMem hu]
    by_cases hd : D.dens i u = 0
    · rw [hd, ENNReal.ofReal_zero, mul_zero]
    · by_cases hθ : θ (D.rep i u) = 0
      · rw [hθ, zero_mul]
      · exfalso
        apply hu
        rw [D.dom_eq i]
        exact ⟨Metric.ball_subset_closedBall (D.dens_supp i u hd), hθL _ hθ⟩

/-- The densities are bounded. -/
theorem exists_dens_bound (i : D.ι) : ∃ C : ℝ, ∀ u, D.dens i u ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i)).exists_bound_of_continuousOn
      (D.dens_cont i).continuousOn
  refine ⟨C, fun u ↦ ?_⟩
  by_cases hu : u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i)
  · exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hC u hu)
  · have hd : D.dens i u = 0 := by
      by_contra h
      exact hu (Metric.ball_subset_closedBall (D.dens_supp i u h))
    rw [hd]
    have h0 : (0 : Fin (m + 1) → ℝ) ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i) :=
      Metric.mem_closedBall_self (D.ρ_pos i).le
    exact (norm_nonneg _).trans (hC 0 h0)

theorem continuous_chartFun {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hθc : Continuous θ) {M : ℝ≥0∞}
    (hM : M ≠ ∞) (hθM : ∀ z, θ z ≤ M) (hθL : ∀ z, θ z ≠ 0 → z ∈ L') (i : D.ι) :
    Continuous (D.chartFun θ i) := by
  rw [D.chartFun_eq hθL i]
  refine continuous_iff_continuousAt.mpr fun u ↦ ?_
  exact ENNReal.Tendsto.mul (hθc.comp (D.rep_cont i)).continuousAt (Or.inr ENNReal.ofReal_ne_top)
    (ENNReal.continuous_ofReal.comp (D.dens_cont i)).continuousAt
    (Or.inr (ne_top_of_le_ne_top hM (hθM _)))

/-- The total fibre kernel is continuous at every `s₀ ≠ 0`, for a continuous bounded `θ`
supported in `L'`. -/
theorem continuousAt_totalKernel {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hθc : Continuous θ) {M : ℝ≥0∞}
    (hM : M ≠ ∞) (hθM : ∀ z, θ z ≤ M) (hθL : ∀ z, θ z ≠ 0 → z ∈ L') {s₀ : ℝ} (hs₀ : s₀ ≠ 0) :
    ContinuousAt (D.totalKernel θ) s₀ := by
  unfold TruthChartsData.totalKernel
  refine tendsto_finsetSum _ fun i _ ↦ ?_
  obtain ⟨C, hC⟩ := D.exists_dens_bound i
  refine continuousAt_fibreKernel (D.k i) (D.S i) (D.q_pos i)
    (D.continuous_chartFun hθc hM hθM hθL i) (M := M * ENNReal.ofReal C)
    (ENNReal.mul_ne_top hM ENNReal.ofReal_ne_top) ?_ (D.ρ_pos i).le ?_ hs₀
  · intro u
    rw [D.chartFun_eq hθL i]
    exact mul_le_mul' (hθM _) (ENNReal.ofReal_le_ofReal (hC u))
  · intro u hu
    rw [D.chartFun_eq hθL i] at hu
    have hd : D.dens i u ≠ 0 := by
      intro h
      apply hu
      simp only [h, ENNReal.ofReal_zero, mul_zero]
    exact mem_ball_zero_iff.mp (D.dens_supp i u hd)

end TruthChartsData

namespace WallChartsData

variable {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}

/-- The coordinate splitting at `ℓ`. -/
local notation "splitAt" => MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) ℓ

/-- **The pointwise fibre identity.** For `L' = splitAt⁻¹(B ×ˢ A)` and a continuous bounded `θ`
supported in `L'` and in a ball, the ambient fibre integral equals the total fibre kernel at every
`s ∈ interior B` with `s ≠ 0`. -/
theorem fibre_eqOn {B : Set ℝ} (hB : MeasurableSet B) {A : Set (Fin m → ℝ)} (hA : MeasurableSet A)
    (D : WallChartsData m ℓ (splitAt ⁻¹' (B ×ˢ A)))
    {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hθc : Continuous θ) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hθM : ∀ z, θ z ≤ M) {R : ℝ} (hθR : ∀ z, θ z ≠ 0 → ‖z‖ < R)
    (hθL : ∀ z, θ z ≠ 0 → z ∈ splitAt ⁻¹' (B ×ˢ A)) :
    EqOn (fun s ↦ ∫⁻ z' in A, θ (ℓ.insertNth s z')) (D.totalKernel θ)
      (interior B ∩ {s | s ≠ 0}) := by
  have hU : IsOpen (interior B ∩ {s : ℝ | s ≠ 0}) := isOpen_interior.inter isOpen_ne
  refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hU
    (continuous_ambientFibre ℓ A hθc hM hθM hθR).continuousOn
    (continuousOn_of_forall_continuousAt fun s hs ↦
      D.continuousAt_totalKernel hθc hM hθM hθL hs.2)
  exact ae_restrict_of_ae_restrict_of_subset (inter_subset_left.trans interior_subset)
    (D.fibre_ae hB hA hθc.measurable)

/-- The pointwise fibre identity at one `s`. -/
theorem fibre_eq {B : Set ℝ} (hB : MeasurableSet B) {A : Set (Fin m → ℝ)} (hA : MeasurableSet A)
    (D : WallChartsData m ℓ (splitAt ⁻¹' (B ×ˢ A)))
    {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hθc : Continuous θ) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hθM : ∀ z, θ z ≤ M) {R : ℝ} (hθR : ∀ z, θ z ≠ 0 → ‖z‖ < R)
    (hθL : ∀ z, θ z ≠ 0 → z ∈ splitAt ⁻¹' (B ×ˢ A)) {s : ℝ} (hsB : s ∈ interior B)
    (hs : s ≠ 0) : ∫⁻ z' in A, θ (ℓ.insertNth s z') = D.totalKernel θ s :=
  D.fibre_eqOn hB hA hθc hM hθM hθR hθL ⟨hsB, hs⟩

end WallChartsData

end Laplace.Multi
