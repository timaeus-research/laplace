/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.WallChartsData

/-!
# Continuity of the fibre kernel off the wall

Route A, step 3 of the fibre-identity plan: for a bounded measurable `Φ` supported in the open box
`‖u‖ < ρ`, the fibre kernel `fibreKernel k S q Φ` is continuous at every `s₀ ≠ 0`
(`continuousAt_fibreKernel`). Mechanism: for each unsolved coordinate `w` the branch kernel is
continuous at `s₀ ≠ 0` — the sign sets are open half-lines, the solved coordinate
`V = (|s|/|c(w)|)^{1/q}` is continuous, and the density `V/(q|s|)` is continuous away from `s = 0`
— and it is dominated near `s₀` by `2 M · (2ρ/(q|s₀|)) · 1_{‖w‖ ≤ ρ}`, since the integrand vanishes
unless `‖w‖ < ρ` and `V < ρ` (`branchKernel_le`). Dominated convergence finishes.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

variable {m : ℕ}

/-- The sign set `{s | 0 < c' s}` is open. -/
theorem isOpen_signSet (c' : ℝ) : IsOpen {s : ℝ | 0 < c' * s} :=
  isOpen_lt continuous_const (continuous_const.mul continuous_id)

/-- Off `0`, the complement of a sign set is a neighbourhood of each of its points. -/
theorem signSet_compl_mem_nhds {c' s₀ : ℝ} (hs₀ : s₀ ≠ 0) (h : ¬ 0 < c' * s₀) :
    {s : ℝ | 0 < c' * s}ᶜ ∈ 𝓝 s₀ := by
  rcases eq_or_ne c' 0 with hc | hc
  · exact univ_mem' fun s ↦ by simp [hc]
  · have hlt : c' * s₀ < 0 := lt_of_le_of_ne (not_lt.mp h) (mul_ne_zero hc hs₀)
    have hopen : IsOpen {s : ℝ | c' * s < 0} :=
      isOpen_lt (continuous_const.mul continuous_id) continuous_const
    refine mem_of_superset (hopen.mem_nhds hlt) fun s hs ↦ ?_
    change ¬ 0 < c' * s
    exact not_lt.mpr (le_of_lt (show c' * s < 0 from hs))

/-- The solved coordinate is continuous in `s`. -/
theorem continuous_solvedCoord (c : ℝ) (q : ℕ) : Continuous (solvedCoord c q) := by
  unfold solvedCoord
  exact (continuous_abs.div_const _).rpow_const fun _ ↦ Or.inr (by positivity)

/-- One branch of the kernel: continuous at `s₀ ≠ 0` for continuous `Φ`. -/
theorem continuousAt_branch {c : ℝ} {q : ℕ} (hq : 0 < q) {c' : ℝ}
    {Φ : ℝ → ℝ≥0∞} (hΦ : Continuous Φ) (hΦtop : ∀ x, Φ x ≠ ∞) (σ : ℝ) {s₀ : ℝ} (hs₀ : s₀ ≠ 0) :
    ContinuousAt (fun s ↦ {s | 0 < c' * s}.indicator
      (fun s ↦ Φ (σ * solvedCoord c q s) * ENNReal.ofReal (solvedCoord c q s / (q * |s|))) s)
      s₀ := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hf : ContinuousAt
      (fun s ↦ Φ (σ * solvedCoord c q s) * ENNReal.ofReal (solvedCoord c q s / (q * |s|))) s₀ := by
    have hfa : ContinuousAt (fun s ↦ Φ (σ * solvedCoord c q s)) s₀ :=
      hΦ.continuousAt.comp ((continuous_const.mul (continuous_solvedCoord c q)).continuousAt)
    have hfb : ContinuousAt (fun s ↦ ENNReal.ofReal (solvedCoord c q s / (q * |s|))) s₀ := by
      refine ENNReal.continuous_ofReal.continuousAt.comp ?_
      refine ContinuousAt.div (continuous_solvedCoord c q).continuousAt
        (continuous_const.mul continuous_abs).continuousAt ?_
      exact mul_ne_zero hq' (abs_ne_zero.mpr hs₀)
    exact ENNReal.Tendsto.mul hfa (Or.inr ENNReal.ofReal_ne_top) hfb (Or.inr (hΦtop _))
  by_cases hs : 0 < c' * s₀
  · refine hf.congr (eventuallyEq_of_mem ((isOpen_signSet c').mem_nhds hs) fun s hs' ↦ ?_)
    rw [indicator_of_mem hs']
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (0 : ℝ≥0∞)) s₀).congr
      (eventuallyEq_of_mem (signSet_compl_mem_nhds hs₀ hs) fun s hs' ↦ ?_)
    rw [indicator_of_notMem hs']

/-- For each `w`, the branch kernel is continuous at `s₀ ≠ 0` (continuous `Φ`). -/
theorem continuousAt_branchKernel (k : Fin (m + 1)) (S : ℝ) {q : Fin (m + 1) → ℕ} (hq : 0 < q k)
    {Φ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hΦ : Continuous Φ) (hΦtop : ∀ u, Φ u ≠ ∞) (w : Fin m → ℝ)
    {s₀ : ℝ} (hs₀ : s₀ ≠ 0) : ContinuousAt (branchKernel k S q Φ w) s₀ := by
  have hins : Continuous fun v : ℝ ↦ Φ (k.insertNth v w) :=
    hΦ.comp (Continuous.finInsertNth (A := fun _ : Fin (m + 1) ↦ ℝ) k (f := id)
      (g := fun _ ↦ w) continuous_id continuous_const)
  unfold branchKernel
  refine ContinuousAt.add ?_ ?_
  · have := continuousAt_branch (c := solvedCoeff k S q w) hq
      (c' := solvedCoeff k S q w * (-1) ^ q k) hins (fun _ ↦ hΦtop _) (-1) hs₀
    simpa only [neg_one_mul] using this
  · have := continuousAt_branch (c := solvedCoeff k S q w) hq (c' := solvedCoeff k S q w) hins
      (fun _ ↦ hΦtop _) 1 hs₀
    simpa only [one_mul] using this

/-- The domination: if `Φ ≤ M` and `Φ` vanishes off the open box `‖u‖ < ρ`, then the branch
kernel at `s ≠ 0` is at most `2 M · ofReal (ρ / (q |s|))` and vanishes unless `‖w‖ < ρ`. -/
theorem branchKernel_le (k : Fin (m + 1)) (S : ℝ) {q : Fin (m + 1) → ℕ} (hq : 0 < q k)
    {Φ : (Fin (m + 1) → ℝ) → ℝ≥0∞} {M : ℝ≥0∞} (hM : ∀ u, Φ u ≤ M) {ρ : ℝ}
    (hsupp : ∀ u, Φ u ≠ 0 → ‖u‖ < ρ) (w : Fin m → ℝ) {s : ℝ} (hs : s ≠ 0) :
    branchKernel k S q Φ w s ≤
      (Metric.closedBall (0 : Fin m → ℝ) ρ).indicator
        (fun _ ↦ 2 * M * ENNReal.ofReal (ρ / (q k * |s|))) w := by
  have hq' : (0 : ℝ) < q k := by exact_mod_cast hq
  have hpos : 0 < (q k : ℝ) * |s| := mul_pos hq' (abs_pos.mpr hs)
  -- one branch
  have key : ∀ (σ : ℝ), |σ| = 1 → ∀ (c' : ℝ),
      {s | 0 < c' * s}.indicator (fun s ↦ Φ (k.insertNth (σ * solvedCoord (solvedCoeff k S q w)
        (q k) s) w) * ENNReal.ofReal (solvedCoord (solvedCoeff k S q w) (q k) s / (q k * |s|))) s ≤
      (Metric.closedBall (0 : Fin m → ℝ) ρ).indicator
        (fun _ ↦ M * ENNReal.ofReal (ρ / (q k * |s|))) w := by
    intro σ hσ c'
    set V := solvedCoord (solvedCoeff k S q w) (q k) s with hV
    by_cases hs' : 0 < c' * s
    · have hs'' : s ∈ {s : ℝ | 0 < c' * s} := hs'
      rw [indicator_of_mem hs'']
      by_cases h0 : Φ (k.insertNth (σ * V) w) = 0
      · rw [h0, zero_mul]; exact zero_le
      · have hnorm := hsupp _ h0
        have hw : ‖w‖ ≤ ρ := by
          refine le_of_lt (lt_of_le_of_lt ?_ hnorm)
          rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
          intro j
          have := norm_le_pi_norm (k.insertNth (σ * V) w : Fin (m + 1) → ℝ) (k.succAbove j)
          rwa [Fin.insertNth_apply_succAbove] at this
        have hVle : V ≤ ρ := by
          have := norm_le_pi_norm (k.insertNth (σ * V) w : Fin (m + 1) → ℝ) k
          rw [Fin.insertNth_apply_same, Real.norm_eq_abs, abs_mul, hσ, one_mul,
            abs_of_nonneg (solvedCoord_nonneg _ _ _)] at this
          exact this.trans hnorm.le
        rw [indicator_of_mem (mem_closedBall_zero_iff.mpr hw)]
        refine mul_le_mul' (hM _) (ENNReal.ofReal_le_ofReal ?_)
        exact div_le_div_of_nonneg_right hVle hpos.le
    · have hs'' : s ∉ {s : ℝ | 0 < c' * s} := hs'
      rw [indicator_of_notMem hs'']
      exact zero_le
  unfold branchKernel
  have h1 := key (-1) (by simp) (solvedCoeff k S q w * (-1) ^ q k)
  have h2 := key 1 (by simp) (solvedCoeff k S q w)
  simp only [neg_one_mul, one_mul] at h1 h2
  calc _ ≤ (Metric.closedBall (0 : Fin m → ℝ) ρ).indicator
        (fun _ ↦ M * ENNReal.ofReal (ρ / (q k * |s|))) w +
      (Metric.closedBall (0 : Fin m → ℝ) ρ).indicator
        (fun _ ↦ M * ENNReal.ofReal (ρ / (q k * |s|))) w := add_le_add h1 h2
    _ = _ := by
      by_cases hw : w ∈ Metric.closedBall (0 : Fin m → ℝ) ρ
      · simp only [indicator_of_mem hw]; ring
      · simp only [indicator_of_notMem hw, add_zero]

/-- **Continuity of the fibre kernel off the wall.** For a continuous `Φ`, bounded by `M < ∞` and
supported in the open box `‖u‖ < ρ`, the fibre kernel is continuous at every `s₀ ≠ 0`. -/
theorem continuousAt_fibreKernel (k : Fin (m + 1)) (S : ℝ) {q : Fin (m + 1) → ℕ} (hq : 0 < q k)
    {Φ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hΦ : Continuous Φ) {M : ℝ≥0∞} (hMtop : M ≠ ∞)
    (hM : ∀ u, Φ u ≤ M) {ρ : ℝ} (hρ : 0 ≤ ρ) (hsupp : ∀ u, Φ u ≠ 0 → ‖u‖ < ρ) {s₀ : ℝ}
    (hs₀ : s₀ ≠ 0) : ContinuousAt (fibreKernel k S q Φ) s₀ := by
  have hq' : (0 : ℝ) < q k := by exact_mod_cast hq
  have hK := measurable_branchKernel_uncurry k S q hΦ.measurable
  unfold fibreKernel
  refine tendsto_lintegral_filter_of_dominated_convergence
    ((Metric.closedBall (0 : Fin m → ℝ) ρ).indicator
      (fun _ ↦ 2 * M * ENNReal.ofReal (2 * ρ / (q k * |s₀|))))
    (Eventually.of_forall fun s ↦ ?_) ?_ ?_ (Eventually.of_forall fun w ↦ ?_)
  · exact (show Measurable (Function.uncurry (branchKernel k S q Φ)) from hK).of_uncurry_right
  · -- the bound holds for `|s| ≥ |s₀|/2`
    have hnhds : {s : ℝ | |s₀| / 2 < |s|} ∈ 𝓝 s₀ :=
      (isOpen_lt continuous_const continuous_abs).mem_nhds
        (by simp [half_lt_self (abs_pos.mpr hs₀)])
    filter_upwards [hnhds] with s hs
    refine Eventually.of_forall fun w ↦ (branchKernel_le k S hq hM hsupp w ?_).trans ?_
    · intro h; rw [h, abs_zero] at hs; exact absurd hs (not_lt.mpr (by positivity))
    · by_cases hw : w ∈ Metric.closedBall (0 : Fin m → ℝ) ρ
      · simp only [indicator_of_mem hw]
        refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
        have hs' : |s₀| / 2 < |s| := hs
        have hs0 : 0 < |s| := lt_of_le_of_lt (by positivity) hs'
        rw [div_le_div_iff₀ (mul_pos hq' hs0) (mul_pos hq' (abs_pos.mpr hs₀))]
        nlinarith [mul_nonneg (mul_nonneg hρ hq'.le) (by linarith : (0 : ℝ) ≤ 2 * |s| - |s₀|)]
      · simp only [indicator_of_notMem hw, le_refl]
  · rw [lintegral_indicator_const measurableSet_closedBall]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hMtop)
      ENNReal.ofReal_ne_top) measure_closedBall_lt_top.ne
  · exact continuousAt_branchKernel k S hq hΦ (fun u ↦ ne_top_of_le_ne_top hMtop (hM u)) w hs₀

end Laplace.Multi
