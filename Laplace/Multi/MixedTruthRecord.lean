/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.WallChartsData
import Laplace.Multi.MixedTruthLog
import Laplace.Multi.ToyWallRecord

/-!
# The mixed truth monomial at the record level

Two facts about where the logarithmic mass of a mixed truth monomial can live.

**Coordinate truths carry no logarithm.** For Euclidean wall data `D : WallChartsData m ℓ L'` the
truth is the coordinate `z ℓ` and the ambient measure on `L'` is Lebesgue; when `L'` is bounded
the fibre kernel of a bounded observable is bounded almost everywhere
(`WallChartsData.totalKernel_ae_le`): the push-forward identity bounds `∫⁻_E K_θ` by the measure
of `L' ∩ {z ℓ ∈ E}`, which is at most `(2R)^m · |E|`. So a bounded observable has no growing
logarithmic fibre mass (`K(σ/t)/log t → c > 0` is impossible along the full ray; decaying
`t^{-λ}(log t)^k` terms from the loss are of course untouched, and the bound is almost everywhere
in `s`). In a chart with a genuinely mixed truth monomial (`q = (1,1)`, as the blow-up chart
`(x, y) ↦ (xy, y)` of `BlowupSectorRecord`) the Jacobian vanishes at the corner and cancels the
`1/w` of the coarea formula: the log endpoint of `MixedTruthLog` is a phenomenon of truth
functions, not of coordinate truths.

**General truths do.** `TruthChartsData m T L'` is the same Euclidean interface for a truth
function `T` on `L'` in place of the coordinate `z ℓ` (a `WallChartsData` is the special case
`T = (· ℓ)`, `WallChartsData.toTruth`), with the same push-forward identity
`∫⁻_{L'} θ(z) η(T z) dz = ∫⁻ η(s) K_θ(s) ds` (`TruthChartsData.lintegral_mul_comp_truth`). The
identity chart of the square `(0, 1/2]²` with `T = z₀ z₁` is such data (`mixData`): its fibre kernel
is exactly the logarithmic fibre integral, `K_θ(s) = ∫_{2s}^{1/2} θ(s/x, x) dx/x`
(`mixData_totalKernel`), and for the loss `F = z₀ z₁ · a(z)` along the ray `s = σ/t`
`K(σ/t)/log t → e^{-σ a(0)} ψ(0)` (`mix_tendsto_totalKernel`), so the fibre expectation converges
to the point evaluation `ψ(0)/χ(0)` (`mix_tendsto_fibre_expectation`): the coefficient measure of
the mixed truth at the logarithmic scale is the point mass `e^{-σ a(0)} δ_0` (Astra, round 4,
target 1).
-/

open Real MeasureTheory Set Filter Topology Laplace.Multi.ToyWall
open scoped ENNReal

namespace Laplace.Multi

variable {m : ℕ}

/-! ### Coordinate truths over bounded regions have bounded fibre kernels -/

namespace WallChartsData

variable {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)} (D : WallChartsData m ℓ L')

/-- The slice of a closed sup-norm ball over a set of truth values has measure at most
`(2R)^m` times the measure of the set. -/
theorem volume_closedBall_inter_le {R : ℝ} (hR : 0 ≤ R) {E : Set ℝ} (hE : MeasurableSet E) :
    volume (Metric.closedBall (0 : Fin (m + 1) → ℝ) R ∩ {z | z ℓ ∈ E}) ≤
      ENNReal.ofReal ((2 * R) ^ m) * volume E := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) ℓ with he
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) ℓ
  have hsub : Metric.closedBall (0 : Fin (m + 1) → ℝ) R ∩ {z | z ℓ ∈ E} ⊆
      e ⁻¹' (E ×ˢ Metric.closedBall (0 : Fin m → ℝ) R) := by
    intro z hz
    refine ⟨hz.2, ?_⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR]
    intro j
    exact (norm_le_pi_norm z _).trans (mem_closedBall_zero_iff.mp hz.1)
  refine (measure_mono hsub).trans (le_of_eq ?_)
  rw [hmp.measure_preimage (hE.prod Metric.isClosed_closedBall.measurableSet).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_pi_closedBall 0 hR, Fintype.card_fin,
    mul_comm]

/-- **Coordinate truths carry no logarithmic mass.** Over a bounded region the total fibre kernel
of a bounded observable is bounded almost everywhere. -/
theorem totalKernel_ae_le {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hθ : Measurable θ) {M : ℝ≥0∞}
    (hM : ∀ z, θ z ≤ M) {R : ℝ} (hR : 0 ≤ R)
    (hL : L' ⊆ Metric.closedBall (0 : Fin (m + 1) → ℝ) R) :
    ∀ᵐ s, D.totalKernel θ s ≤ M * ENNReal.ofReal ((2 * R) ^ m) := by
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (D.measurable_totalKernel hθ)
    fun E hE _ ↦ ?_
  set η : ℝ → ℝ≥0∞ := E.indicator (fun _ ↦ 1) with hη
  have hηm : Measurable η := measurable_const.indicator hE
  have hR' : ∫⁻ s, η s * D.totalKernel θ s = ∫⁻ s in E, D.totalKernel θ s := by
    rw [← lintegral_indicator hE]
    refine lintegral_congr fun s ↦ ?_
    by_cases hs : s ∈ E
    · simp only [hη, indicator_of_mem hs, one_mul]
    · simp only [hη, indicator_of_notMem hs, zero_mul]
  rw [← hR', ← D.lintegral_mul_comp_coord hθ hηm, setLIntegral_const]
  have hset : MeasurableSet {z : Fin (m + 1) → ℝ | z ℓ ∈ E} := measurable_pi_apply ℓ hE
  have hpt : ∀ z, θ z * η (z ℓ) ≤ {z | z ℓ ∈ E}.indicator (fun _ ↦ M) z := by
    intro z
    by_cases hz : z ℓ ∈ E
    · have hz' : z ∈ {z | z ℓ ∈ E} := hz
      simp only [hη, indicator_of_mem hz, indicator_of_mem hz', mul_one]
      exact hM z
    · have hz' : z ∉ {z | z ℓ ∈ E} := hz
      simp only [hη, indicator_of_notMem hz, indicator_of_notMem hz', mul_zero, le_refl]
  calc ∫⁻ z in L', θ z * η (z ℓ)
      ≤ ∫⁻ z in L', {z | z ℓ ∈ E}.indicator (fun _ ↦ M) z := lintegral_mono hpt
    _ = M * volume (L' ∩ {z | z ℓ ∈ E}) := by
        rw [lintegral_indicator hset, Measure.restrict_restrict hset, setLIntegral_const,
          inter_comm]
    _ ≤ M * (ENNReal.ofReal ((2 * R) ^ m) * volume E) := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        exact (measure_mono (inter_subset_inter_left _ hL)).trans
          (volume_closedBall_inter_le hR hE)
    _ = M * ENNReal.ofReal ((2 * R) ^ m) * volume E := by rw [mul_assoc]

end WallChartsData

/-! ### Euclidean chart data for a general truth function -/

/-- Euclidean wall data is chart data for the coordinate truth `z ℓ` (definitionally). -/
def WallChartsData.toTruth {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}
    (D : WallChartsData m ℓ L') : TruthChartsData m (fun z ↦ z ℓ) L' := D

/-! ### The identity chart of the square with the truth `z₀ z₁` -/

/-- The square `(0, 1/2]²`. -/
def mixL' : Set (Fin 2 → ℝ) := {z | z 0 ∈ Ioc 0 (1 / 2) ∧ z 1 ∈ Ioc 0 (1 / 2)}

theorem mem_mixL'_iff (v x : ℝ) :
    (![v, x] : Fin 2 → ℝ) ∈ mixL' ↔ (0 < v ∧ v ≤ 1 / 2) ∧ (0 < x ∧ x ≤ 1 / 2) := by
  simp [mixL', mem_Ioc]

theorem measurableSet_mixL' : MeasurableSet mixL' :=
  (measurable_pi_apply (0 : Fin 2) measurableSet_Ioc).inter
    (measurable_pi_apply (1 : Fin 2) measurableSet_Ioc)

theorem mixL'_subset : mixL' ⊆ Metric.closedBall (0 : Fin 2 → ℝ) (1 / 2) := by
  intro z hz
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hz.1.1], hz.1.2⟩
  · rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hz.2.1], hz.2.2⟩

theorem mixL'_subset_one : mixL' ⊆ Metric.closedBall (0 : Fin 2 → ℝ) 1 :=
  mixL'_subset.trans (Metric.closedBall_subset_closedBall (by norm_num))

/-- The identity chart of the square, with the mixed truth monomial `z₀ z₁` solved for `z₀`. -/
noncomputable def mixData : TruthChartsData 1 (fun z ↦ z 0 * z 1) mixL' where
  ι := Unit
  rep := fun _ u ↦ u
  rep_cont := fun _ ↦ continuous_id
  ρ := fun _ ↦ 1
  ρ_pos := fun _ ↦ one_pos
  dom := fun _ ↦ Metric.closedBall (0 : Fin 2 → ℝ) 1 ∩ mixL'
  dom_eq := fun _ ↦ rfl
  dom_meas := fun _ ↦ Metric.isClosed_closedBall.measurableSet.inter measurableSet_mixL'
  dens := fun _ ↦ toyDens
  dens_cont := fun _ ↦ continuous_toyDens
  dens_nonneg := fun _ ↦ toyDens_nonneg
  dens_supp := fun _ u hu ↦ mem_ball_zero_iff.mpr (toyDens_supp hu)
  S := fun _ ↦ 1
  S_ne := fun _ ↦ one_ne_zero
  q := fun _ ↦ ![1, 1]
  k := fun _ ↦ 0
  q_pos := fun _ ↦ by simp
  truth := fun _ u _ ↦ by
    simp [truthMono, Fin.prod_univ_two]
  transport := fun Ψ _ ↦ by
    rw [Fintype.sum_unique, Set.inter_eq_right.mpr mixL'_subset_one]
    refine (setLIntegral_congr_fun measurableSet_mixL' fun u hu ↦ ?_).symm
    rw [toyDens_eq_one (mem_closedBall_zero_iff.mp (mixL'_subset hu)), ENNReal.ofReal_one,
      mul_one]

instance : Unique mixData.ι := inferInstanceAs (Unique Unit)

theorem mixData_chartFun (θ : (Fin 2 → ℝ) → ℝ≥0∞) (z : Fin 2 → ℝ) :
    mixData.chartFun θ default z = mixL'.indicator θ z := by
  unfold TruthChartsData.chartFun
  by_cases hz : z ∈ mixL'
  · have hz' : z ∈ mixData.dom default := ⟨mixL'_subset_one hz, hz⟩
    rw [indicator_of_mem hz', indicator_of_mem hz]
    change θ z * ENNReal.ofReal (toyDens z) = θ z
    rw [toyDens_eq_one (mem_closedBall_zero_iff.mp (mixL'_subset hz)), ENNReal.ofReal_one,
      mul_one]
  · have hz' : z ∉ mixData.dom default := fun h ↦ hz h.2
    rw [indicator_of_notMem hz', indicator_of_notMem hz]

theorem mix_solvedCoeff (x : ℝ) :
    solvedCoeff (0 : Fin 2) 1 ![1, 1] (fun _ : Fin 1 ↦ x) = x := by
  simp [solvedCoeff]

theorem mix_solvedCoord {x s : ℝ} (hs : 0 < s) : solvedCoord x 1 s = s / |x| := by
  simp [solvedCoord, abs_of_pos hs]

theorem insertNth_zero_const (v x : ℝ) :
    (0 : Fin 2).insertNth (α := fun _ ↦ ℝ) v (fun _ : Fin 1 ↦ x) = ![v, x] := by
  funext i
  fin_cases i <;> rfl

/-- The branch kernel of the identity chart at a positive truth value: only the branch `x > 0`
contributes, with the fibre point `(s/x, x)` and the Jacobian `1/x`. -/
theorem mixData_branchKernel {θ : (Fin 2 → ℝ) → ℝ≥0∞} {s : ℝ} (hs : 0 < s) (x : ℝ) :
    branchKernel 0 1 ![1, 1] (mixData.chartFun θ default) (fun _ : Fin 1 ↦ x) s =
      (Icc (2 * s) (1 / 2)).indicator (fun x ↦ θ ![s / x, x] * ENNReal.ofReal (1 / x)) x := by
  unfold branchKernel
  simp only [Matrix.cons_val_zero, pow_one, Nat.cast_one, one_mul, mix_solvedCoeff]
  rcases le_or_gt x 0 with hx | hx
  · have hx2 : x ∉ Icc (2 * s) (1 / 2) := fun h ↦ by linarith [h.1]
    have hneg : s ∉ {s | 0 < x * s} := fun h ↦ by
      have : x * s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx hs.le
      exact absurd h (not_lt.mpr this)
    rw [indicator_of_notMem hx2, indicator_of_notMem hneg, add_zero]
    by_cases hmem : s ∈ {s | 0 < x * -1 * s}
    · rw [indicator_of_mem hmem, insertNth_zero_const, mixData_chartFun]
      have hnot : (![-solvedCoord x 1 s, x] : Fin 2 → ℝ) ∉ mixL' := fun h ↦ by
        rw [mem_mixL'_iff] at h
        linarith [h.2.1]
      rw [indicator_of_notMem hnot, zero_mul]
    · rw [indicator_of_notMem hmem]
  · have hpos : s ∈ {s | 0 < x * s} := mul_pos hx hs
    have hneg : s ∉ {s | 0 < x * -1 * s} := fun h ↦ by
      have : x * -1 * s < 0 := by nlinarith
      exact absurd h (not_lt.mpr this.le)
    rw [indicator_of_notMem hneg, zero_add, indicator_of_mem hpos, insertNth_zero_const,
      mixData_chartFun, mix_solvedCoord hs, abs_of_pos hx, abs_of_pos hs]
    have hjac : s / x / s = 1 / x := by field_simp
    rw [hjac]
    by_cases hmem : x ∈ Icc (2 * s) (1 / 2)
    · have hin : (![s / x, x] : Fin 2 → ℝ) ∈ mixL' := by
        rw [mem_mixL'_iff]
        exact ⟨⟨div_pos hs hx, by rw [div_le_iff₀ hx]; linarith [hmem.1]⟩, hx, hmem.2⟩
      rw [indicator_of_mem hin, indicator_of_mem hmem]
    · have hnot : (![s / x, x] : Fin 2 → ℝ) ∉ mixL' := fun h ↦ by
        rw [mem_mixL'_iff] at h
        refine hmem ⟨?_, h.2.2⟩
        have := (div_le_iff₀ hx).mp h.1.2
        linarith
      rw [indicator_of_notMem hnot, indicator_of_notMem hmem, zero_mul]

/-- **The fibre kernel of the mixed truth.** `K_θ(s) = ∫_{2s}^{1/2} θ(s/x, x) dx/x`. -/
theorem mixData_totalKernel {θ : (Fin 2 → ℝ) → ℝ≥0∞} {s : ℝ} (hs : 0 < s) :
    mixData.totalKernel θ s =
      ∫⁻ x in Icc (2 * s) (1 / 2), θ ![s / x, x] * ENNReal.ofReal (1 / x) := by
  unfold TruthChartsData.totalKernel
  rw [Fintype.sum_unique]
  change fibreKernel 0 1 ![1, 1] (mixData.chartFun θ default) s = _
  unfold fibreKernel
  have hmp := volume_preserving_funUnique (Fin 1) ℝ
  change ∫⁻ w : Fin 1 → ℝ, branchKernel 0 1 ![1, 1] (mixData.chartFun θ default) w s = _
  refine (hmp.symm.lintegral_comp_emb (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding
    (fun w ↦ branchKernel 0 1 ![1, 1] (mixData.chartFun θ default) w s)).symm.trans ?_
  rw [← lintegral_indicator measurableSet_Icc]
  refine lintegral_congr fun x ↦ ?_
  exact mixData_branchKernel hs x

theorem vec_two_zero : (![0, 0] : Fin 2 → ℝ) = 0 := by
  funext i
  fin_cases i <;> rfl

/-- The real form of the fibre kernel for a nonnegative continuous integrand. -/
theorem mixData_totalKernel_toReal {g : (Fin 2 → ℝ) → ℝ} (hgc : Continuous g) (hg : ∀ z, 0 ≤ g z)
    {s : ℝ} (hs : 0 < s) :
    (mixData.totalKernel (fun z ↦ ENNReal.ofReal (g z)) s).toReal =
      ∫ x in Icc (2 * s) (1 / 2), g ![s / x, x] / x := by
  rw [mixData_totalKernel hs]
  have hvec : ContinuousOn (fun x : ℝ ↦ (![s / x, x] : Fin 2 → ℝ)) (Icc (2 * s) (1 / 2)) := by
    refine continuousOn_pi.2 fun i ↦ ?_
    fin_cases i
    · exact continuousOn_const.div continuousOn_id fun x hx ↦ by
        have := hx.1
        exact (by linarith : (0 : ℝ) < x).ne'
    · exact continuousOn_id
  have hcont : ContinuousOn (fun x : ℝ ↦ g ![s / x, x] / x) (Icc (2 * s) (1 / 2)) :=
    (hgc.comp_continuousOn hvec).div continuousOn_id fun x hx ↦ by
      have := hx.1
      exact (by linarith : (0 : ℝ) < x).ne'
  have hint : IntegrableOn (fun x : ℝ ↦ g ![s / x, x] / x) (Icc (2 * s) (1 / 2)) :=
    hcont.integrableOn_compact isCompact_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Icc (2 * s) (1 / 2))] fun x : ℝ ↦ g ![s / x, x] / x := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun x hx ↦ ?_)
    have := hx.1
    exact div_nonneg (hg _) (by linarith)
  have h1 : ∫⁻ x in Icc (2 * s) (1 / 2), ENNReal.ofReal (g ![s / x, x]) * ENNReal.ofReal (1 / x) =
      ∫⁻ x in Icc (2 * s) (1 / 2), ENNReal.ofReal (g ![s / x, x] / x) :=
    setLIntegral_congr_fun measurableSet_Icc fun x _ ↦ by
      rw [← ENNReal.ofReal_mul (hg _), mul_one_div]
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn)]

/-- **The mixed truth at the logarithmic scale, record level.** For the loss `F = z₀ z₁ · a(z)`
along the ray `s = σ/t`, the fibre kernel of `e^{-tF} ψ` grows like `log t` with coefficient
`e^{-σ a(0)} ψ(0)`. -/
theorem mix_tendsto_totalKernel {σ : ℝ} (hσ : 0 < σ) {a ψ : (Fin 2 → ℝ) → ℝ} (ha : Continuous a)
    (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z) :
    Tendsto (fun t ↦ (mixData.totalKernel
        (fun z ↦ ENNReal.ofReal (exp (-(t * (z 0 * z 1 * a z))) * ψ z)) (σ / t)).toReal / log t)
      atTop (𝓝 (exp (-(σ * a 0)) * ψ 0)) := by
  have hvec : Continuous fun p : ℝ × ℝ ↦ (![p.2, p.1] : Fin 2 → ℝ) := by
    refine continuous_pi fun i ↦ ?_
    fin_cases i
    · exact continuous_snd
    · exact continuous_fst
  have hf : ContinuousOn (fun p : ℝ × ℝ ↦ exp (-(σ * a ![p.2, p.1])) * ψ ![p.2, p.1])
      (Icc 0 (1 / 2) ×ˢ Icc 0 (1 / 2)) :=
    ((Real.continuous_exp.comp (continuous_const.mul (ha.comp hvec)).neg).mul
      (hψc.comp hvec)).continuousOn
  have key := tendsto_mixedLog (ρ := 1 / 2) (by norm_num) hσ
    (f := fun x y ↦ exp (-(σ * a ![y, x])) * ψ ![y, x]) hf
  simp only [vec_two_zero] at key
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hs : 0 < σ / t := div_pos hσ ht
  rw [mixData_totalKernel_toReal (g := fun z ↦ exp (-(t * (z 0 * z 1 * a z))) * ψ z)
    (by fun_prop) (fun z ↦ mul_nonneg (exp_pos _).le (hψ z)) hs, integral_Icc_eq_integral_Ioo,
    show σ / (1 / 2 * t) = 2 * (σ / t) by ring]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ ?_
  have hx : 0 < x := by linarith [hx.1, mul_pos two_pos hs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [div_div, show t * (σ / (t * x) * x * a ![σ / (t * x), x]) = σ * a ![σ / (t * x), x] by
    field_simp]

/-- **The fibre expectation of the mixed truth converges to the point evaluation.** -/
theorem mix_tendsto_fibre_expectation {σ : ℝ} (hσ : 0 < σ) {a ψ χ : (Fin 2 → ℝ) → ℝ}
    (ha : Continuous a) (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z) (hχc : Continuous χ)
    (hχ : ∀ z, 0 ≤ χ z) (hχ0 : 0 < χ 0) :
    Tendsto (fun t ↦ (mixData.totalKernel
        (fun z ↦ ENNReal.ofReal (exp (-(t * (z 0 * z 1 * a z))) * ψ z)) (σ / t)).toReal /
      (mixData.totalKernel
        (fun z ↦ ENNReal.ofReal (exp (-(t * (z 0 * z 1 * a z))) * χ z)) (σ / t)).toReal)
      atTop (𝓝 (ψ 0 / χ 0)) := by
  have h := (mix_tendsto_totalKernel hσ ha hψc hψ).div (mix_tendsto_totalKernel hσ ha hχc hχ)
    (mul_pos (exp_pos _) hχ0).ne'
  rw [mul_div_mul_left _ _ (exp_pos _).ne'] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ (log_pos ht).ne']

end Laplace.Multi
