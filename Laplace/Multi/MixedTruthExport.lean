/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.KernelAtlasIndependence
import Laplace.Multi.MixedTruthRecord
import Laplace.Multi.FibrePointwise

/-!
# The mixed truth through an arbitrary chart system: the exported `xy` regression

Astra round 14, items 2 and 3. **Limit identification through exact transport.** Two chart
systems for the same truth function have almost everywhere equal fibre kernels; for an
observable supported in both regions this holds across different regions
(`TruthChartsData.totalKernel_ae_eq_of_support`), and at every `s ≠ 0` at which both kernels are
continuous the kernels agree (`eq_of_ae_eq_of_continuousAt`). The fibre kernel at `s` only sees
the fibre `T = s`, so a cutoff in the truth variable factors out of the kernel
(`TruthChartsData.totalKernel_mul_comp_truth`): with the cutoff `truthCutoff ε` (equal to `1` on
`|s| ≤ ε/2`, vanishing off `|s| < ε`) an observable supported in a region `L` becomes one
supported in the thin region `L ∩ {|T| ≤ ε}` without changing the kernel at small `s`.

**The regression.** For the mixed truth `T = z₀ z₁` on the closed square `mixLc = [0, 1/2]²`
(the identity chart `mixDataC`, whose fibre kernel is the logarithmic integral
`∫_{2s}^{1/2} θ(s/x, x) dx/x` exactly as for `mixData`), ANY chart system `D` for `T` over the thin
region `closedBall 0 (1/2) ∩ {|T| ≤ ε}` — in particular the one produced by the resolution of
`F · T` (hironaka `exists_truthChartsData_withPhase`) — has the same logarithmic coefficient:
`K^D_{e^{-tF}ψ}(σ/t)/log t → e^{-σ a(0)} ψ(0)` for `F = z₀ z₁ a(z)` and `ψ ≥ 0` continuous
supported in the closed square (`exported_mix_tendsto_totalKernel`). The coefficient is thus
independent of the atlas, as it must be, and the exported kernel reproduces the identity-chart
computation of `MixedTruthRecord` through exact transport, once both limits are known to exist.
-/

open Real MeasureTheory Set Filter Topology Laplace.Multi.ToyWall
open scoped ENNReal

namespace Laplace.Multi

variable {m : ℕ}

/-! ### Limit identification through exact transport -/

namespace TruthChartsData

/-- Two chart systems for the same truth over (possibly different) measurable regions have almost
everywhere equal fibre kernels for an observable supported in both regions. -/
theorem totalKernel_ae_eq_of_support {T : (Fin (m + 1) → ℝ) → ℝ} {L₁ L₂ : Set (Fin (m + 1) → ℝ)}
    (D₁ : TruthChartsData m T L₁) (D₂ : TruthChartsData m T L₂) (hT : Measurable T)
    (hL₁ : MeasurableSet L₁) (hL₂ : MeasurableSet L₂) {θ : (Fin (m + 1) → ℝ) → ℝ≥0∞}
    (hθ : Measurable θ) (hθL : ∀ z, θ z ≠ 0 → z ∈ L₁ ∩ L₂) :
    D₁.totalKernel θ =ᵐ[volume] D₂.totalKernel θ := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (D₁.measurable_totalKernel hθ)
    (D₂.measurable_totalKernel hθ) fun E hE _ ↦ ?_
  have key : ∀ {L : Set (Fin (m + 1) → ℝ)} (D : TruthChartsData m T L), MeasurableSet L →
      (∀ z, θ z ≠ 0 → z ∈ L) → ∫⁻ s in E, D.totalKernel θ s =
        ∫⁻ z, θ z * E.indicator (fun _ ↦ 1) (T z) := by
    intro L D hL hLθ
    have h1 : ∫⁻ s in E, D.totalKernel θ s = ∫⁻ z in L, θ z * E.indicator (fun _ ↦ 1) (T z) := by
      rw [D.lintegral_mul_comp_truth hT hθ (measurable_const.indicator hE),
        ← lintegral_indicator hE]
      refine lintegral_congr fun s ↦ ?_
      by_cases hs : s ∈ E
      · simp only [indicator_of_mem hs, one_mul]
      · simp only [indicator_of_notMem hs, zero_mul]
    rw [h1, ← lintegral_indicator hL]
    refine lintegral_congr fun z ↦ ?_
    by_cases hz : z ∈ L
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz]
      have : θ z = 0 := by
        by_contra h
        exact hz (hLθ z h)
      rw [this, zero_mul]
  rw [key D₁ hL₁ fun z hz ↦ (hθL z hz).1, key D₂ hL₂ fun z hz ↦ (hθL z hz).2]

/-- The fibre kernel at `s` sees only the fibre `T = s`: a function of the truth factors out. -/
theorem totalKernel_mul_comp_truth {T : (Fin (m + 1) → ℝ) → ℝ} {L' : Set (Fin (m + 1) → ℝ)}
    (D : TruthChartsData m T L') (θ : (Fin (m + 1) → ℝ) → ℝ≥0∞) (η : ℝ → ℝ≥0∞) {s : ℝ}
    (hηs : η s ≠ ⊤) :
    D.totalKernel (fun z ↦ θ z * η (T z)) s = η s * D.totalKernel θ s := by
  unfold totalKernel
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  unfold fibreKernel
  rw [← lintegral_const_mul' _ _ hηs]
  refine lintegral_congr fun w ↦ ?_
  have hq := D.q_pos i
  have key : ∀ v : ℝ, truthMono (D.S i) (D.q i) ((D.k i).insertNth (α := fun _ ↦ ℝ) v w) = s →
      D.chartFun (fun z ↦ θ z * η (T z)) i ((D.k i).insertNth (α := fun _ ↦ ℝ) v w) =
        η s * D.chartFun θ i ((D.k i).insertNth (α := fun _ ↦ ℝ) v w) := by
    intro v hv
    unfold chartFun
    by_cases hu : (D.k i).insertNth (α := fun _ ↦ ℝ) v w ∈ D.dom i
    · rw [indicator_of_mem hu, indicator_of_mem hu]
      beta_reduce
      rw [D.truth i _ hu, hv]
      ring
    · rw [indicator_of_notMem hu, indicator_of_notMem hu, mul_zero]
  unfold branchKernel
  rw [mul_add]
  congr 1
  · by_cases hmem : s ∈ {s | 0 < solvedCoeff (D.k i) (D.S i) (D.q i) w * (-1) ^ D.q i (D.k i) * s}
    · have hc : solvedCoeff (D.k i) (D.S i) (D.q i) w ≠ 0 := by
        intro h0
        simp [h0] at hmem
      rw [indicator_of_mem hmem, indicator_of_mem hmem, key _ (by
        rw [truthMono_insertNth]
        exact solvedCoord_neg_spec hc hq hmem), mul_assoc]
    · rw [indicator_of_notMem hmem, indicator_of_notMem hmem, mul_zero]
  · by_cases hmem : s ∈ {s | 0 < solvedCoeff (D.k i) (D.S i) (D.q i) w * s}
    · have hc : solvedCoeff (D.k i) (D.S i) (D.q i) w ≠ 0 := by
        intro h0
        simp [h0] at hmem
      rw [indicator_of_mem hmem, indicator_of_mem hmem, key _ (by
        rw [truthMono_insertNth]
        exact solvedCoord_pos_spec hc hq hmem), mul_assoc]
    · rw [indicator_of_notMem hmem, indicator_of_notMem hmem, mul_zero]

end TruthChartsData

/-- Two functions almost everywhere equal and both continuous at a point agree at that point. -/
theorem eq_of_ae_eq_of_continuousAt {f g : ℝ → ℝ≥0∞} (h : f =ᵐ[volume] g) {s₀ : ℝ}
    (hf : ContinuousAt f s₀) (hg : ContinuousAt g s₀) : f s₀ = g s₀ := by
  by_contra hne
  have hopen : ∀ᶠ s in 𝓝 s₀, f s ≠ g s := by
    have hpair : Tendsto (fun s ↦ (f s, g s)) (𝓝 s₀) (𝓝 (f s₀, g s₀)) := hf.prodMk_nhds hg
    have hmem : (diagonal ℝ≥0∞)ᶜ ∈ 𝓝 (f s₀, g s₀) :=
      isClosed_diagonal.isOpen_compl.mem_nhds (by simpa [mem_diagonal_iff] using hne)
    filter_upwards [hpair.eventually hmem] with s hs
    simpa [mem_diagonal_iff] using hs
  have hpos : 0 < volume {s | f s ≠ g s} :=
    Measure.measure_pos_of_mem_nhds (μ := volume) hopen
  have h0 : volume {s | f s ≠ g s} = 0 := ae_iff.mp h
  exact hpos.ne' h0

/-! ### The truth cutoff -/

/-- A continuous cutoff in the truth variable: `1` on `|s| ≤ ε/2`, `0` off `|s| < ε`. -/
noncomputable def truthCutoff (ε s : ℝ) : ℝ := min 1 (max 0 (2 - 2 * |s| / ε))

theorem truthCutoff_nonneg (ε s : ℝ) : 0 ≤ truthCutoff ε s :=
  le_min zero_le_one (le_max_left _ _)

theorem truthCutoff_le_one (ε s : ℝ) : truthCutoff ε s ≤ 1 := min_le_left _ _

theorem continuous_truthCutoff (ε : ℝ) : Continuous (truthCutoff ε) := by
  unfold truthCutoff
  fun_prop

theorem truthCutoff_eq_one {ε s : ℝ} (hε : 0 < ε) (hs : |s| ≤ ε / 2) : truthCutoff ε s = 1 := by
  unfold truthCutoff
  refine min_eq_left (le_max_of_le_right ?_)
  have : 2 * |s| / ε ≤ 1 := by
    rw [div_le_one hε]
    linarith
  linarith

theorem truthCutoff_eq_zero {ε s : ℝ} (hε : 0 < ε) (hs : ε ≤ |s|) : truthCutoff ε s = 0 := by
  unfold truthCutoff
  have : 2 - 2 * |s| / ε ≤ 0 := by
    have : 1 ≤ |s| / ε := by rw [le_div_iff₀ hε]; linarith
    have e : 2 * |s| / ε = 2 * (|s| / ε) := by ring
    rw [e]
    linarith
  rw [max_eq_left this, min_eq_right zero_le_one]

theorem abs_lt_of_truthCutoff_ne_zero {ε s : ℝ} (hε : 0 < ε) (h : truthCutoff ε s ≠ 0) :
    |s| < ε := by
  by_contra h'
  exact h (truthCutoff_eq_zero hε (not_lt.mp h'))

/-! ### The identity chart of the closed square -/

/-- The closed square `[0, 1/2]²`. -/
def mixLc : Set (Fin 2 → ℝ) := {z | z 0 ∈ Icc 0 (1 / 2) ∧ z 1 ∈ Icc 0 (1 / 2)}

theorem mem_mixLc_iff (v x : ℝ) :
    (![v, x] : Fin 2 → ℝ) ∈ mixLc ↔ (0 ≤ v ∧ v ≤ 1 / 2) ∧ (0 ≤ x ∧ x ≤ 1 / 2) := by
  simp [mixLc, mem_Icc]

theorem measurableSet_mixLc : MeasurableSet mixLc :=
  (measurable_pi_apply (0 : Fin 2) measurableSet_Icc).inter
    (measurable_pi_apply (1 : Fin 2) measurableSet_Icc)

theorem isClosed_mixLc : IsClosed mixLc :=
  (isClosed_Icc.preimage (continuous_apply (0 : Fin 2))).inter
    (isClosed_Icc.preimage (continuous_apply (1 : Fin 2)))

theorem mixLc_subset : mixLc ⊆ Metric.closedBall (0 : Fin 2 → ℝ) (1 / 2) := by
  intro z hz
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hz.1.1], hz.1.2⟩
  · rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hz.2.1], hz.2.2⟩

theorem mixLc_subset_one : mixLc ⊆ Metric.closedBall (0 : Fin 2 → ℝ) 1 :=
  mixLc_subset.trans (Metric.closedBall_subset_closedBall (by norm_num))

theorem isCompact_mixLc : IsCompact mixLc :=
  Metric.isCompact_of_isClosed_isBounded isClosed_mixLc
    (Metric.isBounded_closedBall.subset mixLc_subset)

theorem zero_mem_mixLc : (0 : Fin 2 → ℝ) ∈ mixLc :=
  ⟨⟨le_rfl, by norm_num⟩, ⟨le_rfl, by norm_num⟩⟩

/-- The identity chart of the closed square, with the mixed truth `z₀ z₁` solved for `z₀`. -/
noncomputable def mixDataC : TruthChartsData 1 (fun z ↦ z 0 * z 1) mixLc where
  ι := Unit
  rep := fun _ u ↦ u
  rep_cont := fun _ ↦ continuous_id
  ρ := fun _ ↦ 1
  ρ_pos := fun _ ↦ one_pos
  dom := fun _ ↦ Metric.closedBall (0 : Fin 2 → ℝ) 1 ∩ mixLc
  dom_eq := fun _ ↦ rfl
  dom_meas := fun _ ↦ Metric.isClosed_closedBall.measurableSet.inter measurableSet_mixLc
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
    rw [Fintype.sum_unique, Set.inter_eq_right.mpr mixLc_subset_one]
    refine (setLIntegral_congr_fun measurableSet_mixLc fun u hu ↦ ?_).symm
    rw [toyDens_eq_one (mem_closedBall_zero_iff.mp (mixLc_subset hu)), ENNReal.ofReal_one,
      mul_one]

instance : Unique mixDataC.ι := inferInstanceAs (Unique Unit)

theorem mixDataC_chartFun (θ : (Fin 2 → ℝ) → ℝ≥0∞) (z : Fin 2 → ℝ) :
    mixDataC.chartFun θ default z = mixLc.indicator θ z := by
  unfold TruthChartsData.chartFun
  by_cases hz : z ∈ mixLc
  · have hz' : z ∈ mixDataC.dom default := ⟨mixLc_subset_one hz, hz⟩
    rw [indicator_of_mem hz', indicator_of_mem hz]
    change θ z * ENNReal.ofReal (toyDens z) = θ z
    rw [toyDens_eq_one (mem_closedBall_zero_iff.mp (mixLc_subset hz)), ENNReal.ofReal_one,
      mul_one]
  · have hz' : z ∉ mixDataC.dom default := fun h ↦ hz h.2
    rw [indicator_of_notMem hz', indicator_of_notMem hz]

/-- The branch kernel of the identity chart of the closed square at a positive truth value. -/
theorem mixDataC_branchKernel {θ : (Fin 2 → ℝ) → ℝ≥0∞} {s : ℝ} (hs : 0 < s) (x : ℝ) :
    branchKernel 0 1 ![1, 1] (mixDataC.chartFun θ default) (fun _ : Fin 1 ↦ x) s =
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
    · rw [indicator_of_mem hmem, insertNth_zero_const, mixDataC_chartFun]
      have hxneg : x < 0 := by
        rcases lt_or_eq_of_le hx with h | h
        · exact h
        · exfalso
          simp [h] at hmem
      have hnot : (![-solvedCoord x 1 s, x] : Fin 2 → ℝ) ∉ mixLc := fun h ↦ by
        rw [mem_mixLc_iff] at h
        linarith [h.2.1]
      rw [indicator_of_notMem hnot, zero_mul]
    · rw [indicator_of_notMem hmem]
  · have hpos : s ∈ {s | 0 < x * s} := mul_pos hx hs
    have hneg : s ∉ {s | 0 < x * -1 * s} := fun h ↦ by
      have : x * -1 * s < 0 := by nlinarith
      exact absurd h (not_lt.mpr this.le)
    rw [indicator_of_notMem hneg, zero_add, indicator_of_mem hpos, insertNth_zero_const,
      mixDataC_chartFun, mix_solvedCoord hs, abs_of_pos hx, abs_of_pos hs]
    have hjac : s / x / s = 1 / x := by field_simp
    rw [hjac]
    by_cases hmem : x ∈ Icc (2 * s) (1 / 2)
    · have hin : (![s / x, x] : Fin 2 → ℝ) ∈ mixLc := by
        rw [mem_mixLc_iff]
        exact ⟨⟨(div_pos hs hx).le, by rw [div_le_iff₀ hx]; linarith [hmem.1]⟩, hx.le, hmem.2⟩
      rw [indicator_of_mem hin, indicator_of_mem hmem]
    · have hnot : (![s / x, x] : Fin 2 → ℝ) ∉ mixLc := fun h ↦ by
        rw [mem_mixLc_iff] at h
        refine hmem ⟨?_, h.2.2⟩
        have := (div_le_iff₀ hx).mp h.1.2
        linarith
      rw [indicator_of_notMem hnot, indicator_of_notMem hmem, zero_mul]

/-- The fibre kernel of the closed square is the logarithmic integral, as for `mixData`. -/
theorem mixDataC_totalKernel {θ : (Fin 2 → ℝ) → ℝ≥0∞} {s : ℝ} (hs : 0 < s) :
    mixDataC.totalKernel θ s =
      ∫⁻ x in Icc (2 * s) (1 / 2), θ ![s / x, x] * ENNReal.ofReal (1 / x) := by
  unfold TruthChartsData.totalKernel
  rw [Fintype.sum_unique]
  change fibreKernel 0 1 ![1, 1] (mixDataC.chartFun θ default) s = _
  unfold fibreKernel
  have hmp := volume_preserving_funUnique (Fin 1) ℝ
  change ∫⁻ w : Fin 1 → ℝ, branchKernel 0 1 ![1, 1] (mixDataC.chartFun θ default) w s = _
  refine (hmp.symm.lintegral_comp_emb (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding
    (fun w ↦ branchKernel 0 1 ![1, 1] (mixDataC.chartFun θ default) w s)).symm.trans ?_
  rw [← lintegral_indicator measurableSet_Icc]
  refine lintegral_congr fun x ↦ ?_
  exact mixDataC_branchKernel hs x

theorem mixDataC_totalKernel_eq {θ : (Fin 2 → ℝ) → ℝ≥0∞} {s : ℝ} (hs : 0 < s) :
    mixDataC.totalKernel θ s = mixData.totalKernel θ s := by
  rw [mixDataC_totalKernel hs, mixData_totalKernel hs]

/-! ### The regression -/

/-- The thin region of the mixed truth around the origin: the ball of radius `1/2` cut by
`|z₀ z₁| ≤ ε`. -/
def mixThin (ε : ℝ) : Set (Fin 2 → ℝ) :=
  Metric.closedBall (0 : Fin 2 → ℝ) (1 / 2) ∩ {z | |z 0 * z 1| ≤ ε}

theorem continuous_mixTruth : Continuous fun z : Fin 2 → ℝ ↦ z 0 * z 1 :=
  (continuous_apply 0).mul (continuous_apply 1)

theorem measurableSet_mixThin (ε : ℝ) : MeasurableSet (mixThin ε) :=
  Metric.isClosed_closedBall.measurableSet.inter
    (measurableSet_le (continuous_abs.comp continuous_mixTruth).measurable measurable_const)

/-- **The exported `xy` regression.** Any chart system for the mixed truth `z₀ z₁` over the thin
region `mixThin ε` has the logarithmic coefficient `e^{-σ a(0)} ψ(0)` of the identity chart, for
`F = z₀ z₁ a(z)` and a continuous nonnegative `ψ` supported in the closed square. -/
theorem exported_mix_tendsto_totalKernel {ε : ℝ} (hε : 0 < ε)
    (D : TruthChartsData 1 (fun z ↦ z 0 * z 1) (mixThin ε)) {σ : ℝ} (hσ : 0 < σ)
    {a ψ : (Fin 2 → ℝ) → ℝ} (ha : Continuous a) (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z)
    (hψL : ∀ z, ψ z ≠ 0 → z ∈ mixLc) :
    Tendsto (fun t ↦ (D.totalKernel
        (fun z ↦ ENNReal.ofReal (exp (-(t * (z 0 * z 1 * a z))) * ψ z)) (σ / t)).toReal / log t)
      atTop (𝓝 (exp (-(σ * a 0)) * ψ 0)) := by
  have hT : Measurable fun z : Fin 2 → ℝ ↦ z 0 * z 1 := continuous_mixTruth.measurable
  refine (mix_tendsto_totalKernel hσ ha hψc hψ).congr' ?_
  filter_upwards [eventually_gt_atTop (max 1 (2 * σ / ε))] with t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans ht.le)
  have hs : 0 < σ / t := div_pos hσ ht0
  have hsε : |σ / t| ≤ ε / 2 := by
    rw [abs_of_pos hs, div_le_iff₀ ht0]
    have h2 : 2 * σ / ε < t := (le_max_right _ _).trans_lt ht
    rw [div_lt_iff₀ hε] at h2
    linarith
  -- the observable and its cutoff
  set θr : (Fin 2 → ℝ) → ℝ := fun z ↦ exp (-(t * (z 0 * z 1 * a z))) * ψ z with hθr
  set θ : (Fin 2 → ℝ) → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (θr z) with hθ
  set θε : (Fin 2 → ℝ) → ℝ≥0∞ :=
    fun z ↦ θ z * ENNReal.ofReal (truthCutoff ε (z 0 * z 1)) with hθε
  have hθrc : Continuous θr := by
    rw [hθr]
    fun_prop
  have hθrn : ∀ z, 0 ≤ θr z := fun z ↦ mul_nonneg (exp_pos _).le (hψ z)
  have hθrL : ∀ z, θr z ≠ 0 → z ∈ mixLc := fun z hz ↦ by
    refine hψL z fun h ↦ hz ?_
    simp only [hθr, h, mul_zero]
  have hθc : Continuous θ := ENNReal.continuous_ofReal.comp hθrc
  have hθεc : Continuous θε := by
    have e : θε = fun z ↦ ENNReal.ofReal (θr z * truthCutoff ε (z 0 * z 1)) := by
      funext z
      simp only [hθε, hθ]
      rw [ENNReal.ofReal_mul (hθrn z)]
    rw [e]
    exact ENNReal.continuous_ofReal.comp
      (hθrc.mul ((continuous_truthCutoff ε).comp continuous_mixTruth))
  -- a bound
  obtain ⟨C, hC⟩ := isCompact_mixLc.exists_bound_of_continuousOn hθrc.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 zero_mem_mixLc)
  have hθb : ∀ z, θ z ≤ ENNReal.ofReal C := fun z ↦ by
    by_cases hz : z ∈ mixLc
    · exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hC z hz))
    · have : θr z = 0 := by
        by_contra h
        exact hz (hθrL z h)
      simp only [hθ, this, ENNReal.ofReal_zero]
      exact zero_le
  have hθεb : ∀ z, θε z ≤ ENNReal.ofReal C := fun z ↦ by
    refine (mul_le_of_le_one_right zero_le ?_).trans (hθb z)
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (truthCutoff_le_one _ _)
  -- the cutoff observable is supported in both regions
  have hθεL : ∀ z, θε z ≠ 0 → z ∈ mixLc ∩ mixThin ε := fun z hz ↦ by
    have h1 : θ z ≠ 0 := fun h ↦ hz (by simp only [hθε, h, zero_mul])
    have h2 : truthCutoff ε (z 0 * z 1) ≠ 0 := fun h ↦ hz (by
      simp only [hθε, h, ENNReal.ofReal_zero, mul_zero])
    have hzL : z ∈ mixLc := hθrL z fun h ↦ h1 (by simp only [hθ, h, ENNReal.ofReal_zero])
    exact ⟨hzL, mixLc_subset hzL, (abs_lt_of_truthCutoff_ne_zero hε h2).le⟩
  -- the two kernels of the cutoff observable agree at `σ/t`
  have hae := TruthChartsData.totalKernel_ae_eq_of_support mixDataC D hT measurableSet_mixLc
    (measurableSet_mixThin ε) hθεc.measurable hθεL
  have heq : mixDataC.totalKernel θε (σ / t) = D.totalKernel θε (σ / t) :=
    eq_of_ae_eq_of_continuousAt hae
      (mixDataC.continuousAt_totalKernel hθεc ENNReal.ofReal_ne_top hθεb
        (fun z hz ↦ (hθεL z hz).1) hs.ne')
      (D.continuousAt_totalKernel hθεc ENNReal.ofReal_ne_top hθεb
        (fun z hz ↦ (hθεL z hz).2) hs.ne')
  -- the cutoff is `1` at `σ/t`
  have hcut : ∀ {L : Set (Fin 2 → ℝ)} (D' : TruthChartsData 1 (fun z ↦ z 0 * z 1) L),
      D'.totalKernel θε (σ / t) = D'.totalKernel θ (σ / t) := fun D' ↦ by
    rw [hθε, TruthChartsData.totalKernel_mul_comp_truth D' θ
      (fun s ↦ ENNReal.ofReal (truthCutoff ε s)) ENNReal.ofReal_ne_top,
      truthCutoff_eq_one hε hsε, ENNReal.ofReal_one, one_mul]
  rw [hcut, hcut] at heq
  change (mixData.totalKernel θ (σ / t)).toReal / log t = (D.totalKernel θ (σ / t)).toReal / log t
  rw [← heq, mixDataC_totalKernel_eq hs]

end Laplace.Multi
