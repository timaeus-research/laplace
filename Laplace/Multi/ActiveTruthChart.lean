/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthGeneral
import Laplace.Multi.SpectatorEnvelope
import Laplace.Multi.TermData
import Laplace.Multi.WallPartialTerm

/-!
# The chart-level active-truth term

Astra round 9, item 4: the general-unit face theorem applied to a chart of the wall atlas. The
chart weight `W_φ(x, u) = 1_{dom} φ(rep(bridgePt x u)) wt |b|` and unit `|a(bridgePt x u)|` are
jointly continuous, bounded, and converge as `x → 0` to their values at the truth point
`bridgePt 0 u = (0, …, ±u, …, 0)`; the unit is bounded below by `m_a` on the domain (we replace
it by `max(unit, m_a)` off the domain, which does not change the kernel). The leading measure of
an active-truth chart is therefore the push-forward under `u ↦ rep(bridgePt 0 u)` of the density
`A Γ(β) B^{-β} q D^{-qη} vol(F')/|det M| · u^{qη−1} (wt |b|)(bridgePt 0 u) |a(bridgePt 0 u)|^{-β}`
on `(0, ρ)` (`activeTruthMeasure`): supported on the truth segment of the chart, not at the wall
point (`tendsto_modelKernelOf_activeTruth`, `TermData.activeTruth`).
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

/-- The model kernel only sees the unit on the model domain. -/
theorem modelKernel_congr_unit {ι : Type*} [Fintype ι] {ρ A B D γ p q δ : ℝ} {Q κ r : ι → ℝ}
    {W a a' : (ι → ℝ) → ℝ → ℝ} {t : ℝ}
    (h : ∀ x ∈ modelDomain ρ D γ q Q t, a x (cutVar D γ q Q t x) = a' x (cutVar D γ q Q t x)) :
    modelKernel ρ A B D γ p q δ Q κ r W a t = modelKernel ρ A B D γ p q δ Q κ r W a' t := by
  unfold modelKernel
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  unfold modelIntegrand
  by_cases hx : x ∈ modelDomain ρ D γ q Q t
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, h x hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

theorem continuous_reindex {ι ι' : Type*} (e : ι ≃ ι') :
    Continuous fun y : ι → ℝ ↦ fun j ↦ y (e.symm j) :=
  continuous_pi fun j ↦ continuous_apply (e.symm j)

namespace TruthChartsData.Phase

variable {m k : ℕ} {L' : Set (Fin (m + 1) → ℝ)} {T : (Fin (m + 1) → ℝ) → ℝ}
  {D : TruthChartsData m T L'}
  {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F) {i : D.ι} {ε : Fin m → Bool} {b : Bool}
  {σ γ β η : ℝ} {φ : (Fin (m + 1) → ℝ) → ℝ}

/-- The geometric constant of the active face: `vol(F')/|det M|` for the solved pair chosen by
`e`. -/
noncomputable def faceConst (i : D.ι) (γ : ℝ) (e : Fin k ⊕ Fin 2 ≃ Fin m) : ℝ :=
  (volume (facePolytope (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ)).toReal /
    |(transMat (P.kappa i ∘ e) (D.Qexp i ∘ e)).det|

theorem faceConst_nonneg (i : D.ι) (γ : ℝ) (e : Fin k ⊕ Fin 2 ≃ Fin m) :
    0 ≤ P.faceConst i γ e :=
  div_nonneg ENNReal.toReal_nonneg (abs_nonneg _)

/-- The density of the active-truth measure on the truth segment, before the cut. -/
noncomputable def activeTruthDensityFn (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ β η : ℝ)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) (u : ℝ) : ℝ :=
  P.constA i σ * Gamma β * P.constB i σ ^ (-β) * (D.q i (D.k i) : ℝ) *
    D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) * P.faceConst i γ e *
    (u ^ ((D.q i (D.k i) : ℝ) * η - 1) *
      ((P.wt i (D.bridgePt i ε b 0 u) * |P.b i (D.bridgePt i ε b 0 u)|) *
        |P.a i (D.bridgePt i ε b 0 u)| ^ (-β)))

/-- The density of the active-truth measure on the truth segment. -/
noncomputable def activeTruthDensity (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ β η : ℝ)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) (u : ℝ) : ℝ :=
  (Ioo (0 : ℝ) (D.ρ i)).indicator (P.activeTruthDensityFn i ε b σ γ β η e) u

/-- The leading measure of an active-truth chart: the density pushed forward along the truth
segment `u ↦ rep(bridgePt 0 u)`. -/
noncomputable def activeTruthMeasure (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ β η : ℝ)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) : Measure (Fin (m + 1) → ℝ) :=
  (volume.withDensity fun u ↦ ENNReal.ofReal (P.activeTruthDensity i ε b σ γ β η e u)).map
    (fun u ↦ D.rep i (D.bridgePt i ε b 0 u))

theorem continuous_truthPt (i : D.ι) (ε : Fin m → Bool) (b : Bool) :
    Continuous fun u : ℝ ↦ D.bridgePt i ε b 0 u :=
  (D.continuous_bridgePt i ε b).comp (continuous_const.prodMk continuous_id)

theorem truthPt_mem_ball (i : D.ι) (ε : Fin m → Bool) (b : Bool) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) (D.ρ i)) :
    D.bridgePt i ε b 0 u ∈ Metric.ball (0 : Fin (m + 1) → ℝ) (D.ρ i) :=
  D.bridgePt_mem_ball_of_abs_lt i ε b (D.ρ_pos i) (fun j ↦ by simpa using D.ρ_pos i)
    (by rw [abs_of_pos hu.1]; exact hu.2)

theorem measurable_activeTruthDensityFn (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ β η : ℝ)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) : Measurable (P.activeTruthDensityFn i ε b σ γ β η e) := by
  unfold activeTruthDensityFn
  have hpt := continuous_truthPt (D := D) i ε b
  refine measurable_const.mul ?_
  refine (measurable_id.pow_const _).mul ?_
  refine (((P.wt_cont i).comp hpt).mul (continuous_abs.comp ((P.b_cont i).comp hpt))).measurable.mul
    ?_
  exact ((continuous_abs.comp ((P.a_cont i).comp hpt)).measurable).pow_const _

theorem measurable_activeTruthDensity (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ β η : ℝ)
    (e : Fin k ⊕ Fin 2 ≃ Fin m) : Measurable (P.activeTruthDensity i ε b σ γ β η e) :=
  (P.measurable_activeTruthDensityFn i ε b σ γ β η e).indicator measurableSet_Ioo

theorem activeTruthDensity_nonneg (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ η : ℝ)
    {β : ℝ} (hβ : 0 < β) (e : Fin k ⊕ Fin 2 ≃ Fin m) (u : ℝ) :
    0 ≤ P.activeTruthDensity i ε b σ γ β η e u := by
  unfold activeTruthDensity activeTruthDensityFn
  refine Set.indicator_nonneg (fun u hu ↦ ?_) u
  have h1 := P.constA_nonneg (i := i) (σ := σ)
  have h2 := (Real.Gamma_pos_of_pos hβ).le
  have h3 : 0 ≤ P.constB i σ ^ (-β) := Real.rpow_nonneg (Real.rpow_nonneg (abs_nonneg _) _) _
  have h4 : 0 ≤ D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) :=
    Real.rpow_nonneg (D.constD_nonneg i σ) _
  have h5 := P.faceConst_nonneg i γ e
  have h6 : 0 ≤ u ^ ((D.q i (D.k i) : ℝ) * η - 1) := Real.rpow_nonneg hu.1.le _
  have h7 : 0 ≤ P.wt i (D.bridgePt i ε b 0 u) * |P.b i (D.bridgePt i ε b 0 u)| :=
    mul_nonneg (P.wt_nonneg i _) (abs_nonneg _)
  have h8 : 0 ≤ |P.a i (D.bridgePt i ε b 0 u)| ^ (-β) := Real.rpow_nonneg (abs_nonneg _) _
  have h9 : (0 : ℝ) ≤ (D.q i (D.k i) : ℝ) := Nat.cast_nonneg _
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h9) h4)
    h5) (mul_nonneg h6 (mul_nonneg h7 h8))

theorem integral_activeTruthMeasure (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ η : ℝ)
    {β : ℝ} (hβ : 0 < β) (e : Fin k ⊕ Fin 2 ≃ Fin m) (hφm : Measurable φ) :
    ∫ x, φ x ∂(P.activeTruthMeasure i ε b σ γ β η e) =
      ∫ u, φ (D.rep i (D.bridgePt i ε b 0 u)) * P.activeTruthDensity i ε b σ γ β η e u := by
  unfold activeTruthMeasure
  have hm : Measurable fun u ↦ ENNReal.ofReal (P.activeTruthDensity i ε b σ γ β η e u) :=
    ENNReal.measurable_ofReal.comp (P.measurable_activeTruthDensity i ε b σ γ β η e)
  have hmap : Measurable fun u : ℝ ↦ D.rep i (D.bridgePt i ε b 0 u) :=
    (D.rep_cont i).measurable.comp (continuous_truthPt (D := D) i ε b).measurable
  rw [integral_map hmap.aemeasurable hφm.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ hm.aemeasurable
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (P.activeTruthDensity_nonneg i ε b σ γ η hβ e u), mul_comm]

/-- The density is integrable: `u^{qη−1}` against the bounded chart factors. -/
theorem integrable_activeTruthDensity (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ : ℝ)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) (e : Fin k ⊕ Fin 2 ≃ Fin m) :
    Integrable (P.activeTruthDensity i ε b σ γ β η e) := by
  have hρ := D.ρ_pos i
  have hq : (0 : ℝ) < D.q i (D.k i) := Nat.cast_pos.mpr (D.q_pos i)
  have hd : 0 < (D.q i (D.k i) : ℝ) * η := mul_pos hq hη
  unfold activeTruthDensity
  rw [integrable_indicator_iff measurableSet_Ioo]
  have hint : IntegrableOn (fun u : ℝ ↦ u ^ ((D.q i (D.k i) : ℝ) * η - 1)) (Ioo 0 (D.ρ i)) := by
    have := integrableOn_rpow_mul_log_pow hd zero_le_one le_rfl hρ 0
    refine this.congr_fun (fun x _ ↦ ?_) measurableSet_Ioo
    simp
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = P.constA i σ * Gamma β * P.constB i σ ^ (-β) *
    (D.q i (D.k i) : ℝ) * D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) * P.faceConst i γ e :=
    ⟨_, rfl⟩
  refine (hint.const_mul (|C| * (P.Mb i * P.ma i ^ (-β)))).mono' ?_ ?_
  · exact (P.measurable_activeTruthDensityFn i ε b σ γ β η e).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun u hu ↦ ?_
    have hcb : D.bridgePt i ε b 0 u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i) :=
      Metric.ball_subset_closedBall (truthPt_mem_ball (D := D) i ε b hu)
    have hb := (P.b_bounds i _ hcb).2
    have ha := (P.a_bounds i _ hcb).1
    have hu0 : 0 ≤ u ^ ((D.q i (D.k i) : ℝ) * η - 1) := Real.rpow_nonneg hu.1.le _
    have hapow : |P.a i (D.bridgePt i ε b 0 u)| ^ (-β) ≤ P.ma i ^ (-β) := by
      rw [Real.rpow_neg (abs_nonneg _), Real.rpow_neg (P.ma_pos i).le]
      exact inv_anti₀ (Real.rpow_pos_of_pos (P.ma_pos i) _)
        (Real.rpow_le_rpow (P.ma_pos i).le ha hβ.le)
    have hwb : P.wt i (D.bridgePt i ε b 0 u) * |P.b i (D.bridgePt i ε b 0 u)| ≤ P.Mb i := by
      calc P.wt i (D.bridgePt i ε b 0 u) * |P.b i (D.bridgePt i ε b 0 u)| ≤ 1 * P.Mb i :=
            mul_le_mul (P.wt_le_one i _) hb (abs_nonneg _) zero_le_one
        _ = P.Mb i := one_mul _
    have h7 : 0 ≤ P.wt i (D.bridgePt i ε b 0 u) * |P.b i (D.bridgePt i ε b 0 u)| :=
      mul_nonneg (P.wt_nonneg i _) (abs_nonneg _)
    have h8 : 0 ≤ |P.a i (D.bridgePt i ε b 0 u)| ^ (-β) := Real.rpow_nonneg (abs_nonneg _) _
    unfold activeTruthDensityFn
    rw [hC, Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg hu0 (mul_nonneg h7 h8))]
    calc |P.constA i σ * Gamma β * P.constB i σ ^ (-β) * (D.q i (D.k i) : ℝ) *
          D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) * P.faceConst i γ e| *
          (u ^ ((D.q i (D.k i) : ℝ) * η - 1) *
            (P.wt i (D.bridgePt i ε b 0 u) * |P.b i (D.bridgePt i ε b 0 u)| *
              |P.a i (D.bridgePt i ε b 0 u)| ^ (-β)))
        ≤ |P.constA i σ * Gamma β * P.constB i σ ^ (-β) * (D.q i (D.k i) : ℝ) *
          D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) * P.faceConst i γ e| *
          (u ^ ((D.q i (D.k i) : ℝ) * η - 1) * (P.Mb i * P.ma i ^ (-β))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul hwb hapow h8 P.Mb_nonneg) hu0) (abs_nonneg _)
      _ = _ := by ring

theorem isFiniteMeasure_activeTruthMeasure (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ : ℝ)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) (e : Fin k ⊕ Fin 2 ≃ Fin m) :
    IsFiniteMeasure (P.activeTruthMeasure i ε b σ γ β η e) := by
  unfold activeTruthMeasure
  have := isFiniteMeasure_withDensity_ofReal
    (P.integrable_activeTruthDensity i ε b σ γ hβ hη e).hasFiniteIntegral
  infer_instance

/-- **The active-truth chart term**: the normalised model kernel of an active-truth chart converges
to the integral of the observable against the active-truth measure. -/
theorem tendsto_modelKernelOf_activeTruth (e : Fin k ⊕ Fin 2 ≃ Fin m) (hσ : σ ≠ 0)
    (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ P.phaseExp i γ) (hκ : ∀ j, 0 < P.kappa i j)
    (hΔ : (transMat (P.kappa i ∘ e) (D.Qexp i ∘ e)).det ≠ 0)
    (hc₀ : fibreCoef (P.kappa i ∘ e) (D.Qexp i ∘ e) 0 ≠ 0 ∨
      fibreA (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ 0 ≠ 0)
    (hc₁ : fibreCoef (P.kappa i ∘ e) (D.Qexp i ∘ e) 1 ≠ 0 ∨
      fibreA (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ 1 ≠ 0)
    (hr : ∀ j, P.rExp i (e j) + 1 = β * P.kappa i (e j) - η * D.Qexp i (e j))
    (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ)
    (hφL : ∀ z, φ z ≠ 0 → z ∈ L') :
    Tendsto (fun t ↦ t ^ (γ * P.pExp i + (β * P.phaseExp i γ - η * γ)) / log t ^ k *
        P.modelKernelOf i φ ε b t γ σ) atTop
      (𝓝 (∫ x, φ x ∂(P.activeTruthMeasure i ε b σ γ β η e))) := by
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
  have hgen := tendsto_modelKernel_general (k := k) (ρ := D.ρ i) (A := P.constA i σ)
    (B := P.constB i σ) (D := D.constD i σ) (γ := γ) (p := P.pExp i) (q := D.q i (D.k i))
    (δ := P.phaseExp i γ) (β := β) (η := η) (Q := D.Qexp i ∘ e) (κ := P.kappa i ∘ e)
    (r := P.rExp i ∘ e) (W := We) (a := ae') (Wstar := Mφ * P.Mb i) (amin := P.ma i)
    (Wtr := fun u ↦ P.weightFn i φ ε b 0 u) (atr := fun u ↦ P.unitFn i ε b 0 u)
    hρ hDpos hq hB hβ hη hδ (fun j ↦ hκ _) hΔ hc₀ hc₁ (fun j ↦ hr j) (P.ma_pos i)
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
  -- the limit value is the integral against the active-truth measure
  have hval : ∫ x, φ x ∂(P.activeTruthMeasure i ε b σ γ β η e) =
      P.constA i σ * Gamma β * P.constB i σ ^ (-β) * (D.q i (D.k i) : ℝ) *
        D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) *
        (volume (facePolytope (P.kappa i ∘ e) (D.Qexp i ∘ e) (P.phaseExp i γ) γ)).toReal /
        |(transMat (P.kappa i ∘ e) (D.Qexp i ∘ e)).det| *
        ∫ u in Ioo (0 : ℝ) (D.ρ i), u ^ ((D.q i (D.k i) : ℝ) * η - 1) *
          (P.weightFn i φ ε b 0 u * P.unitFn i ε b 0 u ^ (-β)) := by
    rw [P.integral_activeTruthMeasure i ε b σ γ η hβ e hφc.measurable]
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
/-- **The active-truth term**: `(γp + βδ − ηγ, k, activeTruthMeasure)`. -/
noncomputable def TermData.activeTruth (e : Fin k ⊕ Fin 2 ≃ Fin m) (hσ : σ ≠ 0)
    {p : TruthChartsData.Phase.TermIdx D} (hadm : D.admissible p.1 p.2.1 p.2.2 σ) (hβ : 0 < β)
    (hη : 0 < η) (hδ : 0 ≤ P.phaseExp p.1 γ) (hκ : ∀ j, 0 < P.kappa p.1 j)
    (hΔ : (transMat (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e)).det ≠ 0)
    (hc₀ : fibreCoef (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e) 0 ≠ 0 ∨
      fibreA (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e) (P.phaseExp p.1 γ) γ 0 ≠ 0)
    (hc₁ : fibreCoef (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e) 1 ≠ 0 ∨
      fibreA (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e) (P.phaseExp p.1 γ) γ 1 ≠ 0)
    (hr : ∀ j, P.rExp p.1 (e j) + 1 = β * P.kappa p.1 (e j) - η * D.Qexp p.1 (e j)) :
    P.TermData σ γ p where
  lam := γ * P.pExp p.1 + (β * P.phaseExp p.1 γ - η * γ)
  kk := k
  μ := P.activeTruthMeasure p.1 p.2.1 p.2.2 σ γ β η e
  finite := P.isFiniteMeasure_activeTruthMeasure p.1 p.2.1 p.2.2 σ γ hβ hη e
  tendsto := fun φ hφc hφ ⟨M, hM⟩ hφL ↦ by
    have h := P.tendsto_modelKernelOf_activeTruth (ε := p.2.1) (b := p.2.2) e hσ hβ hη hδ hκ hΔ
      hc₀ hc₁ hr hφc hφ hM hφL
    refine h.congr' (Eventually.of_forall fun t ↦ ?_)
    unfold termKernel
    simp only [if_pos hadm]

end TruthChartsData.Phase

end Laplace.Multi
