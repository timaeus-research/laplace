/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PartialTiedVariable
import Laplace.Multi.WallLogTerm

/-!
# The partially tied term of a wall chart

The chart-level form of `tendsto_modelKernel_partial_var`. A wall chart with a pure truth
monomial (`Q = 0`) whose transverse coordinates split, along `e : Fin (k+1) ⊕ ν ≃ Fin m`, into a
tied block (`(r_j+1)/κ_j = λ`) and a strictly worse block (`λκ_j < r_j + 1`). Reindexing the model
kernel along `e` (`modelKernel_reindex`, Lebesgue measure is invariant under
`MeasurableEquiv.piCongrLeft`) puts it in the form of the partially tied model; the chart weight
is jointly continuous at every face point `(x_z, 0)` whose bridge point lies in the open ball
(`continuousAt_weightFn`), the unit everywhere (`continuousAt_unitFn`), and the unit is bounded
below by `m_a` on the closed ball. Hence (`tendsto_modelKernelOf_partial`)

`t^{γp+δλ}/(log t)^k K(t) → A δ^k Γ(λ)/k! ∏_T κ^{-1} ∫_{(0,ρ)^N} F(pt_z) ∏_N z^{r−λκ} dz`,
`F(pt) = φ(ρ_i(pt)) wt(pt) |b(pt)| (B |a(pt)|)^{-λ}`,

where `pt_z = bridgePt x_z 0` is the face point with solved coordinate `0`, tied coordinates `0`
and worse coordinates `±z`: the face density of a partially tied face at the chart level.
-/

open Real MeasureTheory Set Filter Topology Function

namespace Laplace.Multi

section Reindex

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

omit [Fintype ι] [Fintype ι'] in
theorem piCongrLeft_apply_const (e : ι ≃ ι') (y : ι → ℝ) :
    (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e) y = fun j ↦ y (e.symm j) := by
  funext j
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

omit [Fintype ι] [Fintype ι'] in
theorem reindex_mem_box (e : ι ≃ ι') {ρ : ℝ} (y : ι → ℝ) :
    (fun j ↦ y (e.symm j)) ∈ (Set.pi univ fun _ : ι' ↦ Ioo (0 : ℝ) ρ) ↔
      y ∈ (Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ) := by
  simp only [Set.mem_univ_pi]
  constructor
  · intro h j
    simpa using h (e j)
  · intro h j
    exact h _

theorem cutVar_reindex (e : ι ≃ ι') {D γ q t : ℝ} (Q : ι' → ℝ) (y : ι → ℝ) :
    cutVar D γ q Q t (fun j ↦ y (e.symm j)) = cutVar D γ q (Q ∘ e) t y := by
  unfold cutVar
  congr 1
  exact (Equiv.prod_comp e fun j ↦ y (e.symm j) ^ (-(Q j / q))).symm.trans
    (Finset.prod_congr rfl fun j _ ↦ by simp)

theorem modelDomain_reindex (e : ι ≃ ι') {ρ D γ q t : ℝ} (Q : ι' → ℝ) (y : ι → ℝ) :
    (fun j ↦ y (e.symm j)) ∈ modelDomain ρ D γ q Q t ↔ y ∈ modelDomain ρ D γ q (Q ∘ e) t := by
  unfold modelDomain
  rw [Set.mem_inter_iff, Set.mem_inter_iff, reindex_mem_box, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
    cutVar_reindex]

theorem prod_reindex_rpow (e : ι ≃ ι') (f : ι' → ℝ) (y : ι → ℝ) :
    ∏ j, y (e.symm j) ^ f j = ∏ j, y j ^ f (e j) :=
  (Equiv.prod_comp e fun j ↦ y (e.symm j) ^ f j).symm.trans
    (Finset.prod_congr rfl fun j _ ↦ by simp)

/-- The model kernel is invariant under reindexing the coordinates. -/
theorem modelKernel_reindex (e : ι ≃ ι') {ρ A B D γ p q δ : ℝ} (Q κ r : ι' → ℝ)
    (W a : (ι' → ℝ) → ℝ → ℝ) (t : ℝ) :
    modelKernel ρ A B D γ p q δ Q κ r W a t =
      modelKernel ρ A B D γ p q δ (Q ∘ e) (κ ∘ e) (r ∘ e) (fun y v ↦ W (fun j ↦ y (e.symm j)) v)
        (fun y v ↦ a (fun j ↦ y (e.symm j)) v) t := by
  unfold modelKernel
  congr 1
  rw [← (volume_measurePreserving_piCongrLeft (fun _ : ι' ↦ ℝ) e).integral_comp'
    (modelIntegrand ρ B D γ q δ Q κ r W a t)]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  beta_reduce
  rw [piCongrLeft_apply_const]
  unfold modelIntegrand
  by_cases hy : y ∈ modelDomain ρ D γ q (Q ∘ e) t
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem ((modelDomain_reindex e Q y).mpr hy),
      cutVar_reindex, prod_reindex_rpow, prod_reindex_rpow]
    rfl
  · rw [Set.indicator_of_notMem hy,
      Set.indicator_of_notMem (fun h ↦ hy ((modelDomain_reindex e Q y).mp h))]

end Reindex

variable {m : ℕ} {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}

namespace WallChartsData

variable (D : WallChartsData m ℓ L')

/-- The bridge point lies in the open ball as soon as all its coordinates do. -/
theorem bridgePt_mem_ball_of_abs_lt (i : D.ι) (ε : Fin m → Bool) (b : Bool) {ρ : ℝ} (hρ : 0 < ρ)
    {x : Fin m → ℝ} (hx : ∀ j, |x j| < ρ) {v : ℝ} (hv : |v| < ρ) :
    D.bridgePt i ε b x v ∈ Metric.ball (0 : Fin (m + 1) → ℝ) ρ := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff hρ, Fin.forall_iff_succAbove (D.k i)]
  simp only [bridgePt, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Real.norm_eq_abs,
    abs_mul, abs_bsign, one_mul, abs_orth]
  exact ⟨hv, hx⟩

namespace Phase

variable {D} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)
variable {i : D.ι} {ε : Fin m → Bool} {b : Bool} {φ : (Fin (m + 1) → ℝ) → ℝ}

/-- Joint continuity of the weight at any point whose bridge point lies in the open ball. -/
theorem continuousAt_weightFn (hφc : Continuous φ) (hφL : ∀ z, φ z ≠ 0 → z ∈ L')
    {x₀ : Fin m → ℝ} {v₀ : ℝ}
    (hb : D.bridgePt i ε b x₀ v₀ ∈ Metric.ball (0 : Fin (m + 1) → ℝ) (D.ρ i)) :
    ContinuousAt (uncurry (P.weightFn i φ ε b)) (x₀, v₀) := by
  have hg : Continuous fun z ↦ φ (D.rep i z) * (P.wt i z * |P.b i z|) :=
    (hφc.comp (D.rep_cont i)).mul ((P.wt_cont i).mul (continuous_abs.comp (P.b_cont i)))
  have hbp := D.continuous_bridgePt i ε b
  have hlim : ContinuousAt (fun p : (Fin m → ℝ) × ℝ ↦
      (fun z ↦ φ (D.rep i z) * (P.wt i z * |P.b i z|)) (D.bridgePt i ε b p.1 p.2)) (x₀, v₀) :=
    (hg.continuousAt).comp hbp.continuousAt
  have hball : ∀ᶠ p : (Fin m → ℝ) × ℝ in 𝓝 (x₀, v₀),
      D.bridgePt i ε b p.1 p.2 ∈ Metric.ball (0 : Fin (m + 1) → ℝ) (D.ρ i) :=
    hbp.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hb)
  refine hlim.congr (Filter.EventuallyEq.symm ?_)
  filter_upwards [hball] with p hp
  exact P.weightFn_eq_of_mem_closedBall hφL (Metric.ball_subset_closedBall hp)

theorem continuousAt_unitFn (p : (Fin m → ℝ) × ℝ) :
    ContinuousAt (uncurry (P.unitFn i ε b)) p :=
  ((continuous_abs.comp (P.a_cont i)).comp (D.continuous_bridgePt i ε b)).continuousAt

/-- The unit at a point of the open ball is at least `m_a`. -/
theorem ma_le_unitFn_of_mem_ball {x : Fin m → ℝ} {v : ℝ}
    (hb : D.bridgePt i ε b x v ∈ Metric.ball (0 : Fin (m + 1) → ℝ) (D.ρ i)) :
    P.ma i ≤ P.unitFn i ε b x v :=
  (P.a_bounds i _ (Metric.ball_subset_closedBall hb)).1

end Phase

end WallChartsData

section PartialTerm

variable {k : ℕ} {ν : Type*} [Fintype ν] {D : WallChartsData m ℓ L'}
  {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)
  {i : D.ι} {ε : Fin m → Bool} {b : Bool} {σ γ : ℝ} {φ : (Fin (m + 1) → ℝ) → ℝ}

/-- The transverse face point of a partially tied face: tied coordinates `0`, worse coordinates
`z`. -/
def partialFace (e : Fin (k + 1) ⊕ ν ≃ Fin m) (z : ν → ℝ) : Fin m → ℝ :=
  fun j ↦ Sum.elim (0 : Fin (k + 1) → ℝ) z (e.symm j)

omit [Fintype ν] in
theorem abs_partialFace_lt (e : Fin (k + 1) ⊕ ν ≃ Fin m) {ρ : ℝ} (hρ : 0 < ρ) {z : ν → ℝ}
    (hz : ∀ j, z j ∈ Ioo (0 : ℝ) ρ) (j : Fin m) : |partialFace e z j| < ρ := by
  unfold partialFace
  rcases h : e.symm j with l | l
  · simp [hρ]
  · simp only [Sum.elim_inr]
    rw [abs_of_pos (hz l).1]
    exact (hz l).2

/-- **The partially tied term asymptotic of a wall chart.** For a chart with a pure truth
monomial (`Q = 0`) whose transverse coordinates split along `e` into a tied block and a
strictly worse block, `t^{γp + δλ}/(log t)^k · K(t)` converges to the face integral of the
weight times the `−λ` power of the unit against the residual monomial. -/
theorem WallChartsData.Phase.tendsto_modelKernelOf_partial (e : Fin (k + 1) ⊕ ν ≃ Fin m)
    (hσ : σ ≠ 0) (hγ : 0 < γ) (hQ : D.Qexp i = 0) (hκ : ∀ j, 0 < P.kappa i j) {lam : ℝ}
    (hlam : 0 < lam)
    (htied : ∀ j, (P.rExp i (e (Sum.inl j)) + 1) / P.kappa i (e (Sum.inl j)) = lam)
    (hgap : ∀ j, lam * P.kappa i (e (Sum.inr j)) < P.rExp i (e (Sum.inr j)) + 1)
    (hδ : 0 < P.phaseExp i γ) (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ}
    (hMφ : ∀ z, φ z ≤ Mφ) (hφL : ∀ z, φ z ≠ 0 → z ∈ L') :
    Tendsto (fun t ↦ t ^ (γ * P.pExp i + P.phaseExp i γ * lam) / log t ^ k *
        P.modelKernelOf i φ ε b t γ σ) atTop
      (𝓝 (P.constA i σ * (P.phaseExp i γ ^ k *
          (Gamma lam / k.factorial * ∏ j, 1 / P.kappa i (e (Sum.inl j)))) *
        ∫ z in Set.pi univ (fun _ : ν ↦ Ioo (0 : ℝ) (D.ρ i)),
          φ (D.rep i (D.bridgePt i ε b (partialFace e z) 0)) *
            (P.wt i (D.bridgePt i ε b (partialFace e z) 0) *
              |P.b i (D.bridgePt i ε b (partialFace e z) 0)|) *
            (P.constB i σ * |P.a i (D.bridgePt i ε b (partialFace e z) 0)|) ^ (-lam) *
            ∏ j, z j ^ (P.rExp i (e (Sum.inr j)) - lam * P.kappa i (e (Sum.inr j))))) := by
  have hρ := D.ρ_pos i
  have hmapC : Continuous fun p : (Fin (k + 1) ⊕ ν → ℝ) × ℝ ↦
      ((fun j ↦ p.1 (e.symm j)), p.2) :=
    (continuous_pi fun j ↦ (continuous_apply (e.symm j)).comp continuous_fst).prodMk
      continuous_snd
  have hmapM : Measurable fun p : (Fin (k + 1) ⊕ ν → ℝ) × ℝ ↦
      ((fun j ↦ p.1 (e.symm j)), p.2) :=
    (measurable_pi_lambda _ fun j ↦ (measurable_pi_apply (e.symm j)).comp measurable_fst).prodMk
      measurable_snd
  have hface : ∀ z : ν → ℝ, (∀ j, z j ∈ Ioo (0 : ℝ) (D.ρ i)) →
      D.bridgePt i ε b (partialFace e z) 0 ∈ Metric.ball (0 : Fin (m + 1) → ℝ) (D.ρ i) :=
    fun z hz ↦ D.bridgePt_mem_ball_of_abs_lt i ε b hρ (abs_partialFace_lt e hρ hz)
      (by rw [abs_zero]; exact hρ)
  unfold WallChartsData.Phase.modelKernelOf
  rw [hQ]
  have hre : ∀ t, modelKernel (D.ρ i) (P.constA i σ) (P.constB i σ) (D.constD i σ) γ (P.pExp i)
      (D.q i (D.k i)) (P.phaseExp i γ) (0 : Fin m → ℝ) (P.kappa i) (P.rExp i)
      (P.weightFn i φ ε b) (P.unitFn i ε b) t =
      modelKernel (D.ρ i) (P.constA i σ) (P.constB i σ) (D.constD i σ) γ (P.pExp i)
        (D.q i (D.k i)) (P.phaseExp i γ) ((0 : Fin m → ℝ) ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e)
        (fun y v ↦ P.weightFn i φ ε b (fun j ↦ y (e.symm j)) v)
        (fun y v ↦ P.unitFn i ε b (fun j ↦ y (e.symm j)) v) t :=
    fun t ↦ modelKernel_reindex e _ _ _ _ _ t
  simp only [hre]
  have h := tendsto_modelKernel_partial_var (A := P.constA i σ) (B := P.constB i σ)
    (p := P.pExp i) (κ := P.kappa i ∘ e) (r := P.rExp i ∘ e)
    (W := fun y v ↦ P.weightFn i φ ε b (fun j ↦ y (e.symm j)) v)
    (a := fun y v ↦ P.unitFn i ε b (fun j ↦ y (e.symm j)) v) hρ (D.constD_nonneg i σ)
    (fun j ↦ hκ _) hlam htied hgap (P.constB_pos hσ) hδ
    (div_pos hγ (Nat.cast_pos.mpr (D.q_pos i))) (P.ma_pos i)
    ((P.measurable_weightFn hφc.measurable).comp hmapM) (P.measurable_unitFn.comp hmapM)
    (fun x v ↦ P.weightFn_nonneg hφ _ _)
    (fun x v ↦ (le_abs_self _).trans (P.abs_weightFn_le hφ hMφ _ _))
    (fun x v hx hv0 hv ↦ P.ma_le_unitFn (fun j ↦ hx (e.symm j)) hv0 hv)
    (fun z hz ↦ (P.ma_pos i).trans_le (P.ma_le_unitFn_of_mem_ball (hface z hz)))
    (fun z hz ↦ (P.continuousAt_weightFn hφc hφL (hface z hz)).comp_of_eq hmapC.continuousAt rfl)
    (fun z _ ↦ (P.continuousAt_unitFn (partialFace e z, 0)).comp_of_eq hmapC.continuousAt rfl)
  have hbox : MeasurableSet (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) (D.ρ i)) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have hint : (∫ z in Set.pi univ (fun _ : ν ↦ Ioo (0 : ℝ) (D.ρ i)),
      φ (D.rep i (D.bridgePt i ε b (partialFace e z) 0)) *
        (P.wt i (D.bridgePt i ε b (partialFace e z) 0) *
          |P.b i (D.bridgePt i ε b (partialFace e z) 0)|) *
        (P.constB i σ * |P.a i (D.bridgePt i ε b (partialFace e z) 0)|) ^ (-lam) *
        ∏ j, z j ^ (P.rExp i (e (Sum.inr j)) - lam * P.kappa i (e (Sum.inr j)))) =
      ∫ z in Set.pi univ (fun _ : ν ↦ Ioo (0 : ℝ) (D.ρ i)),
        P.weightFn i φ ε b (partialFace e z) 0 *
          (P.constB i σ * P.unitFn i ε b (partialFace e z) 0) ^ (-lam) *
          ∏ j, z j ^ (P.rExp i (e (Sum.inr j)) - lam * P.kappa i (e (Sum.inr j))) := by
    refine setIntegral_congr_fun hbox fun z hz ↦ ?_
    have hzb : ∀ j, z j ∈ Ioo (0 : ℝ) (D.ρ i) := Set.mem_univ_pi.mp hz
    rw [P.weightFn_eq_of_mem_closedBall hφL (Metric.ball_subset_closedBall (hface z hzb))]
    rfl
  rw [hint]
  exact h

end PartialTerm

end Laplace.Multi
