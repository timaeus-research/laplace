/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LogExactConstant
import Laplace.Multi.LimitingMeasure

/-!
# The logarithmic term asymptotic at the chart level

The exact constant of a fully tied logarithmic face (`LogExactConstant`) transported to a wall
chart term. For a chart whose transverse truth exponents vanish (`Q = 0`, a pure truth monomial
`z_ℓ = S u_k^{q_k}`) and whose transverse face is fully tied (`κ_j > 0`, `(r_j+1)/κ_j = λ` for all
`j`), the weight `W(x, v) = 1_dom(bp(x,v)) φ(rep bp) wt(bp)|b(bp)|` and the unit
`a(x, v) = |a(bp(x, v))|` of the model kernel are jointly continuous at the face point `(0, 0)`
(the bridge point `bp(0, 0) = 0` lies in the open box; `tendsto_weightFn_face`,
`tendsto_unitFn_face`), the unit is bounded below by `m_a` for small cut values, and the weight is
bounded by `M_φ M_b`. Hence

`t^{γp + δλ} / (log t)^k · K_{i,ε,b}(t) → tiedConst A B δ κ r λ ρ |a(0)| (φ(rep 0) wt(0) |b(0)|)`

(`tendsto_modelKernelOf_tied`): the logarithmic term constant is the constant-unit one with the
unit, the observable and the weight evaluated at the wall point.
-/

open Real MeasureTheory Set Filter Topology Function

namespace Laplace.Multi

variable {m : ℕ} {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}

namespace WallChartsData

variable (D : WallChartsData m ℓ L')

theorem bridgePt_zero (i : D.ι) (ε : Fin m → Bool) (b : Bool) : D.bridgePt i ε b 0 0 = 0 := by
  unfold bridgePt
  funext j
  revert j
  rw [Fin.forall_iff_succAbove (D.k i)]
  refine ⟨by rw [Fin.insertNth_apply_same]; simp, fun j ↦ ?_⟩
  rw [Fin.insertNth_apply_succAbove]
  simp [orth]

theorem continuous_bridgePt (i : D.ι) (ε : Fin m → Bool) (b : Bool) :
    Continuous fun p : (Fin m → ℝ) × ℝ ↦ D.bridgePt i ε b p.1 p.2 :=
  Continuous.finInsertNth (D.k i) (continuous_const.mul continuous_snd)
    ((continuous_orth ε).comp continuous_fst)

theorem constD_nonneg (i : D.ι) (σ : ℝ) : 0 ≤ D.constD i σ := rpow_nonneg (abs_nonneg _) _

namespace Phase

variable {D} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)
variable {i : D.ι} {ε : Fin m → Bool} {b : Bool} {σ γ : ℝ} {φ : (Fin (m + 1) → ℝ) → ℝ}

theorem constB_pos (hσ : σ ≠ 0) : 0 < P.constB i σ := rpow_pos_of_pos (abs_pos.mpr hσ) _

theorem weightFn_nonneg (hφ : ∀ z, 0 ≤ φ z) (x : Fin m → ℝ) (v : ℝ) :
    0 ≤ P.weightFn i φ ε b x v :=
  Set.indicator_nonneg (fun u _ ↦ mul_nonneg (hφ _) (mul_nonneg (P.wt_nonneg i u) (abs_nonneg _)))
    _

/-- Inside the closed box the weight is the smooth expression, for an observable supported in
`L'`. -/
theorem weightFn_eq_of_mem_closedBall (hφL : ∀ z, φ z ≠ 0 → z ∈ L') {x : Fin m → ℝ} {v : ℝ}
    (h : D.bridgePt i ε b x v ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i)) :
    P.weightFn i φ ε b x v = φ (D.rep i (D.bridgePt i ε b x v)) *
      (P.wt i (D.bridgePt i ε b x v) * |P.b i (D.bridgePt i ε b x v)|) := by
  unfold WallChartsData.Phase.weightFn
  by_cases hφ0 : φ (D.rep i (D.bridgePt i ε b x v)) = 0
  · rw [hφ0, zero_mul]
    exact (Set.indicator_apply_eq_zero (s := D.dom i)
      (f := fun u ↦ φ (D.rep i u) * (P.wt i u * |P.b i u|)) (a := D.bridgePt i ε b x v)).mpr
      fun _ ↦ by rw [hφ0, zero_mul]
  · have hmem : D.bridgePt i ε b x v ∈ D.dom i := by
      rw [D.dom_eq]
      exact ⟨h, hφL _ hφ0⟩
    rw [Set.indicator_of_mem hmem]

/-- Joint continuity of the weight at the face point. -/
theorem tendsto_weightFn_face (hφc : Continuous φ) (hφL : ∀ z, φ z ≠ 0 → z ∈ L') :
    Tendsto (uncurry (P.weightFn i φ ε b)) (𝓝 (0, 0))
      (𝓝 (φ (D.rep i 0) * (P.wt i 0 * |P.b i 0|))) := by
  have hg : Continuous fun z ↦ φ (D.rep i z) * (P.wt i z * |P.b i z|) :=
    (hφc.comp (D.rep_cont i)).mul ((P.wt_cont i).mul (continuous_abs.comp (P.b_cont i)))
  have hbp := D.continuous_bridgePt i ε b
  have hlim : Tendsto (fun p : (Fin m → ℝ) × ℝ ↦
      (fun z ↦ φ (D.rep i z) * (P.wt i z * |P.b i z|)) (D.bridgePt i ε b p.1 p.2)) (𝓝 (0, 0))
      (𝓝 (φ (D.rep i 0) * (P.wt i 0 * |P.b i 0|))) := by
    have := (hg.tendsto (D.bridgePt i ε b 0 0)).comp (hbp.tendsto (0, 0))
    rwa [D.bridgePt_zero] at this
  refine hlim.congr' ?_
  have hball : ∀ᶠ p : (Fin m → ℝ) × ℝ in 𝓝 (0, 0),
      D.bridgePt i ε b p.1 p.2 ∈ Metric.ball (0 : Fin (m + 1) → ℝ) (D.ρ i) := by
    refine hbp.continuousAt.preimage_mem_nhds ?_
    rw [D.bridgePt_zero]
    exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (D.ρ_pos i))
  filter_upwards [hball] with p hp
  exact (P.weightFn_eq_of_mem_closedBall hφL (Metric.ball_subset_closedBall hp)).symm

/-- Joint continuity of the unit at the face point. -/
theorem tendsto_unitFn_face :
    Tendsto (uncurry (P.unitFn i ε b)) (𝓝 (0, 0)) (𝓝 |P.a i 0|) := by
  have := ((continuous_abs.comp (P.a_cont i)).tendsto (D.bridgePt i ε b 0 0)).comp
    ((D.continuous_bridgePt i ε b).tendsto (0, 0))
  rwa [D.bridgePt_zero] at this

/-- The unit is bounded below on the box for small cut values. -/
theorem ma_le_unitFn {x : Fin m → ℝ} (hx : ∀ j, x j ∈ Ioo (0 : ℝ) (D.ρ i)) {v : ℝ} (hv0 : 0 ≤ v)
    (hv : v < D.ρ i) : P.ma i ≤ P.unitFn i ε b x v := by
  have hb : D.bridgePt i ε b x v ∈ Metric.ball (0 : Fin (m + 1) → ℝ) (D.ρ i) :=
    (D.bridgePt_mem_ball_iff i ε b (D.ρ_pos i) (fun j ↦ (hx j).1) hv0).mpr
      ⟨fun j ↦ (hx j).2, hv⟩
  exact (P.a_bounds i _ (Metric.ball_subset_closedBall hb)).1

theorem ma_le_abs_a_zero : P.ma i ≤ |P.a i 0| :=
  (P.a_bounds i 0 (Metric.mem_closedBall_self (D.ρ_pos i).le)).1

end Phase

end WallChartsData

section LogTerm

variable {k : ℕ} {ℓ : Fin (k + 1 + 1)} {L' : Set (Fin (k + 1 + 1) → ℝ)}
  {D : WallChartsData (k + 1) ℓ L'} {F : (Fin (k + 1 + 1) → ℝ) → ℝ} (P : D.Phase F)
  {i : D.ι} {ε : Fin (k + 1) → Bool} {b : Bool} {σ γ : ℝ} {φ : (Fin (k + 1 + 1) → ℝ) → ℝ}

/-- **The logarithmic term asymptotic of a wall chart.** For a chart with a pure truth monomial
(`Q = 0`) and a fully tied transverse face, the model kernel of the term satisfies
`t^{γp + δλ}/(log t)^k · K(t) → tiedConst A B δ κ r λ ρ |a(0)| (φ(rep 0) wt(0) |b(0)|)`. -/
theorem WallChartsData.Phase.tendsto_modelKernelOf_tied (hσ : σ ≠ 0) (hγ : 0 < γ)
    (hQ : D.Qexp i = 0) (hκ : ∀ j, 0 < P.kappa i j) {lam : ℝ} (hlam : 0 < lam)
    (htied : ∀ j, (P.rExp i j + 1) / P.kappa i j = lam) (hδ : 0 < P.phaseExp i γ)
    (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ)
    (hφL : ∀ z, φ z ≠ 0 → z ∈ L') :
    Tendsto (fun t ↦ t ^ (γ * P.pExp i + P.phaseExp i γ * lam) / log t ^ k *
        P.modelKernelOf i φ ε b t γ σ) atTop
      (𝓝 (tiedConst (P.constA i σ) (P.constB i σ) (P.phaseExp i γ) (P.kappa i) (P.rExp i) lam
        (D.ρ i) |P.a i 0| (φ (D.rep i 0) * (P.wt i 0 * |P.b i 0|)))) := by
  unfold WallChartsData.Phase.modelKernelOf
  rw [hQ]
  refine tendsto_modelKernel_tied (D.ρ_pos i) P.constA_nonneg (D.constD_nonneg i σ) hκ hlam htied
    (P.constB_pos hσ) hδ (div_pos hγ (Nat.cast_pos.mpr (D.q_pos i))) (P.ma_pos i)
    (P.measurable_weightFn hφc.measurable) P.measurable_unitFn (P.weightFn_nonneg hφ)
    (fun x v ↦ (le_abs_self _).trans (P.abs_weightFn_le hφ hMφ x v))
    (fun x v hx hv0 hv ↦ P.ma_le_unitFn hx hv0 hv) ((P.ma_pos i).trans_le P.ma_le_abs_a_zero)
    (mul_nonneg (hφ _) (mul_nonneg (P.wt_nonneg i _) (abs_nonneg _)))
    (P.tendsto_weightFn_face hφc hφL) P.tendsto_unitFn_face

end LogTerm

end Laplace.Multi
