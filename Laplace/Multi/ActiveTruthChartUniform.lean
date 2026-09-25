/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ActiveTruthChartParam

/-!
# Uniformity in the parameter on compact sets

Astra round 12, item 1. Convergence along every moving parameter `σ(t) → σ₀` with a limit
continuous in `σ₀` gives convergence uniform in `σ` on a compact set
(`eventually_uniform_of_moving`): otherwise a sequence of escaping times and bad parameters has a
convergent parameter subsequence, and a parameter path interpolating it contradicts the moving
statement. Applied to the active-truth term: the limit `∫ φ dμ_σ` is continuous in `σ ≠ 0`
(`continuousOn_integral_activeTruthMeasure`, from the explicit coefficient formula
`integral_activeTruthMeasure_eq`), so for a compact set of nonzero parameters on which the branch
is admissible, the normalised term kernel converges uniformly in `σ`
(`tendsto_termKernel_activeTruth_uniform`). Uniform in `σ` for each fixed test function `φ`, not
over test functions.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal Matrix

namespace Laplace.Multi

/-- **From moving parameters to uniformity on compacts.** -/
theorem eventually_uniform_of_moving {C : Set ℝ} (hC : IsCompact C) {F : ℝ → ℝ → ℝ} {L : ℝ → ℝ}
    (hL : ContinuousOn L C)
    (hmove : ∀ σ₀ ∈ C, ∀ σ : ℝ → ℝ, (∀ t, σ t ∈ C) → Tendsto σ atTop (𝓝 σ₀) →
      Tendsto (fun t ↦ F t (σ t)) atTop (𝓝 (L σ₀)))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ t in atTop, ∀ σ ∈ C, |F t σ - L σ| < ε := by
  classical
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq : ∀ a : ℝ, ∃ t, a ≤ t ∧ ∃ σ, σ ∈ C ∧ ε ≤ |F t σ - L σ| := by
    intro a
    obtain ⟨t, ht, h⟩ := Filter.frequently_atTop.mp hcon a
    push Not at h
    obtain ⟨σ, hσ, h⟩ := h
    exact ⟨t, ht, σ, hσ, h⟩
  choose! T hT using hfreq
  choose! S hS using fun a ↦ (hT a).2
  -- strictly increasing times
  let arg : ℕ → ℝ := fun n ↦ Nat.rec (motive := fun _ ↦ ℝ) 0 (fun _ prev ↦ T prev + 1) n
  have harg : ∀ n, arg (n + 1) = T (arg n) + 1 := fun n ↦ rfl
  let tn : ℕ → ℝ := fun n ↦ T (arg n)
  have htn_succ : ∀ n, tn n + 1 ≤ tn (n + 1) := fun n ↦ by
    change T (arg n) + 1 ≤ T (arg (n + 1))
    rw [harg]
    exact (hT _).1
  have htn_mono : StrictMono tn := strictMono_nat_of_lt_succ fun n ↦ by linarith [htn_succ n]
  have htn_ge : ∀ n : ℕ, (n : ℝ) ≤ tn n := by
    intro n
    induction n with
    | zero =>
      change ((0 : ℕ) : ℝ) ≤ T (arg 0)
      rw [Nat.cast_zero]
      exact (hT 0).1
    | succ n ih =>
      push_cast
      linarith [htn_succ n]
  have htn_top : Tendsto tn atTop atTop :=
    tendsto_atTop_mono htn_ge tendsto_natCast_atTop_atTop
  -- a convergent subsequence of the bad parameters
  obtain ⟨σ₀, hσ₀C, φ, hφ, hlim⟩ := hC.tendsto_subseq (x := fun n ↦ S (arg n))
    fun n ↦ (hS (arg n)).1
  have hinj : Function.Injective fun k ↦ tn (φ k) := (htn_mono.comp hφ).injective
  -- the interpolating path
  let σpath : ℝ → ℝ := fun t ↦
    if h : ∃ k, tn (φ k) = t then S (arg (φ (Nat.find h))) else σ₀
  have hpathC : ∀ t, σpath t ∈ C := fun t ↦ by
    change (if h : ∃ k, tn (φ k) = t then S (arg (φ (Nat.find h))) else σ₀) ∈ C
    split_ifs
    · exact (hS _).1
    · exact hσ₀C
  have hpath_at : ∀ k, σpath (tn (φ k)) = S (arg (φ k)) := fun k ↦ by
    have hk : ∃ k', tn (φ k') = tn (φ k) := ⟨k, rfl⟩
    change (if h : ∃ k', tn (φ k') = tn (φ k) then S (arg (φ (Nat.find h))) else σ₀) =
      S (arg (φ k))
    rw [dif_pos hk]
    congr 3
    exact hinj (Nat.find_spec hk)
  have hpath : Tendsto σpath atTop (𝓝 σ₀) := by
    rw [tendsto_def]
    intro U hU
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hlim.eventually hU)
    refine Filter.eventually_atTop.mpr ⟨tn (φ K) + 1, fun t ht ↦ ?_⟩
    change (if h : ∃ k, tn (φ k) = t then S (arg (φ (Nat.find h))) else σ₀) ∈ U
    split_ifs with h
    · have hspec := Nat.find_spec h
      have hK' : K ≤ Nat.find h := by
        by_contra hlt
        push Not at hlt
        have := htn_mono (hφ hlt)
        rw [hspec] at this
        linarith
      exact hK _ hK'
    · exact mem_of_mem_nhds hU
  -- the moving statement along the path, at the escaping times
  have hF := (hmove σ₀ hσ₀C σpath hpathC hpath).comp (htn_top.comp hφ.tendsto_atTop)
  have hLlim : Tendsto (fun k ↦ L (S (arg (φ k)))) atTop (𝓝 (L σ₀)) :=
    (hL σ₀ hσ₀C).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun k ↦ (hS _).1⟩)
  have hdiff : Tendsto (fun k ↦ F (tn (φ k)) (S (arg (φ k))) - L (S (arg (φ k)))) atTop
      (𝓝 (L σ₀ - L σ₀)) := by
    refine (hF.congr fun k ↦ ?_).sub hLlim
    simp only [Function.comp]
    rw [hpath_at]
  rw [sub_self] at hdiff
  have hev := hdiff.eventually (Metric.ball_mem_nhds 0 hε)
  obtain ⟨k, hk⟩ := hev.exists
  rw [dist_zero_right, Real.norm_eq_abs] at hk
  exact absurd (hS (arg (φ k))).2 (not_le.mpr hk)

namespace TruthChartsData.Phase

variable {m k : ℕ} {L' : Set (Fin (m + 1) → ℝ)} {T : (Fin (m + 1) → ℝ) → ℝ}
  {D : TruthChartsData m T L'}
  {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F) {i : D.ι} {ε : Fin m → Bool} {b : Bool}
  {σ γ β η : ℝ} {φ : (Fin (m + 1) → ℝ) → ℝ}

/-- The integral against the active-truth measure, explicitly. -/
theorem integral_activeTruthMeasure_eq (e : Fin k ⊕ Fin 2 ≃ Fin m) (hβ : 0 < β)
    (hφc : Continuous φ) (hφL : ∀ z, φ z ≠ 0 → z ∈ L') :
    ∫ x, φ x ∂(P.activeTruthMeasure i ε b σ γ β η e) =
      P.constA i σ * Gamma β * P.constB i σ ^ (-β) * (D.q i (D.k i) : ℝ) *
        D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) * P.faceConst i γ e *
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
  unfold activeTruthDensityFn unitFn
  ring

/-- The integral against the active-truth measure is continuous in `σ ≠ 0`. -/
theorem continuousOn_integral_activeTruthMeasure (e : Fin k ⊕ Fin 2 ≃ Fin m) (hβ : 0 < β)
    (hφc : Continuous φ) (hφL : ∀ z, φ z ≠ 0 → z ∈ L') :
    ContinuousOn (fun σ ↦ ∫ x, φ x ∂(P.activeTruthMeasure i ε b σ γ β η e)) {σ | σ ≠ 0} := by
  have e1 : (fun σ ↦ ∫ x, φ x ∂(P.activeTruthMeasure i ε b σ γ β η e)) = fun σ ↦
      P.constA i σ * Gamma β * P.constB i σ ^ (-β) * (D.q i (D.k i) : ℝ) *
        D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η)) * P.faceConst i γ e *
        ∫ u in Ioo (0 : ℝ) (D.ρ i), u ^ ((D.q i (D.k i) : ℝ) * η - 1) *
          (P.weightFn i φ ε b 0 u * P.unitFn i ε b 0 u ^ (-β)) := by
    funext σ
    exact P.integral_activeTruthMeasure_eq e hβ hφc hφL
  rw [e1]
  have habs : ContinuousOn (fun σ : ℝ ↦ |σ|) {σ | σ ≠ 0} := continuous_abs.continuousOn
  have hne : ∀ σ ∈ {σ : ℝ | σ ≠ 0}, |σ| ≠ 0 := fun σ hσ ↦ abs_ne_zero.mpr hσ
  have hA : ContinuousOn (fun σ ↦ P.constA i σ) {σ | σ ≠ 0} :=
    (habs.rpow_const fun σ hσ ↦ Or.inl (hne σ hσ)).div_const _
  have hB : ContinuousOn (fun σ ↦ P.constB i σ ^ (-β)) {σ | σ ≠ 0} :=
    (habs.rpow_const fun σ hσ ↦ Or.inl (hne σ hσ)).rpow_const fun σ hσ ↦
      Or.inl (Real.rpow_pos_of_pos (abs_pos.mpr hσ) _).ne'
  have hD : ContinuousOn (fun σ ↦ D.constD i σ ^ (-((D.q i (D.k i) : ℝ) * η))) {σ | σ ≠ 0} :=
    (habs.rpow_const fun σ hσ ↦ Or.inl (hne σ hσ)).rpow_const fun σ hσ ↦
      Or.inl (Real.rpow_pos_of_pos (abs_pos.mpr hσ) _).ne'
  exact (((((hA.mul continuousOn_const).mul hB).mul continuousOn_const).mul hD).mul
    continuousOn_const).mul continuousOn_const

open scoped Classical in
/-- **Uniformity in the parameter**: on a compact set of nonzero parameters on which the branch
is admissible, the normalised active-truth term kernel converges uniformly in `σ`. -/
theorem tendsto_termKernel_activeTruth_uniform (e : Fin k ⊕ Fin 2 ≃ Fin m) {C : Set ℝ}
    (hC : IsCompact C) (hC0 : ∀ σ ∈ C, σ ≠ 0) (hγ : 0 < γ)
    {p : TruthChartsData.Phase.TermIdx D} (hadm : ∀ σ ∈ C, D.admissible p.1 p.2.1 p.2.2 σ)
    (hβ : 0 < β) (hη : 0 < η) (hδ : 0 ≤ P.phaseExp p.1 γ) (hκ : ∀ j, 0 < P.kappa p.1 j)
    (hΔ : (transMat (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e)).det ≠ 0)
    (hc₀ : fibreCoef (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e) 0 ≠ 0 ∨
      fibreA (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e) (P.phaseExp p.1 γ) γ 0 ≠ 0)
    (hc₁ : fibreCoef (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e) 1 ≠ 0 ∨
      fibreA (P.kappa p.1 ∘ e) (D.Qexp p.1 ∘ e) (P.phaseExp p.1 γ) γ 1 ≠ 0)
    (hr : ∀ j, P.rExp p.1 (e j) + 1 = β * P.kappa p.1 (e j) - η * D.Qexp p.1 (e j))
    (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ)
    (hφL : ∀ z, φ z ≠ 0 → z ∈ L') {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ t in atTop, ∀ σ ∈ C,
      |t ^ (γ * P.pExp p.1 + (β * P.phaseExp p.1 γ - η * γ)) / log t ^ k *
          P.termKernel φ σ γ p t -
        ∫ x, φ x ∂(P.activeTruthMeasure p.1 p.2.1 p.2.2 σ γ β η e)| < ε' := by
  refine eventually_uniform_of_moving hC
    (F := fun t σ ↦ t ^ (γ * P.pExp p.1 + (β * P.phaseExp p.1 γ - η * γ)) / log t ^ k *
      P.termKernel φ σ γ p t)
    (L := fun σ ↦ ∫ x, φ x ∂(P.activeTruthMeasure p.1 p.2.1 p.2.2 σ γ β η e))
    ((P.continuousOn_integral_activeTruthMeasure e hβ hφc hφL).mono fun σ hσ ↦ hC0 σ hσ)
    (fun σ₀ hσ₀ σ _ hσ ↦ ?_) hε'
  exact P.tendsto_termKernel_activeTruth_param e hσ (hC0 σ₀ hσ₀) hγ (hadm σ₀ hσ₀) hβ hη hδ hκ hΔ
    hc₀ hc₁ hr hφc hφ hMφ hφL

end TruthChartsData.Phase

end Laplace.Multi
