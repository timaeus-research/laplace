/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.WallFibreExpectation
import Laplace.Multi.LimitingMeasure

/-!
# Support-free observables: the interior form of the term chain

Astra round 17, item 1 (second stage): the term theorems take observables `φ` supported in the
region `L'` of the chart data (`hφL : ∀ z, φ z ≠ 0 → z ∈ L'`), and that hypothesis enters the
chain at exactly one place — `tendsto_weightFn`, where it shows that the moving branch point
lies in the chart domain `dom_i = closedBall ∩ rep_i⁻¹ L'` whenever `φ` is nonzero there. A
globally continuous observable supported in a closed region vanishes on the region's boundary,
which is where the boundary regimes put their mass; the support hypothesis is therefore the
wrong interface for them.

This file replaces it by the geometric hypothesis Astra asked for: **at every point of the
limiting domain, the limiting face point lies in the interior of `L'`, or the observable
vanishes on a neighbourhood of it** (`D.faceMap i ε b σ γ α u ∈ interior L' ∨ φ =ᶠ[𝓝 (face)] 0`).
In the first case the moving branch point is eventually in the region by convergence alone; in
the second the moving weight and the limiting weight both vanish. The second alternative is what
lets a chart ball larger than the region be used (the limiting domain is cut by the chart radius
`ρ`, the region by its own radius, and the face points in between carry no weight once the
observable is supported inside the region's radius). The whole chain then goes through with an
arbitrary bounded continuous nonnegative `φ`:
`tendsto_weightFn_of_interior`, `wallDominantScaleHyp_of_interior`,
`tendsto_modelKernelOf_of_interior`, `tendsto_term_of_interior`,
`tendsto_termKernel_of_interior`, `tendsto_fibre_expectation_of_interior`. The restriction to
`L'` is then internal to the kernel (the chart-domain indicator), never a property of the
observable — the interface under which a boundary trace such as `ψ(σ/u, 0)` is visible to the
certificate route.
-/

open Filter MeasureTheory Set Topology Real

namespace Laplace.Multi

variable {m : ℕ} {L' : Set (Fin (m + 1) → ℝ)} {T : (Fin (m + 1) → ℝ) → ℝ}
  {D : TruthChartsData m T L'} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)

namespace TruthChartsData.Phase

variable {i : D.ι} {φ : (Fin (m + 1) → ℝ) → ℝ} {ε : Fin m → Bool} {b : Bool} {σ γ : ℝ}
  {α : Fin m → ℝ}

/-- **The weight converges along the rescaling, interior form**: no support hypothesis on `φ`;
the limiting face point lies in the interior of the region. -/
theorem tendsto_weightFn_of_interior
    (hface : ∀ u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α,
      D.rep i (D.limitBranchPt i ε b σ γ α u) ∈ interior L' ∨
        ∀ᶠ z in 𝓝 (D.rep i (D.limitBranchPt i ε b σ γ α u)), φ z = 0)
    (hφc : Continuous φ) (hα : ∀ j, 0 ≤ α j) (htr : ∑ j, D.Qexp i j * α j ≤ γ) {u : Fin m → ℝ}
    (hu : u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α) :
    Tendsto (fun t ↦ P.weightFn i φ ε b (rescale t α u)
        (rescaledCut (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α t u)) atTop
      (𝓝 (P.limitWeight i φ ε b σ γ α u)) := by
  have hpt := D.tendsto_bridgePt i ε b (σ := σ) hα htr u
  have hg : Continuous fun z ↦ φ (D.rep i z) * (P.wt i z * |P.b i z|) :=
    (hφc.comp (D.rep_cont i)).mul ((P.wt_cont i).mul (continuous_abs.comp (P.b_cont i)))
  have hlim : Tendsto (fun t ↦ (fun z ↦ φ (D.rep i z) * (P.wt i z * |P.b i z|))
      (D.bridgePt i ε b (rescale t α u)
        (rescaledCut (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α t u))) atTop
      (𝓝 (P.limitWeight i φ ε b σ γ α u)) := (hg.tendsto _).comp hpt
  have hball := hpt.eventually_mem (Metric.isOpen_ball.mem_nhds
    (D.limitBranchPt_mem_ball i ε b hu))
  rcases hface u hu with hin | hvan
  · refine hlim.congr' ?_
    have hreg := (((D.rep_cont i).tendsto _).comp hpt).eventually_mem
      (isOpen_interior.mem_nhds hin)
    filter_upwards [hball, hreg] with t hb hr
    have hmem : D.bridgePt i ε b (rescale t α u)
        (rescaledCut (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α t u) ∈ D.dom i := by
      rw [D.dom_eq]
      exact ⟨Metric.ball_subset_closedBall hb, Set.mem_preimage.mpr (interior_subset hr)⟩
    unfold weightFn
    rw [Set.indicator_of_mem hmem]
  · -- the observable vanishes near the face point: both weights are eventually `0`
    have h0 : P.limitWeight i φ ε b σ γ α u = 0 := by
      unfold limitWeight
      rw [hvan.self_of_nhds, zero_mul]
    rw [h0]
    have hev := (((D.rep_cont i).tendsto _).comp hpt).eventually hvan
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with t ht
    unfold weightFn
    refine ((Set.indicator_apply_eq_zero (s := D.dom i)
      (f := fun u ↦ φ (D.rep i u) * (P.wt i u * |P.b i u|))).mpr fun _ ↦ ?_).symm
    rw [show φ (D.rep i (D.bridgePt i ε b (rescale t α u)
      (rescaledCut (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α t u))) = 0 from ht, zero_mul]

/-- **The dominant-scale certificate, interior form.** -/
theorem wallDominantScaleHyp_of_interior (hσ : σ ≠ 0)
    (hface : ∀ u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α,
      D.rep i (D.limitBranchPt i ε b σ γ α u) ∈ interior L' ∨
        ∀ᶠ z in 𝓝 (D.rep i (D.limitBranchPt i ε b σ γ α u)), φ z = 0)
    (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ)
    (hfeas : ConstrainedFeasible (D.Qexp i) (P.kappa i) γ (P.phaseExp i γ) α)
    (hint : Integrable fun u ↦
      dsEnvelope (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) (P.rExp i) α (Mφ * P.Mb i) u *
        exp (-(P.ma i / P.Ma i * dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i))
          (P.phaseExp i γ) (D.Qexp i) (P.kappa i) α (P.limitUnit i ε b σ γ α) u)))
    (hΦint : Integrable fun u ↦
      dsEnvelope (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) (P.rExp i) α (Mφ * P.Mb i) u *
        (dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
            (D.Qexp i) (P.kappa i) α (P.limitUnit i ε b σ γ α) u *
          exp (-(P.ma i / P.Ma i * dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ
            (D.q i (D.k i)) (P.phaseExp i γ) (D.Qexp i) (P.kappa i) α
              (P.limitUnit i ε b σ γ α) u)))) :
    DominantScaleHyp (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
      (D.Qexp i) (P.kappa i) (P.rExp i) α (P.weightFn i φ ε b) (P.unitFn i ε b)
      (P.limitWeight i φ ε b σ γ α) (P.limitUnit i ε b σ γ α) (Mφ * P.Mb i) (P.ma i)
      (P.Ma i) where
  hρ := D.ρ_pos i
  hq := Nat.cast_pos.mpr (D.q_pos i)
  hB := rpow_pos_of_pos (abs_pos.mpr hσ) _
  hamin := P.ma_pos i
  hle := (P.a_bounds i 0 (Metric.mem_closedBall_self (D.ρ_pos i).le)).1.trans
    (P.a_bounds i 0 (Metric.mem_closedBall_self (D.ρ_pos i).le)).2
  feasible := hfeas
  W_meas := P.measurable_weightFn hφc.measurable
  a_meas := P.measurable_unitFn
  W_bd := P.abs_weightFn_le hφ hMφ
  a_bounds := fun x v h ↦ by
    have hm := P.weightFn_ne_zero_mem h
    rw [D.dom_eq] at hm
    exact P.a_bounds i _ hm.1
  a₀_bounds := fun u hu ↦
    P.a_bounds i _ (Metric.ball_subset_closedBall (D.limitBranchPt_mem_ball i ε b hu))
  W_lim := fun u hu ↦ P.tendsto_weightFn_of_interior hface hφc hfeas.1 hfeas.2.1 hu
  a_lim := fun u _ ↦ ((continuous_abs.comp (P.a_cont i)).tendsto _).comp
    (D.tendsto_bridgePt i ε b hfeas.1 hfeas.2.1 u)
  int := hint
  Φint := hΦint

/-- **The asymptotic of a wall model kernel, interior form.** -/
theorem tendsto_modelKernelOf_of_interior (hσ : σ ≠ 0)
    (hface : ∀ u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α,
      D.rep i (D.limitBranchPt i ε b σ γ α u) ∈ interior L' ∨
        ∀ᶠ z in 𝓝 (D.rep i (D.limitBranchPt i ε b σ γ α u)), φ z = 0)
    (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ)
    (hfeas : ConstrainedFeasible (D.Qexp i) (P.kappa i) γ (P.phaseExp i γ) α)
    (hprof : P.ProfileIntegrableOf i ε b σ γ α) :
    Tendsto (fun t ↦ t ^ lpExponent γ (P.pExp i) (fun j ↦ P.rExp i j + 1) α *
        P.modelKernelOf i φ ε b t γ σ) atTop (𝓝 (P.termConst i φ ε b σ γ α)) :=
  (P.wallDominantScaleHyp_of_interior hσ hface hφc hφ hMφ hfeas (hprof.int' _ _)
    (hprof.Φint' _ _)).tendsto_modelKernel (P.constA i σ) (P.pExp i)

end TruthChartsData.Phase

namespace TruthChartsData.Phase

variable {σ γ : ℝ}

/-- **The certified term kernels converge, interior form**: every admissible term with a
certified scale whose limiting face lies in the interior of the region. -/
theorem tendsto_termKernel_of_interior (hσ : σ ≠ 0)
    {φ : (Fin (m + 1) → ℝ) → ℝ} (hφc : Continuous φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ}
    (hMφ : ∀ z, φ z ≤ Mφ) {α : D.ι → (Fin m → Bool) → Bool → Fin m → ℝ}
    (hface : ∀ i ε b, D.admissible i ε b σ →
      ∀ u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) (α i ε b),
        D.faceMap i ε b σ γ (α i ε b) u ∈ interior L' ∨
          ∀ᶠ z in 𝓝 (D.faceMap i ε b σ γ (α i ε b) u), φ z = 0)
    (hfeas : ∀ i ε b, D.admissible i ε b σ →
      ConstrainedFeasible (D.Qexp i) (P.kappa i) γ (P.phaseExp i γ) (α i ε b))
    (hprof : ∀ i ε b, D.admissible i ε b σ → P.ProfileIntegrableOf i ε b σ γ (α i ε b))
    (p : TermIdx D) :
    Tendsto (fun t ↦ t ^ P.termLam γ α p * P.termKernel φ σ γ p t) atTop
      (𝓝 (P.termConst' φ σ γ α p)) := by
  classical
  unfold termKernel termConst'
  by_cases hadm : D.admissible p.1 p.2.1 p.2.2 σ
  · simp only [if_pos hadm]
    exact P.tendsto_modelKernelOf_of_interior hσ (hface _ _ _ hadm) hφc hφ hMφ
      (hfeas _ _ _ hadm) (hprof _ _ _ hadm)
  · simp only [if_neg hadm, mul_zero]
    exact tendsto_const_nhds

/-- **The expectation along the truth fibre, interior form**: bounded continuous nonnegative
observables with no support condition, the limiting faces of the certified terms in the interior
of the region. -/
theorem tendsto_fibre_expectation_of_interior (hS : ∀ i, |D.S i| = 1) (hF : ∀ z, 0 ≤ F z)
    (hFm : Measurable F) (hσ : σ ≠ 0) {ψ χ : (Fin (m + 1) → ℝ) → ℝ} (hψc : Continuous ψ)
    (hψ : ∀ z, 0 ≤ ψ z) {Mψ : ℝ} (hMψ : ∀ z, ψ z ≤ Mψ) (hχc : Continuous χ)
    (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ} (hMχ : ∀ z, χ z ≤ Mχ)
    {α : D.ι → (Fin m → Bool) → Bool → Fin m → ℝ}
    (hfaceψ : ∀ i ε b, D.admissible i ε b σ →
      ∀ u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) (α i ε b),
        D.faceMap i ε b σ γ (α i ε b) u ∈ interior L' ∨
          ∀ᶠ z in 𝓝 (D.faceMap i ε b σ γ (α i ε b) u), ψ z = 0)
    (hfaceχ : ∀ i ε b, D.admissible i ε b σ →
      ∀ u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) (α i ε b),
        D.faceMap i ε b σ γ (α i ε b) u ∈ interior L' ∨
          ∀ᶠ z in 𝓝 (D.faceMap i ε b σ γ (α i ε b) u), χ z = 0)
    (hfeas : ∀ i ε b, D.admissible i ε b σ →
      ConstrainedFeasible (D.Qexp i) (P.kappa i) γ (P.phaseExp i γ) (α i ε b))
    (hprof : ∀ i ε b, D.admissible i ε b σ → P.ProfileIntegrableOf i ε b σ γ (α i ε b))
    {lam₀ : ℝ} (hmin : ∀ p : TermIdx D, lam₀ ≤ P.termLam γ α p)
    (hpos : (∑ p : TermIdx D, if P.termLam γ α p = lam₀ then P.termConst' χ σ γ α p else 0) ≠ 0) :
    Tendsto (fun t ↦
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * ψ z)) (σ * t ^ (-γ))).toReal /
        (D.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * F z)) * χ z)) (σ * t ^ (-γ))).toReal)
      atTop
      (𝓝 ((∑ p : TermIdx D, if P.termLam γ α p = lam₀ then P.termConst' ψ σ γ α p else 0) /
        ∑ p : TermIdx D, if P.termLam γ α p = lam₀ then P.termConst' χ σ γ α p else 0)) := by
  classical
  have hK := P.tendsto_termKernel_of_interior hσ hχc hχ hMχ hfaceχ hfeas hprof
  have hKψ := P.tendsto_termKernel_of_interior hσ hψc hψ hMψ hfaceψ hfeas hprof
  refine (tendsto_sum_ratio hmin hK hKψ hpos).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [P.totalKernel_toReal_eq_sum_terms hS hF hFm hψc.measurable hψ hMψ ht hσ,
    P.totalKernel_toReal_eq_sum_terms hS hF hFm hχc.measurable hχ hMχ ht hσ]

end TruthChartsData.Phase

end Laplace.Multi
