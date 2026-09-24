/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.WallModelKernel
import Laplace.Multi.DominantScale

/-!
# The dominant-scale certificate of a wall model kernel

For one term of `fibreKernel_eq_sum_modelKernel` — a chart with phase data, an orthant `ε`, an
admissible branch `b` — a feasible scale `α` of the constrained LP yields a `DominantScaleHyp`
(`wallDominantScaleHyp`), hence the asymptotic `t^λ K_{ε,b}(t) → A ∫ w₀ e^{-Φ₀}` of that model
kernel (`tendsto_modelKernelOf`). The weight and unit converge along the rescaling because the
branch point converges to the limiting branch point `(ε·facePt(u), ± limitCut(u))`
(`tendsto_bridgePt`), which lies in the open chart ball for `u` in the limiting domain
(`limitBranchPt_mem_ball`); the chart-domain indicator is eventually `1` where `φ` is nonzero
because the branch point solves the truth equation (`truthMono_bridgePt`) and the truth fibre
where `φ ≠ 0` eventually lies in `L'` (hypothesis `hLφ`, which the slab of the fibre identity
provides). The remaining hypothesis is the integrability of the limiting profile.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

/-! ### The face point and the limiting cutoff -/

/-- The limiting unscaled point of the rescaling `x = t^{-α} u`: the coordinates with `α_j > 0`
go to `0`. -/
noncomputable def facePt {ι : Type*} (α u : ι → ℝ) : ι → ℝ := fun j ↦ if α j = 0 then u j else 0

/-- The limiting cutoff variable: `D ∏ u^{-Q/q}` when the truth constraint is tied, else `0`. -/
noncomputable def limitCut {ι : Type*} [Fintype ι] (D γ q : ℝ) (Q α : ι → ℝ) (u : ι → ℝ) : ℝ :=
  if ∑ j, Q j * α j = γ then D * ∏ j, u j ^ (-(Q j / q)) else 0

theorem tendsto_rescale {ι : Type*} {α : ι → ℝ} (hα : ∀ j, 0 ≤ α j) (u : ι → ℝ) :
    Tendsto (fun t : ℝ ↦ rescale t α u) atTop (𝓝 (facePt α u)) := by
  refine tendsto_pi_nhds.mpr fun j ↦ ?_
  unfold rescale facePt
  by_cases h0 : α j = 0
  · simp only [h0, neg_zero, Real.rpow_zero, one_mul, if_true]
    exact tendsto_const_nhds
  · simp only [h0, if_false]
    have hpos : 0 < α j := lt_of_le_of_ne (hα j) (Ne.symm h0)
    simpa using (tendsto_rpow_neg_atTop hpos).mul_const (u j)

theorem tendsto_rescaledCut {ι : Type*} [Fintype ι] {D γ q : ℝ} {Q α : ι → ℝ} (hq : 0 < q)
    (htruth : ∑ j, Q j * α j ≤ γ) (u : ι → ℝ) :
    Tendsto (fun t : ℝ ↦ rescaledCut D γ q Q α t u) atTop (𝓝 (limitCut D γ q Q α u)) := by
  unfold rescaledCut limitCut
  by_cases htied : ∑ j, Q j * α j = γ
  · rw [if_pos htied]
    simp only [htied, sub_self, zero_div, neg_zero, Real.rpow_zero, mul_one]
    exact tendsto_const_nhds
  · rw [if_neg htied]
    have hlt := lt_of_le_of_ne htruth htied
    simpa using ((tendsto_rpow_truth hq hlt).const_mul D).mul_const (∏ j, u j ^ (-(Q j / q)))

theorem continuous_orth {ι : Type*} (ε : ι → Bool) : Continuous (orth ε) :=
  continuous_pi fun j ↦ continuous_const.mul (continuous_apply j)

variable {m : ℕ} {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}

namespace WallChartsData

variable (D : WallChartsData m ℓ L')

/-- The limiting branch point of the rescaling. -/
noncomputable def limitBranchPt (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ : ℝ)
    (α u : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  D.bridgePt i ε b (facePt α u) (limitCut (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α u)

theorem tendsto_bridgePt (i : D.ι) (ε : Fin m → Bool) (b : Bool) {σ γ : ℝ} {α : Fin m → ℝ}
    (hα : ∀ j, 0 ≤ α j) (htruth : ∑ j, D.Qexp i j * α j ≤ γ) (u : Fin m → ℝ) :
    Tendsto (fun t : ℝ ↦ D.bridgePt i ε b (rescale t α u)
        (rescaledCut (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α t u)) atTop
      (𝓝 (D.limitBranchPt i ε b σ γ α u)) := by
  unfold limitBranchPt WallChartsData.bridgePt
  exact Tendsto.finInsertNth (D.k i)
    ((tendsto_rescaledCut (Nat.cast_pos.mpr (D.q_pos i)) htruth u).const_mul (bsign b))
    (((continuous_orth ε).tendsto _).comp (tendsto_rescale hα u))

theorem limitBranchPt_mem_ball (i : D.ι) (ε : Fin m → Bool) (b : Bool) {σ γ : ℝ}
    {α u : Fin m → ℝ}
    (hu : u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α) :
    D.limitBranchPt i ε b σ γ α u ∈ Metric.ball (0 : Fin (m + 1) → ℝ) (D.ρ i) := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff (D.ρ_pos i), Fin.forall_iff_succAbove (D.k i)]
  unfold limitBranchPt WallChartsData.bridgePt
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Real.norm_eq_abs, abs_mul,
    abs_bsign, one_mul, abs_orth]
  refine ⟨?_, fun j ↦ ?_⟩
  · unfold limitCut
    split_ifs with htied
    · have hD : 0 ≤ D.constD i σ := rpow_nonneg (abs_nonneg σ) _
      rw [abs_of_nonneg (mul_nonneg hD
        (Finset.prod_nonneg fun j _ ↦ rpow_nonneg (limitDomain_pos hu j).le _))]
      exact hu.2 htied
    · rw [abs_zero]
      exact D.ρ_pos i
  · unfold facePt
    have hj := Set.mem_univ_pi.mp hu.1 j
    split_ifs with h0
    · rw [if_pos h0] at hj
      rw [abs_of_pos hj.1]
      exact hj.2
    · rw [abs_zero]
      exact D.ρ_pos i

/-- The branch point of an admissible branch solves the truth equation. -/
theorem truthMono_bridgePt (i : D.ι) (hS : |D.S i| = 1) (ε : Fin m → Bool) (b : Bool)
    {σ γ t : ℝ} (ht : 0 < t) {x : Fin m → ℝ} (hx : ∀ j, 0 < x j) (hadm : D.admissible i ε b σ) :
    truthMono (D.S i) (D.q i) (D.bridgePt i ε b x
        (solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x)) (D.q i (D.k i))
          (σ * t ^ (-γ)))) = σ * t ^ (-γ) := by
  unfold WallChartsData.bridgePt
  rw [truthMono_insertNth]
  have hc : solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε x) ≠ 0 := by
    rw [D.solvedCoeff_orth]
    refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun j _ ↦ pow_ne_zero _ (hx j).ne')
    rw [← abs_ne_zero, D.abs_orthSign i hS]
    exact one_ne_zero
  cases b
  · simp only [bsign, Bool.false_eq_true, if_false, neg_one_mul]
    have hadm' : 0 < D.orthSign i ε * (-1) ^ D.q i (D.k i) * σ := by
      simpa [admissible] using hadm
    exact solvedCoord_neg_spec hc (D.q_pos i) ((D.admissible_iff_pos i ε ht hx _).mpr hadm')
  · simp only [bsign, if_true, one_mul]
    have hadm' : 0 < D.orthSign i ε * 1 * σ := by
      simpa [admissible] using hadm
    have := (D.admissible_iff_pos i ε (σ := σ) (γ := γ) ht hx 1).mpr hadm'
    rw [mul_one] at this
    exact solvedCoord_pos_spec hc (D.q_pos i) this

end WallChartsData

namespace WallChartsData.Phase

variable {D : WallChartsData m ℓ L'} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)
variable {i : D.ι} {φ : (Fin (m + 1) → ℝ) → ℝ} {ε : Fin m → Bool} {b : Bool} {σ γ : ℝ}
  {α : Fin m → ℝ}

/-- The limiting weight `φ(rep u∞) wt(u∞) |b(u∞)|` at the limiting branch point. -/
noncomputable def limitWeight (i : D.ι) (φ : (Fin (m + 1) → ℝ) → ℝ) (ε : Fin m → Bool) (b : Bool)
    (σ γ : ℝ) (α u : Fin m → ℝ) : ℝ :=
  φ (D.rep i (D.limitBranchPt i ε b σ γ α u)) *
    (P.wt i (D.limitBranchPt i ε b σ γ α u) * |P.b i (D.limitBranchPt i ε b σ γ α u)|)

/-- The limiting unit `|a(u∞)|` at the limiting branch point. -/
noncomputable def limitUnit (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ : ℝ) (α u : Fin m → ℝ) :
    ℝ :=
  |P.a i (D.limitBranchPt i ε b σ γ α u)|

theorem weightFn_ne_zero_mem {x : Fin m → ℝ} {v : ℝ} (h : P.weightFn i φ ε b x v ≠ 0) :
    D.bridgePt i ε b x v ∈ D.dom i := by
  unfold weightFn at h
  by_contra hm
  exact h (Set.indicator_of_notMem hm _)

theorem Mb_nonneg : 0 ≤ P.Mb i :=
  (P.mb_pos i).le.trans ((P.b_bounds i 0 (Metric.mem_closedBall_self (D.ρ_pos i).le)).1.trans
    (P.b_bounds i 0 (Metric.mem_closedBall_self (D.ρ_pos i).le)).2)

theorem abs_weightFn_le (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ) (x : Fin m → ℝ)
    (v : ℝ) : |P.weightFn i φ ε b x v| ≤ Mφ * P.Mb i := by
  have hMφ0 : 0 ≤ Mφ := (hφ 0).trans (hMφ 0)
  unfold weightFn
  by_cases hm : D.bridgePt i ε b x v ∈ D.dom i
  · rw [Set.indicator_of_mem hm]
    have hcb : D.bridgePt i ε b x v ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i) := by
      rw [D.dom_eq] at hm
      exact hm.1
    have hnn : 0 ≤ P.wt i (D.bridgePt i ε b x v) * |P.b i (D.bridgePt i ε b x v)| :=
      mul_nonneg (P.wt_nonneg i _) (abs_nonneg _)
    rw [abs_of_nonneg (mul_nonneg (hφ _) hnn)]
    calc φ (D.rep i (D.bridgePt i ε b x v)) *
          (P.wt i (D.bridgePt i ε b x v) * |P.b i (D.bridgePt i ε b x v)|)
        ≤ Mφ * (1 * P.Mb i) :=
          mul_le_mul (hMφ _) (mul_le_mul (P.wt_le_one i _) (P.b_bounds i _ hcb).2 (abs_nonneg _)
            zero_le_one) hnn hMφ0
      _ = Mφ * P.Mb i := by ring
  · rw [Set.indicator_of_notMem hm, abs_zero]
    exact mul_nonneg hMφ0 P.Mb_nonneg

/-- **The weight converges along the rescaling** to the limiting weight, for `u` in the limiting
domain: the branch point converges into the chart ball, and the chart-domain indicator is
eventually `1` wherever `φ` is nonzero. -/
theorem tendsto_weightFn (hS : |D.S i| = 1) (hadm : D.admissible i ε b σ)
    (htruth : ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
      D.rep i u ℓ = truthMono (D.S i) (D.q i) u)
    (hLφ : ∀ᶠ t in atTop, ∀ z, z ℓ = σ * t ^ (-γ) → φ z ≠ 0 → z ∈ L')
    (hφc : Continuous φ) (hα : ∀ j, 0 ≤ α j) (htr : ∑ j, D.Qexp i j * α j ≤ γ) {u : Fin m → ℝ}
    (hu : u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α) :
    Tendsto (fun t ↦ P.weightFn i φ ε b (rescale t α u)
        (rescaledCut (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α t u)) atTop
      (𝓝 (P.limitWeight i φ ε b σ γ α u)) := by
  have hu' : ∀ j, 0 < u j := limitDomain_pos hu
  have hpt := D.tendsto_bridgePt i ε b (σ := σ) hα htr u
  have hg : Continuous fun z ↦ φ (D.rep i z) * (P.wt i z * |P.b i z|) :=
    (hφc.comp (D.rep_cont i)).mul ((P.wt_cont i).mul (continuous_abs.comp (P.b_cont i)))
  have hlim : Tendsto (fun t ↦ (fun z ↦ φ (D.rep i z) * (P.wt i z * |P.b i z|))
      (D.bridgePt i ε b (rescale t α u)
        (rescaledCut (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α t u))) atTop
      (𝓝 (P.limitWeight i φ ε b σ γ α u)) := (hg.tendsto _).comp hpt
  refine hlim.congr' ?_
  have hball := hpt.eventually_mem (Metric.isOpen_ball.mem_nhds
    (D.limitBranchPt_mem_ball i ε b hu))
  filter_upwards [hball, hLφ, eventually_gt_atTop 0] with t hb hL ht
  have hx : ∀ j, 0 < rescale t α u j := rescale_pos ht α hu'
  have hVeq : rescaledCut (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α t u =
      solvedCoord (solvedCoeff (D.k i) (D.S i) (D.q i) (orth ε (rescale t α u)))
        (D.q i (D.k i)) (σ * t ^ (-γ)) := by
    rw [D.solvedCoord_orth_eq_cutVar i hS ε ht hx, cutVar_rescale ht hu']
  have hcb := Metric.ball_subset_closedBall hb
  unfold weightFn
  set ut := D.bridgePt i ε b (rescale t α u)
    (rescaledCut (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α t u) with hut
  by_cases hφ0 : φ (D.rep i ut) = 0
  · have hg0 : φ (D.rep i ut) * (P.wt i ut * |P.b i ut|) = 0 := by rw [hφ0, zero_mul]
    rw [hg0]
    exact ((Set.indicator_apply_eq_zero (s := D.dom i)
      (f := fun u ↦ φ (D.rep i u) * (P.wt i u * |P.b i u|)) (a := ut)).mpr fun _ ↦ hg0).symm
  · have hmem : ut ∈ D.dom i := by
      rw [D.dom_eq]
      refine ⟨hcb, hL _ ?_ hφ0⟩
      rw [htruth _ hcb, hut, hVeq]
      exact D.truthMono_bridgePt i hS ε b ht hx hadm
    rw [Set.indicator_of_mem hmem]

/-- **The dominant-scale certificate of a wall model kernel.** -/
theorem wallDominantScaleHyp (hS : |D.S i| = 1) (hσ : σ ≠ 0) (hadm : D.admissible i ε b σ)
    (htruth : ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
      D.rep i u ℓ = truthMono (D.S i) (D.q i) u)
    (hLφ : ∀ᶠ t in atTop, ∀ z, z ℓ = σ * t ^ (-γ) → φ z ≠ 0 → z ∈ L')
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
  W_lim := fun u hu ↦ P.tendsto_weightFn hS hadm htruth hLφ hφc hfeas.1 hfeas.2.1 hu
  a_lim := fun u _ ↦ ((continuous_abs.comp (P.a_cont i)).tendsto _).comp
    (D.tendsto_bridgePt i ε b hfeas.1 hfeas.2.1 u)
  int := hint
  Φint := hΦint

/-- **The asymptotic of a wall model kernel**: `t^λ K_{ε,b}(t) → A ∫ w₀ e^{-Φ₀}` with
`λ = γp + ∑ (r_j + 1) α_j` the LP value at the certified scale. -/
theorem tendsto_modelKernelOf (hS : |D.S i| = 1) (hσ : σ ≠ 0) (hadm : D.admissible i ε b σ)
    (htruth : ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
      D.rep i u ℓ = truthMono (D.S i) (D.q i) u)
    (hLφ : ∀ᶠ t in atTop, ∀ z, z ℓ = σ * t ^ (-γ) → φ z ≠ 0 → z ∈ L')
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
    Tendsto (fun t ↦ t ^ lpExponent γ (P.pExp i) (fun j ↦ P.rExp i j + 1) α *
        P.modelKernelOf i φ ε b t γ σ) atTop
      (𝓝 (P.constA i σ * ∫ u, dsWeight₀ (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i)
          (P.rExp i) α (P.limitWeight i φ ε b σ γ α) u *
        exp (-dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
          (D.Qexp i) (P.kappa i) α (P.limitUnit i ε b σ γ α) u))) :=
  (P.wallDominantScaleHyp hS hσ hadm htruth hLφ hφc hφ hMφ hfeas hint hΦint).tendsto_modelKernel
    (P.constA i σ) (P.pExp i)

end WallChartsData.Phase

end Laplace.Multi
