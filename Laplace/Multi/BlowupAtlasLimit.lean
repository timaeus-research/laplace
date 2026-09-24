/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BlowupAtlasRecord
import Laplace.Multi.BlowupSectorLimit

/-!
# The two-chart blow-up atlas through the analytic layer

The atlas of `BlowupAtlasRecord` (charts `A : (x, y) ↦ (x, xy)` and `B : (x, y) ↦ (xy, y)` for
`F = z₀² + z₁²`, truth `z₀`, over the unit box) along the fibre `z₀ = σ t^{-γ}`, `γ > 1/2`.

Chart `A` (solving for `x`): `q = (1, 0)`, `Q = 0`, `ν = 2`, `κ = 0`, `p = 1`, `r = 0`,
`δ = 1 − 2γ < 0`; the LP `α ≥ 0`, `0 ≤ γ`, `0 ≥ δ` has objective `γ + α`, minimised at
`α = 0` with value `λ_A = γ`; the phase constraint is slack, so the limiting profile is `0` and
the certificate is trivial. Chart `B` is the sector chart of `BlowupSectorLimit` with the new
weight `ω_B(xy, y) = h_B(x)`, `h_B(0) = 1`: `λ_B = 1/2 < γ`. So chart `A` is *subdominant*, only
the two admissible sign branches of chart `B` contribute, and the expectation along the fibre
converges to `ψ(0)/χ(0)` (`at_tendsto_fibre_expectation`) — the same answer as on the sector, now
from a genuine two-chart transport identity with a partition of unity.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi.BlowupAtlas

open Laplace.Multi.ToyWall Laplace.Multi.BlowupSector

variable (ε : Fin 1 → Bool) (b : Bool) (σ γ : ℝ)

/-! ### The constants of chart `A` -/

theorem atPhase_kF_zero : atPhase.kF iA = ![2, 0] := rfl
theorem atPhase_kF_one : atPhase.kF iB = ![0, 2] := rfl
theorem atPhase_hJ_zero : atPhase.hJ iA = ![1, 0] := rfl
theorem atPhase_hJ_one : atPhase.hJ iB = ![0, 1] := rfl
theorem atPhase_a_zero (u : Fin 2 → ℝ) : atPhase.a iA u = 1 + u 1 ^ 2 := rfl
theorem atPhase_a_one (u : Fin 2 → ℝ) : atPhase.a iB u = 1 + u 0 ^ 2 := rfl
theorem atPhase_b (i : atData.ι) (u : Fin 2 → ℝ) : atPhase.b i u = 1 := rfl
theorem atPhase_wt_zero (u : Fin 2 → ℝ) : atPhase.wt iA u = gA (u 1) * cutA u := rfl
theorem atPhase_wt_one (u : Fin 2 → ℝ) : atPhase.wt iB u = hB (u 0) * bsCut u := rfl
theorem atPhase_ma (i : atData.ι) : atPhase.ma i = 1 := rfl
theorem atPhase_Ma_one : atPhase.Ma iB = 5 := rfl

theorem atA_succAbove : (0 : Fin 2).succAbove (0 : Fin 1) = 1 := rfl

theorem atA_qk_real : (atData.q iA (atData.k iA) : ℝ) = 1 := by
  rw [atData_q_iA, atData_k_iA]; simp

theorem atA_Qexp (j : Fin 1) : atData.Qexp iA j = 0 := by
  unfold WallChartsData.Qexp
  rw [atData_q_iA, atData_k_iA, Fin.fin_one_eq_zero j, atA_succAbove]
  simp

theorem atA_nu : atPhase.nu iA = 2 := by
  unfold WallChartsData.Phase.nu
  rw [atPhase_kF_zero, atData_q_iA, atData_k_iA]
  simp

theorem atA_kappa (j : Fin 1) : atPhase.kappa iA j = 0 := by
  unfold WallChartsData.Phase.kappa
  rw [atPhase_kF_zero, atData_q_iA, atData_k_iA, Fin.fin_one_eq_zero j, atA_succAbove]
  simp

theorem atA_pExp : atPhase.pExp iA = 1 := by
  unfold WallChartsData.Phase.pExp
  rw [atPhase_hJ_zero, atData_q_iA, atData_k_iA]
  norm_num

theorem atA_rExp (j : Fin 1) : atPhase.rExp iA j = 0 := by
  unfold WallChartsData.Phase.rExp
  rw [atPhase_hJ_zero, atData_q_iA, atData_k_iA, Fin.fin_one_eq_zero j, atA_succAbove]
  norm_num

theorem atA_phaseExp : atPhase.phaseExp iA γ = 1 - 2 * γ := by
  unfold WallChartsData.Phase.phaseExp
  rw [atA_nu]
  ring

/-- The scale of chart `A`: `α = 0`. -/
def atAlphaA : Fin 1 → ℝ := fun _ ↦ 0

theorem atA_feasible (hγ : 1 / 2 < γ) :
    ConstrainedFeasible (atData.Qexp iA) (atPhase.kappa iA) γ
      (atPhase.phaseExp iA γ) atAlphaA := by
  refine ⟨fun _ ↦ le_rfl, ?_, ?_⟩
  · simp only [atA_Qexp, zero_mul, Finset.sum_const_zero]
    linarith
  · simp only [atA_kappa, zero_mul, Finset.sum_const_zero, atA_phaseExp]
    linarith

theorem atA_lpExponent :
    lpExponent γ (atPhase.pExp iA) (fun j ↦ atPhase.rExp iA j + 1) atAlphaA =
      γ := by
  unfold lpExponent
  simp only [Fin.sum_univ_one, atA_pExp, atA_rExp, atAlphaA]
  ring

theorem atA_limitDomain (hγ : 1 / 2 < γ) :
    limitDomain (atData.ρ iA) (atData.constD iA σ) γ (atData.q iA (atData.k iA))
        (atData.Qexp iA) atAlphaA = Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 4 := by
  ext u
  simp only [limitDomain, mem_inter_iff, Set.mem_univ_pi, mem_ofPred_eq, atA_Qexp, zero_mul,
    Finset.sum_const_zero, atAlphaA, if_true, atData_ρ_iA]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun h0 ↦ absurd h0 (by linarith)⟩⟩

theorem atA_dsProfile (hγ : 1 / 2 < γ) (u : Fin 1 → ℝ) :
    dsProfile (atData.ρ iA) (atPhase.constB iA σ) (atData.constD iA σ) γ
        (atData.q iA (atData.k iA)) (atPhase.phaseExp iA γ)
        (atData.Qexp iA) (atPhase.kappa iA) atAlphaA
        (atPhase.limitUnit iA ε b σ γ atAlphaA) u = 0 := by
  unfold dsProfile
  have hne : ∑ j, atPhase.kappa iA j * atAlphaA j ≠ atPhase.phaseExp iA γ := by
    simp only [atA_kappa, zero_mul, Finset.sum_const_zero, atA_phaseExp]
    linarith
  rw [if_neg hne, ite_self]

/-- The trivial certificate of chart `A`: the phase constraint is slack, the profile vanishes. -/
theorem atA_profile (hγ : 1 / 2 < γ) :
    atPhase.ProfileIntegrableOf iA ε b σ γ atAlphaA where
  int := by
    have key : (fun u : Fin 1 → ℝ ↦
        dsEnvelope (atData.ρ iA) (atData.constD iA σ) γ
            (atData.q iA (atData.k iA)) (atData.Qexp iA)
            (atPhase.rExp iA) atAlphaA 1 u *
          exp (-(atPhase.ma iA / atPhase.Ma iA *
            dsProfile (atData.ρ iA) (atPhase.constB iA σ)
              (atData.constD iA σ) γ (atData.q iA (atData.k iA))
              (atPhase.phaseExp iA γ) (atData.Qexp iA)
              (atPhase.kappa iA) atAlphaA
              (atPhase.limitUnit iA ε b σ γ atAlphaA) u))) =
        fun u ↦ (Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 4).indicator (fun _ ↦ (1 : ℝ)) u := by
      funext u
      rw [atA_dsProfile ε b σ γ hγ u, mul_zero, neg_zero, Real.exp_zero, mul_one]
      unfold dsEnvelope
      rw [atA_limitDomain σ γ hγ, one_mul]
      simp [atA_rExp]
    rw [key]
    refine (integrable_indicator_iff
      (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo)).mpr ?_
    refine integrableOn_const ?_
    rw [Real.volume_pi_Ioo]
    exact ENNReal.prod_ne_top fun _ _ ↦ ENNReal.ofReal_ne_top
  Φint := by
    have key : (fun u : Fin 1 → ℝ ↦
        dsEnvelope (atData.ρ iA) (atData.constD iA σ) γ
            (atData.q iA (atData.k iA)) (atData.Qexp iA)
            (atPhase.rExp iA) atAlphaA 1 u *
          (dsProfile (atData.ρ iA) (atPhase.constB iA σ)
              (atData.constD iA σ) γ (atData.q iA (atData.k iA))
              (atPhase.phaseExp iA γ) (atData.Qexp iA)
              (atPhase.kappa iA) atAlphaA
              (atPhase.limitUnit iA ε b σ γ atAlphaA) u *
            exp (-(atPhase.ma iA / atPhase.Ma iA *
              dsProfile (atData.ρ iA) (atPhase.constB iA σ)
                (atData.constD iA σ) γ (atData.q iA (atData.k iA))
                (atPhase.phaseExp iA γ) (atData.Qexp iA)
                (atPhase.kappa iA) atAlphaA
                (atPhase.limitUnit iA ε b σ γ atAlphaA) u)))) = fun _ ↦ 0 := by
      funext u
      rw [atA_dsProfile ε b σ γ hγ u, zero_mul, mul_zero]
    rw [key]
    exact integrable_zero _ _ _

/-! ### The constants of chart `B` -/

theorem atB_succAbove : (1 : Fin 2).succAbove (0 : Fin 1) = 0 := rfl

theorem atB_qk : atData.q iB (atData.k iB) = 1 := rfl

theorem atB_qk_real : (atData.q iB (atData.k iB) : ℝ) = 1 := by
  rw [atB_qk]; simp

theorem atB_Qexp (j : Fin 1) : atData.Qexp iB j = 1 := by
  unfold WallChartsData.Qexp
  rw [atData_q_iB, atData_k_iB, Fin.fin_one_eq_zero j, atB_succAbove]
  simp

theorem atB_nu : atPhase.nu iB = 2 := by
  unfold WallChartsData.Phase.nu
  rw [atPhase_kF_one, atData_q_iB, atData_k_iB]
  simp

theorem atB_kappa (j : Fin 1) : atPhase.kappa iB j = -2 := by
  unfold WallChartsData.Phase.kappa
  rw [atPhase_kF_one, atData_q_iB, atData_k_iB, Fin.fin_one_eq_zero j, atB_succAbove]
  simp

theorem atB_pExp : atPhase.pExp iB = 1 := by
  unfold WallChartsData.Phase.pExp
  rw [atPhase_hJ_one, atData_q_iB, atData_k_iB]
  norm_num

theorem atB_rExp (j : Fin 1) : atPhase.rExp iB j = -2 := by
  unfold WallChartsData.Phase.rExp
  rw [atPhase_hJ_one, atData_q_iB, atData_k_iB, Fin.fin_one_eq_zero j, atB_succAbove]
  norm_num

theorem atB_phaseExp : atPhase.phaseExp iB γ = 1 - 2 * γ := by
  unfold WallChartsData.Phase.phaseExp
  rw [atB_nu]
  ring

theorem atB_constB : atPhase.constB iB σ = σ ^ 2 := by
  unfold WallChartsData.Phase.constB
  rw [atB_nu, Real.rpow_two, sq_abs]

theorem atB_constA : atPhase.constA iB σ = |σ| := by
  unfold WallChartsData.Phase.constA
  rw [atB_pExp, atB_qk_real, Real.rpow_one, div_one]

theorem atB_orthSign : atData.orthSign iB ε = bsign (ε 0) := by
  unfold WallChartsData.orthSign
  rw [atData_S, atData_q_iB, atData_k_iB, Fin.prod_univ_one, atB_succAbove]
  simp

theorem atB_admissible_iff :
    atData.admissible iB ε b σ ↔ 0 < bsign (ε 0) * (if b then 1 else -1) * σ := by
  unfold WallChartsData.admissible
  rw [atB_orthSign, atB_qk, pow_one]

theorem atB_sum_Q_alpha : ∑ j : Fin 1, atData.Qexp iB j * bsAlpha γ j = γ - 1 / 2 := by
  rw [Fin.sum_univ_one, atB_Qexp, one_mul]
  rfl

theorem atB_sum_kappa_alpha :
    ∑ j : Fin 1, atPhase.kappa iB j * bsAlpha γ j = 1 - 2 * γ := by
  rw [Fin.sum_univ_one, atB_kappa]
  unfold bsAlpha
  ring

theorem atB_feasible (hγ : 1 / 2 < γ) :
    ConstrainedFeasible (atData.Qexp iB) (atPhase.kappa iB) γ
      (atPhase.phaseExp iB γ) (bsAlpha γ) := by
  refine ⟨fun _ ↦ by unfold bsAlpha; linarith, ?_, ?_⟩
  · rw [atB_sum_Q_alpha]
    linarith
  · rw [atB_sum_kappa_alpha, atB_phaseExp]

theorem atB_lpExponent :
    lpExponent γ (atPhase.pExp iB) (fun j ↦ atPhase.rExp iB j + 1) (bsAlpha γ) =
      1 / 2 := by
  unfold lpExponent
  simp only [Fin.sum_univ_one, atB_pExp, atB_rExp, bsAlpha]
  ring

theorem atB_limitDomain (hγ : 1 / 2 < γ) :
    limitDomain (atData.ρ iB) (atData.constD iB σ) γ
        (atData.q iB (atData.k iB)) (atData.Qexp iB) (bsAlpha γ) =
      {u : Fin 1 → ℝ | 0 < u 0} := by
  have hne : ∀ j, bsAlpha γ j ≠ 0 := fun j ↦ by unfold bsAlpha; linarith
  have hstrict : γ - 1 / 2 ≠ γ := by linarith
  ext u
  simp only [limitDomain, mem_inter_iff, Set.mem_univ_pi, mem_ofPred_eq, atB_sum_Q_alpha, hstrict,
    false_imp_iff, and_true, hne, if_false, mem_Ioi]
  constructor
  · intro h
    exact h 0
  · intro h j
    rw [Fin.fin_one_eq_zero j]
    exact h

theorem atB_limitCut (u : Fin 1 → ℝ) :
    limitCut (atData.constD iB σ) γ (atData.q iB (atData.k iB))
      (atData.Qexp iB) (bsAlpha γ) u = 0 := by
  have hstrict : γ - 1 / 2 ≠ γ := by linarith
  unfold limitCut
  rw [atB_sum_Q_alpha, if_neg hstrict]

theorem atB_limitBranchPt (hγ : 1 / 2 < γ) (u : Fin 1 → ℝ) :
    atData.limitBranchPt iB ε b σ γ (bsAlpha γ) u = 0 := by
  unfold WallChartsData.limitBranchPt WallChartsData.bridgePt
  rw [bs_facePt γ hγ u, atB_limitCut σ γ u, mul_zero, atData_k_iB]
  funext j
  revert j
  rw [Fin.forall_iff_succAbove (1 : Fin 2)]
  refine ⟨by rw [Fin.insertNth_apply_same]; rfl, fun j ↦ ?_⟩
  rw [Fin.insertNth_apply_succAbove]
  simp [orth]

theorem atB_limitUnit (hγ : 1 / 2 < γ) (u : Fin 1 → ℝ) :
    atPhase.limitUnit iB ε b σ γ (bsAlpha γ) u = 1 := by
  unfold WallChartsData.Phase.limitUnit
  rw [atB_limitBranchPt ε b σ γ hγ u, atPhase_a_one]
  simp

theorem atB_limitWeight (hγ : 1 / 2 < γ) (φ : (Fin 2 → ℝ) → ℝ) (u : Fin 1 → ℝ) :
    atPhase.limitWeight iB φ ε b σ γ (bsAlpha γ) u = φ 0 := by
  unfold WallChartsData.Phase.limitWeight
  rw [atB_limitBranchPt ε b σ γ hγ u, atData_rep_iB, atPhase_wt_one, atPhase_b, bsRep_zero_pt,
    bsCut_eq_one (by rw [norm_zero]; norm_num)]
  simp [hB_zero]

theorem atB_dsProfile (hγ : 1 / 2 < γ) (u : Fin 1 → ℝ) :
    dsProfile (atData.ρ iB) (atPhase.constB iB σ) (atData.constD iB σ)
        γ (atData.q iB (atData.k iB)) (atPhase.phaseExp iB γ)
        (atData.Qexp iB) (atPhase.kappa iB) (bsAlpha γ)
        (atPhase.limitUnit iB ε b σ γ (bsAlpha γ)) u =
      if 0 < u 0 then σ ^ 2 * u 0 ^ (-2 : ℝ) else 0 := by
  unfold dsProfile
  rw [atB_limitDomain σ γ hγ, atB_sum_kappa_alpha, atB_phaseExp]
  simp only [mem_ofPred_eq, if_true, atB_constB, atB_limitUnit ε b σ γ hγ, mul_one,
    Fin.prod_univ_one, atB_kappa]

theorem atB_dsWeight₀ (hγ : 1 / 2 < γ) (φ : (Fin 2 → ℝ) → ℝ) (u : Fin 1 → ℝ) :
    dsWeight₀ (atData.ρ iB) (atData.constD iB σ) γ
        (atData.q iB (atData.k iB)) (atData.Qexp iB)
        (atPhase.rExp iB) (bsAlpha γ) (atPhase.limitWeight iB φ ε b σ γ
          (bsAlpha γ)) u =
      if 0 < u 0 then φ 0 * u 0 ^ (-2 : ℝ) else 0 := by
  unfold dsWeight₀
  rw [atB_limitDomain σ γ hγ, Set.indicator_apply]
  simp [atB_rExp, atB_limitWeight ε b σ γ hγ φ]

theorem atB_profile (hσ : σ ≠ 0) (hγ : 1 / 2 < γ) :
    atPhase.ProfileIntegrableOf iB ε b σ γ (bsAlpha γ) := by
  refine WallChartsData.Phase.ProfileIntegrableOf.of_vertex atPhase hσ (0 : Fin 1) ?_ ?_ ?_ ?_ ?_
    ?_
  · rw [atB_kappa]; norm_num
  · rw [atB_kappa, atB_rExp]; norm_num
  · rw [atB_kappa, atB_phaseExp]
    have : (1 - 2 * γ) / -2 = γ - 1 / 2 := by ring
    rw [this]
    linarith
  · intro l
    rw [Fin.fin_one_eq_zero l, if_pos rfl, atB_kappa, atB_phaseExp]
    unfold bsAlpha
    ring
  · rw [atB_sum_Q_alpha]
    linarith
  · intro l hl
    exact absurd (Fin.fin_one_eq_zero l) hl

theorem atB_termConst (hσ : σ ≠ 0) (hγ : 1 / 2 < γ) (φ : (Fin 2 → ℝ) → ℝ) :
    atPhase.termConst iB φ ε b σ γ (bsAlpha γ) = φ 0 * (√π / 2) := by
  unfold WallChartsData.Phase.termConst
  rw [atB_constA]
  have key : (fun u : Fin 1 → ℝ ↦
      dsWeight₀ (atData.ρ iB) (atData.constD iB σ) γ
          (atData.q iB (atData.k iB)) (atData.Qexp iB)
          (atPhase.rExp iB) (bsAlpha γ)
          (atPhase.limitWeight iB φ ε b σ γ (bsAlpha γ)) u *
        exp (-dsProfile (atData.ρ iB) (atPhase.constB iB σ)
          (atData.constD iB σ) γ (atData.q iB (atData.k iB))
          (atPhase.phaseExp iB γ) (atData.Qexp iB) (atPhase.kappa iB)
          (bsAlpha γ) (atPhase.limitUnit iB ε b σ γ (bsAlpha γ)) u)) =
      fun u ↦ φ 0 * invProfile (σ ^ 2) (u 0) := by
    funext u
    rw [atB_dsWeight₀ ε b σ γ hγ φ, atB_dsProfile ε b σ γ hγ]
    unfold invProfile
    by_cases h : 0 < u 0
    · rw [if_pos h, if_pos h, Set.indicator_of_mem (mem_Ioi.mpr h), neg_mul, mul_assoc]
    · rw [if_neg h, if_neg h, Set.indicator_of_notMem (fun h' ↦ h (mem_Ioi.mp h')), zero_mul,
        mul_zero]
  rw [key, integral_const_mul, integral_comp_zero, integral_invProfile (by positivity),
    Real.sqrt_sq_eq_abs]
  have hσ' : |σ| ≠ 0 := abs_ne_zero.mpr hσ
  field_simp

theorem atB_admissible_true (hσ : 0 < σ) : atData.admissible iB (fun _ ↦ true) true σ := by
  rw [atB_admissible_iff]
  simpa [bsign] using hσ

/-! ### The assembled limit -/

/-- The scales of the atlas: `0` on chart `A`, the vertex `γ − 1/2` on chart `B`. -/
noncomputable def atAlpha (γ : ℝ) : atData.ι → Fin 1 → ℝ := ![atAlphaA, bsAlpha γ]

theorem atAlpha_iA : atAlpha γ iA = atAlphaA := rfl
theorem atAlpha_iB : atAlpha γ iB = bsAlpha γ := rfl

theorem at_truth (i : atData.ι) (u : Fin 2 → ℝ) :
    atData.rep i u 0 = truthMono (atData.S i) (atData.q i) u := by
  revert i
  refine forall_index.mpr ⟨?_, ?_⟩
  · rw [atData_rep_iA, atData_S, atData_q_iA]
    exact truthA u
  · rw [atData_rep_iB, atData_S, atData_q_iB]
    exact truthB u

theorem at_termLam (p : WallChartsData.Phase.TermIdx atData) :
    atPhase.termLam γ (fun i _ _ ↦ atAlpha γ i) p = if p.1 = iA then γ else 1 / 2 := by
  unfold WallChartsData.Phase.termLam
  obtain ⟨i, ε, b⟩ := p
  dsimp only
  revert i
  refine forall_index.mpr ⟨?_, ?_⟩
  · rw [if_pos rfl, atAlpha_iA]
    exact atA_lpExponent γ
  · rw [if_neg iB_ne_iA, atAlpha_iB]
    exact atB_lpExponent γ

open scoped Classical in
/-- **The expectation along the truth fibre for the two-chart atlas**: for `γ > 1/2` and `σ > 0`,
chart `A` is subdominant and the ratio of the total kernels converges to `ψ(0)/χ(0)`. -/
theorem at_tendsto_fibre_expectation (hσ : 0 < σ) (hγ : 1 / 2 < γ)
    {ψ χ : (Fin 2 → ℝ) → ℝ} (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z) {Mψ : ℝ}
    (hMψ : ∀ z, ψ z ≤ Mψ) (hψL : ∀ z, ψ z ≠ 0 → z ∈ atL') (hχc : Continuous χ)
    (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ} (hMχ : ∀ z, χ z ≤ Mχ) (hχL : ∀ z, χ z ≠ 0 → z ∈ atL')
    (hχ0 : 0 < χ 0) :
    Tendsto (fun t ↦
        (atData.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * bsF z)) * ψ z))
          (σ * t ^ (-γ))).toReal /
        (atData.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * bsF z)) * χ z))
          (σ * t ^ (-γ))).toReal) atTop (𝓝 (ψ 0 / χ 0)) := by
  have hS : ∀ i, |atData.S i| = 1 := fun i ↦ by rw [atData_S, abs_one]
  have hF : ∀ z, 0 ≤ bsF z := fun z ↦ by unfold bsF; positivity
  have hFm : Measurable bsF := by unfold bsF; fun_prop
  have htruth : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin 2 → ℝ) (atData.ρ i),
      atData.rep i u 0 = truthMono (atData.S i) (atData.q i) u := fun i u _ ↦ at_truth i u
  set c : ℝ := √π / 2 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  set Sc : ℝ := ∑ p : WallChartsData.Phase.TermIdx atData,
    if p.1 = iA then 0 else if atData.admissible p.1 p.2.1 p.2.2 σ then c else 0 with hSc
  have hScpos : 0 < Sc := by
    have h1 : c ≤ Sc := by
      rw [hSc]
      have := Finset.single_le_sum (f := fun p : WallChartsData.Phase.TermIdx atData ↦
        if p.1 = iA then 0 else if atData.admissible p.1 p.2.1 p.2.2 σ then c else 0)
        (fun p _ ↦ by split_ifs <;> positivity)
        (Finset.mem_univ ((iB, fun _ ↦ true, true) : WallChartsData.Phase.TermIdx atData))
      dsimp only at this
      rwa [if_neg iB_ne_iA, if_pos (atB_admissible_true σ hσ)] at this
    exact hcpos.trans_le h1
  have hterm : ∀ (φ : (Fin 2 → ℝ) → ℝ) (p : WallChartsData.Phase.TermIdx atData),
      (if atPhase.termLam γ (fun i _ _ ↦ atAlpha γ i) p = 1 / 2 then
        atPhase.termConst' φ σ γ (fun i _ _ ↦ atAlpha γ i) p else 0) =
      φ 0 * (if p.1 = iA then 0 else if atData.admissible p.1 p.2.1 p.2.2 σ then c else 0) := by
    intro φ p
    rw [at_termLam γ p]
    obtain ⟨i, ε, b⟩ := p
    dsimp only
    revert i
    refine forall_index.mpr ⟨?_, ?_⟩
    · rw [if_pos rfl, if_pos rfl, mul_zero, if_neg (by linarith : γ ≠ 1 / 2)]
    · rw [if_neg iB_ne_iA, if_neg iB_ne_iA, if_pos rfl]
      unfold WallChartsData.Phase.termConst'
      dsimp only
      split_ifs with hadm
      · rw [atAlpha_iB, atB_termConst ε b σ γ hσ.ne' hγ φ, hc]
      · rw [mul_zero]
  have hsum : ∀ φ : (Fin 2 → ℝ) → ℝ,
      (∑ p : WallChartsData.Phase.TermIdx atData,
        if atPhase.termLam γ (fun i _ _ ↦ atAlpha γ i) p = 1 / 2 then
          atPhase.termConst' φ σ γ (fun i _ _ ↦ atAlpha γ i) p else 0) = φ 0 * Sc := by
    intro φ
    rw [hSc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ ↦ hterm φ p
  have hpos : (∑ p : WallChartsData.Phase.TermIdx atData,
      if atPhase.termLam γ (fun i _ _ ↦ atAlpha γ i) p = 1 / 2 then
        atPhase.termConst' χ σ γ (fun i _ _ ↦ atAlpha γ i) p else 0) ≠ 0 := by
    rw [hsum χ]
    exact (mul_pos hχ0 hScpos).ne'
  have hfeas : ∀ i ε b, atData.admissible i ε b σ →
      ConstrainedFeasible (atData.Qexp i) (atPhase.kappa i) γ (atPhase.phaseExp i γ)
        (atAlpha γ i) := by
    refine forall_index.mpr ⟨fun _ _ _ ↦ ?_, fun _ _ _ ↦ ?_⟩
    · exact atA_feasible γ hγ
    · exact atB_feasible γ hγ
  have hprof : ∀ i ε b, atData.admissible i ε b σ →
      atPhase.ProfileIntegrableOf i ε b σ γ (atAlpha γ i) := by
    refine forall_index.mpr ⟨fun ε b _ ↦ ?_, fun ε b _ ↦ ?_⟩
    · exact atA_profile ε b σ γ hγ
    · exact atB_profile ε b σ γ hσ.ne' hγ
  have hmin : ∀ p : WallChartsData.Phase.TermIdx atData,
      1 / 2 ≤ atPhase.termLam γ (fun i _ _ ↦ atAlpha γ i) p := fun p ↦ by
    rw [at_termLam γ p]
    split_ifs
    · exact hγ.le
    · exact le_rfl
  have hlim := atPhase.tendsto_fibre_expectation hS hF hFm htruth hσ.ne' hψc hψ hMψ hψL hχc hχ
    hMχ hχL (α := fun i _ _ ↦ atAlpha γ i) hfeas hprof (lam₀ := 1 / 2) hmin hpos
  rw [hsum ψ, hsum χ, mul_div_mul_right _ _ hScpos.ne'] at hlim
  exact hlim

end Laplace.Multi.BlowupAtlas
