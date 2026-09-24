/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BlowupSectorRecord
import Laplace.Multi.ToyWallLimit
import Laplace.Multi.VertexCertificate

/-!
# The blow-up chart through the analytic layer

The constants of the blow-up chart `(x, y) ↦ (xy, y)` (`BlowupSectorRecord`) for `F = z₀² + z₁²`
along the fibre `z₀ = σ t^{-γ}`, `γ > 1/2`: solving for `y`, `q_k = 1`, `Q = 1`, `ν = 2`,
`κ = −2`, `p = 1`, `r = −2`, `δ = 1 − 2γ`, `A = |σ|`, `B = σ²`, `D = |σ|`. The constrained LP
`α ≥ 0`, `α ≤ γ` (truth), `−2α ≥ 1 − 2γ` (phase) with objective `λ = γ − α` is optimised at the
vertex `α = γ − 1/2`, where the phase constraint is tied, the truth constraint is strict and
`λ = 1/2`. The scaled coordinate carries the *negative* phase exponent `κ = −2` and the
non-integrable density exponent `r = −2`, so the certificate is the `κ_j < 0` case of the vertex
certificate (`ProfileIntegrableOf.of_vertex` with `η = (r + 1)/κ = 1/2`). The limiting profile is
`σ² u^{-2}` on `(0, ∞)`, the term constant is `φ(0) √π / 2` (a Gamma integral in `1/u`), and the
expectation along the fibre converges to `ψ(0)/χ(0)` (`bs_tendsto_fibre_expectation`) — as it
must, since the fibre integral is `∫ e^{-t(s² + z₁²)} ψ dz₁ ~ √(π/t) ψ(0)` directly.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi.BlowupSector

open Laplace.Multi.ToyWall

variable (i : bsData.ι) (ε : Fin 1 → Bool) (b : Bool) (σ γ : ℝ)

/-! ### The constants of the chart -/

theorem bsPhase_kF (i : bsData.ι) : bsPhase.kF i = ![0, 2] := rfl
theorem bsPhase_hJ (i : bsData.ι) : bsPhase.hJ i = ![0, 1] := rfl
theorem bsPhase_a (i : bsData.ι) (u : Fin 2 → ℝ) : bsPhase.a i u = 1 + u 0 ^ 2 := rfl
theorem bsPhase_b (i : bsData.ι) (u : Fin 2 → ℝ) : bsPhase.b i u = 1 := rfl
theorem bsPhase_wt (i : bsData.ι) (u : Fin 2 → ℝ) : bsPhase.wt i u = bsCut u := rfl
theorem bsPhase_ma (i : bsData.ι) : bsPhase.ma i = 1 := rfl
theorem bsPhase_Ma (i : bsData.ι) : bsPhase.Ma i = 5 := rfl
theorem bsPhase_Mb (i : bsData.ι) : bsPhase.Mb i = 1 := rfl

theorem bs_succAbove : (1 : Fin 2).succAbove (0 : Fin 1) = 0 := rfl

theorem bs_qk : bsData.q i (bsData.k i) = 1 := rfl

theorem bs_qk_real : (bsData.q i (bsData.k i) : ℝ) = 1 := by rw [bs_qk]; simp

theorem bs_Qexp (j : Fin 1) : bsData.Qexp i j = 1 := by
  unfold WallChartsData.Qexp
  rw [bsData_q, bsData_k, Fin.fin_one_eq_zero j, bs_succAbove]
  simp

theorem bs_nu : bsPhase.nu i = 2 := by
  unfold WallChartsData.Phase.nu
  rw [bsPhase_kF, bsData_q, bsData_k]
  simp

theorem bs_kappa (j : Fin 1) : bsPhase.kappa i j = -2 := by
  unfold WallChartsData.Phase.kappa
  rw [bsPhase_kF, bsData_q, bsData_k, Fin.fin_one_eq_zero j, bs_succAbove]
  simp

theorem bs_pExp : bsPhase.pExp i = 1 := by
  unfold WallChartsData.Phase.pExp
  rw [bsPhase_hJ, bsData_q, bsData_k]
  norm_num

theorem bs_rExp (j : Fin 1) : bsPhase.rExp i j = -2 := by
  unfold WallChartsData.Phase.rExp
  rw [bsPhase_hJ, bsData_q, bsData_k, Fin.fin_one_eq_zero j, bs_succAbove]
  norm_num

theorem bs_phaseExp : bsPhase.phaseExp i γ = 1 - 2 * γ := by
  unfold WallChartsData.Phase.phaseExp
  rw [bs_nu]
  ring

theorem bs_constD : bsData.constD i σ = |σ| := by
  unfold WallChartsData.constD
  rw [bs_qk_real]
  simp

theorem bs_constB : bsPhase.constB i σ = σ ^ 2 := by
  unfold WallChartsData.Phase.constB
  rw [bs_nu, Real.rpow_two, sq_abs]

theorem bs_constA : bsPhase.constA i σ = |σ| := by
  unfold WallChartsData.Phase.constA
  rw [bs_pExp, bs_qk_real, Real.rpow_one, div_one]

theorem bs_orthSign : bsData.orthSign i ε = bsign (ε 0) := by
  unfold WallChartsData.orthSign
  rw [bsData_S, bsData_q, bsData_k, Fin.prod_univ_one, bs_succAbove]
  simp

theorem bs_admissible_iff :
    bsData.admissible i ε b σ ↔ 0 < bsign (ε 0) * (if b then 1 else -1) * σ := by
  unfold WallChartsData.admissible
  rw [bs_orthSign, bs_qk, pow_one]

/-- The vertex scale `α = γ − 1/2`. -/
noncomputable def bsAlpha (γ : ℝ) : Fin 1 → ℝ := fun _ ↦ γ - 1 / 2

theorem bs_sum_Q_alpha : ∑ j : Fin 1, bsData.Qexp i j * bsAlpha γ j = γ - 1 / 2 := by
  rw [Fin.sum_univ_one, bs_Qexp, one_mul]
  rfl

theorem bs_sum_kappa_alpha : ∑ j : Fin 1, bsPhase.kappa i j * bsAlpha γ j = 1 - 2 * γ := by
  rw [Fin.sum_univ_one, bs_kappa]
  unfold bsAlpha
  ring

theorem bs_feasible (hγ : 1 / 2 < γ) :
    ConstrainedFeasible (bsData.Qexp i) (bsPhase.kappa i) γ (bsPhase.phaseExp i γ)
      (bsAlpha γ) := by
  refine ⟨fun _ ↦ by unfold bsAlpha; linarith, ?_, ?_⟩
  · rw [bs_sum_Q_alpha]
    linarith
  · rw [bs_sum_kappa_alpha, bs_phaseExp]

theorem bs_lpExponent :
    lpExponent γ (bsPhase.pExp i) (fun j ↦ bsPhase.rExp i j + 1) (bsAlpha γ) = 1 / 2 := by
  unfold lpExponent
  simp only [Fin.sum_univ_one, bs_pExp, bs_rExp, bsAlpha]
  ring

/-! ### The limiting objects -/

theorem bs_limitDomain (hγ : 1 / 2 < γ) :
    limitDomain (bsData.ρ i) (bsData.constD i σ) γ (bsData.q i (bsData.k i)) (bsData.Qexp i)
      (bsAlpha γ) = {u : Fin 1 → ℝ | 0 < u 0} := by
  have hne : ∀ j, bsAlpha γ j ≠ 0 := fun j ↦ by unfold bsAlpha; linarith
  have hstrict : γ - 1 / 2 ≠ γ := by linarith
  ext u
  simp only [limitDomain, mem_inter_iff, Set.mem_univ_pi, mem_ofPred_eq, bs_sum_Q_alpha, hstrict,
    false_imp_iff, and_true, hne, if_false, mem_Ioi]
  constructor
  · intro h
    exact h 0
  · intro h j
    rw [Fin.fin_one_eq_zero j]
    exact h

theorem bs_facePt (hγ : 1 / 2 < γ) (u : Fin 1 → ℝ) : facePt (bsAlpha γ) u = 0 := by
  have hne : ∀ j, bsAlpha γ j ≠ 0 := fun j ↦ by unfold bsAlpha; linarith
  funext j
  simp [facePt, hne]

theorem bs_limitCut (u : Fin 1 → ℝ) :
    limitCut (bsData.constD i σ) γ (bsData.q i (bsData.k i)) (bsData.Qexp i) (bsAlpha γ) u =
      0 := by
  have hstrict : γ - 1 / 2 ≠ γ := by linarith
  unfold limitCut
  rw [bs_sum_Q_alpha, if_neg hstrict]

theorem bs_limitBranchPt (hγ : 1 / 2 < γ) (u : Fin 1 → ℝ) :
    bsData.limitBranchPt i ε b σ γ (bsAlpha γ) u = 0 := by
  unfold WallChartsData.limitBranchPt WallChartsData.bridgePt
  rw [bs_facePt γ hγ u, bs_limitCut i σ γ u, mul_zero, bsData_k]
  funext j
  revert j
  rw [Fin.forall_iff_succAbove (1 : Fin 2)]
  refine ⟨by rw [Fin.insertNth_apply_same]; rfl, fun j ↦ ?_⟩
  rw [Fin.insertNth_apply_succAbove]
  simp [orth]

theorem bs_limitUnit (hγ : 1 / 2 < γ) (u : Fin 1 → ℝ) :
    bsPhase.limitUnit i ε b σ γ (bsAlpha γ) u = 1 := by
  unfold WallChartsData.Phase.limitUnit
  rw [bs_limitBranchPt i ε b σ γ hγ u, bsPhase_a]
  simp

theorem bsRep_zero_pt : bsRep 0 = 0 := by
  funext j
  revert j
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;> simp [bsRep_zero, bsRep_one]

theorem bs_limitWeight (hγ : 1 / 2 < γ) (φ : (Fin 2 → ℝ) → ℝ) (u : Fin 1 → ℝ) :
    bsPhase.limitWeight i φ ε b σ γ (bsAlpha γ) u = φ 0 := by
  unfold WallChartsData.Phase.limitWeight
  rw [bs_limitBranchPt i ε b σ γ hγ u, bsData_rep, bsPhase_wt, bsPhase_b, bsRep_zero_pt,
    bsCut_eq_one (by rw [norm_zero]; norm_num)]
  simp

theorem bs_dsProfile (hγ : 1 / 2 < γ) (u : Fin 1 → ℝ) :
    dsProfile (bsData.ρ i) (bsPhase.constB i σ) (bsData.constD i σ) γ
        (bsData.q i (bsData.k i)) (bsPhase.phaseExp i γ) (bsData.Qexp i) (bsPhase.kappa i)
        (bsAlpha γ) (bsPhase.limitUnit i ε b σ γ (bsAlpha γ)) u =
      if 0 < u 0 then σ ^ 2 * u 0 ^ (-2 : ℝ) else 0 := by
  unfold dsProfile
  rw [bs_limitDomain i σ γ hγ, bs_sum_kappa_alpha, bs_phaseExp]
  simp only [mem_ofPred_eq, if_true, bs_constB, bs_limitUnit i ε b σ γ hγ, mul_one,
    Fin.prod_univ_one, bs_kappa]

theorem bs_dsEnvelope (hγ : 1 / 2 < γ) (u : Fin 1 → ℝ) :
    dsEnvelope (bsData.ρ i) (bsData.constD i σ) γ (bsData.q i (bsData.k i)) (bsData.Qexp i)
        (bsPhase.rExp i) (bsAlpha γ) 1 u = if 0 < u 0 then u 0 ^ (-2 : ℝ) else 0 := by
  unfold dsEnvelope
  rw [bs_limitDomain i σ γ hγ, Set.indicator_apply]
  simp [bs_rExp]

theorem bs_dsWeight₀ (hγ : 1 / 2 < γ) (φ : (Fin 2 → ℝ) → ℝ) (u : Fin 1 → ℝ) :
    dsWeight₀ (bsData.ρ i) (bsData.constD i σ) γ (bsData.q i (bsData.k i)) (bsData.Qexp i)
        (bsPhase.rExp i) (bsAlpha γ) (bsPhase.limitWeight i φ ε b σ γ (bsAlpha γ)) u =
      if 0 < u 0 then φ 0 * u 0 ^ (-2 : ℝ) else 0 := by
  unfold dsWeight₀
  rw [bs_limitDomain i σ γ hγ, Set.indicator_apply]
  simp [bs_rExp, bs_limitWeight i ε b σ γ hγ φ]

/-! ### The profile certificate: the `κ < 0` vertex -/

theorem bs_profile (hσ : σ ≠ 0) (hγ : 1 / 2 < γ) :
    bsPhase.ProfileIntegrableOf i ε b σ γ (bsAlpha γ) := by
  refine WallChartsData.Phase.ProfileIntegrableOf.of_vertex bsPhase hσ (0 : Fin 1) ?_ ?_ ?_ ?_ ?_
    ?_
  · rw [bs_kappa]; norm_num
  · rw [bs_kappa, bs_rExp]; norm_num
  · rw [bs_kappa, bs_phaseExp]
    have : (1 - 2 * γ) / -2 = γ - 1 / 2 := by ring
    rw [this]
    linarith
  · intro l
    rw [Fin.fin_one_eq_zero l, if_pos rfl, bs_kappa, bs_phaseExp]
    unfold bsAlpha
    ring
  · rw [bs_sum_Q_alpha]
    linarith
  · intro l hl
    exact absurd (Fin.fin_one_eq_zero l) hl

/-! ### The constant and the limit -/

/-- The half-line profile `x^{-2} e^{-c x^{-2}}`. -/
noncomputable def invProfile (c : ℝ) (x : ℝ) : ℝ :=
  (Ioi 0).indicator (fun x ↦ x ^ (-2 : ℝ) * exp (-c * x ^ (-2 : ℝ))) x

theorem integral_invProfile {c : ℝ} (hc : 0 < c) : ∫ x, invProfile c x = √π / (2 * √c) := by
  unfold invProfile
  rw [integral_indicator measurableSet_Ioi,
    integral_rpow_mul_exp_neg_mul_rpow_of_neg (by norm_num) (by norm_num) hc]
  have e1 : -(-2 + 1 : ℝ) / -2 = -(1 / 2) := by norm_num
  have e2 : (-2 + 1 : ℝ) / -2 = 1 / 2 := by norm_num
  rw [e1, e2, Real.Gamma_one_half_eq, Real.rpow_neg hc.le, ← Real.sqrt_eq_rpow]
  field_simp

theorem bs_termConst (hσ : σ ≠ 0) (hγ : 1 / 2 < γ) (φ : (Fin 2 → ℝ) → ℝ) :
    bsPhase.termConst i φ ε b σ γ (bsAlpha γ) = φ 0 * (√π / 2) := by
  unfold WallChartsData.Phase.termConst
  rw [bs_constA]
  have key : (fun u : Fin 1 → ℝ ↦
      dsWeight₀ (bsData.ρ i) (bsData.constD i σ) γ (bsData.q i (bsData.k i)) (bsData.Qexp i)
          (bsPhase.rExp i) (bsAlpha γ) (bsPhase.limitWeight i φ ε b σ γ (bsAlpha γ)) u *
        exp (-dsProfile (bsData.ρ i) (bsPhase.constB i σ) (bsData.constD i σ) γ
          (bsData.q i (bsData.k i)) (bsPhase.phaseExp i γ) (bsData.Qexp i) (bsPhase.kappa i)
          (bsAlpha γ) (bsPhase.limitUnit i ε b σ γ (bsAlpha γ)) u)) =
      fun u ↦ φ 0 * invProfile (σ ^ 2) (u 0) := by
    funext u
    rw [bs_dsWeight₀ i ε b σ γ hγ φ, bs_dsProfile i ε b σ γ hγ]
    unfold invProfile
    by_cases h : 0 < u 0
    · rw [if_pos h, if_pos h, Set.indicator_of_mem (mem_Ioi.mpr h), neg_mul, mul_assoc]
    · rw [if_neg h, if_neg h, Set.indicator_of_notMem (fun h' ↦ h (mem_Ioi.mp h')), zero_mul,
        mul_zero]
  rw [key, integral_const_mul, integral_comp_zero, integral_invProfile (by positivity),
    Real.sqrt_sq_eq_abs]
  have hσ' : |σ| ≠ 0 := abs_ne_zero.mpr hσ
  field_simp

/-- The admissible term for `σ > 0`: positive transverse sign and the `+` branch. -/
theorem bs_admissible_true (hσ : 0 < σ) : bsData.admissible i (fun _ ↦ true) true σ := by
  rw [bs_admissible_iff]
  simpa [bsign] using hσ

theorem bs_truth (i : bsData.ι) (u : Fin 2 → ℝ) :
    bsData.rep i u 0 = truthMono (bsData.S i) (bsData.q i) u := by
  rw [bsData_rep, bsData_S, bsData_q]
  simp [truthMono, bsRep_zero, Fin.prod_univ_two]

open scoped Classical in
/-- **The expectation along the truth fibre in the blow-up chart**: for `γ > 1/2` and `σ > 0`,
the ratio of the total kernels of two observables localised in the sector converges to
`ψ(0)/χ(0)`. -/
theorem bs_tendsto_fibre_expectation (hσ : 0 < σ) (hγ : 1 / 2 < γ)
    {ψ χ : (Fin 2 → ℝ) → ℝ} (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z) {Mψ : ℝ}
    (hMψ : ∀ z, ψ z ≤ Mψ) (hψL : ∀ z, ψ z ≠ 0 → z ∈ bsL') (hχc : Continuous χ)
    (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ} (hMχ : ∀ z, χ z ≤ Mχ) (hχL : ∀ z, χ z ≠ 0 → z ∈ bsL')
    (hχ0 : 0 < χ 0) :
    Tendsto (fun t ↦
        (bsData.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * bsF z)) * ψ z))
          (σ * t ^ (-γ))).toReal /
        (bsData.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * bsF z)) * χ z))
          (σ * t ^ (-γ))).toReal) atTop (𝓝 (ψ 0 / χ 0)) := by
  have hS : ∀ i, |bsData.S i| = 1 := fun i ↦ by rw [bsData_S, abs_one]
  have hF : ∀ z, 0 ≤ bsF z := fun z ↦ by unfold bsF; positivity
  have hFm : Measurable bsF := by unfold bsF; fun_prop
  have htruth : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin 2 → ℝ) (bsData.ρ i),
      bsData.rep i u 0 = truthMono (bsData.S i) (bsData.q i) u := fun i u _ ↦ bs_truth i u
  set c : ℝ := √π / 2 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  set Sc : ℝ := ∑ p : WallChartsData.Phase.TermIdx bsData,
    if bsData.admissible p.1 p.2.1 p.2.2 σ then c else 0 with hSc
  have hScpos : 0 < Sc := by
    have h1 : c ≤ Sc := by
      rw [hSc]
      have := Finset.single_le_sum (f := fun p : WallChartsData.Phase.TermIdx bsData ↦
        if bsData.admissible p.1 p.2.1 p.2.2 σ then c else 0)
        (fun p _ ↦ by split_ifs <;> positivity)
        (Finset.mem_univ (((), fun _ ↦ true, true) : WallChartsData.Phase.TermIdx bsData))
      simpa [bs_admissible_true () σ hσ] using this
    exact hcpos.trans_le h1
  have hsum : ∀ φ : (Fin 2 → ℝ) → ℝ,
      (∑ p : WallChartsData.Phase.TermIdx bsData,
        if bsPhase.termLam γ (fun _ _ _ ↦ bsAlpha γ) p = 1 / 2 then
          bsPhase.termConst' φ σ γ (fun _ _ _ ↦ bsAlpha γ) p else 0) = φ 0 * Sc := by
    intro φ
    rw [hSc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    have hl : bsPhase.termLam γ (fun _ _ _ ↦ bsAlpha γ) p = 1 / 2 := by
      unfold WallChartsData.Phase.termLam
      exact bs_lpExponent p.1 γ
    rw [if_pos hl]
    unfold WallChartsData.Phase.termConst'
    split_ifs with hadm
    · rw [bs_termConst _ _ _ σ γ hσ.ne' hγ φ]
    · rw [mul_zero]
  have hpos : (∑ p : WallChartsData.Phase.TermIdx bsData,
      if bsPhase.termLam γ (fun _ _ _ ↦ bsAlpha γ) p = 1 / 2 then
        bsPhase.termConst' χ σ γ (fun _ _ _ ↦ bsAlpha γ) p else 0) ≠ 0 := by
    rw [hsum χ]
    exact (mul_pos hχ0 hScpos).ne'
  have hlim := bsPhase.tendsto_fibre_expectation hS hF hFm htruth hσ.ne' hψc hψ hMψ hψL hχc hχ
    hMχ hχL (α := fun _ _ _ ↦ bsAlpha γ) (fun i _ _ _ ↦ bs_feasible i γ hγ)
    (fun i ε b _ ↦ bs_profile i ε b σ γ hσ.ne' hγ)
    (lam₀ := 1 / 2) (fun p ↦ by
      unfold WallChartsData.Phase.termLam
      rw [bs_lpExponent]) hpos
  rw [hsum ψ, hsum χ, mul_div_mul_right _ _ hScpos.ne'] at hlim
  exact hlim

end Laplace.Multi.BlowupSector
