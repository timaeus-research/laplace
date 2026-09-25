/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BlowupAtlasLimit
import Laplace.Multi.LimitingMeasure

/-!
# The two-chart atlas at the Gaussian scale: two leading charts

The atlas of `BlowupAtlasRecord` along the fibre `z₀ = σ t^{-1/2}`, i.e. `γ = 1/2`. Now both
charts have exponent `λ = 1/2`: chart `A`'s phase constraint becomes tied at `α = 0` (its profile
is the constant `σ²(1 + y²)`), and chart `B`'s vertex collapses to `α = 0` with a tied phase
(profile `σ²(1 + x²) x^{-2}` on the bounded box). All four admissible terms are dominant, none of
them has a closed-form constant, and every face map is constant at the origin. The point
theorem of `LimitingMeasure` therefore gives `⟨ψ⟩_χ → ψ(0)/χ(0)`
(`at_tendsto_fibre_expectation_half`) — consistent with the direct computation
`∫ e^{-t(σ²/t + z₁²)} ψ dz₁ = e^{-σ²} ∫ e^{-t z₁²} ψ`,
where the factor `e^{-σ²}` cancels in the ratio.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi.BlowupAtlas

open Laplace.Multi.ToyWall Laplace.Multi.BlowupSector

variable (ε : Fin 1 → Bool) (b : Bool) (σ : ℝ)

theorem mul_exp_neg_le_two_div {c X : ℝ} (hc : 0 < c) :
    X * exp (-(c * X)) ≤ 2 / c * exp (-(c * X / 2)) := by
  have hsplit : exp (-(c * X)) = exp (-(c * X / 2)) * exp (-(c * X / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 : c * X / 2 * exp (-(c * X / 2)) ≤ 1 := by
    have := mul_exp_neg_half_le_two (c * X)
    have e : c * X * exp (-(c * X / 2)) = 2 * (c * X / 2 * exp (-(c * X / 2))) := by ring
    linarith
  have hcc : 2 / c * (c / 2) = 1 := by field_simp
  calc X * exp (-(c * X))
      = 2 / c * (c * X / 2 * exp (-(c * X / 2))) * exp (-(c * X / 2)) := by
        rw [hsplit]
        linear_combination (-(X * exp (-(c * X / 2)) * exp (-(c * X / 2)))) * hcc
    _ ≤ 2 / c * 1 * exp (-(c * X / 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) (exp_pos _).le
    _ = _ := by ring

theorem clamp_pos {s : ℝ} (hs : 0 < s) : 0 < clamp s := lt_min one_pos (lt_max_of_lt_right hs)

theorem clamp_lt_one {s : ℝ} (hs : s < 1) : clamp s < 1 :=
  (min_le_right _ _).trans_lt (max_lt one_pos hs)

theorem gA_pos {y : ℝ} (hy : y ^ 2 < 4) : 0 < gA y :=
  clamp_pos (div_pos (by linarith) (by positivity))

theorem hB_pos {x : ℝ} (hx : 3 * x ^ 2 < 2) : 0 < hB x := by
  unfold hB
  have : (4 * x ^ 2 - 1) / (x ^ 2 + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  linarith [clamp_lt_one this]

theorem volume_pi_Ioo_fin_one_pos {c : ℝ} (hc : 0 < c) :
    0 < volume (Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) c) := by
  rw [Real.volume_pi_Ioo, Fin.prod_univ_one, sub_zero]
  exact ENNReal.ofReal_pos.mpr hc

theorem facePt_atAlphaA (u : Fin 1 → ℝ) : facePt atAlphaA u = u := by
  funext j
  simp [facePt, atAlphaA]

/-! ### Chart `A` at `γ = 1/2` -/

theorem atA_feasible_half :
    ConstrainedFeasible (atData.Qexp iA) (atPhase.kappa iA) (1 / 2) (atPhase.phaseExp iA (1 / 2))
      atAlphaA := by
  refine ⟨fun _ ↦ le_rfl, ?_, ?_⟩
  · simp only [atA_Qexp, zero_mul, Finset.sum_const_zero]
    norm_num
  · simp only [atA_kappa, zero_mul, Finset.sum_const_zero, atA_phaseExp]
    norm_num

theorem atA_limitDomain_half :
    limitDomain (atData.ρ iA) (atData.constD iA σ) (1 / 2) (atData.q iA (atData.k iA))
        (atData.Qexp iA) atAlphaA = Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 4 := by
  ext u
  simp only [limitDomain, mem_inter_iff, Set.mem_univ_pi, mem_ofPred_eq, atA_Qexp, zero_mul,
    Finset.sum_const_zero, atAlphaA, if_true, atData_ρ_iA]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun h0 ↦ absurd h0 (by norm_num)⟩⟩

theorem atA_limitCut_half (u : Fin 1 → ℝ) :
    limitCut (atData.constD iA σ) (1 / 2) (atData.q iA (atData.k iA)) (atData.Qexp iA) atAlphaA
      u = 0 := by
  unfold limitCut
  simp only [atA_Qexp, zero_mul, Finset.sum_const_zero]
  rw [if_neg (by norm_num)]

theorem atA_limitBranchPt_half (u : Fin 1 → ℝ) :
    atData.limitBranchPt iA ε b σ (1 / 2) atAlphaA u = ![0, bsign (ε 0) * u 0] := by
  unfold TruthChartsData.limitBranchPt TruthChartsData.bridgePt
  rw [facePt_atAlphaA, atA_limitCut_half, mul_zero, atData_k_iA]
  funext j
  revert j
  rw [Fin.forall_iff_succAbove (0 : Fin 2)]
  refine ⟨by rw [Fin.insertNth_apply_same]; simp, fun j ↦ ?_⟩
  rw [Fin.insertNth_apply_succAbove, Fin.fin_one_eq_zero j]
  simp [orth]

theorem repA_of_zero (y : ℝ) : repA ![0, y] = 0 := by
  funext j
  revert j
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;> simp [repA_zero, repA_one]

theorem atA_faceMap_half (u : Fin 1 → ℝ) :
    atData.faceMap iA ε b σ (1 / 2) atAlphaA u = 0 := by
  unfold TruthChartsData.faceMap
  rw [atA_limitBranchPt_half, atData_rep_iA, repA_of_zero]

theorem atA_limitUnit_half (u : Fin 1 → ℝ) :
    atPhase.limitUnit iA ε b σ (1 / 2) atAlphaA u = 1 + u 0 ^ 2 := by
  unfold TruthChartsData.Phase.limitUnit
  rw [atA_limitBranchPt_half, atPhase_a_zero]
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [mul_pow, show bsign (ε 0) ^ 2 = 1 by rw [sq, bsign_mul_self], one_mul,
    abs_of_pos (by positivity)]

theorem atA_dsProfile_half (u : Fin 1 → ℝ) :
    dsProfile (atData.ρ iA) (atPhase.constB iA σ) (atData.constD iA σ) (1 / 2)
        (atData.q iA (atData.k iA)) (atPhase.phaseExp iA (1 / 2)) (atData.Qexp iA)
        (atPhase.kappa iA) atAlphaA (atPhase.limitUnit iA ε b σ (1 / 2) atAlphaA) u =
      (Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 4).indicator (fun u ↦ σ ^ 2 * (1 + u 0 ^ 2)) u := by
  unfold dsProfile
  rw [atA_limitDomain_half]
  have htied : ∑ j, atPhase.kappa iA j * atAlphaA j = atPhase.phaseExp iA (1 / 2) := by
    simp only [atA_kappa, zero_mul, Finset.sum_const_zero, atA_phaseExp]
    norm_num
  have hB : atPhase.constB iA σ = σ ^ 2 := by
    unfold TruthChartsData.Phase.constB
    rw [atA_nu, Real.rpow_two, sq_abs]
  by_cases hu : u ∈ Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 4
  · rw [if_pos hu, if_pos htied, Set.indicator_of_mem hu]
    simp only [hB, atA_limitUnit_half, atA_kappa, Fin.prod_univ_one, Real.rpow_zero, mul_one]
  · rw [if_neg hu, Set.indicator_of_notMem hu]

theorem atA_profile_half : atPhase.ProfileIntegrableOf iA ε b σ (1 / 2) atAlphaA := by
  have hc0 : 0 ≤ atPhase.ma iA / atPhase.Ma iA := by
    rw [atPhase_ma, show atPhase.Ma iA = 17 from rfl]
    norm_num
  have hbox : MeasurableSet (Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 4) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have hvol : volume (Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 4) ≠ ∞ := by
    rw [Real.volume_pi_Ioo]
    exact ENNReal.prod_ne_top fun _ _ ↦ ENNReal.ofReal_ne_top
  have henv : ∀ u, dsEnvelope (atData.ρ iA) (atData.constD iA σ) (1 / 2)
      (atData.q iA (atData.k iA)) (atData.Qexp iA) (atPhase.rExp iA) atAlphaA 1 u =
      (Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 4).indicator (fun _ ↦ (1 : ℝ)) u := by
    intro u
    unfold dsEnvelope
    rw [atA_limitDomain_half, one_mul]
    simp [atA_rExp]
  refine ⟨?_, ?_⟩
  · have key : (fun u : Fin 1 → ℝ ↦
        dsEnvelope (atData.ρ iA) (atData.constD iA σ) (1 / 2) (atData.q iA (atData.k iA))
            (atData.Qexp iA) (atPhase.rExp iA) atAlphaA 1 u *
          exp (-(atPhase.ma iA / atPhase.Ma iA * dsProfile (atData.ρ iA) (atPhase.constB iA σ)
            (atData.constD iA σ) (1 / 2) (atData.q iA (atData.k iA)) (atPhase.phaseExp iA (1 / 2))
              (atData.Qexp iA) (atPhase.kappa iA) atAlphaA
              (atPhase.limitUnit iA ε b σ (1 / 2) atAlphaA) u))) =
        (Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 4).indicator
          (fun u ↦ exp (-(atPhase.ma iA / atPhase.Ma iA * (σ ^ 2 * (1 + u 0 ^ 2))))) := by
      funext u
      rw [henv, atA_dsProfile_half]
      by_cases hu : u ∈ Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 4
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, Set.indicator_of_mem hu, one_mul]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, Set.indicator_of_notMem hu,
          zero_mul]
    rw [key]
    refine (integrable_indicator_iff hbox).mpr (Measure.integrableOn_of_bounded (M := 1) hvol
      (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun u ↦ ?_))
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hc0 (by positivity)))
  · have key : (fun u : Fin 1 → ℝ ↦
        dsEnvelope (atData.ρ iA) (atData.constD iA σ) (1 / 2) (atData.q iA (atData.k iA))
            (atData.Qexp iA) (atPhase.rExp iA) atAlphaA 1 u *
          (dsProfile (atData.ρ iA) (atPhase.constB iA σ) (atData.constD iA σ) (1 / 2)
              (atData.q iA (atData.k iA)) (atPhase.phaseExp iA (1 / 2)) (atData.Qexp iA)
              (atPhase.kappa iA) atAlphaA (atPhase.limitUnit iA ε b σ (1 / 2) atAlphaA) u *
            exp (-(atPhase.ma iA / atPhase.Ma iA * dsProfile (atData.ρ iA) (atPhase.constB iA σ)
              (atData.constD iA σ) (1 / 2) (atData.q iA (atData.k iA))
                (atPhase.phaseExp iA (1 / 2)) (atData.Qexp iA) (atPhase.kappa iA) atAlphaA
                (atPhase.limitUnit iA ε b σ (1 / 2) atAlphaA) u)))) =
        (Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 4).indicator (fun u ↦ σ ^ 2 * (1 + u 0 ^ 2) *
          exp (-(atPhase.ma iA / atPhase.Ma iA * (σ ^ 2 * (1 + u 0 ^ 2))))) := by
      funext u
      rw [henv, atA_dsProfile_half]
      by_cases hu : u ∈ Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 4
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, Set.indicator_of_mem hu, one_mul]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, Set.indicator_of_notMem hu,
          zero_mul]
    rw [key]
    refine (integrable_indicator_iff hbox).mpr (Measure.integrableOn_of_bounded
      (M := σ ^ 2 * 17) hvol (Continuous.aestronglyMeasurable (by fun_prop))
      ((ae_restrict_iff' hbox).2 (ae_of_all _ fun u hu ↦ ?_)))
    have hu0 : u 0 ∈ Ioo (0 : ℝ) 4 := Set.mem_univ_pi.mp hu 0
    have hu2 : u 0 ^ 2 ≤ 16 := by nlinarith [hu0.1, hu0.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc σ ^ 2 * (1 + u 0 ^ 2) * exp (-(atPhase.ma iA / atPhase.Ma iA * (σ ^ 2 * (1 + u 0 ^ 2))))
        ≤ σ ^ 2 * 17 * 1 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg σ))
            (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hc0 (by positivity))))
            (exp_pos _).le (by positivity)
      _ = σ ^ 2 * 17 := mul_one _

/-! ### Chart `B` at `γ = 1/2` -/

theorem bsAlpha_half : bsAlpha (1 / 2) = atAlphaA := by
  funext j
  simp [bsAlpha, atAlphaA]

theorem atB_feasible_half :
    ConstrainedFeasible (atData.Qexp iB) (atPhase.kappa iB) (1 / 2) (atPhase.phaseExp iB (1 / 2))
      atAlphaA := by
  refine ⟨fun _ ↦ le_rfl, ?_, ?_⟩
  · simp only [atB_Qexp, atAlphaA, mul_zero, Finset.sum_const_zero]
    norm_num
  · simp only [atB_kappa, atAlphaA, mul_zero, Finset.sum_const_zero, atB_phaseExp]
    norm_num

theorem atB_limitDomain_half :
    limitDomain (atData.ρ iB) (atData.constD iB σ) (1 / 2) (atData.q iB (atData.k iB))
        (atData.Qexp iB) atAlphaA = Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 2 := by
  ext u
  simp only [limitDomain, mem_inter_iff, Set.mem_univ_pi, mem_ofPred_eq, atB_Qexp, atAlphaA,
    mul_zero, Finset.sum_const_zero, if_true, atData_ρ_iB]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun h0 ↦ absurd h0 (by norm_num)⟩⟩

theorem atB_limitCut_half (u : Fin 1 → ℝ) :
    limitCut (atData.constD iB σ) (1 / 2) (atData.q iB (atData.k iB)) (atData.Qexp iB) atAlphaA
      u = 0 := by
  unfold limitCut
  simp only [atB_Qexp, atAlphaA, mul_zero, Finset.sum_const_zero]
  rw [if_neg (by norm_num)]

theorem atB_limitBranchPt_half (u : Fin 1 → ℝ) :
    atData.limitBranchPt iB ε b σ (1 / 2) atAlphaA u = ![bsign (ε 0) * u 0, 0] := by
  unfold TruthChartsData.limitBranchPt TruthChartsData.bridgePt
  rw [facePt_atAlphaA, atB_limitCut_half, mul_zero, atData_k_iB]
  funext j
  revert j
  rw [Fin.forall_iff_succAbove (1 : Fin 2)]
  refine ⟨by rw [Fin.insertNth_apply_same]; simp, fun j ↦ ?_⟩
  rw [Fin.insertNth_apply_succAbove, Fin.fin_one_eq_zero j]
  simp [orth]

theorem bsRep_of_zero (x : ℝ) : bsRep ![x, 0] = 0 := by
  funext j
  revert j
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;> simp [bsRep_zero, bsRep_one]

theorem atB_faceMap_half (u : Fin 1 → ℝ) :
    atData.faceMap iB ε b σ (1 / 2) atAlphaA u = 0 := by
  unfold TruthChartsData.faceMap
  rw [atB_limitBranchPt_half, atData_rep_iB, bsRep_of_zero]

theorem atB_limitUnit_half (u : Fin 1 → ℝ) :
    atPhase.limitUnit iB ε b σ (1 / 2) atAlphaA u = 1 + u 0 ^ 2 := by
  unfold TruthChartsData.Phase.limitUnit
  rw [atB_limitBranchPt_half, atPhase_a_one]
  simp only [Matrix.cons_val_zero]
  rw [mul_pow, show bsign (ε 0) ^ 2 = 1 by rw [sq, bsign_mul_self], one_mul,
    abs_of_pos (by positivity)]

theorem atB_dsProfile_half (u : Fin 1 → ℝ) :
    dsProfile (atData.ρ iB) (atPhase.constB iB σ) (atData.constD iB σ) (1 / 2)
        (atData.q iB (atData.k iB)) (atPhase.phaseExp iB (1 / 2)) (atData.Qexp iB)
        (atPhase.kappa iB) atAlphaA (atPhase.limitUnit iB ε b σ (1 / 2) atAlphaA) u =
      (Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 2).indicator
        (fun u ↦ σ ^ 2 * (1 + u 0 ^ 2) * u 0 ^ (-2 : ℝ)) u := by
  unfold dsProfile
  rw [atB_limitDomain_half]
  have htied : ∑ j, atPhase.kappa iB j * atAlphaA j = atPhase.phaseExp iB (1 / 2) := by
    simp only [atB_kappa, atAlphaA, mul_zero, Finset.sum_const_zero, atB_phaseExp]
    norm_num
  by_cases hu : u ∈ Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 2
  · rw [if_pos hu, if_pos htied, Set.indicator_of_mem hu]
    simp only [atB_constB, atB_limitUnit_half, atB_kappa, Fin.prod_univ_one]
  · rw [if_neg hu, Set.indicator_of_notMem hu]

/-- The one-dimensional dominating profile `x^{-2} e^{-c x^{-2}}` on the half line. -/
theorem integrable_invProfile' {c : ℝ} (hc : 0 < c) : Integrable (invProfile c) := by
  unfold invProfile
  refine (integrable_indicator_iff measurableSet_Ioi).mpr ?_
  exact integrableOn_rpow_mul_exp_neg_mul_rpow_of_neg (p := -2) (s := -2) (by norm_num)
    (by norm_num) hc

theorem atB_profile_half (hσ : σ ≠ 0) : atPhase.ProfileIntegrableOf iB ε b σ (1 / 2) atAlphaA := by
  have hbox : MeasurableSet (Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 2) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  set c : ℝ := atPhase.ma iB / atPhase.Ma iB with hc
  have hcpos : 0 < c := by rw [hc, atPhase_ma, atPhase_Ma_one]; norm_num
  have hσ2 : 0 < σ ^ 2 := by positivity
  have henv : ∀ u, dsEnvelope (atData.ρ iB) (atData.constD iB σ) (1 / 2)
      (atData.q iB (atData.k iB)) (atData.Qexp iB) (atPhase.rExp iB) atAlphaA 1 u =
      (Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 2).indicator (fun u ↦ u 0 ^ (-2 : ℝ)) u := by
    intro u
    unfold dsEnvelope
    rw [atB_limitDomain_half, one_mul]
    simp [atB_rExp]
  have hmeasP : Measurable (dsProfile (atData.ρ iB) (atPhase.constB iB σ) (atData.constD iB σ)
      (1 / 2) (atData.q iB (atData.k iB)) (atPhase.phaseExp iB (1 / 2)) (atData.Qexp iB)
      (atPhase.kappa iB) atAlphaA (atPhase.limitUnit iB ε b σ (1 / 2) atAlphaA)) :=
    measurable_dsProfile atPhase.measurable_limitUnit
  have hmeasE : Measurable (dsEnvelope (atData.ρ iB) (atData.constD iB σ) (1 / 2)
      (atData.q iB (atData.k iB)) (atData.Qexp iB) (atPhase.rExp iB) atAlphaA 1) :=
    measurable_dsEnvelope_one _ _ _ _ _ _ _
  -- the pointwise bounds on the box
  have hbound : ∀ u ∈ (Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 2), ∀ κ' : ℝ, 0 < κ' →
      exp (-(κ' * (σ ^ 2 * (1 + u 0 ^ 2) * u 0 ^ (-2 : ℝ)))) ≤
        exp (-(κ' * σ ^ 2) * u 0 ^ (-2 : ℝ)) := by
    intro u hu κ' hκ'
    have hu0 : 0 < u 0 := (Set.mem_univ_pi.mp hu 0).1
    have hp : 0 < u 0 ^ (-2 : ℝ) := rpow_pos_of_pos hu0 _
    refine Real.exp_le_exp.mpr ?_
    have : κ' * σ ^ 2 * u 0 ^ (-2 : ℝ) ≤ κ' * (σ ^ 2 * (1 + u 0 ^ 2) * u 0 ^ (-2 : ℝ)) := by
      have h1 : σ ^ 2 * u 0 ^ (-2 : ℝ) ≤ σ ^ 2 * (1 + u 0 ^ 2) * u 0 ^ (-2 : ℝ) := by
        nlinarith [mul_nonneg (mul_nonneg hσ2.le (sq_nonneg (u 0))) hp.le]
      nlinarith [mul_le_mul_of_nonneg_left h1 hκ'.le]
    linarith
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' (integrable_comp_zero (integrable_invProfile' (mul_pos hcpos hσ2)))
      ((hmeasE.mul (Real.measurable_exp.comp
        ((measurable_const.mul hmeasP).neg))).aestronglyMeasurable)
      (ae_of_all _ fun u ↦ ?_)
    rw [henv, atB_dsProfile_half]
    unfold invProfile
    by_cases hu : u ∈ Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 2
    · have hu0 : 0 < u 0 := (Set.mem_univ_pi.mp hu 0).1
      rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, Set.indicator_of_mem (mem_Ioi.mpr hu0),
        Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (rpow_nonneg hu0.le _) (exp_pos _).le)]
      exact mul_le_mul_of_nonneg_left (hbound u hu c hcpos) (rpow_nonneg hu0.le _)
    · rw [Set.indicator_of_notMem hu, zero_mul, norm_zero]
      exact Set.indicator_nonneg (fun x hx ↦ mul_nonneg (rpow_nonneg (le_of_lt hx) _)
        (exp_pos _).le) _
  · refine Integrable.mono' ((integrable_comp_zero
      (integrable_invProfile' (mul_pos (half_pos hcpos) hσ2))).const_mul (2 / c))
      ((hmeasE.mul (hmeasP.mul (Real.measurable_exp.comp
        ((measurable_const.mul hmeasP).neg)))).aestronglyMeasurable)
      (ae_of_all _ fun u ↦ ?_)
    rw [henv, atB_dsProfile_half]
    unfold invProfile
    by_cases hu : u ∈ Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) 2
    · have hu0 : 0 < u 0 := (Set.mem_univ_pi.mp hu 0).1
      have hX : 0 ≤ σ ^ 2 * (1 + u 0 ^ 2) * u 0 ^ (-2 : ℝ) := by positivity
      rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, Set.indicator_of_mem (mem_Ioi.mpr hu0),
        Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (rpow_nonneg hu0.le _)
          (mul_nonneg hX (exp_pos _).le))]
      have h1 := mul_exp_neg_le_two_div (X := σ ^ 2 * (1 + u 0 ^ 2) * u 0 ^ (-2 : ℝ)) hcpos
      have h2 := hbound u hu (c / 2) (half_pos hcpos)
      have e : -(c / 2 * (σ ^ 2 * (1 + u 0 ^ 2) * u 0 ^ (-2 : ℝ))) =
          -(c * (σ ^ 2 * (1 + u 0 ^ 2) * u 0 ^ (-2 : ℝ)) / 2) := by ring
      rw [e] at h2
      have e2 : -(c / 2 * σ ^ 2) * u 0 ^ (-2 : ℝ) = -(c / 2 * σ ^ 2 * u 0 ^ (-2 : ℝ)) := by ring
      calc u 0 ^ (-2 : ℝ) * (σ ^ 2 * (1 + u 0 ^ 2) * u 0 ^ (-2 : ℝ) *
            exp (-(c * (σ ^ 2 * (1 + u 0 ^ 2) * u 0 ^ (-2 : ℝ)))))
          ≤ u 0 ^ (-2 : ℝ) * (2 / c * exp (-(c * σ ^ 2 * (1 + u 0 ^ 2) * u 0 ^ (-2 : ℝ) / 2))) := by
            refine mul_le_mul_of_nonneg_left ?_ (rpow_nonneg hu0.le _)
            calc _ ≤ 2 / c * exp (-(c * (σ ^ 2 * (1 + u 0 ^ 2) * u 0 ^ (-2 : ℝ)) / 2)) := h1
              _ = _ := by ring_nf
        _ ≤ u 0 ^ (-2 : ℝ) * (2 / c * exp (-(c / 2 * σ ^ 2) * u 0 ^ (-2 : ℝ))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
              (rpow_nonneg hu0.le _)
            calc _ = exp (-(c * (σ ^ 2 * (1 + u 0 ^ 2) * u 0 ^ (-2 : ℝ)) / 2)) := by ring_nf
              _ ≤ _ := h2
        _ = 2 / c * (u 0 ^ (-2 : ℝ) * exp (-(c / 2 * σ ^ 2) * u 0 ^ (-2 : ℝ))) := by ring
    · rw [Set.indicator_of_notMem hu, zero_mul, norm_zero]
      exact mul_nonneg (by positivity) (Set.indicator_nonneg (fun x hx ↦
        mul_nonneg (rpow_nonneg (le_of_lt hx) _) (exp_pos _).le) _)

/-! ### Positivity of the dominant mass -/

theorem atB_limitWeight_half_pos (φ : (Fin 2 → ℝ) → ℝ) (hφ0 : 0 < φ 0) {u : Fin 1 → ℝ}
    (hu : u ∈ Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) (1 / 2)) :
    0 < atPhase.limitWeight iB φ ε b σ (1 / 2) atAlphaA u := by
  unfold TruthChartsData.Phase.limitWeight
  rw [atB_limitBranchPt_half, atData_rep_iB, bsRep_of_zero, atPhase_wt_one, atPhase_b, abs_one,
    mul_one]
  have hu0 : u 0 ∈ Ioo (0 : ℝ) (1 / 2) := Set.mem_univ_pi.mp hu 0
  refine mul_pos hφ0 (mul_pos ?_ ?_)
  · simp only [Matrix.cons_val_zero]
    refine hB_pos ?_
    rw [mul_pow, show bsign (ε 0) ^ 2 = 1 by rw [sq, bsign_mul_self], one_mul]
    nlinarith [hu0.1, hu0.2]
  · rw [bsCut_eq_one]
    · exact one_pos
    · rw [pi_norm_le_iff_of_nonneg zero_le_one]
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · simp only [Matrix.cons_val_zero, Real.norm_eq_abs, abs_mul, abs_bsign, one_mul,
          abs_of_pos hu0.1]
        linarith [hu0.2]
      · simp

/-! ### The assembled limit -/

theorem at_termLam_half (p : TruthChartsData.Phase.TermIdx atData) :
    atPhase.termLam (1 / 2) (fun i _ _ ↦ atAlpha (1 / 2) i) p = 1 / 2 := by
  rw [at_termLam]
  split_ifs <;> rfl

open scoped Classical in
/-- **Two leading charts.** At `γ = 1/2` both charts of the blow-up atlas are dominant with
exponent `1/2`, every dominant face map is the origin, and the expectation along the fibre
converges to `ψ(0)/χ(0)`. -/
theorem at_tendsto_fibre_expectation_half (hσ : 0 < σ)
    {ψ χ : (Fin 2 → ℝ) → ℝ} (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z) {Mψ : ℝ}
    (hMψ : ∀ z, ψ z ≤ Mψ) (hψL : ∀ z, ψ z ≠ 0 → z ∈ atL') (hχc : Continuous χ)
    (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ} (hMχ : ∀ z, χ z ≤ Mχ) (hχL : ∀ z, χ z ≠ 0 → z ∈ atL')
    (hχ0 : 0 < χ 0) :
    Tendsto (fun t ↦
        (atData.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * bsF z)) * ψ z))
          (σ * t ^ (-(1 / 2 : ℝ)))).toReal /
        (atData.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * bsF z)) * χ z))
          (σ * t ^ (-(1 / 2 : ℝ)))).toReal) atTop (𝓝 (ψ 0 / χ 0)) := by
  have hS : ∀ i, |atData.S i| = 1 := fun i ↦ by rw [atData_S, abs_one]
  have hF : ∀ z, 0 ≤ bsF z := fun z ↦ by unfold bsF; positivity
  have hFm : Measurable bsF := by unfold bsF; fun_prop
  have htruth : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin 2 → ℝ) (atData.ρ i),
      atData.rep i u 0 = truthMono (atData.S i) (atData.q i) u := fun i u _ ↦ at_truth i u
  have hfeas : ∀ i ε b, atData.admissible i ε b σ →
      ConstrainedFeasible (atData.Qexp i) (atPhase.kappa i) (1 / 2) (atPhase.phaseExp i (1 / 2))
        (atAlpha (1 / 2) i) := by
    refine forall_index.mpr ⟨fun _ _ _ ↦ ?_, fun _ _ _ ↦ ?_⟩
    · rw [atAlpha_iA]; exact atA_feasible_half
    · rw [atAlpha_iB, bsAlpha_half]; exact atB_feasible_half
  have hprof : ∀ i ε b, atData.admissible i ε b σ →
      atPhase.ProfileIntegrableOf i ε b σ (1 / 2) (atAlpha (1 / 2) i) := by
    refine forall_index.mpr ⟨fun ε b _ ↦ ?_, fun ε b _ ↦ ?_⟩
    · rw [atAlpha_iA]; exact atA_profile_half ε b σ
    · rw [atAlpha_iB, bsAlpha_half]; exact atB_profile_half ε b σ hσ.ne'
  have hmin : ∀ p : TruthChartsData.Phase.TermIdx atData,
      1 / 2 ≤ atPhase.termLam (1 / 2) (fun i _ _ ↦ atAlpha (1 / 2) i) p := fun p ↦ by
    rw [at_termLam_half]
  have hpt : ∀ p ∈ atPhase.dominantTerms σ (1 / 2) (fun i _ _ ↦ atAlpha (1 / 2) i) (1 / 2),
      ∀ u ∈ limitDomain (atData.ρ p.1) (atData.constD p.1 σ) (1 / 2)
        (atData.q p.1 (atData.k p.1)) (atData.Qexp p.1) (atAlpha (1 / 2) p.1),
        atData.faceMap p.1 p.2.1 p.2.2 σ (1 / 2) (atAlpha (1 / 2) p.1) u = 0 := by
    intro p hp u hu
    clear hp hu
    obtain ⟨i, ε, b⟩ := p
    dsimp only
    revert i
    refine forall_index.mpr ⟨?_, ?_⟩
    · rw [atAlpha_iA]; exact atA_faceMap_half ε b σ u
    · rw [atAlpha_iB, bsAlpha_half]; exact atB_faceMap_half ε b σ u
  -- the dominant mass is positive: the `+` branch of chart `B`
  set p₀ : TruthChartsData.Phase.TermIdx atData := (iB, fun _ ↦ true, true) with hp₀
  have hp₀mem : p₀ ∈ atPhase.dominantTerms σ (1 / 2) (fun i _ _ ↦ atAlpha (1 / 2) i) (1 / 2) := by
    unfold TruthChartsData.Phase.dominantTerms
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, at_termLam_half p₀, atB_admissible_true σ hσ⟩
  have hprof₀ := hprof iB (fun _ ↦ true) true (atB_admissible_true σ hσ)
  have hmass : atPhase.limitMeasure σ (1 / 2) (fun i _ _ ↦ atAlpha (1 / 2) i) (1 / 2) univ ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le ?_ (atPhase.termMeasure_le_limitMeasure σ (1 / 2)
      (fun i _ _ ↦ atAlpha (1 / 2) i) (1 / 2) hp₀mem univ))
    rw [atPhase.termMeasure_univ hσ.ne' hprof₀]
    refine ENNReal.ofReal_pos.mpr ?_
    refine atPhase.termConst_pos_of_subset hσ.ne' measurable_const (fun _ ↦ zero_le_one)
      (Mφ := 1) (fun _ ↦ le_rfl) hprof₀ (V := Set.pi univ fun _ : Fin 1 ↦ Ioo (0 : ℝ) (1 / 2))
      ?_ ?_ (volume_pi_Ioo_fin_one_pos (by norm_num))
    · rw [show atAlpha (1 / 2) iB = atAlphaA by rw [atAlpha_iB, bsAlpha_half],
        atB_limitDomain_half]
      exact fun u hu ↦ Set.mem_univ_pi.mpr fun j ↦
        ⟨(Set.mem_univ_pi.mp hu j).1, (Set.mem_univ_pi.mp hu j).2.trans (by norm_num)⟩
    · intro u hu
      rw [show atAlpha (1 / 2) iB = atAlphaA by rw [atAlpha_iB, bsAlpha_half]]
      exact atB_limitWeight_half_pos _ _ σ (fun _ ↦ (1 : ℝ)) one_pos hu
  exact atPhase.tendsto_fibre_expectation_point hS hF hFm htruth hσ.ne' hψc hψ hMψ hψL hχc hχ hMχ
    hχL hfeas hprof hmin hpt hχ0.ne' hmass

end Laplace.Multi.BlowupAtlas
