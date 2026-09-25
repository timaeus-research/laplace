/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ToyWallRecord
import Laplace.Multi.WallFibreExpectation

/-!
# The toy wall record through the analytic layer

The constants of the toy chart (`ToyWallRecord`) for `F = (1 + x²) s² x²` along `s = σ t^{-γ}`,
`0 < γ < 1/2`: `q_k = 1`, `Q = 0`, `ν = 2`, `κ = 2`, `p = 0`, `r = 0`, `δ = 1 − 2γ`, `A = 1`,
`B = σ²`, `D = |σ|`; the scale `α = (1 − 2γ)/2` is feasible with the phase constraint tied and the
truth constraint strict; the limiting branch point is the origin, so the limiting unit is `1` and
the limiting weight is `φ(0)`; the limiting profile is `σ² u²` on `(0, ∞)`. The certificate
hypotheses of `tendsto_fibre_expectation` are all verified, and the expectation along the fibre
converges to `ψ(0)/χ(0)` (`toy_tendsto_fibre_expectation`): for this loss, the observable
localises at the wall point at the scale `x ~ t^{-(1-2γ)/2}`, with
`∫_{fibre} e^{-tF} φ ~ φ(0) √π/|σ| · t^{-(1−2γ)/2}`.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi.ToyWall

variable (i : toyData.ι) (ε : Fin 1 → Bool) (b : Bool) (σ γ : ℝ)

/-! ### The constants of the toy chart -/

theorem toyPhase_kF (i : toyData.ι) : toyPhase.kF i = ![2, 2] := rfl
theorem toyPhase_hJ (i : toyData.ι) : toyPhase.hJ i = ![0, 0] := rfl
theorem toyPhase_a (i : toyData.ι) (u : Fin 2 → ℝ) : toyPhase.a i u = 1 + u 1 ^ 2 := rfl
theorem toyPhase_b (i : toyData.ι) (u : Fin 2 → ℝ) : toyPhase.b i u = 1 := rfl
theorem toyPhase_wt (i : toyData.ι) (u : Fin 2 → ℝ) : toyPhase.wt i u = toyDens u := rfl
theorem toyPhase_ma (i : toyData.ι) : toyPhase.ma i = 1 := rfl
theorem toyPhase_Ma (i : toyData.ι) : toyPhase.Ma i = 2 := rfl
theorem toyPhase_Mb (i : toyData.ι) : toyPhase.Mb i = 1 := rfl

theorem toy_qk : toyData.q i (toyData.k i) = 1 := rfl

theorem toy_qk_real : (toyData.q i (toyData.k i) : ℝ) = 1 := by rw [toy_qk]; simp

theorem toy_Qexp (j : Fin 1) : toyData.Qexp i j = 0 := by
  unfold TruthChartsData.Qexp
  rw [toyData_q, toyData_k, Fin.zero_succAbove, Fin.fin_one_eq_zero j]
  simp

theorem toy_nu : toyPhase.nu i = 2 := by
  unfold TruthChartsData.Phase.nu
  rw [toyPhase_kF, toyData_q, toyData_k]
  simp

theorem toy_kappa (j : Fin 1) : toyPhase.kappa i j = 2 := by
  unfold TruthChartsData.Phase.kappa
  rw [toyPhase_kF, toyData_q, toyData_k, Fin.zero_succAbove, Fin.fin_one_eq_zero j]
  simp

theorem toy_pExp : toyPhase.pExp i = 0 := by
  unfold TruthChartsData.Phase.pExp
  rw [toyPhase_hJ, toyData_q, toyData_k]
  simp

theorem toy_rExp (j : Fin 1) : toyPhase.rExp i j = 0 := by
  unfold TruthChartsData.Phase.rExp
  rw [toyPhase_hJ, toyData_q, toyData_k, Fin.zero_succAbove, Fin.fin_one_eq_zero j]
  simp

theorem toy_phaseExp : toyPhase.phaseExp i γ = 1 - 2 * γ := by
  unfold TruthChartsData.Phase.phaseExp
  rw [toy_nu]
  ring

theorem toy_constD : toyData.constD i σ = |σ| := by
  unfold TruthChartsData.constD
  rw [toy_qk_real]
  simp

theorem toy_constB : toyPhase.constB i σ = σ ^ 2 := by
  unfold TruthChartsData.Phase.constB
  rw [toy_nu, Real.rpow_two, sq_abs]

theorem toy_constA : toyPhase.constA i σ = 1 := by
  unfold TruthChartsData.Phase.constA
  rw [toy_pExp, toy_qk_real, Real.rpow_zero, div_one]

theorem toy_orthSign : toyData.orthSign i ε = 1 := by
  unfold TruthChartsData.orthSign
  rw [toyData_S, toyData_q, toyData_k]
  simp [Fin.zero_succAbove]

theorem toy_admissible_iff : toyData.admissible i ε b σ ↔ 0 < (if b then 1 else -1) * σ := by
  unfold TruthChartsData.admissible
  rw [toy_orthSign, toy_qk, one_mul, pow_one]

/-- The toy scale `α = (1 − 2γ)/2`. -/
noncomputable def toyAlpha (γ : ℝ) : Fin 1 → ℝ := fun _ ↦ (1 - 2 * γ) / 2

theorem toy_feasible (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ConstrainedFeasible (toyData.Qexp i) (toyPhase.kappa i) γ (toyPhase.phaseExp i γ)
      (toyAlpha γ) := by
  refine ⟨fun _ ↦ by unfold toyAlpha; linarith, ?_, ?_⟩
  · simp only [toy_Qexp, zero_mul, Finset.sum_const_zero]
    exact hγ0.le
  · simp only [toy_kappa, toy_phaseExp, toyAlpha, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, one_smul]
    linarith

theorem toy_lpExponent :
    lpExponent γ (toyPhase.pExp i) (fun j ↦ toyPhase.rExp i j + 1) (toyAlpha γ) =
      (1 - 2 * γ) / 2 := by
  unfold lpExponent toyAlpha
  simp [toy_pExp, toy_rExp]


/-! ### The limiting objects -/

theorem toy_limitDomain (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    limitDomain (toyData.ρ i) (toyData.constD i σ) γ (toyData.q i (toyData.k i)) (toyData.Qexp i)
      (toyAlpha γ) = {u : Fin 1 → ℝ | 0 < u 0} := by
  have hne : (1 - 2 * γ) / 2 ≠ 0 := by linarith
  ext u
  simp only [limitDomain, mem_inter_iff, Set.mem_univ_pi, mem_ofPred_eq, toyAlpha, toy_Qexp,
    zero_mul, Finset.sum_const_zero, hne, if_false, mem_Ioi]
  constructor
  · rintro ⟨h, _⟩
    exact h 0
  · intro h
    exact ⟨fun j ↦ by rw [Fin.fin_one_eq_zero j]; exact h, fun h0 ↦ absurd h0 hγ0.ne⟩

theorem toy_facePt (hγ : γ < 1 / 2) (u : Fin 1 → ℝ) : facePt (toyAlpha γ) u = 0 := by
  have hne : (1 - 2 * γ) / 2 ≠ 0 := by linarith
  funext j
  simp [facePt, toyAlpha, hne]

theorem toy_limitCut (hγ0 : 0 < γ) (u : Fin 1 → ℝ) :
    limitCut (toyData.constD i σ) γ (toyData.q i (toyData.k i)) (toyData.Qexp i) (toyAlpha γ) u =
      0 := by
  unfold limitCut
  simp [toy_Qexp, hγ0.ne]

theorem toy_limitBranchPt (hγ0 : 0 < γ) (hγ : γ < 1 / 2) (u : Fin 1 → ℝ) :
    toyData.limitBranchPt i ε b σ γ (toyAlpha γ) u = 0 := by
  unfold TruthChartsData.limitBranchPt TruthChartsData.bridgePt
  rw [toy_facePt γ hγ u, toy_limitCut i σ γ hγ0 u, mul_zero, toyData_k]
  funext j
  revert j
  rw [Fin.forall_iff_succAbove (0 : Fin 2)]
  refine ⟨by rw [Fin.insertNth_apply_same]; rfl, fun j ↦ ?_⟩
  rw [Fin.insertNth_apply_succAbove]
  simp [orth]

theorem toy_limitUnit (hγ0 : 0 < γ) (hγ : γ < 1 / 2) (u : Fin 1 → ℝ) :
    toyPhase.limitUnit i ε b σ γ (toyAlpha γ) u = 1 := by
  unfold TruthChartsData.Phase.limitUnit
  rw [toy_limitBranchPt i ε b σ γ hγ0 hγ u, toyPhase_a]
  simp

theorem toy_limitWeight (hγ0 : 0 < γ) (hγ : γ < 1 / 2) (φ : (Fin 2 → ℝ) → ℝ) (u : Fin 1 → ℝ) :
    toyPhase.limitWeight i φ ε b σ γ (toyAlpha γ) u = φ 0 := by
  unfold TruthChartsData.Phase.limitWeight
  rw [toy_limitBranchPt i ε b σ γ hγ0 hγ u, toyData_rep, toyPhase_wt, toyPhase_b,
    toyDens_eq_one (by rw [norm_zero]; norm_num)]
  simp

theorem toy_dsProfile (hγ0 : 0 < γ) (hγ : γ < 1 / 2) (u : Fin 1 → ℝ) :
    dsProfile (toyData.ρ i) (toyPhase.constB i σ) (toyData.constD i σ) γ
        (toyData.q i (toyData.k i)) (toyPhase.phaseExp i γ) (toyData.Qexp i) (toyPhase.kappa i)
        (toyAlpha γ) (toyPhase.limitUnit i ε b σ γ (toyAlpha γ)) u =
      if 0 < u 0 then σ ^ 2 * u 0 ^ 2 else 0 := by
  unfold dsProfile
  rw [toy_limitDomain i σ γ hγ0 hγ]
  have h2 : ∑ j : Fin 1, (2 : ℝ) * toyAlpha γ j = 1 - 2 * γ := by
    rw [Fin.sum_univ_one]
    unfold toyAlpha
    ring
  simp only [mem_ofPred_eq, toy_kappa, h2, toy_phaseExp, if_true, toy_constB,
    toy_limitUnit i ε b σ γ hγ0 hγ, mul_one, Fin.prod_univ_one, Real.rpow_two]

theorem toy_dsEnvelope (hγ0 : 0 < γ) (hγ : γ < 1 / 2) (u : Fin 1 → ℝ) :
    dsEnvelope (toyData.ρ i) (toyData.constD i σ) γ (toyData.q i (toyData.k i)) (toyData.Qexp i)
        (toyPhase.rExp i) (toyAlpha γ) 1 u = if 0 < u 0 then 1 else 0 := by
  unfold dsEnvelope
  rw [toy_limitDomain i σ γ hγ0 hγ, Set.indicator_apply]
  simp [toy_rExp]

theorem toy_dsWeight₀ (hγ0 : 0 < γ) (hγ : γ < 1 / 2) (φ : (Fin 2 → ℝ) → ℝ) (u : Fin 1 → ℝ) :
    dsWeight₀ (toyData.ρ i) (toyData.constD i σ) γ (toyData.q i (toyData.k i)) (toyData.Qexp i)
        (toyPhase.rExp i) (toyAlpha γ) (toyPhase.limitWeight i φ ε b σ γ (toyAlpha γ)) u =
      if 0 < u 0 then φ 0 else 0 := by
  unfold dsWeight₀
  rw [toy_limitDomain i σ γ hγ0 hγ, Set.indicator_apply]
  simp [toy_rExp, toy_limitWeight i ε b σ γ hγ0 hγ φ]

/-! ### The profile certificate -/

/-- The one-dimensional Gaussian profile on the half line. -/
noncomputable def halfGauss (c : ℝ) (x : ℝ) : ℝ := (Ioi 0).indicator (fun x ↦ exp (-c * x ^ 2)) x

theorem integrable_halfGauss {c : ℝ} (hc : 0 < c) : Integrable (halfGauss c) :=
  (integrable_exp_neg_mul_sq hc).indicator measurableSet_Ioi

theorem integrable_sq_mul_halfGauss {c : ℝ} (hc : 0 < c) :
    Integrable fun x ↦ (Ioi 0).indicator (fun x ↦ x ^ 2 * exp (-c * x ^ 2)) x := by
  refine Integrable.indicator ?_ measurableSet_Ioi
  have := integrable_rpow_mul_exp_neg_mul_sq hc (s := 2) (by norm_num)
  refine this.congr (Eventually.of_forall fun x ↦ ?_)
  simp only [Real.rpow_two]

/-- Transfer of integrability from `ℝ` to `Fin 1 → ℝ`. -/
theorem integrable_comp_zero {G : ℝ → ℝ} (hG : Integrable G) :
    Integrable fun u : Fin 1 → ℝ ↦ G (u 0) :=
  ((volume_preserving_funUnique (Fin 1) ℝ).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)).mpr hG

theorem integral_comp_zero (G : ℝ → ℝ) : ∫ u : Fin 1 → ℝ, G (u 0) = ∫ x, G x :=
  (volume_preserving_funUnique (Fin 1) ℝ).integral_comp (MeasurableEquiv.measurableEmbedding _) G

theorem toy_profile (hσ : σ ≠ 0) (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    toyPhase.ProfileIntegrableOf i ε b σ γ (toyAlpha γ) where
  int := by
    have key : (fun u : Fin 1 → ℝ ↦
        dsEnvelope (toyData.ρ i) (toyData.constD i σ) γ (toyData.q i (toyData.k i))
            (toyData.Qexp i) (toyPhase.rExp i) (toyAlpha γ) 1 u *
          exp (-(toyPhase.ma i / toyPhase.Ma i * dsProfile (toyData.ρ i) (toyPhase.constB i σ)
            (toyData.constD i σ) γ (toyData.q i (toyData.k i)) (toyPhase.phaseExp i γ)
              (toyData.Qexp i) (toyPhase.kappa i) (toyAlpha γ)
              (toyPhase.limitUnit i ε b σ γ (toyAlpha γ)) u))) =
        fun u ↦ halfGauss (σ ^ 2 / 2) (u 0) := by
      funext u
      rw [toy_dsEnvelope i σ γ hγ0 hγ, toy_dsProfile i ε b σ γ hγ0 hγ, toyPhase_ma, toyPhase_Ma]
      unfold halfGauss
      by_cases h : 0 < u 0
      · rw [if_pos h, if_pos h, Set.indicator_of_mem (mem_Ioi.mpr h), one_mul]
        congr 1
        ring
      · rw [if_neg h, if_neg h, Set.indicator_of_notMem (fun h' ↦ h (mem_Ioi.mp h')), zero_mul]
    rw [key]
    exact integrable_comp_zero (integrable_halfGauss (by positivity))
  Φint := by
    have key : (fun u : Fin 1 → ℝ ↦
        dsEnvelope (toyData.ρ i) (toyData.constD i σ) γ (toyData.q i (toyData.k i))
            (toyData.Qexp i) (toyPhase.rExp i) (toyAlpha γ) 1 u *
          (dsProfile (toyData.ρ i) (toyPhase.constB i σ) (toyData.constD i σ) γ
              (toyData.q i (toyData.k i)) (toyPhase.phaseExp i γ) (toyData.Qexp i)
              (toyPhase.kappa i) (toyAlpha γ) (toyPhase.limitUnit i ε b σ γ (toyAlpha γ)) u *
            exp (-(toyPhase.ma i / toyPhase.Ma i * dsProfile (toyData.ρ i) (toyPhase.constB i σ)
              (toyData.constD i σ) γ (toyData.q i (toyData.k i)) (toyPhase.phaseExp i γ)
                (toyData.Qexp i) (toyPhase.kappa i) (toyAlpha γ)
                (toyPhase.limitUnit i ε b σ γ (toyAlpha γ)) u)))) =
        fun u ↦ σ ^ 2 * (Ioi 0).indicator (fun x ↦ x ^ 2 * exp (-(σ ^ 2 / 2) * x ^ 2)) (u 0) := by
      funext u
      rw [toy_dsEnvelope i σ γ hγ0 hγ, toy_dsProfile i ε b σ γ hγ0 hγ, toyPhase_ma, toyPhase_Ma]
      by_cases h : 0 < u 0
      · rw [if_pos h, if_pos h, Set.indicator_of_mem (mem_Ioi.mpr h), one_mul]
        have e : -(1 / 2 * (σ ^ 2 * u 0 ^ 2)) = -(σ ^ 2 / 2) * u 0 ^ 2 := by ring
        rw [e]
        ring
      · rw [if_neg h, if_neg h, Set.indicator_of_notMem (fun h' ↦ h (mem_Ioi.mp h')), zero_mul,
          mul_zero]
    rw [key]
    exact (integrable_comp_zero (integrable_sq_mul_halfGauss (by positivity))).const_mul _

/-! ### The constants and the limit -/

theorem toy_termConst (hγ0 : 0 < γ) (hγ : γ < 1 / 2) (φ : (Fin 2 → ℝ) → ℝ) :
    toyPhase.termConst i φ ε b σ γ (toyAlpha γ) = φ 0 * (√(π / σ ^ 2) / 2) := by
  unfold TruthChartsData.Phase.termConst
  rw [toy_constA, one_mul]
  have key : (fun u : Fin 1 → ℝ ↦
      dsWeight₀ (toyData.ρ i) (toyData.constD i σ) γ (toyData.q i (toyData.k i)) (toyData.Qexp i)
          (toyPhase.rExp i) (toyAlpha γ) (toyPhase.limitWeight i φ ε b σ γ (toyAlpha γ)) u *
        exp (-dsProfile (toyData.ρ i) (toyPhase.constB i σ) (toyData.constD i σ) γ
          (toyData.q i (toyData.k i)) (toyPhase.phaseExp i γ) (toyData.Qexp i) (toyPhase.kappa i)
          (toyAlpha γ) (toyPhase.limitUnit i ε b σ γ (toyAlpha γ)) u)) =
      fun u ↦ φ 0 * halfGauss (σ ^ 2) (u 0) := by
    funext u
    rw [toy_dsWeight₀ i ε b σ γ hγ0 hγ φ, toy_dsProfile i ε b σ γ hγ0 hγ]
    unfold halfGauss
    by_cases h : 0 < u 0
    · rw [if_pos h, if_pos h, Set.indicator_of_mem (mem_Ioi.mpr h), neg_mul]
    · rw [if_neg h, if_neg h, Set.indicator_of_notMem (fun h' ↦ h (mem_Ioi.mp h')), zero_mul,
        mul_zero]
  rw [key, integral_const_mul, integral_comp_zero]
  unfold halfGauss
  rw [integral_indicator measurableSet_Ioi, integral_gaussian_Ioi]

/-- The admissible term for `σ > 0`: the `+V` branch. -/
theorem toy_admissible_true (hσ : 0 < σ) : toyData.admissible i ε true σ := by
  rw [toy_admissible_iff]
  simpa using hσ

theorem toy_truth (i : toyData.ι) (u : Fin 2 → ℝ) :
    toyData.rep i u 0 = truthMono (toyData.S i) (toyData.q i) u := by
  rw [toyData_rep, toyData_S, toyData_q]
  simp [truthMono, Fin.prod_univ_succ]

open scoped Classical in
/-- **The toy expectation along the truth fibre**: for `0 < γ < 1/2` and `σ > 0`, the ratio of the
total kernels of two localised observables converges to `ψ(0)/χ(0)`. -/
theorem toy_tendsto_fibre_expectation (hσ : 0 < σ) (hγ0 : 0 < γ) (hγ : γ < 1 / 2)
    {ψ χ : (Fin 2 → ℝ) → ℝ} (hψc : Continuous ψ) (hψ : ∀ z, 0 ≤ ψ z) {Mψ : ℝ}
    (hMψ : ∀ z, ψ z ≤ Mψ) (hψL : ∀ z, ψ z ≠ 0 → z ∈ toyL') (hχc : Continuous χ)
    (hχ : ∀ z, 0 ≤ χ z) {Mχ : ℝ} (hMχ : ∀ z, χ z ≤ Mχ) (hχL : ∀ z, χ z ≠ 0 → z ∈ toyL')
    (hχ0 : 0 < χ 0) :
    Tendsto (fun t ↦
        (toyData.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * toyF z)) * ψ z))
          (σ * t ^ (-γ))).toReal /
        (toyData.totalKernel (fun z ↦ ENNReal.ofReal (exp (-(t * toyF z)) * χ z))
          (σ * t ^ (-γ))).toReal) atTop (𝓝 (ψ 0 / χ 0)) := by
  have hS : ∀ i, |toyData.S i| = 1 := fun i ↦ by rw [toyData_S, abs_one]
  have hF : ∀ z, 0 ≤ toyF z := fun z ↦ by unfold toyF; positivity
  have hFm : Measurable toyF := by unfold toyF; fun_prop
  have htruth : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin 2 → ℝ) (toyData.ρ i),
      toyData.rep i u 0 = truthMono (toyData.S i) (toyData.q i) u := fun i u _ ↦ toy_truth i u
  set c : ℝ := √(π / σ ^ 2) / 2 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  set Sc : ℝ := ∑ p : TruthChartsData.Phase.TermIdx toyData,
    if toyData.admissible p.1 p.2.1 p.2.2 σ then c else 0 with hSc
  have hScpos : 0 < Sc := by
    have h1 : c ≤ Sc := by
      rw [hSc]
      have := Finset.single_le_sum (f := fun p : TruthChartsData.Phase.TermIdx toyData ↦
        if toyData.admissible p.1 p.2.1 p.2.2 σ then c else 0)
        (fun p _ ↦ by split_ifs <;> positivity)
        (Finset.mem_univ (((), fun _ ↦ true, true) : TruthChartsData.Phase.TermIdx toyData))
      simpa [toy_admissible_true () _ σ hσ] using this
    exact hcpos.trans_le h1
  have hsum : ∀ φ : (Fin 2 → ℝ) → ℝ,
      (∑ p : TruthChartsData.Phase.TermIdx toyData,
        if toyPhase.termLam γ (fun _ _ _ ↦ toyAlpha γ) p = (1 - 2 * γ) / 2 then
          toyPhase.termConst' φ σ γ (fun _ _ _ ↦ toyAlpha γ) p else 0) = φ 0 * Sc := by
    intro φ
    rw [hSc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    have hl : toyPhase.termLam γ (fun _ _ _ ↦ toyAlpha γ) p = (1 - 2 * γ) / 2 := by
      unfold TruthChartsData.Phase.termLam
      exact toy_lpExponent p.1 γ
    rw [if_pos hl]
    unfold TruthChartsData.Phase.termConst'
    split_ifs with hadm
    · rw [toy_termConst _ _ _ σ γ hγ0 hγ φ]
    · rw [mul_zero]
  have hpos : (∑ p : TruthChartsData.Phase.TermIdx toyData,
      if toyPhase.termLam γ (fun _ _ _ ↦ toyAlpha γ) p = (1 - 2 * γ) / 2 then
        toyPhase.termConst' χ σ γ (fun _ _ _ ↦ toyAlpha γ) p else 0) ≠ 0 := by
    rw [hsum χ]
    exact (mul_pos hχ0 hScpos).ne'
  have hlim := toyPhase.tendsto_fibre_expectation hS hF hFm htruth hσ.ne' hψc hψ hMψ hψL hχc hχ
    hMχ hχL (α := fun _ _ _ ↦ toyAlpha γ) (fun i _ _ _ ↦ toy_feasible i γ hγ0 hγ)
    (fun i ε b _ ↦ toy_profile i ε b σ γ hσ.ne' hγ0 hγ)
    (lam₀ := (1 - 2 * γ) / 2) (fun p ↦ by
      unfold TruthChartsData.Phase.termLam
      rw [toy_lpExponent]) hpos
  rw [hsum ψ, hsum χ, mul_div_mul_right _ _ hScpos.ne'] at hlim
  exact hlim

end Laplace.Multi.ToyWall
