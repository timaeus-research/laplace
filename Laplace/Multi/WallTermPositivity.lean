/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.WallFibreExpectation

/-!
# Positivity of a term constant

Astra's review (§1.5): the nonzero-denominator hypothesis of the fibre-expectation theorems is
positivity of one dominant constant, and a sufficient condition is that the limiting weight is
positive on the limiting domain and that domain has positive measure. `termConst_pos` proves it:
the integrand `dsWeight₀ e^{-dsProfile}` is nonnegative, integrable (dominated by the profile
certificate's envelope), and positive on the limiting domain.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

variable {m : ℕ} {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}

namespace WallChartsData

variable (D : WallChartsData m ℓ L')

theorem measurable_facePt {ι : Type*} (α : ι → ℝ) : Measurable (facePt α) :=
  measurable_pi_lambda _ fun j ↦ by
    unfold facePt
    split_ifs
    · exact measurable_pi_apply j
    · exact measurable_const

theorem measurable_limitCut {ι : Type*} [Fintype ι] (Dc γ q : ℝ) (Q α : ι → ℝ) :
    Measurable (limitCut Dc γ q Q α) := by
  unfold limitCut
  split_ifs
  · exact measurable_const.mul
      (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _)
  · exact measurable_const

theorem measurable_limitBranchPt (i : D.ι) (ε : Fin m → Bool) (b : Bool) (σ γ : ℝ)
    (α : Fin m → ℝ) : Measurable (D.limitBranchPt i ε b σ γ α) := by
  have e : D.limitBranchPt i ε b σ γ α = fun u ↦
      (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) (D.k i)).symm
        (bsign b * limitCut (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α u,
          orth ε (facePt α u)) := rfl
  rw [e]
  exact (MeasurableEquiv.measurable _).comp
    ((measurable_const.mul (measurable_limitCut _ _ _ _ _)).prodMk
      ((measurable_orth ε).comp (measurable_facePt α)))

end WallChartsData

namespace WallChartsData.Phase

variable {D : WallChartsData m ℓ L'} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)
variable {i : D.ι} {φ : (Fin (m + 1) → ℝ) → ℝ} {ε : Fin m → Bool} {b : Bool} {σ γ : ℝ}
  {α : Fin m → ℝ}

theorem dsProfile_nonneg' (hσ : σ ≠ 0) (u : Fin m → ℝ) :
    0 ≤ dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
      (D.Qexp i) (P.kappa i) α (P.limitUnit i ε b σ γ α) u := by
  unfold dsProfile
  split_ifs with hu
  · exact mul_nonneg (mul_nonneg (rpow_pos_of_pos (abs_pos.mpr hσ) _).le (abs_nonneg _))
      (Finset.prod_nonneg fun j _ ↦ rpow_nonneg (limitDomain_pos hu j).le _)
  · exact le_rfl
  · exact le_rfl

theorem measurable_limitWeight (hφ : Measurable φ) :
    Measurable (P.limitWeight i φ ε b σ γ α) := by
  unfold limitWeight
  have hpt := D.measurable_limitBranchPt i ε b σ γ α
  exact ((hφ.comp (D.rep_meas i)).comp hpt).mul
    (((P.wt_cont i).measurable.comp hpt).mul
      ((continuous_abs.comp (P.b_cont i)).measurable.comp hpt))

theorem measurable_limitUnit : Measurable (P.limitUnit i ε b σ γ α) :=
  (continuous_abs.comp (P.a_cont i)).measurable.comp (D.measurable_limitBranchPt i ε b σ γ α)

omit P in
theorem measurable_dsProfile_of {ρ B Dc γ q δ : ℝ} {Q κ α : Fin m → ℝ} {a₀ : (Fin m → ℝ) → ℝ}
    (ha₀ : Measurable a₀) : Measurable (dsProfile ρ B Dc γ q δ Q κ α a₀) := by
  unfold dsProfile
  refine Measurable.ite measurableSet_limitDomain ?_ measurable_const
  split_ifs
  · exact (measurable_const.mul ha₀).mul
      (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _)
  · exact measurable_const

theorem limitWeight_le (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ} (hMφ : ∀ z, φ z ≤ Mφ) {u : Fin m → ℝ}
    (hu : u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α) :
    P.limitWeight i φ ε b σ γ α u ≤ Mφ * P.Mb i := by
  have hMφ0 : 0 ≤ Mφ := (hφ 0).trans (hMφ 0)
  have hcb := Metric.ball_subset_closedBall (D.limitBranchPt_mem_ball i ε b hu)
  unfold limitWeight
  calc φ (D.rep i (D.limitBranchPt i ε b σ γ α u)) *
        (P.wt i (D.limitBranchPt i ε b σ γ α u) * |P.b i (D.limitBranchPt i ε b σ γ α u)|)
      ≤ Mφ * (1 * P.Mb i) :=
        mul_le_mul (hMφ _) (mul_le_mul (P.wt_le_one i _) (P.b_bounds i _ hcb).2 (abs_nonneg _)
          zero_le_one) (mul_nonneg (P.wt_nonneg i _) (abs_nonneg _)) hMφ0
    _ = Mφ * P.Mb i := by ring

/-- **Positivity of a term constant**: if the limiting weight is positive on the limiting domain
and that domain has positive measure, the term constant is positive. -/
theorem termConst_pos (hσ : σ ≠ 0) (hφm : Measurable φ) (hφ : ∀ z, 0 ≤ φ z) {Mφ : ℝ}
    (hMφ : ∀ z, φ z ≤ Mφ) (hprof : P.ProfileIntegrableOf i ε b σ γ α)
    (hlimW : ∀ u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α,
      0 < P.limitWeight i φ ε b σ γ α u)
    (hvol : 0 < volume (limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α)) :
    0 < P.termConst i φ ε b σ γ α := by
  unfold termConst
  have hA : 0 < P.constA i σ := by
    unfold constA
    exact div_pos (rpow_pos_of_pos (abs_pos.mpr hσ) _) (Nat.cast_pos.mpr (D.q_pos i))
  refine mul_pos hA ?_
  have hprodpos : ∀ u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α,
      0 < ∏ j, u j ^ P.rExp i j := fun u hu ↦
    Finset.prod_pos fun j _ ↦ rpow_pos_of_pos (limitDomain_pos hu j) _
  have hf0 : ∀ u, 0 ≤ dsWeight₀ (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) (P.rExp i) α
      (P.limitWeight i φ ε b σ γ α) u *
      exp (-dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
        (D.Qexp i) (P.kappa i) α (P.limitUnit i ε b σ γ α) u) := fun u ↦ by
    unfold dsWeight₀
    exact mul_nonneg (Set.indicator_nonneg (fun u hu ↦
      mul_nonneg (hlimW u hu).le (hprodpos u hu).le) u) (exp_pos _).le
  have hfpos : ∀ u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α,
      0 < dsWeight₀ (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) (P.rExp i) α
        (P.limitWeight i φ ε b σ γ α) u *
      exp (-dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
        (D.Qexp i) (P.kappa i) α (P.limitUnit i ε b σ γ α) u) := fun u hu ↦ by
    unfold dsWeight₀
    rw [Set.indicator_of_mem hu]
    exact mul_pos (mul_pos (hlimW u hu) (hprodpos u hu)) (exp_pos _)
  have hmeas : Measurable fun u ↦ dsWeight₀ (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i)
      (P.rExp i) α (P.limitWeight i φ ε b σ γ α) u *
      exp (-dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
        (D.Qexp i) (P.kappa i) α (P.limitUnit i ε b σ γ α) u) := by
    unfold dsWeight₀
    exact (((P.measurable_limitWeight hφm).mul
      (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _)).indicator
        measurableSet_limitDomain).mul
      (Real.measurable_exp.comp (measurable_dsProfile_of P.measurable_limitUnit).neg)
  have hc1 : P.ma i / P.Ma i ≤ 1 := by
    have h := P.a_bounds i 0 (Metric.mem_closedBall_self (D.ρ_pos i).le)
    have hMa : 0 < P.Ma i := (P.ma_pos i).trans_le (h.1.trans h.2)
    rw [div_le_one hMa]
    exact h.1.trans h.2
  have hint : Integrable fun u ↦ dsWeight₀ (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i)
      (P.rExp i) α (P.limitWeight i φ ε b σ γ α) u *
      exp (-dsProfile (D.ρ i) (P.constB i σ) (D.constD i σ) γ (D.q i (D.k i)) (P.phaseExp i γ)
        (D.Qexp i) (P.kappa i) α (P.limitUnit i ε b σ γ α) u) := by
    refine Integrable.mono' (hprof.int' _ (Mφ * P.Mb i)) hmeas.aestronglyMeasurable
      (Eventually.of_forall fun u ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 u)]
    unfold dsWeight₀ dsEnvelope
    by_cases hu : u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
      have hΦ := P.dsProfile_nonneg' (i := i) (ε := ε) (b := b) (γ := γ) (α := α) hσ u
      refine mul_le_mul (mul_le_mul_of_nonneg_right (P.limitWeight_le hφ hMφ hu)
        (hprodpos u hu).le) (Real.exp_le_exp.mpr ?_) (exp_pos _).le
        (mul_nonneg (mul_nonneg ((hφ 0).trans (hMφ 0)) P.Mb_nonneg) (hprodpos u hu).le)
      nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hΦ]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul, mul_zero, zero_mul]
  rw [integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hf0) hint]
  exact hvol.trans_le (measure_mono fun u hu ↦ (hfpos u hu).ne')

end WallChartsData.Phase

end Laplace.Multi
