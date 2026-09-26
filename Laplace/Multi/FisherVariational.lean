/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.StraightPathAtlas
import Laplace.Multi.AngularBound

/-!
# The dual Fisher metric as a minimal Fisher cost

Let `P` be a probability law, `S` bounded statistics, and `Ṁ` a moment velocity. A **score
perturbation producing `Ṁ`** is a bounded `h` with `E_P h = 0` and `E_P[h ⟨e, S⟩] = ⟨e, Ṁ⟩` for
every direction `e` (so `E_P[h (S − M)] = Ṁ`); its Fisher cost is `E_P h²`.

* Cauchy–Schwarz: `⟨v, Ṁ⟩² ≤ Var_P⟨v, S⟩ · E_P h²` for every `v`
  (`sq_dotJ_le_lawCov_mul_integral_sq`);
* hence, if `v` solves `C_P v = Ṁ` (i.e. `Cov_P(⟨e,S⟩, ⟨v,S⟩) = ⟨e, Ṁ⟩` for all `e`),
  `Var_P⟨v, S⟩ ≤ E_P h²` (`lawCov_le_integral_sq_of_cov_eq`), and the centred score
  `h = ⟨v, S⟩ − E_P⟨v, S⟩` attains it (`centred_dirLoss_attains`): the dual Fisher metric
  `⟨Ṁ, C_P⁻¹ Ṁ⟩ = Var_P⟨C_P⁻¹Ṁ, S⟩` is **the minimal Fisher cost of producing the moment velocity
  `Ṁ`**;
* along the straight path of the atlas the curvature `κ(s) = Var_{P_{θ_s}}⟨θ_s', S⟩` is the
  minimal Fisher cost of moving the response with velocity `Δ = M − m₀` at `P_{θ_s}`
  (`atlasCurv_le_integral_sq`): the information budget `𝓘(M) = ∫₀¹ (1 − s) κ(s) ds` integrates
  minimal Fisher costs.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section Variational

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (P : Measure X) [IsProbabilityMeasure P]
include hS

omit hS in
/-- The variance is the centred second moment. -/
theorem lawCov_self_eq_integral_sq {g : X → ℝ} (hg : Bdd g) :
    lawCov P g g = ∫ x, (g x - ∫ y, g y ∂P) * (g x - ∫ y, g y ∂P) ∂P := by
  have hi := integrable_of_bdd_prob P hg
  have hi2 := integrable_of_bdd_prob P (hg.mul hg)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∫ y, g y ∂P := ⟨_, rfl⟩
  rw [← hc]
  have e : ∀ x, (g x - c) * (g x - c) = g x * g x - 2 * c * g x + c * c := fun x ↦ by ring
  simp_rw [e]
  have h1 : Integrable (fun x ↦ g x * g x - 2 * c * g x) P := hi2.sub (hi.const_mul _)
  rw [integral_add h1 (integrable_const _), integral_sub hi2 (hi.const_mul _),
    integral_const_mul, integral_const, probReal_univ, one_smul]
  unfold lawCov
  rw [← hc]
  ring

/-- **Cauchy–Schwarz for score perturbations**: `⟨v, Ṁ⟩² ≤ Var_P⟨v,S⟩ · E_P h²`. -/
theorem sq_dotJ_le_lawCov_mul_integral_sq {h : X → ℝ} (hh : Bdd h) (hmean : ∫ x, h x ∂P = 0)
    {Mdot : J → ℝ} (hmom : ∀ e, ∫ x, h x * dirLoss S e x ∂P = dotJ e Mdot) (v : J → ℝ) :
    dotJ v Mdot ^ 2 ≤ lawCov P (dirLoss S v) (dirLoss S v) * ∫ x, h x * h x ∂P := by
  have hg := bdd_dirLoss hS v
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∫ y, dirLoss S v y ∂P := ⟨_, rfl⟩
  have hgc : Bdd fun x ↦ dirLoss S v x - c := hg.sub (Bdd.const c)
  have hhi := integrable_of_bdd_prob P hh
  have h1 : ∫ x, h x * (dirLoss S v x - c) ∂P = dotJ v Mdot := by
    have e : ∀ x, h x * (dirLoss S v x - c) = h x * dirLoss S v x - h x * c := fun x ↦ by ring
    simp_rw [e]
    rw [integral_sub (integrable_of_bdd_prob P (hh.mul hg)) (hhi.mul_const c),
      integral_mul_const, hmean, hmom, zero_mul, sub_zero]
  have h2 : lawCov P (dirLoss S v) (dirLoss S v) =
      ∫ x, (dirLoss S v x - c) * (dirLoss S v x - c) ∂P := by
    rw [lawCov_self_eq_integral_sq P hg, hc]
  have hcs := integral_mul_sq_le (ν := P) (f := h) (g := fun x ↦ dirLoss S v x - c)
    (integrable_of_bdd_prob P (hh.mul hh)) (integrable_of_bdd_prob P (hgc.mul hgc))
    (integrable_of_bdd_prob P (hh.mul hgc))
  rw [h1] at hcs
  rw [h2, mul_comm]
  exact hcs

/-- **The minimal Fisher cost of a moment velocity**: if `C_P v = Ṁ`, every score perturbation
producing `Ṁ` costs at least `Var_P⟨v, S⟩ = ⟨Ṁ, C_P⁻¹ Ṁ⟩`. -/
theorem lawCov_le_integral_sq_of_cov_eq {h : X → ℝ} (hh : Bdd h) (hmean : ∫ x, h x ∂P = 0)
    {Mdot : J → ℝ} (hmom : ∀ e, ∫ x, h x * dirLoss S e x ∂P = dotJ e Mdot) {v : J → ℝ}
    (hC : ∀ e, lawCov P (dirLoss S e) (dirLoss S v) = dotJ e Mdot) :
    lawCov P (dirLoss S v) (dirLoss S v) ≤ ∫ x, h x * h x ∂P := by
  have hcs := sq_dotJ_le_lawCov_mul_integral_sq hS P hh hmean hmom v
  rw [← hC v, sq] at hcs
  rcases (lawCov_self_nonneg P (bdd_dirLoss hS v)).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact integral_nonneg fun x ↦ mul_self_nonneg _
  · exact le_of_mul_le_mul_left hcs hpos

/-- **The centred score attains the minimal cost**: `h = ⟨v,S⟩ − E_P⟨v,S⟩` has mean zero,
produces the velocity `C_P v`, and costs exactly `Var_P⟨v,S⟩`. -/
theorem centred_dirLoss_attains (v : J → ℝ) :
    (∫ x, (dirLoss S v x - ∫ y, dirLoss S v y ∂P) ∂P = 0) ∧
      (∀ e, ∫ x, (dirLoss S v x - ∫ y, dirLoss S v y ∂P) * dirLoss S e x ∂P =
        lawCov P (dirLoss S e) (dirLoss S v)) ∧
      ∫ x, (dirLoss S v x - ∫ y, dirLoss S v y ∂P) * (dirLoss S v x - ∫ y, dirLoss S v y ∂P) ∂P =
        lawCov P (dirLoss S v) (dirLoss S v) := by
  have hg := bdd_dirLoss hS v
  have hgi := integrable_of_bdd_prob P hg
  refine ⟨?_, fun e ↦ ?_, (lawCov_self_eq_integral_sq P hg).symm⟩
  · rw [integral_sub hgi (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]
  · have he := bdd_dirLoss hS e
    have e1 : ∀ x, (dirLoss S v x - ∫ y, dirLoss S v y ∂P) * dirLoss S e x =
        dirLoss S e x * dirLoss S v x - (∫ y, dirLoss S v y ∂P) * dirLoss S e x := fun x ↦ by ring
    simp_rw [e1]
    rw [integral_sub (integrable_of_bdd_prob P (he.mul hg))
      ((integrable_of_bdd_prob P he).const_mul _), integral_const_mul]
    unfold lawCov
    ring

end Variational

section Atlas

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤)
include hS hfin

/-- The atlas velocity solves `C_{θ_s} (−θ_s') = Δ`. -/
theorem lawCov_dirLoss_neg_atlasVel (s : ℝ) (e : J → ℝ) :
    lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s))
        (dirLoss S e) (dirLoss S (-(atlasVel hS ν hfin s : J → ℝ))) =
      dotJ e (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by
  have hcd : ∀ w, chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS (atlasTheta hS ν M s) w =
      chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
        (atlasTheta hS ν M s) w := fun w ↦ by
    rw [← coe_chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (atlasTheta hS ν M s)]
    rfl
  have hv : (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (atlasTheta hS ν M s) (atlasVel hS ν hfin s) : J → ℝ) =
      M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 := by
    rw [← hcd]
    unfold atlasVel
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have h1 := dotJ_chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (atlasTheta hS ν M s) e (atlasVel hS ν hfin s)
  rw [hv, priorCov_eq_lawCov_familyMeasure hS ν] at h1
  have hneg : dirLoss S (-(atlasVel hS ν hfin s : J → ℝ)) =
      fun x ↦ -dirLoss S (atlasVel hS ν hfin s : J → ℝ) x := funext fun x ↦ dirLoss_neg (S := S) _ x
  rw [hneg, lawCov_comm, lawCov_neg_left, lawCov_comm, ← h1]

/-- **The curvature of the rate is the minimal Fisher cost of the response velocity**: every
bounded `h` with `E h = 0` and `E[h ⟨e,S⟩] = ⟨e, Δ⟩` under `P_{θ_s}` satisfies
`κ(s) ≤ E_{P_{θ_s}} h²`. -/
theorem atlasCurv_le_integral_sq (s : ℝ) {h : X → ℝ} (hh : Bdd h)
    (hmean : ∫ x, h x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s) = 0)
    (hmom : ∀ e, ∫ x, h x * dirLoss S e x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s) = dotJ e (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)) :
    atlasCurv hS ν hfin s ≤
      ∫ x, h x * h x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (atlasTheta hS ν M s) := by
  have hP := isProbabilityMeasure_familyMeasure (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ))
    measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const
    (M₀ := 0) (fun _ ↦ by simp) hS (t := 1) (atlasTheta hS ν M s : J → ℝ)
  have hmin := lawCov_le_integral_sq_of_cov_eq hS _ hh hmean hmom
    (lawCov_dirLoss_neg_atlasVel hS ν hfin s)
  have hneg : dirLoss S (-(atlasVel hS ν hfin s : J → ℝ)) =
      fun x ↦ -dirLoss S (atlasVel hS ν hfin s : J → ℝ) x := funext fun x ↦ dirLoss_neg (S := S) _ x
  rw [hneg, lawCov_neg_left, lawCov_comm, lawCov_neg_left, neg_neg, lawCov_comm] at hmin
  rw [atlasCurv_eq_priorCov, priorCov_eq_lawCov_familyMeasure hS ν]
  exact hmin

end Atlas

end Laplace.Multi
