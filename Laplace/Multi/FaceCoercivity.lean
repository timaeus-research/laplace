/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FaceGauge
import Laplace.Multi.FaceMassConcentration
import Laplace.Multi.ResponsePathDifferential
import Laplace.Multi.FacetSchurBound

/-!
# Tangential coercivity near a face

The variance of a visible contrast `⟨w, S⟩` under a law `q` dominates the face-conditional
variance times the face mass, `Var_q ⟨w,S⟩ ≥ q(A) Var_{q(·|A)} ⟨w,S⟩`
(`mul_lawCov_faceMeasure_le_lawCov`); the face-conditional law of a family member is the face
family member (`faceMeasure_familyMeasure_eq`), which only depends on the tangential coordinate;
and on the face direction space `T'` the face-family variance is coercive,
`Var_{P^A_θ}⟨w,S⟩ ≥ λ ‖w‖²` (`exists_coercive_familyMeasure`), by compactness of the unit sphere
and strict positivity of the variance of nonzero visible contrasts. Along a sequence
`v_n − r_n u` with `v_n → v_M` and `r_n → ∞` the three facts combine, through the bounded-tilt
variance comparison and the concentration of mass on the face, into a uniform coercivity constant
(`eventually_coercive_of_components`): the tangential covariance stays nondegenerate all the way
to the face. This is the coercivity input of the Schur complement estimate.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Conditional

variable {X : Type*} [MeasurableSpace X]

/-- **Conditioning lowers the variance by the mass**: `q(A) Var_{q(·|A)} f ≤ Var_q f`. -/
theorem mul_lawCov_faceMeasure_le_lawCov (q : Measure X) [IsProbabilityMeasure q] {A : Set X}
    (hA0 : 0 < q.real A) {f : X → ℝ} (hf : Bdd f) :
    q.real A * lawCov (faceMeasure q A) f f ≤ lawCov q f f := by
  have hAne : q A ≠ 0 := (ENNReal.toReal_pos_iff.1 hA0).1.ne'
  have hPA := isProbabilityMeasure_faceMeasure q hAne
  have hint : Integrable (fun x ↦ (f x - ∫ y, f y ∂q) * (f x - ∫ y, f y ∂q)) q :=
    integrable_of_bdd_prob q ((hf.sub (Bdd.const _)).mul (hf.sub (Bdd.const _)))
  calc q.real A * lawCov (faceMeasure q A) f f
      ≤ q.real A * ∫ x, (f x - ∫ y, f y ∂q) * (f x - ∫ y, f y ∂q) ∂faceMeasure q A :=
        mul_le_mul_of_nonneg_left (lawCov_self_le_integral_sq _ hf _) measureReal_nonneg
    _ = ∫ x in A, (f x - ∫ y, f y ∂q) * (f x - ∫ y, f y ∂q) ∂q := by
        rw [integral_faceMeasure, ← mul_assoc, mul_inv_cancel₀ hA0.ne', one_mul]
    _ ≤ ∫ x, (f x - ∫ y, f y ∂q) * (f x - ∫ y, f y ∂q) ∂q :=
        setIntegral_le_integral hint (ae_of_all _ fun x ↦ mul_self_nonneg _)
    _ = lawCov q f f := (lawCov_self_eq_integral_sq q hf).symm

end Conditional

section Face

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty J] in
/-- The face-conditional law of a family member is the face family member. -/
theorem faceMeasure_familyMeasure_eq {A : Set X} (hA : MeasurableSet A) (hA0 : ν A ≠ 0)
    [IsProbabilityMeasure (faceMeasure ν A)] (θ : J → ℝ) :
    faceMeasure (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) A =
      familyMeasure (faceMeasure ν A) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ := by
  rw [familyMeasure_one_zero_eq_tilted hS ν, familyMeasure_one_zero_eq_tilted hS (faceMeasure ν A)]
  exact faceMeasure_tilted ν hA hA0 ((bdd_dirLoss hS θ).1.const_mul (-1))
    (integrable_exp_of_bdd ν ((bdd_dirLoss hS θ).const_mul (-1)))

omit [Nonempty X] [Nonempty J] in
/-- The variance of a visible contrast is a continuous function of the contrast. -/
theorem continuous_lawCov_dirLoss_self (P : Measure X) [IsProbabilityMeasure P] :
    Continuous fun w : J → ℝ ↦ lawCov P (dirLoss S w) (dirLoss S w) := by
  have e : ∀ w : J → ℝ, lawCov P (dirLoss S w) (dirLoss S w) =
      ∑ i, w i * ∑ j, w j * lawCov P (S j) (S i) := by
    intro w
    rw [lawCov_dirLoss_left hS P w _ (bdd_dirLoss hS w)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [lawCov_comm, lawCov_dirLoss_left hS P w _ (hS i)]
  simp_rw [e]
  refine continuous_finsetSum _ fun i _ ↦ (continuous_apply i).mul ?_
  exact continuous_finsetSum _ fun j _ ↦ (continuous_apply j).mul continuous_const

omit [Nonempty X] [Nonempty J] hS in
theorem lawCov_dirLoss_smul_self (P : Measure X) [IsProbabilityMeasure P] (c : ℝ) (w : J → ℝ) :
    lawCov P (dirLoss S (c • w)) (dirLoss S (c • w)) =
      c ^ 2 * lawCov P (dirLoss S w) (dirLoss S w) := by
  rw [dirLoss_smul, lawCov_const_mul_self]

omit [Nonempty J] in
/-- **Coercivity of the family variance on the direction space**: `Var_{P_θ}⟨w,S⟩ ≥ λ ‖w‖²`. -/
theorem exists_coercive_familyMeasure (θ : J → ℝ) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S,
      lam * ‖w‖ ^ 2 ≤ lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ)
        (dirLoss S w) (dirLoss S w) := by
  set P := familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ with hP
  have hPP : IsProbabilityMeasure P := by
    rw [hP, familyMeasure_one_zero_eq_tilted hS ν]
    exact isProbabilityMeasure_tilted
      (integrable_exp_of_bdd ν ((bdd_dirLoss hS _).const_mul (-1)))
  have hpos : ∀ w ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S, w ≠ 0 →
      0 < lawCov P (dirLoss S w) (dirLoss S w) := fun w hw hw0 ↦ by
    have := priorCov_dirLoss_self_pos measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS θ hw hw0
    rwa [priorCov_eq_lawCov_familyMeasure hS ν] at this
  have hcont := continuous_lawCov_dirLoss_self hS P
  set K : Set (J → ℝ) := Metric.sphere 0 1 ∩ (dirSpan ν (fun _ ↦ (1 : ℝ)) S : Set (J → ℝ))
    with hK
  have hKc : IsCompact K :=
    (isCompact_sphere 0 1).inter_right (Submodule.closed_of_finiteDimensional _)
  by_cases hne : K.Nonempty
  · obtain ⟨w₀, hw₀, hmin⟩ := hKc.exists_isMinOn hne hcont.continuousOn
    have hw₀T : w₀ ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := hw₀.2
    have hw₀n : ‖w₀‖ = 1 := by simpa using hw₀.1
    refine ⟨lawCov P (dirLoss S w₀) (dirLoss S w₀),
      hpos w₀ hw₀T (by rintro rfl; simp at hw₀n), fun w hw ↦ ?_⟩
    by_cases hw0 : w = 0
    · subst hw0
      have e0 : dirLoss S (0 : J → ℝ) = fun _ ↦ (0 : ℝ) := funext (dirLoss_zero S)
      rw [e0, lawCov_const_left_eq_zero]
      simp
    · have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw0
      have hw' : ‖w‖⁻¹ • w ∈ K := by
        refine ⟨?_, Submodule.smul_mem _ _ hw⟩
        simp [norm_smul, hnw.ne']
      have h1 := (isMinOn_iff.1 hmin) _ hw'
      have h2 : lawCov P (dirLoss S w) (dirLoss S w) =
          ‖w‖ ^ 2 * lawCov P (dirLoss S (‖w‖⁻¹ • w)) (dirLoss S (‖w‖⁻¹ • w)) := by
        rw [lawCov_dirLoss_smul_self P, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hnw.ne',
          one_pow, one_mul]
      rw [h2, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  · refine ⟨1, one_pos, fun w hw ↦ ?_⟩
    have hw0 : w = 0 := by
      by_contra h
      have hnw : 0 < ‖w‖ := norm_pos_iff.2 h
      exact hne ⟨‖w‖⁻¹ • w, by simp [norm_smul, hnw.ne'], Submodule.smul_mem _ _ hw⟩
    subst hw0
    have e0 : dirLoss S (0 : J → ℝ) = fun _ ↦ (0 : ℝ) := funext (dirLoss_zero S)
    rw [e0, lawCov_const_left_eq_zero]
    simp

end Face

section Uniform

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (u : J → ℝ) (β : ℝ)
include hS

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The normal shift `−r u` is invisible on the face fibre. -/
theorem neg_smul_mem_invisible_faceMeasure (r : ℝ) :
    -(r • u) ∈ invisibleSet (faceMeasure ν {x | dirLoss S u x = β}) S := by
  refine ⟨-(r * β), ?_⟩
  filter_upwards [ae_mem_faceMeasure ν (measurableSet_faceFibre hS u β)] with x hx
  have hx' : dirLoss S u x = β := hx
  rw [dirLoss_neg]
  simp only [dirLoss_smul]
  rw [hx']

omit [Nonempty J] in
/-- **Uniform coercivity along a decomposed family**: with `v_i → v_M` and `r_i → ∞`, the
variances of the face-tangential contrasts under `P_{v_i − r_i u}` are eventually bounded below by
a fixed multiple of `‖w‖²`. -/
theorem eventually_coercive_of_components {ι : Type*} {l : Filter ι}
    (hβ : ∀ᵐ x ∂ν, dirLoss S u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss S u x = β}) {v : ι → J → ℝ} {vM : J → ℝ}
    (hv : Tendsto v l (𝓝 vM)) {r : ι → ℝ} (hr : Tendsto r l atTop) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ᶠ n in l,
      ∀ w ∈ dirSpan (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) S,
        lam * ‖w‖ ^ 2 ≤ lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
          (v n - r n • u)) (dirLoss S w) (dirLoss S w) := by
  have hF := measurableSet_faceFibre hS u β
  have hA0 : ν {x | dirLoss S u x = β} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have hPA := isProbabilityMeasure_faceMeasure ν hA0
  obtain ⟨lamM, hlamM, hcoer⟩ :=
    exists_coercive_familyMeasure hS (faceMeasure ν {x | dirLoss S u x = β}) vM
  obtain ⟨B, hB0, hB⟩ := exists_uniform_bound hS
  -- the tilt sizes tend to zero
  have hc : Tendsto (fun n ↦ (∑ i, |(v n - vM) i|) * B) l (𝓝 0) := by
    have h0 : Tendsto (fun n ↦ v n - vM) l (𝓝 0) := by simpa using hv.sub_const vM
    have h1 : Tendsto (fun n ↦ ∑ i, |(v n - vM) i|) l (𝓝 (∑ i, |(0 : J → ℝ) i|)) :=
      tendsto_finsetSum _ fun i _ ↦
        ((continuous_abs.comp (continuous_apply i)).tendsto _).comp h0
    simpa using h1.mul_const B
  have hmass := tendsto_measureReal_family_faceFibre_of_components hS ν u β hβ hp hv hr
  refine ⟨1 / 2 * exp (-(2 * 1)) * lamM, by positivity, ?_⟩
  filter_upwards [hc.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hmass.eventually (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with n hcn hmn
  intro w hw
  set q := familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (v n - r n • u) with hq
  have hqP : IsProbabilityMeasure q := by
    rw [hq, familyMeasure_one_zero_eq_tilted hS ν]
    exact isProbabilityMeasure_tilted
      (integrable_exp_of_bdd ν ((bdd_dirLoss hS _).const_mul (-1)))
  have hqA : 0 < q.real {x | dirLoss S u x = β} := lt_of_lt_of_le (by norm_num) hmn
  -- step 1: conditioning
  have h1 := mul_lawCov_faceMeasure_le_lawCov q hqA (bdd_dirLoss hS w)
  -- step 2: the conditional law is the face family member of the tangential part
  have h2 : faceMeasure q {x | dirLoss S u x = β} =
      familyMeasure (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ))
        S 1 (v n) := by
    rw [hq, faceMeasure_familyMeasure_eq hS ν hF hA0, sub_eq_add_neg,
      familyMeasure_add_of_invisible hS _ (v n) (neg_smul_mem_invisible_faceMeasure hS ν u β
        (r n))]
  -- step 3: bounded tilt comparison with `v_M`
  have h3 : familyMeasure (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
      (fun _ ↦ (0 : ℝ)) S 1 (v n) =
      (familyMeasure (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ))
        S 1 vM).tilted (fun x ↦ -(dirLoss S (v n - vM) x)) := by
    have := familyMeasure_sub_smul_eq_tilted hS (faceMeasure ν {x | dirLoss S u x = β}) (v n) vM u 0
    simpa using this
  have hPvM : IsProbabilityMeasure (familyMeasure (faceMeasure ν {x | dirLoss S u x = β})
      (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 vM) := by
    rw [familyMeasure_one_zero_eq_tilted hS]
    exact isProbabilityMeasure_tilted
      (integrable_exp_of_bdd _ ((bdd_dirLoss hS _).const_mul (-1)))
  have hc' : ∀ x, |(fun x ↦ -(dirLoss S (v n - vM) x)) x| ≤ 1 := fun x ↦ by
    simp only [abs_neg]
    exact (abs_dirLoss_le_sum_mul hB _ x).trans hcn
  have h4 := le_lawCov_tilted (familyMeasure (faceMeasure ν {x | dirLoss S u x = β})
    (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 vM) (bdd_neg (bdd_dirLoss hS _)) hc'
    (bdd_dirLoss hS w)
  rw [← h3, ← h2] at h4
  have h5 := hcoer w hw
  calc 1 / 2 * exp (-(2 * 1)) * lamM * ‖w‖ ^ 2
      = 1 / 2 * (exp (-(2 * 1)) * (lamM * ‖w‖ ^ 2)) := by ring
    _ ≤ q.real {x | dirLoss S u x = β} * (exp (-(2 * 1)) * (lamM * ‖w‖ ^ 2)) :=
        mul_le_mul_of_nonneg_right hmn (by positivity)
    _ ≤ q.real {x | dirLoss S u x = β} *
          lawCov (faceMeasure q {x | dirLoss S u x = β}) (dirLoss S w) (dirLoss S w) := by
        gcongr
        exact le_trans (mul_le_mul_of_nonneg_left h5 (exp_pos _).le) h4
    _ ≤ _ := h1

end Uniform

end Laplace.Multi
