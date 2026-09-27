/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseTestingData

/-!
# The influence function of a posterior expectation on the space of data laws

The posterior expectation of a bounded observable `F` is a function of the data law,
`Ψ_F(D) = E_{R_{m_D}} F` (`dataObs`), through the entropy response of its feature mean. Its
derivative along the tilted perturbations `D_t ∝ e^{t h} D` of the data law is

* **the data-law influence** (`hasDerivAt_dataObs_tilted`):
  `d/dt Ψ_F(D_t)|_{t=0} = Cov_D(⟨u_F, S⟩, h)`, with `u_F` the regression direction of `F` at the
  response of `D`, so the **influence function** is `IF_{F,D}(x) = ⟨u_F, S(x) − m_D⟩`
  (`dataInfluence`, `lawCov_dataInfluence`);
* **its kernel and its extremal directions** (`sq_lawCov_influence_le`): the response is
  insensitive exactly to the scores uncorrelated with `⟨u_F, S⟩`, and
  `|Ψ̇_F|² ≤ Σ_D(u_F, u_F) · Var_D(h)`, with equality along `h ∝ IF_{F,D}`;
* **the minimum-information lift** (`isLeast_information_lift`): among the scores `h` producing
  a prescribed response velocity `Cov_D(⟨u,S⟩, h) = ⟨u, e⟩` for all `u ∈ W`, the least variance
  is `⟨e, Σ_D⁻¹ e⟩`, attained by `h_e = ⟨Σ_D⁻¹ e, S⟩` — the covariance-dual alternative of
  `ResponseMismatchResolution`/`ResponseTestingData` is the least-information way to realise a
  prescribed response velocity.

Together with `ResponseTestingData` this closes the loop: a data-law perturbation has a
least-information response velocity, and its information `s²⟨e, Σ_D⁻¹e⟩/2` is exactly what the
testing obstruction charges.
-/

open MeasureTheory InformationTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Influence

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (D : Measure X) [IsProbabilityMeasure D]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

set_option linter.unusedFintypeInType false

/-- The feature mean of a law. -/
local notation "mD" => (fun j : J ↦ ∫ x, S j x ∂D)

/-- **The posterior expectation as a function of the data law**: `Ψ_F(D) = E_{R_{m_D}} F`. -/
noncomputable def dataObs (F : X → ℝ) (D : Measure X) : ℝ :=
  ∫ x, F x ∂responseProjection hS ν (fun j ↦ ∫ x, S j x ∂D)

omit [IsProbabilityMeasure D] in
/-- The influence function `IF_{F,D}(x) = ⟨u_F, S(x) − m_D⟩` at a law with interior response. -/
noncomputable def dataInfluence (F : X → ℝ) (x : X) : ℝ :=
  dirLoss S (regressionDir hS ν F (θr mD) : J → ℝ) x -
    dotJ (regressionDir hS ν F (θr mD) : J → ℝ) mD

variable (hDν : D ≪ ν) (hνD : ν ≪ D)
include hDν hνD

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The tilted data laws are equivalent to the base law. -/
theorem tilted_absolutelyContinuous_base {h : X → ℝ} (hh : Bdd h) (t : ℝ) :
    (D.tilted fun x ↦ t * h x) ≪ ν ∧ ν ≪ (D.tilted fun x ↦ t * h x) :=
  ⟨(tilted_absolutelyContinuous D _).trans hDν,
    hνD.trans (absolutelyContinuous_tilted (integrable_exp_of_bdd D (hh.const_mul t)))⟩

/-- The mean displacement of the tilted data law lies in the direction space. -/
theorem mean_tilted_sub_mem {h : X → ℝ} (hh : Bdd h) (t : ℝ) :
    (fun j ↦ ∫ x, S j x ∂(D.tilted fun x ↦ t * h x)) - mD ∈ 𝕍 := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd D (hh.const_mul t))
  exact sub_mem_dirSpan_of_mem_momentBody' hS ν (mean_mem_momentBody_of_ac hS ν D hDν)
    (mean_mem_momentBody_of_ac hS ν _ (tilted_absolutelyContinuous_base ν D hDν hνD hh t).1)

/-- The mean displacement path of the tilted data laws, as a path in the direction space. -/
noncomputable def meanPath {h : X → ℝ} (hh : Bdd h) (t : ℝ) : 𝕍 :=
  ⟨_, mean_tilted_sub_mem hS ν D hDν hνD hh t⟩

theorem meanPath_coe {h : X → ℝ} (hh : Bdd h) (t : ℝ) :
    (meanPath hS ν D hDν hνD hh t : J → ℝ) =
      (fun j ↦ ∫ x, S j x ∂(D.tilted fun x ↦ t * h x)) - mD := rfl

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hDν hνD in
theorem tilted_zero_mul_eq {h : X → ℝ} : (D.tilted fun x ↦ (0 : ℝ) * h x) = D := by
  have e : (fun x ↦ (0 : ℝ) * h x) = 0 := by
    funext x
    simp
  rw [e, tilted_zero]

theorem meanPath_zero {h : X → ℝ} (hh : Bdd h) : meanPath hS ν D hDν hνD hh 0 = 0 := by
  apply Subtype.ext
  rw [meanPath_coe, Submodule.coe_zero, tilted_zero_mul_eq, sub_self]

/-- The coordinates of the mean path are differentiable. -/
theorem hasDerivAt_meanPath_coe {h : X → ℝ} (hh : Bdd h) (t : ℝ) :
    HasDerivAt (fun s ↦ (meanPath hS ν D hDν hνD hh s : J → ℝ))
      (fun i ↦ ∫ x, S i x * h x ∂(D.tilted fun x ↦ t * h x) -
        (∫ x, S i x ∂(D.tilted fun x ↦ t * h x)) * ∫ x, h x ∂(D.tilted fun x ↦ t * h x)) t := by
  simp only [meanPath_coe]
  refine hasDerivAt_pi.2 fun i ↦ ?_
  have := (hasDerivAt_dataResponsePath hS D hh i t).sub_const (∫ x, S i x ∂D)
  exact this

/-- The mean path is differentiable in the direction space (through a retraction). -/
theorem exists_hasDerivAt_meanPath {h : X → ℝ} (hh : Bdd h) :
    ∃ z' : ℝ → 𝕍, (∀ t, HasDerivAt (meanPath hS ν D hDν hνD hh) (z' t) t) ∧
      ((z' 0 : 𝕍) : J → ℝ) = fun i ↦ lawCov D (S i) h := by
  obtain ⟨p, hp⟩ := exists_retraction ν
  set c' : ℝ → J → ℝ := fun t i ↦ ∫ x, S i x * h x ∂(D.tilted fun x ↦ t * h x) -
    (∫ x, S i x ∂(D.tilted fun x ↦ t * h x)) * ∫ x, h x ∂(D.tilted fun x ↦ t * h x) with hc'
  have e : meanPath hS ν D hDν hνD hh = fun s ↦ p (meanPath hS ν D hDν hνD hh s : J → ℝ) := by
    funext s
    rw [hp]
  have hz : ∀ t, HasDerivAt (meanPath hS ν D hDν hνD hh) (p (c' t)) t := fun t ↦ by
    have hpc : HasFDerivAt (fun y : J → ℝ ↦ p y) (LinearMap.toContinuousLinearMap p)
        (meanPath hS ν D hDν hνD hh t : J → ℝ) :=
      (LinearMap.toContinuousLinearMap p).hasFDerivAt
    have := hpc.comp_hasDerivAt t (hasDerivAt_meanPath_coe hS ν D hDν hνD hh t)
    rw [e]
    exact this
  refine ⟨fun t ↦ p (c' t), hz, ?_⟩
  · -- the derivative of the coordinates at `0` is the covariance vector, which lies in `W`
    have h1 : HasDerivAt (fun s ↦ (meanPath hS ν D hDν hνD hh s : J → ℝ)) ((p (c' 0) : 𝕍) : J → ℝ)
        0 := (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt 0 (hz 0)
    have h2 := hasDerivAt_meanPath_coe hS ν D hDν hνD hh 0
    have e := h1.unique h2
    rw [e]
    funext i
    simp only [tilted_zero_mul_eq, lawCov]

/-- **The data-law influence of a posterior expectation**: along the tilted perturbations
`D_t ∝ e^{t h} D` of a data law with interior response,
`d/dt E_{R_{m(D_t)}} F |_{t=0} = Cov_D(⟨u_F, S⟩, h)`. -/
theorem hasDerivAt_dataObs_tilted {F : X → ℝ} (hF : Bdd F) {h : X → ℝ} (hh : Bdd h) :
    HasDerivAt (fun t ↦ dataObs hS ν F (D.tilted fun x ↦ t * h x))
      (lawCov D (dirLoss S (regressionDir hS ν F (θr mD) : J → ℝ)) h) 0 := by
  obtain ⟨z', hz', hz'0⟩ := exists_hasDerivAt_meanPath hS ν D hDν hνD hh
  have hrel : ∀ t, (fun j ↦ ∫ x, S j x ∂(D.tilted fun x ↦ t * h x)) ∈ Ω := fun t ↦ by
    have := isProbabilityMeasure_tilted (integrable_exp_of_bdd D (hh.const_mul t))
    exact mean_mem_intrinsicInterior_of_equiv hS ν _
      (tilted_absolutelyContinuous_base ν D hDν hνD hh t).1
      (tilted_absolutelyContinuous_base ν D hDν hνD hh t).2
  have hrel0 : mD ∈ Ω := mean_mem_intrinsicInterior_of_equiv hS ν D hDν hνD
  -- the observable along the path is the family integral along the chart path
  have e : (fun t ↦ dataObs hS ν F (D.tilted fun x ↦ t * h x)) =
      fun t ↦ ∫ x, F x ∂Pfam (θr (mD + (meanPath hS ν D hDν hνD hh t : J → ℝ)) : J → ℝ) := by
    funext t
    unfold dataObs
    rw [responseProjection_eq_familyMeasure_responseTheta hS ν (hrel t)]
    congr 3
    rw [meanPath_coe, add_sub_cancel]
  rw [e]
  have hθ0 : mD + (meanPath hS ν D hDν hνD hh 0 : J → ℝ) ∈ Ω := by
    rw [meanPath_zero, Submodule.coe_zero, add_zero]
    exact hrel0
  have hm : mD = mean (θr mD : J → ℝ) := by
    rw [meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS hrel0]
  have hθc : HasDerivAt (fun t ↦ (θr (mD + (meanPath hS ν D hDν hνD hh t : J → ℝ)) : J → ℝ))
      (((CDE (θr mD)).symm (z' 0) : 𝕍) : J → ℝ) 0 := by
    have h1 := hasDerivAt_responseTheta_meanPath hS ν (θr mD) (z := meanPath hS ν D hDν hνD hh)
      (z' := z') hz' (t₀ := 0) (by rw [← hm]; exact hθ0)
    have h2 := (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt 0 h1
    rw [← hm, meanPath_zero, Submodule.coe_zero, add_zero] at h2
    exact h2
  have hd := hasDerivAt_integral_familyMeasure_path hS ν hθc hF
  refine hd.congr_deriv ?_
  simp only [meanPath_zero, Submodule.coe_zero, add_zero]
  rw [← fisherInner_regressionDir hS ν hF, fisherInner_chartDerivEquiv_symm' hS ν, neg_neg,
    lawCov_dirLoss_left hS D _ h hh, hz'0]
  rfl

omit hDν hνD in
/-- The influence function is centred. -/
theorem integral_dataInfluence (F : X → ℝ) : ∫ x, dataInfluence hS ν D F x ∂D = 0 := by
  unfold dataInfluence
  have hi : Integrable (dirLoss S (regressionDir hS ν F (θr mD) : J → ℝ)) D :=
    integrable_of_bdd_prob D (bdd_dirLoss hS _)
  rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul, sub_eq_zero]
  unfold dirLoss dotJ
  rw [integral_finsetSum _ fun i _ ↦ (integrable_of_bdd_prob D (hS i)).const_mul _]
  exact Finset.sum_congr rfl fun i _ ↦ integral_const_mul _ _

omit hDν hνD in
/-- The influence function has the covariances of the regression feature `⟨u_F, S⟩`. -/
theorem lawCov_dataInfluence (F : X → ℝ) {h : X → ℝ} (hh : Bdd h) :
    lawCov D (dataInfluence hS ν D F) h =
      lawCov D (dirLoss S (regressionDir hS ν F (θr mD) : J → ℝ)) h := by
  unfold dataInfluence
  rw [lawCov_sub_left_eq D (bdd_dirLoss hS _) (Bdd.const _) hh, lawCov_const_left_eq_zero,
    sub_zero]

omit hDν hνD in
/-- **The response is bounded by the data covariance of the regression feature times the variance
of the score**: `|Ψ̇_F|² ≤ Σ_D(u_F, u_F) · Var_D(h)`, with equality along `h ∝ ⟨u_F, S⟩`. -/
theorem sq_lawCov_influence_le (F : X → ℝ) {h : X → ℝ} (hh : Bdd h) :
    lawCov D (dirLoss S (regressionDir hS ν F (θr mD) : J → ℝ)) h ^ 2 ≤
      dataBilin hS ν D (regressionDir hS ν F (θr mD)) (regressionDir hS ν F (θr mD)) *
        lawCov D h h :=
  lawCov_sq_le D (bdd_dirLoss hS _) hh

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] hDν hνD in
/-- **The minimum-information lift**: among the bounded scores `h` producing the response velocity
`Cov_D(⟨u,S⟩, h) = ⟨u, e⟩` for every `u ∈ W`, the least variance is `⟨e, Σ_D⁻¹ e⟩`, attained by
the covariance-dual feature `h_e = ⟨Σ_D⁻¹ e, S⟩`. -/
theorem isLeast_information_lift (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u) (e : 𝕍) :
    IsLeast {v | ∃ h : X → ℝ, Bdd h ∧
        (∀ u : 𝕍, lawCov D (dirLoss S (u : J → ℝ)) h = dotJ (u : J → ℝ) (e : J → ℝ)) ∧
        v = lawCov D h h}
      (dataBilin hS ν D (dataDual hS ν D hpd e) (dataDual hS ν D hpd e)) := by
  constructor
  · refine ⟨dirLoss S (dataDual hS ν D hpd e : J → ℝ), bdd_dirLoss hS _, fun u ↦ ?_, rfl⟩
    rw [← dataBilin_apply hS ν D, dataBilin_comm hS ν D, dataBilin_dataDual hS ν D hpd]
  · rintro v ⟨h, hh, hcov, rfl⟩
    have h1 : lawCov D (dirLoss S (dataDual hS ν D hpd e : J → ℝ)) h =
        dataBilin hS ν D (dataDual hS ν D hpd e) (dataDual hS ν D hpd e) := by
      rw [hcov, dataBilin_dataDual_self hS ν D hpd]
    have hcs := lawCov_sq_le D (bdd_dirLoss hS (dataDual hS ν D hpd e : J → ℝ)) hh
    rw [h1, ← dataBilin_apply hS ν D] at hcs
    rcases eq_or_lt_of_le (dataBilin_self_nonneg hS ν D (dataDual hS ν D hpd e)) with h0 | hpos
    · rw [← h0]
      exact lawCov_self_nonneg D hh
    · rw [sq] at hcs
      exact le_of_mul_le_mul_left hcs hpos

end Influence

end Laplace.Multi
