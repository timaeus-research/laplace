/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseSamplingGeometry
import Laplace.Multi.ResponseCurvatureDefect
import Laplace.Multi.ObservableCurvature
import Laplace.Multi.SqrtDensityAffinity

/-!
# The residual is the second response of every observable

For a bounded observable `F` and the response line `θ_t = m⁻¹(m(θ₀) + t e)` in a mean displacement
`e ∈ W` (velocity `V_t = A_{θ_t}⁻¹ e`), the model expectation `t ↦ E_{P_{θ_t}} F` has

* first derivative `−Cov_{P_{θ_t}}(F, ⟨V_t, S⟩)` (`hasDerivAt_lineObservable`),
* second derivative `E_{P_{θ_t}}[(F − E F) · r_{V_t V_t}]` (`hasDerivAt_deriv_lineObservable`),

where `r_{uv} = f_u f_v − G(u,v) + f_{C(u,v)}` is the score residual of `ResponseCurvatureDefect`.
So **the part of score multiplication that the structural features cannot represent is exactly
what bends the response of every other observable along mean-straight journeys**:

* `abs_secondResponse_le`: `|E[(F − EF) r]| ≤ √Var(F) √E[r²]` (Cauchy–Schwarz);
* `saturatedAt_iff_secondResponse_eq_zero`: saturation at `θ` is equivalent to the vanishing of
  the second response of every bounded observable in every direction (the converse tests `F = r`);
* `hasDerivAt_lineVariance`: the response of fluctuations,
  `d/dt Var_{P_{θ_t}}(F) = −Cov_{P_{θ_t}}((F − EF)², ⟨V_t, S⟩)`.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Observable

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

/-- The centred score. -/
local notation "f" => modelScore S ν

/-- The response line. -/
local notation "θl" => responseLine hS ν

/-- The response line velocity. -/
local notation "Vl" => responseLineVel hS ν

/-- **The model expectation of an observable along a response line.** -/
noncomputable def lineObservable (F : X → ℝ) (θ₀ e : 𝕍) (t : ℝ) : ℝ :=
  ∫ x, F x ∂Pfam (θl θ₀ e t : J → ℝ)

/-- The response line, coerced, is differentiable on its domain. -/
theorem hasDerivAt_responseLine_coe (θ₀ e : 𝕍) {t : ℝ} (ht : t ∈ responseLineDomain S ν θ₀ e) :
    HasDerivAt (fun s ↦ (θl θ₀ e s : J → ℝ)) (Vl θ₀ e t : J → ℝ) t := by
  have h := (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_responseLine hS ν θ₀ e ht)
  exact h

/-- **The first response of an observable**: `d/dt E_{θ_t} F = −Cov_{θ_t}(F, ⟨V_t, S⟩)`. -/
theorem hasDerivAt_lineObservable {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) {t : ℝ}
    (ht : t ∈ responseLineDomain S ν θ₀ e) :
    HasDerivAt (lineObservable hS ν F θ₀ e)
      (-lawCov (Pfam (θl θ₀ e t : J → ℝ)) F (dirLoss S (Vl θ₀ e t : J → ℝ))) t :=
  hasDerivAt_integral_familyMeasure_path hS ν (hasDerivAt_responseLine_coe hS ν θ₀ e ht) hF

omit [Nonempty X] [Nonempty J] in
/-- The first response expanded on the coordinates of the velocity. -/
theorem lawCov_dirLoss_eq_sum (P : Measure X) [IsProbabilityMeasure P] {F : X → ℝ} (hF : Bdd F)
    (v : J → ℝ) : lawCov P F (dirLoss S v) = ∑ i, v i * lawCov P F (S i) := by
  rw [lawCov_comm, lawCov_dirLoss_left hS P v F hF]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [lawCov_comm]

/-- **The second response of an observable is the pairing with the score residual**:
`d²/dt² E_{θ_t} F = E_{θ_t}[(F − E F) r_{V_t V_t}]`. -/
theorem hasDerivAt_deriv_lineObservable {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) {t : ℝ}
    (ht : t ∈ responseLineDomain S ν θ₀ e) :
    HasDerivAt (fun s ↦ -lawCov (Pfam (θl θ₀ e s : J → ℝ)) F (dirLoss S (Vl θ₀ e s : J → ℝ)))
      (∫ x, (F x - ∫ y, F y ∂Pfam (θl θ₀ e t : J → ℝ)) *
        scoreResidual hS ν (θl θ₀ e t) (Vl θ₀ e t) (Vl θ₀ e t) x ∂Pfam (θl θ₀ e t : J → ℝ)) t := by
  have hP := isProbabilityMeasure_family hS ν (θl θ₀ e t : J → ℝ)
  -- rewrite the first response on velocity coordinates
  have e1 : (fun s ↦ -lawCov (Pfam (θl θ₀ e s : J → ℝ)) F (dirLoss S (Vl θ₀ e s : J → ℝ))) =
      fun s ↦ -∑ i, (Vl θ₀ e s : J → ℝ) i * lawCov (Pfam (θl θ₀ e s : J → ℝ)) F (S i) := by
    funext s
    have := isProbabilityMeasure_family hS ν (θl θ₀ e s : J → ℝ)
    rw [lawCov_dirLoss_eq_sum hS _ hF]
  rw [e1]
  -- coordinates of the velocity and covariances along the line
  have hV : HasDerivAt (fun s ↦ (Vl θ₀ e s : J → ℝ))
      ((-mChristoffel hS ν (θl θ₀ e t) (Vl θ₀ e t) (Vl θ₀ e t) : 𝕍) : J → ℝ) t := by
    have h := (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_responseLineVel hS ν θ₀ e ht)
    exact h
  have hsum : HasDerivAt
      (fun s ↦ ∑ i, (Vl θ₀ e s : J → ℝ) i * lawCov (Pfam (θl θ₀ e s : J → ℝ)) F (S i))
      (∑ i, (((-mChristoffel hS ν (θl θ₀ e t) (Vl θ₀ e t) (Vl θ₀ e t) : 𝕍) : J → ℝ) i *
          lawCov (Pfam (θl θ₀ e t : J → ℝ)) F (S i) +
        (Vl θ₀ e t : J → ℝ) i * -thirdCentral (Pfam (θl θ₀ e t : J → ℝ)) F (S i)
          (dirLoss S (Vl θ₀ e t : J → ℝ)))) t := by
    refine HasDerivAt.fun_sum fun i _ ↦ ?_
    exact (hasDerivAt_pi.mp hV i).mul (hasDerivAt_lawCov_familyMeasure_path hS ν
      (hasDerivAt_responseLine_coe hS ν θ₀ e ht) hF (hS i))
  refine hsum.neg.congr_deriv ?_
  -- assemble: `−Cov(F, ⟨V',S⟩) + T(F, f_V, f_V)` with `V' = −C(V,V)`
  set θ := θl θ₀ e t with hθ
  set V := Vl θ₀ e t with hVdef
  set C := mChristoffel hS ν θ V V with hC
  have hcovC : ∑ i, ((-C : 𝕍) : J → ℝ) i * lawCov (Pfam (θ : J → ℝ)) F (S i) =
      -lawCov (Pfam (θ : J → ℝ)) F (dirLoss S (C : J → ℝ)) := by
    rw [lawCov_dirLoss_eq_sum hS _ hF, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by simp only [Submodule.coe_neg, Pi.neg_apply, neg_mul]
  have hthird : ∑ i, (V : J → ℝ) i * -thirdCentral (Pfam (θ : J → ℝ)) F (S i)
      (dirLoss S (V : J → ℝ)) =
      -thirdCentral (Pfam (θ : J → ℝ)) F (dirLoss S (V : J → ℝ)) (dirLoss S (V : J → ℝ)) := by
    have e : ∀ i, (V : J → ℝ) i * -thirdCentral (Pfam (θ : J → ℝ)) F (S i)
        (dirLoss S (V : J → ℝ)) =
        -((V : J → ℝ) i * thirdCentral (Pfam (θ : J → ℝ)) (S i) F (dirLoss S (V : J → ℝ))) :=
      fun i ↦ by rw [thirdCentral_comm₁₂]; ring
    simp only [e, Finset.sum_neg_distrib]
    rw [← thirdCentral_dirLoss_left (Pfam (θ : J → ℝ)) hS _ hF (bdd_dirLoss hS _),
      thirdCentral_comm₁₂]
  rw [Finset.sum_add_distrib, hcovC, hthird]
  -- the residual pairing
  have hFi := integrable_of_bdd_prob (Pfam (θ : J → ℝ)) hF
  set m := ∫ y, F y ∂Pfam (θ : J → ℝ) with hm
  have hbF : Bdd fun x ↦ F x - m := hF.sub (Bdd.const _)
  have hbV := bdd_modelScore hS ν θ V
  have hbC := bdd_modelScore hS ν θ C
  have hb1 : Integrable (fun x ↦ (F x - m) * (f θ V x * f θ V x)) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (hbF.mul (hbV.mul hbV))
  have hb2 : Integrable (fun x ↦ (F x - m) * G θ V V) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (hbF.mul (Bdd.const _))
  have hb3 : Integrable (fun x ↦ (F x - m) * f θ C x) (Pfam (θ : J → ℝ)) :=
    integrable_of_bdd_prob _ (hbF.mul hbC)
  have hb12 : Integrable (fun x ↦ (F x - m) * (f θ V x * f θ V x) - (F x - m) * G θ V V)
      (Pfam (θ : J → ℝ)) := hb1.sub hb2
  have e2 : (fun x ↦ (F x - m) * scoreResidual hS ν θ V V x) = fun x ↦
      ((F x - m) * (f θ V x * f θ V x) - (F x - m) * G θ V V) + (F x - m) * f θ C x := by
    funext x; simp only [scoreResidual]; ring
  rw [e2, integral_add hb12 hb3, integral_sub hb1 hb2, integral_mul_const,
    integral_sub hFi (integrable_const _), integral_const, probReal_univ, one_smul, ← hm, sub_self,
    zero_mul, sub_zero]
  -- `∫ (F − m) f_V f_V = T(F, ⟨V,S⟩, ⟨V,S⟩)` and `∫ (F − m) f_C = Cov(F, ⟨C,S⟩)`
  have e3 : ∫ x, (F x - m) * (f θ V x * f θ V x) ∂Pfam (θ : J → ℝ) =
      thirdCentral (Pfam (θ : J → ℝ)) F (dirLoss S (V : J → ℝ)) (dirLoss S (V : J → ℝ)) := by
    unfold thirdCentral modelScore
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  have e4 : ∫ x, (F x - m) * f θ C x ∂Pfam (θ : J → ℝ) =
      lawCov (Pfam (θ : J → ℝ)) F (dirLoss S (C : J → ℝ)) := by
    rw [lawCov_eq_integral_centred _ hF (bdd_dirLoss hS _)]
    rfl
  rw [e3, e4]
  ring

/-- **The observable-curvature bound**: `|E[(F − EF) r]| ≤ √Var(F) √E[r²]`. -/
theorem abs_secondResponse_le {F : X → ℝ} (hF : Bdd F) (θ u v : 𝕍) :
    |∫ x, (F x - ∫ y, F y ∂Pfam (θ : J → ℝ)) * scoreResidual hS ν θ u v x ∂Pfam (θ : J → ℝ)| ≤
      Real.sqrt (lawCov (Pfam (θ : J → ℝ)) F F) *
        Real.sqrt (∫ x, scoreResidual hS ν θ u v x ^ 2 ∂Pfam (θ : J → ℝ)) := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  have hbF : Bdd fun x ↦ F x - ∫ y, F y ∂Pfam (θ : J → ℝ) := hF.sub (Bdd.const _)
  have h := sq_integral_mul_le (Pfam (θ : J → ℝ)) hbF (bdd_scoreResidual hS ν θ u v)
  have hvar : ∫ x, (F x - ∫ y, F y ∂Pfam (θ : J → ℝ)) * (F x - ∫ y, F y ∂Pfam (θ : J → ℝ))
      ∂Pfam (θ : J → ℝ) = lawCov (Pfam (θ : J → ℝ)) F F :=
    (lawCov_eq_integral_centred _ hF hF).symm
  have hsq : ∫ x, scoreResidual hS ν θ u v x * scoreResidual hS ν θ u v x ∂Pfam (θ : J → ℝ) =
      ∫ x, scoreResidual hS ν θ u v x ^ 2 ∂Pfam (θ : J → ℝ) :=
    integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  rw [hvar, hsq] at h
  have h1 : 0 ≤ lawCov (Pfam (θ : J → ℝ)) F F := lawCov_self_nonneg _ hF
  have h2 : 0 ≤ ∫ x, scoreResidual hS ν θ u v x ^ 2 ∂Pfam (θ : J → ℝ) :=
    integral_nonneg fun x ↦ sq_nonneg _
  rw [← Real.sqrt_mul h1]
  exact Real.abs_le_sqrt h

/-- Under saturation every second response vanishes. -/
theorem secondResponse_eq_zero_of_saturated (θ : 𝕍) (hsat : SaturatedAt S ν θ) (F : X → ℝ)
    (u v : 𝕍) :
    ∫ x, (F x - ∫ y, F y ∂Pfam (θ : J → ℝ)) * scoreResidual hS ν θ u v x ∂Pfam (θ : J → ℝ) = 0 := by
  have h := scoreResidual_eq_zero_ae_of_saturated hS ν θ hsat u v
  refine integral_eq_zero_of_ae ?_
  filter_upwards [h] with x hx
  simp [hx]

/-- **Saturation is universal response flatness**: the second response of every bounded observable
in every direction vanishes at `θ` iff the family is saturated at `θ`. -/
theorem saturatedAt_iff_secondResponse_eq_zero (θ : 𝕍) :
    SaturatedAt S ν θ ↔ ∀ (F : X → ℝ), Bdd F → ∀ u v : 𝕍,
      ∫ x, (F x - ∫ y, F y ∂Pfam (θ : J → ℝ)) * scoreResidual hS ν θ u v x ∂Pfam (θ : J → ℝ) =
        0 := by
  have hP := isProbabilityMeasure_family hS ν (θ : J → ℝ)
  constructor
  · intro hsat F _ u v
    exact secondResponse_eq_zero_of_saturated hS ν θ hsat F u v
  · intro hflat u v
    -- test against the residual itself: `E[r²] = 0`
    have hr := hflat _ (bdd_scoreResidual hS ν θ u v) u v
    simp only [integral_scoreResidual hS ν, sub_zero] at hr
    have hint : Integrable (fun x ↦ scoreResidual hS ν θ u v x * scoreResidual hS ν θ u v x)
        (Pfam (θ : J → ℝ)) :=
      integrable_of_bdd_prob _ ((bdd_scoreResidual hS ν θ u v).mul (bdd_scoreResidual hS ν θ u v))
    have h0 := (integral_eq_zero_iff_of_nonneg (fun x ↦ mul_self_nonneg _) hint).mp hr
    refine ⟨-mChristoffel hS ν θ u v, ?_⟩
    filter_upwards [h0] with x hx
    simp only [Pi.zero_apply, mul_self_eq_zero, scoreResidual] at hx
    simp only [modelScore, Submodule.coe_neg, dirLoss_neg, integral_neg]
    simp only [modelScore] at hx
    linarith

/-- **The response of fluctuations**: `d/dt Var_{θ_t}(F) = −Cov_{θ_t}((F − EF)², ⟨V_t, S⟩)`. -/
theorem hasDerivAt_lineVariance {F : X → ℝ} (hF : Bdd F) (θ₀ e : 𝕍) {t : ℝ}
    (ht : t ∈ responseLineDomain S ν θ₀ e) :
    HasDerivAt (fun s ↦ lawCov (Pfam (θl θ₀ e s : J → ℝ)) F F)
      (-thirdCentral (Pfam (θl θ₀ e t : J → ℝ)) F F (dirLoss S (Vl θ₀ e t : J → ℝ))) t :=
  hasDerivAt_lawCov_familyMeasure_path hS ν (hasDerivAt_responseLine_coe hS ν θ₀ e ht) hF hF

end Observable

end Laplace.Multi
