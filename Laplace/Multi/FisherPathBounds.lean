/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.SusceptibilityFisherBound

/-!
# The scalar lower bound on the Fisher speed

For a visible direction `v` at an interior response `M`, the Fisher speed squared is
`⟨v, C_M⁻¹ v⟩ = −⟨R_M v, v⟩`, and for every functional `u` the projection `⟨u, v⟩` is bounded by the
Fisher speed times the standard deviation of `⟨u, S⟩` under `q_M`:

  `⟨u, v⟩² ≤ Var_{q_M}⟨u,S⟩ · ⟨v, C_M⁻¹ v⟩`   (`sq_dotJ_le_lawCov_mul_fisher`).

This is Cauchy–Schwarz against the response score, `⟨u,v⟩ = Cov_{q_M}(⟨u,S⟩, ℓ_{M,v})`
(`dotJ_eq_lawCov_dirLoss_responseScore`).  Along any `C¹` interior path `M_s`, the progress of the
exposing functional is therefore dominated by the Fisher length weighted by the normal standard
deviation, `|⟨u, M'_s⟩| ≤ √Var_{q_{M_s}}⟨u,S⟩ · |M'_s|_F` (`abs_dotJ_deriv_le_sqrt_mul_fisher`):
the path-dependent form of the ray classification, whose denominator cannot be replaced by the
variance profile of a fixed ray in higher codimension (Astra's charged-square example).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Scalar

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family `P_θ = exp(−⟨θ,S⟩) ν / Z(θ)`. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The response chart `θ(M)`. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The inverse chart derivative `R_M = (Dm(θ(M))|_𝕍)⁻¹`. -/
local notation "Rinv" M => ContinuousLinearEquiv.symm (chartDerivEquiv measurable_const
  (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS (θr M))

variable {M : J → ℝ} (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

omit hrel in
/-- **The pairing with a visible direction is the covariance with the response score**:
`⟨u, v⟩ = Cov_{q_M}(⟨u,S⟩, ℓ_{M,v})`. -/
theorem dotJ_eq_lawCov_dirLoss_responseScore (u : J → ℝ) (v : 𝕍) :
    dotJ u (v : J → ℝ) =
      lawCov (Pfam (θr M)) (dirLoss S u) (responseScore hS ν M v) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  rw [lawCov_dirLoss_left hS _ u _ (bdd_responseScore hS ν M v)]
  have h := respCov_responseScore hS ν (M := M) v
  have h' : ∀ j, lawCov (Pfam (θr M)) (S j) (responseScore hS ν M v) = (v : J → ℝ) j :=
    fun j ↦ congrFun h j
  simp only [h', dotJ]

/-- **The scalar Fisher lower bound**: `⟨u, v⟩² ≤ Var_{q_M}⟨u,S⟩ · ⟨v, C_M⁻¹ v⟩`. -/
theorem sq_dotJ_le_lawCov_mul_fisher (u : J → ℝ) (v : 𝕍) :
    dotJ u (v : J → ℝ) ^ 2 ≤
      lawCov (Pfam (θr M)) (dirLoss S u) (dirLoss S u) *
        (-dotJ ((Rinv M) v : J → ℝ) (v : J → ℝ)) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have h := abs_linForm_le_sqrt_var_mul_sqrt hS ν hrel (bdd_dirLoss hS u) v
  rw [linForm_eq_lawCov_responseScore hS ν hrel (bdd_dirLoss hS u) v,
    ← dotJ_eq_lawCov_dirLoss_responseScore hS ν u v] at h
  have hvar := lawCov_self_nonneg (Pfam (θr M)) (bdd_dirLoss hS u)
  have hfis : 0 ≤ -dotJ ((Rinv M) v : J → ℝ) (v : J → ℝ) := by
    rw [← integral_responseScore_mul hS ν hrel v v]
    exact integral_nonneg fun x ↦ mul_self_nonneg _
  calc dotJ u (v : J → ℝ) ^ 2 = |dotJ u (v : J → ℝ)| ^ 2 := (sq_abs _).symm
    _ ≤ (√(lawCov (Pfam (θr M)) (dirLoss S u) (dirLoss S u)) *
          √(-dotJ ((Rinv M) v : J → ℝ) (v : J → ℝ))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hvar, Real.sq_sqrt hfis]

/-- The absolute form: `|⟨u, v⟩| ≤ √Var_{q_M}⟨u,S⟩ · √⟨v, C_M⁻¹ v⟩`. -/
theorem abs_dotJ_le_sqrt_lawCov_mul_sqrt_fisher (u : J → ℝ) (v : 𝕍) :
    |dotJ u (v : J → ℝ)| ≤
      √(lawCov (Pfam (θr M)) (dirLoss S u) (dirLoss S u)) *
        √(-dotJ ((Rinv M) v : J → ℝ) (v : J → ℝ)) := by
  have h := abs_linForm_le_sqrt_var_mul_sqrt hS ν hrel (bdd_dirLoss hS u) v
  rwa [linForm_eq_lawCov_responseScore hS ν hrel (bdd_dirLoss hS u) v,
    ← dotJ_eq_lawCov_dirLoss_responseScore hS ν u v] at h

end Scalar

end Laplace.Multi
