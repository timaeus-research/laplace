/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.SamplingResolution
import Laplace.Multi.DataRayFacet

/-!
# The response-side resolution floor

`SamplingResolution` compares the truth shift `⟨w, b_t⟩` of the structural coordinate with the
sampling noise `Var_{ρ_t}⟨w,S⟩/n` under the data law. The same signal is a covariance under the
**response** law: since the chart derivative maps the response velocity to the forcing,
`⟨w, b_t⟩ = −Cov_{P_{θ_t}}(⟨w,S⟩, ⟨θ'_t,S⟩)`, so Cauchy–Schwarz in the response Fisher form gives

`⟨w, b_t⟩² ≤ Var_{P_{θ_t}}⟨w,S⟩ · |θ'_t|²_F`   (`sq_dotJ_dataCov_le_responseSpeedSq`),

with equality along `w = θ'_t`. At a matched point (samples drawn from the model law `P_{θ_t}`)
the noise in direction `w` is `Var_{P_{θ_t}}⟨w,S⟩/n`, and the **response resolution floor** reads

`⟨w, b_t⟩² ≤ n · E[⟨w, M̂_n − m⟩²] · |θ'_t|²_F`,   hence   `δ² · n · |θ'_t|²_F ≥ 1`

for any truth shift `δ` that some direction of the observables resolves above the noise
(`response_resolution_floor`), and the floor is attained along the response velocity
(`sq_signal_eq_mul_noise_response_vel`). In words: a truth shift is resolvable at sample size `n`
exactly when its response displacement `δ |θ'_t|_F` exceeds `1/√n` — the sampling noise is
scale-free in the response Fisher geometry, and the chambers of the response that `n` samples can
tell apart are those of Fisher diameter at least of order `1/√n`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Response

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {h : X → ℝ} (hh : Bdd h)
include hS hh

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- **The truth shift pairs with the response velocity through the response Fisher form**:
`⟨w, b_t⟩ = −Cov_{P_{θ_t}}(⟨w,S⟩, ⟨θ'_t,S⟩)`. -/
theorem dotJ_dataCov_eq_neg_lawCov_response (t : ℝ) (w : J → ℝ) :
    dotJ w (dataCov S ν h t) =
      -lawCov (Pfam (dataTheta hS ν hh t : J → ℝ)) (dirLoss S w)
        (dirLoss S (dataThetaVel hS ν hh t : J → ℝ)) := by
  rw [← chartDeriv_dataThetaVel hS ν hh t, dotJ_chartDeriv_eq_neg_lawCov hS ν]

/-- **Signal against the response Fisher form**: `⟨w, b_t⟩² ≤ Var_{P_{θ_t}}⟨w,S⟩ · |θ'_t|²_F`. -/
theorem sq_dotJ_dataCov_le_responseSpeedSq (t : ℝ) (w : J → ℝ) :
    dotJ w (dataCov S ν h t) ^ 2 ≤
      fisherVar S ν (dataTheta hS ν hh t : J → ℝ) w * responseSpeedSq hS ν hh t := by
  have := isProbabilityMeasure_family_dataTheta hS ν hh t
  rw [dotJ_dataCov_eq_neg_lawCov_response hS ν hh, neg_sq, fisherVar, responseSpeedSq]
  exact lawCov_sq_le _ (bdd_dirLoss hS w) (bdd_dirLoss hS _)

/-- Along the response velocity the pairing is minus the response speed squared. -/
theorem dotJ_dataThetaVel_dataCov (t : ℝ) :
    dotJ (dataThetaVel hS ν hh t : J → ℝ) (dataCov S ν h t) = -responseSpeedSq hS ν hh t := by
  rw [responseSpeedSq_eq_neg_dotJ, neg_neg]

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Xs : ℕ → Ω → X)
  (hXm : ∀ i, Measurable (Xs i)) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P)
  (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
include hXm hid hind

/-- **The response-side resolution floor at a matched law**: with `n` samples from the model law
`P_{θ_t}`, `⟨w, b_t⟩² ≤ n · E[⟨w, M̂_n − m⟩²] · |θ'_t|²_F` in every direction `w`. -/
theorem sq_signal_le_mul_noise_response (t : ℝ)
    (hlaw : P.map (Xs 0) = Pfam (dataTheta hS ν hh t : J → ℝ)) {n : ℕ} (hn : 0 < n)
    (w : J → ℝ) :
    dotJ w (dataCov S ν h t) ^ 2 ≤
      n * (∫ ω, dotJ w (fun j ↦ sampleResponse S Xs n ω j -
        ∫ x, S j x ∂(Pfam (dataTheta hS ν hh t : J → ℝ))) ^ 2 ∂P) *
        responseSpeedSq hS ν hh t := by
  have := isProbabilityMeasure_family_dataTheta hS ν hh t
  rw [integral_sq_dotJ_sampleResponse_sub hS P _ Xs hXm hid hlaw hind hn w,
    mul_div_cancel₀ _ (by exact_mod_cast hn.ne')]
  exact sq_dotJ_dataCov_le_responseSpeedSq hS ν hh t w

/-- **Unresolvable truth shifts, response form**: a shift `δ` that moves the structural
coordinate in direction `w` by at least the sampling noise satisfies `δ² · n · |θ'_t|²_F ≥ 1`:
the response displacement `δ |θ'_t|_F` must exceed `1/√n`. -/
theorem response_resolution_floor (t : ℝ)
    (hlaw : P.map (Xs 0) = Pfam (dataTheta hS ν hh t : J → ℝ)) {n : ℕ} (hn : 0 < n)
    (w : J → ℝ) {δ : ℝ}
    (hnoise : 0 < ∫ ω, dotJ w (fun j ↦ sampleResponse S Xs n ω j -
      ∫ x, S j x ∂(Pfam (dataTheta hS ν hh t : J → ℝ))) ^ 2 ∂P)
    (hdetect : ∫ ω, dotJ w (fun j ↦ sampleResponse S Xs n ω j -
      ∫ x, S j x ∂(Pfam (dataTheta hS ν hh t : J → ℝ))) ^ 2 ∂P ≤
        (dotJ w (dataCov S ν h t) * δ) ^ 2) :
    1 ≤ δ ^ 2 * (n * responseSpeedSq hS ν hh t) := by
  have hkey := sq_signal_le_mul_noise_response hS ν hh P Xs hXm hid hind t hlaw hn w
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = ∫ ω, dotJ w (fun j ↦ sampleResponse S Xs n ω j -
      ∫ x, S j x ∂(Pfam (dataTheta hS ν hh t : J → ℝ))) ^ 2 ∂P := ⟨_, rfl⟩
  rw [← hNdef] at hnoise hdetect hkey
  rw [mul_pow] at hdetect
  have hV : 0 ≤ responseSpeedSq hS ν hh t := responseSpeedSq_nonneg hS ν hh t
  have hδ : 0 ≤ δ ^ 2 := sq_nonneg δ
  have h1 : N ≤ N * (δ ^ 2 * (n * responseSpeedSq hS ν hh t)) := by
    calc N ≤ dotJ w (dataCov S ν h t) ^ 2 * δ ^ 2 := hdetect
      _ ≤ (n * N * responseSpeedSq hS ν hh t) * δ ^ 2 := mul_le_mul_of_nonneg_right hkey hδ
      _ = N * (δ ^ 2 * (n * responseSpeedSq hS ν hh t)) := by ring
  exact le_of_mul_le_mul_left (by linarith [h1] : N * 1 ≤ N * (δ ^ 2 *
    (n * responseSpeedSq hS ν hh t))) hnoise

/-- **The floor is attained along the response velocity**: for `w = θ'_t`,
`⟨θ'_t, b_t⟩² = n · E[⟨θ'_t, M̂_n − m⟩²] · |θ'_t|²_F`. -/
theorem sq_signal_eq_mul_noise_response_vel (t : ℝ)
    (hlaw : P.map (Xs 0) = Pfam (dataTheta hS ν hh t : J → ℝ)) {n : ℕ} (hn : 0 < n) :
    dotJ (dataThetaVel hS ν hh t : J → ℝ) (dataCov S ν h t) ^ 2 =
      n * (∫ ω, dotJ (dataThetaVel hS ν hh t : J → ℝ) (fun j ↦ sampleResponse S Xs n ω j -
        ∫ x, S j x ∂(Pfam (dataTheta hS ν hh t : J → ℝ))) ^ 2 ∂P) *
        responseSpeedSq hS ν hh t := by
  have := isProbabilityMeasure_family_dataTheta hS ν hh t
  rw [integral_sq_dotJ_sampleResponse_sub hS P _ Xs hXm hid hlaw hind hn _,
    mul_div_cancel₀ _ (by exact_mod_cast hn.ne'), dotJ_dataThetaVel_dataCov hS ν hh, neg_sq, sq]
  rfl

end Response

end Laplace.Multi
