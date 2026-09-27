/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseTiltPathBudget
import Laplace.Multi.ResponseBilinearForm
import Laplace.Multi.FisherNormalisedSampling

/-!
# Continuity of the response forms along a journey through the data manifold

Along a coefficient path `g_t = ⟨a(t), h⟩` (`a ∈ C¹`) every object of the covariance-quotient
geometry varies continuously in `t`:

* the forcings `b_{g_t}(k)` and the response velocities `DΦ_{g_t}[k]` of fixed bounded contrasts
  (`continuous_forcing_coeff`, `continuous_responseVel_coeff`);
* the bilinear response form `G_{g_t}(k, ℓ)` and the pull-back speed `G_{g_t}(ġ_t)`
  (`continuous_pullbackBilin_coeff`, `continuous_pullbackForm_coeff`);
* the effective dimension `d_eff(t) = tr(R_{Φ(g_t)} C_{ρ_t})` of the Fisher-normalised sampling
  noise (`continuous_effDim_coeff`).

So the quotient geometry, its noise floor and the chamber margins it certifies vary continuously
with the data law along any journey through data.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Continuity

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {ι : Type*} [Fintype ι] {h : ι → X → ℝ} (hh : ∀ j, Bdd (h j)) {a a' : ℝ → ι → ℝ}
  (ha : ∀ t, HasDerivAt a (a' t) t) (ha' : Continuous a')
include hS hh ha ha'

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

omit [Fintype J] [Nonempty J] hS in
/-- Tilted covariances of fixed bounded contrasts are continuous along the path. -/
theorem continuous_lawCov_coeff {φ ψ : X → ℝ} (hφ : Bdd φ) (hψ : Bdd ψ) :
    Continuous fun t ↦ lawCov (ν.tilted (dirLoss h (a t))) φ ψ := by
  have e : ∀ t, lawCov (ν.tilted (dirLoss h (a t))) φ ψ =
      (∫ x, φ x * ψ x ∂ν.tilted (dirLoss h (a t))) -
        (∫ x, φ x ∂ν.tilted (dirLoss h (a t))) * ∫ x, ψ x ∂ν.tilted (dirLoss h (a t)) :=
    fun t ↦ rfl
  simp only [e]
  exact (continuous_integral_tilted_dirLoss ν hh ha ha' (hφ.mul hψ)).sub
    ((continuous_integral_tilted_dirLoss ν hh ha ha' hφ).mul
      (continuous_integral_tilted_dirLoss ν hh ha ha' hψ))

omit [Fintype J] [Nonempty J] in
/-- **The forcing of a fixed contrast is continuous along the path.** -/
theorem continuous_forcing_coeff {k : X → ℝ} (hk : Bdd k) :
    Continuous fun t ↦ forcing S ν (dirLoss h (a t)) k :=
  continuous_pi fun i ↦ continuous_lawCov_coeff ν hh ha ha' (hS i) hk

/-- **The response velocity of a fixed contrast is continuous along the path.** -/
theorem continuous_responseVel_coeff {k : X → ℝ} (hk : Bdd k) :
    Continuous fun t ↦ (responseVel hS ν (bdd_dirLoss hh (a t)) hk : J → ℝ) := by
  have hL : Continuous fun t ↦ ((CDE (coeffResponse hS ν h a t)).symm : 𝕍 →L[ℝ] 𝕍) :=
    (continuous_chartDerivEquiv_symm measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS).comp (continuous_coeffResponse hS ν hh ha ha')
  have hv : Continuous fun t ↦ (⟨forcing S ν (dirLoss h (a t)) k,
      forcing_mem_dirSpan hS ν (bdd_dirLoss hh (a t)) hk⟩ : 𝕍) :=
    Continuous.subtype_mk (continuous_forcing_coeff hS ν hh ha ha' hk) _
  exact continuous_subtype_val.comp (hL.clm_apply hv)

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] hh ha ha' in
theorem continuous_dotJ_comp {α : Type*} [TopologicalSpace α] {f g : α → J → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun t ↦ dotJ (f t) (g t) := by
  simp only [dotJ]
  exact continuous_finsetSum _ fun i _ ↦
    ((continuous_apply i).comp hf).mul ((continuous_apply i).comp hg)

/-- **The bilinear response form of fixed contrasts is continuous along the path.** -/
theorem continuous_pullbackBilin_coeff {k ℓ : X → ℝ} (hk : Bdd k) (hℓ : Bdd ℓ) :
    Continuous fun t ↦ pullbackBilin hS ν (bdd_dirLoss hh (a t)) hk hℓ := by
  have e : ∀ t, pullbackBilin hS ν (bdd_dirLoss hh (a t)) hk hℓ =
      -dotJ (responseVel hS ν (bdd_dirLoss hh (a t)) hk : J → ℝ)
        (forcing S ν (dirLoss h (a t)) ℓ) := fun t ↦ rfl
  simp only [e]
  exact (continuous_dotJ_comp (continuous_responseVel_coeff hS ν hh ha ha' hk)
    (continuous_forcing_coeff hS ν hh ha ha' hℓ)).neg

/-- **The pull-back speed is continuous along the path**: `t ↦ G_{g_t}(ġ_t)`. -/
theorem continuous_pullbackForm_coeff :
    Continuous fun t ↦ pullbackForm hS ν (bdd_dirLoss hh (a t)) (bdd_dirLoss hh (a' t)) := by
  have e : ∀ t, pullbackForm hS ν (bdd_dirLoss hh (a t)) (bdd_dirLoss hh (a' t)) =
      fisherVar S ν (coeffResponse hS ν h a t : J → ℝ)
        (responseVel hS ν (bdd_dirLoss hh (a t)) (bdd_dirLoss hh (a' t)) : J → ℝ) := fun t ↦ rfl
  simp only [e]
  have hA : Continuous fun t ↦ (coeffResponse hS ν h a t : J → ℝ) :=
    continuous_subtype_val.comp (continuous_coeffResponse hS ν hh ha ha')
  have hB := continuous_responseVel_tilt hS ν hh ha ha'
  change Continuous fun t ↦ (fun p : (J → ℝ) × (J → ℝ) ↦ fisherVar S ν p.1 p.2)
    ((coeffResponse hS ν h a t : J → ℝ),
      (responseVel hS ν (bdd_dirLoss hh (a t)) (bdd_dirLoss hh (a' t)) : J → ℝ))
  exact (continuous_fisherVar hS ν).comp (hA.prodMk hB)

/-- **The effective dimension is continuous along the path**:
`t ↦ tr(R_{Φ(g_t)} C_{ρ_t}) = −∑ (R_t)_{ab} Cov_{ρ_t}(S_a, S_b)`. -/
theorem continuous_effDim_coeff [DecidableEq J] (p : (J → ℝ) →ₗ[ℝ] 𝕍) :
    Continuous fun t ↦ -(∑ a₁, ∑ b,
      samplingOp hS ν (coeffResponse hS ν h a t) p (Pi.single b 1) a₁ *
        lawCov (ν.tilted (dirLoss h (a t))) (S a₁) (S b)) := by
  refine (continuous_finsetSum _ fun a₁ _ ↦ continuous_finsetSum _ fun b _ ↦
    Continuous.mul ?_ (continuous_lawCov_coeff ν hh ha ha' (hS a₁) (hS b))).neg
  have hL : Continuous fun t ↦ ((CDE (coeffResponse hS ν h a t)).symm : 𝕍 →L[ℝ] 𝕍) :=
    (continuous_chartDerivEquiv_symm measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS).comp (continuous_coeffResponse hS ν hh ha ha')
  have e : ∀ t, samplingOp hS ν (coeffResponse hS ν h a t) p (Pi.single b 1) a₁ =
      ((((CDE (coeffResponse hS ν h a t)).symm : 𝕍 →L[ℝ] 𝕍) (p (Pi.single b 1)) : 𝕍) : J → ℝ) a₁ :=
    fun t ↦ rfl
  simp only [e]
  exact (continuous_apply a₁).comp (continuous_subtype_val.comp (hL.clm_apply continuous_const))

end Continuity

end Laplace.Multi
