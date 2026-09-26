/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DualFlat
import Laplace.Multi.BoundaryBlowup
import Laplace.Multi.GlobalChart

/-!
# The structure theorem for the response map

One statement collecting the programme: for bounded features `S` and a featureless posterior `ν`,

1. **global chart** — the reconstruction `M ↦ Π(M)` is a homeomorphism from the direction subspace
   onto the relative interior of the moment body, strictly differentiable both ways, with `Π(M)` the
   unique entropy minimiser on its fibre;
2. **differential duality** — at every interior `M` the response scores satisfy
   `E_Q[ℓ_{M,u} ℓ_{M,z}] = −⟨R_M u, z⟩`, positive definite on `𝕍`, and the rate is a potential with
   Hessian the Fisher form and third derivative minus the cubic tensor;
3. **normal geometry** — the second derivative of the reconstruction density in response coordinates
   is `q_M N_M(ℓ_{M,u} ℓ_{M,w})`, and every bounded observable has the Peano expansion
   `E_{Π(M+z)}φ = E_Qφ + E_Q[φ ℓ_z] + ½ E_Q[φ N_M(ℓ_z²)] + o(‖z‖²)`;
4. **accounting** — for every data law `D` with interior response `M`,
   `E_D φ − E_ν φ = E_ν[φ ℓ_0] + ∫₀¹ (1−s) E_{Q_s}[φ N_{M_s}(ℓ_s²)] ds + E_D[N_M φ]`;
5. **boundary obstruction** — a finite-rate response on the relative boundary has `κ(s) → ∞` along
   the atlas, `∫₀¹ κ = ∞`, and logarithmic escape of the natural coordinates.
-/

open MeasureTheory Filter Topology Set InformationTheory

namespace Laplace.Multi

section Structure

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative as a linear equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The moment body. -/
local notation "K" => momentBody ν (fun _ ↦ (1 : ℝ)) S

include hS

/-- **The structure theorem for the response map.** -/
theorem response_structure_theorem :
    -- 1. global chart
    (∃ e : 𝕍 ≃ₜ intrinsicInterior ℝ K,
      (∀ θ, (e θ : J → ℝ) = meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) ∧
      (∀ θ, HasStrictFDerivAt (fun θ ↦ (e θ : J → ℝ)) ((𝕍).subtypeL.comp (chartDeriv
        measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS θ)) θ) ∧
      (∀ M : intrinsicInterior ℝ K, responseProjection hS ν M = Pfam (e.symm M)) ∧
      (∀ M : intrinsicInterior ℝ K, (fun i ↦ ∫ x, S i x ∂responseProjection hS ν M) = M ∧
        ∀ ρ : Measure X, IsProbabilityMeasure ρ → (fun i ↦ ∫ x, S i x ∂ρ) = (M : J → ℝ) →
          klDiv ρ ν = genRate ν S M → ρ = responseProjection hS ν M)) ∧
    -- 2. differential duality and the dual-flat structure
    (∀ M ∈ intrinsicInterior ℝ K, (∀ u z : 𝕍,
        ∫ x, responseScore hS ν M u x * responseScore hS ν M z x ∂(Pfam (θr M)) =
          -dotJ (ContinuousLinearEquiv.symm (CDE (θr M)) u : J → ℝ) z) ∧
      (∀ u : 𝕍, u ≠ 0 →
        0 < ∫ x, responseScore hS ν M u x * responseScore hS ν M u x ∂(Pfam (θr M))) ∧
      HasFDerivAt (fun z : 𝕍 ↦ (genRate ν S (M + z)).toReal)
        (-(dotCLM (θr M : J → ℝ)).comp (𝕍).subtypeL) 0 ∧
      (∀ u : 𝕍, ∃ L : 𝕍 →L[ℝ] ℝ, HasFDerivAt (fun z : 𝕍 ↦ -dotJ (θr (M + z) : J → ℝ) u) L 0 ∧
        ∀ w, L w = fisherForm hS ν M u w) ∧
      (∀ u w : 𝕍, ∃ L : 𝕍 →L[ℝ] ℝ, HasFDerivAt
        (fun z : 𝕍 ↦ -dotJ (ContinuousLinearEquiv.symm (CDE (θr (M + z))) u : J → ℝ) w) L 0 ∧
        ∀ v, L v = -cubicScore hS ν M u v w)) ∧
    -- 3. normal geometry: the polarised Hessian and the Peano expansion
    (∀ M ∈ intrinsicInterior ℝ K, (∀ (w : 𝕍) (x : X), ∃ L : 𝕍 →L[ℝ] ℝ,
        HasFDerivAt (fun z : 𝕍 ↦ famDens S ν (θr (M + z)) x * responseScore hS ν (M + z) w x)
          L 0 ∧
        ∀ u, L u = famDens S ν (θr M) x *
          normalProj hS ν M ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M w)) x) ∧
      ∀ φ : X → ℝ, Bdd φ →
        (fun z : 𝕍 ↦ (∫ x, φ x ∂(Pfam (θr (M + z)))) - (∫ x, φ x ∂(Pfam (θr M))) -
          (∫ x, φ x * responseScore hS ν M z x ∂(Pfam (θr M))) -
          (1 / 2) * ∫ x, φ x * normalProj hS ν M
            ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x ∂(Pfam (θr M)))
          =o[𝓝 0] fun z ↦ ‖z‖ ^ 2) ∧
    -- 4. the accounting identity
    (∀ M ∈ intrinsicInterior ℝ K, ∀ hfin : genRate ν S M ≠ ⊤,
      ∀ D : Measure X, IsProbabilityMeasure D → (fun j ↦ ∫ x, S j x ∂D) = M →
      ∀ φ : X → ℝ, ∀ hφ : Bdd φ,
        (∫ x, φ x ∂D) - (∫ x, φ x ∂ν) =
          (∫ x, φ x * atlasScore hS ν hfin 0 x ∂ν) +
            (∫ t in (0 : ℝ)..1, (1 - t) * ∫ x, φ x * normalProj hS ν (atlasPath S ν M t)
              (bdd_atlasScore_sq hS ν hfin (s := t)) x ∂(Pfam (atlasTheta hS ν M t))) +
            ∫ x, normalProj hS ν M hφ x ∂D) ∧
    -- 5. the boundary obstruction
    ∀ M (hfin : genRate ν S M ≠ ⊤), M ∉ intrinsicInterior ℝ K →
      Tendsto (atlasCurv hS ν hfin) (𝓝[<] (1 : ℝ)) atTop ∧
      ¬ IntervalIntegrable (atlasCurv hS ν hfin) volume 0 1 := by
  refine ⟨global_response_chart hS ν, fun M hrel ↦ ?_, fun M hrel ↦ ?_,
    fun M hrel hfin D _ hD φ hφ ↦ response_accounting hS ν hfin hrel D hD hφ, fun M hfin hbd ↦
    ⟨tendsto_atlasCurv_nhdsLT_one hS ν hfin hbd, not_intervalIntegrable_atlasCurv hS ν hfin hbd⟩⟩
  · obtain ⟨h1, h2, h3, -, -⟩ := dual_flat_structure hS ν hrel
    exact ⟨integral_responseScore_mul hS ν hrel,
      fun u hu ↦ integral_responseScore_sq_pos hS ν hrel hu, h1, h2, h3⟩
  · exact ⟨hasFDerivAt_famDens_responseScore hS ν hrel, fun φ hφ ↦ response_peano hS ν hrel hφ⟩

end Structure

end Laplace.Multi
