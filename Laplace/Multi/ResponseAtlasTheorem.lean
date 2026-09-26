/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DensityPeanoUniform
import Laplace.Multi.AtlasTotalVariation

/-!
# The response atlas and reconstruction theorem

The programme "map the space of responses across the data manifold, from the featureless posterior
to the data law" is packaged as one statement in four layers (`response_atlas_reconstruction`):

* **B. Dependence on the data law.** The reconstruction `D ↦ Π(E_D S)` is a retraction of
  distribution space onto the family (it fixes every family member), its derivative
  `u ↦ Π(M) ℓ_{M,u}` has zero mass and transmits exactly the moment perturbation, and it is
  total-variation Lipschitz on every compact convex set of interior responses.
* **A. Interior response geometry.** On every compact convex set of interior responses the
  reconstructed density has a compact-uniform relative second-order expansion
  `q_{M+z} = q_M (1 + ℓ_{M,z} + ½ N_M(ℓ_{M,z}²)) + o(‖z‖²)`.
* **C. Radial transport of laws, observables and information.** Along the straight atlas of any
  finite-rate response `M`: the accounting identity
  `E_{Q_t}φ − E_νφ = t E_ν[φℓ_0] + ∫₀ᵗ (t − u) E_{Q_u}[φ N(ℓ_u²)] du` for `t < 1`; the total
  variation moves at most at the Fisher speed, `∫ |q_s − q_t| ≤ ∫_t^s √κ`; and for every data law
  `D` with response `M` and finite information the budget
  `KL(D ‖ ν) = KL(D ‖ Π(M)) + ∫₀¹ (1 − s) κ_s ds` (invisible plus visible information).
* **D. Finite-rate boundary completion.** The atlas completes at `s = 1` to the information
  projection `Π(M)`: `KL(Π(M) ‖ Q_s) = ∫_s^1 (1 − u) κ_u du → 0`, every bounded observable's
  response converges, and the accounting identity holds in the limit.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **The information budget at every finite-rate response**: for a data law with response `M` and
finite information, `KL(D ‖ ν) = KL(D ‖ Π(M)) + ∫₀¹ (1 − s) κ_s ds`. -/
theorem klDiv_data_eq_add_integral_of_ne_top {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
    (D : Measure X) [IsProbabilityMeasure D] (hDkl : klDiv D ν ≠ ⊤)
    (hD : (fun j ↦ ∫ x, S j x ∂D) = M) :
    (klDiv D ν).toReal = (klDiv D (responseProjection hS ν M)).toReal +
      ∫ s in Ioo (0 : ℝ) 1, (1 - s) * atlasCurv hS ν hfin s := by
  obtain ⟨-, -, -, hpyth⟩ := responseProjection_spec hS ν hfin
  have h := hpyth D inferInstance hD
  have hDQ : klDiv D (responseProjection hS ν M) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at h
    exact hDkl h
  rw [h, ENNReal.toReal_add hDQ hfin, genRate_toReal_eq_integral_atlasCurv hS ν hfin]

/-- **The response atlas and reconstruction theorem** (four layers, see the module docstring). -/
theorem response_atlas_reconstruction :
    -- B. dependence on the data law: retraction, derivative projection, TV-Lipschitz on compacts
    ((∀ θ : J → ℝ, responseProjection hS ν (fun i ↦ ∫ x, S i x ∂(Pfam θ)) = Pfam θ) ∧
      (∀ M : J → ℝ, M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) → ∀ u : 𝕍,
        (∫ x, responseScore hS ν M u x ∂(Pfam (θr M))) = 0 ∧
          respCov hS ν M (responseScore hS ν M u) = u) ∧
      (∀ C : Set (J → ℝ), IsCompact C → Convex ℝ C →
        C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) →
        ∃ L : ℝ, 0 ≤ L ∧ ∀ M ∈ C, ∀ M' ∈ C,
          ∫ x, |famDens S ν (θr M') x - famDens S ν (θr M) x| ∂ν ≤ L * ‖M' - M‖)) ∧
    -- A. interior response geometry: compact-uniform relative second-order expansion
    (∀ C : Set (J → ℝ), IsCompact C → Convex ℝ C →
      C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) →
      ∀ ε > 0, ∃ δ > 0, ∀ M ∈ C, ∀ z : 𝕍, M + (z : J → ℝ) ∈ C → ‖z‖ ≤ δ → ∀ x,
        |famDens S ν (θr (M + z)) x - famDens S ν (θr M) x * (1 + responseScore hS ν M z x +
          (1 / 2) * normalProj hS ν M
            ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)| ≤
        ε * ‖z‖ ^ 2 * famDens S ν (θr M) x) ∧
    -- C and D. radial transport and boundary completion at every finite-rate response
    (∀ (M : J → ℝ) (hfin : genRate ν S M ≠ ⊤),
      -- C1. the accounting identity on `[0, t]`
      (∀ t : ℝ, 0 ≤ t → t < 1 → ∀ φ : X → ℝ, Bdd φ →
        (∫ x, φ x ∂(Pfam (atlasTheta hS ν M t))) - (∫ x, φ x ∂ν) =
          t * (∫ x, φ x * atlasScore hS ν hfin 0 x ∂ν) +
            ∫ u in (0 : ℝ)..t, (t - u) * ∫ x, φ x * normalProj hS ν (atlasPath S ν M u)
              (bdd_atlasScore_sq hS ν hfin (s := u)) x ∂(Pfam (atlasTheta hS ν M u))) ∧
      -- C2. total variation moves at most at the Fisher speed
      (∀ t s : ℝ, 0 ≤ t → t ≤ s → s < 1 →
        ∫ x, |famDens S ν (atlasTheta hS ν M s) x - famDens S ν (atlasTheta hS ν M t) x| ∂ν ≤
          ∫ u in t..s, √(atlasCurv hS ν hfin u)) ∧
      -- C3. the information budget of every data law with response `M`
      (∀ D : Measure X, IsProbabilityMeasure D → klDiv D ν ≠ ⊤ →
        (fun j ↦ ∫ x, S j x ∂D) = M →
        (klDiv D ν).toReal = (klDiv D (responseProjection hS ν M)).toReal +
          ∫ s in Ioo (0 : ℝ) 1, (1 - s) * atlasCurv hS ν hfin s) ∧
      -- D. the boundary completion package
      (IsProbabilityMeasure (responseProjection hS ν M) ∧
        (fun i ↦ ∫ x, S i x ∂responseProjection hS ν M) = M ∧
        klDiv (responseProjection hS ν M) ν = genRate ν S M ∧
        (∀ ρ : Measure X, IsProbabilityMeasure ρ → (fun i ↦ ∫ x, S i x ∂ρ) = M →
          klDiv ρ ν = klDiv ρ (responseProjection hS ν M) + genRate ν S M) ∧
        (∀ s : ℝ, 0 ≤ s → s < 1 →
          (klDiv (responseProjection hS ν M) (Pfam (atlasTheta hS ν M s))).toReal =
            ∫ u in s..1, (1 - u) * atlasCurv hS ν hfin u) ∧
        Tendsto (fun s ↦ klDiv (responseProjection hS ν M) (Pfam (atlasTheta hS ν M s)))
          (𝓝[<] (1 : ℝ)) (𝓝 0) ∧
        (∀ φ : X → ℝ, Bdd φ → Tendsto (fun t ↦ ∫ x, φ x ∂(Pfam (atlasTheta hS ν M t)))
          (𝓝[<] (1 : ℝ)) (𝓝 (∫ x, φ x ∂responseProjection hS ν M))) ∧
        (∀ φ : X → ℝ, Bdd φ →
          Tendsto (fun t ↦ t * (∫ x, φ x * atlasScore hS ν hfin 0 x ∂ν) +
            ∫ u in (0 : ℝ)..t, (t - u) * ∫ x, φ x * normalProj hS ν (atlasPath S ν M u)
              (bdd_atlasScore_sq hS ν hfin (s := u)) x ∂(Pfam (atlasTheta hS ν M u)))
            (𝓝[<] (1 : ℝ)) (𝓝 ((∫ x, φ x ∂responseProjection hS ν M) - ∫ x, φ x ∂ν))))) :=
  ⟨reconstruction_retraction hS ν,
    fun _ hC hCc hCK ↦ famDens_response_peano_uniform hS ν hC hCc hCK,
    fun _ hfin ↦
      ⟨fun _ ht0 ht1 _ hφ ↦ integral_atlas_taylor_of_lt hS ν hfin ht0 ht1 hφ,
        fun _ _ ht0 hts hs1 ↦ integral_abs_famDens_atlas_sub_le hS ν hfin ht0 hts hs1,
        fun D _ hDkl hD ↦ klDiv_data_eq_add_integral_of_ne_top hS ν hfin D hDkl hD,
        boundary_completion hS ν hfin⟩⟩

end Laplace.Multi
