/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.VertexGapConditioning

/-!
# The vertex-gap criterion for natural-parameter convergence to a face

On a charged polytope `P = conv V`, let `M ∈ P` and let `(u, β)` expose the minimal face of `M`
(as supplied by `exists_exposing_polytope`), with a tight vertex `v₀` (`⟨u,v₀⟩ = β`, equivalently
`v₀` charged by `M`).  For a sequence of natural parameters `η_n`,

  `m_ν(η_n) → M  ⟺  m_{ν_F}(η_n) → M  ∧  ∀ v ∈ V, ⟨u,v⟩ < β → ⟨η_n, v − v₀⟩ → +∞`

(`tendsto_meanMap_iff_faceMean_and_vertexGaps`): the means of the family laws converge to `M`
exactly when the face-conditional means converge to `M` and every off-face vertex gap diverges.
The tangential part is a convergence statement inside the face family (a homeomorphism onto the
relative interior of the face), the normal part is a finite family of divergent linear
functionals of `η_n`: this is the topology of parameter escape towards a face, with a finite
certificate and no orthogonal decomposition.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Criterion

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hpoly hcharged

/-- **The vertex-gap criterion.** -/
theorem tendsto_meanMap_iff_faceMean_and_vertexGaps {u : J → ℝ} {β : ℝ}
    (hV : ∀ v ∈ V, dotJ u v ≤ β) {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ)))
    (hMβ : dotJ u M = β)
    (hF : minimalFacePoly V M =
      convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)))
    {v₀ : J → ℝ} (hv₀V : v₀ ∈ V) (hv₀β : dotJ u v₀ = β) (η : ℕ → J → ℝ) :
    Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η n)) atTop (𝓝 M) ↔
      Tendsto (fun n ↦ meanMap (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
        (fun _ ↦ (0 : ℝ)) S 1 (η n)) atTop (𝓝 M) ∧
      ∀ v ∈ V, dotJ u v < β → Tendsto (fun n ↦ dotJ (η n) (v - v₀)) atTop atTop := by
  have hp : 0 < ν.real {x | dirLoss S u x = β} :=
    faceFibre_pos_of_charged ν V hcharged hv₀V hv₀β
  have hv₀F : v₀ ∈ minimalFacePoly V M := by
    rw [hF]
    exact subset_convexHull ℝ _ (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hv₀V, hv₀β⟩))
  constructor
  · intro hlim
    exact ⟨tendsto_meanMap_faceMeasure_of_tendsto_meanMap hS ν u β V hpoly hcharged hV hp hM hMβ
      hlim, fun v hvV hvβ ↦ tendsto_vertexGap_of_tendsto_meanMap hS ν V hpoly hcharged hV hM hMβ
        hv₀V hv₀F hvV hvβ hlim⟩
  · rintro ⟨hface, hgap⟩
    exact tendsto_meanMap_of_faceMean_of_vertexGaps hS ν V u β hpoly hcharged hV hv₀V hv₀β hface
      hgap

/-- **The vertex-gap criterion with the exposing data of the minimal face**: for every `M` of a
charged polytope there are `u, β, v₀` for which the criterion holds. -/
theorem exists_vertexGap_criterion {M : J → ℝ} (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) :
    ∃ u : J → ℝ, ∃ β : ℝ, ∃ v₀ ∈ V, (∀ v ∈ V, dotJ u v ≤ β) ∧ dotJ u v₀ = β ∧ dotJ u M = β ∧
      minimalFacePoly V M =
        convexHull ℝ ((V.filter fun v ↦ dotJ u v = β : Finset (J → ℝ)) : Set (J → ℝ)) ∧
      ∀ η : ℕ → J → ℝ,
        Tendsto (fun n ↦ meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η n)) atTop (𝓝 M) ↔
          Tendsto (fun n ↦ meanMap (faceMeasure ν {x | dirLoss S u x = β}) (fun _ ↦ (1 : ℝ))
            (fun _ ↦ (0 : ℝ)) S 1 (η n)) atTop (𝓝 M) ∧
          ∀ v ∈ V, dotJ u v < β → Tendsto (fun n ↦ dotJ (η n) (v - v₀)) atTop atTop := by
  obtain ⟨u, β, hV, hMβ, ⟨v₀, hv₀V, hv₀β⟩, -, -, hF⟩ := exists_exposing_polytope ν V hcharged hM
  exact ⟨u, β, v₀, hv₀V, hV, hv₀β, hMβ, hF, fun η ↦
    tendsto_meanMap_iff_faceMean_and_vertexGaps hS ν V hpoly hcharged hV hM hMβ hF hv₀V hv₀β η⟩

end Criterion

end Laplace.Multi
