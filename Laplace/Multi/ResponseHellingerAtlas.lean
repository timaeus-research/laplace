/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseLocalTesting
import Laplace.Multi.ResponseProductAffinity

/-!
# The Hellinger atlas: Fisher and Hellinger topologies, stratum by stratum

Two separate assertions are kept apart.

* **On a finite regular stratum the two topologies agree** (`tendsto_fisherDist_iff_hellingerDist`,
  `tendsto_rootDensLp_iff_fisherDist`): on a coercive convex patch of interior means the Hellinger
  distance of the response laws and the intrinsic Fisher distance of the responses are
  bi-Lipschitz equivalent, `√λ d_F ≤ 2B H ≤ B d_F`, so convergence in one is convergence in the
  other.
* **Fisher convergence contracts to Hellinger convergence on the whole completion**
  (`hellingerExt`, `tendsto_rootDensExt`, `tendsto_integral_completionLaw`): the extended
  square-root density is `½`-Lipschitz, so completion convergence gives Hellinger convergence of
  the laws and convergence of every bounded test.
* **The converse is a genuine inverse-continuity theorem** and is proved only under a package:
  if the completion is compact and law fibres are singletons, then `x ↦ Ψ_x` is a closed embedding
  (`isClosedEmbedding_rootDensExt`) and completion convergence is equivalent to Hellinger
  convergence of the laws (`tendsto_iff_tendsto_rootDensExt`). Neither compactness of the
  completion nor uniqueness of the fibres is claimed here; an `L¹` compactification of the laws
  does not by itself give either.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Stratum

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

variable {U : Set (J → ℝ)} (hU : Convex ℝ U)
  (hUint : U ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hU hUint

/-- **Topology agreement on a finite regular stratum**: along a net of means in a coercive convex
patch, Fisher convergence of the responses is equivalent to Hellinger convergence of their laws. -/
theorem tendsto_fisherDist_iff_hellingerDist {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ M ∈ U, ∀ w : J → ℝ, lam * dotJ w w ≤ fisherVar S ν (θr M : J → ℝ) w)
    {a : J → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, dotJ (statPoint S x - a) (statPoint S x - a) ≤ B ^ 2)
    {α : Type*} {l : Filter α} {M : α → J → ℝ} (hM : ∀ n, M n ∈ U) {M₀ : J → ℝ} (hM₀ : M₀ ∈ U) :
    Tendsto (fun n ↦ fisherDist S ν (θr (M n)) (θr M₀)) l (𝓝 0) ↔
      Tendsto (fun n ↦ hellingerDist S ν (θr (M n) : J → ℝ) (θr M₀ : J → ℝ)) l (𝓝 0) := by
  have hsq : 0 < √lam := Real.sqrt_pos.2 hlam
  constructor
  · intro h
    refine squeeze_zero (fun n ↦ hellingerDist_nonneg S ν _ _) (fun n ↦ ?_)
      (by simpa using h.const_mul (1 / 2))
    exact (hellinger_fisher_sandwich hS ν hU hUint hlam hcoer hB0 hB (hM n) hM₀).2
  · intro h
    refine squeeze_zero (fun n ↦ fisherDist_nonneg) (fun n ↦ ?_)
      (by simpa using h.const_mul (2 * B / √lam))
    have h1 := (hellinger_fisher_sandwich hS ν hU hUint hlam hcoer hB0 hB (hM n) hM₀).1
    rw [div_mul_eq_mul_div, le_div_iff₀ hsq, mul_comm]
    exact h1

/-- **The same, in `L²`**: Fisher convergence of the responses is equivalent to convergence of the
square-root densities in `L²(ν)`. -/
theorem tendsto_rootDensLp_iff_fisherDist {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ M ∈ U, ∀ w : J → ℝ, lam * dotJ w w ≤ fisherVar S ν (θr M : J → ℝ) w)
    {a : J → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, dotJ (statPoint S x - a) (statPoint S x - a) ≤ B ^ 2)
    {α : Type*} {l : Filter α} {M : α → J → ℝ} (hM : ∀ n, M n ∈ U) {M₀ : J → ℝ} (hM₀ : M₀ ∈ U) :
    Tendsto (fun n ↦ rootDensLp hS ν (θr (M n) : J → ℝ)) l (𝓝 (rootDensLp hS ν (θr M₀ : J → ℝ))) ↔
      Tendsto (fun n ↦ fisherDist S ν (θr (M n)) (θr M₀)) l (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero, tendsto_fisherDist_iff_hellingerDist hS ν hU hUint hlam hcoer
    hB0 hB hM hM₀]
  simp only [dist_rootDensLp]

end Stratum

section Completion

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **The Hellinger distance between completion laws**: `H(Q_x, Q_y) = ‖Ψ_x − Ψ_y‖₂`. -/
noncomputable def hellingerExt (x y : FisherCompletion hS ν) : ℝ :=
  dist (rootDensExt hS ν x) (rootDensExt hS ν y)

/-- At finite points the extended Hellinger distance is the Hellinger distance of the family. -/
theorem hellingerExt_coe (p q : FisherPoint hS ν) :
    hellingerExt hS ν p q = hellingerDist S ν (p.param : J → ℝ) (q.param : J → ℝ) := by
  rw [hellingerExt, rootDensExt_coe, rootDensExt_coe, dist_rootDensLp]

/-- **Fisher contracts to Hellinger on the completion**: `H(Q_x, Q_y) ≤ d̂(x, y)/2`. -/
theorem hellingerExt_le (x y : FisherCompletion hS ν) : hellingerExt hS ν x y ≤ dist x y / 2 :=
  dist_rootDensExt_le hS ν x y

/-- **Completion convergence gives Hellinger convergence of the laws.** -/
theorem tendsto_rootDensExt {α : Type*} {l : Filter α} {x : α → FisherCompletion hS ν}
    {x₀ : FisherCompletion hS ν} (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun n ↦ rootDensExt hS ν (x n)) l (𝓝 (rootDensExt hS ν x₀)) :=
  ((continuous_rootDensExt hS ν).tendsto x₀).comp hx

/-- **Completion convergence gives convergence of every bounded test**: the laws converge in
total variation. -/
theorem tendsto_integral_completionLaw {α : Type*} {l : Filter α} {x : α → FisherCompletion hS ν}
    {x₀ : FisherCompletion hS ν} (hx : Tendsto x l (𝓝 x₀)) {φ : X → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : ∀ y, φ y ≤ 1) :
    Tendsto (fun n ↦ ∫ y, φ y ∂completionLaw hS ν (x n)) l
      (𝓝 (∫ y, φ y ∂completionLaw hS ν x₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (by simpa using (tendsto_iff_dist_tendsto_zero.1 hx).const_mul (1 / 2))
  rw [Real.norm_eq_abs, abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · refine (integral_rootLaw_sub_le ν (norm_rootDensExt hS ν _) (norm_rootDensExt hS ν _) hφm hφ0
      hφ1).trans ?_
    rw [← dist_eq_norm]
    have := hellingerExt_le hS ν (x n) x₀
    rw [hellingerExt] at this
    linarith
  · refine (integral_rootLaw_sub_le ν (norm_rootDensExt hS ν _) (norm_rootDensExt hS ν _) hφm hφ0
      hφ1).trans ?_
    rw [← dist_eq_norm, dist_comm]
    have := hellingerExt_le hS ν (x n) x₀
    rw [hellingerExt] at this
    linarith

/-- **The conditional inverse-continuity package**: if the completion is compact and law fibres
are singletons, the square-root density map is a closed embedding of the completion into `L²(ν)`.
-/
theorem isClosedEmbedding_rootDensExt [CompactSpace (FisherCompletion hS ν)]
    (huniq : ∀ x y : FisherCompletion hS ν, completionLaw hS ν x = completionLaw hS ν y → x = y) :
    Topology.IsClosedEmbedding (rootDensExt hS ν) :=
  (continuous_rootDensExt hS ν).isClosedEmbedding fun x y h ↦
    huniq x y (by rw [completionLaw_eq_rootLaw, completionLaw_eq_rootLaw, h])

/-- **Under the package, completion convergence is Hellinger convergence of the laws.** -/
theorem tendsto_iff_tendsto_rootDensExt [CompactSpace (FisherCompletion hS ν)]
    (huniq : ∀ x y : FisherCompletion hS ν, completionLaw hS ν x = completionLaw hS ν y → x = y)
    {α : Type*} {l : Filter α} {x : α → FisherCompletion hS ν} {x₀ : FisherCompletion hS ν} :
    Tendsto x l (𝓝 x₀) ↔
      Tendsto (fun n ↦ rootDensExt hS ν (x n)) l (𝓝 (rootDensExt hS ν x₀)) :=
  (isClosedEmbedding_rootDensExt hS ν huniq).isEmbedding.tendsto_nhds_iff

end Completion

end Laplace.Multi
