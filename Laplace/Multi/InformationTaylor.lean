/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ThetaUniformPeano
import Laplace.Multi.FibreHessian
import Laplace.Multi.DualFlat
import Laplace.Multi.BiasForm

/-!
# The compact-uniform second-order expansion of the visible information

The visible information `𝓘(M) = KL(Π(M) ‖ ν)` has gradient `−θ(M)` and Hessian the Fisher form
`g_M` in response coordinates. Composing the interior differentiability of `𝓘` and of `θ` with the
generic uniform Peano lemma gives the compact-uniform expansion
`𝓘(M + h) = 𝓘(M) − ⟨h, θ(M)⟩ + ½ g_M(h, h) + O(ε ‖h‖²)` (`uniform_rate_peano`,
`rate_peano_at`), and the ambient bilinear extension `fisherAmb` of `g_M` through the direction
projection (`fisherAmb_coe`). These are the analytic inputs of the information-bias theorem.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The inverse chart derivative at `m₀ + z`. -/
local notation "Rat" z => (ContinuousLinearEquiv.symm (CDE (θr (m₀ + (z : J → ℝ)))) : 𝕍 →L[ℝ] 𝕍)

/-- The pairing `θ ↦ (v ↦ −⟨v, θ⟩)`, the gradient of the rate as a function of the natural
coordinate. -/
noncomputable def pairLin : 𝕍 →L[ℝ] (𝕍 →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ ↦ -(dotCLM (θ : J → ℝ)).comp (𝕍).subtypeL
      map_add' := fun θ η ↦ by
        ext v
        simp only [neg_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
          dotCLM_apply, add_apply, Submodule.coe_add, dotJ, Pi.add_apply, mul_add,
          Finset.sum_add_distrib]
        ring
      map_smul' := fun c θ ↦ by
        ext v
        simp only [neg_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
          dotCLM_apply, smul_apply, Submodule.coe_smul, dotJ, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        rw [mul_neg, Finset.mul_sum]
        refine congrArg Neg.neg (Finset.sum_congr rfl fun j _ ↦ ?_)
        ring }

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem pairLin_apply (θ v : 𝕍) : pairLin ν θ v = -dotJ (v : J → ℝ) (θ : J → ℝ) := by
  simp only [pairLin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    neg_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, dotCLM_apply]

/-- The rate is differentiable on the interior with gradient the pairing with `−θ`. -/
theorem hasFDerivAt_rate_add {z₀ : 𝕍}
    (hz₀ : m₀ + (z₀ : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    HasFDerivAt (fun z : 𝕍 ↦ (genRate ν S (m₀ + z)).toReal) (pairLin ν (θr (m₀ + z₀))) z₀ :=
  hasFDerivAt_genRate_response_at hS ν hz₀

/-- The gradient field of the rate is differentiable with derivative `pairLin ∘ R`. -/
theorem hasFDerivAt_pairLin_theta {z₀ : 𝕍}
    (hz₀ : m₀ + (z₀ : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    HasFDerivAt (fun z : 𝕍 ↦ pairLin ν (θr (m₀ + z))) ((pairLin ν).comp (Rat z₀)) z₀ :=
  (pairLin ν).hasFDerivAt.comp z₀ (hasFDerivAt_responseTheta_add_at hS ν hz₀)

/-- **The compact-uniform second-order expansion of the visible information** in the direction
picture of a compact convex interior set. -/
theorem uniform_rate_peano {C' : Set 𝕍} (hC : IsCompact C') (hCc : Convex ℝ C')
    (hC' : ∀ z ∈ C', m₀ + (z : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∀ ε > 0, ∃ δ > 0, ∀ z ∈ C', ∀ z' ∈ C', ‖z' - z‖ ≤ δ →
      ‖(genRate ν S (m₀ + z')).toReal - (genRate ν S (m₀ + z)).toReal -
        pairLin ν (θr (m₀ + (z : J → ℝ))) (z' - z) -
        (1 / 2 : ℝ) • ((pairLin ν).comp (Rat z)) (z' - z) (z' - z)‖ ≤ ε * ‖z' - z‖ ^ 2 :=
  uniform_peano_of_hasFDerivAt hC hCc (fun z hz ↦ hasFDerivAt_rate_add hS ν (hC' z hz))
    (fun z hz ↦ hasFDerivAt_pairLin_theta hS ν (hC' z hz))
    (continuousOn_const.clm_comp (continuousOn_inverse_add hS ν hC'))

/-- The quadratic term of the expansion is the Fisher form. -/
theorem pairLin_comp_inverse_apply {z : 𝕍}
    (hz : m₀ + (z : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) (w : 𝕍) :
    ((pairLin ν).comp (Rat z)) w w = fisherForm hS ν (m₀ + (z : J → ℝ)) w w := by
  rw [ContinuousLinearMap.comp_apply, pairLin_apply, fisherForm_eq_neg_dotJ hS ν hz, dotJ_comm]
  rfl

/-- **The ambient Fisher form** at an interior response, extended to the coordinate space through
the direction projection: `g_M(πu, πv) = −⟨R_M πu, πv⟩`. -/
noncomputable def fisherAmb (M : J → ℝ) : (J → ℝ) →ₗ[ℝ] (J → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v ↦
      -dotJ (((CDE (θr M)).symm (dirProj S ν u) : 𝕍) : J → ℝ) ((dirProj S ν v : 𝕍) : J → ℝ))
    (fun u u' v ↦ by
      simp only [map_add, Submodule.coe_add, dotJ_add_left]
      ring)
    (fun c u v ↦ by
      simp only [map_smul, Submodule.coe_smul, dotJ_smul_left, smul_eq_mul]
      ring)
    (fun u v v' ↦ by
      simp only [map_add, Submodule.coe_add]
      rw [dotJ_comm, dotJ_add_left, dotJ_comm, dotJ_comm (_ : J → ℝ) ((CDE _).symm _ : J → ℝ)]
      ring)
    (fun c u v ↦ by
      simp only [map_smul, Submodule.coe_smul, smul_eq_mul]
      rw [dotJ_comm, dotJ_smul_left, dotJ_comm]
      ring)

theorem fisherAmb_apply (M : J → ℝ) (u v : J → ℝ) :
    fisherAmb hS ν M u v =
      -dotJ (((CDE (θr M)).symm (dirProj S ν u) : 𝕍) : J → ℝ) ((dirProj S ν v : 𝕍) : J → ℝ) :=
  rfl

/-- On visible directions the ambient Fisher form is the Fisher form. -/
theorem fisherAmb_coe {M : J → ℝ}
    (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) (u v : 𝕍) :
    fisherAmb hS ν M (u : J → ℝ) (v : J → ℝ) = fisherForm hS ν M u v := by
  rw [fisherAmb_apply, dirProj_coe, dirProj_coe, fisherForm_eq_neg_dotJ hS ν hrel]

/-- **The second-order expansion of the visible information at an interior response**, uniform
on a compact convex interior neighbourhood: for visible `h` with `M + h ∈ C`,
`|𝓘(M + h) − 𝓘(M) + ⟨h, θ(M)⟩ − ½ g_M(h, h)| ≤ ε ‖h‖²` once `‖h‖ ≤ δ`. -/
theorem rate_peano_at {C : Set (J → ℝ)} (hC : IsCompact C) (hCc : Convex ℝ C)
    (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {M : J → ℝ} (hM : M ∈ C) :
    ∀ ε > 0, ∃ δ > 0, ∀ h : 𝕍, M + (h : J → ℝ) ∈ C → ‖h‖ ≤ δ →
      |(genRate ν S (M + h)).toReal - (genRate ν S M).toReal + dotJ (h : J → ℝ) (θr M : J → ℝ) -
        (1 / 2) * fisherAmb hS ν M (h : J → ℝ) (h : J → ℝ)| ≤ ε * ‖h‖ ^ 2 := by
  intro ε hε
  have hC' : IsCompact {z : 𝕍 | m₀ + (z : J → ℝ) ∈ C} := isCompact_preimage_add_mean ν hC
  have hCc' : Convex ℝ {z : 𝕍 | m₀ + (z : J → ℝ) ∈ C} := convex_preimage_add_mean ν hCc
  have hint : ∀ z ∈ {z : 𝕍 | m₀ + (z : J → ℝ) ∈ C},
      m₀ + (z : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) :=
    fun z hz ↦ hCK hz
  obtain ⟨δ, hδ, hpe⟩ := uniform_rate_peano hS ν hC' hCc' hint ε hε
  refine ⟨δ, hδ, fun h hMh hhδ ↦ ?_⟩
  have hMmem : M - m₀ ∈ 𝕍 := sub_mem_dirSpan_of_mem_momentBody measurable_const
    (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
    (intrinsicInterior_subset (hCK hM))
  obtain ⟨z, hz⟩ : ∃ z : 𝕍, z = ⟨M - m₀, hMmem⟩ := ⟨_, rfl⟩
  have hzM : m₀ + (z : J → ℝ) = M := by rw [hz]; simp
  have hz'M : m₀ + ((z + h : 𝕍) : J → ℝ) = M + h := by
    rw [Submodule.coe_add, ← add_assoc, hzM]
  have hzC : z ∈ {z : 𝕍 | m₀ + (z : J → ℝ) ∈ C} := by
    change m₀ + (z : J → ℝ) ∈ C
    rw [hzM]; exact hM
  have hz'C : z + h ∈ {z : 𝕍 | m₀ + (z : J → ℝ) ∈ C} := by
    change m₀ + ((z + h : 𝕍) : J → ℝ) ∈ C
    rw [hz'M]; exact hMh
  have key := hpe z hzC (z + h) hz'C (by rw [add_sub_cancel_left]; exact hhδ)
  rw [add_sub_cancel_left, pairLin_comp_inverse_apply hS ν (hint z hzC), hz'M, hzM,
    pairLin_apply, Real.norm_eq_abs, smul_eq_mul, ← fisherAmb_coe hS ν (hCK hM)] at key
  have e : (genRate ν S (M + h)).toReal - (genRate ν S M).toReal +
      dotJ (h : J → ℝ) (θr M : J → ℝ) - 1 / 2 * fisherAmb hS ν M (h : J → ℝ) (h : J → ℝ) =
      (genRate ν S (M + h)).toReal - (genRate ν S M).toReal - -dotJ (h : J → ℝ) (θr M : J → ℝ) -
        1 / 2 * fisherAmb hS ν M (h : J → ℝ) (h : J → ℝ) := by ring
  rw [e]
  exact key

end Laplace.Multi
