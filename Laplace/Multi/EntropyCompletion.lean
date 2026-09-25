/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ConditioningChainRule

/-!
# The completion principle: every finite-rate response has a unique entropy minimiser

For a probability law `ν` with bounded features `S` and a response `M` of finite rate,
  `∃! ρ, ρ probability ∧ E_ρ S = M ∧ KL(ρ ‖ ν) = 𝓘_ν(M)`     (`exists_unique_entropy_minimiser`),
and consequently the constrained relative entropy is the rate **everywhere**:
  `entropyProj ν S M = genRate ν S M`                          (`entropyProj_eq_genRate`).

The proof is a strong induction on the affine dimension of the moment body, over all probability
laws on the sample space with the same features. A response of finite rate lies in the moment body.
If it lies in the relative interior, it is the mean of a member `ν.tilted(−θ·S)` of the exponential
family (`range_meanMap_eq_intrinsicInterior_momentBody`), which attains the rate and is the unique
minimiser (`klDiv_familyMeasure_zero`, `rateFun_meanMap`, `klDiv_eq_rateFun_iff`). Otherwise a
supporting functional `e·` maximised at `M` and not constant on the body exists
(`mem_intrinsicInterior_iff_forall_supporting`); its face `F = {e·S = e·M}` has positive mass
(else the rate would be infinite, `genRate_eq_top_of_null_face`), the rate decomposes as
`𝓘_ν(M) = −log ν(F) + 𝓘_{ν_F}(M)` (`genRate_face_eq`), the affine dimension of the moment body of
`ν_F` is strictly smaller (`finrank_dirSpan_faceMeasure_lt`), and the induction hypothesis for
`ν_F` gives the minimiser; the chain rule `KL(ρ ‖ ν) = KL(ρ ‖ ν_F) − log ν(F)` for laws carried by
`F` (`klDiv_eq_klDiv_faceMeasure_add`) transports existence and uniqueness back to `ν`, any
competitor being carried by `F` because its mean lies on the face (`compl_eq_zero_of_mean_face`).

So the minimiser is a bounded exponential tilt of a law obtained from `ν` by at most
`dim` positive-mass exposed conditionings: interior response charts, accessible conditional walls
with additive entry costs, and infinite-rate inaccessible boundary points are all readings of one
constrained relative entropy.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
include hS

/-- **The completion principle**: every response of finite rate has a unique entropy minimiser. -/
theorem exists_unique_entropy_minimiser (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
    (hfin : genRate ν S M ≠ ⊤) :
    ∃! ρ : Measure X, IsProbabilityMeasure ρ ∧ (fun i ↦ ∫ x, S i x ∂ρ) = M ∧
      klDiv ρ ν = genRate ν S M := by
  suffices H : ∀ n : ℕ, ∀ (ν : Measure X) [IsProbabilityMeasure ν],
      Module.finrank ℝ (dirSpan ν (fun _ ↦ (1 : ℝ)) S) = n → ∀ M : J → ℝ, genRate ν S M ≠ ⊤ →
        ∃! ρ : Measure X, IsProbabilityMeasure ρ ∧ (fun i ↦ ∫ x, S i x ∂ρ) = M ∧
          klDiv ρ ν = genRate ν S M from H _ ν rfl M hfin
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ν _ hn M hfin
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hπpos : (0 : ℝ) < ∫ x, (fun _ : X ↦ (1 : ℝ)) x ∂ν := by simp
  have hπi : Integrable (fun _ : X ↦ (1 : ℝ)) ν := integrable_const _
  have hπ : ∀ x, (0 : ℝ) < (fun _ : X ↦ (1 : ℝ)) x := fun _ ↦ one_pos
  have hrate : genRate ν S M = rateFun ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 M :=
    genRate_eq_rateFun ν S M
  have hMK : M ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S := by
    by_contra h
    refine hfin ?_
    rw [hrate]
    exact rateFun_eq_top_of_not_mem measurable_const hπi hπ hπpos measurable_const h0 hS (t := 1) h
  by_cases hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)
  · rw [← range_meanMap_eq_intrinsicInterior_momentBody measurable_const hπi hπ hπpos hS] at hrel
    obtain ⟨θ, hθ⟩ := hrel
    have hQ := familyMeasure_one_zero ν S
    have hP := isProbabilityMeasure_familyMeasure measurable_const hπi hπ hπpos measurable_const h0
      hS (t := 1) θ
    have hmean : (fun i ↦ ∫ x, S i x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) =
        M := by
      rw [← hθ]
      exact funext fun i ↦
        integral_familyMeasure measurable_const hπi hπ hπpos measurable_const h0 hS θ (S i)
    have hkl0 := klDiv_familyMeasure_zero measurable_const hπi hπ hπpos measurable_const h0 hS
      one_pos θ
    rw [hQ] at hkl0
    have hkl : klDiv (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ) ν =
        genRate ν S M := by
      rw [hkl0, hrate, ← hθ,
        rateFun_meanMap measurable_const hπi hπ hπpos measurable_const h0 hS one_pos θ]
    refine ⟨familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ, ⟨hP, hmean, hkl⟩,
      fun ρ ⟨hρP, hρM, hρkl⟩ ↦ ?_⟩
    have hiff := klDiv_eq_rateFun_iff measurable_const hπi hπ hπpos measurable_const h0 hS one_pos
      θ ρ (hρM.trans hθ.symm)
    rw [hQ] at hiff
    refine hiff.1 ?_
    rw [hρkl, hrate, ← hθ]
  · rw [mem_intrinsicInterior_iff_forall_supporting (convex_momentBody S)] at hrel
    push Not at hrel
    obtain ⟨e, he, y₁, hy₁, hne⟩ := hrel hMK
    obtain ⟨F, hFdef⟩ : ∃ F : Set X, F = {x | dirLoss S e x = dotJ e M} := ⟨_, rfl⟩
    have hF : MeasurableSet F := by
      rw [hFdef]
      exact measurableSet_eq_fun (bdd_dirLoss hS e).1 measurable_const
    have hβ : ∀ᵐ x ∂ν, dirLoss S e x ≤ dotJ e M := by
      filter_upwards [ae_statPoint_mem_essRange (μ := ν) measurable_const hπ hS] with x hx
      exact he _ (essRange_subset_momentBody S hx)
    have hF0 : ν F ≠ 0 := by
      intro h0'
      refine hfin (genRate_eq_top_of_null_face ν hS hβ ?_ rfl)
      rw [← hFdef]
      exact h0'
    have hp : 0 < ν.real F := ENNReal.toReal_pos hF0 (measure_ne_top _ _)
    have hface := genRate_face_eq ν hS hβ (by rw [← hFdef]; exact hp) rfl
    rw [← hFdef] at hface
    have hPF := isProbabilityMeasure_faceMeasure ν hF0
    have hfinF : genRate (faceMeasure ν F) S M ≠ ⊤ := by
      intro h
      rw [h, add_top] at hface
      exact hfin hface
    have hlt := finrank_dirSpan_faceMeasure_lt ν hF hS hp hFdef hy₁ hMK hne
    rw [hn] at hlt
    obtain ⟨ρ, ⟨hρP, hρM, hρkl⟩, huniq⟩ := ih _ hlt (faceMeasure ν F) rfl M hfinF
    have hρac : ρ ≪ faceMeasure ν F := (klDiv_ne_top_iff.1 (by rw [hρkl]; exact hfinF)).1
    have hchain := klDiv_eq_klDiv_faceMeasure_add ν hF hp ρ hρac
    refine ⟨ρ, ⟨hρP, hρM, ?_⟩, fun ρ' ⟨hρ'P, hρ'M, hρ'kl⟩ ↦ ?_⟩
    · rw [hchain, hρkl, hface, add_comm]
    · have hρ'ν : ρ' ≪ ν := (klDiv_ne_top_iff.1 (by rw [hρ'kl]; exact hfin)).1
      have hcompl : ρ' Fᶜ = 0 := by
        rw [hFdef]
        exact compl_eq_zero_of_mean_face ν hS ρ' hρ'ν hβ (by rw [hρ'M])
      have hρ'F : ρ' ≪ faceMeasure ν F := absolutelyContinuous_faceMeasure ν hF hρ'ν hcompl
      have hchain' := klDiv_eq_klDiv_faceMeasure_add ν hF hp ρ' hρ'F
      have hρ'klF : klDiv ρ' (faceMeasure ν F) = genRate (faceMeasure ν F) S M := by
        have h := hρ'kl
        rw [hchain', hface, add_comm] at h
        exact (ENNReal.add_right_inj ENNReal.ofReal_ne_top).1 h
      exact huniq ρ' ⟨hρ'P, hρ'M, hρ'klF⟩

/-- **The constrained relative entropy is the rate everywhere**: `𝓔_ν(M) = 𝓘_ν(M)` for every
response `M`, infinite values included. -/
theorem entropyProj_eq_genRate (ν : Measure X) [IsProbabilityMeasure ν] (M : J → ℝ) :
    entropyProj ν S M = genRate ν S M := by
  refine le_antisymm ?_ (genRate_le_entropyProj ν hS M)
  by_cases hfin : genRate ν S M = ⊤
  · rw [hfin]
    exact le_top
  · obtain ⟨ρ, ⟨hρP, hρM, hρkl⟩, -⟩ := exists_unique_entropy_minimiser hS ν hfin
    rw [← hρkl]
    exact entropyProj_le_klDiv ν ρ hρM

end Laplace.Multi
