/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CurvedTransport
import Laplace.Multi.NormalForm

/-!
# The normal form is a `C^∞` diffeomorphism

The reconstruction `M ↦ [q_M]` is `C^∞` on the interior responses `Ω` (relative to the affine
hull, `contDiffOn_reconstructionL1_interior`), hence the response map `R(d) = [q_{m(d)}]` is `C^∞`
on the data space `U` (`contDiffOn_dataRecon`), and the normal-form coordinates
`Φ(d) = (m(d), d − R(d))` and their inverse `Ψ(M, k) = [q_M] + k` are `C^∞` on `U` and on
`Ω × K` respectively (`contDiffOn_normalForm`, `contDiffOn_normalFormInv`). Together with the
bijection `U ≃ Ω × K` of `NormalForm` this is the smooth global normal form of the response
retraction (`smooth_normal_form`): the data space is `C^∞`-diffeomorphic to
(response) × (invisible residual), and the response map is the projection onto the first factor.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

/-- An interior response is the featureless response plus the projected displacement. -/
theorem eq_add_dirProjL_sub_of_mem {M : J → ℝ} (hM : M ∈ Ω) :
    M = m₀ + (dirProjL S ν (M - m₀) : J → ℝ) := by
  rw [dirProjL_of_mem ν (sub_mem_dirSpan_of_mem_momentBody' hS ν
    (intrinsicInterior_subset (featureless_mem_intrinsicInterior hS ν))
    (intrinsicInterior_subset hM)), add_sub_cancel]

/-- The projected displacement of an interior response is an interior displacement from `m₀`. -/
theorem dirProjL_sub_mem_addDomain {M : J → ℝ} (hM : M ∈ Ω) :
    dirProjL S ν (M - m₀) ∈ addDomain S ν m₀ := by
  rw [mem_addDomain, ← eq_add_dirProjL_sub_of_mem hS ν hM]
  exact hM

/-- **The reconstruction is `C^∞` on the interior responses.** -/
theorem contDiffOn_reconstructionL1_interior : ContDiffOn ℝ ∞ (reconstructionL1 hS ν) Ω := by
  have h := (contDiffOn_reconstructionL1_add hS ν (featureless_mem_intrinsicInterior hS ν)).comp
    (f := fun M : J → ℝ ↦ dirProjL S ν (M - m₀))
    ((dirProjL S ν).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn
    fun M hM ↦ dirProjL_sub_mem_addDomain hS ν hM
  refine h.congr fun M hM ↦ ?_
  simp only [Function.comp_def]
  rw [← eq_add_dirProjL_sub_of_mem hS ν hM]

/-- **The response map is `C^∞` on the data space.** -/
theorem contDiffOn_dataRecon : ContDiffOn ℝ ∞ (dataRecon hS ν) (dataSet hS ν) :=
  (contDiffOn_reconstructionL1_interior hS ν).comp (momentL1 hS ν).contDiff.contDiffOn
    fun _ hd ↦ hd.2

/-- **The normal-form coordinates are `C^∞` on the data space.** -/
theorem contDiffOn_normalForm : ContDiffOn ℝ ∞ (normalForm hS ν) (dataSet hS ν) := by
  have e : normalForm hS ν = fun d ↦ (momentL1 hS ν d, d - dataRecon hS ν d) := rfl
  rw [e]
  exact (momentL1 hS ν).contDiff.contDiffOn.prodMk (contDiffOn_id.sub (contDiffOn_dataRecon hS ν))

/-- **The inverse normal form is `C^∞` on `Ω × K`.** -/
theorem contDiffOn_normalFormInv :
    ContDiffOn ℝ ∞ (normalFormInv hS ν) (Ω ×ˢ invisibleDirs hS ν) := by
  have e : normalFormInv hS ν = fun Mk : (J → ℝ) × (X →₁[ν] ℝ) ↦
      reconstructionL1 hS ν Mk.1 + Mk.2 := rfl
  rw [e]
  exact ((contDiffOn_reconstructionL1_interior hS ν).comp contDiffOn_fst
    fun Mk hMk ↦ hMk.1).add contDiffOn_snd

/-- **The smooth global normal form of the response retraction**: `Φ` and `Ψ` are mutually inverse
`C^∞` bijections between the data space `U` and `Ω × K`, and in these coordinates the response map
is the projection onto the response, `R(Ψ(M, k)) = [q_M]`. -/
theorem smooth_normal_form :
    ContDiffOn ℝ ∞ (normalForm hS ν) (dataSet hS ν) ∧
    ContDiffOn ℝ ∞ (normalFormInv hS ν) (Ω ×ˢ invisibleDirs hS ν) ∧
    (∀ d ∈ dataSet hS ν, (normalForm hS ν d).1 ∈ Ω ∧ (normalForm hS ν d).2 ∈ invisibleDirs hS ν) ∧
    (∀ M ∈ Ω, ∀ k ∈ invisibleDirs hS ν, normalFormInv hS ν (M, k) ∈ dataSet hS ν) ∧
    (∀ d, normalFormInv hS ν (normalForm hS ν d) = d) ∧
    (∀ M ∈ Ω, ∀ k ∈ invisibleDirs hS ν, normalForm hS ν (normalFormInv hS ν (M, k)) = (M, k)) ∧
    (∀ M ∈ Ω, ∀ k ∈ invisibleDirs hS ν,
      dataRecon hS ν (normalFormInv hS ν (M, k)) = reconstructionL1 hS ν M) :=
  ⟨contDiffOn_normalForm hS ν, contDiffOn_normalFormInv hS ν, fun _ hd ↦ normalForm_mem hS ν hd,
    fun _ hM _ hk ↦ normalFormInv_mem hS ν hM hk, normalFormInv_normalForm hS ν,
    fun _ hM _ hk ↦ normalForm_normalFormInv hS ν hM hk,
    fun _ hM _ hk ↦ dataRecon_normalFormInv hS ν hM hk⟩

end Laplace.Multi
