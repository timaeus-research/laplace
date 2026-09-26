/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FibreOrthogonality

/-!
# The global visible–invisible normal form of the response retraction

Let `U = {d ∈ L¹(ν) : ∫ d dν = 1, m(d) ∈ Ω}` be the data space of unit mass and interior response,
`Ω` the interior of the moment body, and `K = {k : ∫ k = 0, ∫ S k = 0}` the invisible directions.
The maps
`Φ(d) = (m(d), d − p(m(d)))` and `Ψ(M, k) = p(M) + k`, `p(M) = [q_M]`,
are mutually inverse bijections `U ≃ Ω × K` (`normalForm_mem`, `normalFormInv_mem`,
`normalFormInv_normalForm`, `normalForm_normalFormInv`), both differentiable within their domains
(`hasFDerivWithinAt_normalForm`, `hasFDerivWithinAt_normalFormInv`), and in these coordinates
the reconstruction is the projection onto the first factor: `R(Ψ(M, k)) = p(M)`
(`dataRecon_normalFormInv`, `normalForm_dataRecon`).

So the response family is a global section of the data space, every datum has response
coordinates plus an exactly invisible residual, and the response map forgets the residual.
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

/-- The interior response domain `Ω`. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

/-- **The invisible directions** `K = {k : ∫ k dν = 0, ∫ S k dν = 0}`. -/
def invisibleDirs : Set (X →₁[ν] ℝ) := {k | ∫ x, k x ∂ν = 0 ∧ momentL1 hS ν k = 0}

/-- **The data space** `U = {d : ∫ d dν = 1, m(d) ∈ Ω}`. -/
def dataSet : Set (X →₁[ν] ℝ) := {d | ∫ x, d x ∂ν = 1 ∧ momentL1 hS ν d ∈ Ω}

/-- **The normal-form coordinates** `Φ(d) = (m(d), d − p(m(d)))`. -/
noncomputable def normalForm (d : X →₁[ν] ℝ) : (J → ℝ) × (X →₁[ν] ℝ) :=
  (momentL1 hS ν d, d - dataRecon hS ν d)

/-- **The inverse normal form** `Ψ(M, k) = p(M) + k`. -/
noncomputable def normalFormInv (Mk : (J → ℝ) × (X →₁[ν] ℝ)) : X →₁[ν] ℝ :=
  reconstructionL1 hS ν Mk.1 + Mk.2

/-- The reconstruction has unit mass. -/
theorem integral_reconstructionL1 (M : J → ℝ) : ∫ x, (reconstructionL1 hS ν M) x ∂ν = 1 := by
  rw [← integral_famDens hS ν (θr M)]
  refine integral_congr_ae ?_
  filter_upwards [Integrable.coeFn_toL1 (integrable_famDens hS ν (θr M))] with x hx
  exact hx

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The mass functional is additive on `L¹`. -/
theorem integral_L1_add (d e : X →₁[ν] ℝ) :
    ∫ x, (d + e) x ∂ν = (∫ x, d x ∂ν) + ∫ x, e x ∂ν := by
  rw [← integral_add (L1.integrable_coeFn d) (L1.integrable_coeFn e)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add d e] with x hx
  rw [hx, Pi.add_apply]

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The mass functional respects subtraction on `L¹`. -/
theorem integral_L1_sub (d e : X →₁[ν] ℝ) :
    ∫ x, (d - e) x ∂ν = (∫ x, d x ∂ν) - ∫ x, e x ∂ν := by
  rw [← integral_sub (L1.integrable_coeFn d) (L1.integrable_coeFn e)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub d e] with x hx
  rw [hx, Pi.sub_apply]

/-- `Φ` maps the data space into `Ω × K`. -/
theorem normalForm_mem {d : X →₁[ν] ℝ} (hd : d ∈ dataSet hS ν) :
    (normalForm hS ν d).1 ∈ Ω ∧ (normalForm hS ν d).2 ∈ invisibleDirs hS ν := by
  refine ⟨hd.2, ?_, ?_⟩
  · simp only [normalForm, dataRecon]
    rw [integral_L1_sub ν, hd.1, integral_reconstructionL1, sub_self]
  · simp only [normalForm, dataRecon]
    rw [map_sub, momentL1_reconstructionL1 hS ν hd.2, sub_self]

/-- `Ψ` maps `Ω × K` into the data space. -/
theorem normalFormInv_mem {M : J → ℝ} (hM : M ∈ Ω) {k : X →₁[ν] ℝ}
    (hk : k ∈ invisibleDirs hS ν) : normalFormInv hS ν (M, k) ∈ dataSet hS ν := by
  refine ⟨?_, ?_⟩
  · simp only [normalFormInv]
    rw [integral_L1_add ν, integral_reconstructionL1, hk.1, add_zero]
  · simp only [normalFormInv]
    rw [map_add, momentL1_reconstructionL1 hS ν hM, hk.2, add_zero]
    exact hM

/-- `Ψ ∘ Φ = id` on the data space (in fact everywhere). -/
theorem normalFormInv_normalForm (d : X →₁[ν] ℝ) : normalFormInv hS ν (normalForm hS ν d) = d := by
  simp only [normalFormInv, normalForm, dataRecon]
  abel

/-- `Φ ∘ Ψ = id` on `Ω × K`. -/
theorem normalForm_normalFormInv {M : J → ℝ} (hM : M ∈ Ω) {k : X →₁[ν] ℝ}
    (hk : k ∈ invisibleDirs hS ν) : normalForm hS ν (normalFormInv hS ν (M, k)) = (M, k) := by
  have hm : momentL1 hS ν (normalFormInv hS ν (M, k)) = M := by
    simp only [normalFormInv]
    rw [map_add, momentL1_reconstructionL1 hS ν hM, hk.2, add_zero]
  simp only [normalForm, dataRecon, hm]
  simp only [normalFormInv]
  abel_nf

/-- **In normal-form coordinates the reconstruction is the projection onto the response**:
`R(Ψ(M, k)) = p(M)`. -/
theorem dataRecon_normalFormInv {M : J → ℝ} (hM : M ∈ Ω) {k : X →₁[ν] ℝ}
    (hk : k ∈ invisibleDirs hS ν) :
    dataRecon hS ν (normalFormInv hS ν (M, k)) = reconstructionL1 hS ν M := by
  unfold dataRecon
  congr 1
  simp only [normalFormInv]
  rw [map_add, momentL1_reconstructionL1 hS ν hM, hk.2, add_zero]

/-- `Φ(R(d)) = (m(d), 0)`: the reconstruction has zero invisible residual. -/
theorem normalForm_dataRecon {d : X →₁[ν] ℝ} (hd : d ∈ dataSet hS ν) :
    normalForm hS ν (dataRecon hS ν d) = (momentL1 hS ν d, 0) := by
  simp only [normalForm, dataRecon_dataRecon hS ν hd.2, momentL1_dataRecon hS ν hd.2, sub_self]

/-- **`Φ` is differentiable within the data space**, with derivative
`h ↦ (m(h), h − DR_d[h])`. -/
theorem hasFDerivWithinAt_normalForm {d₀ : X →₁[ν] ℝ} (hd : d₀ ∈ dataSet hS ν) :
    HasFDerivWithinAt (normalForm hS ν)
      ((momentL1 hS ν).prod (ContinuousLinearMap.id ℝ _ -
        (reconstructionDeriv hS ν (momentL1 hS ν d₀)).comp (visibleL1 hS ν)))
      (dataSet hS ν) d₀ := by
  have h1 : HasFDerivWithinAt (dataRecon hS ν)
      ((reconstructionDeriv hS ν (momentL1 hS ν d₀)).comp (visibleL1 hS ν)) (dataSet hS ν) d₀ :=
    (hasFDerivWithinAt_dataRecon hS ν hd.2).mono fun d hd' ↦ by
      change ∫ x, d x ∂ν = ∫ x, d₀ x ∂ν
      rw [hd'.1, hd.1]
  exact (momentL1 hS ν).hasFDerivWithinAt.prodMk
    ((ContinuousLinearMap.id ℝ _).hasFDerivWithinAt.sub h1)

/-- The reconstruction is differentiable within `Ω` (as a map on all of `J → ℝ`), with
derivative `Dp_M ∘ π`. -/
theorem hasFDerivWithinAt_reconstructionL1_dirProjL {M : J → ℝ} (hM : M ∈ Ω) :
    HasFDerivWithinAt (reconstructionL1 hS ν) ((reconstructionDeriv hS ν M).comp (dirProjL S ν))
      Ω M := by
  have hg : HasFDerivAt (fun M' ↦ dirProjL S ν (M' - M)) (dirProjL S ν) M := by
    have := (dirProjL S ν).hasFDerivAt.comp M ((hasFDerivAt_id M).sub_const M)
    simpa [Function.comp_def] using this
  have hf : HasFDerivAt (fun z : 𝕍 ↦ reconstructionL1 hS ν (M + z))
      (reconstructionDeriv hS ν M) (dirProjL S ν (M - M)) := by
    rw [sub_self, map_zero]
    exact hasFDerivAt_reconstructionL1 hS ν hM
  refine (hf.comp M hg).hasFDerivWithinAt.congr (fun M' hM' ↦ ?_) ?_
  · simp only [Function.comp_def]
    rw [dirProjL_of_mem ν (sub_mem_dirSpan_of_mem_momentBody' hS ν
      (intrinsicInterior_subset hM) (intrinsicInterior_subset hM')), add_sub_cancel]
  · simp only [Function.comp_def, sub_self, map_zero, Submodule.coe_zero, add_zero]

/-- **`Ψ` is differentiable within `Ω × K`**, with derivative `(u, k) ↦ Dp_M(π u) + k`. -/
theorem hasFDerivWithinAt_normalFormInv {M : J → ℝ} (hM : M ∈ Ω) (k : X →₁[ν] ℝ) :
    HasFDerivWithinAt (normalFormInv hS ν)
      (((reconstructionDeriv hS ν M).comp (dirProjL S ν)).comp
          (ContinuousLinearMap.fst ℝ (J → ℝ) (X →₁[ν] ℝ)) +
        ContinuousLinearMap.snd ℝ (J → ℝ) (X →₁[ν] ℝ))
      (Ω ×ˢ invisibleDirs hS ν) (M, k) := by
  have h1 : HasFDerivWithinAt (fun Mk : (J → ℝ) × (X →₁[ν] ℝ) ↦ reconstructionL1 hS ν Mk.1)
      (((reconstructionDeriv hS ν M).comp (dirProjL S ν)).comp
        (ContinuousLinearMap.fst ℝ (J → ℝ) (X →₁[ν] ℝ))) (Ω ×ˢ invisibleDirs hS ν) (M, k) :=
    HasFDerivWithinAt.comp (M, k) (g := reconstructionL1 hS ν)
      (f := (Prod.fst : (J → ℝ) × (X →₁[ν] ℝ) → J → ℝ)) (t := Ω) (s := Ω ×ˢ invisibleDirs hS ν)
      (hasFDerivWithinAt_reconstructionL1_dirProjL hS ν hM) hasFDerivWithinAt_fst
      fun Mk hMk ↦ hMk.1
  exact h1.add (ContinuousLinearMap.snd ℝ (J → ℝ) (X →₁[ν] ℝ)).hasFDerivWithinAt

end Laplace.Multi
