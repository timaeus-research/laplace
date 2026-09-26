/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AnalyticTilt

/-!
# The analytic response atlas

At grade `ω` (real-analytic) the whole response calculus is analytic:

* `contDiff_omega_famMean`, `contDiff_omega_meanMap`, `contDiff_omega_meanMapDeriv`,
  `contDiff_omega_chartV`, `contDiff_omega_chartDeriv`, `contDiff_omega_chartDerivEquiv_symm`: the
  mean map, its Jacobian, the intrinsic chart, the covariance operator and its inverse are analytic
  (composition with the analytic tilt map of `AnalyticTilt`);
* `contDiffOn_omega_chartVInv`: **the inverse chart is analytic** on its open domain, by the
  grade-`ω` inverse function theorem `ContDiffAt.to_localInverse` at each point and the
  identification of the local inverse with `chartVInv` through the left inverse
  `chartVInv ∘ chartV = id`;
* `contDiffOn_omega_responseTheta_add` / `analyticOnNhd_responseTheta_add`: `z ↦ θ(m₀ + z)` is
  analytic on the interior displacements; `contDiff_omega_densL1`: `θ ↦ [q_θ]` is analytic into
  `L¹`;
* `contDiffOn_omega_reconstructionL1_add` / **`analyticOnNhd_reconstructionL1_add`**: the
  reconstruction `z ↦ [q_{M+z}] ∈ L¹(ν)` is real-analytic on the open set of interior displacements;
* `contDiffOn_omega_atlasTheta`, **`analyticAt_reconstructionL1_atlas`**,
  **`analyticAt_obsResponse_atlas`**: the atlas curve `s ↦ [q_{M_s}]` and every bounded-observable
  response `s ↦ E_{Q_{M_s}}F` are real-analytic on the interior atlas domain.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

/-- The chart derivative as a linear equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The intrinsic chart. -/
local notation "chV" => chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The inverse chart. -/
local notation "chVInv" => chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

section Family

omit [Nonempty X] in
/-- **The mean map is analytic.** -/
theorem contDiff_omega_famMean : ContDiff ℝ ω (famMean S ν) := by
  refine contDiff_pi.2 fun j ↦ ?_
  have e : (fun θ ↦ famMean S ν θ j) = fun θ ↦ famNum S ν (S j) θ / famZ S ν θ := by
    funext θ
    exact famMean_eq_famNum_div ν θ j
  rw [e]
  exact (contDiff_omega_famNum hS ν (hS j)).div (contDiff_omega_famZ hS ν) fun θ ↦
    (famZ_pos hS ν θ).ne'

omit [Nonempty X] in
theorem contDiff_omega_meanMap :
    ContDiff ℝ ω (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1) := by
  have e : meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 = famMean S ν := by
    funext θ
    exact (famMean_eq_meanMap hS ν θ).symm
  rw [e]
  exact contDiff_omega_famMean hS ν

/-- **The Jacobian of the mean map is analytic.** -/
theorem contDiff_omega_meanMapDeriv :
    ContDiff ℝ ω (meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1) := by
  have e : meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 =
      fderiv ℝ (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1) := by
    funext θ
    exact meanMapDeriv_eq_fderiv hS ν θ
  rw [e]
  exact (contDiff_omega_meanMap hS ν).fderiv_right le_top

/-- **The intrinsic chart is analytic.** -/
theorem contDiff_omega_chartV : ContDiff ℝ ω chV := by
  have e : chV =
      fun θ : 𝕍 ↦ dirProjL S ν (meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ - m₀) := by
    funext θ
    refine Subtype.ext ?_
    rw [chartV_apply, dirProjL_of_mem ν (meanMap_sub_mem_dirSpan measurable_const
      (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS _ _)]
  rw [e]
  exact (dirProjL S ν).contDiff.comp
    (((contDiff_omega_meanMap hS ν).comp (𝕍).subtypeL.contDiff).sub contDiff_const)

/-- **The covariance operator is analytic** as a map `𝕍 → (𝕍 →L 𝕍)`. -/
theorem contDiff_omega_chartDeriv :
    ContDiff ℝ ω (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS) := by
  refine contDiff_clm_apply_iff.2 fun v ↦ ?_
  have e : (fun θ : 𝕍 ↦ chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS θ v) = fun θ : 𝕍 ↦ dirProjL S ν
        (meanMapDeriv ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ v) := by
    funext θ
    exact chartDeriv_eq_dirProjL hS ν θ v
  rw [e]
  exact (dirProjL S ν).contDiff.comp
    (((contDiff_omega_meanMapDeriv hS ν).comp (𝕍).subtypeL.contDiff).clm_apply contDiff_const)

/-- **The inverse covariance operator is analytic.** -/
theorem contDiff_omega_chartDerivEquiv_symm :
    ContDiff ℝ ω (fun θ : 𝕍 ↦ ((CDE θ).symm : 𝕍 →L[ℝ] 𝕍)) := by
  refine contDiff_iff_contDiffAt.2 fun θ₀ ↦ ?_
  have e : (fun θ : 𝕍 ↦ ((CDE θ).symm : 𝕍 →L[ℝ] 𝕍)) = fun θ : 𝕍 ↦
      ContinuousLinearMap.inverse (chartDeriv measurable_const (integrable_const 1)
        (fun _ ↦ one_pos) (one_integral_pos ν) hS θ) := by
    funext θ
    rw [← coe_chartDerivEquiv, ContinuousLinearMap.inverse_equiv]
  rw [e]
  have h1 := contDiffAt_map_inverse (n := ω) (CDE θ₀)
  rw [coe_chartDerivEquiv] at h1
  exact h1.comp θ₀ (contDiff_omega_chartDeriv hS ν).contDiffAt

end Family

section Chart

/-- **The inverse chart is analytic on its domain** (grade-`ω` inverse function theorem, identified
with `chartVInv` through the left inverse `chartVInv ∘ chartV = id`). -/
theorem contDiffOn_omega_chartVInv : ContDiffOn ℝ ω chVInv (Set.range chV) := by
  rintro _ ⟨θ₀, rfl⟩
  have hf : ContDiffAt ℝ ω chV θ₀ := (contDiff_omega_chartV hS ν).contDiffAt
  have hf' : HasFDerivAt chV (CDE θ₀ : 𝕍 →L[ℝ] 𝕍) θ₀ := by
    rw [coe_chartDerivEquiv]
    exact (hasStrictFDerivAt_chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS θ₀).hasFDerivAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have h := hf.to_localInverse hf' hn
  have hstrict := hf.hasStrictFDerivAt' hf' hn
  have hev : chVInv =ᶠ[𝓝 (chV θ₀)] hf.localInverse hf' hn := by
    refine hstrict.eventually_right_inverse.mono fun y hy ↦ ?_
    have hy' : chV (hf.localInverse hf' hn y) = y := hy
    calc chVInv y = chVInv (chV (hf.localInverse hf' hn y)) := by rw [hy']
      _ = hf.localInverse hf' hn y :=
          chartVInv_chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
            (one_integral_pos ν) hS _
  exact (h.congr_of_eventuallyEq hev).contDiffWithinAt

/-- **The natural coordinate is analytic in the response** on the interior displacements. -/
theorem contDiffOn_omega_responseTheta_add :
    ContDiffOn ℝ ω (fun z : 𝕍 ↦ θr (m₀ + z)) {z : 𝕍 | m₀ + (z : J → ℝ) ∈ Ω} := by
  have e : {z : 𝕍 | m₀ + (z : J → ℝ) ∈ Ω} = Set.range chV := by
    ext v
    exact (mem_range_chartV_iff hS ν v).symm
  rw [e]
  exact (contDiffOn_omega_chartVInv hS ν).congr fun z _ ↦ responseTheta_add_eq_chartVInv hS ν z

/-- The interior displacement domain is open in `𝕍`. -/
theorem isOpen_interior_displacements : IsOpen {z : 𝕍 | m₀ + (z : J → ℝ) ∈ Ω} := by
  have e : {z : 𝕍 | m₀ + (z : J → ℝ) ∈ Ω} = Set.range chV := by
    ext v
    exact (mem_range_chartV_iff hS ν v).symm
  rw [e]
  exact isOpen_range_chartV hS ν

theorem analyticOnNhd_responseTheta_add :
    AnalyticOnNhd ℝ (fun z : 𝕍 ↦ θr (m₀ + z)) {z : 𝕍 | m₀ + (z : J → ℝ) ∈ Ω} := fun _ hz ↦
  ((contDiffOn_omega_responseTheta_add hS ν).contDiffAt
    ((isOpen_interior_displacements hS ν).mem_nhds hz)).analyticAt

omit [Nonempty X] in
/-- **The density `θ ↦ [q_θ]` is analytic into `L¹`.** -/
theorem contDiff_omega_densL1 : ContDiff ℝ ω (densL1 hS ν) := by
  have e : densL1 hS ν = fun θ ↦ (famZ S ν θ)⁻¹ • weightL1 hS ν (Bdd.const 1) θ := by
    funext θ
    exact densL1_eq hS ν θ
  rw [e]
  exact ((contDiff_omega_famZ hS ν).inv fun θ ↦ (famZ_pos hS ν θ).ne').smul
    (contDiff_omega_weightL1 hS ν (Bdd.const 1))

variable {M : J → ℝ} (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- The reconstruction of the displacements of `M`. -/
local notation "P" => fun z : 𝕍 ↦ reconstructionL1 hS ν (M + z)

/-- **The reconstruction is analytic on the interior displacements of `M`.** -/
theorem contDiffOn_omega_reconstructionL1_add : ContDiffOn ℝ ω P (addDomain S ν M) := by
  have e : P = densL1 hS ν ∘ ((𝕍).subtypeL ∘ ((fun w : 𝕍 ↦ θr (m₀ + w)) ∘
      fun z : 𝕍 ↦ dirProjL S ν (M - m₀) + z)) := by
    funext z
    simp only [Function.comp_def, reconstructionL1_eq_densL1]
    congr 3
    rw [Submodule.coe_add, dirProjL_of_mem ν (sub_mem_dirSpan_of_mem_momentBody' hS ν
      (intrinsicInterior_subset (featureless_mem_intrinsicInterior hS ν))
      (intrinsicInterior_subset hrel))]
    abel
  rw [e]
  refine (contDiff_omega_densL1 hS ν).comp_contDiffOn ((𝕍).subtypeL.contDiff.comp_contDiffOn ?_)
  refine (contDiffOn_omega_responseTheta_add hS ν).comp
    (contDiff_const.add contDiff_id).contDiffOn fun z hz ↦ ?_
  change m₀ + ((dirProjL S ν (M - m₀) + z : 𝕍) : J → ℝ) ∈ Ω
  rw [Submodule.coe_add, dirProjL_of_mem ν (sub_mem_dirSpan_of_mem_momentBody' hS ν
    (intrinsicInterior_subset (featureless_mem_intrinsicInterior hS ν))
    (intrinsicInterior_subset hrel)), ← add_assoc, add_sub_cancel]
  exact hz

/-- **The analytic response atlas**: `z ↦ [q_{M+z}] ∈ L¹(ν)` is real-analytic on the open set of
interior displacements of every interior response `M`. -/
theorem analyticOnNhd_reconstructionL1_add : AnalyticOnNhd ℝ P (addDomain S ν M) := fun _ hz ↦
  ((contDiffOn_omega_reconstructionL1_add hS ν hrel).contDiffAt
    ((isOpen_addDomain hS ν hrel).mem_nhds hz)).analyticAt

/-- The reconstruction is analytic at every interior response. -/
theorem analyticAt_reconstructionL1_add : AnalyticAt ℝ P 0 :=
  analyticOnNhd_reconstructionL1_add hS ν hrel 0 (zero_mem_addDomain ν hrel)

end Chart

section Atlas

variable {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
include hfin

/-- The reconstruction curve along the atlas. -/
local notation "p" => fun s ↦ reconstructionL1 hS ν (atlasPath S ν M s)

/-- **The atlas coordinate is analytic** on the interior atlas domain. -/
theorem contDiffOn_omega_atlasTheta :
    ContDiffOn ℝ ω (atlasTheta hS ν M) (atlasDomain S ν M) := by
  have e : atlasTheta hS ν M = (fun z : 𝕍 ↦ θr (m₀ + z)) ∘ fun s : ℝ ↦ s • atlasInc hS ν hfin := by
    funext s
    simp only [atlasTheta, Function.comp_def]
    rw [atlasPath_eq_add_smul_atlasInc hS ν hfin]
  rw [e]
  refine (contDiffOn_omega_responseTheta_add hS ν).comp (contDiff_id.smul contDiff_const).contDiffOn
    fun s hs ↦ ?_
  change m₀ + ((s • atlasInc hS ν hfin : 𝕍) : J → ℝ) ∈ Ω
  rw [← atlasPath_eq_add_smul_atlasInc hS ν hfin]
  exact hs

/-- **The reconstruction curve is analytic** on the interior atlas domain. -/
theorem contDiffOn_omega_reconstructionL1_atlas : ContDiffOn ℝ ω p (atlasDomain S ν M) := by
  have e : p = densL1 hS ν ∘ ((𝕍).subtypeL ∘ atlasTheta hS ν M) := by
    funext s
    rfl
  rw [e]
  exact (contDiff_omega_densL1 hS ν).comp_contDiffOn
    ((𝕍).subtypeL.contDiff.comp_contDiffOn (contDiffOn_omega_atlasTheta hS ν hfin))

/-- **The atlas curve `s ↦ [q_{M_s}]` is real-analytic** at every interior atlas point. -/
theorem analyticAt_reconstructionL1_atlas {s : ℝ} (hs : s ∈ atlasDomain S ν M) :
    AnalyticAt ℝ p s :=
  ((contDiffOn_omega_reconstructionL1_atlas hS ν hfin).contDiffAt
    ((isOpen_atlas_interior hS ν hfin).mem_nhds hs)).analyticAt

/-- **Every bounded-observable response is real-analytic along the atlas.** -/
theorem analyticAt_obsResponse_atlas {s : ℝ} (hs : s ∈ atlasDomain S ν M) {F : X → ℝ}
    (hF : Bdd F) : AnalyticAt ℝ (fun s ↦ obsResponse hS ν F (atlasPath S ν M s)) s := by
  have e : (fun s ↦ obsResponse hS ν F (atlasPath S ν M s)) =
      fun s ↦ obsL1 ν hF (reconstructionL1 hS ν (atlasPath S ν M s)) :=
    funext fun s ↦ (obsL1_reconstructionL1 hS ν hF _).symm
  rw [e]
  exact ((obsL1 ν hF).analyticAt _).comp (analyticAt_reconstructionL1_atlas hS ν hfin hs)

end Atlas

end Laplace.Multi
