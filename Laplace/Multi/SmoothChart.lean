/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.SmoothFamily
import Laplace.Multi.SecondOrderTransport

/-!
# The response chart is `C^∞`: the smooth bootstrap

The inverse chart `chartVInv : 𝕍 → 𝕍` (natural coordinate as a function of the response
displacement) is `C^1` with derivative `(Dm(θ)|_𝕍)⁻¹` at `θ = chartVInv v`. Since the inverse
chart derivative is `C^∞` in `θ` (`contDiff_chartDerivEquiv_symm`), a bootstrap gives
`C^n ⇒ C^{n+1}` on the open chart domain `U = range chartV = {v : m₀ + v ∈ Ω}`, hence
`chartVInv ∈ C^∞(U)` (`contDiffOn_infty_chartVInv`). Consequently the natural coordinate
`z ↦ θ(m₀ + z)` is `C^∞` on `{z : m₀ + z ∈ Ω}` (`contDiffOn_responseTheta_add`), the atlas
coordinate `s ↦ θ(M_s)` is `C^∞` wherever the atlas is interior (`contDiffOn_atlasTheta`), and
the response of every bounded observable is `C^∞` along the atlas
(`contDiffOn_integral_atlasTheta`): the response calculus exists to all orders.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The intrinsic chart. -/
local notation "chV" => chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The inverse intrinsic chart. -/
local notation "chVInv" => chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

/-- The chart domain is the set of interior displacements: `v ∈ range chartV ↔ m₀ + v ∈ Ω`. -/
theorem mem_range_chartV_iff (v : 𝕍) : v ∈ Set.range chV ↔ m₀ + (v : J → ℝ) ∈ Ω := by
  constructor
  · rintro ⟨θ, rfl⟩
    rw [chartV_apply, add_sub_cancel, ← range_meanMap_eq_intrinsicInterior_momentBody
      measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS]
    exact ⟨θ, rfl⟩
  · intro h
    exact ⟨chVInv v, chartV_chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS h⟩

/-- **The chart domain is open** (inverse function theorem). -/
theorem isOpen_range_chartV : IsOpen (Set.range chV) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨θ₀, rfl⟩
  have h : HasStrictFDerivAt chV (CDE θ₀ : 𝕍 →L[ℝ] 𝕍) θ₀ := by
    rw [coe_chartDerivEquiv]
    exact hasStrictFDerivAt_chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS θ₀
  rw [← h.map_nhds_eq_of_equiv, ← Set.image_univ]
  exact Filter.image_mem_map univ_mem

/-- The derivative of the inverse chart on its domain: `D chartVInv(v) = (Dm(θ)|_𝕍)⁻¹` at
`θ = chartVInv v`. -/
theorem fderiv_chartVInv_of_mem {v : 𝕍} (hv : v ∈ Set.range chV) :
    fderiv ℝ chVInv v = ((CDE (chVInv v)).symm : 𝕍 →L[ℝ] 𝕍) := by
  obtain ⟨θ₀, rfl⟩ := hv
  rw [chartVInv_chartV]
  exact (hasStrictFDerivAt_chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS θ₀).hasFDerivAt.fderiv

/-- The inverse chart is differentiable on its domain. -/
theorem differentiableOn_chartVInv : DifferentiableOn ℝ chVInv (Set.range chV) := by
  rintro _ ⟨θ₀, rfl⟩
  exact (hasStrictFDerivAt_chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS θ₀).differentiableAt.differentiableWithinAt

/-- **The smooth bootstrap**: `chartVInv ∈ C^n(U)` for every `n`, since its derivative is the
`C^∞` inverse covariance evaluated along `chartVInv` itself. -/
theorem contDiffOn_chartVInv (n : ℕ) : ContDiffOn ℝ n chVInv (Set.range chV) := by
  induction n with
  | zero => exact contDiffOn_zero.2 (differentiableOn_chartVInv hS ν).continuousOn
  | succ n ih =>
    rw [Nat.cast_succ]
    refine (contDiffOn_succ_iff_fderiv_of_isOpen (isOpen_range_chartV hS ν)).2
      ⟨differentiableOn_chartVInv hS ν, fun h ↦ absurd h (WithTop.natCast_ne_top n), ?_⟩
    refine (((contDiff_chartDerivEquiv_symm hS ν).of_le (by exact_mod_cast natCast_le_infty n))
      |>.comp_contDiffOn ih).congr fun v hv ↦ ?_
    exact fderiv_chartVInv_of_mem hS ν hv

/-- **The inverse chart is `C^∞` on its domain.** -/
theorem contDiffOn_infty_chartVInv : ContDiffOn ℝ ∞ chVInv (Set.range chV) :=
  contDiffOn_infty.2 fun n ↦ contDiffOn_chartVInv hS ν n

/-- The natural coordinate of `m₀ + z` is the inverse chart at `z`. -/
theorem responseTheta_add_eq_chartVInv (z : 𝕍) : θr (m₀ + z) = chVInv z := by
  unfold responseTheta
  congr 1
  refine Subtype.ext ?_
  rw [toV_apply (by rw [add_sub_cancel_left]; exact z.2), add_sub_cancel_left]

/-- **The natural coordinate is `C^∞` in the response**: `z ↦ θ(m₀ + z)` is `C^∞` on the
interior displacements. -/
theorem contDiffOn_responseTheta_add :
    ContDiffOn ℝ ∞ (fun z : 𝕍 ↦ θr (m₀ + z)) {z : 𝕍 | m₀ + (z : J → ℝ) ∈ Ω} := by
  have e : {z : 𝕍 | m₀ + (z : J → ℝ) ∈ Ω} = Set.range chV := by
    ext v
    exact (mem_range_chartV_iff hS ν v).symm
  rw [e]
  exact (contDiffOn_infty_chartVInv hS ν).congr fun z _ ↦ responseTheta_add_eq_chartVInv hS ν z

omit [Nonempty J] in
/-- **The response of a bounded observable is `C^∞` in the natural parameter.** -/
theorem contDiff_integral_familyMeasure {F : X → ℝ} (hF : Bdd F) :
    ContDiff ℝ ∞ (fun θ : J → ℝ ↦ ∫ x, F x ∂(Pfam θ)) := by
  have e : (fun θ : J → ℝ ↦ ∫ x, F x ∂(Pfam θ)) = fun θ ↦ famNum S ν F θ / famZ S ν θ := by
    funext θ
    rw [integral_famDens_mul hS ν]
    simp only [famDens, famNum]
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    ring
  rw [e]
  exact (contDiff_infty_famNum hS ν hF).div (contDiff_famZ hS ν) fun θ ↦ (famZ_pos hS ν θ).ne'

section Atlas

variable {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
include hfin

/-- The atlas point as a displacement from the featureless response. -/
theorem atlasPath_eq_add_smul_atlasInc (s : ℝ) :
    atlasPath S ν M s = m₀ + ((s • atlasInc hS ν hfin : 𝕍) : J → ℝ) := by
  rw [Submodule.coe_smul, atlasInc_coe, ← atlasPath_sub, add_sub_cancel]

/-- **The atlas coordinate `s ↦ θ(M_s)` is `C^∞`** wherever the atlas is interior. -/
theorem contDiffOn_atlasTheta :
    ContDiffOn ℝ ∞ (atlasTheta hS ν M) {s : ℝ | atlasPath S ν M s ∈ Ω} := by
  have e : atlasTheta hS ν M = (fun z : 𝕍 ↦ θr (m₀ + z)) ∘ fun s : ℝ ↦ s • atlasInc hS ν hfin := by
    funext s
    simp only [atlasTheta, Function.comp_def]
    rw [atlasPath_eq_add_smul_atlasInc hS ν hfin]
  rw [e]
  refine (contDiffOn_responseTheta_add hS ν).comp (contDiff_id.smul contDiff_const).contDiffOn
    fun s hs ↦ ?_
  change m₀ + ((s • atlasInc hS ν hfin : 𝕍) : J → ℝ) ∈ Ω
  rw [← atlasPath_eq_add_smul_atlasInc hS ν hfin]
  exact hs

/-- The open unit interval lies in the interior atlas domain. -/
theorem Ioo_subset_atlas_interior : Ioo (0 : ℝ) 1 ⊆ {s : ℝ | atlasPath S ν M s ∈ Ω} :=
  fun _ hs ↦ atlas_mem_intrinsicInterior hS ν hfin hs.1.le hs.2

/-- **The response of every bounded observable is `C^∞` along the atlas.** -/
theorem contDiffOn_integral_atlasTheta {F : X → ℝ} (hF : Bdd F) :
    ContDiffOn ℝ ∞ (fun s ↦ ∫ x, F x ∂(Pfam (atlasTheta hS ν M s)))
      {s : ℝ | atlasPath S ν M s ∈ Ω} := by
  have e : (fun s ↦ ∫ x, F x ∂(Pfam (atlasTheta hS ν M s))) =
      (fun θ : J → ℝ ↦ ∫ x, F x ∂(Pfam θ)) ∘ ((𝕍).subtypeL ∘ atlasTheta hS ν M) := by
    funext s
    rfl
  rw [e]
  exact (contDiff_integral_familyMeasure hS ν hF).comp_contDiffOn
    ((𝕍).subtypeL.contDiff.comp_contDiffOn (contDiffOn_atlasTheta hS ν hfin))

end Atlas

end Laplace.Multi
