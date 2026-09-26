/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FeaturelessJet

/-!
# The Hessian of the reconstruction in all directions

At an interior response `M`, the reconstruction `P(z) = [q_{M+z}] ∈ L¹(ν)` (`z ∈ 𝕍`) is `C^∞` near
`0` (`contDiffAt_reconstructionL1_add`), and its second Fréchet derivative is the **invisible
Hessian**
`D²P_M[u, v] = [q_M N_M(ℓ_{M,u} ℓ_{M,v})]` (`fderiv_fderiv_reconstructionL1_add`).
The diagonal `D²P_M[w,w]` is identified along the line `s ↦ M + s w` by uniqueness of Peano
coefficients (the total-variation Peano expansion against Taylor's theorem), the off-diagonal by
polarisation using the symmetry of second derivatives; the pairing with every bounded observable
is the bias form, `∫ F · D²P_M[u,v] dν = b_{F,M}(u, v)` (`integral_mul_fderiv_fderiv_eq_biasForm`).
-/

open MeasureTheory Filter Topology Set Asymptotics
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

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

/-- The bias form is symmetric. -/
theorem biasForm_comm {M : J → ℝ} {F : X → ℝ} (hF : Bdd F) (u v : J → ℝ) :
    biasForm hS ν M hF u v = biasForm hS ν M hF v u := by
  rw [biasForm_apply, biasForm_apply]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  ring

variable {M : J → ℝ} (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

omit hrel in
variable (S M) in
/-- The interior displacements from `M`: `{z ∈ 𝕍 | M + z ∈ Ω}`. -/
def addDomain : Set 𝕍 := {z | M + (z : J → ℝ) ∈ Ω}

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hrel in
theorem mem_addDomain {z : 𝕍} : z ∈ addDomain S ν M ↔ M + (z : J → ℝ) ∈ Ω := Iff.rfl

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hrel in
/-- The line `s ↦ s • w` through the origin of `𝕍`, as a continuous linear map. -/
noncomputable def lineCLM (w : 𝕍) : ℝ →L[ℝ] 𝕍 := (ContinuousLinearMap.id ℝ ℝ).smulRight w

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hrel in
theorem lineCLM_apply (w : 𝕍) (s : ℝ) : lineCLM ν w s = s • w := rfl

/-- The reconstruction as a function of the displacement from `M`. -/
local notation "P" => fun z : 𝕍 ↦ reconstructionL1 hS ν (M + z)

set_option linter.unusedFintypeInType false in
/-- The interior displacements form an open set. -/
theorem isOpen_addDomain : IsOpen (addDomain S ν M) := by
  have e : addDomain S ν M = (fun z : 𝕍 ↦ dirProjL S ν (M - m₀) + z) ⁻¹' Set.range (chartV
      measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS) := by
    ext z
    rw [Set.mem_preimage, mem_range_chartV_iff, Submodule.coe_add,
      dirProjL_of_mem ν (sub_mem_dirSpan_of_mem_momentBody' hS ν
        (intrinsicInterior_subset (featureless_mem_intrinsicInterior hS ν))
        (intrinsicInterior_subset hrel)), mem_addDomain, ← add_assoc, add_sub_cancel]
  rw [e]
  exact (isOpen_range_chartV hS ν).preimage (continuous_const.add continuous_id)

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hrel in
/-- `0` is an interior displacement. -/
theorem zero_mem_addDomain (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    (0 : 𝕍) ∈ addDomain S ν M := by
  rw [mem_addDomain, Submodule.coe_zero, add_zero]
  exact hrel

/-- **The reconstruction is `C^∞` on the interior displacements.** -/
theorem contDiffOn_reconstructionL1_add : ContDiffOn ℝ ∞ P (addDomain S ν M) := by
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
  refine (contDiff_densL1 hS ν).comp_contDiffOn ((𝕍).subtypeL.contDiff.comp_contDiffOn ?_)
  refine (contDiffOn_responseTheta_add hS ν).comp (contDiff_const.add contDiff_id).contDiffOn
    fun z hz ↦ ?_
  change m₀ + ((dirProjL S ν (M - m₀) + z : 𝕍) : J → ℝ) ∈ Ω
  rw [Submodule.coe_add, dirProjL_of_mem ν (sub_mem_dirSpan_of_mem_momentBody' hS ν
    (intrinsicInterior_subset (featureless_mem_intrinsicInterior hS ν))
    (intrinsicInterior_subset hrel)), ← add_assoc, add_sub_cancel]
  exact hz

/-- **The reconstruction is `C^∞` at every interior response.** -/
theorem contDiffAt_reconstructionL1_add : ContDiffAt ℝ ∞ P 0 :=
  (contDiffOn_reconstructionL1_add hS ν hrel).contDiffAt
    ((isOpen_addDomain hS ν hrel).mem_nhds (zero_mem_addDomain ν hrel))

/-- The second derivative of the reconstruction is symmetric. -/
theorem isSymmSndFDerivAt_reconstructionL1_add : IsSymmSndFDerivAt ℝ P 0 :=
  (contDiffAt_reconstructionL1_add hS ν hrel).isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact_mod_cast natCast_le_infty 2)

/-- **The second derivative along a line is the diagonal Hessian**:
`d²/ds² P(s w)|₀ = D²P_0[w, w]`. -/
theorem iteratedDeriv_two_line_eq (w : 𝕍) :
    iteratedDeriv 2 (P ∘ lineCLM ν w) 0 = fderiv ℝ (fderiv ℝ P) 0 w w := by
  have hU := isOpen_addDomain hS ν hrel
  have h0 := zero_mem_addDomain ν hrel
  have hL0 : lineCLM ν w 0 = 0 := by rw [lineCLM_apply, zero_smul]
  have h0' : (0 : ℝ) ∈ lineCLM ν w ⁻¹' addDomain S ν M := by
    rw [Set.mem_preimage, hL0]
    exact h0
  have hpre : IsOpen (lineCLM ν w ⁻¹' addDomain S ν M) := hU.preimage (lineCLM ν w).continuous
  rw [← iteratedDerivWithin_of_isOpen hpre h0', iteratedDerivWithin_eq_iteratedFDerivWithin,
    ContinuousLinearMap.iteratedFDerivWithin_comp_right (lineCLM ν w)
      (contDiffOn_reconstructionL1_add hS ν hrel) hU.uniqueDiffOn hpre.uniqueDiffOn
      (by rw [hL0]; exact h0) (i := 2) (by exact_mod_cast natCast_le_infty 2),
    ContinuousMultilinearMap.compContinuousLinearMap_apply, hL0,
    iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
      ((contDiffAt_reconstructionL1_add hS ν hrel).of_le (by exact_mod_cast natCast_le_infty 2))
      h0, iteratedFDeriv_two_apply]
  simp [lineCLM_apply]

/-- The derivative of the reconstruction along a line at its base point. -/
theorem hasDerivAt_reconstructionL1_line (w : 𝕍) :
    HasDerivAt (P ∘ lineCLM ν w) (reconstructionDeriv hS ν M w) 0 := by
  have hL0 : lineCLM ν w 0 = 0 := by rw [lineCLM_apply, zero_smul]
  have hγ : HasDerivAt (fun s : ℝ ↦ lineCLM ν w s) w 0 := by
    have := (hasDerivAt_id (0 : ℝ)).smul_const w
    simpa [lineCLM_apply] using this
  have h := hasDerivAt_reconstructionL1_curve hS ν (M := M) (γ := fun s ↦ lineCLM ν w s)
    (γ' := fun _ ↦ w) (t := 0) hγ (by rw [hL0, Submodule.coe_zero, add_zero]; exact hrel)
  rw [hL0, Submodule.coe_zero, add_zero] at h
  exact h

section Line

variable {w : dirSpan ν (fun _ ↦ (1 : ℝ)) S}
  (hw : ∀ s ∈ Icc (0 : ℝ) 1, M + ((s • w : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ) ∈
    intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hw

/-- The line curve is `C^∞` on the unit interval. -/
theorem contDiffOn_line_Icc : ContDiffOn ℝ ∞ (P ∘ lineCLM ν w) (Icc (0 : ℝ) 1) :=
  (contDiffOn_reconstructionL1_add hS ν hrel).comp (lineCLM ν w).contDiff.contDiffOn
    fun s hs ↦ by rw [mem_addDomain, lineCLM_apply]; exact hw s hs

omit hw in
/-- The line curve is smooth at the base point. -/
theorem contDiffAt_line_zero (n : ℕ) : ContDiffAt ℝ n (P ∘ lineCLM ν w) 0 := by
  have hL0 : lineCLM ν w 0 = 0 := by rw [lineCLM_apply, zero_smul]
  have h : ContDiffAt ℝ ∞ P (lineCLM ν w 0) := by
    rw [hL0]
    exact contDiffAt_reconstructionL1_add hS ν hrel
  exact (h.comp 0 (lineCLM ν w).contDiff.contDiffAt).of_le (by exact_mod_cast natCast_le_infty n)

omit hrel hw in
/-- The pairing of the zeroth jet of the line curve. -/
theorem integral_mul_iteratedDeriv_zero_line {F : X → ℝ} (hF : Bdd F) :
    ∫ x, F x * (iteratedDeriv 0 (P ∘ lineCLM ν w) 0) x ∂ν = obsResponse hS ν F M := by
  rw [iteratedDeriv_zero, ← obsL1_apply ν hF, Function.comp_apply, lineCLM_apply, zero_smul,
    Submodule.coe_zero, add_zero, obsL1_reconstructionL1 hS ν hF]

omit hw in
/-- The pairing of the first jet of the line curve: `∫ F · d/ds P(s w)|₀ = lin_{F,M}(w)`. -/
theorem integral_mul_iteratedDeriv_one_line {F : X → ℝ} (hF : Bdd F) :
    ∫ x, F x * (iteratedDeriv 1 (P ∘ lineCLM ν w) 0) x ∂ν = linForm hS ν M hF w := by
  rw [iteratedDeriv_one, (hasDerivAt_reconstructionL1_line hS ν hrel w).deriv,
    reconstructionDeriv_apply, ← integral_mul_responseScore_eq_linForm hS ν hF w,
    integral_famDens_mul hS ν]
  refine integral_congr_ae ?_
  filter_upwards [Integrable.coeFn_toL1 (integrable_famDens_mul_responseScore hS ν (M := M) w)]
    with x hx
  rw [hx]
  ring

omit hw in
/-- The Peano expansion of the observable response along the line. -/
theorem isLittleO_obsResponse_line {F : X → ℝ} (hF : Bdd F) :
    (fun s : ℝ ↦ obsResponse hS ν F (M + ((s • w : 𝕍) : J → ℝ)) - obsResponse hS ν F M -
      s * linForm hS ν M hF w - (1 / 2) * (s ^ 2 * biasForm hS ν M hF w w))
      =o[𝓝[Ioo (0 : ℝ) 1] 0] fun s ↦ s ^ 2 := by
  obtain ⟨BF, hBF⟩ := hF.2
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have hz : Tendsto (fun s : ℝ ↦ s • w) (𝓝[Ioo (0 : ℝ) 1] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ ↦ s • w) (𝓝 0) (𝓝 ((0 : ℝ) • w)) := tendsto_id.smul_const _
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hd := (isLittleO_integral_famDens_response_peano hS ν hrel).comp_tendsto hz
  have hnorm : (fun s : ℝ ↦ ‖s • w‖ ^ 2) =O[𝓝[Ioo (0 : ℝ) 1] 0] fun s ↦ s ^ 2 := by
    refine IsBigO.of_bound (‖w‖ ^ 2) (Eventually.of_forall fun s ↦ ?_)
    have e : ‖s • w‖ ^ 2 = ‖w‖ ^ 2 * s ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [e, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
  refine IsBigO.trans_isLittleO (IsBigO.of_bound BF ?_) (hd.trans_isBigO hnorm)
  filter_upwards [self_mem_nhdsWithin] with s _
  have hb := (bdd_responseScore hS ν M (s • w)).mul (bdd_responseScore hS ν M (s • w))
  have hint1 := integrable_famDens hS ν (θr (M + (s • w : 𝕍)))
  have hint2 : Integrable (fun x ↦ famDens S ν (θr M) x *
      (1 + responseScore hS ν M (s • w) x + (1 / 2) * normalProj hS ν M hb x)) ν :=
    integrable_famDens_mul_of_bdd hS ν
      (((Bdd.const 1).add (bdd_responseScore hS ν M _)).add
        (Bdd.const_mul (1 / 2) (bdd_normalProj hS ν hb)))
  have hr : Integrable (fun x ↦ famDens S ν (θr (M + (s • w : 𝕍))) x -
      famDens S ν (θr M) x *
        (1 + responseScore hS ν M (s • w) x + (1 / 2) * normalProj hS ν M hb x)) ν :=
    hint1.sub hint2
  have e2 : obsResponse hS ν F (M + ((s • w : 𝕍) : J → ℝ)) - obsResponse hS ν F M -
      s * linForm hS ν M hF w - (1 / 2) * (s ^ 2 * biasForm hS ν M hF w w) =
      ∫ x, F x * (famDens S ν (θr (M + (s • w : 𝕍))) x -
        famDens S ν (θr M) x * (1 + responseScore hS ν M (s • w) x +
          (1 / 2) * normalProj hS ν M hb x)) ∂ν := by
    have l1 : s * linForm hS ν M hF w =
        ∫ x, F x * responseScore hS ν M (s • w) x ∂(Pfam (θr M)) := by
      rw [integral_mul_responseScore_eq_linForm hS ν hF, Submodule.coe_smul, map_smul, smul_eq_mul]
    have l2 : s ^ 2 * biasForm hS ν M hF w w =
        ∫ x, F x * normalProj hS ν M hb x ∂(Pfam (θr M)) := by
      rw [integral_mul_normalProj_sq_eq_biasForm hS ν hrel hF, Submodule.coe_smul,
        LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul, sq]
      ring
    rw [l1, l2]
    unfold obsResponse
    rw [integral_famDens_mul hS ν, integral_famDens_mul hS ν, integral_famDens_mul hS ν,
      integral_famDens_mul hS ν]
    have hA : Integrable (fun x ↦ famDens S ν (θr (M + (s • w : 𝕍))) x * F x) ν :=
      integrable_famDens_mul_of_bdd hS ν hF
    have hB : Integrable (fun x ↦ famDens S ν (θr M) x * F x) ν :=
      integrable_famDens_mul_of_bdd hS ν hF
    have hC : Integrable (fun x ↦ famDens S ν (θr M) x *
        (F x * responseScore hS ν M (s • w) x)) ν :=
      integrable_famDens_mul_of_bdd hS ν (hF.mul (bdd_responseScore hS ν M _))
    have hD : Integrable (fun x ↦ famDens S ν (θr M) x * (F x * normalProj hS ν M hb x)) ν :=
      integrable_famDens_mul_of_bdd hS ν (hF.mul (bdd_normalProj hS ν hb))
    have hAB : Integrable (fun x ↦ famDens S ν (θr (M + (s • w : 𝕍))) x * F x -
        famDens S ν (θr M) x * F x) ν := hA.sub hB
    have hABC : Integrable (fun x ↦ (famDens S ν (θr (M + (s • w : 𝕍))) x * F x -
        famDens S ν (θr M) x * F x) -
        famDens S ν (θr M) x * (F x * responseScore hS ν M (s • w) x)) ν := hAB.sub hC
    have hD' : Integrable (fun x ↦ (1 / 2) *
        (famDens S ν (θr M) x * (F x * normalProj hS ν M hb x))) ν := hD.const_mul _
    rw [← integral_sub hA hB, ← integral_sub hAB hC, ← integral_const_mul, ← integral_sub hABC hD']
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    ring
  rw [e2, Function.comp_apply, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun x ↦ abs_nonneg _)]
  have hFr : Integrable (fun x ↦ F x * (famDens S ν (θr (M + (s • w : 𝕍))) x -
      famDens S ν (θr M) x *
        (1 + responseScore hS ν M (s • w) x + (1 / 2) * normalProj hS ν M hb x))) ν :=
    hr.bdd_mul hF.1.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hBF x)
  calc _ ≤ ∫ x, |F x * (famDens S ν (θr (M + (s • w : 𝕍))) x -
      famDens S ν (θr M) x *
        (1 + responseScore hS ν M (s • w) x + (1 / 2) * normalProj hS ν M hb x))| ∂ν :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, BF * |famDens S ν (θr (M + (s • w : 𝕍))) x -
      famDens S ν (θr M) x *
        (1 + responseScore hS ν M (s • w) x + (1 / 2) * normalProj hS ν M hb x)| ∂ν := by
        refine integral_mono hFr.abs (hr.abs.const_mul BF) fun x ↦ ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hBF x) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

/-- The Taylor expansion of the observable response along the line. -/
theorem isLittleO_obsResponse_line_taylor_two {F : X → ℝ} (hF : Bdd F) :
    (fun s : ℝ ↦ obsResponse hS ν F (M + ((s • w : 𝕍) : J → ℝ)) -
      ∑ k ∈ Finset.range 3, ((k.factorial : ℝ)⁻¹ * s ^ k) *
        ∫ x, F x * (iteratedDeriv k (P ∘ lineCLM ν w) 0) x ∂ν)
      =o[𝓝[Ioo (0 : ℝ) 1] 0] fun s ↦ s ^ 2 := by
  have hf : ContDiffOn ℝ (2 : ℕ) (P ∘ lineCLM ν w) (Icc (0 : ℝ) 1) :=
    (contDiffOn_line_Icc hS ν hrel hw).of_le (natCast_le_infty 2)
  have h := taylor_isLittleO (convex_Icc (0 : ℝ) 1) (left_mem_Icc.2 zero_le_one) hf
  simp only [sub_zero] at h
  have h' := h.mono (nhdsWithin_mono _ Ioo_subset_Icc_self)
  have hL := ((obsL1 ν hF).isBigO_comp _ _).trans_isLittleO h'
  refine hL.congr_left fun s ↦ ?_
  have ht : taylorWithinEval (P ∘ lineCLM ν w) 2 (Icc (0 : ℝ) 1) 0 s =
      ∑ k ∈ Finset.range 3, ((k.factorial : ℝ)⁻¹ * s ^ k) •
        iteratedDeriv k (P ∘ lineCLM ν w) 0 := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [sub_zero, iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc_zero_one
      (contDiffAt_line_zero hS ν hrel k) (left_mem_Icc.2 zero_le_one)]
  simp only [map_sub, ht, map_sum, map_smul, smul_eq_mul, obsL1_apply, Function.comp_apply,
    lineCLM_apply, obsL1_reconstructionL1 hS ν hF]

/-- **The diagonal Hessian pairs to the bias form**: `∫ F · D²P_0[w,w] dν = b_{F,M}(w,w)` for
lines staying in the interior. -/
theorem integral_mul_fderiv_fderiv_diag_of_line {F : X → ℝ} (hF : Bdd F) :
    ∫ x, F x * (fderiv ℝ (fderiv ℝ P) 0 w w) x ∂ν = biasForm hS ν M hF w w := by
  rw [← iteratedDeriv_two_line_eq hS ν hrel w]
  have hA := isLittleO_obsResponse_line hS ν hrel (w := w) hF
  have hB := isLittleO_obsResponse_line_taylor_two hS ν hrel hw hF
  have hc0 := integral_mul_iteratedDeriv_zero_line hS ν (M := M) (w := w) hF
  have hc1 := integral_mul_iteratedDeriv_one_line hS ν hrel (w := w) hF
  have hdiff : (fun s : ℝ ↦ 0 * s + ((1 / 2) * (biasForm hS ν M hF w w -
      ∫ x, F x * (iteratedDeriv 2 (P ∘ lineCLM ν w) 0) x ∂ν)) * s ^ 2)
      =o[𝓝[Ioo (0 : ℝ) 1] 0] fun s ↦ s ^ 2 := by
    refine (hB.sub hA).congr_left fun s ↦ ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc0, hc1, Nat.factorial]
    push_cast
    ring
  obtain ⟨-, hb⟩ := eq_zero_of_isLittleO_sq hdiff
  linarith

end Line

/-- **The diagonal Hessian pairs to the bias form** in every direction, by rescaling into the
interior. -/
theorem integral_mul_fderiv_fderiv_diag (u : 𝕍) {F : X → ℝ} (hF : Bdd F) :
    ∫ x, F x * (fderiv ℝ (fderiv ℝ P) 0 u u) x ∂ν = biasForm hS ν M hF u u := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_addDomain hS ν hrel) 0
    (zero_mem_addDomain ν hrel)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = r / (2 * (‖u‖ + 1)) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  have hw : ∀ s ∈ Icc (0 : ℝ) 1, M + ((s • (c • u) : 𝕍) : J → ℝ) ∈ Ω := fun s hs ↦ by
    rw [← mem_addDomain]
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hs.1, abs_of_pos hc0, hc]
    have h1 : s * (r / (2 * (‖u‖ + 1)) * ‖u‖) ≤ r / (2 * (‖u‖ + 1)) * ‖u‖ := by
      refine mul_le_of_le_one_left (by positivity) hs.2
    refine h1.trans_lt ?_
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg u]
  have h := integral_mul_fderiv_fderiv_diag_of_line hS ν hrel hw hF
  have e1 : fderiv ℝ (fderiv ℝ P) 0 (c • u) (c • u) = (c * c) • fderiv ℝ (fderiv ℝ P) 0 u u := by
    rw [map_smul, map_smul, smul_apply, smul_smul]
  have e2 : biasForm hS ν M hF ((c • u : 𝕍) : J → ℝ) ((c • u : 𝕍) : J → ℝ) =
      (c * c) * biasForm hS ν M hF u u := by
    rw [Submodule.coe_smul, LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul, mul_assoc]
  rw [e1, e2, ← obsL1_apply ν hF, map_smul, smul_eq_mul, obsL1_apply] at h
  have hcc : c * c ≠ 0 := by positivity
  exact mul_left_cancel₀ hcc h

/-- **The Hessian pairs to the bias form**: `∫ F · D²P_0[u,v] dν = b_{F,M}(u,v)`, by polarisation
and the symmetry of second derivatives. -/
theorem integral_mul_fderiv_fderiv_eq_biasForm (u v : 𝕍) {F : X → ℝ} (hF : Bdd F) :
    ∫ x, F x * (fderiv ℝ (fderiv ℝ P) 0 u v) x ∂ν = biasForm hS ν M hF u v := by
  have hsymm := isSymmSndFDerivAt_reconstructionL1_add hS ν hrel
  have huu := integral_mul_fderiv_fderiv_diag hS ν hrel u hF
  have hvv := integral_mul_fderiv_fderiv_diag hS ν hrel v hF
  have huv := integral_mul_fderiv_fderiv_diag hS ν hrel (u + v) hF
  have e1 : fderiv ℝ (fderiv ℝ P) 0 (u + v) (u + v) =
      fderiv ℝ (fderiv ℝ P) 0 u u + (2 : ℝ) • fderiv ℝ (fderiv ℝ P) 0 u v +
        fderiv ℝ (fderiv ℝ P) 0 v v := by
    simp only [map_add, add_apply]
    rw [hsymm v u, two_smul]
    abel
  have e2 : biasForm hS ν M hF ((u + v : 𝕍) : J → ℝ) ((u + v : 𝕍) : J → ℝ) =
      biasForm hS ν M hF u u + 2 * biasForm hS ν M hF u v + biasForm hS ν M hF v v := by
    rw [Submodule.coe_add, LinearMap.map_add₂, map_add, map_add, biasForm_comm hS ν hF v u]
    ring
  rw [e1, e2, ← obsL1_apply ν hF, map_add, map_add, map_smul, smul_eq_mul, obsL1_apply,
    obsL1_apply, obsL1_apply] at huv
  linarith

/-- **The Hessian of the reconstruction is the invisible bilinear map**
`D²P_M[u, v] = [q_M N_M(ℓ_{M,u} ℓ_{M,v})]`. -/
theorem fderiv_fderiv_reconstructionL1_add (u v : 𝕍) :
    fderiv ℝ (fderiv ℝ P) 0 u v =
      (integrable_famDens_mul_of_bdd hS ν (M := M) (bdd_normalProj hS ν
        ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M v)))).toL1
        (fun x ↦ famDens S ν (θr M) x * normalProj hS ν M
          ((bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M v)) x) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  refine L1_ext_of_forall_integral_mul ν _ _ fun F hF ↦ ?_
  rw [integral_mul_fderiv_fderiv_eq_biasForm hS ν hrel u v hF]
  have hb := (bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M v)
  have e : ∫ x, F x * ((integrable_famDens_mul_of_bdd hS ν (M := M) (bdd_normalProj hS ν hb)).toL1
      (fun x ↦ famDens S ν (θr M) x * normalProj hS ν M hb x)) x ∂ν =
      ∫ x, F x * normalProj hS ν M hb x ∂(Pfam (θr M)) := by
    rw [integral_famDens_mul hS ν]
    refine integral_congr_ae ?_
    filter_upwards [Integrable.coeFn_toL1 (integrable_famDens_mul_of_bdd hS ν (M := M)
      (bdd_normalProj hS ν hb))] with x hx
    rw [hx]
    ring
  rw [e, integral_mul_normalProj_comm hS ν hrel hF hb, biasForm_apply, dirProj_coe, dirProj_coe]

/-- **The Hessian is invisible**: it has zero mass and zero feature moments. -/
theorem momentL1_fderiv_fderiv_eq_zero (u v : 𝕍) :
    momentL1 hS ν (fderiv ℝ (fderiv ℝ P) 0 u v) = 0 ∧
      ∫ x, (fderiv ℝ (fderiv ℝ P) 0 u v) x ∂ν = 0 := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  have hb := (bdd_responseScore hS ν M u).mul (bdd_responseScore hS ν M v)
  rw [fderiv_fderiv_reconstructionL1_add hS ν hrel u v]
  constructor
  · funext j
    rw [momentL1_apply]
    have e : ∫ x, S j x * ((integrable_famDens_mul_of_bdd hS ν (M := M)
        (bdd_normalProj hS ν hb)).toL1 (fun x ↦ famDens S ν (θr M) x * normalProj hS ν M hb x))
          x ∂ν = ∫ x, S j x * normalProj hS ν M hb x ∂(Pfam (θr M)) := by
      rw [integral_famDens_mul hS ν]
      refine integral_congr_ae ?_
      filter_upwards [Integrable.coeFn_toL1 (integrable_famDens_mul_of_bdd hS ν (M := M)
        (bdd_normalProj hS ν hb))] with x hx
      rw [hx]
      ring
    rw [e, integral_stat_mul_normalProj hS ν hrel hb j]
    rfl
  · have e : ∫ x, ((integrable_famDens_mul_of_bdd hS ν (M := M)
        (bdd_normalProj hS ν hb)).toL1 (fun x ↦ famDens S ν (θr M) x * normalProj hS ν M hb x))
          x ∂ν = ∫ x, normalProj hS ν M hb x ∂(Pfam (θr M)) := by
      rw [integral_famDens_mul hS ν]
      exact integral_congr_ae (Integrable.coeFn_toL1 _)
    rw [e, integral_normalProj hS ν hrel hb]

end Laplace.Multi
