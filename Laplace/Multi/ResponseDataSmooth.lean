/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseDataHessian
import Laplace.Multi.SmoothChart
import Laplace.Multi.AllOrders

/-!
# Smoothness of the response map on finite data slices

For bounded directions `k₁, …, kₙ` the finite data slice `z ↦ Φ(g + ∑ zᵢ kᵢ)` of the response map
is `C^∞` (`contDiff_responseOf_slice`). The slice means `z ↦ E_{ν.tilted(g + ∑ zᵢkᵢ)} S` are
quotients of weighted normalisers of the family `k` at the natural parameter `−z`, hence `C^∞` by
`SmoothFamily` (`contDiff_sliceMean`); they stay in the open moment body, and composing with the
`C^∞` inverse chart `z ↦ θ(m₀ + z)` of `SmoothChart` gives the result.

The first and second Fréchet derivatives of the slice are identified with the response velocity
and the response Hessian: `DΦ(z)[eᵢ] = DΦ_{g_z}[kᵢ]` (`fderiv_slice_single`) and
`D²Φ(z)[eⱼ, eᵢ] = H_{g_z}(kⱼ, kᵢ)` (`fderiv_fderiv_slice_single`). Since a `C²` map has a symmetric
second Fréchet derivative (`isSymmSndFDerivAt_slice`), this recovers the symmetry of the response
Hessian from general calculus (`responseHess_symm_of_slice`), independently of the cumulant proof.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Laplace.Multi

section Slice

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {ι : Type*} [Fintype ι] {g : X → ℝ} (hg : Bdd g) {k : ι → X → ℝ} (hk : ∀ i, Bdd (k i))
include hS hg hk

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The response (inverse chart). -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

omit [MeasurableSpace X] [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg hk in
variable (g k) in
/-- The finite data slice `g + ∑ zᵢ kᵢ`. -/
def sliceFun (z : ι → ℝ) : X → ℝ := fun x ↦ g x + ∑ i, z i * k i x

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem bdd_slice (z : ι → ℝ) : Bdd (sliceFun g k z) := hg.add (bdd_dirLoss hk z)

omit [MeasurableSpace X] [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg hk in
/-- The slice tilt factorises: `e^{g + ∑ zᵢkᵢ} = e^g · w_k(−z)`. -/
theorem exp_slice (z : ι → ℝ) (x : X) :
    Real.exp (sliceFun g k z x) = Real.exp (g x) * famWeight k (-z) x := by
  simp only [sliceFun, famWeight, dirLoss, ← Real.exp_add]
  congr 1
  simp [Finset.sum_neg_distrib]

variable (S g k) in
/-- The slice means `E_{ρ_z} S`. -/
noncomputable def sliceMean (z : ι → ℝ) : J → ℝ := fun j ↦ ∫ x, S j x ∂ν.tilted (sliceFun g k z)

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg hk in
/-- A slice expectation is a quotient of weighted normalisers of the family `k` at `−z`. -/
theorem integral_tilted_slice {φ : X → ℝ} (z : ι → ℝ) :
    ∫ x, φ x ∂ν.tilted (sliceFun g k z) =
      famNum k ν (fun x ↦ φ x * Real.exp (g x)) (-z) /
        famNum k ν (fun x ↦ Real.exp (g x)) (-z) := by
  rw [integral_tilted]
  have e1 : ∀ x, (Real.exp (sliceFun g k z x) / ∫ y, Real.exp (sliceFun g k z y) ∂ν) • φ x =
      (φ x * Real.exp (g x) * famWeight k (-z) x) /
        ∫ y, Real.exp (g y) * famWeight k (-z) y ∂ν := fun x ↦ by
    simp only [smul_eq_mul, exp_slice]
    ring
  simp_rw [e1]
  rw [integral_div]
  rfl

omit [Nonempty X] [Fintype J] [Nonempty J] hS in
/-- The slice normaliser is positive. -/
theorem famNum_exp_pos (θ : ι → ℝ) : 0 < famNum k ν (fun x ↦ Real.exp (g x)) θ := by
  have e : famNum k ν (fun x ↦ Real.exp (g x)) θ = ∫ x, Real.exp (g x - dirLoss k θ x) ∂ν := by
    simp only [famNum, famWeight, ← Real.exp_add, sub_eq_add_neg]
  rw [e]
  exact integral_exp_pos (integrable_exp_of_bdd ν (hg.sub (bdd_dirLoss hk θ)))

omit [Fintype J] [Nonempty J] hS in
/-- **Slice expectations of bounded observables are `C^∞`.** -/
theorem contDiff_integral_tilted_slice {φ : X → ℝ} (hφ : Bdd φ) :
    ContDiff ℝ ∞ (fun z : ι → ℝ ↦ ∫ x, φ x ∂ν.tilted (sliceFun g k z)) := by
  have e : (fun z : ι → ℝ ↦ ∫ x, φ x ∂ν.tilted (sliceFun g k z)) = fun z ↦
      famNum k ν (fun x ↦ φ x * Real.exp (g x)) (-z) /
        famNum k ν (fun x ↦ Real.exp (g x)) (-z) :=
    funext fun z ↦ integral_tilted_slice ν (g := g) (k := k) z
  rw [e]
  refine ContDiff.div ?_ ?_ fun z ↦ (famNum_exp_pos ν hg hk (-z)).ne'
  · exact (contDiff_infty_famNum hk ν (hφ.mul (bdd_exp_of_bdd hg))).comp contDiff_neg
  · exact (contDiff_infty_famNum hk ν (bdd_exp_of_bdd hg)).comp contDiff_neg

omit [Nonempty J] in
/-- **The slice means are `C^∞`.** -/
theorem contDiff_sliceMean : ContDiff ℝ ∞ (sliceMean S ν g k) :=
  contDiff_pi.2 fun j ↦ contDiff_integral_tilted_slice ν hg hk (hS j)

set_option linter.unusedFintypeInType false in
omit [Nonempty J] in
theorem sliceMean_mem (z : ι → ℝ) : sliceMean S ν g k z ∈ Ω :=
  mean_tilted_mem_intrinsicInterior hS ν (bdd_slice hg hk z)

set_option linter.unusedFintypeInType false in
theorem sliceMean_sub_mem (z : ι → ℝ) : sliceMean S ν g k z - m₀ ∈ 𝕍 :=
  sub_mem_dirSpan_of_mem_momentBody' hS ν (meanMap_mem_momentBody measurable_const
    (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS 0)
    (intrinsicInterior_subset (sliceMean_mem hS ν hg hk z))

variable (S g k) in
/-- The slice displacement in the direction space. -/
noncomputable def sliceZ (z : ι → ℝ) : 𝕍 := dirProjL S ν (sliceMean S ν g k z - m₀)

theorem coe_sliceZ (z : ι → ℝ) : (sliceZ S ν g k z : J → ℝ) = sliceMean S ν g k z - m₀ :=
  dirProjL_of_mem ν (sliceMean_sub_mem hS ν hg hk z)

omit [Nonempty J] in
theorem contDiff_sliceZ : ContDiff ℝ ∞ (sliceZ S ν g k) :=
  (dirProjL S ν).contDiff.comp ((contDiff_sliceMean hS ν hg hk).sub contDiff_const)

theorem responseOf_slice_eq (z : ι → ℝ) :
    responseOf hS ν (sliceFun g k z) = θr (m₀ + (sliceZ S ν g k z : J → ℝ)) := by
  change θr (sliceMean S ν g k z) = _
  rw [coe_sliceZ hS ν hg hk z, add_sub_cancel]

/-- **Finite data slices of the response map are `C^∞`.** -/
theorem contDiff_responseOf_slice :
    ContDiff ℝ ∞ (fun z : ι → ℝ ↦ responseOf hS ν (sliceFun g k z)) := by
  have e : (fun z : ι → ℝ ↦ responseOf hS ν (sliceFun g k z)) =
      (fun w : 𝕍 ↦ θr (m₀ + (w : J → ℝ))) ∘ sliceZ S ν g k :=
    funext fun z ↦ responseOf_slice_eq hS ν hg hk z
  rw [e]
  refine (contDiffOn_responseTheta_add hS ν).comp_contDiff (contDiff_sliceZ hS ν hg hk) fun z ↦ ?_
  change m₀ + (sliceZ S ν g k z : J → ℝ) ∈ Ω
  rw [coe_sliceZ hS ν hg hk z, add_sub_cancel]
  exact sliceMean_mem hS ν hg hk z

omit [MeasurableSpace X] [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg hk in
/-- Moving along a coordinate line of the slice adds a multiple of one direction. -/
theorem sliceFun_add_single [DecidableEq ι] (z : ι → ℝ) (i : ι) (t : ℝ) :
    sliceFun g k (z + t • Pi.single i 1) = fun x ↦ sliceFun g k z x + t * k i x := by
  funext x
  simp only [sliceFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

/-- The response along a coordinate line of the slice. -/
theorem hasDerivAt_slice_line [DecidableEq ι] (z : ι → ℝ) (i : ι) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ responseOf hS ν (sliceFun g k (z + t • Pi.single i 1)))
      (responseVel hS ν (bdd_slice hg hk (z + t₀ • Pi.single i 1)) (hk i)) t₀ := by
  have h := hasDerivAt_responseOf_add hS ν (bdd_slice hg hk z) (hk i) t₀
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
  · rw [sliceFun_add_single]
  · exact responseVel_congr hS ν _ _ _ _ (sliceFun_add_single (g := g) (k := k) z i t₀).symm rfl

set_option linter.unusedFintypeInType false in
omit [MeasurableSpace X] [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg hk in
theorem hasDerivAt_line [DecidableEq ι] (z : ι → ℝ) (i : ι) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ z + t • (Pi.single i 1 : ι → ℝ)) (Pi.single i 1) t₀ := by
  simpa using ((hasDerivAt_id t₀).smul_const (Pi.single i 1 : ι → ℝ)).const_add z

/-- **The Fréchet derivative of the slice is the response velocity**: `DΦ(z)[eᵢ] = DΦ_{g_z}[kᵢ]`. -/
theorem fderiv_slice_single [DecidableEq ι] (z : ι → ℝ) (i : ι) :
    fderiv ℝ (fun z : ι → ℝ ↦ responseOf hS ν (sliceFun g k z)) z (Pi.single i 1) =
      responseVel hS ν (bdd_slice hg hk z) (hk i) := by
  have hF := ((contDiff_responseOf_slice hS ν hg hk).differentiable (by simp)).differentiableAt
    (x := z) |>.hasFDerivAt
  have h1 := hF.comp_hasDerivAt_of_eq 0 (hasDerivAt_line (ι := ι) z i 0)
    (by simp : z = z + (0 : ℝ) • (Pi.single i 1 : ι → ℝ))
  have h2 := hasDerivAt_slice_line hS ν hg hk z i 0
  rw [h1.unique h2]
  exact responseVel_congr hS ν _ _ _ _ (by simp) rfl

/-- **The second Fréchet derivative of the slice is the response Hessian**:
`D²Φ(z)[eⱼ, eᵢ] = H_{g_z}(kⱼ, kᵢ)`. -/
theorem fderiv_fderiv_slice_single [DecidableEq ι] (z : ι → ℝ) (i j : ι) :
    fderiv ℝ (fderiv ℝ (fun z : ι → ℝ ↦ responseOf hS ν (sliceFun g k z))) z (Pi.single j 1)
        (Pi.single i 1) =
      responseHess hS ν (bdd_slice hg hk z) (hk j) (hk i) := by
  have hG : ContDiff ℝ ∞ (fderiv ℝ (fun z : ι → ℝ ↦ responseOf hS ν (sliceFun g k z))) :=
    (contDiff_infty_iff_fderiv.1 (contDiff_responseOf_slice hS ν hg hk)).2
  have e : (fun z : ι → ℝ ↦ fderiv ℝ (fun z : ι → ℝ ↦ responseOf hS ν (sliceFun g k z)) z
      (Pi.single i 1)) = fun z ↦ responseVel hS ν (bdd_slice hg hk z) (hk i) :=
    funext fun z ↦ fderiv_slice_single hS ν hg hk z i
  have h1 : fderiv ℝ (fun z : ι → ℝ ↦ fderiv ℝ (fun z : ι → ℝ ↦ responseOf hS ν (sliceFun g k z))
      z (Pi.single i 1)) z (Pi.single j 1) =
      fderiv ℝ (fderiv ℝ (fun z : ι → ℝ ↦ responseOf hS ν (sliceFun g k z))) z (Pi.single j 1)
        (Pi.single i 1) := by
    rw [fderiv_clm_apply (hG.differentiable (by simp)).differentiableAt (differentiableAt_const _)]
    simp
  rw [← h1, e]
  have hV : ContDiff ℝ ∞ (fun z ↦ responseVel hS ν (bdd_slice hg hk z) (hk i)) := by
    rw [← e]
    exact hG.clm_apply contDiff_const
  have hF := (hV.differentiable (by simp)).differentiableAt (x := z) |>.hasFDerivAt
  have hl := hF.comp_hasDerivAt_of_eq 0 (hasDerivAt_line (ι := ι) z j 0)
    (by simp : z = z + (0 : ℝ) • (Pi.single j 1 : ι → ℝ))
  have h2 : HasDerivAt (fun t : ℝ ↦ responseVel hS ν (bdd_slice hg hk (z + t • Pi.single j 1))
      (hk i)) (responseHess hS ν (bdd_slice hg hk z) (hk j) (hk i)) 0 := by
    have h := hasDerivAt_responseVel_add hS ν (bdd_slice hg hk z) (hk j) (hk i) 0
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
    · exact responseVel_congr hS ν _ _ _ _ (sliceFun_add_single (g := g) (k := k) z j t) rfl
    · exact responseHess_congr hS ν _ _ _ _ (by funext x; simp)
  exact hl.unique h2

/-- The slice has a symmetric second Fréchet derivative. -/
theorem isSymmSndFDerivAt_slice (z : ι → ℝ) :
    IsSymmSndFDerivAt ℝ (fun z : ι → ℝ ↦ responseOf hS ν (sliceFun g k z)) z :=
  (contDiff_responseOf_slice hS ν hg hk).contDiffAt.isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact natCast_le_infty 2)

/-- **The symmetry of the response Hessian from general calculus**: `H_g(kⱼ,kᵢ) = H_g(kᵢ,kⱼ)`,
as the symmetry of the second Fréchet derivative of a `C²` slice. -/
theorem responseHess_symm_of_slice (z : ι → ℝ) (i j : ι) :
    responseHess hS ν (bdd_slice hg hk z) (hk j) (hk i) =
      responseHess hS ν (bdd_slice hg hk z) (hk i) (hk j) := by
  classical
  rw [← fderiv_fderiv_slice_single hS ν hg hk z i j, ← fderiv_fderiv_slice_single hS ν hg hk z j i]
  exact isSymmSndFDerivAt_slice hS ν hg hk z _ _

end Slice

end Laplace.Multi
