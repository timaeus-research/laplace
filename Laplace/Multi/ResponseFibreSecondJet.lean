/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseSliceSubmersion

/-!
# The second jet of the response fibre

Near a data law `g` the fixed-response fibre `Φ⁻¹(Φ(g))` inside a horizontally augmented slice is
the graph `u = σ₀(z)` of the fibre section at the response `Φ(g)` (`fibreGraph`). Its first jet is
minus the slice velocity, `Dσ₀(0) ξ = −DΦ_g[⟨ξ,k⟩]` (`hasFDerivAt_fibreGraph_zero`), so the tangent
vectors of the fibre are the **verticalised** slice directions `Jξ = ⟨ξ,k⟩ − hor_g(DΦ_g[⟨ξ,k⟩])`
(`fibreTangent`, `responseVel_fibreTangent`: `DΦ_g[Jξ] = 0`). Differentiating the identity
`Ψ(z, σ₀(z)) = Φ(g)` twice gives the second jet of the fibre graph as the response Hessian on the
vertical tangents,

  `D²σ₀(0)[η, ξ] = −H_g(Jη, Jξ)`   (`fderiv_fderiv_fibreGraph_zero`),

the quadratic bending of the fixed-response fibre in log-density coordinates. The fibres are convex
in density coordinates (`convex_responseFibre`) but curved in log-density coordinates, and their
curvature is the response Hessian restricted to the invisible directions.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Laplace.Multi

section Jet

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {ι : Type*} [Fintype ι] {g : X → ℝ} (hg : Bdd g) {k : ι → X → ℝ} (hk : ∀ i, Bdd (k i))
include hS hg hk

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The augmented coefficient map. -/
local notation "L" => augCoeffL S ν ι

/-- The augmented slice in coefficient form. -/
local notation "sl" => fun c ↦ responseOf hS ν (sliceFun g (augDir hS ν hg k) c)

/-- **The fibre graph**: the fibre section at the response of `g`, `σ₀(z) = σ(z, Φ(g))`. -/
noncomputable def fibreGraph (z : ι → ℝ) : 𝕍 := fibreSection hS ν hg hk (z, responseOf hS ν g)

theorem fibreGraph_zero : fibreGraph hS ν hg hk 0 = 0 := fibreSection_base hS ν hg hk

theorem contDiffAt_fibreGraph : ContDiffAt ℝ ∞ (fibreGraph hS ν hg hk) 0 :=
  (contDiffAt_fibreSection hS ν hg hk).comp (0 : ι → ℝ) (contDiffAt_id.prodMk contDiffAt_const)

/-- **The first jet of the fibre graph** is minus the slice velocity. -/
theorem hasFDerivAt_fibreGraph_zero :
    HasFDerivAt (fibreGraph hS ν hg hk) (-sliceVelL hS ν hg hk) 0 := by
  have hpair : HasFDerivAt (fun z : ι → ℝ ↦ (z, responseOf hS ν g))
      ((ContinuousLinearMap.id ℝ (ι → ℝ)).prod 0) 0 :=
    (hasFDerivAt_id (0 : ι → ℝ)).prodMk (hasFDerivAt_const (responseOf hS ν g) 0)
  have h := (hasStrictFDerivAt_fibreSection hS ν hg hk).hasFDerivAt.comp (0 : ι → ℝ) hpair
  have h' : HasFDerivAt (fibreGraph hS ν hg hk)
      (((ContinuousLinearMap.snd ℝ (ι → ℝ) 𝕍).comp (augDerivInvL hS ν hg hk)).comp
        ((ContinuousLinearMap.id ℝ (ι → ℝ)).prod 0)) 0 := h
  refine h'.congr_fderiv ?_
  ext ξ
  simp [augDerivInvL_apply]

theorem fderiv_fibreGraph_zero : fderiv ℝ (fibreGraph hS ν hg hk) 0 = -sliceVelL hS ν hg hk :=
  (hasFDerivAt_fibreGraph_zero hS ν hg hk).fderiv

/-- The fibre graph lies in the fibre: `Ψ(z, σ₀(z)) = Φ(g)` near `0`. -/
theorem eventually_augSlice_fibreGraph :
    ∀ᶠ z : ι → ℝ in 𝓝 0, augSlice hS ν hg k (z, fibreGraph hS ν hg hk z) = responseOf hS ν g := by
  have ht : Tendsto (fun z : ι → ℝ ↦ (z, responseOf hS ν g)) (𝓝 0)
      (𝓝 ((0 : ι → ℝ), responseOf hS ν g)) :=
    (continuous_id.prodMk continuous_const).tendsto 0
  exact ht.eventually (eventually_augSlice_fibreSection hS ν hg hk)

theorem eventually_hasFDerivAt_fibreGraph :
    ∀ᶠ z : ι → ℝ in 𝓝 0,
      HasFDerivAt (fibreGraph hS ν hg hk) (fderiv ℝ (fibreGraph hS ν hg hk) z) z := by
  have h := ((contDiffAt_fibreGraph hS ν hg hk).of_le
    (by exact_mod_cast natCast_le_infty 2)).eventually (by simp)
  filter_upwards [h] with z hz
  exact (hz.differentiableAt (by simp)).hasFDerivAt

theorem hasFDerivAt_fderiv_fibreGraph :
    HasFDerivAt (fderiv ℝ (fibreGraph hS ν hg hk))
      (fderiv ℝ (fderiv ℝ (fibreGraph hS ν hg hk)) 0) 0 := by
  have h := (contDiffAt_fibreGraph hS ν hg hk).fderiv_right (m := 1)
    (by exact_mod_cast natCast_le_infty 2)
  exact (h.differentiableAt one_ne_zero).hasFDerivAt

theorem contDiff_sl : ContDiff ℝ ∞ sl := contDiff_responseOf_slice hS ν hg (bdd_augDir hS ν hg hk)

theorem hasFDerivAt_sl (c : ι ⊕ Fin (Module.finrank ℝ 𝕍) → ℝ) :
    HasFDerivAt sl (fderiv ℝ sl c) c :=
  ((contDiff_sl hS ν hg hk).differentiable (by simp) c).hasFDerivAt

theorem hasFDerivAt_fderiv_sl (c : ι ⊕ Fin (Module.finrank ℝ 𝕍) → ℝ) :
    HasFDerivAt (fderiv ℝ sl) (fderiv ℝ (fderiv ℝ sl) c) c :=
  (((contDiff_infty_iff_fderiv.1 (contDiff_sl hS ν hg hk)).2).differentiable (by simp)
    c).hasFDerivAt

/-- **The first-order fibre identity** near `0`: the slice derivative kills the tangent of the
graph, `Dsl(L(z,σ₀ z))[L(ξ, Dσ₀(z) ξ)] = 0`. -/
theorem eventually_fderiv_sl_fibreGraph (ξ : ι → ℝ) :
    ∀ᶠ z : ι → ℝ in 𝓝 0,
      fderiv ℝ sl (L (z, fibreGraph hS ν hg hk z))
        (L (ξ, fderiv ℝ (fibreGraph hS ν hg hk) z ξ)) = 0 := by
  filter_upwards [(eventually_augSlice_fibreGraph hS ν hg hk).eventually_nhds,
    eventually_hasFDerivAt_fibreGraph hS ν hg hk] with z hz hσ
  have hpair : HasFDerivAt (fun z' : ι → ℝ ↦ (z', fibreGraph hS ν hg hk z'))
      ((ContinuousLinearMap.id ℝ (ι → ℝ)).prod (fderiv ℝ (fibreGraph hS ν hg hk) z)) z :=
    (hasFDerivAt_id z).prodMk hσ
  have hcomp := (hasFDerivAt_sl hS ν hg hk (L (z, fibreGraph hS ν hg hk z))).comp z
    ((L).hasFDerivAt.comp z hpair)
  have h1 : HasFDerivAt (fun z' ↦ augSlice hS ν hg k (z', fibreGraph hS ν hg hk z'))
      ((fderiv ℝ sl (L (z, fibreGraph hS ν hg hk z))).comp
        ((L).comp ((ContinuousLinearMap.id ℝ (ι → ℝ)).prod (fderiv ℝ (fibreGraph hS ν hg hk) z))))
      z := hcomp
  have h0 : HasFDerivAt (fun z' ↦ augSlice hS ν hg k (z', fibreGraph hS ν hg hk z'))
      (0 : (ι → ℝ) →L[ℝ] 𝕍) z :=
    (hasFDerivAt_const (responseOf hS ν g) z).congr_of_eventuallyEq hz
  have e := h1.unique h0
  have := congrArg (fun T : (ι → ℝ) →L[ℝ] 𝕍 ↦ T ξ) e
  simpa using this

/-- The slice derivative at the base is the identity on the horizontal component:
`Dsl(0)[L(0, w)] = w`. -/
theorem fderiv_sl_zero_horizontal (w : 𝕍) :
    fderiv ℝ sl (L ((0 : ι → ℝ), (0 : 𝕍))) (L ((0 : ι → ℝ), w)) = w := by
  have hΨ : HasFDerivAt (augSlice hS ν hg k)
      ((fderiv ℝ sl (L ((0 : ι → ℝ), (0 : 𝕍)))).comp (L)) ((0 : ι → ℝ), (0 : 𝕍)) :=
    (hasFDerivAt_sl hS ν hg hk _).comp _ (L).hasFDerivAt
  have h := fderiv_augSlice_zero hS ν hg hk 0 w
  rw [hΨ.fderiv, ContinuousLinearMap.comp_apply, map_zero, zero_add] at h
  exact h

/-- **The second jet of the fibre graph in coefficient form**:
`D²σ₀(0)[η, ξ] = −D²sl(0)[L(η, −Vη), L(ξ, −Vξ)]`. -/
theorem fderiv_fderiv_fibreGraph_zero_eq_neg (ξ η : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (fibreGraph hS ν hg hk)) 0 η ξ =
      -(fderiv ℝ (fderiv ℝ sl) (L ((0 : ι → ℝ), (0 : 𝕍)))
        (L (η, -sliceVelL hS ν hg hk η)) (L (ξ, -sliceVelL hS ν hg hk ξ))) := by
  have hσ0 : HasFDerivAt (fibreGraph hS ν hg hk) (fderiv ℝ (fibreGraph hS ν hg hk) 0) 0 :=
    (hasFDerivAt_fibreGraph_zero hS ν hg hk).differentiableAt.hasFDerivAt
  have hpair : HasFDerivAt (fun z : ι → ℝ ↦ (z, fibreGraph hS ν hg hk z))
      ((ContinuousLinearMap.id ℝ (ι → ℝ)).prod (fderiv ℝ (fibreGraph hS ν hg hk) 0)) 0 :=
    (hasFDerivAt_id (0 : ι → ℝ)).prodMk hσ0
  have hc : HasFDerivAt (fun z : ι → ℝ ↦ fderiv ℝ sl (L (z, fibreGraph hS ν hg hk z)))
      ((fderiv ℝ (fderiv ℝ sl) (L ((0 : ι → ℝ), fibreGraph hS ν hg hk 0))).comp
        ((L).comp ((ContinuousLinearMap.id ℝ (ι → ℝ)).prod
          (fderiv ℝ (fibreGraph hS ν hg hk) 0)))) 0 :=
    (hasFDerivAt_fderiv_sl hS ν hg hk _).comp (0 : ι → ℝ) ((L).hasFDerivAt.comp 0 hpair)
  have hD := (hasFDerivAt_fderiv_fibreGraph hS ν hg hk).clm_apply (hasFDerivAt_const ξ (0 : ι → ℝ))
  have hu : HasFDerivAt (fun z : ι → ℝ ↦ L (ξ, fderiv ℝ (fibreGraph hS ν hg hk) z ξ))
      ((L).comp ((0 : (ι → ℝ) →L[ℝ] (ι → ℝ)).prod
        ((fderiv ℝ (fibreGraph hS ν hg hk) 0).comp 0 +
          (fderiv ℝ (fderiv ℝ (fibreGraph hS ν hg hk)) 0).flip ξ))) 0 :=
    (L).hasFDerivAt.comp (0 : ι → ℝ) ((hasFDerivAt_const ξ (0 : ι → ℝ)).prodMk hD)
  have hN := hc.clm_apply hu
  have h0 : HasFDerivAt (fun z : ι → ℝ ↦ fderiv ℝ sl (L (z, fibreGraph hS ν hg hk z))
      (L (ξ, fderiv ℝ (fibreGraph hS ν hg hk) z ξ))) (0 : (ι → ℝ) →L[ℝ] 𝕍) 0 :=
    (hasFDerivAt_const (0 : 𝕍) (0 : ι → ℝ)).congr_of_eventuallyEq
      ((eventually_fderiv_sl_fibreGraph hS ν hg hk ξ).mono fun z hz ↦ hz)
  have e := hN.unique h0
  have h := congrArg (fun T : (ι → ℝ) →L[ℝ] 𝕍 ↦ T η) e
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.prod_apply, _root_.zero_apply, map_zero, zero_add,
    ContinuousLinearMap.coe_id', id_eq] at h
  rw [fibreGraph_zero, fderiv_fibreGraph_zero, fderiv_sl_zero_horizontal hS ν hg hk] at h
  simp only [_root_.neg_apply] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The second derivative of the augmented slice in coefficient form is the response Hessian of
the corresponding bounded directions. -/
theorem fderiv_fderiv_sl_zero (a b : ι ⊕ Fin (Module.finrank ℝ 𝕍) → ℝ) :
    fderiv ℝ (fderiv ℝ sl) 0 a b =
      responseHess hS ν hg (bdd_dirLoss (bdd_augDir hS ν hg hk) a)
        (bdd_dirLoss (bdd_augDir hS ν hg hk) b) := by
  classical
  have hterm : ∀ α β, fderiv ℝ (fderiv ℝ sl) 0 (Pi.single α 1) (Pi.single β 1) =
      responseHess hS ν hg (bdd_augDir hS ν hg hk α) (bdd_augDir hS ν hg hk β) := fun α β ↦ by
    rw [fderiv_fderiv_slice_single hS ν hg (bdd_augDir hS ν hg hk) 0 β α]
    exact responseHess_congr' hS ν _ hg _ _ _ _ (sliceFun_zero' hS ν hg (k := k)) rfl rfl
  have e1 : fderiv ℝ (fderiv ℝ sl) 0 a =
      ∑ α, a α • fderiv ℝ (fderiv ℝ sl) 0 (Pi.single α 1) := by
    conv_lhs => rw [eq_sum_single_aug ν a]
    rw [map_sum]
    simp only [map_smul]
  have e2 : ∀ α, fderiv ℝ (fderiv ℝ sl) 0 (Pi.single α 1) b =
      ∑ β, b β • fderiv ℝ (fderiv ℝ sl) 0 (Pi.single α 1) (Pi.single β 1) := fun α ↦ by
    conv_lhs => rw [eq_sum_single_aug ν b]
    rw [map_sum]
    simp only [map_smul]
  have hlhs : fderiv ℝ (fderiv ℝ sl) 0 a b =
      ∑ α, ∑ β, (a α * b β) • responseHess hS ν hg (bdd_augDir hS ν hg hk α)
        (bdd_augDir hS ν hg hk β) := by
    rw [e1, _root_.sum_apply]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [_root_.smul_apply, e2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun β _ ↦ ?_
    rw [hterm, smul_smul]
  have hrhs : responseHess hS ν hg (bdd_dirLoss (bdd_augDir hS ν hg hk) a)
      (bdd_dirLoss (bdd_augDir hS ν hg hk) b) =
      ∑ β, ∑ α, (b β * a α) • responseHess hS ν hg (bdd_augDir hS ν hg hk α)
        (bdd_augDir hS ν hg hk β) := by
    rw [responseHess_dirLoss hS ν hg (bdd_augDir hS ν hg hk) b]
    refine Finset.sum_congr rfl fun β _ ↦ ?_
    rw [responseHess_symm hS ν hg, responseHess_dirLoss hS ν hg (bdd_augDir hS ν hg hk) a,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [smul_smul, responseHess_symm hS ν hg]
  rw [hlhs, hrhs, Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ ↦ Finset.sum_congr rfl fun α _ ↦ ?_
  rw [mul_comm]

/-- The response velocity of an augmented direction: `DΦ_g[⟨ξ,k⟩ + hor_g(w)] = DΦ_g[⟨ξ,k⟩] + w`. -/
theorem responseVel_augDir_coeff (ξ : ι → ℝ) (w : 𝕍) :
    responseVel hS ν hg (bdd_dirLoss (bdd_augDir hS ν hg hk) (L (ξ, w))) =
      sliceVelL hS ν hg hk ξ + w := by
  rw [responseVel_dirLoss hS ν hg (bdd_augDir hS ν hg hk), augCoeffL_apply, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  congr 1
  · rw [sliceVelL_apply, responseVel_dirLoss hS ν hg hk ξ]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
  · conv_rhs => rw [← (wBasis S ν).sum_equivFun w]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1
    exact responseVel_horizontalLift hS ν hg _

/-- **The vertical tangent of the fibre**: `Jξ = ⟨ξ,k⟩ − hor_g(DΦ_g[⟨ξ,k⟩])`, in augmented
coefficients. -/
noncomputable def fibreTangent (ξ : ι → ℝ) : X → ℝ :=
  dirLoss (augDir hS ν hg k) (L (ξ, -sliceVelL hS ν hg hk ξ))

theorem bdd_fibreTangent (ξ : ι → ℝ) : Bdd (fibreTangent hS ν hg hk ξ) :=
  bdd_dirLoss (bdd_augDir hS ν hg hk) _

/-- **The fibre tangents are invisible**: `DΦ_g[Jξ] = 0`. -/
theorem responseVel_fibreTangent (ξ : ι → ℝ) :
    responseVel hS ν hg (bdd_fibreTangent hS ν hg hk ξ) = 0 := by
  unfold fibreTangent
  rw [responseVel_augDir_coeff hS ν hg hk, add_neg_cancel]

/-- **The second jet of the response fibre**: the second derivative of the fibre graph is minus
the response Hessian on the vertical tangents, `D²σ₀(0)[η, ξ] = −H_g(Jη, Jξ)`. -/
theorem fderiv_fderiv_fibreGraph_zero (ξ η : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (fibreGraph hS ν hg hk)) 0 η ξ =
      -responseHess hS ν hg (bdd_fibreTangent hS ν hg hk η) (bdd_fibreTangent hS ν hg hk ξ) := by
  rw [fderiv_fderiv_fibreGraph_zero_eq_neg hS ν hg hk, Prod.mk_zero_zero, map_zero,
    fderiv_fderiv_sl_zero hS ν hg hk]
  rfl

end Jet

end Laplace.Multi
