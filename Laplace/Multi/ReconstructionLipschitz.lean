/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseTaylor
import Laplace.Multi.DualFlat
import Laplace.Multi.GlobalChart
import Laplace.Multi.AtlasRefinement

/-!
# The reconstruction as a total-variation Lipschitz retraction

The reconstruction `M ↦ Π(M)` is total-variation Lipschitz on every compact convex subset of the
relative interior of the moment body, with the Lipschitz constant `√(|J| Λ)`, `Λ` a bound on the
inverse chart derivative `R_M = Dθ(M)` there:

`∫ |q_{M'} − q_M| dν ≤ √(|J| Λ) ‖M' − M‖` (`integral_abs_famDens_sub_le_of_segment`,
`exists_tv_lipschitz_of_isCompact_convex`).

The proof is the mean value inequality for the observable response `t ↦ E_{Q_{M_t}}F` along the
segment `M_t = M + t(M' − M)` (derivative `E_{Q_{M_t}}[F ℓ_{M_t, M'−M}]`, differentiable at every
interior point), the Cauchy–Schwarz bound `E_Q|ℓ_u| ≤ √(E_Q ℓ_u²) = √⟨u, Σ⁻¹u⟩ ≤ √(|J|‖R‖) ‖u‖`
(`integral_abs_responseScore_le_sqrt`, `fisherForm_self_le`), and the sign test
`F = sign(q_{M'} − q_M)` which turns the bound on observables into the total-variation bound. No
total-variation topology on measures is needed.

Composed with the response of a data density, `d ↦ E_{dν}S`, which is Lipschitz from `L¹(ν)` to the
sup norm with constant `B = sup‖S‖` (`norm_density_response_sub_le`), this gives the reconstruction
`d ↦ Π(E_{dν}S)` as a total-variation Lipschitz map of data laws whose responses lie in a compact
convex interior set (`integral_abs_famDens_density_sub_le`). Finally the reconstruction is a
retraction:
`Π(E_{P_θ}S) = P_θ` for every family member (`responseProjection_mean_familyMeasure`, from
`AtlasRefinement`), and its
derivative `u ↦ Q ℓ_{M,u}` transmits exactly the moment perturbation (`respCov_responseScore`) with
zero mass (`integral_responseScore`) — the derivative is a projection onto the tangent scores along
the moment-invisible perturbations. `reconstruction_retraction` packages the three statements.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory

namespace Laplace.Multi

section Score

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
include hS

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative as a linear equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **Cauchy–Schwarz for the response score**: `E_Q|ℓ_u| ≤ √(E_Q ℓ_u²)`. -/
theorem integral_abs_responseScore_le_sqrt (u : 𝕍) :
    ∫ x, |responseScore hS ν M u x| ∂(Pfam (θr M)) ≤ √(fisherForm hS ν M u u) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  obtain ⟨hm, B, hB⟩ := bdd_responseScore hS ν M u
  have hL : MemLp (fun x ↦ |responseScore hS ν M u x|) 2 (Pfam (θr M)) :=
    MemLp.of_bound hm.abs.aestronglyMeasurable B (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_abs]
      exact hB x)
  have hv := variance_nonneg (fun x ↦ |responseScore hS ν M u x|) (Pfam (θr M))
  rw [variance_eq_sub hL] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  have e : ∫ x, responseScore hS ν M u x ^ 2 ∂(Pfam (θr M)) = fisherForm hS ν M u u := by
    unfold fisherForm
    exact integral_congr_ae (Eventually.of_forall fun x ↦ sq _)
  rw [e] at hv
  have hnn : 0 ≤ ∫ x, |responseScore hS ν M u x| ∂(Pfam (θr M)) :=
    integral_nonneg fun x ↦ abs_nonneg _
  exact (Real.le_sqrt hnn (by nlinarith)).2 (by linarith)

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- **The Fisher form is bounded by the inverse chart derivative**: `E_Q ℓ_u² ≤ |J| ‖R_M‖ ‖u‖²`. -/
theorem fisherForm_self_le (u : 𝕍) :
    fisherForm hS ν M u u ≤ (Fintype.card J : ℝ) *
      ‖(ContinuousLinearEquiv.symm (CDE (θr M)) : 𝕍 →L[ℝ] 𝕍)‖ * ‖u‖ ^ 2 := by
  rw [fisherForm_eq_neg_dotJ hS ν hrel]
  refine (neg_le_abs _).trans ((abs_dotJ_le_card_mul _ _).trans ?_)
  rw [Submodule.norm_coe, Submodule.norm_coe]
  calc (Fintype.card J : ℝ) * ‖ContinuousLinearEquiv.symm (CDE (θr M)) u‖ * ‖u‖
      ≤ (Fintype.card J : ℝ) *
          (‖(ContinuousLinearEquiv.symm (CDE (θr M)) : 𝕍 →L[ℝ] 𝕍)‖ * ‖u‖) * ‖u‖ := by
        gcongr
        exact (ContinuousLinearEquiv.symm (CDE (θr M)) : 𝕍 →L[ℝ] 𝕍).le_opNorm u
    _ = (Fintype.card J : ℝ) *
          ‖(ContinuousLinearEquiv.symm (CDE (θr M)) : 𝕍 →L[ℝ] 𝕍)‖ * ‖u‖ ^ 2 := by ring

end Score

section Segment

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative as a linear equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

variable {M M' : J → ℝ} {Λ : ℝ}
  (hseg : ∀ t ∈ Icc (0 : ℝ) 1,
    M + t • (M' - M) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
  (hΛ : ∀ t ∈ Icc (0 : ℝ) 1,
    ‖(ContinuousLinearEquiv.symm (chartDerivEquiv measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS (responseTheta measurable_const (integrable_const 1)
        (fun _ ↦ one_pos) (one_integral_pos ν) hS (M + t • (M' - M)))) :
      dirSpan ν (fun _ ↦ (1 : ℝ)) S →L[ℝ] dirSpan ν (fun _ ↦ (1 : ℝ)) S)‖ ≤ Λ)
include hseg hΛ

/-- **The observable response is Lipschitz along an interior segment**: for `|F| ≤ 1`,
`|E_{Π(M')}F − E_{Π(M)}F| ≤ √(|J| Λ) ‖M' − M‖`. -/
theorem abs_integral_sub_le_of_segment {F : X → ℝ} (hF : Bdd F) (hF1 : ∀ x, |F x| ≤ 1) :
    |(∫ x, F x ∂(Pfam (θr M'))) - ∫ x, F x ∂(Pfam (θr M))| ≤
      √((Fintype.card J : ℝ) * Λ) * ‖M' - M‖ := by
  have hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
    simpa using hseg 0 ⟨le_rfl, zero_le_one⟩
  have hrel' : M' ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
    simpa using hseg 1 ⟨zero_le_one, le_rfl⟩
  have hmem : M' - M ∈ 𝕍 := by
    have h1 := sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS (intrinsicInterior_subset hrel')
    have h2 := sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS (intrinsicInterior_subset hrel)
    have e : M' - M = (M' - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) -
        (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) := by abel
    rw [e]
    exact Submodule.sub_mem _ h1 h2
  obtain ⟨u, hu⟩ : ∃ u : 𝕍, (u : J → ℝ) = M' - M := ⟨⟨M' - M, hmem⟩, rfl⟩
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = √((Fintype.card J : ℝ) * Λ) * ‖u‖ := ⟨_, rfl⟩
  have hcoe : ∀ t : ℝ, M + ((t • u : 𝕍) : J → ℝ) = M + t • (M' - M) := fun t ↦ by
    rw [Submodule.coe_smul, hu]
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ ↦ ∫ x, F x ∂(Pfam (θr (M + ((t • u : 𝕍) : J → ℝ)))))
        (responseDerivField hS ν M F (t • u) u) t := fun t ht ↦ by
    have hz : M + ((t • u : 𝕍) : J → ℝ) ∈
        intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
      rw [hcoe]
      exact hseg t ht
    have h := hasFDerivAt_integral_response_at hS ν hF hz
    have hl : HasDerivAt (fun t : ℝ ↦ t • u) u t := by
      simpa using (hasDerivAt_id t).smul_const u
    exact h.comp_hasDerivAt t hl
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖responseDerivField hS ν M F (t • u) u‖ ≤ C := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    have hz : M + ((t • u : 𝕍) : J → ℝ) ∈
        intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
      rw [hcoe]
      exact hseg t ht'
    have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M + ((t • u : 𝕍) : J → ℝ))
    rw [responseDerivField_apply hS ν hF hz, Real.norm_eq_abs]
    have hI : Integrable (fun x ↦ |F x * responseScore hS ν (M + ((t • u : 𝕍) : J → ℝ)) u x|)
        (Pfam (θr (M + ((t • u : 𝕍) : J → ℝ)))) :=
      (integrable_of_bdd_prob _ (hF.mul (bdd_responseScore hS ν _ u))).abs
    have hI' : Integrable (fun x ↦ |responseScore hS ν (M + ((t • u : 𝕍) : J → ℝ)) u x|)
        (Pfam (θr (M + ((t • u : 𝕍) : J → ℝ)))) :=
      (integrable_of_bdd_prob _ (bdd_responseScore hS ν _ u)).abs
    calc |∫ x, F x * responseScore hS ν (M + ((t • u : 𝕍) : J → ℝ)) u x
          ∂(Pfam (θr (M + ((t • u : 𝕍) : J → ℝ))))|
        ≤ ∫ x, |F x * responseScore hS ν (M + ((t • u : 𝕍) : J → ℝ)) u x|
          ∂(Pfam (θr (M + ((t • u : 𝕍) : J → ℝ)))) := by
          have := norm_integral_le_integral_norm (μ := Pfam (θr (M + ((t • u : 𝕍) : J → ℝ))))
            (fun x ↦ F x * responseScore hS ν (M + ((t • u : 𝕍) : J → ℝ)) u x)
          simpa only [Real.norm_eq_abs] using this
      _ ≤ ∫ x, |responseScore hS ν (M + ((t • u : 𝕍) : J → ℝ)) u x|
          ∂(Pfam (θr (M + ((t • u : 𝕍) : J → ℝ)))) := by
          refine integral_mono hI hI' fun x ↦ ?_
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hF1 x)
      _ ≤ √(fisherForm hS ν (M + ((t • u : 𝕍) : J → ℝ)) u u) :=
          integral_abs_responseScore_le_sqrt hS ν u
      _ ≤ √((Fintype.card J : ℝ) * Λ * ‖u‖ ^ 2) := by
          refine Real.sqrt_le_sqrt ((fisherForm_self_le hS ν hz u).trans ?_)
          have := hΛ t ht'
          rw [← hcoe] at this
          gcongr
      _ = C := by
          rw [hC, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ ↦ ∫ x, F x ∂(Pfam (θr (M + ((t • u : 𝕍) : J → ℝ))))) (a := 0) (b := 1)
    (fun t ht ↦ (hderiv t ht).hasDerivWithinAt) hbound 1 (right_mem_Icc.mpr zero_le_one)
  simp only [one_smul, zero_smul, Submodule.coe_zero, add_zero, hu, add_sub_cancel, sub_zero,
    mul_one, Real.norm_eq_abs] at key
  rw [hC, ← Submodule.norm_coe, hu] at key
  exact key

/-- **The reconstruction is total-variation Lipschitz along an interior segment**:
`∫ |q_{M'} − q_M| dν ≤ √(|J| Λ) ‖M' − M‖`. -/
theorem integral_abs_famDens_sub_le_of_segment :
    ∫ x, |famDens S ν (θr M') x - famDens S ν (θr M) x| ∂ν ≤
      √((Fintype.card J : ℝ) * Λ) * ‖M' - M‖ := by
  obtain ⟨F, hF⟩ : ∃ F : X → ℝ, F = fun x ↦
      if 0 ≤ famDens S ν (θr M') x - famDens S ν (θr M) x then (1 : ℝ) else -1 := ⟨_, rfl⟩
  have hFm : Measurable F := by
    rw [hF]
    exact Measurable.ite (measurableSet_le measurable_const
      ((measurable_famDens hS ν _).sub (measurable_famDens hS ν _))) measurable_const
      measurable_const
  have hF1 : ∀ x, |F x| ≤ 1 := fun x ↦ by
    rw [hF]
    beta_reduce
    split_ifs <;> simp
  have h := abs_integral_sub_le_of_segment hS ν hseg hΛ ⟨hFm, 1, hF1⟩ hF1
  rw [integral_famDens_mul hS ν, integral_famDens_mul hS ν] at h
  have hI : ∀ N : J → ℝ, Integrable (fun x ↦ famDens S ν N x * F x) ν := fun N ↦
    (integrable_famDens hS ν N).mul_bdd hFm.aestronglyMeasurable (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]
      exact hF1 x)
  have e : (∫ x, famDens S ν (θr M') x * F x ∂ν) - ∫ x, famDens S ν (θr M) x * F x ∂ν =
      ∫ x, |famDens S ν (θr M') x - famDens S ν (θr M) x| ∂ν := by
    rw [← integral_sub (hI _) (hI _)]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    rw [hF]
    beta_reduce
    split_ifs with h0
    · rw [abs_of_nonneg h0]
      ring
    · rw [abs_of_neg (lt_of_not_ge h0)]
      ring
  rw [e, abs_of_nonneg (integral_nonneg fun x ↦ abs_nonneg _)] at h
  exact h

end Segment

section Compact

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative as a linear equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **Compact-uniform total-variation Lipschitz bound**: on every compact convex subset `C` of the
relative interior of the moment body there is `L` with `∫ |q_{M'} − q_M| dν ≤ L ‖M' − M‖` for all
`M, M' ∈ C`. -/
theorem exists_tv_lipschitz_of_isCompact_convex {C : Set (J → ℝ)} (hC : IsCompact C)
    (hCc : Convex ℝ C) (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ M ∈ C, ∀ M' ∈ C,
      ∫ x, |famDens S ν (θr M') x - famDens S ν (θr M) x| ∂ν ≤ L * ‖M' - M‖ := by
  have hcont : Continuous (fun m : intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) ↦
      ‖(ContinuousLinearEquiv.symm (CDE ((relintChart hS ν).symm m)) : 𝕍 →L[ℝ] 𝕍)‖) :=
    ((continuous_chartDerivEquiv_symm measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS).comp (relintChart hS ν).symm.continuous).norm
  have hCs : IsCompact (Subtype.val ⁻¹' C :
      Set (intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr hCK]
    exact hC
  obtain ⟨Λ, hΛ⟩ := hCs.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨√((Fintype.card J : ℝ) * max Λ 0), by positivity, fun M hM M' hM' ↦ ?_⟩
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1,
      M + t • (M' - M) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) :=
    fun t ht ↦ hCK (hCc.add_smul_sub_mem hM hM' ht)
  refine integral_abs_famDens_sub_le_of_segment hS ν hseg (Λ := max Λ 0) fun t ht ↦ ?_
  have hmem := hCc.add_smul_sub_mem hM hM' ht
  have h := hΛ ⟨M + t • (M' - M), hCK hmem⟩ hmem
  rw [relintChart_symm_apply] at h
  simp only [Real.norm_eq_abs, abs_norm] at h
  exact h.trans (le_max_left _ _)

omit [IsProbabilityMeasure ν] in
/-- **The response of a data density is Lipschitz from `L¹(ν)` to the sup norm**:
`‖E_{dν}S − E_{d'ν}S‖ ≤ B ∫ |d − d'| dν` when `|S_j| ≤ B`. -/
theorem norm_density_response_sub_le {B : ℝ} (hB : ∀ j x, |S j x| ≤ B) {d d' : X → ℝ}
    (hd : Integrable d ν) (hd' : Integrable d' ν) :
    ‖(fun j ↦ ∫ x, S j x * d' x ∂ν) - fun j ↦ ∫ x, S j x * d x ∂ν‖ ≤
      B * ∫ x, |d' x - d x| ∂ν := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary J) (Classical.arbitrary X))
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j ↦ ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  have hj : ∀ f : X → ℝ, Integrable f ν → Integrable (fun x ↦ S j x * f x) ν := fun f hf ↦
    hf.bdd_mul (hS j).1.aestronglyMeasurable (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]
      exact hB j x)
  rw [← integral_sub (hj d' hd') (hj d hd)]
  have hI : Integrable (fun x ↦ S j x * d' x - S j x * d x) ν := (hj d' hd').sub (hj d hd)
  calc |∫ x, S j x * d' x - S j x * d x ∂ν|
      ≤ ∫ x, |S j x * d' x - S j x * d x| ∂ν := by
        have := norm_integral_le_integral_norm (μ := ν)
          (fun x ↦ S j x * d' x - S j x * d x)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∫ x, B * |d' x - d x| ∂ν := by
        refine integral_mono hI.abs ((hd'.sub hd).abs.const_mul B) fun x ↦ ?_
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_right (hB j x) (abs_nonneg _)
    _ = B * ∫ x, |d' x - d x| ∂ν := integral_const_mul _ _

/-- **The reconstruction of data laws is total-variation Lipschitz on compact convex interior
response sets**: for data densities `d, d'` whose responses lie in `C`,
`∫ |q_{M_{d'}} − q_{M_d}| dν ≤ L B ∫ |d' − d| dν`. -/
theorem integral_abs_famDens_density_sub_le {C : Set (J → ℝ)} (hC : IsCompact C)
    (hCc : Convex ℝ C) (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
    {B : ℝ} (hB : ∀ j x, |S j x| ≤ B) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ d d' : X → ℝ, Integrable d ν → Integrable d' ν →
      (fun j ↦ ∫ x, S j x * d x ∂ν) ∈ C → (fun j ↦ ∫ x, S j x * d' x ∂ν) ∈ C →
      ∫ x, |famDens S ν (θr (fun j ↦ ∫ x, S j x * d' x ∂ν)) x -
        famDens S ν (θr (fun j ↦ ∫ x, S j x * d x ∂ν)) x| ∂ν ≤
        L * B * ∫ x, |d' x - d x| ∂ν := by
  obtain ⟨L, hL0, hL⟩ := exists_tv_lipschitz_of_isCompact_convex hS ν hC hCc hCK
  refine ⟨L, hL0, fun d d' hd hd' hMd hMd' ↦ ?_⟩
  calc ∫ x, |famDens S ν (θr (fun j ↦ ∫ x, S j x * d' x ∂ν)) x -
        famDens S ν (θr (fun j ↦ ∫ x, S j x * d x ∂ν)) x| ∂ν
      ≤ L * ‖(fun j ↦ ∫ x, S j x * d' x ∂ν) - fun j ↦ ∫ x, S j x * d x ∂ν‖ := hL _ hMd _ hMd'
    _ ≤ L * (B * ∫ x, |d' x - d x| ∂ν) :=
        mul_le_mul_of_nonneg_left (norm_density_response_sub_le hS ν hB hd hd') hL0
    _ = L * B * ∫ x, |d' x - d x| ∂ν := by ring

/-- **The reconstruction is a total-variation Lipschitz retraction of distribution space onto the
family**: it fixes every family member, its derivative `u ↦ Π(M) ℓ_{M,u}` has zero mass and
transmits exactly the moment perturbation `u` (a projection onto the tangent scores along the
moment-invisible perturbations), and it is total-variation Lipschitz on every compact convex
interior response set. -/
theorem reconstruction_retraction :
    (∀ θ : J → ℝ, responseProjection hS ν (fun i ↦ ∫ x, S i x ∂(Pfam θ)) = Pfam θ) ∧
      (∀ M : J → ℝ, M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) → ∀ u : 𝕍,
        (∫ x, responseScore hS ν M u x ∂(Pfam (θr M))) = 0 ∧
          respCov hS ν M (responseScore hS ν M u) = u) ∧
      (∀ C : Set (J → ℝ), IsCompact C → Convex ℝ C →
        C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) →
        ∃ L : ℝ, 0 ≤ L ∧ ∀ M ∈ C, ∀ M' ∈ C,
          ∫ x, |famDens S ν (θr M') x - famDens S ν (θr M) x| ∂ν ≤ L * ‖M' - M‖) :=
  ⟨fun θ ↦ responseProjection_mean_familyMeasure hS ν θ,
    fun _ hrel u ↦ ⟨integral_responseScore hS ν hrel u, respCov_responseScore hS ν u⟩,
    fun _ hC hCc hCK ↦ exists_tv_lipschitz_of_isCompact_convex hS ν hC hCc hCK⟩

end Compact

end Laplace.Multi
