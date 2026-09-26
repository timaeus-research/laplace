/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.InvisibleTower

/-!
# The jets of the reconstruction along the atlas in `L¹`, and the `L¹` Taylor expansion

* `obsL1`: pairing with a bounded observable as a continuous linear functional on `L¹(ν)`;
  `L1_ext_of_forall_integral_mul`: two `L¹` elements with the same pairings against all bounded
  observables are equal (duality);
* `iteratedDeriv_one_reconstructionL1_atlas`: `p'(s) = [q_{M_s} ℓ_{M_s, M−m₀}]` on the interior
  atlas domain; `iteratedDeriv_two_reconstructionL1_atlas`: `p''(s) = [atlasHess_s] =
  [q_{M_s} N_{M_s}(ℓ_s²)]` on `(0,1)` — the density-acceleration theorem lifted to `L¹`, via duality
  and the observable-level second derivative `b_F`;
* `reconstructionL1_taylor_remainder`: the Taylor expansion of `p` at the featureless law with the
  Lagrange bound `‖p(s) − Σ_{k≤n} s^k/k! p^{(k)}(0)‖₁ ≤ C s^{n+1}/n!`, and
  `obsResponse_atlas_taylor`: the same expansion for the response of every bounded observable at
  once, with error `‖F‖∞ · C s^{n+1}/n!` — the **featureless expansion** of the response map.
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

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

section Pairing

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- A bounded observable times an `L¹` function is integrable. -/
theorem integrable_bdd_mul_L1 {F : X → ℝ} (hF : Bdd F) (d : X →₁[ν] ℝ) :
    Integrable (fun x ↦ F x * d x) ν :=
  (L1.integrable_coeFn d).bdd_mul hF.1.aestronglyMeasurable
    (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hF.2.choose_spec x)

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The pairing `d ↦ ∫ F d dν` with a bounded observable, as a linear map on `L¹`. -/
noncomputable def obsLin {F : X → ℝ} (hF : Bdd F) : (X →₁[ν] ℝ) →ₗ[ℝ] ℝ where
  toFun d := ∫ x, F x * d x ∂ν
  map_add' d e := by
    change ∫ x, F x * (d + e) x ∂ν = (∫ x, F x * d x ∂ν) + ∫ x, F x * e x ∂ν
    rw [← integral_add (integrable_bdd_mul_L1 ν hF d) (integrable_bdd_mul_L1 ν hF e)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add d e] with x hx
    rw [hx, Pi.add_apply]
    ring
  map_smul' c d := by
    change ∫ x, F x * (c • d) x ∂ν = c * ∫ x, F x * d x ∂ν
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c d] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul]
    ring

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The pairing is bounded by the sup norm. -/
theorem abs_obsLin_le {F : X → ℝ} (hF : Bdd F) {BF : ℝ} (hBF : ∀ x, |F x| ≤ BF) (d : X →₁[ν] ℝ) :
    |obsLin ν hF d| ≤ BF * ‖d‖ := by
  change |∫ x, F x * d x ∂ν| ≤ BF * ‖d‖
  rw [L1.norm_eq_integral_norm, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((L1.integrable_coeFn d).norm.const_mul BF)
    (Eventually.of_forall fun x ↦ ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hBF x) (norm_nonneg _)

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The pairing `d ↦ ∫ F d dν` with a bounded observable, as a continuous linear functional. -/
noncomputable def obsL1 {F : X → ℝ} (hF : Bdd F) : (X →₁[ν] ℝ) →L[ℝ] ℝ :=
  (obsLin ν hF).mkContinuousOfExistsBound ⟨hF.2.choose, fun d ↦ by
    rw [Real.norm_eq_abs]
    exact abs_obsLin_le ν hF hF.2.choose_spec d⟩

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem obsL1_apply {F : X → ℝ} (hF : Bdd F) (d : X →₁[ν] ℝ) :
    obsL1 ν hF d = ∫ x, F x * d x ∂ν := rfl

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
theorem abs_obsL1_le {F : X → ℝ} (hF : Bdd F) {BF : ℝ} (hBF : ∀ x, |F x| ≤ BF) (d : X →₁[ν] ℝ) :
    |obsL1 ν hF d| ≤ BF * ‖d‖ :=
  abs_obsLin_le ν hF hBF d

/-- The pairing of a bounded observable with the reconstruction is its response. -/
theorem obsL1_reconstructionL1 {F : X → ℝ} (hF : Bdd F) (M : J → ℝ) :
    obsL1 ν hF (reconstructionL1 hS ν M) = obsResponse hS ν F M := by
  rw [obsL1_apply]
  unfold obsResponse
  rw [integral_famDens_mul hS ν]
  refine integral_congr_ae ?_
  filter_upwards [Integrable.coeFn_toL1 (integrable_famDens hS ν (θr M))] with x hx
  unfold reconstructionL1
  rw [hx, mul_comm]

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- **Duality**: an `L¹` element killed by every bounded observable is zero. -/
theorem L1_eq_zero_of_forall_integral_mul (f : X →₁[ν] ℝ)
    (h : ∀ F : X → ℝ, Bdd F → ∫ x, F x * f x ∂ν = 0) : f = 0 := by
  have hm : Measurable f := (Lp.stronglyMeasurable f).measurable
  obtain ⟨F, hF⟩ : ∃ F : X → ℝ, F = fun x ↦ if 0 ≤ f x then 1 else -1 := ⟨_, rfl⟩
  have hFb : Bdd F := ⟨by
      rw [hF]
      exact Measurable.ite (measurableSet_le measurable_const hm) measurable_const
        measurable_const, 1, fun x ↦ by
      rw [hF]
      beta_reduce
      split_ifs <;> simp⟩
  have h1 : ∫ x, F x * f x ∂ν = ∫ x, |f x| ∂ν := by
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    rw [hF]
    beta_reduce
    split_ifs with hx
    · rw [one_mul, abs_of_nonneg hx]
    · rw [neg_one_mul, abs_of_neg (not_le.1 hx)]
  have h2 : ‖f‖ = 0 := by
    rw [L1.norm_eq_integral_norm]
    simp only [Real.norm_eq_abs]
    rw [← h1]
    exact h F hFb
  exact norm_eq_zero.1 h2

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- **Duality**: two `L¹` elements with the same pairings against all bounded observables are
equal. -/
theorem L1_ext_of_forall_integral_mul (f g : X →₁[ν] ℝ)
    (h : ∀ F : X → ℝ, Bdd F → ∫ x, F x * f x ∂ν = ∫ x, F x * g x ∂ν) : f = g := by
  rw [← sub_eq_zero]
  refine L1_eq_zero_of_forall_integral_mul ν _ fun F hF ↦ ?_
  have e : ∫ x, F x * (f - g) x ∂ν = (∫ x, F x * f x ∂ν) - ∫ x, F x * g x ∂ν := by
    rw [← integral_sub (integrable_bdd_mul_L1 ν hF f) (integrable_bdd_mul_L1 ν hF g)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub f g] with x hx
    rw [hx, Pi.sub_apply]
    ring
  rw [e, h F hF, sub_self]

end Pairing

section Jets

variable {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
include hfin

/-- The reconstruction curve along the atlas. -/
local notation "p" => fun s ↦ reconstructionL1 hS ν (atlasPath S ν M s)

/-- The reconstruction is differentiable along the atlas on the interior domain, with derivative
`[q_{M_s} ℓ_{M_s, M − m₀}]`. -/
theorem hasDerivAt_reconstructionL1_atlas {s : ℝ} (hs : s ∈ atlasDomain S ν M) :
    HasDerivAt p (reconstructionDeriv hS ν (atlasPath S ν M s) (atlasInc hS ν hfin)) s := by
  have hcoe : ∀ t, m₀ + (dirProjL S ν (atlasPath S ν M t - m₀) : J → ℝ) = atlasPath S ν M t :=
    fun t ↦ by rw [dirProjL_of_mem ν (atlasPath_sub_mem_dirSpan hS ν hfin t), add_sub_cancel]
  have hγ : HasDerivAt (fun t ↦ dirProjL S ν (atlasPath S ν M t - m₀)) (atlasInc hS ν hfin) s := by
    have h := (dirProjL S ν).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_atlasPath ν (S := S) (M := M) s).sub_const m₀)
    refine h.congr_deriv (Subtype.ext ?_)
    rw [atlasInc_coe]
    exact dirProjL_of_mem ν (sub_mem_dirSpan_of_genRate_ne_top hS ν hfin)
  have h := hasDerivAt_reconstructionL1_curve hS ν (M := m₀)
    (γ := fun t ↦ dirProjL S ν (atlasPath S ν M t - m₀)) (γ' := fun _ ↦ atlasInc hS ν hfin)
    (t := s) hγ (by rw [hcoe]; exact hs)
  simp only [hcoe] at h
  exact h

/-- **The first jet**: `p'(s) = [q_{M_s} ℓ_{M_s, M−m₀}]` on the interior atlas domain. -/
theorem iteratedDeriv_one_reconstructionL1_atlas {s : ℝ} (hs : s ∈ atlasDomain S ν M) :
    iteratedDeriv 1 p s = reconstructionDeriv hS ν (atlasPath S ν M s) (atlasInc hS ν hfin) := by
  rw [iteratedDeriv_one]
  exact (hasDerivAt_reconstructionL1_atlas hS ν hfin hs).deriv

/-- Continuous linear functionals commute with the iterated derivatives of the reconstruction
curve on the interior atlas domain. -/
theorem clm_iteratedDeriv_reconstructionL1_atlas {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : (X →₁[ν] ℝ) →L[ℝ] F) (k : ℕ) {s : ℝ} (hs : s ∈ atlasDomain S ν M) :
    L (iteratedDeriv k p s) =
      iteratedDeriv k (fun s ↦ L (reconstructionL1 hS ν (atlasPath S ν M s))) s := by
  have hU := isOpen_atlas_interior hS ν hfin
  rw [← iteratedDerivWithin_of_isOpen hU hs, ← iteratedDerivWithin_of_isOpen hU hs]
  exact clm_iteratedDerivWithin_reconstructionL1_atlas hS ν hfin L k hs

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- **The pairing of the density acceleration with an observable is the bias form**:
`∫ F · atlasHess_s dν = b_{F,M_s}(M − m₀, M − m₀)`. -/
theorem integral_mul_atlasHess_eq_biasForm {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {F : X → ℝ}
    (hF : Bdd F) :
    ∫ x, F x * atlasHess hS ν hfin hrel hs0 hs1 x ∂ν =
      biasForm hS ν (atlasPath S ν M s) hF (M - m₀) (M - m₀) := by
  have hrels := atlas_mem_intrinsicInterior' hS ν hfin hrel hs0 hs1
  have hQ := isProbabilityMeasure_family_responseTheta hS ν (M := atlasPath S ν M s)
  have e : dirProj S ν (M - m₀) = ⟨M - m₀, sub_mem_dirSpan_of_genRate_ne_top hS ν hfin⟩ :=
    dirProj_coe S ν ⟨M - m₀, sub_mem_dirSpan_of_genRate_ne_top hS ν hfin⟩
  rw [biasForm_apply, e]
  have hb := bdd_atlasScore_sq hS ν hfin (s := s)
  have e1 : ∫ x, F x * atlasHess hS ν hfin hrel hs0 hs1 x ∂ν =
      ∫ x, F x * normalProj hS ν (atlasPath S ν M s) hb x ∂(Pfam (θr (atlasPath S ν M s))) := by
    rw [integral_famDens_mul hS ν]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [atlasHess_eq_normalProj hS ν hfin hrel hs0 hs1 x]
    change F x * (famDens S ν (θr (atlasPath S ν M s)) x * _) = _
    ring
  rw [e1, integral_mul_normalProj_comm hS ν hrels hF hb]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [sq]
  rfl

/-- **The second jet**: `p''(s) = [atlasHess_s] = [q_{M_s} N_{M_s}(ℓ_s²)]` on `(0, 1)` — the
density-acceleration theorem in `L¹`. -/
theorem iteratedDeriv_two_reconstructionL1_atlas {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    iteratedDeriv 2 p s =
      ((integrable_famDens_mul_of_bdd hS ν (M := atlasPath S ν M s)
          (bdd_normalProj hS ν (bdd_atlasScore_sq hS ν hfin (s := s)))).congr
        (Eventually.of_forall fun x ↦
          (atlasHess_eq_normalProj hS ν hfin hrel hs.1.le hs.2.le x).symm)).toL1
        (atlasHess hS ν hfin hrel hs.1.le hs.2.le) := by
  have hsD : s ∈ atlasDomain S ν M := Ioo_subset_atlas_interior hS ν hfin hs
  refine L1_ext_of_forall_integral_mul ν _ _ fun F hF ↦ ?_
  have h1 : ∫ x, F x * (iteratedDeriv 2 p s) x ∂ν = iteratedDeriv 2
      (fun s ↦ obsResponse hS ν F (atlasPath S ν M s)) s := by
    have e : (fun t ↦ obsL1 ν hF (reconstructionL1 hS ν (atlasPath S ν M t))) =
        fun t ↦ obsResponse hS ν F (atlasPath S ν M t) :=
      funext fun t ↦ obsL1_reconstructionL1 hS ν hF _
    rw [← obsL1_apply ν hF, clm_iteratedDeriv_reconstructionL1_atlas hS ν hfin _ 2 hsD, e]
  have h2 : iteratedDeriv 2 (fun s ↦ obsResponse hS ν F (atlasPath S ν M s)) s =
      biasForm hS ν (atlasPath S ν M s) hF (M - m₀) (M - m₀) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (hasDerivAt_deriv_obsResponse_atlas hS ν hfin hs hF).deriv
  rw [h1, h2, ← integral_mul_atlasHess_eq_biasForm hS ν hfin hrel hs.1.le hs.2.le hF]
  refine integral_congr_ae ?_
  filter_upwards [Integrable.coeFn_toL1 ((integrable_famDens_mul_of_bdd hS ν
    (M := atlasPath S ν M s) (bdd_normalProj hS ν (bdd_atlasScore_sq hS ν hfin (s := s)))).congr
      (Eventually.of_forall fun x ↦
      (atlasHess_eq_normalProj hS ν hfin hrel hs.1.le hs.2.le x).symm))] with x hx
  rw [hx]

end Jets

section Taylor

variable {M : J → ℝ} (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- The reconstruction curve along the atlas. -/
local notation "p" => fun s ↦ reconstructionL1 hS ν (atlasPath S ν M s)

/-- The unit interval lies in the interior atlas domain when the endpoint is interior. -/
theorem Icc_subset_atlasDomain : Icc (0 : ℝ) 1 ⊆ atlasDomain S ν M := fun _ hs ↦
  atlas_mem_intrinsicInterior' hS ν (genRate_ne_top_of_mem_intrinsicInterior hS ν hrel) hrel
    hs.1 hs.2

/-- The reconstruction curve is `C^∞` on the unit interval. -/
theorem contDiffOn_reconstructionL1_atlas_Icc : ContDiffOn ℝ ∞ p (Icc (0 : ℝ) 1) :=
  (contDiffOn_reconstructionL1_atlas hS ν
    (genRate_ne_top_of_mem_intrinsicInterior hS ν hrel)).mono (Icc_subset_atlasDomain hS ν hrel)

/-- The reconstruction curve is smooth at the featureless law. -/
theorem contDiffAt_reconstructionL1_atlas_zero (n : ℕ) : ContDiffAt ℝ n p 0 :=
  ((contDiffOn_reconstructionL1_atlas hS ν
    (genRate_ne_top_of_mem_intrinsicInterior hS ν hrel)).contDiffAt
    ((isOpen_atlas_interior hS ν (genRate_ne_top_of_mem_intrinsicInterior hS ν hrel)).mem_nhds
      (Icc_subset_atlasDomain hS ν hrel (left_mem_Icc.2 zero_le_one)))).of_le
    (by exact_mod_cast natCast_le_infty n)

/-- The Taylor polynomial of the reconstruction at the featureless law, in terms of the ordinary
iterated derivatives. -/
theorem taylorWithinEval_reconstructionL1_atlas (n : ℕ) (s : ℝ) :
    taylorWithinEval p n (Icc (0 : ℝ) 1) 0 s =
      ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹ * s ^ k) • iteratedDeriv k p 0 := by
  rw [taylor_within_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [sub_zero, iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc_zero_one
    (contDiffAt_reconstructionL1_atlas_zero hS ν hrel k) (left_mem_Icc.2 zero_le_one)]

/-- **The `L¹` Taylor expansion of the reconstruction at the featureless law**: there is `C` with
`‖p(s) − Σ_{k≤n} s^k/k! p^{(k)}(0)‖₁ ≤ C s^{n+1}/n!` for all `s ∈ [0, 1]`. -/
theorem reconstructionL1_taylor_remainder (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0 : ℝ) 1,
    ‖reconstructionL1 hS ν (atlasPath S ν M s) -
        ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹ * s ^ k) • iteratedDeriv k p 0‖ ≤
      C * s ^ (n + 1) / n.factorial := by
  have hf : ContDiffOn ℝ (n + 1 : ℕ) p (Icc (0 : ℝ) 1) :=
    (contDiffOn_reconstructionL1_atlas_Icc hS ν hrel).of_le (by exact_mod_cast natCast_le_infty _)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuousOn_iteratedDerivWithin le_rfl uniqueDiffOn_Icc_zero_one)
  refine ⟨max C 0, le_max_right _ _, fun s hs ↦ ?_⟩
  rw [← taylorWithinEval_reconstructionL1_atlas hS ν hrel n s]
  have h := taylor_mean_remainder_bound (C := max C 0) zero_le_one hf hs
    (fun y hy ↦ (hC y hy).trans (le_max_left C 0))
  rwa [sub_zero] at h

/-- **The featureless expansion of the response map**: for every bounded observable `F`,
`|E_{Q_{M_s}}F − Σ_{k≤n} s^k/k! ∫ F p^{(k)}(0) dν| ≤ ‖F‖∞ · C s^{n+1}/n!` on `[0, 1]`, with the
same constant `C` for all observables. -/
theorem obsResponse_atlas_taylor (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ {F : X → ℝ}, Bdd F → ∀ {BF : ℝ}, (∀ x, |F x| ≤ BF) →
      |obsResponse hS ν F (atlasPath S ν M s) - ∑ k ∈ Finset.range (n + 1),
          ((k.factorial : ℝ)⁻¹ * s ^ k) * ∫ x, F x * (iteratedDeriv k p 0) x ∂ν| ≤
        BF * (C * s ^ (n + 1) / n.factorial) := by
  obtain ⟨C, hC0, hC⟩ := reconstructionL1_taylor_remainder hS ν hrel n
  refine ⟨C, hC0, fun s hs F hF BF hBF ↦ ?_⟩
  have e : obsResponse hS ν F (atlasPath S ν M s) - ∑ k ∈ Finset.range (n + 1),
      ((k.factorial : ℝ)⁻¹ * s ^ k) * ∫ x, F x * (iteratedDeriv k p 0) x ∂ν =
      obsL1 ν hF (reconstructionL1 hS ν (atlasPath S ν M s) -
        ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹ * s ^ k) • iteratedDeriv k p 0) := by
    rw [map_sub, map_sum, obsL1_reconstructionL1 hS ν hF]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_smul, smul_eq_mul, obsL1_apply]
  rw [e]
  exact (abs_obsL1_le ν hF hBF _).trans (mul_le_mul_of_nonneg_left (hC s hs)
    ((abs_nonneg _).trans (hBF (Classical.arbitrary X))))

end Taylor

end Laplace.Multi
