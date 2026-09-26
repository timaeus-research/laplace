/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.AnalyticChart

/-!
# The `L¹` jets of the reconstruction are the pointwise jets: the Bell tower

* `contDiffOn_iteratedDeriv_of_isOpen`, `hasDerivAt_iteratedDeriv_of_contDiffOn`: iterated
  derivatives of a `C^∞` map on an open set are `C^∞` and differentiable there;
* `contDiff_famDens_apply`, `contDiffOn_famDens_atlas`: for every `x` the pointwise density
  `s ↦ q_{M_s}(x)` is `C^∞` on the interior atlas domain;
* **`coeFn_iteratedDeriv_reconstructionL1_atlas`**: for every `k` and every interior atlas
  point, `p^{(k)}(s) = [x ↦ ∂_s^k q_{M_s}(x)]` — the `L¹` jets of the reconstruction curve are the
  pointwise jets of the density (induction on `k` through the `L¹`-pointwise principle);
* `atlasJet`, `atlasBell`: the pointwise jet `∂_s^k q_s` and the Bell coefficient
  `B_k = q_s⁻¹ ∂_s^k q_s`; **`atlasBell_succ`**: the structural tower `B_{k+1} = ∂_s B_k + ℓ_s B_k`
  on the unit interval (`q' = q ℓ`); `atlasBell_one` (`B_1 = ℓ_s`);
* `integral_atlasJet`, `integral_stat_mul_atlasJet`: every pointwise jet of order `≥ 2` has zero
  mass and zero feature moments (the invisible tower, pointwise).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Laplace.Multi

section Iterated

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F} {U : Set ℝ}

/-- Iterated derivatives of a `C^∞` map on an open set are `C^∞` there. -/
theorem contDiffOn_iteratedDeriv_of_isOpen (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (k : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv k f) U := by
  induction k generalizing f with
  | zero => simpa [iteratedDeriv_zero] using hf
  | succ k ih =>
    rw [iteratedDeriv_succ']
    exact ih ((contDiffOn_infty_iff_deriv_of_isOpen hU).1 hf).2

/-- Iterated derivatives of a `C^∞` map on an open set are differentiable there, with derivative
the next iterated derivative. -/
theorem hasDerivAt_iteratedDeriv_of_contDiffOn (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (k : ℕ)
    {x : ℝ} (hx : x ∈ U) : HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := by
  rw [iteratedDeriv_succ]
  exact (((contDiffOn_iteratedDeriv_of_isOpen hU hf k).differentiableOn (by simp)).differentiableAt
    (hU.mem_nhds hx)).hasDerivAt

end Iterated

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

omit [Nonempty J] in
/-- The pointwise density is `C^∞` in the natural parameter. -/
theorem contDiff_famDens_apply (x : X) : ContDiff ℝ ∞ (fun θ : J → ℝ ↦ famDens S ν θ x) := by
  have e : (fun θ : J → ℝ ↦ famDens S ν θ x) =
      fun θ ↦ Real.exp (-∑ j, θ j * S j x) / famZ S ν θ := by
    funext θ
    rfl
  rw [e]
  refine ContDiff.div ?_ (contDiff_famZ hS ν) fun θ ↦ (famZ_pos hS ν θ).ne'
  exact (ContDiff.sum fun j _ ↦ (contDiff_apply ℝ ℝ j).mul contDiff_const).neg.exp

section Jets

variable {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
include hfin

/-- The reconstruction curve along the atlas. -/
local notation "p" => fun s ↦ reconstructionL1 hS ν (atlasPath S ν M s)

/-- The pointwise density `s ↦ q_{M_s}(x)` is `C^∞` on the interior atlas domain. -/
theorem contDiffOn_famDens_atlas (x : X) :
    ContDiffOn ℝ ∞ (fun t ↦ famDens S ν (atlasTheta hS ν M t) x) (atlasDomain S ν M) :=
  (contDiff_famDens_apply hS ν x).comp_contDiffOn
    ((dirSpan ν (fun _ ↦ (1 : ℝ)) S).subtypeL.contDiff.comp_contDiffOn
      (contDiffOn_atlasTheta hS ν hfin))

/-- **The `L¹` jets are the pointwise jets**: `p^{(k)}(s) = [x ↦ ∂_s^k q_{M_s}(x)]` at every
interior atlas point. -/
theorem coeFn_iteratedDeriv_reconstructionL1_atlas (k : ℕ) {s : ℝ}
    (hs : s ∈ atlasDomain S ν M) :
    ((iteratedDeriv k p s : X →₁[ν] ℝ) : X → ℝ) =ᵐ[ν]
      fun x ↦ iteratedDeriv k (fun t ↦ famDens S ν (atlasTheta hS ν M t) x) s := by
  have hU := isOpen_atlas_interior hS ν hfin
  induction k generalizing s with
  | zero =>
    simp only [iteratedDeriv_zero]
    exact Integrable.coeFn_toL1 _
  | succ k ih =>
    refine coeFn_hasDerivAt_L1_ae ν (hasDerivAt_iteratedDeriv_of_contDiffOn hU
      (contDiffOn_reconstructionL1_atlas hS ν hfin) k hs)
      (φ := fun t x ↦ iteratedDeriv k (fun t ↦ famDens S ν (atlasTheta hS ν M t) x) t) ?_
      fun x ↦ ?_
    · filter_upwards [hU.mem_nhds hs] with t ht
      exact ih ht
    · exact hasDerivAt_iteratedDeriv_of_contDiffOn hU (contDiffOn_famDens_atlas hS ν hfin x) k hs

/-- The pointwise jets are integrable. -/
theorem integrable_iteratedDeriv_famDens_atlas (k : ℕ) {s : ℝ} (hs : s ∈ atlasDomain S ν M) :
    Integrable (fun x ↦ iteratedDeriv k (fun t ↦ famDens S ν (atlasTheta hS ν M t) x) s) ν :=
  (L1.integrable_coeFn _).congr (coeFn_iteratedDeriv_reconstructionL1_atlas hS ν hfin k hs)

theorem iteratedDeriv_reconstructionL1_atlas_eq_toL1 (k : ℕ) {s : ℝ} (hs : s ∈ atlasDomain S ν M) :
    iteratedDeriv k p s = (integrable_iteratedDeriv_famDens_atlas hS ν hfin k hs).toL1 _ :=
  Lp.ext ((coeFn_iteratedDeriv_reconstructionL1_atlas hS ν hfin k hs).trans
    (Integrable.coeFn_toL1 _).symm)

omit hfin in
variable (M) in
/-- The pointwise jet `∂_s^k q_{M_s}(x)`. -/
noncomputable def atlasJet (k : ℕ) (s : ℝ) (x : X) : ℝ :=
  iteratedDeriv k (fun t ↦ famDens S ν (atlasTheta hS ν M t) x) s

omit hfin in
variable (M) in
/-- The Bell coefficient `B_k = q_s⁻¹ ∂_s^k q_s`. -/
noncomputable def atlasBell (k : ℕ) (s : ℝ) (x : X) : ℝ :=
  atlasJet hS ν M k s x / famDens S ν (atlasTheta hS ν M s) x

omit hfin in
theorem atlasJet_zero (s : ℝ) (x : X) :
    atlasJet hS ν M 0 s x = famDens S ν (atlasTheta hS ν M s) x := by
  unfold atlasJet
  rw [iteratedDeriv_zero]

omit hfin in
theorem atlasBell_zero (s : ℝ) (x : X) : atlasBell hS ν M 0 s x = 1 := by
  unfold atlasBell
  rw [atlasJet_zero, div_self (famDens_pos hS ν _ x).ne']

theorem hasDerivAt_atlasJet (k : ℕ) {s : ℝ} (hs : s ∈ atlasDomain S ν M) (x : X) :
    HasDerivAt (fun t ↦ atlasJet hS ν M k t x) (atlasJet hS ν M (k + 1) s x) s :=
  hasDerivAt_iteratedDeriv_of_contDiffOn (isOpen_atlas_interior hS ν hfin)
    (contDiffOn_famDens_atlas hS ν hfin x) k hs

/-- **The invisible tower, pointwise**: jets of order `≥ 2` have zero mass. -/
theorem integral_atlasJet {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hs : s ∈ atlasDomain S ν M) :
    ∫ x, atlasJet hS ν M k s x ∂ν = 0 := by
  have h := (invisible_tower hS ν hfin hk hs).2
  rw [iteratedDerivWithin_of_isOpen (isOpen_atlas_interior hS ν hfin) hs,
    iteratedDeriv_reconstructionL1_atlas_eq_toL1 hS ν hfin k hs, ← L1.integral_eq,
    L1.integral_eq_integral] at h
  exact (integral_congr_ae
    (Integrable.coeFn_toL1 (integrable_iteratedDeriv_famDens_atlas hS ν hfin k hs)).symm).trans h

/-- **The invisible tower, pointwise**: jets of order `≥ 2` have zero feature moments. -/
theorem integral_stat_mul_atlasJet {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hs : s ∈ atlasDomain S ν M)
    (j : J) : ∫ x, S j x * atlasJet hS ν M k s x ∂ν = 0 := by
  have h := congrFun (invisible_tower hS ν hfin hk hs).1 j
  rw [iteratedDerivWithin_of_isOpen (isOpen_atlas_interior hS ν hfin) hs,
    iteratedDeriv_reconstructionL1_atlas_eq_toL1 hS ν hfin k hs, momentL1_apply,
    Pi.zero_apply] at h
  refine (integral_congr_ae ?_).trans h
  filter_upwards [Integrable.coeFn_toL1 (integrable_iteratedDeriv_famDens_atlas hS ν hfin k hs)]
    with x hx
  rw [hx]
  rfl

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- `B_1 = ℓ_s` on the unit interval. -/
theorem atlasBell_one {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : X) :
    atlasBell hS ν M 1 s x = atlasScore hS ν hfin s x := by
  unfold atlasBell atlasJet
  rw [iteratedDeriv_one, (hasDerivAt_famDens_atlas hS ν hfin hrel hs0 hs1 x).deriv,
    mul_div_cancel_left₀ _ (famDens_pos hS ν _ x).ne']
  rfl

/-- **The Bell tower**: `B_{k+1} = ∂_s B_k + ℓ_s B_k` on the unit interval (from `q' = q ℓ`). -/
theorem atlasBell_succ (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : X) :
    atlasBell hS ν M (k + 1) s x =
      deriv (fun t ↦ atlasBell hS ν M k t x) s +
        atlasScore hS ν hfin s x * atlasBell hS ν M k s x := by
  have hsD : s ∈ atlasDomain S ν M := atlas_mem_intrinsicInterior' hS ν hfin hrel hs0 hs1
  have hq := hasDerivAt_famDens_atlas hS ν hfin hrel hs0 hs1 x
  have hJ := hasDerivAt_atlasJet hS ν hfin k hsD x
  have hq0 := (famDens_pos hS ν (atlasTheta hS ν M s) x).ne'
  have hB : HasDerivAt (fun t ↦ atlasBell hS ν M k t x)
      ((atlasJet hS ν M (k + 1) s x * famDens S ν (atlasTheta hS ν M s) x -
        atlasJet hS ν M k s x * (famDens S ν (atlasTheta hS ν M s) x *
          (dotJ (atlasVel hS ν hfin s) (atlasPath S ν M s) -
            dirLoss S (atlasVel hS ν hfin s) x))) / famDens S ν (atlasTheta hS ν M s) x ^ 2) s :=
    hJ.div hq hq0
  rw [hB.deriv]
  unfold atlasBell atlasScore
  field_simp
  ring

end Jets

end Laplace.Multi
