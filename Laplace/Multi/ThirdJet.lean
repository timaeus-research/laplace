/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.L1PointwiseDeriv

/-!
# The third jet of the reconstruction along the atlas: projection after differentiation

* `normalProj_eq_self_of_invisible`: an observable with zero mean and zero feature moments under
  `Q_M` is its own normal part; `famDens_mul_normalProj_of_invisible`: a signed density `q_M F`
  with zero mass and zero feature moments equals `q_M N_M F` pointwise;
* `normalProj_add`, `normalProj_const`, `normalProj_const_mul`: linearity of the normal projection;
* `contDiffOn_atlasVel`: the velocity `s ↦ β_s` of the natural coordinates is `C^∞` on the
  interior atlas domain, so `β' = atlasVelD` and `β'' = atlasVelDD` exist;
  `hasDerivAt_atlasScore_of_mem`, `hasDerivAt_atlasScoreD_of_mem`: the score derivatives
  `ℓ' = ⟨β', M_s⟩ + ⟨β, M − m₀⟩ − ⟨β', S⟩` and `ℓ'' = ⟨β'', M_s⟩ + 2⟨β', M − m₀⟩ − ⟨β'', S⟩`;
* `hasDerivAt_atlasHess'`: `q''' = q (ℓ³ + 3ℓℓ' + ℓ'')` pointwise along the atlas;
* `iteratedDeriv_three_reconstructionL1_atlas`: **the third jet**
  `p'''(s) = [q_s (ℓ³ + 3ℓℓ' + ℓ'')]` in `L¹`, by the `L¹`-pointwise principle;
* `iteratedDeriv_three_reconstructionL1_atlas_cubic`: **projection after differentiation**,
  `p'''(s) = [q_s N_s(ℓ_s³ − 3 ℓ_s r_s)]` where `r_s = ⟨β'_s, S − M_s⟩` is the bending score
  (`ℓ' = −c − r`): the invisible tower forces `q H₃ = q N H₃`, and `N_s` kills the affine part
  `ℓ''` and the multiple `c ℓ` of the tangent score;
* `iteratedDeriv_three_obsResponse_atlas`: the third derivative of every observable response along
  the atlas is `E_{Q_s}[N_s F · (ℓ_s³ − 3 ℓ_s r_s)]`.
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

/-- The chart derivative as a linear equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

section Invisible

variable {M : J → ℝ}

theorem responseScore_zero (x : X) : responseScore hS ν M 0 x = 0 := by
  unfold responseScore
  rw [map_zero, Submodule.coe_zero, dotJ_zero_left, dirLoss_zero, sub_zero]

/-- An observable with zero mean and zero feature moments has zero covariance vector. -/
theorem respCov_eq_zero_of_invisible {F : X → ℝ} (h0 : ∫ x, F x ∂(Pfam (θr M)) = 0)
    (hj : ∀ j, ∫ x, S j x * F x ∂(Pfam (θr M)) = 0) : respCov hS ν M F = 0 := by
  funext j
  simp only [respCov, lawCov, hj j, h0, mul_zero, sub_zero, Pi.zero_apply]

/-- **Invisible observables are their own normal parts**: zero mean and zero feature moments
under `Q_M` give `N_M F = F`. -/
theorem normalProj_eq_self_of_invisible {F : X → ℝ} (hF : Bdd F)
    (h0 : ∫ x, F x ∂(Pfam (θr M)) = 0) (hj : ∀ j, ∫ x, S j x * F x ∂(Pfam (θr M)) = 0) :
    normalProj hS ν M hF = F := by
  funext x
  unfold normalProj regProj
  have e : (⟨respCov hS ν M F, respCov_mem_dirSpan hS ν hF⟩ : 𝕍) = 0 :=
    Subtype.ext (respCov_eq_zero_of_invisible hS ν h0 hj)
  rw [h0, e, responseScore_zero]
  ring

/-- **Invisible signed densities are normal**: if `q_M F` has zero mass and zero feature moments
then `q_M N_M F = q_M F`. -/
theorem famDens_mul_normalProj_of_invisible {F : X → ℝ} (hF : Bdd F)
    (h0 : ∫ x, famDens S ν (θr M) x * F x ∂ν = 0)
    (hj : ∀ j, ∫ x, S j x * (famDens S ν (θr M) x * F x) ∂ν = 0) (x : X) :
    famDens S ν (θr M) x * normalProj hS ν M hF x = famDens S ν (θr M) x * F x := by
  rw [normalProj_eq_self_of_invisible hS ν hF ?_ ?_]
  · rw [integral_famDens_mul hS ν]
    exact h0
  · intro j
    rw [integral_famDens_mul hS ν]
    refine (integral_congr_ae (Eventually.of_forall fun x ↦ ?_)).trans (hj j)
    ring

/-- The covariance vector is additive in the observable. -/
theorem respCov_add {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) :
    respCov hS ν M (fun x ↦ f x + g x) = respCov hS ν M f + respCov hS ν M g := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  funext j
  simp only [respCov, lawCov, Pi.add_apply]
  have h1 : Integrable (fun x ↦ S j x * f x) (Pfam (θr M)) :=
    integrable_of_bdd_prob _ ((hS j).mul hf)
  have h2 : Integrable (fun x ↦ S j x * g x) (Pfam (θr M)) :=
    integrable_of_bdd_prob _ ((hS j).mul hg)
  have e : (fun x ↦ S j x * (f x + g x)) = fun x ↦ S j x * f x + S j x * g x :=
    funext fun x ↦ by ring
  rw [e, integral_add h1 h2,
    integral_add (integrable_of_bdd_prob _ hf) (integrable_of_bdd_prob _ hg)]
  ring

/-- The normal projection is additive. -/
theorem normalProj_add {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) (x : X) :
    normalProj hS ν M (hf.add hg) x = normalProj hS ν M hf x + normalProj hS ν M hg x := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  unfold normalProj regProj
  have e : (⟨respCov hS ν M (fun x ↦ f x + g x), respCov_mem_dirSpan hS ν (hf.add hg)⟩ : 𝕍) =
      ⟨respCov hS ν M f, respCov_mem_dirSpan hS ν hf⟩ +
        ⟨respCov hS ν M g, respCov_mem_dirSpan hS ν hg⟩ :=
    Subtype.ext (respCov_add hS ν hf hg)
  rw [e, responseScore_add,
    integral_add (integrable_of_bdd_prob _ hf) (integrable_of_bdd_prob _ hg)]
  ring

/-- The normal projection kills constants. -/
theorem normalProj_const (c : ℝ) (x : X) : normalProj hS ν M (Bdd.const c) x = 0 := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  unfold normalProj regProj
  have e : (⟨respCov hS ν M (fun _ ↦ c), respCov_mem_dirSpan hS ν (Bdd.const c)⟩ : 𝕍) = 0 := by
    refine Subtype.ext ?_
    funext j
    simp [respCov, lawCov, integral_mul_const, integral_const]
  rw [e, responseScore_zero, integral_const, probReal_univ, one_smul]
  ring

/-- The normal projection commutes with scalars. -/
theorem normalProj_const_mul (c : ℝ) {f : X → ℝ} (hf : Bdd f) (x : X) :
    normalProj hS ν M (Bdd.const_mul c hf) x = c * normalProj hS ν M hf x :=
  normalProj_congr_smul hS ν M (Bdd.const_mul c hf) hf (fun _ ↦ rfl) x

/-- The normal projection only depends on the observable. -/
theorem normalProj_congr {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) (h : f = g) (x : X) :
    normalProj hS ν M hf x = normalProj hS ν M hg x := by
  subst h
  rfl

end Invisible

section ThirdJet

variable {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
  (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hfin

/-- The reconstruction curve along the atlas. -/
local notation "p" => fun s ↦ reconstructionL1 hS ν (atlasPath S ν M s)

/-- **The velocity of the natural coordinates is `C^∞`** on the interior atlas domain. -/
theorem contDiffOn_atlasVel : ContDiffOn ℝ ∞ (atlasVel hS ν hfin) (atlasDomain S ν M) := by
  have e : atlasVel hS ν hfin = fun s ↦ ((CDE (atlasTheta hS ν M s)).symm : 𝕍 →L[ℝ] 𝕍)
      ⟨M - m₀, sub_mem_dirSpan_of_genRate_ne_top hS ν hfin⟩ := by
    funext s
    rfl
  rw [e]
  exact ((contDiff_chartDerivEquiv_symm hS ν).comp_contDiffOn
    (contDiffOn_atlasTheta hS ν hfin)).clm_apply contDiffOn_const

/-- The acceleration `β'_s = d/ds β_s` of the natural coordinates, as a `𝕍`-valued function. -/
noncomputable def atlasVelD (s : ℝ) : 𝕍 := deriv (atlasVel hS ν hfin) s

/-- The jerk `β''_s = d²/ds² β_s` of the natural coordinates. -/
noncomputable def atlasVelDD (s : ℝ) : 𝕍 := deriv (deriv (atlasVel hS ν hfin)) s

theorem hasDerivAt_atlasVel_of_mem {s : ℝ} (hs : s ∈ atlasDomain S ν M) :
    HasDerivAt (atlasVel hS ν hfin) (atlasVelD hS ν hfin s) s :=
  (((contDiffOn_atlasVel hS ν hfin).differentiableOn (by simp)).differentiableAt
    ((isOpen_atlas_interior hS ν hfin).mem_nhds hs)).hasDerivAt

theorem contDiffOn_deriv_atlasVel :
    ContDiffOn ℝ ∞ (deriv (atlasVel hS ν hfin)) (atlasDomain S ν M) :=
  ((contDiffOn_infty_iff_deriv_of_isOpen (isOpen_atlas_interior hS ν hfin)).1
    (contDiffOn_atlasVel hS ν hfin)).2

theorem hasDerivAt_atlasVelD_of_mem {s : ℝ} (hs : s ∈ atlasDomain S ν M) :
    HasDerivAt (atlasVelD hS ν hfin) (atlasVelDD hS ν hfin s) s :=
  (((contDiffOn_deriv_atlasVel hS ν hfin).differentiableOn (by simp)).differentiableAt
    ((isOpen_atlas_interior hS ν hfin).mem_nhds hs)).hasDerivAt

include hrel in
/-- On `[0, 1]` the acceleration is the seabed's `atlasAccel = −Σ_s⁻¹ D_s β_s`. -/
theorem atlasVelD_eq_atlasAccel {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    atlasVelD hS ν hfin s = atlasAccel hS ν hfin hrel hs0 hs1 :=
  (hasDerivAt_atlasVel hS ν hfin hrel hs0 hs1).deriv

theorem hasDerivAt_atlasVel_coe_of_mem {s : ℝ} (hs : s ∈ atlasDomain S ν M) :
    HasDerivAt (fun t ↦ (atlasVel hS ν hfin t : J → ℝ)) (atlasVelD hS ν hfin s : J → ℝ) s :=
  (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_atlasVel_of_mem hS ν hfin hs)

theorem hasDerivAt_atlasVelD_coe_of_mem {s : ℝ} (hs : s ∈ atlasDomain S ν M) :
    HasDerivAt (fun t ↦ (atlasVelD hS ν hfin t : J → ℝ)) (atlasVelDD hS ν hfin s : J → ℝ) s :=
  (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_atlasVelD_of_mem hS ν hfin hs)

/-- `ℓ'_s = ⟨β'_s, M_s⟩ + ⟨β_s, M − m₀⟩ − ⟨β'_s, S⟩`, the derivative of the atlas score. -/
noncomputable def atlasScoreD (s : ℝ) (x : X) : ℝ :=
  dotJ (atlasVelD hS ν hfin s : J → ℝ) (atlasPath S ν M s) +
    dotJ (atlasVel hS ν hfin s : J → ℝ) (M - m₀) - dirLoss S (atlasVelD hS ν hfin s : J → ℝ) x

/-- `ℓ''_s = ⟨β''_s, M_s⟩ + 2⟨β'_s, M − m₀⟩ − ⟨β''_s, S⟩`, the second derivative of the score. -/
noncomputable def atlasScoreDD (s : ℝ) (x : X) : ℝ :=
  dotJ (atlasVelDD hS ν hfin s : J → ℝ) (atlasPath S ν M s) +
    2 * dotJ (atlasVelD hS ν hfin s : J → ℝ) (M - m₀) -
      dirLoss S (atlasVelDD hS ν hfin s : J → ℝ) x

theorem hasDerivAt_atlasScore_of_mem {s : ℝ} (hs : s ∈ atlasDomain S ν M) (x : X) :
    HasDerivAt (fun t ↦ atlasScore hS ν hfin t x) (atlasScoreD hS ν hfin s x) s := by
  have hβ := hasDerivAt_atlasVel_coe_of_mem hS ν hfin hs
  have hM := hasDerivAt_atlasPath ν (S := S) (M := M) s
  have h1 : HasDerivAt (fun t ↦ dotJ (atlasVel hS ν hfin t : J → ℝ) (atlasPath S ν M t))
      (dotJ (atlasVelD hS ν hfin s : J → ℝ) (atlasPath S ν M s) +
        dotJ (atlasVel hS ν hfin s : J → ℝ) (M - m₀)) s := by
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
      (hasDerivAt_pi.1 hβ i).mul (hasDerivAt_pi.1 hM i)
    refine h.congr_deriv ?_
    simp only [dotJ, Finset.sum_add_distrib]
  have h2 : HasDerivAt (fun t ↦ dirLoss S (atlasVel hS ν hfin t : J → ℝ) x)
      (dirLoss S (atlasVelD hS ν hfin s : J → ℝ) x) s :=
    HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ (hasDerivAt_pi.1 hβ i).mul_const (S i x)
  exact h1.sub h2

theorem hasDerivAt_atlasScoreD_of_mem {s : ℝ} (hs : s ∈ atlasDomain S ν M) (x : X) :
    HasDerivAt (fun t ↦ atlasScoreD hS ν hfin t x) (atlasScoreDD hS ν hfin s x) s := by
  have hβ := hasDerivAt_atlasVel_coe_of_mem hS ν hfin hs
  have hβ' := hasDerivAt_atlasVelD_coe_of_mem hS ν hfin hs
  have hM := hasDerivAt_atlasPath ν (S := S) (M := M) s
  have h1 : HasDerivAt (fun t ↦ dotJ (atlasVelD hS ν hfin t : J → ℝ) (atlasPath S ν M t))
      (dotJ (atlasVelDD hS ν hfin s : J → ℝ) (atlasPath S ν M s) +
        dotJ (atlasVelD hS ν hfin s : J → ℝ) (M - m₀)) s := by
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
      (hasDerivAt_pi.1 hβ' i).mul (hasDerivAt_pi.1 hM i)
    refine h.congr_deriv ?_
    simp only [dotJ, Finset.sum_add_distrib]
  have h2 : HasDerivAt (fun t ↦ dotJ (atlasVel hS ν hfin t : J → ℝ) (M - m₀))
      (dotJ (atlasVelD hS ν hfin s : J → ℝ) (M - m₀)) s :=
    HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
      (hasDerivAt_pi.1 hβ i).mul_const ((M - m₀) i)
  have h3 : HasDerivAt (fun t ↦ dirLoss S (atlasVelD hS ν hfin t : J → ℝ) x)
      (dirLoss S (atlasVelDD hS ν hfin s : J → ℝ) x) s :=
    HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ (hasDerivAt_pi.1 hβ' i).mul_const (S i x)
  refine ((h1.add h2).sub h3).congr_deriv ?_
  unfold atlasScoreDD
  ring

/-- `q_s (ℓ_s² + ℓ'_s)`: the density acceleration in terms of `β'`, defined for every `s`. -/
noncomputable def atlasHess' (s : ℝ) (x : X) : ℝ :=
  famDens S ν (atlasTheta hS ν M s) x *
    (atlasScore hS ν hfin s x ^ 2 + atlasScoreD hS ν hfin s x)

/-- The pointwise third-order coefficient `H₃ = ℓ³ + 3ℓℓ' + ℓ''`. -/
noncomputable def atlasH3 (s : ℝ) (x : X) : ℝ :=
  atlasScore hS ν hfin s x ^ 3 + 3 * atlasScore hS ν hfin s x * atlasScoreD hS ν hfin s x +
    atlasScoreDD hS ν hfin s x

/-- `q''' = q_s H₃`, the third derivative of the density along the atlas. -/
noncomputable def atlasThird (s : ℝ) (x : X) : ℝ :=
  famDens S ν (atlasTheta hS ν M s) x * atlasH3 hS ν hfin s x

include hrel in
theorem atlasHess'_eq_atlasHess {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : X) :
    atlasHess' hS ν hfin s x = atlasHess hS ν hfin hrel hs0 hs1 x := by
  unfold atlasHess' atlasHess atlasScoreD atlasCurv atlasScore
  rw [atlasVelD_eq_atlasAccel hS ν hfin hrel hs0 hs1, atlasAccel_eq_neg_atlasBend,
    Submodule.coe_neg, dotJ_neg_left, dirLoss_neg]
  ring

include hrel in
/-- **The third derivative of the density along the atlas**: `q''' = q (ℓ³ + 3ℓℓ' + ℓ'')`. -/
theorem hasDerivAt_atlasHess' {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (x : X) :
    HasDerivAt (fun t ↦ atlasHess' hS ν hfin t x) (atlasThird hS ν hfin s x) s := by
  have hsD : s ∈ atlasDomain S ν M := Ioo_subset_atlas_interior hS ν hfin hs
  have hq := hasDerivAt_famDens_atlas hS ν hfin hrel hs.1.le hs.2.le x
  have hℓ := hasDerivAt_atlasScore_of_mem hS ν hfin hsD x
  have hℓ' := hasDerivAt_atlasScoreD_of_mem hS ν hfin hsD x
  have h := hq.mul ((hℓ.mul hℓ).add hℓ')
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
  · simp only [atlasHess', sq, Pi.mul_apply, Pi.add_apply]
  · simp only [Pi.mul_apply, Pi.add_apply]
    unfold atlasThird atlasH3 atlasScore
    ring

theorem bdd_atlasScoreD (s : ℝ) : Bdd (atlasScoreD hS ν hfin s) :=
  ((Bdd.const _).add (Bdd.const _)).sub (bdd_dirLoss hS _)

theorem bdd_atlasScoreDD (s : ℝ) : Bdd (atlasScoreDD hS ν hfin s) :=
  ((Bdd.const _).add (Bdd.const _)).sub (bdd_dirLoss hS _)

theorem bdd_atlasH3 (s : ℝ) : Bdd (atlasH3 hS ν hfin s) := by
  have hb := bdd_atlasScore hS ν hfin (s := s)
  have e : atlasH3 hS ν hfin s = fun x ↦ atlasScore hS ν hfin s x *
      (atlasScore hS ν hfin s x * atlasScore hS ν hfin s x) +
        3 * atlasScore hS ν hfin s x * atlasScoreD hS ν hfin s x + atlasScoreDD hS ν hfin s x := by
    funext x
    unfold atlasH3
    ring
  rw [e]
  exact ((hb.mul (hb.mul hb)).add ((Bdd.const_mul 3 hb).mul (bdd_atlasScoreD hS ν hfin s))).add
    (bdd_atlasScoreDD hS ν hfin s)

/-- `p''` is differentiable on the interior atlas domain with derivative `p'''`. -/
theorem hasDerivAt_iteratedDeriv_two_reconstructionL1_atlas {s : ℝ}
    (hs : s ∈ atlasDomain S ν M) : HasDerivAt (iteratedDeriv 2 p) (iteratedDeriv 3 p s) s := by
  have hU := isOpen_atlas_interior hS ν hfin
  have h1 := (contDiffOn_infty_iff_deriv_of_isOpen hU).1
    (contDiffOn_reconstructionL1_atlas hS ν hfin)
  have h2 := (contDiffOn_infty_iff_deriv_of_isOpen hU).1 h1.2
  have e2 : iteratedDeriv 2 p = deriv (deriv p) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have e3 : iteratedDeriv 3 p = deriv (deriv (deriv p)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  rw [e2, e3]
  exact ((h2.2.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hs)).hasDerivAt

include hrel in
/-- Near `(0, 1)` the second jet has the pointwise representatives `atlasHess'`. -/
theorem iteratedDeriv_two_reconstructionL1_atlas_ae {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ t in 𝓝 s, ((iteratedDeriv 2 p t : X →₁[ν] ℝ) : X → ℝ) =ᵐ[ν] atlasHess' hS ν hfin t := by
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
  rw [iteratedDeriv_two_reconstructionL1_atlas hS ν hfin hrel ht]
  refine (Integrable.coeFn_toL1 _).trans ?_
  exact Eventually.of_forall fun x ↦ (atlasHess'_eq_atlasHess hS ν hfin hrel ht.1.le ht.2.le x).symm

include hrel in
theorem integrable_atlasThird {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    Integrable (atlasThird hS ν hfin s) ν :=
  integrable_of_hasDerivAt_L1 ν
    (hasDerivAt_iteratedDeriv_two_reconstructionL1_atlas hS ν hfin
      (Ioo_subset_atlas_interior hS ν hfin hs))
    (iteratedDeriv_two_reconstructionL1_atlas_ae hS ν hfin hrel hs)
    (hasDerivAt_atlasHess' hS ν hfin hrel hs)

include hrel in
/-- **The third jet**: `p'''(s) = [q_s (ℓ_s³ + 3 ℓ_s ℓ'_s + ℓ''_s)]` on `(0, 1)`. -/
theorem iteratedDeriv_three_reconstructionL1_atlas {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    iteratedDeriv 3 p s =
      (integrable_atlasThird hS ν hfin hrel hs).toL1 (atlasThird hS ν hfin s) :=
  hasDerivAt_L1_eq_toL1 ν
    (hasDerivAt_iteratedDeriv_two_reconstructionL1_atlas hS ν hfin
      (Ioo_subset_atlas_interior hS ν hfin hs))
    (iteratedDeriv_two_reconstructionL1_atlas_ae hS ν hfin hrel hs)
    (hasDerivAt_atlasHess' hS ν hfin hrel hs) _

include hrel in
/-- The third derivative of the density has zero mass. -/
theorem integral_atlasThird {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ∫ x, atlasThird hS ν hfin s x ∂ν = 0 := by
  have hsD := Ioo_subset_atlas_interior hS ν hfin hs
  have h := (invisible_tower hS ν hfin (k := 3) (by norm_num) hsD).2
  rw [iteratedDerivWithin_of_isOpen (isOpen_atlas_interior hS ν hfin) hsD,
    iteratedDeriv_three_reconstructionL1_atlas hS ν hfin hrel hs, ← L1.integral_eq,
    L1.integral_eq_integral] at h
  exact (integral_congr_ae
    (Integrable.coeFn_toL1 (integrable_atlasThird hS ν hfin hrel hs)).symm).trans h

include hrel in
/-- The third derivative of the density has zero feature moments. -/
theorem integral_stat_mul_atlasThird {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (j : J) :
    ∫ x, S j x * atlasThird hS ν hfin s x ∂ν = 0 := by
  have hsD := Ioo_subset_atlas_interior hS ν hfin hs
  have h := congrFun (invisible_tower hS ν hfin (k := 3) (by norm_num) hsD).1 j
  rw [iteratedDerivWithin_of_isOpen (isOpen_atlas_interior hS ν hfin) hsD,
    iteratedDeriv_three_reconstructionL1_atlas hS ν hfin hrel hs, momentL1_apply,
    Pi.zero_apply] at h
  refine (integral_congr_ae ?_).trans h
  filter_upwards [Integrable.coeFn_toL1 (integrable_atlasThird hS ν hfin hrel hs)] with x hx
  rw [hx]

include hrel in
/-- **Projection after differentiation, pointwise**: `q_s H₃ = q_s N_{M_s} H₃`. -/
theorem atlasThird_eq_normalProj {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (x : X) :
    atlasThird hS ν hfin s x =
      famDens S ν (atlasTheta hS ν M s) x *
        normalProj hS ν (atlasPath S ν M s) (bdd_atlasH3 hS ν hfin s) x :=
  (famDens_mul_normalProj_of_invisible hS ν (bdd_atlasH3 hS ν hfin s)
    (integral_atlasThird hS ν hfin hrel hs) (integral_stat_mul_atlasThird hS ν hfin hrel hs) x).symm

include hrel in
/-- **The third jet is a normal signed density**: `p'''(s) = [q_s N_{M_s}(ℓ³ + 3ℓℓ' + ℓ'')]`. -/
theorem iteratedDeriv_three_reconstructionL1_atlas_normal {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    iteratedDeriv 3 p s =
      (integrable_famDens_mul_of_bdd hS ν (M := atlasPath S ν M s)
        (bdd_normalProj hS ν (bdd_atlasH3 hS ν hfin s))).toL1
        (fun x ↦ famDens S ν (θr (atlasPath S ν M s)) x *
          normalProj hS ν (atlasPath S ν M s) (bdd_atlasH3 hS ν hfin s) x) := by
  rw [iteratedDeriv_three_reconstructionL1_atlas hS ν hfin hrel hs]
  exact (Integrable.toL1_eq_toL1_iff _ _ _ _).2
    (Eventually.of_forall fun x ↦ atlasThird_eq_normalProj hS ν hfin hrel hs x)

/-- **The bending score** `r_s = ⟨β'_s, S − M_s⟩ = ⟨w_s, M_s − S⟩`, so that `ℓ'_s = −c_s − r_s`. -/
noncomputable def atlasRho (s : ℝ) (x : X) : ℝ :=
  dirLoss S (atlasVelD hS ν hfin s : J → ℝ) x -
    dotJ (atlasVelD hS ν hfin s : J → ℝ) (atlasPath S ν M s)

theorem atlasScoreD_eq (s : ℝ) (x : X) :
    atlasScoreD hS ν hfin s x = -atlasCurv hS ν hfin s - atlasRho hS ν hfin s x := by
  unfold atlasScoreD atlasCurv atlasRho
  ring

/-- The bending score is the tangent score of `−β'_s`. -/
theorem atlasRho_eq_responseScore (s : ℝ) (x : X) :
    atlasRho hS ν hfin s x =
      responseScore hS ν (atlasPath S ν M s)
        (CDE (θr (atlasPath S ν M s)) (-atlasVelD hS ν hfin s)) x := by
  unfold atlasRho responseScore
  rw [ContinuousLinearEquiv.symm_apply_apply, Submodule.coe_neg, dotJ_neg_left, dirLoss_neg]
  ring

theorem bdd_atlasRho (s : ℝ) : Bdd (atlasRho hS ν hfin s) :=
  (bdd_dirLoss hS _).sub (Bdd.const _)

/-- **The cubic-minus-bending observable** `ℓ_s³ − 3 ℓ_s r_s`. -/
noncomputable def atlasCubicRho (s : ℝ) (x : X) : ℝ :=
  atlasScore hS ν hfin s x ^ 3 - 3 * atlasScore hS ν hfin s x * atlasRho hS ν hfin s x

theorem bdd_atlasCubicRho (s : ℝ) : Bdd (atlasCubicRho hS ν hfin s) := by
  have hb := bdd_atlasScore hS ν hfin (s := s)
  have e : atlasCubicRho hS ν hfin s = fun x ↦ atlasScore hS ν hfin s x *
      (atlasScore hS ν hfin s x * atlasScore hS ν hfin s x) -
        3 * atlasScore hS ν hfin s x * atlasRho hS ν hfin s x := by
    funext x
    unfold atlasCubicRho
    ring
  rw [e]
  exact (hb.mul (hb.mul hb)).sub ((Bdd.const_mul 3 hb).mul (bdd_atlasRho hS ν hfin s))

/-- `H₃ = (ℓ³ − 3ℓr) + (tangent score + constant)`: the affine part of the third coefficient. -/
theorem atlasH3_decomp (s : ℝ) :
    atlasH3 hS ν hfin s = fun x ↦ atlasCubicRho hS ν hfin s x +
      (responseScore hS ν (atlasPath S ν M s)
        ((-3 * atlasCurv hS ν hfin s) •
            (⟨M - m₀, sub_mem_dirSpan_of_genRate_ne_top hS ν hfin⟩ : 𝕍) +
          CDE (θr (atlasPath S ν M s)) (atlasVelDD hS ν hfin s)) x +
        2 * dotJ (atlasVelD hS ν hfin s : J → ℝ) (M - m₀)) := by
  funext x
  unfold atlasH3 atlasCubicRho atlasScoreDD
  rw [atlasScoreD_eq, responseScore_add, responseScore_smul,
    ← atlasScore_eq_responseScore hS ν hfin]
  unfold responseScore
  rw [ContinuousLinearEquiv.symm_apply_apply]
  ring

/-- **The normal projection sees only the cubic-minus-bending part of `H₃`.** -/
theorem normalProj_atlasH3_eq {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (x : X) :
    normalProj hS ν (atlasPath S ν M s) (bdd_atlasH3 hS ν hfin s) x =
      normalProj hS ν (atlasPath S ν M s) (bdd_atlasCubicRho hS ν hfin s) x := by
  have hrels : atlasPath S ν M s ∈ Ω := Ioo_subset_atlas_interior hS ν hfin hs
  have hG := bdd_atlasCubicRho hS ν hfin s
  have hA1 := bdd_responseScore hS ν (atlasPath S ν M s)
    ((-3 * atlasCurv hS ν hfin s) •
        (⟨M - m₀, sub_mem_dirSpan_of_genRate_ne_top hS ν hfin⟩ : 𝕍) +
      CDE (θr (atlasPath S ν M s)) (atlasVelDD hS ν hfin s))
  have hA2 := Bdd.const (X := X) (2 * dotJ (atlasVelD hS ν hfin s : J → ℝ) (M - m₀))
  rw [normalProj_congr hS ν (bdd_atlasH3 hS ν hfin s) (hG.add (hA1.add hA2))
    (atlasH3_decomp hS ν hfin s) x, normalProj_add hS ν hG (hA1.add hA2) x,
    normalProj_add hS ν hA1 hA2 x, normalProj_responseScore hS ν hrels, normalProj_const hS ν]
  simp

include hrel in
/-- **Projection after differentiation**: `p'''(s) = [q_s N_{M_s}(ℓ_s³ − 3 ℓ_s r_s)]` on
`(0, 1)`. -/
theorem iteratedDeriv_three_reconstructionL1_atlas_cubic {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    iteratedDeriv 3 p s =
      (integrable_famDens_mul_of_bdd hS ν (M := atlasPath S ν M s)
        (bdd_normalProj hS ν (bdd_atlasCubicRho hS ν hfin s))).toL1
        (fun x ↦ famDens S ν (θr (atlasPath S ν M s)) x *
          normalProj hS ν (atlasPath S ν M s) (bdd_atlasCubicRho hS ν hfin s) x) := by
  rw [iteratedDeriv_three_reconstructionL1_atlas_normal hS ν hfin hrel hs]
  refine (Integrable.toL1_eq_toL1_iff _ _ _ _).2 (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [normalProj_atlasH3_eq hS ν hfin hs x]

include hrel in
/-- The pairing of the third jet with an observable is `E_{Q_s}[N_s F · (ℓ³ − 3ℓr)]`. -/
theorem integral_mul_iteratedDeriv_three_atlas {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {F : X → ℝ}
    (hF : Bdd F) :
    ∫ x, F x * (iteratedDeriv 3 p s) x ∂ν =
      ∫ x, normalProj hS ν (atlasPath S ν M s) hF x * atlasCubicRho hS ν hfin s x
        ∂(Pfam (θr (atlasPath S ν M s))) := by
  have hrels : atlasPath S ν M s ∈ Ω := Ioo_subset_atlas_interior hS ν hfin hs
  rw [← integral_mul_normalProj_comm hS ν hrels hF (bdd_atlasCubicRho hS ν hfin s),
    integral_famDens_mul hS ν, iteratedDeriv_three_reconstructionL1_atlas_cubic hS ν hfin hrel hs]
  refine integral_congr_ae ?_
  filter_upwards [Integrable.coeFn_toL1 (integrable_famDens_mul_of_bdd hS ν
    (M := atlasPath S ν M s) (bdd_normalProj hS ν (bdd_atlasCubicRho hS ν hfin s)))] with x hx
  rw [hx]
  ring

include hrel in
/-- **The third derivative of every observable response along the atlas** is
`E_{Q_s}[N_s F · (ℓ_s³ − 3 ℓ_s r_s)]`. -/
theorem iteratedDeriv_three_obsResponse_atlas {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {F : X → ℝ}
    (hF : Bdd F) :
    iteratedDeriv 3 (fun s ↦ obsResponse hS ν F (atlasPath S ν M s)) s =
      ∫ x, normalProj hS ν (atlasPath S ν M s) hF x * atlasCubicRho hS ν hfin s x
        ∂(Pfam (θr (atlasPath S ν M s))) := by
  have hsD := Ioo_subset_atlas_interior hS ν hfin hs
  have e : (fun t ↦ obsL1 ν hF (reconstructionL1 hS ν (atlasPath S ν M t))) =
      fun t ↦ obsResponse hS ν F (atlasPath S ν M t) :=
    funext fun t ↦ obsL1_reconstructionL1 hS ν hF _
  rw [← integral_mul_iteratedDeriv_three_atlas hS ν hfin hrel hs hF, ← obsL1_apply ν hF,
    clm_iteratedDeriv_reconstructionL1_atlas hS ν hfin _ 3 hsD, e]

end ThirdJet

end Laplace.Multi
