/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ThirdJet
import Laplace.Multi.AtlasTotalVariation
import Laplace.Multi.InverseStability

/-!
# Explicit `L¹` bounds on the jets of the reconstruction along the atlas

With `λ` a lower bound on the feature covariance on the direction subspace at `M_s`
(`λ|v|² ≤ Var_{Q_s}⟨v, S⟩`), `L` a bound on the centred features (`|S − M_s| ≤ L`) and
`D ≥ |M − m₀|` (Euclidean norms in feature space):

* `atlasCurv_le`: `c_s = E_{Q_s} ℓ_s² ≤ D²/λ`; `abs_atlasScore_le`: `|ℓ_s| ≤ DL/λ`;
* `norm_iteratedDeriv_one_atlas_le`: `‖p'(s)‖₁ ≤ D/√λ`;
* `norm_iteratedDeriv_two_atlas_le`: `‖p''(s)‖₁ ≤ L D²/λ^{3/2}`;
* `integral_atlasRho_sq_le`: the bending score has `E_{Q_s} r_s² ≤ L² c_s²/λ`;
* `norm_iteratedDeriv_three_atlas_le`: `‖p'''(s)‖₁ ≤ 4 L² D³/λ^{5/2}`.

The route is uniform: an `L¹` norm `‖[q_s N_s g]‖₁ = E_{Q_s}|N_s g|` is at most `√(E_{Q_s} g²)`
(Cauchy–Schwarz and tangent Pythagoras, `integral_abs_normalProj_le_sqrt`), and the moments of the
scores are controlled by the coercivity `λ` through the pairing identities `c_s = −⟨β_s, δ⟩`,
`E r_s² = ⟨β'_s, Cov_{Q_s}(S, ℓ_s²)⟩` (`le_sq_div_of_coercive`).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Laplace.Multi

section Real

/-- `λ b ≤ a ≤ √b K` forces `a ≤ K²/λ`. -/
theorem le_sq_div_of_coercive {a b K lam : ℝ} (hlam : 0 < lam) (hb : 0 ≤ b)
    (h1 : lam * b ≤ a) (h2 : a ≤ √b * K) : a ≤ K ^ 2 / lam := by
  rcases le_or_gt a 0 with h | h
  · exact h.trans (by positivity)
  · have h3 : a ^ 2 ≤ b * K ^ 2 := by
      calc a ^ 2 ≤ (√b * K) ^ 2 := pow_le_pow_left₀ h.le h2 2
        _ = b * K ^ 2 := by rw [mul_pow, Real.sq_sqrt hb]
    have h4 : lam * a ^ 2 ≤ a * K ^ 2 := by
      calc lam * a ^ 2 ≤ lam * (b * K ^ 2) := by gcongr
        _ = (lam * b) * K ^ 2 := by ring
        _ ≤ a * K ^ 2 := by gcongr
    rw [le_div_iff₀ hlam]
    have := le_of_mul_le_mul_left (by linarith : a * (lam * a) ≤ a * K ^ 2) h
    linarith

end Real

section DotJ

variable {J : Type*} [Fintype J]

theorem dotJ_self_nonneg (a : J → ℝ) : 0 ≤ dotJ a a :=
  Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _

/-- Cauchy–Schwarz for the pairing. -/
theorem abs_dotJ_le_sqrt_mul (a b : J → ℝ) : |dotJ a b| ≤ √(dotJ a a) * √(dotJ b b) := by
  rw [← Real.sqrt_mul (dotJ_self_nonneg a)]
  exact Real.abs_le_sqrt (sq_dotJ_le a b)

end DotJ

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

/-- The chart derivative as a linear equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

section Norms

variable {M : J → ℝ}

/-- The variance of `⟨v, S⟩` under `P_θ` is `−⟨v, Dm(θ) v⟩`. -/
theorem lawCov_dirLoss_self_eq_neg_dotJ (θ v : 𝕍) :
    lawCov (Pfam (θ : J → ℝ)) (dirLoss S v) (dirLoss S v) =
      -dotJ (v : J → ℝ) (CDE θ v : J → ℝ) := by
  have h := dotJ_chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS θ (v : J → ℝ) v
  rw [priorCov_eq_lawCov_familyMeasure hS ν] at h
  have h' : dotJ (v : J → ℝ) (CDE θ v : J → ℝ) =
      -lawCov (Pfam (θ : J → ℝ)) (dirLoss S v) (dirLoss S v) := h
  linarith

/-- The `L¹` norm of `[q_M g]` is `E_{Q_M}|g|`. -/
theorem norm_toL1_famDens_mul {g : X → ℝ} (hg : Bdd g) :
    ‖(integrable_famDens_mul_of_bdd hS ν (M := M) hg).toL1 _‖ =
      ∫ x, |g x| ∂(Pfam (θr M)) := by
  rw [L1.norm_of_fun_eq_integral_norm, integral_famDens_mul hS ν]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (famDens_nonneg hS ν _ x)]

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- **The normal part is small in `L¹(Q_M)`**: `E_{Q_M}|N_M g| ≤ √(E_{Q_M} g²)`. -/
theorem integral_abs_normalProj_le_sqrt {g : X → ℝ} (hg : Bdd g) :
    ∫ x, |normalProj hS ν M hg x| ∂(Pfam (θr M)) ≤ √(∫ x, g x ^ 2 ∂(Pfam (θr M))) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  refine (integral_abs_le_sqrt_integral_sq _ (bdd_normalProj hS ν hg)).trans
    (Real.sqrt_le_sqrt ?_)
  have h1 := tangent_pythagoras hS ν hrel hg
  have hG : 0 ≤ fisherForm hS ν M ⟨respCov hS ν M g, respCov_mem_dirSpan hS ν hg⟩
      ⟨respCov hS ν M g, respCov_mem_dirSpan hS ν hg⟩ :=
    integral_nonneg fun x ↦ mul_self_nonneg _
  have h2 : ∫ x, (g x - ∫ y, g y ∂(Pfam (θr M))) ^ 2 ∂(Pfam (θr M)) ≤
      ∫ x, g x ^ 2 ∂(Pfam (θr M)) := by
    have hc := lawCov_self_eq_integral_sq (Pfam (θr M)) hg
    have e1 : ∫ x, (g x - ∫ y, g y ∂(Pfam (θr M))) ^ 2 ∂(Pfam (θr M)) =
        ∫ x, (g x - ∫ y, g y ∂(Pfam (θr M))) * (g x - ∫ y, g y ∂(Pfam (θr M))) ∂(Pfam (θr M)) :=
      integral_congr_ae (Eventually.of_forall fun x ↦ sq _)
    have e2 : ∫ x, g x ^ 2 ∂(Pfam (θr M)) = ∫ x, g x * g x ∂(Pfam (θr M)) :=
      integral_congr_ae (Eventually.of_forall fun x ↦ sq _)
    rw [e1, e2, ← hc]
    unfold lawCov
    nlinarith [mul_self_nonneg (∫ y, g y ∂(Pfam (θr M)))]
  linarith

end Norms

section Bounds

variable {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
  (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
  {lam L D : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L) (hD : 0 ≤ D)
  (hδ : dotJ (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)
    (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0) ≤ D ^ 2) {s : ℝ}
  (hcov : ∀ v : dirSpan ν (fun _ ↦ (1 : ℝ)) S, lam * dotJ (v : J → ℝ) v ≤
    lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s : J → ℝ))
      (dirLoss S v) (dirLoss S v))
  (hSb : ∀ x, dotJ (fun j ↦ atlasPath S ν M s j - S j x) (fun j ↦ atlasPath S ν M s j - S j x) ≤
    L ^ 2)
include hfin

/-- The reconstruction curve along the atlas. -/
local notation "p" => fun s ↦ reconstructionL1 hS ν (atlasPath S ν M s)

/-- The reconstruction at the atlas point. -/
local notation "Qs" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
  (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
    (atlasPath S ν M s))

theorem chartDerivEquiv_atlasVel :
    CDE (atlasTheta hS ν M s) (atlasVel hS ν hfin s) =
      ⟨M - m₀, sub_mem_dirSpan_of_genRate_ne_top hS ν hfin⟩ := by
  unfold atlasVel
  exact ContinuousLinearEquiv.apply_symm_apply _ _

/-- The curvature is the variance of `⟨β_s, S⟩` under `Q_s`. -/
theorem atlasCurv_eq_lawCov :
    atlasCurv hS ν hfin s = lawCov (Pfam (atlasTheta hS ν M s : J → ℝ))
      (dirLoss S (atlasVel hS ν hfin s)) (dirLoss S (atlasVel hS ν hfin s)) := by
  rw [atlasCurv_eq_priorCov, priorCov_eq_lawCov_familyMeasure hS ν]

include hcov in
/-- Coercivity: `λ |β_s|² ≤ c_s`. -/
theorem lam_mul_dotJ_atlasVel_le :
    lam * dotJ (atlasVel hS ν hfin s : J → ℝ) (atlasVel hS ν hfin s) ≤ atlasCurv hS ν hfin s := by
  rw [atlasCurv_eq_lawCov hS ν hfin]
  exact hcov _

include hD hδ in
/-- `c_s = −⟨β_s, δ⟩ ≤ |β_s| D`. -/
theorem atlasCurv_le_sqrt_mul :
    atlasCurv hS ν hfin s ≤ √(dotJ (atlasVel hS ν hfin s : J → ℝ) (atlasVel hS ν hfin s)) * D := by
  unfold atlasCurv
  calc -dotJ (atlasVel hS ν hfin s : J → ℝ) (M - m₀) ≤
        |dotJ (atlasVel hS ν hfin s : J → ℝ) (M - m₀)| := neg_le_abs _
    _ ≤ √(dotJ (atlasVel hS ν hfin s : J → ℝ) (atlasVel hS ν hfin s)) * √(dotJ (M - m₀) (M - m₀)) :=
        abs_dotJ_le_sqrt_mul _ _
    _ ≤ √(dotJ (atlasVel hS ν hfin s : J → ℝ) (atlasVel hS ν hfin s)) * D := by
        gcongr
        exact (Real.sqrt_le_sqrt hδ).trans_eq (Real.sqrt_sq hD)

include hlam hD hδ hcov in
/-- **The curvature bound** `c_s ≤ D²/λ`. -/
theorem atlasCurv_le : atlasCurv hS ν hfin s ≤ D ^ 2 / lam :=
  le_sq_div_of_coercive hlam (dotJ_self_nonneg _) (lam_mul_dotJ_atlasVel_le hS ν hfin hcov)
    (atlasCurv_le_sqrt_mul hS ν hfin hD hδ)

include hlam hD hδ hcov in
/-- **The velocity bound** `|β_s|² ≤ D²/λ²`. -/
theorem dotJ_atlasVel_self_le :
    dotJ (atlasVel hS ν hfin s : J → ℝ) (atlasVel hS ν hfin s) ≤ D ^ 2 / lam ^ 2 := by
  have h1 := lam_mul_dotJ_atlasVel_le hS ν hfin hcov
  have h2 := atlasCurv_le hS ν hfin hlam hD hδ hcov
  rw [le_div_iff₀ hlam] at h2
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem atlasScore_eq_dotJ (x : X) :
    atlasScore hS ν hfin s x =
      dotJ (atlasVel hS ν hfin s : J → ℝ) (fun j ↦ atlasPath S ν M s j - S j x) := by
  simp only [atlasScore, dotJ, dirLoss, mul_sub, Finset.sum_sub_distrib]

include hlam hL hD hδ hcov hSb in
/-- **The score bound** `|ℓ_s| ≤ DL/λ`. -/
theorem abs_atlasScore_le (x : X) : |atlasScore hS ν hfin s x| ≤ D / lam * L := by
  rw [atlasScore_eq_dotJ hS ν hfin]
  refine (abs_dotJ_le_sqrt_mul _ _).trans ?_
  have h1 : √(dotJ (atlasVel hS ν hfin s : J → ℝ) (atlasVel hS ν hfin s)) ≤ D / lam :=
    (Real.sqrt_le_sqrt (dotJ_atlasVel_self_le hS ν hfin hlam hD hδ hcov)).trans_eq
      (by rw [show D ^ 2 / lam ^ 2 = (D / lam) ^ 2 by ring, Real.sqrt_sq (by positivity)])
  have h2 : √(dotJ (fun j ↦ atlasPath S ν M s j - S j x) (fun j ↦ atlasPath S ν M s j - S j x)) ≤
      L := (Real.sqrt_le_sqrt (hSb x)).trans_eq (Real.sqrt_sq hL)
  exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)

include hrel in
/-- `E_{Q_s} ℓ_s² = c_s`. -/
theorem integral_atlasScore_sq (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∫ x, atlasScore hS ν hfin s x ^ 2 ∂Qs = atlasCurv hS ν hfin s :=
  (atlasCurv_eq_integral_score_sq hS ν hfin hrel hs0 hs1).symm

include hrel in
/-- Fourth moment from the sup bound: `E ℓ⁴ ≤ K² c`. -/
theorem integral_atlasScore_sq_sq_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {K : ℝ}
    (hK : ∀ x, |atlasScore hS ν hfin s x| ≤ K) :
    ∫ x, (atlasScore hS ν hfin s x ^ 2) ^ 2 ∂Qs ≤ K ^ 2 * atlasCurv hS ν hfin s := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := atlasPath S ν M s)
  have hb2 := bdd_atlasScore_sq hS ν hfin (s := s)
  rw [← integral_atlasScore_sq hS ν hfin hrel hs0 hs1, ← integral_const_mul]
  refine integral_mono ((integrable_of_bdd_prob _ (hb2.mul hb2)).congr
    (Eventually.of_forall fun x ↦ (sq _).symm)) ((integrable_of_bdd_prob _ hb2).const_mul _)
    fun x ↦ ?_
  have h := hK x
  have hsq : atlasScore hS ν hfin s x ^ 2 ≤ K ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  calc (atlasScore hS ν hfin s x ^ 2) ^ 2 =
        atlasScore hS ν hfin s x ^ 2 * atlasScore hS ν hfin s x ^ 2 := sq _
    _ ≤ K ^ 2 * atlasScore hS ν hfin s x ^ 2 := by gcongr

include hrel hlam hD hδ hcov in
/-- **`‖p'(s)‖₁ ≤ D/√λ`.** -/
theorem norm_iteratedDeriv_one_atlas_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖iteratedDeriv 1 p s‖ ≤ D / √lam := by
  have hsD : s ∈ atlasDomain S ν M :=
    atlas_mem_intrinsicInterior' hS ν hfin hrel hs0 hs1
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := atlasPath S ν M s)
  rw [iteratedDeriv_one_reconstructionL1_atlas hS ν hfin hsD, reconstructionDeriv_apply,
    L1.norm_of_fun_eq_integral_norm]
  have e : ∫ x, ‖famDens S ν (θr (atlasPath S ν M s)) x *
        responseScore hS ν (atlasPath S ν M s) (atlasInc hS ν hfin) x‖ ∂ν =
      ∫ x, |atlasScore hS ν hfin s x| ∂Qs := by
    rw [integral_famDens_mul hS ν]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (famDens_nonneg hS ν _ x)]
    rfl
  rw [e]
  refine (integral_abs_le_sqrt_integral_sq _ (bdd_atlasScore hS ν hfin)).trans ?_
  rw [integral_atlasScore_sq hS ν hfin hrel hs0 hs1]
  refine (Real.sqrt_le_sqrt (atlasCurv_le hS ν hfin hlam hD hδ hcov)).trans_eq ?_
  rw [Real.sqrt_div (sq_nonneg D), Real.sqrt_sq hD]

include hrel hlam hL hD hδ hcov hSb in
/-- **`‖p''(s)‖₁ ≤ L D²/λ^{3/2}`.** -/
theorem norm_iteratedDeriv_two_atlas_le (hs : s ∈ Ioo (0 : ℝ) 1) :
    ‖iteratedDeriv 2 p s‖ ≤ L * D ^ 2 / (lam * √lam) := by
  have hrels : atlasPath S ν M s ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) :=
    Ioo_subset_atlas_interior hS ν hfin hs
  have hb2 := bdd_atlasScore_sq hS ν hfin (s := s)
  rw [iteratedDeriv_two_reconstructionL1_atlas hS ν hfin hrel hs, L1.norm_of_fun_eq_integral_norm]
  have e : ∫ x, ‖atlasHess hS ν hfin hrel hs.1.le hs.2.le x‖ ∂ν =
      ∫ x, |normalProj hS ν (atlasPath S ν M s) hb2 x| ∂Qs := by
    rw [integral_famDens_mul hS ν]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [atlasHess_eq_normalProj hS ν hfin hrel hs.1.le hs.2.le, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (famDens_nonneg hS ν _ x)]
    rfl
  rw [e]
  refine (integral_abs_normalProj_le_sqrt hS ν hrels hb2).trans ?_
  have hK := abs_atlasScore_le hS ν hfin hlam hL hD hδ hcov hSb (s := s)
  have h4 := integral_atlasScore_sq_sq_le hS ν hfin hrel hs.1.le hs.2.le hK
  have hc := atlasCurv_le hS ν hfin hlam hD hδ hcov (s := s)
  have hc0 := atlasCurv_nonneg hS ν hfin s
  calc √(∫ x, (atlasScore hS ν hfin s x ^ 2) ^ 2 ∂Qs) ≤ √((D / lam * L) ^ 2 * (D ^ 2 / lam)) := by
        refine Real.sqrt_le_sqrt (h4.trans ?_)
        gcongr
    _ = L * D ^ 2 / (lam * √lam) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), Real.sqrt_div (sq_nonneg D),
          Real.sqrt_sq hD]
        field_simp

include hrel in
/-- The bending score is centred: `E_{Q_s} r_s² = Var_{Q_s}⟨β'_s, S⟩`. -/
theorem integral_atlasRho_sq_eq_lawCov (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∫ x, atlasRho hS ν hfin s x ^ 2 ∂Qs =
      lawCov Qs (dirLoss S (atlasVelD hS ν hfin s)) (dirLoss S (atlasVelD hS ν hfin s)) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := atlasPath S ν M s)
  have hm : ∫ y, dirLoss S (atlasVelD hS ν hfin s : J → ℝ) y ∂Qs =
      dotJ (atlasVelD hS ν hfin s : J → ℝ) (atlasPath S ν M s) :=
    integral_dirLoss_atlasTheta hS ν hfin hrel hs0 hs1 _
  rw [lawCov_self_eq_integral_sq _ (bdd_dirLoss hS _), hm]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by unfold atlasRho; ring)

include hrel in
/-- `Dm(θ_s) β'_s = −Cov_{Q_s}(S, ℓ_s²)`. -/
theorem chartDerivEquiv_atlasVelD (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    CDE (atlasTheta hS ν M s) (atlasVelD hS ν hfin s) =
      -⟨respCov hS ν (atlasPath S ν M s) (fun x ↦ atlasScore hS ν hfin s x ^ 2),
        respCov_mem_dirSpan hS ν (bdd_atlasScore_sq hS ν hfin)⟩ := by
  rw [atlasVelD_eq_atlasAccel hS ν hfin hrel hs0 hs1, atlasAccel_eq_neg_atlasBend,
    atlasBend_eq_respCov hS ν hfin hrel hs0 hs1, map_neg]
  congr 1
  exact ContinuousLinearEquiv.apply_symm_apply _ _

include hrel in
/-- The covariance vector of the squared score pairs as a centred third moment:
`⟨v, Cov(S, ℓ²)⟩ = E[⟨v, S − M_s⟩ ℓ²]`. -/
theorem dotJ_respCov_atlasScore_sq (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (v : J → ℝ) :
    dotJ v (respCov hS ν (atlasPath S ν M s) (fun x ↦ atlasScore hS ν hfin s x ^ 2)) =
      ∫ x, (dirLoss S v x - dotJ v (atlasPath S ν M s)) * atlasScore hS ν hfin s x ^ 2 ∂Qs := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := atlasPath S ν M s)
  have hb2 := bdd_atlasScore_sq hS ν hfin (s := s)
  have hM : ∀ j, ∫ y, S j y ∂Qs = atlasPath S ν M s j := fun j ↦
    congrFun (integral_stat_atlasTheta hS ν hfin hrel hs0 hs1) j
  have hc : ∫ y, atlasScore hS ν hfin s y ^ 2 ∂Qs = atlasCurv hS ν hfin s :=
    integral_atlasScore_sq hS ν hfin hrel hs0 hs1
  have hi1 : Integrable (fun x ↦ dirLoss S v x * atlasScore hS ν hfin s x ^ 2) Qs :=
    integrable_of_bdd_prob _ ((bdd_dirLoss hS v).mul hb2)
  have hi2 : Integrable (fun x ↦ dotJ v (atlasPath S ν M s) * atlasScore hS ν hfin s x ^ 2) Qs :=
    (integrable_of_bdd_prob _ hb2).const_mul _
  have e : ∀ x, (dirLoss S v x - dotJ v (atlasPath S ν M s)) * atlasScore hS ν hfin s x ^ 2 =
      dirLoss S v x * atlasScore hS ν hfin s x ^ 2 -
        dotJ v (atlasPath S ν M s) * atlasScore hS ν hfin s x ^ 2 := fun x ↦ by ring
  simp_rw [e]
  rw [integral_sub hi1 hi2, integral_const_mul, hc]
  have hsum : ∫ x, dirLoss S v x * atlasScore hS ν hfin s x ^ 2 ∂Qs =
      ∑ j, v j * ∫ x, S j x * atlasScore hS ν hfin s x ^ 2 ∂Qs := by
    have e2 : ∀ x, dirLoss S v x * atlasScore hS ν hfin s x ^ 2 =
        ∑ j, v j * (S j x * atlasScore hS ν hfin s x ^ 2) := fun x ↦ by
      simp only [dirLoss, Finset.sum_mul, mul_assoc]
    simp_rw [e2]
    rw [integral_finsetSum _ fun j _ ↦ (integrable_of_bdd_prob _ ((hS j).mul hb2)).const_mul (v j)]
    exact Finset.sum_congr rfl fun j _ ↦ integral_const_mul _ _
  rw [hsum]
  simp only [respCov, lawCov, dotJ, hM, hc, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ by ring

include hrel hL hSb in
/-- `|⟨v, Cov(S, ℓ²)⟩| ≤ |v| L c_s`. -/
theorem abs_dotJ_respCov_atlasScore_sq_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (v : J → ℝ) :
    |dotJ v (respCov hS ν (atlasPath S ν M s) (fun x ↦ atlasScore hS ν hfin s x ^ 2))| ≤
      √(dotJ v v) * L * atlasCurv hS ν hfin s := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := atlasPath S ν M s)
  have hb2 := bdd_atlasScore_sq hS ν hfin (s := s)
  rw [dotJ_respCov_atlasScore_sq hS ν hfin hrel hs0 hs1]
  have hpt : ∀ x, |dirLoss S v x - dotJ v (atlasPath S ν M s)| ≤ √(dotJ v v) * L := fun x ↦ by
    have e : dirLoss S v x - dotJ v (atlasPath S ν M s) =
        -dotJ v (fun j ↦ atlasPath S ν M s j - S j x) := by
      simp only [dotJ, dirLoss, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e, abs_neg]
    refine (abs_dotJ_le_sqrt_mul _ _).trans ?_
    gcongr
    exact (Real.sqrt_le_sqrt (hSb x)).trans_eq (Real.sqrt_sq hL)
  have hi : Integrable (fun x ↦ (dirLoss S v x - dotJ v (atlasPath S ν M s)) *
      atlasScore hS ν hfin s x ^ 2) Qs :=
    integrable_of_bdd_prob _ (((bdd_dirLoss hS v).sub (Bdd.const _)).mul hb2)
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_atlasScore_sq hS ν hfin hrel hs0 hs1, ← integral_const_mul]
  refine integral_mono hi.abs ((integrable_of_bdd_prob _ hb2).const_mul _) fun x ↦ ?_
  rw [abs_mul, abs_of_nonneg (sq_nonneg (atlasScore hS ν hfin s x))]
  exact mul_le_mul_of_nonneg_right (hpt x) (sq_nonneg _)

include hrel hL hSb in
/-- `|Cov(S, ℓ²)| ≤ L c_s`. -/
theorem sqrt_dotJ_respCov_atlasScore_sq_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    √(dotJ (respCov hS ν (atlasPath S ν M s) (fun x ↦ atlasScore hS ν hfin s x ^ 2))
      (respCov hS ν (atlasPath S ν M s) (fun x ↦ atlasScore hS ν hfin s x ^ 2))) ≤
      L * atlasCurv hS ν hfin s := by
  set κ := respCov hS ν (atlasPath S ν M s) (fun x ↦ atlasScore hS ν hfin s x ^ 2) with hκ
  have h := abs_dotJ_respCov_atlasScore_sq_le hS ν hfin hrel hL hSb hs0 hs1 κ
  rw [← hκ] at h
  have hc0 := atlasCurv_nonneg hS ν hfin s
  have hk0 := dotJ_self_nonneg κ
  have h1 : dotJ κ κ ≤ √(dotJ κ κ) * (L * atlasCurv hS ν hfin s) := by
    rw [← mul_assoc]
    exact (le_abs_self _).trans h
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (dotJ κ κ)) with h0 | h0
  · rw [← h0]
    positivity
  · have h1' : √(dotJ κ κ) * √(dotJ κ κ) ≤ √(dotJ κ κ) * (L * atlasCurv hS ν hfin s) := by
      rw [Real.mul_self_sqrt hk0]
      exact h1
    exact le_of_mul_le_mul_left h1' h0

include hrel hlam hL hcov hSb in
/-- **The bending-score bound** `E_{Q_s} r_s² ≤ L² c_s²/λ`. -/
theorem integral_atlasRho_sq_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∫ x, atlasRho hS ν hfin s x ^ 2 ∂Qs ≤ (L * atlasCurv hS ν hfin s) ^ 2 / lam := by
  have hc0 := atlasCurv_nonneg hS ν hfin s
  refine le_sq_div_of_coercive hlam (dotJ_self_nonneg (atlasVelD hS ν hfin s : J → ℝ)) ?_ ?_
  · rw [integral_atlasRho_sq_eq_lawCov hS ν hfin hrel hs0 hs1]
    exact hcov _
  · rw [integral_atlasRho_sq_eq_lawCov hS ν hfin hrel hs0 hs1]
    have h1 := lawCov_dirLoss_self_eq_neg_dotJ hS ν (atlasTheta hS ν M s) (atlasVelD hS ν hfin s)
    have h1' : lawCov Qs (dirLoss S (atlasVelD hS ν hfin s)) (dirLoss S (atlasVelD hS ν hfin s)) =
        -dotJ (atlasVelD hS ν hfin s : J → ℝ)
          (CDE (atlasTheta hS ν M s) (atlasVelD hS ν hfin s) : J → ℝ) := h1
    rw [h1', chartDerivEquiv_atlasVelD hS ν hfin hrel hs0 hs1, Submodule.coe_neg, dotJ_comm,
      dotJ_neg_left, neg_neg, dotJ_comm]
    refine (le_abs_self _).trans ((abs_dotJ_le_sqrt_mul _ _).trans ?_)
    gcongr
    exact sqrt_dotJ_respCov_atlasScore_sq_le hS ν hfin hrel hL hSb hs0 hs1

theorem bdd_atlasScore_cube : Bdd fun x ↦ atlasScore hS ν hfin s x ^ 3 := by
  have hb := bdd_atlasScore hS ν hfin (s := s)
  have e : (fun x ↦ atlasScore hS ν hfin s x ^ 3) = fun x ↦ atlasScore hS ν hfin s x *
      (atlasScore hS ν hfin s x * atlasScore hS ν hfin s x) := funext fun x ↦ by ring
  rw [e]
  exact hb.mul (hb.mul hb)

theorem bdd_atlasScore_mul_atlasRho :
    Bdd fun x ↦ atlasScore hS ν hfin s x * atlasRho hS ν hfin s x :=
  (bdd_atlasScore hS ν hfin).mul (bdd_atlasRho hS ν hfin s)

include hrel hlam hL hD hδ hcov hSb in
/-- **`‖p'''(s)‖₁ ≤ 4 L² D³/λ^{5/2}`.** -/
theorem norm_iteratedDeriv_three_atlas_le (hs : s ∈ Ioo (0 : ℝ) 1) :
    ‖iteratedDeriv 3 p s‖ ≤ 4 * L ^ 2 * D ^ 3 / (lam ^ 2 * √lam) := by
  have hrels : atlasPath S ν M s ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) :=
    Ioo_subset_atlas_interior hS ν hfin hs
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := atlasPath S ν M s)
  have hb := bdd_atlasScore hS ν hfin (s := s)
  have hb3 := bdd_atlasScore_cube hS ν hfin (s := s)
  have hbr := bdd_atlasScore_mul_atlasRho hS ν hfin (s := s)
  have hbr3 := Bdd.const_mul (-3) hbr
  rw [iteratedDeriv_three_reconstructionL1_atlas_cubic hS ν hfin hrel hs,
    norm_toL1_famDens_mul hS ν (bdd_normalProj hS ν (bdd_atlasCubicRho hS ν hfin s))]
  -- split the normal projection
  have hdec : atlasCubicRho hS ν hfin s = fun x ↦ atlasScore hS ν hfin s x ^ 3 +
      (-3) * (atlasScore hS ν hfin s x * atlasRho hS ν hfin s x) := by
    funext x
    unfold atlasCubicRho
    ring
  have hN : ∀ x, normalProj hS ν (atlasPath S ν M s) (bdd_atlasCubicRho hS ν hfin s) x =
      normalProj hS ν (atlasPath S ν M s) hb3 x +
        (-3) * normalProj hS ν (atlasPath S ν M s) hbr x := fun x ↦ by
    rw [normalProj_congr hS ν (bdd_atlasCubicRho hS ν hfin s) (hb3.add hbr3) hdec x,
      normalProj_add hS ν hb3 hbr3 x, normalProj_const_mul hS ν (-3) hbr x]
  simp_rw [hN]
  -- the two pieces
  have hK := abs_atlasScore_le hS ν hfin hlam hL hD hδ hcov hSb (s := s)
  have hc := atlasCurv_le hS ν hfin hlam hD hδ hcov (s := s)
  have hc0 := atlasCurv_nonneg hS ν hfin s
  have hK0 : 0 ≤ D / lam * L := by positivity
  have hA : ∫ x, |normalProj hS ν (atlasPath S ν M s) hb3 x| ∂Qs ≤
      (D / lam * L) ^ 2 * (D / √lam) := by
    refine (integral_abs_normalProj_le_sqrt hS ν hrels hb3).trans ?_
    have h6 : ∫ x, (atlasScore hS ν hfin s x ^ 3) ^ 2 ∂Qs ≤
        ((D / lam * L) ^ 2) ^ 2 * atlasCurv hS ν hfin s := by
      rw [← integral_atlasScore_sq hS ν hfin hrel hs.1.le hs.2.le, ← integral_const_mul]
      refine integral_mono (integrable_of_bdd_prob _ (hb3.mul hb3) |>.congr
        (Eventually.of_forall fun x ↦ (sq _).symm))
        ((integrable_of_bdd_prob _ (bdd_atlasScore_sq hS ν hfin)).const_mul _) fun x ↦ ?_
      have hsq : atlasScore hS ν hfin s x ^ 2 ≤ (D / lam * L) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hK x) 2
      calc (atlasScore hS ν hfin s x ^ 3) ^ 2 =
            atlasScore hS ν hfin s x ^ 2 * atlasScore hS ν hfin s x ^ 2 *
              atlasScore hS ν hfin s x ^ 2 := by ring
        _ ≤ (D / lam * L) ^ 2 * (D / lam * L) ^ 2 * atlasScore hS ν hfin s x ^ 2 := by
            gcongr
        _ = ((D / lam * L) ^ 2) ^ 2 * atlasScore hS ν hfin s x ^ 2 := by ring
    calc √(∫ x, (atlasScore hS ν hfin s x ^ 3) ^ 2 ∂Qs) ≤
          √(((D / lam * L) ^ 2) ^ 2 * (D ^ 2 / lam)) := by
          refine Real.sqrt_le_sqrt (h6.trans ?_)
          gcongr
      _ = (D / lam * L) ^ 2 * (D / √lam) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
            Real.sqrt_div (sq_nonneg D), Real.sqrt_sq hD]
  have hB : ∫ x, |normalProj hS ν (atlasPath S ν M s) hbr x| ∂Qs ≤
      (D / lam * L) * (L * (D ^ 2 / lam) / √lam) := by
    refine (integral_abs_normalProj_le_sqrt hS ν hrels hbr).trans ?_
    have hr := integral_atlasRho_sq_le hS ν hfin hrel hlam hL hcov hSb hs.1.le hs.2.le
    have h2 : ∫ x, (atlasScore hS ν hfin s x * atlasRho hS ν hfin s x) ^ 2 ∂Qs ≤
        (D / lam * L) ^ 2 * ∫ x, atlasRho hS ν hfin s x ^ 2 ∂Qs := by
      rw [← integral_const_mul]
      refine integral_mono (integrable_of_bdd_prob _ (hbr.mul hbr) |>.congr
        (Eventually.of_forall fun x ↦ (sq _).symm))
        ((integrable_of_bdd_prob _ ((bdd_atlasRho hS ν hfin s).mul (bdd_atlasRho hS ν hfin s))
          |>.congr (Eventually.of_forall fun x ↦ (sq _).symm)).const_mul _) fun x ↦ ?_
      have hsq : atlasScore hS ν hfin s x ^ 2 ≤ (D / lam * L) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hK x) 2
      calc (atlasScore hS ν hfin s x * atlasRho hS ν hfin s x) ^ 2 =
            atlasScore hS ν hfin s x ^ 2 * atlasRho hS ν hfin s x ^ 2 := by ring
        _ ≤ (D / lam * L) ^ 2 * atlasRho hS ν hfin s x ^ 2 := by gcongr
    have h2' : ∫ x, (atlasScore hS ν hfin s x * atlasRho hS ν hfin s x) ^ 2 ∂Qs ≤
        (D / lam * L) ^ 2 * ((L * atlasCurv hS ν hfin s) ^ 2 / lam) :=
      h2.trans (by gcongr)
    calc √(∫ x, (atlasScore hS ν hfin s x * atlasRho hS ν hfin s x) ^ 2 ∂Qs) ≤
          √((D / lam * L) ^ 2 * ((L * (D ^ 2 / lam)) ^ 2 / lam)) := by
          refine Real.sqrt_le_sqrt (h2'.trans ?_)
          gcongr
      _ = (D / lam * L) * (L * (D ^ 2 / lam) / √lam) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hK0, Real.sqrt_div (by positivity),
            Real.sqrt_sq (by positivity)]
  -- assemble
  have hi1 : Integrable (fun x ↦ |normalProj hS ν (atlasPath S ν M s) hb3 x|) Qs :=
    (integrable_of_bdd_prob _ (bdd_normalProj hS ν hb3)).abs
  have hi2 : Integrable (fun x ↦ |normalProj hS ν (atlasPath S ν M s) hbr x|) Qs :=
    (integrable_of_bdd_prob _ (bdd_normalProj hS ν hbr)).abs
  have hi12 : Integrable (fun x ↦ |normalProj hS ν (atlasPath S ν M s) hb3 x| +
      3 * |normalProj hS ν (atlasPath S ν M s) hbr x|) Qs := hi1.add (hi2.const_mul 3)
  have htri : ∫ x, |normalProj hS ν (atlasPath S ν M s) hb3 x +
      (-3) * normalProj hS ν (atlasPath S ν M s) hbr x| ∂Qs ≤
      ∫ x, (|normalProj hS ν (atlasPath S ν M s) hb3 x| +
        3 * |normalProj hS ν (atlasPath S ν M s) hbr x|) ∂Qs := by
    refine integral_mono ((integrable_of_bdd_prob _
      ((bdd_normalProj hS ν hb3).add (Bdd.const_mul (-3) (bdd_normalProj hS ν hbr)))).abs) hi12
      fun x ↦ ?_
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  refine htri.trans ?_
  rw [integral_add hi1 (hi2.const_mul 3), integral_const_mul]
  calc (∫ x, |normalProj hS ν (atlasPath S ν M s) hb3 x| ∂Qs) +
        3 * ∫ x, |normalProj hS ν (atlasPath S ν M s) hbr x| ∂Qs ≤
        (D / lam * L) ^ 2 * (D / √lam) + 3 * ((D / lam * L) * (L * (D ^ 2 / lam) / √lam)) := by
        gcongr
    _ = 4 * L ^ 2 * D ^ 3 / (lam ^ 2 * √lam) := by
        have hsl : √lam ≠ 0 := (Real.sqrt_pos.2 hlam).ne'
        field_simp
        ring

end Bounds

end Laplace.Multi
