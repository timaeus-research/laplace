/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DensityPeano
import Laplace.Multi.ThetaUniformPeano

/-!
# The compact-uniform relative second-order expansion of the reconstruction density

The pointwise-uniform Peano expansion of `DensityPeano` is made uniform over compact convex sets of
interior responses. The explicit route pays off: the remainder of `DensityPeano` is a polynomial in
`‖z‖`, the bound `Λ` on the inverse chart derivative, the bound `Mb` on the responses, the feature
bound `B`, and the natural-coordinate remainder `ε‖z‖²` (`abs_famDens_response_remainder_le`,
`densPeanoBound`). On a compact convex interior set the first three are uniform, and the
natural-coordinate remainder is uniformly small by the compact-uniform Peano lemma
(`uniform_responseTheta_peano`). Hence (`famDens_response_peano_uniform`): for every compact convex
`C` in the relative interior and every `ε > 0` there is `δ > 0` with

`|q_{M+z}(x) − q_M(x)(1 + ℓ_{M,z}(x) + ½ N_M(ℓ_{M,z}²)(x))| ≤ ε ‖z‖² q_M(x)`

for all `M ∈ C`, `z` with `M + z ∈ C` and `‖z‖ ≤ δ`, and all `x`; integrating gives the
compact-uniform total-variation expansion (`integral_abs_famDens_response_peano_uniform`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-- The explicit remainder coefficient of the second-order density expansion: `n = |J|`, `B` the
feature bound, `Λ` the bound on the inverse chart derivative, `Mb` the response bound, `ε` the
natural-coordinate remainder coefficient, `r = ‖z‖`. -/
noncomputable def densPeanoBound (n B Λ Mb ε r : ℝ) : ℝ :=
  13 * (n * B * ((Λ + 1) * r)) ^ 3 + n * (Mb + B) * (ε * r ^ 2) +
    ((n * (Mb + B)) ^ 2 * Λ + 2 * (n * B) ^ 2 * Λ) * r *
      ((B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + ε) * r ^ 2) +
    (1 / 2) * ((n * (Mb + B)) ^ 2 + 2 * (n * B) ^ 2) *
      ((B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + ε) * r ^ 2) ^ 2

/-- The leading coefficient of the remainder bound after the small parameters are removed. -/
noncomputable def densPeanoLead (n B Λ Mb : ℝ) : ℝ :=
  13 * (n * B * (Λ + 1)) ^ 3 +
    ((n * (Mb + B)) ^ 2 * Λ + 2 * (n * B) ^ 2 * Λ) * (B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + 1) +
    (1 / 2) * ((n * (Mb + B)) ^ 2 + 2 * (n * B) ^ 2) * (B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + 1) ^ 2

/-- For `r ≤ 1` and `ε ≤ 1` the remainder coefficient is at most `(D r + n(Mb+B) ε) r²`. -/
theorem densPeanoBound_le {n B Λ Mb ε r : ℝ} (hn : 0 ≤ n) (hB : 0 ≤ B) (hΛ : 0 ≤ Λ) (hMb : 0 ≤ Mb)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    densPeanoBound n B Λ Mb ε r ≤ (densPeanoLead n B Λ Mb * r + n * (Mb + B) * ε) * r ^ 2 := by
  unfold densPeanoBound densPeanoLead
  have hK₂ : 0 ≤ n * (Mb + B) := by positivity
  have hE : B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + ε ≤ B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + 1 := by linarith
  have hE0 : 0 ≤ B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + ε := by positivity
  have hr2 : r ^ 2 ≤ r := by nlinarith
  have hr3 : r ^ 3 ≤ r := by nlinarith [sq_nonneg r]
  have t1 : 13 * (n * B * ((Λ + 1) * r)) ^ 3 ≤ 13 * (n * B * (Λ + 1)) ^ 3 * r * r ^ 2 := by
    have : (n * B * ((Λ + 1) * r)) ^ 3 = (n * B * (Λ + 1)) ^ 3 * r ^ 3 := by ring
    rw [this]
    have h3 : (n * B * (Λ + 1)) ^ 3 * r ^ 3 ≤ (n * B * (Λ + 1)) ^ 3 * r ^ 3 := le_rfl
    nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ n * B * (Λ + 1)) 3]
  have t3 : ((n * (Mb + B)) ^ 2 * Λ + 2 * (n * B) ^ 2 * Λ) * r *
      ((B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + ε) * r ^ 2) ≤
      ((n * (Mb + B)) ^ 2 * Λ + 2 * (n * B) ^ 2 * Λ) * (B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + 1) * r *
        r ^ 2 := by
    have h0 : 0 ≤ (n * (Mb + B)) ^ 2 * Λ + 2 * (n * B) ^ 2 * Λ := by positivity
    calc ((n * (Mb + B)) ^ 2 * Λ + 2 * (n * B) ^ 2 * Λ) * r *
          ((B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + ε) * r ^ 2)
        = ((n * (Mb + B)) ^ 2 * Λ + 2 * (n * B) ^ 2 * Λ) * (B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + ε) *
            r * r ^ 2 := by ring
      _ ≤ ((n * (Mb + B)) ^ 2 * Λ + 2 * (n * B) ^ 2 * Λ) * (B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + 1) *
            r * r ^ 2 := by gcongr
  have t4 : (1 / 2) * ((n * (Mb + B)) ^ 2 + 2 * (n * B) ^ 2) *
      ((B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + ε) * r ^ 2) ^ 2 ≤
      (1 / 2) * ((n * (Mb + B)) ^ 2 + 2 * (n * B) ^ 2) * (B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + 1) ^ 2 *
        r * r ^ 2 := by
    have h0 : 0 ≤ (1 / 2) * ((n * (Mb + B)) ^ 2 + 2 * (n * B) ^ 2) := by positivity
    have h4 : r ^ 4 ≤ r * r ^ 2 := by nlinarith [sq_nonneg r, pow_nonneg hr0 3]
    calc (1 / 2) * ((n * (Mb + B)) ^ 2 + 2 * (n * B) ^ 2) *
          ((B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + ε) * r ^ 2) ^ 2
        = (1 / 2) * ((n * (Mb + B)) ^ 2 + 2 * (n * B) ^ 2) *
            (B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + ε) ^ 2 * r ^ 4 := by ring
      _ ≤ (1 / 2) * ((n * (Mb + B)) ^ 2 + 2 * (n * B) ^ 2) *
            (B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + 1) ^ 2 * (r * r ^ 2) := by gcongr
      _ = _ := by ring
  nlinarith [t1, t3, t4]

section Quantitative

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

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

set_option maxHeartbeats 2400000 in
-- the proof composes three explicit bounds (natural-coordinate Peano, cubic density remainder,
-- truncation splitting) in one declaration and exceeds the default budget
/-- **The quantitative pointwise second-order expansion of the reconstruction density**: with `B`
a feature bound, `Λ ≥ ‖R_M‖`, `Mb ≥ ‖M‖`, and a natural-coordinate remainder `≤ ε‖z‖²`, for `z`
small (`(B K₂² Λ³ + ε)‖z‖ ≤ 1`, `4K(Λ+1)‖z‖ ≤ 1`) the relative remainder is at most
`densPeanoBound |J| B Λ Mb ε ‖z‖`. -/
theorem abs_famDens_response_remainder_le {B Λ Mb : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j x, |S j x| ≤ B)
    (hΛ : ‖(ContinuousLinearEquiv.symm (CDE (θr M)) : 𝕍 →L[ℝ] 𝕍)‖ ≤ Λ) (hMb : ‖M‖ ≤ Mb)
    {ε : ℝ} (z : 𝕍)
    (hv : ‖θr (M + z) - θr M - ContinuousLinearEquiv.symm (CDE (θr M)) z -
      (1 / 2 : ℝ) • (-(ContinuousLinearEquiv.symm (CDE (θr M))
        (thirdOp hS ν (θr M) (ContinuousLinearEquiv.symm (CDE (θr M)) z)
          (ContinuousLinearEquiv.symm (CDE (θr M)) z))))‖ ≤ ε * ‖z‖ ^ 2)
    (hz1 : (B * ((Fintype.card J : ℝ) * (Mb + B)) ^ 2 * Λ ^ 3 + ε) * ‖z‖ ≤ 1)
    (hz2 : 4 * ((Fintype.card J : ℝ) * B * (Λ + 1)) * ‖z‖ ≤ 1) (x : X) :
    |famDens S ν (θr (M + z)) x - famDens S ν (θr M) x * (1 + responseScore hS ν M z x +
        (1 / 2) * normalProj hS ν M
          ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)| ≤
      densPeanoBound (Fintype.card J) B Λ Mb ε ‖z‖ * famDens S ν (θr M) x := by
  -- constants
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans hΛ
  have hMb0 : 0 ≤ Mb := (norm_nonneg _).trans hMb
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (Fintype.card J : ℝ) * B := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = (Fintype.card J : ℝ) * (Mb + B) := ⟨_, rfl⟩
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  obtain ⟨K₃, hK₃⟩ : ∃ K₃ : ℝ, K₃ = 2 * K ^ 2 := ⟨_, rfl⟩
  have hK₃0 : 0 ≤ K₃ := by rw [hK₃]; positivity
  -- the base point
  obtain ⟨θ, hθ⟩ : ∃ θ : 𝕍, θ = θr M := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : 𝕍 →L[ℝ] 𝕍, R = (ContinuousLinearEquiv.symm (CDE θ) : 𝕍 →L[ℝ] 𝕍) :=
    ⟨_, rfl⟩
  have hRΛ : ‖R‖ ≤ Λ := by rw [hR, hθ]; exact hΛ
  have hmean : famMean S ν θ = M := by
    rw [hθ, famMean_eq_meanMap hS ν]
    exact meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS hrel
  -- the response score as an affine score
  have hscore : ∀ (z : 𝕍) (x : X), responseScore hS ν M z x = affScoreAt S M (R z) x := by
    intro z x
    rw [responseScore_apply, hR, hθ]
    rfl
  have hRz : ∀ z : 𝕍, ‖(R z : J → ℝ)‖ ≤ Λ * ‖z‖ := fun z ↦ by
    rw [Submodule.norm_coe]
    exact (R.le_opNorm z).trans (mul_le_mul_of_nonneg_right hRΛ (norm_nonneg _))
  have hA : ∀ (w : 𝕍) (x : X), |affScoreAt S M (w : J → ℝ) x| ≤ K₂ * ‖w‖ := fun w x ↦ by
    rw [hK₂, ← Submodule.norm_coe]
    refine (abs_affScoreAt_le hB0 hB M _ x).trans ?_
    gcongr
  have hscore_bd : ∀ (z : 𝕍) (x : X), |responseScore hS ν M z x| ≤ K₂ * Λ * ‖z‖ := by
    intro z x
    rw [hscore]
    refine (hA (R z) x).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hRz z) hK₂0
  -- the quadratic term of the natural coordinate
  obtain ⟨c, hc⟩ : ∃ c : 𝕍, c = thirdOp hS ν θ (ContinuousLinearEquiv.symm (CDE θ) z)
    (ContinuousLinearEquiv.symm (CDE θ) z) := ⟨_, rfl⟩
  have hc_eq : c = ⟨respCov hS ν M (fun x ↦ responseScore hS ν M z x *
      responseScore hS ν M z x), respCov_mem_dirSpan hS ν
        ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z))⟩ := by
    rw [hc, hθ]
    exact responseTheta_peano_quadratic hS ν hrel z
  have hc_bd : ‖c‖ ≤ 2 * B * (K₂ * Λ * ‖z‖) ^ 2 := by
    rw [hc_eq, ← Submodule.norm_coe, Submodule.coe_mk]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j ↦ ?_
    rw [Real.norm_eq_abs]
    unfold respCov
    have := isProbabilityMeasure_family_responseTheta hS ν (M := M)
    refine abs_lawCov_le _ (hB j) fun x ↦ ?_
    rw [abs_mul, sq]
    exact mul_le_mul (hscore_bd z x) (hscore_bd z x) (abs_nonneg _)
      (mul_nonneg (mul_nonneg hK₂0 hΛ0) (norm_nonneg _))
  -- the regression projection as an affine score of `R c`
  have hreg : ∀ x : X, regProj hS ν M
      ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x =
      affScoreAt S M (R c) x := fun x ↦ by
    unfold regProj
    rw [hc_eq, responseScore_apply, hR, hθ]
    rfl
  -- the second moment of the score
  have hvar : covQ S ν θ (R z : J → ℝ) (R z : J → ℝ) =
      ∫ y, responseScore hS ν M z y * responseScore hS ν M z y ∂(Pfam (θr M)) := by
    rw [covQ_self_eq hS ν, hmean, integral_famDens_mul hS ν, ← hθ]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    beta_reduce
    rw [hscore]
    ring
  -- the natural-coordinate remainder
  obtain ⟨v, hvdef⟩ : ∃ v : 𝕍, v = θr (M + z) - θ - R z - (1 / 2 : ℝ) • (-(R c)) := ⟨_, rfl⟩
  have hvz : ‖v‖ ≤ ε * ‖z‖ ^ 2 := by
    rw [hvdef, hR, hc, hθ]
    exact hv
  obtain ⟨ζ, hζ⟩ : ∃ ζ : 𝕍, ζ = -(1 / 2 : ℝ) • R c + v := ⟨_, rfl⟩
  have hη : (θr (M + z) : J → ℝ) - (θ : J → ℝ) = (R z : J → ℝ) + (ζ : J → ℝ) := by
    rw [hζ, hvdef]
    simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_neg]
    module
  have hζ_bd : ‖ζ‖ ≤ 1 / 2 * Λ * (2 * B * (K₂ * Λ * ‖z‖) ^ 2) + ‖v‖ := by
    rw [hζ]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc 1 / 2 * ‖R c‖ ≤ 1 / 2 * (Λ * (2 * B * (K₂ * Λ * ‖z‖) ^ 2)) := by
          gcongr
          exact (R.le_opNorm _).trans (mul_le_mul hRΛ hc_bd (norm_nonneg _) hΛ0)
      _ = 1 / 2 * Λ * (2 * B * (K₂ * Λ * ‖z‖) ^ 2) := by ring
  have hζz : ‖ζ‖ ≤ (B * K₂ ^ 2 * Λ ^ 3 + ε) * ‖z‖ ^ 2 := by
    refine hζ_bd.trans ?_
    calc 1 / 2 * Λ * (2 * B * (K₂ * Λ * ‖z‖) ^ 2) + ‖v‖
        ≤ B * K₂ ^ 2 * Λ ^ 3 * ‖z‖ ^ 2 + ε * ‖z‖ ^ 2 := add_le_add (le_of_eq (by ring)) hvz
      _ = (B * K₂ ^ 2 * Λ ^ 3 + ε) * ‖z‖ ^ 2 := by ring
  have hζz' : ‖ζ‖ ≤ ‖z‖ := by
    have hζz2 : ‖ζ‖ ≤ (B * ((Fintype.card J : ℝ) * (Mb + B)) ^ 2 * Λ ^ 3 + ε) * ‖z‖ ^ 2 := by
      rw [hK₂] at hζz
      exact hζz
    calc ‖ζ‖ ≤ (B * ((Fintype.card J : ℝ) * (Mb + B)) ^ 2 * Λ ^ 3 + ε) * ‖z‖ ^ 2 := hζz2
      _ = ((B * ((Fintype.card J : ℝ) * (Mb + B)) ^ 2 * Λ ^ 3 + ε) * ‖z‖) * ‖z‖ := by ring
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hz1 (norm_nonneg _)
      _ = ‖z‖ := one_mul _
  -- the truncation at `η = Rz + ζ`: the exact identity
  have hsplit : ∀ x : X, densTrunc S ν θ ((R z : J → ℝ) + (ζ : J → ℝ)) x -
      (1 + responseScore hS ν M z x + (1 / 2) * normalProj hS ν M
        ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x) =
      affScoreAt S M v x + responseScore hS ν M z x * affScoreAt S M ζ x +
        (1 / 2) * affScoreAt S M ζ x ^ 2 - covQ S ν θ (R z : J → ℝ) (ζ : J → ℝ) -
        (1 / 2) * covQ S ν θ (ζ : J → ℝ) (ζ : J → ℝ) := fun x ↦ by
    rw [densTrunc_add hS ν, hmean, hvar, ← hscore]
    unfold normalProj
    rw [hreg]
    have e : affScoreAt S M ζ x = -(1 / 2) * affScoreAt S M (R c) x + affScoreAt S M v x := by
      rw [hζ]
      simp only [Submodule.coe_add, Submodule.coe_smul]
      rw [affScoreAt_add, affScoreAt_smul]
    rw [e]
    ring
  have hq0 := famDens_nonneg hS ν (θ : J → ℝ) x
  -- the natural-coordinate increment and its size
  obtain ⟨η, hηdef⟩ : ∃ η : J → ℝ, η = (θr (M + z) : J → ℝ) - (θ : J → ℝ) := ⟨_, rfl⟩
  have hηz : ‖η‖ ≤ (Λ + 1) * ‖z‖ := by
    rw [hηdef, hη]
    calc ‖(R z : J → ℝ) + (ζ : J → ℝ)‖ ≤ ‖(R z : J → ℝ)‖ + ‖(ζ : J → ℝ)‖ := norm_add_le _ _
      _ ≤ Λ * ‖z‖ + ‖z‖ := by
          refine add_le_add (hRz z) ?_
          rw [Submodule.norm_coe]
          exact hζz'
      _ = (Λ + 1) * ‖z‖ := by ring
  have hKη : (Fintype.card J : ℝ) * B * ‖η‖ ≤ 1 / 4 := by
    rw [← hK]
    rw [← hK] at hz2
    calc K * ‖η‖ ≤ K * ((Λ + 1) * ‖z‖) := mul_le_mul_of_nonneg_left hηz hK0
      _ = (4 * (K * (Λ + 1)) * ‖z‖) / 4 := by ring
      _ ≤ 1 / 4 := by gcongr
  -- the two remainders
  have hθη : (θ : J → ℝ) + η = (θr (M + z) : J → ℝ) := by rw [hηdef, add_sub_cancel]
  have hmain := abs_famDens_second_remainder_le hS ν hB0 hB (θ : J → ℝ) η hKη x
  rw [hθη] at hmain
  have hI : |famDens S ν (θr (M + z)) x - famDens S ν (θ : J → ℝ) x *
      densTrunc S ν θ ((R z : J → ℝ) + (ζ : J → ℝ)) x| ≤
      13 * (K * ((Λ + 1) * ‖z‖)) ^ 3 * famDens S ν (θ : J → ℝ) x := by
    rw [← hη, ← hηdef]
    refine hmain.trans (mul_le_mul_of_nonneg_right ?_ hq0)
    rw [← hK]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ 3) (by norm_num)
    exact mul_le_mul_of_nonneg_left hηz hK0
  have hII : |densTrunc S ν θ ((R z : J → ℝ) + (ζ : J → ℝ)) x -
      (1 + responseScore hS ν M z x + (1 / 2) * normalProj hS ν M
        ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)| ≤
      K₂ * ‖v‖ + (K₂ * Λ * K₂ + K₃ * Λ) * ‖z‖ * ‖ζ‖ + (1 / 2) * (K₂ ^ 2 + K₃) * ‖ζ‖ ^ 2 := by
    rw [hsplit]
    have hC : ∀ v w : 𝕍, |covQ S ν θ (v : J → ℝ) (w : J → ℝ)| ≤ K₃ * ‖v‖ * ‖w‖ := fun v w ↦ by
      rw [hK₃, hK, ← Submodule.norm_coe v, ← Submodule.norm_coe w]
      exact abs_covQ_le hS ν hB0 hB _ _ _
    have h1 := hA v x
    have h2 : |responseScore hS ν M z x * affScoreAt S M ζ x| ≤
        K₂ * Λ * ‖z‖ * (K₂ * ‖ζ‖) := by
      rw [abs_mul]
      exact mul_le_mul (hscore_bd z x) (hA ζ x) (abs_nonneg _) (by positivity)
    have h3 : |(1 / 2) * affScoreAt S M ζ x ^ 2| ≤ (1 / 2) * (K₂ * ‖ζ‖) ^ 2 := by
      rw [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hA ζ x) 2)
        (by norm_num)
    have h4 : |covQ S ν θ (R z : J → ℝ) (ζ : J → ℝ)| ≤ K₃ * (Λ * ‖z‖) * ‖ζ‖ := by
      refine (hC (R z) ζ).trans ?_
      gcongr
      rw [← Submodule.norm_coe]
      exact hRz z
    have h5 : |(1 / 2) * covQ S ν θ (ζ : J → ℝ) (ζ : J → ℝ)| ≤
        (1 / 2) * (K₃ * ‖ζ‖ * ‖ζ‖) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (hC ζ ζ) (by norm_num)
    calc |affScoreAt S M v x + responseScore hS ν M z x * affScoreAt S M ζ x +
          (1 / 2) * affScoreAt S M ζ x ^ 2 - covQ S ν θ (R z : J → ℝ) (ζ : J → ℝ) -
          (1 / 2) * covQ S ν θ (ζ : J → ℝ) (ζ : J → ℝ)|
        ≤ |affScoreAt S M v x| + |responseScore hS ν M z x * affScoreAt S M ζ x| +
          |(1 / 2) * affScoreAt S M ζ x ^ 2| + |covQ S ν θ (R z : J → ℝ) (ζ : J → ℝ)| +
          |(1 / 2) * covQ S ν θ (ζ : J → ℝ) (ζ : J → ℝ)| := by
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          exact abs_add_le _ _
      _ ≤ K₂ * ‖v‖ + K₂ * Λ * ‖z‖ * (K₂ * ‖ζ‖) + (1 / 2) * (K₂ * ‖ζ‖) ^ 2 +
          K₃ * (Λ * ‖z‖) * ‖ζ‖ + (1 / 2) * (K₃ * ‖ζ‖ * ‖ζ‖) := by
          gcongr
      _ = _ := by ring
  -- assemble
  have hφ : 13 * (K * ((Λ + 1) * ‖z‖)) ^ 3 + (K₂ * ‖v‖ + (K₂ * Λ * K₂ + K₃ * Λ) * ‖z‖ * ‖ζ‖ +
      (1 / 2) * (K₂ ^ 2 + K₃) * ‖ζ‖ ^ 2) ≤ densPeanoBound (Fintype.card J) B Λ Mb ε ‖z‖ := by
    unfold densPeanoBound
    rw [hK, hK₂, hK₃] at *
    have hζ0 : 0 ≤ ‖ζ‖ := norm_nonneg _
    have h2' : ((Fintype.card J : ℝ) * (Mb + B)) ^ 2 * Λ + 2 * ((Fintype.card J : ℝ) * B) ^ 2 * Λ
        = (Fintype.card J : ℝ) * (Mb + B) * Λ * ((Fintype.card J : ℝ) * (Mb + B)) +
          2 * ((Fintype.card J : ℝ) * B) ^ 2 * Λ := by ring
    have hzz : ‖ζ‖ ^ 2 ≤ ((B * ((Fintype.card J : ℝ) * (Mb + B)) ^ 2 * Λ ^ 3 + ε) * ‖z‖ ^ 2) ^ 2 :=
      pow_le_pow_left₀ hζ0 hζz 2
    have hm : ((Fintype.card J : ℝ) * (Mb + B) * Λ * ((Fintype.card J : ℝ) * (Mb + B)) +
        2 * ((Fintype.card J : ℝ) * B) ^ 2 * Λ) * ‖z‖ * ‖ζ‖ ≤
        ((Fintype.card J : ℝ) * (Mb + B) * Λ * ((Fintype.card J : ℝ) * (Mb + B)) +
        2 * ((Fintype.card J : ℝ) * B) ^ 2 * Λ) * ‖z‖ *
          ((B * ((Fintype.card J : ℝ) * (Mb + B)) ^ 2 * Λ ^ 3 + ε) * ‖z‖ ^ 2) := by
      gcongr
    have hv' : (Fintype.card J : ℝ) * (Mb + B) * ‖v‖ ≤
        (Fintype.card J : ℝ) * (Mb + B) * (ε * ‖z‖ ^ 2) := by gcongr
    have hq : (1 / 2) * (((Fintype.card J : ℝ) * (Mb + B)) ^ 2 +
        2 * ((Fintype.card J : ℝ) * B) ^ 2) * ‖ζ‖ ^ 2 ≤
        (1 / 2) * (((Fintype.card J : ℝ) * (Mb + B)) ^ 2 + 2 * ((Fintype.card J : ℝ) * B) ^ 2) *
          ((B * ((Fintype.card J : ℝ) * (Mb + B)) ^ 2 * Λ ^ 3 + ε) * ‖z‖ ^ 2) ^ 2 := by
      gcongr
    rw [h2']
    linarith
  calc |famDens S ν (θr (M + z)) x - famDens S ν (θr M) x * (1 + responseScore hS ν M z x +
        (1 / 2) * normalProj hS ν M
          ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)|
      = |(famDens S ν (θr (M + z)) x - famDens S ν (θ : J → ℝ) x *
          densTrunc S ν θ ((R z : J → ℝ) + (ζ : J → ℝ)) x) +
        famDens S ν (θ : J → ℝ) x * (densTrunc S ν θ ((R z : J → ℝ) + (ζ : J → ℝ)) x -
          (1 + responseScore hS ν M z x + (1 / 2) * normalProj hS ν M
            ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x))| := by
        rw [hθ]
        congr 1
        ring
    _ ≤ 13 * (K * ((Λ + 1) * ‖z‖)) ^ 3 * famDens S ν (θ : J → ℝ) x +
        famDens S ν (θ : J → ℝ) x * (K₂ * ‖v‖ + (K₂ * Λ * K₂ + K₃ * Λ) * ‖z‖ * ‖ζ‖ +
          (1 / 2) * (K₂ ^ 2 + K₃) * ‖ζ‖ ^ 2) := by
        refine (abs_add_le _ _).trans (add_le_add hI ?_)
        rw [abs_mul, abs_of_nonneg hq0]
        exact mul_le_mul_of_nonneg_left hII hq0
    _ = (13 * (K * ((Λ + 1) * ‖z‖)) ^ 3 + (K₂ * ‖v‖ + (K₂ * Λ * K₂ + K₃ * Λ) * ‖z‖ * ‖ζ‖ +
          (1 / 2) * (K₂ ^ 2 + K₃) * ‖ζ‖ ^ 2)) * famDens S ν (θ : J → ℝ) x := by ring
    _ ≤ densPeanoBound (Fintype.card J) B Λ Mb ε ‖z‖ * famDens S ν (θ : J → ℝ) x :=
        mul_le_mul_of_nonneg_right hφ hq0
    _ = densPeanoBound (Fintype.card J) B Λ Mb ε ‖z‖ * famDens S ν (θr M) x := by rw [hθ]

end Quantitative

section Uniform

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

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The inverse chart derivative is bounded on compact interior sets. -/
theorem exists_bound_inverse_of_isCompact {C : Set (J → ℝ)} (hC : IsCompact C)
    (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ M ∈ C, ‖(ContinuousLinearEquiv.symm (CDE (θr M)) : 𝕍 →L[ℝ] 𝕍)‖ ≤ Λ := by
  have hcont : Continuous (fun m : intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) ↦
      ‖(ContinuousLinearEquiv.symm (CDE ((relintChart hS ν).symm m)) : 𝕍 →L[ℝ] 𝕍)‖) :=
    ((continuous_chartDerivEquiv_symm measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS).comp (relintChart hS ν).symm.continuous).norm
  have hCs : IsCompact (Subtype.val ⁻¹' C :
      Set (intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr hCK]
    exact hC
  obtain ⟨Λ, hΛ⟩ := hCs.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max Λ 0, le_max_right _ _, fun M hM ↦ ?_⟩
  have h := hΛ ⟨M, hCK hM⟩ hM
  rw [relintChart_symm_apply] at h
  simp only [Real.norm_eq_abs, abs_norm] at h
  exact h.trans (le_max_left _ _)

set_option maxHeartbeats 800000 in
-- the assembly instantiates the quantitative bound with several uniform constants
/-- **The compact-uniform relative second-order expansion of the reconstruction density**: on
every compact convex set `C` of interior responses, for every `ε > 0` there is `δ > 0` such that
for all `M ∈ C`, all `z` with `M + z ∈ C` and `‖z‖ ≤ δ`, and every sample point `x`,
`|q_{M+z}(x) − q_M(x)(1 + ℓ_{M,z}(x) + ½ N_M(ℓ_{M,z}²)(x))| ≤ ε ‖z‖² q_M(x)`. -/
theorem famDens_response_peano_uniform {C : Set (J → ℝ)} (hC : IsCompact C) (hCc : Convex ℝ C)
    (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∀ ε > 0, ∃ δ > 0, ∀ M ∈ C, ∀ z : 𝕍, M + (z : J → ℝ) ∈ C → ‖z‖ ≤ δ → ∀ x,
      |famDens S ν (θr (M + z)) x - famDens S ν (θr M) x * (1 + responseScore hS ν M z x +
        (1 / 2) * normalProj hS ν M
          ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)| ≤
      ε * ‖z‖ ^ 2 * famDens S ν (θr M) x := by
  intro ε hε
  -- uniform constants
  choose Mj hMj using fun j ↦ (hS j).2
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, |S j x| ≤ B :=
    ⟨∑ j, |Mj j|, Finset.sum_nonneg fun j _ ↦ abs_nonneg _, fun j x ↦
      (hMj j x).trans ((le_abs_self _).trans (Finset.single_le_sum
        (f := fun j ↦ |Mj j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ j)))⟩
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_bound_inverse_of_isCompact hS ν hC hCK
  obtain ⟨Mb₀, hMb₀⟩ := isBounded_iff_forall_norm_le.1 hC.isBounded
  obtain ⟨Mb, hMb0, hMb⟩ : ∃ Mb : ℝ, 0 ≤ Mb ∧ ∀ M ∈ C, ‖M‖ ≤ Mb :=
    ⟨max Mb₀ 0, le_max_right _ _, fun M hM ↦ (hMb₀ M hM).trans (le_max_left _ _)⟩
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (Fintype.card J : ℝ) := ⟨_, rfl⟩
  have hn0 : 0 ≤ n := by rw [hn]; positivity
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = densPeanoLead n B Λ Mb := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; unfold densPeanoLead; positivity
  -- the direction picture of `C`
  obtain ⟨C', hC'def⟩ : ∃ C' : Set 𝕍, C' = {z : 𝕍 | m₀ + (z : J → ℝ) ∈ C} := ⟨_, rfl⟩
  have hC'c : IsCompact C' := hC'def ▸ isCompact_preimage_add_mean ν hC
  have hC'v : Convex ℝ C' := hC'def ▸ convex_preimage_add_mean ν hCc
  have hC'K : ∀ z ∈ C', m₀ + (z : J → ℝ) ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) :=
    fun z hz ↦ hCK (by rw [hC'def] at hz; exact hz)
  -- the uniform natural-coordinate remainder
  obtain ⟨ε₁, hε₁0, hε₁1, hε₁⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ n * (Mb + B) * ε₁ ≤ ε / 2 :=
    ⟨min 1 (ε / 2 / (n * (Mb + B) + 1)), lt_min one_pos (by positivity), min_le_left _ _, by
      calc n * (Mb + B) * min 1 (ε / 2 / (n * (Mb + B) + 1))
          ≤ n * (Mb + B) * (ε / 2 / (n * (Mb + B) + 1)) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
        _ ≤ (n * (Mb + B) + 1) * (ε / 2 / (n * (Mb + B) + 1)) := by gcongr; linarith
        _ = ε / 2 := mul_div_cancel₀ _ (by positivity)⟩
  obtain ⟨δ₁, hδ₁, hθu⟩ := uniform_responseTheta_peano hS ν hC'c hC'v hC'K ε₁ hε₁0
  -- the smallness thresholds
  obtain ⟨δ, hδ0, hδ₁', hδ1, hδD, hδz1, hδz2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₁ ∧ δ ≤ 1 ∧
      δ ≤ ε / 2 / (D + 1) ∧ δ ≤ 1 / (B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + 1) ∧
      δ ≤ 1 / (4 * (n * B * (Λ + 1)) + 1) :=
    ⟨min δ₁ (min 1 (min (ε / 2 / (D + 1)) (min (1 / (B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + 1))
      (1 / (4 * (n * B * (Λ + 1)) + 1))))),
      lt_min hδ₁ (lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) (by positivity)))),
      min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))),
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_right _ _)))⟩
  refine ⟨δ, hδ0, fun M hM z hMz hz x ↦ ?_⟩
  have hrel := hCK hM
  -- the natural-coordinate remainder at `M`, from the uniform statement at `z₀ = M − m₀`
  have hmem : M - m₀ ∈ 𝕍 := sub_mem_dirSpan_of_mem_momentBody measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS (intrinsicInterior_subset hrel)
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : 𝕍, (z₀ : J → ℝ) = M - m₀ := ⟨⟨M - m₀, hmem⟩, rfl⟩
  have hz₀M : m₀ + (z₀ : J → ℝ) = M := by rw [hz₀, add_sub_cancel]
  have hz₀' : m₀ + ((z₀ + z : 𝕍) : J → ℝ) = M + (z : J → ℝ) := by
    rw [Submodule.coe_add, hz₀]
    abel
  have hz₀C : z₀ ∈ C' := by
    rw [hC'def]
    change m₀ + (z₀ : J → ℝ) ∈ C
    rw [hz₀M]
    exact hM
  have hz₀'C : z₀ + z ∈ C' := by
    rw [hC'def]
    change m₀ + ((z₀ + z : 𝕍) : J → ℝ) ∈ C
    rw [hz₀']
    exact hMz
  have hv := hθu z₀ hz₀C (z₀ + z) hz₀'C (by rw [add_sub_cancel_left]; exact hz.trans hδ₁')
  rw [add_sub_cancel_left, hz₀', hz₀M] at hv
  simp only [ContinuousLinearEquiv.coe_coe] at hv
  -- the quantitative bound
  have hz1 : (B * ((Fintype.card J : ℝ) * (Mb + B)) ^ 2 * Λ ^ 3 + ε₁) * ‖z‖ ≤ 1 := by
    rw [← hn]
    have hpos : 0 < B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + 1 := by positivity
    calc (B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + ε₁) * ‖z‖
        ≤ (B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + 1) * δ := by gcongr
      _ ≤ (B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + 1) * (1 / (B * (n * (Mb + B)) ^ 2 * Λ ^ 3 + 1)) := by
          gcongr
      _ = 1 := mul_one_div_cancel hpos.ne'
  have hz2 : 4 * ((Fintype.card J : ℝ) * B * (Λ + 1)) * ‖z‖ ≤ 1 := by
    rw [← hn]
    have hpos : 0 < 4 * (n * B * (Λ + 1)) + 1 := by positivity
    calc 4 * (n * B * (Λ + 1)) * ‖z‖ ≤ (4 * (n * B * (Λ + 1)) + 1) * δ := by
          gcongr
          linarith
      _ ≤ (4 * (n * B * (Λ + 1)) + 1) * (1 / (4 * (n * B * (Λ + 1)) + 1)) := by gcongr
      _ = 1 := mul_one_div_cancel hpos.ne'
  have h := abs_famDens_response_remainder_le hS ν hrel hB0 hB (hΛ M hM) (hMb M hM) z hv hz1 hz2 x
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (famDens_nonneg hS ν _ x))
  -- the remainder coefficient is at most `ε ‖z‖²`
  have hb := densPeanoBound_le hn0 hB0 hΛ0 hMb0 hε₁0.le hε₁1 (norm_nonneg z) (hz.trans hδ1)
  rw [← hn]
  refine hb.trans ?_
  rw [← hD]
  have hDz : D * ‖z‖ ≤ ε / 2 := by
    calc D * ‖z‖ ≤ (D + 1) * δ := by gcongr; linarith
      _ ≤ (D + 1) * (ε / 2 / (D + 1)) := by gcongr
      _ = ε / 2 := mul_div_cancel₀ _ (by positivity)
  have : D * ‖z‖ + n * (Mb + B) * ε₁ ≤ ε := by linarith
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

/-- **The compact-uniform total-variation second-order expansion of the reconstruction**: on
every compact convex set `C` of interior responses, for every `ε > 0` there is `δ > 0` with
`∫ |q_{M+z} − q_M − q_M ℓ_{M,z} − ½ q_M N_M(ℓ_{M,z}²)| dν ≤ ε ‖z‖²` for all `M ∈ C` and `z` with
`M + z ∈ C`, `‖z‖ ≤ δ`. -/
theorem integral_abs_famDens_response_peano_uniform {C : Set (J → ℝ)} (hC : IsCompact C)
    (hCc : Convex ℝ C) (hCK : C ⊆ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) :
    ∀ ε > 0, ∃ δ > 0, ∀ M ∈ C, ∀ z : 𝕍, M + (z : J → ℝ) ∈ C → ‖z‖ ≤ δ →
      ∫ x, |famDens S ν (θr (M + z)) x - famDens S ν (θr M) x * (1 + responseScore hS ν M z x +
        (1 / 2) * normalProj hS ν M
          ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)| ∂ν ≤
      ε * ‖z‖ ^ 2 := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := famDens_response_peano_uniform hS ν hC hCc hCK ε hε
  refine ⟨δ, hδ, fun M hM z hMz hz ↦ ?_⟩
  calc ∫ x, |famDens S ν (θr (M + z)) x - famDens S ν (θr M) x * (1 + responseScore hS ν M z x +
        (1 / 2) * normalProj hS ν M
          ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)| ∂ν
      ≤ ∫ x, ε * ‖z‖ ^ 2 * famDens S ν (θr M) x ∂ν := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x ↦ abs_nonneg _)
          ((integrable_famDens hS ν _).const_mul _) (Eventually.of_forall fun x ↦ h M hM z hMz hz x)
    _ = ε * ‖z‖ ^ 2 := by rw [integral_const_mul, integral_famDens hS ν, mul_one]

end Uniform

end Laplace.Multi
