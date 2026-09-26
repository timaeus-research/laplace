/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.DensityPeanoAlgebra

/-!
# The pointwise-uniform and total-variation Peano expansions of the reconstruction density

For an interior response `M` there is a function `φ = o(‖z‖²)` such that, for `z` near `0` and
**every** `x`,

`|q_{M+z}(x) − q_M(x) (1 + ℓ_{M,z}(x) + ½ N_M(ℓ_{M,z}²)(x))| ≤ φ(z) q_M(x)`

(`famDens_response_peano`): the relative second-order remainder of the reconstructed law is
uniformly `o(‖z‖²)`. Integrating gives the total-variation Peano expansion

`∫ |q_{M+z} − q_M − q_M ℓ_{M,z} − ½ q_M N_M(ℓ_{M,z}²)| dν = o(‖z‖²)`

(`isLittleO_integral_famDens_response_peano`): the score is the first derivative of the
reconstructed law and the normalised squared score is its second derivative, as signed measures.

The proof composes the second-order expansion of the natural coordinate (`ThetaPeano`) with the
pointwise second-order bound in natural coordinates (`DensitySecondOrder`), using the splitting of
the truncation under `η = Rz + ζ` (`DensityPeanoAlgebra`).
-/

open MeasureTheory Filter Topology Set Asymptotics

namespace Laplace.Multi

section Peano

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}

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

include hS

omit [Nonempty X] [Nonempty J] in
/-- The family density is bounded. -/
theorem bdd_famDens {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j x, |S j x| ≤ B) (θ : J → ℝ) :
    Bdd (famDens S ν θ) := by
  refine ⟨measurable_famDens hS ν θ, Real.exp ((Fintype.card J : ℝ) * B * ‖θ‖) / famZ S ν θ,
    fun x ↦ ?_⟩
  unfold famDens
  rw [abs_div, abs_of_pos (famZ_pos hS ν θ), abs_of_pos (famWeight_pos θ x)]
  refine div_le_div_of_nonneg_right ?_ (famZ_pos hS ν θ).le
  unfold famWeight
  exact Real.exp_le_exp.2 (by linarith [abs_le.1 (abs_dirLoss_le_card_mul hB0 hB θ x)])

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

set_option maxHeartbeats 2400000 in
-- the proof composes three explicit bounds (natural-coordinate Peano, cubic density remainder,
-- truncation splitting) in one declaration and exceeds the default budget
/-- **The pointwise-uniform Peano expansion of the reconstruction density.** -/
theorem famDens_response_peano :
    ∃ φ : 𝕍 → ℝ, (φ =o[𝓝 0] fun z ↦ ‖z‖ ^ 2) ∧ ∀ᶠ z : 𝕍 in 𝓝 0, ∀ x,
      |famDens S ν (θr (M + z)) x - famDens S ν (θr M) x * (1 + responseScore hS ν M z x +
        (1 / 2) * normalProj hS ν M
          ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)| ≤
      φ z * famDens S ν (θr M) x := by
  -- constants
  choose Mj hMj using fun j ↦ (hS j).2
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, |S j x| ≤ B :=
    ⟨∑ j, |Mj j|, Finset.sum_nonneg fun j _ ↦ abs_nonneg _, fun j x ↦
      (hMj j x).trans ((le_abs_self _).trans (Finset.single_le_sum
        (f := fun j ↦ |Mj j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ j)))⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (Fintype.card J : ℝ) * B := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = (Fintype.card J : ℝ) * (‖M‖ + B) := ⟨_, rfl⟩
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  obtain ⟨K₃, hK₃⟩ : ∃ K₃ : ℝ, K₃ = 2 * K ^ 2 := ⟨_, rfl⟩
  have hK₃0 : 0 ≤ K₃ := by rw [hK₃]; positivity
  -- the base point
  obtain ⟨θ, hθ⟩ : ∃ θ : 𝕍, θ = θr M := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : 𝕍 →L[ℝ] 𝕍, R = (ContinuousLinearEquiv.symm (CDE θ) : 𝕍 →L[ℝ] 𝕍) :=
    ⟨_, rfl⟩
  have hR0 : 0 ≤ ‖R‖ := norm_nonneg _
  have hmean : famMean S ν θ = M := by
    rw [hθ, famMean_eq_meanMap hS ν]
    exact meanMap_responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS hrel
  -- the response score as an affine score
  have hscore : ∀ (z : 𝕍) (x : X), responseScore hS ν M z x = affScoreAt S M (R z) x := by
    intro z x
    rw [responseScore_apply, hR, hθ]
    rfl
  have hRz : ∀ z : 𝕍, ‖(R z : J → ℝ)‖ ≤ ‖R‖ * ‖z‖ := fun z ↦ by
    rw [Submodule.norm_coe]
    exact R.le_opNorm z
  have hscore_bd : ∀ (z : 𝕍) (x : X), |responseScore hS ν M z x| ≤ K₂ * ‖R‖ * ‖z‖ := by
    intro z x
    rw [hscore, hK₂]
    refine (abs_affScoreAt_le hB0 hB M _ x).trans ?_
    calc (Fintype.card J : ℝ) * (‖M‖ + B) * ‖(R z : J → ℝ)‖
        ≤ (Fintype.card J : ℝ) * (‖M‖ + B) * (‖R‖ * ‖z‖) :=
          mul_le_mul_of_nonneg_left (hRz z) (by positivity)
      _ = (Fintype.card J : ℝ) * (‖M‖ + B) * ‖R‖ * ‖z‖ := by ring
  -- the quadratic term of the natural coordinate
  obtain ⟨c, hc⟩ : ∃ c : 𝕍 → 𝕍, c = fun z ↦ thirdOp hS ν θ (ContinuousLinearEquiv.symm (CDE θ) z)
    (ContinuousLinearEquiv.symm (CDE θ) z) := ⟨_, rfl⟩
  have hc_eq : ∀ z, c z = ⟨respCov hS ν M (fun x ↦ responseScore hS ν M z x *
      responseScore hS ν M z x), respCov_mem_dirSpan hS ν
        ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z))⟩ := fun z ↦ by
    rw [hc, hθ]
    exact responseTheta_peano_quadratic hS ν hrel z
  have hc_bd : ∀ z, ‖c z‖ ≤ 2 * B * (K₂ * ‖R‖ * ‖z‖) ^ 2 := fun z ↦ by
    rw [hc_eq, ← Submodule.norm_coe, Submodule.coe_mk]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j ↦ ?_
    rw [Real.norm_eq_abs]
    unfold respCov
    have := isProbabilityMeasure_family_responseTheta hS ν (M := M)
    refine abs_lawCov_le _ (hB j) fun x ↦ ?_
    rw [abs_mul, sq]
    exact mul_le_mul (hscore_bd z x) (hscore_bd z x) (abs_nonneg _)
      (mul_nonneg (mul_nonneg hK₂0 hR0) (norm_nonneg _))
  -- the regression projection as an affine score of `R c`
  have hreg : ∀ (z : 𝕍) (x : X), regProj hS ν M
      ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x =
      affScoreAt S M (R (c z)) x := fun z x ↦ by
    unfold regProj
    rw [hc_eq, responseScore_apply, hR, hθ]
    rfl
  -- the second moment of the score
  have hvar : ∀ z : 𝕍, covQ S ν θ (R z : J → ℝ) (R z : J → ℝ) =
      ∫ y, responseScore hS ν M z y * responseScore hS ν M z y ∂(Pfam (θr M)) := fun z ↦ by
    rw [covQ_self_eq hS ν, hmean, integral_famDens_mul hS ν, ← hθ]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    beta_reduce
    rw [hscore]
    ring
  -- the Peano expansion of the natural coordinate
  obtain ⟨v, hv⟩ : ∃ v : 𝕍 → 𝕍, v = fun z : 𝕍 ↦ θr (M + z) - θ - R z - (1 / 2 : ℝ) • (-(R (c z))) :=
    ⟨_, rfl⟩
  have hvo : v =o[𝓝 0] fun z : 𝕍 ↦ ‖z‖ ^ 2 := by
    have h := isLittleO_responseTheta_peano hS ν hrel
    refine h.congr_left fun z ↦ ?_
    rw [hv, hR, hc, hθ]
    rfl
  obtain ⟨ζ, hζ⟩ : ∃ ζ : 𝕍 → 𝕍, ζ = fun z : 𝕍 ↦ -(1 / 2 : ℝ) • R (c z) + v z := ⟨_, rfl⟩
  have hη : ∀ z : 𝕍, (θr (M + z) : J → ℝ) - (θ : J → ℝ) = (R z : J → ℝ) + (ζ z : J → ℝ) :=
    fun z ↦ by
    rw [hζ, hv]
    simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_neg]
    module
  have hζ_bd : ∀ z : 𝕍, ‖ζ z‖ ≤ 1 / 2 * ‖R‖ * (2 * B * (K₂ * ‖R‖ * ‖z‖) ^ 2) + ‖v z‖ := fun z ↦ by
    rw [hζ]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc 1 / 2 * ‖R (c z)‖ ≤ 1 / 2 * (‖R‖ * (2 * B * (K₂ * ‖R‖ * ‖z‖) ^ 2)) := by
          gcongr
          exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hc_bd z) hR0)
      _ = 1 / 2 * ‖R‖ * (2 * B * (K₂ * ‖R‖ * ‖z‖) ^ 2) := by ring
  -- the truncation at `η = Rz + ζ`: the exact identity
  have hsplit : ∀ (z : 𝕍) (x : X), densTrunc S ν θ ((R z : J → ℝ) + (ζ z : J → ℝ)) x -
      (1 + responseScore hS ν M z x + (1 / 2) * normalProj hS ν M
        ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x) =
      affScoreAt S M (v z) x + responseScore hS ν M z x * affScoreAt S M (ζ z) x +
        (1 / 2) * affScoreAt S M (ζ z) x ^ 2 - covQ S ν θ (R z : J → ℝ) (ζ z : J → ℝ) -
        (1 / 2) * covQ S ν θ (ζ z : J → ℝ) (ζ z : J → ℝ) := fun z x ↦ by
    rw [densTrunc_add hS ν, hmean, hvar, ← hscore]
    unfold normalProj
    rw [hreg]
    have e : affScoreAt S M (ζ z) x = -(1 / 2) * affScoreAt S M (R (c z)) x +
        affScoreAt S M (v z) x := by
      rw [hζ]
      simp only [Submodule.coe_add, Submodule.coe_smul]
      rw [affScoreAt_add, affScoreAt_smul]
    rw [e]
    ring
  -- the remainder function
  obtain ⟨φ, hφ⟩ : ∃ φ : 𝕍 → ℝ, φ = fun z : 𝕍 ↦
      13 * (K * ((‖R‖ + 1) * ‖z‖)) ^ 3 + K₂ * ‖v z‖ + (K₂ * ‖R‖ * K₂ + K₃ * ‖R‖) * ‖z‖ * ‖ζ z‖ +
        (1 / 2) * (K₂ ^ 2 + K₃) * ‖ζ z‖ ^ 2 := ⟨_, rfl⟩
  refine ⟨φ, ?_, ?_⟩
  · -- `φ = o(‖z‖²)`
    have hζO : ζ =O[𝓝 0] fun z : 𝕍 ↦ ‖z‖ ^ 2 := by
      have h1 : (fun z : 𝕍 ↦ -(1 / 2 : ℝ) • R (c z)) =O[𝓝 0] fun z ↦ ‖z‖ ^ 2 := by
        refine IsBigO.of_bound (1 / 2 * ‖R‖ * (2 * B * (K₂ * ‖R‖) ^ 2)) (Eventually.of_forall
          fun z ↦ ?_)
        rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
          Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        calc 1 / 2 * ‖R (c z)‖ ≤ 1 / 2 * (‖R‖ * (2 * B * (K₂ * ‖R‖ * ‖z‖) ^ 2)) := by
              gcongr
              exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hc_bd z) hR0)
          _ = 1 / 2 * ‖R‖ * (2 * B * (K₂ * ‖R‖) ^ 2) * ‖z‖ ^ 2 := by ring
      have := h1.add hvo.isBigO
      rw [hζ]
      exact this
    have hz3 : (fun z : 𝕍 ↦ ‖z‖ ^ 3) =o[𝓝 0] fun z ↦ ‖z‖ ^ 2 :=
      isLittleO_norm_pow_norm_pow (by norm_num)
    have hone : (fun z : 𝕍 ↦ ‖z‖ ^ 2) =o[𝓝 0] fun _ ↦ (1 : ℝ) := by
      rw [isLittleO_one_iff]
      have := (tendsto_norm_zero (E := 𝕍)).pow 2
      simpa using this
    have hzζ : (fun z : 𝕍 ↦ ‖z‖ * ‖ζ z‖) =o[𝓝 0] fun z ↦ ‖z‖ ^ 2 := by
      have h1 : (fun z : 𝕍 ↦ ‖z‖) =o[𝓝 0] fun _ ↦ (1 : ℝ) := by
        rw [isLittleO_one_iff]
        exact tendsto_norm_zero
      have h2 := h1.mul_isBigO hζO.norm_left
      simpa using h2
    have hζ2 : (fun z : 𝕍 ↦ ‖ζ z‖ ^ 2) =o[𝓝 0] fun z ↦ ‖z‖ ^ 2 := by
      have h1 : (fun z : 𝕍 ↦ ‖ζ z‖) =o[𝓝 0] fun _ ↦ (1 : ℝ) := hζO.norm_left.trans_isLittleO hone
      have h2 := h1.mul_isBigO hζO.norm_left
      simpa [sq] using h2
    rw [hφ]
    have t1 : (fun z : 𝕍 ↦ 13 * (K * ((‖R‖ + 1) * ‖z‖)) ^ 3) =o[𝓝 0] fun z ↦ ‖z‖ ^ 2 := by
      refine (hz3.const_mul_left (13 * (K * (‖R‖ + 1)) ^ 3)).congr_left fun z ↦ ?_
      ring
    have t2 : (fun z : 𝕍 ↦ K₂ * ‖v z‖) =o[𝓝 0] fun z ↦ ‖z‖ ^ 2 :=
      hvo.norm_left.const_mul_left K₂
    have t3 : (fun z : 𝕍 ↦ (K₂ * ‖R‖ * K₂ + K₃ * ‖R‖) * ‖z‖ * ‖ζ z‖) =o[𝓝 0]
        fun z ↦ ‖z‖ ^ 2 := by
      refine (hzζ.const_mul_left (K₂ * ‖R‖ * K₂ + K₃ * ‖R‖)).congr_left fun z ↦ ?_
      ring
    have t4 : (fun z : 𝕍 ↦ (1 / 2) * (K₂ ^ 2 + K₃) * ‖ζ z‖ ^ 2) =o[𝓝 0] fun z ↦ ‖z‖ ^ 2 :=
      hζ2.const_mul_left _
    exact ((t1.add t2).add t3).add t4
  · -- the eventual pointwise bound
    have hpos : 0 < B * K₂ ^ 2 * ‖R‖ ^ 3 + 1 := by positivity
    obtain ⟨δ, hδ0, hδ2, hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / (4 * (K * (‖R‖ + 1)) + 1) ∧
        δ ≤ 1 / (B * K₂ ^ 2 * ‖R‖ ^ 3 + 1) :=
      ⟨min (1 / (4 * (K * (‖R‖ + 1)) + 1)) (1 / (B * K₂ ^ 2 * ‖R‖ ^ 3 + 1)),
        lt_min (by positivity) (by positivity), min_le_left _ _, min_le_right _ _⟩
    have hev : ∀ᶠ z : 𝕍 in 𝓝 0, ‖z‖ ≤ δ ∧ ‖v z‖ ≤ ‖z‖ ^ 2 := by
      refine (Metric.eventually_nhds_iff.2 ⟨δ, hδ0, fun z hz ↦ ?_⟩).and ?_
      · rw [dist_zero_right] at hz
        exact hz.le
      · filter_upwards [hvo.def one_pos] with z hz
        simpa using hz
    filter_upwards [hev] with z ⟨hz, hvz⟩ x
    have hq0 := famDens_nonneg hS ν (θ : J → ℝ) x
    -- the natural-coordinate increment and its size
    obtain ⟨η, hηdef⟩ : ∃ η : J → ℝ, η = (θr (M + z) : J → ℝ) - (θ : J → ℝ) := ⟨_, rfl⟩
    have hCz : (B * K₂ ^ 2 * ‖R‖ ^ 3 + 1) * ‖z‖ ≤ 1 := by
      calc (B * K₂ ^ 2 * ‖R‖ ^ 3 + 1) * ‖z‖ ≤ (B * K₂ ^ 2 * ‖R‖ ^ 3 + 1) * δ := by gcongr
        _ ≤ (B * K₂ ^ 2 * ‖R‖ ^ 3 + 1) * (1 / (B * K₂ ^ 2 * ‖R‖ ^ 3 + 1)) := by gcongr
        _ = 1 := mul_one_div_cancel hpos.ne'
    have hζz : ‖ζ z‖ ≤ (B * K₂ ^ 2 * ‖R‖ ^ 3 + 1) * ‖z‖ ^ 2 := by
      refine (hζ_bd z).trans ?_
      calc 1 / 2 * ‖R‖ * (2 * B * (K₂ * ‖R‖ * ‖z‖) ^ 2) + ‖v z‖
          ≤ B * K₂ ^ 2 * ‖R‖ ^ 3 * ‖z‖ ^ 2 + ‖z‖ ^ 2 := add_le_add (le_of_eq (by ring)) hvz
        _ = (B * K₂ ^ 2 * ‖R‖ ^ 3 + 1) * ‖z‖ ^ 2 := by ring
    have hζz' : ‖ζ z‖ ≤ ‖z‖ := by
      calc ‖ζ z‖ ≤ (B * K₂ ^ 2 * ‖R‖ ^ 3 + 1) * ‖z‖ ^ 2 := hζz
        _ = ((B * K₂ ^ 2 * ‖R‖ ^ 3 + 1) * ‖z‖) * ‖z‖ := by ring
        _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hCz (norm_nonneg _)
        _ = ‖z‖ := one_mul _
    have hηz : ‖η‖ ≤ (‖R‖ + 1) * ‖z‖ := by
      rw [hηdef, hη z]
      calc ‖(R z : J → ℝ) + (ζ z : J → ℝ)‖ ≤ ‖(R z : J → ℝ)‖ + ‖(ζ z : J → ℝ)‖ := norm_add_le _ _
        _ ≤ ‖R‖ * ‖z‖ + ‖z‖ := by
            refine add_le_add (hRz z) ?_
            rw [Submodule.norm_coe]
            exact hζz'
        _ = (‖R‖ + 1) * ‖z‖ := by ring
    have hKη : (Fintype.card J : ℝ) * B * ‖η‖ ≤ 1 / 4 := by
      rw [← hK]
      calc K * ‖η‖ ≤ K * ((‖R‖ + 1) * ‖z‖) := mul_le_mul_of_nonneg_left hηz hK0
        _ ≤ K * ((‖R‖ + 1) * δ) := by gcongr
        _ ≤ K * ((‖R‖ + 1) * (1 / (4 * (K * (‖R‖ + 1)) + 1))) := by gcongr
        _ ≤ 1 / 4 := by
            rw [← mul_assoc, mul_one_div, div_le_iff₀ (by positivity)]
            nlinarith [mul_nonneg hK0 (by positivity : (0 : ℝ) ≤ ‖R‖ + 1)]
    -- the two remainders
    have hθη : (θ : J → ℝ) + η = (θr (M + z) : J → ℝ) := by rw [hηdef, add_sub_cancel]
    have hmain := abs_famDens_second_remainder_le hS ν hB0 hB (θ : J → ℝ) η hKη x
    rw [hθη] at hmain
    have hI : |famDens S ν (θr (M + z)) x - famDens S ν (θ : J → ℝ) x *
        densTrunc S ν θ ((R z : J → ℝ) + (ζ z : J → ℝ)) x| ≤
        13 * (K * ((‖R‖ + 1) * ‖z‖)) ^ 3 * famDens S ν (θ : J → ℝ) x := by
      rw [← hη z, ← hηdef]
      refine hmain.trans (mul_le_mul_of_nonneg_right ?_ hq0)
      rw [← hK]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ 3) (by norm_num)
      exact mul_le_mul_of_nonneg_left hηz hK0
    have hII : |densTrunc S ν θ ((R z : J → ℝ) + (ζ z : J → ℝ)) x -
        (1 + responseScore hS ν M z x + (1 / 2) * normalProj hS ν M
          ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)| ≤
        K₂ * ‖v z‖ + (K₂ * ‖R‖ * K₂ + K₃ * ‖R‖) * ‖z‖ * ‖ζ z‖ +
          (1 / 2) * (K₂ ^ 2 + K₃) * ‖ζ z‖ ^ 2 := by
      rw [hsplit]
      have hA : ∀ w : 𝕍, |affScoreAt S M (w : J → ℝ) x| ≤ K₂ * ‖w‖ := fun w ↦ by
        rw [hK₂, ← Submodule.norm_coe]
        exact abs_affScoreAt_le hB0 hB M _ x
      have hC : ∀ v w : 𝕍, |covQ S ν θ (v : J → ℝ) (w : J → ℝ)| ≤ K₃ * ‖v‖ * ‖w‖ := fun v w ↦ by
        rw [hK₃, hK, ← Submodule.norm_coe v, ← Submodule.norm_coe w]
        exact abs_covQ_le hS ν hB0 hB _ _ _
      have h1 := hA (v z)
      have h2 : |responseScore hS ν M z x * affScoreAt S M (ζ z) x| ≤
          K₂ * ‖R‖ * ‖z‖ * (K₂ * ‖ζ z‖) := by
        rw [abs_mul]
        exact mul_le_mul (hscore_bd z x) (hA (ζ z)) (abs_nonneg _) (by positivity)
      have h3 : |(1 / 2) * affScoreAt S M (ζ z) x ^ 2| ≤ (1 / 2) * (K₂ * ‖ζ z‖) ^ 2 := by
        rw [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hA (ζ z)) 2)
          (by norm_num)
      have h4 : |covQ S ν θ (R z : J → ℝ) (ζ z : J → ℝ)| ≤ K₃ * (‖R‖ * ‖z‖) * ‖ζ z‖ := by
        refine (hC (R z) (ζ z)).trans ?_
        gcongr
        exact R.le_opNorm z
      have h5 : |(1 / 2) * covQ S ν θ (ζ z : J → ℝ) (ζ z : J → ℝ)| ≤
          (1 / 2) * (K₃ * ‖ζ z‖ * ‖ζ z‖) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact mul_le_mul_of_nonneg_left (hC (ζ z) (ζ z)) (by norm_num)
      calc |affScoreAt S M (v z) x + responseScore hS ν M z x * affScoreAt S M (ζ z) x +
            (1 / 2) * affScoreAt S M (ζ z) x ^ 2 - covQ S ν θ (R z : J → ℝ) (ζ z : J → ℝ) -
            (1 / 2) * covQ S ν θ (ζ z : J → ℝ) (ζ z : J → ℝ)|
          ≤ |affScoreAt S M (v z) x| + |responseScore hS ν M z x * affScoreAt S M (ζ z) x| +
            |(1 / 2) * affScoreAt S M (ζ z) x ^ 2| + |covQ S ν θ (R z : J → ℝ) (ζ z : J → ℝ)| +
            |(1 / 2) * covQ S ν θ (ζ z : J → ℝ) (ζ z : J → ℝ)| := by
            refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
            refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
            refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
            exact abs_add_le _ _
        _ ≤ K₂ * ‖v z‖ + K₂ * ‖R‖ * ‖z‖ * (K₂ * ‖ζ z‖) + (1 / 2) * (K₂ * ‖ζ z‖) ^ 2 +
            K₃ * (‖R‖ * ‖z‖) * ‖ζ z‖ + (1 / 2) * (K₃ * ‖ζ z‖ * ‖ζ z‖) := by
            gcongr
        _ = _ := by ring
    -- assemble
    calc |famDens S ν (θr (M + z)) x - famDens S ν (θr M) x * (1 + responseScore hS ν M z x +
          (1 / 2) * normalProj hS ν M
            ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)|
        = |(famDens S ν (θr (M + z)) x - famDens S ν (θ : J → ℝ) x *
            densTrunc S ν θ ((R z : J → ℝ) + (ζ z : J → ℝ)) x) +
          famDens S ν (θ : J → ℝ) x * (densTrunc S ν θ ((R z : J → ℝ) + (ζ z : J → ℝ)) x -
            (1 + responseScore hS ν M z x + (1 / 2) * normalProj hS ν M
              ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x))| := by
          rw [hθ]
          congr 1
          ring
      _ ≤ 13 * (K * ((‖R‖ + 1) * ‖z‖)) ^ 3 * famDens S ν (θ : J → ℝ) x +
          famDens S ν (θ : J → ℝ) x * (K₂ * ‖v z‖ + (K₂ * ‖R‖ * K₂ + K₃ * ‖R‖) * ‖z‖ * ‖ζ z‖ +
            (1 / 2) * (K₂ ^ 2 + K₃) * ‖ζ z‖ ^ 2) := by
          refine (abs_add_le _ _).trans (add_le_add hI ?_)
          rw [abs_mul, abs_of_nonneg hq0]
          exact mul_le_mul_of_nonneg_left hII hq0
      _ = φ z * famDens S ν (θr M) x := by
          rw [hφ, hθ]
          ring

/-- **The total-variation Peano expansion of the reconstruction density**:
`∫ |q_{M+z} − q_M − q_M ℓ_{M,z} − ½ q_M N_M(ℓ_{M,z}²)| dν = o(‖z‖²)`. -/
theorem isLittleO_integral_famDens_response_peano :
    (fun z : 𝕍 ↦ ∫ x, |famDens S ν (θr (M + z)) x - famDens S ν (θr M) x *
      (1 + responseScore hS ν M z x + (1 / 2) * normalProj hS ν M
        ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)| ∂ν)
      =o[𝓝 0] fun z ↦ ‖z‖ ^ 2 := by
  obtain ⟨φ, hφ, hev⟩ := famDens_response_peano hS ν hrel
  refine IsBigO.trans_isLittleO ?_ hφ
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hev] with z hz
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun x ↦ abs_nonneg _)]
  refine le_trans ?_ (le_abs_self _)
  calc ∫ x, |famDens S ν (θr (M + z)) x - famDens S ν (θr M) x *
        (1 + responseScore hS ν M z x + (1 / 2) * normalProj hS ν M
          ((bdd_responseScore hS ν M z).mul (bdd_responseScore hS ν M z)) x)| ∂ν
      ≤ ∫ x, φ z * famDens S ν (θr M) x ∂ν := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x ↦ abs_nonneg _)
          ((integrable_famDens hS ν _).const_mul _) (Eventually.of_forall fun x ↦ hz x)
    _ = φ z := by rw [integral_const_mul, integral_famDens hS ν, mul_one]

end Peano

end Laplace.Multi
