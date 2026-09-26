/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.SmoothChart
import Laplace.Multi.NormalForm

/-!
# The invisible tower: the reconstruction is a `C^∞` curve in `L¹` and every higher
derivative along the atlas is invisible

The weighted family weight `θ ↦ [g e^{−⟨θ,S⟩}] ∈ L¹(ν)` is `C^∞` (`contDiff_weightL1`): its
derivative in direction `η` is `−[g ⟨η,S⟩ e^{−⟨θ,S⟩}]`, again a weighted weight, with a
quadratic remainder bound from `|e^{−u} − 1 + u| ≤ u²`. Hence the reconstruction density
`θ ↦ [q_θ] = Z(θ)⁻¹ [e^{−⟨θ,S⟩}]` is `C^∞` into `L¹` (`contDiff_densL1`), and along the atlas the
curve `p(s) = [q_{M_s}]` is `C^∞` wherever the atlas is interior
(`contDiffOn_reconstructionL1_atlas`). Since the mass and moment functionals are continuous
linear and `(m ∘ p)(s) = M_s` is affine, **every derivative of order `≥ 2` of the reconstruction
along the atlas has zero mass and zero
feature moments** (`invisible_tower`), while the first derivative carries exactly the atlas
velocity `M − m₀` (`momentL1_iteratedDerivWithin_one`). This is the all-orders form of "invisible
bending".
-/

open MeasureTheory Filter Topology Set Asymptotics
open scoped ContDiff

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

section Weight

/-- The weighted family weight as an `L¹` element: `θ ↦ [g e^{−⟨θ,S⟩}]`. -/
noncomputable def weightL1 {g : X → ℝ} (hg : Bdd g) (θ : J → ℝ) : X →₁[ν] ℝ :=
  (integrable_mul_famWeight hS ν hg θ).toL1 (fun x ↦ g x * famWeight S θ x)

/-- The candidate derivative of `weightL1`: `η ↦ −Σ_j η_j [g S_j e^{−⟨θ,S⟩}]`. -/
noncomputable def weightDeriv {g : X → ℝ} (hg : Bdd g) (θ : J → ℝ) :
    (J → ℝ) →L[ℝ] (X →₁[ν] ℝ) :=
  -∑ j, (ContinuousLinearMap.proj j).smulRight (weightL1 hS ν (hg.mul (hS j)) θ)

omit [Nonempty X] [Nonempty J] in
/-- The derivative applied to `η` is the `L¹` element `−[g ⟨η,S⟩ e^{−⟨θ,S⟩}]`. -/
theorem weightDeriv_apply {g : X → ℝ} (hg : Bdd g) (θ η : J → ℝ) :
    weightDeriv hS ν hg θ η =
      (integrable_mul_famWeight hS ν ((hg.mul (bdd_dirLoss hS η)).const_mul (-1)) θ).toL1
        (fun x ↦ -1 * (g x * dirLoss S η x) * famWeight S θ x) := by
  refine Lp.ext ?_
  simp only [weightDeriv, neg_apply, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]
  have hj : ∀ᵐ x ∂ν, ∀ j, ((η j • weightL1 hS ν (hg.mul (hS j)) θ) : X →₁[ν] ℝ) x =
      η j * (g x * S j x * famWeight S θ x) := by
    rw [eventually_all]
    intro j
    filter_upwards [Lp.coeFn_smul (η j) (weightL1 hS ν (hg.mul (hS j)) θ),
      Integrable.coeFn_toL1 (integrable_mul_famWeight hS ν (hg.mul (hS j)) θ)] with x h1 h2
    rw [h1, Pi.smul_apply, smul_eq_mul]
    unfold weightL1
    rw [h2]
  filter_upwards [Lp.coeFn_neg (∑ j, η j • weightL1 hS ν (hg.mul (hS j)) θ),
    Lp.coeFn_finsetSum Finset.univ (fun j ↦ η j • weightL1 hS ν (hg.mul (hS j)) θ), hj,
    Integrable.coeFn_toL1
      (integrable_mul_famWeight hS ν ((hg.mul (bdd_dirLoss hS η)).const_mul (-1)) θ)]
    with x h1 h2 h3 h4
  rw [h1, Pi.neg_apply, h2, Finset.sum_apply, h4]
  simp only [h3, dirLoss, Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

omit [Nonempty X] [Nonempty J] in
/-- The direction loss is bounded by `(Σ_j ‖S_j‖∞) ‖η‖`. -/
theorem exists_dirLoss_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ (η : J → ℝ) x, |dirLoss S η x| ≤ B * ‖η‖ := by
  choose Bj hBj using fun j ↦ (hS j).2
  refine ⟨∑ j, |Bj j|, Finset.sum_nonneg fun _ _ ↦ abs_nonneg _, fun η x ↦ ?_⟩
  unfold dirLoss
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rw [abs_mul]
  calc |η j| * |S j x| ≤ ‖η‖ * |Bj j| := by
        refine mul_le_mul ?_ ((hBj j x).trans (le_abs_self _)) (abs_nonneg _) (norm_nonneg _)
        rw [← Real.norm_eq_abs]
        exact norm_le_pi_norm η j
    _ = |Bj j| * ‖η‖ := mul_comm _ _

omit [Nonempty X] [Nonempty J] in
/-- The quadratic remainder of the weight: for `‖η‖ B ≤ 1`,
`‖[g e^{−⟨θ+η,S⟩}] − [g e^{−⟨θ,S⟩}] − D(η)‖₁ ≤ B² (∫ |g| e^{−⟨θ,S⟩}) ‖η‖²`. -/
theorem norm_weightL1_remainder_le {g : X → ℝ} (hg : Bdd g) (θ : J → ℝ) {B : ℝ}
    (hB : ∀ (η : J → ℝ) x, |dirLoss S η x| ≤ B * ‖η‖) {η : J → ℝ} (hη : B * ‖η‖ ≤ 1) :
    ‖weightL1 hS ν hg (θ + η) - weightL1 hS ν hg θ - weightDeriv hS ν hg θ η‖ ≤
      B ^ 2 * (∫ x, |g x| * famWeight S θ x ∂ν) * ‖η‖ ^ 2 := by
  have hint : Integrable (fun x ↦ g x * famWeight S θ x *
      (Real.exp (-dirLoss S η x) - 1 + dirLoss S η x)) ν := by
    have hb : Bdd fun x ↦ g x * (Real.exp (-dirLoss S η x) - 1 + dirLoss S η x) := by
      refine hg.mul ?_
      obtain ⟨hm, L, hL⟩ := bdd_dirLoss hS η
      refine ⟨((hm.neg.exp).sub measurable_const).add hm, Real.exp L + 1 + L, fun x ↦ ?_⟩
      have h1 := hL x
      have h2 : Real.exp (-dirLoss S η x) ≤ Real.exp L :=
        Real.exp_le_exp.2 (by linarith [neg_abs_le (dirLoss S η x)])
      have h3 := Real.exp_pos (-dirLoss S η x)
      rw [abs_le] at h1 ⊢
      constructor <;> nlinarith [Real.exp_pos L]
    refine (integrable_mul_famWeight hS ν hb θ).congr (Eventually.of_forall fun x ↦ ?_)
    ring
  have e : weightL1 hS ν hg (θ + η) - weightL1 hS ν hg θ - weightDeriv hS ν hg θ η =
      hint.toL1 _ := by
    rw [weightDeriv_apply]
    unfold weightL1
    rw [← Integrable.toL1_sub, ← Integrable.toL1_sub, Integrable.toL1_eq_toL1_iff]
    refine Eventually.of_forall fun x ↦ ?_
    simp only [Pi.sub_apply, famWeight, dirLoss_add, neg_add, Real.exp_add]
    ring
  rw [e, L1.norm_of_fun_eq_integral_norm, mul_comm (B ^ 2), mul_assoc, ← integral_mul_const]
  refine integral_mono hint.norm ?_ fun x ↦ ?_
  · have hga : Bdd fun x ↦ |g x| :=
      ⟨hg.1.abs, hg.2.choose, fun x ↦ by rw [abs_abs]; exact hg.2.choose_spec x⟩
    exact (integrable_mul_famWeight hS ν hga θ).mul_const _
  · have hu := hB η x
    have hu1 : |dirLoss S η x| ≤ 1 := hu.trans hη
    have hexp : |Real.exp (-dirLoss S η x) - 1 - (-dirLoss S η x)| ≤ (-dirLoss S η x) ^ 2 :=
      Real.abs_exp_sub_one_sub_id_le (by rwa [abs_neg])
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (famWeight_pos θ x)]
    have hsq : (dirLoss S η x) ^ 2 ≤ B ^ 2 * ‖η‖ ^ 2 := by
      rw [← mul_pow, ← sq_abs (dirLoss S η x)]
      exact pow_le_pow_left₀ (abs_nonneg _) hu 2
    calc |g x| * famWeight S θ x * |Real.exp (-dirLoss S η x) - 1 + dirLoss S η x|
        ≤ |g x| * famWeight S θ x * (B ^ 2 * ‖η‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) (famWeight_pos θ x).le)
          calc |Real.exp (-dirLoss S η x) - 1 + dirLoss S η x|
              = |Real.exp (-dirLoss S η x) - 1 - (-dirLoss S η x)| := by ring_nf
            _ ≤ (-dirLoss S η x) ^ 2 := hexp
            _ = (dirLoss S η x) ^ 2 := by ring
            _ ≤ B ^ 2 * ‖η‖ ^ 2 := hsq

omit [Nonempty X] [Nonempty J] in
/-- **The weighted weight is Fréchet differentiable in `L¹`.** -/
theorem hasFDerivAt_weightL1 {g : X → ℝ} (hg : Bdd g) (θ : J → ℝ) :
    HasFDerivAt (weightL1 hS ν hg) (weightDeriv hS ν hg θ) θ := by
  obtain ⟨B, hB0, hB⟩ := exists_dirLoss_bound hS
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine (IsBigO.of_bound (B ^ 2 * ∫ x, |g x| * famWeight S θ x ∂ν) ?_).trans_isLittleO
    (isLittleO_norm_pow_id (E' := J → ℝ) one_lt_two)
  have hδ : 0 < 1 / (B + 1) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : J → ℝ) hδ] with η hη
  rw [Metric.mem_ball, dist_zero_right] at hη
  have hη1 : B * ‖η‖ ≤ 1 := by
    have : B * ‖η‖ ≤ B * (1 / (B + 1)) := mul_le_mul_of_nonneg_left hη.le hB0
    refine this.trans ?_
    rw [mul_one_div, div_le_one (by linarith)]
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact norm_weightL1_remainder_le hS ν hg θ hB hη1

omit [Nonempty X] [Nonempty J] in
/-- **The weighted weight is `C^n` into `L¹` for every `n`**, by induction. -/
theorem contDiff_weightL1 (n : ℕ) :
    ∀ {g : X → ℝ} (hg : Bdd g), ContDiff ℝ n (weightL1 hS ν hg) := by
  induction n with
  | zero =>
    intro g hg
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun θ ↦
      (hasFDerivAt_weightL1 hS ν hg θ).continuousAt)
  | succ n ih =>
    intro g hg
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_fderiv.2 ⟨fun θ ↦ (hasFDerivAt_weightL1 hS ν hg θ).differentiableAt,
      fun h ↦ absurd h (WithTop.natCast_ne_top n), ?_⟩
    have e : fderiv ℝ (weightL1 hS ν hg) = fun θ ↦ -∑ j,
        ContinuousLinearMap.smulRightL ℝ (J → ℝ) (X →₁[ν] ℝ) (ContinuousLinearMap.proj j)
          (weightL1 hS ν (hg.mul (hS j)) θ) := by
      funext θ
      rw [(hasFDerivAt_weightL1 hS ν hg θ).fderiv]
      rfl
    rw [e]
    exact (ContDiff.sum fun j _ ↦ (ContinuousLinearMap.smulRightL ℝ (J → ℝ) (X →₁[ν] ℝ)
      (ContinuousLinearMap.proj j)).contDiff.comp (ih (hg.mul (hS j)))).neg

omit [Nonempty X] [Nonempty J] in
/-- The weighted weight is `C^∞` into `L¹`. -/
theorem contDiff_infty_weightL1 {g : X → ℝ} (hg : Bdd g) : ContDiff ℝ ∞ (weightL1 hS ν hg) :=
  contDiff_infty.2 fun n ↦ contDiff_weightL1 hS ν n hg

end Weight

section Density

/-- The reconstruction density in natural coordinates, as an `L¹` element. -/
noncomputable def densL1 (θ : J → ℝ) : X →₁[ν] ℝ := (integrable_famDens hS ν θ).toL1 _

omit [Nonempty X] [Nonempty J] in
/-- `[q_θ] = Z(θ)⁻¹ • [e^{−⟨θ,S⟩}]`. -/
theorem densL1_eq (θ : J → ℝ) :
    densL1 hS ν θ = (famZ S ν θ)⁻¹ • weightL1 hS ν (Bdd.const 1) θ := by
  unfold densL1 weightL1
  rw [← Integrable.toL1_smul, Integrable.toL1_eq_toL1_iff]
  refine Eventually.of_forall fun x ↦ ?_
  simp only [famDens, smul_eq_mul, one_mul]
  ring

omit [Nonempty J] in
/-- **The reconstruction density is a `C^∞` map into `L¹(ν)`.** -/
theorem contDiff_densL1 : ContDiff ℝ ∞ (densL1 hS ν) := by
  have e : densL1 hS ν = fun θ ↦ (famZ S ν θ)⁻¹ • weightL1 hS ν (Bdd.const 1) θ := by
    funext θ
    exact densL1_eq hS ν θ
  rw [e]
  exact ((contDiff_famZ hS ν).inv fun θ ↦ (famZ_pos hS ν θ).ne').smul
    (contDiff_infty_weightL1 hS ν (Bdd.const 1))

/-- The reconstruction of a response is the density at its natural coordinate. -/
theorem reconstructionL1_eq_densL1 (M : J → ℝ) : reconstructionL1 hS ν M = densL1 hS ν (θr M) :=
  rfl

end Density

section Atlas

variable {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
include hfin

omit hfin in
variable (S M) in
/-- The interior atlas domain `{s | M_s ∈ Ω}`. -/
def atlasDomain : Set ℝ := {s | atlasPath S ν M s ∈ Ω}

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] hfin in
theorem mem_atlasDomain {s : ℝ} : s ∈ atlasDomain S ν M ↔ atlasPath S ν M s ∈ Ω := Iff.rfl

/-- **The reconstruction is a `C^∞` curve in `L¹` along the atlas.** -/
theorem contDiffOn_reconstructionL1_atlas :
    ContDiffOn ℝ ∞ (fun s ↦ reconstructionL1 hS ν (atlasPath S ν M s)) (atlasDomain S ν M) := by
  have e : (fun s ↦ reconstructionL1 hS ν (atlasPath S ν M s)) =
      densL1 hS ν ∘ ((𝕍).subtypeL ∘ atlasTheta hS ν M) := by
    funext s
    rfl
  rw [e]
  exact (contDiff_densL1 hS ν).comp_contDiffOn
    ((𝕍).subtypeL.contDiff.comp_contDiffOn (contDiffOn_atlasTheta hS ν hfin))

/-- The interior atlas domain is open. -/
theorem isOpen_atlas_interior : IsOpen (atlasDomain S ν M) := by
  have h : atlasDomain S ν M = (fun s ↦ s • atlasInc hS ν hfin) ⁻¹' Set.range
      (chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS) := by
    ext s
    rw [Set.mem_preimage, mem_range_chartV_iff, ← atlasPath_eq_add_smul_atlasInc hS ν hfin]
    rfl
  rw [h]
  exact (isOpen_range_chartV hS ν).preimage (continuous_id.smul continuous_const)

omit hfin in
/-- The moment functional along the atlas is the atlas itself: `m(p(s)) = M_s` on `D`. -/
theorem momentL1_reconstructionL1_atlas {s : ℝ} (hs : s ∈ atlasDomain S ν M) :
    momentL1 hS ν (reconstructionL1 hS ν (atlasPath S ν M s)) = atlasPath S ν M s :=
  momentL1_reconstructionL1 hS ν hs

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] hfin in
/-- Higher derivatives of an affine curve vanish: for `k ≥ 2`,
`iteratedDerivWithin k (fun s ↦ c + s • v) U = 0` on an open `U`. -/
theorem iteratedDerivWithin_affine_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set ℝ} (hU : IsOpen U) (c v : E) {k : ℕ} (hk : 2 ≤ k) :
    ∀ s ∈ U, iteratedDerivWithin k (fun s : ℝ ↦ c + s • v) U s = 0 := by
  have h1 : ∀ s ∈ U, iteratedDerivWithin 1 (fun s : ℝ ↦ c + s • v) U s = v := fun s hs ↦ by
    rw [iteratedDerivWithin_one]
    exact (((hasDerivAt_id s).smul_const v).const_add c).hasDerivWithinAt.derivWithin
      (hU.uniqueDiffWithinAt hs) |>.trans (by simp)
  have h2 : ∀ s ∈ U, iteratedDerivWithin 2 (fun s : ℝ ↦ c + s • v) U s = 0 := fun s hs ↦ by
    rw [iteratedDerivWithin_succ, derivWithin_congr (fun t ht ↦ h1 t ht) (h1 s hs)]
    exact congrFun (derivWithin_fun_const _ _) s
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  induction m with
  | zero => exact h2
  | succ m ih =>
    intro s hs
    rw [show m + 1 + 2 = (m + 2) + 1 by ring, iteratedDerivWithin_succ,
      derivWithin_congr (fun t ht ↦ ih (by omega) t ht) (ih (by omega) s hs)]
    exact congrFun (derivWithin_fun_const _ _) s

/-- Continuous linear functionals commute with the iterated derivative of the reconstruction
curve on the open atlas domain. -/
theorem clm_iteratedDerivWithin_reconstructionL1_atlas {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : (X →₁[ν] ℝ) →L[ℝ] F) (k : ℕ) {s : ℝ} (hs : s ∈ atlasDomain S ν M) :
    L (iteratedDerivWithin k (fun s ↦ reconstructionL1 hS ν (atlasPath S ν M s))
        (atlasDomain S ν M) s) =
      iteratedDerivWithin k (fun s ↦ L (reconstructionL1 hS ν (atlasPath S ν M s)))
        (atlasDomain S ν M) s := by
  have h := ContinuousLinearMap.iteratedFDerivWithin_comp_left L
    ((contDiffOn_reconstructionL1_atlas hS ν hfin).contDiffWithinAt hs)
    (isOpen_atlas_interior hS ν hfin).uniqueDiffOn hs (i := k)
    (by exact_mod_cast natCast_le_infty k)
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin,
    Function.comp_def] at *
  rw [h]
  rfl

/-- **The invisible tower**: every derivative of order `≥ 2` of the reconstruction along the
atlas has zero feature moments and zero mass. -/
theorem invisible_tower {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hs : s ∈ atlasDomain S ν M) :
    momentL1 hS ν (iteratedDerivWithin k
        (fun s ↦ reconstructionL1 hS ν (atlasPath S ν M s)) (atlasDomain S ν M) s) = 0 ∧
      L1.integralCLM (iteratedDerivWithin k
        (fun s ↦ reconstructionL1 hS ν (atlasPath S ν M s)) (atlasDomain S ν M) s) = 0 := by
  have hU := isOpen_atlas_interior hS ν hfin
  constructor
  · rw [clm_iteratedDerivWithin_reconstructionL1_atlas hS ν hfin _ k hs]
    have e : EqOn (fun s ↦ momentL1 hS ν (reconstructionL1 hS ν (atlasPath S ν M s)))
        (fun s : ℝ ↦ m₀ + s • (M - m₀)) (atlasDomain S ν M) := fun t ht ↦ by
      beta_reduce
      rw [momentL1_reconstructionL1_atlas hS ν ht, ← atlasPath_sub, add_sub_cancel]
    rw [iteratedDerivWithin_congr e hs]
    exact iteratedDerivWithin_affine_eq_zero hU _ _ hk s hs
  · rw [clm_iteratedDerivWithin_reconstructionL1_atlas hS ν hfin _ k hs]
    have e : EqOn (fun s ↦ L1.integralCLM (reconstructionL1 hS ν (atlasPath S ν M s)))
        (fun s : ℝ ↦ (1 : ℝ) + s • (0 : ℝ)) (atlasDomain S ν M) := fun t _ ↦ by
      beta_reduce
      rw [smul_zero, add_zero, ← L1.integral_eq, L1.integral_eq_integral]
      exact integral_reconstructionL1 hS ν _
    rw [iteratedDerivWithin_congr e hs]
    exact iteratedDerivWithin_affine_eq_zero hU _ _ hk s hs

/-- **The first derivative carries exactly the atlas velocity**: `m(p'(s)) = M − m₀` on `D`. -/
theorem momentL1_iteratedDerivWithin_one {s : ℝ} (hs : s ∈ atlasDomain S ν M) :
    momentL1 hS ν (iteratedDerivWithin 1
      (fun s ↦ reconstructionL1 hS ν (atlasPath S ν M s)) (atlasDomain S ν M) s) = M - m₀ := by
  have hU := isOpen_atlas_interior hS ν hfin
  rw [clm_iteratedDerivWithin_reconstructionL1_atlas hS ν hfin _ 1 hs]
  have e : EqOn (fun s ↦ momentL1 hS ν (reconstructionL1 hS ν (atlasPath S ν M s)))
      (fun s : ℝ ↦ m₀ + s • (M - m₀)) (atlasDomain S ν M) := fun t ht ↦ by
    beta_reduce
    rw [momentL1_reconstructionL1_atlas hS ν ht, ← atlasPath_sub, add_sub_cancel]
  rw [iteratedDerivWithin_congr e hs, iteratedDerivWithin_one]
  exact ((((hasDerivAt_id s).smul_const (M - m₀)).const_add m₀).hasDerivWithinAt.derivWithin
    (hU.uniqueDiffWithinAt hs)).trans (by simp)

end Atlas

end Laplace.Multi
