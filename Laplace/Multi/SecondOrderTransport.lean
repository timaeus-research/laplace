/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ObservableCurvature
import Laplace.Multi.ResponseTransport
import Laplace.Multi.ReconstructionC1
import Laplace.Multi.AtlasSkewness

/-!
# Second-order transport along the affine data path

Along the straight atlas `M_s = m₀ + s δ` (the response path of the affine data path from the
featureless law to the data), the reconstructed response `G_F(M_s)` of a bounded observable has
first derivative `lin_{F,M_s}(δ)` and second derivative the bias form `b_{F,M_s}(δ, δ)`
(`hasDerivAt_atlasLin`, `atlasQuad_eq_biasForm`): the seabed's `thirdCentral` second derivative
with the canonical regression coefficient is exactly `E_{Q_M}[N_M F ℓ_δ²]`. The exact second-order
transport formula follows by Taylor's theorem with integral remainder:

  `G_F(M_t) = G_F(m₀) + t lin_{F,m₀}(δ) + ∫₀ᵗ (t − r) b_{F,M_r}(δ, δ) dr`

(`integral_response_atlas_taylor`). Curvature of the response along the data path is the invisible
(normal) interaction of the observable with the squared score.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Bound

variable {X : Type*} [MeasurableSpace X] [Nonempty X] (ρ : Measure X) [IsProbabilityMeasure ρ]

/-- The third central moment of three bounded functions is bounded by `8 B_g B_k B_f`. -/
theorem abs_thirdCentral_le {g k f : X → ℝ} {Bg Bk Bf : ℝ} (hg : ∀ x, |g x| ≤ Bg)
    (hk : ∀ x, |k x| ≤ Bk) (hf : ∀ x, |f x| ≤ Bf) :
    |thirdCentral ρ g k f| ≤ 8 * Bg * Bk * Bf := by
  have hmean : ∀ {h : X → ℝ} {B : ℝ}, (∀ x, |h x| ≤ B) → ∀ x, |h x - ∫ y, h y ∂ρ| ≤ 2 * B := by
    intro h B hB x
    have hm : |∫ y, h y ∂ρ| ≤ B := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le (integrable_const B)
        (Eventually.of_forall fun x ↦ ?_)).trans ?_
      · rw [Real.norm_eq_abs]; exact hB x
      · simp
    exact (abs_sub _ _).trans (by linarith [hB x])
  have hg0 : 0 ≤ Bg := (abs_nonneg _).trans (hg (Classical.arbitrary X))
  have hk0 : 0 ≤ Bk := (abs_nonneg _).trans (hk (Classical.arbitrary X))
  unfold thirdCentral
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (integrable_const (8 * Bg * Bk * Bf))
    (Eventually.of_forall fun x ↦ ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |g x - ∫ y, g y ∂ρ| * |k x - ∫ y, k y ∂ρ| * |f x - ∫ y, f y ∂ρ|
        ≤ (2 * Bg) * (2 * Bk) * (2 * Bf) :=
          mul_le_mul (mul_le_mul (hmean hg x) (hmean hk x) (abs_nonneg _) (by positivity))
            (hmean hf x) (abs_nonneg _) (by positivity)
      _ = 8 * Bg * Bk * Bf := by ring
  · simp

end Bound

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤)
include hS hfin

/-- The family `θ ↦ P_θ` in natural coordinates. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The atlas increment `M − m₀` as a visible direction. -/
noncomputable def atlasInc : 𝕍 := ⟨M - m₀, sub_mem_dirSpan_of_genRate_ne_top hS ν hfin⟩

theorem atlasInc_coe : (atlasInc hS ν hfin : J → ℝ) = M - m₀ := rfl

/-- **The first-order transport along the atlas**, `−Cov_{Q_s}(F, ⟨v_s, S⟩)`. -/
noncomputable def atlasLin (F : X → ℝ) (s : ℝ) : ℝ :=
  -lawCov (Pfam (atlasTheta hS ν M s)) F (dirLoss S (atlasVel hS ν hfin s))

/-- The reconstructed response is differentiable along the atlas with derivative `atlasLin`. -/
theorem hasDerivAt_integral_atlas_atlasLin {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {F : X → ℝ}
    (hF : Bdd F) :
    HasDerivAt (fun s ↦ ∫ x, F x ∂(Pfam (atlasTheta hS ν M s))) (atlasLin hS ν hfin F s) s :=
  hasDerivAt_integral_familyMeasure_atlas hS ν hfin hs0 hs1 hF

/-- The atlas velocity is the inverse chart derivative applied to the increment. -/
theorem atlasVel_eq (s : ℝ) :
    atlasVel hS ν hfin s = (CDE (θr (atlasPath S ν M s))).symm (atlasInc hS ν hfin) := rfl

/-- The first-order transport is the linear form on the increment. -/
theorem atlasLin_eq_linForm {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {F : X → ℝ} (hF : Bdd F) :
    atlasLin hS ν hfin F s = linForm hS ν (atlasPath S ν M s) hF (M - m₀) := by
  have hint := atlas_mem_intrinsicInterior hS ν hfin hs0 hs1
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := atlasPath S ν M s)
  have h := integral_mul_responseScore_eq_linForm hS ν (M := atlasPath S ν M s) hF
    (atlasInc hS ν hfin)
  rw [← atlasInc_coe hS ν hfin, ← h]
  unfold atlasLin lawCov
  simp only [atlasTheta]
  rw [atlasVel_eq]
  unfold responseScore
  have hv := bdd_dirLoss hS ((CDE (θr (atlasPath S ν M s))).symm (atlasInc hS ν hfin) : J → ℝ)
  simp only [mul_sub]
  rw [integral_sub ((integrable_of_bdd_prob _ hF).mul_const _)
    (integrable_of_bdd_prob _ (hF.mul hv)), integral_mul_const,
    integral_dirLoss_responseTheta hS ν hint]
  ring

variable (M) in
/-- **The canonical regression coefficient** along the atlas: `−R_{M_s} Cov_{Q_s}(S, F)`. -/
noncomputable def atlasBeta (F : X → ℝ) (hF : Bdd F) (s : ℝ) : J → ℝ :=
  -((CDE (θr (atlasPath S ν M s))).symm
    ⟨respCov hS ν (atlasPath S ν M s) F, respCov_mem_dirSpan hS ν hF⟩ : J → ℝ)

/-- The canonical regression coefficient solves the regression equations. -/
theorem atlasBeta_regression {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {F : X → ℝ} (hF : Bdd F) (i : J) :
    lawCov (Pfam (atlasTheta hS ν M s)) (S i) (dirLoss S (atlasBeta hS ν M F hF s)) =
      lawCov (Pfam (atlasTheta hS ν M s)) (S i) F := by
  have hint := atlas_mem_intrinsicInterior hS ν hfin hs0 hs1
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := atlasPath S ν M s)
  have h := lawCov_stat_responseScore hS ν (M := atlasPath S ν M s)
    ⟨respCov hS ν (atlasPath S ν M s) F, respCov_mem_dirSpan hS ν hF⟩ i
  unfold responseScore at h
  rw [lawCov_comm, lawCov_sub_left_eq _ (Bdd.const _) (bdd_dirLoss hS _) (hS i),
    lawCov_const_left_eq_zero, zero_sub, lawCov_comm] at h
  unfold atlasBeta atlasTheta
  rw [show dirLoss S (-((CDE (θr (atlasPath S ν M s))).symm
      ⟨respCov hS ν (atlasPath S ν M s) F, respCov_mem_dirSpan hS ν hF⟩ : J → ℝ)) =
      fun x ↦ -dirLoss S ((CDE (θr (atlasPath S ν M s))).symm
        ⟨respCov hS ν (atlasPath S ν M s) F, respCov_mem_dirSpan hS ν hF⟩ : J → ℝ) x from
    funext fun x ↦ dirLoss_neg _ _]
  rw [lawCov_neg_right_eq, h]
  rfl

/-- **The second-order transport coefficient** along the atlas: the third central moment of the
residual against the squared feature velocity. -/
noncomputable def atlasQuad (F : X → ℝ) (hF : Bdd F) (s : ℝ) : ℝ :=
  thirdCentral (Pfam (atlasTheta hS ν M s)) (fun x ↦ F x - dirLoss S (atlasBeta hS ν M F hF s) x)
    (dirLoss S (atlasVel hS ν hfin s)) (dirLoss S (atlasVel hS ν hfin s))

/-- **The first-order transport is differentiable along the atlas with derivative `atlasQuad`.** -/
theorem hasDerivAt_atlasLin {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {F : X → ℝ} (hF : Bdd F) :
    HasDerivAt (atlasLin hS ν hfin F) (atlasQuad hS ν hfin F hF s) s := by
  unfold atlasLin atlasQuad
  exact hasDerivAt_neg_lawCov_atlasVel hS ν hfin hs0 hs1 hF
    (atlasBeta_regression hS ν hfin hs0 hs1 hF)

/-- **The second-order coefficient is the bias form on the increment**:
`atlasQuad = b_{F,M_s}(δ, δ) = E_{Q_s}[N_{M_s} F ℓ_δ²]`. -/
theorem atlasQuad_eq_biasForm {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {F : X → ℝ} (hF : Bdd F) :
    atlasQuad hS ν hfin F hF s = biasForm hS ν (atlasPath S ν M s) hF (M - m₀) (M - m₀) := by
  have hint := atlas_mem_intrinsicInterior hS ν hfin hs0 hs1
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := atlasPath S ν M s)
  have hb := biasForm_apply hS ν (M := atlasPath S ν M s) hF (M - m₀) (M - m₀)
  have hproj : dirProj S ν (M - m₀) = (atlasInc hS ν hfin) := dirProj_coe S ν (atlasInc hS ν hfin)
  rw [hproj] at hb
  rw [hb]
  unfold atlasQuad thirdCentral atlasTheta
  -- the centred residual is the normal part, the centred velocity is minus the score
  have hEv : ∫ y, dirLoss S (atlasVel hS ν hfin s) y ∂(Pfam (θr (atlasPath S ν M s))) =
      dotJ (atlasVel hS ν hfin s : J → ℝ) (atlasPath S ν M s) :=
    integral_dirLoss_responseTheta hS ν hint _
  have hEβ : ∫ y, dirLoss S (atlasBeta hS ν M F hF s) y ∂(Pfam (θr (atlasPath S ν M s))) =
      dotJ (atlasBeta hS ν M F hF s) (atlasPath S ν M s) :=
    integral_dirLoss_responseTheta hS ν hint _
  have hEres : ∫ y, (F y - dirLoss S (atlasBeta hS ν M F hF s) y)
      ∂(Pfam (θr (atlasPath S ν M s))) =
      (∫ y, F y ∂(Pfam (θr (atlasPath S ν M s)))) - dotJ (atlasBeta hS ν M F hF s)
        (atlasPath S ν M s) := by
    rw [integral_sub (integrable_of_bdd_prob _ hF) (integrable_of_bdd_prob _ (bdd_dirLoss hS _)),
      hEβ]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [hEres, hEv]
  have hres : F x - dirLoss S (atlasBeta hS ν M F hF s) x -
      ((∫ y, F y ∂(Pfam (θr (atlasPath S ν M s)))) - dotJ (atlasBeta hS ν M F hF s)
        (atlasPath S ν M s)) = normalProj hS ν (atlasPath S ν M s) hF x := by
    unfold normalProj regProj responseScore atlasBeta
    rw [dirLoss_neg, dotJ_neg_left]
    ring
  have hvel : dirLoss S (atlasVel hS ν hfin s) x -
      dotJ (atlasVel hS ν hfin s : J → ℝ) (atlasPath S ν M s) =
      -responseScore hS ν (atlasPath S ν M s) (atlasInc hS ν hfin) x := by
    unfold responseScore
    rw [atlasVel_eq]
    ring
  rw [hres, hvel]
  ring

/-- The second-order coefficient is bounded on `[0, t]` for `t < 1`. -/
theorem exists_bound_atlasQuad {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {F : X → ℝ} (hF : Bdd F) {BF : ℝ}
    (hBF : ∀ x, |F x| ≤ BF) :
    ∃ K : ℝ, ∀ r ∈ Icc (0 : ℝ) t, |atlasQuad hS ν hfin F hF r| ≤ K := by
  classical
  -- a uniform bound on the features
  have hB' : ∀ j, ∃ B, ∀ x, |S j x| ≤ B := fun j ↦ (hS j).2
  choose Bj hBj using hB'
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∑ j, |Bj j| := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hBdef ▸ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hB : ∀ j x, |S j x| ≤ B := fun j x ↦
    (hBj j x).trans ((le_abs_self _).trans (hBdef ▸ Finset.single_le_sum (f := fun j ↦ |Bj j|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)))
  have hBF0 : 0 ≤ BF := (abs_nonneg _).trans (hBF (Classical.arbitrary X))
  -- a uniform bound on the inverse chart derivative along the atlas
  have hint : ∀ r ∈ Icc (0 : ℝ) t,
      atlasPath S ν M r ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) :=
    fun r hr ↦ atlas_mem_intrinsicInterior hS ν hfin hr.1 (lt_of_le_of_lt hr.2 ht1)
  have hRc : ContinuousOn (fun r ↦ ((CDE (θr (atlasPath S ν M r))).symm : 𝕍 →L[ℝ] 𝕍))
      (Icc (0 : ℝ) t) :=
    (continuousOn_inverse_chart hS ν).comp
      (fun r _ ↦ (hasDerivAt_atlasPath ν (M := M) r).continuousAt.continuousWithinAt) hint
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hRc
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0 ⟨le_rfl, ht0⟩)
  -- the velocity and the regression coefficient are bounded
  have hv : ∀ r ∈ Icc (0 : ℝ) t, ‖(atlasVel hS ν hfin r : J → ℝ)‖ ≤ R * ‖M - m₀‖ := by
    intro r hr
    rw [atlasVel_eq, Submodule.norm_coe]
    have := ((CDE (θr (atlasPath S ν M r))).symm : 𝕍 →L[ℝ] 𝕍).le_opNorm (atlasInc hS ν hfin)
    rw [ContinuousLinearEquiv.coe_coe] at this
    refine this.trans (mul_le_mul_of_nonneg_right (hR r hr) (norm_nonneg _))
  have hcov : ∀ r : ℝ, ‖respCov hS ν (atlasPath S ν M r) F‖ ≤ 2 * B * BF := by
    intro r
    have hP := isProbabilityMeasure_family_responseTheta hS ν (M := atlasPath S ν M r)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j ↦ ?_
    rw [Real.norm_eq_abs]
    unfold respCov lawCov
    have h1 : |∫ x, S j x * F x ∂(Pfam (θr (atlasPath S ν M r)))| ≤ B * BF := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le_const (C := B * BF)
        (Eventually.of_forall fun x ↦ ?_)).trans ?_
      · rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hB j x) (hBF x) (abs_nonneg _) hB0
      · rw [probReal_univ, mul_one]
    have h2 : |∫ x, S j x ∂(Pfam (θr (atlasPath S ν M r)))| ≤ B := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le_const (C := B)
        (Eventually.of_forall fun x ↦ ?_)).trans ?_
      · rw [Real.norm_eq_abs]; exact hB j x
      · rw [probReal_univ, mul_one]
    have h3 : |∫ x, F x ∂(Pfam (θr (atlasPath S ν M r)))| ≤ BF := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le_const (C := BF)
        (Eventually.of_forall fun x ↦ ?_)).trans ?_
      · rw [Real.norm_eq_abs]; exact hBF x
      · rw [probReal_univ, mul_one]
    calc |(∫ x, S j x * F x ∂(Pfam (θr (atlasPath S ν M r)))) -
          (∫ x, S j x ∂(Pfam (θr (atlasPath S ν M r)))) * ∫ x, F x ∂(Pfam (θr (atlasPath S ν M r)))|
        ≤ |∫ x, S j x * F x ∂(Pfam (θr (atlasPath S ν M r)))| +
          |∫ x, S j x ∂(Pfam (θr (atlasPath S ν M r)))| *
            |∫ x, F x ∂(Pfam (θr (atlasPath S ν M r)))| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul]
      _ ≤ B * BF + B * BF := by gcongr
      _ = 2 * B * BF := by ring
  have hβ : ∀ r ∈ Icc (0 : ℝ) t, ‖atlasBeta hS ν M F hF r‖ ≤ R * (2 * B * BF) := by
    intro r hr
    unfold atlasBeta
    rw [norm_neg, Submodule.norm_coe]
    have := ((CDE (θr (atlasPath S ν M r))).symm : 𝕍 →L[ℝ] 𝕍).le_opNorm
      (⟨respCov hS ν (atlasPath S ν M r) F, respCov_mem_dirSpan hS ν hF⟩ : 𝕍)
    rw [ContinuousLinearEquiv.coe_coe] at this
    refine this.trans (mul_le_mul (hR r hr) ?_ (norm_nonneg _) hR0)
    change ‖respCov hS ν (atlasPath S ν M r) F‖ ≤ _
    exact hcov r
  -- a bounded coefficient vector gives a bounded feature combination
  have hdir : ∀ (w : J → ℝ) (x : X), |dirLoss S w x| ≤ Fintype.card J * ‖w‖ * B := by
    intro w x
    unfold dirLoss
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |w i * S i x| ≤ ∑ _i : J, ‖w‖ * B := Finset.sum_le_sum fun i _ ↦ by
          rw [abs_mul]
          exact mul_le_mul (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w i) (hB i x)
            (abs_nonneg _) (norm_nonneg _)
      _ = Fintype.card J * ‖w‖ * B := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  refine ⟨8 * (BF + Fintype.card J * (R * (2 * B * BF)) * B) *
    (Fintype.card J * (R * ‖M - m₀‖) * B) * (Fintype.card J * (R * ‖M - m₀‖) * B),
    fun r hr ↦ ?_⟩
  unfold atlasQuad
  have hP' : IsProbabilityMeasure (Pfam (atlasTheta hS ν M r)) :=
    isProbabilityMeasure_family_responseTheta hS ν (M := atlasPath S ν M r)
  refine abs_thirdCentral_le _ (fun x ↦ ?_) (fun x ↦ ?_) (fun x ↦ ?_)
  · refine (abs_sub _ _).trans (add_le_add (hBF x) ((hdir _ x).trans ?_))
    have := hβ r hr
    gcongr
  · exact (hdir _ x).trans (by have := hv r hr; gcongr)
  · exact (hdir _ x).trans (by have := hv r hr; gcongr)

/-- **Taylor's formula with integral remainder along the atlas**:
`G_F(M_t) − G_F(m₀) − t · atlasLin(0) = ∫₀ᵗ (t − r) · atlasQuad(r) dr` for `0 ≤ t < 1`. -/
theorem integral_response_atlas_taylor {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {F : X → ℝ}
    (hF : Bdd F) {BF : ℝ} (hBF : ∀ x, |F x| ≤ BF) :
    (∫ x, F x ∂(Pfam (atlasTheta hS ν M t))) - (∫ x, F x ∂(Pfam (atlasTheta hS ν M 0))) -
      t * atlasLin hS ν hfin F 0 = ∫ r in (0 : ℝ)..t, (t - r) * atlasQuad hS ν hfin F hF r := by
  obtain ⟨K, hK⟩ := exists_bound_atlasQuad hS ν hfin ht0 ht1 hF hBF
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ⟨le_rfl, ht0⟩)
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun s ↦ ∫ x, F x ∂(Pfam (atlasTheta hS ν M s)) := ⟨_, rfl⟩
  have hf' : ∀ r ∈ Icc (0 : ℝ) t, HasDerivAt f (atlasLin hS ν hfin F r) r := fun r hr ↦ by
    rw [hf]
    exact hasDerivAt_integral_atlas_atlasLin hS ν hfin hr.1 (lt_of_le_of_lt hr.2 ht1) hF
  have hf'' : ∀ r ∈ Icc (0 : ℝ) t,
      HasDerivAt (atlasLin hS ν hfin F) (atlasQuad hS ν hfin F hF r) r := fun r hr ↦
    hasDerivAt_atlasLin hS ν hfin hr.1 (lt_of_le_of_lt hr.2 ht1) hF
  have hderiv : ∀ r ∈ Icc (0 : ℝ) t, deriv (atlasLin hS ν hfin F) r = atlasQuad hS ν hfin F hF r :=
    fun r hr ↦ (hf'' r hr).deriv
  -- the auxiliary function `g r = f t − f r − (t − r) f'(r)`
  have hg : ∀ r ∈ uIcc (0 : ℝ) t,
      HasDerivAt (fun r ↦ f t - f r - (t - r) * atlasLin hS ν hfin F r)
        (-(t - r) * deriv (atlasLin hS ν hfin F) r) r := by
    intro r hr
    rw [uIcc_of_le ht0] at hr
    have h := ((hasDerivAt_const r (f t)).sub (hf' r hr)).sub
      (((hasDerivAt_id r).const_sub t).mul (hf'' r hr))
    rw [hderiv r hr]
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  have hint : IntervalIntegrable (fun r ↦ -(t - r) * deriv (atlasLin hS ν hfin F) r)
      volume 0 t := by
    rw [intervalIntegrable_iff, uIoc_of_le ht0]
    refine Measure.integrableOn_of_bounded (M := 1 * K) (Real.volume_Ioc ▸ ENNReal.ofReal_ne_top)
      (((measurable_const.sub measurable_id).neg.mul (measurable_deriv _)).aestronglyMeasurable) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun r hr ↦ ?_
    have hr' : r ∈ Icc (0 : ℝ) t := ⟨hr.1.le, hr.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_neg, hderiv r hr']
    refine mul_le_mul ?_ (hK r hr') (abs_nonneg _) zero_le_one
    rw [abs_of_nonneg (by linarith [hr.2])]
    linarith [hr.1]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hg hint
  have hcongr : ∫ r in (0 : ℝ)..t, (t - r) * atlasQuad hS ν hfin F hF r =
      ∫ r in (0 : ℝ)..t, (t - r) * deriv (atlasLin hS ν hfin F) r := by
    refine intervalIntegral.integral_congr fun r hr ↦ ?_
    rw [uIcc_of_le ht0] at hr
    simp only [hderiv r hr]
  have hneg : ∫ r in (0 : ℝ)..t, -(t - r) * deriv (atlasLin hS ν hfin F) r =
      -∫ r in (0 : ℝ)..t, (t - r) * deriv (atlasLin hS ν hfin F) r := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun r _ ↦ ?_
    ring
  rw [hneg] at hftc
  simp only [sub_self, zero_mul, sub_zero] at hftc
  rw [hcongr]
  have e1 : f t = ∫ x, F x ∂(Pfam (atlasTheta hS ν M t)) := by rw [hf]
  have e0 : f 0 = ∫ x, F x ∂(Pfam (atlasTheta hS ν M 0)) := by rw [hf]
  rw [← e1, ← e0]
  linarith

/-- **The exact second-order transport formula** along the affine data path: for `0 ≤ t < 1`,
`G_F(M_t) = G_F(m₀) + t lin_{F,m₀}(δ) + ∫₀ᵗ (t − r) b_{F,M_r}(δ, δ) dr` with `δ = M − m₀`. -/
theorem obsResponse_atlas_eq_second_order {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {F : X → ℝ}
    (hF : Bdd F) {BF : ℝ} (hBF : ∀ x, |F x| ≤ BF) :
    obsResponse hS ν F (atlasPath S ν M t) =
      obsResponse hS ν F m₀ + t * linForm hS ν m₀ hF (M - m₀) +
        ∫ r in (0 : ℝ)..t, (t - r) * biasForm hS ν (atlasPath S ν M r) hF (M - m₀) (M - m₀) := by
  have h := integral_response_atlas_taylor hS ν hfin ht0 ht1 hF hBF
  have hcongr : ∫ r in (0 : ℝ)..t, (t - r) * atlasQuad hS ν hfin F hF r =
      ∫ r in (0 : ℝ)..t, (t - r) * biasForm hS ν (atlasPath S ν M r) hF (M - m₀) (M - m₀) := by
    refine intervalIntegral.integral_congr fun r hr ↦ ?_
    rw [uIcc_of_le ht0] at hr
    simp only [atlasQuad_eq_biasForm hS ν hfin hr.1 (lt_of_le_of_lt hr.2 ht1) hF]
  have hlin : atlasLin hS ν hfin F 0 = linForm hS ν m₀ hF (M - m₀) := by
    rw [atlasLin_eq_linForm hS ν hfin le_rfl zero_lt_one hF, atlasPath_zero]
  have e1 : obsResponse hS ν F (atlasPath S ν M t) = ∫ x, F x ∂(Pfam (atlasTheta hS ν M t)) := rfl
  have e0 : obsResponse hS ν F m₀ = ∫ x, F x ∂(Pfam (atlasTheta hS ν M 0)) := by
    unfold atlasTheta
    rw [atlasPath_zero]
    rfl
  rw [e1, e0, ← hlin, ← hcongr]
  linarith

/-- **The second derivative of the reconstructed response along the atlas is the bias form**:
for `s ∈ (0, 1)`, `(G_F ∘ M_·)''(s) = b_{F,M_s}(δ, δ)`. -/
theorem hasDerivAt_deriv_obsResponse_atlas {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {F : X → ℝ}
    (hF : Bdd F) :
    HasDerivAt (deriv fun r ↦ obsResponse hS ν F (atlasPath S ν M r))
      (biasForm hS ν (atlasPath S ν M s) hF (M - m₀) (M - m₀)) s := by
  have h := hasDerivAt_atlasLin hS ν hfin hs.1.le hs.2 hF
  rw [atlasQuad_eq_biasForm hS ν hfin hs.1.le hs.2 hF] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
  exact (hasDerivAt_integral_atlas_atlasLin hS ν hfin hr.1.le hr.2 hF).deriv

end Laplace.Multi
