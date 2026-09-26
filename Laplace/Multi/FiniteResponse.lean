/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherRaoCurvature

/-!
# Finite response: the accounting identity along the atlas

For a bounded observable `φ`, the response `F_φ(s) = E_{Q_s} φ` along the atlas `Q_s = Π(M_s)` from
the featureless posterior `Q_0 = ν` to the reconstruction `Q_1 = Π(M)` has

`F_φ'(s) = E_{Q_s}[φ ℓ_s]` and `F_φ''(s) = E_{Q_s}[φ N_{M_s}(ℓ_s²)]`

(`hasDerivAt_integral_atlas`, `hasDerivAt_integral_atlasScore`). Integrating by parts on `[0,1]` and
adding the fibre identity `E_D[N_M φ] = E_D φ − E_{Π(M)} φ` for every data law `D` with response `M`
(`integral_normalProj_eq_sub`) gives the **accounting identity** (`response_accounting`):

`E_D φ − E_ν φ = E_ν[φ ℓ_0] + ∫₀¹ (1−s) E_{Q_s}[φ N_{M_s}(ℓ_s²)] ds + E_D[N_M φ]`,

the baseline linear susceptibility, the accumulated nonlinear response along the atlas, and the
feature-invisible residual between the data law and its reconstruction.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Finite

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤)
include hS

/-- The reconstruction at the atlas point `s`. -/
local notation "Qat" s => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
  (atlasTheta hS ν M s)

omit [Nonempty J] in
/-- The family member at `θ = 0` is the featureless posterior. -/
theorem familyMeasure_zero_eq :
    familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 = ν := by
  rw [familyMeasure_one_zero_eq_tilted hS ν 0]
  have e : (fun x ↦ -1 * dirLoss S (0 : J → ℝ) x) = 0 := by
    funext x
    simp [dirLoss]
  rw [e, tilted_zero]

theorem atlas_zero_eq : (Qat (0 : ℝ)) = ν := by
  rw [atlasTheta_zero, Submodule.coe_zero, familyMeasure_zero_eq hS ν]

include hfin

/-- The response of a bounded observable along the atlas as a finite combination of feature
responses: `E_{Q_t}[φ ℓ_t] = ⟨β_t, M_t⟩ E_{Q_t}φ − Σⱼ β_{t,j} E_{Q_t}[φ Sⱼ]`. -/
theorem integral_mul_atlasScore_eq {φ : X → ℝ} (hφ : Bdd φ) (t : ℝ) :
    ∫ x, φ x * atlasScore hS ν hfin t x ∂(Qat t) =
      dotJ (atlasVel hS ν hfin t : J → ℝ) (atlasPath S ν M t) * (∫ x, φ x ∂(Qat t)) -
        ∑ j, (atlasVel hS ν hfin t : J → ℝ) j * ∫ x, φ x * S j x ∂(Qat t) := by
  have := isProbabilityMeasure_family hS ν (atlasTheta hS ν M t : J → ℝ)
  unfold atlasScore
  exact integral_mul_sub_dirLoss hS _ hφ _ _

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)) {s : ℝ}
  (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
include hrel hs0 hs1

/-- **First derivative of the response along the atlas**: `d/ds E_{Q_s}φ = E_{Q_s}[φ ℓ_s]`. -/
theorem hasDerivAt_integral_atlas {φ : X → ℝ} (hφ : Bdd φ) :
    HasDerivAt (fun t ↦ ∫ x, φ x ∂(Qat t))
      (∫ x, φ x * atlasScore hS ν hfin s x ∂(Qat s)) s := by
  have hP := isProbabilityMeasure_family hS ν (atlasTheta hS ν M s : J → ℝ)
  have h := hasDerivAt_integral_familyMeasure_path hS ν
    (hasDerivAt_atlasTheta_coe' hS ν hfin hrel hs0 hs1) hφ
  refine h.congr_deriv ?_
  unfold lawCov
  rw [integral_dirLoss_atlasTheta hS ν hfin hrel hs0 hs1, integral_mul_atlasScore_eq hS ν hfin hφ,
    integral_mul_dirLoss hS _ hφ]
  ring

/-- **Second derivative of the response along the atlas**:
`d²/ds² E_{Q_s}φ = E_{Q_s}[φ N_{M_s}(ℓ_s²)]`. -/
theorem hasDerivAt_integral_atlasScore {φ : X → ℝ} (hφ : Bdd φ) :
    HasDerivAt (fun t ↦ ∫ x, φ x * atlasScore hS ν hfin t x ∂(Qat t))
      (∫ x, φ x * normalProj hS ν (atlasPath S ν M s) (bdd_atlasScore_sq hS ν hfin (s := s)) x
        ∂(Qat s)) s := by
  have hP := isProbabilityMeasure_family hS ν (atlasTheta hS ν M s : J → ℝ)
  have hrel' := atlas_mem_intrinsicInterior' hS ν hfin hrel hs0 hs1
  have hβ := hasDerivAt_atlasVel_coe hS ν hfin hrel hs0 hs1
  have hM := hasDerivAt_atlasPath ν (S := S) (M := M) s
  have hE := hasDerivAt_integral_atlas hS ν hfin hrel hs0 hs1 hφ
  have hEj : ∀ j, HasDerivAt (fun t ↦ ∫ x, φ x * S j x ∂(Qat t))
      (∫ x, (φ x * S j x) * atlasScore hS ν hfin s x ∂(Qat s)) s := fun j ↦
    hasDerivAt_integral_atlas hS ν hfin hrel hs0 hs1 (hφ.mul (hS j))
  have hβj : ∀ j, HasDerivAt (fun t ↦ (atlasVel hS ν hfin t : J → ℝ) j)
      ((atlasAccel hS ν hfin hrel hs0 hs1 : J → ℝ) j) s := fun j ↦ hasDerivAt_pi.mp hβ j
  have hA : HasDerivAt (fun t ↦ dotJ (atlasVel hS ν hfin t : J → ℝ) (atlasPath S ν M t))
      (dotJ (atlasAccel hS ν hfin hrel hs0 hs1 : J → ℝ) (atlasPath S ν M s) +
        dotJ (atlasVel hS ν hfin s : J → ℝ)
          (M - meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0)) s := by
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
      (hasDerivAt_pi.1 hβ i).mul (hasDerivAt_pi.1 hM i)
    refine h.congr_deriv ?_
    simp only [dotJ, Finset.sum_add_distrib]
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun j _ ↦ (hβj j).mul (hEj j)
  have h := (hA.mul hE).sub hsum
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun t ↦
    (integral_mul_atlasScore_eq hS ν hfin hφ t))).congr_deriv ?_
  -- the target as a combination of integrals
  have hb := bdd_atlasScore_sq hS ν hfin (s := s)
  have hκ := atlasCurv_eq_integral_score_sq hS ν hfin hrel hs0 hs1
  have hN : ∫ x, φ x * normalProj hS ν (atlasPath S ν M s) hb x ∂(Qat s) =
      (∫ x, (φ x * atlasScore hS ν hfin s x) * atlasScore hS ν hfin s x ∂(Qat s)) -
      atlasCurv hS ν hfin s * (∫ x, φ x ∂(Qat s)) -
      ∫ x, φ x * regProj hS ν (atlasPath S ν M s) hb x ∂(Qat s) := by
    have i1 : Integrable (fun x ↦ (φ x * atlasScore hS ν hfin s x) * atlasScore hS ν hfin s x)
        (Qat s) := integrable_of_bdd_prob _ ((hφ.mul (bdd_atlasScore hS ν hfin)).mul
          (bdd_atlasScore hS ν hfin))
    have i2 : Integrable (fun x ↦ φ x * atlasCurv hS ν hfin s) (Qat s) :=
      (integrable_of_bdd_prob _ hφ).mul_const _
    have i3 : Integrable (fun x ↦ φ x * regProj hS ν (atlasPath S ν M s) hb x) (Qat s) :=
      integrable_of_bdd_prob _ (hφ.mul (bdd_responseScore hS ν _ _))
    have i12 : Integrable (fun x ↦ (φ x * atlasScore hS ν hfin s x) * atlasScore hS ν hfin s x -
        φ x * atlasCurv hS ν hfin s) (Qat s) := i1.sub i2
    have hκ' : atlasCurv hS ν hfin s = ∫ y, atlasScore hS ν hfin s y ^ 2
        ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
          (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
            (one_integral_pos ν) hS (atlasPath S ν M s)) := by
      unfold atlasTheta at hκ
      exact hκ
    have e : (fun x ↦ φ x * normalProj hS ν (atlasPath S ν M s) hb x) = fun x ↦
        (φ x * atlasScore hS ν hfin s x) * atlasScore hS ν hfin s x -
        φ x * atlasCurv hS ν hfin s - φ x * regProj hS ν (atlasPath S ν M s) hb x := by
      funext x
      unfold normalProj
      rw [← hκ']
      ring
    rw [e, integral_sub i12 i3, integral_sub i1 i2, integral_mul_const]
    ring
  have hT1 : ∫ x, (φ x * atlasScore hS ν hfin s x) * atlasScore hS ν hfin s x ∂(Qat s) =
      dotJ (atlasVel hS ν hfin s : J → ℝ) (atlasPath S ν M s) *
        (∫ x, φ x * atlasScore hS ν hfin s x ∂(Qat s)) -
      ∑ j, (atlasVel hS ν hfin s : J → ℝ) j *
        ∫ x, (φ x * S j x) * atlasScore hS ν hfin s x ∂(Qat s) := by
    rw [integral_mul_atlasScore_eq hS ν hfin (hφ.mul (bdd_atlasScore hS ν hfin))]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  have hT2 : ∫ x, φ x * regProj hS ν (atlasPath S ν M s) hb x ∂(Qat s) =
      dotJ (atlasBend hS ν hfin hrel hs0 hs1 : J → ℝ) (atlasPath S ν M s) *
        (∫ x, φ x ∂(Qat s)) -
      ∑ j, (atlasBend hS ν hfin hrel hs0 hs1 : J → ℝ) j * ∫ x, φ x * S j x ∂(Qat s) := by
    rw [atlasBend_eq_respCov hS ν hfin hrel hs0 hs1]
    unfold regProj
    conv_lhs => simp only [responseScore_apply hS ν (M := atlasPath S ν M s)
      ⟨respCov hS ν (atlasPath S ν M s) (fun x ↦ atlasScore hS ν hfin s x ^ 2),
        respCov_mem_dirSpan hS ν hb⟩]
    exact integral_mul_sub_dirLoss hS _ hφ _ _
  rw [hN, hT1, hT2, atlasAccel_eq_neg_atlasBend, Submodule.coe_neg, dotJ_neg_left]
  unfold atlasCurv
  simp only [Pi.neg_apply, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

omit hfin hrel hs0 hs1 in
/-- **The fibre identity**: for a data law `D` with response `M`, `E_D[N_M φ] = E_D φ − E_{Π(M)} φ`:
the normal part of an observable measures exactly what the reconstruction misses. -/
theorem integral_normalProj_eq_sub (D : Measure X) [IsProbabilityMeasure D]
    (hD : (fun j ↦ ∫ x, S j x ∂D) = M) {φ : X → ℝ} (hφ : Bdd φ) :
    ∫ x, normalProj hS ν M hφ x ∂D = (∫ x, φ x ∂D) -
      ∫ x, φ x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
          (one_integral_pos ν) hS M) := by
  have h1 : Integrable (fun x ↦ φ x - ∫ y, φ y ∂familyMeasure ν (fun _ ↦ (1 : ℝ))
      (fun _ ↦ (0 : ℝ)) S 1 (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS M)) D := (integrable_of_bdd_prob _ hφ).sub (integrable_const _)
  have h3 : Integrable (regProj hS ν M hφ) D :=
    integrable_of_bdd_prob _ (bdd_responseScore hS ν M _)
  unfold normalProj
  rw [integral_sub h1 h3, integral_sub (integrable_of_bdd_prob _ hφ) (integrable_const _),
    integral_const, probReal_univ, one_smul]
  unfold regProj
  simp only [responseScore_apply]
  rw [integral_sub (integrable_const _) (integrable_of_bdd_prob _ (bdd_dirLoss hS _)),
    integral_const, probReal_univ, one_smul, ← dotJ_integral_eq D hS, hD]
  ring

omit [Fintype J] [Nonempty J] hS hfin hrel hs0 hs1 in
/-- `|Cov_ρ(f,g)| ≤ 2 B_f B_g` for bounded observables. -/
theorem abs_lawCov_le (ρ : Measure X) [IsProbabilityMeasure ρ] {f g : X → ℝ} {Bf Bg : ℝ}
    (hf : ∀ x, |f x| ≤ Bf) (hg : ∀ x, |g x| ≤ Bg) : |lawCov ρ f g| ≤ 2 * Bf * Bg := by
  have hBf : 0 ≤ Bf := (abs_nonneg _).trans (hf (Classical.arbitrary X))
  have hBg : 0 ≤ Bg := (abs_nonneg _).trans (hg (Classical.arbitrary X))
  have h1 : |∫ x, f x * g x ∂ρ| ≤ Bf * Bg := by
    have := norm_integral_le_of_norm_le (integrable_const (Bf * Bg)) (μ := ρ)
      (f := fun x ↦ f x * g x) (Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hf x) (hg x) (abs_nonneg _) hBf)
    rwa [integral_const, probReal_univ, one_smul, Real.norm_eq_abs] at this
  have h2 : |∫ x, f x ∂ρ| ≤ Bf := by
    have := norm_integral_le_of_norm_le (integrable_const Bf) (μ := ρ) (f := f)
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hf x)
    rwa [integral_const, probReal_univ, one_smul, Real.norm_eq_abs] at this
  have h3 : |∫ x, g x ∂ρ| ≤ Bg := by
    have := norm_integral_le_of_norm_le (integrable_const Bg) (μ := ρ) (f := g)
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hg x)
    rwa [integral_const, probReal_univ, one_smul, Real.norm_eq_abs] at this
  unfold lawCov
  calc |(∫ x, f x * g x ∂ρ) - (∫ x, f x ∂ρ) * ∫ x, g x ∂ρ|
      ≤ |∫ x, f x * g x ∂ρ| + |(∫ x, f x ∂ρ) * ∫ x, g x ∂ρ| := abs_sub _ _
    _ ≤ Bf * Bg + Bf * Bg := by
        rw [abs_mul]
        exact add_le_add h1 (mul_le_mul h2 h3 (abs_nonneg _) hBf)
    _ = 2 * Bf * Bg := by ring

omit [Nonempty X] [Fintype J] [Nonempty J] hS hfin hrel hs0 hs1 in
theorem abs_integral_le_of_abs_le (ρ : Measure X) [IsProbabilityMeasure ρ] {f : X → ℝ} {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) : |∫ x, f x ∂ρ| ≤ B := by
  have := norm_integral_le_of_norm_le (integrable_const B) (μ := ρ) (f := f)
    (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hf x)
  rwa [integral_const, probReal_univ, one_smul, Real.norm_eq_abs] at this

omit hs0 hs1 in
/-- The inverse chart derivative is continuous along the atlas. -/
theorem continuousOn_ringInverse_chartDeriv_atlas :
    ContinuousOn (fun t ↦ Ring.inverse (chartDeriv measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS (atlasTheta hS ν M t))) (Icc (0 : ℝ) 1) := by
  intro t ht
  have hG := (hasDerivAt_chartDeriv_atlas hS ν hfin hrel ht.1 ht.2).continuousAt
  have hu : IsUnit (chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS (atlasTheta hS ν M t)) := by
    rw [← coe_chartDerivEquiv]
    exact ((ContinuousLinearEquiv.unitsEquiv ℝ (dirSpan ν (fun _ ↦ (1 : ℝ)) S)).symm
      (chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS (atlasTheta hS ν M t))).isUnit
  obtain ⟨u, hu⟩ := hu
  have h := NormedRing.inverse_continuousAt u
  rw [hu] at h
  exact (ContinuousAt.comp (f := fun t ↦ chartDeriv measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS (atlasTheta hS ν M t)) h hG).continuousWithinAt

omit hs0 hs1 in
/-- The inverse chart derivative is bounded along the atlas. -/
theorem exists_bound_ringInverse_atlas :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖Ring.inverse (chartDeriv measurable_const
      (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS
        (atlasTheta hS ν M t))‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_ringInverse_chartDeriv_atlas hS ν hfin hrel)
  exact ⟨max C 0, le_max_right _ _, fun t ht ↦ (hC t ht).trans (le_max_left _ _)⟩

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] hfin hrel hs0 hs1 in
/-- The atlas path is bounded. -/
theorem norm_atlasPath_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖atlasPath S ν M t‖ ≤ ‖meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0‖ + ‖M‖ := by
  unfold atlasPath
  calc ‖(1 - t) • meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0 + t • M‖
      ≤ ‖(1 - t) • meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0‖ + ‖t • M‖ := norm_add_le _ _
    _ = |1 - t| * ‖meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0‖ + |t| * ‖M‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * ‖meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0‖ + 1 * ‖M‖ := by
        gcongr
        · rw [abs_le]
          constructor <;> linarith [ht.1, ht.2]
        · rw [abs_le]
          constructor <;> linarith [ht.1, ht.2]
    _ = _ := by ring

omit hs0 hs1 in
/-- **The second-derivative field is interval integrable on `[0,1]`.** -/
theorem intervalIntegrable_integral_normalProj_atlas {φ : X → ℝ} (hφ : Bdd φ) :
    IntervalIntegrable (fun t ↦ ∫ x, φ x * normalProj hS ν (atlasPath S ν M t)
      (bdd_atlasScore_sq hS ν hfin (s := t)) x ∂(Qat t)) volume 0 1 := by
  -- constants
  choose Mj hMj using fun j ↦ (hS j).2
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, |S j x| ≤ B :=
    ⟨∑ j, |Mj j|, Finset.sum_nonneg fun j _ ↦ abs_nonneg _, fun j x ↦
      (hMj j x).trans ((le_abs_self _).trans (Finset.single_le_sum
        (f := fun j ↦ |Mj j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ j)))⟩
  obtain ⟨hφm, Mφ, hφb⟩ := hφ
  have hMφ : 0 ≤ Mφ := (abs_nonneg _).trans (hφb (Classical.arbitrary X))
  obtain ⟨Cβ, hCβ0, hCβ⟩ := exists_bound_atlasVel hS ν hfin hrel
  obtain ⟨CR, hCR0, hCR⟩ := exists_bound_ringInverse_atlas hS ν hfin hrel
  obtain ⟨CM, hCM⟩ : ∃ CM : ℝ, CM = ‖meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0‖ + ‖M‖ :=
    ⟨_, rfl⟩
  have hCM0 : 0 ≤ CM := by rw [hCM]; positivity
  obtain ⟨Kℓ, hKℓ⟩ : ∃ Kℓ : ℝ, Kℓ = (Fintype.card J : ℝ) * Cβ * (CM + B) := ⟨_, rfl⟩
  have hKℓ0 : 0 ≤ Kℓ := by rw [hKℓ]; positivity
  -- pointwise bound on the score
  have hscore : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, |atlasScore hS ν hfin t x| ≤ Kℓ := fun t ht x ↦ by
    unfold atlasScore
    have h1 := abs_dotJ_le_card_mul (atlasVel hS ν hfin t : J → ℝ) (atlasPath S ν M t)
    have h2 := abs_dirLoss_le_card_mul hB0 hB (atlasVel hS ν hfin t : J → ℝ) x
    have hβ : ‖(atlasVel hS ν hfin t : J → ℝ)‖ ≤ Cβ := by
      rw [Submodule.norm_coe]
      exact hCβ t ht
    have hMt := norm_atlasPath_le ν (S := S) (M := M) t ht
    rw [← hCM] at hMt
    calc |dotJ (atlasVel hS ν hfin t : J → ℝ) (atlasPath S ν M t) -
          dirLoss S (atlasVel hS ν hfin t : J → ℝ) x|
        ≤ |dotJ (atlasVel hS ν hfin t : J → ℝ) (atlasPath S ν M t)| +
          |dirLoss S (atlasVel hS ν hfin t : J → ℝ) x| := abs_sub _ _
      _ ≤ (Fintype.card J : ℝ) * Cβ * CM + (Fintype.card J : ℝ) * B * Cβ := by
          refine add_le_add (h1.trans ?_) (h2.trans ?_)
          · have := mul_le_mul hβ hMt (norm_nonneg _) hCβ0
            calc (Fintype.card J : ℝ) * ‖(atlasVel hS ν hfin t : J → ℝ)‖ * ‖atlasPath S ν M t‖
                = (Fintype.card J : ℝ) * (‖(atlasVel hS ν hfin t : J → ℝ)‖ * ‖atlasPath S ν M t‖) :=
                  by ring
              _ ≤ (Fintype.card J : ℝ) * (Cβ * CM) := by gcongr
              _ = _ := by ring
          · exact mul_le_mul_of_nonneg_left hβ (by positivity)
      _ = Kℓ := by rw [hKℓ]; ring
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  -- the field is a derivative, hence measurable
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      deriv (fun t ↦ ∫ x, φ x * atlasScore hS ν hfin t x ∂(Qat t)) t =
      ∫ x, φ x * normalProj hS ν (atlasPath S ν M t) (bdd_atlasScore_sq hS ν hfin (s := t)) x
        ∂(Qat t) := fun t ht ↦
    (hasDerivAt_integral_atlasScore hS ν hfin hrel ht.1 ht.2 ⟨hφm, Mφ, hφb⟩).deriv
  refine (Integrable.of_bound (measurable_deriv _).aestronglyMeasurable
    (Mφ * (Kℓ ^ 2 + Kℓ ^ 2 + (Fintype.card J : ℝ) * (CR * (2 * B * Kℓ ^ 2)) * (CM + B))) ?_).congr
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ hderiv t ⟨ht.1.le, ht.2⟩)
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun t ht ↦ ?_
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  rw [hderiv t ht', Real.norm_eq_abs]
  have hP := isProbabilityMeasure_family hS ν (atlasTheta hS ν M t : J → ℝ)
  have hrel' := atlas_mem_intrinsicInterior' hS ν hfin hrel ht'.1 ht'.2
  -- bound on the normal projection
  have hN : ∀ x, |normalProj hS ν (atlasPath S ν M t) (bdd_atlasScore_sq hS ν hfin (s := t)) x| ≤
      Kℓ ^ 2 + Kℓ ^ 2 + (Fintype.card J : ℝ) * (CR * (2 * B * Kℓ ^ 2)) * (CM + B) := fun x ↦ by
    have hsq : ∀ y, |atlasScore hS ν hfin t y ^ 2| ≤ Kℓ ^ 2 := fun y ↦ by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hscore t ht' y) 2
    have hint : |∫ y, atlasScore hS ν hfin t y ^ 2 ∂(Qat t)| ≤ Kℓ ^ 2 :=
      abs_integral_le_of_abs_le _ hsq
    -- the regression term
    have hc : ∀ j, |respCov hS ν (atlasPath S ν M t) (fun y ↦ atlasScore hS ν hfin t y ^ 2) j| ≤
        2 * B * Kℓ ^ 2 := fun j ↦ by
      unfold respCov
      unfold atlasTheta at hP
      exact abs_lawCov_le _ (hB j) hsq
    have hcn : ‖(⟨respCov hS ν (atlasPath S ν M t) (fun y ↦ atlasScore hS ν hfin t y ^ 2),
        respCov_mem_dirSpan hS ν (bdd_atlasScore_sq hS ν hfin (s := t))⟩ :
          dirSpan ν (fun _ ↦ (1 : ℝ)) S)‖ ≤ 2 * B * Kℓ ^ 2 := by
      rw [← Submodule.norm_coe, Submodule.coe_mk]
      exact (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j ↦ by
        rw [Real.norm_eq_abs]
        exact hc j
    have hbend : ‖(atlasBend hS ν hfin hrel ht'.1 ht'.2 : J → ℝ)‖ ≤ CR * (2 * B * Kℓ ^ 2) := by
      rw [atlasBend_eq_respCov hS ν hfin hrel ht'.1 ht'.2, Submodule.norm_coe,
        ← ContinuousLinearEquiv.coe_coe, coe_chartDerivEquiv_symm]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have := hCR t ht'
      unfold atlasTheta at this
      exact mul_le_mul this hcn (norm_nonneg _) hCR0
    have hreg : |regProj hS ν (atlasPath S ν M t) (bdd_atlasScore_sq hS ν hfin (s := t)) x| ≤
        (Fintype.card J : ℝ) * (CR * (2 * B * Kℓ ^ 2)) * (CM + B) := by
      have e : regProj hS ν (atlasPath S ν M t) (bdd_atlasScore_sq hS ν hfin (s := t)) x =
          dotJ (atlasBend hS ν hfin hrel ht'.1 ht'.2 : J → ℝ) (atlasPath S ν M t) -
            dirLoss S (atlasBend hS ν hfin hrel ht'.1 ht'.2 : J → ℝ) x := by
        rw [atlasBend_eq_respCov hS ν hfin hrel ht'.1 ht'.2]
        rfl
      rw [e]
      have hMt := norm_atlasPath_le ν (S := S) (M := M) t ht'
      rw [← hCM] at hMt
      calc |dotJ (atlasBend hS ν hfin hrel ht'.1 ht'.2 : J → ℝ) (atlasPath S ν M t) -
            dirLoss S (atlasBend hS ν hfin hrel ht'.1 ht'.2 : J → ℝ) x|
          ≤ |dotJ (atlasBend hS ν hfin hrel ht'.1 ht'.2 : J → ℝ) (atlasPath S ν M t)| +
            |dirLoss S (atlasBend hS ν hfin hrel ht'.1 ht'.2 : J → ℝ) x| := abs_sub _ _
        _ ≤ (Fintype.card J : ℝ) * (CR * (2 * B * Kℓ ^ 2)) * CM +
            (Fintype.card J : ℝ) * B * (CR * (2 * B * Kℓ ^ 2)) := by
            refine add_le_add ((abs_dotJ_le_card_mul _ _).trans ?_)
              ((abs_dirLoss_le_card_mul hB0 hB _ x).trans ?_)
            · calc (Fintype.card J : ℝ) * ‖(atlasBend hS ν hfin hrel ht'.1 ht'.2 : J → ℝ)‖ *
                  ‖atlasPath S ν M t‖
                  = (Fintype.card J : ℝ) * (‖(atlasBend hS ν hfin hrel ht'.1 ht'.2 : J → ℝ)‖ *
                    ‖atlasPath S ν M t‖) := by ring
                _ ≤ (Fintype.card J : ℝ) * ((CR * (2 * B * Kℓ ^ 2)) * CM) := by
                    gcongr
                _ = _ := by ring
            · exact mul_le_mul_of_nonneg_left hbend (by positivity)
        _ = _ := by ring
    unfold normalProj
    calc |atlasScore hS ν hfin t x ^ 2 - (∫ y, atlasScore hS ν hfin t y ^ 2 ∂familyMeasure ν
          (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (responseTheta measurable_const
            (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS (atlasPath S ν M t))) -
          regProj hS ν (atlasPath S ν M t) (bdd_atlasScore_sq hS ν hfin (s := t)) x|
        ≤ |atlasScore hS ν hfin t x ^ 2 - ∫ y, atlasScore hS ν hfin t y ^ 2 ∂familyMeasure ν
          (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (responseTheta measurable_const
            (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS (atlasPath S ν M t))| +
          |regProj hS ν (atlasPath S ν M t) (bdd_atlasScore_sq hS ν hfin (s := t)) x| :=
          abs_sub _ _
      _ ≤ (Kℓ ^ 2 + Kℓ ^ 2) + (Fintype.card J : ℝ) * (CR * (2 * B * Kℓ ^ 2)) * (CM + B) := by
          refine add_le_add ((abs_sub _ _).trans (add_le_add (hsq x) ?_)) hreg
          unfold atlasTheta at hint
          exact hint
      _ = _ := by ring
  refine abs_integral_le_of_abs_le _ fun x ↦ ?_
  rw [abs_mul]
  exact mul_le_mul (hφb x) (hN x) (abs_nonneg _) hMφ

omit hs0 hs1 in
/-- **Taylor's formula with integral remainder along the atlas**:
`E_{Q_1}φ − E_{Q_0}φ = E_{Q_0}[φ ℓ_0] + ∫₀¹ (1−s) E_{Q_s}[φ N_{M_s}(ℓ_s²)] ds`. -/
theorem integral_atlas_taylor {φ : X → ℝ} (hφ : Bdd φ) :
    (∫ x, φ x ∂(Qat (1 : ℝ))) - (∫ x, φ x ∂(Qat (0 : ℝ))) =
      (∫ x, φ x * atlasScore hS ν hfin 0 x ∂(Qat (0 : ℝ))) +
        ∫ t in (0 : ℝ)..1, (1 - t) * ∫ x, φ x * normalProj hS ν (atlasPath S ν M t)
          (bdd_atlasScore_sq hS ν hfin (s := t)) x ∂(Qat t) := by
  have hI : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have h1 : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) t := fun t _ ↦ by
    simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
  have h2 : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t ↦ ∫ x, φ x * atlasScore hS ν hfin t x ∂(Qat t))
        (∫ x, φ x * normalProj hS ν (atlasPath S ν M t) (bdd_atlasScore_sq hS ν hfin (s := t)) x
          ∂(Qat t)) t := fun t ht ↦ by
    rw [hI] at ht
    exact hasDerivAt_integral_atlasScore hS ν hfin hrel ht.1 ht.2 hφ
  have h3 : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t ↦ ∫ x, φ x ∂(Qat t))
      (∫ x, φ x * atlasScore hS ν hfin t x ∂(Qat t)) t := fun t ht ↦ by
    rw [hI] at ht
    exact hasDerivAt_integral_atlas hS ν hfin hrel ht.1 ht.2 hφ
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul h1 h2 intervalIntegrable_const
    (intervalIntegrable_integral_normalProj_atlas hS ν hfin hrel hφ)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt h3
    (HasDerivAt.continuousOn h2).intervalIntegrable
  simp only [sub_self, zero_mul, sub_zero, one_mul, neg_one_mul, intervalIntegral.integral_neg]
    at hibp
  rw [hftc] at hibp
  linarith

omit hs0 hs1 in
/-- **The accounting identity**: for every data law `D` with response `M` and every bounded
observable `φ`,
`E_D φ − E_ν φ = E_ν[φ ℓ_0] + ∫₀¹ (1−s) E_{Q_s}[φ N_{M_s}(ℓ_s²)] ds + E_D[N_M φ]`:
the change of the posterior expectation from the featureless posterior to the data is the baseline
linear susceptibility, plus the accumulated nonlinear response along the atlas, plus the
feature-invisible residual between the data law and its reconstruction. -/
theorem response_accounting (D : Measure X) [IsProbabilityMeasure D]
    (hD : (fun j ↦ ∫ x, S j x ∂D) = M) {φ : X → ℝ} (hφ : Bdd φ) :
    (∫ x, φ x ∂D) - (∫ x, φ x ∂ν) =
      (∫ x, φ x * atlasScore hS ν hfin 0 x ∂ν) +
        (∫ t in (0 : ℝ)..1, (1 - t) * ∫ x, φ x * normalProj hS ν (atlasPath S ν M t)
          (bdd_atlasScore_sq hS ν hfin (s := t)) x ∂(Qat t)) +
        ∫ x, normalProj hS ν M hφ x ∂D := by
  have h := integral_atlas_taylor hS ν hfin hrel hφ
  have h0 := atlas_zero_eq hS ν (M := M)
  rw [h0] at h
  have hfib := integral_normalProj_eq_sub hS ν D hD hφ
  have h1 : (Qat (1 : ℝ)) = familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν)
        hS M) := by
    rw [atlasTheta_one hS ν]
  rw [h1] at h
  linarith

end Finite

end Laplace.Multi
