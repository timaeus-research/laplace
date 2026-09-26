/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.BregmanGeometry
import Laplace.Multi.DensityDerivative
import Laplace.Multi.ObservableCurvature
import Laplace.Multi.SusceptibilityDefect

/-!
# Skewness controls the variation of the atlas curvature

Along the straight response path `M_s = (1−s)m₀ + sM` with natural coordinates `θ_s` and velocity
`β_s = (Dm(θ_s)|_𝕍)⁻¹Δ`, the atlas curvature `κ(s) = Var_{Q_s}⟨β_s, S⟩` is differentiable, with

`κ'(s) = T_{Q_s}(f_s, f_s, f_s)`, `f_s = ⟨β_s, S⟩`

(the third central moment of the velocity loss), equivalently `κ'(s) = −E_{Q_s} ℓ_s³` for the
centred score `ℓ_s = E_{Q_s} f_s − f_s`. The proof avoids differentiating the inverse covariance:
the exact
identity `κ(t) − κ(s) = Cov_{Q_s}(f_t, f_s) − Cov_{Q_t}(f_t, f_s)` (from the constancy of the
first-order transport `Cov_{Q_s}(⟨e,S⟩, f_s) = −⟨e, Δ⟩`) splits into a frozen-argument covariance
increment, differentiated by `hasDerivAt_lawCov_familyMeasure_path`, and a bilinear remainder
`⟨β_t − β_s, W_t − W_s⟩` which is `o(t − s)` by continuity of the velocity.

Integrating by parts the landed asymmetry formula `KL(Π(M)‖ν) − KL(ν‖Π(M)) = ∫₀¹ (1−2s)κ`,

`KL(Π(M)‖ν) − KL(ν‖Π(M)) = ∫₀¹ s(1−s) E_{Q_s} ℓ_s³ ds`:

the asymmetry of information is accumulated directional skewness of the response score.
-/

open MeasureTheory Filter Topology Set InformationTheory Asymptotics
open scoped ENNReal

namespace Laplace.Multi

section Bounds

variable {X : Type*} [MeasurableSpace X] [Nonempty X] (ρ : Measure X) [IsProbabilityMeasure ρ]

/-- The third central moment of a function bounded by `B` is bounded by `8B³`. -/
theorem abs_thirdCentral_self_le {f : X → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    |thirdCentral ρ f f f| ≤ 8 * B ^ 3 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary X))
  have hm : |∫ y, f y ∂ρ| ≤ B := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (integrable_const B)
      (Eventually.of_forall fun x ↦ ?_)).trans ?_
    · rw [Real.norm_eq_abs]
      exact hB x
    · simp
  have hc : ∀ x, |f x - ∫ y, f y ∂ρ| ≤ 2 * B := fun x ↦
    (abs_sub _ _).trans (by linarith [hB x])
  unfold thirdCentral
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (integrable_const (8 * B ^ 3))
    (Eventually.of_forall fun x ↦ ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |f x - ∫ y, f y ∂ρ| * |f x - ∫ y, f y ∂ρ| * |f x - ∫ y, f y ∂ρ|
        ≤ (2 * B) * (2 * B) * (2 * B) :=
          mul_le_mul (mul_le_mul (hc x) (hc x) (abs_nonneg _) (by positivity)) (hc x)
            (abs_nonneg _) (by positivity)
      _ = 8 * B ^ 3 := by ring
  · simp

omit [Nonempty X] [IsProbabilityMeasure ρ] in
/-- Minus the third central moment is the third moment of the centred score `E f − f`. -/
theorem neg_thirdCentral_self_eq (f : X → ℝ) :
    -thirdCentral ρ f f f = ∫ x, ((∫ y, f y ∂ρ) - f x) ^ 3 ∂ρ := by
  unfold thirdCentral
  rw [← integral_neg]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

end Bounds

section Skew

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤)
include hS hfin

/-- **The exact curvature increment**: `κ(t) − κ(s) = Cov_{Q_s}(f_t, f_s) − Cov_{Q_t}(f_t, f_s)`. -/
theorem atlasCurv_sub_eq (s t : ℝ) :
    atlasCurv hS ν hfin t - atlasCurv hS ν hfin s =
      lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s))
          (dirLoss S (atlasVel hS ν hfin t)) (dirLoss S (atlasVel hS ν hfin s)) -
        lawCov (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M t))
          (dirLoss S (atlasVel hS ν hfin t)) (dirLoss S (atlasVel hS ν hfin s)) := by
  have h1 := lawCov_dirLoss_atlasVel hS ν hfin s (atlasVel hS ν hfin t)
  have h2 := lawCov_dirLoss_atlasVel hS ν hfin t (atlasVel hS ν hfin s)
  rw [lawCov_comm] at h2
  rw [h1, h2]
  rfl

/-- **The derivative of the atlas curvature is the third central moment of the velocity loss**,
given differentiability of the natural coordinates and continuity of the velocity at `s`. -/
theorem hasDerivAt_atlasCurv_of {s : ℝ}
    (hθ : HasDerivAt (fun t ↦ (atlasTheta hS ν M t : J → ℝ)) (atlasVel hS ν hfin s : J → ℝ) s)
    (hvel : ContinuousAt (atlasVel hS ν hfin) s) :
    HasDerivAt (atlasCurv hS ν hfin)
      (thirdCentral (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s))
        (dirLoss S (atlasVel hS ν hfin s)) (dirLoss S (atlasVel hS ν hfin s))
        (dirLoss S (atlasVel hS ν hfin s))) s := by
  obtain ⟨fs, hfs⟩ : ∃ fs : X → ℝ, fs = dirLoss S (atlasVel hS ν hfin s : J → ℝ) := ⟨_, rfl⟩
  have hfsB : Bdd fs := by rw [hfs]; exact bdd_dirLoss hS _
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → Measure X, Q = fun t ↦
    familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M t) := ⟨_, rfl⟩
  have hQP : ∀ t, IsProbabilityMeasure (Q t) := fun t ↦ by
    rw [hQ]
    exact isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS
      (t := 1) _
  -- frozen-argument covariance and its derivative
  have hC : HasDerivAt (fun t ↦ lawCov (Q t) fs fs)
      (-thirdCentral (Q s) fs fs (dirLoss S (atlasVel hS ν hfin s))) s := by
    have h := hasDerivAt_lawCov_familyMeasure_path hS ν hθ hfsB hfsB
    rw [hQ]
    exact h
  have hW : ∀ j, HasDerivAt (fun t ↦ lawCov (Q t) (S j) fs)
      (-thirdCentral (Q s) (S j) fs (dirLoss S (atlasVel hS ν hfin s))) s := fun j ↦ by
    have h := hasDerivAt_lawCov_familyMeasure_path hS ν hθ (hS j) hfsB
    rw [hQ]
    exact h
  -- the velocity increment vanishes
  have hβ : ∀ j, Tendsto (fun t ↦ (atlasVel hS ν hfin t : J → ℝ) j -
      (atlasVel hS ν hfin s : J → ℝ) j) (𝓝 s) (𝓝 0) := fun j ↦ by
    have h := ((continuous_apply j).continuousAt.comp
      (continuous_subtype_val.continuousAt.comp hvel)).tendsto
    have h2 := h.sub_const ((atlasVel hS ν hfin s : J → ℝ) j)
    simpa [Function.comp_def] using h2
  -- the bilinear remainder is `o(t − s)`
  have hR : (fun t ↦ ∑ j, ((atlasVel hS ν hfin t : J → ℝ) j - (atlasVel hS ν hfin s : J → ℝ) j) *
      (lawCov (Q t) (S j) fs - lawCov (Q s) (S j) fs)) =o[𝓝 s] fun t ↦ t - s := by
    have h : ∀ j ∈ (Finset.univ : Finset J), (fun t ↦ ((atlasVel hS ν hfin t : J → ℝ) j -
        (atlasVel hS ν hfin s : J → ℝ) j) * (lawCov (Q t) (S j) fs - lawCov (Q s) (S j) fs))
        =o[𝓝 s] fun t ↦ t - s := fun j _ ↦ by
      have h1 : (fun t ↦ (atlasVel hS ν hfin t : J → ℝ) j - (atlasVel hS ν hfin s : J → ℝ) j)
          =o[𝓝 s] fun _ ↦ (1 : ℝ) := (isLittleO_one_iff ℝ).2 (hβ j)
      have h2 := (hW j).isBigO_sub
      have h3 := h1.mul_isBigO h2
      refine h3.congr_right fun t ↦ ?_
      simp
    have h4 := IsLittleO.sum h
    refine h4.congr_left fun t ↦ ?_
    simp [Finset.sum_apply]
  -- the exact identity
  have hid : ∀ t, atlasCurv hS ν hfin t - atlasCurv hS ν hfin s =
      -(lawCov (Q t) fs fs - lawCov (Q s) fs fs) -
        ∑ j, ((atlasVel hS ν hfin t : J → ℝ) j - (atlasVel hS ν hfin s : J → ℝ) j) *
          (lawCov (Q t) (S j) fs - lawCov (Q s) (S j) fs) := fun t ↦ by
    have e1 : ∀ t', lawCov (Q t') (dirLoss S (atlasVel hS ν hfin t)) fs =
        lawCov (Q t') fs fs + ∑ j, ((atlasVel hS ν hfin t : J → ℝ) j -
          (atlasVel hS ν hfin s : J → ℝ) j) * lawCov (Q t') (S j) fs := fun t' ↦ by
      have := hQP t'
      have hd : dirLoss S ((atlasVel hS ν hfin t : J → ℝ) - (atlasVel hS ν hfin s : J → ℝ)) =
          fun x ↦ dirLoss S (atlasVel hS ν hfin t) x - fs x := by
        funext x
        rw [hfs]
        simp only [dirLoss, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      have h1 := lawCov_dirLoss_left hS (Q t') ((atlasVel hS ν hfin t : J → ℝ) -
        (atlasVel hS ν hfin s : J → ℝ)) fs hfsB
      rw [hd, lawCov_sub_left_eq (Q t') (bdd_dirLoss hS _) hfsB hfsB] at h1
      simp only [Pi.sub_apply] at h1
      linarith
    have e2 := e1 s
    have e3 := e1 t
    rw [atlasCurv_sub_eq hS ν hfin s t]
    rw [hfs, hQ] at e2 e3 ⊢
    simp only at e2 e3 ⊢
    rw [e2, e3]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hasDerivAt_iff_isLittleO]
  have hC' := hasDerivAt_iff_isLittleO.1 hC
  refine ((hC'.neg_left).sub hR).congr_left fun t ↦ ?_
  rw [hid t, hfs, hQ]
  simp only [smul_eq_mul]
  ring

/-- `κ'(s) = T_{Q_s}(f_s, f_s, f_s)` on `[0, 1)`. -/
theorem hasDerivAt_atlasCurv {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasDerivAt (atlasCurv hS ν hfin)
      (thirdCentral (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s))
        (dirLoss S (atlasVel hS ν hfin s)) (dirLoss S (atlasVel hS ν hfin s))
        (dirLoss S (atlasVel hS ν hfin s))) s :=
  hasDerivAt_atlasCurv_of hS ν hfin (hasDerivAt_atlasTheta_coe hS ν hfin hs0 hs1)
    (continuousAt_atlasVel hS ν hfin hs0 hs1)

variable (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

theorem atlas_mem_intrinsicInterior' {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    atlasPath S ν M s ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
  rcases eq_or_lt_of_le hs1 with rfl | h
  · rw [atlasPath_one]
    exact hrel
  · exact atlas_mem_intrinsicInterior hS ν hfin hs0 h

theorem hasDerivAt_atlasTheta' {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    HasDerivAt (atlasTheta hS ν M) (atlasVel hS ν hfin s) s :=
  hasDerivAt_responseTheta_path measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (atlasPath_sub_mem_dirSpan hS ν hfin)
    (atlas_mem_intrinsicInterior' hS ν hfin hrel hs0 hs1) (hasDerivAt_atlasPath ν s)

theorem hasDerivAt_atlasTheta_coe' {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    HasDerivAt (fun s ↦ (atlasTheta hS ν M s : J → ℝ)) (atlasVel hS ν hfin s : J → ℝ) s :=
  (dirSpan ν (fun _ ↦ (1 : ℝ)) S).subtypeL.hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_atlasTheta' hS ν hfin hrel hs0 hs1)

theorem continuousAt_atlasVel' {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ContinuousAt (atlasVel hS ν hfin) s := by
  have hθ : ContinuousAt (atlasTheta hS ν M) s :=
    (hasDerivAt_atlasTheta' hS ν hfin hrel hs0 hs1).continuousAt
  have hsymm : ContinuousAt (fun s ↦ ((chartDerivEquiv measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) hS (atlasTheta hS ν M s)).symm :
        dirSpan ν (fun _ ↦ (1 : ℝ)) S →L[ℝ] dirSpan ν (fun _ ↦ (1 : ℝ)) S)) s :=
    (continuous_chartDerivEquiv_symm measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos ν) hS).continuousAt.comp hθ
  exact hsymm.clm_apply continuousAt_const

/-- `κ'(s) = T_{Q_s}(f_s, f_s, f_s)` on `[0, 1]` for an interior target. -/
theorem hasDerivAt_atlasCurv' {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    HasDerivAt (atlasCurv hS ν hfin)
      (thirdCentral (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s))
        (dirLoss S (atlasVel hS ν hfin s)) (dirLoss S (atlasVel hS ν hfin s))
        (dirLoss S (atlasVel hS ν hfin s))) s :=
  hasDerivAt_atlasCurv_of hS ν hfin (hasDerivAt_atlasTheta_coe' hS ν hfin hrel hs0 hs1)
    (continuousAt_atlasVel' hS ν hfin hrel hs0 hs1)

/-- The velocity is bounded on `[0, 1]`. -/
theorem exists_bound_atlasVel :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0 : ℝ) 1, ‖atlasVel hS ν hfin s‖ ≤ C := by
  have hcont : ContinuousOn (atlasVel hS ν hfin) (Icc (0 : ℝ) 1) := fun s hs ↦
    (continuousAt_atlasVel' hS ν hfin hrel hs.1 hs.2).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨C, (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩), hC⟩

/-- The derivative of the curvature is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_deriv_atlasCurv :
    IntervalIntegrable (deriv (atlasCurv hS ν hfin)) volume 0 1 := by
  choose Mj hMj using fun j ↦ (hS j).2
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, |S j x| ≤ B :=
    ⟨∑ j, |Mj j|, Finset.sum_nonneg fun j _ ↦ abs_nonneg _, fun j x ↦
      (hMj j x).trans ((le_abs_self _).trans (Finset.single_le_sum
        (f := fun j ↦ |Mj j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ j)))⟩
  obtain ⟨C, hC0, hC⟩ := exists_bound_atlasVel hS ν hfin hrel
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Integrable.of_bound (measurable_deriv _).aestronglyMeasurable
    (8 * ((Fintype.card J : ℝ) * B * C) ^ 3) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun s hs ↦ ?_
  have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
  rw [(hasDerivAt_atlasCurv' hS ν hfin hrel hs'.1 hs'.2).deriv, Real.norm_eq_abs]
  have hP : IsProbabilityMeasure (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (atlasTheta hS ν M s)) :=
    isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS
      (t := 1) (atlasTheta hS ν M s : J → ℝ)
  refine abs_thirdCentral_self_le _ fun x ↦ ?_
  calc |dirLoss S (atlasVel hS ν hfin s) x|
      ≤ (Fintype.card J : ℝ) * B * ‖(atlasVel hS ν hfin s : J → ℝ)‖ :=
        abs_dirLoss_le_card_mul hB0 hB _ x
    _ ≤ (Fintype.card J : ℝ) * B * C := by
        rw [Submodule.norm_coe]
        exact mul_le_mul_of_nonneg_left (hC s hs') (by positivity)

/-- **Information asymmetry is accumulated skewness**:
`KL(Π(M)‖ν) − KL(ν‖Π(M)) = −∫₀¹ s(1−s) T_{Q_s}(f_s,f_s,f_s) ds = ∫₀¹ s(1−s) E_{Q_s} ℓ_s³ ds`. -/
theorem toReal_klDiv_responseProjection_sub_symm_eq_skew :
    (klDiv (responseProjection hS ν M) ν).toReal - (klDiv ν (responseProjection hS ν M)).toReal =
      ∫ s in (0 : ℝ)..1, s * (1 - s) *
        ∫ x, ((∫ y, dirLoss S (atlasVel hS ν hfin s) y
          ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s)) -
          dirLoss S (atlasVel hS ν hfin s) x) ^ 3
          ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (atlasTheta hS ν M s) := by
  rw [toReal_klDiv_responseProjection_sub_symm hS ν hfin hrel, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  have hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ ↦ s * (1 - s)) (1 - 2 * x) x :=
    fun x _ ↦ ((hasDerivAt_id' x).mul ((hasDerivAt_id' x).const_sub 1)).congr_deriv (by ring)
  have hv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (atlasCurv hS ν hfin)
      (deriv (atlasCurv hS ν hfin) x) x := fun x hx ↦ by
    rw [uIcc_of_le zero_le_one] at hx
    exact (hasDerivAt_atlasCurv' hS ν hfin hrel hx.1 hx.2).differentiableAt.hasDerivAt
  have hu' : IntervalIntegrable (fun s : ℝ ↦ 1 - 2 * s) volume 0 1 :=
    (by fun_prop : Continuous fun s : ℝ ↦ 1 - 2 * s).intervalIntegrable 0 1
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'
    (intervalIntegrable_deriv_atlasCurv hS ν hfin hrel)
  simp only [mul_zero, sub_zero, zero_mul, sub_self, zero_sub] at hibp
  have h2 : ∫ x in (0 : ℝ)..1, (1 - 2 * x) * atlasCurv hS ν hfin x =
      ∫ x in (0 : ℝ)..1, -(x * (1 - x) * deriv (atlasCurv hS ν hfin) x) := by
    rw [intervalIntegral.integral_neg, hibp, neg_neg]
  rw [h2]
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [uIcc_of_le zero_le_one] at hs
  rw [(hasDerivAt_atlasCurv' hS ν hfin hrel hs.1 hs.2).deriv, ← neg_thirdCentral_self_eq]
  ring

end Skew

end Laplace.Multi
