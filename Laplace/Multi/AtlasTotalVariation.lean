/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ReconstructionLipschitz
import Laplace.Multi.BoundaryCompletion
import Laplace.Multi.ObservableCurvature

/-!
# The atlas as a curve in total variation

Along the straight atlas `s ↦ Q_s = Π(M_s)` of a finite-rate response, the law moves in total
variation at most as fast as the Fisher speed `√κ_s`:

`∫ |q_s − q_t| dν ≤ ∫_t^s √κ_u du` for `0 ≤ t ≤ s < 1` (`integral_abs_famDens_atlas_sub_le`).

The proof: for a test `|F| ≤ 1` the response `g(u) = E_{Q_u}F` is differentiable on `[0, 1)` with
derivative `E_{Q_u}[F ℓ_u]` (`hasDerivAt_integral_atlas_of_lt`, obtained from the interior
response derivative at the base point `m₀`, so no interior hypothesis on `M` is needed), the
derivative is continuous (`continuousOn_integral_mul_atlasScore`), so the fundamental theorem of
calculus gives `g(s) − g(t) = ∫_t^s E_{Q_u}[Fℓ_u] du`, and `|E_{Q_u}[Fℓ_u]| ≤ E_{Q_u}|ℓ_u| ≤
√(E_{Q_u}ℓ_u²) = √κ_u` (`integral_abs_le_sqrt_integral_sq`). The sign test `F = sign(q_s − q_t)`
converts the bound to total variation. This is the path-length counterpart of the information
bound `(E_{Q_*}F − E_{Q_s}F)² ≤ 2L² ∫_s^1 (1 − u) κ_u du` of `BoundaryCompletion`; the two are
complementary, and finiteness of `∫₀¹ (1 − u) κ_u du` does not imply finiteness of `∫₀¹ √κ_u du`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory

namespace Laplace.Multi

section Generic

variable {X : Type*} [MeasurableSpace X]

/-- **Cauchy–Schwarz**: `∫ |f| dμ ≤ √(∫ f² dμ)` for a bounded measurable `f` and a probability
`μ`. -/
theorem integral_abs_le_sqrt_integral_sq (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ}
    (hf : Bdd f) :
    ∫ x, |f x| ∂μ ≤ √(∫ x, f x ^ 2 ∂μ) := by
  obtain ⟨hm, B, hB⟩ := hf
  have hL : MemLp (fun x ↦ |f x|) 2 μ :=
    MemLp.of_bound hm.abs.aestronglyMeasurable B (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_abs]
      exact hB x)
  have hv := variance_nonneg (fun x ↦ |f x|) μ
  rw [variance_eq_sub hL] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  have hnn : 0 ≤ ∫ x, |f x| ∂μ := integral_nonneg fun x ↦ abs_nonneg _
  exact (Real.le_sqrt hnn (by nlinarith)).2 (by linarith)

end Generic

section Atlas

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {M : J → ℝ}
  (hfin : genRate ν S M ≠ ⊤)
include hS hfin

/-- The reconstruction at the atlas point `s`. -/
local notation "Qat" s => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
  (atlasTheta hS ν M s)

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- **The response of a bounded observable is differentiable along the atlas of any finite-rate
response**, for `u < 1`, with derivative `E_{Q_u}[F ℓ_u]`. -/
theorem hasDerivAt_integral_atlas_of_lt {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {F : X → ℝ}
    (hF : Bdd F) :
    HasDerivAt (fun t ↦ ∫ x, F x ∂(Qat t)) (∫ x, F x * atlasScore hS ν hfin u x ∂(Qat u)) u := by
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : dirSpan ν (fun _ ↦ (1 : ℝ)) S,
      Δ = ⟨M - m₀, sub_mem_dirSpan_of_genRate_ne_top hS ν hfin⟩ := ⟨_, rfl⟩
  have hpath : ∀ t : ℝ,
      atlasPath S ν M t = m₀ + ((t • Δ : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ) := fun t ↦ by
    rw [hΔ, Submodule.coe_smul, Submodule.coe_mk]
    unfold atlasPath
    module
  have hz : m₀ + ((u • Δ : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ) ∈
      intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := by
    rw [← hpath]
    exact atlas_mem_intrinsicInterior hS ν hfin hu0 hu1
  have h := hasFDerivAt_integral_response_at hS ν hF hz
  have hl : HasDerivAt (fun t : ℝ ↦ t • Δ) Δ u := by
    simpa using (hasDerivAt_id u).smul_const Δ
  have h2 := h.comp_hasDerivAt u hl
  have hfun : (fun t ↦ ∫ x, F x ∂(Qat t)) = fun t ↦ ∫ x, F x ∂familyMeasure ν (fun _ ↦ (1 : ℝ))
      (fun _ ↦ (0 : ℝ)) S 1 (responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
        (one_integral_pos ν) hS (m₀ + ((t • Δ : dirSpan ν (fun _ ↦ (1 : ℝ)) S) : J → ℝ))) := by
    funext t
    unfold atlasTheta
    rw [hpath]
  rw [hfun]
  refine h2.congr_deriv ?_
  rw [responseDerivField_apply hS ν hF hz]
  unfold atlasTheta
  rw [hpath u]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [atlasScore_eq_responseScore, hpath u, hΔ]

/-- The curvature is the second moment of the atlas score, for `u < 1` at any finite-rate
response. -/
theorem atlasCurv_eq_integral_score_sq_of_lt {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    atlasCurv hS ν hfin u = ∫ x, atlasScore hS ν hfin u x ^ 2 ∂(Qat u) := by
  have hP := isProbabilityMeasure_family hS ν (atlasTheta hS ν M u : J → ℝ)
  have hmean : ∫ x, dirLoss S (atlasVel hS ν hfin u : J → ℝ) x ∂(Qat u) =
      dotJ (atlasVel hS ν hfin u : J → ℝ) (atlasPath S ν M u) := by
    rw [← dotJ_integral_eq _ hS _, mean_familyMeasure_one_zero hS ν,
      meanMap_atlasTheta hS ν hfin hu0 hu1]
  rw [atlasCurv_eq_priorCov, priorCov_eq_lawCov_familyMeasure hS ν,
    lawCov_self_eq_integral_sq _ (bdd_dirLoss hS _), hmean]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  unfold atlasScore
  ring

/-- The derivative field `u ↦ E_{Q_u}[F ℓ_u]` is continuous on `[0, 1)`. -/
theorem continuousOn_integral_mul_atlasScore {F : X → ℝ} (hF : Bdd F) :
    ContinuousOn (fun u ↦ ∫ x, F x * atlasScore hS ν hfin u x ∂(Qat u)) (Ico (0 : ℝ) 1) := by
  intro u hu
  have e : (fun u ↦ ∫ x, F x * atlasScore hS ν hfin u x ∂(Qat u)) = fun u ↦
      dotJ (atlasVel hS ν hfin u : J → ℝ) (atlasPath S ν M u) * (∫ x, F x ∂(Qat u)) -
        ∑ j, (atlasVel hS ν hfin u : J → ℝ) j * ∫ x, F x * S j x ∂(Qat u) :=
    funext fun u ↦ integral_mul_atlasScore_eq hS ν hfin hF u
  rw [e]
  refine ContinuousAt.continuousWithinAt ?_
  have hβ : ContinuousAt (fun u ↦ (atlasVel hS ν hfin u : J → ℝ)) u :=
    continuous_subtype_val.continuousAt.comp (continuousAt_atlasVel hS ν hfin hu.1 hu.2)
  have hβj : ∀ j, ContinuousAt (fun u ↦ (atlasVel hS ν hfin u : J → ℝ) j) u := fun j ↦
    (continuous_apply j).continuousAt.comp hβ
  have hM : ContinuousAt (atlasPath S ν M) u := (continuous_atlasPath ν).continuousAt
  have hMj : ∀ j, ContinuousAt (fun u ↦ atlasPath S ν M u j) u := fun j ↦
    (continuous_apply j).continuousAt.comp hM
  have hG : ∀ φ : X → ℝ, Bdd φ → ContinuousAt (fun u ↦ ∫ x, φ x ∂(Qat u)) u := fun φ hφ ↦
    (hasDerivAt_integral_atlas_of_lt hS ν hfin hu.1 hu.2 hφ).continuousAt
  have hdot : ContinuousAt (fun u ↦ dotJ (atlasVel hS ν hfin u : J → ℝ) (atlasPath S ν M u)) u := by
    simp only [dotJ]
    exact tendsto_finsetSum Finset.univ fun j _ ↦ (hβj j).mul (hMj j)
  refine (hdot.mul (hG F hF)).sub ?_
  exact tendsto_finsetSum Finset.univ fun j _ ↦ (hβj j).mul (hG _ (hF.mul (hS j)))

/-- **The atlas moves in total variation at most at the Fisher speed**:
`∫ |q_s − q_t| dν ≤ ∫_t^s √κ_u du` for `0 ≤ t ≤ s < 1`. -/
theorem integral_abs_famDens_atlas_sub_le {t s : ℝ} (ht0 : 0 ≤ t) (hts : t ≤ s) (hs1 : s < 1) :
    ∫ x, |famDens S ν (atlasTheta hS ν M s) x - famDens S ν (atlasTheta hS ν M t) x| ∂ν ≤
      ∫ u in t..s, √(atlasCurv hS ν hfin u) := by
  obtain ⟨F, hF⟩ : ∃ F : X → ℝ, F = fun x ↦
      if 0 ≤ famDens S ν (atlasTheta hS ν M s) x - famDens S ν (atlasTheta hS ν M t) x then (1 : ℝ)
      else -1 := ⟨_, rfl⟩
  have hFm : Measurable F := by
    rw [hF]
    exact Measurable.ite (measurableSet_le measurable_const
      ((measurable_famDens hS ν _).sub (measurable_famDens hS ν _))) measurable_const
      measurable_const
  have hF1 : ∀ x, |F x| ≤ 1 := fun x ↦ by
    rw [hF]
    beta_reduce
    split_ifs <;> simp
  have hFb : Bdd F := ⟨hFm, 1, hF1⟩
  have hsub : Icc t s ⊆ Ico (0 : ℝ) 1 := fun u hu ↦ ⟨ht0.trans hu.1, lt_of_le_of_lt hu.2 hs1⟩
  -- the derivative and its integrability
  have hderiv : ∀ u ∈ uIcc t s, HasDerivAt (fun u ↦ ∫ x, F x ∂(Qat u))
      (∫ x, F x * atlasScore hS ν hfin u x ∂(Qat u)) u := fun u hu ↦ by
    rw [uIcc_of_le hts] at hu
    exact hasDerivAt_integral_atlas_of_lt hS ν hfin (hsub hu).1 (hsub hu).2 hFb
  have hint : IntervalIntegrable (fun u ↦ ∫ x, F x * atlasScore hS ν hfin u x ∂(Qat u)) volume
      t s :=
    ((continuousOn_integral_mul_atlasScore hS ν hfin hFb).mono hsub).intervalIntegrable_of_Icc hts
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- the Fisher speed is integrable
  have hκcont : ContinuousOn (fun u ↦ √(atlasCurv hS ν hfin u)) (Icc t s) := fun u hu ↦
    (Real.continuous_sqrt.continuousAt.comp
      (continuousAt_atlasCurv hS ν hfin (hsub hu).1 (hsub hu).2)).continuousWithinAt
  have hκint : IntervalIntegrable (fun u ↦ √(atlasCurv hS ν hfin u)) volume t s :=
    hκcont.intervalIntegrable_of_Icc hts
  -- the pointwise bound `|E[Fℓ_u]| ≤ √κ_u`
  have hbound : ∀ u ∈ Icc t s,
      (∫ x, F x * atlasScore hS ν hfin u x ∂(Qat u)) ≤ √(atlasCurv hS ν hfin u) := by
    intro u hu
    have hP := isProbabilityMeasure_family hS ν (atlasTheta hS ν M u : J → ℝ)
    have hI : Integrable (fun x ↦ |F x * atlasScore hS ν hfin u x|) (Qat u) :=
      (integrable_of_bdd_prob _ (hFb.mul (bdd_atlasScore hS ν hfin))).abs
    have hI' : Integrable (fun x ↦ |atlasScore hS ν hfin u x|) (Qat u) :=
      (integrable_of_bdd_prob _ (bdd_atlasScore hS ν hfin)).abs
    calc ∫ x, F x * atlasScore hS ν hfin u x ∂(Qat u)
        ≤ |∫ x, F x * atlasScore hS ν hfin u x ∂(Qat u)| := le_abs_self _
      _ ≤ ∫ x, |F x * atlasScore hS ν hfin u x| ∂(Qat u) := by
          have := norm_integral_le_integral_norm (μ := Qat u)
            (fun x ↦ F x * atlasScore hS ν hfin u x)
          simpa only [Real.norm_eq_abs] using this
      _ ≤ ∫ x, |atlasScore hS ν hfin u x| ∂(Qat u) := by
          refine integral_mono hI hI' fun x ↦ ?_
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hF1 x)
      _ ≤ √(∫ x, atlasScore hS ν hfin u x ^ 2 ∂(Qat u)) :=
          integral_abs_le_sqrt_integral_sq _ (bdd_atlasScore hS ν hfin)
      _ = √(atlasCurv hS ν hfin u) := by
          rw [atlasCurv_eq_integral_score_sq_of_lt hS ν hfin (hsub hu).1 (hsub hu).2]
  -- the sign test
  have hI : ∀ N : J → ℝ, Integrable (fun x ↦ famDens S ν N x * F x) ν := fun N ↦
    (integrable_famDens hS ν N).mul_bdd hFm.aestronglyMeasurable (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs]
      exact hF1 x)
  have e : ∫ x, |famDens S ν (atlasTheta hS ν M s) x - famDens S ν (atlasTheta hS ν M t) x| ∂ν =
      (∫ x, F x ∂(Qat s)) - ∫ x, F x ∂(Qat t) := by
    rw [integral_famDens_mul hS ν, integral_famDens_mul hS ν, ← integral_sub (hI _) (hI _)]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    rw [hF]
    beta_reduce
    split_ifs with h0
    · rw [abs_of_nonneg h0]
      ring
    · rw [abs_of_neg (lt_of_not_ge h0)]
      ring
  rw [e, ← hftc]
  exact intervalIntegral.integral_mono_on hts hint hκint hbound

/-- **Total-variation distance along the atlas**: `d_TV(Q_s, Q_t) ≤ ½ ∫_t^s √κ_u du`. -/
theorem half_integral_abs_famDens_atlas_sub_le {t s : ℝ} (ht0 : 0 ≤ t) (hts : t ≤ s)
    (hs1 : s < 1) :
    (1 / 2) * ∫ x, |famDens S ν (atlasTheta hS ν M s) x - famDens S ν (atlasTheta hS ν M t) x| ∂ν ≤
      (1 / 2) * ∫ u in t..s, √(atlasCurv hS ν hfin u) :=
  mul_le_mul_of_nonneg_left (integral_abs_famDens_atlas_sub_le hS ν hfin ht0 hts hs1) (by norm_num)

end Atlas

end Laplace.Multi
