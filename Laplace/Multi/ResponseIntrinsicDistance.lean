/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseEndpointInformationAction
import Laplace.Multi.ResponseFaceFisherSeparation
import Laplace.Multi.FisherCauchyRealisation
import Laplace.Multi.MeanSegment

/-!
# The intrinsic response distance and its information bounds

The intrinsic Fisher distance `d_F` on the direction space `W` (the infimum of Fisher lengths of
`C¹` paths, `FisherDistance`) is sandwiched between the spherical (Hellinger-angle) distance of the
model laws and the square root of their Jeffreys divergence:

`2 arccos Aff(P_{θ₀}, P_{θ₁}) ≤ d_F(θ₀, θ₁) ≤ L_F(segment θ₀ θ₁) ≤ √J(P_{θ₀}, P_{θ₁})`.

* `sphericalDist_le_fisherDist`: every `C¹` path is at least as long as the Hellinger angle
  (`sphericalDist_le_integral` for each competitor, then the infimum).
* `jeffreys_model_eq_natSegment_action`: along the **natural segment** `θ_t = θ₀ + t(θ₁ − θ₀)`
  (the e-geodesic) the Jeffreys divergence is again the Fisher action `∫₀¹ G_{θ_t}(Δθ,Δθ) dt`
  (the mean-affine journey of `ResponseEndpointInformationAction` gives the same number: both
  are `−⟨θ₁ − θ₀, m(θ₁) − m(θ₀)⟩`).
* `sq_length_segment_le_jeffreys`, `sq_fisherDist_le_jeffreys`: Cauchy–Schwarz.
* `responseDist`: the pull-back `d_resp(ρ_g, ρ_k) = d_F(Φ(g), Φ(k))` is a pseudometric on data
  laws, a metric on response classes, with the same two-sided information bounds.

Note: `√J` is not a metric, and `d_F` need not be attained; the segment is a competitor, not
claimed shortest.
-/

open MeasureTheory Filter Topology Set InformationTheory

namespace Laplace.Multi

section Distance

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The Fisher form. -/
local notation "G" => fisherInner S ν

omit [Nonempty J] in
/-- **The spherical distance is a lower bound for every Fisher length**, hence for the intrinsic
distance. -/
theorem sphericalDist_le_fisherDist (θ₀ θ₁ : 𝕍) :
    sphericalDist S ν (θ₀ : J → ℝ) (θ₁ : J → ℝ) ≤ fisherDist S ν θ₀ θ₁ := by
  refine le_csInf fisherLengths_nonempty fun L ⟨p, hp⟩ ↦ ?_
  rw [← hp]
  have hγ : ∀ t, HasDerivAt (fun t ↦ (p.toFun t : J → ℝ)) (p.vel t : J → ℝ) t := fun t ↦
    (𝕍).subtypeL.hasFDerivAt.comp_hasDerivAt t (p.hasDerivAt t)
  have hγ' : Continuous fun t ↦ (p.vel t : J → ℝ) := continuous_subtype_val.comp p.continuous_vel
  have h := sphericalDist_le_integral hS ν hγ hγ'
  simp only [p.source, p.target] at h
  rw [sphericalDist_comm ν] at h
  exact h

omit [Nonempty J] in
/-- The pairing of the coordinate displacement with the mean along the natural segment has
derivative minus the Fisher speed. -/
theorem hasDerivAt_dotJ_meanMap_natSegment (θ₀ θ₁ : 𝕍) (t : ℝ) :
    HasDerivAt (fun s ↦ dotJ ((θ₁ : J → ℝ) - (θ₀ : J → ℝ))
        (mean ((θ₀ : J → ℝ) + s • ((θ₁ : J → ℝ) - (θ₀ : J → ℝ)))))
      (-G (θ₀ + t • (θ₁ - θ₀)) (θ₁ - θ₀) (θ₁ - θ₀)) t := by
  set Δ : J → ℝ := (θ₁ : J → ℝ) - (θ₀ : J → ℝ) with hΔ
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hline : HasDerivAt (fun s : ℝ ↦ (θ₀ : J → ℝ) + s • Δ) Δ t := by
    simpa using ((hasDerivAt_id t).smul_const Δ).const_add (θ₀ : J → ℝ)
  have hm := (hasStrictFDerivAt_meanMap measurable_const (integrable_const 1)
    (fun _ ↦ zero_le_one) (one_integral_pos ν) measurable_const h0 hS one_pos
    ((θ₀ : J → ℝ) + t • Δ)).hasFDerivAt.comp_hasDerivAt t hline
  have h := hasDerivAt_dotJ (hasDerivAt_const t Δ) hm
  refine h.congr_deriv ?_
  rw [dotJ_zero_left, zero_add, dotJ_meanMapDeriv (μ := ν) measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos ν) hS, priorCov_eq_lawCov_familyMeasure hS ν]
  rfl

/-- The Fisher speed along the natural segment is continuous. -/
theorem continuous_natSegment_speed (θ₀ θ₁ : 𝕍) :
    Continuous fun t : ℝ ↦ G (θ₀ + t • (θ₁ - θ₀)) (θ₁ - θ₀) (θ₁ - θ₀) := by
  have hmap : Continuous fun t : ℝ ↦ (θ₀ + t • (θ₁ - θ₀), (θ₁ - θ₀, θ₁ - θ₀)) :=
    (continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_const
  have h := (continuous_fisherInner hS ν).comp hmap
  simpa only [Function.comp_def] using h

/-- **The Jeffreys divergence is the Fisher action of the natural segment** (the e-geodesic):
`KL(P_{θ₁}‖P_{θ₀}) + KL(P_{θ₀}‖P_{θ₁}) = ∫₀¹ G_{θ₀ + t(θ₁−θ₀)}(θ₁ − θ₀, θ₁ − θ₀) dt`. -/
theorem jeffreys_model_eq_natSegment_action (θ₀ θ₁ : 𝕍) :
    (klDiv (Pfam (θ₁ : J → ℝ)) (Pfam (θ₀ : J → ℝ))).toReal +
      (klDiv (Pfam (θ₀ : J → ℝ)) (Pfam (θ₁ : J → ℝ))).toReal =
      ∫ t in (0 : ℝ)..1, G (θ₀ + t • (θ₁ - θ₀)) (θ₁ - θ₀) (θ₁ - θ₀) := by
  rw [jeffreys_model_eq_neg_dotJ hS ν]
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s ↦ -dotJ ((θ₁ : J → ℝ) - (θ₀ : J → ℝ))
        (mean ((θ₀ : J → ℝ) + s • ((θ₁ : J → ℝ) - (θ₀ : J → ℝ)))))
        (G (θ₀ + t • (θ₁ - θ₀)) (θ₁ - θ₀) (θ₁ - θ₀)) t := fun t _ ↦ by
    have h := (hasDerivAt_dotJ_meanMap_natSegment hS ν θ₀ θ₁ t).neg
    rwa [neg_neg] at h
  have hint : IntervalIntegrable (fun t ↦ G (θ₀ + t • (θ₁ - θ₀)) (θ₁ - θ₀) (θ₁ - θ₀)) volume 0 1 :=
    (continuous_natSegment_speed hS ν θ₀ θ₁).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [one_smul, zero_smul, add_zero, add_sub_cancel]
  rw [(isLinearMap_dotJ _).map_sub]
  ring

omit [Nonempty J] in
/-- The Fisher length of the natural segment. -/
theorem length_segment_eq (θ₀ θ₁ : 𝕍) :
    (FisherPath.segment θ₀ θ₁).length =
      ∫ t in (0 : ℝ)..1, Real.sqrt (G (θ₀ + t • (θ₁ - θ₀)) (θ₁ - θ₀) (θ₁ - θ₀)) := by
  rw [FisherPath.segment, FisherPath.length_flat hS ν]
  rfl

/-- **The Fisher length of the natural segment is at most the square root of the Jeffreys
divergence** (Cauchy–Schwarz). -/
theorem sq_length_segment_le_jeffreys (θ₀ θ₁ : 𝕍) :
    (FisherPath.segment θ₀ θ₁).length ^ 2 ≤
      (klDiv (Pfam (θ₁ : J → ℝ)) (Pfam (θ₀ : J → ℝ))).toReal +
        (klDiv (Pfam (θ₀ : J → ℝ)) (Pfam (θ₁ : J → ℝ))).toReal := by
  rw [length_segment_eq hS ν, jeffreys_model_eq_natSegment_action hS ν]
  have hnn : ∀ t : ℝ, 0 ≤ G (θ₀ + t • (θ₁ - θ₀)) (θ₁ - θ₀) (θ₁ - θ₀) := fun t ↦
    fisherVar_nonneg hS ν _ _
  have h := sq_integral_sqrt_mul_le (continuous_natSegment_speed hS ν θ₀ θ₁).continuousOn
    continuousOn_const (fun t _ ↦ hnn t) (fun _ _ ↦ zero_le_one)
  simpa [intervalIntegral.integral_const] using h

/-- **The intrinsic distance squared is at most the Jeffreys divergence.** -/
theorem sq_fisherDist_le_jeffreys (θ₀ θ₁ : 𝕍) :
    fisherDist S ν θ₀ θ₁ ^ 2 ≤
      (klDiv (Pfam (θ₁ : J → ℝ)) (Pfam (θ₀ : J → ℝ))).toReal +
        (klDiv (Pfam (θ₀ : J → ℝ)) (Pfam (θ₁ : J → ℝ))).toReal :=
  (pow_le_pow_left₀ (fisherDist_nonneg) (fisherDist_le_length (FisherPath.segment θ₀ θ₁)) 2).trans
    (sq_length_segment_le_jeffreys hS ν θ₀ θ₁)

/-- **The two-sided information bound on the intrinsic distance**:
`2 arccos Aff(P_{θ₀},P_{θ₁}) ≤ d_F(θ₀,θ₁) ≤ √J(P_{θ₀},P_{θ₁})`. -/
theorem sphericalDist_le_fisherDist_le_sqrt_jeffreys (θ₀ θ₁ : 𝕍) :
    sphericalDist S ν (θ₀ : J → ℝ) (θ₁ : J → ℝ) ≤ fisherDist S ν θ₀ θ₁ ∧
      fisherDist S ν θ₀ θ₁ ≤ Real.sqrt ((klDiv (Pfam (θ₁ : J → ℝ)) (Pfam (θ₀ : J → ℝ))).toReal +
        (klDiv (Pfam (θ₀ : J → ℝ)) (Pfam (θ₁ : J → ℝ))).toReal) :=
  ⟨sphericalDist_le_fisherDist hS ν θ₀ θ₁,
    Real.le_sqrt_of_sq_le (sq_fisherDist_le_jeffreys hS ν θ₀ θ₁)⟩

/-- **The response distance** `d_resp(ρ_g, ρ_k) = d_F(Φ(g), Φ(k))` on data laws. -/
noncomputable def responseDist (g k : X → ℝ) : ℝ :=
  fisherDist S ν (responseOf hS ν g) (responseOf hS ν k)

theorem responseDist_self (g : X → ℝ) : responseDist hS ν g g = 0 := fisherDist_self hS ν _

theorem responseDist_comm (g k : X → ℝ) : responseDist hS ν g k = responseDist hS ν k g :=
  fisherDist_comm hS ν

theorem responseDist_nonneg (g k : X → ℝ) : 0 ≤ responseDist hS ν g k := fisherDist_nonneg

theorem responseDist_triangle (g k l : X → ℝ) :
    responseDist hS ν g l ≤ responseDist hS ν g k + responseDist hS ν k l :=
  fisherDist_triangle hS ν _ _ _

/-- The response distance vanishes exactly on response classes. -/
theorem responseDist_eq_zero_iff (g k : X → ℝ) :
    responseDist hS ν g k = 0 ↔ responseOf hS ν g = responseOf hS ν k :=
  fisherDist_eq_zero_iff hS ν

/-- The response distance is bounded below by the Hellinger angle of the two responses' model
laws and above by the square root of their Jeffreys divergence. -/
theorem sphericalDist_le_responseDist_le_sqrt_jeffreys (g k : X → ℝ) :
    sphericalDist S ν (responseOf hS ν g : J → ℝ) (responseOf hS ν k : J → ℝ) ≤
        responseDist hS ν g k ∧
      responseDist hS ν g k ≤
        Real.sqrt ((klDiv (Pfam (responseOf hS ν k : J → ℝ))
          (Pfam (responseOf hS ν g : J → ℝ))).toReal +
          (klDiv (Pfam (responseOf hS ν g : J → ℝ))
            (Pfam (responseOf hS ν k : J → ℝ))).toReal) :=
  sphericalDist_le_fisherDist_le_sqrt_jeffreys hS ν _ _

end Distance

end Laplace.Multi
