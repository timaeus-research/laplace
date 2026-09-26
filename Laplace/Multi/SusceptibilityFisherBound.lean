/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PolytopeResponseTransport
import Laplace.Multi.BiasForm
import Laplace.Multi.QuantitativeJets

/-!
# The susceptibility is bounded by the Fisher speed

The susceptibility `lin_{F,M}(u) = D[M ↦ E_{q_M} F](u)` of a bounded observable is the covariance
of `F` with the response score `ℓ_{M,u}`, whose second moment is the Fisher quadratic form
`⟨u, C_M⁻¹ u⟩`.  Cauchy–Schwarz gives the coordinate-free bound

  `|lin_{F,M}(u)| ≤ √Var_{q_M}(F) · √⟨u, C_M⁻¹ u⟩`

(`abs_linForm_le_sqrt_var_mul_sqrt`).  Along the straight path from the featureless response the
right-hand side is `√Var · √κ(s)` with `κ` the curvature of the rate, i.e. the Fisher speed of the
path (`abs_linForm_atlasPath_le`).  Integrating, the change of any bounded posterior expectation is
bounded by its sup-norm times the Fisher length of the path
(`abs_integral_responseProjection_atlasPath_sub_le`), and on a charged polytope this passes to the
endpoint: for every completed response `M`, if the straight path has Fisher length at most `L`, then

  `|E_{q_M} F − E_ν F| ≤ ‖F‖_∞ · L`

(`abs_integral_responseProjection_sub_featureless_le`).
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Bound

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The reconstructed family `P_θ = exp(−⟨θ,S⟩) ν / Z(θ)`. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The response chart `θ(M)`. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The direction subspace. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The featureless response `m₀ = E_ν S`. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The inverse chart derivative `R_M = (Dm(θ(M))|_𝕍)⁻¹`. -/
local notation "Rinv" M => ContinuousLinearEquiv.symm (chartDerivEquiv measurable_const
  (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS (θr M))

omit hS in
/-- The variance of a bounded observable is at most the square of its bound. -/
theorem sqrt_lawCov_self_le (ρ : Measure X) [IsProbabilityMeasure ρ] {F : X → ℝ} (hF : Bdd F)
    {K : ℝ} (hK : ∀ x, |F x| ≤ K) : √(lawCov ρ F F) ≤ K := by
  have hK0 : 0 ≤ K := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact (abs_nonneg _).trans (hK x)
  rw [Real.sqrt_le_iff]
  refine ⟨hK0, (lawCov_self_le_integral_sq ρ hF 0).trans ?_⟩
  have hint : Integrable (fun x ↦ (F x - 0) * (F x - 0)) ρ := by
    simp only [sub_zero]
    exact integrable_of_bdd_prob ρ (hF.mul hF)
  calc ∫ x, (F x - 0) * (F x - 0) ∂ρ ≤ ∫ _, K ^ 2 ∂ρ := by
        refine integral_mono hint (integrable_const _) fun x ↦ ?_
        simp only [sub_zero]
        rw [← abs_mul_abs_self, ← sq]
        exact pow_le_pow_left₀ (abs_nonneg _) (hK x) 2
    _ = K ^ 2 := by simp

variable {M : J → ℝ} (hrel : M ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S))
include hrel

/-- The susceptibility is the covariance of the observable with the response score. -/
theorem linForm_eq_lawCov_responseScore {F : X → ℝ} (hF : Bdd F) (u : 𝕍) :
    linForm hS ν M hF (u : J → ℝ) = lawCov (Pfam (θr M)) F (responseScore hS ν M u) := by
  rw [← integral_mul_responseScore_eq_linForm hS ν hF u, lawCov, integral_responseScore hS ν hrel u,
    mul_zero, sub_zero]

/-- **The susceptibility is bounded by the Fisher speed**:
`|lin_{F,M}(u)| ≤ √Var_{q_M}(F) · √⟨u, C_M⁻¹ u⟩`. -/
theorem abs_linForm_le_sqrt_var_mul_sqrt {F : X → ℝ} (hF : Bdd F) (u : 𝕍) :
    |linForm hS ν M hF (u : J → ℝ)| ≤
      √(lawCov (Pfam (θr M)) F F) * √(-dotJ ((Rinv M) u : J → ℝ) (u : J → ℝ)) := by
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := M)
  rw [linForm_eq_lawCov_responseScore hS ν hrel hF u, ← Real.sqrt_mul (lawCov_self_nonneg _ hF),
    ← integral_responseScore_mul hS ν hrel u u]
  refine Real.abs_le_sqrt ?_
  have h := lawCov_sq_le (Pfam (θr M)) hF (bdd_responseScore hS ν M u)
  have hℓ : lawCov (Pfam (θr M)) (responseScore hS ν M u) (responseScore hS ν M u) =
      ∫ x, responseScore hS ν M u x * responseScore hS ν M u x ∂(Pfam (θr M)) := by
    rw [lawCov, integral_responseScore hS ν hrel u, mul_zero, sub_zero]
  rwa [hℓ] at h

end Bound

section Path

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
include hS hfin

/-- The reconstructed family `P_θ = exp(−⟨θ,S⟩) ν / Z(θ)`. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The response chart `θ(M)`. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The featureless response `m₀ = E_ν S`. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- **Along the straight path the susceptibility is bounded by `√Var · √κ`**, the Fisher speed. -/
theorem abs_linForm_atlasPath_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {F : X → ℝ} (hF : Bdd F) :
    |linForm hS ν (atlasPath S ν M s) hF (M - m₀)| ≤
      √(lawCov (Pfam (θr (atlasPath S ν M s))) F F) * √(atlasCurv hS ν hfin s) := by
  have hrel := atlas_mem_intrinsicInterior hS ν hfin hs0 hs1
  have := abs_linForm_le_sqrt_var_mul_sqrt hS ν hrel hF
    ⟨M - m₀, sub_mem_dirSpan_of_genRate_ne_top hS ν hfin⟩
  unfold atlasCurv atlasVel atlasTheta
  exact this

/-- The Fisher speed of the straight path is continuous before the endpoint. -/
theorem continuousOn_sqrt_atlasCurv {r : ℝ} (hr1 : r < 1) :
    ContinuousOn (fun s ↦ √(atlasCurv hS ν hfin s)) (Icc 0 r) :=
  Real.continuous_sqrt.comp_continuousOn fun _ hs ↦
    (continuousAt_atlasCurv hS ν hfin hs.1 (lt_of_le_of_lt hs.2 hr1)).continuousWithinAt

/-- **The change of a bounded posterior expectation along the straight path is bounded by the
sup-norm times the Fisher length.** -/
theorem abs_integral_responseProjection_atlasPath_sub_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {F : X → ℝ} (hF : Bdd F) {K : ℝ} (hK : ∀ x, |F x| ≤ K) :
    |(∫ x, F x ∂responseProjection hS ν (atlasPath S ν M r)) - ∫ x, F x ∂ν| ≤
      K * ∫ s in (0 : ℝ)..r, √(atlasCurv hS ν hfin s) := by
  rw [integral_responseProjection_atlasPath_sub_eq hS ν hfin hr0 hr1 hF]
  refine (intervalIntegral.abs_integral_le_integral_abs hr0).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  have hint : ∀ s ∈ Icc (0 : ℝ) r,
      atlasPath S ν M s ∈ intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S) := fun s hs ↦
    atlas_mem_intrinsicInterior hS ν hfin hs.1 (lt_of_le_of_lt hs.2 hr1)
  have hMc : ContinuousOn (atlasPath S ν M) (Icc 0 r) := fun s _ ↦
    (hasDerivAt_atlasPath ν s).continuousAt.continuousWithinAt
  have hcont := continuousOn_linForm_path hS ν (M' := fun _ ↦ M - m₀)
    (atlasPath_sub_mem_dirSpan hS ν hfin) hint hMc continuousOn_const
    (fun _ _ ↦ sub_mem_dirSpan_of_genRate_ne_top hS ν hfin) hF
  have h1 : IntervalIntegrable (fun s ↦ |linForm hS ν (atlasPath S ν M s) hF (M - m₀)|)
      volume 0 r := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hr0]
    exact hcont.abs
  have h2 : IntervalIntegrable (fun s ↦ K * √(atlasCurv hS ν hfin s)) volume 0 r := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hr0]
    exact continuousOn_const.mul (continuousOn_sqrt_atlasCurv hS ν hfin hr1)
  refine intervalIntegral.integral_mono_on hr0 h1 h2 fun s hs ↦ ?_
  have hrel := atlas_mem_intrinsicInterior hS ν hfin hs.1 (lt_of_le_of_lt hs.2 hr1)
  have hP := isProbabilityMeasure_family_responseTheta hS ν (M := atlasPath S ν M s)
  calc |linForm hS ν (atlasPath S ν M s) hF (M - m₀)|
      ≤ √(lawCov (Pfam (θr (atlasPath S ν M s))) F F) * √(atlasCurv hS ν hfin s) :=
        abs_linForm_atlasPath_le hS ν hfin hs.1 (lt_of_le_of_lt hs.2 hr1) hF
    _ ≤ K * √(atlasCurv hS ν hfin s) :=
        mul_le_mul_of_nonneg_right (sqrt_lawCov_self_le _ hF hK) (Real.sqrt_nonneg _)

end Path

section Endpoint

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (V : Finset (J → ℝ)) [Nonempty V]
  (hpoly : momentBody ν (fun _ ↦ (1 : ℝ)) S = convexHull ℝ (V : Set (J → ℝ)))
  (hcharged : ∀ v ∈ V, 0 < ν.real (statFibre S v))
include hS hpoly hcharged

/-- **Posterior expectations move at most as far as the Fisher length of the path from the
featureless law**: on a charged polytope, for every completed response `M` whose straight path has
Fisher length at most `L`, `|E_{q_M} F − E_ν F| ≤ ‖F‖_∞ · L`. -/
theorem abs_integral_responseProjection_sub_featureless_le {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (V : Set (J → ℝ))) {F : X → ℝ} (hF : Bdd F) {K : ℝ}
    (hK : ∀ x, |F x| ≤ K) {L : ℝ}
    (hL : ∀ r, 0 ≤ r → r < 1 → ∫ s in (0 : ℝ)..r,
      √(atlasCurv hS ν (genRate_ne_top_of_mem_convexHull_vertices hS ν V hcharged hM) s) ≤ L) :
    |(∫ x, F x ∂responseProjection hS ν M) - ∫ x, F x ∂ν| ≤ K * L := by
  have hfin := genRate_ne_top_of_mem_convexHull_vertices hS ν V hcharged hM
  have hK0 : 0 ≤ K := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact (abs_nonneg _).trans (hK x)
  have hlim := (continuous_abs.tendsto _).comp
    (tendsto_integral_linForm_atlasPath hS ν V hpoly hcharged hM hF)
  have : (𝓝[<] (1 : ℝ)).NeBot := nhdsWithin_Iio_neBot le_rfl
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
  have h := abs_integral_responseProjection_atlasPath_sub_le hS ν hfin hr.1.le hr.2 hF hK
  rw [integral_responseProjection_atlasPath_sub_eq hS ν hfin hr.1.le hr.2 hF] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hL r hr.1.le hr.2) hK0)

end Endpoint

end Laplace.Multi
