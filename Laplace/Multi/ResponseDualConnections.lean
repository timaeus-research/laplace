/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseFisherJets

/-!
# The dual connections of the response chart and mean-affine geodesics

In the natural coordinates the exponential connection has vanishing Christoffel symbols, the mixture
connection has Christoffel operator `C_θ = A_θ⁻¹ T_θ` (`mChristoffel`), and the `α`-family
interpolates: `Γ^α_θ = ((1−α)/2) C_θ` (`alphaChristoffel`; `α = 1` exponential, `α = −1` mixture,
`α = 0` Levi-Civita). The pair `(Γ^α, Γ^{−α})` is metric-dual for the Fisher form,

  `∂_u G(v,w) = G(Γ^α(u,v), w) + G(v, Γ^{−α}(u,w))`   (`hasDerivAt_fisherInner_line_dual`),

and `Γ^0` satisfies the Koszul formula (`koszul_alphaChristoffel_zero`), so it is the Levi-Civita
connection of the Fisher metric.

Along a `C²` path `θ` in the natural chart the mean path `μ = m ∘ θ` has second derivative

  `μ'' = A_θ θ'' + T_θ(θ', θ')`   (`hasDerivAt_deriv_chartV_path`),

so `θ` is an m-geodesic (`θ'' + C_θ(θ',θ') = 0`) exactly when its mean path has zero acceleration
(`mean_accel_eq_zero_iff_mGeodesic`): **m-geodesics are the mean-affine paths**, and the mixture
journeys of the data manifold (`ResponseMixtureConnection`) are their response images.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Dual

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative. -/
local notation "CD" => chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The intrinsic chart `θ ↦ m(θ) − m(0)`. -/
local notation "chV" => chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **The derivative of the Fisher form** in the direction `u`: `∂_u G_θ(v,w) = −⟨v, T_θ(u,w)⟩`. -/
noncomputable def fisherDeriv (θ u v w : 𝕍) : ℝ := -dotJ (v : J → ℝ) (thirdOp hS ν θ u w : J → ℝ)

theorem hasDerivAt_fisherInner_line_fisherDeriv (θ u v w : 𝕍) :
    HasDerivAt (fun t : ℝ ↦ fisherInner S ν (θ + t • u) v w) (fisherDeriv hS ν θ u v w) 0 := by
  have h := hasDerivAt_fisherInner_line hS ν θ u v w 0
  rw [zero_smul, add_zero] at h
  exact h

/-- The metric derivative is totally symmetric. -/
theorem fisherDeriv_swap₁₂ (θ u v w : 𝕍) :
    fisherDeriv hS ν θ u v w = fisherDeriv hS ν θ v u w := by
  unfold fisherDeriv
  rw [dotJ_thirdOp_symm₁₂ hS ν θ v u w]

theorem fisherDeriv_swap₂₃ (θ u v w : 𝕍) :
    fisherDeriv hS ν θ u v w = fisherDeriv hS ν θ u w v := by
  unfold fisherDeriv
  rw [dotJ_thirdOp_symm₁₂ hS ν θ v u w, dotJ_thirdOp_symm₂₃ hS ν θ u v w,
    dotJ_thirdOp_symm₁₂ hS ν θ u w v]

theorem fisherDeriv_swap₁₃ (θ u v w : 𝕍) :
    fisherDeriv hS ν θ u v w = fisherDeriv hS ν θ w v u := by
  rw [fisherDeriv_swap₁₂ hS ν, fisherDeriv_swap₂₃ hS ν, fisherDeriv_swap₁₂ hS ν]

/-- **The `α`-Christoffel operator** `Γ^α_θ(u,v) = ((1 − α)/2) C_θ(u,v)`. -/
noncomputable def alphaChristoffel (α : ℝ) (θ u v : 𝕍) : 𝕍 :=
  ((1 - α) / 2) • mChristoffel hS ν θ u v

/-- The exponential connection is flat in the natural chart. -/
theorem alphaChristoffel_one (θ u v : 𝕍) : alphaChristoffel hS ν 1 θ u v = 0 := by
  simp [alphaChristoffel]

/-- The mixture connection is `α = −1`. -/
theorem alphaChristoffel_neg_one (θ u v : 𝕍) :
    alphaChristoffel hS ν (-1) θ u v = mChristoffel hS ν θ u v := by
  unfold alphaChristoffel
  norm_num

/-- The Levi-Civita connection is `α = 0`: half the mixture Christoffel operator. -/
theorem alphaChristoffel_zero (θ u v : 𝕍) :
    alphaChristoffel hS ν 0 θ u v = (1 / 2 : ℝ) • mChristoffel hS ν θ u v := by
  unfold alphaChristoffel
  norm_num

/-- The `α`-connections are torsion-free in the natural chart. -/
theorem alphaChristoffel_symm (α : ℝ) (θ u v : 𝕍) :
    alphaChristoffel hS ν α θ u v = alphaChristoffel hS ν α θ v u := by
  unfold alphaChristoffel
  rw [mChristoffel_symm hS ν]

/-- Lowering the `α`-Christoffel operator: `G(Γ^α(u,v), w) = ((1−α)/2) ∂_u G(v,w)`. -/
theorem fisherInner_alphaChristoffel (α : ℝ) (θ u v w : 𝕍) :
    fisherInner S ν θ (alphaChristoffel hS ν α θ u v) w =
      (1 - α) / 2 * fisherDeriv hS ν θ u v w := by
  unfold alphaChristoffel fisherDeriv
  rw [fisherInner_smul_left, fisherInner_mChristoffel hS ν, dotJ_thirdOp_symm₁₂ hS ν θ w u v,
    dotJ_thirdOp_symm₂₃ hS ν θ u w v, dotJ_thirdOp_symm₁₂ hS ν θ u v w]

/-- **Metric duality of the `α` and `−α` connections**:
`G(Γ^α(u,v), w) + G(v, Γ^{−α}(u,w)) = ∂_u G(v,w)`. -/
theorem fisherInner_alphaChristoffel_dual (α : ℝ) (θ u v w : 𝕍) :
    fisherInner S ν θ (alphaChristoffel hS ν α θ u v) w +
      fisherInner S ν θ v (alphaChristoffel hS ν (-α) θ u w) = fisherDeriv hS ν θ u v w := by
  rw [fisherInner_comm hS ν θ v, fisherInner_alphaChristoffel hS ν,
    fisherInner_alphaChristoffel hS ν, ← fisherDeriv_swap₂₃ hS ν]
  ring

/-- The dual pair `(∇^α, ∇^{−α})` is metric: the derivative of the Fisher form along `u` is the sum
of the two lowered Christoffel operators. -/
theorem hasDerivAt_fisherInner_line_dual (α : ℝ) (θ u v w : 𝕍) :
    HasDerivAt (fun t : ℝ ↦ fisherInner S ν (θ + t • u) v w)
      (fisherInner S ν θ (alphaChristoffel hS ν α θ u v) w +
        fisherInner S ν θ v (alphaChristoffel hS ν (-α) θ u w)) 0 := by
  rw [fisherInner_alphaChristoffel_dual hS ν]
  exact hasDerivAt_fisherInner_line_fisherDeriv hS ν θ u v w

/-- **The Koszul formula** for `α = 0`: `2 G(Γ⁰(u,v), w) = ∂_u G(v,w) + ∂_v G(u,w) − ∂_w G(u,v)`,
so `Γ⁰` is the Levi-Civita connection of the Fisher metric in the natural chart. -/
theorem koszul_alphaChristoffel_zero (θ u v w : 𝕍) :
    2 * fisherInner S ν θ (alphaChristoffel hS ν 0 θ u v) w =
      fisherDeriv hS ν θ u v w + fisherDeriv hS ν θ v u w - fisherDeriv hS ν θ w u v := by
  rw [fisherInner_alphaChristoffel hS ν, fisherDeriv_swap₁₂ hS ν θ v u w,
    fisherDeriv_swap₁₂ hS ν θ w u v, ← fisherDeriv_swap₂₃ hS ν θ u v w]
  ring

theorem chartDeriv_chartDerivEquiv_symm (θ x : 𝕍) : CD θ ((CDE θ).symm x) = x := by
  rw [← ContinuousLinearMap.coe_coe (CD θ), ← coe_chartDerivEquiv, ContinuousLinearMap.coe_coe,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

theorem chartDerivEquiv_symm_chartDeriv (θ x : 𝕍) : (CDE θ).symm (CD θ x) = x := by
  rw [← ContinuousLinearMap.coe_coe (CD θ), ← coe_chartDerivEquiv, ContinuousLinearMap.coe_coe,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

/-- Raising the mixture Christoffel operator: `A_θ C_θ(u,v) = T_θ(u,v)`. -/
theorem chartDeriv_mChristoffel (θ u v : 𝕍) :
    CD θ (mChristoffel hS ν θ u v) = thirdOp hS ν θ u v :=
  chartDeriv_chartDerivEquiv_symm hS ν θ _

end Dual

section Path

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative. -/
local notation "CD" => chartDeriv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The intrinsic chart `θ ↦ m(θ) − m(0)`. -/
local notation "chV" => chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- **The mean path of a `C¹` path in the natural chart** has velocity `A_θ θ'`. -/
theorem hasDerivAt_chartV_path {θ θ' : ℝ → 𝕍} {t₀ : ℝ} (hθ : HasDerivAt θ (θ' t₀) t₀) :
    HasDerivAt (fun t ↦ chV (θ t)) (CD (θ t₀) (θ' t₀)) t₀ :=
  (hasStrictFDerivAt_chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) hS (θ t₀)).hasFDerivAt.comp_hasDerivAt t₀ hθ

/-- The restricted covariance operator along a `C²` path, applied to the velocity. -/
theorem hasDerivAt_chartDeriv_path {θ θ' : ℝ → 𝕍} {θ'' : 𝕍} {t₀ : ℝ}
    (hθ : HasDerivAt θ (θ' t₀) t₀) (hθ' : HasDerivAt θ' θ'' t₀) :
    HasDerivAt (fun t ↦ CD (θ t) (θ' t))
      (thirdOp hS ν (θ t₀) (θ' t₀) (θ' t₀) + CD (θ t₀) θ'') t₀ := by
  have hc : HasDerivAt (fun t ↦ CD (θ t)) (thirdOp hS ν (θ t₀) (θ' t₀)) t₀ :=
    (hasFDerivAt_chartDeriv hS ν (θ t₀)).comp_hasDerivAt t₀ hθ
  exact hc.clm_apply hθ'

/-- **The mean path law**: along a `C²` path `θ` of the natural chart,
`(m ∘ θ)'' = A_θ θ'' + T_θ(θ', θ')`. -/
theorem hasDerivAt_deriv_chartV_path {θ θ' : ℝ → 𝕍} {θ'' : 𝕍} {t₀ : ℝ}
    (hθ : ∀ t, HasDerivAt θ (θ' t) t) (hθ' : HasDerivAt θ' θ'' t₀) :
    HasDerivAt (deriv fun t ↦ chV (θ t))
      (CD (θ t₀) θ'' + thirdOp hS ν (θ t₀) (θ' t₀) (θ' t₀)) t₀ := by
  have e : (deriv fun t ↦ chV (θ t)) = fun t ↦ CD (θ t) (θ' t) :=
    funext fun t ↦ (hasDerivAt_chartV_path hS ν (hθ t)).deriv
  rw [e, add_comm]
  exact hasDerivAt_chartDeriv_path hS ν (hθ t₀) hθ'

/-- **m-geodesics are the mean-affine paths**: the mean acceleration `A_θ θ'' + T_θ(θ',θ')`
vanishes iff `θ'' + C_θ(θ',θ') = 0`. -/
theorem mean_accel_eq_zero_iff_mGeodesic (θ₀ v a : 𝕍) :
    CD θ₀ a + thirdOp hS ν θ₀ v v = 0 ↔ a + mChristoffel hS ν θ₀ v v = 0 := by
  constructor
  · intro h
    have h1 : CD θ₀ (a + mChristoffel hS ν θ₀ v v) = 0 := by
      rw [map_add, chartDeriv_mChristoffel hS ν]
      exact h
    have h2 := congrArg (CDE θ₀).symm h1
    rw [chartDerivEquiv_symm_chartDeriv hS ν, map_zero] at h2
    exact h2
  · intro h
    have h1 := congrArg (CD θ₀) h
    rw [map_add, chartDeriv_mChristoffel hS ν, map_zero] at h1
    exact h1

/-- An m-geodesic of the natural chart has an affine mean path: `(m ∘ θ)'' = 0`. -/
theorem hasDerivAt_deriv_chartV_path_of_mGeodesic {θ θ' : ℝ → 𝕍} {θ'' : 𝕍} {t₀ : ℝ}
    (hθ : ∀ t, HasDerivAt θ (θ' t) t) (hθ' : HasDerivAt θ' θ'' t₀)
    (hgeo : θ'' + mChristoffel hS ν (θ t₀) (θ' t₀) (θ' t₀) = 0) :
    HasDerivAt (deriv fun t ↦ chV (θ t)) 0 t₀ := by
  have h := hasDerivAt_deriv_chartV_path hS ν hθ hθ'
  rwa [(mean_accel_eq_zero_iff_mGeodesic hS ν _ _ _).2 hgeo] at h

/-- The Levi-Civita geodesic equation `θ'' + Γ⁰(θ',θ') = 0` in terms of the mean acceleration:
the mean path accelerates by half the model third cumulant, `(m ∘ θ)'' = ½ T_θ(θ',θ')`. -/
theorem hasDerivAt_deriv_chartV_path_of_lcGeodesic {θ θ' : ℝ → 𝕍} {θ'' : 𝕍} {t₀ : ℝ}
    (hθ : ∀ t, HasDerivAt θ (θ' t) t) (hθ' : HasDerivAt θ' θ'' t₀)
    (hgeo : θ'' + alphaChristoffel hS ν 0 (θ t₀) (θ' t₀) (θ' t₀) = 0) :
    HasDerivAt (deriv fun t ↦ chV (θ t))
      ((1 / 2 : ℝ) • thirdOp hS ν (θ t₀) (θ' t₀) (θ' t₀)) t₀ := by
  have h := hasDerivAt_deriv_chartV_path hS ν hθ hθ'
  have ha : θ'' = -((1 / 2 : ℝ) • mChristoffel hS ν (θ t₀) (θ' t₀) (θ' t₀)) := by
    rw [← alphaChristoffel_zero hS ν]
    exact eq_neg_of_add_eq_zero_left hgeo
  rw [ha, map_neg, map_smul, chartDeriv_mChristoffel hS ν] at h
  refine h.congr_deriv ?_
  module

end Path

end Laplace.Multi
