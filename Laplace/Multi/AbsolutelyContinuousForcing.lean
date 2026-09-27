/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.TangentPythagoras
import Laplace.Multi.ResponseLawContinuity
import Laplace.Multi.ResponsePullbackForm

/-!
# Covariance vectors of dominated laws lie in the direction space

For any probability law `D ≪ ν` and any bounded contrast `k`, the covariance vector
`Cov_D(S, k) = (Cov_D(S_i, k))_i` lies in the direction space `W` (`covVec_mem_dirSpan`): it is the
`D`-integral of `k(x) · (S(x) − E_D S)`, whose integrand lies `D`-a.e. in the closed convex set `W`.

Consequently the retraction `p` in the density formulation of the response geometry is inert:
`p (b_q(k)) = b_q(k)` for every retraction (`retraction_densForcing`), the density response velocity
is retraction-free (`densVel_eq_symm`, `densVel_eq`), and at a normalised tilt density
`q = e^g / Z` the density objects are the tilt objects (`densForcing_tiltDens`,
`densResponse_tiltDens`, `densVel_tiltDens`). The intrinsic, retraction-free density formulation of
`ResponseLawContinuity` is thereby justified.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Vector

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (D : Measure X) [IsProbabilityMeasure D] (hDν : D ≪ ν)
include hS hDν

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] hDν in
/-- The covariance with a statistic is the integral of `k · (S_i − E_D S_i)`. -/
theorem lawCov_stat_eq_integral {k : X → ℝ} (hk : Bdd k) (i : J) :
    lawCov D (S i) k = ∫ x, k x * (S i x - ∫ y, S i y ∂D) ∂D := by
  have h1 : Integrable (fun x ↦ k x * S i x) D := integrable_of_bdd_prob D (hk.mul (hS i))
  have h2 : Integrable (fun x ↦ k x * ∫ y, S i y ∂D) D :=
    (integrable_of_bdd_prob D hk).mul_const _
  have e : (fun x ↦ k x * (S i x - ∫ y, S i y ∂D)) =
      fun x ↦ k x * S i x - k x * ∫ y, S i y ∂D := funext fun x ↦ by ring
  rw [e, integral_sub h1 h2, integral_mul_const, lawCov]
  have e2 : (fun x ↦ S i x * k x) = fun x ↦ k x * S i x := funext fun x ↦ mul_comm _ _
  rw [e2]
  ring

set_option linter.unusedFintypeInType false in
/-- **The covariance vector of a dominated law lies in the direction space**:
`Cov_D(S, k) ∈ W` for every `D ≪ ν` and bounded `k`. -/
theorem covVec_mem_dirSpan {k : X → ℝ} (hk : Bdd k) : (fun i ↦ lawCov D (S i) k) ∈ 𝕍 := by
  have hM : (fun i ↦ ∫ y, S i y ∂D) ∈ momentBody ν (fun _ ↦ (1 : ℝ)) S :=
    mean_mem_momentBody_of_ac hS ν D hDν
  have hae := ae_statPoint_sub_mem_dirSpan hS ν D hDν hM
  have hint : Integrable (fun x ↦ k x • (statPoint S x - fun i ↦ ∫ y, S i y ∂D)) D := by
    rw [integrable_pi_iff]
    intro i
    refine (integrable_of_bdd_prob D (hk.mul ((hS i).sub ⟨measurable_const, |∫ y, S i y ∂D|,
      fun _ ↦ le_rfl⟩))).congr (Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rfl
  have hmem : (∫ x, k x • (statPoint S x - fun i ↦ ∫ y, S i y ∂D) ∂D) ∈ 𝕍 :=
    (𝕍).convex.integral_mem (Submodule.closed_of_finiteDimensional _)
      (by filter_upwards [hae] with x hx using Submodule.smul_mem _ _ hx) hint
  convert hmem using 1
  funext i
  rw [lawCov_stat_eq_integral hS D hk i]
  have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J ↦ ℝ) i).integral_comp_comm hint
  simp only [ContinuousLinearMap.proj_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    statPoint] at this
  exact this

end Vector

section Retraction

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

variable {q : X → ℝ} (hq0 : ∀ x, 0 ≤ q x) (hqi : Integrable q ν) (hq1 : ∫ x, q x ∂ν = 1)
include hq0 hqi hq1

set_option linter.unusedFintypeInType false in
/-- **The density forcing lies in the direction space.** -/
theorem densForcing_mem_dirSpan {k : X → ℝ} (hk : Bdd k) : densForcing S ν q k ∈ 𝕍 := by
  have := isProbabilityMeasure_withDensity_ofReal ν hq0 hqi hq1
  exact covVec_mem_dirSpan hS ν _ (withDensity_absolutelyContinuous _ _) hk

set_option linter.unusedFintypeInType false in
/-- **Every retraction is inert on the density forcing.** -/
theorem retraction_densForcing (p : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w)
    {k : X → ℝ} (hk : Bdd k) :
    p (densForcing S ν q k) = ⟨densForcing S ν q k, densForcing_mem_dirSpan hS ν hq0 hqi hq1 hk⟩ :=
  hp ⟨densForcing S ν q k, densForcing_mem_dirSpan hS ν hq0 hqi hq1 hk⟩

/-- **The density response velocity is retraction-free**:
`DΦ_q[k] = (Dm(Φ(q))|_W)⁻¹ b_q(k)` with the forcing taken as an element of `W`. -/
theorem densVel_eq_symm (p : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {k : X → ℝ}
    (hk : Bdd k) :
    densVel hS ν q p k = ((CDE (densResponse hS ν q)).symm : 𝕍 →L[ℝ] 𝕍)
      ⟨densForcing S ν q k, densForcing_mem_dirSpan hS ν hq0 hqi hq1 hk⟩ := by
  rw [densVel, retraction_densForcing hS ν hq0 hqi hq1 p hp hk]

/-- **Two retractions give the same density response velocity.** -/
theorem densVel_eq (p p' : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w)
    (hp' : ∀ w : 𝕍, p' (w : J → ℝ) = w) {k : X → ℝ} (hk : Bdd k) :
    densVel hS ν q p k = densVel hS ν q p' k := by
  rw [densVel_eq_symm hS ν hq0 hqi hq1 p hp hk, densVel_eq_symm hS ν hq0 hqi hq1 p' hp' hk]

end Retraction

section Tilt

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {g : X → ℝ} (hg : Bdd g)
include hS hg

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The normalised tilt density `e^g / Z`. -/
local notation "tq" => fun x ↦ Real.exp (g x) / ∫ y, Real.exp (g y) ∂ν

omit [Nonempty X] [Nonempty J] [Fintype J] hS [IsProbabilityMeasure ν] hg in
/-- The tilted law is the law with the normalised tilt density. -/
theorem tilted_eq_withDensity_tq :
    ν.tilted g = ν.withDensity fun x ↦ ENNReal.ofReal (tq x) := rfl

omit [Nonempty X] [Nonempty J] [Fintype J] hS in
theorem integral_tq : ∫ x, tq x ∂ν = 1 := by
  rw [integral_div, div_self (integral_exp_pos (integrable_exp_of_bdd ν hg)).ne']

omit [Nonempty X] [Fintype J] [Nonempty J] hS [IsProbabilityMeasure ν] hg in
/-- At a normalised tilt density the density forcing is the tilt forcing. -/
theorem densForcing_tiltDens (k : X → ℝ) : densForcing S ν tq k = forcing S ν g k := rfl

omit hg in
/-- At a normalised tilt density the density response is the tilt response. -/
theorem densResponse_tiltDens : densResponse hS ν tq = responseOf hS ν g := rfl

/-- **At a normalised tilt density the density response velocity is the tilt response velocity.**
-/
theorem densVel_tiltDens (p : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) {k : X → ℝ}
    (hk : Bdd k) : densVel hS ν tq p k = responseVel hS ν hg hk := by
  unfold densVel responseVel
  rw [densForcing_tiltDens, densResponse_tiltDens,
    hp ⟨forcing S ν g k, forcing_mem_dirSpan hS ν hg hk⟩]
  rfl

end Tilt

end Laplace.Multi
