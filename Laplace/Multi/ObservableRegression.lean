/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.DualPotential
import Laplace.Multi.DataQuotient

/-!
# The response of an arbitrary observable in mean coordinates: regression on the statistic

The posterior expectation `⟨φ⟩_a` of a bounded observable is a function of the data `a`, and through
the inverse mean chart `θ = m⁻¹` a function `Φ(y) = ⟨φ⟩_{θ(y)}` of the response coordinates `y`.
Its derivative is characterised by the **regression identity**

  `DΦ(m(a)) (Cov_a(Rᵢ, R_v))ᵢ = Cov_a(φ, R_v)`   (`obsMean_deriv_cov`),

i.e. `DΦ = Cov(φ, R) · Cov(R, R)⁻¹`: the change of any posterior expectation value with the change
of the response coordinates is the linear regression coefficient of `φ` on the sufficient statistic.
In
particular the sensitivity of `⟨φ⟩` to a response direction is bounded by
`√Var(φ)` times the dual-Hessian length of that direction (`abs_obsMean_deriv_le`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
  (hnd : ∀ v : ι → ℝ, v ≠ 0 → ¬ ∃ c : ℝ, ∀ᵐ x ∂μ, π x ≠ 0 → dirLoss R v x = c)
  {φ : X → ℝ} (hφm : Measurable φ) {Mφ : ℝ} (hφ : ∀ x, |φ x| ≤ Mφ)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht hnd hφm hφ

/-- The observable as a function of the response coordinates, `Φ(y) = ⟨φ⟩_{θ(y)}`. -/
noncomputable def obsMean (μ : Measure X) (π L₀ φ : X → ℝ) (R : ι → X → ℝ) (t : ℝ) (y : ι → ℝ) :
    ℝ :=
  priorExp μ π (affLoss L₀ R (Function.invFun (meanMap μ π L₀ R t) y)) φ t

omit hφm hφ in
theorem obsMean_meanMap (a : ι → ℝ) :
    obsMean μ π L₀ φ R t (meanMap μ π L₀ R t a) = priorExp μ π (affLoss L₀ R a) φ t := by
  unfold obsMean
  rw [invFun_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd]

/-- `Φ` is differentiable in the response coordinates, with derivative `D⟨φ⟩ ∘ (Dm)⁻¹`. -/
theorem hasFDerivAt_obsMean (a : ι → ℝ) :
    HasFDerivAt (obsMean μ π L₀ φ R t)
      ((obsMapDeriv μ π L₀ φ R t a).comp
        (invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a))
      (meanMap μ π L₀ R t a) := by
  have hθ := (hasStrictFDerivAt_invFun_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd
    a).hasFDerivAt
  have hθa : Function.invFun (meanMap μ π L₀ R t) (meanMap μ π L₀ R t a) = a :=
    invFun_meanMap hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a
  have h := (hasFDerivAt_obsMap hπm hπi hπ hπpos hL₀m hL₀ hR hφm hφ ht
    (Function.invFun (meanMap μ π L₀ R t) (meanMap μ π L₀ R t a))).comp (meanMap μ π L₀ R t a) hθ
  rw [hθa] at h
  exact h

/-- **The regression identity**: `DΦ(m(a)) (Cov_a(Rᵢ, R_v))ᵢ = Cov_a(φ, R_v)` — the response of
`⟨φ⟩` in mean coordinates is the regression of `φ` on the statistic. -/
theorem obsMean_deriv_cov (a v : ι → ℝ) :
    ((obsMapDeriv μ π L₀ φ R t a).comp
        (invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a))
      (fun i ↦ priorCov μ π (affLoss L₀ R a) (R i) (dirLoss R v) t) =
      priorCov μ π (affLoss L₀ R a) φ (dirLoss R v) t := by
  have hZ : priorZ μ π (affLoss L₀ R a) t ≠ 0 :=
    (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a).ne'
  have e : (fun i ↦ priorCov μ π (affLoss L₀ R a) (R i) (dirLoss R v) t) =
      (-t)⁻¹ • meanMapDeriv μ π L₀ R t a v := by
    funext i
    rw [Pi.smul_apply, meanMapDeriv_apply hπm hπi (fun x ↦ (hπ x).le) hL₀m hL₀ hR ht hZ v i,
      smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by linarith : (-t) ≠ 0), one_mul]
  rw [e, ContinuousLinearMap.comp_apply, map_smul, invJac_meanMapDeriv, map_smul, smul_eq_mul,
    obsMapDeriv_apply hπm hπi hπ hπpos hL₀m hL₀ hR hφm hφ ht a v, ← mul_assoc,
    inv_mul_cancel₀ (by linarith : (-t) ≠ 0), one_mul]

/-- **Sensitivity bound in mean coordinates**: along a response velocity `ṁ = Dm(a) v`,
`|DΦ(m(a)) ṁ| ≤ √Var_a(φ) · √⟨ṁ, D²I ṁ⟩`. -/
theorem abs_obsMean_deriv_le (a v : ι → ℝ) :
    |((obsMapDeriv μ π L₀ φ R t a).comp
        (invJac hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a))
        (meanMapDeriv μ π L₀ R t a v)| ≤
      Real.sqrt (priorCov μ π (affLoss L₀ R a) φ φ t) *
        Real.sqrt (dotJ (meanMapDeriv μ π L₀ R t a v)
          (dualHessian hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a
            (meanMapDeriv μ π L₀ R t a v))) := by
  rw [ContinuousLinearMap.comp_apply, invJac_meanMapDeriv,
    dualHessian_quadratic_form hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR ht hnd a v]
  exact abs_obsMapDeriv_le hπm hπi hπ hπpos hL₀m hL₀ hR hφm hφ ht a v

end

end Laplace.Multi
