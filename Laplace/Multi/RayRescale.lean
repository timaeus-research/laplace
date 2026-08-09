/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.QuadForm

/-!
# Fixed-ray quadratic rescaling

Stage H3a of the multivariate programme: for a `C²` loss with
vanishing gradient at the origin, the rescaled loss quotient
`(L(q•x) - L(0))/q²` converges along `q → 0⁺` to `qform H x / 2`,
where `H` is the Hessian matrix at the origin. The route is the shape
consult's ray reduction: restrict `L` to the ray `q ↦ q•x`, compute
the ray's first and second derivatives by the chain rule, and apply
Mathlib's one-dimensional Peano remainder `taylor_isLittleO` (the
`SmoothRecovery` pattern). The Hessian bridge from the second Fréchet
derivative's diagonal to the matrix quadratic form is by one-hot
basis expansion of the continuous bilinear map.
-/

open Real Matrix Filter Topology Asymptotics

namespace Laplace.Multi

variable {d : ℕ}

/-- The Hessian of a loss at the origin, as a continuous bilinear
map (the second Fréchet derivative in curried form). -/
noncomputable def hess (L : EuclidD d → ℝ) :
    EuclidD d →L[ℝ] EuclidD d →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ L) 0

/-- The Hessian matrix at the origin, by one-hot basis evaluation. -/
noncomputable def hessianMatrix (L : EuclidD d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ hess L (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- Euclidean vectors decompose over the one-hot basis. -/
theorem eq_sum_single (x : EuclidD d) :
    x = ∑ i, x i • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp

/-- Continuous bilinear maps expand over the one-hot basis. -/
theorem clm_bilinear_expand (B : EuclidD d →L[ℝ] EuclidD d →L[ℝ] ℝ)
    (x y : EuclidD d) :
    B x y = ∑ i, ∑ j, x i * y j *
      B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  calc B x y
      = B (∑ i, x i • EuclideanSpace.single i (1 : ℝ)) y := by
        rw [← eq_sum_single]
    _ = ∑ i, x i * B (EuclideanSpace.single i 1) y := by
        rw [map_sum, ContinuousLinearMap.sum_apply]
        exact Finset.sum_congr rfl fun i _ ↦ by
          rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    _ = ∑ i, x i * ∑ j, y j *
          B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        congr 1
        calc B (EuclideanSpace.single i 1) y
            = B (EuclideanSpace.single i 1)
                (∑ j, y j • EuclideanSpace.single j (1 : ℝ)) := by
              rw [← eq_sum_single]
          _ = ∑ j, y j * B (EuclideanSpace.single i 1)
                (EuclideanSpace.single j 1) := by
              rw [map_sum]
              exact Finset.sum_congr rfl fun j _ ↦ by
                rw [map_smul, smul_eq_mul]
    _ = ∑ i, ∑ j, x i * y j *
          B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **The Hessian bridge**: the second derivative's diagonal is the
quadratic form of the Hessian matrix. -/
theorem hess_apply_self (L : EuclidD d → ℝ) (x : EuclidD d) :
    hess L x x = qform (hessianMatrix L) x := by
  rw [clm_bilinear_expand, qform_eq_dotProduct]
  simp only [dotProduct, Matrix.mulVec, hessianMatrix]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- First ray derivative at any point, by the chain rule. -/
theorem ray_hasDerivAt {L : EuclidD d → ℝ} (hL : ContDiff ℝ 2 L)
    (x : EuclidD d) (q : ℝ) :
    HasDerivAt (fun t : ℝ ↦ L (t • x)) (fderiv ℝ L (q • x) x) q := by
  have h1 : HasFDerivAt L (fderiv ℝ L (q • x)) (q • x) :=
    (hL.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ ↦ t • x) x q := by
    simpa using (hasDerivAt_id q).smul_const x
  simpa using h1.comp_hasDerivAt q h2

/-- The ray derivative as a function. -/
theorem ray_deriv {L : EuclidD d → ℝ} (hL : ContDiff ℝ 2 L)
    (x : EuclidD d) :
    deriv (fun t : ℝ ↦ L (t • x)) = fun q ↦ fderiv ℝ L (q • x) x :=
  funext fun q ↦ (ray_hasDerivAt hL x q).deriv

/-- Second ray derivative at the origin is the Hessian diagonal. -/
theorem ray_hasDerivAt_two {L : EuclidD d → ℝ} (hL : ContDiff ℝ 2 L)
    (x : EuclidD d) :
    HasDerivAt (fun q : ℝ ↦ fderiv ℝ L (q • x) x) (hess L x x) 0 := by
  have hC1 : ContDiff ℝ 1 (fderiv ℝ L) := hL.fderiv_right (by norm_num)
  have h1 : HasFDerivAt (fderiv ℝ L) (fderiv ℝ (fderiv ℝ L) 0)
      ((0 : ℝ) • x) := by
    rw [zero_smul]
    exact (hC1.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ ↦ t • x) x 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const x
  have h3 : HasDerivAt (fun q : ℝ ↦ fderiv ℝ L (q • x))
      (fderiv ℝ (fderiv ℝ L) 0 x) 0 := h1.comp_hasDerivAt 0 h2
  have h4 := h3.clm_apply (hasDerivAt_const (0 : ℝ) x)
  simpa [hess] using h4

/-- The ray's second iterated derivative at the origin. -/
theorem ray_iteratedDeriv_two {L : EuclidD d → ℝ}
    (hL : ContDiff ℝ 2 L) (x : EuclidD d) :
    iteratedDeriv 2 (fun t : ℝ ↦ L (t • x)) 0 = hess L x x := by
  have h2 : iteratedDeriv 2 (fun t : ℝ ↦ L (t • x)) =
      deriv (deriv (fun t : ℝ ↦ L (t • x))) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_one]
  rw [h2, ray_deriv hL x]
  exact (ray_hasDerivAt_two hL x).deriv

/-- The ray Taylor polynomial of order two collapses to
`L 0 + q²·(hess/2)` when the gradient vanishes. -/
theorem ray_taylor_eval {L : EuclidD d → ℝ} (hL : ContDiff ℝ 2 L)
    (hgrad : fderiv ℝ L 0 = 0) (x : EuclidD d) (q : ℝ) :
    taylorWithinEval (fun t : ℝ ↦ L (t • x)) 2 Set.univ 0 q =
      L 0 + q ^ 2 * (hess L x x / 2) := by
  rw [taylor_within_apply]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp only [iteratedDerivWithin_univ]
  have h0 : iteratedDeriv 0 (fun t : ℝ ↦ L (t • x)) 0 = L 0 := by
    rw [iteratedDeriv_zero]
    simp
  have h1 : iteratedDeriv 1 (fun t : ℝ ↦ L (t • x)) 0 = 0 := by
    rw [iteratedDeriv_one, ray_deriv hL x]
    simp [hgrad]
  rw [h0, h1, ray_iteratedDeriv_two hL x]
  simp [Nat.factorial]
  ring

/-- **Fixed-ray quadratic rescaling** (germbij multivariate H3a): for
a `C²` loss with vanishing gradient at the origin, the rescaled loss
quotient converges along every ray to half the Hessian quadratic
form. -/
theorem rescaled_loss_tendsto {L : EuclidD d → ℝ}
    (hL : ContDiff ℝ 2 L) (hgrad : fderiv ℝ L 0 = 0) (x : EuclidD d) :
    Tendsto (fun q : ℝ ↦ (L (q • x) - L 0) / q ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (qform (hessianMatrix L) x / 2)) := by
  have hg : ContDiff ℝ 2 (fun t : ℝ ↦ L (t • x)) := by
    have hray : ContDiff ℝ 2 fun t : ℝ ↦ t • x :=
      (ContinuousLinearMap.toSpanSingleton ℝ x).contDiff.of_le le_top
    exact hL.comp hray
  have hlo : (fun q : ℝ ↦ L (q • x) - L 0 - q ^ 2 * (hess L x x / 2))
      =o[𝓝 0] fun q : ℝ ↦ q ^ 2 := by
    have h := taylor_isLittleO (convex_univ) (Set.mem_univ (0 : ℝ))
      (hg.contDiffOn (s := Set.univ))
    rw [nhdsWithin_univ] at h
    refine (h.congr' ?_ ?_)
    · filter_upwards with q
      rw [ray_taylor_eval hL hgrad x q]
      ring
    · filter_upwards with q
      rw [sub_zero]
  have hdiv : Tendsto
      (fun q : ℝ ↦ (L (q • x) - L 0 - q ^ 2 * (hess L x x / 2)) / q ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hlo.tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds
  have hsub : Tendsto
      (fun q : ℝ ↦ (L (q • x) - L 0) / q ^ 2 - hess L x x / 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine hdiv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hq
    field_simp
  have := tendsto_sub_nhds_zero_iff.mp hsub
  rwa [hess_apply_self L x] at this

end Laplace.Multi
