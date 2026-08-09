/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.RayRescale

/-!
# Uniform quadratic Peano remainder and the local lower bound

Stage H3b of the multivariate programme, the shape consult's flagged
hardest step. Three layers: coercivity of the quadratic form of a
positive-definite matrix (sphere compactness, no spectral theory);
the multivariate quadratic Peano remainder
`L y - L 0 - qform H y / 2 = o(‖y‖²)` for `C²` losses with vanishing
gradient (two applications of the mean value inequality, against the
continuity of the second derivative at the origin); and the local
nondegenerate lower bound `c‖x‖² ≤ (L(q•x) - L(0))/q²`. The
`LocalQuadraticApprox` structure packages exactly what stage H4's
dominated convergence consumes, with a `ofContDiff` constructor.
-/

open Real Matrix Filter Topology Asymptotics Metric

namespace Laplace.Multi

variable {d : ℕ}

/-- The quadratic form is homogeneous of degree two. -/
theorem qform_smul (H : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (x : EuclidD d) :
    qform H (c • x) = c ^ 2 * qform H x := by
  unfold qform
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- The quadratic form vanishes at the origin. -/
theorem qform_zero (H : Matrix (Fin d) (Fin d) ℝ) :
    qform H 0 = 0 := by
  unfold qform
  rw [inner_zero_left]

/-- **Coercivity**: a positive-definite quadratic form dominates a
positive multiple of the squared norm, by sphere compactness. -/
theorem qform_coercive {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) :
    ∃ lam : ℝ, 0 < lam ∧
      ∀ x : EuclidD d, lam * ‖x‖ ^ 2 ≤ qform H x := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · refine ⟨1, one_pos, fun x ↦ ?_⟩
    subst hd
    have hx : x = 0 := Subsingleton.elim x 0
    simp [hx, qform_zero]
  · have hsph : (Metric.sphere (0 : EuclidD d) 1).Nonempty := by
      refine ⟨EuclideanSpace.single ⟨0, hd⟩ 1, ?_⟩
      simp
    obtain ⟨x₀, hx₀mem, hx₀min⟩ :=
      (isCompact_sphere (0 : EuclidD d) 1).exists_isMinOn hsph
        (qform_continuous H).continuousOn
    have hx₀norm : ‖x₀‖ = 1 := by simpa using hx₀mem
    have hx₀ne : x₀ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx₀norm
      exact one_ne_zero hx₀norm.symm
    have hlam_pos : 0 < qform H x₀ := by
      have hnz : WithLp.ofLp x₀ ≠ 0 := by simpa using hx₀ne
      have := hH.re_dotProduct_pos hnz
      rw [qform_eq_dotProduct]
      simpa using this
    refine ⟨qform H x₀, hlam_pos, fun x ↦ ?_⟩
    rcases eq_or_ne x 0 with rfl | hx
    · simp [qform_zero]
    · have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hxs : (‖x‖⁻¹ • x) ∈ Metric.sphere (0 : EuclidD d) 1 := by
        simp [norm_smul, inv_mul_cancel₀ hnorm]
      have hmin := hx₀min hxs
      simp only [Set.mem_setOf_eq] at hmin
      rw [qform_smul] at hmin
      have hn2 : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
      have hinv : (‖x‖⁻¹) ^ 2 * ‖x‖ ^ 2 = 1 := by
        field_simp
      calc qform H x₀ * ‖x‖ ^ 2
          ≤ (‖x‖⁻¹) ^ 2 * qform H x * ‖x‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hmin hn2.le
        _ = qform H x * ((‖x‖⁻¹) ^ 2 * ‖x‖ ^ 2) := by ring
        _ = qform H x := by rw [hinv, mul_one]

/-- The second derivative of a `C²` function is symmetric. -/
theorem hess_symm {L : EuclidD d → ℝ} (hL : ContDiff ℝ 2 L)
    (v w : EuclidD d) : hess L v w = hess L w v := by
  have hC1 : ContDiff ℝ 1 (fderiv ℝ L) := hL.fderiv_right (by norm_num)
  exact second_derivative_symmetric
    (fun y ↦ ((hL.differentiable (by norm_num)) y).hasFDerivAt)
    ((hC1.differentiable (by norm_num) 0).hasFDerivAt) v w

/-- Derivative of the diagonal of a continuous bilinear map. -/
theorem hasFDerivAt_bilinear_diag
    (B : EuclidD d →L[ℝ] EuclidD d →L[ℝ] ℝ) (x : EuclidD d) :
    HasFDerivAt (fun w ↦ B w w) (B x + B.flip x) x := by
  have h := (B.hasFDerivAt (x := x)).clm_apply (hasFDerivAt_id x)
  refine h.congr_fderiv ?_
  ext v
  simp

/-- The gradient of `w ↦ (hess L)(w,w)/2` is `hess L · w` when the
second derivative is symmetric. -/
theorem hasFDerivAt_hess_diag_half {L : EuclidD d → ℝ}
    (hL : ContDiff ℝ 2 L) (x : EuclidD d) :
    HasFDerivAt (fun w ↦ hess L w w / 2) (hess L x) x := by
  have h2' := (hasFDerivAt_bilinear_diag (hess L) x).const_smul (2⁻¹ : ℝ)
  have h2 : HasFDerivAt (fun w : EuclidD d ↦ (2⁻¹ : ℝ) • (hess L w w))
      ((2⁻¹ : ℝ) • ((hess L) x + (hess L).flip x)) x := h2'
  have hfun : (fun w : EuclidD d ↦ (2⁻¹ : ℝ) • (hess L w w)) =
      fun w ↦ hess L w w / 2 := by
    funext w
    rw [smul_eq_mul]
    ring
  rw [hfun] at h2
  have hflip : (2⁻¹ : ℝ) • ((hess L) x + (hess L).flip x) = hess L x := by
    ext v
    simp only [ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
      smul_eq_mul]
    rw [hess_symm hL v x]
    ring
  rwa [hflip] at h2

/-- **The multivariate quadratic Peano remainder**: a `C²` loss with
vanishing gradient at the origin deviates from its Hessian quadratic
by `o(‖y‖²)`. Proved by two applications of the mean value
inequality against the continuity of the second derivative. -/
theorem quadratic_peano {L : EuclidD d → ℝ} (hL : ContDiff ℝ 2 L)
    (hgrad : fderiv ℝ L 0 = 0) :
    (fun y : EuclidD d ↦ L y - L 0 - qform (hessianMatrix L) y / 2)
      =o[𝓝 0] fun y : EuclidD d ↦ ‖y‖ ^ 2 := by
  have hC1 : ContDiff ℝ 1 (fderiv ℝ L) := hL.fderiv_right (by norm_num)
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hcont : ContinuousAt (fderiv ℝ (fderiv ℝ L)) 0 :=
    ((hC1.fderiv_right (by norm_num)).continuous (n := 0)).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hball⟩ := hcont ε hε
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun y hy ↦ ?_⟩
  rw [dist_eq_norm, sub_zero] at hy
  -- Step A: ‖fderiv L w - hess L w‖ ≤ ε‖w‖ on the δ-ball.
  have hpsi : ∀ w : EuclidD d, ‖w‖ < δ →
      ‖fderiv ℝ L w - hess L w‖ ≤ ε * ‖w‖ := by
    intro w hw
    have hderiv : ∀ z ∈ Metric.ball (0 : EuclidD d) δ,
        HasFDerivWithinAt (fun u ↦ fderiv ℝ L u - hess L u)
          (fderiv ℝ (fderiv ℝ L) z - hess L)
          (Metric.ball (0 : EuclidD d) δ) z := by
      intro z _
      exact (((hC1.differentiable (by norm_num)) z).hasFDerivAt.sub
        (hess L).hasFDerivAt).hasFDerivWithinAt
    have hbound : ∀ z ∈ Metric.ball (0 : EuclidD d) δ,
        ‖fderiv ℝ (fderiv ℝ L) z - hess L‖ ≤ ε := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
      have := hball (show dist z 0 < δ by rwa [dist_eq_norm, sub_zero])
      rw [dist_eq_norm] at this
      exact this.le
    have hmvt := (convex_ball (0 : EuclidD d) δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hderiv hbound (Metric.mem_ball_self hδ)
      (by rwa [Metric.mem_ball, dist_eq_norm, sub_zero])
    have hpsi0 : fderiv ℝ L 0 - hess L 0 = 0 := by
      rw [hgrad, map_zero, sub_zero]
    rw [hpsi0, sub_zero, sub_zero] at hmvt
    exact hmvt
  -- Step B: MVT for φ on the closed ball of radius ‖y‖.
  have hkey : ‖(L y - hess L y y / 2) - (L 0 - hess L 0 0 / 2)‖ ≤
      (ε * ‖y‖) * ‖y - 0‖ := by
    have hderiv : ∀ z ∈ Metric.closedBall (0 : EuclidD d) ‖y‖,
        HasFDerivWithinAt (fun u ↦ L u - hess L u u / 2)
          (fderiv ℝ L z - hess L z)
          (Metric.closedBall (0 : EuclidD d) ‖y‖) z := by
      intro z _
      exact (((hL.differentiable (by norm_num)) z).hasFDerivAt.sub
        (hasFDerivAt_hess_diag_half hL z)).hasFDerivWithinAt
    have hbound : ∀ z ∈ Metric.closedBall (0 : EuclidD d) ‖y‖,
        ‖fderiv ℝ L z - hess L z‖ ≤ ε * ‖y‖ := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
      calc ‖fderiv ℝ L z - hess L z‖
          ≤ ε * ‖z‖ := hpsi z (lt_of_le_of_lt hz hy)
        _ ≤ ε * ‖y‖ := by
            apply mul_le_mul_of_nonneg_left hz hε.le
    exact (convex_closedBall (0 : EuclidD d) ‖y‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hderiv hbound (Metric.mem_closedBall_self (norm_nonneg y))
      (by simp [Metric.mem_closedBall, dist_eq_norm])
  have hhess0 : hess L 0 0 = 0 := by
    rw [map_zero]
  rw [hhess0] at hkey
  rw [sub_zero] at hkey
  rw [zero_div, sub_zero] at hkey
  have hqf : qform (hessianMatrix L) y = hess L y y :=
    (hess_apply_self L y).symm
  rw [Real.norm_eq_abs]
  calc |L y - L 0 - qform (hessianMatrix L) y / 2|
      = ‖L y - hess L y y / 2 - L 0‖ := by
        rw [Real.norm_eq_abs, hqf]
        congr 1
        ring
    _ ≤ (ε * ‖y‖) * ‖y‖ := hkey
    _ = ε * ‖‖y‖ ^ 2‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        ring

/-- **The H3 hypothesis package** (per the shape consult): the
positive-definite Hessian with a quantitative coercivity constant and
the quadratic Peano remainder — exactly what stage H4's dominated
convergence consumes. -/
structure LocalQuadraticApprox {d : ℕ} (L : EuclidD d → ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ) where
  hH_posDef : H.PosDef
  lambda : ℝ
  lambda_pos : 0 < lambda
  qform_lower : ∀ x : EuclidD d, lambda * ‖x‖ ^ 2 ≤ qform H x
  quadratic_peano :
    (fun y : EuclidD d ↦ L y - L 0 - qform H y / 2)
      =o[𝓝 0] fun y : EuclidD d ↦ ‖y‖ ^ 2

/-- The package holds for any `C²` loss with vanishing gradient and
positive-definite Hessian at the origin. -/
noncomputable def LocalQuadraticApprox.ofContDiff {L : EuclidD d → ℝ}
    (hL : ContDiff ℝ 2 L) (hgrad : fderiv ℝ L 0 = 0)
    (hH : (hessianMatrix L).PosDef) :
    LocalQuadraticApprox L (hessianMatrix L) where
  hH_posDef := hH
  lambda := (qform_coercive hH).choose
  lambda_pos := (qform_coercive hH).choose_spec.1
  qform_lower := (qform_coercive hH).choose_spec.2
  quadratic_peano := _root_.Laplace.Multi.quadratic_peano hL hgrad

namespace LocalQuadraticApprox

variable {L : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- **The local nondegenerate lower bound**: on a small ball the
rescaled loss quotient dominates `c‖x‖²`. -/
theorem exists_local_lower_bound (A : LocalQuadraticApprox L H) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ q : ℝ, ∀ x : EuclidD d, 0 < q → ‖q • x‖ ≤ δ →
        c * ‖x‖ ^ 2 ≤ (L (q • x) - L 0) / q ^ 2 := by
  have hpe := A.quadratic_peano
  rw [Asymptotics.isLittleO_iff] at hpe
  have h4 := hpe (show (0 : ℝ) < A.lambda / 4 by
    have := A.lambda_pos; positivity)
  rw [Metric.eventually_nhds_iff] at h4
  obtain ⟨δ₀, hδ₀, hb⟩ := h4
  refine ⟨δ₀ / 2, A.lambda / 4, by positivity,
    by have := A.lambda_pos; positivity, fun q x hq hqx ↦ ?_⟩
  set y : EuclidD d := q • x with hy_def
  have hyδ : dist y 0 < δ₀ := by
    rw [dist_eq_norm, sub_zero]
    calc ‖y‖ ≤ δ₀ / 2 := hqx
      _ < δ₀ := by linarith
  have hbnd := hb hyδ
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖y‖ ^ 2)] at hbnd
  have hlow := A.qform_lower y
  have hstep : A.lambda / 4 * ‖y‖ ^ 2 ≤ L y - L 0 := by
    nlinarith [hlow, neg_le_of_abs_le hbnd]
  have hnorm_y : ‖y‖ ^ 2 = q ^ 2 * ‖x‖ ^ 2 := by
    rw [hy_def, norm_smul, Real.norm_eq_abs, abs_of_pos hq, mul_pow]
  rw [hnorm_y] at hstep
  rw [le_div_iff₀ (by positivity : (0:ℝ) < q ^ 2)]
  nlinarith [hstep]

/-- The rescaled loss quotient converges to the half quadratic form
along every ray (derived from the Peano remainder, superseding the
`C²` ray version for package consumers). -/
theorem rescaled_tendsto (A : LocalQuadraticApprox L H)
    (x : EuclidD d) :
    Tendsto (fun q : ℝ ↦ (L (q • x) - L 0) / q ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (qform H x / 2)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hz : ∀ q : ℝ, (L (q • (0 : EuclidD d)) - L 0) / q ^ 2 = 0 := by
      intro q
      rw [smul_zero, sub_self, zero_div]
    have h0 : qform H (0 : EuclidD d) / 2 = 0 := by
      rw [qform_zero]
      norm_num
    rw [h0]
    exact Tendsto.congr (fun q ↦ (hz q).symm) tendsto_const_nhds
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    have hpe := A.quadratic_peano
    rw [Asymptotics.isLittleO_iff] at hpe
    have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := by
      have := norm_pos_iff.mpr hx
      positivity
    have h4 := hpe (show (0 : ℝ) < ε / (2 * ‖x‖ ^ 2) by positivity)
    rw [Metric.eventually_nhds_iff] at h4
    obtain ⟨δ₀, hδ₀, hb⟩ := h4
    refine ⟨δ₀ / (‖x‖ + 1), by positivity, fun q hq hqd ↦ ?_⟩
    have hq0 : (0 : ℝ) < q := hq
    rw [Real.dist_eq, sub_zero, abs_of_pos hq0] at hqd
    set y : EuclidD d := q • x with hy_def
    have hyδ : dist y 0 < δ₀ := by
      rw [dist_eq_norm, sub_zero, hy_def, norm_smul, Real.norm_eq_abs,
        abs_of_pos hq0]
      calc q * ‖x‖ < δ₀ / (‖x‖ + 1) * ‖x‖ := by
            apply mul_lt_mul_of_pos_right hqd
            exact norm_pos_iff.mpr hx
        _ ≤ δ₀ := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [norm_nonneg x, hδ₀]
    have hbnd := hb hyδ
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖y‖ ^ 2)] at hbnd
    have hnorm_y : ‖y‖ ^ 2 = q ^ 2 * ‖x‖ ^ 2 := by
      rw [hy_def, norm_smul, Real.norm_eq_abs, abs_of_pos hq0, mul_pow]
    have hqf_y : qform H y = q ^ 2 * qform H x := qform_smul H q x
    rw [Real.dist_eq]
    have hq2 : (0 : ℝ) < q ^ 2 := by positivity
    have hexpand : (L (q • x) - L 0) / q ^ 2 - qform H x / 2 =
        (L y - L 0 - qform H y / 2) / q ^ 2 := by
      rw [hqf_y, hy_def]
      field_simp
    rw [hexpand, abs_div, abs_of_pos hq2, div_lt_iff₀ hq2]
    calc |L y - L 0 - qform H y / 2|
        ≤ ε / (2 * ‖x‖ ^ 2) * ‖y‖ ^ 2 := hbnd
      _ = ε / 2 * q ^ 2 := by
          rw [hnorm_y]
          field_simp
      _ < ε * q ^ 2 := by nlinarith

end LocalQuadraticApprox

end Laplace.Multi
