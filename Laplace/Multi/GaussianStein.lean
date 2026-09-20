/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.GaussianCovariance
import Laplace.Multi.QuadLowerBound
import Laplace.Multi.HomogeneousTaylor
import Laplace.Multi.MonomialTests

/-!
# Stein's identity for the quadratic Gaussian and the radial-moment identities

For the kernel `e^{-q(x)/2}`, `q(x) = ⟪x, Hx⟫`, integration by parts on `ℝ^d`
(Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, which needs
only integrability) gives **Stein's identity** for smooth `f` of polynomial
growth with polynomially growing derivative:

  `∫ ∂_v f · e^{-q/2} = ∫ f · ½(⟪x, Hv⟫ + ⟪v, Hx⟫) · e^{-q/2}`

(`stein_quadKernel`; no symmetry of `H` is used). Summed over the coordinate
directions with `f = xᵢ F` this is the radial identity

  `∫ F q e^{-q/2} = d ∫ F e^{-q/2} + ∫ (x·∇F) e^{-q/2}`

(`integral_mul_qform_quadKernel`), and with Euler's identity `x·∇Q = k Q` for
`Q` homogeneous of degree `k` (`fderiv_apply_self_of_isHomogeneous`) it yields the
two covariance identities behind the two-radial-probe rigidity of the germbij
plan:

  `Cov_γ[q, Q] = k E_γ[Q]`,   `Cov_γ[q², Q] = k (k + 2d + 2) E_γ[Q]`

(`gaussianCovariance_qform_of_isHomogeneous`, `gaussianCovariance_qform_sq_of_isHomogeneous`),
under `γ = N(0, H⁻¹)`.
-/

open MeasureTheory
open scoped ContDiff

namespace Laplace.Multi

variable {d : ℕ}

/-! ### Derivatives of the quadratic form and of the kernel -/

/-- The symmetrised bilinear derivative `⟪x, Hv⟫ + ⟪v, Hx⟫` of `q` at `x` in direction `v`. -/
noncomputable def qderiv (H : Matrix (Fin d) (Fin d) ℝ) (x v : EuclidD d) : ℝ :=
  inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) H v) + inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) H x)

theorem hasFDerivAt_qform (H : Matrix (Fin d) (Fin d) ℝ) (x : EuclidD d) :
    HasFDerivAt (qform H)
      ((fderivInnerCLM ℝ (x, Matrix.toEuclideanCLM (𝕜 := ℝ) H x)).comp
        ((ContinuousLinearMap.id ℝ (EuclidD d)).prod (Matrix.toEuclideanCLM (𝕜 := ℝ) H))) x := by
  have h := (hasFDerivAt_id x).inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) H).hasFDerivAt
  exact h

theorem fderiv_qform_apply (H : Matrix (Fin d) (Fin d) ℝ) (x v : EuclidD d) :
    fderiv ℝ (qform H) x v = qderiv H x v := by
  rw [(hasFDerivAt_qform H x).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, fderivInnerCLM_apply, qderiv]

theorem quadKernel_eq (H : Matrix (Fin d) (Fin d) ℝ) :
    quadKernel H = fun y ↦ Real.exp (-(1 / 2 : ℝ) * qform H y) := by
  funext y
  unfold quadKernel
  congr 1
  ring

theorem hasFDerivAt_quadKernel (H : Matrix (Fin d) (Fin d) ℝ) (x : EuclidD d) :
    HasFDerivAt (quadKernel H)
      (quadKernel H x • ((-(1 / 2 : ℝ)) • fderiv ℝ (qform H) x)) x := by
  have h1 : HasFDerivAt (fun y ↦ -(1 / 2 : ℝ) * qform H y)
      ((-(1 / 2 : ℝ)) • fderiv ℝ (qform H) x) x :=
    ((hasFDerivAt_qform H x).const_mul (-(1 / 2 : ℝ))).congr_fderiv
      (by rw [(hasFDerivAt_qform H x).fderiv])
  have h2 := h1.exp
  rw [quadKernel_eq]
  exact h2

theorem fderiv_quadKernel_apply (H : Matrix (Fin d) (Fin d) ℝ) (x v : EuclidD d) :
    fderiv ℝ (quadKernel H) x v = -(qderiv H x v / 2) * quadKernel H x := by
  rw [(hasFDerivAt_quadKernel H x).fderiv]
  simp only [smul_apply, smul_eq_mul, fderiv_qform_apply]
  ring

theorem differentiable_quadKernel (H : Matrix (Fin d) (Fin d) ℝ) :
    Differentiable ℝ (quadKernel H) := fun x ↦ (hasFDerivAt_quadKernel H x).differentiableAt

/-! ### Polynomial growth of the linear factors -/

theorem hasPolynomialGrowth_inner_left (v : EuclidD d) :
    HasPolynomialGrowth fun x : EuclidD d ↦ inner ℝ x v := by
  refine ⟨‖v‖, 1, norm_nonneg _, fun x ↦ ?_⟩
  calc |inner ℝ x v| ≤ ‖x‖ * ‖v‖ := abs_real_inner_le_norm x v
    _ ≤ ‖v‖ * (1 + ‖x‖ ^ 1) := by nlinarith [norm_nonneg x, norm_nonneg v]

theorem hasPolynomialGrowth_qderiv (H : Matrix (Fin d) (Fin d) ℝ) (v : EuclidD d) :
    HasPolynomialGrowth fun x : EuclidD d ↦ qderiv H x v := by
  set A := Matrix.toEuclideanCLM (𝕜 := ℝ) H
  refine ⟨‖A v‖ + ‖v‖ * ‖A‖, 1, by positivity, fun x ↦ ?_⟩
  have h1 : |inner ℝ x (A v)| ≤ ‖x‖ * ‖A v‖ := abs_real_inner_le_norm _ _
  have h2 : |inner ℝ v (A x)| ≤ ‖v‖ * (‖A‖ * ‖x‖) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (A.le_opNorm x) (norm_nonneg _))
  calc |qderiv H x v| ≤ |inner ℝ x (A v)| + |inner ℝ v (A x)| := abs_add_le _ _
    _ ≤ ‖x‖ * ‖A v‖ + ‖v‖ * (‖A‖ * ‖x‖) := add_le_add h1 h2
    _ ≤ (‖A v‖ + ‖v‖ * ‖A‖) * (1 + ‖x‖ ^ 1) := by
        nlinarith [norm_nonneg x, norm_nonneg v, norm_nonneg A, norm_nonneg (A v)]

theorem hasPolynomialGrowth_coord (i : Fin d) :
    HasPolynomialGrowth fun x : EuclidD d ↦ x i :=
  ⟨1, 1, zero_le_one, fun x ↦ by
    have := euclid_abs_coord_le_norm x i
    nlinarith [norm_nonneg x]⟩

theorem hasPolynomialGrowth_const (c : ℝ) : HasPolynomialGrowth fun _ : EuclidD d ↦ c :=
  ⟨|c|, 0, abs_nonneg _, fun x ↦ by
    simp only [pow_zero]
    nlinarith [abs_nonneg c]⟩

/-! ### Stein's identity -/

/-- **Stein's identity for the quadratic Gaussian**: for smooth `f` with `f` and `∂_v f`
of polynomial growth, `∫ ∂_v f e^{-q/2} = ∫ f · (qderiv/2) e^{-q/2}`. -/
theorem stein_quadKernel {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {f : EuclidD d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfg : HasPolynomialGrowth f) (v : EuclidD d)
    (hf'g : HasPolynomialGrowth fun x ↦ fderiv ℝ f x v) :
    ∫ x, fderiv ℝ f x v * quadKernel H x = ∫ x, f x * (qderiv H x v / 2) * quadKernel H x := by
  have hfc : Continuous f := hf.continuous
  have hf'c : Continuous fun x ↦ fderiv ℝ f x v :=
    (hf.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hqc : Continuous fun x ↦ qderiv H x v := by
    unfold qderiv
    fun_prop
  have hA : Integrable fun x ↦ fderiv ℝ f x v * quadKernel H x :=
    integrable_mul_quadKernel_of_polynomialGrowth hH hf'c.aestronglyMeasurable hf'g
  have hB : Integrable fun x ↦ f x * fderiv ℝ (quadKernel H) x v := by
    have h := integrable_mul_quadKernel_of_polynomialGrowth hH
      (hfc.mul (continuous_const.mul hqc)).aestronglyMeasurable
      (hfg.mul ((hasPolynomialGrowth_const (-(1 / 2 : ℝ))).mul (hasPolynomialGrowth_qderiv H v)))
    refine h.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.mul_apply]
    rw [fderiv_quadKernel_apply]
    ring
  have hC : Integrable fun x ↦ f x * quadKernel H x :=
    integrable_mul_quadKernel_of_polynomialGrowth hH hfc.aestronglyMeasurable hfg
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hA hB hC
    (fun x _ ↦ (hf.differentiable (by simp) x)) (fun x _ ↦ (differentiable_quadKernel H x))
  have hlhs : ∫ x, f x * fderiv ℝ (quadKernel H) x v =
      -∫ x, f x * (qderiv H x v / 2) * quadKernel H x := by
    rw [← integral_neg]
    congr 1
    funext x
    rw [fderiv_quadKernel_apply]
    ring
  rw [hlhs] at key
  linarith

/-! ### Euler's identity -/

/-- **Euler's identity**: `x·∇Q = k Q(x)` for `Q` differentiable and homogeneous of degree `k`. -/
theorem fderiv_apply_self_of_isHomogeneous {Q : EuclidD d → ℝ} (hQ : Differentiable ℝ Q)
    {k : ℕ} (hhom : IsHomogeneousOfDegree k Q) (x : EuclidD d) :
    fderiv ℝ Q x x = k * Q x := by
  have h1 : HasDerivAt (fun s : ℝ ↦ Q (s • x)) (fderiv ℝ Q x x) 1 := by
    have hline : HasDerivAt (fun s : ℝ ↦ s • x) ((1 : ℝ) • x) 1 := (hasDerivAt_id 1).smul_const x
    have := (hQ ((1 : ℝ) • x)).hasFDerivAt.comp_hasDerivAt 1 hline
    rw [one_smul] at this
    convert this using 1 <;> rfl
  have h2 : HasDerivAt (fun s : ℝ ↦ s ^ k * Q x) ((k : ℝ) * (1 : ℝ) ^ (k - 1) * Q x) 1 :=
    (hasDerivAt_pow k 1).mul_const (Q x)
  have hfun : (fun s : ℝ ↦ Q (s • x)) = fun s : ℝ ↦ s ^ k * Q x := funext fun s ↦ hhom s x
  rw [hfun] at h1
  have := h1.unique h2
  simpa using this

/-! ### The radial identities -/

/-- The coordinate expansion `∑ᵢ xᵢ qderiv(x, eᵢ) = 2 q(x)`. -/
theorem sum_coord_mul_qderiv (H : Matrix (Fin d) (Fin d) ℝ) (x : EuclidD d) :
    ∑ i, x i * qderiv H x (EuclideanSpace.single i (1 : ℝ)) = 2 * qform H x := by
  have hx : ∑ i, x i • (EuclideanSpace.single i (1 : ℝ) : EuclidD d) = x := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) H x) =
      ∑ i, x i * inner ℝ x
        (Matrix.toEuclideanCLM (𝕜 := ℝ) H (EuclideanSpace.single i (1 : ℝ))) := by
    calc inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) H x)
        = inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) H
            (∑ i, x i • (EuclideanSpace.single i (1 : ℝ) : EuclidD d))) := by rw [hx]
      _ = ∑ i, x i * inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) H
            (EuclideanSpace.single i (1 : ℝ))) := by
          rw [map_sum, inner_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [map_smul, inner_smul_right]
  have h2 : inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) H x) =
      ∑ i, x i * inner ℝ (EuclideanSpace.single i (1 : ℝ))
        (Matrix.toEuclideanCLM (𝕜 := ℝ) H x) := by
    calc inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) H x)
        = inner ℝ (∑ i, x i • (EuclideanSpace.single i (1 : ℝ) : EuclidD d))
            (Matrix.toEuclideanCLM (𝕜 := ℝ) H x) := by rw [hx]
      _ = ∑ i, x i * inner ℝ (EuclideanSpace.single i (1 : ℝ))
            (Matrix.toEuclideanCLM (𝕜 := ℝ) H x) := by
          rw [sum_inner]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [inner_smul_left]
          simp
  unfold qderiv qform
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← h1, ← h2]
  ring

/-- **The radial identity**: `∫ F q e^{-q/2} = d ∫ F e^{-q/2} + ∫ (x·∇F) e^{-q/2}` for smooth `F`
with `F` and its coordinate derivatives of polynomial growth. -/
theorem integral_mul_qform_quadKernel {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {F : EuclidD d → ℝ} (hF : ContDiff ℝ ∞ F) (hFg : HasPolynomialGrowth F)
    (hF'g : ∀ v, HasPolynomialGrowth fun x ↦ fderiv ℝ F x v) :
    ∫ x, F x * qform H x * quadKernel H x =
      d * (∫ x, F x * quadKernel H x) + ∫ x, fderiv ℝ F x x * quadKernel H x := by
  classical
  set e : Fin d → EuclidD d := fun i ↦ EuclideanSpace.single i (1 : ℝ) with he_def
  -- Stein for `fᵢ = xᵢ F` in direction `eᵢ`
  have hcoordD : ∀ (i : Fin d) (x : EuclidD d), HasFDerivAt (fun x : EuclidD d ↦ x i)
      (EuclideanSpace.proj (𝕜 := ℝ) i) x := fun i x ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
  have hfi : ∀ i : Fin d, ∀ x, fderiv ℝ (fun x : EuclidD d ↦ x i * F x) x (e i) =
      F x + x i * fderiv ℝ F x (e i) := by
    intro i x
    have hd : HasFDerivAt (fun y : EuclidD d ↦ y i * F y) _ x :=
      (hcoordD i x).mul (hF.differentiable (by simp) x).hasFDerivAt
    rw [hd.fderiv]
    simp [he_def, add_comm]
  have hsmooth : ∀ i : Fin d, ContDiff ℝ ∞ fun x : EuclidD d ↦ x i * F x := fun i ↦
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).mul hF
  have hgrowth : ∀ i : Fin d, HasPolynomialGrowth fun x : EuclidD d ↦ x i * F x := fun i ↦
    (hasPolynomialGrowth_coord i).mul hFg
  have hgrowth' : ∀ i : Fin d, HasPolynomialGrowth fun x : EuclidD d ↦
      fderiv ℝ (fun x : EuclidD d ↦ x i * F x) x (e i) := by
    intro i
    have h := hFg.add ((hasPolynomialGrowth_coord i).mul (hF'g (e i)))
    obtain ⟨C, n, hC, hb⟩ := h
    refine ⟨C, n, hC, fun x ↦ ?_⟩
    dsimp only
    rw [hfi i x]
    exact hb x
  have hstein : ∀ i : Fin d,
      ∫ x, (F x + x i * fderiv ℝ F x (e i)) * quadKernel H x =
        ∫ x, (x i * F x) * (qderiv H x (e i) / 2) * quadKernel H x := by
    intro i
    have := stein_quadKernel hH (hsmooth i) (hgrowth i) (e i) (hgrowth' i)
    rw [← this]
    congr 1
    funext x
    rw [hfi i x]
  -- integrability of the pieces
  have hFc : Continuous F := hF.continuous
  have hF'c : ∀ v, Continuous fun x ↦ fderiv ℝ F x v := fun v ↦
    (hF.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hcoordc : ∀ i : Fin d, Continuous fun x : EuclidD d ↦ x i := fun i ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
  have hqc : ∀ v, Continuous fun x ↦ qderiv H x v := fun v ↦ by
    unfold qderiv
    fun_prop
  have hIF : Integrable fun x ↦ F x * quadKernel H x :=
    integrable_mul_quadKernel_of_polynomialGrowth hH hFc.aestronglyMeasurable hFg
  have hIx : ∀ i : Fin d, Integrable fun x ↦ x i * fderiv ℝ F x (e i) * quadKernel H x := fun i ↦
    integrable_mul_quadKernel_of_polynomialGrowth hH
      ((hcoordc i).mul (hF'c (e i))).aestronglyMeasurable
      ((hasPolynomialGrowth_coord i).mul (hF'g (e i)))
  have hIR : ∀ i : Fin d,
      Integrable fun x ↦ (x i * F x) * (qderiv H x (e i) / 2) * quadKernel H x := by
    intro i
    have h := integrable_mul_quadKernel_of_polynomialGrowth hH
      (((hcoordc i).mul hFc).mul ((hqc (e i)).mul continuous_const)).aestronglyMeasurable
      (((hasPolynomialGrowth_coord i).mul hFg).mul
        ((hasPolynomialGrowth_qderiv H (e i)).mul (hasPolynomialGrowth_const (1 / 2))))
    refine h.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.mul_apply]
    ring
  -- the two sides of the summed Stein identity
  have hx : ∀ x : EuclidD d, ∑ i, x i • e i = x := by
    intro x
    ext j
    simp [he_def, Finset.sum_apply, Pi.single_apply]
  have hsumL : ∑ i, ∫ x, (F x + x i * fderiv ℝ F x (e i)) * quadKernel H x =
      d * (∫ x, F x * quadKernel H x) + ∫ x, fderiv ℝ F x x * quadKernel H x := by
    have h1 : ∀ i : Fin d, ∫ x, (F x + x i * fderiv ℝ F x (e i)) * quadKernel H x =
        (∫ x, F x * quadKernel H x) + ∫ x, x i * fderiv ℝ F x (e i) * quadKernel H x := by
      intro i
      rw [← integral_add hIF (hIx i)]
      congr 1
      funext x
      ring
    simp only [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    congr 1
    rw [← integral_finsetSum _ fun i _ ↦ hIx i]
    congr 1
    funext x
    rw [← Finset.sum_mul]
    congr 1
    calc ∑ i, x i * fderiv ℝ F x (e i) = fderiv ℝ F x (∑ i, x i • e i) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [map_smul, smul_eq_mul]
      _ = fderiv ℝ F x x := by rw [hx x]
  have hsumR : ∑ i, ∫ x, (x i * F x) * (qderiv H x (e i) / 2) * quadKernel H x =
      ∫ x, F x * qform H x * quadKernel H x := by
    rw [← integral_finsetSum _ fun i _ ↦ hIR i]
    congr 1
    funext x
    have hs := sum_coord_mul_qderiv H x
    simp only [he_def] at hs ⊢
    calc ∑ i, (x i * F x) * (qderiv H x (EuclideanSpace.single i (1 : ℝ)) / 2) * quadKernel H x
        = F x * quadKernel H x / 2 * ∑ i, x i * qderiv H x (EuclideanSpace.single i (1 : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          ring
      _ = F x * qform H x * quadKernel H x := by
          rw [hs]
          ring
  rw [← hsumL, ← hsumR]
  exact Finset.sum_congr rfl fun i _ ↦ (hstein i).symm

/-! ### The covariance identities -/

theorem hasPolynomialGrowth_qform (H : Matrix (Fin d) (Fin d) ℝ) :
    HasPolynomialGrowth (qform H) := by
  set A := Matrix.toEuclideanCLM (𝕜 := ℝ) H
  refine ⟨‖A‖, 2, norm_nonneg _, fun x ↦ ?_⟩
  unfold qform
  calc |inner ℝ x (A x)| ≤ ‖x‖ * ‖A x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := mul_le_mul_of_nonneg_left (A.le_opNorm x) (norm_nonneg _)
    _ ≤ ‖A‖ * (1 + ‖x‖ ^ 2) := by nlinarith [norm_nonneg x, norm_nonneg A]

theorem isHomogeneousOfDegree_two_qform (H : Matrix (Fin d) (Fin d) ℝ) :
    IsHomogeneousOfDegree 2 (qform H) := fun a x ↦ qform_smul H a x

/-- `∫ q e^{-q/2} = d ∫ e^{-q/2}`. -/
theorem integral_qform_mul_quadKernel {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) :
    ∫ x, qform H x * quadKernel H x = d * ∫ x, quadKernel H x := by
  have hd : ∀ v,
      HasPolynomialGrowth fun x : EuclidD d ↦ fderiv ℝ (fun _ : EuclidD d ↦ (1 : ℝ)) x v := by
    intro v
    have : (fun x : EuclidD d ↦ fderiv ℝ (fun _ : EuclidD d ↦ (1 : ℝ)) x v) = fun _ ↦ 0 := by
      funext x
      rw [fderiv_const_apply]
      rfl
    rw [this]
    exact hasPolynomialGrowth_const 0
  have h := integral_mul_qform_quadKernel hH (F := fun _ ↦ (1 : ℝ)) contDiff_const
    (hasPolynomialGrowth_const 1) hd
  simp only [one_mul, fderiv_const_apply, zero_apply, zero_mul, integral_zero, add_zero] at h
  exact h

/-- `∫ q² e^{-q/2} = (d + 2) d ∫ e^{-q/2}`. -/
theorem integral_qform_sq_mul_quadKernel {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) :
    ∫ x, qform H x * qform H x * quadKernel H x = (d + 2) * d * ∫ x, quadKernel H x := by
  have h := integral_mul_qform_quadKernel hH (F := qform H) (contDiff_qform H)
    (hasPolynomialGrowth_qform H) (fun v ↦ by
      have : (fun x : EuclidD d ↦ fderiv ℝ (qform H) x v) = fun x ↦ qderiv H x v := by
        funext x
        exact fderiv_qform_apply H x v
      rw [this]
      exact hasPolynomialGrowth_qderiv H v)
  have hE : (fun x ↦ fderiv ℝ (qform H) x x * quadKernel H x) =
      fun x ↦ 2 * (qform H x * quadKernel H x) := by
    funext x
    rw [fderiv_apply_self_of_isHomogeneous ((contDiff_qform H).differentiable (by simp))
      (isHomogeneousOfDegree_two_qform H)]
    push_cast
    ring
  rw [hE, integral_const_mul, integral_qform_mul_quadKernel hH] at h
  rw [h]
  ring

/-- **First radial covariance identity**: `Cov_γ[q, Q] = k E_γ[Q]` for `Q` smooth, homogeneous
of degree `k`, of polynomial growth with polynomially growing derivatives. -/
theorem gaussianCovariance_qform_of_isHomogeneous {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {Q : EuclidD d → ℝ} (hQ : ContDiff ℝ ∞ Q) {k : ℕ} (hhom : IsHomogeneousOfDegree k Q)
    (hQg : HasPolynomialGrowth Q) (hQ'g : ∀ v, HasPolynomialGrowth fun x ↦ fderiv ℝ Q x v) :
    gaussianCovariance H (qform H) Q = k * gaussianExpectation H Q := by
  have h1 := integral_mul_qform_quadKernel hH hQ hQg hQ'g
  have hE : (fun x ↦ fderiv ℝ Q x x * quadKernel H x) = fun x ↦ k * (Q x * quadKernel H x) := by
    funext x
    rw [fderiv_apply_self_of_isHomogeneous (hQ.differentiable (by simp)) hhom]
    ring
  rw [hE, integral_const_mul] at h1
  have h0 := integral_qform_mul_quadKernel hH
  have hZ := integral_quadKernel_pos hH
  unfold gaussianCovariance gaussianExpectation
  have hcomm : (∫ x, (fun x ↦ qform H x * Q x) x * quadKernel H x) =
      ∫ x, Q x * qform H x * quadKernel H x := by
    congr 1
    funext x
    ring
  rw [hcomm, h1, h0]
  field_simp
  ring

/-- **Second radial covariance identity**: `Cov_γ[q², Q] = k (k + 2d + 2) E_γ[Q]`. -/
theorem gaussianCovariance_qform_sq_of_isHomogeneous {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {Q : EuclidD d → ℝ} (hQ : ContDiff ℝ ∞ Q) {k : ℕ}
    (hhom : IsHomogeneousOfDegree k Q) (hQg : HasPolynomialGrowth Q)
    (hQ'g : ∀ v, HasPolynomialGrowth fun x ↦ fderiv ℝ Q x v) :
    gaussianCovariance H (fun x ↦ qform H x ^ 2) Q =
      k * (k + 2 * d + 2) * gaussianExpectation H Q := by
  set F : EuclidD d → ℝ := fun x ↦ Q x * qform H x with hF_def
  have hFs : ContDiff ℝ ∞ F := hQ.mul (contDiff_qform H)
  have hFg : HasPolynomialGrowth F := hQg.mul (hasPolynomialGrowth_qform H)
  have hQd : Differentiable ℝ Q := hQ.differentiable (by simp)
  have hFderiv : ∀ x v, fderiv ℝ F x v = Q x * qderiv H x v + qform H x * fderiv ℝ Q x v := by
    intro x v
    have hd : HasFDerivAt F _ x := (hQd x).hasFDerivAt.mul (hasFDerivAt_qform H x)
    rw [hd.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [← fderiv_qform_apply H x v, (hasFDerivAt_qform H x).fderiv]
  have hF'g : ∀ v, HasPolynomialGrowth fun x ↦ fderiv ℝ F x v := by
    intro v
    obtain ⟨C, n, hC, hb⟩ := (hQg.mul (hasPolynomialGrowth_qderiv H v)).add
      ((hasPolynomialGrowth_qform H).mul (hQ'g v))
    refine ⟨C, n, hC, fun x ↦ ?_⟩
    dsimp only
    rw [hFderiv x v]
    exact hb x
  -- Euler for `F`: `x·∇F = (k + 2) F`
  have hEuler : ∀ x, fderiv ℝ F x x = (k + 2) * F x := by
    intro x
    rw [hFderiv, ← fderiv_qform_apply H x x,
      fderiv_apply_self_of_isHomogeneous ((contDiff_qform H).differentiable (by simp))
        (isHomogeneousOfDegree_two_qform H),
      fderiv_apply_self_of_isHomogeneous hQd hhom]
    simp only [hF_def]
    push_cast
    ring
  have h1 := integral_mul_qform_quadKernel hH hFs hFg hF'g
  have hE : (fun x ↦ fderiv ℝ F x x * quadKernel H x) =
      fun x ↦ (k + 2) * (F x * quadKernel H x) := by
    funext x
    rw [hEuler x]
    ring
  rw [hE, integral_const_mul] at h1
  -- `∫ F K = (d + k) ∫ Q K`
  have h2 := integral_mul_qform_quadKernel hH hQ hQg hQ'g
  have hE2 : (fun x ↦ fderiv ℝ Q x x * quadKernel H x) = fun x ↦ k * (Q x * quadKernel H x) := by
    funext x
    rw [fderiv_apply_self_of_isHomogeneous hQd hhom]
    ring
  rw [hE2, integral_const_mul] at h2
  have hF_eq : (fun x ↦ F x * quadKernel H x) = fun x ↦ Q x * qform H x * quadKernel H x := rfl
  have hsq := integral_qform_sq_mul_quadKernel hH
  have hZ := integral_quadKernel_pos hH
  unfold gaussianCovariance gaussianExpectation
  have hcomm : (∫ x, (fun x ↦ qform H x ^ 2 * Q x) x * quadKernel H x) =
      ∫ x, F x * qform H x * quadKernel H x := by
    congr 1
    funext x
    simp only [hF_def]
    ring
  have hcomm2 : (∫ x, (fun x ↦ qform H x ^ 2) x * quadKernel H x) =
      ∫ x, qform H x * qform H x * quadKernel H x := by
    congr 1
    funext x
    ring
  rw [hcomm, hcomm2, h1, hF_eq, h2, hsq]
  field_simp
  ring

end Laplace.Multi
