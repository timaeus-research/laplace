/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.StdGaussian

/-!
# The quadratic form and the whitening map

Stage H2b of the multivariate programme, first installment: the
public quadratic form `qform H x = ⟪x, H·x⟫` and its Gaussian kernel
`quadKernel H x = e^(-qform H x / 2)`, the whitening map
`B = toEuclideanCLM (CFC.sqrt H)`, the forward identity
`qform H x = ‖B x‖²` (never inverting inside the form), and the
nonvanishing of `LinearMap.det B` — kept opaque per the shape
consult: it cancels in the normalized second moment and only its
positivity feeds the partition value.
-/

open Real MeasureTheory Matrix
open scoped MatrixOrder

namespace Laplace.Multi

variable {d : ℕ}

/-- The quadratic form `⟪x, H·x⟫` of a matrix on Euclidean space. -/
noncomputable def qform (H : Matrix (Fin d) (Fin d) ℝ)
    (x : EuclidD d) : ℝ :=
  inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) H x)

/-- The Gaussian kernel of a quadratic form. -/
noncomputable def quadKernel (H : Matrix (Fin d) (Fin d) ℝ)
    (x : EuclidD d) : ℝ :=
  Real.exp (-qform H x / 2)

theorem quadKernel_pos (H : Matrix (Fin d) (Fin d) ℝ) (x : EuclidD d) :
    0 < quadKernel H x :=
  Real.exp_pos _

theorem qform_continuous (H : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (qform H) :=
  continuous_id.inner (Matrix.toEuclideanCLM (𝕜 := ℝ) H).continuous

theorem quadKernel_continuous (H : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (quadKernel H) :=
  Real.continuous_exp.comp ((qform_continuous H).neg.div_const 2)

/-- The coordinate bridge: `qform` as a matrix dot product. -/
theorem qform_eq_dotProduct (H : Matrix (Fin d) (Fin d) ℝ)
    (x : EuclidD d) :
    qform H x = WithLp.ofLp x ⬝ᵥ H *ᵥ WithLp.ofLp x :=
  Matrix.inner_toEuclideanCLM H x x

/-- The whitening map `B = √H` as a continuous linear endomorphism. -/
noncomputable def whitening (H : Matrix (Fin d) (Fin d) ℝ) :
    EuclidD d →L[ℝ] EuclidD d :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt H)

/-- The square root of a positive-definite matrix is positive
definite. -/
theorem sqrt_posDef {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) :
    (CFC.sqrt H).PosDef :=
  Matrix.isStrictlyPositive_iff_posDef.mp hH.isStrictlyPositive.sqrt

/-- The square root squares back to the matrix. -/
theorem sqrt_mul_sqrt {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) :
    CFC.sqrt H * CFC.sqrt H = H :=
  CFC.sqrt_mul_sqrt_self H (ha := hH.posSemidef.nonneg)

/-- The whitening map is self-adjoint. -/
theorem whitening_adjoint {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) :
    ContinuousLinearMap.adjoint (whitening H) = whitening H := by
  have hstar : Matrix.toEuclideanCLM (𝕜 := ℝ) (star (CFC.sqrt H)) =
      star (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt H)) :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ)).map_star' (CFC.sqrt H)
  unfold whitening
  rw [← ContinuousLinearMap.star_eq_adjoint, ← hstar,
    Matrix.star_eq_conjTranspose, (sqrt_posDef hH).isHermitian]

/-- **The forward whitening identity**: `qform H x = ‖B x‖²`. -/
theorem qform_eq_norm_sq_whitening {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) (x : EuclidD d) :
    qform H x = ‖whitening H x‖ ^ 2 := by
  have hcomp : Matrix.toEuclideanCLM (𝕜 := ℝ) H =
      whitening H * whitening H := by
    unfold whitening
    rw [← map_mul, sqrt_mul_sqrt hH]
  unfold qform
  rw [hcomp, ContinuousLinearMap.mul_apply,
    ← ContinuousLinearMap.adjoint_inner_left (whitening H),
    whitening_adjoint hH, real_inner_self_eq_norm_sq]

/-- The kernel in whitened form. -/
theorem quadKernel_eq_stdKernel_whitening
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (x : EuclidD d) :
    quadKernel H x = stdKernel (whitening H x) := by
  unfold quadKernel stdKernel
  rw [qform_eq_norm_sq_whitening hH]

/-- The whitening map is injective. -/
theorem whitening_injective {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) : Function.Injective (whitening H) := by
  have hker : ∀ x : EuclidD d, whitening H x = 0 → x = 0 := by
    intro x hx
    by_contra hx0
    have hq : inner ℝ x (whitening H x) = 0 := by
      rw [hx, inner_zero_right]
    have hpos : 0 < WithLp.ofLp x ⬝ᵥ CFC.sqrt H *ᵥ WithLp.ofLp x := by
      have hnz : WithLp.ofLp x ≠ 0 := by simpa using hx0
      have := (sqrt_posDef hH).re_dotProduct_pos hnz
      simpa using this
    rw [show inner ℝ x (whitening H x) =
        WithLp.ofLp x ⬝ᵥ CFC.sqrt H *ᵥ WithLp.ofLp x from
      Matrix.inner_toEuclideanCLM _ x x] at hq
    exact absurd hq hpos.ne'
  intro a b hab
  have : whitening H (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  simpa [sub_eq_zero] using hker _ this

/-- **The whitening Jacobian is nonvanishing** (kept opaque: only
this fact, never the determinant's value, enters the programme). -/
theorem whitening_det_ne_zero {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) :
    LinearMap.det ((whitening H : EuclidD d →L[ℝ] EuclidD d) :
      EuclidD d →ₗ[ℝ] EuclidD d) ≠ 0 := by
  have h1 : IsUnit ((whitening H : EuclidD d →L[ℝ] EuclidD d) :
      EuclidD d →ₗ[ℝ] EuclidD d) := by
    rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot]
    exact whitening_injective hH
  exact IsUnit.ne_zero ((LinearMap.isUnit_iff_isUnit_det _).mp h1)

end Laplace.Multi
