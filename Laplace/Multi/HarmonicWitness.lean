/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.GaussianStein
import Laplace.Multi.SufficientFamilies

/-!
# Harmonic homogeneous polynomials: the real and imaginary parts of `(y₀ + i y₁)^k`

In `d ≥ 2` variables the functions `harmRe k y = Re (y₀ + i y₁)^k` and
`harmIm k y = Im (y₀ + i y₁)^k` are nonzero homogeneous polynomials of degree `k`
(members of `homogPolySpan d k`), smooth with polynomial growth, satisfying the recursion
`harmRe (k+1) = y₀ harmRe k − y₁ harmIm k`, `harmIm (k+1) = y₀ harmIm k + y₁ harmRe k` and the
Cauchy–Riemann derivative formulas
`∂_v harmRe (k+1) = (k+1) (harmRe k · v₀ − harmIm k · v₁)`,
`∂_v harmIm (k+1) = (k+1) (harmIm k · v₀ + harmRe k · v₁)`.
They are the witnesses for the directions of a degree-`k` jet invisible to all monomial
observables of degree `< k` (`MonomialVisibility`).
-/

open Real MeasureTheory Filter Topology
open scoped ContDiff

namespace Laplace.Multi

variable {d : ℕ}

/-- The first coordinate index. -/
def i0 (hd : 2 ≤ d) : Fin d := ⟨0, by omega⟩

/-- The second coordinate index. -/
def i1 (hd : 2 ≤ d) : Fin d := ⟨1, by omega⟩

theorem i0_ne_i1 (hd : 2 ≤ d) : i0 hd ≠ i1 hd := by
  intro h
  have := congrArg Fin.val h
  simp [i0, i1] at this

/-- The real-linear map `y ↦ y₀ + i y₁`. -/
noncomputable def zlin (hd : 2 ≤ d) : EuclidD d →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (i0 hd)) +
    Complex.I • Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (i1 hd))

theorem zlin_apply (hd : 2 ≤ d) (v : EuclidD d) :
    zlin hd v = (v (i0 hd) : ℂ) + Complex.I * (v (i1 hd) : ℂ) := by
  simp [zlin]

theorem zlin_re (hd : 2 ≤ d) (v : EuclidD d) : (zlin hd v).re = v (i0 hd) := by
  simp [zlin_apply]

theorem zlin_im (hd : 2 ≤ d) (v : EuclidD d) : (zlin hd v).im = v (i1 hd) := by
  simp [zlin_apply]

/-- `Re (y₀ + i y₁)^k`. -/
noncomputable def harmRe (hd : 2 ≤ d) (k : ℕ) (y : EuclidD d) : ℝ := (zlin hd y ^ k).re

/-- `Im (y₀ + i y₁)^k`. -/
noncomputable def harmIm (hd : 2 ≤ d) (k : ℕ) (y : EuclidD d) : ℝ := (zlin hd y ^ k).im

theorem harmRe_zero (hd : 2 ≤ d) (y : EuclidD d) : harmRe hd 0 y = 1 := by
  simp [harmRe]

theorem harmIm_zero (hd : 2 ≤ d) (y : EuclidD d) : harmIm hd 0 y = 0 := by
  simp [harmIm]

/-- The recursion for the real part. -/
theorem harmRe_succ (hd : 2 ≤ d) (k : ℕ) (y : EuclidD d) :
    harmRe hd (k + 1) y = y (i0 hd) * harmRe hd k y - y (i1 hd) * harmIm hd k y := by
  unfold harmRe harmIm
  rw [pow_succ', Complex.mul_re, zlin_re, zlin_im]

/-- The recursion for the imaginary part. -/
theorem harmIm_succ (hd : 2 ≤ d) (k : ℕ) (y : EuclidD d) :
    harmIm hd (k + 1) y = y (i0 hd) * harmIm hd k y + y (i1 hd) * harmRe hd k y := by
  unfold harmRe harmIm
  rw [pow_succ', Complex.mul_im, zlin_re, zlin_im]

/-! ### Smoothness, growth, derivatives -/

theorem contDiff_harmRe (hd : 2 ≤ d) (k : ℕ) : ContDiff ℝ ∞ (harmRe hd k) :=
  Complex.reCLM.contDiff.comp ((zlin hd).contDiff.pow k)

theorem contDiff_harmIm (hd : 2 ≤ d) (k : ℕ) : ContDiff ℝ ∞ (harmIm hd k) :=
  Complex.imCLM.contDiff.comp ((zlin hd).contDiff.pow k)

theorem hasPolynomialGrowth_harm (hd : 2 ≤ d) (k : ℕ) :
    HasPolynomialGrowth (harmRe hd k) ∧ HasPolynomialGrowth (harmIm hd k) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · have : harmRe hd 0 = fun _ ↦ (1 : ℝ) := funext (harmRe_zero hd)
      rw [this]
      exact hasPolynomialGrowth_const 1
    · have : harmIm hd 0 = fun _ ↦ (0 : ℝ) := funext (harmIm_zero hd)
      rw [this]
      exact hasPolynomialGrowth_const 0
  | succ k ih =>
    obtain ⟨hR, hI⟩ := ih
    refine ⟨?_, ?_⟩
    · have : harmRe hd (k + 1) =
          fun y ↦ y (i0 hd) * harmRe hd k y + (-1) * (y (i1 hd) * harmIm hd k y) := by
        funext y
        rw [harmRe_succ]
        ring
      rw [this]
      exact ((hasPolynomialGrowth_coord _).mul hR).add
        ((hasPolynomialGrowth_const (-1)).mul ((hasPolynomialGrowth_coord _).mul hI))
    · have : harmIm hd (k + 1) = fun y ↦ y (i0 hd) * harmIm hd k y + y (i1 hd) * harmRe hd k y := by
        funext y
        rw [harmIm_succ]
      rw [this]
      exact ((hasPolynomialGrowth_coord _).mul hI).add ((hasPolynomialGrowth_coord _).mul hR)

theorem hasFDerivAt_zpow (hd : 2 ≤ d) (k : ℕ) (y : EuclidD d) :
    HasFDerivAt (fun y ↦ zlin hd y ^ k) ((k • zlin hd y ^ (k - 1)) • zlin hd) y :=
  (zlin hd).hasFDerivAt.pow k

/-- Cauchy–Riemann for the real part. -/
theorem fderiv_harmRe_succ (hd : 2 ≤ d) (k : ℕ) (y v : EuclidD d) :
    fderiv ℝ (harmRe hd (k + 1)) y v =
      (k + 1) * (harmRe hd k y * v (i0 hd) - harmIm hd k y * v (i1 hd)) := by
  have h := (Complex.reCLM.hasFDerivAt.comp y (hasFDerivAt_zpow hd (k + 1) y))
  have hfun : (Complex.reCLM ∘ fun y ↦ zlin hd y ^ (k + 1)) = harmRe hd (k + 1) := by
    funext y
    simp [harmRe]
  rw [hfun] at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, Complex.reCLM_apply, Nat.add_sub_cancel,
    nsmul_eq_mul, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, zlin_re, zlin_im]
  unfold harmRe harmIm
  push_cast
  ring

/-- Cauchy–Riemann for the imaginary part. -/
theorem fderiv_harmIm_succ (hd : 2 ≤ d) (k : ℕ) (y v : EuclidD d) :
    fderiv ℝ (harmIm hd (k + 1)) y v =
      (k + 1) * (harmIm hd k y * v (i0 hd) + harmRe hd k y * v (i1 hd)) := by
  have h := (Complex.imCLM.hasFDerivAt.comp y (hasFDerivAt_zpow hd (k + 1) y))
  have hfun : (Complex.imCLM ∘ fun y ↦ zlin hd y ^ (k + 1)) = harmIm hd (k + 1) := by
    funext y
    simp [harmIm]
  rw [hfun] at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, Complex.imCLM_apply, Nat.add_sub_cancel,
    nsmul_eq_mul, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, zlin_re, zlin_im]
  unfold harmRe harmIm
  push_cast
  ring

theorem fderiv_harmRe_zero (hd : 2 ≤ d) (y v : EuclidD d) : fderiv ℝ (harmRe hd 0) y v = 0 := by
  have : harmRe hd 0 = fun _ ↦ (1 : ℝ) := funext (harmRe_zero hd)
  rw [this]
  simp

theorem fderiv_harmIm_zero (hd : 2 ≤ d) (y v : EuclidD d) : fderiv ℝ (harmIm hd 0) y v = 0 := by
  have : harmIm hd 0 = fun _ ↦ (0 : ℝ) := funext (harmIm_zero hd)
  rw [this]
  simp

/-- Directional derivatives of the harmonic functions have polynomial growth. -/
theorem hasPolynomialGrowth_fderiv_harm (hd : 2 ≤ d) (k : ℕ) (v : EuclidD d) :
    HasPolynomialGrowth (fun y ↦ fderiv ℝ (harmRe hd k) y v) ∧
      HasPolynomialGrowth (fun y ↦ fderiv ℝ (harmIm hd k) y v) := by
  cases k with
  | zero =>
    refine ⟨?_, ?_⟩
    · have : (fun y ↦ fderiv ℝ (harmRe hd 0) y v) = fun _ ↦ (0 : ℝ) := funext fun y ↦
        fderiv_harmRe_zero hd y v
      rw [this]
      exact hasPolynomialGrowth_const 0
    · have : (fun y ↦ fderiv ℝ (harmIm hd 0) y v) = fun _ ↦ (0 : ℝ) := funext fun y ↦
        fderiv_harmIm_zero hd y v
      rw [this]
      exact hasPolynomialGrowth_const 0
  | succ k =>
    obtain ⟨hR, hI⟩ := hasPolynomialGrowth_harm hd k
    refine ⟨?_, ?_⟩
    · have : (fun y ↦ fderiv ℝ (harmRe hd (k + 1)) y v) =
          fun y ↦ ((k : ℝ) + 1) *
            (harmRe hd k y * v (i0 hd) + (-1) * (harmIm hd k y * v (i1 hd))) := by
        funext y
        rw [fderiv_harmRe_succ]
        ring
      rw [this]
      exact (hasPolynomialGrowth_const _).mul ((hR.mul (hasPolynomialGrowth_const _)).add
        ((hasPolynomialGrowth_const (-1)).mul (hI.mul (hasPolynomialGrowth_const _))))
    · have : (fun y ↦ fderiv ℝ (harmIm hd (k + 1)) y v) =
          fun y ↦ ((k : ℝ) + 1) * (harmIm hd k y * v (i0 hd) + harmRe hd k y * v (i1 hd)) := by
        funext y
        rw [fderiv_harmIm_succ]
      rw [this]
      exact (hasPolynomialGrowth_const _).mul ((hI.mul (hasPolynomialGrowth_const _)).add
        (hR.mul (hasPolynomialGrowth_const _)))

/-! ### Membership in the homogeneous span and nonvanishing -/

/-- Multiplying a member of `homogPolySpan d k` by a coordinate lands in
`homogPolySpan d (k+1)`. -/
theorem coord_mul_mem_homogPolySpan {k : ℕ} (i : Fin d) {Q : EuclidD d → ℝ}
    (hQ : Q ∈ homogPolySpan d k) : (fun x ↦ x i * Q x) ∈ homogPolySpan d (k + 1) := by
  unfold homogPolySpan at hQ ⊢
  refine Submodule.span_induction (p := fun Q _ ↦ (fun x ↦ x i * Q x) ∈
      Submodule.span ℝ (Set.range (monomialTest : (Fin (k + 1) → Fin d) → EuclidD d → ℝ)))
    ?_ ?_ ?_ ?_ hQ
  · rintro _ ⟨m, rfl⟩
    refine Submodule.subset_span ⟨Fin.cons i m, ?_⟩
    funext x
    simp only [monomialTest, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  · have : (fun x : EuclidD d ↦ x i * (0 : EuclidD d → ℝ) x) = 0 := by
      funext x
      simp
    rw [this]
    exact Submodule.zero_mem _
  · intro P Q _ _ hP hQ'
    have : (fun x : EuclidD d ↦ x i * (P + Q) x) = (fun x ↦ x i * P x) + fun x ↦ x i * Q x := by
      funext x
      simp [mul_add]
    rw [this]
    exact Submodule.add_mem _ hP hQ'
  · intro c P _ hP
    have : (fun x : EuclidD d ↦ x i * (c • P) x) = c • fun x ↦ x i * P x := by
      funext x
      simp [mul_left_comm]
    rw [this]
    exact Submodule.smul_mem _ c hP

theorem harm_mem_homogPolySpan (hd : 2 ≤ d) (k : ℕ) :
    harmRe hd k ∈ homogPolySpan d k ∧ harmIm hd k ∈ homogPolySpan d k := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · have : harmRe hd 0 = monomialTest (Fin.elim0 : Fin 0 → Fin d) := by
        funext y
        simp [harmRe_zero, monomialTest]
      rw [this]
      exact monomialTest_mem_homogPolySpan _
    · have : harmIm hd 0 = 0 := funext (harmIm_zero hd)
      rw [this]
      exact Submodule.zero_mem _
  | succ k ih =>
    obtain ⟨hR, hI⟩ := ih
    refine ⟨?_, ?_⟩
    · have : harmRe hd (k + 1) =
          (fun y ↦ y (i0 hd) * harmRe hd k y) - fun y ↦ y (i1 hd) * harmIm hd k y := by
        funext y
        simp [harmRe_succ]
      rw [this]
      exact Submodule.sub_mem _ (coord_mul_mem_homogPolySpan _ hR)
        (coord_mul_mem_homogPolySpan _ hI)
    · have : harmIm hd (k + 1) =
          (fun y ↦ y (i0 hd) * harmIm hd k y) + fun y ↦ y (i1 hd) * harmRe hd k y := by
        funext y
        simp [harmIm_succ]
      rw [this]
      exact Submodule.add_mem _ (coord_mul_mem_homogPolySpan _ hI)
        (coord_mul_mem_homogPolySpan _ hR)

theorem harmRe_single (hd : 2 ≤ d) (k : ℕ) :
    harmRe hd k (EuclideanSpace.single (i0 hd) (1 : ℝ)) = 1 := by
  unfold harmRe
  rw [zlin_apply]
  simp [i0_ne_i1 hd]

theorem harmRe_ne_zero (hd : 2 ≤ d) (k : ℕ) : harmRe hd k ≠ 0 := by
  intro h
  have := congrFun h (EuclideanSpace.single (i0 hd) (1 : ℝ))
  rw [harmRe_single] at this
  simp at this

end Laplace.Multi
