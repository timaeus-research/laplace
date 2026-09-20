/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.SufficientFamilies

/-!
# Stable recovery of the visible component

`SufficientFamilies` shows that a family of observables sees the degree-`k`
Taylor difference `Q_k` of two losses exactly through the observation
operator `T_S : Q ↦ (Cov_γ[φ_i, Q])_i` on the degree-`k` homogeneous
polynomials, and that the data determine `Q_k` only modulo `ker T_S`. Here
the recovery of the visible component is made quantitative. The Gaussian
covariance `Cov_γ` is an inner product on `homogPolySpan d k` (bilinear,
symmetric, and positive definite by the rigidity theorem), so the span is a
finite-dimensional normed space with `‖Q‖_γ = √Cov_γ[Q, Q]`; the observation
operator, restricted to a complement of its kernel, is injective between
finite-dimensional normed spaces and therefore bounded below. The result
(`exists_stable_recovery`): there is `C > 0` such that every `Q ∈ H_k` can be
corrected by a kernel element `R` with

  `√Cov_γ[Q - R, Q - R] ≤ C · ‖(Cov_γ[φ_i, Q])_i‖`.

Noisy leading coefficients thus recover the visible component stably, in
the covariance norm, with a constant depending only on the family and `H`.
-/

open Asymptotics Filter MeasureTheory RCLike

namespace Laplace.Multi

variable {d k : ℕ}

/-- The self-covariance is nonnegative. -/
theorem gaussianCovariance_self_nonneg {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {Q : EuclidD d → ℝ} (hQc : Continuous Q) (hQg : HasPolynomialGrowth Q) :
    0 ≤ gaussianCovariance H Q Q := by
  have h := gaussianCovariance_self_eq hH hQc.aestronglyMeasurable hQg
  have hZ := integral_quadKernel_pos hH
  have hI : 0 ≤ ∫ x : EuclidD d, (Q x - gaussianExpectation H Q) ^ 2 * quadKernel H x :=
    integral_nonneg fun x ↦ mul_nonneg (sq_nonneg _) (quadKernel_pos H x).le
  rw [h] at hI
  exact (mul_nonneg_iff_of_pos_left hZ).mp hI

/-- **The covariance inner product** on the degree-`k` homogeneous polynomials. -/
@[instance_reducible]
noncomputable def covCore {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (hk : 0 < k) :
    InnerProductSpace.Core ℝ (homogPolySpan d k) where
  inner P Q := gaussianCovariance H P Q
  conj_inner_symm x y := by
    simp only [conj_trivial]
    exact gaussianCovariance_comm _ _
  re_inner_nonneg x := by
    simp only [re_to_real]
    exact gaussianCovariance_self_nonneg hH (homogPolySpan_continuous x.2)
      (homogPolySpan_hasPolynomialGrowth x.2)
  add_left x y z := by
    simp only [Submodule.coe_add]
    rw [gaussianCovariance_comm, gaussianCovariance_add_right hH (homogPolySpan_continuous z.2)
      (homogPolySpan_hasPolynomialGrowth z.2) (homogPolySpan_continuous x.2)
      (homogPolySpan_hasPolynomialGrowth x.2) (homogPolySpan_continuous y.2)
      (homogPolySpan_hasPolynomialGrowth y.2), gaussianCovariance_comm (z : EuclidD d → ℝ) x,
      gaussianCovariance_comm (z : EuclidD d → ℝ) y]
  smul_left x y r := by
    simp only [Submodule.coe_smul, conj_trivial]
    rw [gaussianCovariance_comm, gaussianCovariance_const_smul_right,
      gaussianCovariance_comm (y : EuclidD d → ℝ) x]
  definite x hx := by
    have h0 : (x : EuclidD d → ℝ) = 0 :=
      homogeneous_eq_zero_of_gaussianCovariance_self_eq_zero hH hk (homogPolySpan_continuous x.2)
        (homogPolySpan_hasPolynomialGrowth x.2) (homogPolySpan_isHomogeneous x.2) hx
    exact Submodule.coe_eq_zero.mp h0

/-- **Stable recovery of the visible component, orthogonal form.** For a finite
family of continuous polynomially growing tests there is `C > 0` such that every
degree-`k` homogeneous polynomial `Q` splits as `Q = R + (Q - R)` with `R` in the
kernel of the observation operator (all pairings with the family vanish), `Q - R`
covariance-orthogonal to that kernel (the visible component), and
`√Cov_γ[Q - R, Q - R] ≤ C · ‖(Cov_γ[φ_i, Q])_i‖`. -/
theorem exists_stable_recovery_orthogonal {ι : Type*} [Fintype ι]
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) (hk : 0 < k) (φ : ι → EuclidD d → ℝ)
    (hφc : ∀ i, Continuous (φ i)) (hφg : ∀ i, HasPolynomialGrowth (φ i)) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q ∈ homogPolySpan d k, ∃ R ∈ homogPolySpan d k,
      (∀ i, gaussianCovariance H (φ i) R = 0) ∧
      (∀ P ∈ homogPolySpan d k, (∀ i, gaussianCovariance H (φ i) P = 0) →
        gaussianCovariance H P (fun x ↦ Q x - R x) = 0) ∧
      Real.sqrt (gaussianCovariance H (fun x ↦ Q x - R x) (fun x ↦ Q x - R x)) ≤
        C * ‖fun i ↦ gaussianCovariance H (φ i) Q‖ := by
  classical
  let core : InnerProductSpace.Core ℝ (homogPolySpan d k) := covCore hH hk
  let _ : NormedAddCommGroup (homogPolySpan d k) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let _ : UniformSpace (homogPolySpan d k) := PseudoMetricSpace.toUniformSpace
  let _ : TopologicalSpace (homogPolySpan d k) := UniformSpace.toTopologicalSpace
  let _ : InnerProductSpace ℝ (homogPolySpan d k) := InnerProductSpace.ofCore core.toCore
  have : FiniteDimensional ℝ (homogPolySpan d k) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  set T : homogPolySpan d k →ₗ[ℝ] (ι → ℝ) := pairingMap (k := k) hH φ hφc hφg with hT_def
  set K : Submodule ℝ (homogPolySpan d k) := LinearMap.ker T with hK_def
  have : CompleteSpace K := FiniteDimensional.complete ℝ K
  have hW : IsCompl K Kᗮ := K.isCompl_orthogonal
  -- the restriction of `T` to the orthogonal complement is injective
  set T' : Kᗮ →ₗ[ℝ] (ι → ℝ) := T.domRestrict Kᗮ with hT'_def
  have hker : LinearMap.ker T' = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h1 : (x : homogPolySpan d k) ∈ K := LinearMap.mem_ker.mpr hx
    have h2 : (x : homogPolySpan d k) ∈ K ⊓ Kᗮ := ⟨h1, x.2⟩
    rw [hW.inf_eq_bot, Submodule.mem_bot] at h2
    exact Subtype.ext h2
  obtain ⟨C, hC, hanti⟩ := T'.exists_antilipschitzWith hker
  refine ⟨(C : ℝ), by exact_mod_cast hC, fun Q hQ ↦ ?_⟩
  -- decompose `Q = r + w` with `r ∈ K`, `w ∈ Kᗮ`
  obtain ⟨r, hr, w, hw, hrw⟩ := K.exists_add_mem_mem_orthogonal (⟨Q, hQ⟩ : homogPolySpan d k)
  have hwQ : w = (⟨Q, hQ⟩ : homogPolySpan d k) - r := eq_sub_of_add_eq' hrw.symm
  refine ⟨(r : EuclidD d → ℝ), r.2, ?_, ?_, ?_⟩
  · intro i
    exact congrFun (LinearMap.mem_ker.mp hr) i
  · intro P hP hPker
    have hPK : (⟨P, hP⟩ : homogPolySpan d k) ∈ K := LinearMap.mem_ker.mpr (funext hPker)
    have h := Submodule.inner_right_of_mem_orthogonal hPK hw
    change gaussianCovariance H P (w : EuclidD d → ℝ) = 0 at h
    rw [hwQ] at h
    exact h
  · have hTw : T w = T ⟨Q, hQ⟩ := by
      rw [hwQ, map_sub, LinearMap.mem_ker.mp hr, sub_zero]
    have hdist := hanti.le_mul_dist ⟨w, hw⟩ 0
    rw [dist_zero_right, map_zero, dist_zero_right] at hdist
    have hnorm : ‖(⟨w, hw⟩ : Kᗮ)‖ = Real.sqrt (gaussianCovariance H
        (fun x ↦ Q x - (r : EuclidD d → ℝ) x) (fun x ↦ Q x - (r : EuclidD d → ℝ) x)) := by
      rw [Submodule.coe_norm, InnerProductSpace.Core.norm_eq_sqrt_re_inner]
      change Real.sqrt (gaussianCovariance H (w : EuclidD d → ℝ) w) = _
      rw [hwQ]
      rfl
    have hT' : T' ⟨w, hw⟩ = fun i ↦ gaussianCovariance H (φ i) Q := by
      change T w = _
      rw [hTw]
      rfl
    rw [hnorm, hT'] at hdist
    exact hdist

/-- **Stable recovery of the visible component.** For a finite family of
continuous polynomially growing tests there is `C > 0` such that every
degree-`k` homogeneous polynomial `Q` admits a kernel correction `R` (all
pairings with the family vanish) with
`√Cov_γ[Q - R, Q - R] ≤ C · ‖(Cov_γ[φ_i, Q])_i‖`. -/
theorem exists_stable_recovery {ι : Type*} [Fintype ι] {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) (hk : 0 < k) (φ : ι → EuclidD d → ℝ)
    (hφc : ∀ i, Continuous (φ i)) (hφg : ∀ i, HasPolynomialGrowth (φ i)) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q ∈ homogPolySpan d k, ∃ R ∈ homogPolySpan d k,
      (∀ i, gaussianCovariance H (φ i) R = 0) ∧
      Real.sqrt (gaussianCovariance H (fun x ↦ Q x - R x) (fun x ↦ Q x - R x)) ≤
        C * ‖fun i ↦ gaussianCovariance H (φ i) Q‖ := by
  obtain ⟨C, hC, h⟩ := exists_stable_recovery_orthogonal hH hk φ hφc hφg
  refine ⟨C, hC, fun Q hQ ↦ ?_⟩
  obtain ⟨R, hR, h1, -, h3⟩ := h Q hQ
  exact ⟨R, hR, h1, h3⟩

/-- **Stability under perturbation of the data.** Two degree-`k` polynomials
whose pairings with the family differ by `η` in norm have visible components
within `C η` in covariance norm: apply `exists_stable_recovery` to `Q - Q'`.
Read with `Q'` the polynomial reconstructed from noisy leading coefficients. -/
theorem exists_stable_recovery_sub {ι : Type*} [Fintype ι] {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) (hk : 0 < k) (φ : ι → EuclidD d → ℝ)
    (hφc : ∀ i, Continuous (φ i)) (hφg : ∀ i, HasPolynomialGrowth (φ i)) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q ∈ homogPolySpan d k, ∀ Q' ∈ homogPolySpan d k,
      ∃ R ∈ homogPolySpan d k, (∀ i, gaussianCovariance H (φ i) R = 0) ∧
      Real.sqrt (gaussianCovariance H (fun x ↦ Q x - Q' x - R x) (fun x ↦ Q x - Q' x - R x)) ≤
        C * ‖(fun i ↦ gaussianCovariance H (φ i) Q) - fun i ↦ gaussianCovariance H (φ i) Q'‖ := by
  obtain ⟨C, hC, h⟩ := exists_stable_recovery hH hk φ hφc hφg
  refine ⟨C, hC, fun Q hQ Q' hQ' ↦ ?_⟩
  obtain ⟨R, hR, h1, h2⟩ := h (Q - Q') (Submodule.sub_mem _ hQ hQ')
  refine ⟨R, hR, h1, ?_⟩
  have hlin : (fun i ↦ gaussianCovariance H (φ i) (Q - Q')) =
      (fun i ↦ gaussianCovariance H (φ i) Q) - fun i ↦ gaussianCovariance H (φ i) Q' :=
    map_sub (pairingMap (k := k) hH φ hφc hφg) ⟨Q, hQ⟩ ⟨Q', hQ'⟩
  rw [← hlin]
  exact h2

end Laplace.Multi
