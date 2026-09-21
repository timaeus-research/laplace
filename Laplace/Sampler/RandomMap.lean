/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Sampler.GaussianUniqueness

/-!
# The ULA update as a random map

`gaussStep A R μ = (μ.map A) ∗ N(0, R)` is the law of the output of one affine Gaussian step. Here
it is identified with the algorithm as implemented: the push-forward of `μ ⊗ N(0, I)` under the
sampling map `(w, ξ) ↦ A w + √(2h) ξ` (`ula_update_law`), and, for random variables `X` and `ξ`
that are independent with `ξ` standard Gaussian, the law of `A X + √(2h) ξ`
(`ula_update_law_of_indep`).
-/

open MeasureTheory ProbabilityTheory Matrix

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Scaling the standard Gaussian**: `c • ξ ~ N(0, c² I)` for every real `c`. -/
theorem stdGaussian_map_smul (c : ℝ) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun ξ => c • ξ) =
      multivariateGaussian 0 ((c ^ 2) • (1 : Matrix ι ι ℝ)) := by
  have hpsd : ((c ^ 2) • (1 : Matrix ι ι ℝ)).PosSemidef := Matrix.PosSemidef.one.smul (sq_nonneg c)
  apply Measure.ext_of_charFun
  funext t
  have hnorm : ‖t‖ ^ 2 = t.ofLp ⬝ᵥ t.ofLp := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [charFun_map_smul, charFun_stdGaussian, charFun_multivariateGaussian hpsd]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, smul_mulVec, one_mulVec,
    dotProduct_smul, smul_eq_mul]
  congr 1
  rw [← Complex.ofReal_pow, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hnorm]
  push_cast
  ring

omit [DecidableEq ι] in
set_option linter.unusedFintypeInType false in
/-- **The sampling-map form of a convolution**: `(μ ⊗ ν).map ((x, ξ) ↦ L x + ξ) = (μ.map L) ∗ ν`. -/
theorem map_add_prod (μ ν : Measure (EuclideanSpace ℝ ι)) [SFinite μ] [SFinite ν]
    (L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    (μ.prod ν).map (fun p => L p.1 + p.2) = (μ.map L) ∗ ν := by
  change _ = ((μ.map L).prod ν).map (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => p.1 + p.2)
  conv_rhs => rw [← Measure.map_id (μ := ν)]
  rw [Measure.map_prod_map _ _ L.continuous.measurable measurable_id,
    Measure.map_map (g := fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => p.1 + p.2)
      (f := Prod.map L id) (measurable_fst.add measurable_snd)
      (L.continuous.measurable.prodMap measurable_id)]
  rfl

/-- The affine Gaussian step as a sampling map with `N(0, R)` noise. -/
theorem gaussStep_eq_map_prod (μ : Measure (EuclideanSpace ℝ ι)) [SFinite μ] (A R : Matrix ι ι ℝ) :
    (μ.prod (multivariateGaussian 0 R)).map (fun p => euclid A p.1 + p.2) = gaussStep A R μ :=
  map_add_prod μ _ (euclid A)

/-- **The ULA update as a random map.** The push-forward of `μ ⊗ N(0, I)` under
`(w, ξ) ↦ A w + √(2h) ξ` is `gaussStep A (2h I) μ`. -/
theorem ula_update_law (μ : Measure (EuclideanSpace ℝ ι)) [SFinite μ] (A : Matrix ι ι ℝ) {h : ℝ}
    (hh : 0 ≤ h) :
    (μ.prod (stdGaussian (EuclideanSpace ℝ ι))).map
        (fun p => euclid A p.1 + Real.sqrt (2 * h) • p.2) =
      gaussStep A ((2 * h) • (1 : Matrix ι ι ℝ)) μ := by
  have hs : Measurable (fun ξ : EuclideanSpace ℝ ι => Real.sqrt (2 * h) • ξ) :=
    measurable_const_smul _
  have h1 : (μ.prod (stdGaussian (EuclideanSpace ℝ ι))).map
      (fun p => euclid A p.1 + Real.sqrt (2 * h) • p.2) =
      ((μ.prod (stdGaussian (EuclideanSpace ℝ ι))).map
        (Prod.map id (fun ξ => Real.sqrt (2 * h) • ξ))).map (fun p => euclid A p.1 + p.2) := by
    rw [Measure.map_map
      (g := fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => euclid A p.1 + p.2)
      (f := Prod.map id fun ξ : EuclideanSpace ℝ ι => Real.sqrt (2 * h) • ξ)
      ((euclid A).continuous.measurable.comp measurable_fst |>.add measurable_snd)
      (measurable_id.prodMap hs)]
    rfl
  rw [h1, ← Measure.map_prod_map _ _ measurable_id hs, Measure.map_id, stdGaussian_map_smul,
    Real.sq_sqrt (by positivity), gaussStep_eq_map_prod]

/-- **The ULA update on random variables.** If `X` and `ξ` are independent with `ξ` standard
Gaussian, the law of `A X + √(2h) ξ` is `gaussStep A (2h I)` applied to the law of `X`. -/
theorem ula_update_law_of_indep {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X ξ : Ω → EuclideanSpace ℝ ι) (hX : AEMeasurable X P)
    (hξ : AEMeasurable ξ P) (hind : IndepFun X ξ P)
    (hξlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ ι)) (A : Matrix ι ι ℝ) {h : ℝ} (hh : 0 ≤ h) :
    P.map (fun ω => euclid A (X ω) + Real.sqrt (2 * h) • ξ ω) =
      gaussStep A ((2 * h) • (1 : Matrix ι ι ℝ)) (P.map X) := by
  have hF : Measurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      euclid A p.1 + Real.sqrt (2 * h) • p.2) :=
    ((euclid A).continuous.measurable.comp measurable_fst).add
      ((measurable_const_smul _).comp measurable_snd)
  rw [← ula_update_law (P.map X) A hh, ← hξlaw,
    ← (indepFun_iff_map_prod_eq_prod_map_map hX hξ).mp hind,
    AEMeasurable.map_map_of_aemeasurable hF.aemeasurable (hX.prodMk hξ)]
  rfl

end Laplace.Sampler
