/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.GaussianMomentsPosDef
import Laplace.Sampler.ULA

/-!
# Metropolis–Hastings with Langevin proposals on a Gaussian target

The Sanity on Sampling note uses the Metropolis-adjusted Langevin algorithm (MALA) and its
`P⁻¹`-preconditioned version (pMALA) as reference samplers: "both have the exact stationary law",
and "the Metropolis-corrected MALA lands on `P⁻¹`" where ULA lands on `(P - (h/2) P²)⁻¹`
(`ulaCov_invariant`). This file formalises that claim.

* **General Metropolis–Hastings** on a σ-finite reference space, with unnormalised target and
  proposal densities `π, q > 0`: the accepted flux is `π(x) q(x,y) α(x,y) = min (π(x) q(x,y))
  (π(y) q(y,x))`, symmetric in `(x, y)` (`mul_mhAccept_eq_min`), and the target is invariant under
  the kernel `K(x, E) = Z⁻¹ ∫_E q(x,y) α(x,y) dy + (1 - a(x)) 1_E(x)` (`mh_invariant`), with no
  integrability hypotheses beyond a common row integral `∫ q(x, ·) = Z ∈ (0, ∞)`.
* **Gaussian proposals with symmetric drift**: for `π(x) = exp(-½ xᵀ P x)` and
  `q(x,y) = exp(-(y - A x)ᵀ S (y - A x))` with `Sᵀ = S`, `(S A)ᵀ = S A`, the acceptance ratio is
  `exp(yᵀ G y - xᵀ G x)` with `G = S - Aᵀ S A - P/2` (`targetWeight_propWeight_ratio`).
* **MALA** (`A = 1 - h P`, `S = 1/(4h)`): `G = -(h/4) P²`, ratio `exp(-(h/4)(‖P y‖² - ‖P x‖²))`;
  **pMALA** (`A = (1 - h) 1`, `S = P/(4h)`): `G = -(h/4) P`, ratio `exp(-(h/4)(yᵀ P y - xᵀ P x))`.
* **The exact stationary law**: the Gaussian density with precision `P` is invariant under the MALA
  and pMALA kernels for every `h > 0` (`mala_invariant`, `pmala_invariant`), and so is its
  normalisation, a probability measure (`mala_invariant_prob`).

The invariance is stated at the level of the density `exp(-½ xᵀ P x)` on `ι → ℝ` with Lebesgue
measure; its identification with Mathlib's `multivariateGaussian 0 P⁻¹` is left as a follow-up.
-/

open MeasureTheory ENNReal Matrix Set

namespace Laplace.Sampler

/-! ### A. Metropolis–Hastings on a σ-finite reference space -/

section MHAlgebra

variable {X : Type*} (π : X → ℝ) (q : X → X → ℝ)

/-- The Metropolis–Hastings acceptance probability `min 1 (π(y) q(y,x) / (π(x) q(x,y)))`. -/
noncomputable def mhAccept (x y : X) : ℝ := min 1 (π y * q y x / (π x * q x y))

/-- The accepted flux `min (π(x) q(x,y)) (π(y) q(y,x))`, symmetric in `(x, y)`. -/
noncomputable def mhFlux (x y : X) : ℝ≥0∞ := ENNReal.ofReal (min (π x * q x y) (π y * q y x))

variable {π q}

theorem mhAccept_le_one (x y : X) : mhAccept π q x y ≤ 1 := min_le_left _ _

theorem mhAccept_nonneg (hπ : ∀ x, 0 < π x) (hq : ∀ x y, 0 < q x y) (x y : X) :
    0 ≤ mhAccept π q x y :=
  le_min zero_le_one (div_nonneg (mul_pos (hπ y) (hq y x)).le (mul_pos (hπ x) (hq x y)).le)

/-- **Detailed balance at the level of densities**:
`π(x) q(x,y) α(x,y) = min (π(x) q(x,y)) (π(y) q(y,x))`. -/
theorem mul_mhAccept_eq_min (hπ : ∀ x, 0 < π x) (hq : ∀ x y, 0 < q x y) (x y : X) :
    π x * q x y * mhAccept π q x y = min (π x * q x y) (π y * q y x) := by
  have hpos : 0 < π x * q x y := mul_pos (hπ x) (hq x y)
  unfold mhAccept
  rw [mul_min_of_nonneg _ _ hpos.le, mul_one, mul_div_cancel₀ _ hpos.ne']

/-- **Detailed balance**: `π(x) q(x,y) α(x,y) = π(y) q(y,x) α(y,x)`. -/
theorem mh_detailed_balance (hπ : ∀ x, 0 < π x) (hq : ∀ x y, 0 < q x y) (x y : X) :
    π x * q x y * mhAccept π q x y = π y * q y x * mhAccept π q y x := by
  rw [mul_mhAccept_eq_min hπ hq, mul_mhAccept_eq_min hπ hq, min_comm]

theorem mhFlux_comm (x y : X) : mhFlux π q x y = mhFlux π q y x := by
  unfold mhFlux
  rw [min_comm]

theorem mhFlux_eq (hπ : ∀ x, 0 < π x) (hq : ∀ x y, 0 < q x y) (x y : X) :
    mhFlux π q x y = ENNReal.ofReal (π x) * ENNReal.ofReal (q x y * mhAccept π q x y) := by
  unfold mhFlux
  rw [← mul_mhAccept_eq_min hπ hq, mul_assoc, ENNReal.ofReal_mul (hπ x).le]

end MHAlgebra

section MH

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
variable (π : X → ℝ) (q : X → X → ℝ)

/-- The accepted mass `a(x) = Z⁻¹ ∫ q(x,y) α(x,y) dy`. -/
noncomputable def mhAcceptMass (μ : Measure X) (Z : ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  (∫⁻ y, ENNReal.ofReal (q x y * mhAccept π q x y) ∂μ) / Z

/-- The Metropolis–Hastings kernel on a set: the accepted moves into `E` plus the rejection mass at
`x` when `x ∈ E`. -/
noncomputable def mhKernelSet (μ : Measure X) (Z : ℝ≥0∞) (x : X) (E : Set X) : ℝ≥0∞ :=
  (∫⁻ y in E, ENNReal.ofReal (q x y * mhAccept π q x y) ∂μ) / Z +
    E.indicator (fun x => 1 - mhAcceptMass π q μ Z x) x

variable {π q}

theorem measurable_mhAccept (hπm : Measurable π) (hqm : Measurable (Function.uncurry q)) :
    Measurable (Function.uncurry (mhAccept π q)) := by
  have h1 : Measurable fun p : X × X => q p.1 p.2 := hqm
  have h2 : Measurable fun p : X × X => q p.2 p.1 := hqm.comp measurable_swap
  exact measurable_const.min
    (((hπm.comp measurable_snd).mul h2).div ((hπm.comp measurable_fst).mul h1))

theorem measurable_mhWeight (hπm : Measurable π) (hqm : Measurable (Function.uncurry q)) :
    Measurable (Function.uncurry fun x y => ENNReal.ofReal (q x y * mhAccept π q x y)) :=
  ENNReal.measurable_ofReal.comp (hqm.mul (measurable_mhAccept hπm hqm))

theorem measurable_mhFlux (hπm : Measurable π) (hqm : Measurable (Function.uncurry q)) :
    Measurable (Function.uncurry (mhFlux π q)) := by
  have h2 : Measurable fun p : X × X => q p.2 p.1 := hqm.comp measurable_swap
  exact ENNReal.measurable_ofReal.comp
    (((hπm.comp measurable_fst).mul hqm).min ((hπm.comp measurable_snd).mul h2))

omit [SFinite μ] in
theorem mhAcceptMass_le_one (hq : ∀ x y, 0 < q x y) {Z : ℝ≥0∞}
    (hZ : ∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂μ = Z) (hZ0 : Z ≠ 0) (hZtop : Z ≠ ∞) (x : X) :
    mhAcceptMass π q μ Z x ≤ 1 := by
  unfold mhAcceptMass
  rw [ENNReal.div_le_iff hZ0 hZtop, one_mul, ← hZ x]
  refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
  exact mul_le_of_le_one_right (hq x y).le (mhAccept_le_one x y)

theorem measurable_mhKernelSet (hπm : Measurable π) (hqm : Measurable (Function.uncurry q))
    (Z : ℝ≥0∞) {E : Set X} (hE : MeasurableSet E) :
    Measurable fun x => mhKernelSet π q μ Z x E := by
  have hwm := measurable_mhWeight (π := π) (q := q) hπm hqm
  exact ((hwm.lintegral_prod_right (ν := μ.restrict E)).div_const Z).add
    ((measurable_const.sub (hwm.lintegral_prod_right.div_const Z)).indicator hE)

/-- **Metropolis–Hastings invariance (setwise).** For measurable `π, q > 0` with a common row
integral `∫ q(x, ·) = Z ∈ (0, ∞)`, the target `π` is invariant under the MH kernel:
`∫ π(x) K(x, E) dx = ∫_E π`. -/
theorem mh_invariant (hπm : Measurable π) (hπ : ∀ x, 0 < π x)
    (hqm : Measurable (Function.uncurry q)) (hq : ∀ x y, 0 < q x y) {Z : ℝ≥0∞}
    (hZ : ∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂μ = Z) (hZ0 : Z ≠ 0) (hZtop : Z ≠ ∞) {E : Set X}
    (hE : MeasurableSet E) :
    ∫⁻ x, ENNReal.ofReal (π x) * mhKernelSet π q μ Z x E ∂μ =
      ∫⁻ x in E, ENNReal.ofReal (π x) ∂μ := by
  set w : X → X → ℝ≥0∞ := fun x y => ENNReal.ofReal (q x y * mhAccept π q x y) with hw
  have hwm : Measurable (Function.uncurry w) := measurable_mhWeight hπm hqm
  have hFm : Measurable (Function.uncurry (mhFlux π q)) := measurable_mhFlux hπm hqm
  have hF : ∀ x y, ENNReal.ofReal (π x) * w x y = mhFlux π q x y := fun x y =>
    (mhFlux_eq hπ hq x y).symm
  have hZinv : Z⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hZ0
  have hπm' : Measurable fun x => ENNReal.ofReal (π x) := ENNReal.measurable_ofReal.comp hπm
  have hbm : Measurable fun x => ∫⁻ y, w x y ∂μ := hwm.lintegral_prod_right
  have hbEm : Measurable fun x => ∫⁻ y in E, w x y ∂μ := hwm.lintegral_prod_right
  have hmeas1 : Measurable fun x => ENNReal.ofReal (π x) * ((∫⁻ y in E, w x y ∂μ) / Z) :=
    hπm'.mul (hbEm.div_const Z)
  have hmeasA : Measurable fun x => ENNReal.ofReal (π x) * mhAcceptMass π q μ Z x :=
    hπm'.mul (hbm.div_const Z)
  simp only [mhKernelSet, mul_add]
  rw [lintegral_add_left hmeas1]
  have h1 : ∫⁻ x, ENNReal.ofReal (π x) * ((∫⁻ y in E, w x y ∂μ) / Z) ∂μ =
      ∫⁻ y in E, ENNReal.ofReal (π y) * mhAcceptMass π q μ Z y ∂μ := by
    have e1 : ∀ x, ENNReal.ofReal (π x) * ((∫⁻ y in E, w x y ∂μ) / Z) =
        Z⁻¹ * ∫⁻ y in E, mhFlux π q x y ∂μ := by
      intro x
      rw [div_eq_mul_inv, mul_comm (∫⁻ y in E, w x y ∂μ) Z⁻¹, mul_left_comm,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp_rw [hF]
    have e2 : ∀ y, ∫⁻ x, mhFlux π q y x ∂μ = ENNReal.ofReal (π y) * ∫⁻ x, w y x ∂μ := by
      intro y
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp_rw [hF]
    simp_rw [e1]
    rw [lintegral_const_mul' _ _ hZinv, lintegral_lintegral_swap hFm.aemeasurable,
      lintegral_congr fun y => lintegral_congr fun x => mhFlux_comm x y]
    simp_rw [e2]
    rw [← lintegral_const_mul' _ _ hZinv]
    refine lintegral_congr fun y => ?_
    simp only [mhAcceptMass, div_eq_mul_inv]
    ring
  have h2 : ∫⁻ x, ENNReal.ofReal (π x) *
      E.indicator (fun x => 1 - mhAcceptMass π q μ Z x) x ∂μ =
      ∫⁻ x in E, ENNReal.ofReal (π x) * (1 - mhAcceptMass π q μ Z x) ∂μ := by
    have e : ∀ x, ENNReal.ofReal (π x) * E.indicator (fun x => 1 - mhAcceptMass π q μ Z x) x =
        E.indicator (fun x => ENNReal.ofReal (π x) * (1 - mhAcceptMass π q μ Z x)) x := by
      intro x
      by_cases hx : x ∈ E
      · simp only [Set.indicator_of_mem hx]
      · simp only [Set.indicator_of_notMem hx, mul_zero]
    simp_rw [e]
    rw [lintegral_indicator hE]
  rw [h1, h2, ← lintegral_add_left hmeasA]
  refine lintegral_congr fun x => ?_
  rw [← mul_add, add_tsub_cancel_of_le (mhAcceptMass_le_one hq hZ hZ0 hZtop x), mul_one]

/-- The normalised target `π / T` as a measure on `X`. -/
noncomputable def mhTargetLaw (π : X → ℝ) (μ : Measure X) (T : ℝ≥0∞) : Measure X :=
  μ.withDensity fun x => ENNReal.ofReal (π x) / T

omit [SFinite μ] in
theorem mhTargetLaw_apply (hπm : Measurable π) {T : ℝ≥0∞} {E : Set X} (hE : MeasurableSet E) :
    mhTargetLaw π μ T E = (∫⁻ x in E, ENNReal.ofReal (π x) ∂μ) / T := by
  have hm : Measurable fun x => ENNReal.ofReal (π x) := ENNReal.measurable_ofReal.comp hπm
  rw [mhTargetLaw, withDensity_apply _ hE]
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const _ hm]

omit [SFinite μ] in
/-- The normalised target is a probability measure when `T = ∫ π ∈ (0, ∞)`. -/
theorem isProbabilityMeasure_mhTargetLaw (hπm : Measurable π) {T : ℝ≥0∞}
    (hT : ∫⁻ x, ENNReal.ofReal (π x) ∂μ = T) (hT0 : T ≠ 0) (hTtop : T ≠ ∞) :
    IsProbabilityMeasure (mhTargetLaw π μ T) := by
  refine ⟨?_⟩
  rw [mhTargetLaw_apply hπm MeasurableSet.univ, Measure.restrict_univ, hT,
    ENNReal.div_self hT0 hTtop]

/-- **Metropolis–Hastings invariance of the normalised law**: `∫ K(x, E) dν(x) = ν(E)` for
`ν = π/T`. -/
theorem mh_invariant_law (hπm : Measurable π) (hπ : ∀ x, 0 < π x)
    (hqm : Measurable (Function.uncurry q)) (hq : ∀ x y, 0 < q x y) {Z : ℝ≥0∞}
    (hZ : ∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂μ = Z) (hZ0 : Z ≠ 0) (hZtop : Z ≠ ∞) {T : ℝ≥0∞}
    (hT0 : T ≠ 0) {E : Set X} (hE : MeasurableSet E) :
    ∫⁻ x, mhKernelSet π q μ Z x E ∂(mhTargetLaw π μ T) = mhTargetLaw π μ T E := by
  have hTinv : T⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hT0
  have hf : Measurable fun x => ENNReal.ofReal (π x) / T :=
    (ENNReal.measurable_ofReal.comp hπm).div_const T
  rw [mhTargetLaw_apply hπm hE, mhTargetLaw,
    lintegral_withDensity_eq_lintegral_mul _ hf (measurable_mhKernelSet hπm hqm Z hE)]
  simp only [Pi.mul_apply, div_eq_mul_inv]
  have e : ∀ x, ENNReal.ofReal (π x) * T⁻¹ * mhKernelSet π q μ Z x E =
      T⁻¹ * (ENNReal.ofReal (π x) * mhKernelSet π q μ Z x E) := fun x => by ring
  simp_rw [e]
  rw [lintegral_const_mul' _ _ hTinv, mh_invariant hπm hπ hqm hq hZ hZ0 hZtop hE, mul_comm]

end MH

/-! ### B. Gaussian target and Gaussian proposals with symmetric drift -/

section Gaussian

variable {ι : Type*} [Fintype ι]

/-- The unnormalised Gaussian target density with precision `P`: `exp(-½ xᵀ P x)`. -/
noncomputable def targetWeight (P : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  Real.exp (-(1 / 2) * dotProduct x (P *ᵥ x))

/-- The unnormalised Gaussian proposal density with mean `A x`: `exp(-(y - A x)ᵀ S (y - A x))`. -/
noncomputable def propWeight (A S : Matrix ι ι ℝ) (x y : ι → ℝ) : ℝ :=
  Real.exp (-dotProduct (y - A *ᵥ x) (S *ᵥ (y - A *ᵥ x)))

theorem targetWeight_pos (P : Matrix ι ι ℝ) (x : ι → ℝ) : 0 < targetWeight P x := Real.exp_pos _

theorem propWeight_pos (A S : Matrix ι ι ℝ) (x y : ι → ℝ) : 0 < propWeight A S x y := Real.exp_pos _

theorem continuous_quad (S : Matrix ι ι ℝ) : Continuous fun y : ι → ℝ => dotProduct y (S *ᵥ y) :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

theorem continuous_targetWeight (P : Matrix ι ι ℝ) : Continuous (targetWeight P) :=
  ((continuous_quad P).const_smul (-(1 / 2 : ℝ))).rexp

theorem continuous_propWeight (A S : Matrix ι ι ℝ) :
    Continuous (Function.uncurry (propWeight A S)) := by
  have hr : Continuous fun p : (ι → ℝ) × (ι → ℝ) => p.2 - A *ᵥ p.1 :=
    continuous_snd.sub (continuous_const.matrix_mulVec continuous_fst)
  exact (hr.dotProduct (continuous_const.matrix_mulVec hr)).neg.rexp

theorem dotProduct_mulVec_symm {M : Matrix ι ι ℝ} (hM : Mᵀ = M) (x y : ι → ℝ) :
    dotProduct x (M *ᵥ y) = dotProduct y (M *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]

/-- `(v - A u)ᵀ S (v - A u) = vᵀ S v - 2 vᵀ S A u + uᵀ Aᵀ S A u` for symmetric `S`. -/
theorem residual_quad {A S : Matrix ι ι ℝ} (hS : Sᵀ = S) (u v : ι → ℝ) :
    dotProduct (v - A *ᵥ u) (S *ᵥ (v - A *ᵥ u)) =
      dotProduct v (S *ᵥ v) - 2 * dotProduct v ((S * A) *ᵥ u) +
        dotProduct u ((Aᵀ * S * A) *ᵥ u) := by
  have h1 : dotProduct (A *ᵥ u) (S *ᵥ v) = dotProduct v ((S * A) *ᵥ u) := by
    rw [dotProduct_mulVec_symm hS, mulVec_mulVec]
  have h2 : dotProduct v (S *ᵥ (A *ᵥ u)) = dotProduct v ((S * A) *ᵥ u) := by
    rw [mulVec_mulVec]
  have h3 : dotProduct (A *ᵥ u) (S *ᵥ (A *ᵥ u)) = dotProduct u ((Aᵀ * S * A) *ᵥ u) := by
    rw [mulVec_mulVec, ← vecMul_transpose A u, ← dotProduct_mulVec, mulVec_mulVec,
      ← Matrix.mul_assoc]
  rw [mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, h1, h2, h3]
  ring

/-- **The MH ratio for a Gaussian target and a Gaussian proposal with symmetric drift**:
`π(y) q(y,x) / (π(x) q(x,y)) = exp(yᵀ G y - xᵀ G x)`, `G = S - Aᵀ S A - P/2`, whenever `Sᵀ = S` and
`(S A)ᵀ = S A`. -/
theorem targetWeight_propWeight_ratio {P A S : Matrix ι ι ℝ} (hS : Sᵀ = S)
    (hSA : (S * A)ᵀ = S * A) (x y : ι → ℝ) :
    targetWeight P y * propWeight A S y x / (targetWeight P x * propWeight A S x y) =
      Real.exp (dotProduct y ((S - Aᵀ * S * A - (1 / 2 : ℝ) • P) *ᵥ y) -
        dotProduct x ((S - Aᵀ * S * A - (1 / 2 : ℝ) • P) *ᵥ x)) := by
  unfold targetWeight propWeight
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
  congr 1
  rw [residual_quad hS y x, residual_quad hS x y, dotProduct_mulVec_symm hSA x y]
  simp only [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring

/-! #### MALA: `A = 1 - h P`, `S = 1/(4h)` -/

omit [Fintype ι] in
theorem mala_S_symm [DecidableEq ι] (h : ℝ) :
    ((1 / (4 * h)) • (1 : Matrix ι ι ℝ))ᵀ = (1 / (4 * h)) • 1 := by
  rw [transpose_smul, transpose_one]

theorem mala_SA_symm [DecidableEq ι] {P : Matrix ι ι ℝ} (hP : Pᵀ = P) (h : ℝ) :
    (((1 / (4 * h)) • (1 : Matrix ι ι ℝ)) * (1 - h • P))ᵀ =
      ((1 / (4 * h)) • (1 : Matrix ι ι ℝ)) * (1 - h • P) := by
  rw [Matrix.smul_mul, Matrix.one_mul, transpose_smul, transpose_sub, transpose_one, transpose_smul,
    hP]

theorem mala_G [DecidableEq ι] {P : Matrix ι ι ℝ} (hP : Pᵀ = P) {h : ℝ} (hh : h ≠ 0) :
    (1 / (4 * h)) • (1 : Matrix ι ι ℝ) -
        (1 - h • P)ᵀ * ((1 / (4 * h)) • (1 : Matrix ι ι ℝ)) * (1 - h • P) - (1 / 2 : ℝ) • P =
      (-(h / 4)) • (P * P) := by
  rw [transpose_sub, transpose_one, transpose_smul, hP]
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, smul_smul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **The MALA acceptance ratio on a Gaussian target**: `exp(-(h/4)(‖P y‖² - ‖P x‖²))`. -/
theorem mala_ratio [DecidableEq ι] {P : Matrix ι ι ℝ} (hP : Pᵀ = P) {h : ℝ} (hh : h ≠ 0)
    (x y : ι → ℝ) :
    targetWeight P y * propWeight (1 - h • P) ((1 / (4 * h)) • 1) y x /
        (targetWeight P x * propWeight (1 - h • P) ((1 / (4 * h)) • 1) x y) =
      Real.exp (-(h / 4) * (dotProduct (P *ᵥ y) (P *ᵥ y) - dotProduct (P *ᵥ x) (P *ᵥ x))) := by
  rw [targetWeight_propWeight_ratio (mala_S_symm h) (mala_SA_symm hP h), mala_G hP hh]
  congr 1
  have e : ∀ z : ι → ℝ, dotProduct z (((-(h / 4)) • (P * P)) *ᵥ z) =
      -(h / 4) * dotProduct (P *ᵥ z) (P *ᵥ z) := by
    intro z
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul, ← mulVec_mulVec, dotProduct_mulVec,
      ← mulVec_transpose, hP]
  rw [e, e]
  ring

/-! #### pMALA: `A = (1 - h) 1`, `S = P/(4h)` -/

omit [Fintype ι] in
theorem pmala_S_symm {P : Matrix ι ι ℝ} (hP : Pᵀ = P) (h : ℝ) :
    ((1 / (4 * h)) • P)ᵀ = (1 / (4 * h)) • P := by
  rw [transpose_smul, hP]

theorem pmala_SA_symm [DecidableEq ι] {P : Matrix ι ι ℝ} (hP : Pᵀ = P) (h : ℝ) :
    (((1 / (4 * h)) • P) * ((1 - h) • (1 : Matrix ι ι ℝ)))ᵀ =
      ((1 / (4 * h)) • P) * ((1 - h) • (1 : Matrix ι ι ℝ)) := by
  rw [Matrix.mul_smul, Matrix.mul_one, transpose_smul, transpose_smul, hP]

theorem pmala_G [DecidableEq ι] {P : Matrix ι ι ℝ} {h : ℝ} (hh : h ≠ 0) :
    (1 / (4 * h)) • P -
        ((1 - h) • (1 : Matrix ι ι ℝ))ᵀ * ((1 / (4 * h)) • P) * ((1 - h) • (1 : Matrix ι ι ℝ)) -
        (1 / 2 : ℝ) • P =
      (-(h / 4)) • P := by
  simp only [transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_smul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **The pMALA acceptance ratio on a Gaussian target**: `exp(-(h/4)(yᵀ P y - xᵀ P x))`. -/
theorem pmala_ratio [DecidableEq ι] {P : Matrix ι ι ℝ} (hP : Pᵀ = P) {h : ℝ} (hh : h ≠ 0)
    (x y : ι → ℝ) :
    targetWeight P y * propWeight ((1 - h) • 1) ((1 / (4 * h)) • P) y x /
        (targetWeight P x * propWeight ((1 - h) • 1) ((1 / (4 * h)) • P) x y) =
      Real.exp (-(h / 4) * (dotProduct y (P *ᵥ y) - dotProduct x (P *ᵥ x))) := by
  rw [targetWeight_propWeight_ratio (pmala_S_symm hP h) (pmala_SA_symm hP h), pmala_G hh]
  congr 1
  simp only [smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring

/-! #### The proposal normalisation and the invariance of the Gaussian target -/

/-- The proposal normalisation `Z_S = ∫ exp(-yᵀ S y) dy`. -/
noncomputable def propZ (S : Matrix ι ι ℝ) : ℝ≥0∞ :=
  ∫⁻ y : ι → ℝ, ENNReal.ofReal (Real.exp (-dotProduct y (S *ᵥ y)))

/-- The row integrals of the proposal are all equal to `Z_S` (translation invariance). -/
theorem lintegral_propWeight (A S : Matrix ι ι ℝ) (x : ι → ℝ) :
    ∫⁻ y, ENNReal.ofReal (propWeight A S x y) = propZ S := by
  unfold propWeight propZ
  exact lintegral_sub_right_eq_self
    (fun z : ι → ℝ => ENNReal.ofReal (Real.exp (-dotProduct z (S *ᵥ z)))) (A *ᵥ x)

theorem propZ_ne_zero (S : Matrix ι ι ℝ) : propZ S ≠ 0 := by
  unfold propZ
  have hm : Measurable fun y : ι → ℝ => ENNReal.ofReal (Real.exp (-dotProduct y (S *ᵥ y))) :=
    ENNReal.measurable_ofReal.comp ((continuous_quad S).neg.rexp.measurable)
  refine ((lintegral_pos_iff_support hm).mpr ?_).ne'
  have hsupp : Function.support
      (fun y : ι → ℝ => ENNReal.ofReal (Real.exp (-dotProduct y (S *ᵥ y)))) = Set.univ := by
    ext y
    simp [Function.mem_support, (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne']
  rw [hsupp]
  exact isOpen_univ.measure_pos _ Set.univ_nonempty

/-- `exp(-yᵀ S y)` is the seabed's Gaussian weight with precision `2 S`. -/
theorem exp_neg_quad_eq_gaussianWeight [DecidableEq ι] (S : Matrix ι ι ℝ) (y : ι → ℝ) :
    Real.exp (-dotProduct y (S *ᵥ y)) =
      Laplace.Multi.gaussianWeight (Laplace.Multi.matCLM ((2 : ℝ) • S)) y := by
  rw [Laplace.Multi.gaussianWeight, Laplace.Multi.quadForm_matCLM, smul_mulVec, dotProduct_smul,
    smul_eq_mul]
  congr 1
  ring

theorem propZ_ne_top {S : Matrix ι ι ℝ} (hS : S.PosDef) : propZ S ≠ ∞ := by
  classical
  unfold propZ
  simp_rw [exp_neg_quad_eq_gaussianWeight]
  exact (Laplace.Multi.integrable_gaussianWeight_matCLM
    (hS.smul (by norm_num : (0 : ℝ) < 2))).lintegral_lt_top.ne

/-- The target normalisation `T_P = ∫ exp(-½ xᵀ P x) dx`. -/
noncomputable def targetZ (P : Matrix ι ι ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ι → ℝ, ENNReal.ofReal (targetWeight P x)

theorem targetZ_ne_zero (P : Matrix ι ι ℝ) : targetZ P ≠ 0 := by
  unfold targetZ
  have hm : Measurable fun x : ι → ℝ => ENNReal.ofReal (targetWeight P x) :=
    ENNReal.measurable_ofReal.comp (continuous_targetWeight P).measurable
  refine ((lintegral_pos_iff_support hm).mpr ?_).ne'
  have hsupp :
      Function.support (fun x : ι → ℝ => ENNReal.ofReal (targetWeight P x)) = Set.univ := by
    ext x
    simp [Function.mem_support, (ENNReal.ofReal_pos.mpr (targetWeight_pos P x)).ne']
  rw [hsupp]
  exact isOpen_univ.measure_pos _ Set.univ_nonempty

/-- `targetWeight P` is the seabed's Gaussian weight with precision `P`. -/
theorem targetWeight_eq_gaussianWeight [DecidableEq ι] (P : Matrix ι ι ℝ) :
    targetWeight P = Laplace.Multi.gaussianWeight (Laplace.Multi.matCLM P) := by
  funext x
  rw [targetWeight, Laplace.Multi.gaussianWeight, Laplace.Multi.quadForm_matCLM]

theorem targetZ_ne_top {P : Matrix ι ι ℝ} (hP : P.PosDef) : targetZ P ≠ ∞ := by
  classical
  unfold targetZ
  rw [targetWeight_eq_gaussianWeight]
  exact (Laplace.Multi.integrable_gaussianWeight_matCLM hP).lintegral_lt_top.ne

/-- The normalised Gaussian law with precision `P` (density `exp(-½ xᵀ P x)/T_P`). -/
noncomputable def gaussianLaw (P : Matrix ι ι ℝ) : Measure (ι → ℝ) :=
  mhTargetLaw (targetWeight P) volume (targetZ P)

theorem isProbabilityMeasure_gaussianLaw {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    IsProbabilityMeasure (gaussianLaw P) :=
  isProbabilityMeasure_mhTargetLaw (continuous_targetWeight P).measurable rfl (targetZ_ne_zero P)
    (targetZ_ne_top hP)

variable [DecidableEq ι] {E : Set (ι → ℝ)}

/-- **MALA has the exact stationary law**: for every `h > 0`, the Gaussian density with precision
`P` is invariant under the MALA kernel (proposal `y = x - h P x + √(2h) ξ`); no stability
restriction on `h` and no positivity of `P` is needed for the density-level statement. -/
theorem mala_invariant (P : Matrix ι ι ℝ) {h : ℝ} (hh : 0 < h) (hE : MeasurableSet E) :
    ∫⁻ x, ENNReal.ofReal (targetWeight P x) *
        mhKernelSet (targetWeight P) (propWeight (1 - h • P) ((1 / (4 * h)) • 1)) volume
          (propZ ((1 / (4 * h)) • (1 : Matrix ι ι ℝ))) x E =
      ∫⁻ x in E, ENNReal.ofReal (targetWeight P x) :=
  mh_invariant (continuous_targetWeight P).measurable (targetWeight_pos P)
    (continuous_propWeight _ _).measurable (propWeight_pos _ _) (lintegral_propWeight _ _)
    (propZ_ne_zero _)
    (propZ_ne_top ((Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef).smul (by positivity))) hE

/-- **MALA leaves the Gaussian probability law invariant**: `∫ K(x, E) dν_P(x) = ν_P(E)` (for `P`
positive definite `ν_P` is a probability measure, `isProbabilityMeasure_gaussianLaw`). -/
theorem mala_invariant_law (P : Matrix ι ι ℝ) {h : ℝ} (hh : 0 < h) (hE : MeasurableSet E) :
    ∫⁻ x, mhKernelSet (targetWeight P) (propWeight (1 - h • P) ((1 / (4 * h)) • 1)) volume
        (propZ ((1 / (4 * h)) • (1 : Matrix ι ι ℝ))) x E ∂(gaussianLaw P) = gaussianLaw P E :=
  mh_invariant_law (continuous_targetWeight P).measurable (targetWeight_pos P)
    (continuous_propWeight _ _).measurable (propWeight_pos _ _) (lintegral_propWeight _ _)
    (propZ_ne_zero _)
    (propZ_ne_top ((Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef).smul (by positivity)))
    (targetZ_ne_zero P) hE

/-- **pMALA has the exact stationary law**: for every `h > 0`, the Gaussian density with precision
`P` is invariant under the `P⁻¹`-preconditioned MALA kernel
(proposal `y = (1 - h) x + √(2h) P^{-1/2} ξ`). -/
theorem pmala_invariant {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h)
    (hE : MeasurableSet E) :
    ∫⁻ x, ENNReal.ofReal (targetWeight P x) *
        mhKernelSet (targetWeight P) (propWeight ((1 - h) • 1) ((1 / (4 * h)) • P)) volume
          (propZ ((1 / (4 * h)) • P)) x E =
      ∫⁻ x in E, ENNReal.ofReal (targetWeight P x) :=
  mh_invariant (continuous_targetWeight P).measurable (targetWeight_pos P)
    (continuous_propWeight _ _).measurable (propWeight_pos _ _) (lintegral_propWeight _ _)
    (propZ_ne_zero _) (propZ_ne_top (hP.smul (by positivity))) hE

/-- **pMALA leaves the Gaussian probability law invariant.** -/
theorem pmala_invariant_law {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h)
    (hE : MeasurableSet E) :
    ∫⁻ x, mhKernelSet (targetWeight P) (propWeight ((1 - h) • 1) ((1 / (4 * h)) • P)) volume
        (propZ ((1 / (4 * h)) • P)) x E ∂(gaussianLaw P) = gaussianLaw P E :=
  mh_invariant_law (continuous_targetWeight P).measurable (targetWeight_pos P)
    (continuous_propWeight _ _).measurable (propWeight_pos _ _) (lintegral_propWeight _ _)
    (propZ_ne_zero _) (propZ_ne_top (hP.smul (by positivity))) (targetZ_ne_zero P) hE

end Gaussian

end Laplace.Sampler
