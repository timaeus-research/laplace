/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.Metropolis
import Laplace.Multi.TiltedGaussian

/-!
# The Metropolis–Hastings kernel as a Markov kernel, and the moments of the invariant law

`Laplace.Sampler.Metropolis` proves the invariance of a target density under Metropolis–Hastings
at the level of set functions. This file packages the sampler as a `ProbabilityTheory.Kernel`:

* `mhKernel`: `K(x) = μ.withDensity (q(x,·) α(x,·)/Z) + (1 - a(x)) δ_x`, with `mhKernel_apply_set`
  identifying `K(x)(E)` with `mhKernelSet`;
* `isMarkovKernel_mhKernel`: each `K(x)` is a probability measure;
* `bind_mhKernel`: the normalised target is a fixed point, `ν.bind K = ν`;
* `malaKernel`, `pmalaKernel` and their fixed-point statements `bind_malaKernel`,
  `bind_pmalaKernel` for the Gaussian law `gaussianLaw P`, for every step `h > 0`.

The invariant law is then identified through its moments: under `gaussianLaw P` the coordinates
have mean `0` and second moments `P⁻¹` (`integral_coord_gaussianLaw`,
`integral_coord_mul_gaussianLaw`), by bridging the `ℝ≥0∞`-density measure to the seabed's real
`tiltedExpectation` at zero tilt. This is the note's "the Metropolis-corrected MALA lands on `P⁻¹`"
as a covariance statement.
-/

open MeasureTheory ENNReal Matrix Set ProbabilityTheory

namespace Laplace.Sampler

/-! ### A. The Metropolis–Hastings kernel -/

section Kernel

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
variable (π : X → ℝ) (q : X → X → ℝ)

/-- The MH transition measure from `x`: accepted moves with density `q(x,·) α(x,·)/Z` with respect
to `μ`, plus the rejection mass at `x`. -/
noncomputable def mhKernelFun (μ : Measure X) (Z : ℝ≥0∞) (x : X) : Measure X :=
  μ.withDensity (fun y => ENNReal.ofReal (q x y * mhAccept π q x y) / Z) +
    (1 - mhAcceptMass π q μ Z x) • Measure.dirac x

variable {π q}

omit [SFinite μ] in
theorem mhKernelFun_apply {Z : ℝ≥0∞} (hZ0 : Z ≠ 0) (x : X) {E : Set X} (hE : MeasurableSet E) :
    mhKernelFun π q μ Z x E = mhKernelSet π q μ Z x E := by
  rw [mhKernelFun, Measure.add_apply, Measure.smul_apply, withDensity_apply _ hE,
    Measure.dirac_apply' _ hE, smul_eq_mul, mhKernelSet]
  congr 1
  · simp_rw [div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hZ0)]
  · by_cases hx : x ∈ E
    · simp [hx]
    · simp [hx]

/-- **The Metropolis–Hastings kernel.** -/
noncomputable def mhKernel (hπm : Measurable π) (hqm : Measurable (Function.uncurry q))
    (μ : Measure X) [SFinite μ] {Z : ℝ≥0∞} (hZ0 : Z ≠ 0) : Kernel X X where
  toFun := mhKernelFun π q μ Z
  measurable' := Measure.measurable_of_measurable_coe _ fun E hE => by
    simp_rw [mhKernelFun_apply hZ0 _ hE]
    exact measurable_mhKernelSet hπm hqm Z hE

theorem mhKernel_apply_set (hπm : Measurable π) (hqm : Measurable (Function.uncurry q))
    {Z : ℝ≥0∞} (hZ0 : Z ≠ 0) (x : X) {E : Set X} (hE : MeasurableSet E) :
    mhKernel hπm hqm μ hZ0 x E = mhKernelSet π q μ Z x E :=
  mhKernelFun_apply hZ0 x hE

/-- **The MH kernel is Markov**: each `K(x)` is a probability measure. -/
theorem isMarkovKernel_mhKernel (hπm : Measurable π) (hqm : Measurable (Function.uncurry q))
    (hq : ∀ x y, 0 < q x y) {Z : ℝ≥0∞} (hZ : ∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂μ = Z)
    (hZ0 : Z ≠ 0) (hZtop : Z ≠ ∞) : IsMarkovKernel (mhKernel hπm hqm μ hZ0) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [mhKernel_apply_set hπm hqm hZ0 x MeasurableSet.univ, mhKernelSet, Set.indicator_univ,
    Measure.restrict_univ]
  exact add_tsub_cancel_of_le (mhAcceptMass_le_one hq hZ hZ0 hZtop x)

/-- **The normalised target is a fixed point of the MH kernel**: `ν.bind K = ν`. -/
theorem bind_mhKernel (hπm : Measurable π) (hπ : ∀ x, 0 < π x)
    (hqm : Measurable (Function.uncurry q)) (hq : ∀ x y, 0 < q x y) {Z : ℝ≥0∞}
    (hZ : ∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂μ = Z) (hZ0 : Z ≠ 0) (hZtop : Z ≠ ∞) {T : ℝ≥0∞}
    (hT0 : T ≠ 0) :
    (mhTargetLaw π μ T).bind (mhKernel hπm hqm μ hZ0) = mhTargetLaw π μ T := by
  ext E hE
  rw [Measure.bind_apply hE (mhKernel hπm hqm μ hZ0).measurable.aemeasurable]
  simp_rw [mhKernel_apply_set hπm hqm hZ0 _ hE]
  exact mh_invariant_law hπm hπ hqm hq hZ hZ0 hZtop hT0 hE

/-- **Stationarity after any number of steps**: the target law is unchanged by `n` transitions. -/
theorem bind_mhKernel_iterate (hπm : Measurable π) (hπ : ∀ x, 0 < π x)
    (hqm : Measurable (Function.uncurry q)) (hq : ∀ x y, 0 < q x y) {Z : ℝ≥0∞}
    (hZ : ∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂μ = Z) (hZ0 : Z ≠ 0) (hZtop : Z ≠ ∞) {T : ℝ≥0∞}
    (hT0 : T ≠ 0) (n : ℕ) :
    (fun ν : Measure X => ν.bind (mhKernel hπm hqm μ hZ0))^[n] (mhTargetLaw π μ T) =
      mhTargetLaw π μ T := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, bind_mhKernel hπm hπ hqm hq hZ hZ0 hZtop hT0]

end Kernel

/-! ### B. MALA and pMALA as Markov kernels on the Gaussian law -/

section GaussianKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The MALA kernel on the Gaussian target with precision `P` and step `h`. -/
noncomputable def malaKernel (P : Matrix ι ι ℝ) (h : ℝ) : Kernel (ι → ℝ) (ι → ℝ) :=
  mhKernel (continuous_targetWeight P).measurable
    (continuous_propWeight (1 - h • P) ((1 / (4 * h)) • 1)).measurable volume
    (propZ_ne_zero ((1 / (4 * h)) • (1 : Matrix ι ι ℝ)))

/-- The pMALA kernel (preconditioned by `P⁻¹`) on the Gaussian target with precision `P`. -/
noncomputable def pmalaKernel (P : Matrix ι ι ℝ) (h : ℝ) : Kernel (ι → ℝ) (ι → ℝ) :=
  mhKernel (continuous_targetWeight P).measurable
    (continuous_propWeight ((1 - h) • 1) ((1 / (4 * h)) • P)).measurable volume
    (propZ_ne_zero ((1 / (4 * h)) • P))

theorem isMarkovKernel_malaKernel (P : Matrix ι ι ℝ) {h : ℝ} (hh : 0 < h) :
    IsMarkovKernel (malaKernel P h) :=
  isMarkovKernel_mhKernel _ _ (propWeight_pos _ _) (lintegral_propWeight _ _) _
    (propZ_ne_top ((Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef).smul (by positivity)))

theorem isMarkovKernel_pmalaKernel {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) :
    IsMarkovKernel (pmalaKernel P h) :=
  isMarkovKernel_mhKernel _ _ (propWeight_pos _ _) (lintegral_propWeight _ _) _
    (propZ_ne_top (hP.smul (by positivity)))

/-- **MALA has the exact stationary law**: `gaussianLaw P` is a fixed point of the MALA kernel for
every step `h > 0`. -/
theorem bind_malaKernel (P : Matrix ι ι ℝ) {h : ℝ} (hh : 0 < h) :
    (gaussianLaw P).bind (malaKernel P h) = gaussianLaw P :=
  bind_mhKernel _ (targetWeight_pos P) _ (propWeight_pos _ _) (lintegral_propWeight _ _) _
    (propZ_ne_top ((Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef).smul (by positivity)))
    (targetZ_ne_zero P)

/-- **pMALA has the exact stationary law**: `gaussianLaw P` is a fixed point of the pMALA kernel for
every step `h > 0`. -/
theorem bind_pmalaKernel {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h) :
    (gaussianLaw P).bind (pmalaKernel P h) = gaussianLaw P :=
  bind_mhKernel _ (targetWeight_pos P) _ (propWeight_pos _ _) (lintegral_propWeight _ _) _
    (propZ_ne_top (hP.smul (by positivity))) (targetZ_ne_zero P)

/-- The Gaussian law is unchanged by any number of MALA steps. -/
theorem bind_malaKernel_iterate (P : Matrix ι ι ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    (fun ν : Measure (ι → ℝ) => ν.bind (malaKernel P h))^[n] (gaussianLaw P) = gaussianLaw P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, bind_malaKernel P hh]

end GaussianKernel

/-! ### C. The moments of the invariant law: mean `0`, covariance `P⁻¹` -/

section Moments

open Laplace.Multi

variable {ι : Type*} [Fintype ι]

theorem targetWeight_eq_tiltedWeight_zero (P : Matrix ι ι ℝ) :
    targetWeight P = tiltedWeight P 0 := by
  classical
  rw [targetWeight_eq_gaussianWeight]
  funext u
  rw [tiltedWeight_zero]

theorem targetZ_toReal (P : Matrix ι ι ℝ) : (targetZ P).toReal = tiltedZ P 0 := by
  rw [targetZ, tiltedZ, ← targetWeight_eq_tiltedWeight_zero,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => (targetWeight_pos P x).le)
      (continuous_targetWeight P).aestronglyMeasurable]

/-- Integrals against the Gaussian law are the seabed's zero-tilt expectations. -/
theorem integral_gaussianLaw (P : Matrix ι ι ℝ) (g : (ι → ℝ) → ℝ) :
    ∫ x, g x ∂(gaussianLaw P) = tiltedExpectation P 0 g := by
  have hm : Measurable fun x : ι → ℝ => ENNReal.ofReal (targetWeight P x) / targetZ P :=
    (ENNReal.measurable_ofReal.comp (continuous_targetWeight P).measurable).div_const _
  rw [gaussianLaw, mhTargetLaw, integral_withDensity_eq_integral_toReal_smul₀ hm.aemeasurable
    (ae_of_all _ fun x => ENNReal.div_lt_top ENNReal.ofReal_ne_top (targetZ_ne_zero P)) g]
  simp_rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (targetWeight_pos P _).le, smul_eq_mul,
    targetZ_toReal P]
  rw [tiltedExpectation, ← integral_div]
  congr 1
  funext x
  rw [targetWeight_eq_tiltedWeight_zero]
  ring

/-- Integrability under the Gaussian law reduces to integrability against the Gaussian weight. -/
theorem integrable_gaussianLaw_iff (P : Matrix ι ι ℝ) (g : (ι → ℝ) → ℝ) :
    Integrable g (gaussianLaw P) ↔
      Integrable (fun x => targetWeight P x / tiltedZ P 0 * g x) volume := by
  have hm : Measurable fun x : ι → ℝ => ENNReal.ofReal (targetWeight P x) / targetZ P :=
    (ENNReal.measurable_ofReal.comp (continuous_targetWeight P).measurable).div_const _
  rw [gaussianLaw, mhTargetLaw, integrable_withDensity_iff_integrable_smul₀' hm.aemeasurable
    (ae_of_all _ fun x => ENNReal.div_lt_top ENNReal.ofReal_ne_top (targetZ_ne_zero P))]
  simp_rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (targetWeight_pos P _).le, smul_eq_mul,
    targetZ_toReal P]

theorem integrable_coord_gaussianLaw {P : Matrix ι ι ℝ} (hP : P.PosDef) (i : ι) :
    Integrable (fun x => x i) (gaussianLaw P) := by
  classical
  rw [integrable_gaussianLaw_iff]
  refine ((integrable_coord_mul_gaussianWeight_matCLM' hP i).div_const (tiltedZ P 0)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [targetWeight_eq_tiltedWeight_zero, tiltedWeight_zero]
  ring

theorem integrable_coord_mul_gaussianLaw {P : Matrix ι ι ℝ} (hP : P.PosDef) (i j : ι) :
    Integrable (fun x => x i * x j) (gaussianLaw P) := by
  classical
  rw [integrable_gaussianLaw_iff]
  refine ((integrable_coord_mul_gaussianWeight_matCLM hP i j).div_const (tiltedZ P 0)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [targetWeight_eq_tiltedWeight_zero, tiltedWeight_zero]
  ring

/-- **Mean zero** under the Gaussian law. -/
theorem integral_coord_gaussianLaw {P : Matrix ι ι ℝ} (hP : P.PosDef) (i : ι) :
    ∫ x, x i ∂(gaussianLaw P) = 0 := by
  classical
  rw [integral_gaussianLaw P, tiltedExpectation_coord hP, tiltMean, mulVec_zero, Pi.zero_apply]

/-- **Covariance `P⁻¹`** under the Gaussian law: the MALA/pMALA-invariant law "lands on `P⁻¹`". -/
theorem integral_coord_mul_gaussianLaw [DecidableEq ι] {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (i j : ι) : ∫ x, x i * x j ∂(gaussianLaw P) = P⁻¹ i j := by
  rw [integral_gaussianLaw P, tiltedExpectation_coord_mul hP]
  simp [tiltMean]

/-- **The covariance of the invariant law is `P⁻¹`**: `E[xᵢ xⱼ] - E[xᵢ] E[xⱼ] = P⁻¹ᵢⱼ`. -/
theorem covariance_gaussianLaw [DecidableEq ι] {P : Matrix ι ι ℝ} (hP : P.PosDef) (i j : ι) :
    ∫ x, x i * x j ∂(gaussianLaw P) -
      (∫ x, x i ∂(gaussianLaw P)) * ∫ x, x j ∂(gaussianLaw P) = P⁻¹ i j := by
  rw [integral_coord_mul_gaussianLaw hP, integral_coord_gaussianLaw hP,
    integral_coord_gaussianLaw hP]
  ring

end Moments

end Laplace.Sampler
