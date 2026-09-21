/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Laplace.Sampler.GaussianInvariance

/-!
# Uniqueness of the invariant law and convergence of the ULA chain

For the affine Gaussian step `gaussStep A R μ = (μ.map A) ∗ N(0, R)` with `A` a symmetric
contraction (`A = U diag(a) Uᵀ`, `|a i| < 1`) and `R ⪰ 0`, the centred Gaussian `N(0, S)` with
`S` the covariance fixed point is the *unique* invariant probability law, and the laws of the
chain started from *any* probability law converge to it (pointwise in characteristic functions,
hence weakly by Lévy's theorem). No moment assumption is made.

The proof is the quotient argument: with `g = charFun N(0, S)` (nowhere zero) and `B = Aᵀ`, one
step gives `φ(t) = φ(B t) · r(t)` for the characteristic function `φ` of any input law, and
`g(t) = g(B t) · r(t)`, so `H = φ / g` satisfies `H(t) = H(B t) = … = H(Bⁿ t) → H(0) = 1`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Characteristic functions of push-forwards and of the Gaussian step -/

omit [DecidableEq ι] in
/-- `charFun (μ.map L) t = charFun μ (L† t)` for a continuous linear map on a real Hilbert space. -/
theorem charFun_map_clm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (μ : Measure E) (L : E →L[ℝ] E)
    (t : E) : charFun (μ.map L) t = charFun μ (ContinuousLinearMap.adjoint L t) := by
  rw [charFun_apply, charFun_apply,
    integral_map L.continuous.measurable.aemeasurable (by fun_prop)]
  congr 1
  funext x
  rw [ContinuousLinearMap.adjoint_inner_right]

theorem charFun_map_euclid (μ : Measure (EuclideanSpace ℝ ι)) (A : Matrix ι ι ℝ)
    (t : EuclideanSpace ℝ ι) : charFun (μ.map (euclid A)) t = charFun μ (euclid Aᵀ t) := by
  rw [charFun_map_clm, euclid_adjoint]

/-- The Gaussian factor of one step. -/
noncomputable def gaussFactor (R : Matrix ι ι ℝ) (t : EuclideanSpace ℝ ι) : ℂ :=
  Complex.exp (-(t.ofLp ⬝ᵥ R *ᵥ t.ofLp) / 2)

omit [DecidableEq ι] in
theorem gaussFactor_ne_zero (R : Matrix ι ι ℝ) (t : EuclideanSpace ℝ ι) : gaussFactor R t ≠ 0 :=
  Complex.exp_ne_zero _

theorem charFun_multivariateGaussian_zero {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (t : EuclideanSpace ℝ ι) :
    charFun (multivariateGaussian 0 S) t = gaussFactor S t := by
  rw [charFun_multivariateGaussian hS, gaussFactor]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  congr 1
  ring

theorem charFun_multivariateGaussian_ne_zero {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (m t : EuclideanSpace ℝ ι) : charFun (multivariateGaussian m S) t ≠ 0 := by
  rw [charFun_multivariateGaussian hS]; exact Complex.exp_ne_zero _

instance isProbabilityMeasure_gaussStep (A R : Matrix ι ι ℝ) (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (gaussStep A R μ) := by
  unfold gaussStep
  have : IsProbabilityMeasure (μ.map (euclid A)) :=
    Measure.isProbabilityMeasure_map (euclid A).continuous.measurable.aemeasurable
  infer_instance

theorem isProbabilityMeasure_gaussStep_iterate (A R : Matrix ι ι ℝ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure ((gaussStep A R)^[n] μ) := by
  induction n with
  | zero => simpa
  | succ n ih => rw [Function.iterate_succ_apply']; exact isProbabilityMeasure_gaussStep A R _

/-- **One step on characteristic functions**: `φ_{step μ}(t) = φ_μ(Aᵀ t) · exp(-⟨t, R t⟩/2)`. -/
theorem charFun_gaussStep {R : Matrix ι ι ℝ} (hR : R.PosSemidef) (A : Matrix ι ι ℝ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (t : EuclideanSpace ℝ ι) :
    charFun (gaussStep A R μ) t = charFun μ (euclid Aᵀ t) * gaussFactor R t := by
  have : IsProbabilityMeasure (μ.map (euclid A)) :=
    Measure.isProbabilityMeasure_map (euclid A).continuous.measurable.aemeasurable
  unfold gaussStep
  rw [charFun_conv, charFun_map_euclid, charFun_multivariateGaussian_zero hR]

/-! ### Matrix limits -/

theorem pow_eq_conj_diagonal_pow (U A : Matrix ι ι ℝ) (a : ι → ℝ) (hU : Uᵀ * U = 1)
    (hU' : U * Uᵀ = 1) (hA : A = U * diagonal a * Uᵀ) (n : ℕ) :
    A ^ n = U * diagonal (fun i => a i ^ n) * Uᵀ := by
  induction n with
  | zero => simp [hU']
  | succ n ih =>
    rw [pow_succ, ih, hA]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _) (diagonal _),
      diagonal_mul_diagonal]
    simp only [pow_succ]

omit [Fintype ι] in
theorem tendsto_diagonal_pow (a : ι → ℝ) (ha : ∀ i, |a i| < 1) :
    Tendsto (fun n : ℕ => diagonal (fun i => a i ^ n)) atTop (𝓝 (0 : Matrix ι ι ℝ)) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  simp only [diagonal_apply, Matrix.zero_apply]
  split_ifs with hij
  · subst hij; exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one (ha i)
  · exact tendsto_const_nhds

/-- Powers of a symmetric contraction tend to zero. -/
theorem tendsto_pow_of_spectral (U A : Matrix ι ι ℝ) (a : ι → ℝ) (hU : Uᵀ * U = 1)
    (hU' : U * Uᵀ = 1) (hA : A = U * diagonal a * Uᵀ) (ha : ∀ i, |a i| < 1) :
    Tendsto (fun n : ℕ => A ^ n) atTop (𝓝 0) := by
  simp_rw [pow_eq_conj_diagonal_pow U A a hU hU' hA]
  have h := ((tendsto_diagonal_pow a ha).const_mul U).mul_const Uᵀ
  simpa using h

theorem transpose_eq_self_of_spectral (U A : Matrix ι ι ℝ) (a : ι → ℝ)
    (hA : A = U * diagonal a * Uᵀ) : Aᵀ = A := by
  rw [hA, transpose_mul, transpose_mul, diagonal_transpose, transpose_transpose, Matrix.mul_assoc]

omit [DecidableEq ι] in
/-- Matrices tending to zero act on a fixed vector with limit zero (entrywise). -/
theorem tendsto_mulVec_of_tendsto {M : ℕ → Matrix ι ι ℝ} (hM : Tendsto M atTop (𝓝 0))
    (t : ι → ℝ) : Tendsto (fun n => (M n) *ᵥ t) atTop (𝓝 0) := by
  have hij : ∀ i j, Tendsto (fun n => M n i j) atTop (𝓝 0) := fun i j => by
    have := ((continuous_id.matrix_elem i j).tendsto (0 : Matrix ι ι ℝ)).comp hM
    exact this
  rw [tendsto_pi_nhds]
  intro i
  have h : Tendsto (fun n => ∑ j, M n i j * t j) atTop (𝓝 (∑ j : ι, (0 : ℝ) * t j)) :=
    tendsto_finsetSum _ fun j _ => (hij i j).mul_const _
  simpa [mulVec, dotProduct] using h

/-- The Euclidean action of matrices tending to zero tends to zero. -/
theorem tendsto_euclid_apply_of_tendsto {M : ℕ → Matrix ι ι ℝ} (hM : Tendsto M atTop (𝓝 0))
    (t : EuclideanSpace ℝ ι) : Tendsto (fun n => euclid (M n) t) atTop (𝓝 0) := by
  have h := (PiLp.continuous_toLp (p := 2) (β := fun _ : ι => ℝ)).tendsto 0 |>.comp
    (tendsto_mulVec_of_tendsto hM t.ofLp)
  refine h.congr fun n => ?_
  simp only [Function.comp]
  rw [← ofLp_toEuclideanCLM]

/-- Powers of a symmetric contraction, acting on Euclidean space, tend to zero. -/
theorem tendsto_euclid_pow_of_spectral (U A : Matrix ι ι ℝ) (a : ι → ℝ) (hU : Uᵀ * U = 1)
    (hU' : U * Uᵀ = 1) (hA : A = U * diagonal a * Uᵀ) (ha : ∀ i, |a i| < 1)
    (t : EuclideanSpace ℝ ι) : Tendsto (fun n => euclid ((Aᵀ) ^ n) t) atTop (𝓝 0) := by
  rw [transpose_eq_self_of_spectral U A a hA]
  exact tendsto_euclid_apply_of_tendsto (tendsto_pow_of_spectral U A a hU hU' hA ha) t

/-- **Convergence of the covariance iterates** from any start to the fixed point. -/
theorem tendsto_covStep_iterate (U A : Matrix ι ι ℝ) (a : ι → ℝ) (hU : Uᵀ * U = 1)
    (hU' : U * Uᵀ = 1) (hA : A = U * diagonal a * Uᵀ) (ha : ∀ i, |a i| < 1)
    (R S X₀ : Matrix ι ι ℝ) (hS : covStep A R S = S) :
    Tendsto (fun n : ℕ => (covStep A R)^[n] X₀) atTop (𝓝 S) := by
  have hpow := tendsto_pow_of_spectral U A a hU hU' hA ha
  have hpowT : Tendsto (fun n : ℕ => (Aᵀ) ^ n) atTop (𝓝 0) := by
    rw [transpose_eq_self_of_spectral U A a hA]; exact hpow
  have h : Tendsto (fun n : ℕ => A ^ n * (X₀ - S) * (Aᵀ) ^ n) atTop (𝓝 0) := by
    have := (hpow.mul_const (X₀ - S)).mul hpowT
    simpa using this
  rw [← tendsto_sub_nhds_zero_iff]
  refine h.congr fun n => ?_
  rw [covStep_iterate_sub_fixed A R X₀ S hS n]

/-! ### The quotient argument -/

/-- The Euclidean action of `(Aᵀ)^(n+1)` is `Aᵀ` after `(Aᵀ)^n`. -/
lemma euclid_transpose_pow_succ (A : Matrix ι ι ℝ) (n : ℕ) (t : EuclideanSpace ℝ ι) :
    euclid ((Aᵀ) ^ (n + 1)) t = euclid ((Aᵀ) ^ n) (euclid Aᵀ t) := by
  rw [pow_succ, euclid_mul, mul_apply_eq_comp]

/-- The step identity for a quotient of characteristic functions. -/
theorem quotient_step {R S : Matrix ι ι ℝ} (hR : R.PosSemidef) (hSpsd : S.PosSemidef)
    (A : Matrix ι ι ℝ) (hS : covStep A R S = S) (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ] (t : EuclideanSpace ℝ ι) :
    charFun (gaussStep A R μ) t / charFun (multivariateGaussian 0 S) t =
      charFun μ (euclid Aᵀ t) / charFun (multivariateGaussian 0 S) (euclid Aᵀ t) := by
  have hg : charFun (multivariateGaussian 0 S) t =
      charFun (multivariateGaussian 0 S) (euclid Aᵀ t) * gaussFactor R t := by
    have := charFun_gaussStep hR A (multivariateGaussian 0 S) t
    rwa [show gaussStep A R (multivariateGaussian 0 S) = multivariateGaussian 0 S from
      invariant_of_covStep_fixed hSpsd hR A hS] at this
  rw [charFun_gaussStep hR A μ t, hg,
    mul_div_mul_right _ _ (gaussFactor_ne_zero R t)]

/-- Iterating the step identity: the quotient after `n` steps is the initial quotient at
`(Aᵀ)^n t`. -/
theorem quotient_iterate {R S : Matrix ι ι ℝ} (hR : R.PosSemidef) (hSpsd : S.PosSemidef)
    (A : Matrix ι ι ℝ) (hS : covStep A R S = S) (μ₀ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ₀] (n : ℕ) (t : EuclideanSpace ℝ ι) :
    charFun ((gaussStep A R)^[n] μ₀) t / charFun (multivariateGaussian 0 S) t =
      charFun μ₀ (euclid ((Aᵀ) ^ n) t) /
        charFun (multivariateGaussian 0 S) (euclid ((Aᵀ) ^ n) t) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    have := isProbabilityMeasure_gaussStep_iterate A R μ₀ n
    rw [Function.iterate_succ_apply', quotient_step hR hSpsd A hS _ t, ih,
      euclid_transpose_pow_succ]

/-- The quotient is continuous at `0` with value `1`. -/
theorem tendsto_quotient_zero {S : Matrix ι ι ℝ} (hSpsd : S.PosSemidef)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    Tendsto (fun s => charFun μ s / charFun (multivariateGaussian 0 S) s) (𝓝 0) (𝓝 1) := by
  have h : Tendsto (fun s => charFun μ s / charFun (multivariateGaussian 0 S) s) (𝓝 0)
      (𝓝 (charFun μ 0 / charFun (multivariateGaussian 0 S) 0)) :=
    (continuous_charFun.tendsto 0).div (continuous_charFun.tendsto 0)
      (charFun_multivariateGaussian_ne_zero hSpsd 0 0)
  simpa [charFun_zero, probReal_univ] using h

/-! ### Uniqueness and attraction -/

/-- **Uniqueness of the invariant law (abstract form).** If `S ⪰ 0` is a fixed point of the
covariance step and `(Aᵀ)^n t → 0` for every `t`, then every invariant probability law of the
affine Gaussian step is `N(0, S)`. -/
theorem invariant_eq_multivariateGaussian_of_tendsto {R S : Matrix ι ι ℝ} (hR : R.PosSemidef)
    (hSpsd : S.PosSemidef) (A : Matrix ι ι ℝ) (hS : covStep A R S = S)
    (hdecay : ∀ t : EuclideanSpace ℝ ι, Tendsto (fun n => euclid ((Aᵀ) ^ n) t) atTop (𝓝 0))
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (hinv : gaussStep A R μ = μ) :
    μ = multivariateGaussian 0 S := by
  apply Measure.ext_of_charFun
  funext t
  have hiter : ∀ n : ℕ, (gaussStep A R)^[n] μ = μ := fun n =>
    Function.iterate_fixed hinv n
  have hq : ∀ n : ℕ, charFun μ t / charFun (multivariateGaussian 0 S) t =
      charFun μ (euclid ((Aᵀ) ^ n) t) /
        charFun (multivariateGaussian 0 S) (euclid ((Aᵀ) ^ n) t) := fun n => by
    have := quotient_iterate hR hSpsd A hS μ n t
    rwa [hiter n] at this
  have hlim : Tendsto (fun n => charFun μ (euclid ((Aᵀ) ^ n) t) /
      charFun (multivariateGaussian 0 S) (euclid ((Aᵀ) ^ n) t)) atTop (𝓝 1) :=
    (tendsto_quotient_zero hSpsd μ).comp (hdecay t)
  have hconst : charFun μ t / charFun (multivariateGaussian 0 S) t = 1 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr fun n => hq n) hlim
  exact (div_eq_one_iff_eq (charFun_multivariateGaussian_ne_zero hSpsd 0 t)).mp hconst

/-- **Attraction (abstract form).** From any initial probability law, the characteristic
functions of the chain converge pointwise to that of `N(0, S)`. -/
theorem tendsto_charFun_gaussStep_iterate {R S : Matrix ι ι ℝ} (hR : R.PosSemidef)
    (hSpsd : S.PosSemidef) (A : Matrix ι ι ℝ) (hS : covStep A R S = S)
    (hdecay : ∀ t : EuclideanSpace ℝ ι, Tendsto (fun n => euclid ((Aᵀ) ^ n) t) atTop (𝓝 0))
    (μ₀ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ₀] (t : EuclideanSpace ℝ ι) :
    Tendsto (fun n => charFun ((gaussStep A R)^[n] μ₀) t) atTop
      (𝓝 (charFun (multivariateGaussian 0 S) t)) := by
  have hg := charFun_multivariateGaussian_ne_zero hSpsd 0 t
  have hlim : Tendsto (fun n => charFun μ₀ (euclid ((Aᵀ) ^ n) t) /
      charFun (multivariateGaussian 0 S) (euclid ((Aᵀ) ^ n) t)) atTop (𝓝 1) :=
    (tendsto_quotient_zero hSpsd μ₀).comp (hdecay t)
  have h := hlim.mul_const (charFun (multivariateGaussian 0 S) t)
  rw [one_mul] at h
  refine h.congr fun n => ?_
  rw [← quotient_iterate hR hSpsd A hS μ₀ n t, div_mul_cancel₀ _ hg]

/-- The laws of the chain, bundled as probability measures. -/
noncomputable def gaussStepPM (A R : Matrix ι ι ℝ) (μ₀ : ProbabilityMeasure (EuclideanSpace ℝ ι))
    (n : ℕ) : ProbabilityMeasure (EuclideanSpace ℝ ι) :=
  ⟨(gaussStep A R)^[n] μ₀, isProbabilityMeasure_gaussStep_iterate A R μ₀ n⟩

/-- The centred Gaussian, bundled as a probability measure. -/
noncomputable def gaussianPM (S : Matrix ι ι ℝ) : ProbabilityMeasure (EuclideanSpace ℝ ι) :=
  ⟨multivariateGaussian 0 S, inferInstance⟩

/-- **Weak convergence (Lévy).** -/
theorem tendsto_gaussStepPM {R S : Matrix ι ι ℝ} (hR : R.PosSemidef)
    (hSpsd : S.PosSemidef) (A : Matrix ι ι ℝ) (hS : covStep A R S = S)
    (hdecay : ∀ t : EuclideanSpace ℝ ι, Tendsto (fun n => euclid ((Aᵀ) ^ n) t) atTop (𝓝 0))
    (μ₀ : ProbabilityMeasure (EuclideanSpace ℝ ι)) :
    Tendsto (gaussStepPM A R μ₀) atTop (𝓝 (gaussianPM S)) := by
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_
  have := tendsto_charFun_gaussStep_iterate hR hSpsd A hS hdecay (μ₀ : Measure _) t
  exact this

/-! ### The ULA chain -/

/-- **`N(0, Σ_ULA)` is the unique invariant probability law of the ULA step.** -/
theorem ulaCov_unique_invariant {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ]
    (hinv : gaussStep (ulaStep P h) ((2 * h) • (1 : Matrix ι ι ℝ)) μ = μ) :
    μ = multivariateGaussian 0 (ulaCov P h) := by
  have hPt : Pᵀ = P := by
    have := hP.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hev' : ∀ i, 0 < hP.1.eigenvalues i ∧ h * hP.1.eigenvalues i < 2 :=
    fun i => ⟨hP.eigenvalues_pos i, hev i⟩
  refine invariant_eq_multivariateGaussian_of_tendsto (Matrix.PosSemidef.one.smul (by positivity))
    (ulaCov_posDef hP h hh hev).posSemidef (ulaStep P h)
    (ulaCov_fixed P h hPt (isUnit_det_ulaDenom hP.1 h hev')) ?_ μ hinv
  intro t
  exact tendsto_euclid_pow_of_spectral (orthoOf hP.1) (ulaStep P h) _
    (orthoOf_transpose_mul hP.1) (orthoOf_mul_transpose hP.1) (ulaStep_eq_conj hP.1 h)
    (fun i => abs_one_sub_mul_lt_one hh (hev' i).1 (hev' i).2) t

/-- **The ULA chain converges in law to `N(0, Σ_ULA)` from any initial probability law.** -/
theorem tendsto_ula_iterate {P : Matrix ι ι ℝ} (hP : P.PosDef) {h : ℝ} (hh : 0 < h)
    (hev : ∀ i, h * hP.1.eigenvalues i < 2) (μ₀ : ProbabilityMeasure (EuclideanSpace ℝ ι)) :
    Tendsto (gaussStepPM (ulaStep P h) ((2 * h) • (1 : Matrix ι ι ℝ)) μ₀) atTop
      (𝓝 (gaussianPM (ulaCov P h))) := by
  have hPt : Pᵀ = P := by
    have := hP.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hev' : ∀ i, 0 < hP.1.eigenvalues i ∧ h * hP.1.eigenvalues i < 2 :=
    fun i => ⟨hP.eigenvalues_pos i, hev i⟩
  refine tendsto_gaussStepPM (Matrix.PosSemidef.one.smul (by positivity))
    (ulaCov_posDef hP h hh hev).posSemidef (ulaStep P h)
    (ulaCov_fixed P h hPt (isUnit_det_ulaDenom hP.1 h hev')) ?_ μ₀
  intro t
  exact tendsto_euclid_pow_of_spectral (orthoOf hP.1) (ulaStep P h) _
    (orthoOf_transpose_mul hP.1) (orthoOf_mul_transpose hP.1) (ulaStep_eq_conj hP.1 h)
    (fun i => abs_one_sub_mul_lt_one hh (hev' i).1 (hev' i).2) t

end Laplace.Sampler
