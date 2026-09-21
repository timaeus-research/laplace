/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib.Probability.Moments.Variance
import Laplace.Sampler.AR1Real
import Laplace.Sampler.RandomMap

/-!
# The ULA chain along an eigendirection is an AR(1) chain

The ULA chain from the mode, `w 0 = 0`, `w (k+1) = A w k + √(2h) ξ (k+1)` with `A = I - hQ` and
i.i.d. standard Gaussian `ξ k`, projected on a unit eigenvector `u` of the symmetric precision
`Q` (`Q u = p u`), is the realised AR(1) chain with coefficient `ρ = 1 - h p` and innovations
`η k = √(2h) ⟨u, ξ k⟩`, which are white noise with variance `2h`. The note's finite-chain
prediction (`expected_pooled_sample_variance`) therefore applies to the actual ULA chain along
every eigendirection, with the ULA variance `σ² = 2h/(1 - ρ²) = 1/(p (1 - h p/2))` as its
stationary value.
-/

open MeasureTheory ProbabilityTheory Matrix Finset

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The deterministic projection lemma -/

section Projection

variable {Ω : Type*}

/-- A vector chain from the origin driven by scaled innovations: `w 0 = 0`,
`w (k+1) = B (w k) + a • ξ (k+1)`. -/
noncomputable def vecChain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (B : E →L[ℝ] E)
    (a : ℝ) (ξ : ℕ → Ω → E) : ℕ → Ω → E
  | 0 => fun _ => 0
  | k + 1 => fun ω => B (vecChain B a ξ k ω) + a • ξ (k + 1) ω

/-- **Projection of a vector chain on a left eigenvector** is the realised AR(1) chain. -/
theorem inner_vecChain_eq_realChain {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : E →L[ℝ] E) (a : ℝ) (ξ : ℕ → Ω → E) {u : E} {ρ : ℝ}
    (hproj : ∀ z, inner ℝ u (B z) = ρ * inner ℝ u z) (k : ℕ) (ω : Ω) :
    inner ℝ u (vecChain B a ξ k ω) =
      realChain ρ (fun k ω => a * inner ℝ u (ξ k ω)) k ω := by
  induction k with
  | zero => simp [vecChain, realChain]
  | succ k ih =>
    simp only [vecChain, realChain, inner_add_right, real_inner_smul_right, hproj, ih]

end Projection

/-- The ULA chain from the mode driven by the noise `ξ`. -/
noncomputable def ulaChain {Ω : Type*} (Q : Matrix ι ι ℝ) (h : ℝ)
    (ξ : ℕ → Ω → EuclideanSpace ℝ ι) : ℕ → Ω → EuclideanSpace ℝ ι :=
  vecChain (euclid (ulaStep Q h)) (Real.sqrt (2 * h)) ξ

/-- The projected innovations `√(2h) ⟨u, ξ k⟩`. -/
noncomputable def projNoise {Ω : Type*} (h : ℝ) (u : EuclideanSpace ℝ ι)
    (ξ : ℕ → Ω → EuclideanSpace ℝ ι) (k : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (2 * h) * inner ℝ u (ξ k ω)

/-- Along an eigenvector of a symmetric `Q`, the ULA step scales the projection by `1 - h p`. -/
theorem inner_euclid_ulaStep {Q : Matrix ι ι ℝ} (hsym : Qᵀ = Q) (h : ℝ) {u : EuclideanSpace ℝ ι}
    {p : ℝ} (hu : Q *ᵥ u.ofLp = p • u.ofLp) (z : EuclideanSpace ℝ ι) :
    inner ℝ u (euclid (ulaStep Q h) z) = (1 - h * p) * inner ℝ u z := by
  rw [inner_toEuclideanCLM, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, ulaStep,
    sub_mulVec, one_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, dotProduct_mulVec,
    ← mulVec_transpose, hsym, hu, smul_dotProduct, dotProduct_comm]
  simp only [smul_eq_mul]
  ring

/-- **The ULA chain along an eigendirection is the realised AR(1) chain** with `ρ = 1 - h p`. -/
theorem inner_ulaChain_eq_realChain {Ω : Type*} {Q : Matrix ι ι ℝ} (hsym : Qᵀ = Q) (h : ℝ)
    {u : EuclideanSpace ℝ ι} {p : ℝ} (hu : Q *ᵥ u.ofLp = p • u.ofLp)
    (ξ : ℕ → Ω → EuclideanSpace ℝ ι) (k : ℕ) (ω : Ω) :
    inner ℝ u (ulaChain Q h ξ k ω) = realChain (1 - h * p) (projNoise h u ξ) k ω :=
  inner_vecChain_eq_realChain _ _ ξ (inner_euclid_ulaStep hsym h hu) k ω

/-! ### Gaussian second moments of a projection -/

section Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem memLp_inner_stdGaussian (u : E) : MemLp (fun z => inner ℝ u z) 2 (stdGaussian E) := by
  have h : MemLp id 2 (stdGaussian E) := IsGaussian.memLp_two_id
  have h2 := (innerSL ℝ u).comp_memLp' h
  simpa [innerSL_apply_apply] using h2

theorem integral_innerSL_stdGaussian (u : E) : ∫ z, innerSL ℝ u z ∂stdGaussian E = 0 := by
  have h := (innerSL ℝ u).integral_comp_comm (μ := stdGaussian E) (φ := id)
    IsGaussian.integrable_id
  simp only [id, integral_id_stdGaussian, map_zero] at h
  exact h

theorem integral_inner_stdGaussian (u : E) : ∫ z, inner ℝ u z ∂stdGaussian E = 0 := by
  simpa [innerSL_apply_apply] using integral_innerSL_stdGaussian u

theorem integral_inner_sq_stdGaussian (u : E) :
    ∫ z, inner ℝ u z ^ 2 ∂stdGaussian E = ‖u‖ ^ 2 := by
  have hvar := variance_dual_stdGaussian (innerSL ℝ u)
  rw [innerSL_apply_norm, variance_of_integral_eq_zero
    (innerSL ℝ u).continuous.measurable.aemeasurable (integral_innerSL_stdGaussian u)] at hvar
  simpa [innerSL_apply_apply] using hvar

end Gaussian

/-! ### Transfer through the law of the noise -/

section Transfer

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [DecidableEq ι] [IsProbabilityMeasure P] in
theorem memLp_projNoise (h : ℝ) (u : EuclideanSpace ℝ ι) (ξ : ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ k, Measurable (ξ k))
    (hlaw : ∀ k, P.map (ξ k) = stdGaussian (EuclideanSpace ℝ ι)) (k : ℕ) :
    MemLp (projNoise h u ξ k) 2 P := by
  have h1 : MemLp (fun z => inner ℝ u z) 2 (P.map (ξ k)) := by
    rw [hlaw k]; exact memLp_inner_stdGaussian u
  rw [memLp_map_measure_iff (g := fun z : EuclideanSpace ℝ ι => inner ℝ u z)
    (innerSL ℝ u).continuous.aestronglyMeasurable (hmeas k).aemeasurable] at h1
  unfold projNoise
  exact h1.const_mul _

omit [DecidableEq ι] [IsProbabilityMeasure P] in
theorem integral_projNoise (h : ℝ) (u : EuclideanSpace ℝ ι) (ξ : ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ k, Measurable (ξ k))
    (hlaw : ∀ k, P.map (ξ k) = stdGaussian (EuclideanSpace ℝ ι)) (k : ℕ) :
    ∫ ω, projNoise h u ξ k ω ∂P = 0 := by
  unfold projNoise
  rw [integral_const_mul]
  have h1 : ∫ ω, inner ℝ u (ξ k ω) ∂P = ∫ z, inner ℝ u z ∂(P.map (ξ k)) := by
    rw [integral_map (f := fun z : EuclideanSpace ℝ ι => inner ℝ u z) (hmeas k).aemeasurable
      (innerSL ℝ u).continuous.aestronglyMeasurable]
  rw [h1, hlaw k, integral_inner_stdGaussian, mul_zero]

omit [DecidableEq ι] [IsProbabilityMeasure P] in
theorem integral_projNoise_sq {h : ℝ} (hh : 0 ≤ h) (u : EuclideanSpace ℝ ι)
    (ξ : ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ k, Measurable (ξ k))
    (hlaw : ∀ k, P.map (ξ k) = stdGaussian (EuclideanSpace ℝ ι)) (k : ℕ) :
    ∫ ω, projNoise h u ξ k ω ^ 2 ∂P = 2 * h * ‖u‖ ^ 2 := by
  unfold projNoise
  simp only [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * h)]
  rw [integral_const_mul]
  have h1 : ∫ ω, inner ℝ u (ξ k ω) ^ 2 ∂P = ∫ z, inner ℝ u z ^ 2 ∂(P.map (ξ k)) := by
    rw [integral_map (f := fun z : EuclideanSpace ℝ ι => inner ℝ u z ^ 2) (hmeas k).aemeasurable
      ((innerSL ℝ u).continuous.pow 2).aestronglyMeasurable]
  rw [h1, hlaw k, integral_inner_sq_stdGaussian]

omit [DecidableEq ι] in
/-- **White noise**: the projected innovations of mutually independent standard Gaussians have the
moment table `∫ η j η k = 2h ‖u‖² δ_jk`. -/
theorem integral_projNoise_mul {h : ℝ} (hh : 0 ≤ h) (u : EuclideanSpace ℝ ι)
    (ξ : ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ k, Measurable (ξ k))
    (hlaw : ∀ k, P.map (ξ k) = stdGaussian (EuclideanSpace ℝ ι)) (hind : iIndepFun ξ P) (j k : ℕ) :
    ∫ ω, projNoise h u ξ j ω * projNoise h u ξ k ω ∂P =
      if j = k then 2 * h * ‖u‖ ^ 2 else 0 := by
  have hindep : ∀ a a', a ≠ a' → IndepFun (projNoise h u ξ a) (projNoise h u ξ a') P := by
    intro a a' haa'
    have := (hind.indepFun haa').comp
      (φ := fun z : EuclideanSpace ℝ ι => Real.sqrt (2 * h) * inner ℝ u z)
      (ψ := fun z : EuclideanSpace ℝ ι => Real.sqrt (2 * h) * inner ℝ u z)
      (measurable_const.mul (innerSL ℝ u).continuous.measurable)
      (measurable_const.mul (innerSL ℝ u).continuous.measurable)
    exact this
  rw [white_of_indep (projNoise h u ξ) (memLp_projNoise h u ξ hmeas hlaw)
    (integral_projNoise h u ξ hmeas hlaw) (integral_projNoise_sq hh u ξ hmeas hlaw) hindep j k]

end Transfer

/-! ### The finite-chain prediction for the actual ULA chain -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The note's finite-chain prediction holds for the ULA chain along a unit eigenvector.**
`C` chains driven by mutually independent standard Gaussian noise, started at the mode; the
expectation of the pooled sample variance of the projections on a unit eigenvector `u` of the
symmetric precision `Q` (`Q u = p u`) over the draws `b+1, …, b+N` is the AR(1) closed form with
`ρ = 1 - h p` and innovation variance `v = 2h`. -/
theorem expected_pooled_sample_variance_ula {Q : Matrix ι ι ℝ} (hsym : Qᵀ = Q) {h : ℝ} (hh : 0 ≤ h)
    {u : EuclideanSpace ℝ ι} {p : ℝ} (hu : Q *ᵥ u.ofLp = p • u.ofLp) (hunit : ‖u‖ = 1)
    (hρ : (1 - h * p) ^ 2 ≠ 1) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∫ ω, ((1 / ((C : ℝ) * N)) *
          ∑ c, ∑ i ∈ range N, inner ℝ u (ulaChain Q h (ξ c) (b + 1 + i) ω) ^ 2 -
        ((1 / ((C : ℝ) * N)) *
          ∑ c, ∑ i ∈ range N, inner ℝ u (ulaChain Q h (ξ c) (b + 1 + i) ω)) ^ 2) ∂P =
      (2 * h) / (1 - (1 - h * p) ^ 2) * (N - ∑ i ∈ range N, (1 - h * p) ^ (2 * (b + 1 + i))) / N -
        (2 * h) / (1 - (1 - h * p) ^ 2) *
          ((N + 2 * ∑ m ∈ range N, ((N : ℝ) - (m + 1)) * (1 - h * p) ^ (m + 1)) -
            (∑ i ∈ range N, (1 - h * p) ^ (b + 1 + i)) ^ 2) / (C * N ^ 2) := by
  simp_rw [inner_ulaChain_eq_realChain hsym h hu]
  refine expected_pooled_sample_variance (1 - h * p) hC hN b hρ (fun c => projNoise h u (ξ c))
    (fun c k => memLp_projNoise h u (ξ c) (hmeas c) (hlaw c) k) ?_
  intro c c' j k
  have hindep : ∀ a a' : Fin C × ℕ, a ≠ a' →
      IndepFun (projNoise h u (ξ a.1) a.2) (projNoise h u (ξ a'.1) a'.2) P := by
    intro a a' haa'
    exact (hind.indepFun haa').comp
      (φ := fun z : EuclideanSpace ℝ ι => Real.sqrt (2 * h) * inner ℝ u z)
      (ψ := fun z : EuclideanSpace ℝ ι => Real.sqrt (2 * h) * inner ℝ u z)
      (measurable_const.mul (innerSL ℝ u).continuous.measurable)
      (measurable_const.mul (innerSL ℝ u).continuous.measurable)
  have := white_of_indep (v := 2 * h) (fun a : Fin C × ℕ => projNoise h u (ξ a.1) a.2)
    (fun a => memLp_projNoise h u (ξ a.1) (hmeas a.1) (hlaw a.1) a.2)
    (fun a => integral_projNoise h u (ξ a.1) (hmeas a.1) (hlaw a.1) a.2)
    (fun a => by rw [integral_projNoise_sq hh u (ξ a.1) (hmeas a.1) (hlaw a.1) a.2, hunit]; ring)
    hindep (c, j) (c', k)
  simpa [Prod.ext_iff] using this

/-- The stationary variance of the eigendirection chain is the ULA variance. -/
theorem ula_variance_eq {h p : ℝ} (hh : 0 < h) (hp : 0 < p) (hhp : h * p < 2) :
    (2 * h) / (1 - (1 - h * p) ^ 2) = 1 / (p * (1 - h * p / 2)) := by
  have h1 : 1 - (1 - h * p) ^ 2 ≠ 0 := by nlinarith [mul_pos hh hp]
  have h2 : p * (1 - h * p / 2) ≠ 0 := mul_ne_zero hp.ne' (by linarith)
  rw [div_eq_div_iff h1 h2]
  ring

/-! ### Eigenvectors from the spectral packaging -/

/-- The `i`-th column of `orthoOf hQ`, as a Euclidean vector. -/
noncomputable def orthoCol {Q : Matrix ι ι ℝ} (hQ : Q.IsHermitian) (i : ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun j => orthoOf hQ j i

theorem mul_orthoOf_eq {Q : Matrix ι ι ℝ} (hQ : Q.IsHermitian) :
    Q * orthoOf hQ = orthoOf hQ * diagonal hQ.eigenvalues := by
  have h : Q * orthoOf hQ =
      (orthoOf hQ * diagonal hQ.eigenvalues * (orthoOf hQ)ᵀ) * orthoOf hQ := by
    rw [← spectral_real hQ]
  rw [h, Matrix.mul_assoc, orthoOf_transpose_mul hQ, Matrix.mul_one]

/-- The columns of `orthoOf hQ` are eigenvectors of `Q`. -/
theorem mulVec_orthoCol {Q : Matrix ι ι ℝ} (hQ : Q.IsHermitian) (i : ι) :
    Q *ᵥ (orthoCol hQ i).ofLp = hQ.eigenvalues i • (orthoCol hQ i).ofLp := by
  funext j
  have h := congrFun (congrFun (mul_orthoOf_eq hQ) j) i
  rw [mul_apply, mul_diagonal] at h
  simp only [orthoCol, WithLp.ofLp_toLp, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [h, mul_comm]

/-- The columns of `orthoOf hQ` are unit vectors. -/
theorem norm_orthoCol {Q : Matrix ι ι ℝ} (hQ : Q.IsHermitian) (i : ι) : ‖orthoCol hQ i‖ = 1 := by
  have h := congrFun (congrFun (orthoOf_transpose_mul hQ) i) i
  rw [mul_apply, one_apply_eq] at h
  simp only [transpose_apply] at h
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simpa [orthoCol, Real.norm_eq_abs, sq_abs, sq] using h

end Main

end Laplace.Sampler
