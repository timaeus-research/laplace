/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.FrobeniusLaw

/-!
# The Gaussian four-moment table across eigendirections, and E4 for ULA

The whole-covariance law of `FrobeniusLaw` is conditional on the innovations forming a
`FourthMomentTable` across chains, times and directions. Here that hypothesis is discharged for
the ULA chain driven by independent standard Gaussian noise `ξ_{c,k}` and an orthonormal family of
directions `u_i` (the eigenvectors `orthoCol` of the precision):

* `orthonormal_orthoCol`: the columns of `orthoOf` are orthonormal;
* `covariance_inner_inner_of_stdGaussian`: `cov[⟪x, ξ⟫, ⟪y, ξ⟫] = ⟪x, y⟫` for `ξ ~ stdGaussian`;
* `iIndepFun_inner_window`: the projections `⟪u_i, ξ_{c,k}⟫` on a finite time window are jointly
  independent (jointly Gaussian with vanishing covariances,
  `HasGaussianLaw.iIndepFun_of_covariance_inner`);
* `iIndepFun_of_windows`: independence of an `ℕ`-indexed family from the independence of every
  finite window (the finite-subfamily formulation of `iIndepFun`);
* `fourthMomentTable_projNoise_dir`: the projected innovations `√(2h) ⟪u_i, ξ_{c,k}⟫` form a
  `FourthMomentTable` with `v = 2h`;
* `frobenius_ula_le`: **E4 for the ULA chain**: in the eigenbasis of the precision `Q`, with
  `0 < h pᵢ ≤ 1`, the pooled uncentred second-moment matrix satisfies
  `E ‖Σ̂ - E Σ̂‖_F² ≤ (1/(CN)) ∑ᵢⱼ (1 + δᵢⱼ) s₂ᵢ s₂ⱼ (1 + ρᵢρⱼ)/(1 - ρᵢρⱼ)`, `ρᵢ = 1 - h pᵢ`,
  `s₂ᵢ = 2h/(1 - ρᵢ²)` the ULA variances: "the covariance error follows `√(d/(CN))` with a prefactor
  set by the autocorrelation times".
-/

open MeasureTheory ProbabilityTheory Finset Matrix

namespace Laplace.Sampler

section Orthonormal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The eigenvector columns of `orthoOf hQ` are orthonormal. -/
theorem orthonormal_orthoCol {Q : Matrix ι ι ℝ} (hQ : Q.IsHermitian) :
    Orthonormal ℝ (orthoCol hQ) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := congrFun (congrFun (orthoOf_transpose_mul hQ) i) j
  rw [mul_apply, one_apply] at h
  simp only [transpose_apply] at h
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  simp only [orthoCol, WithLp.ofLp_toLp]
  rw [dotProduct_comm]
  exact h

end Orthonormal

section Gaussian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [IsProbabilityMeasure P] in
theorem hasGaussianLaw_of_map_stdGaussian {ξ : Ω → E} (hlaw : P.map ξ = stdGaussian E) :
    HasGaussianLaw ξ P := by
  have : IsGaussian (P.map ξ) := by rw [hlaw]; infer_instance
  exact IsGaussian.hasGaussianLaw

omit [IsProbabilityMeasure P] in
theorem memLp_two_inner_of_stdGaussian {ξ : Ω → E} (hmeas : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian E) (u : E) : MemLp (fun ω => inner ℝ u (ξ ω)) 2 P := by
  have h1 : MemLp (fun z => inner ℝ u z) 2 (P.map ξ) := by
    rw [hlaw]; exact memLp_inner_stdGaussian u
  rwa [memLp_map_measure_iff (g := fun z : E => inner ℝ u z)
    (innerSL ℝ u).continuous.aestronglyMeasurable hmeas.aemeasurable] at h1

omit [IsProbabilityMeasure P] in
/-- **Covariance of two projections of a standard Gaussian**: `cov[⟪x, ξ⟫, ⟪y, ξ⟫] = ⟪x, y⟫`. -/
theorem covariance_inner_inner_of_stdGaussian {ξ : Ω → E} (hmeas : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian E) (x y : E) :
    cov[fun ω => inner ℝ x (ξ ω), fun ω => inner ℝ y (ξ ω); P] = inner ℝ x y := by
  have h := covariance_map (μ := P) (Z := ξ) (X := fun z : E => inner ℝ x z)
    (Y := fun z : E => inner ℝ y z) (innerSL ℝ x).continuous.aestronglyMeasurable
    (innerSL ℝ y).continuous.aestronglyMeasurable hmeas.aemeasurable
  rw [Function.comp_def, Function.comp_def] at h
  rw [← h, hlaw, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id x y,
    covarianceBilin_stdGaussian]
  rfl

variable {ι : Type*}

omit [IsProbabilityMeasure P] in
/-- **Independence of the Gaussian projections on a finite time window**: for independent standard
Gaussian vectors `ξ_{c,k}` and an orthonormal family `u`, the scalars `⟪uᵢ, ξ_{c,k}⟫`,
`(c, k, i) ∈ Fin C × Fin T × ι`, are jointly independent. -/
theorem iIndepFun_inner_window [Finite ι] {C T : ℕ} (ξ : Fin C → ℕ → Ω → E)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian E)
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) {u : ι → E} (hu : Orthonormal ℝ u) :
    iIndepFun (fun a : Fin C × Fin T × ι => fun ω => inner ℝ (u a.2.2) (ξ a.1 a.2.1 ω)) P := by
  have hindW : iIndepFun (fun a : Fin C × Fin T => ξ a.1 a.2) P :=
    hind.precomp (g := fun a : Fin C × Fin T => ((a.1, (a.2 : ℕ)) : Fin C × ℕ))
      (fun a b hab => by
        simp only [Prod.ext_iff, Fin.val_inj] at hab
        exact Prod.ext hab.1 hab.2)
  have hG : ∀ a : Fin C × Fin T, HasGaussianLaw (ξ a.1 a.2) P :=
    fun a => hasGaussianLaw_of_map_stdGaussian (hlaw a.1 a.2)
  have hjoint : HasGaussianLaw (fun ω => fun a : Fin C × Fin T => ξ a.1 a.2 ω) P :=
    hindW.hasGaussianLaw hG
  let L : (Fin C × Fin T → E) →L[ℝ] (Fin C × Fin T × ι → ℝ) :=
    ContinuousLinearMap.pi fun a =>
      (innerSL ℝ (u a.2.2)).comp (ContinuousLinearMap.proj (a.1, a.2.1))
  have hY : HasGaussianLaw
      (fun ω => fun a : Fin C × Fin T × ι => inner ℝ (u a.2.2) (ξ a.1 a.2.1 ω)) P := by
    have := hjoint.map_of_measurable L L.continuous.measurable
    convert this using 2
    simp [L]
  refine hY.iIndepFun_of_covariance_inner fun a a' haa' x y => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  have e : ∀ (c : ℝ) (Z : Ω → ℝ), (fun ω => Z ω * c) = fun ω => c * Z ω :=
    fun c Z => funext fun ω => mul_comm _ _
  rw [e, e, covariance_const_mul_left, covariance_const_mul_right]
  by_cases hblock : (a.1, a.2.1) = (a'.1, a'.2.1)
  · have hij : a.2.2 ≠ a'.2.2 := by
      intro hij
      apply haa'
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hblock
      exact Prod.ext h1 (Prod.ext h2 hij)
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hblock
    simp only at h1 h2
    rw [h1, h2, covariance_inner_inner_of_stdGaussian (hmeas _ _) (hlaw _ _),
      hu.inner_eq_zero hij, mul_zero, mul_zero]
  · have hI : IndepFun (fun ω => inner ℝ (u a.2.2) (ξ a.1 a.2.1 ω))
        (fun ω => inner ℝ (u a'.2.2) (ξ a'.1 a'.2.1 ω)) P :=
      (hindW.indepFun hblock).comp (innerSL ℝ (u a.2.2)).continuous.measurable
        (innerSL ℝ (u a'.2.2)).continuous.measurable
    rw [hI.covariance_eq_zero (memLp_two_inner_of_stdGaussian (hmeas _ _) (hlaw _ _) _)
      (memLp_two_inner_of_stdGaussian (hmeas _ _) (hlaw _ _) _), mul_zero, mul_zero]

omit [IsProbabilityMeasure P] in
/-- **Independence from finite windows**: an `ℕ`-indexed family is independent as soon as every
finite time window is. -/
theorem iIndepFun_of_windows {C : ℕ} {f : Fin C × ℕ × ι → Ω → ℝ}
    (hf : ∀ T : ℕ, iIndepFun (fun a : Fin C × Fin T × ι => f (a.1, (a.2.1 : ℕ), a.2.2)) P) :
    iIndepFun f P := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  set T := S.sup (fun a => a.2.1) + 1 with hT
  have hTpos : 0 < T := Nat.succ_pos _
  have hlt : ∀ a ∈ S, a.2.1 < T :=
    fun a ha => Nat.lt_succ_of_le (Finset.le_sup (f := fun a : Fin C × ℕ × ι => a.2.1) ha)
  let e : Fin C × ℕ × ι → Fin C × Fin T × ι :=
    fun a => (a.1, ⟨a.2.1 % T, Nat.mod_lt _ hTpos⟩, a.2.2)
  have hre : ∀ a ∈ S, ((e a).1, ((e a).2.1 : ℕ), (e a).2.2) = a := fun a ha => by
    simp [e, Nat.mod_eq_of_lt (hlt a ha)]
  have hinj : ∀ a ∈ S, ∀ b ∈ S, e a = e b → a = b := fun a ha b hb hab => by
    rw [← hre a ha, ← hre b hb, hab]
  have h := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp (hf T)) (S.image e)
    (sets := fun a' => sets (a'.1, (a'.2.1 : ℕ), a'.2.2)) (fun a' ha' => by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha'
      rw [hre a ha]
      exact hsets a ha)
  have hInter : (⋂ a' ∈ S.image e,
      (fun ω => f (a'.1, (a'.2.1 : ℕ), a'.2.2) ω) ⁻¹' sets (a'.1, (a'.2.1 : ℕ), a'.2.2)) =
      ⋂ a ∈ S, f a ⁻¹' sets a := by
    rw [Finset.set_biInter_finset_image]
    exact Set.iInter₂_congr fun a ha => by rw [hre a ha]
  have hProd : (∏ a' ∈ S.image e,
      P ((fun ω => f (a'.1, (a'.2.1 : ℕ), a'.2.2) ω) ⁻¹' sets (a'.1, (a'.2.1 : ℕ), a'.2.2))) =
      ∏ a ∈ S, P (f a ⁻¹' sets a) := by
    rw [Finset.prod_image hinj]
    exact Finset.prod_congr rfl fun a ha => by rw [hre a ha]
  rw [hInter, hProd] at h
  exact h

end Gaussian

/-! ### The four-moment table and E4 for ULA -/

section ULA

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- **The projected innovations across chains, times and orthonormal directions form a
`FourthMomentTable`** with `v = 2h`. -/
theorem fourthMomentTable_projNoise_dir {h : ℝ} (hh : 0 ≤ h) {u : ι → EuclideanSpace ℝ ι}
    (hu : Orthonormal ℝ u) {C : ℕ} (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι)
    (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    FourthMomentTable (fun a : Fin C × ℕ × ι => projNoise h (u a.2.2) (ξ a.1) a.2.1) P
      (2 * h) where
  memLp a := (memLp_four_inner_of_stdGaussian (hmeas a.1 a.2.1) (hlaw a.1 a.2.1)
    (hu.1 a.2.2)).const_mul _
  meas a := measurable_const.mul
    ((innerSL ℝ (u a.2.2)).continuous.measurable.comp (hmeas a.1 a.2.1))
  indep := by
    have hI := iIndepFun_of_windows (P := P)
      (f := fun a : Fin C × ℕ × ι => fun ω => inner ℝ (u a.2.2) (ξ a.1 a.2.1 ω))
      (fun T => iIndepFun_inner_window ξ hmeas hlaw hind hu)
    exact hI.comp (fun _ z => Real.sqrt (2 * h) * z) (fun _ => measurable_const.mul measurable_id)
  m1 a := integral_projNoise h (u a.2.2) (ξ a.1) (hmeas a.1) (hlaw a.1) a.2.1
  m2 a := by
    rw [integral_projNoise_sq hh (u a.2.2) (ξ a.1) (hmeas a.1) (hlaw a.1) a.2.1, hu.1]
    ring
  m3 a := by
    unfold projNoise
    simp only [mul_pow]
    rw [integral_const_mul,
      integral_inner_pow_of_stdGaussian (hmeas a.1 a.2.1) (hlaw a.1 a.2.1) (hu.1 a.2.2) 3,
      integral_pow_three_gaussianReal, mul_zero]
  m4 a := by
    unfold projNoise
    simp only [mul_pow]
    rw [integral_const_mul,
      integral_inner_pow_of_stdGaussian (hmeas a.1 a.2.1) (hlaw a.1 a.2.1) (hu.1 a.2.2) 4,
      integral_pow_four_gaussianReal,
      show Real.sqrt (2 * h) ^ 4 = (2 * h) ^ 2 by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (by positivity)]]
    ring

/-- **E4 for the ULA chain.** In the eigenbasis of the precision `Q` (positive definite), for
independent standard Gaussian noise, `C` chains from the mode, draws `b+1, …, b+N` and steps
`0 < h pᵢ ≤ 1`, the pooled uncentred second-moment matrix of the projections satisfies
`E ‖Σ̂ - E Σ̂‖_F² ≤ (1/(CN)) ∑ᵢⱼ (1 + δᵢⱼ) s₂ᵢ s₂ⱼ (1 + ρᵢρⱼ)/(1 - ρᵢρⱼ)` with `ρᵢ = 1 - h pᵢ` and
`s₂ᵢ = 2h/(1 - ρᵢ²)` the ULA variances. -/
theorem frobenius_ula_le [DecidableEq ι] {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ} (hh : 0 < h)
    (hstab : ∀ i, h * hQ.1.eigenvalues i ≤ 1) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∫ ω, ∑ i, ∑ j,
        (pooledSecondMoment (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω))
            N b i j ω -
          ∫ ω', pooledSecondMoment
            (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) N b i j ω' ∂P) ^ 2
        ∂P ≤
      ∑ i, ∑ j, (if i = j then 2 else 1) / (C * N) *
        (2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
          (2 * h / (1 - (1 - h * hQ.1.eigenvalues j) ^ 2)) *
          (1 + (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j)) /
          (1 - (1 - h * hQ.1.eigenvalues i) * (1 - h * hQ.1.eigenvalues j))) := by
  have hQt : Qᵀ = Q := by
    have := hQ.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hx : (fun c i k ω => inner ℝ (orthoCol hQ.1 i) (ulaChain Q h (ξ c) k ω)) =
      fun c i k => realChain (1 - h * hQ.1.eigenvalues i)
        (fun m => projNoise h (orthoCol hQ.1 i) (ξ c) m) k := by
    funext c i k ω
    exact inner_ulaChain_eq_realChain hQt h (mulVec_orthoCol hQ.1 i) (ξ c) k ω
  rw [hx]
  exact frobenius_realChain_le (fun c k i => projNoise h (orthoCol hQ.1 i) (ξ c) k)
    (fourthMomentTable_projNoise_dir hh.le (orthonormal_orthoCol hQ.1) ξ hmeas hlaw hind)
    (by positivity) (fun i => 1 - h * hQ.1.eigenvalues i) (fun i => by linarith [hstab i])
    (fun i => by nlinarith [mul_pos hh (hQ.eigenvalues_pos i)]) hC hN b

end ULA

end Laplace.Sampler
