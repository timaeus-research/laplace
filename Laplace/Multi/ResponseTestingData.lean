/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.SharpAffinityTesting
import Laplace.Multi.ResponseMismatchResolution
import Laplace.Multi.TiltQuadratic

/-!
# The testing obstruction for data laws: unresolvable means unresolvable by every procedure

The resolution floors of `ResponseSamplingResolution` and `ResponseMismatchResolution` compare
one estimator's signal with its noise. This module turns "unresolvable" into a statement about
**every** decision procedure, off the model.

* **The affinity testing bound for data laws** (`testing_error_data_ge`): for `μ ≪ η` with
  Hellinger affinity `ρ = ∫ √(dμ/dη) dη`, every equal-prior test on `n` i.i.d. samples has error
  at least `(1 − √(1 − ρ^{2n}))/2` — the sharp affinity bound of `SharpAffinityTesting` with the
  root density `√(dμ/dη) ∈ L²(η)` and the constant root `1` for `η`;
* **Hellinger is below Kullback–Leibler** (`two_sub_two_mul_dataAffinity_le`):
  `2(1 − ρ) ≤ KL(μ‖η)`, from the pointwise `2r − 2√r ≤ r log r`;
* **the information form of the obstruction** (`testing_error_data_ge_of_klDiv`):
  every test has error at least `(1 − √(n · KL(μ‖η)))/2`;
* **the local alternatives along the covariance dual** (`tendsto_klDiv_tilted_dataDual_div_sq`,
  `hasDerivAt_dotJ_mean_tilted_dataDual`): the tilts `D_s ∝ e^{s⟨e*,S⟩} D` with `e* = Σ_D⁻¹ e`
  move the mean in the direction `e` at unit speed and carry information
  `KL(D_s‖D) = s² ⟨e, Σ_D⁻¹ e⟩ / 2 + o(s²)`; so the optimal signal-to-noise quadratic form of
  `ResponseMismatchResolution` and the all-procedures testing obstruction meet in the same
  quadratic form `⟨e, Σ_D⁻¹ e⟩`.
-/

open MeasureTheory InformationTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

section DataRoot

variable {Ω : Type*} [MeasurableSpace Ω] (μ η : Measure Ω) [IsProbabilityMeasure μ]
  [IsProbabilityMeasure η]

/-- The root density `√(dμ/dη)`. -/
noncomputable def rootFun (x : Ω) : ℝ := √((μ.rnDeriv η x).toReal)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure η] in
theorem measurable_rootFun : Measurable (rootFun μ η) :=
  Real.continuous_sqrt.measurable.comp (Measure.measurable_rnDeriv μ η).ennreal_toReal

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure η] in
theorem rootFun_nonneg (x : Ω) : 0 ≤ rootFun μ η x := Real.sqrt_nonneg _

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure η] in
theorem rootFun_sq (x : Ω) : rootFun μ η x ^ 2 = (μ.rnDeriv η x).toReal :=
  Real.sq_sqrt ENNReal.toReal_nonneg

variable {μ η} (hμη : μ ≪ η)
include hμη

/-- The density is integrable with integral `1`. -/
theorem integrable_rnDeriv_toReal : Integrable (fun x ↦ (μ.rnDeriv η x).toReal) η := by
  have := (integrable_rnDeriv_smul_iff hμη (f := fun _ : Ω ↦ (1 : ℝ))).2
    (integrable_const 1)
  simpa only [smul_eq_mul, mul_one] using this

theorem integral_rnDeriv_toReal : ∫ x, (μ.rnDeriv η x).toReal ∂η = 1 := by
  rw [Measure.integral_toReal_rnDeriv hμη, probReal_univ]

theorem memLp_rootFun : MemLp (rootFun μ η) 2 η := by
  refine (memLp_two_iff_integrable_sq (measurable_rootFun μ η).aestronglyMeasurable).2 ?_
  simp_rw [rootFun_sq]
  exact integrable_rnDeriv_toReal hμη

/-- The root density as an element of `L²(η)`. -/
noncomputable def dataRoot : Lp ℝ 2 η := (memLp_rootFun hμη).toLp _

theorem dataRoot_ae : (dataRoot hμη : Ω → ℝ) =ᵐ[η] rootFun μ η := (memLp_rootFun hμη).coeFn_toLp

theorem integral_mul_self_dataRoot : ∫ y, dataRoot hμη y * dataRoot hμη y ∂η = 1 := by
  rw [← integral_rnDeriv_toReal hμη]
  refine integral_congr_ae ?_
  filter_upwards [dataRoot_ae hμη] with y hy
  rw [hy, ← sq, rootFun_sq]

theorem norm_dataRoot : ‖dataRoot hμη‖ = 1 := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_eq_integral_mul_self, integral_mul_self_dataRoot,
    Real.sqrt_one]

/-- The root law of the root density is `μ`. -/
theorem rootLaw_dataRoot : rootLaw η (dataRoot hμη) = μ := by
  unfold rootLaw
  have h : (fun y ↦ ENNReal.ofReal (dataRoot hμη y * dataRoot hμη y)) =ᵐ[η] μ.rnDeriv η := by
    filter_upwards [dataRoot_ae hμη, Measure.rnDeriv_lt_top μ η] with y hy hlt
    rw [hy, ← sq, rootFun_sq, ENNReal.ofReal_toReal hlt.ne]
  rw [withDensity_congr_ae h]
  exact Measure.withDensity_rnDeriv_eq μ η hμη

omit hμη in
variable (η) in
/-- The constant root `1`, whose root law is the base law. -/
noncomputable def oneRoot : Lp ℝ 2 η := (memLp_const (1 : ℝ)).toLp _

omit hμη in
variable (η) in
theorem oneRoot_ae : (oneRoot η : Ω → ℝ) =ᵐ[η] fun _ ↦ (1 : ℝ) := (memLp_const 1).coeFn_toLp

omit hμη in
variable (η) in
theorem integral_mul_self_oneRoot : ∫ y, oneRoot η y * oneRoot η y ∂η = 1 := by
  have : ∫ y, oneRoot η y * oneRoot η y ∂η = ∫ _y, (1 : ℝ) ∂η := by
    refine integral_congr_ae ?_
    filter_upwards [oneRoot_ae η] with y hy
    rw [hy, mul_one]
  rw [this, integral_const, probReal_univ, one_smul]

omit hμη in
variable (η) in
theorem norm_oneRoot : ‖oneRoot η‖ = 1 := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_eq_integral_mul_self, integral_mul_self_oneRoot,
    Real.sqrt_one]

omit hμη in
variable (η) in
theorem rootLaw_oneRoot : rootLaw η (oneRoot η) = η := by
  unfold rootLaw
  have h : (fun y ↦ ENNReal.ofReal (oneRoot η y * oneRoot η y)) =ᵐ[η] (1 : Ω → ℝ≥0∞) := by
    filter_upwards [oneRoot_ae η] with y hy
    rw [hy, mul_one, ENNReal.ofReal_one, Pi.one_apply]
  rw [withDensity_congr_ae h, withDensity_one]

omit hμη in
variable (μ η) in
/-- **The Hellinger affinity** `ρ(μ, η) = ∫ √(dμ/dη) dη`. -/
noncomputable def dataAffinity : ℝ := ∫ x, rootFun μ η x ∂η

theorem integral_dataRoot_mul_oneRoot :
    ∫ y, dataRoot hμη y * oneRoot η y ∂η = dataAffinity μ η := by
  refine integral_congr_ae ?_
  filter_upwards [dataRoot_ae hμη, oneRoot_ae η] with y hy hy'
  rw [hy, hy', mul_one]

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure η] hμη in
variable (μ η) in
theorem dataAffinity_nonneg : 0 ≤ dataAffinity μ η :=
  integral_nonneg fun x ↦ rootFun_nonneg μ η x

theorem dataAffinity_le_one : dataAffinity μ η ≤ 1 := by
  have h := abs_real_inner_le_norm (dataRoot hμη) (oneRoot η)
  rw [inner_eq_integral_mul, integral_dataRoot_mul_oneRoot, norm_dataRoot, norm_oneRoot,
    mul_one] at h
  exact (le_abs_self _).trans h

/-- **The affinity testing bound for data laws**: every equal-prior test of `μ` against `η` on
`n` i.i.d. samples has error at least `(1 − √(1 − ρ^{2n}))/2`. -/
theorem testing_error_data_ge (n : ℕ) {φ : (Fin n → Ω) → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    (1 - √(1 - (dataAffinity μ η ^ n) ^ 2)) / 2 ≤
      ((∫ z, φ z ∂(Measure.pi fun _ : Fin n ↦ μ)) +
        ∫ z, (1 - φ z) ∂(Measure.pi fun _ : Fin n ↦ η)) / 2 := by
  have h := testing_error_ge_sqrt (Measure.pi fun _ : Fin n ↦ η)
    (norm_prodRoot η n (norm_dataRoot hμη)) (norm_prodRoot η n (norm_oneRoot η)) hφm hφ0 hφ1
  rw [rootLaw_prodRoot, rootLaw_prodRoot, rootLaw_dataRoot hμη, rootLaw_oneRoot] at h
  have e : ∫ z, prodRoot η n (dataRoot hμη) z * prodRoot η n (oneRoot η) z
      ∂(Measure.pi fun _ : Fin n ↦ η) = dataAffinity μ η ^ n := by
    rw [← inner_eq_integral_mul, inner_prodRoot, integral_dataRoot_mul_oneRoot hμη]
  rwa [e] at h

omit hμη in
variable (μ η) in
/-- The pointwise inequality `2r − 2√r ≤ r log r` for `r ≥ 0`. -/
theorem two_mul_sub_two_mul_sqrt_le_mul_log {r : ℝ} (hr : 0 ≤ r) :
    2 * r - 2 * √r ≤ r * Real.log r := by
  rcases eq_or_lt_of_le hr with h0 | hpos
  · rw [← h0, Real.sqrt_zero, Real.log_zero]
    ring_nf
    exact le_rfl
  · have hs : 0 < √r := Real.sqrt_pos.2 hpos
    have h := Real.log_le_sub_one_of_pos (inv_pos.2 hs)
    rw [Real.log_inv, Real.log_sqrt hr] at h
    have h2 : r * (2 - 2 * (√r)⁻¹) ≤ r * Real.log r :=
      mul_le_mul_of_nonneg_left (by linarith) hr
    have h3 : r * (√r)⁻¹ = √r := by rw [← div_eq_mul_inv, Real.div_sqrt]
    calc 2 * r - 2 * √r = r * (2 - 2 * (√r)⁻¹) := by rw [mul_sub, ← mul_assoc, mul_comm r 2,
          mul_assoc, h3]
      _ ≤ r * Real.log r := h2

/-- **Hellinger is below Kullback–Leibler**: `2(1 − ρ(μ,η)) ≤ KL(μ‖η)`. -/
theorem two_sub_two_mul_dataAffinity_le (hkl : klDiv μ η ≠ ⊤) :
    2 - 2 * dataAffinity μ η ≤ (klDiv μ η).toReal := by
  have hint : Integrable (llr μ η) μ := (klDiv_ne_top_iff.1 hkl).2
  rw [toReal_klDiv hμη hint, probReal_univ, probReal_univ, add_sub_cancel_right,
    ← integral_toReal_rnDeriv_mul hμη]
  have hint' : Integrable (fun x ↦ (μ.rnDeriv η x).toReal * llr μ η x) η :=
    (integrable_toReal_rnDeriv_mul_iff hμη).2 hint
  have hintr := integrable_rnDeriv_toReal hμη
  have hints : Integrable (rootFun μ η) η := (memLp_rootFun hμη).integrable one_le_two
  have hpt : ∀ x, 2 * (μ.rnDeriv η x).toReal - 2 * rootFun μ η x ≤
      (μ.rnDeriv η x).toReal * llr μ η x := fun x ↦
    two_mul_sub_two_mul_sqrt_le_mul_log ENNReal.toReal_nonneg
  have e : 2 - 2 * dataAffinity μ η =
      ∫ x, (2 * (μ.rnDeriv η x).toReal - 2 * rootFun μ η x) ∂η := by
    rw [integral_sub (hintr.const_mul 2) (hints.const_mul 2), integral_const_mul,
      integral_const_mul, integral_rnDeriv_toReal hμη]
    unfold dataAffinity
    ring
  rw [e]
  exact integral_mono ((hintr.const_mul 2).sub (hints.const_mul 2)) hint' hpt

/-- `1 − ρ^{2n} ≤ n · KL(μ‖η)`. -/
theorem one_sub_dataAffinity_pow_le (hkl : klDiv μ η ≠ ⊤) (n : ℕ) :
    1 - (dataAffinity μ η ^ n) ^ 2 ≤ n * (klDiv μ η).toReal := by
  have h0 := dataAffinity_nonneg μ η
  have h1 := dataAffinity_le_one hμη
  have hkl' := two_sub_two_mul_dataAffinity_le hμη hkl
  set ρ := dataAffinity μ η with hρ
  have hx : (1 : ℝ) - ρ ^ 2 ≤ (klDiv μ η).toReal := by nlinarith
  have hb := one_add_mul_le_pow (a := -(1 - ρ ^ 2)) (by nlinarith) n
  have e : (ρ ^ n) ^ 2 = (1 + -(1 - ρ ^ 2)) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    ring_nf
  rw [e]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left hx hn]

/-- **THE TESTING OBSTRUCTION IN INFORMATION FORM**: every equal-prior test of `μ` against `η` on
`n` i.i.d. samples has error at least `(1 − √(n KL(μ‖η)))/2`. -/
theorem testing_error_data_ge_of_klDiv (hkl : klDiv μ η ≠ ⊤) (n : ℕ) {φ : (Fin n → Ω) → ℝ}
    (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    (1 - √(n * (klDiv μ η).toReal)) / 2 ≤
      ((∫ z, φ z ∂(Measure.pi fun _ : Fin n ↦ μ)) +
        ∫ z, (1 - φ z) ∂(Measure.pi fun _ : Fin n ↦ η)) / 2 := by
  refine le_trans ?_ (testing_error_data_ge hμη n hφm hφ0 hφ1)
  have := Real.sqrt_le_sqrt (one_sub_dataAffinity_pow_le hμη hkl n)
  linarith

end DataRoot

section Tilt

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (D : Measure X) [IsProbabilityMeasure D]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] hS in
/-- The tilted alternatives are at finite information from the data law. -/
theorem klDiv_tilted_data_ne_top {f : X → ℝ} (hf : Bdd f) (s : ℝ) :
    klDiv (D.tilted fun x ↦ s * f x) D ≠ ⊤ :=
  klDiv_tilted_ne_top D (hf.const_mul s)

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] hS in
/-- **The testing obstruction for the local alternatives**: every test of `D_s` against `D` on
`n` samples has error at least `(1 − √(n KL(D_s‖D)))/2`. -/
theorem testing_error_tilted_ge {f : X → ℝ} (hf : Bdd f) (s : ℝ) (n : ℕ)
    {φ : (Fin n → X) → ℝ} (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    (1 - √(n * (klDiv (D.tilted fun x ↦ s * f x) D).toReal)) / 2 ≤
      ((∫ z, φ z ∂(Measure.pi fun _ : Fin n ↦ D.tilted fun x ↦ s * f x)) +
        ∫ z, (1 - φ z) ∂(Measure.pi fun _ : Fin n ↦ D)) / 2 := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd D (hf.const_mul s))
  exact testing_error_data_ge_of_klDiv (tilted_absolutelyContinuous D _)
    (klDiv_tilted_data_ne_top D hf s) n hφm hφ0 hφ1

omit [Nonempty J] [IsProbabilityMeasure ν] in
/-- **The information of the local alternatives along the covariance dual** is
`s² ⟨e, Σ_D⁻¹ e⟩ / 2 + o(s²)`. -/
theorem tendsto_klDiv_tilted_dataDual_div_sq (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u)
    (e : 𝕍) :
    Tendsto (fun s ↦ (klDiv (D.tilted fun x ↦
        s * dirLoss S (dataDual hS ν D hpd e : J → ℝ) x) D).toReal / s ^ 2)
      (𝓝[≠] 0) (𝓝 (dotJ (dataDual hS ν D hpd e : J → ℝ) (e : J → ℝ) / 2)) := by
  have h := tendsto_klDiv_tilted_div_sq D (bdd_dirLoss hS (dataDual hS ν D hpd e : J → ℝ))
  rw [← dataBilin_dataDual_self hS ν D hpd e]
  exact h

omit [Nonempty J] [IsProbabilityMeasure ν] in
/-- **The local alternatives along the covariance dual move the mean in the direction `e`**:
`d/ds ⟨u, m(D_s)⟩|_{s=0} = ⟨u, e⟩` for every `u ∈ W`. -/
theorem hasDerivAt_dotJ_mean_tilted_dataDual (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u)
    (e u : 𝕍) :
    HasDerivAt (fun s ↦ dotJ (u : J → ℝ)
        (fun i ↦ ∫ x, S i x ∂(D.tilted fun x ↦ s * dirLoss S (dataDual hS ν D hpd e : J → ℝ) x)))
      (dotJ (u : J → ℝ) (e : J → ℝ)) 0 := by
  set f := dirLoss S (dataDual hS ν D hpd e : J → ℝ) with hf
  have hfb : Bdd f := bdd_dirLoss hS _
  have h : ∀ i, HasDerivAt (fun s ↦ ∫ x, S i x ∂(D.tilted fun x ↦ s * f x))
      (∫ x, S i x * f x ∂(D.tilted fun x ↦ (0 : ℝ) * f x) -
        (∫ x, S i x ∂(D.tilted fun x ↦ (0 : ℝ) * f x)) *
          ∫ x, f x ∂(D.tilted fun x ↦ (0 : ℝ) * f x)) 0 :=
    fun i ↦ hasDerivAt_dataResponsePath hS D hfb i 0
  have h0 : ∀ g : X → ℝ, ∫ x, g x ∂(D.tilted fun x ↦ (0 : ℝ) * f x) = ∫ x, g x ∂D := fun g ↦ by
    have e : (fun x ↦ (0 : ℝ) * f x) = 0 := by
      funext x
      simp
    rw [e, tilted_zero]
  have hsum : HasDerivAt (fun s ↦ ∑ i, (u : J → ℝ) i *
      ∫ x, S i x ∂(D.tilted fun x ↦ s * f x)) (∑ i, (u : J → ℝ) i * lawCov D (S i) f) 0 := by
    refine HasDerivAt.fun_sum fun i _ ↦ ?_
    have := (h i).const_mul ((u : J → ℝ) i)
    simp only [h0] at this
    exact this
  have e1 : ∑ i, (u : J → ℝ) i * lawCov D (S i) f = dotJ (u : J → ℝ) (e : J → ℝ) := by
    rw [← lawCov_dirLoss_left hS D (u : J → ℝ) f hfb, hf, ← dataBilin_apply hS ν D,
      dataBilin_comm hS ν D, dataBilin_dataDual hS ν D hpd]
  rw [← e1]
  exact hsum

end Tilt

end Laplace.Multi
