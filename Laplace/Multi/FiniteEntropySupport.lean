/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PointwiseJets
import Laplace.Multi.DataReachability

/-!
# The completed family on a finite alphabet: probability vectors and maximal support

On a finite alphabet `X` with a full-support reference law `ν`:

* `vecMeasure p = count.withDensity (ofReal ∘ p)` turns a probability vector
  `p ∈ stdSimplex ℝ X` into a probability measure with `vecMeasure p {x} = p x` and
  `∫ f = Σ p x f x` (`vecMeasure_apply_singleton`, `integral_vecMeasure`);
  `vecMoment p = Σ_x p x S(x)` is its response;
* every measure is absolutely continuous with respect to `ν` and has finite relative
  entropy (`absolutelyContinuous_of_full_support`, `klDiv_ne_top_of_full_support`);
* the responses of probability vectors are exactly the moment polytope `conv S(X)`
  (`vecMoment_mem_convexHull`, `exists_stdSimplex_vecMoment_eq`), and **every point of the polytope
  has finite rate** (`genRate_ne_top_of_mem_convexHull`), so the completed family
  `q*(M) = responseProjection M` is defined on the whole polytope;
* **maximal support**: if any probability vector `r` with response `M` has `r x > 0`, then
  `q*(M) {x} > 0` (`responseProjection_singleton_pos`, from the Pythagorean identity
  `KL(r ‖ ν) = KL(r ‖ q*(M)) + 𝓘(M) < ∞`, hence `r ≪ q*(M)`);
* `qStarVec M x = q*(M) {x}` is the completed family as a probability vector
  (`qStarVec_mem_stdSimplex`, `vecMeasure_qStarVec`, `vecMoment_qStarVec`).
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section Vec

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

/-- The measure of a nonnegative vector, `count.withDensity (ofReal ∘ p)`. -/
noncomputable def vecMeasure (p : X → ℝ) : Measure X :=
  Measure.count.withDensity fun x ↦ ENNReal.ofReal (p x)

theorem vecMeasure_apply_singleton (p : X → ℝ) (x : X) :
    vecMeasure p {x} = ENNReal.ofReal (p x) := by
  unfold vecMeasure
  rw [withDensity_apply _ (measurableSet_singleton x), Measure.restrict_singleton,
    lintegral_smul_measure, lintegral_dirac, Measure.count_singleton, one_smul]

theorem vecMeasure_apply_univ [Fintype X] (p : X → ℝ) :
    vecMeasure p univ = ∑ x, ENNReal.ofReal (p x) := by
  unfold vecMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count, tsum_fintype]

theorem isProbabilityMeasure_vecMeasure [Fintype X] {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X) :
    IsProbabilityMeasure (vecMeasure p) :=
  ⟨by rw [vecMeasure_apply_univ, ← ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hp.1 x, hp.2,
    ENNReal.ofReal_one]⟩

theorem integral_vecMeasure [Fintype X] {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (f : X → ℝ) :
    ∫ x, f x ∂vecMeasure p = ∑ x, p x * f x := by
  unfold vecMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀ (measurable_of_finite _).aemeasurable
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) f, integral_count]
  exact Finset.sum_congr rfl fun x _ ↦ by rw [ENNReal.toReal_ofReal (hp x), smul_eq_mul]

/-- The response of a probability vector, `Σ_x p x S(x)`. -/
noncomputable def vecMoment [Fintype X] {J : Type*} (S : J → X → ℝ) (p : X → ℝ) : J → ℝ :=
  fun j ↦ ∑ x, p x * S j x

theorem integral_stat_vecMeasure [Fintype X] {J : Type*} (S : J → X → ℝ) {p : X → ℝ}
    (hp : ∀ x, 0 ≤ p x) :
    (fun j ↦ ∫ x, S j x ∂vecMeasure p) = vecMoment S p :=
  funext fun j ↦ integral_vecMeasure hp (S j)

omit [MeasurableSingletonClass X] in
/-- Every measure is absolutely continuous with respect to a full-support law. -/
theorem absolutelyContinuous_of_full_support {ν : Measure X} (hν : ∀ x, 0 < ν {x})
    (μ : Measure X) : μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk fun s _ hs ↦ ?_
  have he : s = ∅ := eq_empty_iff_forall_notMem.2 fun x hx ↦ (hν x).ne'
    (le_antisymm ((measure_mono (singleton_subset_iff.2 hx)).trans hs.le) zero_le)
  rw [he, measure_empty]

/-- Every finite measure has finite relative entropy with respect to a full-support law. -/
theorem klDiv_ne_top_of_full_support [Finite X] {ν : Measure X} (hν : ∀ x, 0 < ν {x})
    (μ : Measure X) [IsFiniteMeasure μ] : klDiv μ ν ≠ ⊤ :=
  klDiv_ne_top (absolutelyContinuous_of_full_support hν μ) Integrable.of_finite

end Vec

section Polytope

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
  {J : Type*} {S : J → X → ℝ}

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
theorem vecMoment_eq_sum_smul (p : X → ℝ) : vecMoment S p = ∑ x, p x • statPoint S x := by
  funext j
  simp [vecMoment, statPoint, Finset.sum_apply]

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- The response of a probability vector lies in the moment polytope. -/
theorem vecMoment_mem_convexHull [Finite J] {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X) :
    vecMoment S p ∈ convexHull ℝ (range (statPoint S)) := by
  cases nonempty_fintype J
  rw [← reachableCoeff_eq_convexHull, vecMoment_eq_sum_smul]
  exact mem_reachableCoeff_of_mem_stdSimplex _ hp

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- Every point of the moment polytope is the response of a probability vector. -/
theorem exists_stdSimplex_vecMoment_eq [Finite J] {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (range (statPoint S))) :
    ∃ p ∈ stdSimplex ℝ X, vecMoment S p = M := by
  cases nonempty_fintype J
  rw [← reachableCoeff_eq_convexHull] at hM
  obtain ⟨p, hp, rfl⟩ := hM
  exact ⟨p, hp, vecMoment_eq_sum_smul p⟩

variable [Nonempty X] [Fintype J] [Nonempty J] (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x})
include hS hν

omit [Fintype X] in
/-- **Every point of the moment polytope has finite rate** under a full-support law. -/
theorem genRate_ne_top_of_mem_convexHull [Finite X] {M : J → ℝ}
    (hM : M ∈ convexHull ℝ (range (statPoint S))) : genRate ν S M ≠ ⊤ := by
  cases nonempty_fintype X
  obtain ⟨p, hp, hpM⟩ := exists_stdSimplex_vecMoment_eq hM
  have := isProbabilityMeasure_vecMeasure hp
  rw [← entropyProj_eq_genRate hS ν M]
  refine ne_top_of_le_ne_top (klDiv_ne_top_of_full_support hν (vecMeasure p))
    (entropyProj_le_klDiv ν (vecMeasure p) ?_)
  rw [integral_stat_vecMeasure S hp.1, hpM]

omit [Fintype X] in
/-- **Maximal support**: the completed family charges every point charged by some law with the same
response. -/
theorem responseProjection_singleton_pos [Finite X] {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
    (ρ : Measure X) [IsProbabilityMeasure ρ] (hρM : (fun i ↦ ∫ x, S i x ∂ρ) = M) {x : X}
    (hx : 0 < ρ {x}) : 0 < responseProjection hS ν M {x} := by
  have hpy := (responseProjection_spec hS ν hfin).2.2.2 ρ inferInstance hρM
  have hne : klDiv ρ ν ≠ ⊤ := klDiv_ne_top_of_full_support hν ρ
  rw [hpy] at hne
  have hac : ρ ≪ responseProjection hS ν M := (klDiv_ne_top_iff.1 (ENNReal.add_ne_top.1 hne).1).1
  exact pos_iff_ne_zero.2 fun h0 ↦ hx.ne' (hac h0)

/-- Maximal support in vector form. -/
theorem responseProjection_singleton_pos_of_vec {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤)
    {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X) (hpM : vecMoment S p = M) {x : X} (hx : 0 < p x) :
    0 < responseProjection hS ν M {x} := by
  have := isProbabilityMeasure_vecMeasure hp
  refine responseProjection_singleton_pos hS ν hν hfin (vecMeasure p) ?_ ?_
  · rw [integral_stat_vecMeasure S hp.1, hpM]
  · rw [vecMeasure_apply_singleton]
    exact ENNReal.ofReal_pos.2 hx

omit hν in
/-- The completed family as a probability vector, `q*(M) x = q*(M) {x}`. -/
noncomputable def qStarVec (M : J → ℝ) (x : X) : ℝ := (responseProjection hS ν M).real {x}

omit hν in
theorem qStarVec_mem_stdSimplex {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) :
    qStarVec hS ν M ∈ stdSimplex ℝ X := by
  have := (responseProjection_spec hS ν hfin).1
  refine ⟨fun x ↦ measureReal_nonneg, ?_⟩
  unfold qStarVec
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

omit [Fintype X] hν in
theorem vecMeasure_qStarVec [Finite X] {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) :
    vecMeasure (qStarVec hS ν M) = responseProjection hS ν M := by
  have := (responseProjection_spec hS ν hfin).1
  refine Measure.ext_iff_singleton.2 fun x ↦ ?_
  rw [vecMeasure_apply_singleton]
  unfold qStarVec
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

omit hν in
theorem vecMoment_qStarVec {M : J → ℝ} (hfin : genRate ν S M ≠ ⊤) :
    vecMoment S (qStarVec hS ν M) = M := by
  rw [← integral_stat_vecMeasure S (qStarVec_mem_stdSimplex hS ν hfin).1,
    vecMeasure_qStarVec hS ν hfin]
  exact (responseProjection_spec hS ν hfin).2.1

end Polytope

end Laplace.Multi
