/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.MetropolisKernel

/-!
# Reversibility of the Metropolis–Hastings kernel

The Sanity on Sampling note's reference sampler is MALA preconditioned by `P⁻¹`: "the accept–reject
step makes the stationary law exact regardless". Tides `mala-invariance` and `mala-kernel` proved
the invariance (`mh_invariant`, `mh_invariant_law`, `bind_mhKernel`). The textbook reason behind it
is *reversibility*: the joint law `π(dx) K(x, dy)` is symmetric,

  `∫_A K(x, B) π(dx) = ∫_B K(x, A) π(dx)`   for all measurable `A, B`,

of which invariance is the case `A = X`. Here it is proved for the seabed's kernel
`mhKernelSet π q μ Z x E = (1/Z) ∫_E q(x,y) α(x,y) dμ(y) + 1_E(x)(1 − a(x))`:

* `mh_rectangle_mass`: `∫⁻ x in A, π(x) K(x, B) = Z⁻¹ ∬_{A×B} flux + ∫⁻_{A∩B} π(1 − a)`, with
  `flux(x, y) = min(π(x) q(x,y), π(y) q(y,x))` (`mhFlux`);
* `mh_reversible`: reversibility for the unnormalised target; `mh_invariant_of_reversible`
  recovers the invariance;
* `mh_reversible_law`, `mhKernel_reversible`: for the probability law `π/T` and for the
  `Kernel` object; `mhKernel_compProd_swap`: the joint law `ν ⊗ₘ K` is invariant under the swap;
* `mala_reversible`, `pmala_reversible` (and `_law`): the Gaussian instances.
-/

open MeasureTheory ENNReal Set ProbabilityTheory

namespace Laplace.Sampler

section MH

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
variable {π : X → ℝ} {q : X → X → ℝ}

/-- **The mass of a rectangle under `π ⊗ K`**: the accepted flux over `A × B` plus the rejection
mass on `A ∩ B`. -/
theorem mh_rectangle_mass (hπm : Measurable π) (hπ : ∀ x, 0 < π x)
    (hqm : Measurable (Function.uncurry q)) (hq : ∀ x y, 0 < q x y) {Z : ℝ≥0∞} (hZ0 : Z ≠ 0)
    {A B : Set X} (hB : MeasurableSet B) :
    ∫⁻ x in A, ENNReal.ofReal (π x) * mhKernelSet π q μ Z x B ∂μ =
      Z⁻¹ * (∫⁻ x in A, ∫⁻ y in B, mhFlux π q x y ∂μ ∂μ) +
        ∫⁻ x in A ∩ B, ENNReal.ofReal (π x) * (1 - mhAcceptMass π q μ Z x) ∂μ := by
  set w : X → X → ℝ≥0∞ := fun x y => ENNReal.ofReal (q x y * mhAccept π q x y) with hw
  have hwm : Measurable (Function.uncurry w) := measurable_mhWeight hπm hqm
  have hF : ∀ x y, ENNReal.ofReal (π x) * w x y = mhFlux π q x y := fun x y =>
    (mhFlux_eq hπ hq x y).symm
  have hZinv : Z⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hZ0
  have hπm' : Measurable fun x => ENNReal.ofReal (π x) := ENNReal.measurable_ofReal.comp hπm
  have hbBm : Measurable fun x => ∫⁻ y in B, w x y ∂μ := hwm.lintegral_prod_right
  have hmeas1 : Measurable fun x => ENNReal.ofReal (π x) * ((∫⁻ y in B, w x y ∂μ) / Z) :=
    hπm'.mul (hbBm.div_const Z)
  simp only [mhKernelSet, mul_add]
  rw [lintegral_add_left hmeas1]
  have e1 : ∀ x, ENNReal.ofReal (π x) * ((∫⁻ y in B, w x y ∂μ) / Z) =
      Z⁻¹ * ∫⁻ y in B, mhFlux π q x y ∂μ := by
    intro x
    rw [div_eq_mul_inv, mul_comm (∫⁻ y in B, w x y ∂μ) Z⁻¹, mul_left_comm,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    simp_rw [hF]
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ hZinv]
  have e2 : ∀ x, ENNReal.ofReal (π x) * B.indicator (fun x => 1 - mhAcceptMass π q μ Z x) x =
      B.indicator (fun x => ENNReal.ofReal (π x) * (1 - mhAcceptMass π q μ Z x)) x := by
    intro x
    by_cases hx : x ∈ B
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, mul_zero]
  simp_rw [e2]
  rw [lintegral_indicator hB, Measure.restrict_restrict hB, Set.inter_comm]

/-- **Reversibility (detailed balance) of the Metropolis–Hastings kernel** with respect to the
unnormalised target: `∫⁻ x in A, π(x) K(x, B) dμ = ∫⁻ x in B, π(x) K(x, A) dμ`. -/
theorem mh_reversible (hπm : Measurable π) (hπ : ∀ x, 0 < π x)
    (hqm : Measurable (Function.uncurry q)) (hq : ∀ x y, 0 < q x y) {Z : ℝ≥0∞} (hZ0 : Z ≠ 0)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ x in A, ENNReal.ofReal (π x) * mhKernelSet π q μ Z x B ∂μ =
      ∫⁻ x in B, ENNReal.ofReal (π x) * mhKernelSet π q μ Z x A ∂μ := by
  have hFm : Measurable (Function.uncurry (mhFlux π q)) := measurable_mhFlux hπm hqm
  rw [mh_rectangle_mass hπm hπ hqm hq hZ0 hB, mh_rectangle_mass hπm hπ hqm hq hZ0 hA,
    Set.inter_comm]
  congr 2
  have hswap : ∫⁻ x in A, ∫⁻ y in B, mhFlux π q x y ∂μ ∂μ =
      ∫⁻ y in B, ∫⁻ x in A, mhFlux π q x y ∂μ ∂μ :=
    lintegral_lintegral_swap (μ := μ.restrict A) (ν := μ.restrict B)
      (hFm.aemeasurable (μ := (μ.restrict A).prod (μ.restrict B)))
  rw [hswap]
  exact lintegral_congr fun y => lintegral_congr fun x => mhFlux_comm x y

/-- Invariance is the case `A = univ` of reversibility (a consistency check against
`mh_invariant`). -/
theorem mh_invariant_of_reversible (hπm : Measurable π) (hπ : ∀ x, 0 < π x)
    (hqm : Measurable (Function.uncurry q)) (hq : ∀ x y, 0 < q x y) {Z : ℝ≥0∞}
    (hZ : ∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂μ = Z) (hZ0 : Z ≠ 0) (hZtop : Z ≠ ∞) {E : Set X}
    (hE : MeasurableSet E) :
    ∫⁻ x, ENNReal.ofReal (π x) * mhKernelSet π q μ Z x E ∂μ =
      ∫⁻ x in E, ENNReal.ofReal (π x) ∂μ := by
  have h := mh_reversible (μ := μ) hπm hπ hqm hq hZ0 MeasurableSet.univ hE
  rw [Measure.restrict_univ] at h
  rw [h]
  refine lintegral_congr fun x => ?_
  have hK : mhKernelSet π q μ Z x univ = 1 := by
    simp only [mhKernelSet, Measure.restrict_univ, Set.indicator_univ]
    exact add_tsub_cancel_of_le (mhAcceptMass_le_one hq hZ hZ0 hZtop x)
  rw [hK, mul_one]

/-- **Reversibility for the probability law** `ν = π/T`:
`∫⁻ x in A, K(x, B) dν = ∫⁻ x in B, K(x, A) dν`. -/
theorem mh_reversible_law (hπm : Measurable π) (hπ : ∀ x, 0 < π x)
    (hqm : Measurable (Function.uncurry q)) (hq : ∀ x y, 0 < q x y) {Z : ℝ≥0∞} (hZ0 : Z ≠ 0)
    {T : ℝ≥0∞} (hT0 : T ≠ 0) {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ x in A, mhKernelSet π q μ Z x B ∂(mhTargetLaw π μ T) =
      ∫⁻ x in B, mhKernelSet π q μ Z x A ∂(mhTargetLaw π μ T) := by
  have hTinv : T⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hT0
  have hf : Measurable fun x => ENNReal.ofReal (π x) / T :=
    (ENNReal.measurable_ofReal.comp hπm).div_const T
  have key : ∀ {A B : Set X}, MeasurableSet A → MeasurableSet B →
      ∫⁻ x in A, mhKernelSet π q μ Z x B ∂(mhTargetLaw π μ T) =
        T⁻¹ * ∫⁻ x in A, ENNReal.ofReal (π x) * mhKernelSet π q μ Z x B ∂μ := by
    intro A B hA hB
    rw [mhTargetLaw, restrict_withDensity hA,
      lintegral_withDensity_eq_lintegral_mul _ hf (measurable_mhKernelSet hπm hqm Z hB)]
    simp only [Pi.mul_apply, div_eq_mul_inv]
    have e : ∀ x, ENNReal.ofReal (π x) * T⁻¹ * mhKernelSet π q μ Z x B =
        T⁻¹ * (ENNReal.ofReal (π x) * mhKernelSet π q μ Z x B) := fun x => by ring
    simp_rw [e]
    rw [lintegral_const_mul' _ _ hTinv]
  rw [key hA hB, key hB hA, mh_reversible hπm hπ hqm hq hZ0 hA hB]

/-- **Reversibility of the Markov kernel `mhKernel`** with respect to the probability law. -/
theorem mhKernel_reversible (hπm : Measurable π) (hπ : ∀ x, 0 < π x)
    (hqm : Measurable (Function.uncurry q)) (hq : ∀ x y, 0 < q x y) {Z : ℝ≥0∞} (hZ0 : Z ≠ 0)
    {T : ℝ≥0∞} (hT0 : T ≠ 0) {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ x in A, mhKernel hπm hqm μ hZ0 x B ∂(mhTargetLaw π μ T) =
      ∫⁻ x in B, mhKernel hπm hqm μ hZ0 x A ∂(mhTargetLaw π μ T) := by
  simp_rw [mhKernel_apply_set hπm hqm hZ0 _ hB, mhKernel_apply_set hπm hqm hZ0 _ hA]
  exact mh_reversible_law hπm hπ hqm hq hZ0 hT0 hA hB

/-- **The joint law `ν ⊗ K` is symmetric**: for the probability law `ν = π/T` and the Markov kernel
`K = mhKernel`, `(ν ⊗ₘ K).map Prod.swap = ν ⊗ₘ K` (reversibility as a statement about measures on
`X × X`; rectangles generate the product σ-algebra). -/
theorem mhKernel_compProd_swap (hπm : Measurable π) (hπ : ∀ x, 0 < π x)
    (hqm : Measurable (Function.uncurry q)) (hq : ∀ x y, 0 < q x y) {Z : ℝ≥0∞}
    (hZ : ∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂μ = Z) (hZ0 : Z ≠ 0) (hZtop : Z ≠ ∞) {T : ℝ≥0∞}
    (hT : ∫⁻ x, ENNReal.ofReal (π x) ∂μ = T) (hT0 : T ≠ 0) (hTtop : T ≠ ∞) :
    (mhTargetLaw π μ T ⊗ₘ mhKernel hπm hqm μ hZ0).map Prod.swap =
      mhTargetLaw π μ T ⊗ₘ mhKernel hπm hqm μ hZ0 := by
  have := isProbabilityMeasure_mhTargetLaw hπm hT hT0 hTtop
  have := isMarkovKernel_mhKernel hπm hqm hq hZ hZ0 hZtop
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨s, hs, t, ht, rfl⟩
    rw [Measure.map_apply measurable_swap (hs.prod ht), Set.preimage_swap_prod,
      Measure.compProd_apply_prod ht hs, Measure.compProd_apply_prod hs ht]
    exact mhKernel_reversible hπm hπ hqm hq hZ0 hT0 ht hs
  · rw [Measure.map_apply measurable_swap MeasurableSet.univ, Set.preimage_univ]

end MH

section Gaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Set (ι → ℝ)}

/-- **MALA is reversible** with respect to the Gaussian density with precision `P`. -/
theorem mala_reversible (P : Matrix ι ι ℝ) (h : ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    ∫⁻ x in A, ENNReal.ofReal (targetWeight P x) *
        mhKernelSet (targetWeight P) (propWeight (1 - h • P) ((1 / (4 * h)) • 1)) volume
          (propZ ((1 / (4 * h)) • (1 : Matrix ι ι ℝ))) x B =
      ∫⁻ x in B, ENNReal.ofReal (targetWeight P x) *
        mhKernelSet (targetWeight P) (propWeight (1 - h • P) ((1 / (4 * h)) • 1)) volume
          (propZ ((1 / (4 * h)) • (1 : Matrix ι ι ℝ))) x A :=
  mh_reversible (continuous_targetWeight P).measurable (targetWeight_pos P)
    (continuous_propWeight _ _).measurable (propWeight_pos _ _) (propZ_ne_zero _) hA hB

/-- **MALA is reversible** with respect to the Gaussian probability law. -/
theorem mala_reversible_law (P : Matrix ι ι ℝ) (h : ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    ∫⁻ x in A, mhKernelSet (targetWeight P) (propWeight (1 - h • P) ((1 / (4 * h)) • 1)) volume
        (propZ ((1 / (4 * h)) • (1 : Matrix ι ι ℝ))) x B ∂(gaussianLaw P) =
      ∫⁻ x in B, mhKernelSet (targetWeight P) (propWeight (1 - h • P) ((1 / (4 * h)) • 1)) volume
        (propZ ((1 / (4 * h)) • (1 : Matrix ι ι ℝ))) x A ∂(gaussianLaw P) :=
  mh_reversible_law (continuous_targetWeight P).measurable (targetWeight_pos P)
    (continuous_propWeight _ _).measurable (propWeight_pos _ _) (propZ_ne_zero _)
    (targetZ_ne_zero P) hA hB

/-- **pMALA is reversible** with respect to the Gaussian density with precision `P`. -/
theorem pmala_reversible (P : Matrix ι ι ℝ) (h : ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    ∫⁻ x in A, ENNReal.ofReal (targetWeight P x) *
        mhKernelSet (targetWeight P) (propWeight ((1 - h) • 1) ((1 / (4 * h)) • P)) volume
          (propZ ((1 / (4 * h)) • P)) x B =
      ∫⁻ x in B, ENNReal.ofReal (targetWeight P x) *
        mhKernelSet (targetWeight P) (propWeight ((1 - h) • 1) ((1 / (4 * h)) • P)) volume
          (propZ ((1 / (4 * h)) • P)) x A :=
  mh_reversible (continuous_targetWeight P).measurable (targetWeight_pos P)
    (continuous_propWeight _ _).measurable (propWeight_pos _ _) (propZ_ne_zero _) hA hB

/-- **pMALA is reversible** with respect to the Gaussian probability law. -/
theorem pmala_reversible_law (P : Matrix ι ι ℝ) (h : ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    ∫⁻ x in A, mhKernelSet (targetWeight P) (propWeight ((1 - h) • 1) ((1 / (4 * h)) • P)) volume
        (propZ ((1 / (4 * h)) • P)) x B ∂(gaussianLaw P) =
      ∫⁻ x in B, mhKernelSet (targetWeight P) (propWeight ((1 - h) • 1) ((1 / (4 * h)) • P)) volume
        (propZ ((1 / (4 * h)) • P)) x A ∂(gaussianLaw P) :=
  mh_reversible_law (continuous_targetWeight P).measurable (targetWeight_pos P)
    (continuous_propWeight _ _).measurable (propWeight_pos _ _) (propZ_ne_zero _)
    (targetZ_ne_zero P) hA hB

end Gaussian

end Laplace.Sampler
