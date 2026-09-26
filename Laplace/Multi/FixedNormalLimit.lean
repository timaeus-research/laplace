/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ConditioningCertificate
import Laplace.Multi.NormalCone

/-!
# The fixed-normal conditioning limit: diverging tilts condition on the exposed face

Let `⟨a, S⟩ ≤ h` almost surely and let `F = {⟨a,S⟩ = h}` have positive mass. For a fixed `η`, the
tilts `P_{η − t a} ∝ e^{−⟨η,S⟩} e^{t⟨a,S⟩} ν` concentrate on `F` as `t → ∞`, and their limit is the
tilt `Q = e^{−⟨η,S⟩} 1_F ν / Z` of the conditioned law.

The key structural fact is that **conditioning commutes with tilting**
(`faceMeasure_tilted`): `(ν.tilted f)(· | F) = (ν(· | F)).tilted f`. Hence the conditional law of
`P_{η − ta}` on `F` is exactly `Q` for every `t` (`faceMeasure_familyMeasure_fixedNormal`), and
everything reduces to the face probability
`p_t = P_{η − ta}(F) = exp (t h + log ν(F) + Λ_F(−η) − Λ(−η + t a)) → 1`
(`real_familyMeasure_fixedNormal`, `tendsto_real_familyMeasure_fixedNormal_face`, from the landed
`tendsto_featCgf_ray`):

* every event probability and every bounded posterior expectation converges,
  `|P_{η−ta}(A) − Q(A)| ≤ 1 − p_t`, `|E_{P_{η−ta}} φ − E_Q φ| ≤ 2 L (1 − p_t)`
  (`tendsto_real_familyMeasure_fixedNormal`, `tendsto_integral_familyMeasure_fixedNormal`);
* the information distance is exact, `KL(Q ‖ P_{η−ta}) = −log p_t → 0`
  (`klDiv_familyMeasure_fixedNormal`, `tendsto_klDiv_familyMeasure_fixedNormal`).

The reverse divergence `KL(P_{η−ta} ‖ Q)` is infinite for every finite `t` when `ν(Fᶜ) > 0`, so
convergence is in total variation and in the divergence from the limit, not the other way round.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal

namespace Laplace.Multi

section TiltConditioning

variable {X : Type*} [MeasurableSpace X]

/-- Adding a constant to the tilt does nothing. -/
theorem tilted_add_const (μ : Measure X) (f : X → ℝ) (c : ℝ) :
    μ.tilted (fun x ↦ f x + c) = μ.tilted f := by
  unfold Measure.tilted
  congr 1
  funext x
  congr 1
  simp only [Real.exp_add, integral_mul_const]
  exact mul_div_mul_right _ _ (Real.exp_pos c).ne'

/-- **Conditioning commutes with tilting**: `(ν.tilted f)(· | F) = (ν(· | F)).tilted f`. -/
theorem faceMeasure_tilted (ν : Measure X) [IsProbabilityMeasure ν] {F : Set X}
    (hF : MeasurableSet F) (hF0 : ν F ≠ 0) {f : X → ℝ} (hfm : Measurable f)
    (hfi : Integrable (fun x ↦ Real.exp (f x)) ν) :
    faceMeasure (ν.tilted f) F = (faceMeasure ν F).tilted f := by
  have hZ : 0 < ∫ x, Real.exp (f x) ∂ν := integral_exp_pos hfi
  have hI : 0 < ∫ x in F, Real.exp (f x) ∂ν := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun x ↦ (Real.exp_pos _).le) hfi.integrableOn]
    have : Function.support (fun x ↦ Real.exp (f x)) = Set.univ := by
      ext x
      simp [(Real.exp_pos _).ne']
    rw [this, Set.univ_inter]
    exact pos_iff_ne_zero.2 hF0
  have hp : 0 < ν.real F := ENNReal.toReal_pos hF0 (measure_ne_top _ _)
  have hPF : ν.tilted f F =
      ENNReal.ofReal ((∫ x in F, Real.exp (f x) ∂ν) / ∫ x, Real.exp (f x) ∂ν) := by
    rw [tilted_apply_eq_ofReal_integral' f hF, integral_div]
  have hZF : ∫ x, Real.exp (f x) ∂faceMeasure ν F =
      (ν.real F)⁻¹ * ∫ x in F, Real.exp (f x) ∂ν := integral_faceMeasure ν F _
  have hprob : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hfi
  have hνF : ν F = ENNReal.ofReal (ν.real F) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hd₁ : Measurable fun x ↦ ENNReal.ofReal (Real.exp (f x) / ∫ x, Real.exp (f x) ∂ν) := by
    fun_prop
  have hd₂ : Measurable fun x ↦
      ENNReal.ofReal (Real.exp (f x) / ((ν.real F)⁻¹ * ∫ x in F, Real.exp (f x) ∂ν)) := by
    fun_prop
  have hind₁ : Measurable (F.indicator fun _ : X ↦ (ν.tilted f F)⁻¹) :=
    measurable_const.indicator hF
  have hind₂ : Measurable (F.indicator fun _ : X ↦ (ν F)⁻¹) := measurable_const.indicator hF
  have hLHS : faceMeasure (ν.tilted f) F =
      (ν.withDensity fun x ↦ ENNReal.ofReal (Real.exp (f x) / ∫ x, Real.exp (f x) ∂ν)).withDensity
        (F.indicator fun _ : X ↦ (ν.tilted f F)⁻¹) := by
    rw [faceMeasure_eq_withDensity (ν.tilted f) hF]
    rfl
  have hRHS : (faceMeasure ν F).tilted f =
      (ν.withDensity (F.indicator fun _ : X ↦ (ν F)⁻¹)).withDensity fun x ↦
        ENNReal.ofReal (Real.exp (f x) / ((ν.real F)⁻¹ * ∫ x in F, Real.exp (f x) ∂ν)) := by
    unfold Measure.tilted
    rw [hZF, faceMeasure_eq_withDensity ν hF]
  rw [hLHS, hRHS, ← withDensity_mul ν hd₁ hind₁, ← withDensity_mul ν hind₂ hd₂]
  refine withDensity_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [Pi.mul_apply]
  by_cases hx : x ∈ F
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hPF, hνF,
      ← ENNReal.ofReal_inv_of_pos (div_pos hI hZ),
      ← ENNReal.ofReal_mul (div_pos (Real.exp_pos _) hZ).le,
      ← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_mul (inv_pos.2 hp).le]
    congr 1
    field_simp
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero, zero_mul]

/-- Real decomposition of a set along a measurable set. -/
theorem real_inter_add_diff (P : Measure X) [IsFiniteMeasure P] (A : Set X) {F : Set X}
    (hF : MeasurableSet F) : P.real (A ∩ F) + P.real (A \ F) = P.real A := by
  rw [measureReal_def, measureReal_def, measureReal_def,
    ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), measure_inter_add_sdiff A hF]

/-- **Conditioning changes event probabilities by at most the missing mass**:
`|P(A) − P(A | F)| ≤ 1 − P(F)`. -/
theorem abs_real_sub_faceMeasure_real_le (P : Measure X) [IsProbabilityMeasure P] {F : Set X}
    (hF : MeasurableSet F) (hF0 : P F ≠ 0) (A : Set X) :
    |P.real A - (faceMeasure P F).real A| ≤ 1 - P.real F := by
  rw [faceMeasure_real_apply P hF]
  have hp : 0 < P.real F := ENNReal.toReal_pos hF0 (measure_ne_top _ _)
  have hp1 : P.real F ≤ 1 := by
    rw [← probReal_univ (μ := P)]
    exact measureReal_mono (Set.subset_univ _)
  have hdec := real_inter_add_diff P A hF
  have hq : P.real (A ∩ F) ≤ P.real F := measureReal_mono Set.inter_subset_right
  have hq0 : 0 ≤ P.real (A ∩ F) := measureReal_nonneg
  have hr0 : 0 ≤ P.real (A \ F) := measureReal_nonneg
  have hr : P.real (A \ F) ≤ 1 - P.real F := by
    rw [← probReal_univ (μ := P), ← measureReal_compl hF]
    exact measureReal_mono (Set.sdiff_subset_compl A F)
  have hqp : P.real (A ∩ F) / P.real F ≤ 1 := (div_le_one hp).2 hq
  have hqp0 : 0 ≤ P.real (A ∩ F) / P.real F := div_nonneg hq0 hp.le
  have hkey : P.real (A ∩ F) / P.real F - P.real (A ∩ F) =
      P.real (A ∩ F) / P.real F * (1 - P.real F) := by
    field_simp
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hqp (sub_nonneg.2 hp1)]
  · nlinarith [mul_nonneg hqp0 (sub_nonneg.2 hp1)]

/-- **Conditioning changes bounded expectations by at most twice the missing mass**:
`|E_P φ − E_{P(·|F)} φ| ≤ 2 L (1 − P(F))` for `|φ| ≤ L`. -/
theorem abs_integral_sub_faceMeasure_integral_le [Nonempty X] (P : Measure X)
    [IsProbabilityMeasure P]
    {F : Set X} (hF : MeasurableSet F) (hF0 : P F ≠ 0) {φ : X → ℝ} (hφm : Measurable φ) {L : ℝ}
    (hL : ∀ x, |φ x| ≤ L) :
    |(∫ x, φ x ∂P) - ∫ x, φ x ∂faceMeasure P F| ≤ 2 * L * (1 - P.real F) := by
  have hp : 0 < P.real F := ENNReal.toReal_pos hF0 (measure_ne_top _ _)
  have hp1 : P.real F ≤ 1 := by
    rw [← probReal_univ (μ := P)]
    exact measureReal_mono (Set.subset_univ _)
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL (Classical.arbitrary X))
  have hint : Integrable φ P := Integrable.of_bound hφm.aestronglyMeasurable L
    (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hL x)
  rw [integral_faceMeasure P F, ← integral_add_compl hF hint]
  have h1 : |∫ x in Fᶜ, φ x ∂P| ≤ L * (1 - P.real F) := by
    have := norm_setIntegral_le_of_norm_le_const (μ := P) (s := Fᶜ) (f := φ) (C := L)
      (measure_lt_top _ _) (fun x _ ↦ by rw [Real.norm_eq_abs]; exact hL x)
    rw [Real.norm_eq_abs, measureReal_compl hF, probReal_univ] at this
    exact this
  have h2 : |∫ x in F, φ x ∂P| ≤ L * P.real F := by
    have := norm_setIntegral_le_of_norm_le_const (μ := P) (s := F) (f := φ) (C := L)
      (measure_lt_top _ _) (fun x _ ↦ by rw [Real.norm_eq_abs]; exact hL x)
    rwa [Real.norm_eq_abs] at this
  have e : (∫ x in F, φ x ∂P) + (∫ x in Fᶜ, φ x ∂P) - (P.real F)⁻¹ * ∫ x in F, φ x ∂P =
      (∫ x in Fᶜ, φ x ∂P) - ((1 - P.real F) / P.real F) * ∫ x in F, φ x ∂P := by
    field_simp
    ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (div_nonneg (sub_nonneg.2 hp1) hp.le)]
  have h3 : (1 - P.real F) / P.real F * |∫ x in F, φ x ∂P| ≤ L * (1 - P.real F) := by
    calc (1 - P.real F) / P.real F * |∫ x in F, φ x ∂P|
        ≤ (1 - P.real F) / P.real F * (L * P.real F) :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg (sub_nonneg.2 hp1) hp.le)
      _ = L * (1 - P.real F) := by field_simp
  linarith

end TiltConditioning

section FixedNormal

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {a : J → ℝ}
  {h : ℝ} (hβ : ∀ᵐ x ∂ν, dirLoss S a x ≤ h) (hp : 0 < ν.real {x | dirLoss S a x = h})
  (η : J → ℝ)
include hS

omit [Nonempty X] [IsProbabilityMeasure ν] in
theorem measurableSet_face : MeasurableSet {x | dirLoss S a x = h} :=
  measurableSet_eq_fun (bdd_dirLoss hS a).1 measurable_const

omit [MeasurableSpace X] [Nonempty X] [IsProbabilityMeasure ν] hS in
theorem neg_one_mul_dirLoss_eq (t : ℝ) (x : X) :
    -1 * dirLoss S (η - t • a) x = dirLoss S (-η + t • a) x := by
  simp only [dirLoss, Finset.mul_sum, Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The family member as a Mathlib tilt of the law. -/
theorem familyMeasure_one_zero_eq_tilted (θ : J → ℝ) :
    familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 θ =
      ν.tilted (fun x ↦ -1 * dirLoss S θ x) := by
  rw [familyMeasure_eq_tilted measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos ν) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS one_pos θ,
    familyMeasure_one_zero]

include hp in
/-- **The conditional law of a fixed-normal tilt on its face is the tilt of the conditioned
law**, for every `t`. -/
theorem faceMeasure_familyMeasure_fixedNormal (t : ℝ) :
    faceMeasure (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η - t • a))
        {x | dirLoss S a x = h} =
      familyMeasure (faceMeasure ν {x | dirLoss S a x = h}) (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ))
        S 1 η := by
  have hF := measurableSet_face hS (a := a) (h := h)
  have hF0 : ν {x | dirLoss S a x = h} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have hPF := isProbabilityMeasure_faceMeasure ν hF0
  rw [familyMeasure_one_zero_eq_tilted hS ν, familyMeasure_one_zero_eq_tilted hS (faceMeasure ν _),
    faceMeasure_tilted ν hF hF0 ((bdd_dirLoss hS _).1.const_mul _)
      ((integrable_exp_mul_of_bdd ν (bdd_dirLoss hS _) (-1)).congr
        (Eventually.of_forall fun x ↦ rfl))]
  have hae : (fun x ↦ -1 * dirLoss S (η - t • a) x) =ᵐ[faceMeasure ν {x | dirLoss S a x = h}]
      fun x ↦ -1 * dirLoss S η x + t * h := by
    filter_upwards [ae_mem_faceMeasure ν hF] with x hx
    have hx' : dirLoss S a x = h := hx
    simp only [dirLoss_sub', dirLoss_smul, hx']
    ring
  rw [tilted_congr hae, tilted_add_const]

include hp in
/-- **The face probability of the fixed-normal tilt**:
`P_{η − ta}(F) = exp (t h + log ν(F) + Λ_F(−η) − Λ(−η + t a))`. -/
theorem real_familyMeasure_fixedNormal (t : ℝ) :
    (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η - t • a)).real
        {x | dirLoss S a x = h} =
      Real.exp (t * h + Real.log (ν.real {x | dirLoss S a x = h}) +
        featCgf (faceMeasure ν {x | dirLoss S a x = h}) S (-η) - featCgf ν S (-η + t • a)) := by
  have hF := measurableSet_face hS (a := a) (h := h)
  have hF0 : ν {x | dirLoss S a x = h} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have hPF := isProbabilityMeasure_faceMeasure ν hF0
  rw [familyMeasure_one_zero_eq_tilted hS ν, measureReal_def,
    tilted_apply_eq_ofReal_integral' _ hF, ENNReal.toReal_ofReal
    (integral_nonneg fun x ↦ div_nonneg (Real.exp_pos _).le (integral_nonneg fun x ↦
      (Real.exp_pos _).le)), integral_div]
  simp only [neg_one_mul_dirLoss_eq]
  have hnum : ∫ x in {x | dirLoss S a x = h}, Real.exp (dirLoss S (-η + t • a) x) ∂ν =
      Real.exp (t * h) * (ν.real {x | dirLoss S a x = h} *
        Real.exp (featCgf (faceMeasure ν {x | dirLoss S a x = h}) S (-η))) := by
    have hZF : 0 < ∫ x, Real.exp (dirLoss S (-η) x) ∂faceMeasure ν {x | dirLoss S a x = h} :=
      integral_exp_pos (integrable_exp_dirLoss (faceMeasure ν _) hS (-η))
    rw [featCgf, Real.exp_log hZF, integral_faceMeasure, mul_inv_cancel_left₀ hp.ne',
      ← integral_const_mul]
    refine setIntegral_congr_fun hF fun x hx ↦ ?_
    have hx' : dirLoss S a x = h := hx
    rw [← Real.exp_add]
    congr 1
    rw [← hx']
    simp only [dirLoss, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hden : ∫ x, Real.exp (dirLoss S (-η + t • a) x) ∂ν =
      Real.exp (featCgf ν S (-η + t • a)) := by
    rw [featCgf, Real.exp_log (integral_exp_pos (integrable_exp_dirLoss ν hS _))]
  rw [hnum, hden, Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_log hp]
  ring

include hβ hp in
/-- **The face probability tends to one.** -/
theorem tendsto_real_familyMeasure_fixedNormal_face :
    Tendsto (fun t : ℝ ↦ (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (η - t • a)).real {x | dirLoss S a x = h}) atTop (𝓝 1) := by
  have hray := tendsto_featCgf_ray ν hS hβ hp (-η)
  have hlim : Tendsto (fun t : ℝ ↦ t * h + Real.log (ν.real {x | dirLoss S a x = h}) +
      featCgf (faceMeasure ν {x | dirLoss S a x = h}) S (-η) - featCgf ν S (-η + t • a)) atTop
      (𝓝 0) := by
    have := (hray.sub_const (Real.log (ν.real {x | dirLoss S a x = h}) +
      featCgf (faceMeasure ν {x | dirLoss S a x = h}) S (-η))).neg
    rw [sub_self, neg_zero] at this
    refine this.congr fun t ↦ ?_
    ring
  have := Real.tendsto_exp_nhds_zero_nhds_one.comp hlim
  refine this.congr fun t ↦ ?_
  rw [Function.comp_apply, real_familyMeasure_fixedNormal hS ν hp η t]

include hβ hp in
/-- **Every event probability of the fixed-normal tilt converges** to that of the conditioned
tilt. -/
theorem tendsto_real_familyMeasure_fixedNormal (A : Set X) :
    Tendsto (fun t : ℝ ↦ (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (η - t • a)).real A) atTop
      (𝓝 ((familyMeasure (faceMeasure ν {x | dirLoss S a x = h}) (fun _ ↦ (1 : ℝ))
        (fun _ ↦ (0 : ℝ)) S 1 η).real A)) := by
  have hF := measurableSet_face hS (a := a) (h := h)
  have hp1 := tendsto_real_familyMeasure_fixedNormal_face hS ν hβ hp η
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : Tendsto (fun t : ℝ ↦ 1 - (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (η - t • a)).real {x | dirLoss S a x = h}) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub hp1
    rwa [sub_self] at this
  refine squeeze_zero' (Eventually.of_forall fun t ↦ norm_nonneg _)
    (Eventually.of_forall fun t ↦ ?_) hbound
  have hP := isProbabilityMeasure_familyMeasure (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ))
    measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const
    (M₀ := 0) (fun _ ↦ by simp) hS (t := 1) (η - t • a)
  have hPF0 : familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η - t • a)
      {x | dirLoss S a x = h} ≠ 0 := by
    intro h0
    have := real_familyMeasure_fixedNormal hS ν hp η t
    rw [measureReal_def, h0, ENNReal.toReal_zero] at this
    exact (Real.exp_pos _).ne' this.symm
  rw [Real.norm_eq_abs, ← faceMeasure_familyMeasure_fixedNormal hS ν hp η t]
  exact abs_real_sub_faceMeasure_real_le _ hF hPF0 A

include hβ hp in
/-- **Every bounded posterior expectation of the fixed-normal tilt converges** to that of the
conditioned tilt. -/
theorem tendsto_integral_familyMeasure_fixedNormal {φ : X → ℝ} (hφm : Measurable φ) {L : ℝ}
    (hL : ∀ x, |φ x| ≤ L) :
    Tendsto (fun t : ℝ ↦ ∫ x, φ x ∂familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
      (η - t • a)) atTop
      (𝓝 (∫ x, φ x ∂familyMeasure (faceMeasure ν {x | dirLoss S a x = h}) (fun _ ↦ (1 : ℝ))
        (fun _ ↦ (0 : ℝ)) S 1 η)) := by
  have hF := measurableSet_face hS (a := a) (h := h)
  have hp1 := tendsto_real_familyMeasure_fixedNormal_face hS ν hβ hp η
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : Tendsto (fun t : ℝ ↦ 2 * L * (1 - (familyMeasure ν (fun _ ↦ (1 : ℝ))
      (fun _ ↦ (0 : ℝ)) S 1 (η - t • a)).real {x | dirLoss S a x = h})) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hp1).const_mul (2 * L)
    rwa [sub_self, mul_zero] at this
  refine squeeze_zero' (Eventually.of_forall fun t ↦ norm_nonneg _)
    (Eventually.of_forall fun t ↦ ?_) hbound
  have hP := isProbabilityMeasure_familyMeasure (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ))
    measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const
    (M₀ := 0) (fun _ ↦ by simp) hS (t := 1) (η - t • a)
  have hPF0 : familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η - t • a)
      {x | dirLoss S a x = h} ≠ 0 := by
    intro h0
    have := real_familyMeasure_fixedNormal hS ν hp η t
    rw [measureReal_def, h0, ENNReal.toReal_zero] at this
    exact (Real.exp_pos _).ne' this.symm
  rw [Real.norm_eq_abs, ← faceMeasure_familyMeasure_fixedNormal hS ν hp η t]
  exact abs_integral_sub_faceMeasure_integral_le _ hF hPF0 hφm hL

include hp in
/-- **The exact information distance from the conditioned tilt to the fixed-normal tilt**:
`KL(Q ‖ P_{η − ta}) = −log P_{η − ta}(F)`. -/
theorem klDiv_familyMeasure_fixedNormal (t : ℝ) :
    klDiv (familyMeasure (faceMeasure ν {x | dirLoss S a x = h}) (fun _ ↦ (1 : ℝ))
        (fun _ ↦ (0 : ℝ)) S 1 η)
      (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η - t • a)) =
      ENNReal.ofReal (-Real.log ((familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1
        (η - t • a)).real {x | dirLoss S a x = h})) := by
  have hF := measurableSet_face hS (a := a) (h := h)
  have hF0 : ν {x | dirLoss S a x = h} ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have hPF := isProbabilityMeasure_faceMeasure ν hF0
  have hP := isProbabilityMeasure_familyMeasure (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ))
    measurable_const (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) measurable_const
    (M₀ := 0) (fun _ ↦ by simp) hS (t := 1) (η - t • a)
  have hQ := isProbabilityMeasure_familyMeasure (μ := faceMeasure ν {x | dirLoss S a x = h})
    (π := fun _ ↦ (1 : ℝ)) (L₀ := fun _ ↦ (0 : ℝ)) measurable_const (integrable_const 1)
    (fun _ ↦ one_pos) (one_integral_pos _) measurable_const (M₀ := 0) (fun _ ↦ by simp) hS
    (t := 1) η
  have hpt : 0 < (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η - t • a)).real
      {x | dirLoss S a x = h} := by
    rw [real_familyMeasure_fixedNormal hS ν hp η t]
    exact Real.exp_pos _
  have hcomm := faceMeasure_familyMeasure_fixedNormal hS ν hp η t
  rw [klDiv_eq_klDiv_faceMeasure_add _ hF hpt _ (by rw [hcomm]), hcomm, klDiv_self, zero_add]

include hβ hp in
/-- **The information distance from the conditioned tilt vanishes in the limit.** -/
theorem tendsto_klDiv_familyMeasure_fixedNormal :
    Tendsto (fun t : ℝ ↦ klDiv (familyMeasure (faceMeasure ν {x | dirLoss S a x = h})
        (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 η)
      (familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 (η - t • a))) atTop (𝓝 0) := by
  have hp1 := tendsto_real_familyMeasure_fixedNormal_face hS ν hβ hp η
  have hlog : Tendsto (fun t : ℝ ↦ -Real.log ((familyMeasure ν (fun _ ↦ (1 : ℝ))
      (fun _ ↦ (0 : ℝ)) S 1 (η - t • a)).real {x | dirLoss S a x = h})) atTop (𝓝 0) := by
    have := ((Real.continuousAt_log one_ne_zero).tendsto.comp hp1).neg
    rwa [Real.log_one, neg_zero] at this
  have := (ENNReal.continuous_ofReal.tendsto 0).comp hlog
  rw [ENNReal.ofReal_zero] at this
  refine this.congr fun t ↦ ?_
  rw [Function.comp_apply, klDiv_familyMeasure_fixedNormal hS ν hp η t]

end FixedNormal

end Laplace.Multi
