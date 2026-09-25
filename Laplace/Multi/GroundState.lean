/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ThermalTransport
import Laplace.Multi.FaceTotalVariation
import Laplace.Multi.InteriorThreshold

/-!
# The zero-temperature endpoint of the thermal journey

Fix `a` and let `H_a = L₀ + a·R` (`affLoss L₀ R a`), `α` its essential lower bound under the prior
and `G = {H_a = α}` the ground-state event. As `t → ∞` the family member `P_{t,a} ∝ e^{−t H_a} π`
concentrates on the ground state:

* **the energy relaxes to the ground level**, `⟨H_a⟩_{t,a} → α`, under the essential-infimum
  condition `π(H_a < α + ε) > 0` for every `ε > 0` (`tendsto_energy_temp`; through the
  one-feature family `R' = H_a` on the index `Unit`, `familyMeasure_unit`);
* on a **positive-mass ground state** every bounded observable converges to its conditional prior
  expectation (`tendsto_priorExp_temp_face`), `P_{t,a}(G) → 1` and
  `|P_{t,a}(A) − π̄(A | G)| ≤ 1 − P_{t,a}(G)`, so `P_{t,a} → π̄_G` in total variation
  (`tendsto_familyMeasure_real_temp_face`, `abs_familyMeasure_real_sub_priorFace_le`);
* **the information distance to the prior converges to the entry cost of the ground state**:
  `KL(P_{t,a} ‖ π̄) → −log π̄(G) = KL(π̄_G ‖ π̄)` (`tendsto_klDiv_prior_temp_face`,
  `tendsto_klDiv_prior_temp_face'`), via the identification of the seabed's mixture divergence
  with minus the relative entropy (`mixKL_eq_neg_relEntropy`).

"Degeneracy" here means the prior mass of the ground-state event, not a count of minimisers.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section Family

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hπm hπi hπ hπpos hL₀m hL₀ hR

omit [MeasurableSpace X] [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
/-- The affine loss of the one-feature family `R' = H_a` on `Unit`. -/
theorem affLoss_unit (a : ι → ℝ) (c : ℝ) :
    affLoss (fun _ : X ↦ (0 : ℝ)) (fun _ : Unit ↦ affLoss L₀ R a) (fun _ ↦ c) =
      fun x ↦ c * affLoss L₀ R a x + 0 := by
  funext x
  simp only [affLoss, Fintype.sum_unique]
  ring

omit [MeasurableSpace X] [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
theorem dirLoss_unit (a : ι → ℝ) (c : ℝ) :
    dirLoss (fun _ : Unit ↦ affLoss L₀ R a) (fun _ ↦ c) = fun x ↦ c * affLoss L₀ R a x := by
  funext x
  simp only [dirLoss, Fintype.sum_unique]

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
/-- **The thermal path is the ray of the one-feature family**: `P_{s,a} = P'_{1, s}`. -/
theorem familyMeasure_unit (a : ι → ℝ) (s : ℝ) :
    familyMeasure μ π (fun _ ↦ (0 : ℝ)) (fun _ : Unit ↦ affLoss L₀ R a) 1 (s • fun _ ↦ (1 : ℝ)) =
      familyMeasure μ π L₀ R s a := by
  have e : (s • fun _ : Unit ↦ (1 : ℝ)) = fun _ ↦ s := by
    funext i
    simp
  rw [e]
  unfold familyMeasure
  rw [affLoss_unit]
  unfold priorZ
  simp only [one_mul, add_zero]

omit [MeasurableSpace X] [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
theorem face_unit (a : ι → ℝ) (α : ℝ) :
    {x | dirLoss (fun _ : Unit ↦ affLoss L₀ R a) (fun _ ↦ (1 : ℝ)) x = α} =
      {x | affLoss L₀ R a x = α} := by
  ext x
  simp [dirLoss]

omit [MeasurableSpace X] [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
theorem tiltedPrior_zero_one (x : X) : tiltedPrior π (fun _ : X ↦ (0 : ℝ)) 1 x = π x := by
  simp [tiltedPrior]

/-- `⟨H_a⟩_{t,a} = ⟨L₀⟩_{t,a} + a·m_t(a)`. -/
theorem priorExp_affLoss_self (a : ι → ℝ) (t : ℝ) :
    priorExp μ π (affLoss L₀ R a) (affLoss L₀ R a) t =
      priorExp μ π (affLoss L₀ R a) L₀ t + ∑ i, a i * meanMap μ π L₀ R t a i := by
  have hν : Integrable (baseWeight π (affLoss L₀ R a) t) μ :=
    (tiltData_aff hπm hπi (fun x ↦ (hπ x).le) hπpos hL₀m hL₀ hR a a t).choose_spec.ν_int
  have e : priorExp μ π (affLoss L₀ R a) (affLoss L₀ R a) t =
      priorExp μ π (affLoss L₀ R a) (fun x ↦ L₀ x + dirLoss R a x) t := rfl
  rw [e, priorExp_add_bdd hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a ⟨hL₀m, M₀, hL₀⟩
    (bdd_dirLoss hR a),
    priorExp_dirLoss hν hR a]
  rfl

/-- **The seabed's mixture divergence is minus the relative entropy**:
`mixKL(0, H_a; t, 1, 0) = −𝒮(t, a) = KL(P_{t,a} ‖ π̄)`. -/
theorem mixKL_eq_neg_relEntropy (a : ι → ℝ) (t : ℝ) :
    mixKL μ π (fun _ ↦ (0 : ℝ)) (affLoss L₀ R a) t 1 0 = -relEntropy μ π L₀ R (natCoord t a) := by
  obtain ⟨hHm, MH, hHb⟩ := bdd_affLoss hL₀m hL₀ hR a
  have hT : TiltData μ (baseWeight π (fun _ ↦ (0 : ℝ)) t) (affLoss L₀ R a) MH :=
    tiltData_baseWeight_of_bounded (μ := μ) hπm hπi (fun x ↦ (hπ x).le) hπpos measurable_const
      (M₀ := 0) (fun _ ↦ by simp) hHm hHb t
  rw [hT.mixKL_eq (fun x ↦ (hπ x).le) 1 0, relEntropy_natCoord hπm hπi hπ hπpos hL₀m hL₀ hR]
  unfold mixLogZ mixExp
  have e1 : pathLoss (fun _ : X ↦ (0 : ℝ)) (affLoss L₀ R a) 1 = affLoss L₀ R a :=
    funext fun x ↦ by simp [pathLoss]
  have e0 : pathLoss (fun _ : X ↦ (0 : ℝ)) (affLoss L₀ R a) 0 = fun _ ↦ 0 :=
    funext fun x ↦ by simp [pathLoss]
  rw [e1, e0]
  have hZ0 : priorZ μ π (fun _ : X ↦ (0 : ℝ)) t = ∫ x, π x ∂μ := by
    unfold priorZ
    simp
  have hA : Real.log (priorZ μ π (affLoss L₀ R a) t) = affLogZ μ π L₀ R t a := rfl
  rw [hZ0, hA, priorExp_affLoss_self hπm hπi hπ hπpos hL₀m hL₀ hR a t]
  ring

variable (a : ι → ℝ) {α : ℝ} (hα : ∀ᵐ x ∂μ, α ≤ affLoss L₀ R a x)
include hα

/-- **The energy relaxes to the ground level**: `⟨H_a⟩_{t,a} → α` as `t → ∞`. -/
theorem tendsto_energy_temp
    (hmass : ∀ ε > 0, 0 < ∫ x in {x | affLoss L₀ R a x < α + ε}, π x ∂μ) :
    Tendsto (fun t ↦ priorExp μ π (affLoss L₀ R a) (affLoss L₀ R a) t) atTop (𝓝 α) := by
  have hR' : ∀ i : Unit, Bdd ((fun _ : Unit ↦ affLoss L₀ R a) i) := fun _ ↦
    bdd_affLoss hL₀m hL₀ hR a
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have hβ : ∀ᵐ x ∂μ, dirLoss (fun _ : Unit ↦ affLoss L₀ R a) (fun _ ↦ (-1 : ℝ)) x ≤ -α := by
    filter_upwards [hα] with x hx
    rw [dirLoss_unit]
    linarith
  have hmass' : ∀ ε > 0, 0 < ∫ x in {x | -α - ε <
      dirLoss (fun _ : Unit ↦ affLoss L₀ R a) (fun _ ↦ (-1 : ℝ)) x}, π x ∂μ := by
    intro ε hε
    have e : {x | -α - ε < dirLoss (fun _ : Unit ↦ affLoss L₀ R a) (fun _ ↦ (-1 : ℝ)) x} =
        {x | affLoss L₀ R a x < α + ε} := by
      ext x
      rw [dirLoss_unit]
      constructor <;> intro h <;> simp only [Set.mem_ofPred_eq] at h ⊢ <;> linarith
    rw [e]
    exact hmass ε hε
  have h := tendsto_thresholdFun hπm hπi hπ hπpos measurable_const h0 hR' one_pos 0
    (fun _ ↦ (-1 : ℝ)) hβ hmass'
  have e2 : ∀ lam, thresholdFun μ π (fun _ ↦ (0 : ℝ)) (fun _ : Unit ↦ affLoss L₀ R a) 1 0
      (fun _ ↦ (-1 : ℝ)) lam = -priorExp μ π (affLoss L₀ R a) (affLoss L₀ R a) lam := by
    intro lam
    unfold thresholdFun
    have e3 : ((0 : Unit → ℝ) - (lam / 1) • fun _ ↦ (-1 : ℝ)) = fun _ ↦ lam := by
      funext i
      simp
    rw [e3, affLoss_unit, dirLoss_unit, priorExp_smul_add, mul_one, priorExp_const_mul,
      neg_one_mul]
  have h' := h.congr e2
  simpa using h'.neg

omit [Nonempty X] hπpos in
/-- **The boundary posterior at zero temperature**: on a positive-mass ground state every bounded
observable converges to its conditional prior expectation. -/
theorem tendsto_priorExp_temp_face (hp : 0 < ∫ x in {x | affLoss L₀ R a x = α}, π x ∂μ)
    {φ : X → ℝ} (hφ : Bdd φ) :
    Tendsto (fun t ↦ priorExp μ π (affLoss L₀ R a) φ t) atTop
      (𝓝 ((∫ x in {x | affLoss L₀ R a x = α}, φ x * π x ∂μ) /
        ∫ x in {x | affLoss L₀ R a x = α}, π x ∂μ)) := by
  obtain ⟨hφm, Mφ, hφb⟩ := hφ
  obtain ⟨hHm, MH, hHb⟩ := bdd_affLoss hL₀m hL₀ hR a
  exact tendsto_priorExp_face hπm hπi hπ hHm hα hp hφm hφb

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR hα in
/-- The one-feature ray hypotheses, from the ground-state hypotheses. -/
theorem unit_face_pos (hp : 0 < ∫ x in {x | affLoss L₀ R a x = α}, π x ∂μ) :
    0 < ∫ x in {x | dirLoss (fun _ : Unit ↦ affLoss L₀ R a) (fun _ ↦ (1 : ℝ)) x = α},
      tiltedPrior π (fun _ : X ↦ (0 : ℝ)) 1 x ∂μ := by
  rw [face_unit]
  simpa only [tiltedPrior_zero_one] using hp

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ hR in
theorem unit_face_ae :
    ∀ᵐ x ∂μ, α ≤ dirLoss (fun _ : Unit ↦ affLoss L₀ R a) (fun _ ↦ (1 : ℝ)) x := by
  filter_upwards [hα] with x hx
  simp only [dirLoss_unit, one_mul]
  exact hx

omit [Nonempty X] in
/-- **The ground-state mass tends to one**: `P_{t,a}(G) → 1`. -/
theorem tendsto_familyMeasure_real_ground
    (hp : 0 < ∫ x in {x | affLoss L₀ R a x = α}, π x ∂μ) :
    Tendsto (fun t ↦ (familyMeasure μ π L₀ R t a).real {x | affLoss L₀ R a x = α}) atTop
      (𝓝 1) := by
  have hR' : ∀ i : Unit, Bdd ((fun _ : Unit ↦ affLoss L₀ R a) i) := fun _ ↦
    bdd_affLoss hL₀m hL₀ hR a
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have h := tendsto_familyMeasure_real_face hπm hπi hπ hπpos measurable_const h0 hR' one_pos
    (fun _ ↦ (1 : ℝ)) (unit_face_ae a hα)
    (unit_face_pos a hp)
  simp only [familyMeasure_unit, face_unit] at h
  exact h

omit hα in
/-- **The exact total-variation bound at zero temperature**:
`|P_{t,a}(A) − π̄(A | G)| ≤ 1 − P_{t,a}(G)`. -/
theorem abs_familyMeasure_real_sub_priorFace_le
    (hp : 0 < ∫ x in {x | affLoss L₀ R a x = α}, π x ∂μ) (t : ℝ) {A : Set X}
    (hA : MeasurableSet A) :
    |(familyMeasure μ π L₀ R t a).real A -
        (faceMeasure (familyMeasure μ π L₀ R 0 0) {x | affLoss L₀ R a x = α}).real A| ≤
      1 - (familyMeasure μ π L₀ R t a).real {x | affLoss L₀ R a x = α} := by
  have hR' : ∀ i : Unit, Bdd ((fun _ : Unit ↦ affLoss L₀ R a) i) := fun _ ↦
    bdd_affLoss hL₀m hL₀ hR a
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have h := abs_familyMeasure_real_sub_faceLaw_le hπm hπi hπ hπpos measurable_const h0 hR'
    one_pos (fun _ ↦ (1 : ℝ)) t (unit_face_pos a hp) hA
  have hz : familyMeasure μ π (fun _ ↦ (0 : ℝ)) (fun _ : Unit ↦ affLoss L₀ R a) 1 0 =
      familyMeasure μ π L₀ R 0 0 := by
    rw [← familyMeasure_zero_temp a, ← familyMeasure_unit a 0, zero_smul]
  simp only [familyMeasure_unit, face_unit, hz] at h
  exact h

/-- **Convergence to the conditioned prior in total variation**: `P_{t,a}(A) → π̄(A | G)`. -/
theorem tendsto_familyMeasure_real_temp_face
    (hp : 0 < ∫ x in {x | affLoss L₀ R a x = α}, π x ∂μ) {A : Set X} (hA : MeasurableSet A) :
    Tendsto (fun t ↦ (familyMeasure μ π L₀ R t a).real A) atTop
      (𝓝 ((faceMeasure (familyMeasure μ π L₀ R 0 0) {x | affLoss L₀ R a x = α}).real A)) := by
  have hR' : ∀ i : Unit, Bdd ((fun _ : Unit ↦ affLoss L₀ R a) i) := fun _ ↦
    bdd_affLoss hL₀m hL₀ hR a
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have h := tendsto_familyMeasure_real_ray hπm hπi hπ hπpos measurable_const h0 hR' one_pos
    (fun _ ↦ (1 : ℝ)) (unit_face_ae a hα)
    (unit_face_pos a hp) hA
  have hz : familyMeasure μ π (fun _ ↦ (0 : ℝ)) (fun _ : Unit ↦ affLoss L₀ R a) 1 0 =
      familyMeasure μ π L₀ R 0 0 := by
    rw [← familyMeasure_zero_temp a, ← familyMeasure_unit a 0, zero_smul]
  simp only [familyMeasure_unit, face_unit, hz] at h
  exact h

/-- **The information distance to the prior converges to the entry cost of the ground state**:
`KL(P_{t,a} ‖ π̄) → log ∫π − log ∫_G π`. -/
theorem tendsto_klDiv_prior_temp_face (hp : 0 < ∫ x in {x | affLoss L₀ R a x = α}, π x ∂μ) :
    Tendsto (fun t ↦ (klDiv (familyMeasure μ π L₀ R t a) (familyMeasure μ π L₀ R 0 0)).toReal)
      atTop (𝓝 (Real.log (∫ x, π x ∂μ) -
        Real.log (∫ x in {x | affLoss L₀ R a x = α}, π x ∂μ))) := by
  obtain ⟨hHm, MH, hHb⟩ := bdd_affLoss hL₀m hL₀ hR a
  have h := tendsto_mixKL_face hπm hπi hπ hπpos hHm hHb hα hp
  refine h.congr fun t ↦ ?_
  rw [mixKL_eq_neg_relEntropy hπm hπi hπ hπpos hL₀m hL₀ hR a t,
    klDiv_familyMeasure_prior hπm hπi hπ hπpos hL₀m hL₀ hR,
    ENNReal.toReal_ofReal (neg_nonneg.2 (relEntropy_nonpos hπm hπi hπ hπpos hL₀m hL₀ hR _))]

omit [Nonempty X] hα in
/-- The prior mass of a measurable set, as a ratio of prior integrals. -/
theorem familyMeasure_zero_real_eq {A : Set X} (hA : MeasurableSet A) :
    (familyMeasure μ π L₀ R 0 0).real A = (∫ x in A, π x ∂μ) / ∫ x, π x ∂μ := by
  rw [familyMeasure_real_eq_priorExp hπm hπi hπ hπpos hL₀m hL₀ hR (t := 0) 0 hA]
  unfold priorExp priorZ
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, one_mul]
  rw [← integral_indicator hA]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by
    beta_reduce
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul])

/-- **`KL(P_{t,a} ‖ π̄) → KL(π̄_G ‖ π̄) = −log π̄(G)`**: the thermal journey ends at the entry cost
of its ground state. -/
theorem tendsto_klDiv_prior_temp_face'
    (hp : 0 < ∫ x in {x | affLoss L₀ R a x = α}, π x ∂μ) :
    Tendsto (fun t ↦ (klDiv (familyMeasure μ π L₀ R t a) (familyMeasure μ π L₀ R 0 0)).toReal)
      atTop (𝓝 ((klDiv (faceMeasure (familyMeasure μ π L₀ R 0 0) {x | affLoss L₀ R a x = α})
        (familyMeasure μ π L₀ R 0 0)).toReal)) := by
  obtain ⟨hHm, MH, hHb⟩ := bdd_affLoss hL₀m hL₀ hR a
  have hG : MeasurableSet {x | affLoss L₀ R a x = α} := hHm (measurableSet_singleton α)
  have hQ := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := 0) 0
  have hp' : 0 < (familyMeasure μ π L₀ R 0 0).real {x | affLoss L₀ R a x = α} := by
    rw [familyMeasure_zero_real_eq hπm hπi hπ hπpos hL₀m hL₀ hR hG]
    exact div_pos hp hπpos
  rw [klDiv_faceMeasure _ hG hp', ENNReal.toReal_ofReal,
    familyMeasure_zero_real_eq hπm hπi hπ hπpos hL₀m hL₀ hR hG, Real.log_div hp.ne' hπpos.ne',
    neg_sub]
  · exact tendsto_klDiv_prior_temp_face hπm hπi hπ hπpos hL₀m hL₀ hR a hα hp
  · rw [familyMeasure_zero_real_eq hπm hπi hπ hπpos hL₀m hL₀ hR hG, Real.log_div hp.ne' hπpos.ne',
      neg_sub, sub_nonneg]
    exact Real.log_le_log hp (setIntegral_le_integral hπi (Eventually.of_forall fun x ↦ (hπ x).le))

end Family

end Laplace.Multi
