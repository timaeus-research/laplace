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

/-- **The tangent bound of the log-partition in temperature** (Bregman nonnegativity of the joint
family along the thermal path): `A_t(a) − (s − t)⟨H_a⟩_{t,a} ≤ A_s(a)`. -/
theorem affLogZ_tangent_temp (a : ι → ℝ) (s t : ℝ) :
    affLogZ μ π L₀ R t a - (s - t) * priorExp μ π (affLoss L₀ R a) (affLoss L₀ R a) t ≤
      affLogZ μ π L₀ R s a := by
  have hS' := bdd_jointStat hL₀m hL₀ hR
  have h0 : ∀ x, |(fun _ : X ↦ (0 : ℝ)) x| ≤ 0 := fun x ↦ by simp
  have h := famKL_nonneg hπm hπi hπ hπpos measurable_const h0 hS' one_pos (natCoord t a)
    (natCoord s a)
  rw [famKL_eq hπm hπi hπ hπpos measurable_const h0 hS' (t := 1) (natCoord t a) (natCoord s a),
    affLogZ_natCoord, affLogZ_natCoord, Fintype.sum_option] at h
  simp only [natCoord_none, natCoord_some, meanMap_natCoord_none, meanMap_natCoord_some,
    one_mul] at h
  rw [priorExp_affLoss_self hπm hπi hπ hπpos hL₀m hL₀ hR a t]
  have e : ∑ i, (s * a i - t * a i) * meanMap μ π L₀ R t a i =
      (s - t) * ∑ i, a i * meanMap μ π L₀ R t a i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [e] at h
  linarith

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

/-- **A null ground state is infinitely far**: if `π(H_a = α) = 0` then `KL(P_{t,a} ‖ π̄) → +∞`. The
divergence is monotone in `t`, and a bounded divergence would, through the tangent bound of the
log-partition and `⟨H_a⟩_t → α`, keep `log ∫ e^{−s(H_a − α)} π` bounded below for all `s`,
contradicting its convergence to `log π(G) = −∞`. -/
theorem tendsto_klDiv_prior_temp_null
    (hmass : ∀ ε > 0, 0 < ∫ x in {x | affLoss L₀ R a x < α + ε}, π x ∂μ)
    (h0 : μ {x | affLoss L₀ R a x = α} = 0) :
    Tendsto (fun t ↦ (klDiv (familyMeasure μ π L₀ R t a) (familyMeasure μ π L₀ R 0 0)).toReal)
      atTop atTop := by
  obtain ⟨hHm, MH, hHb⟩ := bdd_affLoss hL₀m hL₀ hR a
  have hH : Bdd (affLoss L₀ R a) := ⟨hHm, MH, hHb⟩
  have hrep : ∀ t, (klDiv (familyMeasure μ π L₀ R t a) (familyMeasure μ π L₀ R 0 0)).toReal =
      Real.log (∫ x, π x ∂μ) - affLogZ μ π L₀ R t a -
        t * priorExp μ π (affLoss L₀ R a) (affLoss L₀ R a) t := fun t ↦ by
    rw [klDiv_familyMeasure_prior hπm hπi hπ hπpos hL₀m hL₀ hR,
      ENNReal.toReal_ofReal (neg_nonneg.2 (relEntropy_nonpos hπm hπi hπ hπpos hL₀m hL₀ hR _)),
      relEntropy_natCoord hπm hπi hπ hπpos hL₀m hL₀ hR,
      priorExp_affLoss_self hπm hπi hπ hπpos hL₀m hL₀ hR a t]
    ring
  have hderiv := hasDerivAt_klDiv_familyMeasure_prior_toReal hπm hπi hπ hπpos hL₀m hL₀ hR a
  have hmono : MonotoneOn (fun t ↦ (klDiv (familyMeasure μ π L₀ R t a)
      (familyMeasure μ π L₀ R 0 0)).toReal) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun t _ ↦ (hderiv t).continuousAt.continuousWithinAt)
      (fun t _ ↦ (hderiv t).differentiableAt.differentiableWithinAt) fun t ht ↦ ?_
    rw [interior_Ici] at ht
    rw [(hderiv t).deriv]
    exact mul_nonneg ht.le (priorCov_self_nonneg' hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a hH)
  have hunb : ∀ C : ℝ, ∃ t, 0 ≤ t ∧
      C ≤ (klDiv (familyMeasure μ π L₀ R t a) (familyMeasure μ π L₀ R 0 0)).toReal := by
    intro C
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    have hE := tendsto_energy_temp hπm hπi hπ hπpos hL₀m hL₀ hR a hα hmass
    have hbound : ∀ s, Real.log (∫ x, π x ∂μ) - C ≤ affLogZ μ π L₀ R s a + s * α := by
      intro s
      have hlim : Tendsto (fun t ↦ affLogZ μ π L₀ R s a +
          s * priorExp μ π (affLoss L₀ R a) (affLoss L₀ R a) t) atTop
          (𝓝 (affLogZ μ π L₀ R s a + s * α)) := (hE.const_mul s).const_add _
      refine ge_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      have h1 := hcon t ht
      rw [hrep t] at h1
      have h2 := affLogZ_tangent_temp hπm hπi hπ hπpos hL₀m hL₀ hR a s t
      linarith
    have hW := tendsto_shifted_priorZ hπm hπi hπ hHm hα
    have hG0 : (∫ x in {x | affLoss L₀ R a x = α}, π x ∂μ) = 0 := by
      rw [Measure.restrict_eq_zero.2 h0, integral_zero_measure]
    rw [hG0] at hW
    have hWpos : ∀ s, 0 < Real.exp (s * α) * priorZ μ π (affLoss L₀ R a) s := fun s ↦
      mul_pos (Real.exp_pos _) (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := s) a)
    have hlog : Tendsto (fun s ↦ Real.log (Real.exp (s * α) * priorZ μ π (affLoss L₀ R a) s))
        atTop atBot :=
      Real.tendsto_log_nhdsNE_zero.comp
        (tendsto_nhdsWithin_iff.2 ⟨hW, Eventually.of_forall fun s ↦ (hWpos s).ne'⟩)
    obtain ⟨s, hs⟩ := (tendsto_atBot.1 hlog (Real.log (∫ x, π x ∂μ) - C - 1)).exists
    have hb := hbound s
    rw [Real.log_mul (Real.exp_pos _).ne' (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := s) a).ne',
      Real.log_exp] at hs
    have e : affLogZ μ π L₀ R s a = Real.log (priorZ μ π (affLoss L₀ R a) s) := rfl
    rw [e] at hb
    linarith
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨t₀, ht₀, hb⟩ := hunb b
  exact ⟨t₀, fun t ht ↦ hb.trans (hmono ht₀ (ht₀.trans ht) ht)⟩

end Family

end Laplace.Multi
