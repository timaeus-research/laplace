/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.RateFunction

/-!
# Exposed faces: the entropy cost of a wall

Let `Q` be a probability law of the features `R`, `u` a direction with `u·R ≤ β` a.e. and
`F = {u·R = β}` the face event, of positive mass `p_F = Q(F)`. The conditional law `Q_F = Q(· | F)`
(`faceMeasure`) has its own Chernoff rate `𝓘_F` (`genRate (faceMeasure Q F)`), and the rate of `Q`
decomposes on the face hyperplane `{u·M = β}` as

  `𝓘(M) = −log p_F + 𝓘_F(M)`   (`genRate_face_eq`):

the boundary inherits the lower-dimensional rate geometry of the face, with an entry cost equal to
the information `−log p_F` of the face event. The inequality `≤` holds everywhere
(`genRate_le_face`), because `Λ(q) ≥ log p_F + Λ_F(q)` for every `q` (`log_add_featCgf_face_le`);
the inequality `≥` on the hyperplane (`face_le_genRate`) comes from pushing the Chernoff direction
to infinity along `u`: `Λ(q + λu) − λβ → log p_F + Λ_F(q)` (`tendsto_featCgf_ray`), the contribution
of the complement of the face dying out by dominated convergence, while the score gains nothing on
the hyperplane since `u·M = β`.

For the response family this is `rateFun_face_eq`: on a positive-mass exposed face of the moment
body
the Cramér rate of the featureless member is the entry cost of the face plus the conditional rate.
(On a null face the rate is `+∞`; that is the other regime of theorem VI.)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι]

/-- The Chernoff rate of the features under a law `ν`. -/
noncomputable def genRate (ν : Measure X) (R : ι → X → ℝ) (M : ι → ℝ) : ℝ≥0∞ :=
  ⨆ q : ι → ℝ, ENNReal.ofReal (dotJ q M - featCgf ν R q)

/-- The conditional law on an event `F`. -/
noncomputable def faceMeasure (ν : Measure X) (F : Set X) : Measure X := (ν F)⁻¹ • ν.restrict F

section

variable (ν : Measure X) [IsProbabilityMeasure ν] {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hR

omit hR in
theorem isProbabilityMeasure_faceMeasure {F : Set X} (hF : ν F ≠ 0) :
    IsProbabilityMeasure (faceMeasure ν F) :=
  ⟨by rw [faceMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    ENNReal.inv_mul_cancel hF (measure_ne_top ν F)]⟩

omit [IsProbabilityMeasure ν] hR in
theorem integral_faceMeasure (F : Set X) (f : X → ℝ) :
    ∫ x, f x ∂faceMeasure ν F = (ν.real F)⁻¹ * ∫ x in F, f x ∂ν := by
  rw [faceMeasure, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul, measureReal_def]

theorem integrable_exp_dirLoss (q : ι → ℝ) :
    Integrable (fun x ↦ Real.exp (dirLoss R q x)) ν :=
  (integrable_exp_mul_of_bdd ν (bdd_dirLoss hR q) 1).congr
    (Eventually.of_forall fun x ↦ by simp only [one_mul])

theorem setIntegral_exp_dirLoss_pos {F : Set X} (hp : 0 < ν.real F) (q : ι → ℝ) :
    0 < ∫ x in F, Real.exp (dirLoss R q x) ∂ν := by
  obtain ⟨_, K, hK⟩ := bdd_dirLoss hR q
  calc (0 : ℝ) < ν.real F * Real.exp (-K) := by positivity
    _ = ∫ _x in F, Real.exp (-K) ∂ν := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ ∫ x in F, Real.exp (dirLoss R q x) ∂ν :=
        integral_mono (integrable_const _) (integrable_exp_dirLoss ν hR q).restrict fun x ↦
          Real.exp_le_exp.2 (neg_le_of_abs_le (hK x))

/-- `Λ_F(q) = log ∫_F e^{q·R} dQ − log p_F`. -/
theorem featCgf_faceMeasure {F : Set X} (hp : 0 < ν.real F) (q : ι → ℝ) :
    featCgf (faceMeasure ν F) R q =
      Real.log (∫ x in F, Real.exp (dirLoss R q x) ∂ν) - Real.log (ν.real F) := by
  unfold featCgf
  rw [integral_faceMeasure, Real.log_mul (inv_ne_zero hp.ne')
    (setIntegral_exp_dirLoss_pos ν hR hp q).ne', Real.log_inv]
  ring

/-- `log p_F + Λ_F(q) ≤ Λ(q)`. -/
theorem log_add_featCgf_face_le {F : Set X} (hp : 0 < ν.real F) (q : ι → ℝ) :
    Real.log (ν.real F) + featCgf (faceMeasure ν F) R q ≤ featCgf ν R q := by
  rw [featCgf_faceMeasure ν hR hp q, add_sub_cancel]
  unfold featCgf
  exact Real.log_le_log (setIntegral_exp_dirLoss_pos ν hR hp q)
    (setIntegral_le_integral (integrable_exp_dirLoss ν hR q)
      (Eventually.of_forall fun x ↦ (Real.exp_pos _).le))

/-- **The entry-cost inequality**: `𝓘(M) ≤ −log p_F + 𝓘_F(M)` for every `M`. -/
theorem genRate_le_face {F : Set X} (hp : 0 < ν.real F) (M : ι → ℝ) :
    genRate ν R M ≤ ENNReal.ofReal (-Real.log (ν.real F)) + genRate (faceMeasure ν F) R M := by
  refine iSup_le fun q ↦ ?_
  calc ENNReal.ofReal (dotJ q M - featCgf ν R q)
      ≤ ENNReal.ofReal (-Real.log (ν.real F) + (dotJ q M - featCgf (faceMeasure ν F) R q)) :=
        ENNReal.ofReal_le_ofReal (by linarith [log_add_featCgf_face_le ν hR hp q])
    _ ≤ ENNReal.ofReal (-Real.log (ν.real F)) +
          ENNReal.ofReal (dotJ q M - featCgf (faceMeasure ν F) R q) := ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (-Real.log (ν.real F)) + genRate (faceMeasure ν F) R M :=
        add_le_add le_rfl (le_iSup (fun q ↦ ENNReal.ofReal
          (dotJ q M - featCgf (faceMeasure ν F) R q)) q)

/-- **The cumulant generating function along the ray `q + λu` towards the face**:
`Λ(q + λu) − λβ → log p_F + Λ_F(q)`. -/
theorem tendsto_featCgf_ray {u : ι → ℝ} {β : ℝ} (hβ : ∀ᵐ x ∂ν, dirLoss R u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss R u x = β}) (q : ι → ℝ) :
    Tendsto (fun lam : ℝ ↦ featCgf ν R (q + lam • u) - lam * β) atTop
      (𝓝 (Real.log (ν.real {x | dirLoss R u x = β}) +
        featCgf (faceMeasure ν {x | dirLoss R u x = β}) R q)) := by
  obtain ⟨hum, _, _⟩ := bdd_dirLoss hR u
  obtain ⟨hqm, _, _⟩ := bdd_dirLoss hR q
  set F : Set X := {x | dirLoss R u x = β} with hFdef
  have hF : MeasurableSet F := measurableSet_eq_fun hum measurable_const
  set A : ℝ := ∫ x in F, Real.exp (dirLoss R q x) ∂ν with hA
  have hApos : 0 < A := setIntegral_exp_dirLoss_pos ν hR hp q
  -- the complement contribution
  set G : ℝ → ℝ := fun lam ↦ ∫ x in Fᶜ, Real.exp (dirLoss R q x) *
    Real.exp (lam * (dirLoss R u x - β)) ∂ν with hG
  have hG0 : ∀ lam, 0 ≤ G lam := fun lam ↦ integral_nonneg fun x ↦ by positivity
  -- decomposition of the full integral
  have hsplit : ∀ lam : ℝ, ∫ x, Real.exp (dirLoss R (q + lam • u) x) ∂ν =
      Real.exp (lam * β) * (A + G lam) := by
    intro lam
    rw [← integral_add_compl hF (integrable_exp_dirLoss ν hR _)]
    have e1 : ∫ x in F, Real.exp (dirLoss R (q + lam • u) x) ∂ν = Real.exp (lam * β) * A := by
      rw [hA, ← integral_const_mul]
      refine setIntegral_congr_fun hF fun x hx ↦ ?_
      have hx' : dirLoss R u x = β := hx
      simp only [dirLoss_add, dirLoss_smul, hx', ← Real.exp_add]
      congr 1
      ring
    have e2 : ∫ x in Fᶜ, Real.exp (dirLoss R (q + lam • u) x) ∂ν = Real.exp (lam * β) * G lam := by
      rw [hG, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only [dirLoss_add, dirLoss_smul, ← Real.exp_add]
      congr 1
      ring
    rw [e1, e2]
    ring
  -- the complement contribution vanishes
  have hGlim : Tendsto G atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _x in Fᶜ, (0 : ℝ) ∂ν := by simp
    rw [hG, h0]
    refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ Real.exp (dirLoss R q x))
      (Eventually.of_forall fun lam ↦ ?_) ?_
      (integrable_exp_dirLoss ν hR q).restrict ?_
    · exact (Measurable.aestronglyMeasurable (by fun_prop))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with lam hlam
      filter_upwards [ae_restrict_of_ae hβ] with x hx
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      refine mul_le_of_le_one_right (Real.exp_pos _).le ?_
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.2 (mul_nonpos_of_nonneg_of_nonpos hlam (by linarith))
    · filter_upwards [ae_restrict_of_ae hβ, ae_restrict_mem hF.compl] with x hx hxF
      have hlt : dirLoss R u x - β < 0 := by
        have : dirLoss R u x ≠ β := hxF
        exact sub_neg.2 (lt_of_le_of_ne hx this)
      have h := (Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg hlt)).const_mul
        (Real.exp (dirLoss R q x))
      simpa using h
  -- assemble
  have hlog : Tendsto (fun lam ↦ Real.log (A + G lam)) atTop (𝓝 (Real.log A)) := by
    have h1 : Tendsto (fun lam ↦ A + G lam) atTop (𝓝 A) := by
      simpa using (tendsto_const_nhds (x := A)).add hGlim
    exact (Real.continuousAt_log hApos.ne').tendsto.comp h1
  have hAeq : Real.log A = Real.log (ν.real F) + featCgf (faceMeasure ν F) R q := by
    rw [featCgf_faceMeasure ν hR hp q]; ring
  rw [← hAeq]
  refine hlog.congr fun lam ↦ ?_
  unfold featCgf
  rw [hsplit lam, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  ring

omit hR in
/-- `Λ_ν(0) = 0`. -/
theorem featCgf_zero' : featCgf ν R 0 = 0 := by
  unfold featCgf
  simp [dirLoss]

/-- **The reverse entry-cost inequality on the face hyperplane**:
`−log p_F + 𝓘_F(M) ≤ 𝓘(M)` whenever `u·M = β`. -/
theorem face_le_genRate {u : ι → ℝ} {β : ℝ} (hβ : ∀ᵐ x ∂ν, dirLoss R u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss R u x = β}) {M : ι → ℝ} (hM : dotJ u M = β) :
    ENNReal.ofReal (-Real.log (ν.real {x | dirLoss R u x = β})) +
        genRate (faceMeasure ν {x | dirLoss R u x = β}) R M ≤ genRate ν R M := by
  set F : Set X := {x | dirLoss R u x = β} with hFdef
  have hp1 : ν.real F ≤ 1 := by
    rw [measureReal_def, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  have hlog : 0 ≤ -Real.log (ν.real F) := by
    have := Real.log_nonpos hp.le hp1
    linarith
  -- the key limit bound
  have key : ∀ q : ι → ℝ,
      ENNReal.ofReal (dotJ q M - featCgf (faceMeasure ν F) R q - Real.log (ν.real F)) ≤
        genRate ν R M := by
    intro q
    have hray := tendsto_featCgf_ray ν hR hβ hp q
    have h := (tendsto_const_nhds (x := dotJ q M)).sub hray
    have h' : Tendsto (fun lam : ℝ ↦ dotJ (q + lam • u) M - featCgf ν R (q + lam • u)) atTop
        (𝓝 (dotJ q M - featCgf (faceMeasure ν F) R q - Real.log (ν.real F))) := by
      have e : dotJ q M - featCgf (faceMeasure ν F) R q - Real.log (ν.real F) =
          dotJ q M - (Real.log (ν.real F) + featCgf (faceMeasure ν F) R q) := by ring
      rw [e]
      refine h.congr fun lam ↦ ?_
      rw [dotJ_add_left, dotJ_smul_left, hM]
      ring
    have hscore := (ENNReal.continuous_ofReal.tendsto _).comp h'
    exact le_of_tendsto' hscore fun lam ↦ le_iSup (fun q ↦ ENNReal.ofReal (dotJ q M -
      featCgf ν R q)) (q + lam • u)
  have hF0 : ν F ≠ 0 := (ENNReal.toReal_pos_iff.1 hp).1.ne'
  have := isProbabilityMeasure_faceMeasure ν hF0
  rw [genRate, ENNReal.add_iSup]
  refine iSup_le fun q ↦ ?_
  rcases le_or_gt 0 (dotJ q M - featCgf (faceMeasure ν F) R q) with hs | hs
  · rw [← ENNReal.ofReal_add hlog hs]
    refine (key q).trans_eq' ?_
    congr 1; ring
  · rw [ENNReal.ofReal_of_nonpos hs.le, add_zero]
    have h0 := key 0
    rw [featCgf_zero', dotJ_zero_left, sub_zero, zero_sub] at h0
    exact h0

/-- **The entropy cost of a wall**: on the face hyperplane `{u·M = β}` of a positive-mass exposed
face, `𝓘(M) = −log p_F + 𝓘_F(M)`. -/
theorem genRate_face_eq {u : ι → ℝ} {β : ℝ} (hβ : ∀ᵐ x ∂ν, dirLoss R u x ≤ β)
    (hp : 0 < ν.real {x | dirLoss R u x = β}) {M : ι → ℝ} (hM : dotJ u M = β) :
    genRate ν R M = ENNReal.ofReal (-Real.log (ν.real {x | dirLoss R u x = β})) +
      genRate (faceMeasure ν {x | dirLoss R u x = β}) R M :=
  le_antisymm (genRate_le_face ν hR hp M) (face_le_genRate ν hR hβ hp hM)

end

section Family

variable [Nonempty X] {μ : Measure X} {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

omit ht in
/-- **The Cramér rate on a positive-mass exposed face of the moment body** is the entry cost of the
face plus the conditional rate. -/
theorem rateFun_face_eq {u : ι → ℝ} {β : ℝ} (hβ : ∀ᵐ x ∂μ, dirLoss R u x ≤ β)
    (hp : 0 < (familyMeasure μ π L₀ R t 0).real {x | dirLoss R u x = β}) {M : ι → ℝ}
    (hM : dotJ u M = β) :
    rateFun μ π L₀ R t M =
      ENNReal.ofReal (-Real.log ((familyMeasure μ π L₀ R t 0).real {x | dirLoss R u x = β})) +
        genRate (faceMeasure (familyMeasure μ π L₀ R t 0) {x | dirLoss R u x = β}) R M := by
  have := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) 0
  have hβ' : ∀ᵐ x ∂(familyMeasure μ π L₀ R t 0), dirLoss R u x ≤ β :=
    (withDensity_absolutelyContinuous _ _) hβ
  exact genRate_face_eq (familyMeasure μ π L₀ R t 0) hR hβ' hp hM

end Family

end Laplace.Multi
