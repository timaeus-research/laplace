/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.TwoAxisResponse

/-!
# The halfspace Chernoff bound and the free energy as a rate function

Sample `n` points i.i.d. from a data distribution `ν` and form the empirical feature mean
`R̄_n = (1/n) ∑ₖ R(xₖ)` (`empMean`). For every direction `u`, level `r` and multiplier `λ ≥ 0`,

`P(u · R̄_n ≥ r) ≤ exp[−n (λ r − Λ_ν(λu))]`   (`halfspace_chernoff`),

where `Λ_ν(θ) = log ∫ e^{θ·R} dν` is the cumulant generating function of the features
(`featCgf`). Taking the best multiplier gives the Chernoff rate `sup_{λ ≥ 0} {λ r − Λ_ν(λu)}`
(`halfspace_chernoff_iInf`). This is the finite-`n` halfspace form of Cramér's theorem; the
closed-set form `P(R̄_n ∈ F) ≤ e^{−n inf_F I}` is **false** at finite `n` for general closed `F`.

When the data distribution is itself a member of the exponential family,
`ν = P_{t,a} ∝ e^{−t(L₀ + a·R)} π` (`familyMeasure`), the cumulant generating function is a
difference of free energies,

`Λ_{P_{t,a}}(θ) = A_t(a − θ/t) − A_t(a)`   (`featCgf_familyMeasure`),

so the large-deviation rate of the empirical feature mean under `P_{t,a}` is the Legendre
transform of the same convex potential `A_t` whose gradient is the mean map: the response map
and the concentration of the sufficient statistic are governed by one function
(`halfspace_chernoff_family`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι]

/-- The cumulant generating function of the features under a data distribution `ν`:
`Λ_ν(θ) = log ∫ e^{θ·R} dν`. -/
noncomputable def featCgf (ν : Measure X) (R : ι → X → ℝ) (θ : ι → ℝ) : ℝ :=
  Real.log (∫ x, Real.exp (dirLoss R θ x) ∂ν)

/-- The empirical feature mean of `n` samples. -/
noncomputable def empMean (R : ι → X → ℝ) (n : ℕ) (x : Fin n → X) : ι → ℝ :=
  fun i ↦ (∑ k, R i (x k)) / n

omit [MeasurableSpace X] in
theorem sum_mul_empMean (R : ι → X → ℝ) (u : ι → ℝ) (n : ℕ) (x : Fin n → X) :
    ∑ i, u i * empMean R n x i = (∑ k, dirLoss R u (x k)) / n := by
  simp only [empMean, dirLoss, ← mul_div_assoc, ← Finset.sum_div, Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

/-- `e^{λ Y}` is integrable for a bounded `Y` on a finite measure. -/
theorem integrable_exp_mul_of_bdd (ν : Measure X) [IsFiniteMeasure ν] {Y : X → ℝ} (hY : Bdd Y)
    (lam : ℝ) : Integrable (fun y ↦ Real.exp (lam * Y y)) ν := by
  obtain ⟨hYm, M, hM⟩ := hY
  have hm : Measurable fun y ↦ Real.exp (lam * Y y) := by fun_prop
  refine Integrable.of_bound hm.aestronglyMeasurable (Real.exp (|lam| * M))
    (ae_of_all _ fun y ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM y) (abs_nonneg _)

section Chernoff

variable (ν : Measure X) [IsProbabilityMeasure ν] {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hR

/-- **The halfspace Chernoff bound**: for `n` i.i.d. samples from `ν`, every direction `u`,
level `r` and multiplier `λ ≥ 0`, `P(u · R̄_n ≥ r) ≤ exp[−n (λ r − Λ_ν(λu))]`. -/
theorem halfspace_chernoff (u : ι → ℝ) (r : ℝ) {n : ℕ} (hn : 0 < n) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    (Measure.pi fun _ : Fin n ↦ ν).real {x | r ≤ ∑ i, u i * empMean R n x i} ≤
      Real.exp (-(n * (lam * r - featCgf ν R (lam • u)))) := by
  obtain ⟨hYm, M, hM⟩ := bdd_dirLoss hR u
  set P : Measure (Fin n → X) := Measure.pi fun _ : Fin n ↦ ν with hP
  set Xk : Fin n → (Fin n → X) → ℝ := fun k x ↦ dirLoss R u (x k) with hXk
  have hind : iIndepFun Xk P :=
    iIndepFun_pi (μ := fun _ : Fin n ↦ ν) (X := fun _ ↦ dirLoss R u) fun _ ↦ hYm.aemeasurable
  have hmeas : ∀ k, Measurable (Xk k) := fun k ↦ hYm.comp (measurable_pi_apply k)
  have hint1 : ∀ k, Integrable (fun x ↦ Real.exp (lam * Xk k x)) P := fun k ↦
    integrable_exp_mul_of_bdd P ⟨hmeas k, M, fun x ↦ hM _⟩ lam
  have hmgf : ∀ k, mgf (Xk k) P lam = mgf (dirLoss R u) ν lam := by
    intro k
    unfold mgf
    calc ∫ x, Real.exp (lam * Xk k x) ∂P
        = ∫ x, Real.exp (lam * dirLoss R u (Function.eval k x)) ∂P := rfl
      _ = ∫ y, Real.exp (lam * dirLoss R u y) ∂(P.map (Function.eval k)) :=
          (integral_map (μ := P) (φ := Function.eval k)
            (f := fun y ↦ Real.exp (lam * dirLoss R u y)) (measurable_pi_apply k).aemeasurable
            (by fun_prop :
              Measurable fun y ↦ Real.exp (lam * dirLoss R u y)).aestronglyMeasurable).symm
      _ = _ := by rw [(measurePreserving_eval (fun _ : Fin n ↦ ν) k).map_eq]
  have hmgfsum : mgf (∑ k, Xk k) P lam = mgf (dirLoss R u) ν lam ^ n := by
    rw [hind.mgf_sum hmeas Finset.univ]
    simp only [hmgf, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hintsum : Integrable (fun x ↦ Real.exp (lam * (∑ k, Xk k) x)) P :=
    hind.integrable_exp_mul_sum hmeas (s := Finset.univ) fun k _ ↦ hint1 k
  have hch := measure_ge_le_exp_mul_mgf (μ := P) (X := ∑ k, Xk k) (n * r) hlam hintsum
  have hset : {x : Fin n → X | r ≤ ∑ i, u i * empMean R n x i} =
      {x | (n : ℝ) * r ≤ (∑ k, Xk k) x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.sum_apply, sum_mul_empMean, hXk]
    rw [le_div_iff₀ (by exact_mod_cast hn)]
    constructor <;> intro h <;> linarith
  have hpos : 0 < mgf (dirLoss R u) ν lam := mgf_pos (integrable_exp_mul_of_bdd ν ⟨hYm, M, hM⟩ lam)
  have hcgf : featCgf ν R (lam • u) = Real.log (mgf (dirLoss R u) ν lam) := by
    unfold featCgf mgf
    rw [dirLoss_smul]
  rw [hset, hcgf]
  refine hch.trans (le_of_eq ?_)
  rw [hmgfsum]
  conv_lhs => rw [← Real.exp_log hpos]
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- The Chernoff bound with the best multiplier:
`P(u · R̄_n ≥ r) ≤ inf_{λ ≥ 0} e^{−n(λr − Λ(λu))}`. -/
theorem halfspace_chernoff_iInf (u : ι → ℝ) (r : ℝ) {n : ℕ} (hn : 0 < n) :
    (Measure.pi fun _ : Fin n ↦ ν).real {x | r ≤ ∑ i, u i * empMean R n x i} ≤
      ⨅ lam : Set.Ici (0 : ℝ),
        Real.exp (-(n * ((lam : ℝ) * r - featCgf ν R ((lam : ℝ) • u)))) := by
  have : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, Set.mem_Ici.2 le_rfl⟩⟩
  exact le_ciInf fun lam ↦ halfspace_chernoff ν hR u r hn lam.2

end Chernoff

/-- The member `P_{t,a} ∝ e^{−t(L₀ + a·R)} π` of the family, as a measure. -/
noncomputable def familyMeasure (μ : Measure X) (π L₀ : X → ℝ) (R : ι → X → ℝ) (t : ℝ)
    (a : ι → ℝ) : Measure X :=
  μ.withDensity fun x ↦ ENNReal.ofReal
    (Real.exp (-(t * affLoss L₀ R a x)) * π x / priorZ μ π (affLoss L₀ R a) t)

section Family

variable {μ : Measure X} [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ)
  (hπ : ∀ x, 0 < π x) (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ}
  (hL₀ : ∀ x, |L₀ x| ≤ M₀) {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ}
include hπm hπi hπ hπpos hL₀m hL₀ hR

omit [Nonempty X] hπi hπ hπpos in
theorem measurable_familyDensity (a : ι → ℝ) :
    Measurable fun x ↦ ENNReal.ofReal
      (Real.exp (-(t * affLoss L₀ R a x)) * π x / priorZ μ π (affLoss L₀ R a) t) := by
  have hA : Measurable (affLoss L₀ R a) := (bdd_affLoss hL₀m hL₀ hR a).1
  fun_prop

omit [Nonempty X] in
/-- Expectations under `P_{t,a}` are the posterior expectations of the family. -/
theorem integral_familyMeasure (a : ι → ℝ) (f : X → ℝ) :
    ∫ x, f x ∂familyMeasure μ π L₀ R t a = priorExp μ π (affLoss L₀ R a) f t := by
  have hZ := affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  unfold familyMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (measurable_familyDensity hπm hL₀m hL₀ hR a).aemeasurable
    (ae_of_all _ fun x ↦ ENNReal.ofReal_lt_top) f]
  unfold priorExp
  rw [← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [ENNReal.toReal_ofReal (div_nonneg (mul_nonneg (Real.exp_pos _).le (hπ x).le) hZ.le),
    smul_eq_mul]
  ring

/-- `P_{t,a}` is a probability measure. -/
theorem isProbabilityMeasure_familyMeasure (a : ι → ℝ) :
    IsProbabilityMeasure (familyMeasure μ π L₀ R t a) := by
  have hZ := affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  have hw : Integrable (fun x ↦ Real.exp (-(t * affLoss L₀ R a x)) * π x) μ :=
    (integrable_mul_affWeight_of_bdd hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a (Bdd.const 1)).congr
      (Eventually.of_forall fun x ↦ by simp)
  refine ⟨?_⟩
  rw [familyMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hw.div_const _)
      (ae_of_all _ fun x ↦ div_nonneg (mul_nonneg (Real.exp_pos _).le (hπ x).le) hZ.le),
    integral_div]
  have : (∫ x, Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ) = priorZ μ π (affLoss L₀ R a) t := rfl
  rw [this, div_self hZ.ne', ENNReal.ofReal_one]

omit [Nonempty X] in
/-- **The cumulant generating function of a family member is a free-energy difference**:
`Λ_{P_{t,a}}(θ) = A_t(a − θ/t) − A_t(a)`. -/
theorem featCgf_familyMeasure (ht : t ≠ 0) (a θ : ι → ℝ) :
    featCgf (familyMeasure μ π L₀ R t a) R θ =
      affLogZ μ π L₀ R t (a - t⁻¹ • θ) - affLogZ μ π L₀ R t a := by
  unfold featCgf
  rw [integral_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR a]
  have hnum : (∫ x, Real.exp (dirLoss R θ x) * Real.exp (-(t * affLoss L₀ R a x)) * π x ∂μ) =
      priorZ μ π (affLoss L₀ R (a - t⁻¹ • θ)) t := by
    unfold priorZ
    rw [sub_eq_add_neg, ← neg_smul, affLoss_add_smul_eq]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    rw [← Real.exp_add]
    congr 2
    field_simp
    ring
  unfold priorExp affLogZ
  rw [hnum, Real.log_div (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) _).ne'
    (affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a).ne']

/-- **Chernoff for the family**: sampling from `P_{t,a}`, the empirical feature mean satisfies
`P(u · R̄_n ≥ r) ≤ exp[−n (λ r − A_t(a − (λ/t) u) + A_t(a))]` — the rate is the Legendre
transform of the free energy. -/
theorem halfspace_chernoff_family (ht : t ≠ 0) (a u : ι → ℝ) (r : ℝ) {n : ℕ} (hn : 0 < n)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (Measure.pi fun _ : Fin n ↦ familyMeasure μ π L₀ R t a).real
        {x | r ≤ ∑ i, u i * empMean R n x i} ≤
      Real.exp (-(n * (lam * r -
        (affLogZ μ π L₀ R t (a - t⁻¹ • (lam • u)) - affLogZ μ π L₀ R t a)))) := by
  have := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  rw [← featCgf_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR ht a (lam • u)]
  exact halfspace_chernoff (familyMeasure μ π L₀ R t a) hR u r hn hlam

end Family

end Laplace.Multi
