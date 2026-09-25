/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.ProductDensity
import Laplace.Multi.InteriorThreshold

/-!
# The tilt-based lower bound: rare responses are exactly as rare as their information cost

Sampling `n` points from `P_a`, the empirical feature mean lands in any neighbourhood of the
response `m_t(b)` of the tilted member `b = a − (λ/t) u` with probability at least
`e^{−n (KL(P_b ‖ P_a) + δ)}` for all large `n` (`tilt_lower_bound`). Together with the halfspace
Chernoff bound this shows that the information distance `KL(P_b ‖ P_a)` is the exact exponential
cost of a response fluctuation to `m_t(b)`: the change of measure to `P_b` (whose product density
is `e^{−n(λ u·R̄_n − Λ_a(λu))}`, `Measure.pi_withDensity_ofReal`) is bounded below near `m_t(b)`,
and Chebyshev's inequality under `P_b^{⊗n}` keeps the empirical mean near `m_t(b)` with probability
close to one.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

section

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

omit [Nonempty X] in
/-- **The tilted member as a density of the base member**:
`P_a = P_b.withDensity exp(−(λ u·R − Λ_a(λu)))` for `b = a − (λ/t) u`. -/
theorem familyMeasure_eq_withDensity_tilt (a u : ι → ℝ) (lam : ℝ) :
    familyMeasure μ π L₀ R t a = (familyMeasure μ π L₀ R t (a - (lam / t) • u)).withDensity
      (fun x ↦ ENNReal.ofReal (Real.exp (-(lam * dirLoss R u x -
        famCgf μ π L₀ R t a (lam • u))))) := by
  have hZa := affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  have hZb := affZ_pos hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) (a - (lam / t) • u)
  have hDm : Measurable (dirLoss R u) := (bdd_dirLoss hR u).1
  unfold familyMeasure
  rw [← withDensity_mul₀ (measurable_familyDensity hπm hL₀m hL₀ hR _).aemeasurable
    (by fun_prop : Measurable fun x ↦ ENNReal.ofReal (Real.exp (-(lam * dirLoss R u x -
      famCgf μ π L₀ R t a (lam • u))))).aemeasurable]
  congr 1
  funext x
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (Real.exp_pos _).le (hπ x).le)
    hZb.le)]
  congr 1
  rw [famCgf_smul]
  unfold affLogZ
  have e : affLoss L₀ R (a - (lam / t) • u) x = affLoss L₀ R a x - lam / t * dirLoss R u x := by
    rw [← sub_div_smul_eq, affLoss_add_smul_eq]
    simp only [dirLoss_smul]
    ring
  rw [e]
  have hZa' := hZa.ne'
  have hZb' := hZb.ne'
  have hE : Real.exp (-(t * (affLoss L₀ R a x - lam / t * dirLoss R u x))) *
      Real.exp (-(lam * dirLoss R u x - (Real.log (priorZ μ π (affLoss L₀ R (a - (lam / t) • u)) t)
        - Real.log (priorZ μ π (affLoss L₀ R a) t)))) =
      Real.exp (-(t * affLoss L₀ R a x)) * priorZ μ π (affLoss L₀ R (a - (lam / t) • u)) t /
        priorZ μ π (affLoss L₀ R a) t := by
    have hexp : -(t * (affLoss L₀ R a x - lam / t * dirLoss R u x)) +
        -(lam * dirLoss R u x - (Real.log (priorZ μ π (affLoss L₀ R (a - (lam / t) • u)) t) -
          Real.log (priorZ μ π (affLoss L₀ R a) t))) =
        -(t * affLoss L₀ R a x) + (Real.log (priorZ μ π (affLoss L₀ R (a - (lam / t) • u)) t) -
          Real.log (priorZ μ π (affLoss L₀ R a) t)) := by
      field_simp
      ring
    rw [← Real.exp_add, hexp, Real.exp_add, Real.exp_sub, Real.exp_log hZb, Real.exp_log hZa]
    ring
  have hre : Real.exp (-(t * (affLoss L₀ R a x - lam / t * dirLoss R u x))) * π x /
      priorZ μ π (affLoss L₀ R (a - (lam / t) • u)) t *
      Real.exp (-(lam * dirLoss R u x -
        (Real.log (priorZ μ π (affLoss L₀ R (a - (lam / t) • u)) t) -
          Real.log (priorZ μ π (affLoss L₀ R a) t)))) =
      (Real.exp (-(t * (affLoss L₀ R a x - lam / t * dirLoss R u x))) *
        Real.exp (-(lam * dirLoss R u x -
          (Real.log (priorZ μ π (affLoss L₀ R (a - (lam / t) • u)) t) -
            Real.log (priorZ μ π (affLoss L₀ R a) t))))) * π x /
        priorZ μ π (affLoss L₀ R (a - (lam / t) • u)) t := by ring
  rw [hre, hE]
  field_simp

/-- `KL(P_b ‖ P_a) = λ u·m(b) − Λ_a(λu)` for `b = a − (λ/t) u`. -/
theorem famKL_tilt_eq (a u : ι → ℝ) (lam : ℝ) :
    famKL μ π L₀ R t (a - (lam / t) • u) a =
      lam * ∑ i, u i * meanMap μ π L₀ R t (a - (lam / t) • u) i -
        famCgf μ π L₀ R t a (lam • u) := by
  rw [famKL_eq hπm hπi hπ hπpos hL₀m hL₀ hR, famCgf_smul, sum_sub_smul_mul, ← mul_assoc,
    mul_div_cancel₀ _ ht.ne']
  ring

end

section Chebyshev

variable (ν : Measure X) [IsProbabilityMeasure ν]

theorem integrable_coord_pi {f : X → ℝ} (hf : Bdd f) {n : ℕ} (k : Fin n) :
    Integrable (fun x : Fin n → X ↦ f (x k)) (Measure.pi fun _ : Fin n ↦ ν) := by
  obtain ⟨hfm, M, hM⟩ := hf
  exact Integrable.of_bound (hfm.comp (measurable_pi_apply k)).aestronglyMeasurable M
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hM _)

theorem integral_coord_pi {f : X → ℝ} (hf : Bdd f) {n : ℕ} (k : Fin n) :
    ∫ x, f (x k) ∂(Measure.pi fun _ : Fin n ↦ ν) = ∫ y, f y ∂ν := by
  calc ∫ x, f (x k) ∂(Measure.pi fun _ : Fin n ↦ ν)
      = ∫ y, f y ∂((Measure.pi fun _ : Fin n ↦ ν).map (Function.eval k)) :=
        (integral_map (μ := Measure.pi fun _ : Fin n ↦ ν) (φ := Function.eval k) (f := f)
          (measurable_pi_apply k).aemeasurable hf.1.aestronglyMeasurable).symm
    _ = _ := by rw [(measurePreserving_eval (fun _ : Fin n ↦ ν) k).map_eq]

/-- The mean of the empirical sum is `n` times the mean. -/
theorem integral_empSum {f : X → ℝ} (hf : Bdd f) (n : ℕ) :
    ∫ x, (∑ k : Fin n, f (x k)) ∂(Measure.pi fun _ : Fin n ↦ ν) = n * ∫ y, f y ∂ν := by
  rw [integral_finsetSum _ fun k _ ↦ integrable_coord_pi ν hf k]
  simp only [integral_coord_pi ν hf, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

theorem memLp_two_of_bdd {f : X → ℝ} (hf : Bdd f) : MemLp f 2 ν := by
  obtain ⟨hfm, M, hM⟩ := hf
  exact MemLp.of_bound hfm.aestronglyMeasurable M
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hM x)

/-- The variance of the empirical sum is `n` times the variance. -/
theorem variance_empSum {f : X → ℝ} (hf : Bdd f) (n : ℕ) :
    variance (fun x : Fin n → X ↦ ∑ k, f (x k)) (Measure.pi fun _ : Fin n ↦ ν) =
      n * variance f ν := by
  have e : (fun x : Fin n → X ↦ ∑ k, f (x k)) = ∑ k : Fin n, fun x ↦ f (x k) := by
    funext x
    simp [Finset.sum_apply]
  rw [e, variance_sum_pi (X := fun _ : Fin n ↦ f) fun _ ↦ memLp_two_of_bdd ν hf]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- **Chebyshev for the empirical mean**: `P(|f̄_n − ⟨f⟩| ≥ ρ) ≤ Var f / (n ρ²)`. -/
theorem measureReal_empMean_far_le {f : X → ℝ} (hf : Bdd f) {n : ℕ} (hn : 0 < n) {ρ : ℝ}
    (hρ : 0 < ρ) :
    (Measure.pi fun _ : Fin n ↦ ν).real {x | ρ ≤ |(∑ k, f (x k)) / n - ∫ y, f y ∂ν|} ≤
      variance f ν / (n * ρ ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hX : MemLp (fun x : Fin n → X ↦ ∑ k, f (x k)) 2 (Measure.pi fun _ : Fin n ↦ ν) := by
    obtain ⟨hfm, M, hM⟩ := hf
    refine MemLp.of_bound (Finset.measurable_sum _ fun k _ ↦
      hfm.comp (measurable_pi_apply k)).aestronglyMeasurable (n * M) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs]
    calc |∑ k, f (x k)| ≤ ∑ k : Fin n, |f (x k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin n, M := Finset.sum_le_sum fun k _ ↦ hM _
      _ = n * M := by simp
  have h := meas_ge_le_variance_div_sq (μ := Measure.pi fun _ : Fin n ↦ ν) hX
    (c := n * ρ) (by positivity)
  rw [integral_empSum ν hf, variance_empSum ν hf] at h
  have hset : {x : Fin n → X | ρ ≤ |(∑ k, f (x k)) / n - ∫ y, f y ∂ν|} =
      {x | n * ρ ≤ |(∑ k, f (x k)) - n * ∫ y, f y ∂ν|} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    have e : (∑ k, f (x k)) - n * ∫ y, f y ∂ν = n * ((∑ k, f (x k)) / n - ∫ y, f y ∂ν) := by
      field_simp
    rw [e, abs_mul, abs_of_pos hn']
    constructor
    · intro h; exact mul_le_mul_of_nonneg_left h hn'.le
    · intro h; exact le_of_mul_le_mul_left h hn'
  rw [hset, measureReal_def]
  have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (div_nonneg (mul_nonneg hn'.le (variance_nonneg _ _))
    (by positivity))] at h'
  refine h'.trans (le_of_eq ?_)
  field_simp

end Chebyshev

section Main

variable [Nonempty X] {π L₀ : X → ℝ} (hπm : Measurable π) (hπi : Integrable π μ) (hπ : ∀ x, 0 < π x)
  (hπpos : 0 < ∫ x, π x ∂μ) (hL₀m : Measurable L₀) {M₀ : ℝ} (hL₀ : ∀ x, |L₀ x| ≤ M₀)
  {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i)) {t : ℝ} (ht : 0 < t)
include hπm hπi hπ hπpos hL₀m hL₀ hR ht

omit [Nonempty X] hπm hπi hπ hπpos hL₀m hL₀ ht in
set_option linter.unusedFintypeInType false in
theorem measurableSet_empMean_near (m : ι → ℝ) (n : ℕ) (ρ : ℝ) :
    MeasurableSet {x : Fin n → X | ∀ i, |empMean R n x i - m i| < ρ} := by
  have : {x : Fin n → X | ∀ i, |empMean R n x i - m i| < ρ} =
      ⋂ i, {x | |empMean R n x i - m i| < ρ} := by
    ext x; simp
  rw [this]
  refine MeasurableSet.iInter fun i ↦ measurableSet_lt ?_ measurable_const
  have hRm : Measurable (R i) := (hR i).1
  unfold empMean
  fun_prop

omit ht in
/-- **The empirical mean concentrates near the response under the product of a family member**:
`P_b^{⊗n}(∀ i, |R̄ᵢ − mᵢ(b)| < ρ) ≥ 1 − ∑ᵢ Var_b(Rᵢ)/(n ρ²)`. -/
theorem measureReal_empMean_near_ge (b : ι → ℝ) {n : ℕ} (hn : 0 < n) {ρ : ℝ} (hρ : 0 < ρ) :
    1 - ∑ i, variance (R i) (familyMeasure μ π L₀ R t b) / (n * ρ ^ 2) ≤
      (Measure.pi fun _ : Fin n ↦ familyMeasure μ π L₀ R t b).real
        {x | ∀ i, |empMean R n x i - meanMap μ π L₀ R t b i| < ρ} := by
  have := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) b
  set P := Measure.pi fun _ : Fin n ↦ familyMeasure μ π L₀ R t b with hP
  have hm : ∀ i, meanMap μ π L₀ R t b i = ∫ y, R i y ∂familyMeasure μ π L₀ R t b := fun i ↦
    (integral_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR b (R i)).symm
  have hmeas := measurableSet_empMean_near hR (meanMap μ π L₀ R t b) n ρ
  have hcompl : {x : Fin n → X | ∀ i, |empMean R n x i - meanMap μ π L₀ R t b i| < ρ}ᶜ ⊆
      ⋃ i, {x | ρ ≤ |(∑ k, R i (x k)) / n - ∫ y, R i y ∂familyMeasure μ π L₀ R t b|} := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_lt] at hx
    obtain ⟨i, hi⟩ := hx
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    simp only [Set.mem_ofPred_eq, empMean] at hi ⊢
    rwa [← hm i]
  have h1 := measureReal_compl (μ := P) hmeas
  have huniv : P.real univ = 1 := by
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one]
  rw [huniv] at h1
  have h2 : P.real {x : Fin n → X | ∀ i, |empMean R n x i - meanMap μ π L₀ R t b i| < ρ}ᶜ ≤
      ∑ i, variance (R i) (familyMeasure μ π L₀ R t b) / (n * ρ ^ 2) :=
    (measureReal_mono hcompl).trans ((measureReal_iUnion_fintype_le _).trans
      (Finset.sum_le_sum fun i _ ↦ measureReal_empMean_far_le _ (hR i) hn hρ))
  linarith

/-- **The tilt lower bound**: sampling from `P_a`, the empirical feature mean lands within `ε` of
the response `m_t(b)` of `b = a − (λ/t) u` with probability at least
`e^{−n (KL(P_b ‖ P_a) + δ)}` for all large `n`. -/
theorem tilt_lower_bound (a u : ι → ℝ) {lam : ℝ} (hlam : 0 ≤ lam) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.exp (-(n * (famKL μ π L₀ R t (a - (lam / t) • u) a + δ))) ≤
        (Measure.pi fun _ : Fin n ↦ familyMeasure μ π L₀ R t a).real
          {x | ∀ i, |empMean R n x i - meanMap μ π L₀ R t (a - (lam / t) • u) i| < ε} := by
  classical
  have hPb := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t)
    (a - (lam / t) • u)
  have hPa := isProbabilityMeasure_familyMeasure hπm hπi hπ hπpos hL₀m hL₀ hR (t := t) a
  obtain ⟨hDm, MD, hMD⟩ := bdd_dirLoss hR u
  -- the density of `P_a` with respect to `P_b`
  have hrm : Measurable fun x ↦
      Real.exp (-(lam * dirLoss R u x - famCgf μ π L₀ R t a (lam • u))) := by
    fun_prop
  have hr0 : ∀ x, 0 ≤ Real.exp (-(lam * dirLoss R u x - famCgf μ π L₀ R t a (lam • u))) :=
    fun x ↦ (Real.exp_pos _).le
  have hrC : ∀ x, Real.exp (-(lam * dirLoss R u x - famCgf μ π L₀ R t a (lam • u))) ≤
      Real.exp (lam * MD + |famCgf μ π L₀ R t a (lam • u)|) := fun x ↦ by
    apply Real.exp_le_exp.2
    have h1 := abs_le.1 (hMD x)
    have h2 := le_abs_self (famCgf μ π L₀ R t a (lam • u))
    nlinarith
  have hQ := familyMeasure_eq_withDensity_tilt hπm hπi hπ hπpos hL₀m hL₀ hR ht a u lam
  have : IsProbabilityMeasure ((familyMeasure μ π L₀ R t (a - (lam / t) • u)).withDensity
      fun x ↦ ENNReal.ofReal
        (Real.exp (-(lam * dirLoss R u x - famCgf μ π L₀ R t a (lam • u))))) := by
    rw [← hQ]; exact hPa
  -- the radius
  set S := ∑ i, |u i| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  set ρ := min ε (δ / (2 * (lam * S + 1))) with hρ
  have hρpos : 0 < ρ := lt_min hε (by positivity)
  have hρε : ρ ≤ ε := min_le_left _ _
  have hρδ : lam * S * ρ ≤ δ / 2 := by
    have hle : ρ ≤ δ / (2 * (lam * S + 1)) := min_le_right _ _
    calc lam * S * ρ ≤ lam * S * (δ / (2 * (lam * S + 1))) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = δ / 2 * (lam * S / (lam * S + 1)) := by field_simp
      _ ≤ δ / 2 := mul_le_of_le_one_right (by positivity)
          ((div_le_one (by positivity)).2 (by linarith))
  -- the variance budget and the threshold
  set V := ∑ i, variance (R i) (familyMeasure μ π L₀ R t (a - (lam / t) • u)) with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun i _ ↦ variance_nonneg _ _
  refine ⟨max (⌈2 * V / ρ ^ 2⌉₊ + 1) (⌈2 * Real.log 2 / δ⌉₊ + 1), fun n hn ↦ ?_⟩
  have hn1 : ⌈2 * V / ρ ^ 2⌉₊ + 1 ≤ n := (le_max_left _ _).trans hn
  have hn2 : ⌈2 * Real.log 2 / δ⌉₊ + 1 ≤ n := (le_max_right _ _).trans hn
  have hnpos : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnV : V / (n * ρ ^ 2) ≤ 1 / 2 := by
    have : 2 * V / ρ ^ 2 ≤ n := by
      have := Nat.le_ceil (2 * V / ρ ^ 2)
      have : ((⌈2 * V / ρ ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn1
      push_cast at this
      linarith
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at this
    nlinarith
  have hnδ : Real.exp (-(n * (δ / 2))) ≤ 1 / 2 := by
    have : 2 * Real.log 2 / δ ≤ n := by
      have := Nat.le_ceil (2 * Real.log 2 / δ)
      have : ((⌈2 * Real.log 2 / δ⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn2
      push_cast at this
      linarith
    rw [div_le_iff₀ hδ] at this
    have h2 : Real.log 2 ≤ n * (δ / 2) := by linarith
    calc Real.exp (-(n * (δ / 2))) ≤ Real.exp (-Real.log 2) :=
          Real.exp_le_exp.2 (by linarith)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log two_pos, one_div]
  -- the product density is bounded below on the near set
  have hsumD : ∀ x : Fin n → X, ∑ k, dirLoss R u (x k) = n * ∑ i, u i * empMean R n x i := by
    intro x
    simp only [dirLoss, empMean, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.mul_sum]
    field_simp
  -- the product density is the exponential of the empirical statistic
  have hprod : ∀ x : Fin n → X,
      ∏ k, Real.exp (-(lam * dirLoss R u (x k) - famCgf μ π L₀ R t a (lam • u))) =
      Real.exp (-(n * (lam * ∑ i, u i * empMean R n x i - famCgf μ π L₀ R t a (lam • u)))) := by
    intro x
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsumD x]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  -- it is bounded below on the near set
  have hge : ∀ x ∈ {x : Fin n → X |
      ∀ i, |empMean R n x i - meanMap μ π L₀ R t (a - (lam / t) • u) i| < ρ},
      Real.exp (-(n * (famKL μ π L₀ R t (a - (lam / t) • u) a + δ / 2))) ≤
        ∏ k, Real.exp (-(lam * dirLoss R u (x k) - famCgf μ π L₀ R t a (lam • u))) := by
    intro x hx
    have hx' : ∀ i, |empMean R n x i - meanMap μ π L₀ R t (a - (lam / t) • u) i| < ρ := hx
    rw [hprod x]
    apply Real.exp_le_exp.2
    have hdev : ∑ i, u i * empMean R n x i -
        ∑ i, u i * meanMap μ π L₀ R t (a - (lam / t) • u) i ≤ S * ρ := by
      rw [← Finset.sum_sub_distrib, hS, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      rw [← mul_sub]
      calc u i * (empMean R n x i - meanMap μ π L₀ R t (a - (lam / t) • u) i)
          ≤ |u i * (empMean R n x i - meanMap μ π L₀ R t (a - (lam / t) • u) i)| :=
            le_abs_self _
        _ = |u i| * |empMean R n x i - meanMap μ π L₀ R t (a - (lam / t) • u) i| := abs_mul _ _
        _ ≤ |u i| * ρ := mul_le_mul_of_nonneg_left (hx' i).le (abs_nonneg _)
    rw [famKL_tilt_eq hπm hπi hπ hπpos hL₀m hL₀ hR ht a u lam]
    have hmul : lam * (∑ i, u i * empMean R n x i -
        ∑ i, u i * meanMap μ π L₀ R t (a - (lam / t) • u) i) ≤ lam * (S * ρ) :=
      mul_le_mul_of_nonneg_left hdev hlam
    have hkey : lam * ∑ i, u i * empMean R n x i - famCgf μ π L₀ R t a (lam • u) ≤
        lam * ∑ i, u i * meanMap μ π L₀ R t (a - (lam / t) • u) i -
          famCgf μ π L₀ R t a (lam • u) + δ / 2 := by
      linarith [hmul, hρδ]
    exact neg_le_neg (mul_le_mul_of_nonneg_left hkey hn'.le)
  -- change of measure and Chebyshev
  have hcm := measureReal_pi_ge_of_density_ge (familyMeasure μ π L₀ R t (a - (lam / t) • u)) hrm
    hr0 hrC (n := n) (measurableSet_empMean_near hR _ n ρ) (Real.exp_pos _).le hge
  rw [← hQ] at hcm
  have hcheb := measureReal_empMean_near_ge hπm hπi hπ hπpos hL₀m hL₀ hR (t := t)
    (a - (lam / t) • u) hnpos hρpos
  rw [← Finset.sum_div, ← hV] at hcheb
  have hPbG : 1 / 2 ≤ (Measure.pi fun _ : Fin n ↦ familyMeasure μ π L₀ R t (a - (lam / t) • u)).real
      {x | ∀ i, |empMean R n x i - meanMap μ π L₀ R t (a - (lam / t) • u) i| < ρ} := by
    linarith [hcheb, hnV]
  have hmono : (Measure.pi fun _ : Fin n ↦ familyMeasure μ π L₀ R t a).real
      {x | ∀ i, |empMean R n x i - meanMap μ π L₀ R t (a - (lam / t) • u) i| < ρ} ≤
      (Measure.pi fun _ : Fin n ↦ familyMeasure μ π L₀ R t a).real
      {x | ∀ i, |empMean R n x i - meanMap μ π L₀ R t (a - (lam / t) • u) i| < ε} :=
    measureReal_mono fun x hx i ↦ lt_of_lt_of_le (hx i) hρε
  calc Real.exp (-(n * (famKL μ π L₀ R t (a - (lam / t) • u) a + δ)))
      = Real.exp (-(n * (famKL μ π L₀ R t (a - (lam / t) • u) a + δ / 2))) *
          Real.exp (-(n * (δ / 2))) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(n * (famKL μ π L₀ R t (a - (lam / t) • u) a + δ / 2))) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hnδ (Real.exp_pos _).le
    _ ≤ Real.exp (-(n * (famKL μ π L₀ R t (a - (lam / t) • u) a + δ / 2))) *
          (Measure.pi fun _ : Fin n ↦ familyMeasure μ π L₀ R t (a - (lam / t) • u)).real
            {x | ∀ i, |empMean R n x i - meanMap μ π L₀ R t (a - (lam / t) • u) i| < ρ} :=
        mul_le_mul_of_nonneg_left hPbG (Real.exp_pos _).le
    _ ≤ _ := hcm
    _ ≤ _ := hmono

end Main

end Laplace.Multi
