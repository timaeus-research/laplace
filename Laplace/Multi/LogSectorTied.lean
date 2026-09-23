/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LogSubstitutionPi
import Laplace.Multi.SimplexReduction
import Laplace.Multi.LogSectorCore

/-!
# The tied-block power–log theorem

For a tied block of exponents, `A_i > 0` and `(h_i + 1)/A_i = λ` for all `i : Fin (k+1)`,
`∫_{(0,1)^{k+1}} e^{−t ∏ x_i^{A_i}} ∏ x_i^{h_i} dx ~ Γ(λ)/k! · ∏ (1/A_i) · t^{−λ} (log t)^k`
(`tendsto_tiedBlock`): the logarithmic sector of dimension `k` (Astra,
`research_kernel_asymptotics_v1`, formula (10)–(11) with all coordinates tied). For `k = 1`,
`A = (2,2)`, `h = (0,0)`: `∫₀¹∫₀¹ e^{−t x² y²} dx dy ~ (√π/4) t^{−1/2} log t`, sharpening the
numerical claim of S13. Proof: the logarithmic substitution on the tied block
(`lintegral_pi_Ioo_tied`), the simplex reduction (`lintegral_pi_Ioi_comp_sum`) and the
one-dimensional core (`tendsto_logSector_core`).
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

/-- The tied-block monomial integral `∫_{(0,1)^{k+1}} e^{−t ∏ x^A} ∏ x^h`. -/
noncomputable def tiedBlockIntegral {k : ℕ} (A h : Fin (k + 1) → ℝ) (t : ℝ) : ℝ :=
  ∫ x in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1),
    exp (-(t * ∏ i, x i ^ A i)) * ∏ i, x i ^ h i

/-- The tied-block integral in `lintegral` form: the logarithmic substitution and the simplex
reduction. -/
theorem lintegral_tiedBlock {k : ℕ} {A h : Fin (k + 1) → ℝ} (hA : ∀ i, 0 < A i) {lam : ℝ}
    (htied : ∀ i, (h i + 1) / A i = lam) (s : ℝ) :
    ∫⁻ x in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1),
        ENNReal.ofReal (exp (-(s * ∏ i, x i ^ A i)) * ∏ i, x i ^ h i) =
      (∏ i, ENNReal.ofReal (1 / A i)) * ∫⁻ z in Ioi (0 : ℝ),
        ENNReal.ofReal (exp (-(s * exp (-z))) * exp (-(lam * z)) * z ^ k / (k.factorial : ℝ)) := by
  have hcube : MeasurableSet (Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1)) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have hG : Measurable fun c : ℝ ↦ ENNReal.ofReal (exp (-(s * c))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id).neg.exp
  have e1 : ∫⁻ x in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1),
      ENNReal.ofReal (exp (-(s * ∏ i, x i ^ A i)) * ∏ i, x i ^ h i) =
      ∫⁻ x in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1),
        (∏ i, ENNReal.ofReal (x i ^ h i)) * ENNReal.ofReal (exp (-(s * ∏ i, x i ^ A i))) := by
    refine setLIntegral_congr_fun hcube fun x hx ↦ ?_
    rw [ENNReal.ofReal_mul (exp_pos _).le,
      ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ rpow_nonneg (hx i (mem_univ _)).1.le _), mul_comm]
  rw [e1, lintegral_pi_Ioo_tied k A h hA lam htied _ hG]
  have hG₂ : Measurable fun z : ℝ ↦
      ENNReal.ofReal (exp (-(lam * z))) * ENNReal.ofReal (exp (-(s * exp (-z)))) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id).neg.exp).mul
      (hG.comp measurable_neg.exp)
  rw [lintegral_pi_Ioi_comp_sum _ hG₂ k]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi fun z hz ↦ ?_
  have hz : 0 < z := hz
  rw [mul_div_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (exp_pos _).le]
  ring

/-- The tied-block integral reduces to the one-dimensional core integral. -/
theorem tiedBlockIntegral_eq {k : ℕ} {A h : Fin (k + 1) → ℝ} (hA : ∀ i, 0 < A i) {lam : ℝ}
    (htied : ∀ i, (h i + 1) / A i = lam) (t : ℝ) :
    tiedBlockIntegral A h t = (∏ i, 1 / A i) * (1 / (k.factorial : ℝ)) *
      ∫ z in Ioi 0, exp (-(t * exp (-z))) * exp (-(lam * z)) * z ^ k := by
  unfold tiedBlockIntegral
  have hcube : MeasurableSet (Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1)) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have hprodA : Measurable fun x : Fin (k + 1) → ℝ ↦ ∏ i, x i ^ A i :=
    Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _
  have hprodh : Measurable fun x : Fin (k + 1) → ℝ ↦ ∏ i, x i ^ h i :=
    Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _
  have hf_meas : Measurable fun x : Fin (k + 1) → ℝ ↦
      exp (-(t * ∏ i, x i ^ A i)) * ∏ i, x i ^ h i :=
    (measurable_const.mul hprodA).neg.exp.mul hprodh
  have hnn : 0 ≤ᵐ[volume.restrict (Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1))]
      fun x : Fin (k + 1) → ℝ ↦ exp (-(t * ∏ i, x i ^ A i)) * ∏ i, x i ^ h i := by
    rw [Filter.EventuallyLE, ae_restrict_iff' hcube]
    refine Eventually.of_forall fun x hx ↦ ?_
    change (0 : ℝ) ≤ _
    exact mul_nonneg (exp_pos _).le
      (Finset.prod_nonneg fun i _ ↦ rpow_nonneg (hx i (mem_univ _)).1.le _)
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf_meas.aestronglyMeasurable, lintegral_tiedBlock hA
    htied t, ENNReal.toReal_mul, ENNReal.toReal_prod]
  have e2 : ∀ i ∈ (Finset.univ : Finset (Fin (k + 1))),
      (ENNReal.ofReal (1 / A i)).toReal = 1 / A i :=
    fun i _ ↦ ENNReal.toReal_ofReal (one_div_pos.mpr (hA i)).le
  rw [Finset.prod_congr rfl e2]
  have hJmeas : Measurable fun z : ℝ ↦
      exp (-(t * exp (-z))) * exp (-(lam * z)) * z ^ k / (k.factorial : ℝ) :=
    (((measurable_const.mul measurable_neg.exp).neg.exp.mul
      (measurable_const.mul measurable_id).neg.exp).mul (measurable_id.pow_const k)).div_const _
  have hJnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun z : ℝ ↦
      exp (-(t * exp (-z))) * exp (-(lam * z)) * z ^ k / (k.factorial : ℝ) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz ↦ ?_
    have hz : 0 < z := hz
    change (0 : ℝ) ≤ _
    positivity
  rw [← integral_eq_lintegral_of_nonneg_ae hJnn hJmeas.aestronglyMeasurable, integral_div]
  ring

/-- **The tied-block power–log theorem.** -/
theorem tendsto_tiedBlock {k : ℕ} {A h : Fin (k + 1) → ℝ} (hA : ∀ i, 0 < A i) {lam : ℝ}
    (hlam : 0 < lam) (htied : ∀ i, (h i + 1) / A i = lam) :
    Tendsto (fun t ↦ t ^ lam / log t ^ k * tiedBlockIntegral A h t) atTop
      (𝓝 (Gamma lam / k.factorial * ∏ i, 1 / A i)) := by
  have h1 := (tendsto_logSector_core hlam k).const_mul ((∏ i, 1 / A i) * (1 / (k.factorial : ℝ)))
  have e : (∏ i, 1 / A i) * (1 / (k.factorial : ℝ)) * Gamma lam =
      Gamma lam / k.factorial * ∏ i, 1 / A i := by ring
  rw [e] at h1
  refine h1.congr' (Eventually.of_forall fun t ↦ ?_)
  beta_reduce
  rw [tiedBlockIntegral_eq hA htied t]
  ring

end Laplace.Multi

namespace Laplace.Multi

/-- **The two-dimensional log sector**: `∫₀¹∫₀¹ e^{−t x² y²} dx dy ~ (√π/4) t^{−1/2} log t`. -/
theorem tendsto_x2y2 :
    Tendsto (fun t ↦ t ^ (1 / 2 : ℝ) / log t *
      ∫ x in Set.pi Set.univ (fun _ : Fin 2 ↦ Ioo (0 : ℝ) 1), exp (-(t * (x 0 ^ 2 * x 1 ^ 2))))
      atTop (𝓝 (√π / 4)) := by
  have hA : ∀ i : Fin 2, 0 < (![2, 2] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> norm_num
  have htied : ∀ i : Fin 2, ((![0, 0] : Fin 2 → ℝ) i + 1) / (![2, 2] : Fin 2 → ℝ) i = 1 / 2 := by
    intro i; fin_cases i <;> norm_num
  have h := tendsto_tiedBlock (k := 1) hA (lam := 1 / 2) one_half_pos htied
  have hc : Gamma (1 / 2) / (Nat.factorial 1 : ℝ) * ∏ i : Fin 2, 1 / (![2, 2] : Fin 2 → ℝ) i =
      √π / 4 := by
    rw [Real.Gamma_one_half_eq, Fin.prod_univ_two]
    simp only [Nat.factorial_one, Nat.cast_one, div_one, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hc] at h
  refine h.congr' (Eventually.of_forall fun t ↦ ?_)
  beta_reduce
  rw [pow_one]
  congr 1
  unfold tiedBlockIntegral
  refine setIntegral_congr_fun (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo)
    fun x _ ↦ ?_
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.succ_zero_eq_one, Real.rpow_two, Real.rpow_zero, mul_one]

end Laplace.Multi
