/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LogSectorTied
import Laplace.Multi.LogSubstitutionPiGeneral

/-!
# The single-monomial power–log theorem with untied coordinates

The tied block `x : (0,1)^{k+1}` (exponents `A_i > 0`, `(h_i+1)/A_i = λ`) and an untied block
`x' : (0,1)^m` (exponents `A'_j > 0`, `(h'_j+1)/A'_j > λ`). The general monomial integral
`∫ e^{−t ∏ x^A ∏ x'^{A'}} ∏ x^h ∏ x'^{h'}` reduces exactly to an integral over the logarithmic
coordinates of the untied block of the one-dimensional core `J(s) = ∫₀^∞ e^{−s e^{−z}} e^{−λ z} z^k`
at `s = t e^{−∑ y'}` (`generalIntegral_eq`); its asymptotics is then
`Γ(λ)/k! · ∏ 1/A_i · ∏ 1/(h'_j + 1 − λ A'_j) · t^{−λ} (log t)^k` (`tendsto_general`, Astra's
formula (10)–(11)): the untied coordinates contribute `∫₀^∞ e^{−ε_j y} dy = 1/ε_j` with
`ε_j = (h'_j+1)/A'_j − λ`.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

/-- The core one-dimensional integral `J(s) = ∫₀^∞ e^{−s e^{−z}} e^{−λ z} z^k dz`. -/
noncomputable def coreIntegral (lam : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  ∫ z in Ioi 0, exp (-(s * exp (-z))) * exp (-(lam * z)) * z ^ k

theorem coreIntegral_nonneg (lam : ℝ) (k : ℕ) (s : ℝ) : 0 ≤ coreIntegral lam k s :=
  setIntegral_nonneg measurableSet_Ioi fun z hz ↦ by
    have : 0 < z := hz
    positivity

theorem measurable_coreIntegral (lam : ℝ) (k : ℕ) : Measurable (coreIntegral lam k) := by
  have hF : Continuous fun p : ℝ × ℝ ↦
      exp (-(p.1 * exp (-p.2))) * exp (-(lam * p.2)) * p.2 ^ k := by
    fun_prop
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi 0))).measurable

/-- The core integrand is integrable for `s ≥ 0`. -/
theorem integrableOn_coreIntegrand {lam : ℝ} (hlam : 0 < lam) (k : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    IntegrableOn (fun z : ℝ ↦ exp (-(s * exp (-z))) * exp (-(lam * z)) * z ^ k) (Ioi 0) := by
  have h0 : IntegrableOn (fun z : ℝ ↦ z ^ (k : ℝ) * exp (-lam * z ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith) one_pos hlam
  refine h0.mono' ?_ ?_
  · exact (Measurable.aestronglyMeasurable
      (((measurable_const.mul measurable_neg.exp).neg.exp.mul
        (measurable_const.mul measurable_id).neg.exp).mul (measurable_id.pow_const k)))
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz ↦ ?_
    have hz : 0 < z := hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_one, Real.rpow_natCast]
    have h1 : exp (-(s * exp (-z))) ≤ 1 := by
      rw [exp_le_one_iff]
      have : 0 ≤ s * exp (-z) := by positivity
      linarith
    calc exp (-(s * exp (-z))) * exp (-(lam * z)) * z ^ k
        ≤ 1 * exp (-(lam * z)) * z ^ k := by gcongr
      _ = z ^ k * exp (-lam * z) := by rw [one_mul, neg_mul]; ring

/-- The tied-block integral in `lintegral` form, as `ofReal` of the core (`s ≥ 0`). -/
theorem lintegral_tiedBlock_ofReal {k : ℕ} {A h : Fin (k + 1) → ℝ} (hA : ∀ i, 0 < A i) {lam : ℝ}
    (hlam : 0 < lam) (htied : ∀ i, (h i + 1) / A i = lam) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ x in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1),
        ENNReal.ofReal (exp (-(s * ∏ i, x i ^ A i)) * ∏ i, x i ^ h i) =
      ENNReal.ofReal ((∏ i, 1 / A i) * (1 / (k.factorial : ℝ)) * coreIntegral lam k s) := by
  rw [lintegral_tiedBlock hA htied s]
  have hint : IntegrableOn
      (fun z : ℝ ↦ exp (-(s * exp (-z))) * exp (-(lam * z)) * z ^ k / (k.factorial : ℝ)) (Ioi 0) :=
    (integrableOn_coreIntegrand hlam k hs).div_const _
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun z : ℝ ↦
      exp (-(s * exp (-z))) * exp (-(lam * z)) * z ^ k / (k.factorial : ℝ) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz ↦ ?_
    have hz : 0 < z := hz
    change (0 : ℝ) ≤ _
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ (one_div_pos.mpr (hA i)).le),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ ↦ (one_div_pos.mpr (hA i)).le)]
  congr 1
  unfold coreIntegral
  rw [integral_div]
  ring

/-- The general monomial integral: a tied block times an untied block. -/
noncomputable def generalIntegral {k m : ℕ} (A h : Fin (k + 1) → ℝ) (A' h' : Fin m → ℝ) (t : ℝ) :
    ℝ :=
  ∫ p in (Set.pi Set.univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1) ×ˢ
      (Set.pi Set.univ fun _ : Fin m ↦ Ioo (0 : ℝ) 1),
    exp (-(t * ((∏ i, p.1 i ^ A i) * ∏ j, p.2 j ^ A' j))) *
      ((∏ i, p.1 i ^ h i) * ∏ j, p.2 j ^ h' j)

/-- **Exact reduction to the untied block**, for `t ≥ 0`. -/
theorem generalIntegral_eq {k m : ℕ} {A h : Fin (k + 1) → ℝ} (hA : ∀ i, 0 < A i) {lam : ℝ}
    (hlam : 0 < lam) (htied : ∀ i, (h i + 1) / A i = lam) {A' h' : Fin m → ℝ}
    (hA' : ∀ j, 0 < A' j) {t : ℝ} (ht : 0 ≤ t) :
    generalIntegral A h A' h' t = (∏ i, 1 / A i) * (1 / (k.factorial : ℝ)) * (∏ j, 1 / A' j) *
      ∫ y' in Set.pi Set.univ (fun _ : Fin m ↦ Ioi (0 : ℝ)),
        (∏ j, exp (-((h' j + 1) / A' j * y' j))) * coreIntegral lam k (t * exp (-(∑ j, y' j))) := by
  unfold generalIntegral
  have hS₁ : MeasurableSet (Set.pi Set.univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have hS₂ : MeasurableSet (Set.pi Set.univ fun _ : Fin m ↦ Ioo (0 : ℝ) 1) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have hprodA : Measurable fun x : Fin (k + 1) → ℝ ↦ ∏ i, x i ^ A i :=
    Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _
  have hprodh : Measurable fun x : Fin (k + 1) → ℝ ↦ ∏ i, x i ^ h i :=
    Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _
  have hprodA' : Measurable fun x : Fin m → ℝ ↦ ∏ j, x j ^ A' j :=
    Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _
  have hprodh' : Measurable fun x : Fin m → ℝ ↦ ∏ j, x j ^ h' j :=
    Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _
  have hf_meas : Measurable fun p : (Fin (k + 1) → ℝ) × (Fin m → ℝ) ↦
      exp (-(t * ((∏ i, p.1 i ^ A i) * ∏ j, p.2 j ^ A' j))) *
        ((∏ i, p.1 i ^ h i) * ∏ j, p.2 j ^ h' j) :=
    (measurable_const.mul ((hprodA.comp measurable_fst).mul
      (hprodA'.comp measurable_snd))).neg.exp.mul
      ((hprodh.comp measurable_fst).mul (hprodh'.comp measurable_snd))
  have hnn : 0 ≤ᵐ[volume.restrict ((Set.pi Set.univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1) ×ˢ
      (Set.pi Set.univ fun _ : Fin m ↦ Ioo (0 : ℝ) 1))]
      fun p : (Fin (k + 1) → ℝ) × (Fin m → ℝ) ↦
        exp (-(t * ((∏ i, p.1 i ^ A i) * ∏ j, p.2 j ^ A' j))) *
          ((∏ i, p.1 i ^ h i) * ∏ j, p.2 j ^ h' j) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' (hS₁.prod hS₂)]
    refine Eventually.of_forall fun p hp ↦ ?_
    change (0 : ℝ) ≤ _
    refine mul_nonneg (exp_pos _).le (mul_nonneg ?_ ?_)
    · exact Finset.prod_nonneg fun i _ ↦ rpow_nonneg (hp.1 i (mem_univ _)).1.le _
    · exact Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hp.2 j (mem_univ _)).1.le _
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf_meas.aestronglyMeasurable, Measure.volume_eq_prod,
    ← Measure.prod_restrict, lintegral_prod_symm' (fun p : (Fin (k + 1) → ℝ) × (Fin m → ℝ) ↦
      ENNReal.ofReal (exp (-(t * ((∏ i, p.1 i ^ A i) * ∏ j, p.2 j ^ A' j))) *
        ((∏ i, p.1 i ^ h i) * ∏ j, p.2 j ^ h' j))) (ENNReal.measurable_ofReal.comp hf_meas)]
  -- the inner tied-block integral, for each point of the untied cube
  have hin : ∀ x' ∈ Set.pi Set.univ (fun _ : Fin m ↦ Ioo (0 : ℝ) 1),
      ∫⁻ x in Set.pi Set.univ (fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1),
        ENNReal.ofReal (exp (-(t * ((∏ i, x i ^ A i) * ∏ j, x' j ^ A' j))) *
          ((∏ i, x i ^ h i) * ∏ j, x' j ^ h' j)) =
      (∏ j, ENNReal.ofReal (x' j ^ h' j)) *
        ENNReal.ofReal ((∏ i, 1 / A i) * (1 / (k.factorial : ℝ)) *
          coreIntegral lam k (t * ∏ j, x' j ^ A' j)) := by
    intro x' hx'
    have hc : 0 ≤ ∏ j, x' j ^ A' j :=
      Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hx' j (mem_univ _)).1.le _
    have hd : 0 ≤ ∏ j, x' j ^ h' j :=
      Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hx' j (mem_univ _)).1.le _
    have hm : Measurable fun x : Fin (k + 1) → ℝ ↦
        ENNReal.ofReal (exp (-((t * ∏ j, x' j ^ A' j) * ∏ i, x i ^ A i)) * ∏ i, x i ^ h i) :=
      ((measurable_const.mul hprodA).neg.exp.mul hprodh).ennreal_ofReal
    rw [← lintegral_tiedBlock_ofReal hA hlam htied (mul_nonneg ht hc),
      ← ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ rpow_nonneg (hx' j (mem_univ _)).1.le _),
      ← lintegral_const_mul _ hm]
    refine setLIntegral_congr_fun hS₁ fun x _ ↦ ?_
    rw [← ENNReal.ofReal_mul hd]
    congr 1
    ring_nf
  rw [setLIntegral_congr_fun hS₂ hin]
  -- the untied block: the logarithmic substitution
  have hG : Measurable fun c : ℝ ↦ ENNReal.ofReal ((∏ i, 1 / A i) * (1 / (k.factorial : ℝ)) *
      coreIntegral lam k (t * c)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((measurable_coreIntegral lam k).comp (measurable_const.mul measurable_id)))
  rw [lintegral_pi_Ioo_log m A' h' hA' _ hG, ENNReal.toReal_mul, ENNReal.toReal_prod]
  have e2 : ∀ j ∈ (Finset.univ : Finset (Fin m)), (ENNReal.ofReal (1 / A' j)).toReal = 1 / A' j :=
    fun j _ ↦ ENNReal.toReal_ofReal (one_div_pos.mpr (hA' j)).le
  rw [Finset.prod_congr rfl e2]
  -- back to the Bochner integral
  have hSy : MeasurableSet (Set.pi Set.univ fun _ : Fin m ↦ Ioi (0 : ℝ)) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi
  have hKmeas : Measurable fun y' : Fin m → ℝ ↦
      (∏ j, exp (-((h' j + 1) / A' j * y' j))) * ((∏ i, 1 / A i) * (1 / (k.factorial : ℝ)) *
        coreIntegral lam k (t * exp (-(∑ j, y' j)))) :=
    (Finset.measurable_prod _ fun j _ ↦
      (measurable_const.mul (measurable_pi_apply j)).neg.exp).mul
      (measurable_const.mul ((measurable_coreIntegral lam k).comp
        (measurable_const.mul (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j).neg.exp)))
  have hKnn : 0 ≤ᵐ[volume.restrict (Set.pi Set.univ fun _ : Fin m ↦ Ioi (0 : ℝ))]
      fun y' : Fin m → ℝ ↦
        (∏ j, exp (-((h' j + 1) / A' j * y' j))) * ((∏ i, 1 / A i) * (1 / (k.factorial : ℝ)) *
          coreIntegral lam k (t * exp (-(∑ j, y' j)))) := by
    refine Eventually.of_forall fun y' ↦ ?_
    change (0 : ℝ) ≤ _
    refine mul_nonneg (Finset.prod_nonneg fun j _ ↦ (exp_pos _).le) (mul_nonneg ?_
      (coreIntegral_nonneg _ _ _))
    exact mul_nonneg (Finset.prod_nonneg fun i _ ↦ (one_div_pos.mpr (hA i)).le) (by positivity)
  have e3 : ∫⁻ y' in Set.pi Set.univ (fun _ : Fin m ↦ Ioi (0 : ℝ)),
      (∏ j, ENNReal.ofReal (exp (-((h' j + 1) / A' j * y' j)))) *
        ENNReal.ofReal ((∏ i, 1 / A i) * (1 / (k.factorial : ℝ)) *
          coreIntegral lam k (t * exp (-(∑ j, y' j)))) =
      ∫⁻ y' in Set.pi Set.univ (fun _ : Fin m ↦ Ioi (0 : ℝ)),
        ENNReal.ofReal ((∏ j, exp (-((h' j + 1) / A' j * y' j))) *
          ((∏ i, 1 / A i) * (1 / (k.factorial : ℝ)) *
            coreIntegral lam k (t * exp (-(∑ j, y' j))))) := by
    refine lintegral_congr fun y' ↦ ?_
    rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ ↦ (exp_pos _).le),
      ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ (exp_pos _).le)]
  rw [e3, ← integral_eq_lintegral_of_nonneg_ae hKnn hKmeas.aestronglyMeasurable]
  have e4 : ∀ y' : Fin m → ℝ,
      (∏ j, exp (-((h' j + 1) / A' j * y' j))) * ((∏ i, 1 / A i) * (1 / (k.factorial : ℝ)) *
        coreIntegral lam k (t * exp (-(∑ j, y' j)))) =
      ((∏ i, 1 / A i) * (1 / (k.factorial : ℝ))) *
        ((∏ j, exp (-((h' j + 1) / A' j * y' j))) * coreIntegral lam k (t * exp (-(∑ j, y' j)))) :=
    fun y' ↦ by ring
  simp_rw [e4]
  rw [integral_const_mul]
  ring

end Laplace.Multi
