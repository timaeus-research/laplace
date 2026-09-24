/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ConstrainedLP
import Laplace.Multi.LogSectorTied

/-!
# The constant-unit model kernel on a fully tied face

The logarithmic endpoint of the comparison: a constrained model kernel with constant unit `a₀`,
constant weight `w₀`, no truth constraint (`Q = 0`) and all coordinates tied
(`(r_i + 1)/κ_i = λ`) is, for large `t`, a scaled tied-block integral
(`modelKernel_const_eq`), and the single-monomial theorem gives
`t^{γp + δλ} (log t)^{-k} K(t) → A w₀ ρ^{∑(r_i+1)} (B a₀ ρ^{∑κ_i})^{-λ} δ^k Γ(λ)/k! ∏ 1/κ_i`
(`tendsto_modelKernel_const`): the power–log law with its exact constant. With the moving-unit
sandwich this brackets a chart kernel whose LP optimal face is the whole coordinate simplex.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

variable {k : ℕ}

theorem cutVar_Q_zero {D γ q t : ℝ} (x : Fin (k + 1) → ℝ) :
    cutVar D γ q (0 : Fin (k + 1) → ℝ) t x = D * t ^ (-(γ / q)) := by
  unfold cutVar
  simp

theorem modelDomain_eq_of_Q_zero {ρ D γ q t : ℝ} (hcut : D * t ^ (-(γ / q)) < ρ) :
    modelDomain ρ D γ q (0 : Fin (k + 1) → ℝ) t = Set.pi univ fun _ ↦ Ioo (0 : ℝ) ρ := by
  ext x
  simp [modelDomain, cutVar_Q_zero, hcut]

/-- `x = ρ y` on the box: `∫_{(0,ρ)^{k+1}} g = ρ^{k+1} ∫_{(0,1)^{k+1}} g(ρ y)`. -/
theorem setIntegral_box_eq_rescale {ρ : ℝ} (hρ : 0 < ρ) (g : (Fin (k + 1) → ℝ) → ℝ)
    (hg : AEStronglyMeasurable g volume) :
    ∫ x in Set.pi univ (fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ), g x =
      ρ ^ (k + 1) * ∫ y in Set.pi univ (fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1), g (ρ • y) := by
  have hbox : MeasurableSet (Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have hbox1 : MeasurableSet (Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  rw [← integral_indicator hbox, ← integral_indicator hbox1,
    integral_comp_rescale (inv_pos.mpr hρ) (fun _ ↦ (1 : ℝ)) _ (hg.indicator hbox)]
  have hres : ∀ y : Fin (k + 1) → ℝ, rescale ρ⁻¹ (fun _ ↦ (1 : ℝ)) y = ρ • y := fun y ↦ by
    funext j
    simp [rescale, Real.rpow_neg_one]
  have hprod : ∏ _j : Fin (k + 1), ρ⁻¹ ^ (-(1 : ℝ)) = ρ ^ (k + 1) := by
    simp [Real.rpow_neg_one]
  rw [hprod]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  beta_reduce
  rw [hres]
  have hmem : ρ • y ∈ (Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ) ↔
      y ∈ Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1 := by
    simp only [Set.mem_univ_pi, Pi.smul_apply, smul_eq_mul, mem_Ioo]
    refine forall_congr' fun j ↦ ?_
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 hρ.le, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos hρ h1, by nlinarith⟩
  by_cases hy : y ∈ Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1
  · rw [Set.indicator_of_mem (hmem.mpr hy), Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem (hmem.not.mpr hy), Set.indicator_of_notMem hy]

/-- The constant-unit model kernel with `Q = 0` is a scaled tied-block integral (for `t` past the
cutoff). -/
theorem modelKernel_const_eq {ρ A B D γ p q δ : ℝ} {κ r : Fin (k + 1) → ℝ} {w₀ a₀ : ℝ}
    (hρ : 0 < ρ) {t : ℝ} (hcut : D * t ^ (-(γ / q)) < ρ) :
    modelKernel ρ A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t =
      A * t ^ (-(γ * p)) * (w₀ * ρ ^ (∑ i, (r i + 1)) *
        tiedBlockIntegral κ r (B * a₀ * ρ ^ (∑ i, κ i) * t ^ δ)) := by
  unfold modelKernel modelIntegrand tiedBlockIntegral
  rw [modelDomain_eq_of_Q_zero hcut]
  have hbox : MeasurableSet (Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  rw [integral_indicator hbox]
  have hmeas : AEStronglyMeasurable (fun x : Fin (k + 1) → ℝ ↦
      w₀ * (∏ j, x j ^ r j) * exp (-(B * t ^ δ * a₀ * ∏ j, x j ^ κ j))) volume := by
    refine Measurable.aestronglyMeasurable ?_
    have hr : Measurable fun x : Fin (k + 1) → ℝ ↦ ∏ j, x j ^ r j :=
      Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _
    have hκ : Measurable fun x : Fin (k + 1) → ℝ ↦ ∏ j, x j ^ κ j :=
      Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _
    exact (measurable_const.mul hr).mul (Real.measurable_exp.comp (measurable_const.mul hκ).neg)
  rw [setIntegral_box_eq_rescale hρ _ hmeas]
  have hpt : ∀ y ∈ Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) 1,
      w₀ * (∏ j, (ρ • y) j ^ r j) * exp (-(B * t ^ δ * a₀ * ∏ j, (ρ • y) j ^ κ j)) =
      w₀ * ρ ^ (∑ i, r i) *
        (exp (-(B * a₀ * ρ ^ (∑ i, κ i) * t ^ δ * ∏ i, y i ^ κ i)) * ∏ i, y i ^ r i) := by
    intro y hy
    have hy' : ∀ j, 0 < y j := fun j ↦ (Set.mem_univ_pi.mp hy j).1
    have e : ∀ e : Fin (k + 1) → ℝ, ∏ j, (ρ • y) j ^ e j = ρ ^ (∑ i, e i) * ∏ j, y j ^ e j := by
      intro e
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Real.rpow_sum_of_pos hρ, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ ↦ Real.mul_rpow hρ.le (hy' j).le
    rw [e, e]
    ring_nf
  rw [setIntegral_congr_fun (MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo) hpt,
    integral_const_mul]
  have hsum : ρ ^ (∑ i, (r i + 1)) = ρ ^ (k + 1) * ρ ^ (∑ i, r i) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Real.rpow_add hρ, Real.rpow_natCast]
    ring
  rw [hsum]
  ring

/-- **The power–log law of the constant-unit fully tied model kernel.** -/
theorem tendsto_modelKernel_const {ρ A B D γ p q δ : ℝ} {κ r : Fin (k + 1) → ℝ} {w₀ a₀ : ℝ}
    (hρ : 0 < ρ) (hκ : ∀ i, 0 < κ i) {lam : ℝ} (hlam : 0 < lam)
    (htied : ∀ i, (r i + 1) / κ i = lam) (hB : 0 < B) (ha₀ : 0 < a₀) (hδ : 0 < δ)
    (hγq : 0 < γ / q) :
    Tendsto (fun t ↦ t ^ (γ * p + δ * lam) / log t ^ k *
        modelKernel ρ A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t)
      atTop
      (𝓝 (A * w₀ * ρ ^ (∑ i, (r i + 1)) * (B * a₀ * ρ ^ (∑ i, κ i)) ^ (-lam) * δ ^ k *
        (Gamma lam / k.factorial * ∏ i, 1 / κ i))) := by
  set c : ℝ := B * a₀ * ρ ^ (∑ i, κ i) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcomp : Tendsto (fun t : ℝ ↦ c * t ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).const_mul_atTop hcpos
  have h1 := (tendsto_tiedBlock hκ hlam htied).comp hcomp
  have hlog : Tendsto (fun t : ℝ ↦ log (c * t ^ δ) / log t) atTop (𝓝 δ) := by
    have h0 : Tendsto (fun t : ℝ ↦ log c / log t + δ) atTop (𝓝 (0 + δ)) :=
      (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop).add tendsto_const_nhds
    rw [zero_add] at h0
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with t ht
    have hlt : 0 < log t := Real.log_pos ht
    rw [Real.log_mul hcpos.ne' (Real.rpow_pos_of_pos (one_pos.trans ht) _).ne',
      Real.log_rpow (one_pos.trans ht)]
    field_simp
  have hcut : ∀ᶠ t : ℝ in atTop, D * t ^ (-(γ / q)) < ρ := by
    have : Tendsto (fun t : ℝ ↦ D * t ^ (-(γ / q))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop hγq).const_mul D
    exact this.eventually_lt_const hρ
  have hbig : ∀ᶠ t : ℝ in atTop, 1 < c * t ^ δ := hcomp.eventually_gt_atTop 1
  have hlim := (h1.mul (hlog.pow k)).const_mul (A * w₀ * ρ ^ (∑ i, (r i + 1)) * c ^ (-lam))
  have e : A * w₀ * ρ ^ (∑ i, (r i + 1)) * c ^ (-lam) *
      (Gamma lam / k.factorial * (∏ i, 1 / κ i) * δ ^ k) =
      A * w₀ * ρ ^ (∑ i, (r i + 1)) * c ^ (-lam) * δ ^ k *
        (Gamma lam / k.factorial * ∏ i, 1 / κ i) := by ring
  rw [e] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1, hcut, hbig] with t ht hcut hbig
  have ht0 : 0 < t := one_pos.trans ht
  have hlt : 0 < log t := Real.log_pos ht
  have hlct : 0 < log (c * t ^ δ) := Real.log_pos hbig
  simp only [Function.comp_def]
  rw [modelKernel_const_eq hρ hcut, ← hc]
  have e1 : (c * t ^ δ) ^ lam = c ^ lam * t ^ (δ * lam) := by
    rw [Real.mul_rpow hcpos.le (Real.rpow_pos_of_pos ht0 _).le, ← Real.rpow_mul ht0.le]
  have e2 : t ^ (γ * p + δ * lam) = t ^ (γ * p) * t ^ (δ * lam) := Real.rpow_add ht0 _ _
  have e3 : t ^ (-(γ * p)) = (t ^ (γ * p))⁻¹ := Real.rpow_neg ht0.le _
  have e4 : c ^ (-lam) = (c ^ lam)⁻¹ := Real.rpow_neg hcpos.le _
  rw [e1, e2, e3, e4]
  have hne1 : t ^ (γ * p) ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
  have hne2 : c ^ lam ≠ 0 := (Real.rpow_pos_of_pos hcpos _).ne'
  have hne3 : log t ^ k ≠ 0 := pow_ne_zero _ hlt.ne'
  have hne4 : log (c * t ^ δ) ^ k ≠ 0 := pow_ne_zero _ hlct.ne'
  rw [div_pow]
  field_simp

end Laplace.Multi
