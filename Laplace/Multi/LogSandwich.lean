/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LogModel

/-!
# The two-sided power–log sandwich for a fully tied model kernel

Astra's "realistic short logarithmic theorem" (`review_endtoend_v1`, §4), for the fully tied case
with `Q = 0`: a model kernel with a moving unit `aL ≤ a ≤ aU` on the box and a moving weight
`0 ≤ W ≤ wU`, bounded below by `wL` on a smaller box `(0, RL)^{k+1}`, is squeezed between two
constant-unit model kernels (`modelKernel_le_const`, `const_le_modelKernel`), so that with
`Λ = γp + δλ` and the constant `tiedConst`,
`C(RL, aU, wL) − ε ≤ t^Λ (log t)^{-k} K(t) ≤ C(ρ, aL, wU) + ε` eventually
(`modelKernel_sandwich`). The constants differ by `(aU/aL)^λ`, `wU/wL` and the box ratio; the
exact constant needs the unit at the face point, which for a fully tied face is the origin.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

variable {k : ℕ}

/-- The power–log constant of the fully tied constant-unit model on the box of radius `R`. -/
noncomputable def tiedConst (A B δ : ℝ) (κ r : Fin (k + 1) → ℝ) (lam R a w : ℝ) : ℝ :=
  A * w * R ^ (∑ i, (r i + 1)) * (B * a * R ^ (∑ i, κ i)) ^ (-lam) * δ ^ k *
    (Gamma lam / k.factorial * ∏ i, 1 / κ i)

theorem tendsto_tiedConst {ρ A B D γ p q δ : ℝ} {κ r : Fin (k + 1) → ℝ} {w₀ a₀ : ℝ}
    (hρ : 0 < ρ) (hκ : ∀ i, 0 < κ i) {lam : ℝ} (hlam : 0 < lam)
    (htied : ∀ i, (r i + 1) / κ i = lam) (hB : 0 < B) (ha₀ : 0 < a₀) (hδ : 0 < δ)
    (hγq : 0 < γ / q) :
    Tendsto (fun t ↦ t ^ (γ * p + δ * lam) / log t ^ k *
        modelKernel ρ A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t)
      atTop (𝓝 (tiedConst A B δ κ r lam ρ a₀ w₀)) :=
  tendsto_modelKernel_const hρ hκ hlam htied hB ha₀ hδ hγq

/-! ### Integrability of the model integrand on a fully tied face -/

theorem prod_indicator_eq {ρ : ℝ} (f : Fin (k + 1) → ℝ → ℝ) (x : Fin (k + 1) → ℝ) :
    ∏ i, (Ioo (0 : ℝ) ρ).indicator (f i) (x i) =
      (Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ).indicator (fun x ↦ ∏ i, f i (x i)) x := by
  by_cases hx : x ∈ Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ
  · rw [Set.indicator_of_mem hx]
    exact Finset.prod_congr rfl fun i _ ↦ Set.indicator_of_mem (Set.mem_univ_pi.mp hx i) _
  · rw [Set.indicator_of_notMem hx]
    obtain ⟨j, hj⟩ : ∃ j, x j ∉ Ioo (0 : ℝ) ρ := by
      by_contra h
      push Not at h
      exact hx (Set.mem_univ_pi.mpr h)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)

theorem integrable_box_prod_rpow {ρ : ℝ} (hρ : 0 < ρ) {r : Fin (k + 1) → ℝ} (hr : ∀ i, -1 < r i) :
    Integrable fun x : Fin (k + 1) → ℝ ↦
      (Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ).indicator (fun x ↦ ∏ i, x i ^ r i) x := by
  have h1 : ∀ i, Integrable ((Ioo (0 : ℝ) ρ).indicator fun y ↦ y ^ r i) := fun i ↦ by
    rw [integrable_indicator_iff measurableSet_Ioo]
    have := (intervalIntegral.intervalIntegrable_rpow' (hr i) (a := 0) (b := ρ))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hρ.le] at this
    exact this.mono_set Ioo_subset_Ioc_self
  have := Integrable.fintype_prod (f := fun i y ↦ (Ioo (0 : ℝ) ρ).indicator (fun y ↦ y ^ r i) y)
    fun i ↦ h1 i
  rw [volume_pi]
  refine this.congr (Eventually.of_forall fun x ↦ ?_)
  exact prod_indicator_eq _ x

variable {ρ A B D γ p q δ : ℝ} {κ r : Fin (k + 1) → ℝ} {W a : (Fin (k + 1) → ℝ) → ℝ → ℝ}

theorem integrable_modelIntegrand_tied (hρ : 0 < ρ) (hr : ∀ i, -1 < r i) (hB : 0 < B)
    {t : ℝ} (ht : 0 < t) (hW : Measurable (Function.uncurry W))
    (ha : Measurable (Function.uncurry a)) {wU : ℝ} (hW0 : ∀ x v, 0 ≤ W x v)
    (hWup : ∀ x v, W x v ≤ wU)
    (ha0 : ∀ x v, (∀ j, x j ∈ Ioo (0 : ℝ) ρ) → 0 ≤ a x v) :
    Integrable (modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) → ℝ) κ r W a t) := by
  have hwU : 0 ≤ wU := (hW0 0 0).trans (hWup 0 0)
  refine Integrable.mono' ((integrable_box_prod_rpow hρ hr).const_mul wU)
    (measurable_modelIntegrand hW ha t).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  unfold modelIntegrand
  by_cases hx : x ∈ modelDomain ρ D γ q (0 : Fin (k + 1) → ℝ) t
  · have hbox : x ∈ Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ := hx.1
    have hxj : ∀ j, x j ∈ Ioo (0 : ℝ) ρ := Set.mem_univ_pi.mp hbox
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hbox]
    have hr0 : 0 ≤ ∏ j, x j ^ r j := Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hxj j).1.le _
    have hκ0 : 0 ≤ ∏ j, x j ^ κ j := Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hxj j).1.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hW0 _ _) hr0) (exp_pos _).le)]
    calc W x (cutVar D γ q 0 t x) * (∏ j, x j ^ r j) * exp (-(B * t ^ δ * a x (cutVar D γ q 0 t x) *
          ∏ j, x j ^ κ j)) ≤ wU * (∏ j, x j ^ r j) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hWup _ _) hr0)
            (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (mul_nonneg
              (mul_nonneg hB.le (rpow_pos_of_pos ht _).le) (ha0 _ _ hxj)) hκ0)))
            (exp_pos _).le (mul_nonneg hwU hr0)
      _ = wU * ∏ j, x j ^ r j := mul_one _
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact mul_nonneg hwU (Set.indicator_nonneg (fun x hx ↦ Finset.prod_nonneg fun j _ ↦
      rpow_nonneg (Set.mem_univ_pi.mp hx j).1.le _) x)

/-! ### The pointwise sandwich -/

theorem modelIntegrand_le_const {t : ℝ} (ht : 0 < t) (hB : 0 < B) {aL wU : ℝ}
    (hW0 : ∀ x v, 0 ≤ W x v) (hWup : ∀ x v, W x v ≤ wU)
    (halow : ∀ x v, (∀ j, x j ∈ Ioo (0 : ℝ) ρ) → aL ≤ a x v) (x : Fin (k + 1) → ℝ) :
    modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) → ℝ) κ r W a t x ≤
      modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wU) (fun _ _ ↦ aL) t x := by
  unfold modelIntegrand
  by_cases hx : x ∈ modelDomain ρ D γ q (0 : Fin (k + 1) → ℝ) t
  · have hxj : ∀ j, x j ∈ Ioo (0 : ℝ) ρ := Set.mem_univ_pi.mp hx.1
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    have hr0 : 0 ≤ ∏ j, x j ^ r j := Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hxj j).1.le _
    have hκ0 : 0 ≤ ∏ j, x j ^ κ j := Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hxj j).1.le _
    have hBt : 0 ≤ B * t ^ δ := mul_nonneg hB.le (rpow_pos_of_pos ht _).le
    refine mul_le_mul (mul_le_mul_of_nonneg_right (hWup _ _) hr0) (Real.exp_le_exp.mpr ?_)
      (exp_pos _).le (mul_nonneg ((hW0 0 0).trans (hWup 0 0)) hr0)
    have := halow x (cutVar D γ q 0 t x) hxj
    nlinarith [mul_nonneg hBt hκ0]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

theorem const_le_modelIntegrand {RL : ℝ} (hRρ : RL ≤ ρ) {t : ℝ} (ht : 0 < t) (hB : 0 < B)
    {aU wL : ℝ} (hW0 : ∀ x v, 0 ≤ W x v)
    (hWlow : ∀ x v, (∀ j, x j ∈ Ioo (0 : ℝ) RL) → wL ≤ W x v)
    (haup : ∀ x v, (∀ j, x j ∈ Ioo (0 : ℝ) ρ) → a x v ≤ aU)
    (hcut : D * t ^ (-(γ / q)) < RL) (x : Fin (k + 1) → ℝ) :
    modelIntegrand RL B D γ q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wL) (fun _ _ ↦ aU) t x ≤
      modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) → ℝ) κ r W a t x := by
  unfold modelIntegrand
  have hcutρ : D * t ^ (-(γ / q)) < ρ := hcut.trans_le hRρ
  rw [modelDomain_eq_of_Q_zero hcut, modelDomain_eq_of_Q_zero hcutρ]
  by_cases hx : x ∈ Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) RL
  · have hxj : ∀ j, x j ∈ Ioo (0 : ℝ) RL := Set.mem_univ_pi.mp hx
    have hxρ : ∀ j, x j ∈ Ioo (0 : ℝ) ρ := fun j ↦ ⟨(hxj j).1, (hxj j).2.trans_le hRρ⟩
    have hx' : x ∈ Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ := Set.mem_univ_pi.mpr hxρ
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    have hr0 : 0 ≤ ∏ j, x j ^ r j := Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hxj j).1.le _
    have hκ0 : 0 ≤ ∏ j, x j ^ κ j := Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hxj j).1.le _
    have hBt : 0 ≤ B * t ^ δ := mul_nonneg hB.le (rpow_pos_of_pos ht _).le
    refine mul_le_mul (mul_le_mul_of_nonneg_right (hWlow _ _ hxj) hr0) (Real.exp_le_exp.mpr ?_)
      (exp_pos _).le (mul_nonneg (hW0 _ _) hr0)
    have := haup x (cutVar D γ q 0 t x) hxρ
    nlinarith [mul_nonneg hBt hκ0]
  · rw [Set.indicator_of_notMem hx]
    exact Set.indicator_nonneg (fun x hx ↦ mul_nonneg (mul_nonneg (hW0 _ _)
      (Finset.prod_nonneg fun j _ ↦ rpow_nonneg (Set.mem_univ_pi.mp hx j).1.le _))
      (exp_pos _).le) x

/-! ### The sandwich -/

/-- **The two-sided power–log sandwich** for a fully tied model kernel with moving unit and
weight. -/
theorem modelKernel_sandwich (hρ : 0 < ρ) {RL : ℝ} (hR : 0 < RL) (hRρ : RL ≤ ρ) (hA : 0 ≤ A)
    (hκ : ∀ i, 0 < κ i) {lam : ℝ} (hlam : 0 < lam) (htied : ∀ i, (r i + 1) / κ i = lam)
    (hB : 0 < B) (hδ : 0 < δ) (hγq : 0 < γ / q) {aL aU wL wU : ℝ} (haL : 0 < aL) (hale : aL ≤ aU)
    (hwL : 0 ≤ wL) (hW : Measurable (Function.uncurry W)) (ha : Measurable (Function.uncurry a))
    (hW0 : ∀ x v, 0 ≤ W x v) (hWup : ∀ x v, W x v ≤ wU)
    (hWlow : ∀ x v, (∀ j, x j ∈ Ioo (0 : ℝ) RL) → wL ≤ W x v)
    (halow : ∀ x v, (∀ j, x j ∈ Ioo (0 : ℝ) ρ) → aL ≤ a x v)
    (haup : ∀ x v, (∀ j, x j ∈ Ioo (0 : ℝ) ρ) → a x v ≤ aU) :
    ∀ ε > 0, ∀ᶠ t in atTop,
      tiedConst A B δ κ r lam RL aU wL - ε ≤ t ^ (γ * p + δ * lam) / log t ^ k *
        modelKernel ρ A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r W a t ∧
      t ^ (γ * p + δ * lam) / log t ^ k *
        modelKernel ρ A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r W a t ≤
          tiedConst A B δ κ r lam ρ aL wU + ε := by
  intro ε hε
  have hr : ∀ i, -1 < r i := fun i ↦ by
    have h := htied i
    have hk := hκ i
    have : r i + 1 = lam * κ i := by
      field_simp at h
      linarith
    nlinarith [mul_pos hlam hk]
  have ha0 : ∀ x v, (∀ j, x j ∈ Ioo (0 : ℝ) ρ) → 0 ≤ a x v := fun x v hx ↦
    haL.le.trans (halow x v hx)
  have hlow := tendsto_tiedConst (A := A) (D := D) (p := p) (w₀ := wL) hR hκ hlam htied hB
    (haL.trans_le hale) hδ hγq
  have hup := tendsto_tiedConst (A := A) (D := D) (p := p) (w₀ := wU) hρ hκ hlam htied hB haL hδ
    hγq
  have hcut : ∀ᶠ t : ℝ in atTop, D * t ^ (-(γ / q)) < RL := by
    have : Tendsto (fun t : ℝ ↦ D * t ^ (-(γ / q))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop hγq).const_mul D
    exact this.eventually_lt_const hR
  filter_upwards [hlow.eventually (Metric.ball_mem_nhds _ hε),
    hup.eventually (Metric.ball_mem_nhds _ hε), hcut, eventually_gt_atTop 1] with t hl hu hcut ht
  have ht0 : 0 < t := one_pos.trans ht
  have hnorm : 0 ≤ t ^ (γ * p + δ * lam) / log t ^ k :=
    div_nonneg (rpow_pos_of_pos ht0 _).le (pow_pos (Real.log_pos ht) _).le
  have hAt : 0 ≤ A * t ^ (-(γ * p)) := mul_nonneg hA (rpow_pos_of_pos ht0 _).le
  have hI_mid := integrable_modelIntegrand_tied (D := D) (γ := γ) (q := q) (δ := δ) (κ := κ) hρ hr
    hB ht0 hW ha hW0 hWup ha0
  have hI_low := integrable_modelIntegrand_tied (D := D) (γ := γ) (q := q) (δ := δ) (κ := κ)
    (W := fun _ _ ↦ wL) (a := fun _ _ ↦ aU) hR hr hB ht0 measurable_const measurable_const
    (wU := wL) (fun _ _ ↦ hwL) (fun _ _ ↦ le_rfl) (fun _ _ _ ↦ (haL.trans_le hale).le)
  have hI_up := integrable_modelIntegrand_tied (D := D) (γ := γ) (q := q) (δ := δ) (κ := κ)
    (W := fun _ _ ↦ wU) (a := fun _ _ ↦ aL) hρ hr hB ht0 measurable_const measurable_const
    (wU := wU) (fun _ _ ↦ (hW0 0 0).trans (hWup 0 0)) (fun _ _ ↦ le_rfl) (fun _ _ _ ↦ haL.le)
  have hK_le : modelKernel ρ A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r W a t ≤
      modelKernel ρ A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wU) (fun _ _ ↦ aL) t := by
    unfold modelKernel
    exact mul_le_mul_of_nonneg_left
      (integral_mono hI_mid hI_up (modelIntegrand_le_const ht0 hB hW0 hWup halow)) hAt
  have hK_ge : modelKernel RL A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r (fun _ _ ↦ wL)
      (fun _ _ ↦ aU) t ≤ modelKernel ρ A B D γ p q δ (0 : Fin (k + 1) → ℝ) κ r W a t := by
    unfold modelKernel
    exact mul_le_mul_of_nonneg_left
      (integral_mono hI_low hI_mid (const_le_modelIntegrand hRρ ht0 hB hW0 hWlow haup hcut))
      hAt
  rw [Real.dist_eq] at hl hu
  have hl' := (abs_lt.mp hl).1
  have hu' := (abs_lt.mp hu).2
  constructor
  · have := mul_le_mul_of_nonneg_left hK_ge hnorm
    linarith
  · have := mul_le_mul_of_nonneg_left hK_le hnorm
    linarith

end Laplace.Multi
