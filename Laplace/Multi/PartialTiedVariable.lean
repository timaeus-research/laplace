/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.PartialTiedModel
import Laplace.Multi.LogSandwich

/-!
# The partially tied model with moving unit and weight

The variable-unit version of `tendsto_modelKernel_partial`: the weight `W` and the unit `a` may
depend on the box point and the cutoff variable, bounded (`0 ≤ W ≤ wU`, `aL ≤ a` on the box) and
continuous at every face point `(0_T, z_N, 0)`. Slicing along the worse block `N`, each slice is
a fully tied kernel with moving unit `a(y, z, v) ∏_N z^κ` and weight `W(y, z, v)`, whose exact
power–log constant is `tendsto_modelKernel_tied`; the slices are dominated by the constant-unit
kernel at `(wU, aL ∏_N z^κ)`, for which the all-scale tied-block bound gives the majorant
`C ∏_N z^{r − λκ}`. Hence (`tendsto_modelKernel_partial_var`)

`t^{γp+δλ}/(log t)^k K(t) → A δ^k Γ(λ)/k! ∏_T κ_i^{-1} ∫_{(0,ρ)^N} W (B a)^{-λ} ∏_N z^{r−λκ} dz`
(the weight and the unit evaluated at `(0_T, z, 0)`):

the face density of a partially tied face is the residual monomial weighted by the weight and
the `−λ` power of the unit at the face point.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

variable {k : ℕ} {ν : Type*} [Fintype ν]

omit [Fintype ν] in
theorem measurable_elim_const (z : ν → ℝ) :
    Measurable fun y : Fin (k + 1) → ℝ ↦ Sum.elim y z := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  cases i with
  | inl i => exact measurable_pi_apply i
  | inr j => exact measurable_const

omit [Fintype ν] in
theorem continuous_elim_const (z : ν → ℝ) :
    Continuous fun y : Fin (k + 1) → ℝ ↦ Sum.elim y z := by
  refine continuous_pi fun i ↦ ?_
  cases i with
  | inl i => exact continuous_apply i
  | inr j => exact continuous_const

/-- The all-scale bound on the constant-unit tied slice at the effective constant
`aL ∏_N z^κ`: uniformly in `t ≥ e` and in `z` on the box, `C ∏_N z^{-λκ}`. -/
theorem slice_const_bound {ρ B D γ q δ : ℝ} {κ r : Fin (k + 1) ⊕ ν → ℝ} (hρ : 0 < ρ)
    (hκ : ∀ i, 0 < κ i) {lam : ℝ} (hlam : 0 < lam)
    (htied : ∀ i, (r (Sum.inl i) + 1) / κ (Sum.inl i) = lam) (hB : 0 < B) {aL : ℝ}
    (haL : 0 < aL) (hδ : 0 < δ) {w : ℝ} (hw : 0 ≤ w) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ t : ℝ, exp 1 ≤ t → D * t ^ (-(γ / q)) < ρ →
      ∀ z : ν → ℝ, z ∈ (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ) →
      t ^ (δ * lam) / log t ^ k *
        modelKernel ρ 1 B D γ 0 q δ (0 : Fin (k + 1) → ℝ) (fun i ↦ κ (Sum.inl i))
          (fun i ↦ r (Sum.inl i)) (fun _ _ ↦ w) (fun _ _ ↦ aL * ∏ j, z j ^ κ (Sum.inr j)) t ≤
        Cb * (∏ j, z j ^ κ (Sum.inr j)) ^ (-lam) := by
  have hκT : ∀ i : Fin (k + 1), 0 < κ (Sum.inl i) := fun i ↦ hκ _
  obtain ⟨M, hM0, hM⟩ := tiedBlockIntegral_le_bound (A := fun i ↦ κ (Sum.inl i))
    (h := fun i ↦ r (Sum.inl i)) hκT hlam htied
  set c₁ : ℝ := B * aL * ρ ^ (∑ i, κ (Sum.inl i)) with hc₁
  have hc₁pos : 0 < c₁ := by rw [hc₁]; positivity
  set L₀ : ℝ := max 0 (log (c₁ * ρ ^ (∑ j, κ (Sum.inr j)))) with hL₀
  have hL₀0 : 0 ≤ L₀ := le_max_left _ _
  refine ⟨w * ρ ^ (∑ i, (r (Sum.inl i) + 1)) * M * c₁ ^ (-lam) * (1 + L₀ + δ) ^ k,
    by positivity, fun t ht hcut z hz ↦ ?_⟩
  have ht0 : 0 < t := (exp_pos 1).trans_le ht
  have hlogt : 1 ≤ log t := by rw [← log_exp 1]; exact log_le_log (exp_pos 1) ht
  have hlogpos : 0 < log t := by linarith
  have hP : 0 < ∏ j, z j ^ κ (Sum.inr j) :=
    Finset.prod_pos fun j _ ↦ rpow_pos_of_pos (Set.mem_univ_pi.mp hz j).1 _
  have hPle : ∏ j, z j ^ κ (Sum.inr j) ≤ ρ ^ (∑ j, κ (Sum.inr j)) := by
    rw [Real.rpow_sum_of_pos hρ]
    exact Finset.prod_le_prod (fun j _ ↦ rpow_nonneg (Set.mem_univ_pi.mp hz j).1.le _)
      fun j _ ↦ Real.rpow_le_rpow (Set.mem_univ_pi.mp hz j).1.le (Set.mem_univ_pi.mp hz j).2.le
        (hκ _).le
  set P : ℝ := ∏ j, z j ^ κ (Sum.inr j) with hPdef
  rw [modelKernel_const_eq hρ hcut, mul_zero, neg_zero, Real.rpow_zero, mul_one, one_mul]
  set s : ℝ := c₁ * P * t ^ δ with hs
  have hspos : 0 < s := by rw [hs]; positivity
  have e1 : B * (aL * P) * ρ ^ (∑ i, κ (Sum.inl i)) * t ^ δ = s := by rw [hs, hc₁]; ring
  rw [e1]
  have hTB := hM s hspos
  have e2 : t ^ (δ * lam) * s ^ (-lam) = (c₁ * P) ^ (-lam) := by
    rw [hs, Real.mul_rpow (by positivity) (rpow_pos_of_pos ht0 _).le, ← Real.rpow_mul ht0.le,
      show δ * -lam = -(δ * lam) by ring, Real.rpow_neg ht0.le]
    have hpos : 0 < t ^ (δ * lam) := rpow_pos_of_pos ht0 _
    rw [mul_comm ((c₁ * P) ^ (-lam)), ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  have e3 : 1 + max 0 (log s) ≤ (1 + L₀ + δ) * log t := by
    have hlogs : log s = log (c₁ * P) + δ * log t := by
      rw [hs, log_mul (by positivity) (rpow_pos_of_pos ht0 _).ne', Real.log_rpow ht0]
    have hlog1 : log (c₁ * P) ≤ log (c₁ * ρ ^ (∑ j, κ (Sum.inr j))) :=
      log_le_log (by positivity) (mul_le_mul_of_nonneg_left hPle hc₁pos.le)
    have hmax : max 0 (log s) ≤ L₀ + δ * log t := by
      refine max_le (by positivity) ?_
      rw [hlogs]
      linarith [le_max_right 0 (log (c₁ * ρ ^ (∑ j, κ (Sum.inr j))))]
    nlinarith [mul_nonneg hL₀0 (sub_nonneg.mpr hlogt)]
  have hnorm : 0 ≤ t ^ (δ * lam) / log t ^ k :=
    div_nonneg (rpow_pos_of_pos ht0 _).le (pow_pos hlogpos _).le
  have hne : log t ^ k ≠ 0 := pow_ne_zero _ hlogpos.ne'
  calc t ^ (δ * lam) / log t ^ k * (w * ρ ^ (∑ i, (r (Sum.inl i) + 1)) *
        tiedBlockIntegral (fun i ↦ κ (Sum.inl i)) (fun i ↦ r (Sum.inl i)) s)
      ≤ t ^ (δ * lam) / log t ^ k * (w * ρ ^ (∑ i, (r (Sum.inl i) + 1)) *
        (M * s ^ (-lam) * (1 + max 0 (log s)) ^ k)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTB (by positivity)) hnorm
    _ = w * ρ ^ (∑ i, (r (Sum.inl i) + 1)) * M * (t ^ (δ * lam) * s ^ (-lam)) *
        ((1 + max 0 (log s)) / log t) ^ k := by
        rw [div_pow]
        field_simp
    _ ≤ w * ρ ^ (∑ i, (r (Sum.inl i) + 1)) * M * (c₁ * P) ^ (-lam) * (1 + L₀ + δ) ^ k := by
        rw [e2]
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ k) (by positivity)
        rw [div_le_iff₀ hlogpos]
        exact e3
    _ = w * ρ ^ (∑ i, (r (Sum.inl i) + 1)) * M * c₁ ^ (-lam) * (1 + L₀ + δ) ^ k *
        P ^ (-lam) := by
        rw [Real.mul_rpow hc₁pos.le hP.le]
        ring

/-- **The partially tied model with moving unit and weight.** -/
theorem tendsto_modelKernel_partial_var {ρ A B D γ p q δ : ℝ} {κ r : Fin (k + 1) ⊕ ν → ℝ}
    {W a : (Fin (k + 1) ⊕ ν → ℝ) → ℝ → ℝ}
    (hρ : 0 < ρ) (hD : 0 ≤ D) (hκ : ∀ i, 0 < κ i) {lam : ℝ} (hlam : 0 < lam)
    (htied : ∀ i, (r (Sum.inl i) + 1) / κ (Sum.inl i) = lam)
    (hgap : ∀ j, lam * κ (Sum.inr j) < r (Sum.inr j) + 1)
    (hB : 0 < B) (hδ : 0 < δ) (hγq : 0 < γ / q) {aL wU : ℝ} (haL : 0 < aL)
    (hW : Measurable (Function.uncurry W)) (ha : Measurable (Function.uncurry a))
    (hW0 : ∀ x v, 0 ≤ W x v) (hWup : ∀ x v, W x v ≤ wU)
    (halow : ∀ x v, (∀ j, x j ∈ Ioo (0 : ℝ) ρ) → 0 ≤ v → v < ρ → aL ≤ a x v)
    (ha₀ : ∀ z : ν → ℝ, (∀ j, z j ∈ Ioo (0 : ℝ) ρ) → 0 < a (Sum.elim 0 z) 0)
    (hWlim : ∀ z : ν → ℝ, (∀ j, z j ∈ Ioo (0 : ℝ) ρ) →
      ContinuousAt (Function.uncurry W) (Sum.elim 0 z, 0))
    (halim : ∀ z : ν → ℝ, (∀ j, z j ∈ Ioo (0 : ℝ) ρ) →
      ContinuousAt (Function.uncurry a) (Sum.elim 0 z, 0)) :
    Tendsto (fun t ↦ t ^ (γ * p + δ * lam) / log t ^ k *
        modelKernel ρ A B D γ p q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r W a t) atTop
      (𝓝 (A * (δ ^ k * (Gamma lam / k.factorial * ∏ i, 1 / κ (Sum.inl i))) *
        ∫ z in Set.pi univ (fun _ : ν ↦ Ioo (0 : ℝ) ρ),
          W (Sum.elim 0 z) 0 * (B * a (Sum.elim 0 z) 0) ^ (-lam) *
            ∏ j, z j ^ (r (Sum.inr j) - lam * κ (Sum.inr j)))) := by
  classical
  have hκT : ∀ i : Fin (k + 1), 0 < κ (Sum.inl i) := fun i ↦ hκ _
  have hr : ∀ i, -1 < r i := by
    rintro (i | j)
    · have h := htied i
      rw [div_eq_iff (hκT i).ne'] at h
      nlinarith [mul_pos hlam (hκT i)]
    · have := hgap j
      nlinarith [mul_pos hlam (hκ (Sum.inr j))]
  have hrT : ∀ i : Fin (k + 1), -1 < r (Sum.inl i) := fun i ↦ hr _
  have hwU : 0 ≤ wU := (hW0 0 0).trans (hWup 0 0)
  have hboxN : MeasurableSet (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have hPNpos : ∀ z ∈ (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ), 0 < ∏ j, z j ^ κ (Sum.inr j) :=
    fun z hz ↦ Finset.prod_pos fun j _ ↦ rpow_pos_of_pos (Set.mem_univ_pi.mp hz j).1 _
  have hcut : ∀ᶠ t : ℝ in atTop, D * t ^ (-(γ / q)) < ρ := by
    have : Tendsto (fun t : ℝ ↦ D * t ^ (-(γ / q))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop hγq).const_mul D
    exact this.eventually_lt_const hρ
  -- measurability of the glued slice data
  have hmapM : ∀ z : ν → ℝ, Measurable fun p : (Fin (k + 1) → ℝ) × ℝ ↦ (Sum.elim p.1 z, p.2) :=
    fun z ↦ ((measurable_elim_const z).comp measurable_fst).prodMk measurable_snd
  have hmapC : ∀ z : ν → ℝ, Continuous fun p : (Fin (k + 1) → ℝ) × ℝ ↦ (Sum.elim p.1 z, p.2) :=
    fun z ↦ ((continuous_elim_const z).comp continuous_fst).prodMk continuous_snd
  have helim : ∀ (y : Fin (k + 1) → ℝ) (z : ν → ℝ), (∀ j, y j ∈ Ioo (0 : ℝ) ρ) →
      (∀ j, z j ∈ Ioo (0 : ℝ) ρ) → ∀ j, Sum.elim y z j ∈ Ioo (0 : ℝ) ρ := by
    intro y z hy hz
    rintro (i | j)
    · exact hy i
    · exact hz j
  -- the slice identity
  have hslice : ∀ (t : ℝ), D * t ^ (-(γ / q)) < ρ → ∀ z : ν → ℝ,
      (∫ y, modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r W a t (Sum.elim y z)) =
      (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ).indicator (fun z ↦ (∏ j, z j ^ r (Sum.inr j)) *
        modelKernel ρ 1 B D γ 0 q δ (0 : Fin (k + 1) → ℝ) (fun i ↦ κ (Sum.inl i))
          (fun i ↦ r (Sum.inl i)) (fun y v ↦ W (Sum.elim y z) v)
          (fun y v ↦ a (Sum.elim y z) v * ∏ j, z j ^ κ (Sum.inr j)) t) z := by
    intro t hcut z
    unfold modelKernel modelIntegrand
    rw [modelDomain_eq_of_Q_zero' (ι := Fin (k + 1) ⊕ ν) hcut,
      modelDomain_eq_of_Q_zero' (ι := Fin (k + 1)) hcut]
    simp only [cutVar_Q_zero', mul_zero, neg_zero, Real.rpow_zero, mul_one, one_mul]
    by_cases hz : z ∈ Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ
    · rw [Set.indicator_of_mem hz, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
      beta_reduce
      by_cases hy : y ∈ Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ
      · rw [Set.indicator_of_mem ((elim_mem_box y z).mpr ⟨hy, hz⟩), Set.indicator_of_mem hy,
          prod_elim_rpow, prod_elim_rpow]
        have e : B * t ^ δ * a (Sum.elim y z) (D * t ^ (-(γ / q))) *
            ((∏ i, y i ^ κ (Sum.inl i)) * ∏ j, z j ^ κ (Sum.inr j)) =
            B * t ^ δ * (a (Sum.elim y z) (D * t ^ (-(γ / q))) * ∏ j, z j ^ κ (Sum.inr j)) *
              ∏ i, y i ^ κ (Sum.inl i) := by ring
        rw [e]
        ring
      · rw [Set.indicator_of_notMem (fun h ↦ hy ((elim_mem_box y z).mp h).1),
          Set.indicator_of_notMem hy, mul_zero]
    · rw [Set.indicator_of_notMem hz]
      refine (integral_congr_ae (Eventually.of_forall fun y ↦ ?_)).trans (integral_zero _ _)
      exact Set.indicator_of_notMem (fun h ↦ hz ((elim_mem_box y z).mp h).2) _
  -- nonnegativity of the slice kernels
  have hMK0 : ∀ (z : ν → ℝ) (t : ℝ), 0 < t →
      0 ≤ modelKernel ρ 1 B D γ 0 q δ (0 : Fin (k + 1) → ℝ) (fun i ↦ κ (Sum.inl i))
        (fun i ↦ r (Sum.inl i)) (fun y v ↦ W (Sum.elim y z) v)
        (fun y v ↦ a (Sum.elim y z) v * ∏ j, z j ^ κ (Sum.inr j)) t := by
    intro z t ht
    unfold modelKernel
    refine mul_nonneg (by positivity) (integral_nonneg fun y ↦ ?_)
    unfold modelIntegrand
    refine Set.indicator_nonneg (fun y hy ↦ ?_) y
    have hyb : ∀ j, y j ∈ Ioo (0 : ℝ) ρ := Set.mem_univ_pi.mp hy.1
    exact mul_nonneg (mul_nonneg (hW0 _ _)
      (Finset.prod_nonneg fun i _ ↦ rpow_nonneg (hyb i).1.le _)) (exp_pos _).le
  -- comparison with the constant-unit slice at `(wU, aL ∏_N z^κ)`
  have hcomp : ∀ (t : ℝ), 0 < t → D * t ^ (-(γ / q)) < ρ →
      ∀ z ∈ (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ),
      modelKernel ρ 1 B D γ 0 q δ (0 : Fin (k + 1) → ℝ) (fun i ↦ κ (Sum.inl i))
        (fun i ↦ r (Sum.inl i)) (fun y v ↦ W (Sum.elim y z) v)
        (fun y v ↦ a (Sum.elim y z) v * ∏ j, z j ^ κ (Sum.inr j)) t ≤
      modelKernel ρ 1 B D γ 0 q δ (0 : Fin (k + 1) → ℝ) (fun i ↦ κ (Sum.inl i))
        (fun i ↦ r (Sum.inl i)) (fun _ _ ↦ wU) (fun _ _ ↦ aL * ∏ j, z j ^ κ (Sum.inr j)) t := by
    intro t ht hcutt z hz
    have hzb : ∀ j, z j ∈ Ioo (0 : ℝ) ρ := Set.mem_univ_pi.mp hz
    have hP := hPNpos z hz
    have hv0 : 0 ≤ D * t ^ (-(γ / q)) := by positivity
    unfold modelKernel
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [modelIntegrand_Q_zero_freeze, modelIntegrand_Q_zero_freeze (W := fun _ _ ↦ wU)]
    have hW' : Measurable (Function.uncurry fun (y : Fin (k + 1) → ℝ) (_ : ℝ) ↦
        W (Sum.elim y z) (D * t ^ (-(γ / q)))) :=
      hW.comp (((measurable_elim_const z).comp measurable_fst).prodMk measurable_const)
    have ha' : Measurable (Function.uncurry fun (y : Fin (k + 1) → ℝ) (_ : ℝ) ↦
        a (Sum.elim y z) (D * t ^ (-(γ / q))) * ∏ j, z j ^ κ (Sum.inr j)) :=
      (ha.comp (((measurable_elim_const z).comp measurable_fst).prodMk measurable_const)).mul
        measurable_const
    refine integral_mono (integrable_modelIntegrand_tied hρ hrT hB ht hW' ha' (wU := wU)
      (fun _ _ ↦ hW0 _ _) (fun _ _ ↦ hWup _ _) fun y _ hy ↦ ?_)
      (integrable_modelIntegrand_tied hρ hrT hB ht (measurable_const (a := wU))
        (measurable_const (a := aL * ∏ j, z j ^ κ (Sum.inr j))) (wU := wU)
        (fun _ _ ↦ hwU) (fun _ _ ↦ le_rfl) fun _ _ _ ↦ by positivity) fun y ↦ ?_
    · exact mul_nonneg (haL.le.trans (halow _ _ (helim y z hy hzb) hv0 hcutt)) hP.le
    · unfold modelIntegrand
      by_cases hy : y ∈ modelDomain ρ D γ q (0 : Fin (k + 1) → ℝ) t
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
        have hyb : ∀ j, y j ∈ Ioo (0 : ℝ) ρ := Set.mem_univ_pi.mp hy.1
        have hprod0 : 0 ≤ ∏ i, y i ^ r (Sum.inl i) :=
          Finset.prod_nonneg fun i _ ↦ rpow_nonneg (hyb i).1.le _
        have hκ0 : 0 ≤ ∏ i, y i ^ κ (Sum.inl i) :=
          Finset.prod_nonneg fun i _ ↦ rpow_nonneg (hyb i).1.le _
        refine mul_le_mul (mul_le_mul_of_nonneg_right (hWup _ _) hprod0)
          (Real.exp_le_exp.mpr (neg_le_neg ?_)) (exp_pos _).le (mul_nonneg hwU hprod0)
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hκ0
        exact mul_le_mul_of_nonneg_right (halow _ _ (helim y z hyb hzb) hv0 hcutt) hP.le
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  -- the uniform bound
  obtain ⟨Cb, hCb0, hCb⟩ := slice_const_bound (D := D) (γ := γ) (q := q) (r := r) hρ hκ hlam
    htied hB haL hδ hwU
  -- the slice limits
  have hlimslice : ∀ z ∈ (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ),
      Tendsto (fun t ↦ t ^ (δ * lam) / log t ^ k *
        modelKernel ρ 1 B D γ 0 q δ (0 : Fin (k + 1) → ℝ) (fun i ↦ κ (Sum.inl i))
          (fun i ↦ r (Sum.inl i)) (fun y v ↦ W (Sum.elim y z) v)
          (fun y v ↦ a (Sum.elim y z) v * ∏ j, z j ^ κ (Sum.inr j)) t) atTop
      (𝓝 (tiedConst 1 B δ (fun i ↦ κ (Sum.inl i)) (fun i ↦ r (Sum.inl i)) lam ρ
        (a (Sum.elim 0 z) 0 * ∏ j, z j ^ κ (Sum.inr j)) (W (Sum.elim 0 z) 0))) := by
    intro z hz
    have hzb : ∀ j, z j ∈ Ioo (0 : ℝ) ρ := Set.mem_univ_pi.mp hz
    have hP := hPNpos z hz
    have hmap : Tendsto (fun p : (Fin (k + 1) → ℝ) × ℝ ↦ (Sum.elim p.1 z, p.2))
        (𝓝 ((0 : Fin (k + 1) → ℝ), (0 : ℝ))) (𝓝 (Sum.elim (0 : Fin (k + 1) → ℝ) z, (0 : ℝ))) :=
      (hmapC z).tendsto _
    have h := tendsto_modelKernel_tied (A := 1) (p := 0) (W := fun y v ↦ W (Sum.elim y z) v)
      (a := fun y v ↦ a (Sum.elim y z) v * ∏ j, z j ^ κ (Sum.inr j)) hρ zero_le_one hD hκT hlam
      htied hB hδ hγq (aL := aL * ∏ j, z j ^ κ (Sum.inr j)) (wU := wU) (mul_pos haL hP)
      (hW.comp (hmapM z)) ((ha.comp (hmapM z)).mul measurable_const) (fun _ _ ↦ hW0 _ _)
      (fun _ _ ↦ hWup _ _)
      (fun y v hy hv0 hv ↦ mul_le_mul_of_nonneg_right (halow _ _ (helim y z hy hzb) hv0 hv) hP.le)
      (a₀ := a (Sum.elim 0 z) 0 * ∏ j, z j ^ κ (Sum.inr j)) (w₀ := W (Sum.elim 0 z) 0)
      (mul_pos (ha₀ z hzb) hP) (hW0 _ _) ((hWlim z hzb).tendsto.comp hmap)
      (((halim z hzb).tendsto.comp hmap).mul_const _)
    rwa [mul_zero, zero_add] at h
  -- measurability and integrability of the full integrand
  have hmeasG : ∀ t : ℝ,
      Measurable (modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r W a t) :=
    fun t ↦ measurable_modelIntegrand hW ha t
  have hintG : ∀ t : ℝ, 0 < t → D * t ^ (-(γ / q)) < ρ →
      Integrable (modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r W a t) := by
    intro t ht hcutt
    refine ((integrable_box_prod_rpow' hρ hr).const_mul wU).mono' (hmeasG t).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ ?_)
    unfold modelIntegrand
    by_cases hx : x ∈ modelDomain ρ D γ q (0 : Fin (k + 1) ⊕ ν → ℝ) t
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx.1]
      have hxb : ∀ j, x j ∈ Ioo (0 : ℝ) ρ := Set.mem_univ_pi.mp hx.1
      have hv : cutVar D γ q (0 : Fin (k + 1) ⊕ ν → ℝ) t x < ρ := hx.2
      rw [cutVar_Q_zero'] at hv
      simp only [cutVar_Q_zero']
      have hr0 : 0 ≤ ∏ i, x i ^ r i :=
        Finset.prod_nonneg fun i _ ↦ rpow_nonneg (hxb i).1.le _
      have hκ0 : 0 ≤ ∏ i, x i ^ κ i :=
        Finset.prod_nonneg fun i _ ↦ rpow_nonneg (hxb i).1.le _
      have hv0 : 0 ≤ D * t ^ (-(γ / q)) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hW0 _ _) hr0) (exp_pos _).le)]
      calc W x (D * t ^ (-(γ / q))) * (∏ i, x i ^ r i) *
            exp (-(B * t ^ δ * a x (D * t ^ (-(γ / q))) * ∏ i, x i ^ κ i))
          ≤ wU * (∏ i, x i ^ r i) * 1 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (hWup _ _) hr0)
              (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ?_)) (exp_pos _).le (mul_nonneg hwU hr0)
            exact mul_nonneg (mul_nonneg (mul_nonneg hB.le (rpow_nonneg ht.le _))
              (haL.le.trans (halow _ _ hxb hv0 hv))) hκ0
        _ = wU * ∏ i, x i ^ r i := mul_one _
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact mul_nonneg hwU (Set.indicator_nonneg (fun x hx ↦ Finset.prod_nonneg fun i _ ↦
        rpow_nonneg (Set.mem_univ_pi.mp hx i).1.le _) x)
  -- dominated convergence over the worse block
  have hmp := (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin (k + 1) ⊕ ν ↦ ℝ)).symm
  have hlimit : ∀ᵐ z : ν → ℝ, Tendsto (fun t ↦ t ^ (δ * lam) / log t ^ k *
      ∫ y, modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r W a t (Sum.elim y z))
      atTop (𝓝 ((Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ).indicator (fun z ↦
        (∏ j, z j ^ r (Sum.inr j)) *
          tiedConst 1 B δ (fun i ↦ κ (Sum.inl i)) (fun i ↦ r (Sum.inl i)) lam ρ
            (a (Sum.elim 0 z) 0 * ∏ j, z j ^ κ (Sum.inr j)) (W (Sum.elim 0 z) 0)) z)) := by
    refine ae_of_all _ fun z ↦ ?_
    by_cases hz : z ∈ Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ
    · rw [Set.indicator_of_mem hz]
      refine ((hlimslice z hz).const_mul (∏ j, z j ^ r (Sum.inr j))).congr' ?_
      filter_upwards [hcut] with t ht
      rw [hslice t ht z, Set.indicator_of_mem hz]
      ring
    · rw [Set.indicator_of_notMem hz]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hcut] with t ht
      rw [hslice t ht z, Set.indicator_of_notMem hz, mul_zero]
  have hbound' : ∀ᶠ t : ℝ in atTop, ∀ᵐ z : ν → ℝ,
      ‖t ^ (δ * lam) / log t ^ k *
        ∫ y, modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r W a t (Sum.elim y z)‖ ≤
      (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ).indicator
        (fun z ↦ Cb * ∏ j, z j ^ (r (Sum.inr j) - lam * κ (Sum.inr j))) z := by
    filter_upwards [hcut, eventually_ge_atTop (exp 1)] with t hcutt ht
    refine ae_of_all _ fun z ↦ ?_
    have ht0 : 0 < t := (exp_pos 1).trans_le ht
    have hlogpos : 0 < log t := log_pos ((Real.one_lt_exp_iff.mpr one_pos).trans_le ht)
    rw [hslice t hcutt z]
    by_cases hz : z ∈ Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      have hzpos : ∀ j, 0 < z j := fun j ↦ (Set.mem_univ_pi.mp hz j).1
      have hr0 : 0 ≤ ∏ j, z j ^ r (Sum.inr j) :=
        Finset.prod_nonneg fun j _ ↦ rpow_nonneg (hzpos j).le _
      have hnorm : 0 ≤ t ^ (δ * lam) / log t ^ k :=
        div_nonneg (rpow_pos_of_pos ht0 _).le (pow_pos hlogpos _).le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnorm (mul_nonneg hr0 (hMK0 z t ht0)))]
      calc t ^ (δ * lam) / log t ^ k * ((∏ j, z j ^ r (Sum.inr j)) *
            modelKernel ρ 1 B D γ 0 q δ (0 : Fin (k + 1) → ℝ) (fun i ↦ κ (Sum.inl i))
              (fun i ↦ r (Sum.inl i)) (fun y v ↦ W (Sum.elim y z) v)
              (fun y v ↦ a (Sum.elim y z) v * ∏ j, z j ^ κ (Sum.inr j)) t)
          = (∏ j, z j ^ r (Sum.inr j)) * (t ^ (δ * lam) / log t ^ k *
            modelKernel ρ 1 B D γ 0 q δ (0 : Fin (k + 1) → ℝ) (fun i ↦ κ (Sum.inl i))
              (fun i ↦ r (Sum.inl i)) (fun y v ↦ W (Sum.elim y z) v)
              (fun y v ↦ a (Sum.elim y z) v * ∏ j, z j ^ κ (Sum.inr j)) t) := by ring
        _ ≤ (∏ j, z j ^ r (Sum.inr j)) * (t ^ (δ * lam) / log t ^ k *
            modelKernel ρ 1 B D γ 0 q δ (0 : Fin (k + 1) → ℝ) (fun i ↦ κ (Sum.inl i))
              (fun i ↦ r (Sum.inl i)) (fun _ _ ↦ wU)
              (fun _ _ ↦ aL * ∏ j, z j ^ κ (Sum.inr j)) t) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hcomp t ht0 hcutt z hz) hnorm) hr0
        _ ≤ (∏ j, z j ^ r (Sum.inr j)) * (Cb * (∏ j, z j ^ κ (Sum.inr j)) ^ (-lam)) :=
            mul_le_mul_of_nonneg_left (hCb t ht hcutt z hz) hr0
        _ = Cb * ∏ j, z j ^ (r (Sum.inr j) - lam * κ (Sum.inr j)) := by
            rw [← prod_rpow_mul_prod_rpow_neg hzpos]
            ring
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero, norm_zero]
  have hbound_int : Integrable ((Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ).indicator
      (fun z ↦ Cb * ∏ j, z j ^ (r (Sum.inr j) - lam * κ (Sum.inr j)))) := by
    have := (integrable_box_prod_rpow' hρ (r := fun j ↦ r (Sum.inr j) - lam * κ (Sum.inr j))
      fun j ↦ by have := hgap j; linarith).const_mul Cb
    refine this.congr (Eventually.of_forall fun z ↦ ?_)
    exact (Set.indicator_const_mul _ _ _ z).symm
  have hmeasS : ∀ᶠ t : ℝ in atTop, AEStronglyMeasurable (fun z : ν → ℝ ↦
      t ^ (δ * lam) / log t ^ k *
        ∫ y, modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r W a t (Sum.elim y z))
      volume := by
    refine Eventually.of_forall fun t ↦ ?_
    refine (Measurable.const_mul ?_ _).aestronglyMeasurable
    have hjoint : StronglyMeasurable fun p : (Fin (k + 1) → ℝ) × (ν → ℝ) ↦
        modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r W a t
          ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (k + 1) ⊕ ν ↦ ℝ)).symm p) :=
      ((hmeasG t).comp (MeasurableEquiv.measurable _)).stronglyMeasurable
    exact hjoint.integral_prod_left'.measurable
  have hDCT := tendsto_integral_filter_of_dominated_convergence _ hmeasS hbound' hbound_int hlimit
  -- the limit as the face integral
  have hconst : (∫ z, (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ).indicator (fun z ↦
      (∏ j, z j ^ r (Sum.inr j)) *
        tiedConst 1 B δ (fun i ↦ κ (Sum.inl i)) (fun i ↦ r (Sum.inl i)) lam ρ
          (a (Sum.elim 0 z) 0 * ∏ j, z j ^ κ (Sum.inr j)) (W (Sum.elim 0 z) 0)) z) =
      δ ^ k * (Gamma lam / k.factorial * ∏ i, 1 / κ (Sum.inl i)) *
        ∫ z in Set.pi univ (fun _ : ν ↦ Ioo (0 : ℝ) ρ),
          W (Sum.elim 0 z) 0 * (B * a (Sum.elim 0 z) 0) ^ (-lam) *
            ∏ j, z j ^ (r (Sum.inr j) - lam * κ (Sum.inr j)) := by
    rw [integral_indicator hboxN, ← integral_const_mul]
    refine setIntegral_congr_fun hboxN fun z hz ↦ ?_
    have hzb : ∀ j, z j ∈ Ioo (0 : ℝ) ρ := Set.mem_univ_pi.mp hz
    have hzpos : ∀ j, 0 < z j := fun j ↦ (hzb j).1
    have hP := hPNpos z hz
    rw [tiedConst_eq hρ (mul_pos hB (mul_pos (ha₀ z hzb) hP)) hκT htied,
      ← prod_rpow_mul_prod_rpow_neg hzpos, ← mul_assoc B,
      Real.mul_rpow (mul_pos hB (ha₀ z hzb)).le hP.le]
    ring
  rw [hconst] at hDCT
  have hDCT' := hDCT.const_mul A
  rw [← mul_assoc A] at hDCT'
  refine hDCT'.congr' ?_
  filter_upwards [hcut, eventually_gt_atTop 1] with t hcutt ht
  have ht0 : 0 < t := one_pos.trans ht
  unfold modelKernel
  rw [← hmp.integral_comp' (modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r W a t),
    Measure.volume_eq_prod (Fin (k + 1) → ℝ) (ν → ℝ),
    integral_prod_symm (fun x ↦ modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r W a t
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (k + 1) ⊕ ν ↦ ℝ)).symm x))
      ((hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr (hintG t ht0 hcutt))]
  change A * (∫ z, t ^ (δ * lam) / log t ^ k *
    ∫ y, modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r W a t (Sum.elim y z)) =
    t ^ (γ * p + δ * lam) / log t ^ k * (A * t ^ (-(γ * p)) *
    ∫ z, ∫ y, modelIntegrand ρ B D γ q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r W a t (Sum.elim y z))
  rw [integral_const_mul]
  have e2 : t ^ (γ * p + δ * lam) * t ^ (-(γ * p)) = t ^ (δ * lam) := by
    rw [← Real.rpow_add ht0]
    congr 1
    ring
  rw [← e2]
  ring

end Laplace.Multi
