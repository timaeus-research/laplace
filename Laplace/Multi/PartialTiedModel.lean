/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.TiedBlockBound
import Laplace.Multi.LogExactConstant
import Laplace.Multi.VertexCertificate

/-!
# The partially tied constant-unit model

A constant-unit model kernel on a box whose coordinates split into a *tied block*
`T = Fin (k+1)` (`(r_i + 1)/κ_i = λ` for all `i ∈ T`) and a *strictly worse block* `ν`
(`λ κ_j < r_j + 1` for `j ∈ ν`). Integrating the tied block first at the effective constant
`a₀ ∏_ν z^κ` gives, for each fixed `z`, a fully tied model kernel whose power–log asymptotic is
known (`tendsto_modelKernel_const`); the all-scale bound on the tied-block integral
(`tiedBlockIntegral_le_bound`) supplies the dominated-convergence majorant
`C ∏_ν z^{r_j − λκ_j}`, integrable exactly because the gaps are strict. Hence

`t^{γp + δλ} (log t)^{-k} K(t) → A w₀ (B a₀)^{-λ} δ^k Γ(λ)/k! ∏_T κ_i^{-1} ∫_{(0,ρ)^ν} ∏ z^{r − λκ}`

(`tendsto_modelKernel_partial`): the logarithmic degree is the dimension of the minimising face
of the LP, and the strictly worse coordinates contribute a finite transverse integral.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

variable {k : ℕ} {ν : Type*} [Fintype ν]

theorem cutVar_Q_zero' {ι : Type*} [Fintype ι] {D γ q t : ℝ} (x : ι → ℝ) :
    cutVar D γ q (0 : ι → ℝ) t x = D * t ^ (-(γ / q)) := by
  unfold cutVar
  simp

theorem modelDomain_eq_of_Q_zero' {ι : Type*} [Fintype ι] {ρ D γ q t : ℝ}
    (hcut : D * t ^ (-(γ / q)) < ρ) :
    modelDomain ρ D γ q (0 : ι → ℝ) t = Set.pi univ fun _ ↦ Ioo (0 : ℝ) ρ := by
  ext x
  simp [modelDomain, cutVar_Q_zero', hcut]

omit [Fintype ν] in
theorem elim_mem_box {ρ : ℝ} (y : Fin (k + 1) → ℝ) (z : ν → ℝ) :
    Sum.elim y z ∈ (Set.pi univ fun _ : Fin (k + 1) ⊕ ν ↦ Ioo (0 : ℝ) ρ) ↔
      y ∈ (Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ) ∧
        z ∈ (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ) := by
  simp only [Set.mem_univ_pi, Sum.forall, Sum.elim_inl, Sum.elim_inr]

theorem prod_elim_rpow (e : Fin (k + 1) ⊕ ν → ℝ) (y : Fin (k + 1) → ℝ) (z : ν → ℝ) :
    ∏ i, Sum.elim y z i ^ e i = (∏ i, y i ^ e (Sum.inl i)) * ∏ j, z j ^ e (Sum.inr j) := by
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]

/-- `∏ z^r · (∏ z^κ)^{-λ} = ∏ z^{r − λκ}` on positive coordinates. -/
theorem prod_rpow_mul_prod_rpow_neg {ι : Type*} [Fintype ι] {z : ι → ℝ} (hz : ∀ j, 0 < z j)
    (r κ : ι → ℝ) (lam : ℝ) :
    (∏ j, z j ^ r j) * (∏ j, z j ^ κ j) ^ (-lam) = ∏ j, z j ^ (r j - lam * κ j) := by
  rw [← Real.finsetProd_rpow _ _ (fun j _ ↦ rpow_nonneg (hz j).le _), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [← Real.rpow_mul (hz j).le, ← Real.rpow_add (hz j)]
  congr 1
  ring

/-- **The partially tied constant-unit model.** -/
theorem tendsto_modelKernel_partial {ρ A B D γ p q δ : ℝ} {κ r : Fin (k + 1) ⊕ ν → ℝ}
    {w₀ a₀ : ℝ} (hρ : 0 < ρ) (hκ : ∀ i, 0 < κ i) {lam : ℝ} (hlam : 0 < lam)
    (htied : ∀ i, (r (Sum.inl i) + 1) / κ (Sum.inl i) = lam)
    (hgap : ∀ j, lam * κ (Sum.inr j) < r (Sum.inr j) + 1)
    (hB : 0 < B) (ha₀ : 0 < a₀) (hδ : 0 < δ) (hγq : 0 < γ / q) :
    Tendsto (fun t ↦ t ^ (γ * p + δ * lam) / log t ^ k *
        modelKernel ρ A B D γ p q δ (0 : Fin (k + 1) ⊕ ν → ℝ) κ r (fun _ _ ↦ w₀) (fun _ _ ↦ a₀) t)
      atTop
      (𝓝 (A * w₀ * ((B * a₀) ^ (-lam) * δ ^ k *
        (Gamma lam / k.factorial * ∏ i, 1 / κ (Sum.inl i)) *
        ∫ z in Set.pi univ (fun _ : ν ↦ Ioo (0 : ℝ) ρ),
          ∏ j, z j ^ (r (Sum.inr j) - lam * κ (Sum.inr j))))) := by
  classical
  -- the blocks
  have hκT : ∀ i : Fin (k + 1), 0 < κ (Sum.inl i) := fun i ↦ hκ _
  have hr : ∀ i, -1 < r i := by
    rintro (i | j)
    · have h := htied i
      rw [div_eq_iff (hκT i).ne'] at h
      nlinarith [mul_pos hlam (hκT i)]
    · have := hgap j
      nlinarith [mul_pos hlam (hκ (Sum.inr j))]
  have hboxT : MeasurableSet (Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have hboxN : MeasurableSet (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have hbox : MeasurableSet (Set.pi univ fun _ : Fin (k + 1) ⊕ ν ↦ Ioo (0 : ℝ) ρ) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have hPNpos : ∀ z ∈ (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ), 0 < ∏ j, z j ^ κ (Sum.inr j) :=
    fun z hz ↦ Finset.prod_pos fun j _ ↦ rpow_pos_of_pos (Set.mem_univ_pi.mp hz j).1 _
  have hPNle : ∀ z ∈ (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ),
      ∏ j, z j ^ κ (Sum.inr j) ≤ ρ ^ (∑ j, κ (Sum.inr j)) := fun z hz ↦ by
    rw [Real.rpow_sum_of_pos hρ]
    exact Finset.prod_le_prod (fun j _ ↦ rpow_nonneg (Set.mem_univ_pi.mp hz j).1.le _)
      fun j _ ↦ Real.rpow_le_rpow (Set.mem_univ_pi.mp hz j).1.le (Set.mem_univ_pi.mp hz j).2.le
        (hκ _).le
  -- the slice kernel: the tied block at the effective constant `c'`
  have hMKeq : ∀ (c' t : ℝ), D * t ^ (-(γ / q)) < ρ →
      modelKernel ρ 1 B D γ 0 q δ (0 : Fin (k + 1) → ℝ) (fun i ↦ κ (Sum.inl i))
        (fun i ↦ r (Sum.inl i)) (fun _ _ ↦ (1 : ℝ)) (fun _ _ ↦ c') t =
      ∫ y, (Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ).indicator
        (fun y ↦ (∏ i, y i ^ r (Sum.inl i)) *
          exp (-(B * t ^ δ * c' * ∏ i, y i ^ κ (Sum.inl i)))) y := by
    intro c' t hcut
    unfold modelKernel modelIntegrand
    rw [modelDomain_eq_of_Q_zero hcut, mul_zero, neg_zero, Real.rpow_zero, mul_one, one_mul]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    beta_reduce
    by_cases hy : y ∈ Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  have hMK0 : ∀ (c' t : ℝ), D * t ^ (-(γ / q)) < ρ →
      0 ≤ modelKernel ρ 1 B D γ 0 q δ (0 : Fin (k + 1) → ℝ) (fun i ↦ κ (Sum.inl i))
        (fun i ↦ r (Sum.inl i)) (fun _ _ ↦ (1 : ℝ)) (fun _ _ ↦ c') t := fun c' t hcut ↦ by
    rw [hMKeq c' t hcut]
    refine integral_nonneg fun y ↦ Set.indicator_nonneg (fun y hy ↦ ?_) y
    exact mul_nonneg (Finset.prod_nonneg fun i _ ↦
      rpow_nonneg (Set.mem_univ_pi.mp hy i).1.le _) (exp_pos _).le
  -- the slice identity
  have hslice : ∀ (t : ℝ), D * t ^ (-(γ / q)) < ρ → ∀ z : ν → ℝ,
      (∫ y, (Set.pi univ fun _ : Fin (k + 1) ⊕ ν ↦ Ioo (0 : ℝ) ρ).indicator
        (fun x ↦ (∏ i, x i ^ r i) * exp (-(B * t ^ δ * a₀ * ∏ i, x i ^ κ i))) (Sum.elim y z)) =
      (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ).indicator (fun z ↦ (∏ j, z j ^ r (Sum.inr j)) *
        modelKernel ρ 1 B D γ 0 q δ (0 : Fin (k + 1) → ℝ) (fun i ↦ κ (Sum.inl i))
          (fun i ↦ r (Sum.inl i)) (fun _ _ ↦ (1 : ℝ))
          (fun _ _ ↦ a₀ * ∏ j, z j ^ κ (Sum.inr j)) t) z := by
    intro t hcut z
    by_cases hz : z ∈ Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ
    · rw [Set.indicator_of_mem hz, hMKeq _ t hcut, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
      beta_reduce
      by_cases hy : y ∈ Set.pi univ fun _ : Fin (k + 1) ↦ Ioo (0 : ℝ) ρ
      · rw [Set.indicator_of_mem ((elim_mem_box y z).mpr ⟨hy, hz⟩), Set.indicator_of_mem hy,
          prod_elim_rpow, prod_elim_rpow]
        have e : B * t ^ δ * a₀ * ((∏ i, y i ^ κ (Sum.inl i)) * ∏ j, z j ^ κ (Sum.inr j)) =
            B * t ^ δ * (a₀ * ∏ j, z j ^ κ (Sum.inr j)) * ∏ i, y i ^ κ (Sum.inl i) := by ring
        rw [e]
        ring
      · rw [Set.indicator_of_notMem (fun h ↦ hy ((elim_mem_box y z).mp h).1),
          Set.indicator_of_notMem hy, mul_zero]
    · rw [Set.indicator_of_notMem hz]
      refine (integral_congr_ae (Eventually.of_forall fun y ↦ ?_)).trans (integral_zero _ _)
      exact Set.indicator_of_notMem (fun h ↦ hz ((elim_mem_box y z).mp h).2) _
  -- the slice limit
  have hlimslice : ∀ z ∈ (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ),
      Tendsto (fun t ↦ t ^ (δ * lam) / log t ^ k *
        modelKernel ρ 1 B D γ 0 q δ (0 : Fin (k + 1) → ℝ) (fun i ↦ κ (Sum.inl i))
          (fun i ↦ r (Sum.inl i)) (fun _ _ ↦ (1 : ℝ))
          (fun _ _ ↦ a₀ * ∏ j, z j ^ κ (Sum.inr j)) t) atTop
      (𝓝 ((B * (a₀ * ∏ j, z j ^ κ (Sum.inr j))) ^ (-lam) * δ ^ k *
        (Gamma lam / k.factorial * ∏ i, 1 / κ (Sum.inl i)))) := by
    intro z hz
    have h := tendsto_modelKernel_const (A := 1) (D := D) (p := 0) (w₀ := 1)
      (a₀ := a₀ * ∏ j, z j ^ κ (Sum.inr j)) (κ := fun i ↦ κ (Sum.inl i))
      (r := fun i ↦ r (Sum.inl i)) hρ hκT hlam htied hB (mul_pos ha₀ (hPNpos z hz)) hδ hγq
    rw [mul_zero, zero_add] at h
    have e : (1 : ℝ) * 1 * ρ ^ (∑ i, (r (Sum.inl i) + 1)) *
        (B * (a₀ * ∏ j, z j ^ κ (Sum.inr j)) * ρ ^ (∑ i, κ (Sum.inl i))) ^ (-lam) * δ ^ k *
        (Gamma lam / k.factorial * ∏ i, 1 / κ (Sum.inl i)) =
        (B * (a₀ * ∏ j, z j ^ κ (Sum.inr j))) ^ (-lam) * δ ^ k *
          (Gamma lam / k.factorial * ∏ i, 1 / κ (Sum.inl i)) := by
      have := tiedConst_eq (A := 1) (B := B) (δ := δ) (κ := fun i ↦ κ (Sum.inl i))
        (r := fun i ↦ r (Sum.inl i)) (lam := lam) (R := ρ) (a := a₀ * ∏ j, z j ^ κ (Sum.inr j))
        (w := 1) hρ (mul_pos hB (mul_pos ha₀ (hPNpos z hz))) hκT htied
      unfold tiedConst at this
      rw [this]
      ring
    rwa [e] at h
  -- the uniform bound on the slices
  obtain ⟨M, hM0, hM⟩ := tiedBlockIntegral_le_bound (A := fun i ↦ κ (Sum.inl i))
    (h := fun i ↦ r (Sum.inl i)) hκT hlam htied
  set c₁ : ℝ := B * a₀ * ρ ^ (∑ i, κ (Sum.inl i)) with hc₁
  have hc₁pos : 0 < c₁ := by rw [hc₁]; positivity
  set L₀ : ℝ := max 0 (log (c₁ * ρ ^ (∑ j, κ (Sum.inr j)))) with hL₀
  have hL₀0 : 0 ≤ L₀ := le_max_left _ _
  set Cb : ℝ := ρ ^ (∑ i, (r (Sum.inl i) + 1)) * M * c₁ ^ (-lam) * (1 + L₀ + δ) ^ k with hCb
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  have hbound : ∀ (t : ℝ), exp 1 ≤ t → D * t ^ (-(γ / q)) < ρ →
      ∀ z ∈ (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ),
      t ^ (δ * lam) / log t ^ k *
        modelKernel ρ 1 B D γ 0 q δ (0 : Fin (k + 1) → ℝ) (fun i ↦ κ (Sum.inl i))
          (fun i ↦ r (Sum.inl i)) (fun _ _ ↦ (1 : ℝ))
          (fun _ _ ↦ a₀ * ∏ j, z j ^ κ (Sum.inr j)) t ≤
        Cb * (∏ j, z j ^ κ (Sum.inr j)) ^ (-lam) := by
    intro t ht hcut z hz
    have ht0 : 0 < t := (exp_pos 1).trans_le ht
    have hlogt : 1 ≤ log t := by rw [← log_exp 1]; exact log_le_log (exp_pos 1) ht
    have hlogpos : 0 < log t := by linarith
    have hP := hPNpos z hz
    set P : ℝ := ∏ j, z j ^ κ (Sum.inr j) with hPdef
    rw [modelKernel_const_eq hρ hcut, mul_zero, neg_zero, Real.rpow_zero, mul_one, one_mul,
      one_mul]
    set s : ℝ := c₁ * P * t ^ δ with hs
    have hspos : 0 < s := by rw [hs]; positivity
    have e1 : B * (a₀ * P) * ρ ^ (∑ i, κ (Sum.inl i)) * t ^ δ = s := by rw [hs, hc₁]; ring
    rw [e1]
    have hTB := hM s hspos
    -- `t^{δλ} s^{-λ} = (c₁ P)^{-λ}`
    have e2 : t ^ (δ * lam) * s ^ (-lam) = (c₁ * P) ^ (-lam) := by
      rw [hs, Real.mul_rpow (by positivity) (rpow_pos_of_pos ht0 _).le, ← Real.rpow_mul ht0.le,
        show δ * -lam = -(δ * lam) by ring, Real.rpow_neg ht0.le]
      have hpos : 0 < t ^ (δ * lam) := rpow_pos_of_pos ht0 _
      rw [mul_comm ((c₁ * P) ^ (-lam)), ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    -- `1 + log⁺ s ≤ (1 + L₀ + δ) log t`
    have e3 : 1 + max 0 (log s) ≤ (1 + L₀ + δ) * log t := by
      have hPle := hPNle z hz
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
    calc t ^ (δ * lam) / log t ^ k * (ρ ^ (∑ i, (r (Sum.inl i) + 1)) *
          tiedBlockIntegral (fun i ↦ κ (Sum.inl i)) (fun i ↦ r (Sum.inl i)) s)
        ≤ t ^ (δ * lam) / log t ^ k * (ρ ^ (∑ i, (r (Sum.inl i) + 1)) *
          (M * s ^ (-lam) * (1 + max 0 (log s)) ^ k)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTB (rpow_pos_of_pos hρ _).le)
            hnorm
      _ = ρ ^ (∑ i, (r (Sum.inl i) + 1)) * M * (t ^ (δ * lam) * s ^ (-lam)) *
          ((1 + max 0 (log s)) / log t) ^ k := by
          rw [div_pow]
          field_simp
      _ ≤ ρ ^ (∑ i, (r (Sum.inl i) + 1)) * M * (c₁ * P) ^ (-lam) * (1 + L₀ + δ) ^ k := by
          rw [e2]
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ k)
            (by positivity)
          rw [div_le_iff₀ hlogpos]
          exact e3
      _ = Cb * P ^ (-lam) := by
          rw [hCb, Real.mul_rpow hc₁pos.le hP.le]
          ring
  -- the dominated convergence over the worse block
  have hcut : ∀ᶠ t : ℝ in atTop, D * t ^ (-(γ / q)) < ρ := by
    have : Tendsto (fun t : ℝ ↦ D * t ^ (-(γ / q))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop hγq).const_mul D
    exact this.eventually_lt_const hρ
  have hmp := (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin (k + 1) ⊕ ν ↦ ℝ)).symm
  have hmeasG : ∀ t : ℝ, Measurable fun x : Fin (k + 1) ⊕ ν → ℝ ↦
      (Set.pi univ fun _ : Fin (k + 1) ⊕ ν ↦ Ioo (0 : ℝ) ρ).indicator
        (fun x ↦ (∏ i, x i ^ r i) * exp (-(B * t ^ δ * a₀ * ∏ i, x i ^ κ i))) x := fun t ↦
    ((Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _).mul
      (Real.measurable_exp.comp ((measurable_const.mul
        (Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _)).neg))).indicator
      hbox
  have hintG : ∀ t : ℝ, 0 ≤ t → Integrable fun x : Fin (k + 1) ⊕ ν → ℝ ↦
      (Set.pi univ fun _ : Fin (k + 1) ⊕ ν ↦ Ioo (0 : ℝ) ρ).indicator
        (fun x ↦ (∏ i, x i ^ r i) * exp (-(B * t ^ δ * a₀ * ∏ i, x i ^ κ i))) x := fun t ht ↦ by
    refine (integrable_box_prod_rpow' hρ hr).mono' (hmeasG t).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ Set.pi univ fun _ : Fin (k + 1) ⊕ ν ↦ Ioo (0 : ℝ) ρ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      have hr0 : 0 ≤ ∏ i, x i ^ r i :=
        Finset.prod_nonneg fun i _ ↦ rpow_nonneg (Set.mem_univ_pi.mp hx i).1.le _
      have hκ0 : 0 ≤ ∏ i, x i ^ κ i :=
        Finset.prod_nonneg fun i _ ↦ rpow_nonneg (Set.mem_univ_pi.mp hx i).1.le _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr0 (exp_pos _).le)]
      calc (∏ i, x i ^ r i) * exp (-(B * t ^ δ * a₀ * ∏ i, x i ^ κ i))
          ≤ (∏ i, x i ^ r i) * 1 := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ?_)) hr0
            exact mul_nonneg (mul_nonneg (mul_nonneg hB.le (rpow_nonneg ht _)) ha₀.le) hκ0
        _ = ∏ i, x i ^ r i := mul_one _
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, norm_zero]
  -- the normalised slice function and its limit
  have hlimit : ∀ᵐ z : ν → ℝ, Tendsto (fun t ↦ t ^ (δ * lam) / log t ^ k *
      ∫ y, (Set.pi univ fun _ : Fin (k + 1) ⊕ ν ↦ Ioo (0 : ℝ) ρ).indicator
        (fun x ↦ (∏ i, x i ^ r i) * exp (-(B * t ^ δ * a₀ * ∏ i, x i ^ κ i))) (Sum.elim y z))
      atTop (𝓝 ((Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ).indicator (fun z ↦
        (∏ j, z j ^ r (Sum.inr j)) * ((B * (a₀ * ∏ j, z j ^ κ (Sum.inr j))) ^ (-lam) * δ ^ k *
          (Gamma lam / k.factorial * ∏ i, 1 / κ (Sum.inl i)))) z)) := by
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
        ∫ y, (Set.pi univ fun _ : Fin (k + 1) ⊕ ν ↦ Ioo (0 : ℝ) ρ).indicator
          (fun x ↦ (∏ i, x i ^ r i) * exp (-(B * t ^ δ * a₀ * ∏ i, x i ^ κ i))) (Sum.elim y z)‖ ≤
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
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnorm (mul_nonneg hr0 (hMK0 _ t hcutt)))]
      calc t ^ (δ * lam) / log t ^ k * ((∏ j, z j ^ r (Sum.inr j)) *
            modelKernel ρ 1 B D γ 0 q δ (0 : Fin (k + 1) → ℝ) (fun i ↦ κ (Sum.inl i))
              (fun i ↦ r (Sum.inl i)) (fun _ _ ↦ (1 : ℝ))
              (fun _ _ ↦ a₀ * ∏ j, z j ^ κ (Sum.inr j)) t)
          = (∏ j, z j ^ r (Sum.inr j)) * (t ^ (δ * lam) / log t ^ k *
            modelKernel ρ 1 B D γ 0 q δ (0 : Fin (k + 1) → ℝ) (fun i ↦ κ (Sum.inl i))
              (fun i ↦ r (Sum.inl i)) (fun _ _ ↦ (1 : ℝ))
              (fun _ _ ↦ a₀ * ∏ j, z j ^ κ (Sum.inr j)) t) := by ring
        _ ≤ (∏ j, z j ^ r (Sum.inr j)) * (Cb * (∏ j, z j ^ κ (Sum.inr j)) ^ (-lam)) :=
            mul_le_mul_of_nonneg_left (hbound t ht hcutt z hz) hr0
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
        ∫ y, (Set.pi univ fun _ : Fin (k + 1) ⊕ ν ↦ Ioo (0 : ℝ) ρ).indicator
          (fun x ↦ (∏ i, x i ^ r i) * exp (-(B * t ^ δ * a₀ * ∏ i, x i ^ κ i))) (Sum.elim y z))
      volume := by
    refine Eventually.of_forall fun t ↦ ?_
    refine (Measurable.const_mul ?_ _).aestronglyMeasurable
    have hjoint : StronglyMeasurable fun p : (Fin (k + 1) → ℝ) × (ν → ℝ) ↦
        (Set.pi univ fun _ : Fin (k + 1) ⊕ ν ↦ Ioo (0 : ℝ) ρ).indicator
          (fun x ↦ (∏ i, x i ^ r i) * exp (-(B * t ^ δ * a₀ * ∏ i, x i ^ κ i)))
          ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (k + 1) ⊕ ν ↦ ℝ)).symm p) :=
      ((hmeasG t).comp (MeasurableEquiv.measurable _)).stronglyMeasurable
    exact hjoint.integral_prod_left'.measurable
  have hDCT := tendsto_integral_filter_of_dominated_convergence _ hmeasS hbound' hbound_int hlimit
  -- assemble
  have hconst : (∫ z, (Set.pi univ fun _ : ν ↦ Ioo (0 : ℝ) ρ).indicator (fun z ↦
      (∏ j, z j ^ r (Sum.inr j)) * ((B * (a₀ * ∏ j, z j ^ κ (Sum.inr j))) ^ (-lam) * δ ^ k *
        (Gamma lam / k.factorial * ∏ i, 1 / κ (Sum.inl i)))) z) =
      (B * a₀) ^ (-lam) * δ ^ k * (Gamma lam / k.factorial * ∏ i, 1 / κ (Sum.inl i)) *
        ∫ z in Set.pi univ (fun _ : ν ↦ Ioo (0 : ℝ) ρ),
          ∏ j, z j ^ (r (Sum.inr j) - lam * κ (Sum.inr j)) := by
    rw [integral_indicator hboxN, ← integral_const_mul]
    refine setIntegral_congr_fun hboxN fun z hz ↦ ?_
    have hzpos : ∀ j, 0 < z j := fun j ↦ (Set.mem_univ_pi.mp hz j).1
    rw [← prod_rpow_mul_prod_rpow_neg hzpos, ← mul_assoc B a₀, Real.mul_rpow (by positivity)
      (hPNpos z hz).le]
    ring
  rw [hconst] at hDCT
  refine (hDCT.const_mul (A * w₀)).congr' ?_
  filter_upwards [hcut, eventually_gt_atTop 1] with t hcutt ht
  have ht0 : 0 < t := one_pos.trans ht
  -- the kernel as the iterated integral
  unfold modelKernel modelIntegrand
  rw [modelDomain_eq_of_Q_zero' hcutt]
  have e1 : (fun x : Fin (k + 1) ⊕ ν → ℝ ↦
      (Set.pi univ fun _ : Fin (k + 1) ⊕ ν ↦ Ioo (0 : ℝ) ρ).indicator
      (fun x ↦ (fun _ _ ↦ w₀) x (cutVar D γ q (0 : Fin (k + 1) ⊕ ν → ℝ) t x) * (∏ j, x j ^ r j) *
        exp (-(B * t ^ δ * (fun _ _ ↦ a₀) x (cutVar D γ q (0 : Fin (k + 1) ⊕ ν → ℝ) t x) *
          ∏ j, x j ^ κ j))) x) =
      fun x ↦ w₀ * (Set.pi univ fun _ : Fin (k + 1) ⊕ ν ↦ Ioo (0 : ℝ) ρ).indicator
        (fun x ↦ (∏ i, x i ^ r i) * exp (-(B * t ^ δ * a₀ * ∏ i, x i ^ κ i))) x := by
    funext x
    rw [← Set.indicator_const_mul]
    congr 1
    funext x
    ring
  rw [e1, integral_const_mul w₀, ← hmp.integral_comp' (fun x ↦
    (Set.pi univ fun _ : Fin (k + 1) ⊕ ν ↦ Ioo (0 : ℝ) ρ).indicator (fun x ↦ (∏ i, x i ^ r i) *
      exp (-(B * t ^ δ * a₀ * ∏ i, x i ^ κ i))) x),
    Measure.volume_eq_prod (Fin (k + 1) → ℝ) (ν → ℝ),
    integral_prod_symm (fun x ↦ (Set.pi univ fun _ : Fin (k + 1) ⊕ ν ↦ Ioo (0 : ℝ) ρ).indicator
      (fun x ↦ (∏ i, x i ^ r i) * exp (-(B * t ^ δ * a₀ * ∏ i, x i ^ κ i)))
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (k + 1) ⊕ ν ↦ ℝ)).symm x))
      ((hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr (hintG t ht0.le))]
  change A * w₀ * (∫ z, t ^ (δ * lam) / log t ^ k *
    ∫ y, (Set.pi univ fun _ : Fin (k + 1) ⊕ ν ↦ Ioo (0 : ℝ) ρ).indicator
      (fun x ↦ (∏ i, x i ^ r i) * exp (-(B * t ^ δ * a₀ * ∏ i, x i ^ κ i))) (Sum.elim y z)) =
    t ^ (γ * p + δ * lam) / log t ^ k * (A * t ^ (-(γ * p)) * (w₀ *
    ∫ z, ∫ y, (Set.pi univ fun _ : Fin (k + 1) ⊕ ν ↦ Ioo (0 : ℝ) ρ).indicator
      (fun x ↦ (∏ i, x i ^ r i) * exp (-(B * t ^ δ * a₀ * ∏ i, x i ^ κ i))) (Sum.elim y z)))
  rw [integral_const_mul]
  have e2 : t ^ (γ * p + δ * lam) * t ^ (-(γ * p)) = t ^ (δ * lam) := by
    rw [← Real.rpow_add ht0]
    congr 1
    ring
  rw [← e2]
  ring

end Laplace.Multi
