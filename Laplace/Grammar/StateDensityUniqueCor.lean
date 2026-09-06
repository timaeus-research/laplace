/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.StateDensityUnique

/-!
# State density III: positivity and the asymptotic-equivalence form (grammar §4.2)

The divisor density of unit 70 is integrable on the box, and positive when `η(0, ·) > 0`, so its
integral is a positive constant `C(ξ, η)` and the state integral satisfies

  `Z(n) ~ C(ξ, η) · n^{-p/2}`,  `C(ξ, η) = (1/k₀) ∫_v v^{h'}(v^{k'})^{-p} A_{p-1}(ξ(0,v)) η(0,v) dv`

(`stateIntegral_isEquivalent`). Also: the fluctuation mass `A_γ(a)` is monotone (hence measurable)
in `a`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- `a ↦ A_γ(a)` is monotone. -/
theorem weightedMass_mono_left (β γ : ℝ) (hβ : 0 < β) (hγ : -1 < γ) :
    Monotone fun a => weightedMass β a γ := by
  intro a₁ a₂ h
  unfold weightedMass
  refine setIntegral_mono_on (weightedKernel_integrableOn β a₁ γ hβ hγ)
    (weightedKernel_integrableOn β a₂ γ hβ hγ) measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht0.le _)
  unfold quadKernel
  apply Real.exp_le_exp.2
  nlinarith [mul_nonneg hβ.le ht0.le]

theorem weightedMass_measurable_left (β γ : ℝ) (hβ : 0 < β) (hγ : -1 < γ) :
    Measurable fun a => weightedMass β a γ :=
  (weightedMass_mono_left β γ hβ hγ).measurable

/-- The divisor weight `∏ v_i^{h'_i} (v_i^{k'_i})^{-p}` is integrable on the box when all
`q_i > p`. -/
theorem divisorWeight_integrable (b : ℝ) {d : ℕ} (k' h' : Fin d → ℕ) (hk' : ∀ i, 0 < k' i) (p : ℝ)
    (hq : ∀ i, p < ((h' i : ℝ) + 1) / k' i) :
    Integrable (fun v : Fin d → ℝ => ∏ i, (v i ^ h' i * (v i ^ k' i) ^ (-p))) (boxMeasure b d) := by
  have hfac : ∀ i, Integrable (fun t : ℝ => t ^ h' i * (t ^ k' i) ^ (-p))
      ((volume : Measure ℝ).restrict (Ioc 0 b)) := by
    intro i
    have hexp : -1 < (h' i : ℝ) - k' i * p := by
      have := hq i
      have hki : (0 : ℝ) < k' i := Nat.cast_pos.2 (hk' i)
      rw [lt_div_iff₀ hki] at this
      linarith
    have hr := (intervalIntegral.intervalIntegrable_rpow' hexp (a := 0) (b := b)).1
    refine hr.congr_fun (fun t ht => ?_) measurableSet_Ioc
    have ht0 : 0 < t := ht.1
    rw [← Real.rpow_natCast t (h' i), ← Real.rpow_natCast t (k' i), ← Real.rpow_mul ht0.le,
      ← Real.rpow_add ht0]
    ring_nf
  exact Integrable.fintype_prod (μ := fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc 0 b))
    (f := fun i t => t ^ h' i * (t ^ k' i) ^ (-p)) hfac

theorem divisorDensity_measurable (β : ℝ) (hβ : 0 < β) (h₀ k₀ : ℕ) (hk₀ : 0 < k₀) {d : ℕ}
    (k' h' : Fin d → ℕ) (ξ η : ℝ → (Fin d → ℝ) → ℝ)
    (hξc : Continuous fun x : ℝ × (Fin d → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : ℝ × (Fin d → ℝ) => η x.1 x.2) :
    Measurable (divisorDensity β h₀ k₀ k' h' ξ η) := by
  have hk₀' : (0 : ℝ) < k₀ := Nat.cast_pos.2 hk₀
  have hγ : -1 < ((h₀ : ℝ) + 1) / k₀ - 1 := by
    have : 0 < ((h₀ : ℝ) + 1) / k₀ := by positivity
    linarith
  have hξ0 : Continuous fun v : Fin d → ℝ => ξ 0 v :=
    hξc.comp (continuous_const.prodMk continuous_id)
  have hη0 : Continuous fun v : Fin d → ℝ => η 0 v :=
    hηc.comp (continuous_const.prodMk continuous_id)
  unfold divisorDensity
  refine (((continuous_prod_pow h').measurable.mul
    ((continuous_prod_pow k').measurable.pow_const _)).mul ?_)
  exact (measurable_const.mul ((weightedMass_measurable_left β _ hβ hγ).comp hξ0.measurable)).mul
    hη0.measurable

/-- **Integrability of the divisor density.** -/
theorem divisorDensity_integrable (β b : ℝ) (hβ : 0 < β) (h₀ k₀ : ℕ) (hk₀ : 0 < k₀)
    {d : ℕ} (k' h' : Fin d → ℕ) (hk' : ∀ i, 0 < k' i)
    (hq : ∀ i, ((h₀ : ℝ) + 1) / k₀ < ((h' i : ℝ) + 1) / k' i) (ξ η : ℝ → (Fin d → ℝ) → ℝ)
    (hξc : Continuous fun x : ℝ × (Fin d → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : ℝ × (Fin d → ℝ) => η x.1 x.2) :
    Integrable (divisorDensity β h₀ k₀ k' h' ξ η) (boxMeasure b d) := by
  have hk₀' : (0 : ℝ) < k₀ := Nat.cast_pos.2 hk₀
  set p : ℝ := ((h₀ : ℝ) + 1) / k₀ with hp
  have hp0 : 0 < p := by positivity
  have hγ : -1 < p - 1 := by linarith
  -- bounds for ξ(0,·), η(0,·) on the closed box
  have hcpt : IsCompact (Set.pi univ fun _ : Fin d => Icc (0 : ℝ) b) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hξ0 : Continuous fun v : Fin d → ℝ => ξ 0 v :=
    hξc.comp (continuous_const.prodMk continuous_id)
  have hη0 : Continuous fun v : Fin d → ℝ => η 0 v :=
    hηc.comp (continuous_const.prodMk continuous_id)
  obtain ⟨L, hL⟩ := hcpt.exists_bound_of_continuousOn hξ0.continuousOn
  obtain ⟨M₀, hM₀⟩ := hcpt.exists_bound_of_continuousOn hη0.continuousOn
  set M : ℝ := max M₀ 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hAL : 0 ≤ weightedMass β L (p - 1) := (weightedMass_pos β L (p - 1) hβ hγ).le
  set K : ℝ := 1 / (k₀ : ℝ) * weightedMass β L (p - 1) * M with hK
  have hmem : ∀ᵐ v ∂(boxMeasure b d), v ∈ Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) b := by
    rw [boxMeasure_eq_restrict]
    exact ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
  refine Integrable.mono' (g := fun v => K * ∏ i, (v i ^ h' i * (v i ^ k' i) ^ (-p)))
    ((divisorWeight_integrable b k' h' hk' p hq).const_mul K)
    (divisorDensity_measurable β hβ h₀ k₀ hk₀ k' h' ξ η hξc hηc).aestronglyMeasurable ?_
  filter_upwards [hmem] with v hv
  have hv' : ∀ i, 0 < v i := by rw [Set.mem_univ_pi] at hv; exact fun i => (hv i).1
  have hvI : v ∈ Set.pi univ fun _ : Fin d => Icc (0 : ℝ) b := by
    rw [Set.mem_univ_pi] at hv ⊢; exact fun i => ⟨(hv i).1.le, (hv i).2⟩
  have hξv : ξ 0 v ≤ L := by
    have := hL v hvI
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have hηv : |η 0 v| ≤ M := by
    have := hM₀ v hvI
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hV : 0 < ∏ i, v i ^ k' i := Finset.prod_pos fun i _ => pow_pos (hv' i) _
  have hprodh : 0 ≤ ∏ i, v i ^ h' i := Finset.prod_nonneg fun i _ => pow_nonneg (hv' i).le _
  have hprod : (∏ i, v i ^ h' i) * (∏ i, v i ^ k' i) ^ (-p)
      = ∏ i, (v i ^ h' i * (v i ^ k' i) ^ (-p)) := by
    rw [Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ fun i _ => pow_nonneg (hv' i).le _]
  have hA0 : 0 ≤ weightedMass β (ξ 0 v) (p - 1) := (weightedMass_pos β _ (p - 1) hβ hγ).le
  have hAle : weightedMass β (ξ 0 v) (p - 1) ≤ weightedMass β L (p - 1) :=
    weightedMass_mono_left β (p - 1) hβ hγ hξv
  rw [Real.norm_eq_abs, divisorDensity, ← hp, ← hprod, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg hprodh, abs_of_pos (Real.rpow_pos_of_pos hV _), abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (k₀ : ℝ)), abs_of_nonneg hA0]
  calc (∏ i, v i ^ h' i) * (∏ i, v i ^ k' i) ^ (-p)
        * (1 / (k₀ : ℝ) * weightedMass β (ξ 0 v) (p - 1) * |η 0 v|)
      ≤ (∏ i, v i ^ h' i) * (∏ i, v i ^ k' i) ^ (-p)
          * (1 / (k₀ : ℝ) * weightedMass β L (p - 1) * M) := by
        gcongr
    _ = K * ((∏ i, v i ^ h' i) * (∏ i, v i ^ k' i) ^ (-p)) := by rw [hK]; ring

/-- **Positivity of the divisor coefficient** when `η(0, ·) > 0` on the box. -/
theorem integral_divisorDensity_pos (β b : ℝ) (hβ : 0 < β) (hb : 0 < b) (h₀ k₀ : ℕ) (hk₀ : 0 < k₀)
    {d : ℕ} (k' h' : Fin d → ℕ) (hk' : ∀ i, 0 < k' i)
    (hq : ∀ i, ((h₀ : ℝ) + 1) / k₀ < ((h' i : ℝ) + 1) / k' i) (ξ η : ℝ → (Fin d → ℝ) → ℝ)
    (hξc : Continuous fun x : ℝ × (Fin d → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : ℝ × (Fin d → ℝ) => η x.1 x.2)
    (hηpos : ∀ v : Fin d → ℝ, (∀ i, 0 < v i ∧ v i ≤ b) → 0 < η 0 v) :
    0 < ∫ v, divisorDensity β h₀ k₀ k' h' ξ η v ∂(boxMeasure b d) := by
  have hk₀' : (0 : ℝ) < k₀ := Nat.cast_pos.2 hk₀
  set p : ℝ := ((h₀ : ℝ) + 1) / k₀ with hp
  have hp0 : 0 < p := by positivity
  have hγ : -1 < p - 1 := by linarith
  have hmem : ∀ᵐ v ∂(boxMeasure b d), v ∈ Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) b := by
    rw [boxMeasure_eq_restrict]
    exact ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
  have hpos : ∀ v : Fin d → ℝ, v ∈ (Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) b) →
      0 < divisorDensity β h₀ k₀ k' h' ξ η v := by
    intro v hv
    rw [Set.mem_univ_pi] at hv
    have hv' : ∀ i, 0 < v i := fun i => (hv i).1
    have hη := hηpos v fun i => ⟨(hv i).1, (hv i).2⟩
    have hA := weightedMass_pos β (ξ 0 v) (p - 1) hβ hγ
    have hV : 0 < ∏ i, v i ^ k' i := Finset.prod_pos fun i _ => pow_pos (hv' i) _
    have hH : 0 < ∏ i, v i ^ h' i := Finset.prod_pos fun i _ => pow_pos (hv' i) _
    unfold divisorDensity
    rw [← hp]
    positivity
  rw [integral_pos_iff_support_of_nonneg_ae ?_
    (divisorDensity_integrable β b hβ h₀ k₀ hk₀ k' h' hk' hq ξ η hξc hηc)]
  · have hsub : (Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) b)
        ⊆ Function.support (divisorDensity β h₀ k₀ k' h' ξ η) := fun v hv => (hpos v hv).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [boxMeasure, Measure.pi_pi]
    simp only [Measure.restrict_apply measurableSet_Ioc, inter_self, Real.volume_Ioc, sub_zero,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact ENNReal.pow_pos (ENNReal.ofReal_pos.2 hb) _
  · filter_upwards [hmem] with v hv
    exact (hpos v hv).le

/-- **State-density asymptotic, unique minimal coordinate**: `Z(n) ~ C(ξ,η) n^{-p/2}`. -/
theorem stateIntegral_isEquivalent (β b : ℝ) (hβ : 0 < β) (hb : 0 < b) (h₀ k₀ : ℕ) (hk₀ : 0 < k₀)
    {d : ℕ} (k' h' : Fin d → ℕ) (hk' : ∀ i, 0 < k' i)
    (hq : ∀ i, ((h₀ : ℝ) + 1) / k₀ < ((h' i : ℝ) + 1) / k' i)
    (ξ η : ℝ → (Fin d → ℝ) → ℝ)
    (hξc : Continuous fun x : ℝ × (Fin d → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : ℝ × (Fin d → ℝ) => η x.1 x.2) (C C' : ℝ) (hC : 0 ≤ C)
    (hξ : ∀ u ∈ Ioc (0 : ℝ) b, ∀ v : Fin d → ℝ, |ξ u v - ξ 0 v| ≤ C * u)
    (hη : ∀ u ∈ Ioc (0 : ℝ) b, ∀ v : Fin d → ℝ, |η u v - η 0 v| ≤ C' * u)
    (hηpos : ∀ v : Fin d → ℝ, (∀ i, 0 < v i ∧ v i ≤ b) → 0 < η 0 v) :
    (fun n : ℝ => stateIntegral β b n h₀ k₀ k' h' ξ η) ~[atTop]
      fun n : ℝ => (∫ v, divisorDensity β h₀ k₀ k' h' ξ η v ∂(boxMeasure b d))
        * n ^ (-(((h₀ : ℝ) + 1) / k₀ / 2)) := by
  set p : ℝ := ((h₀ : ℝ) + 1) / k₀ with hp
  set Cd : ℝ := ∫ v, divisorDensity β h₀ k₀ k' h' ξ η v ∂(boxMeasure b d) with hCd
  have hCd0 : 0 < Cd :=
    integral_divisorDensity_pos β b hβ hb h₀ k₀ hk₀ k' h' hk' hq ξ η hξc hηc hηpos
  have ht := stateIntegral_tendsto β b hβ hb h₀ k₀ hk₀ k' h' hk' hq ξ η hξc hηc C C' hC hξ hη
  rw [← hp, ← hCd] at ht
  have h1 : (fun n : ℝ => n ^ (p / 2) * stateIntegral β b n h₀ k₀ k' h' ξ η) ~[atTop]
      Function.const ℝ Cd := (isEquivalent_const_iff_tendsto hCd0.ne').2 ht
  have h2 := (IsEquivalent.refl (u := fun n : ℝ => n ^ (-(p / 2))) (l := atTop)).mul h1
  refine (h2.congr_left ?_).congr_right ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← Real.rpow_add hn, neg_add_cancel, Real.rpow_zero, one_mul]
  · filter_upwards with n
    simp only [Pi.mul_apply, Function.const_apply]
    ring

end Laplace.Grammar
