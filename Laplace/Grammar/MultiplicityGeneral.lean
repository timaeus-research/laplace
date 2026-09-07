/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.FreezingLimit

/-!
# The multiplicity-`m` leading term for general `ξ, η` (grammar §4.2, `thm:TaylorTree` leading term)

Combining the freezing limit (unit 78) with the frozen coefficient theorem (unit 75): for a block of
`m = d₀+2` coordinates with common exponent `p = (hᵢ+1)/kᵢ` and noncritical coordinates with
exponents `> p`, and jointly continuous `ξ, η`,

  `N^p Z(N) / (log N)^{d₀+1} → C(ξ,η)`,
  `C(ξ,η) = (∏ kᵢ⁻¹) / (d₀+1)! · ∫_v v^{h'} (v^{k'})^{-p} A_{p-1}(ξ(0,v)) η(0,v) dv`

(`blockStateIntegral_tendsto`); `C > 0` when `η(0,·) > 0`
(`integral_blockDivisorDensity_pos`), giving the asymptotic equivalences
`Z(N) ~ C N^{-p} (log N)^{d₀+1}` (`blockStateIntegral_isEquivalent`) and, at `N = √n`,
`Z ~ (C / 2^{d₀+1}) n^{-p/2} (log n)^{d₀+1}` (`blockStateIntegral_sqrt_isEquivalent`).
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology Asymptotics

namespace Laplace.Grammar

/-- Measurability of the block divisor density. -/
theorem blockDivisorDensity_measurable (β p : ℝ) (hβ : 0 < β) (hp : 0 < p) (k : ℕ → ℕ) (d : ℕ)
    {d' : ℕ} (k' h' : Fin d' → ℕ) (a e : (Fin d' → ℝ) → ℝ) (hac : Continuous a)
    (hec : Continuous e) : Measurable (blockDivisorDensity β p k d k' h' a e) := by
  have hγ : -1 < p - 1 := by linarith
  unfold blockDivisorDensity
  refine ((continuous_prod_pow h').measurable.mul hec.measurable).mul ?_
  exact ((measurable_const.mul ((continuous_prod_pow k').measurable.pow_const _)).mul
    ((weightedMass_measurable_left β _ hβ hγ).comp hac.measurable))

/-- Integrability of the block divisor density. -/
theorem blockDivisorDensity_integrable (β b p : ℝ) (hβ : 0 < β) (hp : 0 < p) (k : ℕ → ℕ) (d : ℕ)
    {d' : ℕ} (k' h' : Fin d' → ℕ) (hk' : ∀ i, 0 < k' i) (hq : ∀ i, p < ((h' i : ℝ) + 1) / k' i)
    (a e : (Fin d' → ℝ) → ℝ) (hac : Continuous a) (hec : Continuous e) :
    Integrable (blockDivisorDensity β p k d k' h' a e) (boxMeasure b d') := by
  have hγ : -1 < p - 1 := by linarith
  have hcpt : IsCompact (Set.pi univ fun _ : Fin d' => Icc (0 : ℝ) b) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨L, hL⟩ := hcpt.exists_bound_of_continuousOn hac.continuousOn
  obtain ⟨M₀, hM₀⟩ := hcpt.exists_bound_of_continuousOn hec.continuousOn
  set M : ℝ := max M₀ 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  set P : ℝ := (∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i) * (1 / (d.factorial : ℝ)) with hP
  have hP0 : 0 ≤ P := by positivity
  have hAL : 0 ≤ weightedMass β L (p - 1) := (weightedMass_pos β L (p - 1) hβ hγ).le
  set K : ℝ := M * (P * weightedMass β L (p - 1)) with hK
  have hmem : ∀ᵐ v ∂(boxMeasure b d'), v ∈ Set.pi univ fun _ : Fin d' => Ioc (0 : ℝ) b := by
    rw [boxMeasure_eq_restrict]
    exact ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
  refine Integrable.mono' (g := fun v => K * ∏ i, (v i ^ h' i * (v i ^ k' i) ^ (-p)))
    ((divisorWeight_integrable b k' h' hk' p hq).const_mul K)
    (blockDivisorDensity_measurable β p hβ hp k d k' h' a e hac hec).aestronglyMeasurable ?_
  filter_upwards [hmem] with v hv
  have hmemI : v ∈ Set.pi univ fun _ : Fin d' => Icc (0 : ℝ) b := by
    rw [Set.mem_univ_pi] at hv ⊢; exact fun i => ⟨(hv i).1.le, (hv i).2⟩
  have hv' : ∀ i, 0 < v i := by rw [Set.mem_univ_pi] at hv; exact fun i => (hv i).1
  have hV : 0 < ∏ i, v i ^ k' i := Finset.prod_pos fun i _ => pow_pos (hv' i) _
  have hH : 0 ≤ ∏ i, v i ^ h' i := Finset.prod_nonneg fun i _ => pow_nonneg (hv' i).le _
  have haL : a v ≤ L := by
    have := hL v hmemI; rw [Real.norm_eq_abs] at this; exact (le_abs_self _).trans this
  have heM : |e v| ≤ M := by
    have := hM₀ v hmemI; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hA : weightedMass β (a v) (p - 1) ≤ weightedMass β L (p - 1) :=
    weightedMass_mono_left β (p - 1) hβ hγ haL
  have hA0 : 0 ≤ weightedMass β (a v) (p - 1) := (weightedMass_pos β _ (p - 1) hβ hγ).le
  have hprod : (∏ i, v i ^ h' i) * (∏ i, v i ^ k' i) ^ (-p)
      = ∏ i, (v i ^ h' i * (v i ^ k' i) ^ (-p)) := by
    rw [Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ fun i _ => pow_nonneg (hv' i).le _]
  have hVp : 0 ≤ (∏ i, v i ^ k' i) ^ (-p) := Real.rpow_nonneg hV.le _
  unfold blockDivisorDensity
  rw [Real.norm_eq_abs, ← hP, ← hprod, abs_mul, abs_mul, abs_of_nonneg hH,
    abs_of_nonneg (mul_nonneg (mul_nonneg hP0 hVp) hA0)]
  calc (∏ i, v i ^ h' i) * |e v| * (P * (∏ i, v i ^ k' i) ^ (-p) * weightedMass β (a v) (p - 1))
      ≤ (∏ i, v i ^ h' i) * M * (P * (∏ i, v i ^ k' i) ^ (-p) * weightedMass β L (p - 1)) := by
        gcongr
    _ = K * ((∏ i, v i ^ h' i) * (∏ i, v i ^ k' i) ^ (-p)) := by rw [hK]; ring

/-- **Positivity of the block divisor coefficient** when `e > 0` on the box. -/
theorem integral_blockDivisorDensity_pos (β b p : ℝ) (hβ : 0 < β) (hb : 0 < b) (hp : 0 < p)
    (k : ℕ → ℕ) (hk : ∀ i, 0 < k i) (d : ℕ) {d' : ℕ} (k' h' : Fin d' → ℕ) (hk' : ∀ i, 0 < k' i)
    (hq : ∀ i, p < ((h' i : ℝ) + 1) / k' i) (a e : (Fin d' → ℝ) → ℝ) (hac : Continuous a)
    (hec : Continuous e) (hepos : ∀ v : Fin d' → ℝ, (∀ i, 0 < v i ∧ v i ≤ b) → 0 < e v) :
    0 < ∫ v, blockDivisorDensity β p k d k' h' a e v ∂(boxMeasure b d') := by
  have hγ : -1 < p - 1 := by linarith
  have hmem : ∀ᵐ v ∂(boxMeasure b d'), v ∈ Set.pi univ fun _ : Fin d' => Ioc (0 : ℝ) b := by
    rw [boxMeasure_eq_restrict]
    exact ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
  have hpos : ∀ v : Fin d' → ℝ, v ∈ (Set.pi univ fun _ : Fin d' => Ioc (0 : ℝ) b) →
      0 < blockDivisorDensity β p k d k' h' a e v := by
    intro v hv
    rw [Set.mem_univ_pi] at hv
    have hv' : ∀ i, 0 < v i := fun i => (hv i).1
    have he := hepos v fun i => ⟨(hv i).1, (hv i).2⟩
    have hA := weightedMass_pos β (a v) (p - 1) hβ hγ
    have hV : 0 < ∏ i, v i ^ k' i := Finset.prod_pos fun i _ => pow_pos (hv' i) _
    have hH : 0 < ∏ i, v i ^ h' i := Finset.prod_pos fun i _ => pow_pos (hv' i) _
    have hP : 0 < ∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i :=
      Finset.prod_pos fun i _ => by have := hk i; positivity
    unfold blockDivisorDensity
    positivity
  rw [integral_pos_iff_support_of_nonneg_ae ?_
    (blockDivisorDensity_integrable β b p hβ hp k d k' h' hk' hq a e hac hec)]
  · have hsub : (Set.pi univ fun _ : Fin d' => Ioc (0 : ℝ) b)
        ⊆ Function.support (blockDivisorDensity β p k d k' h' a e) := fun v hv => (hpos v hv).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [boxMeasure, Measure.pi_pi]
    simp only [Measure.restrict_apply measurableSet_Ioc, inter_self, Real.volume_Ioc, sub_zero,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact ENNReal.pow_pos (ENNReal.ofReal_pos.2 hb) _
  · filter_upwards [hmem] with v hv
    exact (hpos v hv).le

/-- The leading coefficient of the multiplicity-`(d₀+2)` block with general `ξ, η`. -/
noncomputable def blockCoeff (β b p : ℝ) {d₀ d' : ℕ} (k : Fin (d₀ + 2) → ℕ) (k' h' : Fin d' → ℕ)
    (ξ η : (Fin (d₀ + 2) → ℝ) → (Fin d' → ℝ) → ℝ) : ℝ :=
  ∫ v, blockDivisorDensity β p (toNatFun k 1) (d₀ + 1) k' h' (fun v => ξ 0 v) (fun v => η 0 v) v
    ∂(boxMeasure b d')

/-- **Leading term of the general multiplicity-`m` block**: `N^p Z(N)/(log N)^{d₀+1} → C(ξ,η)`. -/
theorem blockStateIntegral_tendsto (β b p : ℝ) (hβ : 0 < β) (hb : 0 < b) {d₀ d' : ℕ}
    (k h : Fin (d₀ + 2) → ℕ) (hk : ∀ j, 0 < k j) (hp : ∀ j, finExp k h j = p)
    (k' h' : Fin d' → ℕ) (hk' : ∀ i, 0 < k' i) (hq : ∀ i, p < ((h' i : ℝ) + 1) / k' i)
    (ξ η : (Fin (d₀ + 2) → ℝ) → (Fin d' → ℝ) → ℝ)
    (hξc : Continuous fun x : (Fin (d₀ + 2) → ℝ) × (Fin d' → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : (Fin (d₀ + 2) → ℝ) × (Fin d' → ℝ) => η x.1 x.2) :
    Tendsto (fun N : ℝ => N ^ p / Real.log N ^ (d₀ + 1) * blockStateIntegral β b N k h k' h' ξ η)
      atTop (𝓝 (blockCoeff β b p k k' h' ξ η)) := by
  have hp' : ∀ i, i ≤ d₀ + 1 → ((toNatFun h 0 i : ℝ) + 1) / toNatFun k 1 i = p := by
    intro i hi
    have hi' : i < d₀ + 2 := by omega
    have := chartExp_toNatFun_eq_finExp k h ⟨i, hi'⟩
    rw [chartExp] at this
    rw [this]; exact hp _
  have hk'' : ∀ i, 0 < toNatFun k 1 i := toNatFun_pos k hk
  have hξ0 : Continuous fun v : Fin d' → ℝ => ξ 0 v :=
    hξc.comp (continuous_const.prodMk continuous_id)
  have hη0 : Continuous fun v : Fin d' → ℝ => η 0 v :=
    hηc.comp (continuous_const.prodMk continuous_id)
  have hZ₀ := frozenStateIntegral_tendsto β b p hβ hb (toNatFun k 1) (toNatFun h 0) hk'' (d₀ + 1)
    hp' k' h' hk' hq (fun v => ξ 0 v) (fun v => η 0 v) hξ0 hη0
  have hdiff := blockStateIntegral_sub_frozen_tendsto β b p hβ hb k h hk hp k' h' hk' hq ξ η hξc hηc
  have hsum := hdiff.add hZ₀
  rw [zero_add] at hsum
  refine hsum.congr' (Filter.Eventually.of_forall fun N => ?_)
  simp only
  rw [blockStateIntegral_frozen_eq]
  ring

/-- **Asymptotic equivalence** `Z(N) ~ C(ξ,η) N^{-p} (log N)^{d₀+1}` when `η(0,·) > 0`. -/
theorem blockStateIntegral_isEquivalent (β b p : ℝ) (hβ : 0 < β) (hb : 0 < b) {d₀ d' : ℕ}
    (k h : Fin (d₀ + 2) → ℕ) (hk : ∀ j, 0 < k j) (hp : ∀ j, finExp k h j = p)
    (k' h' : Fin d' → ℕ) (hk' : ∀ i, 0 < k' i) (hq : ∀ i, p < ((h' i : ℝ) + 1) / k' i)
    (ξ η : (Fin (d₀ + 2) → ℝ) → (Fin d' → ℝ) → ℝ)
    (hξc : Continuous fun x : (Fin (d₀ + 2) → ℝ) × (Fin d' → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : (Fin (d₀ + 2) → ℝ) × (Fin d' → ℝ) => η x.1 x.2)
    (hηpos : ∀ v : Fin d' → ℝ, (∀ i, 0 < v i ∧ v i ≤ b) → 0 < η 0 v) :
    (fun N : ℝ => blockStateIntegral β b N k h k' h' ξ η) ~[atTop]
      fun N : ℝ => blockCoeff β b p k k' h' ξ η * (N ^ (-p) * Real.log N ^ (d₀ + 1)) := by
  have hp0 : 0 < p := by rw [← hp 0]; exact finExp_pos k h hk 0
  have hC : 0 < blockCoeff β b p k k' h' ξ η :=
    integral_blockDivisorDensity_pos β b p hβ hb hp0 (toNatFun k 1) (toNatFun_pos k hk) (d₀ + 1)
      k' h' hk' hq (fun v => ξ 0 v) (fun v => η 0 v)
      (hξc.comp (continuous_const.prodMk continuous_id))
      (hηc.comp (continuous_const.prodMk continuous_id)) hηpos
  have ht := blockStateIntegral_tendsto β b p hβ hb k h hk hp k' h' hk' hq ξ η hξc hηc
  have h1 : (fun N : ℝ => N ^ p / Real.log N ^ (d₀ + 1) * blockStateIntegral β b N k h k' h' ξ η)
      ~[atTop] Function.const ℝ (blockCoeff β b p k k' h' ξ η) :=
    (isEquivalent_const_iff_tendsto hC.ne').2 ht
  have h2 := (IsEquivalent.refl (u := fun N : ℝ => N ^ (-p) * Real.log N ^ (d₀ + 1))
    (l := atTop)).mul h1
  refine (h2.congr_left ?_).congr_right ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    have hlog : 0 < Real.log N := Real.log_pos hN
    simp only [Pi.mul_apply]
    have hNN : N ^ (-p) * N ^ p = 1 := by rw [← Real.rpow_add hN0]; simp
    have hlogne : Real.log N ^ (d₀ + 1) ≠ 0 := pow_ne_zero _ hlog.ne'
    rw [show N ^ (-p) * Real.log N ^ (d₀ + 1)
        * (N ^ p / Real.log N ^ (d₀ + 1) * blockStateIntegral β b N k h k' h' ξ η)
      = (N ^ (-p) * N ^ p) * (Real.log N ^ (d₀ + 1) / Real.log N ^ (d₀ + 1))
        * blockStateIntegral β b N k h k' h' ξ η by ring, hNN, div_self hlogne, one_mul, one_mul]
  · filter_upwards with N
    simp only [Pi.mul_apply, Function.const_apply]
    ring

/-- **The `n`-form** (`N = √n`): `Z(√n) ~ (C/2^{d₀+1}) n^{-p/2} (log n)^{d₀+1}`. -/
theorem blockStateIntegral_sqrt_isEquivalent (β b p : ℝ) (hβ : 0 < β) (hb : 0 < b) {d₀ d' : ℕ}
    (k h : Fin (d₀ + 2) → ℕ) (hk : ∀ j, 0 < k j) (hp : ∀ j, finExp k h j = p)
    (k' h' : Fin d' → ℕ) (hk' : ∀ i, 0 < k' i) (hq : ∀ i, p < ((h' i : ℝ) + 1) / k' i)
    (ξ η : (Fin (d₀ + 2) → ℝ) → (Fin d' → ℝ) → ℝ)
    (hξc : Continuous fun x : (Fin (d₀ + 2) → ℝ) × (Fin d' → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : (Fin (d₀ + 2) → ℝ) × (Fin d' → ℝ) => η x.1 x.2)
    (hηpos : ∀ v : Fin d' → ℝ, (∀ i, 0 < v i ∧ v i ≤ b) → 0 < η 0 v) :
    (fun n : ℝ => blockStateIntegral β b (Real.sqrt n) k h k' h' ξ η) ~[atTop]
      fun n : ℝ => blockCoeff β b p k k' h' ξ η / 2 ^ (d₀ + 1)
        * (n ^ (-(p / 2)) * Real.log n ^ (d₀ + 1)) := by
  have hE := blockStateIntegral_isEquivalent β b p hβ hb k h hk hp k' h' hk' hq ξ η hξc hηc hηpos
  have hcomp := hE.comp_tendsto tendsto_sqrt_atTop
  refine hcomp.congr_right ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
  simp only [Function.comp]
  rw [Real.log_sqrt hn.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le, div_pow]
  rw [show (1 / 2 : ℝ) * -p = -(p / 2) by ring]
  ring

end Laplace.Grammar
