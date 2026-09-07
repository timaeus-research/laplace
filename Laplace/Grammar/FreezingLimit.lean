/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.FreezingInequality

/-!
# Minimal block VI: the freezing limit (grammar §4.2, multiplicity `m = d₀+2`)

The right-hand side of the freezing inequality is normalised by `N^p / (log N)^{d₀+1}`:

* the strip terms (shifted exponents) vanish, since the mixed-block envelope loses one logarithm
  (`constStateIntegral_shift_tendsto_zero`);
* the corner term converges to `ω · C₄` by the frozen coefficient theorem;
* uniform continuity of `ξ, η` on the closed box makes `ω` arbitrarily small
  (`corner_oscillation`).

Hence `N^p (Z(N) − Z₀(N)) / (log N)^{d₀+1} → 0` (`blockStateIntegral_sub_frozen_tendsto`): the
leading coefficient of a multiplicity-`m ≥ 2` block sees only the values of `ξ, η` on the minimal
face `u = 0`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- **Uniform continuity on the closed box, corner form**: for every `ε > 0` there is `δ > 0` with
`|ξ(u,v) − ξ(0,v)| ≤ ε` whenever all `uᵢ ≤ δ`. -/
theorem corner_oscillation {m d' : ℕ} (b : ℝ) (hb : 0 < b) (ξ : (Fin m → ℝ) → (Fin d' → ℝ) → ℝ)
    (hξc : Continuous fun x : (Fin m → ℝ) × (Fin d' → ℝ) => ξ x.1 x.2) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ u v, (∀ i, 0 ≤ u i ∧ u i ≤ b) → (∀ i, 0 ≤ v i ∧ v i ≤ b) → (∀ i, u i ≤ δ) →
      |ξ u v - ξ 0 v| ≤ ε := by
  set S : Set ((Fin m → ℝ) × (Fin d' → ℝ)) :=
    (Set.pi univ fun _ : Fin m => Icc (0 : ℝ) b) ×ˢ (Set.pi univ fun _ : Fin d' => Icc (0 : ℝ) b)
    with hS
  have hcpt : IsCompact S :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have huc := hcpt.uniformContinuousOn_of_continuous hξc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ₀, hδ₀, hδ⟩ := huc ε hε
  refine ⟨δ₀ / 2, by positivity, fun u v hu hv hcorner => ?_⟩
  have hmem1 : (u, v) ∈ S := by
    rw [hS, mem_prod, Set.mem_univ_pi, Set.mem_univ_pi]
    exact ⟨fun i => hu i, fun i => hv i⟩
  have hmem2 : ((0 : Fin m → ℝ), v) ∈ S := by
    rw [hS, mem_prod, Set.mem_univ_pi, Set.mem_univ_pi]
    exact ⟨fun i => ⟨le_rfl, hb.le⟩, fun i => hv i⟩
  have hdist : dist (u, v) ((0 : Fin m → ℝ), v) < δ₀ := by
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    refine lt_of_le_of_lt ((dist_pi_le_iff (by positivity)).2 fun i => ?_) (half_lt_self hδ₀)
    change |u i - (0 : Fin m → ℝ) i| ≤ δ₀ / 2
    rw [Pi.zero_apply, sub_zero, abs_of_nonneg (hu i).1]
    exact hcorner i
  have := hδ _ hmem1 _ hmem2 hdist
  rw [Real.dist_eq] at this
  exact this.le

/-- Joint corner oscillation bound for `ξ` and `η`. -/
theorem corner_oscillation₂ {m d' : ℕ} (b : ℝ) (hb : 0 < b)
    (ξ η : (Fin m → ℝ) → (Fin d' → ℝ) → ℝ)
    (hξc : Continuous fun x : (Fin m → ℝ) × (Fin d' → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : (Fin m → ℝ) × (Fin d' → ℝ) => η x.1 x.2) (ω : ℝ) (hω : 0 < ω) :
    ∃ δ > 0, ∀ u v, (∀ i, 0 < u i ∧ u i ≤ b) → (∀ i, 0 < v i ∧ v i ≤ b) → (∀ i, u i ≤ δ) →
      |η u v - η 0 v| + |ξ u v - ξ 0 v| ≤ ω := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := corner_oscillation b hb ξ hξc (ω / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, h₂⟩ := corner_oscillation b hb η hηc (ω / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun u v hu hv hc => ?_⟩
  have hu' : ∀ i, 0 ≤ u i ∧ u i ≤ b := fun i => ⟨(hu i).1.le, (hu i).2⟩
  have hv' : ∀ i, 0 ≤ v i ∧ v i ≤ b := fun i => ⟨(hv i).1.le, (hv i).2⟩
  have a1 := h₁ u v hu' hv' fun i => (hc i).trans (min_le_left _ _)
  have a2 := h₂ u v hu' hv' fun i => (hc i).trans (min_le_right _ _)
  linarith

/-- The constant-`ξ` state integral is nonnegative. -/
theorem constStateIntegral_nonneg (β a b N : ℝ) {m d' : ℕ} (k h : Fin m → ℕ)
    (k' h' : Fin d' → ℕ) : 0 ≤ constStateIntegral β a b N k h k' h' := by
  unfold constStateIntegral
  refine integral_nonneg_of_ae ?_
  rw [boxMeasure_eq_restrict]
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ : Fin d' => measurableSet_Ioc)]
    with v hv
  rw [Set.mem_univ_pi] at hv
  exact mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (hv i).1.le _)
    (boxIntegralFin_nonneg _ _ _ _ _ _)

/-- **The strip terms vanish**: for an equal-exponent block on `Fin (d₀+2)` with one exponent
shifted, `N^p Z^{a}_{h+eᵢ}(N) / (log N)^{d₀+1} → 0`. -/
theorem constStateIntegral_shift_tendsto_zero (β a b p : ℝ) (hβ : 0 < β) (hb : 0 < b) {d₀ d' : ℕ}
    (k h : Fin (d₀ + 2) → ℕ) (hk : ∀ j, 0 < k j) (hp : ∀ j, finExp k h j = p)
    (k' h' : Fin d' → ℕ) (hk' : ∀ i, 0 < k' i) (hq : ∀ i, p < ((h' i : ℝ) + 1) / k' i)
    (i : Fin (d₀ + 2)) :
    Tendsto (fun N : ℝ => N ^ p / Real.log N ^ (d₀ + 1)
      * constStateIntegral β a b N k (shiftExp h i) k' h') atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ := boxIntegralFin_shift_le β a b hβ hb k h hk p hp i
  set B : ℝ := b ^ (∑ j, k j) with hB
  have hBpos : 0 < B := by positivity
  set B' : ℝ := b ^ (∑ i, k' i) with hB'
  have hB'pos : 0 < B' := by positivity
  set I : ℝ := ∫ v, ∏ i, (v i ^ h' i * (v i ^ k' i) ^ (-p)) ∂(boxMeasure b d') with hI
  have hIint := divisorWeight_integrable b k' h' hk' p hq
  have hI0 : 0 ≤ I := by
    rw [hI]
    refine integral_nonneg_of_ae ?_
    rw [boxMeasure_eq_restrict]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ : Fin d' => measurableSet_Ioc)]
      with v hv
    rw [Set.mem_univ_pi] at hv
    exact Finset.prod_nonneg fun i _ => mul_nonneg (pow_nonneg (hv i).1.le _)
      (Real.rpow_nonneg (pow_nonneg (hv i).1.le _) _)
  set C : ℝ := K * (2 + logPlus (B' * B)) ^ d₀ * I with hC
  have hC0 : 0 ≤ C := by
    have := logPlus_nonneg (B' * B)
    positivity
  have hlim : Tendsto (fun N : ℝ => C / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hNpos : 0 < N := by linarith
    exact mul_nonneg (div_nonneg (Real.rpow_nonneg hNpos.le _)
      (pow_nonneg (Real.log_nonneg hN.le) _)) (constStateIntegral_nonneg _ _ _ _ _ _ _ _)
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
  have hNpos : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hN
  have hlogN : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hN
  have hlogN0 : 0 < Real.log N := by linarith
  have hNp : 0 < N ^ p := Real.rpow_pos_of_pos hNpos p
  -- pointwise bound on the open box
  have hpt : ∀ v : Fin d' → ℝ, (∀ i, 0 < v i ∧ v i ≤ b) →
      (∏ i, v i ^ h' i) * boxIntegralFin β a b (N * ∏ i, v i ^ k' i) k (shiftExp h i)
        ≤ (K * (2 + logPlus (B' * B)) ^ d₀ * (Real.log N ^ d₀ / N ^ p))
          * ∏ i, (v i ^ h' i * (v i ^ k' i) ^ (-p)) := by
    intro v hv
    have hv' : ∀ i, 0 < v i := fun i => (hv i).1
    have hV : 0 < ∏ i, v i ^ k' i := Finset.prod_pos fun i _ => pow_pos (hv' i) _
    set c : ℝ := N * ∏ i, v i ^ k' i with hc
    have hc0 : 0 < c := by positivity
    have henv := hbound c hc0
    have hscale : ∏ i, v i ^ k' i ≤ B' := by
      rw [hB', ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod (fun i _ => pow_nonneg (hv i).1.le _)
        fun i _ => pow_le_pow_left₀ (hv i).1.le (hv i).2 _
    have hlogcB : logPlus (c * B) ≤ Real.log N + logPlus (B' * B) := by
      calc logPlus (c * B) = logPlus (N * ((∏ i, v i ^ k' i) * B)) := by rw [hc, mul_assoc]
        _ ≤ logPlus N + logPlus ((∏ i, v i ^ k' i) * B) :=
            logPlus_mul_le _ _ hNpos (by positivity)
        _ ≤ Real.log N + logPlus (B' * B) := by
            rw [logPlus_eq_log N (by linarith [Real.add_one_le_exp (1 : ℝ)])]
            gcongr
            exact logPlus_le_logPlus _ _ (by positivity)
              (mul_le_mul_of_nonneg_right hscale hBpos.le)
    have hratio : (1 + logPlus (c * B)) ^ d₀ ≤ (2 + logPlus (B' * B)) ^ d₀ * Real.log N ^ d₀ := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by linarith [logPlus_nonneg (c * B)]) ?_ d₀
      have := logPlus_nonneg (B' * B)
      nlinarith
    have hZ0 := boxIntegralFin_nonneg β a b c k (shiftExp h i)
    have hcp : 0 < c ^ p := Real.rpow_pos_of_pos hc0 p
    have hZ : boxIntegralFin β a b c k (shiftExp h i)
        ≤ K * (2 + logPlus (B' * B)) ^ d₀ * Real.log N ^ d₀ * c ^ (-p) := by
      have h1 : c ^ p * boxIntegralFin β a b c k (shiftExp h i)
          ≤ K * ((2 + logPlus (B' * B)) ^ d₀ * Real.log N ^ d₀) :=
        henv.trans (mul_le_mul_of_nonneg_left hratio hK)
      have hcinv : c ^ (-p) = (c ^ p)⁻¹ := Real.rpow_neg hc0.le p
      rw [hcinv, ← div_eq_mul_inv, le_div_iff₀ hcp]
      linarith [h1]
    have hnpow : c ^ (-p) = (N ^ p)⁻¹ * (∏ i, v i ^ k' i) ^ (-p) := by
      rw [hc, Real.mul_rpow hNpos.le hV.le, Real.rpow_neg hNpos.le]
    have hprodh : 0 ≤ ∏ i, v i ^ h' i := Finset.prod_nonneg fun i _ => pow_nonneg (hv' i).le _
    have hprod : (∏ i, v i ^ h' i) * (∏ i, v i ^ k' i) ^ (-p)
        = ∏ i, (v i ^ h' i * (v i ^ k' i) ^ (-p)) := by
      rw [Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ fun i _ => pow_nonneg (hv' i).le _]
    calc (∏ i, v i ^ h' i) * boxIntegralFin β a b c k (shiftExp h i)
        ≤ (∏ i, v i ^ h' i) * (K * (2 + logPlus (B' * B)) ^ d₀ * Real.log N ^ d₀ * c ^ (-p)) :=
          mul_le_mul_of_nonneg_left hZ hprodh
      _ = (K * (2 + logPlus (B' * B)) ^ d₀ * (Real.log N ^ d₀ / N ^ p))
          * ((∏ i, v i ^ h' i) * (∏ i, v i ^ k' i) ^ (-p)) := by
          rw [hnpow]; field_simp
      _ = _ := by rw [hprod]
  -- integrate the bound
  have hint : constStateIntegral β a b N k (shiftExp h i) k' h'
      ≤ (K * (2 + logPlus (B' * B)) ^ d₀ * (Real.log N ^ d₀ / N ^ p)) * I := by
    unfold constStateIntegral
    rw [hI, ← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hIint.const_mul _) ?_
    · rw [boxMeasure_eq_restrict]
      filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ : Fin d' => measurableSet_Ioc)]
        with v hv
      rw [Set.mem_univ_pi] at hv
      exact mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (hv i).1.le _)
        (boxIntegralFin_nonneg _ _ _ _ _ _)
    · rw [boxMeasure_eq_restrict]
      filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ : Fin d' => measurableSet_Ioc)]
        with v hv
      rw [Set.mem_univ_pi] at hv
      exact hpt v hv
  calc N ^ p / Real.log N ^ (d₀ + 1) * constStateIntegral β a b N k (shiftExp h i) k' h'
      ≤ N ^ p / Real.log N ^ (d₀ + 1)
          * ((K * (2 + logPlus (B' * B)) ^ d₀ * (Real.log N ^ d₀ / N ^ p)) * I) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = C / Real.log N := by
        rw [hC]; field_simp; ring

/-- The frozen block state integral equals the frozen state integral of unit 75. -/
theorem blockStateIntegral_frozen_eq (β b N : ℝ) {d d' : ℕ} (k h : Fin (d + 1) → ℕ)
    (k' h' : Fin d' → ℕ) (ξ η : (Fin (d + 1) → ℝ) → (Fin d' → ℝ) → ℝ) :
    blockStateIntegral β b N k h k' h' (fun _ v => ξ 0 v) (fun _ v => η 0 v)
      = frozenStateIntegral β b N (toNatFun k 1) (toNatFun h 0) d k' h' (fun v => ξ 0 v)
          (fun v => η 0 v) := by
  unfold blockStateIntegral frozenStateIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  beta_reduce
  rw [← boxIntegral_eq_iterChartGen, ← boxIntegralFin_eq_toNatFun, boxIntegralFin]
  have hL : (∫ u : Fin (d + 1) → ℝ, (∏ i, u i ^ h i) * η 0 v
        * quadKernel β (ξ 0 v) (N * (∏ i, v i ^ k' i) * ∏ i, u i ^ k i) ∂(boxMeasure b (d + 1)))
      = ∫ u : Fin (d + 1) → ℝ, η 0 v * ((∏ i, u i ^ h i)
        * quadKernel β (ξ 0 v) (N * (∏ i, v i ^ k' i) * ∏ i, u i ^ k i)) ∂(boxMeasure b (d + 1)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
  rw [hL, integral_const_mul]
  ring

/-- **The freezing limit**: `N^p (Z(N) − Z₀(N)) / (log N)^{d₀+1} → 0` for jointly continuous
`ξ, η` on an equal-exponent block of multiplicity `d₀+2` with noncritical coordinates. -/
theorem blockStateIntegral_sub_frozen_tendsto (β b p : ℝ) (hβ : 0 < β) (hb : 0 < b) {d₀ d' : ℕ}
    (k h : Fin (d₀ + 2) → ℕ) (hk : ∀ j, 0 < k j) (hp : ∀ j, finExp k h j = p)
    (k' h' : Fin d' → ℕ) (hk' : ∀ i, 0 < k' i) (hq : ∀ i, p < ((h' i : ℝ) + 1) / k' i)
    (ξ η : (Fin (d₀ + 2) → ℝ) → (Fin d' → ℝ) → ℝ)
    (hξc : Continuous fun x : (Fin (d₀ + 2) → ℝ) × (Fin d' → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : (Fin (d₀ + 2) → ℝ) × (Fin d' → ℝ) => η x.1 x.2) :
    Tendsto (fun N : ℝ => N ^ p / Real.log N ^ (d₀ + 1)
      * (blockStateIntegral β b N k h k' h' ξ η
        - blockStateIntegral β b N k h k' h' (fun _ v => ξ 0 v) (fun _ v => η 0 v))) atTop
      (𝓝 0) := by
  -- bounds on the closed box
  have hcpt : IsCompact ((Set.pi univ fun _ : Fin (d₀ + 2) => Icc (0 : ℝ) b)
      ×ˢ (Set.pi univ fun _ : Fin d' => Icc (0 : ℝ) b)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨L₀, hL₀⟩ := hcpt.exists_bound_of_continuousOn hξc.continuousOn
  obtain ⟨M₀, hM₀⟩ := hcpt.exists_bound_of_continuousOn hηc.continuousOn
  set L : ℝ := max L₀ 0 with hLdef
  set M : ℝ := max M₀ 0 with hMdef
  have hL : 0 ≤ L := le_max_right _ _
  have hM : 0 ≤ M := le_max_right _ _
  have hξL : ∀ u v, (∀ i, 0 ≤ u i ∧ u i ≤ b) → (∀ i, 0 ≤ v i ∧ v i ≤ b) → |ξ u v| ≤ L := by
    intro u v hu hv
    have hmem : (u, v) ∈ (Set.pi univ fun _ : Fin (d₀ + 2) => Icc (0 : ℝ) b)
        ×ˢ (Set.pi univ fun _ : Fin d' => Icc (0 : ℝ) b) := by
      rw [mem_prod, Set.mem_univ_pi, Set.mem_univ_pi]; exact ⟨hu, hv⟩
    have := hL₀ (u, v) hmem; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hηM : ∀ u v, (∀ i, 0 ≤ u i ∧ u i ≤ b) → (∀ i, 0 ≤ v i ∧ v i ≤ b) → |η u v| ≤ M := by
    intro u v hu hv
    have hmem : (u, v) ∈ (Set.pi univ fun _ : Fin (d₀ + 2) => Icc (0 : ℝ) b)
        ×ˢ (Set.pi univ fun _ : Fin d' => Icc (0 : ℝ) b) := by
      rw [mem_prod, Set.mem_univ_pi, Set.mem_univ_pi]; exact ⟨hu, hv⟩
    have := hM₀ (u, v) hmem; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  set C₂ : ℝ := max 1 (M * Real.exp (β / 2)) with hC₂
  have hC₂pos : 0 < C₂ := lt_of_lt_of_le one_pos (le_max_left _ _)
  set Dmax : ℝ := 2 * M + 2 * L with hDmax
  have hDmax0 : 0 ≤ Dmax := by positivity
  -- the corner term converges
  have hp' : ∀ i, i ≤ d₀ + 1 → ((toNatFun h 0 i : ℝ) + 1) / toNatFun k 1 i = p := by
    intro i hi
    have hi' : i < d₀ + 2 := by omega
    have := chartExp_toNatFun_eq_finExp k h ⟨i, hi'⟩
    rw [chartExp] at this
    rw [this]; exact hp _
  have hk'' : ∀ i, 0 < toNatFun k 1 i := toNatFun_pos k hk
  have hA := frozenStateIntegral_tendsto (β / 2) b p (by positivity) hb (toNatFun k 1)
    (toNatFun h 0) hk'' (d₀ + 1) hp' k' h' hk' hq (fun _ => 2 * L) (fun _ => 1) continuous_const
    continuous_const
  set C₄ := ∫ v, blockDivisorDensity (β / 2) p (toNatFun k 1) (d₀ + 1) k' h' (fun _ => 2 * L)
    (fun _ => 1) v ∂(boxMeasure b d') with hC₄
  have hA' : Tendsto (fun N : ℝ => N ^ p / Real.log N ^ (d₀ + 1)
      * constStateIntegral (β / 2) (2 * L) b N k h k' h') atTop (𝓝 C₄) := by
    refine hA.congr' (Filter.Eventually.of_forall fun N => ?_)
    beta_reduce
    rw [constStateIntegral_eq_frozen]
  -- the strip terms vanish
  have hS : Tendsto (fun N : ℝ => N ^ p / Real.log N ^ (d₀ + 1)
      * ∑ i, constStateIntegral (β / 2) (2 * L) b N k (shiftExp h i) k' h') atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin (d₀ + 2))) fun i _ =>
      constStateIntegral_shift_tendsto_zero (β / 2) (2 * L) b p (by positivity) hb k h hk hp k' h'
        hk' hq i
    simp only [Finset.sum_const_zero] at this
    refine this.congr' (Filter.Eventually.of_forall fun N => ?_)
    beta_reduce
    rw [Finset.mul_sum]
  -- ε-argument
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ω : ℝ := ε / (2 * C₂ * (|C₄| + 1)) with hω
  have hωpos : 0 < ω := by positivity
  obtain ⟨δ, hδ, hcorner⟩ := corner_oscillation₂ b hb ξ η hξc hηc ω hωpos
  set ε₂ : ℝ := ε / (2 * C₂ * (Dmax / δ + 1)) with hε₂
  have hε₂pos : 0 < ε₂ := by positivity
  have hAev : ∀ᶠ N in atTop, N ^ p / Real.log N ^ (d₀ + 1)
      * constStateIntegral (β / 2) (2 * L) b N k h k' h' < |C₄| + 1 :=
    hA'.eventually_lt_const (by linarith [le_abs_self C₄])
  have hSev : ∀ᶠ N in atTop, N ^ p / Real.log N ^ (d₀ + 1)
      * ∑ i, constStateIntegral (β / 2) (2 * L) b N k (shiftExp h i) k' h' < ε₂ :=
    hS.eventually_lt_const hε₂pos
  filter_upwards [hAev, hSev, eventually_gt_atTop (1 : ℝ)] with N hAN hSN hN1
  have hNpos : 0 < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hpref : 0 < N ^ p / Real.log N ^ (d₀ + 1) := by positivity
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hpref]
  have hkey := blockStateIntegral_sub_le β b hβ hb k h k' h' ξ η hξc hηc L M hL hM hξL hηM ω δ
    hωpos.le hδ hcorner N hNpos.le
  have hA0 : 0 ≤ N ^ p / Real.log N ^ (d₀ + 1)
      * constStateIntegral (β / 2) (2 * L) b N k h k' h' :=
    mul_nonneg hpref.le (constStateIntegral_nonneg _ _ _ _ _ _ _ _)
  have h1 : N ^ p / Real.log N ^ (d₀ + 1)
      * (C₂ * ω * constStateIntegral (β / 2) (2 * L) b N k h k' h') < ε / 2 := by
    have : C₂ * ω * (|C₄| + 1) = ε / 2 := by
      rw [hω]; field_simp
    calc N ^ p / Real.log N ^ (d₀ + 1) * (C₂ * ω * constStateIntegral (β / 2) (2 * L) b N k h k' h')
        = C₂ * ω * (N ^ p / Real.log N ^ (d₀ + 1)
            * constStateIntegral (β / 2) (2 * L) b N k h k' h') := by ring
      _ < C₂ * ω * (|C₄| + 1) := by gcongr
      _ = ε / 2 := this
  have h2 : N ^ p / Real.log N ^ (d₀ + 1) * (C₂ * (Dmax / δ)
      * ∑ i, constStateIntegral (β / 2) (2 * L) b N k (shiftExp h i) k' h') ≤ ε / 2 := by
    have hDδ : 0 ≤ Dmax / δ := div_nonneg hDmax0 hδ.le
    have : C₂ * (Dmax / δ) * ε₂ ≤ ε / 2 := by
      rw [hε₂]
      rw [show C₂ * (Dmax / δ) * (ε / (2 * C₂ * (Dmax / δ + 1)))
        = ε / 2 * ((Dmax / δ) / (Dmax / δ + 1)) by field_simp]
      have : (Dmax / δ) / (Dmax / δ + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      nlinarith
    calc N ^ p / Real.log N ^ (d₀ + 1) * (C₂ * (Dmax / δ)
          * ∑ i, constStateIntegral (β / 2) (2 * L) b N k (shiftExp h i) k' h')
        = C₂ * (Dmax / δ) * (N ^ p / Real.log N ^ (d₀ + 1)
            * ∑ i, constStateIntegral (β / 2) (2 * L) b N k (shiftExp h i) k' h') := by ring
      _ ≤ C₂ * (Dmax / δ) * ε₂ := by gcongr
      _ ≤ ε / 2 := this
  calc N ^ p / Real.log N ^ (d₀ + 1) * |blockStateIntegral β b N k h k' h' ξ η
        - blockStateIntegral β b N k h k' h' (fun _ v => ξ 0 v) (fun _ v => η 0 v)|
      ≤ N ^ p / Real.log N ^ (d₀ + 1) * (C₂ * (ω * constStateIntegral (β / 2) (2 * L) b N k h k' h'
          + Dmax / δ * ∑ i, constStateIntegral (β / 2) (2 * L) b N k (shiftExp h i) k' h')) :=
        mul_le_mul_of_nonneg_left hkey hpref.le
    _ = N ^ p / Real.log N ^ (d₀ + 1) * (C₂ * ω * constStateIntegral (β / 2) (2 * L) b N k h k' h')
        + N ^ p / Real.log N ^ (d₀ + 1) * (C₂ * (Dmax / δ)
          * ∑ i, constStateIntegral (β / 2) (2 * L) b N k (shiftExp h i) k' h') := by ring
    _ < ε := by linarith

end Laplace.Grammar
