/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MixedBlockEnvelope

/-!
# Minimal block V: the freezing inequality (grammar §4.2, multiplicity `m`)

For the block state integral with general jointly continuous `ξ, η` (block `u ∈ (0,b]^m`,
noncritical `v ∈ (0,b]^{d'}`) and its frozen version (`ξ(0,v), η(0,v)`), the mean-value bound,
the corner/strip split and the exact structure of the integrand give, at every scale `N ≥ 0`,

  `|Z(N) − Z₀(N)| ≤ C₂ (ω Z^{β/2,2L}_{h}(N) + (D_max/δ) ∑ᵢ Z^{β/2,2L}_{h+eᵢ}(N))`

(`blockStateIntegral_sub_le`), where `Z^{β/2,2L}_{h}` is the constant-`ξ` state integral with
kernel `e^{-(β/2)s² + βLs}` and `ω` bounds the oscillation of `ξ, η` on the corner
`{uᵢ ≤ δ}`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- Continuous functions on the product box are integrable for the product box measure. -/
theorem integrable_box_prod_of_continuous (b : ℝ) {d' m : ℕ}
    (F : (Fin d' → ℝ) × (Fin m → ℝ) → ℝ) (hF : Continuous F) :
    Integrable F ((boxMeasure b d').prod (boxMeasure b m)) := by
  rw [boxMeasure_eq_restrict, boxMeasure_eq_restrict, Measure.prod_restrict,
    ← Measure.volume_eq_prod]
  have hcpt : IsCompact ((Set.pi univ fun _ : Fin d' => Icc (0 : ℝ) b)
      ×ˢ (Set.pi univ fun _ : Fin m => Icc (0 : ℝ) b)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  exact (hF.continuousOn.integrableOn_compact hcpt).mono_set
    (prod_mono (pi_mono fun i _ => Ioc_subset_Icc_self) (pi_mono fun i _ => Ioc_subset_Icc_self))

/-- Almost every point of the product box lies in the open product box. -/
theorem ae_mem_box_prod (b : ℝ) {d' m : ℕ} :
    ∀ᵐ z : (Fin d' → ℝ) × (Fin m → ℝ) ∂((boxMeasure b d').prod (boxMeasure b m)),
      (∀ i, 0 < z.1 i ∧ z.1 i ≤ b) ∧ (∀ i, 0 < z.2 i ∧ z.2 i ≤ b) := by
  rw [boxMeasure_eq_restrict, boxMeasure_eq_restrict, Measure.prod_restrict]
  have := ae_restrict_mem (μ := (volume : Measure (Fin d' → ℝ)).prod (volume : Measure (Fin m → ℝ)))
    (s := (Set.pi univ fun _ : Fin d' => Ioc (0 : ℝ) b)
      ×ˢ (Set.pi univ fun _ : Fin m => Ioc (0 : ℝ) b))
    ((MeasurableSet.univ_pi fun _ : Fin d' => measurableSet_Ioc).prod
      (MeasurableSet.univ_pi fun _ : Fin m => measurableSet_Ioc))
  filter_upwards [this] with z hz
  rw [mem_prod, Set.mem_univ_pi, Set.mem_univ_pi] at hz
  exact hz

/-- `u^{h+eᵢ} = u^h uᵢ`. -/
theorem prod_shiftExp {m : ℕ} (u : Fin m → ℝ) (h : Fin m → ℕ) (i : Fin m) :
    ∏ j, u j ^ shiftExp h i j = (∏ j, u j ^ h j) * u i := by
  simp only [shiftExp, pow_add, Finset.prod_mul_distrib]
  congr 1
  simp [Finset.prod_ite_eq']

/-- The block state integral with general `ξ, η`: outer noncritical `v`, inner block `u`. -/
noncomputable def blockStateIntegral (β b N : ℝ) {m d' : ℕ} (k h : Fin m → ℕ) (k' h' : Fin d' → ℕ)
    (ξ η : (Fin m → ℝ) → (Fin d' → ℝ) → ℝ) : ℝ :=
  ∫ v : Fin d' → ℝ, (∏ i, v i ^ h' i) * (∫ u : Fin m → ℝ, (∏ i, u i ^ h i) * η u v
      * quadKernel β (ξ u v) (N * (∏ i, v i ^ k' i) * ∏ i, u i ^ k i) ∂(boxMeasure b m))
    ∂(boxMeasure b d')

/-- The constant-`ξ` state integral `∫_v v^{h'} Z^a_{k,h}(N v^{k'}) dv`. -/
noncomputable def constStateIntegral (β a b N : ℝ) {m d' : ℕ} (k h : Fin m → ℕ)
    (k' h' : Fin d' → ℕ) : ℝ :=
  ∫ v : Fin d' → ℝ, (∏ i, v i ^ h' i) * boxIntegralFin β a b (N * ∏ i, v i ^ k' i) k h
    ∂(boxMeasure b d')

/-- The product-form integrand of the block state integral. -/
noncomputable def blockIntegrand (β N : ℝ) {m d' : ℕ} (k h : Fin m → ℕ) (k' h' : Fin d' → ℕ)
    (ξ η : (Fin m → ℝ) → (Fin d' → ℝ) → ℝ) (z : (Fin d' → ℝ) × (Fin m → ℝ)) : ℝ :=
  (∏ i, z.1 i ^ h' i) * ((∏ i, z.2 i ^ h i) * η z.2 z.1
    * quadKernel β (ξ z.2 z.1) (N * (∏ i, z.1 i ^ k' i) * ∏ i, z.2 i ^ k i))

theorem blockIntegrand_continuous (β N : ℝ) {m d' : ℕ} (k h : Fin m → ℕ) (k' h' : Fin d' → ℕ)
    (ξ η : (Fin m → ℝ) → (Fin d' → ℝ) → ℝ)
    (hξc : Continuous fun x : (Fin m → ℝ) × (Fin d' → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : (Fin m → ℝ) × (Fin d' → ℝ) => η x.1 x.2) :
    Continuous (blockIntegrand β N k h k' h' ξ η) := by
  unfold blockIntegrand
  have h1 : Continuous fun z : (Fin d' → ℝ) × (Fin m → ℝ) => η z.2 z.1 :=
    hηc.comp (continuous_snd.prodMk continuous_fst)
  have h2 : Continuous fun z : (Fin d' → ℝ) × (Fin m → ℝ) => ξ z.2 z.1 :=
    hξc.comp (continuous_snd.prodMk continuous_fst)
  have h3 : Continuous fun z : (Fin d' → ℝ) × (Fin m → ℝ) =>
      N * (∏ i, z.1 i ^ k' i) * ∏ i, z.2 i ^ k i :=
    (continuous_const.mul ((continuous_prod_pow k').comp continuous_fst)).mul
      ((continuous_prod_pow k).comp continuous_snd)
  refine ((continuous_prod_pow h').comp continuous_fst).mul
    ((((continuous_prod_pow h).comp continuous_snd).mul h1).mul ?_)
  unfold quadKernel
  exact Real.continuous_exp.comp ((continuous_const.mul (h3.pow 2)).add
    ((continuous_const.mul h2).mul h3))

/-- The block state integral in product form. -/
theorem blockStateIntegral_eq_prod (β b N : ℝ) {m d' : ℕ} (k h : Fin m → ℕ) (k' h' : Fin d' → ℕ)
    (ξ η : (Fin m → ℝ) → (Fin d' → ℝ) → ℝ)
    (hξc : Continuous fun x : (Fin m → ℝ) × (Fin d' → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : (Fin m → ℝ) × (Fin d' → ℝ) => η x.1 x.2) :
    blockStateIntegral β b N k h k' h' ξ η
      = ∫ z, blockIntegrand β N k h k' h' ξ η z ∂((boxMeasure b d').prod (boxMeasure b m)) := by
  rw [integral_prod _ (integrable_box_prod_of_continuous b _
    (blockIntegrand_continuous β N k h k' h' ξ η hξc hηc))]
  unfold blockStateIntegral blockIntegrand
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  beta_reduce
  rw [← integral_const_mul]

/-- The constant-`ξ` state integral is the block state integral with `ξ = a`, `η = 1`. -/
theorem constStateIntegral_eq_block (β a b N : ℝ) {m d' : ℕ} (k h : Fin m → ℕ)
    (k' h' : Fin d' → ℕ) :
    constStateIntegral β a b N k h k' h'
      = blockStateIntegral β b N k h k' h' (fun _ _ => a) (fun _ _ => 1) := by
  unfold constStateIntegral blockStateIntegral boxIntegralFin
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [mul_one]

/-- The constant-`ξ` state integral equals the frozen state integral of unit 75 with constant
data (`ℕ`-indexed exponents via `toNatFun`). -/
theorem constStateIntegral_eq_frozen (β a b N : ℝ) {d d' : ℕ} (k h : Fin (d + 1) → ℕ)
    (k' h' : Fin d' → ℕ) :
    constStateIntegral β a b N k h k' h'
      = frozenStateIntegral β b N (toNatFun k 1) (toNatFun h 0) d k' h' (fun _ => a)
          (fun _ => 1) := by
  unfold constStateIntegral frozenStateIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  beta_reduce
  rw [boxIntegralFin_eq_toNatFun, boxIntegral_eq_iterChartGen, mul_one]

/-- **The freezing inequality**: with `|ξ| ≤ L`, `|η| ≤ M` on the closed box and oscillation
`|η(u,v) − η(0,v)| + |ξ(u,v) − ξ(0,v)| ≤ ω` on the corner `{uᵢ ≤ δ}`,
`|Z(N) − Z₀(N)| ≤ C₂ (ω Z^{β/2,2L}_h(N) + ((2M+2L)/δ) ∑ᵢ Z^{β/2,2L}_{h+eᵢ}(N))` with
`C₂ = max 1 (M e^{β/2})`. -/
theorem blockStateIntegral_sub_le (β b : ℝ) (hβ : 0 < β) (hb : 0 < b) {m d' : ℕ} (k h : Fin m → ℕ)
    (k' h' : Fin d' → ℕ) (ξ η : (Fin m → ℝ) → (Fin d' → ℝ) → ℝ)
    (hξc : Continuous fun x : (Fin m → ℝ) × (Fin d' → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : (Fin m → ℝ) × (Fin d' → ℝ) => η x.1 x.2) (L M : ℝ) (hL : 0 ≤ L)
    (hM : 0 ≤ M)
    (hξL : ∀ u v, (∀ i, 0 ≤ u i ∧ u i ≤ b) → (∀ i, 0 ≤ v i ∧ v i ≤ b) → |ξ u v| ≤ L)
    (hηM : ∀ u v, (∀ i, 0 ≤ u i ∧ u i ≤ b) → (∀ i, 0 ≤ v i ∧ v i ≤ b) → |η u v| ≤ M)
    (ω δ : ℝ) (hω : 0 ≤ ω) (hδ : 0 < δ)
    (hcorner : ∀ u v, (∀ i, 0 < u i ∧ u i ≤ b) → (∀ i, 0 < v i ∧ v i ≤ b) → (∀ i, u i ≤ δ) →
      |η u v - η 0 v| + |ξ u v - ξ 0 v| ≤ ω)
    (N : ℝ) (hN : 0 ≤ N) :
    |blockStateIntegral β b N k h k' h' ξ η
        - blockStateIntegral β b N k h k' h' (fun _ v => ξ 0 v) (fun _ v => η 0 v)|
      ≤ max 1 (M * Real.exp (β / 2)) * (ω * constStateIntegral (β / 2) (2 * L) b N k h k' h'
          + (2 * M + 2 * L) / δ
            * ∑ i, constStateIntegral (β / 2) (2 * L) b N k (shiftExp h i) k' h') := by
  set μ := (boxMeasure b d').prod (boxMeasure b m) with hμ
  set C₂ : ℝ := max 1 (M * Real.exp (β / 2)) with hC₂
  have hC₂0 : 0 ≤ C₂ := le_trans zero_le_one (le_max_left _ _)
  have hMe : M * Real.exp (β / 2) ≤ C₂ := le_max_right _ _
  have h1C : 1 ≤ C₂ := le_max_left _ _
  set Dmax : ℝ := 2 * M + 2 * L with hDmax
  have hDmax0 : 0 ≤ Dmax := by positivity
  -- continuity of the frozen data
  have hξ0c : Continuous fun x : (Fin m → ℝ) × (Fin d' → ℝ) => ξ 0 x.2 :=
    hξc.comp (continuous_const.prodMk continuous_snd)
  have hη0c : Continuous fun x : (Fin m → ℝ) × (Fin d' → ℝ) => η 0 x.2 :=
    hηc.comp (continuous_const.prodMk continuous_snd)
  -- product forms
  set G := blockIntegrand β N k h k' h' ξ η with hG
  set G₀ := blockIntegrand β N k h k' h' (fun _ v => ξ 0 v) (fun _ v => η 0 v) with hG₀
  set W₀ := blockIntegrand (β / 2) N k h k' h' (fun _ _ => 2 * L) (fun _ _ => 1) with hW₀
  have hGc := blockIntegrand_continuous β N k h k' h' ξ η hξc hηc
  have hG₀c := blockIntegrand_continuous β N k h k' h' (fun _ v => ξ 0 v) (fun _ v => η 0 v)
    hξ0c hη0c
  have hW₀c := blockIntegrand_continuous (β / 2) N k h k' h' (fun _ _ => 2 * L) (fun _ _ => 1)
    continuous_const continuous_const
  have hWic : ∀ i : Fin m, Continuous
      (blockIntegrand (β / 2) N k (shiftExp h i) k' h' (fun _ _ => 2 * L) (fun _ _ => 1)) :=
    fun i => blockIntegrand_continuous (β / 2) N k (shiftExp h i) k' h' (fun _ _ => 2 * L)
      (fun _ _ => 1) continuous_const continuous_const
  have hGi := integrable_box_prod_of_continuous b _ hGc
  have hG₀i := integrable_box_prod_of_continuous b _ hG₀c
  have hW₀i := integrable_box_prod_of_continuous b _ hW₀c
  have hWii : ∀ i, Integrable
      (blockIntegrand (β / 2) N k (shiftExp h i) k' h' (fun _ _ => 2 * L) (fun _ _ => 1)) μ :=
    fun i => integrable_box_prod_of_continuous b _ (hWic i)
  -- the dominating function
  set Hb : (Fin d' → ℝ) × (Fin m → ℝ) → ℝ := fun z => C₂ * (ω * W₀ z + Dmax / δ
    * ∑ i, blockIntegrand (β / 2) N k (shiftExp h i) k' h' (fun _ _ => 2 * L) (fun _ _ => 1) z)
    with hHb
  have hHbi : Integrable Hb μ :=
    ((hW₀i.const_mul ω).add ((integrable_finsetSum _ fun i _ => hWii i).const_mul _)).const_mul _
  -- pointwise bound on the open product box
  have hpt : ∀ᵐ z ∂μ, ‖G z - G₀ z‖ ≤ Hb z := by
    filter_upwards [ae_mem_box_prod b] with z hz
    obtain ⟨hv, hu⟩ := hz
    set v := z.1 with hv_def
    set u := z.2 with hu_def
    have hu0 : ∀ i, 0 ≤ u i ∧ u i ≤ b := fun i => ⟨(hu i).1.le, (hu i).2⟩
    have hv0 : ∀ i, 0 ≤ v i ∧ v i ≤ b := fun i => ⟨(hv i).1.le, (hv i).2⟩
    have hz0 : ∀ i, (0 : ℝ) ≤ (0 : Fin m → ℝ) i ∧ (0 : Fin m → ℝ) i ≤ b := by
      intro i; simp only [Pi.zero_apply]; exact ⟨le_rfl, hb.le⟩
    have hξu : |ξ u v| ≤ L := hξL u v hu0 hv0
    have hξ0 : |ξ 0 v| ≤ L := hξL 0 v hz0 hv0
    have hηu : |η u v| ≤ M := hηM u v hu0 hv0
    have hη0 : |η 0 v| ≤ M := hηM 0 v hz0 hv0
    set s : ℝ := N * (∏ i, v i ^ k' i) * ∏ i, u i ^ k i with hs
    have hs0 : 0 ≤ s := by
      have h1 : 0 ≤ ∏ i, v i ^ k' i := Finset.prod_nonneg fun i _ => pow_nonneg (hv i).1.le _
      have h2 : 0 ≤ ∏ i, u i ^ k i := Finset.prod_nonneg fun i _ => pow_nonneg (hu i).1.le _
      positivity
    have hvh : 0 ≤ ∏ i, v i ^ h' i := Finset.prod_nonneg fun i _ => pow_nonneg (hv i).1.le _
    have huh : 0 ≤ ∏ i, u i ^ h i := Finset.prod_nonneg fun i _ => pow_nonneg (hu i).1.le _
    -- the oscillation bound
    set D : ℝ := |η u v - η 0 v| + |ξ u v - ξ 0 v| with hD
    have hDle : D ≤ ω + Dmax / δ * ∑ i, u i := by
      refine corner_strip_le u (fun i => (hu i).1) D ω δ Dmax hδ hω hDmax0
        (fun hall => hcorner u v hu hv hall) ?_
      rw [hD, hDmax]
      have h1 := abs_sub _ _ |>.trans (add_le_add hηu hη0)
      have h2 := abs_sub _ _ |>.trans (add_le_add hξu hξ0)
      linarith
    -- the mean-value bound
    have hmv := weighted_quadKernel_sub_le β L M (ξ u v) (ξ 0 v) (η u v) (η 0 v) s hβ hs0 hξu hξ0
      hη0
    have hmv' : |η u v * quadKernel β (ξ u v) s - η 0 v * quadKernel β (ξ 0 v) s|
        ≤ C₂ * D * quadKernel (β / 2) (2 * L) s := by
      refine hmv.trans (mul_le_mul_of_nonneg_right ?_ (quadKernel_pos _ _ _).le)
      rw [hD]
      nlinarith [abs_nonneg (η u v - η 0 v), abs_nonneg (ξ u v - ξ 0 v)]
    have hq0 : 0 ≤ quadKernel (β / 2) (2 * L) s := (quadKernel_pos _ _ _).le
    -- assemble
    have hGsub : G z - G₀ z = (∏ i, v i ^ h' i) * (∏ i, u i ^ h i)
        * (η u v * quadKernel β (ξ u v) s - η 0 v * quadKernel β (ξ 0 v) s) := by
      simp only [hG, hG₀, blockIntegrand]; ring
    have hW₀z : W₀ z = (∏ i, v i ^ h' i) * (∏ i, u i ^ h i) * quadKernel (β / 2) (2 * L) s := by
      simp only [hW₀, blockIntegrand]; ring
    have hWiz : ∀ i, blockIntegrand (β / 2) N k (shiftExp h i) k' h' (fun _ _ => 2 * L)
        (fun _ _ => 1) z
          = (∏ i, v i ^ h' i) * (∏ i, u i ^ h i) * quadKernel (β / 2) (2 * L) s * u i := by
      intro i
      simp only [blockIntegrand, prod_shiftExp]; ring
    rw [Real.norm_eq_abs, hGsub, abs_mul, abs_mul, abs_of_nonneg hvh, abs_of_nonneg huh]
    simp only [hHb, hW₀z, hWiz, ← Finset.mul_sum]
    have hP : 0 ≤ (∏ i, v i ^ h' i) * (∏ i, u i ^ h i) := mul_nonneg hvh huh
    calc (∏ i, v i ^ h' i) * (∏ i, u i ^ h i)
          * |η u v * quadKernel β (ξ u v) s - η 0 v * quadKernel β (ξ 0 v) s|
        ≤ (∏ i, v i ^ h' i) * (∏ i, u i ^ h i) * (C₂ * D * quadKernel (β / 2) (2 * L) s) :=
          mul_le_mul_of_nonneg_left hmv' hP
      _ ≤ (∏ i, v i ^ h' i) * (∏ i, u i ^ h i)
          * (C₂ * (ω + Dmax / δ * ∑ i, u i) * quadKernel (β / 2) (2 * L) s) := by
          gcongr
      _ = _ := by ring
  -- integrate
  have hsub : blockStateIntegral β b N k h k' h' ξ η
      - blockStateIntegral β b N k h k' h' (fun _ v => ξ 0 v) (fun _ v => η 0 v)
      = ∫ z, (G z - G₀ z) ∂μ := by
    rw [blockStateIntegral_eq_prod β b N k h k' h' ξ η hξc hηc,
      blockStateIntegral_eq_prod β b N k h k' h' (fun _ v => ξ 0 v) (fun _ v => η 0 v) hξ0c hη0c,
      integral_sub hGi hG₀i]
  have hHb_int : ∫ z, Hb z ∂μ = C₂ * (ω * constStateIntegral (β / 2) (2 * L) b N k h k' h'
      + Dmax / δ * ∑ i, constStateIntegral (β / 2) (2 * L) b N k (shiftExp h i) k' h') := by
    simp only [hHb]
    rw [integral_const_mul, integral_add (hW₀i.const_mul ω)
      ((integrable_finsetSum _ fun i _ => hWii i).const_mul _), integral_const_mul,
      integral_const_mul, integral_finsetSum _ fun i _ => hWii i]
    congr 2
    · rw [constStateIntegral_eq_block, blockStateIntegral_eq_prod _ _ _ _ _ _ _ _ _
        continuous_const continuous_const]
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [constStateIntegral_eq_block, blockStateIntegral_eq_prod _ _ _ _ _ _ _ _ _
        continuous_const continuous_const]
  rw [hsub, ← hHb_int, ← Real.norm_eq_abs]
  calc ‖∫ z, (G z - G₀ z) ∂μ‖ ≤ ∫ z, ‖G z - G₀ z‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, Hb z ∂μ := integral_mono_ae (hGi.sub hG₀i).norm hHbi hpt

end Laplace.Grammar
