/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.BlockScale

/-!
# Minimal block III: the frozen coefficient theorem (grammar §4.2, multiplicity `m = d+1`)

Freeze `ξ, η` on the minimal block: `ξ = a(v)`, `η = e(v)` depend only on the noncritical
coordinates `v ∈ (0,b]^{d'}`, whose exponents `q'_i = (h'_i+1)/k'_i` exceed the common minimal
exponent `p` of the block. The frozen state integral

  `Z₀(N) = ∫_v v^{h'} e(v) Z_{d+1}^{a(v)}(N v^{k'}) dv`

satisfies (`frozenStateIntegral_tendsto`)

  `N^p Z₀(N) / (log N)^d → (∏ k_i⁻¹)(1/d!) ∫_v v^{h'} (v^{k'})^{-p} A_{p-1}(a(v)) e(v) dv`,

by dominated convergence over `v` with the uniform block envelope of unit 74 and the scale limit at
`γ = v^{k'}`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- `log₊` is monotone on positives. -/
theorem logPlus_le_logPlus (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) : logPlus x ≤ logPlus y :=
  max_le_max le_rfl (Real.log_le_log hx hxy)

/-- `iterChartGen ≥ 0`. -/
theorem iterChartGen_nonneg (β a b : ℝ) (k h : ℕ → ℕ) (d : ℕ) (c : ℝ) :
    0 ≤ iterChartGen β a b k h d c := by
  rw [← boxIntegral_eq_iterChartGen, ← boxIntegralFin_eq_boxIntegral]
  exact boxIntegralFin_nonneg β a b c _ _

/-- The frozen state integral: outer integral over the noncritical box, inner equal-exponent block
with frozen `ξ = a(v)`, weight `e(v)`. -/
noncomputable def frozenStateIntegral (β b N : ℝ) (k h : ℕ → ℕ) (d : ℕ) {d' : ℕ}
    (k' h' : Fin d' → ℕ) (a e : (Fin d' → ℝ) → ℝ) : ℝ :=
  ∫ v : Fin d' → ℝ, (∏ i, v i ^ h' i) * e v
    * iterChartGen β (a v) b k h (d + 1) (N * ∏ i, v i ^ k' i) ∂(boxMeasure b d')

/-- The block divisor density
`(∏ k_i⁻¹)(1/d!) v^{h'} (v^{k'})^{-p} A_{p-1}(a(v)) e(v)`. -/
noncomputable def blockDivisorDensity (β p : ℝ) (k : ℕ → ℕ) (d : ℕ) {d' : ℕ} (k' h' : Fin d' → ℕ)
    (a e : (Fin d' → ℝ) → ℝ) (v : Fin d' → ℝ) : ℝ :=
  (∏ i, v i ^ h' i) * e v * ((∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i) * (1 / (d.factorial : ℝ))
    * (∏ i, v i ^ k' i) ^ (-p) * weightedMass β (a v) (p - 1))

/-- The block integral as a box integral, jointly in the parameters. -/
theorem iterChartGen_eq_boxIntegralFin (β a b : ℝ) (k h : ℕ → ℕ) (d : ℕ) (c : ℝ) :
    iterChartGen β a b k h (d + 1) c
      = ∫ u : Fin (d + 1) → ℝ, (∏ i, u i ^ h i) * quadKernel β a (c * ∏ i, u i ^ k i)
          ∂(boxMeasure b (d + 1)) := by
  rw [← boxIntegral_eq_iterChartGen, ← boxIntegralFin_eq_boxIntegral, boxIntegralFin]

/-- **Frozen coefficient theorem**: with all block exponents equal to `p < q'_i`,
`N^p Z₀(N)/(log N)^d → ∫_v blockDivisorDensity`. -/
theorem frozenStateIntegral_tendsto (β b p : ℝ) (hβ : 0 < β) (hb : 0 < b) (k h : ℕ → ℕ)
    (hk : ∀ i, 0 < k i) (d : ℕ) (hp : ∀ i, i ≤ d → ((h i : ℝ) + 1) / k i = p) {d' : ℕ}
    (k' h' : Fin d' → ℕ) (hk' : ∀ i, 0 < k' i) (hq : ∀ i, p < ((h' i : ℝ) + 1) / k' i)
    (a e : (Fin d' → ℝ) → ℝ) (hac : Continuous a) (hec : Continuous e) :
    Tendsto (fun N : ℝ => N ^ p / Real.log N ^ d * frozenStateIntegral β b N k h d k' h' a e)
      atTop (𝓝 (∫ v, blockDivisorDensity β p k d k' h' a e v ∂(boxMeasure b d'))) := by
  have hp0 : 0 < p := by
    rw [← hp 0 (Nat.zero_le d)]; exact chartExp_pos k h hk 0
  set B : ℝ := b ^ (∑ i ∈ Finset.range (d + 1), k i) with hB
  have hBpos : 0 < B := by positivity
  set B' : ℝ := b ^ (∑ i, k' i) with hB'
  have hB'pos : 0 < B' := by positivity
  -- bounds for a, e on the closed box
  have hcpt : IsCompact (Set.pi univ fun _ : Fin d' => Icc (0 : ℝ) b) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨L₀, hL₀⟩ := hcpt.exists_bound_of_continuousOn hac.continuousOn
  obtain ⟨M₀, hM₀⟩ := hcpt.exists_bound_of_continuousOn hec.continuousOn
  set L : ℝ := max L₀ 0 with hLdef
  set M : ℝ := max M₀ 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hbox : ∀ v : Fin d' → ℝ, v ∈ (Set.pi univ fun _ : Fin d' => Ioc (0 : ℝ) b) →
      |a v| ≤ L ∧ |e v| ≤ M := by
    intro v hv
    have hmem : v ∈ Set.pi univ fun _ : Fin d' => Icc (0 : ℝ) b := by
      rw [Set.mem_univ_pi] at hv ⊢
      exact fun i => ⟨(hv i).1.le, (hv i).2⟩
    constructor
    · have := hL₀ v hmem; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
    · have := hM₀ v hmem; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  -- the scale `v^{k'}` is bounded by `B'` on the box
  have hscale : ∀ v : Fin d' → ℝ, v ∈ (Set.pi univ fun _ : Fin d' => Ioc (0 : ℝ) b) →
      ∏ i, v i ^ k' i ≤ B' := by
    intro v hv
    rw [Set.mem_univ_pi] at hv
    rw [hB', ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun i _ => pow_nonneg (hv i).1.le _)
      fun i _ => pow_le_pow_left₀ (hv i).1.le (hv i).2 _
  -- the uniform constant
  set P : ℝ := (∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i) * (1 / (d.factorial : ℝ)) with hP
  have hP0 : 0 ≤ P := by positivity
  set K : ℝ := M * P * blockEnv β L p d * (2 + logPlus (B' * B)) ^ d with hK
  have hK0 : 0 ≤ K :=
    mul_nonneg (mul_nonneg (mul_nonneg hM hP0) (blockEnv_nonneg β L p d))
      (pow_nonneg (by linarith [logPlus_nonneg (B' * B)]) _)
  -- F N v and the bound
  set F : ℝ → (Fin d' → ℝ) → ℝ := fun N v => N ^ p / Real.log N ^ d * ((∏ i, v i ^ h' i) * e v
    * iterChartGen β (a v) b k h (d + 1) (N * ∏ i, v i ^ k' i)) with hF
  set bound : (Fin d' → ℝ) → ℝ := fun v => K * ∏ i, (v i ^ h' i * (v i ^ k' i) ^ (-p))
    with hbound
  have hmem : ∀ᵐ v ∂(boxMeasure b d'), v ∈ Set.pi univ fun _ : Fin d' => Ioc (0 : ℝ) b := by
    rw [boxMeasure_eq_restrict]
    exact ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
  have hprod : ∀ v : Fin d' → ℝ, (∀ i, 0 < v i) →
      (∏ i, v i ^ h' i) * (∏ i, v i ^ k' i) ^ (-p) = ∏ i, (v i ^ h' i * (v i ^ k' i) ^ (-p)) := by
    intro v hv
    rw [Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ fun i _ => pow_nonneg (hv i).le _]
  -- measurability of F N
  have hF_meas : ∀ N : ℝ, AEStronglyMeasurable (F N) (boxMeasure b d') := by
    intro N
    have hG : Continuous fun x : (Fin d' → ℝ) × (Fin (d + 1) → ℝ) =>
        (∏ i, x.2 i ^ h i) * quadKernel β (a x.1) ((N * ∏ i, x.1 i ^ k' i) * ∏ i, x.2 i ^ k i) := by
      have h1 : Continuous fun x : (Fin d' → ℝ) × (Fin (d + 1) → ℝ) => a x.1 :=
        hac.comp continuous_fst
      have h2 : Continuous fun x : (Fin d' → ℝ) × (Fin (d + 1) → ℝ) =>
          (N * ∏ i, x.1 i ^ k' i) * ∏ i, x.2 i ^ k i :=
        (continuous_const.mul ((continuous_prod_pow k').comp continuous_fst)).mul
          ((continuous_prod_pow fun i : Fin (d + 1) => k i).comp continuous_snd)
      refine ((continuous_prod_pow fun i : Fin (d + 1) => h i).comp continuous_snd).mul ?_
      unfold quadKernel
      exact Real.continuous_exp.comp ((continuous_const.mul (h2.pow 2)).add
        ((continuous_const.mul h1).mul h2))
    have hinner : StronglyMeasurable fun v : Fin d' → ℝ =>
        iterChartGen β (a v) b k h (d + 1) (N * ∏ i, v i ^ k' i) := by
      have heq : (fun v : Fin d' → ℝ => iterChartGen β (a v) b k h (d + 1) (N * ∏ i, v i ^ k' i))
          = fun v => ∫ u : Fin (d + 1) → ℝ, (∏ i, u i ^ h i)
              * quadKernel β (a v) ((N * ∏ i, v i ^ k' i) * ∏ i, u i ^ k i)
              ∂(boxMeasure b (d + 1)) :=
        funext fun v => iterChartGen_eq_boxIntegralFin β (a v) b k h d _
      rw [heq]
      exact hG.stronglyMeasurable.integral_prod_right' (ν := boxMeasure b (d + 1))
    exact (continuous_const.stronglyMeasurable.mul
      (((continuous_prod_pow h').mul hec).stronglyMeasurable.mul hinner)).aestronglyMeasurable
  -- the bound
  have h_bound : ∀ᶠ N in atTop, ∀ᵐ v ∂(boxMeasure b d'), ‖F N v‖ ≤ bound v := by
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
    have hNpos : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hN
    have hlogN : 1 ≤ Real.log N := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hN
    have hlogN0 : 0 < Real.log N := by linarith
    filter_upwards [hmem] with v hv
    have hv' : ∀ i, 0 < v i := by rw [Set.mem_univ_pi] at hv; exact fun i => (hv i).1
    have hV : 0 < ∏ i, v i ^ k' i := Finset.prod_pos fun i _ => pow_pos (hv' i) _
    set c : ℝ := N * ∏ i, v i ^ k' i with hc
    have hc0 : 0 < c := by positivity
    have henv := iterChartGen_block_le β b L p k h hβ hb hk d hp (a v) (hbox v hv).1 c hc0
    rw [← hB] at henv
    -- log₊(cB) ≤ log N + log₊(B'B)
    have hlogcB : logPlus (c * B) ≤ Real.log N + logPlus (B' * B) := by
      calc logPlus (c * B) = logPlus (N * ((∏ i, v i ^ k' i) * B)) := by rw [hc, mul_assoc]
        _ ≤ logPlus N + logPlus ((∏ i, v i ^ k' i) * B) :=
            logPlus_mul_le _ _ hNpos (by positivity)
        _ ≤ Real.log N + logPlus (B' * B) := by
            rw [logPlus_eq_log N (by linarith [Real.add_one_le_exp (1 : ℝ)])]
            gcongr
            exact logPlus_le_logPlus _ _ (by positivity)
              (mul_le_mul_of_nonneg_right (hscale v hv) hBpos.le)
    have hratio : (1 + logPlus (c * B)) ^ d ≤ (2 + logPlus (B' * B)) ^ d * Real.log N ^ d := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by linarith [logPlus_nonneg (c * B)]) ?_ d
      have := logPlus_nonneg (B' * B)
      nlinarith
    -- assemble
    have hZ0 := iterChartGen_nonneg β (a v) b k h (d + 1) c
    have hZ : iterChartGen β (a v) b k h (d + 1) c
        ≤ P * blockEnv β L p d * (2 + logPlus (B' * B)) ^ d * Real.log N ^ d * c ^ (-p) := by
      have hcp : 0 < c ^ p := Real.rpow_pos_of_pos hc0 p
      have hE := blockEnv_nonneg β L p d
      have h1 : c ^ p * iterChartGen β (a v) b k h (d + 1) c
          ≤ P * blockEnv β L p d * ((2 + logPlus (B' * B)) ^ d * Real.log N ^ d) := by
        calc c ^ p * iterChartGen β (a v) b k h (d + 1) c
            ≤ (∏ i ∈ Finset.range (d + 1), (1 : ℝ) / k i) * (1 / (d.factorial : ℝ))
              * blockEnv β L p d * (1 + logPlus (c * B)) ^ d := henv
          _ = P * blockEnv β L p d * (1 + logPlus (c * B)) ^ d := by rw [hP]
          _ ≤ P * blockEnv β L p d * ((2 + logPlus (B' * B)) ^ d * Real.log N ^ d) :=
              mul_le_mul_of_nonneg_left hratio (mul_nonneg hP0 hE)
      have hcinv : c ^ (-p) = (c ^ p)⁻¹ := Real.rpow_neg hc0.le p
      rw [hcinv, ← div_eq_mul_inv, le_div_iff₀ hcp]
      linarith [h1]
    have hnpow : N ^ p * c ^ (-p) = (∏ i, v i ^ k' i) ^ (-p) := by
      rw [hc, Real.mul_rpow hNpos.le hV.le, Real.rpow_neg hNpos.le, ← mul_assoc,
        mul_inv_cancel₀ (Real.rpow_pos_of_pos hNpos p).ne', one_mul]
    have hprodh : 0 ≤ ∏ i, v i ^ h' i := Finset.prod_nonneg fun i _ => pow_nonneg (hv' i).le _
    have hev : |e v| ≤ M := (hbox v hv).2
    simp only [hF, hbound]
    rw [← hc, Real.norm_eq_abs, ← hprod v hv']
    have hNp : 0 < N ^ p := Real.rpow_pos_of_pos hNpos p
    have hlogd : 0 < Real.log N ^ d := pow_pos hlogN0 d
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (div_pos hNp hlogd), abs_of_nonneg hprodh,
      abs_of_nonneg hZ0]
    calc N ^ p / Real.log N ^ d * ((∏ i, v i ^ h' i) * |e v| * iterChartGen β (a v) b k h (d + 1) c)
        ≤ N ^ p / Real.log N ^ d * ((∏ i, v i ^ h' i) * M
            * (P * blockEnv β L p d * (2 + logPlus (B' * B)) ^ d * Real.log N ^ d * c ^ (-p))) := by
          refine mul_le_mul_of_nonneg_left ?_ (div_pos hNp hlogd).le
          exact mul_le_mul (mul_le_mul_of_nonneg_left hev hprodh) hZ hZ0 (mul_nonneg hprodh hM)
      _ = K * ((∏ i, v i ^ h' i) * (N ^ p * c ^ (-p))) := by
          rw [hK]; field_simp
      _ = K * ((∏ i, v i ^ h' i) * (∏ i, v i ^ k' i) ^ (-p)) := by rw [hnpow]
  -- integrability of the bound
  have hbound_int : Integrable bound (boxMeasure b d') :=
    (divisorWeight_integrable b k' h' hk' p hq).const_mul K
  -- pointwise limit
  have h_lim : ∀ᵐ v ∂(boxMeasure b d'), Tendsto (fun N => F N v) atTop
      (𝓝 (blockDivisorDensity β p k d k' h' a e v)) := by
    filter_upwards [hmem] with v hv
    have hv' : ∀ i, 0 < v i := by rw [Set.mem_univ_pi] at hv; exact fun i => (hv i).1
    have hV : 0 < ∏ i, v i ^ k' i := Finset.prod_pos fun i _ => pow_pos (hv' i) _
    have hone := Tendsto.const_mul ((∏ i, v i ^ h' i) * e v)
      (iterChartGen_block_tendsto β (a v) b p (∏ i, v i ^ k' i) k h hβ hb hk d hp hV)
    refine hone.congr' (Filter.Eventually.of_forall fun N => ?_)
    simp only [hF]
    ring
  have hmain := tendsto_integral_filter_of_dominated_convergence bound
    (Filter.Eventually.of_forall hF_meas) h_bound hbound_int h_lim
  refine hmain.congr' ?_
  filter_upwards with N
  simp only [hF, frozenStateIntegral]
  rw [← MeasureTheory.integral_const_mul]

end Laplace.Grammar
