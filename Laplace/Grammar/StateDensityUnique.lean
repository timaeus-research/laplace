/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.OneDScale
import Mathlib.MeasureTheory.Integral.Pi

/-!
# State density II: the leading coefficient for a unique minimal coordinate (grammar §4.2)

Coordinates are split as `(u, v)` with `u ∈ (0,b]` the unique coordinate attaining the minimal
candidate exponent `p = (h₀+1)/k₀` and `v ∈ (0,b]^d` the noncritical ones,
`q_i = (h'_i+1)/k'_i > p`.
For `ξ, η` jointly continuous and Lipschitz at `u = 0` uniformly in `v`,

  `n^{p/2} · ∫_v v^{h'} ∫_u u^{h₀} η(u,v) e^{-βn(u^{k₀}v^{k'})² + β√n u^{k₀}v^{k'} ξ(u,v)} du dv`
  `  → (1/k₀) ∫_v v^{h'} (v^{k'})^{-p} A_{p-1}(ξ(0,v)) η(0,v) dv`

(`stateIntegral_tendsto`): the leading coefficient is the fluctuation mass `A_{p-1}(ξ(0,v))`
weighted by `η(0,v)`, integrated along the exceptional divisor `{u = 0}` against the density
`v^{h' - k'p}`, which is integrable exactly because the other exponents are strictly larger. Proof:
for each `v` the inner integral is the one-dimensional integral at scale `c = √n v^{k'}` (unit 69),
and dominated convergence in `v` with the uniform bound of unit 69. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- The iterated standard integral: outer over the noncritical coordinates, inner over the minimal
coordinate `u`. -/
noncomputable def stateIntegral (β b n : ℝ) (h₀ k₀ : ℕ) {d : ℕ} (k' h' : Fin d → ℕ)
    (ξ η : ℝ → (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ v : Fin d → ℝ, ((∏ i, v i ^ h' i) * ∫ u in Ioc (0 : ℝ) b, u ^ h₀ * η u v
      * Real.exp (-β * n * (u ^ k₀ * ∏ i, v i ^ k' i) ^ 2
        + β * Real.sqrt n * (u ^ k₀ * ∏ i, v i ^ k' i) * ξ u v)) ∂(boxMeasure b d)

/-- The divisor density: the limit integrand
`v^{h'} (v^{k'})^{-p} (1/k₀) A_{p-1}(ξ(0,v)) η(0,v)`. -/
noncomputable def divisorDensity (β : ℝ) (h₀ k₀ : ℕ) {d : ℕ} (k' h' : Fin d → ℕ)
    (ξ η : ℝ → (Fin d → ℝ) → ℝ) (v : Fin d → ℝ) : ℝ :=
  (∏ i, v i ^ h' i) * (∏ i, v i ^ k' i) ^ (-(((h₀ : ℝ) + 1) / k₀))
    * (1 / (k₀ : ℝ) * weightedMass β (ξ 0 v) (((h₀ : ℝ) + 1) / k₀ - 1) * η 0 v)

/-- The inner integral at `(n, v)` is the one-dimensional integral at scale `√n v^{k'}`. -/
theorem stateIntegral_inner_eq (β b n : ℝ) (h₀ k₀ : ℕ) {d : ℕ} (k' : Fin d → ℕ)
    (ξ η : ℝ → (Fin d → ℝ) → ℝ) (v : Fin d → ℝ) (hn : 0 ≤ n) :
    (∫ u in Ioc (0 : ℝ) b, u ^ h₀ * η u v
        * Real.exp (-β * n * (u ^ k₀ * ∏ i, v i ^ k' i) ^ 2
          + β * Real.sqrt n * (u ^ k₀ * ∏ i, v i ^ k' i) * ξ u v))
      = oneDScale β b (Real.sqrt n * ∏ i, v i ^ k' i) h₀ k₀ (fun u => ξ u v) (fun u => η u v) := by
  unfold oneDScale
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  have : (Real.sqrt n * ∏ i, v i ^ k' i) ^ 2 = n * (∏ i, v i ^ k' i) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hn]
  congr 2
  beta_reduce
  rw [show (Real.sqrt n * (∏ i, v i ^ k' i) * u ^ k₀) ^ 2
    = Real.sqrt n ^ 2 * (u ^ k₀ * ∏ i, v i ^ k' i) ^ 2 by ring, Real.sq_sqrt hn]
  ring

/-- **The leading coefficient for a unique minimal coordinate.** -/
theorem stateIntegral_tendsto (β b : ℝ) (hβ : 0 < β) (hb : 0 < b) (h₀ k₀ : ℕ) (hk₀ : 0 < k₀)
    {d : ℕ} (k' h' : Fin d → ℕ) (hk' : ∀ i, 0 < k' i)
    (hq : ∀ i, ((h₀ : ℝ) + 1) / k₀ < ((h' i : ℝ) + 1) / k' i)
    (ξ η : ℝ → (Fin d → ℝ) → ℝ)
    (hξc : Continuous fun x : ℝ × (Fin d → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : ℝ × (Fin d → ℝ) => η x.1 x.2) (C C' : ℝ) (hC : 0 ≤ C)
    (hξ : ∀ u ∈ Ioc (0 : ℝ) b, ∀ v : Fin d → ℝ, |ξ u v - ξ 0 v| ≤ C * u)
    (hη : ∀ u ∈ Ioc (0 : ℝ) b, ∀ v : Fin d → ℝ, |η u v - η 0 v| ≤ C' * u) :
    Tendsto (fun n : ℝ => n ^ (((h₀ : ℝ) + 1) / k₀ / 2) * stateIntegral β b n h₀ k₀ k' h' ξ η)
      atTop (𝓝 (∫ v, divisorDensity β h₀ k₀ k' h' ξ η v ∂(boxMeasure b d))) := by
  have hk₀' : (0 : ℝ) < k₀ := Nat.cast_pos.2 hk₀
  set p : ℝ := ((h₀ : ℝ) + 1) / k₀ with hp
  have hp0 : 0 < p := by positivity
  -- bounds for ξ, η on the closed box
  have hcpt : IsCompact (Icc (0 : ℝ) b ×ˢ Set.pi univ fun _ : Fin d => Icc (0 : ℝ) b) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨L₀, hL₀⟩ := hcpt.exists_bound_of_continuousOn hξc.continuousOn
  obtain ⟨M₀, hM₀⟩ := hcpt.exists_bound_of_continuousOn hηc.continuousOn
  set L : ℝ := max L₀ 0 with hLdef
  set M : ℝ := max M₀ 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hbox : ∀ v : Fin d → ℝ, v ∈ (Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) b) →
      ∀ u ∈ Ioc (0 : ℝ) b, |ξ u v| ≤ L ∧ |η u v| ≤ M := by
    intro v hv u hu
    have hmem : (u, v) ∈ Icc (0 : ℝ) b ×ˢ Set.pi univ fun _ : Fin d => Icc (0 : ℝ) b := by
      refine ⟨⟨hu.1.le, hu.2⟩, ?_⟩
      rw [Set.mem_univ_pi] at hv ⊢
      exact fun i => ⟨(hv i).1.le, (hv i).2⟩
    constructor
    · have := hL₀ (u, v) hmem; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
    · have := hM₀ (u, v) hmem; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  -- the uniform constant
  set K : ℝ := M * Real.exp (β * L ^ 2 / 2) * (1 / (k₀ : ℝ)) * weightedMass (β / 2) 0 (p - 1)
    with hK
  have hK0 : 0 ≤ K := by
    have := weightedMass_pos (β / 2) 0 (p - 1) (by positivity) (by linarith)
    positivity
  -- F n v and the bound
  set F : ℝ → (Fin d → ℝ) → ℝ := fun n v => n ^ (p / 2) * ((∏ i, v i ^ h' i)
    * ∫ u in Ioc (0 : ℝ) b, u ^ h₀ * η u v
      * Real.exp (-β * n * (u ^ k₀ * ∏ i, v i ^ k' i) ^ 2
        + β * Real.sqrt n * (u ^ k₀ * ∏ i, v i ^ k' i) * ξ u v)) with hF
  set bound : (Fin d → ℝ) → ℝ := fun v => K * ∏ i, (v i ^ h' i * (v i ^ k' i) ^ (-p)) with hbound
  have hmem : ∀ᵐ v ∂(boxMeasure b d), v ∈ Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) b := by
    rw [boxMeasure_eq_restrict]
    exact ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
  -- product factorisation of the density prefactor
  have hprod : ∀ v : Fin d → ℝ, (∀ i, 0 < v i) →
      (∏ i, v i ^ h' i) * (∏ i, v i ^ k' i) ^ (-p) = ∏ i, (v i ^ h' i * (v i ^ k' i) ^ (-p)) := by
    intro v hv
    rw [Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ fun i _ => pow_nonneg (hv i).le _]
  -- measurability of F n
  have hF_meas : ∀ n : ℝ, AEStronglyMeasurable (F n) (boxMeasure b d) := by
    intro n
    have hG : Continuous fun x : (Fin d → ℝ) × ℝ => x.2 ^ h₀ * η x.2 x.1
        * Real.exp (-β * n * (x.2 ^ k₀ * ∏ i, x.1 i ^ k' i) ^ 2
          + β * Real.sqrt n * (x.2 ^ k₀ * ∏ i, x.1 i ^ k' i) * ξ x.2 x.1) := by
      have h1 : Continuous fun x : (Fin d → ℝ) × ℝ => η x.2 x.1 :=
        hηc.comp (continuous_snd.prodMk continuous_fst)
      have h2 : Continuous fun x : (Fin d → ℝ) × ℝ => ξ x.2 x.1 :=
        hξc.comp (continuous_snd.prodMk continuous_fst)
      have h3 : Continuous fun x : (Fin d → ℝ) × ℝ => x.2 ^ k₀ * ∏ i, x.1 i ^ k' i :=
        (continuous_snd.pow _).mul ((continuous_prod_pow k').comp continuous_fst)
      exact ((continuous_snd.pow _).mul h1).mul (Real.continuous_exp.comp
        ((continuous_const.mul (h3.pow 2)).add ((continuous_const.mul h3).mul h2)))
    have hinner : StronglyMeasurable fun v : Fin d → ℝ => ∫ u in Ioc (0 : ℝ) b, u ^ h₀ * η u v
        * Real.exp (-β * n * (u ^ k₀ * ∏ i, v i ^ k' i) ^ 2
          + β * Real.sqrt n * (u ^ k₀ * ∏ i, v i ^ k' i) * ξ u v) :=
      hG.stronglyMeasurable.integral_prod_right'
    exact (continuous_const.stronglyMeasurable.mul
      ((continuous_prod_pow h').stronglyMeasurable.mul hinner)).aestronglyMeasurable
  -- the bound
  have h_bound : ∀ᶠ n in atTop, ∀ᵐ v ∂(boxMeasure b d), ‖F n v‖ ≤ bound v := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    filter_upwards [hmem] with v hv
    have hv' : ∀ i, 0 < v i := by rw [Set.mem_univ_pi] at hv; exact fun i => (hv i).1
    have hV : 0 < ∏ i, v i ^ k' i := Finset.prod_pos fun i _ => pow_pos (hv' i) _
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
    set c : ℝ := Real.sqrt n * ∏ i, v i ^ k' i with hc
    have hc0 : 0 < c := by positivity
    have hone := oneDScale_abs_le β b c L M h₀ k₀ (fun u => ξ u v) (fun u => η u v) hβ hb hk₀ hc0 hM
      (fun u hu => (hbox v hv u hu).1) (fun u hu => (hbox v hv u hu).2)
    rw [← hp] at hone
    have hnpow : n ^ (p / 2) = c ^ p * (∏ i, v i ^ k' i) ^ (-p) := by
      rw [hc, Real.mul_rpow hsn.le hV.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le,
        Real.rpow_neg hV.le, mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hV p).ne', mul_one]
      congr 1; ring
    have hprodh : 0 ≤ ∏ i, v i ^ h' i := Finset.prod_nonneg fun i _ => pow_nonneg (hv' i).le _
    simp only [hF, hbound]
    rw [stateIntegral_inner_eq β b n h₀ k₀ k' ξ η v hn.le, ← hc, Real.norm_eq_abs, hnpow,
      ← hprod v hv']
    rw [show c ^ p * (∏ i, v i ^ k' i) ^ (-p) * ((∏ i, v i ^ h' i)
        * oneDScale β b c h₀ k₀ (fun u => ξ u v) (fun u => η u v))
      = (∏ i, v i ^ h' i) * (∏ i, v i ^ k' i) ^ (-p)
        * (c ^ p * oneDScale β b c h₀ k₀ (fun u => ξ u v) (fun u => η u v)) by ring,
      abs_mul, abs_mul, abs_mul, abs_of_nonneg hprodh, abs_of_pos (Real.rpow_pos_of_pos hV _),
      abs_of_pos (Real.rpow_pos_of_pos hc0 _)]
    calc (∏ i, v i ^ h' i) * (∏ i, v i ^ k' i) ^ (-p)
          * (c ^ p * |oneDScale β b c h₀ k₀ (fun u => ξ u v) (fun u => η u v)|)
        ≤ (∏ i, v i ^ h' i) * (∏ i, v i ^ k' i) ^ (-p) * K := by
          gcongr
      _ = K * ((∏ i, v i ^ h' i) * (∏ i, v i ^ k' i) ^ (-p)) := by ring
  -- integrability of the bound: a product of single-coordinate integrable functions
  have hbound_int : Integrable bound (boxMeasure b d) := by
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
      ring
    have := (Integrable.fintype_prod (μ := fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc 0 b))
      (f := fun i t => t ^ h' i * (t ^ k' i) ^ (-p)) hfac).const_mul K
    exact this
  -- pointwise limit
  have h_lim : ∀ᵐ v ∂(boxMeasure b d), Tendsto (fun n => F n v) atTop
      (𝓝 (divisorDensity β h₀ k₀ k' h' ξ η v)) := by
    filter_upwards [hmem] with v hv
    have hv' : ∀ i, 0 < v i := by rw [Set.mem_univ_pi] at hv; exact fun i => (hv i).1
    have hV : 0 < ∏ i, v i ^ k' i := Finset.prod_pos fun i _ => pow_pos (hv' i) _
    have hξv : Continuous fun u => ξ u v := hξc.comp (continuous_id.prodMk continuous_const)
    have hηv : Continuous fun u => η u v := hηc.comp (continuous_id.prodMk continuous_const)
    have hone := oneDScale_tendsto β (ξ 0 v) (η 0 v) b C C' (fun u => ξ u v) (fun u => η u v) h₀ k₀
      hβ hb hk₀ hC hξv hηv (fun u hu => hξ u hu v) (fun u hu => hη u hu v)
    rw [← hp] at hone
    have hctend : Tendsto (fun n : ℝ => Real.sqrt n * ∏ i, v i ^ k' i) atTop atTop :=
      tendsto_sqrt_atTop.atTop_mul_const hV
    have hcomp := (hone.comp hctend).const_mul ((∏ i, v i ^ h' i) * (∏ i, v i ^ k' i) ^ (-p))
    refine hcomp.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
    have hnpow : n ^ (p / 2) = (Real.sqrt n * ∏ i, v i ^ k' i) ^ p * (∏ i, v i ^ k' i) ^ (-p) := by
      rw [Real.mul_rpow hsn.le hV.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le,
        Real.rpow_neg hV.le, mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hV p).ne', mul_one]
      ring
    simp only [hF, Function.comp]
    rw [stateIntegral_inner_eq β b n h₀ k₀ k' ξ η v hn.le, hnpow]
    ring
  have hmain := tendsto_integral_filter_of_dominated_convergence bound
    (Filter.Eventually.of_forall hF_meas) h_bound hbound_int h_lim
  refine hmain.congr' ?_
  filter_upwards with n
  simp only [hF, stateIntegral]
  rw [← MeasureTheory.integral_const_mul]

end Laplace.Grammar
