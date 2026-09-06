/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.FreeEnergy

/-!
# The exponential tree series in `d` dimensions (grammar §4.2)

The first step of the proof of `thm:TaylorTree` writes `ξ = ξ(0) + J` and expands
`exp(β√n u^k J(u)) = ∑_p (β√n u^k)^p J(u)^p / p!`. For a continuous `J` on the box the series can be
integrated term by term (dominated convergence on the compact box):

  `∫ u^h e^{-βn u^{2k} + β√n u^k (a + J(u))} du
     = ∑_{p ≥ 0} (β^p/p!) ∫ u^h (√n u^k J(u))^p f(√n u^k) du`

as a convergent series (`boxIntegralXi_hasSum`). Each layer `p` is, for polynomial `J`, a finite
combination of the tree terms of unit 60. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- The chart standard integral with `ξ = a + J`. -/
noncomputable def boxIntegralXi (β a b c : ℝ) {d : ℕ} (k h : Fin d → ℕ) (J : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ u : Fin d → ℝ, (∏ i, u i ^ h i)
    * Real.exp (-β * (c * ∏ i, u i ^ k i) ^ 2 + β * (c * ∏ i, u i ^ k i) * (a + J u))
    ∂(boxMeasure b d)

/-- The `p`-th layer of the exponential tree. -/
noncomputable def treeLayer (β a b c : ℝ) {d : ℕ} (k h : Fin d → ℕ) (J : (Fin d → ℝ) → ℝ)
    (p : ℕ) : ℝ :=
  β ^ p / p.factorial * ∫ u : Fin d → ℝ, (∏ i, u i ^ h i) * ((c * ∏ i, u i ^ k i) * J u) ^ p
    * quadKernel β a (c * ∏ i, u i ^ k i) ∂(boxMeasure b d)

theorem continuous_prod_pow {d : ℕ} (e : Fin d → ℕ) :
    Continuous fun u : Fin d → ℝ => ∏ i, u i ^ e i :=
  continuous_finsetProd _ fun i _ => (continuous_apply i).pow _

/-- **The exponential tree series**: for continuous `J`, the standard integral with `ξ = a + J` is
the convergent sum of its tree layers. -/
theorem boxIntegralXi_hasSum (β a b c : ℝ) (hβ : 0 < β) (hb : 0 < b) (hc : 0 ≤ c) {d : ℕ}
    (k h : Fin d → ℕ) (J : (Fin d → ℝ) → ℝ) (hJ : Continuous J) :
    HasSum (treeLayer β a b c k h J) (boxIntegralXi β a b c k h J) := by
  set μ : Measure (Fin d → ℝ) := boxMeasure b d with hμ
  -- the box and a bound for J on its closure
  have hbox : MeasurableSet (Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) b) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  have hmem : ∀ᵐ u ∂μ, u ∈ Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) b := by
    rw [hμ, boxMeasure_eq_restrict]
    exact ae_restrict_mem hbox
  obtain ⟨CJ, hCJ⟩ := (isCompact_univ_pi fun _ : Fin d => isCompact_Icc (a := (0 : ℝ)) (b := b))
    |>.exists_bound_of_continuousOn hJ.continuousOn
  have hCJ0 : 0 ≤ CJ := (norm_nonneg _).trans (hCJ (fun _ => b)
    (by rw [Set.mem_univ_pi]; exact fun _ => ⟨hb.le, le_rfl⟩))
  set Hb : ℝ := ∏ i : Fin d, b ^ h i with hHb
  set Kb : ℝ := c * ∏ i : Fin d, b ^ k i with hKb
  set E : ℝ := Real.exp (β * a ^ 2 / 2) with hE
  have hHb0 : 0 ≤ Hb := Finset.prod_nonneg fun i _ => pow_nonneg hb.le _
  have hKb0 : 0 ≤ Kb := mul_nonneg hc (Finset.prod_nonneg fun i _ => pow_nonneg hb.le _)
  have hE0 : 0 < E := Real.exp_pos _
  set B : ℝ := β * Kb * CJ with hB
  -- the functions
  set F : ℕ → (Fin d → ℝ) → ℝ := fun p u => β ^ p / p.factorial * ((∏ i, u i ^ h i)
    * ((c * ∏ i, u i ^ k i) * J u) ^ p * quadKernel β a (c * ∏ i, u i ^ k i)) with hF
  set f : (Fin d → ℝ) → ℝ := fun u => (∏ i, u i ^ h i)
    * Real.exp (-β * (c * ∏ i, u i ^ k i) ^ 2 + β * (c * ∏ i, u i ^ k i) * (a + J u)) with hf
  set bound : ℕ → (Fin d → ℝ) → ℝ := fun p _ => Hb * E * (B ^ p / p.factorial) with hbound
  have hcontS : Continuous fun u : Fin d → ℝ => c * ∏ i, u i ^ k i :=
    continuous_const.mul (continuous_prod_pow k)
  have hF_meas : ∀ p, AEStronglyMeasurable (F p) μ := fun p => by
    refine Continuous.aestronglyMeasurable ?_
    simp only [hF]
    exact continuous_const.mul (((continuous_prod_pow h).mul ((hcontS.mul hJ).pow p)).mul
      ((quadKernel_continuous β a).comp hcontS))
  have h_bound : ∀ p, ∀ᵐ u ∂μ, ‖F p u‖ ≤ bound p u := by
    intro p
    filter_upwards [hmem] with u hu
    rw [Set.mem_univ_pi] at hu
    have hu0 : ∀ i, 0 ≤ u i := fun i => (hu i).1.le
    have hub : ∀ i, u i ≤ b := fun i => (hu i).2
    have hprodh : ∏ i, u i ^ h i ≤ Hb :=
      Finset.prod_le_prod (fun i _ => pow_nonneg (hu0 i) _)
        fun i _ => pow_le_pow_left₀ (hu0 i) (hub i) _
    have hprodh0 : 0 ≤ ∏ i, u i ^ h i := Finset.prod_nonneg fun i _ => pow_nonneg (hu0 i) _
    have hS0 : 0 ≤ c * ∏ i, u i ^ k i :=
      mul_nonneg hc (Finset.prod_nonneg fun i _ => pow_nonneg (hu0 i) _)
    have hSle : c * ∏ i, u i ^ k i ≤ Kb := by
      rw [hKb]
      exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ => pow_nonneg (hu0 i) _)
        fun i _ => pow_le_pow_left₀ (hu0 i) (hub i) _) hc
    have hJu : |J u| ≤ CJ := by
      have := hCJ u (by rw [Set.mem_univ_pi]; exact fun i => ⟨hu0 i, hub i⟩)
      rwa [Real.norm_eq_abs] at this
    have hK := quadKernel_le_const β a (c * ∏ i, u i ^ k i) hβ
    have hKpos := quadKernel_pos β a (c * ∏ i, u i ^ k i)
    simp only [hF, hbound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hprodh0, abs_of_pos hKpos,
      abs_pow, abs_mul, abs_of_nonneg hS0, abs_div, abs_pow, abs_of_pos hβ, Nat.abs_cast]
    have hpow : ((c * ∏ i, u i ^ k i) * |J u|) ^ p ≤ (Kb * CJ) ^ p :=
      pow_le_pow_left₀ (mul_nonneg hS0 (abs_nonneg _)) (mul_le_mul hSle hJu (abs_nonneg _) hKb0) p
    calc β ^ p / (p.factorial : ℝ) * ((∏ i, u i ^ h i) * ((c * ∏ i, u i ^ k i) * |J u|) ^ p
          * quadKernel β a (c * ∏ i, u i ^ k i))
        ≤ β ^ p / (p.factorial : ℝ) * (Hb * (Kb * CJ) ^ p * E) := by
          gcongr
        _ = Hb * E * (B ^ p / p.factorial) := by rw [hB, mul_pow, mul_pow]; ring
  have h_summable : ∀ᵐ u ∂μ, Summable fun p => bound p u := by
    filter_upwards with u
    exact (Real.summable_pow_div_factorial B).mul_left _
  have bound_integrable : Integrable (fun u => ∑' p, bound p u) μ := by
    have : (fun u : Fin d → ℝ => ∑' p, bound p u) = fun _ => Hb * E * Real.exp B := by
      funext u
      simp only [hbound]
      rw [tsum_mul_left, Real.exp_eq_exp_ℝ, (NormedSpace.expSeries_div_hasSum_exp B).tsum_eq]
    rw [this, hμ]
    exact integrable_const _
  have h_lim : ∀ᵐ u ∂μ, HasSum (fun p => F p u) (f u) := by
    filter_upwards with u
    set s : ℝ := c * ∏ i, u i ^ k i with hs
    have hexp : HasSum (fun p => (β * (s * J u)) ^ p / p.factorial) (Real.exp (β * (s * J u))) := by
      rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
    have hfval : f u = ((∏ i, u i ^ h i) * quadKernel β a s) * Real.exp (β * (s * J u)) := by
      simp only [hf, quadKernel]
      rw [mul_assoc (∏ i, u i ^ h i), ← Real.exp_add]
      congr 2
      ring
    rw [hfval]
    have := hexp.mul_left ((∏ i, u i ^ h i) * quadKernel β a s)
    refine this.congr_fun fun p => ?_
    simp only [hF]
    rw [mul_pow, div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hmain := hasSum_integral_of_dominated_convergence (μ := μ) (F := F) (f := f) bound hF_meas
    h_bound h_summable bound_integrable h_lim
  have hterm : ∀ p, (∫ u, F p u ∂μ) = treeLayer β a b c k h J p := by
    intro p
    simp only [hF, treeLayer, hμ]
    exact MeasureTheory.integral_const_mul _ _
  rw [show (fun p => ∫ u, F p u ∂μ) = treeLayer β a b c k h J from funext hterm] at hmain
  exact hmain

end Laplace.Grammar
