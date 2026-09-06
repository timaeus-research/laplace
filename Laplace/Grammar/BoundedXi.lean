/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.FreeEnergyPerturbed

/-!
# Exponent and multiplicity are robust for every bounded `ξ` (grammar §4.2)

For an arbitrary continuous `J` on the box (no divisibility assumption) the standard integral with
`ξ = a + J` is sandwiched between the constant-`ξ` integrals at `a − L` and `a + L`, `L = sup |J|`,
since `t ↦ e^{βt ξ}` is monotone in `ξ` for `t ≥ 0`. Both bounds are `~ C_± n^{-p/2} (log n)^m` by
unit 59, hence

  `Z(a + J) = Θ(n^{-p/2} (log n)^m)`

(`boxIntegralXi_isTheta`): the exponent `p/2` and the logarithmic degree `m` of `thm:TaylorTree` are
determined by `(h,k)` alone, for every bounded `ξ`; only the constant depends on `ξ`.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- Sandwich: `Z(a − L) ≤ Z(a + J) ≤ Z(a + L)` when `|J| ≤ L` on the box. -/
theorem boxIntegralXi_sandwich (β a b c : ℝ) (hβ : 0 < β) (hc : 0 ≤ c) {d : ℕ} (k h : Fin d → ℕ)
    (J : (Fin d → ℝ) → ℝ) (hJ : Continuous J) (L : ℝ)
    (hJL : ∀ u : Fin d → ℝ, (∀ i, 0 ≤ u i ∧ u i ≤ b) → |J u| ≤ L) :
    boxIntegralFin β (a - L) b c k h ≤ boxIntegralXi β a b c k h J ∧
      boxIntegralXi β a b c k h J ≤ boxIntegralFin β (a + L) b c k h := by
  have hcontS : Continuous fun u : Fin d → ℝ => c * ∏ i, u i ^ k i :=
    continuous_const.mul (continuous_prod_pow k)
  have hXc : Continuous fun u : Fin d → ℝ => (∏ i, u i ^ h i)
      * Real.exp (-β * (c * ∏ i, u i ^ k i) ^ 2 + β * (c * ∏ i, u i ^ k i) * (a + J u)) :=
    (continuous_prod_pow h).mul (Real.continuous_exp.comp (by fun_prop))
  have hFc : ∀ a' : ℝ, Continuous fun u : Fin d → ℝ =>
      (∏ i, u i ^ h i) * quadKernel β a' (c * ∏ i, u i ^ k i) := fun a' =>
    (continuous_prod_pow h).mul ((quadKernel_continuous β a').comp hcontS)
  have hmem : ∀ᵐ u ∂(boxMeasure b d), u ∈ Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) b := by
    rw [boxMeasure_eq_restrict]
    exact ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
  have key : ∀ u : Fin d → ℝ, (∀ i, 0 ≤ u i ∧ u i ≤ b) →
      (∏ i, u i ^ h i) * quadKernel β (a - L) (c * ∏ i, u i ^ k i)
        ≤ (∏ i, u i ^ h i)
          * Real.exp (-β * (c * ∏ i, u i ^ k i) ^ 2 + β * (c * ∏ i, u i ^ k i) * (a + J u))
      ∧ (∏ i, u i ^ h i)
          * Real.exp (-β * (c * ∏ i, u i ^ k i) ^ 2 + β * (c * ∏ i, u i ^ k i) * (a + J u))
        ≤ (∏ i, u i ^ h i) * quadKernel β (a + L) (c * ∏ i, u i ^ k i) := by
    intro u hu
    have hprod0 : 0 ≤ ∏ i, u i ^ h i := Finset.prod_nonneg fun i _ => pow_nonneg (hu i).1 _
    have ht0 : 0 ≤ c * ∏ i, u i ^ k i :=
      mul_nonneg hc (Finset.prod_nonneg fun i _ => pow_nonneg (hu i).1 _)
    have hJu := abs_le.1 (hJL u hu)
    have hβt : 0 ≤ β * (c * ∏ i, u i ^ k i) := mul_nonneg hβ.le ht0
    simp only [quadKernel]
    constructor
    · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hprod0
      nlinarith [mul_le_mul_of_nonneg_left hJu.1 hβt]
    · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hprod0
      nlinarith [mul_le_mul_of_nonneg_left hJu.2 hβt]
  constructor
  · unfold boxIntegralFin boxIntegralXi
    refine integral_mono_ae (integrable_box_of_continuous b _ (hFc _))
      (integrable_box_of_continuous b _ hXc) ?_
    filter_upwards [hmem] with u hu
    rw [Set.mem_univ_pi] at hu
    exact (key u fun i => ⟨(hu i).1.le, (hu i).2⟩).1
  · unfold boxIntegralFin boxIntegralXi
    refine integral_mono_ae (integrable_box_of_continuous b _ hXc)
      (integrable_box_of_continuous b _ (hFc _)) ?_
    filter_upwards [hmem] with u hu
    rw [Set.mem_univ_pi] at hu
    exact (key u fun i => ⟨(hu i).1.le, (hu i).2⟩).2

/-- **Exponent and multiplicity for every bounded `ξ`**: `Z(a + J) = Θ(n^{-p/2} (log n)^m)` with `p`
the minimal candidate exponent and `m + 1` its multiplicity, for any continuous `J`. -/
theorem boxIntegralXi_isTheta (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) (D : ℕ)
    (k h : Fin (D + 2) → ℕ) (hk : ∀ i, 0 < k i) (J : (Fin (D + 2) → ℝ) → ℝ) (hJ : Continuous J) :
    ∃ (p : ℝ) (m : ℕ), (∀ i, p ≤ finExp k h i) ∧
      m + 1 = (Finset.univ.filter fun i => finExp k h i = p).card ∧
      (fun n : ℝ => boxIntegralXi β a b (Real.sqrt n) k h J)
        =Θ[atTop] fun n : ℝ => n ^ (-(p / 2)) * Real.log n ^ m := by
  obtain ⟨L₀, hL₀⟩ := (isCompact_univ_pi fun _ : Fin (D + 2) =>
    isCompact_Icc (a := (0 : ℝ)) (b := b)) |>.exists_bound_of_continuousOn hJ.continuousOn
  set L : ℝ := max L₀ 0 with hLdef
  have hJL : ∀ u : Fin (D + 2) → ℝ, (∀ i, 0 ≤ u i ∧ u i ≤ b) → |J u| ≤ L := by
    intro u hu
    have := hL₀ u (by rw [Set.mem_univ_pi]; exact fun i => hu i)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  obtain ⟨p, m, Cp, hCp, hmin, hcard, hEp⟩ :=
    boxIntegralFin_isEquivalent_general β (a + L) b hβ hb D k h hk
  obtain ⟨p', m', Cm, hCm, hmin', hcard', hEm⟩ :=
    boxIntegralFin_isEquivalent_general β (a - L) b hβ hb D k h hk
  have hne : (Finset.univ.filter fun i => finExp k h i = p).Nonempty := by
    rw [← Finset.card_pos, ← hcard]; exact Nat.succ_pos m
  have hne' : (Finset.univ.filter fun i => finExp k h i = p').Nonempty := by
    rw [← Finset.card_pos, ← hcard']; exact Nat.succ_pos m'
  obtain ⟨i₀, hi₀⟩ := hne
  obtain ⟨i₁, hi₁⟩ := hne'
  have hi₀' : finExp k h i₀ = p := by simpa using hi₀
  have hi₁' : finExp k h i₁ = p' := by simpa using hi₁
  have hpp : p = p' := le_antisymm (hi₁' ▸ hmin i₁) (hi₀' ▸ hmin' i₀)
  subst hpp
  have hmm : m = m' := by have := hcard.trans hcard'.symm; omega
  subst hmm
  refine ⟨p, m, hmin, hcard, ?_⟩
  set g : ℝ → ℝ := fun n => n ^ (-(p / 2)) * Real.log n ^ m with hg
  have hsand : ∀ n : ℝ, 0 < n →
      boxIntegralFin β (a - L) b (Real.sqrt n) k h ≤ boxIntegralXi β a b (Real.sqrt n) k h J ∧
        boxIntegralXi β a b (Real.sqrt n) k h J ≤ boxIntegralFin β (a + L) b (Real.sqrt n) k h :=
    fun n hn => boxIntegralXi_sandwich β a b (Real.sqrt n) hβ (Real.sqrt_nonneg n) k h J hJ L hJL
  have hlow0 : ∀ n : ℝ, 0 ≤ boxIntegralFin β (a - L) b (Real.sqrt n) k h :=
    fun n => boxIntegralFin_nonneg _ _ _ _ _ _
  -- upper bound: Z(ξ) =O Z(a+L) =O g
  have hup : (fun n : ℝ => boxIntegralXi β a b (Real.sqrt n) k h J)
      =O[atTop] fun n : ℝ => boxIntegralFin β (a + L) b (Real.sqrt n) k h := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    obtain ⟨h1, h2⟩ := hsand n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
      abs_of_nonneg ((hlow0 n).trans h1), abs_of_nonneg ((hlow0 n).trans (h1.trans h2))]
    exact h2
  -- lower bound: g =O Z(a−L) =O Z(ξ)
  have hlo : (fun n : ℝ => boxIntegralFin β (a - L) b (Real.sqrt n) k h)
      =O[atTop] fun n : ℝ => boxIntegralXi β a b (Real.sqrt n) k h J := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    obtain ⟨h1, _⟩ := hsand n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg (hlow0 n),
      abs_of_nonneg ((hlow0 n).trans h1)]
    exact h1
  refine IsBigO.antisymm ?_ ?_
  · exact hup.trans (hEp.isBigO.trans (isBigO_const_mul_self Cp g atTop))
  · exact (isBigO_self_const_mul hCm.ne' g atTop).trans (hEm.isBigO_symm.trans hlo)

end Laplace.Grammar
