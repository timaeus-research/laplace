/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PolynomialTreeD

/-!
# Perturbations divisible by the monomial do not change the leading term (grammar §4.2)

If `ξ(u) = a + u^k J̃(u)` with `J̃` continuous on the box, then with `t = √n u^k` the exponent is
`βta + βt² J̃/√n`, and the one-term exponential remainder bound gives, for `n ≥ 16 L²`
(`L = sup |J̃|`),

  `|Z(ξ) − Z(a)| ≤ (4L/√n) · Z_{β/2, 2a}(a)`,

where the right-hand side has the same leading order `n^{-p/2} (log n)^m` as `Z(a)` (unit 59 at
`(β/2, 2a)`). Hence `Z(ξ) ~ Z(a) ~ C n^{-p/2} (log n)^m`: the multiplicity theorem holds verbatim
for such `ξ` (`boxIntegralXi_div_isEquivalent`). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- Pointwise: `|e^{-βt² + βt(a + tyε)} − e^{-βt² + βta}| ≤ 4Lε e^{-(β/2)t² + βta}` when
`|y| ≤ L` and `Lε ≤ 1/4`. -/
theorem exp_pert_abs_le (β a L ε t y : ℝ) (hβ : 0 < β) (hL : 0 ≤ L) (hε : 0 ≤ ε) (hy : |y| ≤ L)
    (hLε : L * ε ≤ 1 / 4) :
    |Real.exp (-β * t ^ 2 + β * t * (a + t * y * ε)) - Real.exp (-β * t ^ 2 + β * t * a)|
      ≤ 4 * L * ε * Real.exp (-(β / 2) * t ^ 2 + β * t * a) := by
  have hsplit : Real.exp (-β * t ^ 2 + β * t * (a + t * y * ε))
      = Real.exp (-β * t ^ 2 + β * t * a) * Real.exp (β * t ^ 2 * y * ε) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit, ← mul_sub_one, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hx := abs_exp_sub_sum_range_le (β * t ^ 2 * y * ε) 1
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    pow_one, Nat.factorial_one] at hx
  have hxabs : |β * t ^ 2 * y * ε| ≤ β * t ^ 2 * L * ε := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hβ, abs_of_nonneg (sq_nonneg t), abs_of_nonneg hε]
    gcongr
  have hbt : 0 ≤ β * t ^ 2 := mul_nonneg hβ.le (sq_nonneg t)
  have h4 : β * t ^ 2 * L * ε ≤ β * t ^ 2 / 4 := by nlinarith
  have hxe : Real.exp |β * t ^ 2 * y * ε| ≤ Real.exp (β * t ^ 2 / 4) :=
    Real.exp_le_exp.2 (hxabs.trans h4)
  have hxe' : β * t ^ 2 / 4 * Real.exp (-(β * t ^ 2 / 4)) ≤ 1 := by
    have := Real.add_one_le_exp (β * t ^ 2 / 4)
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
    linarith
  have hE : Real.exp (-β * t ^ 2 + β * t * a) * Real.exp (β * t ^ 2 / 4)
      = Real.exp (-(β / 2) * t ^ 2 + β * t * a) * Real.exp (-(β * t ^ 2 / 4)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hLε0 : 0 ≤ 4 * L * ε * Real.exp (-(β / 2) * t ^ 2 + β * t * a) := by positivity
  calc Real.exp (-β * t ^ 2 + β * t * a) * |Real.exp (β * t ^ 2 * y * ε) - 1|
      ≤ Real.exp (-β * t ^ 2 + β * t * a) * (β * t ^ 2 * L * ε * Real.exp (β * t ^ 2 / 4)) := by
        gcongr
        exact hx.trans (mul_le_mul hxabs hxe (Real.exp_pos _).le (by positivity))
    _ = (4 * L * ε * Real.exp (-(β / 2) * t ^ 2 + β * t * a))
          * (β * t ^ 2 / 4 * Real.exp (-(β * t ^ 2 / 4))) := by
        rw [show Real.exp (-β * t ^ 2 + β * t * a) * (β * t ^ 2 * L * ε * Real.exp (β * t ^ 2 / 4))
          = Real.exp (-β * t ^ 2 + β * t * a) * Real.exp (β * t ^ 2 / 4) * (β * t ^ 2 * L * ε)
          by ring, hE]
        ring
    _ ≤ (4 * L * ε * Real.exp (-(β / 2) * t ^ 2 + β * t * a)) * 1 :=
        mul_le_mul_of_nonneg_left hxe' hLε0
    _ = 4 * L * ε * Real.exp (-(β / 2) * t ^ 2 + β * t * a) := mul_one _

/-- The box integral is nonnegative. -/
theorem boxIntegralFin_nonneg (β a b c : ℝ) {d : ℕ} (k h : Fin d → ℕ) :
    0 ≤ boxIntegralFin β a b c k h := by
  unfold boxIntegralFin
  refine integral_nonneg_of_ae ?_
  have hmem : ∀ᵐ u ∂(boxMeasure b d), u ∈ Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) b := by
    rw [boxMeasure_eq_restrict]
    exact ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
  filter_upwards [hmem] with u hu
  rw [Set.mem_univ_pi] at hu
  exact mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (hu i).1.le _)
    (quadKernel_pos β a _).le

/-- **The perturbation bound**: for `ξ = a + u^k J̃`, `|J̃| ≤ L` on the box and `n ≥ 16L²`,
`|Z(ξ) − Z(a)| ≤ (4L/√n) Z_{β/2,2a}(n)`. -/
theorem boxIntegralXi_div_sub_le (β a b : ℝ) (hβ : 0 < β) {d : ℕ} (k h : Fin d → ℕ)
    (J : (Fin d → ℝ) → ℝ) (hJ : Continuous J) (L : ℝ) (hL : 0 ≤ L)
    (hJL : ∀ u : Fin d → ℝ, (∀ i, 0 ≤ u i ∧ u i ≤ b) → |J u| ≤ L) (n : ℝ) (hn : 0 < n)
    (hnL : 16 * L ^ 2 ≤ n) :
    |boxIntegralXi β a b (Real.sqrt n) k h (fun u => (∏ i, u i ^ k i) * J u)
        - boxIntegralFin β a b (Real.sqrt n) k h|
      ≤ 4 * L / Real.sqrt n * boxIntegralFin (β / 2) (2 * a) b (Real.sqrt n) k h := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hLε : L * (1 / Real.sqrt n) ≤ 1 / 4 := by
    have h4L : 4 * L ≤ Real.sqrt n := by
      rw [Real.le_sqrt (by positivity) hn.le]; nlinarith
    rw [mul_one_div, div_le_iff₀ hsn]; linarith
  have hcontS : Continuous fun u : Fin d → ℝ => Real.sqrt n * ∏ i, u i ^ k i :=
    continuous_const.mul (continuous_prod_pow k)
  set F : (Fin d → ℝ) → ℝ := fun u => (∏ i, u i ^ h i)
    * Real.exp (-β * (Real.sqrt n * ∏ i, u i ^ k i) ^ 2
      + β * (Real.sqrt n * ∏ i, u i ^ k i) * (a + (∏ i, u i ^ k i) * J u)) with hF
  set G : (Fin d → ℝ) → ℝ := fun u => (∏ i, u i ^ h i)
    * quadKernel β a (Real.sqrt n * ∏ i, u i ^ k i) with hG
  set W : (Fin d → ℝ) → ℝ := fun u => (∏ i, u i ^ h i)
    * quadKernel (β / 2) (2 * a) (Real.sqrt n * ∏ i, u i ^ k i) with hW
  have hFc : Continuous F := by
    simp only [hF]
    exact (continuous_prod_pow h).mul (Real.continuous_exp.comp (by fun_prop))
  have hGc : Continuous G := (continuous_prod_pow h).mul ((quadKernel_continuous β a).comp hcontS)
  have hWc : Continuous W :=
    (continuous_prod_pow h).mul ((quadKernel_continuous (β / 2) (2 * a)).comp hcontS)
  have hFi := integrable_box_of_continuous b F hFc
  have hGi := integrable_box_of_continuous b G hGc
  have hWi := integrable_box_of_continuous b W hWc
  have hmem : ∀ᵐ u ∂(boxMeasure b d), u ∈ Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) b := by
    rw [boxMeasure_eq_restrict]
    exact ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
  have hpt : ∀ᵐ u ∂(boxMeasure b d), ‖F u - G u‖ ≤ 4 * L / Real.sqrt n * W u := by
    filter_upwards [hmem] with u hu
    rw [Set.mem_univ_pi] at hu
    have hu0 : ∀ i, 0 ≤ u i := fun i => (hu i).1.le
    have hub : ∀ i, u i ≤ b := fun i => (hu i).2
    have hprod0 : 0 ≤ ∏ i, u i ^ h i := Finset.prod_nonneg fun i _ => pow_nonneg (hu0 i) _
    have hpk0 : 0 ≤ ∏ i, u i ^ k i := Finset.prod_nonneg fun i _ => pow_nonneg (hu0 i) _
    have hJu : |J u| ≤ L := hJL u fun i => ⟨hu0 i, hub i⟩
    simp only [hF, hG, hW, quadKernel]
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.sqrt n * ∏ i, u i ^ k i := ⟨_, rfl⟩
    have htε : (∏ i, u i ^ k i) = t * (1 / Real.sqrt n) := by rw [ht]; field_simp
    rw [← ht, Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg hprod0, htε,
      show β * a * t = β * t * a by ring, show β / 2 * (2 * a) * t = β * t * a by ring,
      show t * (1 / Real.sqrt n) * J u = t * J u * (1 / Real.sqrt n) by ring]
    have key := exp_pert_abs_le β a L (1 / Real.sqrt n) t (J u) hβ hL (by positivity) hJu hLε
    calc (∏ i, u i ^ h i) * |Real.exp (-β * t ^ 2 + β * t * (a + t * J u * (1 / Real.sqrt n)))
          - Real.exp (-β * t ^ 2 + β * t * a)|
        ≤ (∏ i, u i ^ h i)
            * (4 * L * (1 / Real.sqrt n) * Real.exp (-(β / 2) * t ^ 2 + β * t * a)) := by
          gcongr
      _ = 4 * L / Real.sqrt n * ((∏ i, u i ^ h i) * Real.exp (-(β / 2) * t ^ 2 + β * t * a)) := by
          ring
  have hsub : boxIntegralXi β a b (Real.sqrt n) k h (fun u => (∏ i, u i ^ k i) * J u)
      - boxIntegralFin β a b (Real.sqrt n) k h = ∫ u, (F u - G u) ∂(boxMeasure b d) := by
    rw [MeasureTheory.integral_sub hFi hGi]; rfl
  have hW' : (∫ u, 4 * L / Real.sqrt n * W u ∂(boxMeasure b d))
      = 4 * L / Real.sqrt n * boxIntegralFin (β / 2) (2 * a) b (Real.sqrt n) k h := by
    rw [MeasureTheory.integral_const_mul]; rfl
  rw [hsub, ← hW', ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le (hWi.const_mul _) hpt

/-- **The multiplicity theorem for `ξ = a + u^k J̃`**: the perturbation does not change the leading
term, so the box integral is still `~ C n^{-p/2} (log n)^m` with the same `p`, `m` as for constant
`ξ`. -/
theorem boxIntegralXi_div_isEquivalent (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) (D : ℕ)
    (k h : Fin (D + 2) → ℕ) (hk : ∀ i, 0 < k i) (J : (Fin (D + 2) → ℝ) → ℝ) (hJ : Continuous J) :
    ∃ (p : ℝ) (m : ℕ) (C : ℝ), 0 < C ∧ (∀ i, p ≤ finExp k h i) ∧
      m + 1 = (Finset.univ.filter fun i => finExp k h i = p).card ∧
      (fun n : ℝ => boxIntegralXi β a b (Real.sqrt n) k h (fun u => (∏ i, u i ^ k i) * J u))
        ~[atTop] fun n : ℝ => C * (n ^ (-(p / 2)) * Real.log n ^ m) := by
  -- a bound for J on the closed box
  obtain ⟨L₀, hL₀⟩ := (isCompact_univ_pi fun _ : Fin (D + 2) =>
    isCompact_Icc (a := (0 : ℝ)) (b := b)) |>.exists_bound_of_continuousOn hJ.continuousOn
  set L : ℝ := max L₀ 0 with hLdef
  have hL : 0 ≤ L := le_max_right _ _
  have hJL : ∀ u : Fin (D + 2) → ℝ, (∀ i, 0 ≤ u i ∧ u i ≤ b) → |J u| ≤ L := by
    intro u hu
    have := hL₀ u (by rw [Set.mem_univ_pi]; exact fun i => hu i)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  -- the two constant-ξ asymptotics
  obtain ⟨p, m, C, hC, hmin, hcard, hE⟩ := boxIntegralFin_isEquivalent_general β a b hβ hb D k h hk
  obtain ⟨p', m', C', hC', hmin', hcard', hE'⟩ :=
    boxIntegralFin_isEquivalent_general (β / 2) (2 * a) b (by positivity) hb D k h hk
  -- p = p' and m = m'
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
  refine ⟨p, m, C, hC, hmin, hcard, ?_⟩
  -- the difference is little-o of the leading term
  set g : ℝ → ℝ := fun n => n ^ (-(p / 2)) * Real.log n ^ m with hg
  have hdiff : (fun n : ℝ => boxIntegralXi β a b (Real.sqrt n) k h (fun u => (∏ i, u i ^ k i) * J u)
      - boxIntegralFin β a b (Real.sqrt n) k h)
      =O[atTop] fun n : ℝ =>
        n ^ (-(1 / 2 : ℝ)) * boxIntegralFin (β / 2) (2 * a) b (Real.sqrt n) k h := by
    apply IsBigO.of_bound (4 * L)
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (16 * L ^ 2)] with n hn hnL
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
    have hZ' : 0 ≤ boxIntegralFin (β / 2) (2 * a) b (Real.sqrt n) k h :=
      boxIntegralFin_nonneg _ _ _ _ _ _
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    calc |boxIntegralXi β a b (Real.sqrt n) k h (fun u => (∏ i, u i ^ k i) * J u)
          - boxIntegralFin β a b (Real.sqrt n) k h|
        ≤ 4 * L / Real.sqrt n * boxIntegralFin (β / 2) (2 * a) b (Real.sqrt n) k h :=
          boxIntegralXi_div_sub_le β a b hβ k h J hJ L hL hJL n hn hnL
      _ = 4 * L * |n ^ (-(1 / 2 : ℝ)) * boxIntegralFin (β / 2) (2 * a) b (Real.sqrt n) k h| := by
          rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hn _), abs_of_nonneg hZ', Real.sqrt_eq_rpow,
            Real.rpow_neg hn.le]
          ring
  have hsmall : (fun n : ℝ =>
      n ^ (-(1 / 2 : ℝ)) * boxIntegralFin (β / 2) (2 * a) b (Real.sqrt n) k h)
      =o[atTop] fun n : ℝ => C * g n := by
    have h1 : (fun n : ℝ => n ^ (-(1 / 2 : ℝ))) =o[atTop] fun _ : ℝ => (1 : ℝ) :=
      (isLittleO_one_iff ℝ).2 (tendsto_rpow_neg_atTop (by norm_num))
    have h2 : (fun n : ℝ => boxIntegralFin (β / 2) (2 * a) b (Real.sqrt n) k h) =O[atTop] g :=
      hE'.isBigO.trans (isBigO_const_mul_self C' g atTop)
    have := h1.mul_isBigO h2
    refine (this.congr_right fun n => ?_).const_mul_right hC.ne'
    simp
  have hsum := hE.add_isLittleO (hdiff.trans_isLittleO hsmall)
  refine hsum.congr_left (Filter.Eventually.of_forall fun n => ?_)
  simp only [Pi.add_apply]
  ring

end Laplace.Grammar
