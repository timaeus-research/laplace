/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.DivisiblePerturbation

/-!
# Divisible perturbations of the weight (grammar §4.2)

The mechanism of unit 65 also handles the weight: for `η = η₀ + u^k η̃` and `ξ = a + u^k J̃` with
`η̃, J̃` continuous, the extra factor `u^k = t/√n` in the weight term gives

  `|Z(ξ, η) − η₀ Z(ξ, 1)| ≤ (L_η (4/β + 1)/√n) · Z_{β/2, 2a}(n)`  (`n ≥ 16 L_J²`),

using `t e^{-(β/4)t²} ≤ 4/β + 1`. Combined with unit 65,
`Z(ξ, η) − η₀ Z(a, 1) = O(n^{-1/2} Z_{β/2,2a})`, so for `η₀ ≠ 0` the standard integral is
`~ η₀ C n^{-p/2} (log n)^m`
(`boxIntegralXiEta_isEquivalent`): the leading coefficient is `η(0)` times the constant-`ξ`
constant, exactly as the paper's remark on the sign of `η` predicts. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- The chart standard integral with `ξ = a + J` and weight `η`. -/
noncomputable def boxIntegralXiEta (β a b c : ℝ) {d : ℕ} (k h : Fin d → ℕ)
    (J η : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ u : Fin d → ℝ, (∏ i, u i ^ h i) * η u
    * Real.exp (-β * (c * ∏ i, u i ^ k i) ^ 2 + β * (c * ∏ i, u i ^ k i) * (a + J u))
    ∂(boxMeasure b d)

/-- `t e^{-(β/4)t²} ≤ 4/β + 1` for `t ≥ 0`. -/
theorem mul_exp_neg_quarter_le (β t : ℝ) (hβ : 0 < β) :
    t * Real.exp (-(β / 4) * t ^ 2) ≤ 4 / β + 1 := by
  have h1 : t ≤ t ^ 2 + 1 := by nlinarith [sq_nonneg (t - 1)]
  have h2 : β / 4 * t ^ 2 + 1 ≤ Real.exp (β / 4 * t ^ 2) := Real.add_one_le_exp _
  have hE : 0 < Real.exp (β / 4 * t ^ 2) := Real.exp_pos _
  have hneg : Real.exp (-(β / 4) * t ^ 2) = (Real.exp (β / 4 * t ^ 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [hneg, ← div_eq_mul_inv, div_le_iff₀ hE]
  have h3 : t ^ 2 ≤ 4 / β * Real.exp (β / 4 * t ^ 2) := by
    have : β / 4 * t ^ 2 ≤ Real.exp (β / 4 * t ^ 2) := by linarith
    calc t ^ 2 = 4 / β * (β / 4 * t ^ 2) := by field_simp
      _ ≤ 4 / β * Real.exp (β / 4 * t ^ 2) := mul_le_mul_of_nonneg_left this (by positivity)
  have h4 : (1 : ℝ) ≤ Real.exp (β / 4 * t ^ 2) := Real.one_le_exp (by positivity)
  calc t ≤ t ^ 2 + 1 := h1
    _ ≤ (4 / β + 1) * Real.exp (β / 4 * t ^ 2) := by nlinarith [h3, h4]

/-- **The weight-perturbation bound**: for `η̃, J̃` bounded by `Lη, L` on the box and `n ≥ 16 L²`,
`|Z(ξ, η₀ + u^k η̃) − η₀ Z(ξ, 1)| ≤ (Lη (4/β+1)/√n) Z_{β/2,2a}(n)`. -/
theorem boxIntegralXiEta_sub_le (β a b : ℝ) (hβ : 0 < β) {d : ℕ} (k h : Fin d → ℕ)
    (J η : (Fin d → ℝ) → ℝ) (hJ : Continuous J) (hη : Continuous η) (η₀ L Lη : ℝ) (hL : 0 ≤ L)
    (hLη : 0 ≤ Lη) (hJL : ∀ u : Fin d → ℝ, (∀ i, 0 ≤ u i ∧ u i ≤ b) → |J u| ≤ L)
    (hηL : ∀ u : Fin d → ℝ, (∀ i, 0 ≤ u i ∧ u i ≤ b) → |η u| ≤ Lη) (n : ℝ) (hn : 0 < n)
    (hnL : 16 * L ^ 2 ≤ n) :
    |boxIntegralXiEta β a b (Real.sqrt n) k h (fun u => (∏ i, u i ^ k i) * J u)
          (fun u => η₀ + (∏ i, u i ^ k i) * η u)
        - η₀ * boxIntegralXi β a b (Real.sqrt n) k h (fun u => (∏ i, u i ^ k i) * J u)|
      ≤ Lη * (4 / β + 1) / Real.sqrt n * boxIntegralFin (β / 2) (2 * a) b (Real.sqrt n) k h := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hLε : L * (1 / Real.sqrt n) ≤ 1 / 4 := by
    have h4L : 4 * L ≤ Real.sqrt n := by
      rw [Real.le_sqrt (by positivity) hn.le]; nlinarith
    rw [mul_one_div, div_le_iff₀ hsn]; linarith
  have hcontS : Continuous fun u : Fin d → ℝ => Real.sqrt n * ∏ i, u i ^ k i :=
    continuous_const.mul (continuous_prod_pow k)
  set E : (Fin d → ℝ) → ℝ := fun u => Real.exp (-β * (Real.sqrt n * ∏ i, u i ^ k i) ^ 2
    + β * (Real.sqrt n * ∏ i, u i ^ k i) * (a + (∏ i, u i ^ k i) * J u)) with hE
  have hEc : Continuous E := by simp only [hE]; exact Real.continuous_exp.comp (by fun_prop)
  set F : (Fin d → ℝ) → ℝ := fun u => (∏ i, u i ^ h i) * (η₀ + (∏ i, u i ^ k i) * η u) * E u
    with hF
  set G : (Fin d → ℝ) → ℝ := fun u => η₀ * ((∏ i, u i ^ h i) * E u) with hG
  set W : (Fin d → ℝ) → ℝ := fun u => (∏ i, u i ^ h i)
    * quadKernel (β / 2) (2 * a) (Real.sqrt n * ∏ i, u i ^ k i) with hW
  have hFc : Continuous F := by
    simp only [hF]
    exact ((continuous_prod_pow h).mul
      (continuous_const.add ((continuous_prod_pow k).mul hη))).mul hEc
  have hGc : Continuous G := continuous_const.mul ((continuous_prod_pow h).mul hEc)
  have hWc : Continuous W :=
    (continuous_prod_pow h).mul ((quadKernel_continuous (β / 2) (2 * a)).comp hcontS)
  have hFi := integrable_box_of_continuous b F hFc
  have hGi := integrable_box_of_continuous b G hGc
  have hWi := integrable_box_of_continuous b W hWc
  have hmem : ∀ᵐ u ∂(boxMeasure b d), u ∈ Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) b := by
    rw [boxMeasure_eq_restrict]
    exact ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
  have hpt : ∀ᵐ u ∂(boxMeasure b d), ‖F u - G u‖ ≤ Lη * (4 / β + 1) / Real.sqrt n * W u := by
    filter_upwards [hmem] with u hu
    rw [Set.mem_univ_pi] at hu
    have hu0 : ∀ i, 0 ≤ u i := fun i => (hu i).1.le
    have hub : ∀ i, u i ≤ b := fun i => (hu i).2
    have hprod0 : 0 ≤ ∏ i, u i ^ h i := Finset.prod_nonneg fun i _ => pow_nonneg (hu0 i) _
    have hpk0 : 0 ≤ ∏ i, u i ^ k i := Finset.prod_nonneg fun i _ => pow_nonneg (hu0 i) _
    have hJu : |J u| ≤ L := hJL u fun i => ⟨hu0 i, hub i⟩
    have hηu : |η u| ≤ Lη := hηL u fun i => ⟨hu0 i, hub i⟩
    simp only [hF, hG, hE, hW, quadKernel]
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.sqrt n * ∏ i, u i ^ k i := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := by rw [ht]; positivity
    have htε : (∏ i, u i ^ k i) = t * (1 / Real.sqrt n) := by rw [ht]; field_simp
    rw [← ht, htε, show β / 2 * (2 * a) * t = β * t * a by ring]
    -- F − G = (∏ u^h) · (t/√n) η(u) · e^{…}
    have hdiff : (∏ i, u i ^ h i) * (η₀ + t * (1 / Real.sqrt n) * η u)
          * Real.exp (-β * t ^ 2 + β * t * (a + t * (1 / Real.sqrt n) * J u))
        - η₀ * ((∏ i, u i ^ h i)
          * Real.exp (-β * t ^ 2 + β * t * (a + t * (1 / Real.sqrt n) * J u)))
        = (∏ i, u i ^ h i) * (t * (1 / Real.sqrt n) * η u)
          * Real.exp (-β * t ^ 2 + β * t * (a + t * (1 / Real.sqrt n) * J u)) := by ring
    rw [hdiff, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hprod0,
      abs_of_pos (Real.exp_pos _), abs_mul, abs_mul, abs_of_nonneg ht0,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.sqrt n)]
    -- the exponential is at most e^{-(3β/4) t² + βta}
    have hexp : Real.exp (-β * t ^ 2 + β * t * (a + t * (1 / Real.sqrt n) * J u))
        ≤ Real.exp (-(β / 4) * t ^ 2) * Real.exp (-(β / 2) * t ^ 2 + β * t * a) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have : β * t * (t * (1 / Real.sqrt n) * J u) ≤ β * t ^ 2 / 4 := by
        have h1 : t * (1 / Real.sqrt n) * J u ≤ t * (1 / Real.sqrt n) * L :=
          mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans hJu) (by positivity)
        have h2 : t * (1 / Real.sqrt n) * L ≤ t / 4 := by
          rw [mul_assoc, mul_comm (1 / Real.sqrt n) L]
          calc t * (L * (1 / Real.sqrt n)) ≤ t * (1 / 4) := mul_le_mul_of_nonneg_left hLε ht0
            _ = t / 4 := by ring
        nlinarith [mul_nonneg hβ.le ht0]
      nlinarith
    have hte := mul_exp_neg_quarter_le β t hβ
    calc (∏ i, u i ^ h i) * (t * (1 / Real.sqrt n) * |η u|)
          * Real.exp (-β * t ^ 2 + β * t * (a + t * (1 / Real.sqrt n) * J u))
        ≤ (∏ i, u i ^ h i) * (t * (1 / Real.sqrt n) * Lη)
          * (Real.exp (-(β / 4) * t ^ 2) * Real.exp (-(β / 2) * t ^ 2 + β * t * a)) := by
          gcongr
      _ = Lη / Real.sqrt n * (t * Real.exp (-(β / 4) * t ^ 2))
          * ((∏ i, u i ^ h i) * Real.exp (-(β / 2) * t ^ 2 + β * t * a)) := by ring
      _ ≤ Lη / Real.sqrt n * (4 / β + 1)
          * ((∏ i, u i ^ h i) * Real.exp (-(β / 2) * t ^ 2 + β * t * a)) := by
          gcongr
      _ = Lη * (4 / β + 1) / Real.sqrt n
          * ((∏ i, u i ^ h i) * Real.exp (-(β / 2) * t ^ 2 + β * t * a)) := by ring
  have hsub : boxIntegralXiEta β a b (Real.sqrt n) k h (fun u => (∏ i, u i ^ k i) * J u)
        (fun u => η₀ + (∏ i, u i ^ k i) * η u)
      - η₀ * boxIntegralXi β a b (Real.sqrt n) k h (fun u => (∏ i, u i ^ k i) * J u)
      = ∫ u, (F u - G u) ∂(boxMeasure b d) := by
    rw [MeasureTheory.integral_sub hFi hGi, boxIntegralXi, ← MeasureTheory.integral_const_mul]
    rfl
  have hW' : (∫ u, Lη * (4 / β + 1) / Real.sqrt n * W u ∂(boxMeasure b d))
      = Lη * (4 / β + 1) / Real.sqrt n * boxIntegralFin (β / 2) (2 * a) b (Real.sqrt n) k h := by
    rw [MeasureTheory.integral_const_mul]; rfl
  rw [hsub, ← hW', ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le (hWi.const_mul _) hpt

/-- **Divisible perturbations of `ξ` and `η`**: for `ξ = a + u^k J̃`, `η = η₀ + u^k η̃` with
`η₀ ≠ 0`,
`Z(ξ, η) ~ η₀ C n^{-p/2} (log n)^m` with the constant-`ξ` exponent, multiplicity and constant. -/
theorem boxIntegralXiEta_isEquivalent (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) (D : ℕ)
    (k h : Fin (D + 2) → ℕ) (hk : ∀ i, 0 < k i) (J η : (Fin (D + 2) → ℝ) → ℝ) (hJ : Continuous J)
    (hη : Continuous η) (η₀ : ℝ) (hη₀ : η₀ ≠ 0) :
    ∃ (p : ℝ) (m : ℕ) (C : ℝ), 0 < C ∧ (∀ i, p ≤ finExp k h i) ∧
      m + 1 = (Finset.univ.filter fun i => finExp k h i = p).card ∧
      (fun n : ℝ => boxIntegralXiEta β a b (Real.sqrt n) k h (fun u => (∏ i, u i ^ k i) * J u)
          (fun u => η₀ + (∏ i, u i ^ k i) * η u))
        ~[atTop] fun n : ℝ => η₀ * C * (n ^ (-(p / 2)) * Real.log n ^ m) := by
  -- bounds for J and η on the closed box
  have hcpt := isCompact_univ_pi fun _ : Fin (D + 2) => isCompact_Icc (a := (0 : ℝ)) (b := b)
  obtain ⟨L₀, hL₀⟩ := hcpt.exists_bound_of_continuousOn hJ.continuousOn
  obtain ⟨Lη₀, hLη₀⟩ := hcpt.exists_bound_of_continuousOn hη.continuousOn
  set L : ℝ := max L₀ 0 with hLdef
  set Lη : ℝ := max Lη₀ 0 with hLηdef
  have hL : 0 ≤ L := le_max_right _ _
  have hLη : 0 ≤ Lη := le_max_right _ _
  have hJL : ∀ u : Fin (D + 2) → ℝ, (∀ i, 0 ≤ u i ∧ u i ≤ b) → |J u| ≤ L := by
    intro u hu
    have := hL₀ u (by rw [Set.mem_univ_pi]; exact fun i => hu i)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hηL : ∀ u : Fin (D + 2) → ℝ, (∀ i, 0 ≤ u i ∧ u i ≤ b) → |η u| ≤ Lη := by
    intro u hu
    have := hLη₀ u (by rw [Set.mem_univ_pi]; exact fun i => hu i)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  obtain ⟨p, m, C, hC, hmin, hcard, hE⟩ := boxIntegralFin_isEquivalent_general β a b hβ hb D k h hk
  obtain ⟨p', m', C', hC', hmin', hcard', hE'⟩ :=
    boxIntegralFin_isEquivalent_general (β / 2) (2 * a) b (by positivity) hb D k h hk
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
  set g : ℝ → ℝ := fun n => n ^ (-(p / 2)) * Real.log n ^ m with hg
  set Zξ : ℝ → ℝ := fun n =>
    boxIntegralXi β a b (Real.sqrt n) k h (fun u => (∏ i, u i ^ k i) * J u) with hZξ
  set Z : ℝ → ℝ := fun n => boxIntegralFin β a b (Real.sqrt n) k h with hZ
  set Z' : ℝ → ℝ := fun n => boxIntegralFin (β / 2) (2 * a) b (Real.sqrt n) k h with hZ'
  set Zη : ℝ → ℝ := fun n => boxIntegralXiEta β a b (Real.sqrt n) k h
    (fun u => (∏ i, u i ^ k i) * J u) (fun u => η₀ + (∏ i, u i ^ k i) * η u) with hZη
  -- |Zη − η₀ Z| ≤ (Lη(4/β+1) + |η₀| 4L)/√n · Z'
  have hdiff : (fun n : ℝ => Zη n - η₀ * Z n) =O[atTop] fun n : ℝ => n ^ (-(1 / 2 : ℝ)) * Z' n := by
    apply IsBigO.of_bound (Lη * (4 / β + 1) + |η₀| * (4 * L))
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (16 * L ^ 2)] with n hn hnL
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
    have hZ'0 : 0 ≤ Z' n := boxIntegralFin_nonneg _ _ _ _ _ _
    have h1 := boxIntegralXiEta_sub_le β a b hβ k h J η hJ hη η₀ L Lη hL hLη hJL hηL n hn hnL
    have h2 := boxIntegralXi_div_sub_le β a b hβ k h J hJ L hL hJL n hn hnL
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hn _),
      abs_of_nonneg hZ'0]
    have hpow : n ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt n := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hn.le]
      exact (one_div _).symm
    rw [hpow]
    calc |Zη n - η₀ * Z n| = |(Zη n - η₀ * Zξ n) + η₀ * (Zξ n - Z n)| := by ring_nf
      _ ≤ |Zη n - η₀ * Zξ n| + |η₀| * |Zξ n - Z n| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ Lη * (4 / β + 1) / Real.sqrt n * Z' n + |η₀| * (4 * L / Real.sqrt n * Z' n) := by
          gcongr
      _ = (Lη * (4 / β + 1) + |η₀| * (4 * L)) * (1 / Real.sqrt n * Z' n) := by ring
  have hsmall : (fun n : ℝ => n ^ (-(1 / 2 : ℝ)) * Z' n) =o[atTop] fun n : ℝ => η₀ * C * g n := by
    have h1 : (fun n : ℝ => n ^ (-(1 / 2 : ℝ))) =o[atTop] fun _ : ℝ => (1 : ℝ) :=
      (isLittleO_one_iff ℝ).2 (tendsto_rpow_neg_atTop (by norm_num))
    have h2 : Z' =O[atTop] g := hE'.isBigO.trans (isBigO_const_mul_self C' g atTop)
    have := h1.mul_isBigO h2
    refine (this.congr_right fun n => ?_).const_mul_right (mul_ne_zero hη₀ hC.ne')
    simp
  have hmain : (fun n : ℝ => η₀ * Z n) ~[atTop] fun n : ℝ => η₀ * C * g n := by
    have := (IsEquivalent.refl (u := fun _ : ℝ => η₀) (l := atTop)).mul hE
    refine (this.congr_left (Filter.Eventually.of_forall fun n => ?_)).congr_right
      (Filter.Eventually.of_forall fun n => ?_)
    · simp only [Pi.mul_apply]
    · simp only [Pi.mul_apply, hg]; ring
  have hsum := hmain.add_isLittleO (hdiff.trans_isLittleO hsmall)
  refine hsum.congr_left (Filter.Eventually.of_forall fun n => ?_)
  simp only [Pi.add_apply]
  ring

end Laplace.Grammar
