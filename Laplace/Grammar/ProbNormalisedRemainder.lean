/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.AmpCoeffJoint

/-!
# Convergence in distribution of the normalised remainders (grammar §4.3, Astra #11 rank 4)

For random Taylor data `X n : Ω → CoeffPair` bounded by `M`, measurable, converging in distribution
to `Z`, and a scale `N_n → ∞`, the ordered normalised remainders of the chart integral converge in
distribution to the limiting canonical coefficients:

* A-slot: `(Z_{N_n}(X n) − L_{<α}) / (N_n^{-α} log N_n) ⇒ A_α(Z)` (`tendstoInDistribution_normA`);
* B-slot: `(Z_{N_n}(X n) − L_{<α} − N_n^{-α} A_α(X n) log N_n) / N_n^{-α} ⇒ B_α(Z)`
  (`tendstoInDistribution_normB`), subtracting the CURRENT random `A_α(X n)`.

Proof: the normalised remainder equals the current coefficient plus a deterministic `o(1)` error
(units 148–149: uniform Taylor tree on the ball and the normalised-remainder bounds), the current
coefficient converges in distribution (unit 147), and Slutsky's theorem
(`TendstoInDistribution.add_of_tendstoInMeasure_const`) absorbs the error. This is the `d = 2`
chart-level form of the second conclusion of thm:strataempiricalexpansion for bounded analytic
families. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real

namespace Laplace.Grammar

/-- Every finite set of exponents has a gap above a given point. -/
theorem exists_gap (P : Finset ℝ) (α : ℝ) : ∃ δ : ℝ, 0 < δ ∧ ∀ γ ∈ P, α < γ → α + δ ≤ γ := by
  by_cases hne : (P.filter (α < ·)).Nonempty
  · obtain ⟨γ₀, hγ₀, hmin⟩ := Finset.exists_min_image (P.filter (α < ·)) (fun γ => γ - α) hne
    have hα₀ : α < γ₀ := (Finset.mem_filter.1 hγ₀).2
    refine ⟨γ₀ - α, by linarith, fun γ hγ hαγ => ?_⟩
    have := hmin γ (Finset.mem_filter.2 ⟨hγ, hαγ⟩)
    linarith
  · refine ⟨1, one_pos, fun γ hγ hαγ => ?_⟩
    exact absurd ⟨γ, Finset.mem_filter.2 ⟨hγ, hαγ⟩⟩ hne

/-- A uniform bound for all canonical coefficients with exponents in `P` on the ball `‖a‖ ≤ M`. -/
noncomputable def ballCoeffBound (β b ρ M : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (P : Finset ℝ) : ℝ :=
  ∑ γ ∈ P, (|canonCEnv ρ M h₁ h₂ k₁ k₂ γ * envMoment β γ 0 (gaussEnv β (2 * M) 0)|
    + |canonUEnv b ρ M h₁ h₂ k₁ k₂ γ * envMoment β γ 0 (gaussEnv β (2 * M) 0)
        + canonVEnv b ρ M h₁ h₂ k₁ k₂ γ * envMoment β γ 0 (gaussEnv β (2 * M) 0)
        + canonCEnv ρ M h₁ h₂ k₁ k₂ γ * envMoment β γ 1 (gaussEnv β (2 * M) 0)|)

theorem ballCoeffBound_nonneg (β b ρ M : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (P : Finset ℝ) :
    0 ≤ ballCoeffBound β b ρ M h₁ h₂ k₁ k₂ P :=
  Finset.sum_nonneg fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)

/-- Coefficient bounds on the ball. -/
theorem coeff_abs_le_ball (β b ρ M : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hM : 0 ≤ M) (P : Finset ℝ) (a : CoeffPair) (ha : ‖a‖ ≤ M)
    (γ : ℝ) (hγ : γ ∈ P) (hγ0 : 0 < γ) :
    |coeffA β ρ h₁ h₂ k₁ k₂ γ a| ≤ ballCoeffBound β b ρ M h₁ h₂ k₁ k₂ P
      ∧ |coeffB β b ρ h₁ h₂ k₁ k₂ γ a| ≤ ballCoeffBound β b ρ M h₁ h₂ k₁ k₂ P := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hx := wsummable_toX ρ hρ a
  have hy := wsummable_toY ρ hρ a
  have hMx : wnorm ρ (toX ρ a) ≤ M := (wnorm_toX_le_norm ρ hρ a).trans ha
  have hMy : wnorm ρ (toY ρ a) ≤ M := (wnorm_toY_le_norm ρ hρ a).trans ha
  have hA := canonA_abs_le_env (ampCoeff β (toX ρ a) (toY ρ a)) b ρ M (2 * M) β
    (ampEnv β ρ (toX ρ a) (toY ρ a)) h₁ h₂ k₁ k₂ 0 hβ hb hbρ hk₁ hk₂ (ampCoeff_continuous β _ _)
    (fun ij s => ampCoeff_abs_le β ρ hρ _ _ hx hy ij s)
    (fun s hs => ampEnv_le_common β ρ hβ hρ _ _ hx M M hMx hMy s hs) γ hγ0
  have hB := canonB_abs_le_env (ampCoeff β (toX ρ a) (toY ρ a)) b ρ M (2 * M) β
    (ampEnv β ρ (toX ρ a) (toY ρ a)) h₁ h₂ k₁ k₂ 0 hβ hb hbρ hk₁ hk₂ hM
    (ampCoeff_continuous β _ _) (ampEnv_continuous β ρ _ _)
    (fun ij s => ampCoeff_abs_le β ρ hρ _ _ hx hy ij s)
    (fun s hs => ampEnv_le_common β ρ hβ hρ _ _ hx M M hMx hMy s hs) γ hγ0
  have hle := Finset.single_le_sum (f := fun γ =>
      |canonCEnv ρ M h₁ h₂ k₁ k₂ γ * envMoment β γ 0 (gaussEnv β (2 * M) 0)|
      + |canonUEnv b ρ M h₁ h₂ k₁ k₂ γ * envMoment β γ 0 (gaussEnv β (2 * M) 0)
          + canonVEnv b ρ M h₁ h₂ k₁ k₂ γ * envMoment β γ 0 (gaussEnv β (2 * M) 0)
          + canonCEnv ρ M h₁ h₂ k₁ k₂ γ * envMoment β γ 1 (gaussEnv β (2 * M) 0)|)
    (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hγ
  unfold ballCoeffBound
  constructor
  · exact hA.trans ((le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans hle))
  · exact hB.trans ((le_abs_self _).trans ((le_add_of_nonneg_left (abs_nonneg _)).trans hle))

/-- The A-slot normalised remainder of the chart integral. -/
noncomputable def normA (β b ρ p₁ p₂ T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (α N : ℝ) (a : CoeffPair) : ℝ :=
  (chartZ β b ρ h₁ h₂ k₁ k₂ N a
      - lowerPart (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) (fun γ => coeffA β ρ h₁ h₂ k₁ k₂ γ a)
          (fun γ => coeffB β b ρ h₁ h₂ k₁ k₂ γ a) α N)
    / (N ^ (-α) * Real.log N)

/-- The B-slot normalised remainder (subtracting the current `A_α`). -/
noncomputable def normB (β b ρ p₁ p₂ T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (α N : ℝ) (a : CoeffPair) : ℝ :=
  (chartZ β b ρ h₁ h₂ k₁ k₂ N a
      - lowerPart (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) (fun γ => coeffA β ρ h₁ h₂ k₁ k₂ γ a)
          (fun γ => coeffB β b ρ h₁ h₂ k₁ k₂ γ a) α N
      - N ^ (-α) * (coeffA β ρ h₁ h₂ k₁ k₂ α a * Real.log N))
    / N ^ (-α)

/-- Deterministic A-slot bound on the ball. -/
theorem normA_sub_le (β b p₁ p₂ ρ T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (M : ℝ) (hM : 0 ≤ M) (a : CoeffPair) (ha : ‖a‖ ≤ M)
    (α : ℝ) (hα : α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) (δ : ℝ) (_hδ : 0 < δ)
    (hgap : ∀ γ ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T, α < γ → α + δ ≤ γ) (N : ℝ)
    (hN : Real.exp 1 ≤ N) :
    |normA β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α N a - coeffA β ρ h₁ h₂ k₁ k₂ α a|
      ≤ errA |uniformTreeConst β b ρ M (2 * M) p₁ p₂ T h₁ h₂ k₁ k₂ 0|
          (ballCoeffBound β b ρ M h₁ h₂ k₁ k₂ (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T)) (2 * T) α δ
          (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) N := by
  unfold normA
  refine normalised_A_le (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) (fun γ => coeffA β ρ h₁ h₂ k₁ k₂ γ a)
    (fun γ => coeffB β b ρ h₁ h₂ k₁ k₂ γ a) (fun N => chartZ β b ρ h₁ h₂ k₁ k₂ N a) _ _ (2 * T) α δ
    (abs_nonneg _) (ballCoeffBound_nonneg _ _ _ _ _ _ _ _ _) hα hgap (fun N hN1 => ?_)
    (fun γ hγ => coeff_abs_le_ball β b ρ M h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hM _ a ha γ hγ
      (pos_of_mem_polesBelowGen h₁ h₂ k₁ k₂ hk₁ hk₂ p₁ p₂ T γ hγ)) N hN
  have h := chartZ_taylor_tree_ball β b p₁ p₂ ρ h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ M hM a ha T
    N hN1
  refine h.trans (mul_le_mul_of_nonneg_right (le_abs_self _) ?_)
  have := Real.log_nonneg hN1
  have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ N) (-(2 * T))
  positivity

/-- Deterministic B-slot bound on the ball. -/
theorem normB_sub_le (β b p₁ p₂ ρ T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b) (hbρ : b < ρ)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (M : ℝ) (hM : 0 ≤ M) (a : CoeffPair) (ha : ‖a‖ ≤ M)
    (α : ℝ) (hα : α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) (δ : ℝ) (_hδ : 0 < δ)
    (hgap : ∀ γ ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T, α < γ → α + δ ≤ γ) (N : ℝ)
    (hN : Real.exp 1 ≤ N) :
    |normB β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α N a - coeffB β b ρ h₁ h₂ k₁ k₂ α a|
      ≤ errB |uniformTreeConst β b ρ M (2 * M) p₁ p₂ T h₁ h₂ k₁ k₂ 0|
          (ballCoeffBound β b ρ M h₁ h₂ k₁ k₂ (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T)) (2 * T) α δ
          (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) N := by
  unfold normB
  refine normalised_B_le (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) (fun γ => coeffA β ρ h₁ h₂ k₁ k₂ γ a)
    (fun γ => coeffB β b ρ h₁ h₂ k₁ k₂ γ a) (fun N => chartZ β b ρ h₁ h₂ k₁ k₂ N a) _ _ (2 * T) α δ
    (abs_nonneg _) (ballCoeffBound_nonneg _ _ _ _ _ _ _ _ _) hα hgap (fun N hN1 => ?_)
    (fun γ hγ => coeff_abs_le_ball β b ρ M h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hM _ a ha γ hγ
      (pos_of_mem_polesBelowGen h₁ h₂ k₁ k₂ hk₁ hk₂ p₁ p₂ T γ hγ)) N hN
  have h := chartZ_taylor_tree_ball β b p₁ p₂ ρ h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ M hM a ha T
    N hN1
  refine h.trans (mul_le_mul_of_nonneg_right (le_abs_self _) ?_)
  have := Real.log_nonneg hN1
  have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ N) (-(2 * T))
  positivity

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_lowerPart_comp (β b ρ r p₁ p₂ T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (α N : ℝ)
    (X : Ω → CoeffPair) (hX : Measurable X) :
    Measurable fun ω => lowerPart (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T)
      (fun γ => coeffA β ρ h₁ h₂ k₁ k₂ γ (X ω)) (fun γ => coeffB β b ρ h₁ h₂ k₁ k₂ γ (X ω))
      α N := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 < r := lt_trans hb hbr
  unfold lowerPart
  refine Finset.measurable_sum _ fun γ hγ => ?_
  have hγ0 : 0 < γ := pos_of_mem_polesBelowGen h₁ h₂ k₁ k₂ hk₁ hk₂ p₁ p₂ T γ
    (Finset.mem_filter.1 hγ).1
  exact measurable_const.mul
    ((((measurable_coeffA β ρ r h₁ h₂ k₁ k₂ hβ hρ hr0 hrρ hk₁ hk₂ γ hγ0).comp hX).mul
      measurable_const).add
      ((measurable_coeffB β b ρ r h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ γ hγ0).comp hX))

theorem measurable_normA_comp (β b ρ r p₁ p₂ T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (α N : ℝ)
    (X : Ω → CoeffPair) (hX : Measurable X) :
    Measurable fun ω => normA β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α N (X ω) := by
  unfold normA
  exact ((measurable_chartZ_comp β b ρ h₁ h₂ k₁ k₂ hb hbρ N X hX).sub
    (measurable_lowerPart_comp β b ρ r p₁ p₂ T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ α N X
      hX)).div_const _

theorem measurable_normB_comp (β b ρ r p₁ p₂ T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (α : ℝ) (hα : 0 < α)
    (N : ℝ) (X : Ω → CoeffPair) (hX : Measurable X) :
    Measurable fun ω => normB β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α N (X ω) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 < r := lt_trans hb hbr
  unfold normB
  exact (((measurable_chartZ_comp β b ρ h₁ h₂ k₁ k₂ hb hbρ N X hX).sub
    (measurable_lowerPart_comp β b ρ r p₁ p₂ T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ α N
      X hX)).sub
    (measurable_const.mul
      (((measurable_coeffA β ρ r h₁ h₂ k₁ k₂ hβ hρ hr0 hrρ hk₁ hk₂ α hα).comp hX).mul
        measurable_const))).div_const _

/-- A sequence dominated by a deterministic null sequence converges to `0` in measure. -/
theorem tendstoInMeasure_of_eventually_abs_le {ι : Type*} {l : Filter ι} (μ : Measure Ω)
    (f : ι → Ω → ℝ) (e : ι → ℝ) (he : Tendsto e l (𝓝 0))
    (hf : ∀ᶠ n in l, ∀ ω, |f n ω| ≤ e n) : TendstoInMeasure μ f l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hev : ∀ᶠ n in l, μ {ω | ε ≤ ‖f n ω - 0‖} = 0 := by
    filter_upwards [hf, he.eventually (gt_mem_nhds hε)] with n hn hlt
    have : {ω | ε ≤ ‖f n ω - 0‖} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le, sub_zero,
        Real.norm_eq_abs]
      exact lt_of_le_of_lt (hn ω) hlt
    rw [this, measure_empty]
  exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)

end Measurability

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}
  [l.IsCountablyGenerated]

/-- **A-slot: the normalised remainder converges in distribution to the limiting log coefficient**
(bounded analytic families). -/
theorem tendstoInDistribution_normA (β b p₁ p₂ ρ r T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (M : ℝ) (hM : 0 ≤ M)
    (X : ι → Ω → CoeffPair) (hXm : ∀ n, Measurable (X n)) (hXb : ∀ n ω, ‖X n ω‖ ≤ M)
    (Z : Ω' → CoeffPair) (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) (α : ℝ) (hα : α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) :
    TendstoInDistribution (fun n ω => normA β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α (Nseq n) (X n ω)) l
      (coeffA β ρ h₁ h₂ k₁ k₂ α ∘ Z) (fun _ => μ) μ' := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 < r := lt_trans hb hbr
  obtain ⟨δ, hδ, hgap⟩ := exists_gap (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) α
  have hα0 : 0 < α := pos_of_mem_polesBelowGen h₁ h₂ k₁ k₂ hk₁ hk₂ p₁ p₂ T α hα
  have hαT : α < 2 * T := ((mem_polesBelowGen_iff h₁ h₂ k₁ k₂ hk₁ hk₂ p₁ p₂ T hp₁ hp₂ α).1 hα).1
  have hA := tendstoInDistribution_coeffA β ρ r h₁ h₂ k₁ k₂ hβ hρ hr0 hrρ hk₁ hk₂ α hα0 X Z hX
  have herr : TendstoInMeasure μ (fun n ω => normA β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α (Nseq n) (X n ω)
      - coeffA β ρ h₁ h₂ k₁ k₂ α (X n ω)) l (fun _ => 0) := by
    refine tendstoInMeasure_of_eventually_abs_le μ _
      (fun n => errA |uniformTreeConst β b ρ M (2 * M) p₁ p₂ T h₁ h₂ k₁ k₂ 0|
        (ballCoeffBound β b ρ M h₁ h₂ k₁ k₂ (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T)) (2 * T) α δ
        (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) (Nseq n))
      ((tendsto_errA _ _ _ _ _ _ hαT hδ).comp hN) ?_
    filter_upwards [hN.eventually_ge_atTop (Real.exp 1)] with n hn ω
    exact normA_sub_le β b p₁ p₂ ρ T h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ M hM (X n ω) (hXb n ω)
      α hα δ hδ hgap (Nseq n) hn
  have hmeas : ∀ n, AEMeasurable (fun ω => normA β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α (Nseq n) (X n ω)
      - coeffA β ρ h₁ h₂ k₁ k₂ α (X n ω)) μ := fun n =>
    ((measurable_normA_comp β b ρ r p₁ p₂ T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ α (Nseq n) (X n)
      (hXm n)).sub
      ((measurable_coeffA β ρ r h₁ h₂ k₁ k₂ hβ hρ hr0 hrρ hk₁ hk₂ α hα0).comp (hXm n))).aemeasurable
  have h := hA.add_of_tendstoInMeasure_const herr hmeas
  refine h.congr (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
  · simp only [Pi.add_apply, Function.comp]; ring
  · simp

/-- **B-slot: the normalised remainder (after removing the current `A_α`) converges in
distribution to the limiting constant coefficient** (bounded analytic families). -/
theorem tendstoInDistribution_normB (β b p₁ p₂ ρ r T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (M : ℝ) (hM : 0 ≤ M)
    (X : ι → Ω → CoeffPair) (hXm : ∀ n, Measurable (X n)) (hXb : ∀ n ω, ‖X n ω‖ ≤ M)
    (Z : Ω' → CoeffPair) (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) (α : ℝ) (hα : α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) :
    TendstoInDistribution (fun n ω => normB β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α (Nseq n) (X n ω)) l
      (coeffB β b ρ h₁ h₂ k₁ k₂ α ∘ Z) (fun _ => μ) μ' := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 < r := lt_trans hb hbr
  obtain ⟨δ, hδ, hgap⟩ := exists_gap (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) α
  have hα0 : 0 < α := pos_of_mem_polesBelowGen h₁ h₂ k₁ k₂ hk₁ hk₂ p₁ p₂ T α hα
  have hαT : α < 2 * T := ((mem_polesBelowGen_iff h₁ h₂ k₁ k₂ hk₁ hk₂ p₁ p₂ T hp₁ hp₂ α).1 hα).1
  have hB := tendstoInDistribution_coeffB β b ρ r h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ α hα0 X Z
    hX
  have herr : TendstoInMeasure μ (fun n ω => normB β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α (Nseq n) (X n ω)
      - coeffB β b ρ h₁ h₂ k₁ k₂ α (X n ω)) l (fun _ => 0) := by
    refine tendstoInMeasure_of_eventually_abs_le μ _
      (fun n => errB |uniformTreeConst β b ρ M (2 * M) p₁ p₂ T h₁ h₂ k₁ k₂ 0|
        (ballCoeffBound β b ρ M h₁ h₂ k₁ k₂ (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T)) (2 * T) α δ
        (polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) (Nseq n))
      ((tendsto_errB _ _ _ _ _ _ hαT hδ).comp hN) ?_
    filter_upwards [hN.eventually_ge_atTop (Real.exp 1)] with n hn ω
    exact normB_sub_le β b p₁ p₂ ρ T h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ M hM (X n ω) (hXb n ω)
      α hα δ hδ hgap (Nseq n) hn
  have hmeas : ∀ n, AEMeasurable (fun ω => normB β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α (Nseq n) (X n ω)
      - coeffB β b ρ h₁ h₂ k₁ k₂ α (X n ω)) μ := fun n =>
    ((measurable_normB_comp β b ρ r p₁ p₂ T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ α hα0 (Nseq n)
      (X n) (hXm n)).sub
      ((measurable_coeffB β b ρ r h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ α hα0).comp
        (hXm n))).aemeasurable
  have h := hB.add_of_tendstoInMeasure_const herr hmeas
  refine h.congr (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
  · simp only [Pi.add_apply, Function.comp]; ring
  · simp

end Laplace.Grammar
