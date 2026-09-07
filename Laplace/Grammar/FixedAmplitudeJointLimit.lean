/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.PositiveDenominatorRatio

/-!
# Joint limit of the normalised chart integrals for deterministic amplitudes (grammar §4.3)

In the paper's §4.3 only the phase `ξ_n` is random; the amplitudes `η_φ = φ·prior·Jacobian` and
`η_1 = prior·Jacobian` are deterministic. We model this by the map `withY y : CoeffPair → CoeffPair`
that keeps the phase data of `a` and replaces the amplitude data by a fixed array `y`
(1-Lipschitz, `continuous_withY`). For equal starting exponents `p` the leading exponent has no
lower terms (`lowerPart_leading_eq_zero`), and the pair of normalised chart integrals
`(Z_{N_n}[φ]/s_n, Z_{N_n}[1]/s_n)`, `s_n = N_n^{−p} log N_n`, converges jointly in distribution to
`(A_p(X; y_φ), A_p(X; y_1))` whenever the random phase data converge in distribution
(`tendstoInDistribution_normA_pair`). Astra #13 unit u158. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real

namespace Laplace.Grammar

/-- Replace the amplitude data of `a` by the fixed array `y`. -/
noncomputable def withY (ρ : ℝ) (hρ : 0 < ρ) (y : ℕ × ℕ → ℝ) (hy : WSummable ρ y) (a : CoeffPair) :
    CoeffPair :=
  ofPair ρ hρ (toX ρ a) y (wsummable_toX ρ hρ a) hy

theorem toX_withY (ρ : ℝ) (hρ : 0 < ρ) (y : ℕ × ℕ → ℝ) (hy : WSummable ρ y) (a : CoeffPair) :
    toX ρ (withY ρ hρ y hy a) = toX ρ a :=
  toX_ofPair ρ hρ _ _ _ _

theorem toY_withY (ρ : ℝ) (hρ : 0 < ρ) (y : ℕ × ℕ → ℝ) (hy : WSummable ρ y) (a : CoeffPair) :
    toY ρ (withY ρ hρ y hy a) = y :=
  toY_ofPair ρ hρ _ _ _ _

theorem withY_apply_inl (ρ : ℝ) (hρ : 0 < ρ) (y : ℕ × ℕ → ℝ) (hy : WSummable ρ y) (a : CoeffPair)
    (k : ℕ × ℕ) : (withY ρ hρ y hy a : PairIdx → ℝ) (Sum.inl k) = a (Sum.inl k) := by
  change toX ρ a k * ρ ^ (k.1 + k.2) = a (Sum.inl k)
  unfold toX
  exact div_mul_cancel₀ _ (pow_pos hρ _).ne'

theorem withY_apply_inr (ρ : ℝ) (hρ : 0 < ρ) (y : ℕ × ℕ → ℝ) (hy : WSummable ρ y) (a : CoeffPair)
    (k : ℕ × ℕ) : (withY ρ hρ y hy a : PairIdx → ℝ) (Sum.inr k) = y k * ρ ^ (k.1 + k.2) := rfl

/-- `withY` is 1-Lipschitz. -/
theorem norm_withY_sub_le (ρ : ℝ) (hρ : 0 < ρ) (y : ℕ × ℕ → ℝ) (hy : WSummable ρ y)
    (a a' : CoeffPair) : ‖withY ρ hρ y hy a - withY ρ hρ y hy a'‖ ≤ ‖a - a'‖ := by
  rw [norm_eq_tsum_abs, norm_eq_tsum_abs]
  refine (summable_abs_coeff _).tsum_le_tsum (fun i => ?_) (summable_abs_coeff _)
  rw [lp.coeFn_sub, lp.coeFn_sub, Pi.sub_apply, Pi.sub_apply]
  rcases i with k | k
  · rw [withY_apply_inl, withY_apply_inl]
  · rw [withY_apply_inr, withY_apply_inr, sub_self, abs_zero]
    exact abs_nonneg _

theorem lipschitzWith_withY (ρ : ℝ) (hρ : 0 < ρ) (y : ℕ × ℕ → ℝ) (hy : WSummable ρ y) :
    LipschitzWith 1 (withY ρ hρ y hy) :=
  LipschitzWith.of_dist_le_mul fun a a' => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact norm_withY_sub_le ρ hρ y hy a a'

theorem continuous_withY (ρ : ℝ) (hρ : 0 < ρ) (y : ℕ × ℕ → ℝ) (hy : WSummable ρ y) :
    Continuous (withY ρ hρ y hy) :=
  (lipschitzWith_withY ρ hρ y hy).continuous

theorem measurable_withY (ρ : ℝ) (hρ : 0 < ρ) (y : ℕ × ℕ → ℝ) (hy : WSummable ρ y) :
    Measurable (withY ρ hρ y hy) :=
  (continuous_withY ρ hρ y hy).measurable

/-- The leading exponent has no lower terms. -/
theorem lowerPart_leading_eq_zero (h₁ h₂ k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (p T : ℝ)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (A B : ℝ → ℝ) (N : ℝ) :
    lowerPart (polesBelowGen h₁ h₂ k₁ k₂ p p T) A B p N = 0 := by
  unfold lowerPart
  have : (polesBelowGen h₁ h₂ k₁ k₂ p p T).filter (· < p) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro γ hγ
    have := min_le_of_mem_polesBelowGen h₁ h₂ k₁ k₂ hk₁ hk₂ p p T hp₁ hp₂ γ hγ
    rw [min_self] at this
    exact not_lt.2 this
  rw [this, Finset.sum_empty]

/-- Componentwise convergence in measure to `0` gives convergence of the pair. -/
theorem tendstoInMeasure_prodMk_zero {ι Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {l : Filter ι} (f g : ι → Ω → ℝ) (hf : TendstoInMeasure μ f l (fun _ => 0))
    (hg : TendstoInMeasure μ g l (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => (f n ω, g n ω)) l (fun _ => ((0 : ℝ), (0 : ℝ))) := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro ε hε
  have h := (hf ε hε).add (hg ε hε)
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    fun n => ?_
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  rw [Prod.mk_sub_mk, Prod.norm_def, sub_zero, sub_zero] at hω
  rcases le_max_iff.1 hω with h1 | h1
  · exact Or.inl (by simpa using h1)
  · exact Or.inr (by simpa using h1)

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}
  [l.IsCountablyGenerated]

omit [l.IsCountablyGenerated] in
/-- Error term of the leading normalised chart integral with a fixed amplitude tends to zero in
probability, for random phase data converging in distribution. -/
theorem tendstoInMeasure_normA_withY_sub (β b p ρ r T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (_hbr : b < r) (_hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (hpT : p < 2 * T)
    (y : ℕ × ℕ → ℝ) (hy : WSummable ρ y) (X : ι → Ω → CoeffPair) (Z : Ω' → CoeffPair)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInMeasure μ (fun n ω =>
        normA β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ (lt_trans hb hbρ) y hy (X n ω))
          - coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ (lt_trans hb hbρ) y hy (X n ω))) l (fun _ => 0) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hα : p ∈ polesBelowGen h₁ h₂ k₁ k₂ p p T :=
    (mem_polesBelowGen_iff h₁ h₂ k₁ k₂ hk₁ hk₂ p p T hp₁ hp₂ p).2
      ⟨hpT, Or.inl ⟨0, uExp_zero h₁ k₁ p hp₁⟩⟩
  obtain ⟨δ, hδ, hgap⟩ := exists_gap (polesBelowGen h₁ h₂ k₁ k₂ p p T) p
  have hX' : TendstoInDistribution (fun n => withY ρ hρ y hy ∘ X n) l (withY ρ hρ y hy ∘ Z)
      (fun _ => μ) μ' := hX.continuous_comp (continuous_withY ρ hρ y hy)
  have htight := normBounded_of_tendstoInDistribution _ _ hX'
  have h := tendstoInMeasure_zero_of_tight μ
    (fun n ω => normA β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ hρ y hy (X n ω))
      - coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ hρ y hy (X n ω)))
    (fun n => withY ρ hρ y hy ∘ X n)
    (fun M n => errA |uniformTreeConst β b ρ M (2 * M) p p T h₁ h₂ k₁ k₂ 0|
      (ballCoeffBound β b ρ M h₁ h₂ k₁ k₂ (polesBelowGen h₁ h₂ k₁ k₂ p p T)) (2 * T) p δ
      (polesBelowGen h₁ h₂ k₁ k₂ p p T) (Nseq n))
    (fun M _ => (tendsto_errA _ _ _ _ _ _ hpT hδ).comp hN) (fun M hM => ?_) htight
  · exact h
  · filter_upwards [hN.eventually_ge_atTop (Real.exp 1)] with n hn ω hω
    exact normA_sub_le β b p p ρ T h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ M hM _ hω p hα δ hδ hgap
      (Nseq n) hn

/-- **Joint convergence of the normalised chart integrals** for two deterministic amplitudes
`y_φ, y_1` and a common random phase. -/
theorem tendstoInDistribution_normA_pair (β b p ρ r T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (hpT : p < 2 * T)
    (yφ y₁ : ℕ × ℕ → ℝ) (hyφ : WSummable ρ yφ) (hy₁ : WSummable ρ y₁)
    (X : ι → Ω → CoeffPair) (hXm : ∀ n, Measurable (X n)) (Z : Ω' → CoeffPair)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInDistribution (fun n ω =>
        (normA β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ (lt_trans hb hbρ) yφ hyφ (X n ω)),
          normA β b ρ p p T h₁ h₂ k₁ k₂ p (Nseq n) (withY ρ (lt_trans hb hbρ) y₁ hy₁ (X n ω)))) l
      (fun ω => (coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ (lt_trans hb hbρ) yφ hyφ (Z ω)),
        coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ (lt_trans hb hbρ) y₁ hy₁ (Z ω)))) (fun _ => μ) μ' := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 < r := lt_trans hb hbr
  have hp0 : 0 < p := by
    rw [← hp₁]; have : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
    positivity
  -- the coefficient pair converges by the continuous mapping theorem
  have hg : Continuous fun a : CoeffPair =>
      (coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ hρ yφ hyφ a),
        coeffA β ρ h₁ h₂ k₁ k₂ p (withY ρ hρ y₁ hy₁ a)) :=
    ((continuous_coeffA β ρ r h₁ h₂ k₁ k₂ hβ hρ hr0 hrρ hk₁ hk₂ p hp0).comp
      (continuous_withY ρ hρ yφ hyφ)).prodMk
      ((continuous_coeffA β ρ r h₁ h₂ k₁ k₂ hβ hρ hr0 hrρ hk₁ hk₂ p hp0).comp
        (continuous_withY ρ hρ y₁ hy₁))
  have hA := hX.continuous_comp hg
  -- the errors tend to zero in probability
  have hEφ := tendstoInMeasure_normA_withY_sub β b p ρ r T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂
    hp₁ hp₂ hpT yφ hyφ X Z hX Nseq hN
  have hE₁ := tendstoInMeasure_normA_withY_sub β b p ρ r T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂
    hp₁ hp₂ hpT y₁ hy₁ X Z hX Nseq hN
  have hE := tendstoInMeasure_prodMk_zero μ _ _ hEφ hE₁
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hA ?_ fun n => ?_
  · exact hE
  · exact ((measurable_normA_comp β b ρ r p p T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ p (Nseq n) _
        ((measurable_withY ρ hρ yφ hyφ).comp (hXm n))).prodMk
      (measurable_normA_comp β b ρ r p p T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ p (Nseq n) _
        ((measurable_withY ρ hρ y₁ hy₁).comp (hXm n)))).aemeasurable

end Laplace.Grammar
