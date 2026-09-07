/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.FinitePartAxis

/-!
# The axis integral as a convergent coefficient series (grammar §4.2, analytic bridge)

The first genuinely infinite coefficient identity. If the one-variable amplitude has a convergent
expansion `Ψ(u, s) = ∑_i c_i(s) u^i` on `[0, b]` with the majorant `|c_i(s)| ρ^i ≤ H(s)` for some
`ρ > b`, then the axis integral of unit 87 is the absolutely convergent series

  `I_Ψ(s) = ∫₀^b (Ψ(u,s) − Ψ(0,s))/u du = ∑_{i≥1} c_i(s) b^i / i`   (`axisIntegral_hasSum`),

and, when `|w| H` is integrable against the Gaussian log weight, the constant coefficient of the
`d = 2` block is the absolutely convergent series (`axisB_series`, `twoDB_series`)

  `B = (k₁k₂)⁻¹(log B_* · M_{p,0}(c₀) − M_{p,1}(c₀)) + k₂⁻¹ ∑_{i≥1} (b^i/i) M_{p,0}(a_i)
       + k₁⁻¹ ∑_{j≥1} (b^j/j) M_{p,0}(b_j)`.

No convergence of the inverse-`N` expansion is asserted. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Finset

namespace Laplace.Grammar

/-- The majorant `|c_i| ρ^i ≤ H` gives the geometric bound `|c_i| b^i ≤ H (b/ρ)^i`. -/
theorem coeff_geometric_bound (c H b ρ : ℝ) (i : ℕ) (hb : 0 ≤ b) (hρ : 0 < ρ)
    (hmaj : |c| * ρ ^ i ≤ H) : |c| * b ^ i ≤ H * (b / ρ) ^ i := by
  have hρi : 0 < ρ ^ i := pow_pos hρ i
  rw [div_pow]
  calc |c| * b ^ i = (|c| * ρ ^ i) * (b ^ i / ρ ^ i) := by field_simp
    _ ≤ H * (b ^ i / ρ ^ i) := mul_le_mul_of_nonneg_right hmaj (by positivity)

/-- The constant term of a convergent expansion at `u = 0`. -/
theorem hasSum_zero_eq (c : ℕ → ℝ) (Ψ0 : ℝ) (h : HasSum (fun i => c i * (0 : ℝ) ^ i) Ψ0) :
    Ψ0 = c 0 := by
  have h0 : HasSum (fun i => c i * (0 : ℝ) ^ i) (c 0 * (0 : ℝ) ^ 0) :=
    hasSum_single 0 fun i hi => by simp [hi]
  rw [pow_zero, mul_one] at h0
  exact h.unique h0

/-- The shifted series `(Ψ(u) − Ψ(0))/u = ∑_i c_{i+1} u^i` for `u ≠ 0`. -/
theorem hasSum_shift_div (c : ℕ → ℝ) (Ψu Ψ0 u : ℝ) (hu : u ≠ 0)
    (h : HasSum (fun i => c i * u ^ i) Ψu) (h0 : Ψ0 = c 0) :
    HasSum (fun i => c (i + 1) * u ^ i) (u⁻¹ * (Ψu - Ψ0)) := by
  have h1 := (hasSum_nat_add_iff' (f := fun i => c i * u ^ i) 1).2 h
  simp only [Finset.sum_range_one, pow_zero, mul_one] at h1
  rw [h0]
  refine (h1.mul_left u⁻¹).congr_fun fun i => ?_
  rw [pow_succ]
  field_simp

/-- **The axis integral as a series**: `I_Ψ(s) = ∑_{i≥0} (b^{i+1}/(i+1)) c_{i+1}(s)`. -/
theorem axisIntegral_hasSum (b ρ : ℝ) (hb : 0 < b) (hbρ : b < ρ) (Ψ : ℝ → ℝ → ℝ)
    (c : ℕ → ℝ → ℝ) (H : ℝ → ℝ) (s : ℝ)
    (hΨ : ∀ u ∈ Icc (0 : ℝ) b, HasSum (fun i => c i s * u ^ i) (Ψ u s))
    (hmaj : ∀ i, |c i s| * ρ ^ i ≤ H s) :
    HasSum (fun i : ℕ => b ^ (i + 1) / ((i : ℝ) + 1) * c (i + 1) s) (axisIntegral b Ψ s) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 ≤ b / ρ := by positivity
  have hr1 : b / ρ < 1 := (div_lt_one hρ).2 hbρ
  have hH0 : 0 ≤ H s := (mul_nonneg (abs_nonneg _) (pow_nonneg hρ.le 0)).trans (hmaj 0)
  have hΨ0 : Ψ 0 s = c 0 s := hasSum_zero_eq (fun i => c i s) _ (hΨ 0 (left_mem_Icc.2 hb.le))
  -- the integrand is the shifted series
  have hpt : ∀ u ∈ Ioc (0 : ℝ) b, u⁻¹ * (Ψ u s - Ψ 0 s) = ∑' i, c (i + 1) s * u ^ i := by
    intro u hu
    exact (hasSum_shift_div (fun i => c i s) _ _ u hu.1.ne' (hΨ u (Ioc_subset_Icc_self hu))
      hΨ0).tsum_eq.symm
  -- termwise integrability and summable `L¹` norms on `(0, b]`
  have hint : ∀ i : ℕ,
      Integrable (fun u => c (i + 1) s * u ^ i) (volume.restrict (Ioc (0 : ℝ) b)) :=
    fun i => (continuous_const.mul (continuous_pow i)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hnorm : ∀ i : ℕ, ∫ u in Ioc (0 : ℝ) b, ‖c (i + 1) s * u ^ i‖ ≤ H s * (b / ρ) ^ (i + 1) := by
    intro i
    have hconst : IntegrableOn (fun _ : ℝ => |c (i + 1) s| * b ^ i) (Ioc 0 b) :=
      integrableOn_const measure_Ioc_lt_top.ne
    have hle : ∫ u in Ioc (0 : ℝ) b, ‖c (i + 1) s * u ^ i‖
        ≤ ∫ _u in Ioc (0 : ℝ) b, |c (i + 1) s| * b ^ i := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _) hconst ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
      beta_reduce
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hu.1]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu.1.le hu.2 i) (abs_nonneg _)
    rw [setIntegral_const, Real.volume_real_Ioc, sub_zero, max_eq_left hb.le, smul_eq_mul] at hle
    refine hle.trans ?_
    calc b * (|c (i + 1) s| * b ^ i) = |c (i + 1) s| * b ^ (i + 1) := by ring
      _ ≤ _ := coeff_geometric_bound (c (i + 1) s) (H s) b ρ (i + 1) hb.le hρ (hmaj (i + 1))
  have hsum : Summable fun i : ℕ => ∫ u in Ioc (0 : ℝ) b, ‖c (i + 1) s * u ^ i‖ := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun u => norm_nonneg _) hnorm ?_
    have := (summable_geometric_of_lt_one hr0 hr1).mul_left (H s * (b / ρ))
    refine this.congr fun i => ?_
    rw [pow_succ]; ring
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  -- identify both sides
  have hI : axisIntegral b Ψ s = ∫ u in Ioc (0 : ℝ) b, ∑' i, c (i + 1) s * u ^ i := by
    unfold axisIntegral
    exact setIntegral_congr_fun measurableSet_Ioc hpt
  rw [hI]
  refine h.congr_fun fun i => ?_
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hb.le, integral_pow,
    zero_pow (Nat.succ_ne_zero i), sub_zero]
  ring

/-- The pointwise sum of the series terms is dominated by `H (b/ρ)/(1 − b/ρ)`. -/
theorem axis_series_dominated (b ρ : ℝ) (hb : 0 < b) (hbρ : b < ρ) (c : ℕ → ℝ → ℝ) (H : ℝ → ℝ)
    (s : ℝ) (hmaj : ∀ i, |c i s| * ρ ^ i ≤ H s) :
    (Summable fun i : ℕ => |b ^ (i + 1) / ((i : ℝ) + 1) * c (i + 1) s|) ∧
      ∑' i : ℕ, |b ^ (i + 1) / ((i : ℝ) + 1) * c (i + 1) s| ≤ (b / ρ) / (1 - b / ρ) * H s := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 ≤ b / ρ := by positivity
  have hr1 : b / ρ < 1 := (div_lt_one hρ).2 hbρ
  have hH0 : 0 ≤ H s := (mul_nonneg (abs_nonneg _) (pow_nonneg hρ.le 0)).trans (hmaj 0)
  have hterm : ∀ i : ℕ,
      |b ^ (i + 1) / ((i : ℝ) + 1) * c (i + 1) s| ≤ H s * (b / ρ) * (b / ρ) ^ i := by
    intro i
    have hi : (1 : ℝ) ≤ (i : ℝ) + 1 := by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    have hbi : 0 ≤ b ^ (i + 1) := pow_nonneg hb.le _
    rw [abs_mul, abs_div, abs_of_nonneg hbi, abs_of_pos (by linarith : (0 : ℝ) < (i : ℝ) + 1)]
    have := coeff_geometric_bound (c (i + 1) s) (H s) b ρ (i + 1) hb.le hρ (hmaj (i + 1))
    calc b ^ (i + 1) / ((i : ℝ) + 1) * |c (i + 1) s| ≤ b ^ (i + 1) * |c (i + 1) s| := by
          rw [div_mul_eq_mul_div]
          exact div_le_self (by positivity) hi
      _ ≤ H s * (b / ρ) ^ (i + 1) := by rw [mul_comm]; exact this
      _ = _ := by rw [pow_succ]; ring
  have hgeo : Summable fun i : ℕ => H s * (b / ρ) * (b / ρ) ^ i :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hsumm : Summable fun i : ℕ => |b ^ (i + 1) / ((i : ℝ) + 1) * c (i + 1) s| :=
    Summable.of_nonneg_of_le (fun i => abs_nonneg _) hterm hgeo
  refine ⟨hsumm, ?_⟩
  calc ∑' i : ℕ, |b ^ (i + 1) / ((i : ℝ) + 1) * c (i + 1) s|
      ≤ ∑' i : ℕ, H s * (b / ρ) * (b / ρ) ^ i := hsumm.tsum_le_tsum hterm hgeo
    _ = H s * (b / ρ) * (1 - b / ρ)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ = _ := by ring

/-- **The log moment of the axis integral as a series.** -/
theorem axisIntegral_logMoment_hasSum (β p b ρ : ℝ) (hb : 0 < b) (hbρ : b < ρ) (Ψ : ℝ → ℝ → ℝ)
    (c : ℕ → ℝ → ℝ) (H : ℝ → ℝ) (hc : ∀ i, Measurable (c i))
    (hΨ : ∀ s, 0 < s → ∀ u ∈ Icc (0 : ℝ) b, HasSum (fun i => c i s * u ^ i) (Ψ u s))
    (hmaj : ∀ s, 0 < s → ∀ i, |c i s| * ρ ^ i ≤ H s)
    (hH : IntegrableOn (fun s => |momentWeight β p 0 s| * H s) (Ioi 0)) :
    HasSum (fun i : ℕ => b ^ (i + 1) / ((i : ℝ) + 1) * logMoment β p 0 (c (i + 1)))
      (logMoment β p 0 (axisIntegral b Ψ)) := by
  have hf : ∀ i : ℕ, Measurable fun s : ℝ => b ^ (i + 1) / ((i : ℝ) + 1) * c (i + 1) s :=
    fun i => measurable_const.mul (hc (i + 1))
  have hG : IntegrableOn (fun s => |momentWeight β p 0 s| * ((b / ρ) / (1 - b / ρ) * H s))
      (Ioi 0) := by
    have this : IntegrableOn (fun s => (b / ρ) / (1 - b / ρ) * (|momentWeight β p 0 s| * H s))
        (Ioi 0) := hH.const_mul ((b / ρ) / (1 - b / ρ))
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    ring
  have h := hasSum_logMoment_of_dominated β p 0
    (fun (i : ℕ) (s : ℝ) => b ^ (i + 1) / ((i : ℝ) + 1) * c (i + 1) s)
    hf (fun s => (b / ρ) / (1 - b / ρ) * H s)
    (fun s hs => (axis_series_dominated b ρ hb hbρ c H s (hmaj s hs)).1)
    (fun s hs => (axis_series_dominated b ρ hb hbρ c H s (hmaj s hs)).2) hG
  have hL : logMoment β p 0 (fun s => ∑' i : ℕ, b ^ (i + 1) / ((i : ℝ) + 1) * c (i + 1) s)
      = logMoment β p 0 (axisIntegral b Ψ) := by
    unfold logMoment
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    beta_reduce
    rw [(axisIntegral_hasSum b ρ hb hbρ Ψ c H s (hΨ s hs) (hmaj s hs)).tsum_eq]
  rw [hL] at h
  refine h.congr_fun fun i => ?_
  rw [logMoment_const_mul]

/-- The log moments of `Ψ(0, ·)` are those of `c₀`. -/
theorem logMoment_axis_zero (β p b : ℝ) (ℓ : ℕ) (hb : 0 < b) (Ψ : ℝ → ℝ → ℝ) (c : ℕ → ℝ → ℝ)
    (hΨ : ∀ s, 0 < s → ∀ u ∈ Icc (0 : ℝ) b, HasSum (fun i => c i s * u ^ i) (Ψ u s)) :
    logMoment β p ℓ (Ψ 0) = logMoment β p ℓ (c 0) := by
  unfold logMoment
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  rw [hasSum_zero_eq (fun i => c i s) _ (hΨ s hs 0 (left_mem_Icc.2 hb.le))]

/-- **The constant coefficient of the axis expansion as a convergent series.** -/
theorem axisB_series (β p b ρ : ℝ) (k₁ k₂ : ℕ) (hb : 0 < b) (hbρ : b < ρ) (Ψ : ℝ → ℝ → ℝ)
    (c : ℕ → ℝ → ℝ) (H : ℝ → ℝ) (hc : ∀ i, Measurable (c i))
    (hΨ : ∀ s, 0 < s → ∀ u ∈ Icc (0 : ℝ) b, HasSum (fun i => c i s * u ^ i) (Ψ u s))
    (hmaj : ∀ s, 0 < s → ∀ i, |c i s| * ρ ^ i ≤ H s)
    (hH : IntegrableOn (fun s => |momentWeight β p 0 s| * H s) (Ioi 0)) :
    axisB β b p k₁ k₂ Ψ
      = 1 / ((k₁ : ℝ) * k₂) * (Real.log (b ^ (k₁ + k₂)) * logMoment β p 0 (c 0)
          - logMoment β p 1 (c 0))
        + 1 / (k₂ : ℝ) * ∑' i : ℕ, b ^ (i + 1) / ((i : ℝ) + 1) * logMoment β p 0 (c (i + 1)) := by
  unfold axisB
  rw [logMoment_axis_zero β p b 0 hb Ψ c hΨ, logMoment_axis_zero β p b 1 hb Ψ c hΨ,
    (axisIntegral_logMoment_hasSum β p b ρ hb hbρ Ψ c H hc hΨ hmaj hH).tsum_eq]

/-- **The `d = 2` constant coefficient as two convergent axis series.** -/
theorem twoDB_series (β p b ρ : ℝ) (k₁ k₂ : ℕ) (hb : 0 < b) (hbρ : b < ρ) (Φ : ℝ → ℝ → ℝ → ℝ)
    (a c : ℕ → ℝ → ℝ) (H : ℝ → ℝ) (ha : ∀ i, Measurable (a i)) (hc : ∀ j, Measurable (c j))
    (hΦu : ∀ s, 0 < s → ∀ u ∈ Icc (0 : ℝ) b, HasSum (fun i => a i s * u ^ i) (Φ u 0 s))
    (hΦv : ∀ s, 0 < s → ∀ v ∈ Icc (0 : ℝ) b, HasSum (fun j => c j s * v ^ j) (Φ 0 v s))
    (hmaja : ∀ s, 0 < s → ∀ i, |a i s| * ρ ^ i ≤ H s)
    (hmajc : ∀ s, 0 < s → ∀ j, |c j s| * ρ ^ j ≤ H s)
    (hH : IntegrableOn (fun s => |momentWeight β p 0 s| * H s) (Ioi 0)) :
    twoDB β b p k₁ k₂ Φ
      = 1 / ((k₁ : ℝ) * k₂) * (Real.log (b ^ (k₁ + k₂)) * logMoment β p 0 (a 0)
          - logMoment β p 1 (a 0))
        + 1 / (k₂ : ℝ) * ∑' i : ℕ, b ^ (i + 1) / ((i : ℝ) + 1) * logMoment β p 0 (a (i + 1))
        + 1 / (k₁ : ℝ) * ∑' j : ℕ, b ^ (j + 1) / ((j : ℝ) + 1) * logMoment β p 0 (c (j + 1)) := by
  unfold twoDB
  have h0 : (fun s => Φ 0 0 s) = (fun u s => Φ u 0 s) 0 := rfl
  rw [h0, logMoment_axis_zero β p b 0 hb (fun u s => Φ u 0 s) a hΦu,
    logMoment_axis_zero β p b 1 hb (fun u s => Φ u 0 s) a hΦu,
    (axisIntegral_logMoment_hasSum β p b ρ hb hbρ (fun u s => Φ u 0 s) a H ha hΦu hmaja hH).tsum_eq,
    (axisIntegral_logMoment_hasSum β p b ρ hb hbρ (fun v s => Φ 0 v s) c H hc hΦv hmajc hH).tsum_eq]

end Laplace.Grammar
