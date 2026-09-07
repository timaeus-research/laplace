/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.KernelTaylor

/-!
# The one-dimensional second-order term (grammar §4.2, `thm:TaylorTree` at `d = 1`)

For `Z(N) = ∫₀^b u^h η(u) e^{-β(Nu^k)² + β N u^k ξ(u)} du` with `ξ, η` admitting first-order Taylor
expansions at `0` with quadratic remainders, the density-transfer theorem (unit 83) applied to the
exact density `ρ(r, s) = k⁻¹ r^{p-1} η(r^{1/k}) e^{βsξ(r^{1/k})}` and the kernel Taylor bound
(unit 84) give, for `N ≥ 1`,

  `Z(N) = C₀ N^{-p} + C₁ N^{-q} + O(N^{-(h+3)/k})`,  `p = (h+1)/k`, `q = (h+2)/k`,
  `C₀ = k⁻¹ η(0) S_p(a)`,  `C₁ = k⁻¹ (η'(0) S_q(a) + β η(0) ξ'(0) S_{q+1}(a))`,

where `S_λ(a) = ∫₀^∞ s^{λ-1} e^{-βs²+βas} ds = weightedMass β a (λ-1)` and `a = ξ(0)`
(`oneDScale_second_order`). At `N = √n` the exponents are `n^{-p/2}`, `n^{-q/2}`, `n^{-(h+3)/(2k)}`.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology Asymptotics

namespace Laplace.Grammar

/-- The exact one-dimensional density `ρ(r, s) = k⁻¹ r^{p-1} η(r^{1/k}) e^{βsξ(r^{1/k})}`. -/
noncomputable def oneDDensity (β p : ℝ) (k : ℕ) (ξ η : ℝ → ℝ) (r s : ℝ) : ℝ :=
  1 / (k : ℝ) * r ^ (p - 1) * (η (r ^ ((k : ℝ)⁻¹)) * Real.exp (β * s * ξ (r ^ ((k : ℝ)⁻¹))))

/-- **The chart integral is a transfer integral** with the exact density. -/
theorem oneDScale_eq_transferZ (β b N : ℝ) (h k : ℕ) (hk : 0 < k) (hb : 0 < b) (ξ η : ℝ → ℝ) :
    oneDScale β b N h k ξ η
      = transferZ (oneDDensity β (((h : ℝ) + 1) / k) k ξ η) β (b ^ k) N := by
  unfold oneDScale transferZ oneDDensity
  set g : ℝ → ℝ := fun x => η (x ^ ((k : ℝ)⁻¹))
    * Real.exp (-β * (N * x) ^ 2 + β * (N * x) * ξ (x ^ ((k : ℝ)⁻¹))) with hg
  have hpt : ∀ u ∈ Ioc (0 : ℝ) b,
      u ^ h * η u * Real.exp (-β * (N * u ^ k) ^ 2 + β * (N * u ^ k) * ξ u)
        = u ^ h * g (u ^ k) := by
    intro u hu
    simp only [hg]
    rw [Real.pow_rpow_inv_natCast hu.1.le hk.ne']
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_Ioc_pow_mul_comp_pow h k b g hk hb,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun r _ => ?_
  simp only [hg]
  rw [show Real.exp (-β * (N * r) ^ 2 + β * (N * r) * ξ (r ^ ((k : ℝ)⁻¹)))
    = Real.exp (-β * (N * r) ^ 2) * Real.exp (β * (N * r) * ξ (r ^ ((k : ℝ)⁻¹))) by
      rw [← Real.exp_add]]
  ring

/-- The leading coefficient function `c₀(s) = k⁻¹ η₀ e^{βsa}`. -/
noncomputable def oneDCoeff₀ (β a η₀ : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  1 / (k : ℝ) * (η₀ * Real.exp (β * s * a))

/-- The second coefficient function `c₁(s) = k⁻¹ e^{βsa}(η₁ + βs η₀ a₁)`. -/
noncomputable def oneDCoeff₁ (β a a₁ η₀ η₁ : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  1 / (k : ℝ) * (Real.exp (β * s * a) * (η₁ + β * s * η₀ * a₁))

/-- The remainder envelope `H(s) = C k⁻¹ (1+s)² e^{3βLs}`. -/
noncomputable def oneDEnvelope (β L C : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  C / (k : ℝ) * ((1 + s) ^ 2 * Real.exp (3 * β * L * s))

/-- `e^{-βs²} e^{βsa} = quadKernel β a s`. -/
theorem exp_mul_exp_eq_quadKernel (β a s : ℝ) :
    Real.exp (-β * s ^ 2) * Real.exp (β * s * a) = quadKernel β a s := by
  unfold quadKernel; rw [← Real.exp_add]; ring_nf

/-- The zeroth log moment of `κ e^{βsa}` is `κ S_α(a)`. -/
theorem logMoment_const_exp (β α a κ : ℝ) :
    logMoment β α 0 (fun s => κ * Real.exp (β * s * a)) = κ * weightedMass β a (α - 1) := by
  unfold logMoment weightedMass
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [pow_zero, mul_one, ← exp_mul_exp_eq_quadKernel]
  ring

/-- The zeroth log moment of the second coefficient. -/
theorem logMoment_oneDCoeff₁ (β α a a₁ η₀ η₁ : ℝ) (k : ℕ) (hβ : 0 < β) (hα : 0 < α) :
    logMoment β α 0 (oneDCoeff₁ β a a₁ η₀ η₁ k)
      = 1 / (k : ℝ) * (η₁ * weightedMass β a (α - 1) + β * η₀ * a₁ * weightedMass β a α) := by
  unfold logMoment oneDCoeff₁ weightedMass
  have h1 := weightedKernel_integrableOn β a (α - 1) hβ (by linarith)
  have h2 := weightedKernel_integrableOn β a α hβ (by linarith)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h1.const_mul _) (h2.const_mul _),
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  have hsα : s ^ α = s ^ (α - 1) * s := by
    rw [← Real.rpow_add_one hs0.ne']; ring_nf
  rw [pow_zero, mul_one, hsα]
  have hq := exp_mul_exp_eq_quadKernel β a s
  rw [← hq]
  ring

/-- Positivity of the Taylor constant used below. -/
theorem taylorConst_nonneg (β b K M M₁ L₁ : ℝ) (hβ : 0 < β) (hb : 0 < b) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hM₁ : 0 ≤ M₁) (hL₁ : 0 ≤ L₁) :
    0 ≤ K + M₁ * (L₁ + K * b) * β + 3 * M * β ^ 2 * (L₁ + K * b) ^ 2 + β * K * M := by
  positivity

/-- **The density expansion of the one-dimensional density** to second order. -/
theorem oneDDensity_expansion (β b L K M M₁ L₁ a a₁ η₀ η₁ : ℝ) (h k : ℕ) (ξ η : ℝ → ℝ)
    (hβ : 0 < β) (hb : 0 < b) (hk : 0 < k) (hK : 0 ≤ K) (hM : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hL₁ : 0 ≤ L₁)
    (hξc : Continuous ξ) (hηc : Continuous η)
    (hξL : ∀ u ∈ Icc (0 : ℝ) b, |ξ u| ≤ L) (hη₀ : |η₀| ≤ M) (hη₁ : |η₁| ≤ M₁) (ha₁ : |a₁| ≤ L₁)
    (hξT : ∀ u ∈ Icc (0 : ℝ) b, |ξ u - a - u * a₁| ≤ K * u ^ 2)
    (hηT : ∀ u ∈ Icc (0 : ℝ) b, |η u - η₀ - u * η₁| ≤ K * u ^ 2) :
    DensityExpansion (oneDDensity β (((h : ℝ) + 1) / k) k ξ η)
      ![((h : ℝ) + 1) / k, ((h : ℝ) + 2) / k] ![0, 0]
      ![oneDCoeff₀ β a η₀ k, oneDCoeff₁ β a a₁ η₀ η₁ k] (((h : ℝ) + 3) / k) (b ^ k) 0
      (oneDEnvelope β L (K + M₁ * (L₁ + K * b) * β + 3 * M * β ^ 2 * (L₁ + K * b) ^ 2 + β * K * M)
        k) where
  R_pos := by positivity
  α_lt := by
    intro i
    have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
    fin_cases i <;> simp <;> rw [div_lt_div_iff_of_pos_right hk'] <;> linarith
  j_le := by intro i; fin_cases i <;> simp
  ρ_meas := by
    unfold oneDDensity Function.uncurry
    refine ((measurable_const.mul (measurable_fst.pow_const _)).mul ?_)
    refine (hηc.measurable.comp (measurable_fst.pow_const _)).mul ?_
    exact Real.measurable_exp.comp ((measurable_const.mul measurable_snd).mul
      (hξc.measurable.comp (measurable_fst.pow_const _)))
  c_meas := by
    intro i
    fin_cases i
    · unfold oneDCoeff₀
      exact measurable_const.mul (measurable_const.mul
        (Real.measurable_exp.comp ((measurable_const.mul measurable_id).mul measurable_const)))
    · unfold oneDCoeff₁
      refine measurable_const.mul ((Real.measurable_exp.comp
        ((measurable_const.mul measurable_id).mul measurable_const)).mul ?_)
      exact measurable_const.add (((measurable_const.mul measurable_id).mul measurable_const).mul
        measurable_const)
  H_meas := by
    unfold oneDEnvelope
    exact measurable_const.mul (((measurable_const.add measurable_id).pow_const _).mul
      (Real.measurable_exp.comp (measurable_const.mul measurable_id)))
  H_nonneg := by
    intro s
    unfold oneDEnvelope
    have := taylorConst_nonneg β b K M M₁ L₁ hβ hb hK hM hM₁ hL₁
    have hC : 0 ≤ (K + M₁ * (L₁ + K * b) * β + 3 * M * β ^ 2 * (L₁ + K * b) ^ 2 + β * K * M)
      / (k : ℝ) := div_nonneg this (Nat.cast_nonneg k)
    exact mul_nonneg hC (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  rem := by
    intro r hr s hs
    have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
    set u : ℝ := r ^ ((k : ℝ)⁻¹) with hu
    have hu0 : 0 < u := Real.rpow_pos_of_pos hr.1 _
    have hub : u ≤ b := by
      have : r ^ ((k : ℝ)⁻¹) ≤ (b ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow hr.1.le hr.2 (by positivity)
      rwa [Real.pow_rpow_inv_natCast hb.le hk.ne'] at this
    have huI : u ∈ Icc (0 : ℝ) b := ⟨hu0.le, hub⟩
    have hkey := kernel_taylor_bound β b L K M M₁ L₁ a a₁ η₀ η₁ ξ η hβ hb hK hM hM₁ hL₁ hξL hη₀ hη₁
      ha₁ hξT hηT u s huI hs.le
    -- the powers of `r`
    have hr1 : r ^ (((h : ℝ) + 2) / k - 1) = r ^ (((h : ℝ) + 1) / k - 1) * u := by
      rw [hu, ← Real.rpow_add hr.1]; congr 1; field_simp; ring
    have hr2 : r ^ (((h : ℝ) + 3) / k - 1) = r ^ (((h : ℝ) + 1) / k - 1) * u ^ 2 := by
      rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hr.1.le, ← Real.rpow_add hr.1]
      congr 1; push_cast; field_simp; ring
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pow_zero, mul_one]
    unfold oneDDensity oneDCoeff₀ oneDCoeff₁ oneDEnvelope
    rw [← hu, hr1, hr2]
    have hrp : 0 ≤ r ^ (((h : ℝ) + 1) / k - 1) := Real.rpow_nonneg hr.1.le _
    have hexpr : 1 / (k : ℝ) * r ^ (((h : ℝ) + 1) / k - 1) * (η u * Real.exp (β * s * ξ u))
        - (r ^ (((h : ℝ) + 1) / k - 1) * (1 / (k : ℝ) * (η₀ * Real.exp (β * s * a)))
          + r ^ (((h : ℝ) + 1) / k - 1) * u
            * (1 / (k : ℝ) * (Real.exp (β * s * a) * (η₁ + β * s * η₀ * a₁))))
        = 1 / (k : ℝ) * r ^ (((h : ℝ) + 1) / k - 1)
          * (η u * Real.exp (β * s * ξ u) - η₀ * Real.exp (β * s * a)
            - u * (Real.exp (β * s * a) * (η₁ + β * s * η₀ * a₁))) := by ring
    rw [hexpr, abs_mul, abs_mul, abs_of_nonneg hrp, abs_of_pos (by positivity : (0:ℝ) < 1 / k)]
    calc 1 / (k : ℝ) * r ^ (((h : ℝ) + 1) / k - 1)
          * |η u * Real.exp (β * s * ξ u) - η₀ * Real.exp (β * s * a)
            - u * (Real.exp (β * s * a) * (η₁ + β * s * η₀ * a₁))|
        ≤ 1 / (k : ℝ) * r ^ (((h : ℝ) + 1) / k - 1)
          * ((K + M₁ * (L₁ + K * b) * β + 3 * M * β ^ 2 * (L₁ + K * b) ^ 2 + β * K * M)
            * u ^ 2 * (1 + s) ^ 2 * Real.exp (3 * β * L * s)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = _ := by ring

/-- A transferred term of log degree `0` is `N^{-α} M₀`. -/
theorem transferTerm_zero (β α : ℝ) (c : ℝ → ℝ) (N : ℝ) :
    transferTerm β α 0 c N = N ^ (-α) * logMoment β α 0 c := by
  unfold transferTerm
  simp

theorem logMoment_oneDCoeff₀ (β α a η₀ : ℝ) (k : ℕ) :
    logMoment β α 0 (oneDCoeff₀ β a η₀ k) = 1 / (k : ℝ) * (η₀ * weightedMass β a (α - 1)) := by
  have : oneDCoeff₀ β a η₀ k = fun s => (1 / (k : ℝ) * η₀) * Real.exp (β * s * a) := by
    funext s; unfold oneDCoeff₀; ring
  rw [this, logMoment_const_exp]; ring

/-- **Weighted-moment integrability from a polynomial-exponential bound**: if
`|c s| ≤ e^{βsa'}(A + B s + D s²)` on `(0,∞)`, the moment integrands of unit 83 at log degree `0`
are integrable for every `γ > -1`. -/
theorem moment_integrableOn_of_bound (β a' γ A B D : ℝ) (hβ : 0 < β) (hγ : -1 < γ)
    (c : ℝ → ℝ) (hc : Measurable c)
    (hbound : ∀ s, 0 < s → |c s| ≤ Real.exp (β * s * a') * (A + B * s + D * s ^ 2)) :
    IntegrableOn (fun s => s ^ γ * (1 + |Real.log s|) ^ 0 * (Real.exp (-β * s ^ 2) * |c s|))
      (Ioi 0) := by
  have h0 := weightedKernel_integrableOn β a' γ hβ hγ
  have h1 := weightedKernel_integrableOn β a' (γ + 1) hβ (by linarith)
  have h2 := weightedKernel_integrableOn β a' (γ + 2) hβ (by linarith)
  have hdom : IntegrableOn (fun s : ℝ => A * (s ^ γ * quadKernel β a' s)
      + B * (s ^ (γ + 1) * quadKernel β a' s) + D * (s ^ (γ + 2) * quadKernel β a' s)) (Ioi 0) :=
    ((h0.const_mul A).add (h1.const_mul B)).add (h2.const_mul D)
  refine Integrable.mono' hdom ?_ ?_
  · exact (((measurable_id.pow_const _).mul ((measurable_const.add
      (continuous_abs.measurable.comp Real.measurable_log)).pow_const _)).mul
      ((Real.measurable_exp.comp (measurable_const.mul (measurable_id.pow_const _))).mul
        (continuous_abs.measurable.comp hc))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hs
    have hsγ : 0 ≤ s ^ γ := Real.rpow_nonneg hs0.le _
    rw [Real.norm_eq_abs, pow_zero, mul_one, abs_of_nonneg
      (mul_nonneg hsγ (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)))]
    have hq : Real.exp (-β * s ^ 2) * Real.exp (β * s * a') = quadKernel β a' s :=
      exp_mul_exp_eq_quadKernel β a' s
    have hs1 : s ^ (γ + 1) = s ^ γ * s := by rw [Real.rpow_add hs0, Real.rpow_one]
    have hs2 : s ^ (γ + 2) = s ^ γ * s ^ 2 := by
      rw [Real.rpow_add hs0, Real.rpow_two]
    rw [hs1, hs2, ← hq]
    have := hbound s hs0
    have hE : 0 ≤ Real.exp (-β * s ^ 2) := (Real.exp_pos _).le
    calc s ^ γ * (Real.exp (-β * s ^ 2) * |c s|)
        ≤ s ^ γ * (Real.exp (-β * s ^ 2) * (Real.exp (β * s * a') * (A + B * s + D * s ^ 2))) := by
          gcongr
      _ = _ := by ring

/-- **The one-dimensional second-order theorem** (`thm:TaylorTree` at `d = 1`, two terms):
for `N ≥ 1`,
`|Z(N) − C₀ N^{-p} − C₁ N^{-q}| ≤ K' N^{-(h+3)/k}` with `C₀ = k⁻¹ η₀ S_p(a)`,
`C₁ = k⁻¹ (η₁ S_q(a) + β η₀ a₁ S_{q+1}(a))`, `S_λ(a) = weightedMass β a (λ - 1)`. -/
theorem oneDScale_second_order (β b L K M M₁ L₁ a a₁ η₀ η₁ : ℝ) (h k : ℕ) (ξ η : ℝ → ℝ)
    (hβ : 0 < β) (hb : 0 < b) (hk : 0 < k) (hK : 0 ≤ K) (hM : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hL₁ : 0 ≤ L₁)
    (hξc : Continuous ξ) (hηc : Continuous η)
    (hξL : ∀ u ∈ Icc (0 : ℝ) b, |ξ u| ≤ L) (hη₀ : |η₀| ≤ M) (hη₁ : |η₁| ≤ M₁) (ha₁ : |a₁| ≤ L₁)
    (hξT : ∀ u ∈ Icc (0 : ℝ) b, |ξ u - a - u * a₁| ≤ K * u ^ 2)
    (hηT : ∀ u ∈ Icc (0 : ℝ) b, |η u - η₀ - u * η₁| ≤ K * u ^ 2) :
    ∃ K' : ℝ, ∀ N : ℝ, 1 ≤ N →
      |oneDScale β b N h k ξ η
        - (N ^ (-(((h : ℝ) + 1) / k))
            * (1 / (k : ℝ) * (η₀ * weightedMass β a (((h : ℝ) + 1) / k - 1)))
          + N ^ (-(((h : ℝ) + 2) / k))
            * (1 / (k : ℝ) * (η₁ * weightedMass β a (((h : ℝ) + 2) / k - 1)
              + β * η₀ * a₁ * weightedMass β a (((h : ℝ) + 2) / k))))|
        ≤ K' * N ^ (-(((h : ℝ) + 3) / k)) := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  set p : ℝ := ((h : ℝ) + 1) / k with hp
  set q : ℝ := ((h : ℝ) + 2) / k with hq
  set a₂ : ℝ := ((h : ℝ) + 3) / k with ha₂
  have hp0 : 0 < p := by positivity
  have hq0 : 0 < q := by positivity
  have ha₂0 : 0 < a₂ := by positivity
  set C : ℝ := K + M₁ * (L₁ + K * b) * β + 3 * M * β ^ 2 * (L₁ + K * b) ^ 2 + β * K * M with hC
  have hC0 : 0 ≤ C := taylorConst_nonneg β b K M M₁ L₁ hβ hb hK hM hM₁ hL₁
  have hD := oneDDensity_expansion β b L K M M₁ L₁ a a₁ η₀ η₁ h k ξ η hβ hb hk hK hM hM₁ hL₁ hξc hηc
    hξL hη₀ hη₁ ha₁ hξT hηT
  rw [← hp, ← hq, ← ha₂, ← hC] at hD
  -- measurability and bounds of the coefficient functions
  have hc₀m : Measurable (oneDCoeff₀ β a η₀ k) := hD.c_meas 0
  have hc₁m : Measurable (oneDCoeff₁ β a a₁ η₀ η₁ k) := hD.c_meas 1
  have hc₀b : ∀ s, 0 < s → |oneDCoeff₀ β a η₀ k s|
      ≤ Real.exp (β * s * a) * (1 / (k : ℝ) * M + 0 * s + 0 * s ^ 2) := by
    intro s _
    unfold oneDCoeff₀
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / k), abs_of_pos (Real.exp_pos _)]
    have : |η₀| * Real.exp (β * s * a) ≤ M * Real.exp (β * s * a) :=
      mul_le_mul_of_nonneg_right hη₀ (Real.exp_pos _).le
    have hk0 : (0 : ℝ) ≤ 1 / k := by positivity
    calc 1 / (k : ℝ) * (|η₀| * Real.exp (β * s * a))
        ≤ 1 / (k : ℝ) * (M * Real.exp (β * s * a)) := mul_le_mul_of_nonneg_left this hk0
      _ = _ := by ring
  have hc₁b : ∀ s, 0 < s → |oneDCoeff₁ β a a₁ η₀ η₁ k s|
      ≤ Real.exp (β * s * a)
        * (1 / (k : ℝ) * M₁ + (1 / (k : ℝ) * (β * M * L₁)) * s + 0 * s ^ 2) := by
    intro s hs
    unfold oneDCoeff₁
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / k), abs_of_pos (Real.exp_pos _)]
    have h1 : |η₁ + β * s * η₀ * a₁| ≤ M₁ + β * s * (M * L₁) := by
      calc |η₁ + β * s * η₀ * a₁| ≤ |η₁| + |β * s * η₀ * a₁| := abs_add_le _ _
        _ = |η₁| + β * s * (|η₀| * |a₁|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos hβ, abs_of_pos hs]; ring
        _ ≤ M₁ + β * s * (M * L₁) := by gcongr
    have hE := Real.exp_pos (β * s * a)
    calc 1 / (k : ℝ) * (Real.exp (β * s * a) * |η₁ + β * s * η₀ * a₁|)
        ≤ 1 / (k : ℝ) * (Real.exp (β * s * a) * (M₁ + β * s * (M * L₁))) := by gcongr
      _ = _ := by ring
  have hHb : ∀ s, 0 < s → |oneDEnvelope β L C k s|
      ≤ Real.exp (β * s * (3 * L))
        * (C / (k : ℝ) + (2 * (C / (k : ℝ))) * s + C / (k : ℝ) * s ^ 2) := by
    intro s _
    have hCk : 0 ≤ C / (k : ℝ) := div_nonneg hC0 hk'.le
    rw [abs_of_nonneg (hD.H_nonneg s)]
    unfold oneDEnvelope
    rw [show 3 * β * L * s = β * s * (3 * L) by ring]
    ring_nf; rfl
  have hCk : 0 ≤ C / (k : ℝ) := div_nonneg hC0 hk'.le
  have hMc : ∀ i, IntegrableOn (fun s => s ^ (![p, q] i - 1) * (1 + |Real.log s|) ^ (![0, 0] i : ℕ)
      * (Real.exp (-β * s ^ 2) * |(![oneDCoeff₀ β a η₀ k, oneDCoeff₁ β a a₁ η₀ η₁ k] i) s|))
      (Ioi 0) := by
    intro i
    fin_cases i
    · exact moment_integrableOn_of_bound β a (p - 1) _ 0 0 hβ (by linarith) _ hc₀m hc₀b
    · exact moment_integrableOn_of_bound β a (q - 1) _ _ 0 hβ (by linarith) _ hc₁m hc₁b
  have hMt : ∀ i, IntegrableOn (fun s => s ^ (a₂ - 1) * (1 + |Real.log s|) ^ (![0, 0] i : ℕ)
      * (Real.exp (-β * s ^ 2) * |(![oneDCoeff₀ β a η₀ k, oneDCoeff₁ β a a₁ η₀ η₁ k] i) s|))
      (Ioi 0) := by
    intro i
    fin_cases i
    · exact moment_integrableOn_of_bound β a (a₂ - 1) _ 0 0 hβ (by linarith) _ hc₀m hc₀b
    · exact moment_integrableOn_of_bound β a (a₂ - 1) _ _ 0 hβ (by linarith) _ hc₁m hc₁b
  have hMH : IntegrableOn (fun s => s ^ (a₂ - 1) * (1 + |Real.log s|) ^ 0
      * (Real.exp (-β * s ^ 2) * oneDEnvelope β L C k s)) (Ioi 0) := by
    have := moment_integrableOn_of_bound β (3 * L) (a₂ - 1) _ _ _ hβ (by linarith) _ hD.H_meas hHb
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    beta_reduce
    rw [abs_of_nonneg (hD.H_nonneg s)]
  -- apply the transfer theorem
  refine ⟨envMoment β a₂ 0 (oneDEnvelope β L C k)
    + ∑ i, (b ^ k) ^ (![p, q] i - a₂) * tailMoment β a₂ (![0, 0] i)
      (![oneDCoeff₀ β a η₀ k, oneDCoeff₁ β a a₁ η₀ η₁ k] i), fun N hN => ?_⟩
  have hmain := densityTransfer_bound hD β hMc hMt hMH N hN
  rw [pow_zero, mul_one] at hmain
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hmain
  rw [transferTerm_zero, transferTerm_zero, logMoment_oneDCoeff₀,
    logMoment_oneDCoeff₁ β q a a₁ η₀ η₁ k hβ hq0, ← oneDScale_eq_transferZ β b N h k hk hb ξ η]
    at hmain
  calc _ ≤ N ^ (-a₂) * (envMoment β a₂ 0 (oneDEnvelope β L C k)
        + ((b ^ k) ^ (p - a₂) * tailMoment β a₂ 0 (oneDCoeff₀ β a η₀ k)
          + (b ^ k) ^ (q - a₂) * tailMoment β a₂ 0 (oneDCoeff₁ β a a₁ η₀ η₁ k))) := hmain
    _ = _ := by
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        ring

end Laplace.Grammar
