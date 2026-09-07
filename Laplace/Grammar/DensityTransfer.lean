/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.BoxGeneralOrder

/-!
# The finite density-transfer theorem (grammar §4.2, from state density to asymptotics)

An abstract, finite, quantitative version of "a power-log expansion of the state density transfers
to a power-log asymptotic expansion of the partition function". Let

  `Z(N) = ∫₀^R e^{-β(Nr)²} ρ(r, Nr) dr`

with a two-variable density `ρ(r, s)` (`r` the monomial radius, `s` the kernel parameter,
specialised to `s = Nr` only at transfer time). If for `0 < r ≤ R`, `s > 0`

  `ρ(r, s) = ∑ᵢ r^{αᵢ-1} (log(1/r))^{jᵢ} cᵢ(s) + E(r, s)`,
  `|E(r, s)| ≤ r^{a-1} (1+|log r|)^J H(s)`,

with `0 < αᵢ < a`, `jᵢ ≤ J` and finite weighted moments, then for `N ≥ 1`

  `Z(N) = ∑ᵢ N^{-αᵢ} ∑_{m ≤ jᵢ} C(jᵢ,m) (log N)^m (-1)^{jᵢ-m} M_{i, jᵢ-m} + O(N^{-a} (1 + log N)^J)`

with the log moments `M_{i,ℓ} = ∫₀^∞ s^{αᵢ-1} (log s)^ℓ e^{-βs²} cᵢ(s) ds` and an explicit constant
(`densityTransfer_bound`). Three elementary mechanisms: the scaling `s = Nr`, the binomial expansion
of `(log N − log s)^j`, and the replacement of the upper limit `NR` by `∞` at a power-saving cost.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- Scaling `r ↦ N r` on `(0, R]`. -/
theorem integral_Ioc_comp_mul_left' (F : ℝ → ℝ) (N R : ℝ) (hN : 0 < N) (hR : 0 < R) :
    ∫ r in Ioc (0 : ℝ) R, F (N * r) = N⁻¹ * ∫ s in Ioc (0 : ℝ) (N * R), F s := by
  rw [← intervalIntegral.integral_of_le hR.le, ← intervalIntegral.integral_of_le (by positivity),
    intervalIntegral.integral_comp_mul_left F hN.ne', mul_zero, smul_eq_mul]

/-- Integrability transports along the scaling `r ↦ N r`. -/
theorem integrableOn_Ioc_comp_mul_left' (F : ℝ → ℝ) (N R : ℝ) (hN : 0 < N) (hR : 0 < R)
    (hF : IntegrableOn F (Ioc 0 (N * R))) : IntegrableOn (fun r => F (N * r)) (Ioc 0 R) := by
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)] at hF
  have := hF.comp_mul_left (c := N)
  rwa [zero_div, mul_div_cancel_left₀ _ hN.ne'] at this

/-- The transfer integral `Z(N) = ∫₀^R e^{-β(Nr)²} ρ(r, Nr) dr`. -/
noncomputable def transferZ (ρ : ℝ → ℝ → ℝ) (β R N : ℝ) : ℝ :=
  ∫ r in Ioc (0 : ℝ) R, Real.exp (-β * (N * r) ^ 2) * ρ r (N * r)

/-- The log moments `M_ℓ = ∫₀^∞ s^{α-1} (log s)^ℓ e^{-βs²} c(s) ds`. -/
noncomputable def logMoment (β α : ℝ) (ℓ : ℕ) (c : ℝ → ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c s)

/-- One transferred expansion term `N^{-α} ∑_{m ≤ j} C(j,m) (log N)^m (-1)^{j-m} M_{j-m}`. -/
noncomputable def transferTerm (β α : ℝ) (j : ℕ) (c : ℝ → ℝ) (N : ℝ) : ℝ :=
  N ^ (-α) * ∑ m ∈ Finset.range (j + 1),
    Real.log N ^ m * (-1) ^ (j - m) * (j.choose m : ℝ) * logMoment β α (j - m) c

/-- The tail moment `∫₀^∞ s^{a-1} (1+|log s|)^j e^{-βs²} |c(s)| ds`. -/
noncomputable def tailMoment (β a : ℝ) (j : ℕ) (c : ℝ → ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ (a - 1) * (1 + |Real.log s|) ^ j * (Real.exp (-β * s ^ 2) * |c s|)

/-- The weighted moment integrand (nonnegative). -/
theorem tailMoment_integrand_nonneg (a : ℝ) (j : ℕ) (c : ℝ → ℝ) (β s : ℝ) (hs : 0 < s) :
    0 ≤ s ^ (a - 1) * (1 + |Real.log s|) ^ j * (Real.exp (-β * s ^ 2) * |c s|) :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) (pow_nonneg (by positivity) _))
    (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))

/-- `1 + |log s − log N| ≤ (1 + log N)(1 + |log s|)` for `N ≥ 1`. -/
theorem one_add_abs_log_sub_le (s N : ℝ) (hN : 1 ≤ N) :
    1 + |Real.log s - Real.log N| ≤ (1 + Real.log N) * (1 + |Real.log s|) := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have h1 : |Real.log s - Real.log N| ≤ |Real.log s| + Real.log N := by
    calc |Real.log s - Real.log N| ≤ |Real.log s| + |Real.log N| := abs_sub _ _
      _ = |Real.log s| + Real.log N := by rw [abs_of_nonneg hlogN]
  nlinarith [abs_nonneg (Real.log s)]

/-- `(1 + x)^j = ∑_{m ≤ j} C(j,m) x^m`. -/
theorem one_add_pow_eq_sum (x : ℝ) (j : ℕ) :
    (1 + x) ^ j = ∑ m ∈ Finset.range (j + 1), x ^ m * (j.choose m : ℝ) := by
  rw [add_comm, add_pow]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [one_pow, mul_one]

/-- **Tail replacement**: for `0 < α < a`, `ℓ ≤ j`, `L ≥ 1`,
`|∫_L^∞ s^{α-1} (log s)^ℓ e^{-βs²} c| ≤ L^{α-a} ∫₀^∞ s^{a-1}(1+|log s|)^j e^{-βs²}|c|`. -/
theorem logMoment_tail_le (β α a L : ℝ) (j ℓ : ℕ) (c : ℝ → ℝ) (hαa : α < a) (hL : 0 < L)
    (hℓ : ℓ ≤ j)
    (hMt : IntegrableOn (fun s => s ^ (a - 1) * (1 + |Real.log s|) ^ j
      * (Real.exp (-β * s ^ 2) * |c s|)) (Ioi 0)) :
    |∫ s in Ioi L, s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c s)|
      ≤ L ^ (α - a) * tailMoment β a j c := by
  have hbound : ∀ s ∈ Ioi L, ‖s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c s)‖
      ≤ L ^ (α - a) * (s ^ (a - 1) * (1 + |Real.log s|) ^ j * (Real.exp (-β * s ^ 2) * |c s|)) := by
    intro s hs
    have hs0 : 0 < s := lt_trans hL hs
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _),
      abs_pow, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : s ^ (α - 1) ≤ L ^ (α - a) * s ^ (a - 1) := by
      have : s ^ (α - 1) = s ^ (α - a) * s ^ (a - 1) := by rw [← Real.rpow_add hs0]; ring_nf
      rw [this]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hL (le_of_lt hs) (by linarith)) (Real.rpow_nonneg hs0.le _)
    have h2 : |Real.log s| ^ ℓ ≤ (1 + |Real.log s|) ^ j :=
      (pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg (Real.log s)]) ℓ).trans
        (pow_le_pow_right₀ (by linarith [abs_nonneg (Real.log s)]) hℓ)
    have hE : 0 ≤ Real.exp (-β * s ^ 2) * |c s| := mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
    calc s ^ (α - 1) * |Real.log s| ^ ℓ * (Real.exp (-β * s ^ 2) * |c s|)
        ≤ (L ^ (α - a) * s ^ (a - 1)) * (1 + |Real.log s|) ^ j
            * (Real.exp (-β * s ^ 2) * |c s|) := by
          gcongr
      _ = _ := by ring
  have hint : IntegrableOn (fun s => L ^ (α - a) * (s ^ (a - 1) * (1 + |Real.log s|) ^ j
      * (Real.exp (-β * s ^ 2) * |c s|))) (Ioi L) :=
    (hMt.mono_set (Ioi_subset_Ioi hL.le)).const_mul _
  calc |∫ s in Ioi L, s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c s)|
      = ‖∫ s in Ioi L, s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c s)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ s in Ioi L, L ^ (α - a) * (s ^ (a - 1) * (1 + |Real.log s|) ^ j
          * (Real.exp (-β * s ^ 2) * |c s|)) :=
        norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).2
          (Filter.Eventually.of_forall hbound))
    _ = L ^ (α - a) * ∫ s in Ioi L, s ^ (a - 1) * (1 + |Real.log s|) ^ j
          * (Real.exp (-β * s ^ 2) * |c s|) := integral_const_mul _ _
    _ ≤ L ^ (α - a) * tailMoment β a j c := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hL.le _)
        refine setIntegral_mono_set hMt ?_ (Ioi_subset_Ioi hL.le).eventuallyLE
        exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall
          fun s hs => tailMoment_integrand_nonneg a j c β s hs)

/-- `|log s|^ℓ ≤ (1 + |log s|)^j` for `ℓ ≤ j`. -/
theorem abs_log_pow_le_one_add (s : ℝ) (j ℓ : ℕ) (hℓ : ℓ ≤ j) :
    |Real.log s| ^ ℓ ≤ (1 + |Real.log s|) ^ j :=
  (pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg (Real.log s)]) ℓ).trans
    (pow_le_pow_right₀ (by linarith [abs_nonneg (Real.log s)]) hℓ)

/-- Pointwise domination of the moment integrand by the weighted moment integrand. -/
theorem moment_integrand_le (β α : ℝ) (j ℓ : ℕ) (c : ℝ → ℝ) (hℓ : ℓ ≤ j) (s : ℝ) (hs : 0 < s) :
    ‖s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c s)‖
      ≤ s ^ (α - 1) * (1 + |Real.log s|) ^ j * (Real.exp (-β * s ^ 2) * |c s|) := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs.le _), abs_pow,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  have hE : 0 ≤ Real.exp (-β * s ^ 2) * |c s| := mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (abs_log_pow_le_one_add s j ℓ hℓ) (Real.rpow_nonneg hs.le _)) hE

theorem moment_integrand_measurable (β α : ℝ) (ℓ : ℕ) (c : ℝ → ℝ) (hc : Measurable c) :
    Measurable fun s : ℝ => s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c s) :=
  ((measurable_id.pow_const _).mul (Real.measurable_log.pow_const _)).mul
    ((Real.measurable_exp.comp (measurable_const.mul (measurable_id.pow_const _))).mul hc)

/-- Integrability of the moment integrand on measurable `S ⊆ (0, ∞)`. -/
theorem moment_integrand_integrableOn (β α : ℝ) (j ℓ : ℕ) (c : ℝ → ℝ) (hℓ : ℓ ≤ j)
    (hc : Measurable c)
    (hMc : IntegrableOn (fun s => s ^ (α - 1) * (1 + |Real.log s|) ^ j
      * (Real.exp (-β * s ^ 2) * |c s|)) (Ioi 0)) (S : Set ℝ) (hSm : MeasurableSet S)
    (hS : S ⊆ Ioi 0) :
    IntegrableOn (fun s => s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c s)) S := by
  refine Integrable.mono' (hMc.mono_set hS)
    (moment_integrand_measurable β α ℓ c hc).aestronglyMeasurable ?_
  exact (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun s hs =>
    moment_integrand_le β α j ℓ c hℓ s (hS hs))

/-- The log moment splits at `L`. -/
theorem logMoment_split (β α : ℝ) (j ℓ : ℕ) (c : ℝ → ℝ) (hℓ : ℓ ≤ j) (hc : Measurable c)
    (hMc : IntegrableOn (fun s => s ^ (α - 1) * (1 + |Real.log s|) ^ j
      * (Real.exp (-β * s ^ 2) * |c s|)) (Ioi 0)) (L : ℝ) (hL : 0 < L) :
    logMoment β α ℓ c
      = (∫ s in Ioc (0 : ℝ) L, s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c s))
        + ∫ s in Ioi L, s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c s) := by
  unfold logMoment
  rw [← Ioc_union_Ioi_eq_Ioi hL.le]
  exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (moment_integrand_integrableOn β α j ℓ c hℓ hc hMc _ measurableSet_Ioc Ioc_subset_Ioi_self)
    (moment_integrand_integrableOn β α j ℓ c hℓ hc hMc _ measurableSet_Ioi (Ioi_subset_Ioi hL.le))

/-- The scaled integrand `G_N(s) = s^{α-1} (log N − log s)^j e^{-βs²} c(s)`. -/
noncomputable def scaledIntegrand (β α : ℝ) (j : ℕ) (c : ℝ → ℝ) (N s : ℝ) : ℝ :=
  s ^ (α - 1) * (Real.log N - Real.log s) ^ j * (Real.exp (-β * s ^ 2) * c s)

/-- On `(0, R]`, `e^{-β(Nr)²} r^{α-1} (log(1/r))^j c(Nr) = N^{1-α} G_N(Nr)`. -/
theorem term_eq_scaled (β α : ℝ) (j : ℕ) (c : ℝ → ℝ) (N r : ℝ) (hN : 0 < N) (hr : 0 < r) :
    Real.exp (-β * (N * r) ^ 2) * (r ^ (α - 1) * Real.log (1 / r) ^ j * c (N * r))
      = N ^ (1 - α) * scaledIntegrand β α j c N (N * r) := by
  unfold scaledIntegrand
  rw [Real.mul_rpow hN.le hr.le, Real.log_mul hN.ne' hr.ne', one_div, Real.log_inv,
    show Real.log N - (Real.log N + Real.log r) = -Real.log r by ring]
  have : N ^ (1 - α) * N ^ (α - 1) = 1 := by rw [← Real.rpow_add hN]; simp
  calc Real.exp (-β * (N * r) ^ 2) * (r ^ (α - 1) * (-Real.log r) ^ j * c (N * r))
      = (N ^ (1 - α) * N ^ (α - 1)) * (Real.exp (-β * (N * r) ^ 2)
          * (r ^ (α - 1) * (-Real.log r) ^ j * c (N * r))) := by rw [this, one_mul]
    _ = _ := by ring

/-- The scaled integrand expands binomially. -/
theorem scaledIntegrand_eq_sum (β α : ℝ) (j : ℕ) (c : ℝ → ℝ) (N s : ℝ) :
    scaledIntegrand β α j c N s = ∑ m ∈ Finset.range (j + 1),
      (Real.log N ^ m * (-1) ^ (j - m) * (j.choose m : ℝ))
        * (s ^ (α - 1) * Real.log s ^ (j - m) * (Real.exp (-β * s ^ 2) * c s)) := by
  unfold scaledIntegrand
  rw [show Real.log N - Real.log s = Real.log N + (-Real.log s) by ring, add_pow, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [neg_pow]; ring

theorem scaledIntegrand_measurable (β α : ℝ) (j : ℕ) (c : ℝ → ℝ) (hc : Measurable c) (N : ℝ) :
    Measurable (scaledIntegrand β α j c N) := by
  unfold scaledIntegrand
  exact ((measurable_id.pow_const _).mul
    ((measurable_const.sub Real.measurable_log).pow_const _)).mul
    ((Real.measurable_exp.comp (measurable_const.mul (measurable_id.pow_const _))).mul hc)

/-- Domination of the scaled integrand for `N ≥ 1`. -/
theorem scaledIntegrand_le (β α : ℝ) (j : ℕ) (c : ℝ → ℝ) (N s : ℝ) (hN : 1 ≤ N) (hs : 0 < s) :
    ‖scaledIntegrand β α j c N s‖ ≤ (1 + Real.log N) ^ j
      * (s ^ (α - 1) * (1 + |Real.log s|) ^ j * (Real.exp (-β * s ^ 2) * |c s|)) := by
  unfold scaledIntegrand
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs.le _), abs_pow,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : |Real.log N - Real.log s| ^ j ≤ ((1 + Real.log N) * (1 + |Real.log s|)) ^ j := by
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ j
    rw [abs_sub_comm]
    exact (le_add_of_nonneg_left zero_le_one).trans (one_add_abs_log_sub_le s N hN)
  have hE : 0 ≤ Real.exp (-β * s ^ 2) * |c s| := mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  calc s ^ (α - 1) * |Real.log N - Real.log s| ^ j * (Real.exp (-β * s ^ 2) * |c s|)
      ≤ s ^ (α - 1) * ((1 + Real.log N) * (1 + |Real.log s|)) ^ j
          * (Real.exp (-β * s ^ 2) * |c s|) := by
        gcongr
    _ = _ := by rw [mul_pow]; ring

/-- Integrability of the scaled integrand on `(0, L]`. -/
theorem scaledIntegrand_integrableOn (β α : ℝ) (j : ℕ) (c : ℝ → ℝ) (hc : Measurable c)
    (hMc : IntegrableOn (fun s => s ^ (α - 1) * (1 + |Real.log s|) ^ j
      * (Real.exp (-β * s ^ 2) * |c s|)) (Ioi 0)) (N L : ℝ) (hN : 1 ≤ N) :
    IntegrableOn (scaledIntegrand β α j c N) (Ioc 0 L) := by
  refine Integrable.mono' ((hMc.mono_set Ioc_subset_Ioi_self).const_mul ((1 + Real.log N) ^ j))
    (scaledIntegrand_measurable β α j c hc N).aestronglyMeasurable ?_
  exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs =>
    scaledIntegrand_le β α j c N s hN hs.1)

/-- Integrability of the transfer term integrand on `(0, R]`. -/
theorem term_integrableOn (β α R : ℝ) (j : ℕ) (c : ℝ → ℝ) (hR : 0 < R) (hc : Measurable c)
    (hMc : IntegrableOn (fun s => s ^ (α - 1) * (1 + |Real.log s|) ^ j
      * (Real.exp (-β * s ^ 2) * |c s|)) (Ioi 0)) (N : ℝ) (hN : 1 ≤ N) :
    IntegrableOn (fun r => Real.exp (-β * (N * r) ^ 2)
      * (r ^ (α - 1) * Real.log (1 / r) ^ j * c (N * r))) (Ioc 0 R) := by
  have hN0 : 0 < N := by linarith
  have h1 : IntegrableOn (fun r => N ^ (1 - α) * scaledIntegrand β α j c N (N * r)) (Ioc 0 R) :=
    (integrableOn_Ioc_comp_mul_left' _ N R hN0 hR
      (scaledIntegrand_integrableOn β α j c hc hMc N (N * R) hN)).const_mul _
  exact h1.congr_fun (fun r hr => (term_eq_scaled β α j c N r hN0 hr.1).symm) measurableSet_Ioc

/-- **One transferred term**: for `N ≥ 1`,
`|∫₀^R e^{-β(Nr)²} r^{α-1} (log(1/r))^j c(Nr) dr − transferTerm| ≤ N^{-a}(1+log N)^J R^{α-a} T`,
`T` the tail moment. -/
theorem transferTerm_bound (β α a R : ℝ) (j J : ℕ) (c : ℝ → ℝ) (hαa : α < a) (hR : 0 < R)
    (hjJ : j ≤ J) (hc : Measurable c)
    (hMc : IntegrableOn (fun s => s ^ (α - 1) * (1 + |Real.log s|) ^ j
      * (Real.exp (-β * s ^ 2) * |c s|)) (Ioi 0))
    (hMt : IntegrableOn (fun s => s ^ (a - 1) * (1 + |Real.log s|) ^ j
      * (Real.exp (-β * s ^ 2) * |c s|)) (Ioi 0)) (N : ℝ) (hN : 1 ≤ N) :
    |(∫ r in Ioc (0 : ℝ) R, Real.exp (-β * (N * r) ^ 2)
        * (r ^ (α - 1) * Real.log (1 / r) ^ j * c (N * r))) - transferTerm β α j c N|
      ≤ N ^ (-a) * (1 + Real.log N) ^ J * (R ^ (α - a) * tailMoment β a j c) := by
  have hN0 : 0 < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hNR : 0 < N * R := by positivity
  -- Step 1: scaling
  have hstep1 : (∫ r in Ioc (0 : ℝ) R, Real.exp (-β * (N * r) ^ 2)
      * (r ^ (α - 1) * Real.log (1 / r) ^ j * c (N * r)))
      = N ^ (-α) * ∫ s in Ioc (0 : ℝ) (N * R), scaledIntegrand β α j c N s := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (fun r hr => term_eq_scaled β α j c N r hN0 hr.1), integral_const_mul,
      integral_Ioc_comp_mul_left' _ N R hN0 hR, ← mul_assoc]
    congr 1
    rw [← Real.rpow_neg_one, ← Real.rpow_add hN0]; ring_nf
  -- Step 2: binomial expansion of the truncated integral
  set coef : ℕ → ℝ := fun m => Real.log N ^ m * (-1) ^ (j - m) * (j.choose m : ℝ) with hcoef
  set T : ℕ → ℝ := fun m => ∫ s in Ioi (N * R),
    s ^ (α - 1) * Real.log s ^ (j - m) * (Real.exp (-β * s ^ 2) * c s) with hT
  have hstep2 : (∫ s in Ioc (0 : ℝ) (N * R), scaledIntegrand β α j c N s)
      = ∑ m ∈ Finset.range (j + 1), coef m * (logMoment β α (j - m) c - T m) := by
    simp_rw [scaledIntegrand_eq_sum]
    rw [integral_finsetSum _ fun m hm => (moment_integrand_integrableOn β α j (j - m) c
      (Nat.sub_le _ _) hc hMc _ measurableSet_Ioc Ioc_subset_Ioi_self).const_mul _]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_mul, logMoment_split β α j (j - m) c (Nat.sub_le _ _) hc hMc (N * R) hNR]
    simp only [hcoef, hT]; ring
  -- Step 3: the difference is the tail sum
  have hdiff : (∫ r in Ioc (0 : ℝ) R, Real.exp (-β * (N * r) ^ 2)
      * (r ^ (α - 1) * Real.log (1 / r) ^ j * c (N * r))) - transferTerm β α j c N
      = -(N ^ (-α) * ∑ m ∈ Finset.range (j + 1), coef m * T m) := by
    rw [hstep1, hstep2, transferTerm, ← mul_sub, ← Finset.sum_sub_distrib]
    simp only [hcoef]
    rw [neg_mul_eq_mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  -- Step 4: bound the tails
  have htail : ∀ m ∈ Finset.range (j + 1), |coef m * T m|
      ≤ (Real.log N ^ m * (j.choose m : ℝ)) * ((N * R) ^ (α - a) * tailMoment β a j c) := by
    intro m hm
    have hm' : j - m ≤ j := Nat.sub_le _ _
    rw [abs_mul, hcoef]
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_of_nonneg hlogN,
      Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (logMoment_tail_le β α a (N * R) j (j - m) c hαa hNR hm' hMt)
      (by positivity)
  have hsum : ∑ m ∈ Finset.range (j + 1), (Real.log N ^ m * (j.choose m : ℝ))
      * ((N * R) ^ (α - a) * tailMoment β a j c)
      = (1 + Real.log N) ^ j * ((N * R) ^ (α - a) * tailMoment β a j c) := by
    rw [← Finset.sum_mul, one_add_pow_eq_sum]
  have hpowj : (1 + Real.log N) ^ j ≤ (1 + Real.log N) ^ J :=
    pow_le_pow_right₀ (by linarith) hjJ
  have hTM : 0 ≤ tailMoment β a j c :=
    setIntegral_nonneg measurableSet_Ioi fun s hs => tailMoment_integrand_nonneg a j c β s hs
  have hNR' : (N * R) ^ (α - a) = N ^ (α - a) * R ^ (α - a) := Real.mul_rpow hN0.le hR.le
  have hNa : N ^ (-α) * N ^ (α - a) = N ^ (-a) := by rw [← Real.rpow_add hN0]; ring_nf
  rw [hdiff, abs_neg, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hN0 _)]
  calc N ^ (-α) * |∑ m ∈ Finset.range (j + 1), coef m * T m|
      ≤ N ^ (-α) * ∑ m ∈ Finset.range (j + 1), |coef m * T m| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Real.rpow_nonneg hN0.le _)
    _ ≤ N ^ (-α) * ∑ m ∈ Finset.range (j + 1), (Real.log N ^ m * (j.choose m : ℝ))
          * ((N * R) ^ (α - a) * tailMoment β a j c) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum htail) (Real.rpow_nonneg hN0.le _)
    _ = (N ^ (-α) * N ^ (α - a)) * ((1 + Real.log N) ^ j * (R ^ (α - a) * tailMoment β a j c)) := by
        rw [hsum, hNR']; ring
    _ ≤ (N ^ (-α) * N ^ (α - a)) * ((1 + Real.log N) ^ J * (R ^ (α - a) * tailMoment β a j c)) := by
        gcongr
    _ = _ := by rw [hNa]; ring

/-- The remainder envelope after scaling: `s^{a-1}(1+|log s − log N|)^J e^{-βs²} H(s)`. -/
noncomputable def scaledEnvelope (β a : ℝ) (J : ℕ) (H : ℝ → ℝ) (N s : ℝ) : ℝ :=
  s ^ (a - 1) * (1 + |Real.log s - Real.log N|) ^ J * (Real.exp (-β * s ^ 2) * H s)

theorem scaledEnvelope_measurable (β a : ℝ) (J : ℕ) (H : ℝ → ℝ) (hH : Measurable H) (N : ℝ) :
    Measurable (scaledEnvelope β a J H N) := by
  unfold scaledEnvelope
  exact ((measurable_id.pow_const _).mul
    ((measurable_const.add (continuous_abs.measurable.comp
      (Real.measurable_log.sub measurable_const))).pow_const _)).mul
    ((Real.measurable_exp.comp (measurable_const.mul (measurable_id.pow_const _))).mul hH)

theorem scaledEnvelope_nonneg (β a : ℝ) (J : ℕ) (H : ℝ → ℝ) (hH0 : ∀ s, 0 ≤ H s) (N s : ℝ)
    (hs : 0 < s) : 0 ≤ scaledEnvelope β a J H N s :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) (pow_nonneg (by positivity) _))
    (mul_nonneg (Real.exp_pos _).le (hH0 s))

/-- `scaledEnvelope ≤ (1 + log N)^J · (weighted moment integrand)` for `N ≥ 1`. -/
theorem scaledEnvelope_le (β a : ℝ) (J : ℕ) (H : ℝ → ℝ) (hH0 : ∀ s, 0 ≤ H s) (N s : ℝ)
    (hN : 1 ≤ N) (hs : 0 < s) :
    scaledEnvelope β a J H N s ≤ (1 + Real.log N) ^ J
      * (s ^ (a - 1) * (1 + |Real.log s|) ^ J * (Real.exp (-β * s ^ 2) * H s)) := by
  unfold scaledEnvelope
  have h1 : (1 + |Real.log s - Real.log N|) ^ J ≤ ((1 + Real.log N) * (1 + |Real.log s|)) ^ J :=
    pow_le_pow_left₀ (by positivity) (one_add_abs_log_sub_le s N hN) J
  have hE : 0 ≤ Real.exp (-β * s ^ 2) * H s := mul_nonneg (Real.exp_pos _).le (hH0 s)
  calc s ^ (a - 1) * (1 + |Real.log s - Real.log N|) ^ J * (Real.exp (-β * s ^ 2) * H s)
      ≤ s ^ (a - 1) * ((1 + Real.log N) * (1 + |Real.log s|)) ^ J
          * (Real.exp (-β * s ^ 2) * H s) := by
        gcongr
    _ = _ := by rw [mul_pow]; ring

/-- On `(0, R]`, the remainder envelope rescales: `r^{a-1}(1+|log r|)^J H(Nr) = N^{1-a} env(Nr)`. -/
theorem envelope_eq_scaled (β a : ℝ) (J : ℕ) (H : ℝ → ℝ) (N r : ℝ) (hN : 0 < N) (hr : 0 < r) :
    Real.exp (-β * (N * r) ^ 2) * (r ^ (a - 1) * (1 + |Real.log r|) ^ J * H (N * r))
      = N ^ (1 - a) * scaledEnvelope β a J H N (N * r) := by
  unfold scaledEnvelope
  rw [Real.mul_rpow hN.le hr.le, Real.log_mul hN.ne' hr.ne',
    show Real.log N + Real.log r - Real.log N = Real.log r by ring]
  have : N ^ (1 - a) * N ^ (a - 1) = 1 := by rw [← Real.rpow_add hN]; simp
  calc Real.exp (-β * (N * r) ^ 2) * (r ^ (a - 1) * (1 + |Real.log r|) ^ J * H (N * r))
      = (N ^ (1 - a) * N ^ (a - 1)) * (Real.exp (-β * (N * r) ^ 2)
          * (r ^ (a - 1) * (1 + |Real.log r|) ^ J * H (N * r))) := by rw [this, one_mul]
    _ = _ := by ring

/-- The weighted remainder moment `M_H = ∫₀^∞ s^{a-1}(1+|log s|)^J e^{-βs²} H(s) ds`. -/
noncomputable def envMoment (β a : ℝ) (J : ℕ) (H : ℝ → ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ (a - 1) * (1 + |Real.log s|) ^ J * (Real.exp (-β * s ^ 2) * H s)

/-- Integrability of the scaled envelope on `(0, L]`. -/
theorem scaledEnvelope_integrableOn (β a : ℝ) (J : ℕ) (H : ℝ → ℝ) (hH : Measurable H)
    (hH0 : ∀ s, 0 ≤ H s)
    (hMH : IntegrableOn (fun s => s ^ (a - 1) * (1 + |Real.log s|) ^ J
      * (Real.exp (-β * s ^ 2) * H s)) (Ioi 0)) (N L : ℝ) (hN : 1 ≤ N) :
    IntegrableOn (scaledEnvelope β a J H N) (Ioc 0 L) := by
  refine Integrable.mono' ((hMH.mono_set Ioc_subset_Ioi_self).const_mul ((1 + Real.log N) ^ J))
    (scaledEnvelope_measurable β a J H hH N).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (scaledEnvelope_nonneg β a J H hH0 N s hs.1)]
  exact scaledEnvelope_le β a J H hH0 N s hN hs.1

/-- **The remainder bound**: if `|g r| ≤ r^{a-1}(1+|log r|)^J H(Nr)` on `(0, R]` then
`|∫₀^R e^{-β(Nr)²} g| ≤ N^{-a}(1+log N)^J M_H` for `N ≥ 1`; the integrand is integrable. -/
theorem remainder_bound (β a R : ℝ) (J : ℕ) (H g : ℝ → ℝ) (hR : 0 < R) (hg : Measurable g)
    (hH : Measurable H) (hH0 : ∀ s, 0 ≤ H s)
    (hMH : IntegrableOn (fun s => s ^ (a - 1) * (1 + |Real.log s|) ^ J
      * (Real.exp (-β * s ^ 2) * H s)) (Ioi 0)) (N : ℝ) (hN : 1 ≤ N)
    (hgb : ∀ r ∈ Ioc (0 : ℝ) R, |g r| ≤ r ^ (a - 1) * (1 + |Real.log r|) ^ J * H (N * r)) :
    IntegrableOn (fun r => Real.exp (-β * (N * r) ^ 2) * g r) (Ioc 0 R) ∧
    |∫ r in Ioc (0 : ℝ) R, Real.exp (-β * (N * r) ^ 2) * g r|
      ≤ N ^ (-a) * (1 + Real.log N) ^ J * envMoment β a J H := by
  have hN0 : 0 < N := by linarith
  have hNR : 0 < N * R := by positivity
  -- the dominating function on `(0, R]` and its integral
  set D : ℝ → ℝ := fun r => Real.exp (-β * (N * r) ^ 2)
    * (r ^ (a - 1) * (1 + |Real.log r|) ^ J * H (N * r)) with hD
  have hDint : IntegrableOn D (Ioc 0 R) := by
    have h1 : IntegrableOn (fun r => N ^ (1 - a) * scaledEnvelope β a J H N (N * r)) (Ioc 0 R) :=
      (integrableOn_Ioc_comp_mul_left' _ N R hN0 hR
        (scaledEnvelope_integrableOn β a J H hH hH0 hMH N (N * R) hN)).const_mul _
    exact h1.congr_fun (fun r hr => (envelope_eq_scaled β a J H N r hN0 hr.1).symm)
      measurableSet_Ioc
  have hpt : ∀ r ∈ Ioc (0 : ℝ) R, ‖Real.exp (-β * (N * r) ^ 2) * g r‖ ≤ D r := by
    intro r hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), hD]
    exact mul_le_mul_of_nonneg_left (hgb r hr) (Real.exp_pos _).le
  have hmeas : Measurable fun r => Real.exp (-β * (N * r) ^ 2) * g r :=
    (Real.measurable_exp.comp (measurable_const.mul
      ((measurable_const.mul measurable_id).pow_const _))).mul hg
  refine ⟨Integrable.mono' hDint hmeas.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hpt)), ?_⟩
  have hDval : ∫ r in Ioc (0 : ℝ) R, D r
      = N ^ (-a) * ∫ s in Ioc (0 : ℝ) (N * R), scaledEnvelope β a J H N s := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (fun r hr => envelope_eq_scaled β a J H N r hN0 hr.1), integral_const_mul,
      integral_Ioc_comp_mul_left' _ N R hN0 hR, ← mul_assoc]
    congr 1
    rw [← Real.rpow_neg_one, ← Real.rpow_add hN0]; ring_nf
  calc |∫ r in Ioc (0 : ℝ) R, Real.exp (-β * (N * r) ^ 2) * g r|
      = ‖∫ r in Ioc (0 : ℝ) R, Real.exp (-β * (N * r) ^ 2) * g r‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ r in Ioc (0 : ℝ) R, D r :=
        norm_integral_le_of_norm_le hDint ((ae_restrict_iff' measurableSet_Ioc).2
          (Filter.Eventually.of_forall hpt))
    _ = N ^ (-a) * ∫ s in Ioc (0 : ℝ) (N * R), scaledEnvelope β a J H N s := hDval
    _ ≤ N ^ (-a) * ∫ s in Ioc (0 : ℝ) (N * R), (1 + Real.log N) ^ J
          * (s ^ (a - 1) * (1 + |Real.log s|) ^ J * (Real.exp (-β * s ^ 2) * H s)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hN0.le _)
        refine setIntegral_mono_on (scaledEnvelope_integrableOn β a J H hH hH0 hMH N (N * R) hN)
          ((hMH.mono_set Ioc_subset_Ioi_self).const_mul _) measurableSet_Ioc fun s hs => ?_
        exact scaledEnvelope_le β a J H hH0 N s hN hs.1
    _ ≤ N ^ (-a) * ((1 + Real.log N) ^ J * envMoment β a J H) := by
        rw [integral_const_mul]
        have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith) _))
          (Real.rpow_nonneg hN0.le _)
        refine setIntegral_mono_set hMH ?_ Ioc_subset_Ioi_self.eventuallyLE
        exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs =>
          mul_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt hs) _) (pow_nonneg (by positivity) _))
            (mul_nonneg (Real.exp_pos _).le (hH0 s)))
    _ = _ := by ring

/-- **Density expansion hypotheses**: `ρ(r,s) = ∑ᵢ r^{αᵢ-1} (log(1/r))^{jᵢ} cᵢ(s) + E(r,s)` on
`(0,R] × (0,∞)` with `|E| ≤ r^{a-1}(1+|log r|)^J H(s)`, `αᵢ < a`, `jᵢ ≤ J`. -/
structure DensityExpansion (ρ : ℝ → ℝ → ℝ) {ι : Type*} [Fintype ι] (α : ι → ℝ) (j : ι → ℕ)
    (c : ι → ℝ → ℝ) (a R : ℝ) (J : ℕ) (H : ℝ → ℝ) : Prop where
  R_pos : 0 < R
  α_lt : ∀ i, α i < a
  j_le : ∀ i, j i ≤ J
  ρ_meas : Measurable (Function.uncurry ρ)
  c_meas : ∀ i, Measurable (c i)
  H_meas : Measurable H
  H_nonneg : ∀ s, 0 ≤ H s
  rem : ∀ r ∈ Ioc (0 : ℝ) R, ∀ s, 0 < s →
    |ρ r s - ∑ i, r ^ (α i - 1) * Real.log (1 / r) ^ j i * c i s|
      ≤ r ^ (a - 1) * (1 + |Real.log r|) ^ J * H s

/-- **The finite density-transfer theorem**: for `N ≥ 1`,
`|Z(N) − ∑ᵢ transferTerm_i(N)| ≤ N^{-a} (1+log N)^J (M_H + ∑ᵢ R^{αᵢ-a} T_i)`. -/
theorem densityTransfer_bound {ρ : ℝ → ℝ → ℝ} {ι : Type*} [Fintype ι] {α : ι → ℝ} {j : ι → ℕ}
    {c : ι → ℝ → ℝ} {a R : ℝ} {J : ℕ} {H : ℝ → ℝ} (hD : DensityExpansion ρ α j c a R J H) (β : ℝ)
    (hMc : ∀ i, IntegrableOn (fun s => s ^ (α i - 1) * (1 + |Real.log s|) ^ j i
      * (Real.exp (-β * s ^ 2) * |c i s|)) (Ioi 0))
    (hMt : ∀ i, IntegrableOn (fun s => s ^ (a - 1) * (1 + |Real.log s|) ^ j i
      * (Real.exp (-β * s ^ 2) * |c i s|)) (Ioi 0))
    (hMH : IntegrableOn (fun s => s ^ (a - 1) * (1 + |Real.log s|) ^ J
      * (Real.exp (-β * s ^ 2) * H s)) (Ioi 0)) (N : ℝ) (hN : 1 ≤ N) :
    |transferZ ρ β R N - ∑ i, transferTerm β (α i) (j i) (c i) N|
      ≤ N ^ (-a) * (1 + Real.log N) ^ J
        * (envMoment β a J H + ∑ i, R ^ (α i - a) * tailMoment β a (j i) (c i)) := by
  have hN0 : 0 < N := by linarith
  have hR := hD.R_pos
  -- the pieces
  set f : ι → ℝ → ℝ := fun i r => Real.exp (-β * (N * r) ^ 2)
    * (r ^ (α i - 1) * Real.log (1 / r) ^ j i * c i (N * r)) with hf
  set g : ℝ → ℝ := fun r => ρ r (N * r) - ∑ i, r ^ (α i - 1) * Real.log (1 / r) ^ j i * c i (N * r)
    with hg
  have hgm : Measurable g := by
    simp only [hg]
    refine (hD.ρ_meas.comp (measurable_id.prodMk (measurable_const.mul measurable_id))).sub ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    exact ((measurable_id.pow_const _).mul
      ((Real.measurable_log.comp (measurable_const.div measurable_id)).pow_const _)).mul
      ((hD.c_meas i).comp (measurable_const.mul measurable_id))
  have hgb : ∀ r ∈ Ioc (0 : ℝ) R, |g r| ≤ r ^ (a - 1) * (1 + |Real.log r|) ^ J * H (N * r) :=
    fun r hr => hD.rem r hr (N * r) (mul_pos hN0 hr.1)
  obtain ⟨hgi, hgbound⟩ := remainder_bound β a R J H g hR hgm hD.H_meas hD.H_nonneg hMH N hN hgb
  have hfi : ∀ i, IntegrableOn (f i) (Ioc 0 R) := fun i =>
    term_integrableOn β (α i) R (j i) (c i) hR (hD.c_meas i) (hMc i) N hN
  -- decomposition of Z
  have hZ : transferZ ρ β R N
      = (∑ i, ∫ r in Ioc (0 : ℝ) R, f i r)
        + ∫ r in Ioc (0 : ℝ) R, Real.exp (-β * (N * r) ^ 2) * g r := by
    unfold transferZ
    rw [← integral_finsetSum _ fun i _ => hfi i,
      ← integral_add (integrable_finsetSum _ fun i _ => hfi i) hgi]
    refine setIntegral_congr_fun measurableSet_Ioc fun r _ => ?_
    simp only [hf, hg]
    rw [mul_sub, Finset.mul_sum]
    ring
  rw [hZ]
  have hterm : ∀ i ∈ Finset.univ,
      |(∫ r in Ioc (0 : ℝ) R, f i r) - transferTerm β (α i) (j i) (c i) N|
      ≤ N ^ (-a) * (1 + Real.log N) ^ J * (R ^ (α i - a) * tailMoment β a (j i) (c i)) :=
    fun i _ => transferTerm_bound β (α i) a R (j i) J (c i) (hD.α_lt i) hR (hD.j_le i) (hD.c_meas i)
      (hMc i) (hMt i) N hN
  calc |(∑ i, ∫ r in Ioc (0 : ℝ) R, f i r)
        + (∫ r in Ioc (0 : ℝ) R, Real.exp (-β * (N * r) ^ 2) * g r)
        - ∑ i, transferTerm β (α i) (j i) (c i) N|
      = |(∑ i, ((∫ r in Ioc (0 : ℝ) R, f i r) - transferTerm β (α i) (j i) (c i) N))
          + ∫ r in Ioc (0 : ℝ) R, Real.exp (-β * (N * r) ^ 2) * g r| := by
        rw [Finset.sum_sub_distrib]; ring_nf
    _ ≤ |∑ i, ((∫ r in Ioc (0 : ℝ) R, f i r) - transferTerm β (α i) (j i) (c i) N)|
          + |∫ r in Ioc (0 : ℝ) R, Real.exp (-β * (N * r) ^ 2) * g r| := abs_add_le _ _
    _ ≤ (∑ i, |(∫ r in Ioc (0 : ℝ) R, f i r) - transferTerm β (α i) (j i) (c i) N|)
          + N ^ (-a) * (1 + Real.log N) ^ J * envMoment β a J H :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) hgbound
    _ ≤ (∑ i, N ^ (-a) * (1 + Real.log N) ^ J * (R ^ (α i - a) * tailMoment β a (j i) (c i)))
          + N ^ (-a) * (1 + Real.log N) ^ J * envMoment β a J H :=
        add_le_add (Finset.sum_le_sum hterm) le_rfl
    _ = _ := by rw [← Finset.mul_sum]; ring

end Laplace.Grammar
