/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.StateDensity
import Laplace.Multi.RenormalisedLength
import Laplace.Multi.LogGammaTails

/-!
# Thermodynamic length detects multiplicity: the exactly solvable `(λ, m) = (1, 2)` model

The state density `ν(dℓ) = (−log ℓ) 1_{(0,1)} dℓ` has Laplace transform `Z(u) ~ (log u)/u`, i.e.
Watanabe exponents `λ = 1`, multiplicity `m = 2`. Its tilted moments are truncated log-Gamma
integrals after the substitution `s = uℓ`,

  `∫₀¹ ℓ^j e^{-uℓ}(−log ℓ) dℓ = u^{-(j+1)} (log u · Γ_j(u) − Λ_j(u))`   (`logModelMoment_eq`),

so `u² Var_u(ℓ) = (J₂J₀ − J₁²)/J₀²` with `J_j = T Γ_j − Λ_j`, `T = log u`
(`logModel_sq_mul_var`). With the tail bounds and the recursion `Λ_{j+1}(∞) = (j+1)Λ_j(∞) + j!` of
`LogGammaTails`, a purely algebraic estimate (`var_ratio_numerator_bound`) gives

  `|u² Var_u(ℓ) − (1 − 1/log u)| ≤ C / log² u`   (`logModel_var_bound`),

the radial speed `u √Var_u = 1 − 1/(2 log u) + O(1/log² u)` (`logModel_speed_bound`), and finally
the **multiplicity law** (`logModel_length_renormalised`):

  `∫_{u₀}^t √Var_u du = log t − ½ log log t + K + o(1)`,

so the featureless-line length sees the multiplicity `m = 2` through the `−(m−1)/(2√λ) log log t`
term. By `StateDensity`, the same holds for every model whose loss law is `ν` (Astra, round 25).
-/

open MeasureTheory Filter Topology Set intervalIntegral

namespace Laplace.Multi

/-! ### The moments of the model -/

/-- `M_j(u) = ∫₀¹ ℓ^j e^{-uℓ} |log ℓ| dℓ`. -/
noncomputable def logModelMoment (j : ℕ) (u : ℝ) : ℝ :=
  ∫ ℓ in Ioo (0 : ℝ) 1, ℓ ^ j * Real.exp (-(u * ℓ)) * |Real.log ℓ|

/-- `J_j(u) = log u · Γ_j(u) − Λ_j(u)`. -/
noncomputable def logModelJ (j : ℕ) (u : ℝ) : ℝ :=
  Real.log u * gammaTrunc j u - logGammaTrunc j u

/-- `s^j e^{-s} log s` is interval integrable. -/
theorem intervalIntegrable_pow_mul_exp_neg_mul_log (j : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ s ^ j * Real.exp (-s) * Real.log s) volume a b :=
  intervalIntegrable_log'.continuousOn_mul
    (by fun_prop : Continuous fun s : ℝ ↦ s ^ j * Real.exp (-s)).continuousOn

/-- **The substitution `s = uℓ`**: `M_j(u) = u^{-(j+1)} J_j(u)` for `u > 0`. -/
theorem logModelMoment_eq (j : ℕ) {u : ℝ} (hu : 0 < u) :
    logModelMoment j u = (u ^ (j + 1))⁻¹ * logModelJ j u := by
  set G : ℝ → ℝ := fun s ↦ (s / u) ^ j * Real.exp (-s) * (Real.log u - Real.log s) with hGdef
  have hG : ∀ ℓ ∈ Ioc (0 : ℝ) 1, ℓ ^ j * Real.exp (-(u * ℓ)) * |Real.log ℓ| = G (u * ℓ) :=
    fun ℓ hℓ ↦ by
    simp only [hGdef]
    rw [mul_div_cancel_left₀ _ hu.ne', Real.log_mul hu.ne' hℓ.1.ne',
      abs_of_nonpos (Real.log_nonpos hℓ.1.le hℓ.2)]
    ring
  have h1 : logModelMoment j u = ∫ ℓ in (0 : ℝ)..1, G (u * ℓ) := by
    rw [logModelMoment, ← integral_Ioc_eq_integral_Ioo, integral_of_le zero_le_one]
    exact setIntegral_congr_fun measurableSet_Ioc hG
  rw [h1, integral_comp_mul_left (f := G) hu.ne', mul_zero, mul_one, smul_eq_mul]
  have h2 : (∫ s in (0 : ℝ)..u, G s) = (u ^ j)⁻¹ * logModelJ j u := by
    simp only [hGdef]
    have e : ∀ s, (s / u) ^ j * Real.exp (-s) * (Real.log u - Real.log s) =
        (u ^ j)⁻¹ * (Real.log u * (s ^ j * Real.exp (-s)) - s ^ j * Real.exp (-s) * Real.log s) :=
      fun s ↦ by rw [div_pow]; ring
    simp_rw [e]
    have hc : Continuous fun s : ℝ ↦ s ^ j * Real.exp (-s) := by fun_prop
    rw [intervalIntegral.integral_const_mul,
      integral_sub ((hc.intervalIntegrable (μ := volume) 0 u).const_mul _)
        (intervalIntegrable_pow_mul_exp_neg_mul_log j 0 u), intervalIntegral.integral_const_mul]
    rfl
  rw [h2, pow_succ, mul_inv]
  ring

/-- The moments of the model are the numerators of its posterior expectations. -/
theorem priorZ_logModel (u : ℝ) :
    priorZ (volume.restrict (Ioo (0 : ℝ) 1)) (fun ℓ ↦ |Real.log ℓ|) id u = logModelMoment 0 u := by
  simp [priorZ, logModelMoment]

theorem priorExp_logModel_one (u : ℝ) :
    priorExp (volume.restrict (Ioo (0 : ℝ) 1)) (fun ℓ ↦ |Real.log ℓ|) id id u =
      logModelMoment 1 u / logModelMoment 0 u := by
  simp [priorExp, priorZ, logModelMoment]

theorem priorExp_logModel_two (u : ℝ) :
    priorExp (volume.restrict (Ioo (0 : ℝ) 1)) (fun ℓ ↦ |Real.log ℓ|) id (fun x ↦ id x * id x) u =
      logModelMoment 2 u / logModelMoment 0 u := by
  simp only [priorExp, priorZ, logModelMoment, id_eq, pow_zero, one_mul, sq]

/-- **The radial Fisher speed of the model**: `u² Var_u(ℓ) = (J₂J₀ − J₁²)/J₀²`. -/
theorem logModel_sq_mul_var {u : ℝ} (hu : 0 < u) (hJ : logModelJ 0 u ≠ 0) :
    u ^ 2 * priorCov (volume.restrict (Ioo (0 : ℝ) 1)) (fun ℓ ↦ |Real.log ℓ|) id id id u =
      (logModelJ 2 u * logModelJ 0 u - logModelJ 1 u ^ 2) / logModelJ 0 u ^ 2 := by
  unfold priorCov
  rw [priorExp_logModel_two, priorExp_logModel_one, logModelMoment_eq 0 hu, logModelMoment_eq 1 hu,
    logModelMoment_eq 2 hu]
  have hu0 : u ≠ 0 := hu.ne'
  field_simp
  ring

/-! ### The algebraic estimate -/

/-- `|ab| ≤ AB` from `|a| ≤ A`, `|b| ≤ B`. -/
theorem abs_mul_le_of_abs_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) (le_trans (abs_nonneg _) ha)

/-- **The algebraic estimate**: if `x_j = g_j − l_j τ + O(τ²)` with `g = (1, 1, 2)`,
`l = (l₀, l₀+1, 2l₀+3)`, then `(x₂x₀ − x₁²) − (1 − τ)x₀² = O(τ²)`, with an explicit constant. -/
theorem var_ratio_numerator_bound {τ x₀ x₁ x₂ l₀ D : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hD : 0 ≤ D)
    (h₀ : |x₀ - (1 - l₀ * τ)| ≤ D * τ ^ 2) (h₁ : |x₁ - (1 - (l₀ + 1) * τ)| ≤ D * τ ^ 2)
    (h₂ : |x₂ - (2 - (2 * l₀ + 3) * τ)| ≤ D * τ ^ 2) :
    |(x₂ * x₀ - x₁ ^ 2) - (1 - τ) * x₀ ^ 2| ≤
      (|l₀| + 1 + l₀ ^ 2 + 6 * (5 + 2 * |l₀|) * D + 3 * D ^ 2) * τ ^ 2 := by
  obtain ⟨d₀, rfl⟩ : ∃ d, x₀ = (1 - l₀ * τ) + d := ⟨x₀ - (1 - l₀ * τ), by ring⟩
  obtain ⟨d₁, rfl⟩ : ∃ d, x₁ = (1 - (l₀ + 1) * τ) + d := ⟨x₁ - (1 - (l₀ + 1) * τ), by ring⟩
  obtain ⟨d₂, rfl⟩ : ∃ d, x₂ = (2 - (2 * l₀ + 3) * τ) + d := ⟨x₂ - (2 - (2 * l₀ + 3) * τ), by ring⟩
  simp only [add_sub_cancel_left] at h₀ h₁ h₂
  have hτ2 : 0 ≤ τ ^ 2 := by positivity
  have hτ3 : τ ^ 3 ≤ τ ^ 2 := by nlinarith
  have hδ0 : 0 ≤ D * τ ^ 2 := by positivity
  -- bounds on the leading terms
  have hl : 0 ≤ |l₀| := abs_nonneg _
  have hy₀ : |1 - l₀ * τ| ≤ 5 + 2 * |l₀| := by
    calc |1 - l₀ * τ| ≤ |1| + |l₀ * τ| := abs_sub _ _
      _ = 1 + |l₀| * τ := by rw [abs_one, abs_mul, abs_of_pos hτ0]
      _ ≤ 5 + 2 * |l₀| := by nlinarith
  have hy₁ : |1 - (l₀ + 1) * τ| ≤ 5 + 2 * |l₀| := by
    calc |1 - (l₀ + 1) * τ| ≤ |1| + |(l₀ + 1) * τ| := abs_sub _ _
      _ = 1 + |l₀ + 1| * τ := by rw [abs_one, abs_mul, abs_of_pos hτ0]
      _ ≤ 1 + (|l₀| + 1) * τ := by gcongr; exact abs_add_le _ _ |>.trans (by rw [abs_one])
      _ ≤ 5 + 2 * |l₀| := by nlinarith
  have hy₂ : |2 - (2 * l₀ + 3) * τ| ≤ 5 + 2 * |l₀| := by
    calc |2 - (2 * l₀ + 3) * τ| ≤ |2| + |(2 * l₀ + 3) * τ| := abs_sub _ _
      _ = 2 + |2 * l₀ + 3| * τ := by rw [abs_two, abs_mul, abs_of_pos hτ0]
      _ ≤ 2 + (2 * |l₀| + 3) * τ := by
          gcongr
          calc |2 * l₀ + 3| ≤ |2 * l₀| + |3| := abs_add_le _ _
            _ = 2 * |l₀| + 3 := by rw [abs_mul, abs_two, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      _ ≤ 5 + 2 * |l₀| := by nlinarith
  -- the exact decomposition
  have key : (((2 - (2 * l₀ + 3) * τ) + d₂) * ((1 - l₀ * τ) + d₀) - ((1 - (l₀ + 1) * τ) + d₁) ^ 2)
      - (1 - τ) * ((1 - l₀ * τ) + d₀) ^ 2 =
      (-(l₀ + 1) * τ ^ 2 + l₀ ^ 2 * τ ^ 3) +
      ((2 - (2 * l₀ + 3) * τ) * d₀ + d₂ * (1 - l₀ * τ) + d₂ * d₀ - 2 * (1 - (l₀ + 1) * τ) * d₁
        - d₁ ^ 2 - (1 - τ) * (2 * (1 - l₀ * τ) * d₀ + d₀ ^ 2)) := by ring
  rw [key]
  -- the polynomial part
  have hP : |-(l₀ + 1) * τ ^ 2 + l₀ ^ 2 * τ ^ 3| ≤ (|l₀| + 1 + l₀ ^ 2) * τ ^ 2 := by
    calc |-(l₀ + 1) * τ ^ 2 + l₀ ^ 2 * τ ^ 3| ≤ |-(l₀ + 1) * τ ^ 2| + |l₀ ^ 2 * τ ^ 3| :=
          abs_add_le _ _
      _ = |l₀ + 1| * τ ^ 2 + l₀ ^ 2 * τ ^ 3 := by
          rw [abs_mul, abs_neg, abs_of_nonneg hτ2, abs_mul, abs_of_nonneg (sq_nonneg l₀),
            abs_of_nonneg (pow_nonneg hτ0.le 3)]
      _ ≤ (|l₀| + 1) * τ ^ 2 + l₀ ^ 2 * τ ^ 2 := by
          gcongr
          exact abs_add_le _ _ |>.trans (by rw [abs_one])
      _ = (|l₀| + 1 + l₀ ^ 2) * τ ^ 2 := by ring
  -- the perturbative part
  set Y := 5 + 2 * |l₀| with hY
  set δ := D * τ ^ 2 with hδ
  have hY0 : 0 ≤ Y := by positivity
  have e1 := abs_mul_le_of_abs_le hy₂ h₀
  have e2 := abs_mul_le_of_abs_le h₂ hy₀
  have e3 := abs_mul_le_of_abs_le h₂ h₀
  have e4 : |2 * (1 - (l₀ + 1) * τ) * d₁| ≤ 2 * Y * δ := by
    rw [mul_assoc, abs_mul, abs_two, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_mul_le_of_abs_le hy₁ h₁) (by norm_num)
  have e5 : |d₁ ^ 2| ≤ δ * δ := by rw [sq]; exact abs_mul_le_of_abs_le h₁ h₁
  have e6 : |2 * (1 - l₀ * τ) * d₀ + d₀ ^ 2| ≤ 2 * Y * δ + δ * δ := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [mul_assoc, abs_mul, abs_two, mul_assoc]
      exact mul_le_mul_of_nonneg_left (abs_mul_le_of_abs_le hy₀ h₀) (by norm_num)
    · rw [sq]; exact abs_mul_le_of_abs_le h₀ h₀
  have e6' : |(1 - τ) * (2 * (1 - l₀ * τ) * d₀ + d₀ ^ 2)| ≤ 2 * Y * δ + δ * δ := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    exact (mul_le_of_le_one_left (abs_nonneg _) (by linarith)).trans e6
  have hQ : |(2 - (2 * l₀ + 3) * τ) * d₀ + d₂ * (1 - l₀ * τ) + d₂ * d₀ - 2 * (1 - (l₀ + 1) * τ) * d₁
      - d₁ ^ 2 - (1 - τ) * (2 * (1 - l₀ * τ) * d₀ + d₀ ^ 2)| ≤ 6 * Y * δ + 3 * (δ * δ) := by
    calc _ ≤ |(2 - (2 * l₀ + 3) * τ) * d₀ + d₂ * (1 - l₀ * τ) + d₂ * d₀
          - 2 * (1 - (l₀ + 1) * τ) * d₁ - d₁ ^ 2| +
          |(1 - τ) * (2 * (1 - l₀ * τ) * d₀ + d₀ ^ 2)| := abs_sub _ _
      _ ≤ (|(2 - (2 * l₀ + 3) * τ) * d₀ + d₂ * (1 - l₀ * τ) + d₂ * d₀ - 2 * (1 - (l₀ + 1) * τ) * d₁|
          + |d₁ ^ 2|) + |(1 - τ) * (2 * (1 - l₀ * τ) * d₀ + d₀ ^ 2)| := by
          gcongr
          exact abs_sub _ _
      _ ≤ ((|(2 - (2 * l₀ + 3) * τ) * d₀ + d₂ * (1 - l₀ * τ) + d₂ * d₀|
          + |2 * (1 - (l₀ + 1) * τ) * d₁|) + |d₁ ^ 2|) +
          |(1 - τ) * (2 * (1 - l₀ * τ) * d₀ + d₀ ^ 2)| := by
          gcongr
          exact abs_sub _ _
      _ ≤ (((|(2 - (2 * l₀ + 3) * τ) * d₀| + |d₂ * (1 - l₀ * τ)|) + |d₂ * d₀|)
          + |2 * (1 - (l₀ + 1) * τ) * d₁|) + |d₁ ^ 2| +
          |(1 - τ) * (2 * (1 - l₀ * τ) * d₀ + d₀ ^ 2)| := by
          gcongr
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (((Y * δ + δ * Y) + δ * δ) + 2 * Y * δ) + δ * δ + (2 * Y * δ + δ * δ) := by
          gcongr
      _ = 6 * Y * δ + 3 * (δ * δ) := by ring
  have hδδ : δ * δ ≤ D ^ 2 * τ ^ 2 := by
    rw [hδ]
    have : D * τ ^ 2 * (D * τ ^ 2) = D ^ 2 * τ ^ 2 * τ ^ 2 := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) (by nlinarith)
  calc |(-(l₀ + 1) * τ ^ 2 + l₀ ^ 2 * τ ^ 3) + _| ≤ (|l₀| + 1 + l₀ ^ 2) * τ ^ 2 +
        (6 * Y * δ + 3 * (δ * δ)) := (abs_add_le _ _).trans (add_le_add hP hQ)
    _ ≤ (|l₀| + 1 + l₀ ^ 2) * τ ^ 2 + (6 * Y * (D * τ ^ 2) + 3 * (D ^ 2 * τ ^ 2)) := by
        gcongr
    _ = (|l₀| + 1 + l₀ ^ 2 + 6 * (5 + 2 * |l₀|) * D + 3 * D ^ 2) * τ ^ 2 := by
        rw [hY]
        ring


/-! ### The variance bound for the model -/

/-- `Λ₁(∞) = Λ₀(∞) + 1`. -/
theorem logGammaFull_one : logGammaFull 1 = logGammaFull 0 + 1 := by
  have := logGammaFull_succ 0
  simpa using this

/-- `Λ₂(∞) = 2Λ₀(∞) + 3`. -/
theorem logGammaFull_two : logGammaFull 2 = 2 * logGammaFull 0 + 3 := by
  have := logGammaFull_succ 1
  rw [logGammaFull_one] at this
  norm_num [Nat.factorial] at this
  linarith

/-- The constant of the variance bound of the model. -/
noncomputable def logModelC : ℝ :=
  4 * (|logGammaFull 0| + 1 + logGammaFull 0 ^ 2 + 6 * (5 + 2 * |logGammaFull 0|) * 240 +
    3 * 240 ^ 2)

theorem logModelC_pos : 0 < logModelC := by
  unfold logModelC
  positivity

/-- **The variance bound of the model**: for `log u ≥ 481 + 2|Λ₀(∞)|`, `J₀ ≥ (log u)/2` and
`|u² Var_u(ℓ) − (1 − 1/log u)| ≤ C/log² u`. -/
theorem logModel_var_bound {u : ℝ} (hu1 : 1 < u)
    (hT : 481 + 2 * |logGammaFull 0| ≤ Real.log u) :
    Real.log u / 2 ≤ logModelJ 0 u ∧
    |u ^ 2 * priorCov (volume.restrict (Ioo (0 : ℝ) 1)) (fun ℓ ↦ |Real.log ℓ|) id id id u -
      (1 - 1 / Real.log u)| ≤ logModelC / Real.log u ^ 2 := by
  set T := Real.log u with hTdef
  set l₀ := logGammaFull 0 with hl₀
  have hl : 0 ≤ |l₀| := abs_nonneg _
  have hT0 : 0 < T := by linarith
  have hu0 : 0 < u := lt_trans zero_lt_one hu1
  have hTu : T ≤ u := by have := Real.log_le_sub_one_of_pos hu0; linarith
  have hT1 : 1 ≤ T := by linarith
  -- tail bounds in terms of `T`
  have hinv : 1 / u ^ 2 ≤ 1 / T ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hT0.le hTu 2)
  have hG : ∀ j, j ≤ 2 → |gammaTrunc j u - (j.factorial : ℝ)| ≤ 120 / T ^ 2 := fun j hj ↦ by
    refine (abs_gammaTrunc_sub_le j hu1.le).trans ?_
    have h1 : ((j + 2).factorial : ℝ) ≤ 120 := by
      interval_cases j <;> norm_num [Nat.factorial]
    calc ((j + 2).factorial : ℝ) / u ^ 2 ≤ 120 / u ^ 2 := by gcongr
      _ = 120 * (1 / u ^ 2) := by ring
      _ ≤ 120 * (1 / T ^ 2) := by gcongr
      _ = 120 / T ^ 2 := by ring
  have hL : ∀ j, j ≤ 2 → |logGammaTrunc j u - logGammaFull j| ≤ 120 / T ^ 2 := fun j hj ↦ by
    refine (abs_logGammaTrunc_sub_le j hu1.le).trans ?_
    have h1 : ((j + 3).factorial : ℝ) ≤ 120 := by
      interval_cases j <;> norm_num [Nat.factorial]
    calc ((j + 3).factorial : ℝ) / u ^ 2 ≤ 120 / u ^ 2 := by gcongr
      _ = 120 * (1 / u ^ 2) := by ring
      _ ≤ 120 * (1 / T ^ 2) := by gcongr
      _ = 120 / T ^ 2 := by ring
  -- the normalised coordinates
  set τ := 1 / T with hτ
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 := by rw [hτ, div_le_one hT0]; exact hT1
  have hτT : τ * T = 1 := by rw [hτ]; field_simp
  have h120 : (120 : ℝ) / T ^ 2 = 120 * τ ^ 2 := by rw [hτ]; field_simp
  set x₀ := gammaTrunc 0 u - logGammaTrunc 0 u * τ with hx₀
  set x₁ := gammaTrunc 1 u - logGammaTrunc 1 u * τ with hx₁
  set x₂ := gammaTrunc 2 u - logGammaTrunc 2 u * τ with hx₂
  have hJ : ∀ j, logModelJ j u = T * (gammaTrunc j u - logGammaTrunc j u * τ) := fun j ↦ by
    unfold logModelJ
    rw [← hTdef, hτ, mul_sub, mul_one_div, mul_div_cancel₀ _ hT0.ne']
  -- the perturbation bounds
  have hpert : ∀ j, j ≤ 2 → ∀ g l : ℝ, (j.factorial : ℝ) = g → logGammaFull j = l →
      |(gammaTrunc j u - logGammaTrunc j u * τ) - (g - l * τ)| ≤ 240 * τ ^ 2 :=
    fun j hj g l hg hl' ↦ by
    have e : (gammaTrunc j u - logGammaTrunc j u * τ) - (g - l * τ) =
        (gammaTrunc j u - g) - (logGammaTrunc j u - l) * τ := by ring
    rw [e]
    have h1 := hG j hj
    have h2 := hL j hj
    rw [hg] at h1
    rw [hl'] at h2
    rw [h120] at h1 h2
    calc |(gammaTrunc j u - g) - (logGammaTrunc j u - l) * τ|
        ≤ |gammaTrunc j u - g| + |(logGammaTrunc j u - l) * τ| := abs_sub _ _
      _ = |gammaTrunc j u - g| + |logGammaTrunc j u - l| * τ := by
          rw [abs_mul, abs_of_pos hτ0]
      _ ≤ 120 * τ ^ 2 + 120 * τ ^ 2 * τ := by gcongr
      _ ≤ 240 * τ ^ 2 := by nlinarith
  have hp₀ := hpert 0 (by norm_num) 1 l₀ (by norm_num) rfl
  have hp₁ := hpert 1 (by norm_num) 1 (l₀ + 1) (by norm_num) logGammaFull_one
  have hp₂ := hpert 2 (by norm_num) 2 (2 * l₀ + 3) (by norm_num [Nat.factorial]) logGammaFull_two
  -- `x₀ ≥ 1/2`
  have hx₀half : 1 / 2 ≤ x₀ := by
    have h1 := hG 0 (by norm_num)
    have h2 := hL 0 (by norm_num)
    rw [h120] at h1 h2
    simp only [Nat.factorial_zero, Nat.cast_one] at h1
    rw [abs_le] at h1 h2
    have hτsq : τ ^ 2 ≤ τ := by nlinarith
    have hτT' : (240 + |l₀|) * τ ≤ 1 / 2 := by
      rw [hτ, mul_one_div, div_le_iff₀ hT0]
      linarith
    have hl₀τ : logGammaTrunc 0 u * τ ≤ (|l₀| + 120 * τ ^ 2) * τ := by
      refine mul_le_mul_of_nonneg_right ?_ hτ0.le
      have := le_abs_self l₀
      linarith
    rw [hx₀]
    nlinarith
  have hx₀pos : 0 < x₀ := by linarith
  refine ⟨?_, ?_⟩
  · rw [hJ 0]
    calc T / 2 = T * (1 / 2) := by ring
      _ ≤ T * x₀ := by gcongr
  -- the algebraic estimate
  have hnum := var_ratio_numerator_bound hτ0 hτ1 (by norm_num : (0 : ℝ) ≤ 240) hp₀ hp₁ hp₂
  have hJ0 : logModelJ 0 u ≠ 0 := by rw [hJ 0]; positivity
  rw [logModel_sq_mul_var hu0 hJ0, hJ 0, hJ 1, hJ 2]
  have hratio : (T * x₂ * (T * x₀) - (T * x₁) ^ 2) / (T * x₀) ^ 2 - (1 - 1 / T) =
      ((x₂ * x₀ - x₁ ^ 2) - (1 - τ) * x₀ ^ 2) / x₀ ^ 2 := by
    rw [hτ]
    field_simp
  rw [hratio, abs_div, abs_of_pos (by positivity : (0 : ℝ) < x₀ ^ 2)]
  have hx₀sq : 1 / 4 ≤ x₀ ^ 2 := by nlinarith
  calc |(x₂ * x₀ - x₁ ^ 2) - (1 - τ) * x₀ ^ 2| / x₀ ^ 2
      ≤ ((|l₀| + 1 + l₀ ^ 2 + 6 * (5 + 2 * |l₀|) * 240 + 3 * 240 ^ 2) * τ ^ 2) / (1 / 4) := by
        gcongr
    _ = logModelC / T ^ 2 := by
        rw [logModelC, hτ]
        field_simp
        ring

/-- `|√a − b| ≤ ε/b` from `|a − b²| ≤ ε` (`a ≥ 0`, `b > 0`). -/
theorem abs_sqrt_sub_le_of_abs_sub_sq_le {a b ε : ℝ} (hb : 0 < b) (ha : 0 ≤ a)
    (h : |a - b ^ 2| ≤ ε) : |Real.sqrt a - b| ≤ ε / b := by
  have hsum : 0 < Real.sqrt a + b := by positivity
  have key : Real.sqrt a - b = (a - b ^ 2) / (Real.sqrt a + b) := by
    rw [eq_div_iff hsum.ne']
    linear_combination Real.sq_sqrt ha
  rw [key, abs_div, abs_of_pos hsum]
  calc |a - b ^ 2| / (Real.sqrt a + b) ≤ |a - b ^ 2| / b :=
        div_le_div_of_nonneg_left (abs_nonneg _) hb (le_add_of_nonneg_left (Real.sqrt_nonneg _))
    _ ≤ ε / b := by gcongr

/-- **The radial speed of the model**: `u √Var_u(ℓ) = 1 − 1/(2 log u) + O(1/log² u)`. -/
theorem logModel_speed_bound {u : ℝ} (hu1 : 1 < u) (hT : 4 * (logModelC + 1) ≤ Real.log u) :
    |Real.sqrt (u ^ 2 * priorCov (volume.restrict (Ioo (0 : ℝ) 1)) (fun ℓ ↦ |Real.log ℓ|)
        id id id u) - (1 - (1 / 2) / Real.log u)| ≤ 2 * (logModelC + 1) / Real.log u ^ 2 := by
  have hC := logModelC_pos
  have hT' : 481 + 2 * |logGammaFull 0| ≤ Real.log u := by
    refine le_trans ?_ hT
    unfold logModelC
    nlinarith [abs_nonneg (logGammaFull 0), sq_nonneg (logGammaFull 0)]
  obtain ⟨_, hvar⟩ := logModel_var_bound hu1 hT'
  set T := Real.log u with hTdef
  set a := u ^ 2 * priorCov (volume.restrict (Ioo (0 : ℝ) 1)) (fun ℓ ↦ |Real.log ℓ|) id id id u
    with ha
  set C := logModelC with hCdef
  have hT0 : 0 < T := by linarith
  set τ := 1 / T with hτ
  have hτ0 : 0 < τ := by positivity
  have hτle : τ * (4 * (C + 1)) ≤ 1 := by
    rw [hτ, div_mul_eq_mul_div, div_le_one hT0]
    linarith
  have hτ4 : τ ≤ 1 / 4 := by nlinarith
  have hCτ : (C + 1) * τ ^ 2 ≤ 1 / 16 := by nlinarith
  have hvar' : |a - (1 - τ)| ≤ C * τ ^ 2 := by
    have : C / T ^ 2 = C * τ ^ 2 := by rw [hτ]; field_simp
    rw [← this]
    exact hvar
  set b := 1 - τ / 2 with hb
  have hb34 : 3 / 4 ≤ b := by rw [hb]; linarith
  have hb0 : 0 < b := by linarith
  have hbsq : b ^ 2 = 1 - τ + τ ^ 2 / 4 := by rw [hb]; ring
  have hab : |a - b ^ 2| ≤ (C + 1) * τ ^ 2 := by
    rw [hbsq]
    calc |a - (1 - τ + τ ^ 2 / 4)| = |(a - (1 - τ)) - τ ^ 2 / 4| := by ring_nf
      _ ≤ |a - (1 - τ)| + |τ ^ 2 / 4| := abs_sub _ _
      _ ≤ C * τ ^ 2 + τ ^ 2 / 4 := by
          gcongr
          rw [abs_of_nonneg (by positivity)]
      _ ≤ (C + 1) * τ ^ 2 := by nlinarith
  have ha0 : 0 ≤ a := by
    rw [abs_le] at hab
    nlinarith
  have key := abs_sqrt_sub_le_of_abs_sub_sq_le hb0 ha0 hab
  have e1 : (1 : ℝ) - (1 / 2) / T = b := by rw [hb, hτ]; ring
  have e2 : 2 * (C + 1) / T ^ 2 = 2 * ((C + 1) * τ ^ 2) := by rw [hτ]; field_simp
  rw [e1, e2]
  refine key.trans ?_
  rw [div_le_iff₀ hb0]
  nlinarith [mul_nonneg hC.le (sq_nonneg τ)]

/-! ### The multiplicity law -/

/-- The truncated integrals are continuous in `u`. -/
theorem continuous_gammaTrunc (j : ℕ) : Continuous (gammaTrunc j) :=
  continuous_primitive (fun a b ↦ (by fun_prop : Continuous fun s : ℝ ↦
    s ^ j * Real.exp (-s)).intervalIntegrable (μ := volume) a b) 0

theorem continuous_logGammaTrunc (j : ℕ) : Continuous (logGammaTrunc j) :=
  continuous_primitive (intervalIntegrable_pow_mul_exp_neg_mul_log j) 0

theorem continuousOn_logModelJ (j : ℕ) : ContinuousOn (logModelJ j) (Ioi 0) := by
  unfold logModelJ
  exact ((Real.continuousOn_log.mono fun x hx ↦ (ne_of_gt hx)).mul
    (continuous_gammaTrunc j).continuousOn).sub (continuous_logGammaTrunc j).continuousOn

/-- **Thermodynamic length detects multiplicity**: for the state density `(−log ℓ) dℓ` on
`(0,1)` (`λ = 1`, `m = 2`), the radial response length satisfies
`∫_{u₀}^t √Var_u du = log t − ½ log log t + K + o(1)`. -/
theorem logModel_length_renormalised :
    ∃ u₀ : ℝ, 1 < u₀ ∧ ∃ K : ℝ, Tendsto (fun t ↦ (∫ u in u₀..t, Real.sqrt (priorCov
      (volume.restrict (Ioo (0 : ℝ) 1)) (fun ℓ ↦ |Real.log ℓ|) id id id u)) -
      (Real.log t - (1 / 2) * Real.log (Real.log t))) atTop (𝓝 K) := by
  have hC := logModelC_pos
  set T₀ := 4 * (logModelC + 1) with hT₀
  set u₀ := Real.exp T₀ with hu₀
  have hu₀1 : 1 < u₀ := Real.one_lt_exp_iff.mpr (by positivity)
  have hlog : ∀ u, u₀ ≤ u → T₀ ≤ Real.log u := fun u hu ↦ by
    rw [← Real.log_exp T₀]
    exact (Real.log_le_log_iff (Real.exp_pos _) (lt_of_lt_of_le (Real.exp_pos _) hu)).mpr hu
  have hu1 : ∀ u, u₀ ≤ u → 1 < u := fun u hu ↦ lt_of_lt_of_le hu₀1 hu
  -- the speed
  set f : ℝ → ℝ := fun u ↦ Real.sqrt (u ^ 2 * priorCov (volume.restrict (Ioo (0 : ℝ) 1))
    (fun ℓ ↦ |Real.log ℓ|) id id id u) with hf
  have hbound : ∀ u, u₀ ≤ u → |f u - (1 - (1 / 2) / Real.log u)| ≤
      2 * (logModelC + 1) / Real.log u ^ 2 := fun u hu ↦
    logModel_speed_bound (hu1 u hu) (hlog u hu)
  -- continuity of the speed on `[u₀, ∞)`
  have hJ0 : ∀ u, u₀ ≤ u → logModelJ 0 u ≠ 0 := fun u hu ↦ by
    have h := (logModel_var_bound (hu1 u hu) (by
      have := hlog u hu
      refine le_trans ?_ this
      rw [hT₀]
      unfold logModelC
      nlinarith [abs_nonneg (logGammaFull 0), sq_nonneg (logGammaFull 0)])).1
    have : 0 < Real.log u := Real.log_pos (hu1 u hu)
    linarith
  have hfc : ContinuousOn f (Ici u₀) := by
    have e : ∀ u ∈ Ici u₀, f u = Real.sqrt ((logModelJ 2 u * logModelJ 0 u - logModelJ 1 u ^ 2) /
        logModelJ 0 u ^ 2) := fun u hu ↦ by
      rw [hf]
      simp only
      rw [logModel_sq_mul_var (lt_trans zero_lt_one (hu1 u hu)) (hJ0 u hu)]
    refine ContinuousOn.congr ?_ e
    have hsub : Ici u₀ ⊆ Ioi 0 := fun u hu ↦ lt_trans zero_lt_one (hu1 u hu)
    refine Real.continuous_sqrt.comp_continuousOn (ContinuousOn.div ?_ ?_ fun u hu ↦ ?_)
    · exact (((continuousOn_logModelJ 2).mono hsub).mul ((continuousOn_logModelJ 0).mono hsub)).sub
        (((continuousOn_logModelJ 1).mono hsub).pow 2)
    · exact ((continuousOn_logModelJ 0).mono hsub).pow 2
    · exact pow_ne_zero 2 (hJ0 u hu)
  obtain ⟨K, hK⟩ := tendsto_renormalised_length (A := 1) (B := 1 / 2) hu₀1 hfc hbound
  refine ⟨u₀, hu₀1, K, hK.congr' ?_⟩
  filter_upwards [eventually_ge_atTop u₀] with t ht
  simp only [one_mul]
  congr 1
  refine integral_congr fun u hu ↦ ?_
  rw [uIcc_of_le ht] at hu
  have hu0 : 0 < u := lt_trans zero_lt_one (hu1 u hu.1)
  rw [hf]
  simp only
  rw [Real.sqrt_mul (sq_nonneg u), Real.sqrt_sq hu0.le, mul_div_cancel_left₀ _ hu0.ne']

end Laplace.Multi
