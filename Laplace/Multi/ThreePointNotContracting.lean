/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseSpeedDistortion
import Laplace.Multi.FiniteEntropySupport

/-!
# The response projection is not Fisher-contracting: a three-point counterexample

Take the uniform law `ν` on `{0, 1, 2}`, the statistic `S(x) = x − 1 ∈ {−1, 0, 1}` and the data
direction `h = 1_{x = 2}`.  Along the data path `ρ_t = ν.tilted(t h)` at `t₀ = log 4`,

* `ρ_{t₀} = (1/6, 1/6, 2/3)`, `m_{t₀} = E_{ρ_{t₀}} S = 1/2`, `Cov_{ρ_{t₀}}(S,h) = 1/3`,
  `Var_{ρ_{t₀}}(h) = 2/9` (the data path's Fisher speed squared);
* the response projection `q_{1/2}` is the tilt with weights `∝ (1, x₀, x₀²)`, `x₀ = (1 + √13)/2`
  (`x₀² = x₀ + 3`), whose variance of `S` is `< 1/2`;
* hence the response path's Fisher speed squared `Cov_{ρ}(S,h)²/Var_q(S) = (1/9)/Var_q(S) > 2/9`.

So `|q'_{t₀}|_F > |ρ'_{t₀}|_F` (`responseSpeedSq_gt_dataSpeedSq`): the response projection
`ρ ↦ q_{E_ρ S}` is **not** a Fisher contraction off the family, although `h` is bounded and the
projection is a one-sided KL contraction and a Fisher-orthogonal projection on the family
(`ResponseDefect`, `ResponseDefectPythagoras`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

namespace ThreePoint

/-- The uniform law on three points. -/
noncomputable def ν3 : Measure (Fin 3) := vecMeasure fun _ ↦ (1 / 3 : ℝ)

instance : IsProbabilityMeasure ν3 :=
  isProbabilityMeasure_vecMeasure ⟨fun _ ↦ by norm_num, by simp [Finset.sum_const]⟩

/-- The statistic `S(x) = x − 1`. -/
noncomputable def S3 : Fin 1 → Fin 3 → ℝ := fun _ x ↦ (x.val : ℝ) - 1

theorem bdd_S3 : ∀ j, Bdd (S3 j) := fun _ ↦
  ⟨Measurable.of_discrete, 1, fun x ↦ by
    fin_cases x <;> simp [S3]
    norm_num⟩

/-- The data direction `h = 1_{x = 2}`. -/
noncomputable def h3 : Fin 3 → ℝ := fun x ↦ if x = 2 then 1 else 0

theorem bdd_h3 : Bdd h3 := ⟨Measurable.of_discrete, 1, fun x ↦ by fin_cases x <;> simp [h3]⟩

/-- The time `t₀ = log 4`. -/
noncomputable def t₀ : ℝ := Real.log 4

/-- Integrals against a tilt of the uniform law on three points. -/
theorem integral_tilted_ν3 (f g : Fin 3 → ℝ) :
    ∫ x, g x ∂ν3.tilted f =
      (Real.exp (f 0) * g 0 + Real.exp (f 1) * g 1 + Real.exp (f 2) * g 2) /
        (Real.exp (f 0) + Real.exp (f 1) + Real.exp (f 2)) := by
  rw [integral_tilted, ν3, integral_vecMeasure (fun _ ↦ by norm_num),
    integral_vecMeasure (fun _ ↦ by norm_num)]
  simp only [Fin.sum_univ_three, smul_eq_mul]
  have hpos : 0 < Real.exp (f 0) + Real.exp (f 1) + Real.exp (f 2) := by positivity
  field_simp

section Data

theorem exp_data_zero : Real.exp (t₀ * h3 0) = 1 := by simp [h3]
theorem exp_data_one : Real.exp (t₀ * h3 1) = 1 := by simp [h3]
theorem exp_data_two : Real.exp (t₀ * h3 2) = 4 := by
  simp only [h3, if_true, mul_one, t₀]
  exact Real.exp_log (by norm_num)

/-- Integrals against the data law at `t₀`: `E_ρ g = (g 0 + g 1 + 4 g 2)/6`. -/
theorem integral_data (g : Fin 3 → ℝ) :
    ∫ x, g x ∂ν3.tilted (fun x ↦ t₀ * h3 x) = (g 0 + g 1 + 4 * g 2) / 6 := by
  rw [integral_tilted_ν3, exp_data_zero, exp_data_one, exp_data_two]
  ring

theorem mean_data : ∫ x, S3 0 x ∂ν3.tilted (fun x ↦ t₀ * h3 x) = 1 / 2 := by
  rw [integral_data]
  simp [S3]
  norm_num

theorem cov_data : dataCov S3 ν3 h3 t₀ 0 = 1 / 3 := by
  simp only [dataCov]
  rw [integral_data, integral_data, integral_data]
  simp [S3, h3]
  norm_num

theorem var_data : lawCov (ν3.tilted fun x ↦ t₀ * h3 x) h3 h3 = 2 / 9 := by
  unfold lawCov
  rw [integral_data, integral_data]
  simp [h3]
  norm_num

end Data

section Response

/-- The root `x₀ = (1 + √13)/2` of `x² = x + 3`. -/
noncomputable def x₀ : ℝ := (1 + Real.sqrt 13) / 2

theorem x₀_sq : x₀ ^ 2 = x₀ + 3 := by
  unfold x₀
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)
  nlinarith [h]

theorem two_lt_x₀ : 2 < x₀ := by
  unfold x₀
  have h : (3 : ℝ) < Real.sqrt 13 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  linarith

theorem x₀_pos : 0 < x₀ := by linarith [two_lt_x₀]

/-- The natural parameter of the response: `θ₀ = −log x₀`. -/
noncomputable def θ₀ : Fin 1 → ℝ := fun _ ↦ -Real.log x₀

theorem dirLoss_θ₀ (x : Fin 3) : -1 * dirLoss S3 θ₀ x = Real.log x₀ * ((x.val : ℝ) - 1) := by
  simp [dirLoss, θ₀, S3]

theorem exp_resp_zero : Real.exp (-1 * dirLoss S3 θ₀ 0) = x₀⁻¹ := by
  rw [dirLoss_θ₀]
  simp [Real.exp_neg, Real.exp_log x₀_pos]

theorem exp_resp_one : Real.exp (-1 * dirLoss S3 θ₀ 1) = 1 := by
  rw [dirLoss_θ₀]
  simp

theorem exp_resp_two : Real.exp (-1 * dirLoss S3 θ₀ 2) = x₀ := by
  rw [dirLoss_θ₀]
  norm_num
  exact Real.exp_log x₀_pos

/-- Integrals against the response law: `E_q g = (g 0 + x₀ g 1 + x₀² g 2)/(1 + x₀ + x₀²)`. -/
theorem integral_resp (g : Fin 3 → ℝ) :
    ∫ x, g x ∂familyMeasure ν3 (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S3 1 θ₀ =
      (g 0 + x₀ * g 1 + x₀ ^ 2 * g 2) / (1 + x₀ + x₀ ^ 2) := by
  rw [familyMeasure_one_zero_eq_tilted bdd_S3 ν3 θ₀, integral_tilted_ν3, exp_resp_zero,
    exp_resp_one, exp_resp_two]
  have hx := x₀_pos
  field_simp

theorem mean_resp : ∫ x, S3 0 x ∂familyMeasure ν3 (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S3 1 θ₀ =
    1 / 2 := by
  rw [integral_resp]
  simp only [S3]
  have hden : (0 : ℝ) < 1 + x₀ + x₀ ^ 2 := by nlinarith [x₀_pos, sq_nonneg x₀]
  rw [div_eq_iff hden.ne']
  norm_num
  linear_combination (1 / 2 : ℝ) * x₀_sq

theorem var_resp_lt : lawCov (familyMeasure ν3 (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S3 1 θ₀) (S3 0)
    (S3 0) < 1 / 2 := by
  unfold lawCov
  rw [mean_resp, integral_resp]
  simp only [S3]
  have hden : (0 : ℝ) < 1 + x₀ + x₀ ^ 2 := by nlinarith [x₀_pos, sq_nonneg x₀]
  have hx := two_lt_x₀
  have hsq := x₀_sq
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hden]
  norm_num
  nlinarith

theorem var_resp_pos : 0 < lawCov (familyMeasure ν3 (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S3 1 θ₀)
    (S3 0) (S3 0) := by
  unfold lawCov
  rw [mean_resp, integral_resp]
  simp only [S3]
  have hden : (0 : ℝ) < 1 + x₀ + x₀ ^ 2 := by nlinarith [x₀_pos, sq_nonneg x₀]
  have hx := two_lt_x₀
  rw [sub_pos, lt_div_iff₀ hden]
  norm_num
  nlinarith

end Response

section Identification

theorem dataCov_eq : dataCov S3 ν3 h3 t₀ = fun _ ↦ (1 / 3 : ℝ) :=
  funext fun i ↦ by rw [Subsingleton.elim i 0]; exact cov_data

theorem θ₀_mem : θ₀ ∈ dirSpan ν3 (fun _ ↦ (1 : ℝ)) S3 := by
  have h := dataCov_mem_dirSpan bdd_S3 ν3 bdd_h3 t₀
  have e : θ₀ = (-3 * Real.log x₀) • dataCov S3 ν3 h3 t₀ := by
    rw [dataCov_eq]
    funext i
    simp [θ₀]
    ring
  rw [e]
  exact Submodule.smul_mem _ _ h

/-- **The natural coordinates of the data response at `t₀` are `θ₀`.** -/
theorem dataTheta_eq : dataTheta bdd_S3 ν3 bdd_h3 t₀ = ⟨θ₀, θ₀_mem⟩ := by
  have hV : pathV bdd_S3 ν3 bdd_h3 t₀ = chartV measurable_const (integrable_const 1)
      (fun _ ↦ one_pos) (one_integral_pos ν3) bdd_S3 ⟨θ₀, θ₀_mem⟩ := by
    apply Subtype.ext
    rw [pathV_apply, chartV_apply, ← mean_familyMeasure_one_zero bdd_S3 ν3 θ₀]
    congr 1
    funext i
    rw [Subsingleton.elim i 0, mean_data, mean_resp]
  unfold dataTheta
  rw [hV, chartVInv_chartV]

end Identification

/-- **The response path is strictly faster than the data path at `t₀`**: the response projection
is not a Fisher contraction. -/
theorem responseSpeedSq_gt_dataSpeedSq :
    lawCov (ν3.tilted fun x ↦ t₀ * h3 x) h3 h3 < responseSpeedSq bdd_S3 ν3 bdd_h3 t₀ := by
  have hvar : 0 < lawCov (familyMeasure ν3 (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S3 1
      (dataTheta bdd_S3 ν3 bdd_h3 t₀ : Fin 1 → ℝ)) (S3 default) (S3 default) := by
    rw [dataTheta_eq]
    exact var_resp_pos
  rw [responseSpeedSq_eq_div_of_unique bdd_S3 ν3 bdd_h3 t₀ hvar, var_data, dataTheta_eq]
  have hlt := var_resp_lt
  have hpos := var_resp_pos
  rw [show (default : Fin 1) = 0 from rfl, cov_data, lt_div_iff₀ hpos]
  nlinarith

end ThreePoint

end Laplace.Multi
