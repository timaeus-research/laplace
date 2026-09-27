/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseObservableIIDExpansion

/-!
# The joint sampling covariance of posterior expectations

For bounded observables `F, H` the reset-localised increments of the posterior expectations,
`A_F(z) = 1_{‖z‖≤δ} (f_F(m₀+z) − f_F(m₀))` (`locInc`), are controlled globally by the linear
influence `ℓ_F(z) = ⟨u_F, z⟩` and the displacement size (`abs_locInc_sub_dotJ_le`,
`abs_locInc_le`):

`|A_F − ℓ_F| ≤ c_F ‖z‖²`,  `|A_F| ≤ d_F ‖z‖`,  `|ℓ_F| ≤ a_F ‖z‖`,

with `a_F = ∑_j |u_{F,j}|`, `b_F = ½‖H_F‖ + K_F δ`, `c_F = max(b_F, a_F/δ)`, `d_F = a_F + b_F δ`.
Hence, **without any fourth-moment estimate**,

* `|A_F A_H − ℓ_F ℓ_H| ≤ (c_F d_H + a_F c_H) ‖z‖³` (`abs_mul_sub_mul_le`);
* for a centred displacement law with moments `M₂, M₃`
  (`abs_lawCov_locInc_sub_le`):
  `|Cov(A_F, A_H) − E[ℓ_F ℓ_H]| ≤ (c_F d_H + a_F c_H) M₃ + c_F c_H M₂²`;
* **the i.i.d. joint covariance** (`iid_lawCov_locInc_sub_le`): for `n` i.i.d. samples from a data
  law `D` with mean `m₀`,
  `Cov(f̂_{F,loc}, f̂_{H,loc}) = Σ_D(u_F, u_H)/n + O(n^{-3/2})` with an explicit constant;
* **the coordinate–observable cross term** (`iid_integral_dotJ_mul_locInc_sub_le`):
  `E[⟨u, ξ_n⟩ (f̂_{F,loc} − f_F(m₀))] = Σ_D(u, u_F)/n + O(n^{-3/2})`.

The leading term is the data covariance of the regression features: the fluctuations of finitely
many posterior expectations are jointly those of their linear influences, at the sampling scale
`1/√n`, with the nonlinear corrections one order smaller.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Real

/-- The product of two localised increments differs from the product of the linear terms by a
cubic amount. -/
theorem abs_mul_sub_mul_le {A ℓ A' ℓ' r c d a c' : ℝ} (h1 : |A - ℓ| ≤ c * r ^ 2)
    (h2 : |A'| ≤ d * r) (h3 : |ℓ| ≤ a * r) (h4 : |A' - ℓ'| ≤ c' * r ^ 2) :
    |A * A' - ℓ * ℓ'| ≤ (c * d + a * c') * r ^ 3 := by
  have e : A * A' - ℓ * ℓ' = (A - ℓ) * A' + ℓ * (A' - ℓ') := by ring
  rw [e]
  calc |(A - ℓ) * A' + ℓ * (A' - ℓ')| ≤ |(A - ℓ) * A'| + |ℓ * (A' - ℓ')| := abs_add_le _ _
    _ = |A - ℓ| * |A'| + |ℓ| * |A' - ℓ'| := by rw [abs_mul, abs_mul]
    _ ≤ (c * r ^ 2) * (d * r) + (a * r) * (c' * r ^ 2) :=
        add_le_add (mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1))
          (mul_le_mul h3 h4 (abs_nonneg _) ((abs_nonneg _).trans h3))
    _ = (c * d + a * c') * r ^ 3 := by ring

/-- `√n ≤ n` for `n ≥ 1`, so `1/n² ≤ 1/(n√n)`. -/
theorem sqrt_le_self_nat {n : ℕ} (hn : 0 < n) : Real.sqrt n ≤ n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc Real.sqrt n ≤ Real.sqrt (n ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = n := Real.sqrt_sq (by linarith)

end Real

section Law

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

variable {δ : ℝ}

/-- The localisation ball. -/
local notation "cball" => Metric.closedBall (0 : 𝕍) δ

/-- **The reset-localised increment** of the posterior expectation:
`A_F(z) = 1_{‖z‖≤δ} (f_F(m₀+z) − f_F(m₀))`. -/
noncomputable def locInc (F : X → ℝ) (θ₀ : 𝕍) (δ : ℝ) (z : 𝕍) : ℝ :=
  (Metric.closedBall (0 : 𝕍) δ).indicator (fun z ↦ obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0) z

/-- The sup-norm size of the regression direction. -/
noncomputable def linSize (F : X → ℝ) (θ₀ : 𝕍) : ℝ := ∑ j, |(regressionDir hS ν F θ₀ : J → ℝ) j|

theorem linSize_nonneg (F : X → ℝ) (θ₀ : 𝕍) : 0 ≤ linSize hS ν F θ₀ :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- `|⟨u_F, z⟩| ≤ a_F ‖z‖`. -/
theorem abs_dotJ_regressionDir_le (F : X → ℝ) (θ₀ z : 𝕍) :
    |dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ)| ≤ linSize hS ν F θ₀ * ‖z‖ := by
  refine (abs_dotJ_le _ _).trans ?_
  rw [Submodule.coe_norm]
  rfl

/-- The quadratic size `b_F = ½‖H_F‖ + K δ`. -/
noncomputable def quadSize {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) (K δ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ‖obsHessCLM hS ν hF θ₀‖ + K * δ

/-- The global quadratic constant `c_F = max(b_F, a_F/δ)`. -/
noncomputable def globQuad {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) (K δ : ℝ) : ℝ :=
  max (quadSize hS ν hF θ₀ K δ) (linSize hS ν F θ₀ / δ)

/-- The global linear constant `d_F = a_F + b_F δ`. -/
noncomputable def globLin {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) (K δ : ℝ) : ℝ :=
  linSize hS ν F θ₀ + quadSize hS ν hF θ₀ K δ * δ

/-- **The localised increment is quadratically close to the linear influence, globally**:
`|A_F(z) − ⟨u_F, z⟩| ≤ c_F ‖z‖²`. -/
theorem abs_locInc_sub_dotJ_le {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) {K : ℝ} (hδ : 0 < δ)
    (hK : 0 ≤ K)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3)
    (z : 𝕍) :
    |locInc hS ν F θ₀ δ z - dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ)| ≤
      globQuad hS ν hF θ₀ K δ * ‖z‖ ^ 2 := by
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have ha := linSize_nonneg hS ν F θ₀
  by_cases hz : z ∈ Metric.closedBall (0 : 𝕍) δ
  · rw [Metric.mem_closedBall, dist_zero_right] at hz
    unfold locInc
    rw [Set.indicator_of_mem (by rwa [Metric.mem_closedBall, dist_zero_right])]
    have h1 := hrem z hz
    have h2 := abs_obsHessForm_le hS ν hF θ₀ z
    have e : obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) =
        (obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
          dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
          (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z) + (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z := by
      ring
    rw [e]
    have hz3 : ‖z‖ ^ 3 ≤ δ * ‖z‖ ^ 2 := by
      rw [pow_succ, mul_comm]
      exact mul_le_mul_of_nonneg_right hz (by positivity)
    calc |_| ≤ |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
          dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
          (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| + |(1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| :=
          abs_add_le _ _
      _ ≤ K * ‖z‖ ^ 3 + (1 / 2 : ℝ) * (‖obsHessCLM hS ν hF θ₀‖ * ‖z‖ ^ 2) := by
          refine add_le_add h1 ?_
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ K * (δ * ‖z‖ ^ 2) + (1 / 2 : ℝ) * (‖obsHessCLM hS ν hF θ₀‖ * ‖z‖ ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hz3 hK) le_rfl
      _ = quadSize hS ν hF θ₀ K δ * ‖z‖ ^ 2 := by unfold quadSize; ring
      _ ≤ globQuad hS ν hF θ₀ K δ * ‖z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · unfold locInc
    rw [Set.indicator_of_notMem hz, zero_sub, abs_neg]
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
    refine (abs_dotJ_regressionDir_le hS ν F θ₀ z).trans ?_
    have h1 : linSize hS ν F θ₀ * ‖z‖ ≤ linSize hS ν F θ₀ / δ * ‖z‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      calc linSize hS ν F θ₀ * ‖z‖ * δ = linSize hS ν F θ₀ * ‖z‖ * δ := rfl
        _ ≤ linSize hS ν F θ₀ * ‖z‖ * ‖z‖ :=
            mul_le_mul_of_nonneg_left hz.le (mul_nonneg ha hz0)
        _ = linSize hS ν F θ₀ * ‖z‖ ^ 2 := by ring
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- **The localised increment is linearly bounded, globally**: `|A_F(z)| ≤ d_F ‖z‖`. -/
theorem abs_locInc_le {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) {K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3)
    (z : 𝕍) : |locInc hS ν F θ₀ δ z| ≤ globLin hS ν hF θ₀ K δ * ‖z‖ := by
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have ha := linSize_nonneg hS ν F θ₀
  have hb : 0 ≤ quadSize hS ν hF θ₀ K δ := by
    unfold quadSize
    positivity
  by_cases hz : z ∈ Metric.closedBall (0 : 𝕍) δ
  · have hz' : ‖z‖ ≤ δ := by rwa [Metric.mem_closedBall, dist_zero_right] at hz
    have h1 := abs_locInc_sub_dotJ_le hS ν hF θ₀ hδ hK hrem z
    have h2 := abs_dotJ_regressionDir_le hS ν F θ₀ z
    -- on the ball the quadratic constant is `b_F`, not `c_F`: redo the estimate with `hz'`
    have h3 : |locInc hS ν F θ₀ δ z - dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ)| ≤
        quadSize hS ν hF θ₀ K δ * ‖z‖ ^ 2 := by
      unfold locInc
      rw [Set.indicator_of_mem hz]
      have h1' := hrem z hz'
      have h2' := abs_obsHessForm_le hS ν hF θ₀ z
      have e : obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
          dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) =
          (obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
            dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
            (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z) + (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z := by
        ring
      rw [e]
      have hz3 : ‖z‖ ^ 3 ≤ δ * ‖z‖ ^ 2 := by
        rw [pow_succ, mul_comm]
        exact mul_le_mul_of_nonneg_right hz' (by positivity)
      calc |_| ≤ |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
            dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
            (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| + |(1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| :=
            abs_add_le _ _
        _ ≤ K * ‖z‖ ^ 3 + (1 / 2 : ℝ) * (‖obsHessCLM hS ν hF θ₀‖ * ‖z‖ ^ 2) := by
            refine add_le_add h1' ?_
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
            exact mul_le_mul_of_nonneg_left h2' (by norm_num)
        _ ≤ K * (δ * ‖z‖ ^ 2) + (1 / 2 : ℝ) * (‖obsHessCLM hS ν hF θ₀‖ * ‖z‖ ^ 2) :=
            add_le_add (mul_le_mul_of_nonneg_left hz3 hK) le_rfl
        _ = quadSize hS ν hF θ₀ K δ * ‖z‖ ^ 2 := by unfold quadSize; ring
    have hz2 : ‖z‖ ^ 2 ≤ δ * ‖z‖ := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right hz' hz0
    calc |locInc hS ν F θ₀ δ z| = |(locInc hS ν F θ₀ δ z -
          dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ)) +
          dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ)| := by ring_nf
      _ ≤ quadSize hS ν hF θ₀ K δ * ‖z‖ ^ 2 + linSize hS ν F θ₀ * ‖z‖ :=
          (abs_add_le _ _).trans (add_le_add h3 h2)
      _ ≤ quadSize hS ν hF θ₀ K δ * (δ * ‖z‖) + linSize hS ν F θ₀ * ‖z‖ :=
          add_le_add (mul_le_mul_of_nonneg_left hz2 hb) le_rfl
      _ = globLin hS ν hF θ₀ K δ * ‖z‖ := by unfold globLin; ring
  · unfold locInc
    rw [Set.indicator_of_notMem hz, abs_zero]
    unfold globLin
    positivity

/-- The localised increment is bounded by `d_F δ`. -/
theorem abs_locInc_le_const {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) {K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3)
    (z : 𝕍) : |locInc hS ν F θ₀ δ z| ≤ globLin hS ν hF θ₀ K δ * δ := by
  have hd : 0 ≤ globLin hS ν hF θ₀ K δ := by
    unfold globLin quadSize
    have := linSize_nonneg hS ν F θ₀
    positivity
  by_cases hz : z ∈ Metric.closedBall (0 : 𝕍) δ
  · have hz' : ‖z‖ ≤ δ := by rwa [Metric.mem_closedBall, dist_zero_right] at hz
    exact (abs_locInc_le hS ν hF θ₀ hδ hK hrem z).trans (mul_le_mul_of_nonneg_left hz' hd)
  · unfold locInc
    rw [Set.indicator_of_notMem hz, abs_zero]
    positivity

/-- The localised increment is measurable on the law of the displacement. -/
theorem aestronglyMeasurable_locInc {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍)
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω) (μ : Measure 𝕍) :
    AEStronglyMeasurable (locInc hS ν F θ₀ δ) μ := by
  have hs : MeasurableSet (cball) := Metric.isClosed_closedBall.measurableSet
  have hballdom : cball ⊆ responseBallDomain S ν θ₀ := fun z hz ↦ by
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact hdom z hz
  unfold locInc
  refine (aestronglyMeasurable_indicator_iff hs).2 ?_
  exact (((contDiffOn_obsChart hS ν hF θ₀).continuousOn.mono hballdom).sub
    continuousOn_const).aestronglyMeasurable hs

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The linear influence is measurable. -/
theorem aestronglyMeasurable_dotJ (u : J → ℝ) (μ : Measure 𝕍) :
    AEStronglyMeasurable (fun z : 𝕍 ↦ dotJ u (z : J → ℝ)) μ :=
  ((continuous_dotJ_right u).comp (𝕍).subtypeL.continuous).aestronglyMeasurable

/-- **The product of two localised increments is close to the product of the linear influences**:
`|∫ A_F A_H dμ − ∫ ℓ_F ℓ_H dμ| ≤ (c_F d_H + a_F c_H) M₃`. -/
theorem abs_integral_locInc_mul_sub_le (μ : Measure 𝕍) [IsFiniteMeasure μ] {F H : X → ℝ}
    (hF : Bdd F) (hH : Bdd H) (θ₀ : 𝕍) {KF KH : ℝ} (hδ : 0 < δ) (hKF : 0 ≤ KF) (hKH : 0 ≤ KH)
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω)
    (hremF : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ KF * ‖z‖ ^ 3)
    (hremH : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν H θ₀ z - obsChart hS ν H θ₀ 0 -
        dotJ (regressionDir hS ν H θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν H θ₀ z| ≤ KH * ‖z‖ ^ 3)
    (h2 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 2) μ) (h3 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 3) μ) :
    |(∫ z, locInc hS ν F θ₀ δ z * locInc hS ν H θ₀ δ z ∂μ) -
        ∫ z, dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) *
          dotJ (regressionDir hS ν H θ₀ : J → ℝ) (z : J → ℝ) ∂μ| ≤
      (globQuad hS ν hF θ₀ KF δ * globLin hS ν hH θ₀ KH δ +
        linSize hS ν F θ₀ * globQuad hS ν hH θ₀ KH δ) * ∫ z, ‖z‖ ^ 3 ∂μ := by
  have hAA : Integrable (fun z ↦ locInc hS ν F θ₀ δ z * locInc hS ν H θ₀ δ z) μ := by
    refine Integrable.of_bound ((aestronglyMeasurable_locInc hS ν hF θ₀ hdom μ).mul
      (aestronglyMeasurable_locInc hS ν hH θ₀ hdom μ))
      ((globLin hS ν hF θ₀ KF δ * δ) * (globLin hS ν hH θ₀ KH δ * δ)) (ae_of_all _ fun z : 𝕍 ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_locInc_le_const hS ν hF θ₀ hδ hKF hremF z)
      (abs_locInc_le_const hS ν hH θ₀ hδ hKH hremH z) (abs_nonneg _)
      ((abs_nonneg _).trans (abs_locInc_le_const hS ν hF θ₀ hδ hKF hremF z))
  have hll : Integrable (fun z : 𝕍 ↦ dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) *
      dotJ (regressionDir hS ν H θ₀ : J → ℝ) (z : J → ℝ)) μ := by
    refine Integrable.mono' (h2.const_mul (linSize hS ν F θ₀ * linSize hS ν H θ₀))
      ((aestronglyMeasurable_dotJ ν _ μ).mul (aestronglyMeasurable_dotJ ν _ μ))
      (ae_of_all _ fun z : 𝕍 ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ)| *
          |dotJ (regressionDir hS ν H θ₀ : J → ℝ) (z : J → ℝ)| ≤
          (linSize hS ν F θ₀ * ‖z‖) * (linSize hS ν H θ₀ * ‖z‖) :=
          mul_le_mul (abs_dotJ_regressionDir_le hS ν F θ₀ z) (abs_dotJ_regressionDir_le hS ν H θ₀ z)
            (abs_nonneg _) (by positivity [linSize_nonneg hS ν F θ₀])
      _ = linSize hS ν F θ₀ * linSize hS ν H θ₀ * ‖z‖ ^ 2 := by ring
  rw [← integral_sub hAA hll, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (g := fun z : 𝕍 ↦ (globQuad hS ν hF θ₀ KF δ *
    globLin hS ν hH θ₀ KH δ + linSize hS ν F θ₀ * globQuad hS ν hH θ₀ KH δ) * ‖z‖ ^ 3)
    (h3.const_mul _) (ae_of_all _ fun z : 𝕍 ↦ ?_)).trans ?_
  · rw [Real.norm_eq_abs]
    exact abs_mul_sub_mul_le (abs_locInc_sub_dotJ_le hS ν hF θ₀ hδ hKF hremF z)
      (abs_locInc_le hS ν hH θ₀ hδ hKH hremH z) (abs_dotJ_regressionDir_le hS ν F θ₀ z)
      (abs_locInc_sub_dotJ_le hS ν hH θ₀ hδ hKH hremH z)
  · rw [integral_const_mul]

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The linear influence of a centred law integrates to zero. -/
theorem integral_dotJ_eq_zero (μ : Measure 𝕍) (u : J → ℝ) (hcent : ∫ z, z ∂μ = 0)
    (hint : Integrable (fun z : 𝕍 ↦ z) μ) : ∫ z, dotJ u (z : J → ℝ) ∂μ = 0 := by
  have e' : ∀ z : 𝕍, dotJ u (z : J → ℝ) = pairCLM ν u z := fun z ↦ (pairCLM_apply ν u z).symm
  simp_rw [e']
  rw [ContinuousLinearMap.integral_comp_comm (pairCLM ν u) hint, hcent, map_zero]

/-- The expectation of a localised increment of a centred law is at most `c_F M₂`. -/
theorem abs_integral_locInc_le (μ : Measure 𝕍) [IsFiniteMeasure μ] {F : X → ℝ} (hF : Bdd F)
    (θ₀ : 𝕍) {K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3)
    (hcent : ∫ z, z ∂μ = 0) (hint : Integrable (fun z : 𝕍 ↦ z) μ)
    (h2 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 2) μ) :
    |∫ z, locInc hS ν F θ₀ δ z ∂μ| ≤ globQuad hS ν hF θ₀ K δ * ∫ z, ‖z‖ ^ 2 ∂μ := by
  have hA : Integrable (locInc hS ν F θ₀ δ) μ :=
    Integrable.of_bound (aestronglyMeasurable_locInc hS ν hF θ₀ hdom μ) _
      (ae_of_all _ fun z ↦ by
        rw [Real.norm_eq_abs]
        exact abs_locInc_le_const hS ν hF θ₀ hδ hK hrem z)
  have hl : Integrable (fun z : 𝕍 ↦ dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ)) μ := by
    refine Integrable.mono' ((integrable_const (linSize hS ν F θ₀)).add
      (h2.const_mul (linSize hS ν F θ₀))) (aestronglyMeasurable_dotJ ν _ μ)
      (ae_of_all _ fun z : 𝕍 ↦ ?_)
    rw [Real.norm_eq_abs]
    refine (abs_dotJ_regressionDir_le hS ν F θ₀ z).trans ?_
    have ha := linSize_nonneg hS ν F θ₀
    have hz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    have h1 : ‖z‖ ≤ 1 + ‖z‖ ^ 2 := by nlinarith [sq_nonneg (‖z‖ - 1)]
    calc linSize hS ν F θ₀ * ‖z‖ ≤ linSize hS ν F θ₀ * (1 + ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 ha
      _ = linSize hS ν F θ₀ + linSize hS ν F θ₀ * ‖z‖ ^ 2 := by ring
  have e : ∫ z, locInc hS ν F θ₀ δ z ∂μ = ∫ z, (locInc hS ν F θ₀ δ z -
      dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ)) ∂μ := by
    rw [integral_sub hA hl, integral_dotJ_eq_zero ν μ _ hcent hint, sub_zero]
  rw [e, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (g := fun z : 𝕍 ↦ globQuad hS ν hF θ₀ K δ * ‖z‖ ^ 2)
    (h2.const_mul _) (ae_of_all _ fun z : 𝕍 ↦ ?_)).trans ?_
  · rw [Real.norm_eq_abs]
    exact abs_locInc_sub_dotJ_le hS ν hF θ₀ hδ hK hrem z
  · rw [integral_const_mul]

/-- **THE JOINT COVARIANCE OF LOCALISED POSTERIOR EXPECTATIONS**: for a centred displacement law
with moments `M₂, M₃`,
`|Cov(A_F, A_H) − E[⟨u_F, Z⟩⟨u_H, Z⟩]| ≤ (c_F d_H + a_F c_H) M₃ + c_F c_H M₂²`. -/
theorem abs_lawCov_locInc_sub_le (μ : Measure 𝕍) [IsFiniteMeasure μ] {F H : X → ℝ}
    (hF : Bdd F) (hH : Bdd H) (θ₀ : 𝕍) {KF KH : ℝ} (hδ : 0 < δ) (hKF : 0 ≤ KF) (hKH : 0 ≤ KH)
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω)
    (hremF : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ KF * ‖z‖ ^ 3)
    (hremH : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν H θ₀ z - obsChart hS ν H θ₀ 0 -
        dotJ (regressionDir hS ν H θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν H θ₀ z| ≤ KH * ‖z‖ ^ 3)
    (hcent : ∫ z, z ∂μ = 0) (hint : Integrable (fun z : 𝕍 ↦ z) μ)
    (h2 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 2) μ) (h3 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 3) μ) :
    |lawCov μ (locInc hS ν F θ₀ δ) (locInc hS ν H θ₀ δ) -
        ∫ z, dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) *
          dotJ (regressionDir hS ν H θ₀ : J → ℝ) (z : J → ℝ) ∂μ| ≤
      (globQuad hS ν hF θ₀ KF δ * globLin hS ν hH θ₀ KH δ +
        linSize hS ν F θ₀ * globQuad hS ν hH θ₀ KH δ) * (∫ z, ‖z‖ ^ 3 ∂μ) +
      globQuad hS ν hF θ₀ KF δ * globQuad hS ν hH θ₀ KH δ * (∫ z, ‖z‖ ^ 2 ∂μ) ^ 2 := by
  have h1 := abs_integral_locInc_mul_sub_le hS ν μ hF hH θ₀ hδ hKF hKH hdom hremF hremH h2 h3
  have hF1 := abs_integral_locInc_le hS ν μ hF θ₀ hδ hKF hdom hremF hcent hint h2
  have hH1 := abs_integral_locInc_le hS ν μ hH θ₀ hδ hKH hdom hremH hcent hint h2
  have hM2 : 0 ≤ ∫ z, ‖z‖ ^ 2 ∂μ := integral_nonneg fun z ↦ by positivity
  have hcF : 0 ≤ globQuad hS ν hF θ₀ KF δ :=
    le_max_of_le_right (div_nonneg (linSize_nonneg hS ν F θ₀) hδ.le)
  have hcH : 0 ≤ globQuad hS ν hH θ₀ KH δ :=
    le_max_of_le_right (div_nonneg (linSize_nonneg hS ν H θ₀) hδ.le)
  unfold lawCov
  set I := ∫ z, locInc hS ν F θ₀ δ z * locInc hS ν H θ₀ δ z ∂μ
  set L := ∫ z, dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) *
    dotJ (regressionDir hS ν H θ₀ : J → ℝ) (z : J → ℝ) ∂μ
  set EF := ∫ z, locInc hS ν F θ₀ δ z ∂μ
  set EH := ∫ z, locInc hS ν H θ₀ δ z ∂μ
  set M2 := ∫ z, ‖z‖ ^ 2 ∂μ
  have e : I - EF * EH - L = (I - L) - EF * EH := by ring
  rw [e]
  calc |(I - L) - EF * EH| ≤ |I - L| + |EF * EH| := abs_sub _ _
    _ ≤ (globQuad hS ν hF θ₀ KF δ * globLin hS ν hH θ₀ KH δ +
          linSize hS ν F θ₀ * globQuad hS ν hH θ₀ KH δ) * (∫ z, ‖z‖ ^ 3 ∂μ) +
        (globQuad hS ν hF θ₀ KF δ * M2) * (globQuad hS ν hH θ₀ KH δ * M2) := by
        refine add_le_add h1 ?_
        rw [abs_mul]
        exact mul_le_mul hF1 hH1 (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- **The coordinate–observable cross term**:
`|E[⟨u, Z⟩ A_F(Z)] − E[⟨u, Z⟩⟨u_F, Z⟩]| ≤ (∑_j |u_j|) c_F M₃`. -/
theorem abs_integral_dotJ_mul_locInc_sub_le (μ : Measure 𝕍) [IsFiniteMeasure μ] (u : J → ℝ)
    {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) {K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ω)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3)
    (h2 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 2) μ) (h3 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 3) μ) :
    |(∫ z, dotJ u (z : J → ℝ) * locInc hS ν F θ₀ δ z ∂μ) -
        ∫ z, dotJ u (z : J → ℝ) * dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) ∂μ| ≤
      (∑ j, |u j|) * globQuad hS ν hF θ₀ K δ * ∫ z, ‖z‖ ^ 3 ∂μ := by
  have hau : ∀ z : 𝕍, |dotJ u (z : J → ℝ)| ≤ (∑ j, |u j|) * ‖z‖ := fun z ↦ by
    refine (abs_dotJ_le _ _).trans ?_
    rw [Submodule.coe_norm]
  have ha0 : 0 ≤ ∑ j, |u j| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hAA : Integrable (fun z : 𝕍 ↦ dotJ u (z : J → ℝ) * locInc hS ν F θ₀ δ z) μ := by
    refine Integrable.mono' (h2.const_mul ((∑ j, |u j|) * globLin hS ν hF θ₀ K δ))
      ((aestronglyMeasurable_dotJ ν u μ).mul (aestronglyMeasurable_locInc hS ν hF θ₀ hdom μ))
      (ae_of_all _ fun z : 𝕍 ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |dotJ u (z : J → ℝ)| * |locInc hS ν F θ₀ δ z| ≤
          ((∑ j, |u j|) * ‖z‖) * (globLin hS ν hF θ₀ K δ * ‖z‖) :=
          mul_le_mul (hau z) (abs_locInc_le hS ν hF θ₀ hδ hK hrem z) (abs_nonneg _)
            (by positivity)
      _ = (∑ j, |u j|) * globLin hS ν hF θ₀ K δ * ‖z‖ ^ 2 := by ring
  have hll : Integrable (fun z : 𝕍 ↦ dotJ u (z : J → ℝ) *
      dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ)) μ := by
    refine Integrable.mono' (h2.const_mul ((∑ j, |u j|) * linSize hS ν F θ₀))
      ((aestronglyMeasurable_dotJ ν u μ).mul (aestronglyMeasurable_dotJ ν _ μ))
      (ae_of_all _ fun z : 𝕍 ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |dotJ u (z : J → ℝ)| * |dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ)| ≤
          ((∑ j, |u j|) * ‖z‖) * (linSize hS ν F θ₀ * ‖z‖) :=
          mul_le_mul (hau z) (abs_dotJ_regressionDir_le hS ν F θ₀ z) (abs_nonneg _)
            (by positivity)
      _ = (∑ j, |u j|) * linSize hS ν F θ₀ * ‖z‖ ^ 2 := by ring
  rw [← integral_sub hAA hll, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le
    (g := fun z : 𝕍 ↦ (∑ j, |u j|) * globQuad hS ν hF θ₀ K δ * ‖z‖ ^ 3)
    (h3.const_mul _) (ae_of_all _ fun z : 𝕍 ↦ ?_)).trans ?_
  · rw [Real.norm_eq_abs]
    have h := abs_mul_sub_mul_le (A := dotJ u (z : J → ℝ)) (ℓ := dotJ u (z : J → ℝ)) (c := 0)
      (r := ‖z‖) (by rw [sub_self, abs_zero, zero_mul])
      (abs_locInc_le hS ν hF θ₀ hδ hK hrem z) (hau z)
      (abs_locInc_sub_dotJ_le hS ν hF θ₀ hδ hK hrem z)
    rw [zero_mul, zero_add] at h
    exact h
  · rw [integral_const_mul]

end Law

section IID

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {Ω : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X)
  [IsProbabilityMeasure ν] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : Measure X) [IsProbabilityMeasure D] (hDν : D ≪ ν) (Xs : ℕ → Ω → X)
  (hXm : ∀ i, Measurable (Xs i)) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P)
  (hlaw : P.map (Xs 0) = D) (hind : iIndepFun Xs P)
include hS hXm hid hlaw hDν hind

set_option linter.unusedFintypeInType false

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The mean map. -/
local notation "mean" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- The interior response domain (the sample space is `Ω`). -/
local notation "Ωm" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

/-- The raw empirical displacement `M̂_n − m_D`. -/
local notation "raw" n => (fun ω : Ω ↦ fun j : J ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)

variable {n : ℕ} (hn : 0 < n) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j x, |S j x| ≤ B)
include hn hB0 hB

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] hDν hid hlaw hind hB0 in
/-- The squared norm of the projected displacement is integrable. -/
theorem integrable_norm_sq_proj_raw (p : (J → ℝ) →ₗ[ℝ] 𝕍) :
    Integrable (fun ω ↦ ‖p ((raw n) ω)‖ ^ 2) P := by
  refine Integrable.of_bound
    ((measurable_proj_raw hS ν D Xs hXm p).norm.pow_const 2).aestronglyMeasurable
    ((‖LinearMap.toContinuousLinearMap p‖ * (Fintype.card J * (2 * B))) ^ 2)
    (ae_of_all _ fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (norm_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_proj_raw_le ν D Xs hn hB p ω) 2

omit hB0 in
/-- **The second moment of the projected displacement** is `O(1/n)`. -/
theorem integral_norm_sq_proj_le (p : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) :
    ∫ ω, ‖p ((raw n) ω)‖ ^ 2 ∂P ≤ Fintype.card J ^ 2 * (2 * B) ^ 2 / n := by
  have e : ∫ ω, ‖p ((raw n) ω)‖ ^ 2 ∂P = ∫ ω, ‖(raw n) ω‖ ^ 2 ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [ae_norm_proj_eq hS ν P D hDν Xs hXm hid hlaw hn p hp] with ω hω
    rw [hω]
  rw [e]
  exact integral_norm_sq_sampleResponse_sub_le hS P D Xs hXm hid hlaw hind hB hn

variable {δ : ℝ}

/-- The localisation ball. -/
local notation "cball" => Metric.closedBall (0 : 𝕍) δ

/-- **THE i.i.d. JOINT COVARIANCE OF LOCALISED POSTERIOR EXPECTATIONS**: for `n` i.i.d. samples
from a data law `D` (with `m_D = m(θ₀)` this is the covariance of the reset-localised empirical
posterior expectations),
`|Cov(f̂_{F,loc}, f̂_{H,loc}) − Σ_D(u_F, u_H)/n| ≤
  ((c_F d_H + a_F c_H) √3 |J|³ (2B)³ + c_F c_H (|J|² (2B)²)²) / n^{3/2}`. -/
theorem iid_lawCov_locInc_sub_le (p : (J → ℝ) →ₗ[ℝ] 𝕍) (hp : ∀ w : 𝕍, p (w : J → ℝ) = w)
    {F H : X → ℝ} (hF : Bdd F) (hH : Bdd H) (θ₀ : 𝕍) {KF KH : ℝ} (hδ : 0 < δ) (hKF : 0 ≤ KF)
    (hKH : 0 ≤ KH) (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ωm)
    (hremF : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ KF * ‖z‖ ^ 3)
    (hremH : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν H θ₀ z - obsChart hS ν H θ₀ 0 -
        dotJ (regressionDir hS ν H θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν H θ₀ z| ≤ KH * ‖z‖ ^ 3) :
    |lawCov P (fun ω ↦ locInc hS ν F θ₀ δ (p ((raw n) ω)))
        (fun ω ↦ locInc hS ν H θ₀ δ (p ((raw n) ω))) -
      lawCov D (dirLoss S (regressionDir hS ν F θ₀ : J → ℝ))
        (dirLoss S (regressionDir hS ν H θ₀ : J → ℝ)) / n| ≤
      ((globQuad hS ν hF θ₀ KF δ * globLin hS ν hH θ₀ KH δ +
          linSize hS ν F θ₀ * globQuad hS ν hH θ₀ KH δ) *
          (Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3) +
        globQuad hS ν hF θ₀ KF δ * globQuad hS ν hH θ₀ KH δ *
          (Fintype.card J ^ 2 * (2 * B) ^ 2) ^ 2) / (n * Real.sqrt n) := by
  have hξm := measurable_proj_raw hS ν D Xs hXm (n := n) p
  set μ : Measure 𝕍 := P.map fun ω ↦ p ((raw n) ω) with hμ
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hξm.aemeasurable
  have hidm : AEStronglyMeasurable (fun z : 𝕍 ↦ z) μ := aestronglyMeasurable_id
  have h2m : AEStronglyMeasurable (fun z : 𝕍 ↦ ‖z‖ ^ 2) μ :=
    (by fun_prop : Continuous fun z : 𝕍 ↦ ‖z‖ ^ 2).aestronglyMeasurable
  have h3m : AEStronglyMeasurable (fun z : 𝕍 ↦ ‖z‖ ^ 3) μ :=
    (by fun_prop : Continuous fun z : 𝕍 ↦ ‖z‖ ^ 3).aestronglyMeasurable
  have hcent : ∫ z, z ∂μ = 0 := by
    rw [hμ, integral_map hξm.aemeasurable hidm]
    exact integral_proj_raw_eq_zero hS ν P D Xs hXm hid hlaw hn hB p
  have hint : Integrable (fun z : 𝕍 ↦ z) μ :=
    (integrable_map_measure hidm hξm.aemeasurable).2 (integrable_proj_raw hS ν P D Xs hXm hn hB p)
  have h2 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 2) μ :=
    (integrable_map_measure h2m hξm.aemeasurable).2
      (integrable_norm_sq_proj_raw hS ν P D Xs hXm hn hB p)
  have h3 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 3) μ :=
    (integrable_map_measure h3m hξm.aemeasurable).2
      (integrable_norm_pow_three_proj_raw hS ν P D Xs hXm hn hB p)
  have hM3 : ∫ z, ‖z‖ ^ 3 ∂μ ≤
      Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3 / (n * Real.sqrt n) := by
    rw [hμ, integral_map hξm.aemeasurable h3m]
    exact integral_norm_pow_three_proj_le hS ν P D hDν Xs hXm hid hlaw hind hn hB0 hB p hp
  have hM2 : ∫ z, ‖z‖ ^ 2 ∂μ ≤ Fintype.card J ^ 2 * (2 * B) ^ 2 / n := by
    rw [hμ, integral_map hξm.aemeasurable h2m]
    exact integral_norm_sq_proj_le hS ν P D hDν Xs hXm hid hlaw hind hn hB p hp
  have hM20 : 0 ≤ ∫ z, ‖z‖ ^ 2 ∂μ := integral_nonneg fun z ↦ by positivity
  -- the linear part is the data covariance of the regression features over `n`
  have hL : ∫ z, dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) *
      dotJ (regressionDir hS ν H θ₀ : J → ℝ) (z : J → ℝ) ∂μ =
      lawCov D (dirLoss S (regressionDir hS ν F θ₀ : J → ℝ))
        (dirLoss S (regressionDir hS ν H θ₀ : J → ℝ)) / n := by
    have hm : AEStronglyMeasurable (fun z : 𝕍 ↦ dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) *
        dotJ (regressionDir hS ν H θ₀ : J → ℝ) (z : J → ℝ)) μ :=
      (aestronglyMeasurable_dotJ ν _ μ).mul (aestronglyMeasurable_dotJ ν _ μ)
    rw [hμ, integral_map hξm.aemeasurable hm]
    rw [← integral_influence_mul_influence hS ν P D Xs hXm hid hlaw
      (fun i k hik ↦ hind.indepFun hik) hn F H θ₀]
    refine integral_congr_ae ?_
    filter_upwards [ae_proj_eq_raw hS ν P D hDν Xs hXm hid hlaw hn p hp] with ω hω
    rw [hω]
  -- the covariance on `P` is the covariance on the law `μ`
  have hAF := aestronglyMeasurable_locInc hS ν hF θ₀ hdom μ
  have hAH := aestronglyMeasurable_locInc hS ν hH θ₀ hdom μ
  have hcov : lawCov P (fun ω ↦ locInc hS ν F θ₀ δ (p ((raw n) ω)))
      (fun ω ↦ locInc hS ν H θ₀ δ (p ((raw n) ω))) =
      lawCov μ (locInc hS ν F θ₀ δ) (locInc hS ν H θ₀ δ) := by
    have hAFH : AEStronglyMeasurable (fun z : 𝕍 ↦ locInc hS ν F θ₀ δ z * locInc hS ν H θ₀ δ z)
        μ := hAF.mul hAH
    unfold lawCov
    rw [hμ, integral_map hξm.aemeasurable hAFH, integral_map hξm.aemeasurable hAF,
      integral_map hξm.aemeasurable hAH]
  rw [hcov, ← hL]
  have h := abs_lawCov_locInc_sub_le hS ν μ hF hH θ₀ hδ hKF hKH hdom hremF hremH hcent hint h2 h3
  refine h.trans ?_
  have hcF : 0 ≤ globQuad hS ν hF θ₀ KF δ :=
    le_max_of_le_right (div_nonneg (linSize_nonneg hS ν F θ₀) hδ.le)
  have hcH : 0 ≤ globQuad hS ν hH θ₀ KH δ :=
    le_max_of_le_right (div_nonneg (linSize_nonneg hS ν H θ₀) hδ.le)
  have hdH : 0 ≤ globLin hS ν hH θ₀ KH δ := by
    unfold globLin quadSize
    have := linSize_nonneg hS ν H θ₀
    positivity
  have haF := linSize_nonneg hS ν F θ₀
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsq := sqrt_le_self_nat hn
  have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
  set T3 := Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3
  set T2 := Fintype.card J ^ 2 * (2 * B) ^ 2
  have hT2 : 0 ≤ T2 := by positivity
  have hM2sq : (∫ z, ‖z‖ ^ 2 ∂μ) ^ 2 ≤ T2 ^ 2 / (n * Real.sqrt n) := by
    calc (∫ z, ‖z‖ ^ 2 ∂μ) ^ 2 ≤ (T2 / n) ^ 2 := pow_le_pow_left₀ hM20 hM2 2
      _ = T2 ^ 2 / (n * n) := by ring
      _ ≤ T2 ^ 2 / (n * Real.sqrt n) := by
          refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
          exact mul_le_mul_of_nonneg_left hsq hn'.le
  calc (globQuad hS ν hF θ₀ KF δ * globLin hS ν hH θ₀ KH δ +
          linSize hS ν F θ₀ * globQuad hS ν hH θ₀ KH δ) * (∫ z, ‖z‖ ^ 3 ∂μ) +
        globQuad hS ν hF θ₀ KF δ * globQuad hS ν hH θ₀ KH δ * (∫ z, ‖z‖ ^ 2 ∂μ) ^ 2
      ≤ (globQuad hS ν hF θ₀ KF δ * globLin hS ν hH θ₀ KH δ +
          linSize hS ν F θ₀ * globQuad hS ν hH θ₀ KH δ) * (T3 / (n * Real.sqrt n)) +
        globQuad hS ν hF θ₀ KF δ * globQuad hS ν hH θ₀ KH δ * (T2 ^ 2 / (n * Real.sqrt n)) :=
        add_le_add (mul_le_mul_of_nonneg_left hM3 (by positivity))
          (mul_le_mul_of_nonneg_left hM2sq (by positivity))
    _ = _ := by ring

/-- **THE i.i.d. COORDINATE–OBSERVABLE CROSS TERM**:
`|E[⟨u, ξ_n⟩ f̂_{F,loc}] − Σ_D(u, u_F)/n| ≤ (∑_j|u_j|) c_F √3 |J|³ (2B)³ / n^{3/2}`. -/
theorem iid_integral_dotJ_mul_locInc_sub_le (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) (u : J → ℝ) {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) {K : ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K) (hdom : ∀ z : 𝕍, ‖z‖ ≤ δ → mean (θ₀ : J → ℝ) + (z : J → ℝ) ∈ Ωm)
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3) :
    |(∫ ω, dotJ u ((raw n) ω) * locInc hS ν F θ₀ δ (p ((raw n) ω)) ∂P) -
        lawCov D (dirLoss S u) (dirLoss S (regressionDir hS ν F θ₀ : J → ℝ)) / n| ≤
      (∑ j, |u j|) * globQuad hS ν hF θ₀ K δ *
        (Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3 / (n * Real.sqrt n)) := by
  have hξm := measurable_proj_raw hS ν D Xs hXm (n := n) p
  set μ : Measure 𝕍 := P.map fun ω ↦ p ((raw n) ω) with hμ
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hξm.aemeasurable
  have h2m : AEStronglyMeasurable (fun z : 𝕍 ↦ ‖z‖ ^ 2) μ :=
    (by fun_prop : Continuous fun z : 𝕍 ↦ ‖z‖ ^ 2).aestronglyMeasurable
  have h3m : AEStronglyMeasurable (fun z : 𝕍 ↦ ‖z‖ ^ 3) μ :=
    (by fun_prop : Continuous fun z : 𝕍 ↦ ‖z‖ ^ 3).aestronglyMeasurable
  have h2 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 2) μ :=
    (integrable_map_measure h2m hξm.aemeasurable).2
      (integrable_norm_sq_proj_raw hS ν P D Xs hXm hn hB p)
  have h3 : Integrable (fun z : 𝕍 ↦ ‖z‖ ^ 3) μ :=
    (integrable_map_measure h3m hξm.aemeasurable).2
      (integrable_norm_pow_three_proj_raw hS ν P D Xs hXm hn hB p)
  have hM3 : ∫ z, ‖z‖ ^ 3 ∂μ ≤
      Real.sqrt 3 * Fintype.card J ^ 3 * (2 * B) ^ 3 / (n * Real.sqrt n) := by
    rw [hμ, integral_map hξm.aemeasurable h3m]
    exact integral_norm_pow_three_proj_le hS ν P D hDν Xs hXm hid hlaw hind hn hB0 hB p hp
  have hAF := aestronglyMeasurable_locInc hS ν hF θ₀ hdom μ
  -- the raw pairing is the projected pairing almost surely
  have e1 : ∫ ω, dotJ u ((raw n) ω) * locInc hS ν F θ₀ δ (p ((raw n) ω)) ∂P =
      ∫ z, dotJ u (z : J → ℝ) * locInc hS ν F θ₀ δ z ∂μ := by
    have hm : AEStronglyMeasurable (fun z : 𝕍 ↦ dotJ u (z : J → ℝ) * locInc hS ν F θ₀ δ z) μ :=
      (aestronglyMeasurable_dotJ ν u μ).mul hAF
    rw [hμ, integral_map hξm.aemeasurable hm]
    refine integral_congr_ae ?_
    filter_upwards [ae_proj_eq_raw hS ν P D hDν Xs hXm hid hlaw hn p hp] with ω hω
    rw [hω]
  have hL : ∫ z, dotJ u (z : J → ℝ) * dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) ∂μ =
      lawCov D (dirLoss S u) (dirLoss S (regressionDir hS ν F θ₀ : J → ℝ)) / n := by
    have hm : AEStronglyMeasurable (fun z : 𝕍 ↦ dotJ u (z : J → ℝ) *
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ)) μ :=
      (aestronglyMeasurable_dotJ ν _ μ).mul (aestronglyMeasurable_dotJ ν _ μ)
    rw [hμ, integral_map hξm.aemeasurable hm]
    rw [← integral_dotJ_sampleResponse_sub_mul hS P D Xs hXm hid hlaw
      (fun i k hik ↦ hind.indepFun hik) hn u (regressionDir hS ν F θ₀ : J → ℝ)]
    refine integral_congr_ae ?_
    filter_upwards [ae_proj_eq_raw hS ν P D hDν Xs hXm hid hlaw hn p hp] with ω hω
    rw [hω]
  rw [e1, ← hL]
  refine (abs_integral_dotJ_mul_locInc_sub_le hS ν μ u hF θ₀ hδ hK hdom hrem h2 h3).trans ?_
  have ha0 : 0 ≤ ∑ j, |u j| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hcF : 0 ≤ globQuad hS ν hF θ₀ K δ :=
    le_max_of_le_right (div_nonneg (linSize_nonneg hS ν F θ₀) hδ.le)
  exact mul_le_mul_of_nonneg_left hM3 (by positivity)

end IID

end Laplace.Multi
