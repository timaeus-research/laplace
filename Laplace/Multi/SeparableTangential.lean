/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.CylinderSufficient
import Laplace.Multi.TotalVariation

/-!
# The fixed cutoff–monomial family for separable losses with a common tangential part

Extends the common-cylinder theorem to losses `L_j (x, y) = K_j x + V y` over a coordinate
splitting, where the tangential part `V ≥ 0` is shared, `C²`, and vanishes at the tangential
coordinate of the base point. The zero set is `{p₁} × Z(V)`: positive dimensional and, when
`V` is singular (e.g. `V y = y₁²`, a hyperplane, or `V y = (y₁ y₂)²`), a singular variety in
the tangential directions.

With a product cutoff the data factor as `T(t) · (transverse datum)`, where
`T(t) = ∫ χ₂ e^{-tV}` is the tangential partition function. `T` is bounded below by a
polynomial `κ t^{-d₂}` (the quadratic bound `V ≤ M ‖y − q‖²` near the zero `q`, a
consequence of `V ≥ 0 = V q` and `C²`, gives `T(t) ≥ c₂ e^{-M r²} vol(B(q, r/t))`), so
"beyond all orders" for the product is "beyond all orders" for the transverse datum, and the
isolated-zero theorem in the transverse variables finishes.
-/

open Real MeasureTheory Filter Topology
open scoped ContDiff

namespace Laplace.Multi

/-- **Quadratic bound at a minimum**: a `C²` nonnegative function vanishing at `q` is bounded
by `M ‖y − q‖²` near `q`. -/
theorem exists_quadratic_bound_of_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → ℝ} {q : E} (hV : ContDiff ℝ 2 V) (hV0 : ∀ y, 0 ≤ V y) (hq : V q = 0) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ∀ y ∈ Metric.ball q r, V y ≤ M * ‖y - q‖ ^ 2 := by
  have hd1 : ContDiffAt ℝ 1 (fderiv ℝ V) q := hV.contDiffAt.fderiv_right (m := 1) (by norm_num)
  obtain ⟨K, s, hs, hK⟩ := hd1.exists_lipschitzOnWith
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hs
  have hmin : IsLocalMin V q := Filter.Eventually.of_forall fun y ↦ by rw [hq]; exact hV0 y
  have hdq : fderiv ℝ V q = 0 := hmin.fderiv_eq_zero
  have hdiff : Differentiable ℝ V := hV.differentiable (by norm_num)
  refine ⟨r, K, hr, K.2, fun y hy ↦ ?_⟩
  have hρ : ‖y - q‖ < r := by
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact hy
  -- the derivative bound on the closed ball of radius `‖y − q‖`
  have hbound : ∀ z ∈ Metric.closedBall q ‖y - q‖, ‖fderiv ℝ V z‖ ≤ K * ‖y - q‖ := by
    intro z hz
    have hzr : z ∈ Metric.ball q r :=
      Metric.closedBall_subset_ball hρ hz
    have h := hK.dist_le_mul z (hrs hzr) q (hrs (Metric.mem_ball_self hr))
    rw [hdq, dist_zero_right, dist_eq_norm] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ K.2)
    rwa [Metric.mem_closedBall, dist_eq_norm] at hz
  have hmv := (convex_closedBall q ‖y - q‖).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ hdiff z) hbound (Metric.mem_closedBall_self (norm_nonneg _))
    (by rw [Metric.mem_closedBall, dist_eq_norm])
  rw [hq, sub_zero, Real.norm_eq_abs, abs_of_nonneg (hV0 y)] at hmv
  calc V y ≤ K * ‖y - q‖ * ‖y - q‖ := hmv
    _ = K * ‖y - q‖ ^ 2 := by ring

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- **Polynomial lower bound of the tangential partition function**: with `χ₂ ≥ c₂ > 0` on a
ball around a zero `q` of `V ≥ 0` where `V ≤ M ‖y − q‖²`,
`∫ χ₂ e^{-tV} ≥ κ t^{-d₂}` for `t ≥ 1`. -/
theorem tangential_partition_lower_bound {χ₂ V : (ι₂ → ℝ) → ℝ} (hχ₂m : Measurable χ₂)
    (hχ₂0 : ∀ y, 0 ≤ χ₂ y) (hχ₂int : Integrable χ₂) (hVm : Measurable V)
    (hV0 : ∀ y, 0 ≤ V y) {q : ι₂ → ℝ} {r c₂ M : ℝ} (hr : 0 < r) (hc₂ : 0 < c₂) (hM : 0 ≤ M)
    (hχ₂c : ∀ y ∈ Metric.ball q r, c₂ ≤ χ₂ y)
    (hVq : ∀ y ∈ Metric.ball q r, V y ≤ M * ‖y - q‖ ^ 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ t : ℝ, 1 ≤ t →
      κ * (t⁻¹) ^ Fintype.card ι₂ ≤ ∫ y, χ₂ y * Real.exp (-(t * V y)) := by
  have hvol_pos : 0 < (volume (Metric.ball (0 : ι₂ → ℝ) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
      measure_ball_lt_top.ne
  refine ⟨c₂ * Real.exp (-(M * r ^ 2)) * r ^ Fintype.card ι₂ *
    (volume (Metric.ball (0 : ι₂ → ℝ) 1)).toReal, by positivity, fun t ht ↦ ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  set ρ : ℝ := r / t with hρ_def
  have hρ : 0 < ρ := div_pos hr ht0
  have hρr : ρ ≤ r := by
    rw [hρ_def, div_le_iff₀ ht0]
    nlinarith
  -- the integrand dominates a constant on the small ball
  have hint : Integrable fun y ↦ χ₂ y * Real.exp (-(t * V y)) := by
    refine hχ₂int.mono' (Measurable.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hχ₂0 y) (Real.exp_pos _).le)]
    have : Real.exp (-(t * V y)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := mul_nonneg ht0.le (hV0 y)
      linarith
    calc χ₂ y * Real.exp (-(t * V y)) ≤ χ₂ y * 1 := mul_le_mul_of_nonneg_left this (hχ₂0 y)
      _ = χ₂ y := mul_one _
  have hlow : ∀ y, (Metric.ball q ρ).indicator (fun _ ↦ c₂ * Real.exp (-(M * r ^ 2))) y ≤
      χ₂ y * Real.exp (-(t * V y)) := by
    intro y
    by_cases hy : y ∈ Metric.ball q ρ
    · rw [Set.indicator_of_mem hy]
      have hyr : y ∈ Metric.ball q r := Metric.ball_subset_ball hρr hy
      have hnorm : ‖y - q‖ < ρ := by
        rw [Metric.mem_ball, dist_eq_norm] at hy
        exact hy
      have hexp : Real.exp (-(M * r ^ 2)) ≤ Real.exp (-(t * V y)) := by
        rw [Real.exp_le_exp, neg_le_neg_iff]
        calc t * V y ≤ t * (M * ‖y - q‖ ^ 2) := mul_le_mul_of_nonneg_left (hVq y hyr) ht0.le
          _ ≤ t * (M * ρ ^ 2) := by
            gcongr
          _ = M * r ^ 2 / t := by
            rw [hρ_def]
            field_simp
          _ ≤ M * r ^ 2 := by
            rw [div_le_iff₀ ht0]
            nlinarith [mul_nonneg hM (sq_nonneg r)]
      exact mul_le_mul (hχ₂c y hyr) hexp (Real.exp_pos _).le (hχ₂0 y)
    · rw [Set.indicator_of_notMem hy]
      exact mul_nonneg (hχ₂0 y) (Real.exp_pos _).le
  have hind : Integrable
      ((Metric.ball q ρ).indicator fun _ : ι₂ → ℝ ↦ c₂ * Real.exp (-(M * r ^ 2))) :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
      (integrableOn_const measure_ball_lt_top.ne)
  have hmono := integral_mono hind hint hlow
  rw [integral_indicator_const _ Metric.isOpen_ball.measurableSet, smul_eq_mul,
    measureReal_def, Measure.addHaar_ball_of_pos volume q hρ, Module.finrank_fintype_fun_eq_card,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hρ_def, div_pow,
    div_eq_mul_inv] at hmono
  calc c₂ * Real.exp (-(M * r ^ 2)) * r ^ Fintype.card ι₂ *
        (volume (Metric.ball (0 : ι₂ → ℝ) 1)).toReal * (t⁻¹) ^ Fintype.card ι₂
      = r ^ Fintype.card ι₂ * (t ^ Fintype.card ι₂)⁻¹ *
        (volume (Metric.ball (0 : ι₂ → ℝ) 1)).toReal * (c₂ * Real.exp (-(M * r ^ 2))) := by
        rw [inv_pow]
        ring
    _ ≤ _ := hmono

/-- **Sufficiency of the fixed cutoff–monomial family for separable losses with a common
tangential part.** For `L_j (x, y) = K_j x + V y` with `K_j` satisfying the isolated-zero
hypotheses in the transverse variables and `V ≥ 0` a `C²` function vanishing at the tangential
coordinate of `p`, a product cutoff `χ₁ ⊗ χ₂` with `χ₂ ≥ c₂ > 0` near that zero: if the
projective data of all coordinate monomials are beyond all orders then `L₁ = L₂` near `p`.
The zero set `{p₁} × Z(V)` is positive dimensional and may be singular. -/
theorem separable_normalized_families_force_germ_eq_at
    {K₁ K₂ : (ι₁ → ℝ) → ℝ} {V : (ι₂ → ℝ) → ℝ} {L₁ L₂ : (ι₁ ⊕ ι₂ → ℝ) → ℝ}
    (hL₁ : ∀ w, L₁ w = K₁ (transverse w) + V (tangential w))
    (hL₂ : ∀ w, L₂ w = K₂ (transverse w) + V (tangential w))
    (h1 : ContDiff ℝ ∞ K₁) (h2 : ContDiff ℝ ∞ K₂)
    (hK1 : ∀ x, 0 ≤ K₁ x) (hK2 : ∀ x, 0 ≤ K₂ x) {p : ι₁ ⊕ ι₂ → ℝ}
    (hA1 : AnalyticAt ℝ K₁ (transverse p)) (hA2 : AnalyticAt ℝ K₂ (transverse p))
    (hp1 : K₁ (transverse p) = 0) (hp2 : K₂ (transverse p) = 0)
    {χ₁ : (ι₁ → ℝ) → ℝ} (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₁s : HasCompactSupport χ₁)
    (hχ₁0 : ∀ x, 0 ≤ χ₁ x) {ρ : ℝ} (hρ : 0 < ρ)
    (hχ₁1 : ∀ x ∈ Metric.ball (transverse p) ρ, χ₁ x = 1)
    (hV : ContDiff ℝ 2 V) (hV0 : ∀ y, 0 ≤ V y) (hVp : V (tangential p) = 0)
    {χ₂ : (ι₂ → ℝ) → ℝ} (hχ₂m : Measurable χ₂) (hχ₂0 : ∀ y, 0 ≤ χ₂ y)
    (hχ₂int : Integrable χ₂) {r c₂ : ℝ} (hr : 0 < r) (hc₂ : 0 < c₂)
    (hχ₂c : ∀ y ∈ Metric.ball (tangential p) r, c₂ ≤ χ₂ y)
    {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hcoer : ∀ x ∈ tsupport χ₁, c * ‖x - transverse p‖ ^ ν ≤ K₁ x)
    {C : ℝ → ℝ}
    (hfam : ∀ (k : ℕ) (m : Fin k → ι₁ ⊕ ι₂),
      SuperPoly (projDiff L₁ L₂ C fun w ↦ χ₁ (transverse w) * χ₂ (tangential w) *
        coordMonomial p m w)) :
    ∀ᶠ w in 𝓝 p, L₁ w = L₂ w := by
  -- the tangential partition function and its polynomial lower bound
  obtain ⟨r', M, hr', hM, hquad⟩ := exists_quadratic_bound_of_nonneg hV hV0 hVp
  have hVm : Measurable V := hV.continuous.measurable
  obtain ⟨κ, hκ, hlow⟩ := tangential_partition_lower_bound hχ₂m hχ₂0 hχ₂int hVm hV0
    (q := tangential p) (lt_min hr hr') hc₂ hM
    (fun y hy ↦ hχ₂c y (Metric.ball_subset_ball (min_le_left _ _) hy))
    (fun y hy ↦ hquad y (Metric.ball_subset_ball (min_le_right _ _) hy))
  set T : ℝ → ℝ := fun t ↦ ∫ y, χ₂ y * Real.exp (-(t * V y)) with hT_def
  have hTpos : ∀ t : ℝ, 1 ≤ t → 0 < T t := fun t ht ↦
    lt_of_lt_of_le (by positivity) (hlow t ht)
  -- the transverse data
  have hfam₁ : ∀ (k : ℕ) (m : Fin k → ι₁),
      SuperPoly (projDiff K₁ K₂ C fun x ↦ χ₁ x * coordMonomial (transverse p) m x) := by
    intro k m
    have h := hfam k (Sum.inl ∘ m)
    have hfactor : ∀ (K : (ι₁ → ℝ) → ℝ) (t : ℝ),
        (∫ w : ι₁ ⊕ ι₂ → ℝ, (χ₁ (transverse w) * χ₂ (tangential w) *
          coordMonomial p (Sum.inl ∘ m) w) *
            Real.exp (-(t * (K (transverse w) + V (tangential w))))) =
        T t * ∫ x : ι₁ → ℝ, (χ₁ x * coordMonomial (transverse p) m x) * Real.exp (-(t * K x)) := by
      intro K t
      rw [hT_def, mul_comm, ← integral_transverse_mul_tangential
        (fun x ↦ (χ₁ x * coordMonomial (transverse p) m x) * Real.exp (-(t * K x)))
        (fun y ↦ χ₂ y * Real.exp (-(t * V y)))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
      beta_reduce
      rw [coordMonomial_inl, mul_add, neg_add, Real.exp_add]
      ring
    have hprod : projDiff L₁ L₂ C (fun w ↦ χ₁ (transverse w) * χ₂ (tangential w) *
        coordMonomial p (Sum.inl ∘ m) w) =
        fun t ↦ T t * projDiff K₁ K₂ C (fun x ↦ χ₁ x * coordMonomial (transverse p) m x) t := by
      funext t
      unfold projDiff
      simp only [hL₁, hL₂]
      rw [hfactor K₂ t, hfactor K₁ t]
      ring
    rw [hprod] at h
    have hB : ∀ᶠ t in atTop, |(T t)⁻¹| ≤ κ⁻¹ * t ^ Fintype.card ι₂ := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
      rw [abs_of_pos (inv_pos.mpr (hTpos t ht))]
      calc (T t)⁻¹ ≤ (κ * (t⁻¹) ^ Fintype.card ι₂)⁻¹ :=
            inv_anti₀ (by positivity) (hlow t ht)
        _ = κ⁻¹ * t ^ Fintype.card ι₂ := by
            rw [mul_inv, inv_pow, inv_inv]
    refine (h.polyBounded_mul (B := fun t ↦ (T t)⁻¹) hB).congr ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact inv_mul_cancel_left₀ (hTpos t ht).ne' _
  -- the transverse conclusion and its lift
  have hK := normalized_families_force_germ_eq_at_of_cutoff_monomials (C := C) h1 h2 hK1 hK2 hA1
    hA2 hp1 hp2 hχ₁ hχ₁s hχ₁0 hρ hχ₁1 hc hν hcoer hfam₁
  obtain ⟨δ, hδ, hK'⟩ := Metric.eventually_nhds_iff.mp hK
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun w hw ↦ ?_⟩
  rw [hL₁, hL₂, hK' ?_]
  rw [dist_eq_norm] at hw ⊢
  exact lt_of_le_of_lt (norm_transverse_sub_le w p) hw

end Laplace.Multi
