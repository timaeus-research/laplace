/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.TotalVariation

/-!
# Local uniform agreement of the Boltzmann weights

`TotalVariation` gives, for smooth nonnegative losses with exact
smooth-test agreement, `∫_K |e^{-tL₂} - e^{-tL₁}| = o(t^{-∞})` on every
compact `K`. Here this is upgraded to a *uniform* statement: for every
compact `K` and every `N`, `sup_{x ∈ K} |e^{-tL₂ x} - e^{-tL₁ x}| ≤ C_N t^{-N}`
eventually, stated without a supremum as
`∀ᶠ t, ∀ x ∈ K, |h_t x| ≤ C t^{-N}` (`eventually_uniform_abs_exp_sub_le`),
with the pointwise corollary `SuperPoly (fun t ↦ h_t x)` for every `x`
(`superPoly_exp_sub_at`).

The mechanism is a Lipschitz-peak argument. The weights are `[0,1]`-valued
and their gradient is `‖∇ e^{-tL}‖ = t e^{-tL} ‖∇L‖ ≤ t ‖∇L‖`
(`norm_fderiv_expWeight_le`), so on the compact `1`-thickening `K'` of `K`
the difference `h_t` is `Λ`-Lipschitz on unit balls with `Λ = tG + 1`,
`G` a bound for `‖∇L₁‖ + ‖∇L₂‖` on `K'`. A peak of height `H = |h_t x₀|`
at `x₀ ∈ K` then carries mass `≥ H/2` on the ball of radius `H/(2Λ) ≤ 1/2`
about `x₀`, so `∫_{K'} |h_t| ≥ (H/2) c_d (H/(2Λ))^d`, i.e.
`H^{d+1} ≤ (2^{d+1}/c_d) Λ^d ∫_{K'} |h_t|` (`pow_abs_le_of_lipschitz_of_setIntegral`,
stated for any bounded Lipschitz function). With `Λ ≤ (G+1) t` for `t ≥ 1`
this is the powered peak inequality
`|h_t x|^{d+1} ≤ C t^d ∫_{K'} |h_t|` (`pow_abs_exp_sub_le`), its root form
(`abs_exp_sub_le_rpow`), and, feeding in the total-variation decay at
exponent `(d+1)N + d`, the uniform bound.

Only differentiability with a bounded gradient near `K` is used in the
upgrade itself; the `C^∞` hypothesis is inherited from the smooth-test
agreement upstream.
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace Laplace

variable {ι : Type*} [Fintype ι]

/-! ### The weights and their gradients -/

omit [Fintype ι] in
/-- For `t ≥ 0` and `L ≥ 0` the Boltzmann weight lies in `[0, 1]`. -/
theorem expWeight_le_one {L : (ι → ℝ) → ℝ} (hL : ∀ w, 0 ≤ L w) {t : ℝ} (ht : 0 ≤ t)
    (w : ι → ℝ) : Real.exp (-(t * L w)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr (mul_nonneg ht (hL w))

omit [Fintype ι] in
/-- The weight difference has amplitude at most `1`. -/
theorem abs_exp_sub_le_one {L₁ L₂ : (ι → ℝ) → ℝ}
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w) {t : ℝ} (ht : 0 ≤ t) (w : ι → ℝ) :
    |Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))| ≤ 1 := by
  have h1 := expWeight_le_one hL1 ht w
  have h2 := expWeight_le_one hL2 ht w
  have e1 := Real.exp_pos (-(t * L₁ w))
  have e2 := Real.exp_pos (-(t * L₂ w))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

set_option linter.unusedSectionVars false in
/-- Derivative of the Boltzmann weight. -/
theorem hasFDerivAt_expWeight {L : (ι → ℝ) → ℝ} {x : ι → ℝ}
    (hd : DifferentiableAt ℝ L x) (t : ℝ) :
    HasFDerivAt (fun w ↦ Real.exp (-(t * L w)))
      (Real.exp (-(t * L x)) • (-(t • fderiv ℝ L x))) x :=
  ((hd.hasFDerivAt.const_mul t).neg).exp

/-- The gradient of the weight is bounded by `t ‖∇L‖` for `t ≥ 0`, `L ≥ 0`. -/
theorem norm_expWeight_deriv_le {L : (ι → ℝ) → ℝ} (hL : ∀ w, 0 ≤ L w) {t : ℝ} (ht : 0 ≤ t)
    (x : ι → ℝ) (v : (ι → ℝ) →L[ℝ] ℝ) :
    ‖Real.exp (-(t * L x)) • (-(t • v))‖ ≤ t * ‖v‖ := by
  rw [norm_smul, norm_neg, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), abs_of_nonneg ht]
  calc Real.exp (-(t * L x)) * (t * ‖v‖) ≤ 1 * (t * ‖v‖) :=
        mul_le_mul_of_nonneg_right (expWeight_le_one hL ht x) (by positivity)
    _ = t * ‖v‖ := one_mul _

/-- The gradient of the weight difference is bounded by `t (‖∇L₁‖ + ‖∇L₂‖)`. -/
theorem norm_fderiv_weightDiff_le {L₁ L₂ : (ι → ℝ) → ℝ}
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w) {x : ι → ℝ}
    (hd1 : DifferentiableAt ℝ L₁ x) (hd2 : DifferentiableAt ℝ L₂ x) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w))) x‖ ≤
      t * (‖fderiv ℝ L₁ x‖ + ‖fderiv ℝ L₂ x‖) := by
  have hh : HasFDerivAt (fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w)))
      (Real.exp (-(t * L₂ x)) • (-(t • fderiv ℝ L₂ x)) -
        Real.exp (-(t * L₁ x)) • (-(t • fderiv ℝ L₁ x))) x :=
    (hasFDerivAt_expWeight hd2 t).sub (hasFDerivAt_expWeight hd1 t)
  rw [hh.fderiv]
  calc ‖Real.exp (-(t * L₂ x)) • (-(t • fderiv ℝ L₂ x)) -
        Real.exp (-(t * L₁ x)) • (-(t • fderiv ℝ L₁ x))‖
      ≤ ‖Real.exp (-(t * L₂ x)) • (-(t • fderiv ℝ L₂ x))‖ +
        ‖Real.exp (-(t * L₁ x)) • (-(t • fderiv ℝ L₁ x))‖ := norm_sub_le _ _
    _ ≤ t * ‖fderiv ℝ L₂ x‖ + t * ‖fderiv ℝ L₁ x‖ :=
        add_le_add (norm_expWeight_deriv_le hL2 ht x _) (norm_expWeight_deriv_le hL1 ht x _)
    _ = t * (‖fderiv ℝ L₁ x‖ + ‖fderiv ℝ L₂ x‖) := by ring

/-! ### The peak lemma -/

/-- **Peak lemma.** A function of amplitude `≤ 1` at `x₀`, `Λ`-Lipschitz on the
unit ball about `x₀` (with `Λ ≥ 1`), which is integrable on a set `K'`
containing that ball, satisfies
`|f x₀|^{d+1} ≤ (2^{d+1}/c_d) Λ^d ∫_{K'} |f|`, `c_d` the volume of the unit ball. -/
theorem pow_abs_le_of_lipschitz_of_setIntegral {f : (ι → ℝ) → ℝ} {K' : Set (ι → ℝ)}
    (hint : IntegrableOn (fun y ↦ |f y|) K') {x₀ : ι → ℝ}
    (hball : Metric.ball x₀ 1 ⊆ K') {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hlip : ∀ y ∈ Metric.ball x₀ 1, |f y - f x₀| ≤ Λ * ‖y - x₀‖) (hamp : |f x₀| ≤ 1) :
    |f x₀| ^ (Fintype.card ι + 1) ≤
      2 ^ (Fintype.card ι + 1) / (volume (Metric.ball (0 : ι → ℝ) 1)).toReal *
        Λ ^ (Fintype.card ι) * ∫ y in K', |f y| := by
  set d := Fintype.card ι with hd
  set c : ℝ := (volume (Metric.ball (0 : ι → ℝ) 1)).toReal with hc_def
  have hcpos : 0 < c :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : ι → ℝ) one_pos).ne'
      measure_ball_lt_top.ne
  have hΛpos : 0 < Λ := lt_of_lt_of_le one_pos hΛ
  have hInn : 0 ≤ ∫ y in K', |f y| := setIntegral_nonneg_of_ae_restrict
    (Eventually.of_forall fun y ↦ abs_nonneg _)
  rcases eq_or_lt_of_le (abs_nonneg (f x₀)) with hH0 | hHpos
  · rw [← hH0]
    simp only [zero_pow (Nat.succ_ne_zero _)]
    positivity
  set H := |f x₀| with hH
  -- the peak radius
  set r : ℝ := H / (2 * Λ) with hr_def
  have hrpos : 0 < r := by positivity
  have hr1 : r ≤ 1 / 2 := by
    rw [hr_def, div_le_iff₀ (by positivity)]
    nlinarith
  have hsub : Metric.ball x₀ r ⊆ Metric.ball x₀ 1 :=
    Metric.ball_subset_ball (by linarith)
  -- on the peak ball the function is at least `H/2`
  have hlow : ∀ y ∈ Metric.ball x₀ r, H / 2 ≤ |f y| := by
    intro y hy
    have hy1 : y ∈ Metric.ball x₀ 1 := hsub hy
    have hdist : ‖y - x₀‖ < r := by
      have := Metric.mem_ball.mp hy
      rwa [dist_eq_norm] at this
    have h1 := hlip y hy1
    have h2 : |f y - f x₀| ≤ Λ * r :=
      h1.trans (mul_le_mul_of_nonneg_left hdist.le hΛpos.le)
    have hΛr : Λ * r = H / 2 := by
      rw [hr_def]
      field_simp
    have h3 : |f x₀| - |f y| ≤ |f x₀ - f y| := abs_sub_abs_le_abs_sub _ _
    rw [abs_sub_comm] at h3
    linarith
  -- the volume of the peak ball
  have hvol : volume.real (Metric.ball x₀ r) = r ^ d * c := by
    rw [Measure.real, Measure.addHaar_ball_of_pos volume x₀ hrpos, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), Module.finrank_fintype_fun_eq_card]
  have hintball : IntegrableOn (fun y ↦ |f y|) (Metric.ball x₀ r) :=
    hint.mono_set (hsub.trans hball)
  have hge : volume.real (Metric.ball x₀ r) • (H / 2) ≤ ∫ y in Metric.ball x₀ r, |f y| :=
    setIntegral_ge_of_const_le measurableSet_ball measure_ball_lt_top.ne hlow hintball
  have hmono : ∫ y in Metric.ball x₀ r, |f y| ≤ ∫ y in K', |f y| :=
    setIntegral_mono_set hint (Eventually.of_forall fun y ↦ abs_nonneg _)
      ((hsub.trans hball).eventuallyLE)
  rw [smul_eq_mul, hvol] at hge
  have hkey : r ^ d * c * (H / 2) ≤ ∫ y in K', |f y| := hge.trans hmono
  -- unwind the algebra
  have hHd : H ^ (d + 1) = (r ^ d * c * (H / 2)) * (2 ^ (d + 1) / c * Λ ^ d) := by
    rw [hr_def, div_pow]
    field_simp
    ring
  calc H ^ (d + 1) = (r ^ d * c * (H / 2)) * (2 ^ (d + 1) / c * Λ ^ d) := hHd
    _ ≤ (∫ y in K', |f y|) * (2 ^ (d + 1) / c * Λ ^ d) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = 2 ^ (d + 1) / c * Λ ^ d * ∫ y in K', |f y| := by ring

/-! ### The powered peak inequality for the weight difference -/

/-- A common bound for the gradients of two smooth losses on a compact set. -/
theorem exists_gradient_bound_on {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂) {S : Set (ι → ℝ)} (hS : IsCompact S) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ x ∈ S, ‖fderiv ℝ L₁ x‖ + ‖fderiv ℝ L₂ x‖ ≤ G := by
  have hc : Continuous fun x ↦ ‖fderiv ℝ L₁ x‖ + ‖fderiv ℝ L₂ x‖ :=
    (h1.continuous_fderiv (by simp)).norm.add (h2.continuous_fderiv (by simp)).norm
  obtain ⟨G, hG⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max G 0, le_max_right _ _, fun x hx ↦ ?_⟩
  have := hG x hx
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

/-- **Powered peak inequality.** For smooth nonnegative losses and compact `K`,
with `K'` its closed `1`-thickening: there is `C` with
`|h_t x|^{d+1} ≤ C t^d ∫_{K'} |h_t|` for all `t ≥ 1`, `x ∈ K`. -/
theorem pow_abs_exp_sub_le {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    {K : Set (ι → ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ x ∈ K,
      |Real.exp (-(t * L₂ x)) - Real.exp (-(t * L₁ x))| ^ (Fintype.card ι + 1) ≤
        C * t ^ (Fintype.card ι) * ∫ y in Metric.cthickening 1 K,
          |Real.exp (-(t * L₂ y)) - Real.exp (-(t * L₁ y))| := by
  set d := Fintype.card ι with hd
  set K' := Metric.cthickening 1 K with hK'_def
  have hK' : IsCompact K' := hK.cthickening
  obtain ⟨G, hG0, hG⟩ := exists_gradient_bound_on h1 h2 hK'
  set c : ℝ := (volume (Metric.ball (0 : ι → ℝ) 1)).toReal with hc_def
  have hcpos : 0 < c :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : ι → ℝ) one_pos).ne'
      measure_ball_lt_top.ne
  refine ⟨2 ^ (d + 1) / c * (G + 1) ^ d, by positivity, ?_⟩
  intro t ht x₀ hx₀
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  set h : (ι → ℝ) → ℝ := fun w ↦ Real.exp (-(t * L₂ w)) - Real.exp (-(t * L₁ w)) with hh_def
  have hhc : Continuous h :=
    (Real.continuous_exp.comp ((continuous_const.mul h2.continuous).neg)).sub
      (Real.continuous_exp.comp ((continuous_const.mul h1.continuous).neg))
  have hint : IntegrableOn (fun y ↦ |h y|) K' := hhc.abs.continuousOn.integrableOn_compact hK'
  have hball : Metric.ball x₀ 1 ⊆ K' := by
    intro y hy
    exact Metric.mem_cthickening_of_dist_le y x₀ 1 K hx₀ (Metric.mem_ball.mp hy).le
  -- Lipschitz bound on the unit ball with constant `t G ≤ Λ := t G + 1`
  have hdiff : ∀ y ∈ Metric.ball x₀ 1, DifferentiableAt ℝ h y := fun y _ ↦
    ((h2.differentiable (by simp) y).const_mul t).neg.exp.sub
      ((h1.differentiable (by simp) y).const_mul t).neg.exp
  have hbound : ∀ y ∈ Metric.ball x₀ 1, ‖fderiv ℝ h y‖ ≤ t * G := by
    intro y hy
    calc ‖fderiv ℝ h y‖ ≤ t * (‖fderiv ℝ L₁ y‖ + ‖fderiv ℝ L₂ y‖) :=
          norm_fderiv_weightDiff_le hL1 hL2 (h1.differentiable (by simp) y)
            (h2.differentiable (by simp) y) htpos.le
      _ ≤ t * G := mul_le_mul_of_nonneg_left (hG y (hball hy)) htpos.le
  have hlip : ∀ y ∈ Metric.ball x₀ 1, |h y - h x₀| ≤ (t * G + 1) * ‖y - x₀‖ := by
    intro y hy
    have := (convex_ball x₀ 1).norm_image_sub_le_of_norm_fderiv_le hdiff hbound
      (Metric.mem_ball_self one_pos) hy
    rw [Real.norm_eq_abs] at this
    calc |h y - h x₀| ≤ t * G * ‖y - x₀‖ := this
      _ ≤ (t * G + 1) * ‖y - x₀‖ := by gcongr; linarith
  have hΛ : (1 : ℝ) ≤ t * G + 1 := by nlinarith
  have hpeak := pow_abs_le_of_lipschitz_of_setIntegral hint hball hΛ hlip
    (abs_exp_sub_le_one hL1 hL2 htpos.le x₀)
  -- `Λ = tG + 1 ≤ (G + 1) t` for `t ≥ 1`
  have hΛle : (t * G + 1) ^ d ≤ ((G + 1) * t) ^ d := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have hInn : 0 ≤ ∫ y in K', |h y| :=
    setIntegral_nonneg_of_ae_restrict (Eventually.of_forall fun y ↦ abs_nonneg _)
  calc |h x₀| ^ (d + 1) ≤ 2 ^ (d + 1) / c * (t * G + 1) ^ d * ∫ y in K', |h y| := hpeak
    _ ≤ 2 ^ (d + 1) / c * ((G + 1) * t) ^ d * ∫ y in K', |h y| := by
        gcongr
    _ = 2 ^ (d + 1) / c * (G + 1) ^ d * t ^ d * ∫ y in K', |h y| := by
        rw [mul_pow]
        ring

/-- **Rate-explicit root form**: `|h_t x| ≤ (C t^d ∫_{K'} |h_t|)^{1/(d+1)}`. -/
theorem abs_exp_sub_le_rpow {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    {K : Set (ι → ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ x ∈ K,
      |Real.exp (-(t * L₂ x)) - Real.exp (-(t * L₁ x))| ≤
        (C * t ^ (Fintype.card ι) * ∫ y in Metric.cthickening 1 K,
          |Real.exp (-(t * L₂ y)) - Real.exp (-(t * L₁ y))|) ^
            (((Fintype.card ι : ℕ) + 1 : ℕ)⁻¹ : ℝ) := by
  obtain ⟨C, hC, hpow⟩ := pow_abs_exp_sub_le h1 h2 hL1 hL2 hK
  refine ⟨C, hC, fun t ht x hx ↦ ?_⟩
  have h := hpow t ht x hx
  have hn : Fintype.card ι + 1 ≠ 0 := Nat.succ_ne_zero _
  have hRHS : 0 ≤ C * t ^ (Fintype.card ι) * ∫ y in Metric.cthickening 1 K,
      |Real.exp (-(t * L₂ y)) - Real.exp (-(t * L₁ y))| := by
    have : 0 ≤ ∫ y in Metric.cthickening 1 K,
        |Real.exp (-(t * L₂ y)) - Real.exp (-(t * L₁ y))| :=
      setIntegral_nonneg_of_ae_restrict (Eventually.of_forall fun y ↦ abs_nonneg _)
    have ht0 : 0 ≤ t := zero_le_one.trans ht
    positivity
  calc |Real.exp (-(t * L₂ x)) - Real.exp (-(t * L₁ x))|
      = (|Real.exp (-(t * L₂ x)) - Real.exp (-(t * L₁ x))| ^ (Fintype.card ι + 1)) ^
          (((Fintype.card ι + 1 : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (abs_nonneg _) hn).symm
    _ ≤ _ := Real.rpow_le_rpow (by positivity) h (by positivity)

/-! ### Uniform agreement beyond all orders -/

/-- **Local uniform agreement beyond all orders.** For smooth nonnegative losses
with exact smooth-test agreement and any compact `K`: for every `N` there is `C`
with `|e^{-tL₂ x} - e^{-tL₁ x}| ≤ C t^{-N}` for all `x ∈ K`, eventually in `t`. -/
theorem eventually_uniform_abs_exp_sub_le {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hexact : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - ∫ w, φ w * Real.exp (-(t * L₁ w)))
    {K : Set (ι → ℝ)} (hK : IsCompact K) :
    ∀ N : ℕ, ∃ C : ℝ, ∀ᶠ t in atTop, ∀ x ∈ K,
      |Real.exp (-(t * L₂ x)) - Real.exp (-(t * L₁ x))| ≤ C * t ^ (-(N : ℝ)) := by
  set d := Fintype.card ι with hd
  obtain ⟨C₀, hC₀, hpow⟩ := pow_abs_exp_sub_le h1 h2 hL1 hL2 hK
  have hTV := superPoly_setIntegral_abs_exp_sub h1 h2 hL1 hL2 hexact
    (K := Metric.cthickening 1 K) (hK.cthickening (r := 1))
  intro N
  refine ⟨C₀ ^ (((d + 1 : ℕ) : ℝ)⁻¹), ?_⟩
  have hTVN := isLittleO_iff.mp (hTV ((d + 1) * N + d)) one_pos
  filter_upwards [hTVN, eventually_ge_atTop (1 : ℝ)] with t hFt ht
  intro x hx
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos htpos _),
    one_mul] at hFt
  have hF := le_trans (le_abs_self _) hFt
  have hn : d + 1 ≠ 0 := Nat.succ_ne_zero _
  have hCt : 0 ≤ C₀ ^ (((d + 1 : ℕ) : ℝ)⁻¹) * t ^ (-(N : ℝ)) := by positivity
  -- `t^d · t^{-((d+1)N + d)} = (t^{-N})^{d+1}`
  have hexp : t ^ d * t ^ (-(((d + 1) * N + d : ℕ) : ℝ)) = (t ^ (-(N : ℝ))) ^ (d + 1) := by
    rw [← Real.rpow_natCast t d, ← Real.rpow_add htpos, ← Real.rpow_natCast (t ^ (-(N : ℝ))),
      ← Real.rpow_mul htpos.le]
    congr 1
    push_cast
    ring
  have hroot : (C₀ ^ (((d + 1 : ℕ) : ℝ)⁻¹)) ^ (d + 1) = C₀ :=
    Real.rpow_inv_natCast_pow hC₀ hn
  refine le_of_pow_le_pow_left₀ hn hCt ?_
  calc |Real.exp (-(t * L₂ x)) - Real.exp (-(t * L₁ x))| ^ (d + 1)
      ≤ C₀ * t ^ d * ∫ y in Metric.cthickening 1 K,
          |Real.exp (-(t * L₂ y)) - Real.exp (-(t * L₁ y))| := hpow t ht x hx
    _ ≤ C₀ * t ^ d * t ^ (-(((d + 1) * N + d : ℕ) : ℝ)) := by
        gcongr
    _ = C₀ * (t ^ (-(N : ℝ))) ^ (d + 1) := by rw [mul_assoc, hexp]
    _ = (C₀ ^ (((d + 1 : ℕ) : ℝ)⁻¹) * t ^ (-(N : ℝ))) ^ (d + 1) := by
        rw [mul_pow, hroot]

/-- **Pointwise agreement beyond all orders** at every point. -/
theorem superPoly_exp_sub_at {L₁ L₂ : (ι → ℝ) → ℝ}
    (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂)
    (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
    (hexact : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      SuperPoly fun t ↦ (∫ w, φ w * Real.exp (-(t * L₂ w)))
        - ∫ w, φ w * Real.exp (-(t * L₁ w)))
    (x : ι → ℝ) :
    SuperPoly fun t ↦ Real.exp (-(t * L₂ x)) - Real.exp (-(t * L₁ x)) := by
  refine superPoly_of_forall_eventually_le fun N ↦ ?_
  obtain ⟨C, hC⟩ := eventually_uniform_abs_exp_sub_le h1 h2 hL1 hL2 hexact
    (isCompact_singleton (x := x)) N
  exact ⟨C, hC.mono fun t ht ↦ ht x (Set.mem_singleton x)⟩

end Laplace
