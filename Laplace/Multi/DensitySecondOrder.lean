/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ThetaPeano

/-!
# The second-order expansion of the family density in the natural coordinates

An explicit, pointwise-uniform bound: for `K‖η‖ ≤ 1/4` (`K = |J| sup|S|`),

`|p_{θ+η}(x) − p_θ(x) T_θ(η)(x)| ≤ 13 (K‖η‖)³ p_θ(x)`,

`T_θ(η)(x) = 1 + ⟨η, m(θ) − S(x)⟩ + ½ (⟨η, m(θ) − S(x)⟩² − Var_{P_θ}⟨η,S⟩)`
(`abs_famDens_second_remainder_le`). The core is a real inequality for a ratio of two truncated
exponentials (`abs_ratio_sub_second_order_le`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section RatioBound

/-- The cubic core of the ratio expansion: with `E₁ = 1 − w + w²/2 + r₁`, `E₂ = 1 − a + s/2 + r₂`
and `T = 1 + (a − w) + ½((w − a)² − (s − a²))`, one has
`E₁ − T E₂ = core(w,a,s) + r₁ − r₂ (1 − w + w²/2 + a − a w + a² − s/2)`; the core is cubic. -/
theorem ratio_core_identity (w a s r₁ r₂ : ℝ) :
    (1 - w + w ^ 2 / 2 + r₁) - (1 + (a - w) + (1 / 2) * ((w - a) ^ 2 - (s - a ^ 2))) *
      (1 - a + s / 2 + r₂) =
      (a ^ 3 - a ^ 2 * s / 2 - a ^ 2 * w + a * s * w / 2 - a * s + a * w ^ 2 / 2 + s ^ 2 / 4 -
        s * w ^ 2 / 4 + s * w / 2) + r₁ -
        r₂ * (1 + (a - w) + (1 / 2) * ((w - a) ^ 2 - (s - a ^ 2))) := by
  ring

/-- The cubic core is bounded by `11/2 · ε³` when `|w|, |a| ≤ ε ≤ 1` and `0 ≤ s ≤ ε²`. -/
theorem abs_ratio_core_le {ε w a s : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hw : |w| ≤ ε)
    (ha : |a| ≤ ε) (hs0 : 0 ≤ s) (hs : s ≤ ε ^ 2) :
    |a ^ 3 - a ^ 2 * s / 2 - a ^ 2 * w + a * s * w / 2 - a * s + a * w ^ 2 / 2 + s ^ 2 / 4 -
        s * w ^ 2 / 4 + s * w / 2| ≤ 11 / 2 * ε ^ 3 := by
  have hε3 : ε ^ 4 ≤ ε ^ 3 := by
    have : ε ^ 4 = ε ^ 3 * ε := by ring
    rw [this]
    calc ε ^ 3 * ε ≤ ε ^ 3 * 1 := by gcongr
      _ = ε ^ 3 := mul_one _
  have ha2 : |a| ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ha 2
  have hw2 : |w| ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hw 2
  have h1 : |a ^ 3| ≤ ε ^ 3 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ha 3
  have h2 : |a ^ 2 * s / 2| ≤ ε ^ 3 / 2 := by
    rw [abs_div, abs_mul, abs_pow, abs_of_nonneg hs0, abs_two]
    have : |a| ^ 2 * s ≤ ε ^ 2 * ε ^ 2 := mul_le_mul ha2 hs hs0 (by positivity)
    have e : ε ^ 2 * ε ^ 2 = ε ^ 4 := by ring
    linarith
  have h3 : |a ^ 2 * w| ≤ ε ^ 3 := by
    rw [abs_mul, abs_pow]
    have : |a| ^ 2 * |w| ≤ ε ^ 2 * ε := mul_le_mul ha2 hw (abs_nonneg _) (by positivity)
    have e : ε ^ 2 * ε = ε ^ 3 := by ring
    linarith
  have h4 : |a * s * w / 2| ≤ ε ^ 3 / 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hs0, abs_two]
    have h' : |a| * s ≤ ε * ε ^ 2 := mul_le_mul ha hs hs0 hε0
    have : |a| * s * |w| ≤ ε * ε ^ 2 * ε := mul_le_mul h' hw (abs_nonneg _) (by positivity)
    have e : ε * ε ^ 2 * ε = ε ^ 4 := by ring
    linarith
  have h5 : |a * s| ≤ ε ^ 3 := by
    rw [abs_mul, abs_of_nonneg hs0]
    have : |a| * s ≤ ε * ε ^ 2 := mul_le_mul ha hs hs0 hε0
    have e : ε * ε ^ 2 = ε ^ 3 := by ring
    linarith
  have h6 : |a * w ^ 2 / 2| ≤ ε ^ 3 / 2 := by
    rw [abs_div, abs_mul, abs_pow, abs_two]
    have : |a| * |w| ^ 2 ≤ ε * ε ^ 2 := mul_le_mul ha hw2 (by positivity) hε0
    have e : ε * ε ^ 2 = ε ^ 3 := by ring
    linarith
  have h7 : |s ^ 2 / 4| ≤ ε ^ 3 / 4 := by
    rw [abs_div, abs_pow, abs_of_nonneg hs0, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have : s ^ 2 ≤ (ε ^ 2) ^ 2 := pow_le_pow_left₀ hs0 hs 2
    have e : (ε ^ 2) ^ 2 = ε ^ 4 := by ring
    linarith
  have h8 : |s * w ^ 2 / 4| ≤ ε ^ 3 / 4 := by
    rw [abs_div, abs_mul, abs_pow, abs_of_nonneg hs0, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have : s * |w| ^ 2 ≤ ε ^ 2 * ε ^ 2 := mul_le_mul hs hw2 (by positivity) (by positivity)
    have e : ε ^ 2 * ε ^ 2 = ε ^ 4 := by ring
    linarith
  have h9 : |s * w / 2| ≤ ε ^ 3 / 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg hs0, abs_two]
    have : s * |w| ≤ ε ^ 2 * ε := mul_le_mul hs hw (abs_nonneg _) (by positivity)
    have e : ε ^ 2 * ε = ε ^ 3 := by ring
    linarith
  calc |a ^ 3 - a ^ 2 * s / 2 - a ^ 2 * w + a * s * w / 2 - a * s + a * w ^ 2 / 2 + s ^ 2 / 4 -
        s * w ^ 2 / 4 + s * w / 2|
      ≤ |a ^ 3| + |a ^ 2 * s / 2| + |a ^ 2 * w| + |a * s * w / 2| + |a * s| + |a * w ^ 2 / 2| +
        |s ^ 2 / 4| + |s * w ^ 2 / 4| + |s * w / 2| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
        exact abs_sub _ _
    _ ≤ 11 / 2 * ε ^ 3 := by linarith

/-- **The ratio of two second-order truncated exponentials**: for `|w|, |a| ≤ ε ≤ 1/4`,
`0 ≤ s ≤ ε²`, `|r₁|, |r₂| ≤ ε³/4`,
`|(1 − w + w²/2 + r₁)/(1 − a + s/2 + r₂) − (1 + (a − w) + ½((w − a)² − (s − a²)))| ≤ 13 ε³`. -/
theorem abs_ratio_sub_second_order_le {ε w a s r₁ r₂ : ℝ} (hε0 : 0 ≤ ε) (hε4 : ε ≤ 1 / 4)
    (hw : |w| ≤ ε) (ha : |a| ≤ ε) (hs0 : 0 ≤ s) (hs : s ≤ ε ^ 2) (hr₁ : |r₁| ≤ ε ^ 3 / 4)
    (hr₂ : |r₂| ≤ ε ^ 3 / 4) :
    |(1 - w + w ^ 2 / 2 + r₁) / (1 - a + s / 2 + r₂) -
      (1 + (a - w) + (1 / 2) * ((w - a) ^ 2 - (s - a ^ 2)))| ≤ 13 * ε ^ 3 := by
  have hε1 : ε ≤ 1 := by linarith
  have hw' := abs_le.1 hw
  have ha' := abs_le.1 ha
  have hr₂' := abs_le.1 hr₂
  have hε2 : ε ^ 2 ≤ ε := by
    have : ε ^ 2 = ε * ε := by ring
    rw [this]
    calc ε * ε ≤ ε * 1 := by gcongr
      _ = ε := mul_one _
  have hε3 : ε ^ 3 ≤ ε := by
    have : ε ^ 3 = ε ^ 2 * ε := by ring
    rw [this]
    calc ε ^ 2 * ε ≤ ε * ε := by gcongr
      _ ≤ ε * 1 := by gcongr
      _ = ε := mul_one _
  have hE2 : 1 / 2 ≤ 1 - a + s / 2 + r₂ := by linarith [ha'.1, hr₂'.1]
  have hE2pos : 0 < 1 - a + s / 2 + r₂ := by linarith
  have hT : |1 + (a - w) + (1 / 2) * ((w - a) ^ 2 - (s - a ^ 2))| ≤ 2 := by
    have h1 : |(w - a) ^ 2| ≤ 4 * ε ^ 2 := by
      rw [abs_pow]
      have : |w - a| ≤ 2 * ε := (abs_sub _ _).trans (by linarith)
      calc |w - a| ^ 2 ≤ (2 * ε) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = 4 * ε ^ 2 := by ring
    have ha2 : a ^ 2 ≤ ε ^ 2 := by
      rw [← sq_abs a]
      exact pow_le_pow_left₀ (abs_nonneg _) ha 2
    have h2 : |s - a ^ 2| ≤ ε ^ 2 := by
      rw [abs_le]
      constructor <;> linarith [sq_nonneg a]
    calc |1 + (a - w) + (1 / 2) * ((w - a) ^ 2 - (s - a ^ 2))|
        ≤ |1 + (a - w)| + |(1 / 2) * ((w - a) ^ 2 - (s - a ^ 2))| := abs_add_le _ _
      _ ≤ (1 + |a - w|) + (1 / 2) * (|(w - a) ^ 2| + |s - a ^ 2|) := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          refine add_le_add ((abs_add_le _ _).trans (by rw [abs_one])) ?_
          exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
      _ ≤ (1 + 2 * ε) + (1 / 2) * (4 * ε ^ 2 + ε ^ 2) := by
          have : |a - w| ≤ 2 * ε := (abs_sub _ _).trans (by linarith)
          gcongr
      _ ≤ 2 := by nlinarith
  have hcore := abs_ratio_core_le hε0 hε1 hw ha hs0 hs
  have hnum : |(1 - w + w ^ 2 / 2 + r₁) -
      (1 + (a - w) + (1 / 2) * ((w - a) ^ 2 - (s - a ^ 2))) * (1 - a + s / 2 + r₂)| ≤
      13 / 2 * ε ^ 3 := by
    rw [ratio_core_identity]
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
    rw [abs_neg, abs_mul]
    have : |r₂| * |1 + (a - w) + (1 / 2) * ((w - a) ^ 2 - (s - a ^ 2))| ≤ ε ^ 3 / 4 * 2 :=
      mul_le_mul hr₂ hT (abs_nonneg _) (by positivity)
    linarith
  rw [div_sub' hE2pos.ne', abs_div, abs_of_pos hE2pos, div_le_iff₀ hE2pos]
  calc |(1 - w + w ^ 2 / 2 + r₁) -
        (1 - a + s / 2 + r₂) * (1 + (a - w) + (1 / 2) * ((w - a) ^ 2 - (s - a ^ 2)))|
      = |(1 - w + w ^ 2 / 2 + r₁) -
        (1 + (a - w) + (1 / 2) * ((w - a) ^ 2 - (s - a ^ 2))) * (1 - a + s / 2 + r₂)| := by
        rw [mul_comm]
    _ ≤ 13 / 2 * ε ^ 3 := hnum
    _ = 13 * ε ^ 3 * (1 / 2) := by ring
    _ ≤ 13 * ε ^ 3 * (1 - a + s / 2 + r₂) := by gcongr

end RatioBound

section Exp

/-- `|e^{−w} − (1 − w + w²/2)| ≤ |w|³/4` for `|w| ≤ 1`. -/
theorem abs_exp_neg_sub_second_le {w : ℝ} (hw : |w| ≤ 1) :
    |Real.exp (-w) - (1 - w + w ^ 2 / 2)| ≤ |w| ^ 3 / 4 := by
  have h := Real.exp_bound (x := -w) (by rwa [abs_neg]) (n := 3) (by norm_num)
  have e : ∑ m ∈ Finset.range 3, (-w) ^ m / (m.factorial : ℝ) = 1 - w + w ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  rw [e, abs_neg] at h
  refine h.trans ?_
  have : ((3 : ℕ).succ : ℝ) / ((3 : ℕ).factorial * (3 : ℕ) : ℝ) = 2 / 9 := by
    norm_num [Nat.factorial]
  rw [this]
  have h3 : 0 ≤ |w| ^ 3 := by positivity
  linarith

end Exp

section Family

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] {S : J → X → ℝ}
  (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν] {B : ℝ} (hB0 : 0 ≤ B)
  (hB : ∀ j x, |S j x| ≤ B)

/-- The second-order truncation of the density ratio,
`T_θ(η)(x) = 1 + ⟨η, m(θ) − S(x)⟩ + ½ (⟨η, m(θ) − S(x)⟩² − Var_{P_θ}⟨η,S⟩)`. -/
noncomputable def densTrunc (S : J → X → ℝ) (ν : Measure X) (θ η : J → ℝ) (x : X) : ℝ :=
  1 + (dotJ η (famMean S ν θ) - dirLoss S η x) +
    (1 / 2) * ((dotJ η (famMean S ν θ) - dirLoss S η x) ^ 2 -
      ((∫ y, (dirLoss S η y) ^ 2 * famDens S ν θ y ∂ν) - dotJ η (famMean S ν θ) ^ 2))

include hS

/-- The normaliser ratio is the `P_θ`-expectation of the tilt. -/
theorem famZ_add_div (θ η : J → ℝ) :
    famZ S ν (θ + η) / famZ S ν θ = ∫ y, Real.exp (-dirLoss S η y) * famDens S ν θ y ∂ν := by
  have hZ := famZ_pos hS ν θ
  have e : (fun y ↦ Real.exp (-dirLoss S η y) * famDens S ν θ y) =
      fun y ↦ famWeight S (θ + η) y / famZ S ν θ := funext fun y ↦ by
    rw [famWeight_add]
    unfold famDens
    ring
  rw [e, integral_div]
  rfl

/-- The first moment of the tilt under `P_θ` is `⟨η, m(θ)⟩`. -/
theorem integral_dirLoss_mul_famDens (θ η : J → ℝ) :
    ∫ y, dirLoss S η y * famDens S ν θ y ∂ν = dotJ η (famMean S ν θ) := by
  have hZ := famZ_pos hS ν θ
  have h := integral_dirLoss_mul_famWeight hS ν θ η
  have e : (fun y ↦ dirLoss S η y * famDens S ν θ y) =
      fun y ↦ (dirLoss S η y * famWeight S θ y) / famZ S ν θ := funext fun y ↦ by
    unfold famDens
    ring
  rw [e, integral_div, h]
  field_simp

include hB0 hB

/-- **Pointwise second-order bound for the density**: for `K‖η‖ ≤ 1/4`,
`|p_{θ+η}(x) − p_θ(x) T_θ(η)(x)| ≤ 13 (K‖η‖)³ p_θ(x)`. -/
theorem abs_famDens_second_remainder_le (θ η : J → ℝ)
    (h1 : (Fintype.card J : ℝ) * B * ‖η‖ ≤ 1 / 4) (x : X) :
    |famDens S ν (θ + η) x - famDens S ν θ x * densTrunc S ν θ η x| ≤
      13 * ((Fintype.card J : ℝ) * B * ‖η‖) ^ 3 * famDens S ν θ x := by
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (Fintype.card J : ℝ) * B * ‖η‖ := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hε4 : ε ≤ 1 / 4 := by rw [hε]; exact h1
  have hε1 : ε ≤ 1 := by linarith
  have hZ := famZ_pos hS ν θ
  have hZ' := famZ_pos hS ν (θ + η)
  have hq0 := famDens_nonneg hS ν θ x
  have hwy : ∀ y, |dirLoss S η y| ≤ ε := fun y ↦ by
    rw [hε]
    exact abs_dirLoss_le_card_mul hB0 hB η y
  have ha : |dotJ η (famMean S ν θ)| ≤ ε := by
    rw [hε]
    exact abs_dotJ_famMean_le hS ν hB0 hB θ η
  have hr₁ : |Real.exp (-dirLoss S η x) - (1 - dirLoss S η x + dirLoss S η x ^ 2 / 2)| ≤
      ε ^ 3 / 4 := by
    refine (abs_exp_neg_sub_second_le ((hwy x).trans hε1)).trans ?_
    have : |dirLoss S η x| ^ 3 ≤ ε ^ 3 := pow_le_pow_left₀ (abs_nonneg _) (hwy x) 3
    linarith
  -- moments of the tilt
  have hint1 : Integrable (fun y ↦ dirLoss S η y * famDens S ν θ y) ν := by
    refine (integrable_famDens hS ν θ).bdd_mul (c := ε) (bdd_dirLoss hS η).1.aestronglyMeasurable
      (Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_eq_abs]
    exact hwy y
  have hint2 : Integrable (fun y ↦ (dirLoss S η y) ^ 2 * famDens S ν θ y) ν := by
    refine (integrable_famDens hS ν θ).bdd_mul (c := ε ^ 2)
      ((bdd_dirLoss hS η).1.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hwy y) 2
  have hs0 : 0 ≤ ∫ y, (dirLoss S η y) ^ 2 * famDens S ν θ y ∂ν :=
    integral_nonneg fun y ↦ mul_nonneg (sq_nonneg _) (famDens_nonneg hS ν θ y)
  have hs : ∫ y, (dirLoss S η y) ^ 2 * famDens S ν θ y ∂ν ≤ ε ^ 2 := by
    calc ∫ y, (dirLoss S η y) ^ 2 * famDens S ν θ y ∂ν
        ≤ ∫ y, ε ^ 2 * famDens S ν θ y ∂ν := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y ↦ mul_nonneg (sq_nonneg _)
            (famDens_nonneg hS ν θ y)) ((integrable_famDens hS ν θ).const_mul _)
            (Eventually.of_forall fun y ↦ ?_)
          have : dirLoss S η y ^ 2 ≤ ε ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hwy y) 2
          exact mul_le_mul_of_nonneg_right this (famDens_nonneg hS ν θ y)
      _ = ε ^ 2 := by rw [integral_const_mul, integral_famDens hS ν, mul_one]
  have hmean := integral_dirLoss_mul_famDens hS ν θ η
  -- the normaliser ratio and its expansion
  have hexp : Integrable (fun y ↦ Real.exp (-dirLoss S η y) * famDens S ν θ y) ν := by
    refine (integrable_famDens hS ν θ).bdd_mul (c := Real.exp ε)
      ((bdd_dirLoss hS η).1.neg.exp).aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by linarith [abs_le.1 (hwy y)])
  have hpoly : Integrable (fun y ↦ (1 - dirLoss S η y + dirLoss S η y ^ 2 / 2) *
      famDens S ν θ y) ν := by
    have i1 : Integrable (fun y ↦ famDens S ν θ y - dirLoss S η y * famDens S ν θ y) ν :=
      (integrable_famDens hS ν θ).sub hint1
    have i12 : Integrable (fun y ↦ (famDens S ν θ y - dirLoss S η y * famDens S ν θ y) +
        dirLoss S η y ^ 2 * famDens S ν θ y / 2) ν := i1.add (hint2.div_const 2)
    exact i12.congr (Eventually.of_forall fun y ↦ by ring)
  have epoly : ∫ y, (1 - dirLoss S η y + dirLoss S η y ^ 2 / 2) * famDens S ν θ y ∂ν =
      1 - dotJ η (famMean S ν θ) + (∫ y, (dirLoss S η y) ^ 2 * famDens S ν θ y ∂ν) / 2 := by
    have i1 : Integrable (fun y ↦ famDens S ν θ y - dirLoss S η y * famDens S ν θ y) ν :=
      (integrable_famDens hS ν θ).sub hint1
    have e' : (fun y ↦ (1 - dirLoss S η y + dirLoss S η y ^ 2 / 2) * famDens S ν θ y) =
        fun y ↦ (famDens S ν θ y - dirLoss S η y * famDens S ν θ y) +
          dirLoss S η y ^ 2 * famDens S ν θ y / 2 := funext fun y ↦ by ring
    rw [e', integral_add i1 (hint2.div_const 2), integral_sub (integrable_famDens hS ν θ) hint1,
      integral_famDens hS ν, hmean, integral_div]
  have hr₂ : |(famZ S ν (θ + η) / famZ S ν θ) -
      (1 - dotJ η (famMean S ν θ) + (∫ y, (dirLoss S η y) ^ 2 * famDens S ν θ y ∂ν) / 2)| ≤
      ε ^ 3 / 4 := by
    rw [famZ_add_div hS ν θ η, ← epoly, ← integral_sub hexp hpoly]
    have := norm_integral_le_of_norm_le ((integrable_famDens hS ν θ).const_mul (ε ^ 3 / 4))
      (μ := ν) (f := fun y ↦ Real.exp (-dirLoss S η y) * famDens S ν θ y -
        (1 - dirLoss S η y + dirLoss S η y ^ 2 / 2) * famDens S ν θ y)
      (Eventually.of_forall fun y ↦ by
        rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (famDens_nonneg hS ν θ y)]
        refine mul_le_mul_of_nonneg_right ?_ (famDens_nonneg hS ν θ y)
        refine (abs_exp_neg_sub_second_le ((hwy y).trans hε1)).trans ?_
        have : |dirLoss S η y| ^ 3 ≤ ε ^ 3 := pow_le_pow_left₀ (abs_nonneg _) (hwy y) 3
        linarith)
    rwa [integral_const_mul, integral_famDens hS ν, mul_one, Real.norm_eq_abs] at this
  -- assemble
  have hratio := abs_ratio_sub_second_order_le hε0 hε4 (hwy x) ha hs0 hs hr₁ hr₂
  rw [add_sub_cancel, add_sub_cancel] at hratio
  have hdiv : famDens S ν (θ + η) x = famDens S ν θ x *
      (Real.exp (-dirLoss S η x) / (famZ S ν (θ + η) / famZ S ν θ)) := by
    unfold famDens
    rw [famWeight_add]
    field_simp
  have hT : 1 + (dotJ η (famMean S ν θ) - dirLoss S η x) +
      (1 / 2) * ((dirLoss S η x - dotJ η (famMean S ν θ)) ^ 2 -
        ((∫ y, (dirLoss S η y) ^ 2 * famDens S ν θ y ∂ν) - dotJ η (famMean S ν θ) ^ 2)) =
      densTrunc S ν θ η x := by
    unfold densTrunc
    ring
  rw [hT] at hratio
  rw [hdiv, ← mul_sub, abs_mul, abs_of_nonneg hq0]
  calc famDens S ν θ x * |Real.exp (-dirLoss S η x) / (famZ S ν (θ + η) / famZ S ν θ) -
        densTrunc S ν θ η x|
      ≤ famDens S ν θ x * (13 * ((Fintype.card J : ℝ) * B * ‖η‖) ^ 3) :=
        mul_le_mul_of_nonneg_left (by rw [← hε]; exact hratio) hq0
    _ = _ := by ring

end Family

end Laplace.Multi
