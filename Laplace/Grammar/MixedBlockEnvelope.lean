/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.FrozenBlock

/-!
# Minimal block IV: the mixed-block envelope and the freezing inequalities (grammar §4.2)

Two inputs for the continuity freezing argument of the multiplicity-`m` theorem.

* **Mixed-block envelope.** If one coordinate of a `(d₀+2)`-block carries an exponent `> p` and the
  other `d₀+1` carry exactly `p`, then `c^p Z(c) ≤ K (1 + log₊(cB))^{d₀}` for every `c > 0`
  (`iterChartGen_mixed_le`): one logarithm is lost. In box form, inserting a factor `u_i` into an
  equal-exponent block gives this bound (`boxIntegralFin_shift_le`), the Hölder-insertion estimate.
* **Freezing inequalities.** The mean-value bound
  `|η₁ e^{-βs²+βξ₁s} − η₂ e^{-βs²+βξ₂s}| ≤ (|η₁−η₂| + M e^{β/2}|ξ₁−ξ₂|) e^{-(β/2)s²+βLs}`
  (`weighted_quadKernel_sub_le`) and the corner/strip split
  `D(u) ≤ ω + (D_max/δ) ∑ᵢ uᵢ` (`corner_strip_le`).

Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- **Mixed-block envelope**: exponent `q_0 > p = q_1 = … = q_{d₀+1}`; then for all `c > 0`,
`c^p Z_{d₀+2}(c) ≤ K (1 + log₊(cB))^{d₀}`. -/
theorem iterChartGen_mixed_le (β a b : ℝ) (k h : ℕ → ℕ) (p : ℝ) (hβ : 0 < β) (hb : 0 < b)
    (hk : ∀ i, 0 < k i) (d₀ : ℕ) (hp : ∀ l, 1 ≤ l → l ≤ d₀ + 1 → chartExp k h l = p)
    (hlt : p < chartExp k h 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c, 0 < c → c ^ p * iterChartGen β a b k h (d₀ + 2) c
      ≤ K * (1 + logPlus (c * b ^ (∑ i ∈ Finset.range (d₀ + 2), k i))) ^ d₀ := by
  obtain ⟨_, M, C', hLB⟩ := genTower_logBase β a k h hβ hk 0 p
    (fun i hi => absurd hi (Nat.not_lt_zero i)) (hp 1 le_rfl (by omega)) hlt
  obtain ⟨K₁, hK₁, hbound⟩ := iterDivPrim_le_polyLog hLB d₀
  have htower := genTower_block_eq_iterDivPrim β a k h 0 d₀ p
    (fun l h1 h2 => hp l h1 (by omega))
  rw [show 0 + 2 + d₀ = d₀ + 2 by omega] at htower
  have hprev : prevExp k h (d₀ + 2) = p := by
    rw [show d₀ + 2 = d₀ + 1 + 1 by ring, prevExp_succ]
    exact hp (d₀ + 1) (by omega) le_rfl
  refine ⟨(∏ i ∈ Finset.range (d₀ + 2), (1 : ℝ) / k i) * genScale b k h (d₀ + 2) * K₁,
    by have := genScale_pos b k h hb (d₀ + 2); positivity, fun c hc => ?_⟩
  rw [iterChartGen_eq_genTower β a b k h hb hk (d₀ + 2) c hc, hprev, htower]
  have hcc : c ^ p * c ^ (-p) = 1 := by rw [← Real.rpow_add hc]; simp
  have hx : 0 < c * b ^ (∑ i ∈ Finset.range (d₀ + 2), k i) := by positivity
  have hH := hbound _ hx
  have hPD : 0 ≤ (∏ i ∈ Finset.range (d₀ + 2), (1 : ℝ) / k i) * genScale b k h (d₀ + 2) := by
    have := genScale_pos b k h hb (d₀ + 2); positivity
  calc c ^ p * ((∏ i ∈ Finset.range (d₀ + 2), (1 : ℝ) / k i) * genScale b k h (d₀ + 2)
        * c ^ (-p)
        * iterDivPrim (genTower β a k h 2) d₀ (c * b ^ (∑ i ∈ Finset.range (d₀ + 2), k i)))
      = (c ^ p * c ^ (-p)) * ((∏ i ∈ Finset.range (d₀ + 2), (1 : ℝ) / k i) * genScale b k h (d₀ + 2)
        * iterDivPrim (genTower β a k h 2) d₀ (c * b ^ (∑ i ∈ Finset.range (d₀ + 2), k i))) := by
        ring
    _ = (∏ i ∈ Finset.range (d₀ + 2), (1 : ℝ) / k i) * genScale b k h (d₀ + 2)
        * iterDivPrim (genTower β a k h 2) d₀ (c * b ^ (∑ i ∈ Finset.range (d₀ + 2), k i)) := by
        rw [hcc, one_mul]
    _ ≤ (∏ i ∈ Finset.range (d₀ + 2), (1 : ℝ) / k i) * genScale b k h (d₀ + 2)
        * (K₁ * (1 + logPlus (c * b ^ (∑ i ∈ Finset.range (d₀ + 2), k i))) ^ d₀) :=
        mul_le_mul_of_nonneg_left hH hPD
    _ = _ := by ring

/-- The exponent vector with `1` added at coordinate `i`. -/
def shiftExp {m : ℕ} (h : Fin m → ℕ) (i : Fin m) : Fin m → ℕ :=
  fun j => h j + if j = i then 1 else 0

theorem shiftExp_apply_self {m : ℕ} (h : Fin m → ℕ) (i : Fin m) : shiftExp h i i = h i + 1 := by
  simp [shiftExp]

theorem shiftExp_apply_ne {m : ℕ} (h : Fin m → ℕ) (i j : Fin m) (hj : j ≠ i) :
    shiftExp h i j = h j := by
  simp [shiftExp, hj]

/-- **Hölder-insertion estimate (box form)**: inserting `u_i` into an equal-exponent block of
`d₀+2` coordinates loses one logarithm: `c^p ∫ u^{h+e_i} e^{…}(c u^k) du ≤ K (1 + log₊(cB))^{d₀}`
for every `c > 0`. -/
theorem boxIntegralFin_shift_le (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) {d₀ : ℕ}
    (k h : Fin (d₀ + 2) → ℕ) (hk : ∀ j, 0 < k j) (p : ℝ) (hp : ∀ j, finExp k h j = p)
    (i : Fin (d₀ + 2)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c, 0 < c → c ^ p * boxIntegralFin β a b c k (shiftExp h i)
      ≤ K * (1 + logPlus (c * b ^ (∑ j, k j))) ^ d₀ := by
  set σ : Equiv.Perm (Fin (d₀ + 2)) := Equiv.swap 0 i with hσ
  set k' : ℕ → ℕ := toNatFun (k ∘ σ) 1 with hk'
  set h' : ℕ → ℕ := toNatFun (shiftExp h i ∘ σ) 0 with hh'
  have hk'pos : ∀ j, 0 < k' j := toNatFun_pos (k ∘ σ) fun j => hk (σ j)
  have hσ0 : σ 0 = i := Equiv.swap_apply_left 0 i
  have hσne : ∀ j : Fin (d₀ + 2), j ≠ 0 → σ j ≠ i := by
    intro j hj heq
    have : j = 0 := by
      have h1 : σ j = σ 0 := by rw [heq, hσ0]
      exact σ.injective h1
    exact hj this
  -- exponents of the relabelled block
  have hexp : ∀ j : Fin (d₀ + 2), chartExp k' h' (j : ℕ) = finExp k (shiftExp h i) (σ j) := by
    intro j
    rw [hk', hh', chartExp_toNatFun_eq_finExp]
    rfl
  have hp' : ∀ l, 1 ≤ l → l ≤ d₀ + 1 → chartExp k' h' l = p := by
    intro l h1 h2
    have hl : l < d₀ + 2 := by omega
    have hj0 : (⟨l, hl⟩ : Fin (d₀ + 2)) ≠ 0 := by
      intro heq
      have := congrArg Fin.val heq
      simp at this
      omega
    have := hexp ⟨l, hl⟩
    rw [this, finExp, shiftExp_apply_ne h i _ (hσne _ hj0)]
    exact hp _
  have hlt : p < chartExp k' h' 0 := by
    have := hexp 0
    simp only [Fin.val_zero] at this
    rw [this, hσ0, finExp, shiftExp_apply_self, ← hp i, finExp]
    have hki : (0 : ℝ) < k i := Nat.cast_pos.2 (hk i)
    rw [div_lt_div_iff_of_pos_right hki]
    push_cast
    linarith
  obtain ⟨K, hK, hbound⟩ := iterChartGen_mixed_le β a b k' h' p hβ hb hk'pos d₀ hp' hlt
  have hsum : ∑ j ∈ Finset.range (d₀ + 2), k' j = ∑ j, k j := by
    rw [Finset.sum_range]
    calc ∑ j : Fin (d₀ + 2), k' (j : ℕ) = ∑ j : Fin (d₀ + 2), k (σ j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hk', toNatFun_coe]; rfl
      _ = ∑ j, k j := Equiv.sum_comp σ k
  refine ⟨K, hK, fun c hc => ?_⟩
  rw [← boxIntegralFin_perm β a b c k (shiftExp h i) σ, boxIntegralFin_eq_toNatFun,
    boxIntegral_eq_iterChartGen, ← hsum]
  exact hbound c hc

/-- `βs e^{-(β/2)s²} ≤ e^{β/2}` for `s ≥ 0`. -/
theorem mul_exp_neg_half_sq_le (β s : ℝ) (hβ : 0 < β) :
    β * s * Real.exp (-(β / 2) * s ^ 2) ≤ Real.exp (β / 2) := by
  have h1 : β * s ≤ Real.exp (β / 2 + β / 2 * s ^ 2) := by
    have := Real.add_one_le_exp (β / 2 + β / 2 * s ^ 2)
    nlinarith [mul_nonneg hβ.le (sq_nonneg (s - 1))]
  calc β * s * Real.exp (-(β / 2) * s ^ 2)
      ≤ Real.exp (β / 2 + β / 2 * s ^ 2) * Real.exp (-(β / 2) * s ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (β / 2) := by rw [← Real.exp_add]; ring_nf

/-- `|e^x − e^y| ≤ |x − y| e^{max x y}`. -/
theorem abs_exp_sub_exp_le (x y : ℝ) :
    |Real.exp x - Real.exp y| ≤ |x - y| * Real.exp (max x y) := by
  wlog hxy : y ≤ x generalizing x y
  · have := this y x (le_of_not_ge hxy)
    rwa [abs_sub_comm (Real.exp y), abs_sub_comm y x, max_comm] at this
  rw [max_eq_left hxy, abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 hxy)),
    abs_of_nonneg (sub_nonneg.2 hxy)]
  have h := Real.add_one_le_exp (y - x)
  have hex : 0 < Real.exp x := Real.exp_pos x
  have : Real.exp y = Real.exp x * Real.exp (y - x) := by rw [← Real.exp_add]; ring_nf
  rw [this]
  nlinarith

/-- **Mean-value bound for weighted kernels**: for `|ξ₁|, |ξ₂| ≤ L`, `|η₂| ≤ M`, `s ≥ 0`,
`|η₁ f_{ξ₁}(s) − η₂ f_{ξ₂}(s)| ≤ (|η₁−η₂| + M e^{β/2} |ξ₁−ξ₂|) e^{-(β/2)s² + βLs}`. -/
theorem weighted_quadKernel_sub_le (β L M ξ₁ ξ₂ η₁ η₂ s : ℝ) (hβ : 0 < β) (hs : 0 ≤ s)
    (hξ₁ : |ξ₁| ≤ L) (hξ₂ : |ξ₂| ≤ L) (hη₂ : |η₂| ≤ M) :
    |η₁ * quadKernel β ξ₁ s - η₂ * quadKernel β ξ₂ s|
      ≤ (|η₁ - η₂| + M * Real.exp (β / 2) * |ξ₁ - ξ₂|) * quadKernel (β / 2) (2 * L) s := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hη₂
  have hL1 : ξ₁ ≤ L := (le_abs_self _).trans hξ₁
  have hL2 : ξ₂ ≤ L := (le_abs_self _).trans hξ₂
  set x₁ := -β * s ^ 2 + β * ξ₁ * s with hx₁
  set x₂ := -β * s ^ 2 + β * ξ₂ * s with hx₂
  have hq : quadKernel (β / 2) (2 * L) s = Real.exp (-(β / 2) * s ^ 2) * Real.exp (β * L * s) := by
    unfold quadKernel; rw [← Real.exp_add]; ring_nf
  have hbs : 0 ≤ β * s := by positivity
  have hx₁le : x₁ ≤ -β * s ^ 2 + β * L * s := by
    rw [hx₁]; nlinarith
  have hx₂le : x₂ ≤ -β * s ^ 2 + β * L * s := by
    rw [hx₂]; nlinarith
  have hmax : max x₁ x₂ ≤ -β * s ^ 2 + β * L * s := max_le hx₁le hx₂le
  have hexp1 : Real.exp x₁ ≤ Real.exp (-(β / 2) * s ^ 2) * Real.exp (β * L * s) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg hβ.le (sq_nonneg s)])
  have hdiff : |Real.exp x₁ - Real.exp x₂|
      ≤ β * s * |ξ₁ - ξ₂| * (Real.exp (-β * s ^ 2) * Real.exp (β * L * s)) := by
    calc |Real.exp x₁ - Real.exp x₂| ≤ |x₁ - x₂| * Real.exp (max x₁ x₂) := abs_exp_sub_exp_le _ _
      _ = β * s * |ξ₁ - ξ₂| * Real.exp (max x₁ x₂) := by
          rw [hx₁, hx₂, show -β * s ^ 2 + β * ξ₁ * s - (-β * s ^ 2 + β * ξ₂ * s)
            = (β * s) * (ξ₁ - ξ₂) by ring, abs_mul, abs_of_nonneg hbs]
      _ ≤ β * s * |ξ₁ - ξ₂| * (Real.exp (-β * s ^ 2) * Real.exp (β * L * s)) := by
          rw [← Real.exp_add]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hmax) (by positivity)
  have hkey : β * s * Real.exp (-β * s ^ 2) ≤ Real.exp (β / 2) * Real.exp (-(β / 2) * s ^ 2) := by
    have h1 : Real.exp (-β * s ^ 2)
        = Real.exp (-(β / 2) * s ^ 2) * Real.exp (-(β / 2) * s ^ 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [h1, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_exp_neg_half_sq_le β s hβ) (Real.exp_pos _).le
  have hsplit : η₁ * quadKernel β ξ₁ s - η₂ * quadKernel β ξ₂ s
      = (η₁ - η₂) * Real.exp x₁ + η₂ * (Real.exp x₁ - Real.exp x₂) := by
    unfold quadKernel; rw [hx₁, hx₂]; ring
  rw [hsplit, hq]
  have hE : 0 ≤ Real.exp (-(β / 2) * s ^ 2) * Real.exp (β * L * s) := by positivity
  calc |(η₁ - η₂) * Real.exp x₁ + η₂ * (Real.exp x₁ - Real.exp x₂)|
      ≤ |η₁ - η₂| * Real.exp x₁ + |η₂| * |Real.exp x₁ - Real.exp x₂| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ |η₁ - η₂| * (Real.exp (-(β / 2) * s ^ 2) * Real.exp (β * L * s))
        + M * (β * s * |ξ₁ - ξ₂| * (Real.exp (-β * s ^ 2) * Real.exp (β * L * s))) := by
        gcongr
    _ = |η₁ - η₂| * (Real.exp (-(β / 2) * s ^ 2) * Real.exp (β * L * s))
        + M * |ξ₁ - ξ₂| * Real.exp (β * L * s) * (β * s * Real.exp (-β * s ^ 2)) := by ring
    _ ≤ |η₁ - η₂| * (Real.exp (-(β / 2) * s ^ 2) * Real.exp (β * L * s))
        + M * |ξ₁ - ξ₂| * Real.exp (β * L * s)
          * (Real.exp (β / 2) * Real.exp (-(β / 2) * s ^ 2)) := by
        gcongr
    _ = _ := by ring

/-- **Corner/strip split**: if `D ≤ ω` whenever all `u_i ≤ δ`, and `D ≤ D_max` always, then for
positive `u`, `D ≤ ω + (D_max/δ) ∑ᵢ uᵢ`. -/
theorem corner_strip_le {m : ℕ} (u : Fin m → ℝ) (hu : ∀ i, 0 < u i) (D ω δ Dmax : ℝ) (hδ : 0 < δ)
    (hω : 0 ≤ ω) (hDmax : 0 ≤ Dmax) (hcorner : (∀ i, u i ≤ δ) → D ≤ ω) (hmax : D ≤ Dmax) :
    D ≤ ω + Dmax / δ * ∑ i, u i := by
  have hsum : 0 ≤ ∑ i, u i := Finset.sum_nonneg fun i _ => (hu i).le
  have hnn : 0 ≤ Dmax / δ * ∑ i, u i := mul_nonneg (div_nonneg hDmax hδ.le) hsum
  by_cases hall : ∀ i, u i ≤ δ
  · linarith [hcorner hall]
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    have h1 : u i ≤ ∑ j, u j := Finset.single_le_sum (fun j _ => (hu j).le) (Finset.mem_univ i)
    calc D ≤ Dmax := hmax
      _ = Dmax / δ * δ := by field_simp
      _ ≤ Dmax / δ * u i := mul_le_mul_of_nonneg_left hi.le (div_nonneg hDmax hδ.le)
      _ ≤ Dmax / δ * ∑ j, u j := mul_le_mul_of_nonneg_left h1 (div_nonneg hDmax hδ.le)
      _ ≤ ω + Dmax / δ * ∑ j, u j := by linarith

end Laplace.Grammar
