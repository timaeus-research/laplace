/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TaylorTreeEqual

/-!
# The Taylor tree in the paper's normalisation, and the leading log coefficient (grammar §4.2)

The paper writes the standard integral with `√n u^k ξ` and `e^{−βn u^{2k}}`; our `N` is `√n`.
`twoD_taylor_tree_equal_n` restates the `d = 2` Taylor tree in `n`: for every `T`,
`Z(√n) − ∑_{α < 2T} n^{−α/2}(A_α · (log n)/2 + B_α) = O(n^{−T}(1 + log n))`, so the paper's
`P_μ(X) = A_{2μ} X/2 + B_{2μ}`.

The leading pole `α = p` is a collision of `i = j = 0`, and `c_{00}(s) = e^{βs x₀₀} y₀₀`
(`ampCoeff_zero`), so the coefficient of `N^{−p} log N` is
`A_p = y₀₀/(k₁k₂) · ∫₀^∞ s^{p−1} e^{−βs² + βs x₀₀} ds` (`leading_log_coeff`): it depends on `ξ` only
through `ξ(0) = x₀₀` and on `η` only through `η(0) = y₀₀` (Astra #8 (f)). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

theorem tendsto_sqrt_atTop' : Tendsto (fun n : ℝ => Real.sqrt n) atTop atTop := by
  have h := tendsto_rpow_atTop (y := (1 / 2 : ℝ)) (by norm_num)
  exact h.congr fun n => (Real.sqrt_eq_rpow n).symm

/-- **The Taylor tree for `d = 2` in the paper's normalisation** `n = N²`. -/
theorem twoD_taylor_tree_equal_n (β b p ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x) (hy : WSummable ρ y)
    (T : ℝ) :
    (fun n : ℝ => twoDAmp β b (Real.sqrt n) h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b)
        - ∑ α ∈ polesBelow h₁ h₂ k₁ k₂ p T,
            n ^ (-(α / 2)) * (canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) α
                * (Real.log n / 2)
              + canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x y) b) (anaFaceV (ampCoeff β x y) b)
                  (fun i j s => ampCoeff β x y (i, j) s) α))
      =O[atTop] fun n : ℝ => n ^ (-T) * (1 + Real.log n) := by
  have h1 := (twoD_taylor_tree_equal β b p ρ h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ x y hx hy
    T).comp_tendsto tendsto_sqrt_atTop'
  have h2 : (fun n : ℝ => Real.sqrt n ^ (-(2 * T)) * (1 + Real.log (Real.sqrt n))) =O[atTop]
      fun n : ℝ => n ^ (-T) * (1 + Real.log n) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with n hn
    have hn0 : (0 : ℝ) ≤ n := by linarith
    have hlog : 0 ≤ Real.log n := Real.log_nonneg hn
    rw [Real.log_sqrt hn0, Real.sqrt_eq_rpow, ← Real.rpow_mul hn0,
      show 1 / (2 : ℝ) * -(2 * T) = -T by ring, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), one_mul]
    gcongr
    linarith
  refine (h1.trans h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with n hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  simp only [Function.comp_apply]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Real.log_sqrt hn0, Real.sqrt_eq_rpow, ← Real.rpow_mul hn0,
    show 1 / (2 : ℝ) * -α = -(α / 2) by ring]

/-- The constant coefficient of the amplitude array: `c_{00}(s) = e^{βs x₀₀} y₀₀`. -/
theorem ampCoeff_zero (β : ℝ) (x y : ℕ × ℕ → ℝ) (s : ℝ) :
    ampCoeff β x y (0, 0) s = Real.exp (β * s * x (0, 0)) * y (0, 0) := by
  unfold ampCoeff conv
  have hbox : box (0, 0) = {(0, 0)} := by
    ext a
    simp only [mem_box, Finset.mem_singleton, Nat.le_zero, Prod.ext_iff]
  rw [hbox, Finset.sum_singleton]
  have hE : expCoeff (dropConst x) (β * s) (0, 0) = 1 := by
    unfold expCoeff
    simp [convPow, delta]
  simp [psub, hE]

/-- The leading pole `p = uExp 0 = vExp 0`. -/
theorem uExp_zero (h₁ k₁ : ℕ) (p : ℝ) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) : uExp h₁ k₁ 0 = p := by
  unfold uExp; push_cast; rw [add_zero, hp₁]

theorem vExp_zero (h₂ k₂ : ℕ) (p : ℝ) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) : vExp h₂ k₂ 0 = p := by
  unfold vExp; push_cast; rw [add_zero, hp₂]

/-- The leading pole lies in `polesBelow` as soon as `p < 2T`. -/
theorem leading_pole_mem (h₁ h₂ k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (p T : ℝ)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (hT : p < 2 * T) :
    p ∈ polesBelow h₁ h₂ k₁ k₂ p T :=
  (mem_polesBelow_iff h₁ h₂ k₁ k₂ hk₁ hk₂ p T hp₁ hp₂ p).2
    ⟨hT, Or.inl ⟨0, uExp_zero h₁ k₁ p hp₁⟩⟩

/-- Every pole is at least the leading one. -/
theorem le_of_mem_polesBelow (h₁ h₂ k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (p T : ℝ)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (α : ℝ)
    (hα : α ∈ polesBelow h₁ h₂ k₁ k₂ p T) : p ≤ α := by
  obtain ⟨-, ⟨i, rfl⟩ | ⟨j, rfl⟩⟩ := (mem_polesBelow_iff h₁ h₂ k₁ k₂ hk₁ hk₂ p T hp₁ hp₂ α).1 hα
  · unfold uExp
    push_cast
    rw [← hp₁]
    have hk : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
    gcongr
    linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  · unfold vExp
    push_cast
    rw [← hp₂]
    have hk : (0 : ℝ) < k₂ := by exact_mod_cast hk₂
    gcongr
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

/-- The collision coefficient at the leading pole is `c_{00}/(k₁k₂)`. -/
theorem canonC_leading (h₁ h₂ k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (p : ℝ)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (c : ℕ → ℕ → ℝ → ℝ) :
    canonC h₁ h₂ k₁ k₂ c p = fun s => c 0 0 s / ((k₁ : ℝ) * k₂) := by
  rw [← uExp_zero h₁ k₁ p hp₁]
  exact canonC_collision h₁ h₂ k₁ k₂ hk₁ hk₂ c 0 0
    (by rw [uExp_zero h₁ k₁ p hp₁, vExp_zero h₂ k₂ p hp₂])

/-- **The leading log coefficient**: `A_p = y₀₀/(k₁k₂) · ∫₀^∞ s^{p−1} e^{−βs²} e^{βs x₀₀} ds`. -/
theorem leading_log_coeff (β : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (p : ℝ)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p) (x y : ℕ × ℕ → ℝ) :
    canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) p
      = y (0, 0) / ((k₁ : ℝ) * k₂)
        * logMoment β p 0 (fun s => Real.exp (β * s * x (0, 0))) := by
  unfold canonA
  rw [canonC_leading h₁ h₂ k₁ k₂ hk₁ hk₂ p hp₁ hp₂]
  unfold logMoment
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  beta_reduce
  rw [ampCoeff_zero]
  ring

end Laplace.Grammar
