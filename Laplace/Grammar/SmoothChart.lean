/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Taylor
import Laplace.Grammar.AllOrdersOneD

/-!
# The all-order 1D chart theorem for `C^R` data (grammar §4.2)

The hypotheses of `oneDChart_all_orders` (order-`R` Taylor remainders of `ξ, η` on `[0,b]` and a
Lipschitz bound for `ξ` at `0`) are derived here from `ContDiff ℝ R ξ` and `ContDiff ℝ R η`, with
Taylor data `taylorData f i = iteratedDeriv i f 0 / i!`. The result `oneDChart_all_orders_smooth`
has hypotheses only on the smoothness of the chart data. Zero `sorry`/`axiom`.
-/

open Real Finset MeasureTheory Set

namespace Laplace.Grammar

/-- The Taylor coefficients of `f` at `0`. -/
noncomputable def taylorData (f : ℝ → ℝ) (i : ℕ) : ℝ :=
  iteratedDeriv i f 0 / (i.factorial : ℝ)

/-- The Taylor polynomial of Mathlib evaluates to `∑_{i≤n} taylorData f i · u^i` on `[0,b]`. -/
theorem taylorWithinEval_eq_taylorData (f : ℝ → ℝ) (n : ℕ) (b : ℝ) (hb : 0 < b)
    (hf : ContDiff ℝ n f) (u : ℝ) :
    taylorWithinEval f n (Icc 0 b) 0 u = ∑ i ∈ range (n + 1), taylorData f i * u ^ i := by
  rw [taylor_within_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : (i : WithTop ℕ∞) ≤ n := by
    rw [Finset.mem_range] at hi
    exact_mod_cast Nat.lt_succ_iff.1 hi
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hb) ((hf.of_le hi').contDiffAt)
    (left_mem_Icc.2 hb.le)]
  unfold taylorData
  simp only [sub_zero, smul_eq_mul]
  ring

/-- **Taylor remainder on `[0,b]` from `C^{n+1}` regularity.** -/
theorem exists_taylor_remainder_bound (f : ℝ → ℝ) (n : ℕ) (b : ℝ) (hb : 0 < b)
    (hf : ContDiff ℝ (n + 1) f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u ∈ Icc (0 : ℝ) b,
      |f u - ∑ i ∈ range (n + 1), taylorData f i * u ^ i| ≤ K * u ^ (n + 1) := by
  have hcont : Continuous (iteratedDeriv (n + 1) f) :=
    hf.continuous_iteratedDeriv (n + 1) (by exact_mod_cast le_rfl)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) b) hcont.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (left_mem_Icc.2 hb.le))
  refine ⟨C / (n.factorial : ℝ), by positivity, fun u hu => ?_⟩
  have hfn : ContDiff ℝ ((n : WithTop ℕ∞) + 1) f := by exact_mod_cast hf
  have hbd : ∀ y ∈ Icc (0 : ℝ) b, ‖iteratedDerivWithin (n + 1) f (Icc 0 b) y‖ ≤ C := by
    intro y hy
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hb)
      (by exact_mod_cast hfn.contDiffAt) hy]
    exact hC y hy
  have hle : ContDiff ℝ n f := hf.of_le (by exact_mod_cast Nat.le_succ n)
  have := taylor_mean_remainder_bound hb.le (hfn.contDiffOn) hu hbd
  rw [Real.norm_eq_abs, taylorWithinEval_eq_taylorData f n b hb hle u, sub_zero] at this
  rw [div_mul_eq_mul_div]
  exact this

/-- The Lipschitz bound at `0` from `C^1` regularity. -/
theorem exists_lipschitz_bound (f : ℝ → ℝ) (b : ℝ) (hb : 0 < b) (hf : ContDiff ℝ 1 f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u ∈ Icc (0 : ℝ) b, |f u - f 0| ≤ L * u := by
  obtain ⟨K, hK0, hK⟩ := exists_taylor_remainder_bound f 0 b hb hf
  refine ⟨K, hK0, fun u hu => ?_⟩
  have := hK u hu
  simp only [zero_add, Finset.sum_range_one, pow_zero, mul_one, pow_one] at this
  unfold taylorData at this
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one] at this
  exact this

theorem taylorData_zero (f : ℝ → ℝ) : taylorData f 0 = f 0 := by
  simp [taylorData]

/-- **The all-order 1D chart theorem for `C^R` data.** For `ξ, η ∈ C^R(ℝ)` and `R ≥ 1`,
`∫₀^b u^h e^{-β(Nu^k)²} η(u) e^{β(Nu^k)ξ(u)} du = ∑_{j<R} c_j N^{-(p+j/k)} + O(N^{-(p+R/k)})` with
`c_j = jetCoeff β p k (chartJet β (taylorData ξ) (taylorData η) R) j`. -/
theorem oneDChart_all_orders_smooth (β b p : ℝ) (h k R : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk : 0 < k) (hp : ((h : ℝ) + 1) / k = p) (hR : 0 < R)
    (ξ η : ℝ → ℝ) (hξ : ContDiff ℝ R ξ) (hη : ContDiff ℝ R η) :
    ∃ K' : ℝ, ∀ N : ℝ, 1 ≤ N →
      |oneDScale β b N h k ξ η
          - ∑ j ∈ range R, jetCoeff β p k (chartJet β (taylorData ξ) (taylorData η) R) j
              * N ^ (-(p + (j : ℝ) / k))|
        ≤ K' * N ^ (-(p + (R : ℝ) / k)) := by
  obtain ⟨n, rfl⟩ : ∃ n, R = n + 1 := ⟨R - 1, by omega⟩
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_taylor_remainder_bound ξ n b hb hξ
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_taylor_remainder_bound η n b hb hη
  have h1 : (1 : WithTop ℕ∞) ≤ ((n + 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast Nat.succ_le_succ n.zero_le
  obtain ⟨L₁, hL₁0, hL₁⟩ := exists_lipschitz_bound ξ b hb (hξ.of_le h1)
  have hξT : ∀ u ∈ Icc (0 : ℝ) b,
      |ξ u - ∑ i ∈ range (n + 1), taylorData ξ i * u ^ i| ≤ max K₁ K₂ * u ^ (n + 1) := by
    intro u hu
    exact (hK₁ u hu).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hu.1 _))
  have hηT : ∀ u ∈ Icc (0 : ℝ) b,
      |η u - ∑ i ∈ range (n + 1), taylorData η i * u ^ i| ≤ max K₁ K₂ * u ^ (n + 1) := by
    intro u hu
    exact (hK₂ u hu).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hu.1 _))
  have hξL : ∀ u ∈ Icc (0 : ℝ) b, |ξ u - taylorData ξ 0| ≤ L₁ * u := by
    rw [taylorData_zero]; exact hL₁
  exact oneDChart_all_orders β b (max K₁ K₂) L₁ p h k (n + 1) hβ hb (le_max_of_le_left hK₁0) hL₁0
    hk hp hR (taylorData ξ) (taylorData η) ξ η hξ.continuous.measurable hη.continuous.measurable
    hξT hηT hξL

end Laplace.Grammar
