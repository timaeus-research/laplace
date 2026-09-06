/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TreeTerm

/-!
# Free energy of the population chart integral (grammar §4.2–4.3)

Taking logarithms in the multiplicity theorem gives the free-energy form familiar from singular
learning theory: if `Z(n) ~ C n^{-λ} (log n)^m` with `C > 0`, then

  `log Z(n) + λ log n − m log log n → log C`,

so the chart contribution to the population free energy `F_n = −log Z(n)` is
`(p/2) log n − m log log n − log C + o(1)`, with `p/2` half the minimal candidate exponent and
`m + 1` its multiplicity (`boxIntegralFin_freeEnergy`). Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- **Logarithm of a power-log equivalence**: `Z ~ C n^{-λ} (log n)^m` with `C > 0` implies
`log Z + λ log n − m log log n → log C`. -/
theorem tendsto_log_of_isEquivalent_powLog {Z : ℝ → ℝ} {C lam : ℝ} {m : ℕ} (hC : 0 < C)
    (hZ : Z ~[atTop] fun n : ℝ => C * (n ^ (-lam) * Real.log n ^ m)) :
    Tendsto (fun n : ℝ => Real.log (Z n) + lam * Real.log n - m * Real.log (Real.log n)) atTop
      (𝓝 (Real.log C)) := by
  set v : ℝ → ℝ := fun n => C * (n ^ (-lam) * Real.log n ^ m) with hv
  have hvpos : ∀ n : ℝ, 1 < n → 0 < v n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hlog := Real.log_pos hn
    simp only [hv]
    positivity
  have hvne : ∀ᶠ n in atTop, v n ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
    exact (hvpos n hn).ne'
  have hratio : Tendsto (Z / v) atTop (𝓝 1) := (isEquivalent_iff_tendsto_one hvne).1 hZ
  have hZne : ∀ᶠ n in atTop, Z n ≠ 0 := by
    filter_upwards [hratio.eventually (lt_mem_nhds (zero_lt_one' ℝ))] with n hn h0
    simp [Pi.div_apply, h0] at hn
  have hlogratio : Tendsto (fun n => Real.log (Z n / v n)) atTop (𝓝 0) := by
    have := hratio.log one_ne_zero
    rw [Real.log_one] at this
    exact this
  have hlogv : ∀ n : ℝ, 1 < n →
      Real.log (v n) = Real.log C - lam * Real.log n + m * Real.log (Real.log n) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hlog := Real.log_pos hn
    simp only [hv]
    rw [Real.log_mul hC.ne' (by positivity), Real.log_mul (Real.rpow_pos_of_pos hn0 _).ne'
      (pow_pos hlog m).ne', Real.log_rpow hn0, Real.log_pow]
    ring
  have h := hlogratio.add_const (Real.log C)
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), hZne] with n hn hZn
  rw [Real.log_div hZn (hvpos n hn).ne', hlogv n hn]
  ring

/-- **Population chart free energy**: for any exponents on `Fin (D+2)`, with `p` the minimal
candidate exponent and `m + 1` its multiplicity,
`−log ∫_{(0,b]^{D+2}} u^h f(√n u^k) du = (p/2) log n − m log log n + F₀ + o(1)`. -/
theorem boxIntegralFin_freeEnergy (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) (D : ℕ)
    (k h : Fin (D + 2) → ℕ) (hk : ∀ i, 0 < k i) :
    ∃ (p : ℝ) (m : ℕ) (F₀ : ℝ), (∀ i, p ≤ finExp k h i) ∧
      m + 1 = (Finset.univ.filter fun i => finExp k h i = p).card ∧
      Tendsto (fun n : ℝ => -Real.log (boxIntegralFin β a b (Real.sqrt n) k h)
        - (p / 2 * Real.log n - m * Real.log (Real.log n))) atTop (𝓝 F₀) := by
  obtain ⟨p, m, C, hC, hmin, hcard, hE⟩ := boxIntegralFin_isEquivalent_general β a b hβ hb D k h hk
  refine ⟨p, m, -Real.log C, hmin, hcard, ?_⟩
  have := (tendsto_log_of_isEquivalent_powLog hC hE).neg
  refine this.congr fun n => ?_
  ring

end Laplace.Grammar
