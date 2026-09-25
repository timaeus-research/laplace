/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.CompactCoverCramer

/-!
# The asymptotic form of the compact-cover Cramér bound

The compact-cover bound `P(R̄_n ∈ F) ≤ N e^{−nα}` (`compact_cover_chernoff`) has the exponential
rate `α` up to a constant prefactor. Absorbing the prefactor into an arbitrarily small loss of rate:

* **root form** — for every `ε > 0` and all large `n`, `P(R̄_n ∈ F) ≤ e^{−n(α − ε)}`
  (`eventually_measureReal_empMean_le`, `eventually_measureReal_empMean_le'` as a filter statement);
* **log form** — whenever the probability is positive, `(1/n) log P(R̄_n ∈ F) ≤ −(α − ε)` for all
  large `n` (`eventually_log_measureReal_empMean_div_le`), i.e. `limsup (1/n) log P(R̄_n ∈ F) ≤ −α`
  in the extended sense (the real logarithm of a zero probability is not `−∞`, so the statement is
  guarded by positivity rather than phrased through `Real.log 0`).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

variable {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι]

section

variable (ν : Measure X) [IsProbabilityMeasure ν] {R : ι → X → ℝ} (hR : ∀ i, Bdd (R i))
include hR

/-- **The asymptotic upper bound, root form**: `P(R̄_n ∈ F) ≤ e^{−n(α − ε)}` for all large `n`. -/
theorem eventually_measureReal_empMean_le {F : Set (ι → ℝ)} (hF : IsCompact F) {α : ℝ}
    (hwit : ∀ x ∈ F, ∃ θ : ι → ℝ, α < ∑ i, θ i * x i - featCgf ν R θ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → 0 < n →
      (Measure.pi fun _ : Fin n ↦ ν).real {x | empMean R n x ∈ F} ≤
        Real.exp (-(n * (α - ε))) := by
  obtain ⟨N, hN⟩ := compact_cover_chernoff ν hR hF hwit
  refine ⟨⌈Real.log N / ε⌉₊, fun n hn hn0 ↦ ?_⟩
  have hNe : (N : ℝ) ≤ Real.exp (n * ε) := by
    rcases Nat.eq_zero_or_pos N with h0 | hNpos
    · rw [h0, Nat.cast_zero]
      exact (Real.exp_pos _).le
    · have hNpos' : (0 : ℝ) < N := by exact_mod_cast hNpos
      rw [← Real.log_le_iff_le_exp hNpos']
      have h1 : Real.log N / ε ≤ n := Nat.ceil_le.1 hn
      rwa [div_le_iff₀ hε] at h1
  calc (Measure.pi fun _ : Fin n ↦ ν).real {x | empMean R n x ∈ F}
      ≤ N * Real.exp (-(n * α)) := hN n hn0
    _ ≤ Real.exp (n * ε) * Real.exp (-(n * α)) :=
        mul_le_mul_of_nonneg_right hNe (Real.exp_pos _).le
    _ = Real.exp (-(n * (α - ε))) := by rw [← Real.exp_add]; congr 1; ring

/-- The root form as a filter statement. -/
theorem eventually_measureReal_empMean_le' {F : Set (ι → ℝ)} (hF : IsCompact F) {α : ℝ}
    (hwit : ∀ x ∈ F, ∃ θ : ι → ℝ, α < ∑ i, θ i * x i - featCgf ν R θ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (Measure.pi fun _ : Fin n ↦ ν).real {x | empMean R n x ∈ F} ≤
      Real.exp (-(n * (α - ε))) := by
  obtain ⟨N₀, hN₀⟩ := eventually_measureReal_empMean_le ν hR hF hwit hε
  exact eventually_atTop.2 ⟨max N₀ 1, fun n hn ↦
    hN₀ n (le_of_max_le_left hn) (lt_of_lt_of_le one_pos (le_of_max_le_right hn))⟩

/-- **The asymptotic upper bound, log form**: `(1/n) log P(R̄_n ∈ F) ≤ −(α − ε)` for all large `n`
with positive probability. -/
theorem eventually_log_measureReal_empMean_div_le {F : Set (ι → ℝ)} (hF : IsCompact F) {α : ℝ}
    (hwit : ∀ x ∈ F, ∃ θ : ι → ℝ, α < ∑ i, θ i * x i - featCgf ν R θ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → 0 < n →
      0 < (Measure.pi fun _ : Fin n ↦ ν).real {x | empMean R n x ∈ F} →
      Real.log ((Measure.pi fun _ : Fin n ↦ ν).real {x | empMean R n x ∈ F}) / n ≤ -(α - ε) := by
  obtain ⟨N₀, hN₀⟩ := eventually_measureReal_empMean_le ν hR hF hwit hε
  refine ⟨N₀, fun n hn hn0 hpos ↦ ?_⟩
  have h := Real.log_le_log hpos (hN₀ n hn hn0)
  rw [Real.log_exp] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [div_le_iff₀ hn']
  linarith

end

end Laplace.Multi
