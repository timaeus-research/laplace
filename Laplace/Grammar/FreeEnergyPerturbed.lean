/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.DivisibleWeight

/-!
# Free energy with divisible perturbations (grammar §4.2–4.3)

Combining unit 66 with the logarithm lemma of unit 61: for `ξ = a + u^k J̃` and `η = η₀ + u^k η̃`
with `η₀ > 0`,

  `−log Z(ξ, η) = (p/2) log n − m log log n + F₀ + o(1)`,

with `p` the minimal candidate exponent and `m + 1` its multiplicity. The perturbations affect only
the constant `F₀ = −log(η₀ C)`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- **Chart free energy with divisible perturbations.** -/
theorem boxIntegralXiEta_freeEnergy (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) (D : ℕ)
    (k h : Fin (D + 2) → ℕ) (hk : ∀ i, 0 < k i) (J η : (Fin (D + 2) → ℝ) → ℝ) (hJ : Continuous J)
    (hη : Continuous η) (η₀ : ℝ) (hη₀ : 0 < η₀) :
    ∃ (p : ℝ) (m : ℕ) (F₀ : ℝ), (∀ i, p ≤ finExp k h i) ∧
      m + 1 = (Finset.univ.filter fun i => finExp k h i = p).card ∧
      Tendsto (fun n : ℝ => -Real.log (boxIntegralXiEta β a b (Real.sqrt n) k h
          (fun u => (∏ i, u i ^ k i) * J u) (fun u => η₀ + (∏ i, u i ^ k i) * η u))
        - (p / 2 * Real.log n - m * Real.log (Real.log n))) atTop (𝓝 F₀) := by
  obtain ⟨p, m, C, hC, hmin, hcard, hE⟩ :=
    boxIntegralXiEta_isEquivalent β a b hβ hb D k h hk J η hJ hη η₀ hη₀.ne'
  refine ⟨p, m, -Real.log (η₀ * C), hmin, hcard, ?_⟩
  have := (tendsto_log_of_isEquivalent_powLog (mul_pos hη₀ hC) hE).neg
  refine this.congr fun n => ?_
  ring

end Laplace.Grammar
