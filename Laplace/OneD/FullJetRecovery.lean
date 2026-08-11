/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.SmoothRecovery

/-!
# Full-jet packaging

Stage C6, closing the one-dimensional Theorem 3.1 statement shape:
the finite-order recovery's coefficient conclusion converted to
iterated derivatives (`smooth_jet_recovery_iteratedDeriv`), and the
all-orders corollary for smooth losses
(`smooth_full_jet_recovery`) — moment data vanishing at every
coefficient-sensitive rate determines every derivative of order at
least two at the minimum, i.e. the full Taylor jet modulo the
constant and the (vanishing) gradient.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.OneD

open Laplace

/-- **Finite-order recovery in derivative form**: under the
hypotheses of `smooth_jet_recovery`, the iterated derivatives of the
two losses agree at every order `2 ≤ k ≤ R + 2`. -/
theorem smooth_jet_recovery_iteratedDeriv
    {L₁ L₂ : ℝ → ℝ} {ρ₁ κ₁ δ₁ ρ₂ κ₂ δ₂ : ℝ} {R : ℕ}
    (h1 : AdmissiblePotential L₁ ρ₁ κ₁ δ₁)
    (h2 : AdmissiblePotential L₂ ρ₂ κ₂ δ₂)
    (hs1 : ContDiff ℝ (R + 2) L₁) (hs2 : ContDiff ℝ (R + 2) L₂)
    (hdata : ∀ r : ℕ, r ≤ R → Tendsto (fun q : ℝ ↦
      ((∫ x : ℝ, x ^ (2 + r) * Real.exp (-((q ^ 2)⁻¹ * L₁ x))) /
          (∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * L₁ x))) -
        (∫ x : ℝ, x ^ (2 + r) * Real.exp (-((q ^ 2)⁻¹ * L₂ x))) /
          (∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * L₂ x)))) /
        q ^ (2 + 2 * r)) (𝓝[>] 0) (𝓝 0)) :
    ∀ k : ℕ, 2 ≤ k → k ≤ R + 2 →
      iteratedDeriv k L₁ 0 = iteratedDeriv k L₂ 0 := by
  obtain ⟨hbase, hcoeff⟩ := smooth_jet_recovery h1 h2 hs1 hs2 hdata
  intro k hk2 hkR
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · -- k = 2: from the base coefficient.
    have hk : k = 2 := by omega
    subst hk
    have h := hbase
    rw [taylorBase, taylorBase] at h
    linarith [h]
  · -- k ≥ 3: from the higher coefficients.
    have hiR : k - 3 < R := by omega
    have := congrFun hcoeff ⟨k - 3, by omega⟩
    rw [taylorCoeff, taylorCoeff] at this
    have hfac : ((Nat.factorial (2 + (k - 3 + 1)) : ℝ)) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos _).ne'
    have hexp : 2 + (k - 3 + 1) = k := by omega
    rw [hexp] at this
    field_simp at this
    exact this

/-- **The all-orders recovery** (stage C6, the note's Theorem 3.1
statement shape in one dimension): two smooth admissible losses whose
normalized moment data vanishes at every coefficient-sensitive rate
have the same derivatives of every order `k ≥ 2` at the minimum —
the full Taylor jet, modulo the constant and the vanishing
gradient. -/
theorem smooth_full_jet_recovery
    {L₁ L₂ : ℝ → ℝ} {ρ₁ κ₁ δ₁ ρ₂ κ₂ δ₂ : ℝ}
    (h1 : AdmissiblePotential L₁ ρ₁ κ₁ δ₁)
    (h2 : AdmissiblePotential L₂ ρ₂ κ₂ δ₂)
    (hs1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L₁)
    (hs2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L₂)
    (hdata : ∀ r : ℕ, Tendsto (fun q : ℝ ↦
      ((∫ x : ℝ, x ^ (2 + r) * Real.exp (-((q ^ 2)⁻¹ * L₁ x))) /
          (∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * L₁ x))) -
        (∫ x : ℝ, x ^ (2 + r) * Real.exp (-((q ^ 2)⁻¹ * L₂ x))) /
          (∫ x : ℝ, Real.exp (-((q ^ 2)⁻¹ * L₂ x)))) /
        q ^ (2 + 2 * r)) (𝓝[>] 0) (𝓝 0)) :
    ∀ k : ℕ, 2 ≤ k → iteratedDeriv k L₁ 0 = iteratedDeriv k L₂ 0 := by
  intro k hk2
  refine smooth_jet_recovery_iteratedDeriv (R := k - 2) h1 h2
    (contDiff_infty.mp hs1 (k - 2 + 2))
    (contDiff_infty.mp hs2 (k - 2 + 2))
    (fun r _ ↦ hdata r) k hk2 (by omega)

end Laplace.OneD
