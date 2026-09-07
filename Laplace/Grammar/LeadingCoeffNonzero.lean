/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.KernelJetTransfer

/-!
# The leading coefficient is positive for a nonnegative face amplitude that is not identically
zero (grammar §4.2)

If `η(0,·) ≥ 0` on the closed noncritical box and `η(0, v₁) ≠ 0` at some point of the closed box,
continuity produces an interior point where `η(0,·) > 0`, so the leading coefficient is positive
(`blockCoeff_pos_of_nonneg_ne_zero`) and the asymptotic equivalence holds
(`blockStateIntegral_isEquivalent_of_ne_zero`). This is the sharp form of the positivity hypothesis
recommended in the third Astra consult (nonnegativity on the minimal face, not on the whole box).
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology Asymptotics

namespace Laplace.Grammar

/-- A continuous function on the closed box, positive at a point of the closed box, is positive at
an interior point. -/
theorem exists_interior_pos {d' : ℕ} (b : ℝ) (hb : 0 < b) (e : (Fin d' → ℝ) → ℝ)
    (hec : Continuous e) (v₁ : Fin d' → ℝ) (hv₁ : ∀ i, 0 ≤ v₁ i ∧ v₁ i ≤ b) (hpos : 0 < e v₁) :
    ∃ v₀ : Fin d' → ℝ, (∀ i, 0 < v₀ i ∧ v₀ i < b) ∧ 0 < e v₀ := by
  have hcl : closure (Set.pi univ fun _ : Fin d' => Ioo (0 : ℝ) b)
      = Set.pi univ fun _ : Fin d' => Icc (0 : ℝ) b := by
    rw [closure_pi_set]
    congr 1
    funext _
    exact closure_Ioo hb.ne
  have hmem : v₁ ∈ closure (Set.pi univ fun _ : Fin d' => Ioo (0 : ℝ) b) := by
    rw [hcl, Set.mem_univ_pi]; exact hv₁
  have hopen : IsOpen {v : Fin d' → ℝ | 0 < e v} := isOpen_lt continuous_const hec
  obtain ⟨v₀, hv₀U, hv₀box⟩ := mem_closure_iff.1 hmem _ hopen hpos
  rw [Set.mem_univ_pi] at hv₀box
  exact ⟨v₀, hv₀box, hv₀U⟩

/-- **Positivity of the leading coefficient** for `η(0,·) ≥ 0`, not identically zero. -/
theorem blockCoeff_pos_of_nonneg_ne_zero (β b p : ℝ) (hβ : 0 < β) (hb : 0 < b) {d₀ d' : ℕ}
    (k h : Fin (d₀ + 1) → ℕ) (hk : ∀ j, 0 < k j) (hp : ∀ j, finExp k h j = p)
    (k' h' : Fin d' → ℕ) (hk' : ∀ i, 0 < k' i) (hq : ∀ i, p < ((h' i : ℝ) + 1) / k' i)
    (ξ η : (Fin (d₀ + 1) → ℝ) → (Fin d' → ℝ) → ℝ)
    (hξc : Continuous fun x : (Fin (d₀ + 1) → ℝ) × (Fin d' → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : (Fin (d₀ + 1) → ℝ) × (Fin d' → ℝ) => η x.1 x.2)
    (henn : ∀ v : Fin d' → ℝ, (∀ i, 0 ≤ v i ∧ v i ≤ b) → 0 ≤ η 0 v)
    (v₁ : Fin d' → ℝ) (hv₁ : ∀ i, 0 ≤ v₁ i ∧ v₁ i ≤ b) (hne : η 0 v₁ ≠ 0) :
    0 < blockCoeff β b p k k' h' ξ η := by
  have hp0 : 0 < p := by rw [← hp 0]; exact finExp_pos k h hk 0
  have hη0c : Continuous fun v : Fin d' → ℝ => η 0 v :=
    hηc.comp (continuous_const.prodMk continuous_id)
  have hpos₁ : 0 < η 0 v₁ := lt_of_le_of_ne (henn v₁ hv₁) hne.symm
  obtain ⟨v₀, hv₀, hpos₀⟩ := exists_interior_pos b hb (fun v => η 0 v) hη0c v₁ hv₁ hpos₁
  exact integral_blockDivisorDensity_pos_of_nonneg β b p hβ hp0 (toNatFun k 1) (toNatFun_pos k hk)
    d₀ k' h' hk' hq (fun v => ξ 0 v) (fun v => η 0 v)
    (hξc.comp (continuous_const.prodMk continuous_id)) hη0c
    (fun v hv => henn v fun i => ⟨(hv i).1.le, (hv i).2⟩) v₀ hv₀ hpos₀

/-- **Asymptotic equivalence** for `η(0,·) ≥ 0` on the face, not identically zero. -/
theorem blockStateIntegral_isEquivalent_of_ne_zero (β b p : ℝ) (hβ : 0 < β) (hb : 0 < b)
    {d₀ d' : ℕ} (k h : Fin (d₀ + 1) → ℕ) (hk : ∀ j, 0 < k j) (hp : ∀ j, finExp k h j = p)
    (k' h' : Fin d' → ℕ) (hk' : ∀ i, 0 < k' i) (hq : ∀ i, p < ((h' i : ℝ) + 1) / k' i)
    (ξ η : (Fin (d₀ + 1) → ℝ) → (Fin d' → ℝ) → ℝ)
    (hξc : Continuous fun x : (Fin (d₀ + 1) → ℝ) × (Fin d' → ℝ) => ξ x.1 x.2)
    (hηc : Continuous fun x : (Fin (d₀ + 1) → ℝ) × (Fin d' → ℝ) => η x.1 x.2)
    (henn : ∀ v : Fin d' → ℝ, (∀ i, 0 ≤ v i ∧ v i ≤ b) → 0 ≤ η 0 v)
    (v₁ : Fin d' → ℝ) (hv₁ : ∀ i, 0 ≤ v₁ i ∧ v₁ i ≤ b) (hne : η 0 v₁ ≠ 0) :
    (fun N : ℝ => blockStateIntegral β b N k h k' h' ξ η) ~[atTop]
      fun N : ℝ => blockCoeff β b p k k' h' ξ η * (N ^ (-p) * Real.log N ^ d₀) :=
  blockStateIntegral_isEquivalent_of_ne β b p hβ hb k h hk hp k' h' hk' hq ξ η hξc hηc
    (blockCoeff_pos_of_nonneg_ne_zero β b p hβ hb k h hk hp k' h' hk' hq ξ η hξc hηc henn v₁ hv₁
      hne).ne'

end Laplace.Grammar
