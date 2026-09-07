/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TwoDCutoffAnalytic

/-!
# Commuting Taylor projections: the general-`d` algebraic skeleton (grammar §4.2)

For a sequence of linear "Taylor projection" operators `P n` on a module, the recursion
`R 0 = id, R (n+1) = (id − P n) R n`, `F 0 = 0, F (n+1) = F n + P n R n` gives the exact
decomposition `id = F n + R n` (`faceOp_add_remOp`) with no commutation or idempotence
hypotheses (Astra #6(d)). For `n = 2` this is the rectangular face-jet decomposition
`F 2 = P₀ + P₁ − P₁P₀`, `R 2 = id − P₀ − P₁ + P₁P₀` (`faceOp_two`, `remOp_two`).

The analytic instantiation is by coefficient truncation: on coefficient arrays indexed by
multi-indices `ℕ → ℕ`, `truncProj ℓ M` keeps the coefficients with `α ℓ < M`; these are linear,
idempotent and commute, and the remainder `R d` of the first `d` coordinates is the tail indicator
`α ℓ ≥ M ℓ` for all `ℓ < d` (`remOp_truncProj_apply`). Zero `sorry`/`axiom`.
-/

namespace Laplace.Grammar

section Abstract

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The remainder operators `R 0 = id`, `R (n+1) = (id − P n) ∘ R n`. -/
noncomputable def remOp (P : ℕ → E →ₗ[ℝ] E) : ℕ → E →ₗ[ℝ] E
  | 0 => LinearMap.id
  | n + 1 => (LinearMap.id - P n) ∘ₗ remOp P n

/-- The face operators `F 0 = 0`, `F (n+1) = F n + P n ∘ R n`. -/
noncomputable def faceOp (P : ℕ → E →ₗ[ℝ] E) : ℕ → E →ₗ[ℝ] E
  | 0 => 0
  | n + 1 => faceOp P n + P n ∘ₗ remOp P n

/-- **The exact decomposition** `id = F n + R n`. -/
theorem faceOp_add_remOp (P : ℕ → E →ₗ[ℝ] E) (n : ℕ) :
    faceOp P n + remOp P n = LinearMap.id := by
  induction n with
  | zero => simp [faceOp, remOp]
  | succ n ih =>
    simp only [faceOp, remOp]
    rw [LinearMap.sub_comp, LinearMap.id_comp]
    calc faceOp P n + P n ∘ₗ remOp P n + (remOp P n - P n ∘ₗ remOp P n)
        = faceOp P n + remOp P n := by abel
      _ = _ := ih

theorem remOp_one (P : ℕ → E →ₗ[ℝ] E) : remOp P 1 = LinearMap.id - P 0 := by
  simp [remOp]

/-- The rectangular remainder `R 2 = id − P₀ − P₁ + P₁ ∘ P₀`. -/
theorem remOp_two (P : ℕ → E →ₗ[ℝ] E) :
    remOp P 2 = LinearMap.id - P 0 - P 1 + P 1 ∘ₗ P 0 := by
  simp only [remOp, LinearMap.comp_id, LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp]
  abel

/-- The rectangular face operator `F 2 = P₀ + P₁ − P₁ ∘ P₀`. -/
theorem faceOp_two (P : ℕ → E →ₗ[ℝ] E) : faceOp P 2 = P 0 + P 1 - P 1 ∘ₗ P 0 := by
  simp only [faceOp, remOp, LinearMap.comp_id, LinearMap.comp_sub, zero_add]
  abel

end Abstract

section Truncation

/-- Coefficient truncation in coordinate `ℓ` at order `M`: keeps the coefficients with `α ℓ < M`. -/
noncomputable def truncProj (ℓ M : ℕ) : ((ℕ → ℕ) → ℝ) →ₗ[ℝ] ((ℕ → ℕ) → ℝ) where
  toFun c := fun α => if α ℓ < M then c α else 0
  map_add' := by
    intro c c'
    funext α
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' := by
    intro r c
    funext α
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem truncProj_apply (ℓ M : ℕ) (c : (ℕ → ℕ) → ℝ) (α : ℕ → ℕ) :
    truncProj ℓ M c α = if α ℓ < M then c α else 0 := rfl

theorem truncProj_idem (ℓ M : ℕ) : truncProj ℓ M ∘ₗ truncProj ℓ M = truncProj ℓ M := by
  ext c α
  simp only [LinearMap.comp_apply, truncProj_apply]
  split_ifs <;> rfl

theorem truncProj_comm (ℓ M ℓ' M' : ℕ) :
    truncProj ℓ M ∘ₗ truncProj ℓ' M' = truncProj ℓ' M' ∘ₗ truncProj ℓ M := by
  ext c α
  simp only [LinearMap.comp_apply, truncProj_apply]
  split_ifs <;> rfl

/-- **The remainder of the first `d` coordinate truncations is the tail indicator**
`α ℓ ≥ M ℓ` for all `ℓ < d`. -/
theorem remOp_truncProj_apply (M : ℕ → ℕ) (d : ℕ) (c : (ℕ → ℕ) → ℝ) (α : ℕ → ℕ) :
    remOp (fun ℓ => truncProj ℓ (M ℓ)) d c α = if ∀ ℓ < d, M ℓ ≤ α ℓ then c α else 0 := by
  induction d with
  | zero => simp [remOp]
  | succ d ih =>
    simp only [remOp, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply,
      truncProj_apply, ih]
    by_cases h1 : ∀ ℓ < d, M ℓ ≤ α ℓ
    · by_cases h2 : α d < M d
      · have h3 : ¬ ∀ ℓ < d + 1, M ℓ ≤ α ℓ := fun h => absurd (h d (Nat.lt_succ_self d)) (by omega)
        rw [if_pos h1, if_pos h2, if_neg h3]
        ring
      · have h3 : ∀ ℓ < d + 1, M ℓ ≤ α ℓ := by
          intro ℓ hℓ
          rcases Nat.lt_succ_iff_lt_or_eq.1 hℓ with hℓ | hℓ
          · exact h1 ℓ hℓ
          · subst hℓ; omega
        rw [if_pos h1, if_neg h2, if_pos h3]
        ring
    · have h3 : ¬ ∀ ℓ < d + 1, M ℓ ≤ α ℓ := fun h => h1 fun ℓ hℓ => h ℓ (Nat.lt_succ_of_lt hℓ)
      rw [if_neg h1, if_neg h3]
      split_ifs <;> simp

end Truncation

end Laplace.Grammar
