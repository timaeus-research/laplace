/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CandidateSupport

/-!
# Permutation and append algebra of monomial lists (Stage 4a)

Unit 241 (Taylor-tree programme, Stage 4 — analytic data by coefficient families; Astra #28). The
coefficient functionals of Stage 3 (`coeffTerm`) depend on a monomial list only through the
multiset of its `(exponent, coefficient)` pairs, so they are invariant under permutation and
additive under `++`. The list product distributes over `++` (exactly on the left, up to permutation
on the right), and the key quantitative fact is the **power-difference estimate**: for
`J' = J ++ Δ`,
```
pow (J ++ Δ) p ~ pow J p ++ R_p,   ‖R_p‖₁ ≤ p ‖Δ‖₁ (‖J‖₁ + ‖Δ‖₁)^{p-1}
```
(`pow_append_perm`), the list form of `mass(x^p − y^p) ≤ p B^{p-1} mass(x − y)`. These are the tools
for the coefficient-stability gate of unit 242. No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology
open scoped List

namespace Laplace.Grammar

namespace MonoRep

variable {d : ℕ}

theorem l1_perm {P Q : MonoRep d} (h : P.Perm Q) : l1 P = l1 Q := (h.map _).sum_eq

theorem eval_perm {P Q : MonoRep d} (h : P.Perm Q) (u : Fin d → ℝ) : eval P u = eval Q u :=
  (h.map _).sum_eq

theorem mul_append_left (P Q R : MonoRep d) : mul (P ++ Q) R = mul P R ++ mul Q R :=
  List.flatMap_append

theorem mul_append_right_perm (P Q R : MonoRep d) : (mul P (Q ++ R)).Perm (mul P Q ++ mul P R) := by
  induction P with
  | nil => simp [mul]
  | cons s P ih =>
    simp only [mul, List.flatMap_cons, List.map_append] at ih ⊢
    refine (ih.append_left _).trans ?_
    rw [List.append_assoc, List.append_assoc]
    exact (List.perm_append_comm_assoc _ _ _).append_left _

theorem mul_perm_left {P P' : MonoRep d} (h : P.Perm P') (Q : MonoRep d) :
    (mul P Q).Perm (mul P' Q) := h.flatMap_right _

theorem mul_perm_right (P : MonoRep d) {Q Q' : MonoRep d} (h : Q.Perm Q') :
    (mul P Q).Perm (mul P Q') := List.Perm.flatMap_left P fun _ _ => h.map _

theorem pow_perm {P P' : MonoRep d} (h : P.Perm P') : ∀ p : ℕ, (pow P p).Perm (pow P' p)
  | 0 => List.Perm.refl _
  | p + 1 => (mul_perm_left h _).trans (mul_perm_right P' (pow_perm h p))

theorem l1_pow_append_le (J Δ : MonoRep d) (p : ℕ) :
    l1 (pow (J ++ Δ) p) ≤ (l1 J + l1 Δ) ^ p := by
  rw [← l1_append]; exact l1_pow_le _ _

/-- **Power-difference estimate**: `pow (J ++ Δ) p ~ pow J p ++ R` with
`‖R‖₁ ≤ p ‖Δ‖₁ (‖J‖₁ + ‖Δ‖₁)^{p-1}`. -/
theorem pow_append_perm (J Δ : MonoRep d) :
    ∀ p : ℕ, ∃ R : MonoRep d, (pow (J ++ Δ) p).Perm (pow J p ++ R) ∧
      l1 R ≤ p * l1 Δ * (l1 J + l1 Δ) ^ (p - 1)
  | 0 => ⟨[], by simp [pow], by simp⟩
  | p + 1 => by
    obtain ⟨R, hR, hl⟩ := pow_append_perm J Δ p
    have hB : 0 ≤ l1 J := l1_nonneg J
    have hδ : 0 ≤ l1 Δ := l1_nonneg Δ
    refine ⟨mul J R ++ mul Δ (pow (J ++ Δ) p), ?_, ?_⟩
    · calc pow (J ++ Δ) (p + 1) = mul J (pow (J ++ Δ) p) ++ mul Δ (pow (J ++ Δ) p) := by
            rw [pow, mul_append_left]
        _ ~ mul J (pow J p ++ R) ++ mul Δ (pow (J ++ Δ) p) := (mul_perm_right J hR).append_right _
        _ ~ (mul J (pow J p) ++ mul J R) ++ mul Δ (pow (J ++ Δ) p) :=
            (mul_append_right_perm J _ R).append_right _
        _ = pow J (p + 1) ++ (mul J R ++ mul Δ (pow (J ++ Δ) p)) := by
            rw [List.append_assoc]; rfl
    · rw [l1_append, l1_mul, l1_mul]
      have h1 := l1_pow_append_le J Δ p
      have hp : (p : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ (p - 1) * l1 J ≤
          (p : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ p := by
        rcases p with _ | p
        · simp
        · rw [Nat.add_sub_cancel]
          calc ((p + 1 : ℕ) : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ p * l1 J
              ≤ ((p + 1 : ℕ) : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ p * (l1 J + l1 Δ) :=
                mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            _ = _ := by ring
      calc l1 J * l1 R + l1 Δ * l1 (pow (J ++ Δ) p)
          ≤ l1 J * ((p : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ (p - 1)) + l1 Δ * (l1 J + l1 Δ) ^ p :=
            add_le_add (mul_le_mul_of_nonneg_left hl hB) (mul_le_mul_of_nonneg_left h1 hδ)
        _ ≤ (p : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ p + l1 Δ * (l1 J + l1 Δ) ^ p := by
            refine add_le_add ?_ le_rfl
            calc l1 J * ((p : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ (p - 1))
                = (p : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ (p - 1) * l1 J := by ring
              _ ≤ _ := hp
        _ = ((p + 1 : ℕ) : ℝ) * l1 Δ * (l1 J + l1 Δ) ^ (p + 1 - 1) := by
            rw [Nat.add_sub_cancel]; push_cast; ring

end MonoRep

open MonoRep

/-! ### Linearity of the coefficient terms -/

theorem coeffTerm_append (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ) (j : ℕ)
    (P Q : MonoRep (n + 1)) :
    coeffTerm n h k β a p μ j (P ++ Q) =
      coeffTerm n h k β a p μ j P + coeffTerm n h k β a p μ j Q := by
  unfold coeffTerm
  rw [List.map_append, List.sum_append, mul_add]

theorem coeffTerm_perm (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ) (j : ℕ)
    {P Q : MonoRep (n + 1)} (hPQ : P.Perm Q) :
    coeffTerm n h k β a p μ j P = coeffTerm n h k β a p μ j Q := by
  unfold coeffTerm
  rw [(hPQ.map _).sum_eq]

end Laplace.Grammar
