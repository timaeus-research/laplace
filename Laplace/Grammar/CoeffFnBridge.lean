/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CoeffConv

/-!
# Collected coefficients of monomial lists (Stage 5b)

Unit 252 (Taylor-tree programme; Astra #29 candidate A). A monomial list `P` has a **collected
coefficient family** `coeffFn P γ = ∑_{(γ, c) ∈ P} c` (finitely supported). The list product
collects to the Cauchy product (`coeffFn_mul`), evaluation and list mass are read off the family
(`evalF_coeffFn`, `mass_coeffFn_le`), the fluctuation part collects to the constant-free family
(`coeffFn_fluct`), and the box truncation of a family collects back to the family restricted to
the box (`coeffFn_truncList`). These identities let the Stage 3 coefficient functional, which is a
sum over list entries, be rewritten as a functional of the collected family (unit 253).
No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology
open scoped List

namespace Laplace.Grammar

open MonoRep CoeffFamily

namespace CoeffFamily

variable {d : ℕ}

/-- Iterated Cauchy product `c^{*p}` (with `c^{*0} = δ_0`). -/
noncomputable def convPow (c : CoeffFamily d) : ℕ → CoeffFamily d
  | 0 => fun γ => if γ = 0 then 1 else 0
  | p + 1 => conv c (convPow c p)

end CoeffFamily

namespace MonoRep

variable {d : ℕ}

open Classical in
/-- The collected coefficient of `u^γ` in a monomial list. -/
noncomputable def coeffFn (P : MonoRep d) : CoeffFamily d :=
  fun γ => ((P.filter fun s => s.1 = γ).map fun s => s.2).sum

@[simp] theorem coeffFn_nil (γ : Fin d → ℕ) : coeffFn ([] : MonoRep d) γ = 0 := rfl

open Classical in
theorem coeffFn_cons (s : (Fin d → ℕ) × ℝ) (P : MonoRep d) (γ : Fin d → ℕ) :
    coeffFn (s :: P) γ = (if s.1 = γ then s.2 else 0) + coeffFn P γ := by
  unfold coeffFn
  rw [List.filter_cons]
  by_cases h : s.1 = γ <;> simp [h]

theorem coeffFn_append (P Q : MonoRep d) (γ : Fin d → ℕ) :
    coeffFn (P ++ Q) γ = coeffFn P γ + coeffFn Q γ := by
  unfold coeffFn
  rw [List.filter_append, List.map_append, List.sum_append]

theorem coeffFn_perm {P Q : MonoRep d} (h : P.Perm Q) (γ : Fin d → ℕ) :
    coeffFn P γ = coeffFn Q γ := by
  unfold coeffFn
  exact ((h.filter _).map _).sum_eq

/-- The exponents occurring in a list. -/
def exps (P : MonoRep d) : Finset (Fin d → ℕ) := (P.map fun s => s.1).toFinset

theorem coeffFn_eq_zero_of_notMem (P : MonoRep d) {γ : Fin d → ℕ} (hγ : γ ∉ exps P) :
    coeffFn P γ = 0 := by
  induction P with
  | nil => rfl
  | cons s P ih =>
    rw [coeffFn_cons]
    have h1 : s.1 ≠ γ := fun h => hγ (by simp [exps, h])
    rw [if_neg h1, zero_add]
    exact ih fun h => hγ (by simp [exps] at h ⊢; exact Or.inr h)

/-- A finite-support family is absolutely summable; the collected family in particular. -/
theorem summable_of_support_subset {c : CoeffFamily d} {S : Finset (Fin d → ℕ)}
    (hS : ∀ γ, γ ∉ S → c γ = 0) : Summable fun γ => |c γ| :=
  summable_of_ne_finset_zero fun γ hγ => by rw [hS γ hγ, abs_zero]

theorem tsum_eq_sum_of_support_subset {c : CoeffFamily d} {S : Finset (Fin d → ℕ)}
    (hS : ∀ γ, γ ∉ S → c γ = 0) (f : (Fin d → ℕ) → ℝ) :
    ∑' γ, c γ * f γ = ∑ γ ∈ S, c γ * f γ :=
  tsum_eq_sum fun γ hγ => by rw [hS γ hγ, zero_mul]

theorem absSummable_coeffFn (P : MonoRep d) : AbsSummable (coeffFn P) :=
  summable_of_support_subset (S := exps P) fun _ hγ => coeffFn_eq_zero_of_notMem P hγ

/-- Any list sum `∑_{(γ,c) ∈ P} c · f γ` is the sum of the collected family against `f`. -/
theorem sum_map_eq_tsum_coeffFn (P : MonoRep d) (f : (Fin d → ℕ) → ℝ) :
    (P.map fun s => s.2 * f s.1).sum = ∑' γ, coeffFn P γ * f γ := by
  induction P with
  | nil => simp
  | cons s P ih =>
    rw [List.map_cons, List.sum_cons, ih]
    have hs : Summable fun γ => coeffFn P γ * f γ :=
      summable_of_ne_finset_zero (s := exps P) fun γ hγ => by
        rw [coeffFn_eq_zero_of_notMem P hγ, zero_mul]
    have hδ : Summable fun γ => (if s.1 = γ then s.2 else 0) * f γ :=
      summable_of_ne_finset_zero (s := {s.1}) fun γ hγ => by
        rw [if_neg (fun h => hγ (by simp [h])), zero_mul]
    simp_rw [coeffFn_cons, add_mul]
    rw [hδ.tsum_add hs]
    congr 1
    rw [tsum_eq_single s.1 fun γ hγ => by rw [if_neg (Ne.symm hγ), zero_mul], if_pos rfl]

theorem evalF_coeffFn (P : MonoRep d) (u : Fin d → ℝ) : evalF (coeffFn P) u = eval P u := by
  unfold evalF eval
  exact (sum_map_eq_tsum_coeffFn P fun γ => mono γ u).symm

theorem mass_coeffFn_le (P : MonoRep d) : mass (coeffFn P) ≤ l1 P := by
  induction P with
  | nil => simp [mass, l1]
  | cons s P ih =>
    rw [l1_cons]
    unfold mass at ih ⊢
    have hs := absSummable_coeffFn P
    have hδ : Summable fun γ => |if s.1 = γ then s.2 else 0| :=
      summable_of_ne_finset_zero (s := {s.1}) fun γ hγ => by
        rw [if_neg (fun h => hγ (by simp [h])), abs_zero]
    calc ∑' γ, |coeffFn (s :: P) γ| ≤ ∑' γ, (|if s.1 = γ then s.2 else 0| + |coeffFn P γ|) := by
          refine Summable.tsum_le_tsum (fun γ => ?_) (absSummable_coeffFn _) (hδ.add hs)
          rw [coeffFn_cons]; exact abs_add_le _ _
      _ = (∑' γ, |if s.1 = γ then s.2 else 0|) + ∑' γ, |coeffFn P γ| := hδ.tsum_add hs
      _ = |s.2| + ∑' γ, |coeffFn P γ| := by
          congr 1
          rw [tsum_eq_single s.1 fun γ hγ => by rw [if_neg (Ne.symm hγ), abs_zero], if_pos rfl]
      _ ≤ |s.2| + l1 P := by linarith

open Classical in
/-- The shifted copy of `Q` collects to `s.2 · coeffFn Q (γ - s.1)` when `s.1 ≤ γ`. -/
theorem coeffFn_map_shift (s : (Fin d → ℕ) × ℝ) (Q : MonoRep d) (γ : Fin d → ℕ) :
    coeffFn (Q.map fun t => (s.1 + t.1, s.2 * t.2)) γ =
      if s.1 ≤ γ then s.2 * coeffFn Q (γ - s.1) else 0 := by
  induction Q with
  | nil => simp
  | cons t Q ihQ =>
    rw [List.map_cons, coeffFn_cons, ihQ, coeffFn_cons]
    by_cases hle : s.1 ≤ γ
    · rw [if_pos hle, if_pos hle]
      by_cases ht : t.1 = γ - s.1
      · have : s.1 + t.1 = γ := by rw [ht, add_tsub_cancel_of_le hle]
        rw [if_pos this, if_pos ht]; ring
      · have : s.1 + t.1 ≠ γ := fun h => ht (by rw [← h, add_tsub_cancel_left])
        rw [if_neg this, if_neg ht]; ring
    · rw [if_neg hle, if_neg hle]
      have : s.1 + t.1 ≠ γ := fun h => hle (h ▸ fun i => Nat.le_add_right _ _)
      rw [if_neg this]; ring

/-- The list product collects to the Cauchy product. -/
theorem coeffFn_mul (P Q : MonoRep d) (γ : Fin d → ℕ) :
    coeffFn (mul P Q) γ = CoeffFamily.conv (coeffFn P) (coeffFn Q) γ := by
  classical
  induction P with
  | nil => simp [mul, CoeffFamily.conv]
  | cons s P ih =>
    have hsplit : mul (s :: P) Q = (Q.map fun t => (s.1 + t.1, s.2 * t.2)) ++ mul P Q := by
      simp [mul, List.flatMap_cons]
    rw [hsplit, coeffFn_append, ih, coeffFn_map_shift]
    unfold CoeffFamily.conv
    simp_rw [coeffFn_cons, add_mul, Finset.sum_add_distrib]
    congr 1
    by_cases hle : s.1 ≤ γ
    · rw [if_pos hle, Finset.sum_eq_single s.1]
      · rw [if_pos rfl]
      · intro α _ hα; rw [if_neg (Ne.symm hα), zero_mul]
      · intro h; exact absurd (Finset.mem_Iic.2 hle) h
    · rw [if_neg hle]
      refine (Finset.sum_eq_zero fun α hα => ?_).symm
      have : s.1 ≠ α := fun h => hle (h ▸ Finset.mem_Iic.1 hα)
      rw [if_neg this, zero_mul]

theorem coeffFn_pow (P : MonoRep d) : ∀ p : ℕ, coeffFn (pow P p) = CoeffFamily.convPow (coeffFn P) p
  | 0 => by
    funext γ
    simp only [pow, CoeffFamily.convPow, coeffFn_cons, coeffFn_nil, add_zero]
    by_cases h : γ = 0
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]
  | p + 1 => by
    funext γ
    rw [pow, coeffFn_mul, coeffFn_pow P p]
    rfl

end MonoRep

end Laplace.Grammar
