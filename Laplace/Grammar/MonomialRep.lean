/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MonomialBoxBridge
import Laplace.Grammar.ContinuousMomentTransfer

/-!
# Polynomial data as finite monomial lists, with the `ℓ¹` coefficient norm (Stage 3c)

Unit 233 (Taylor-tree programme; Astra #27). Polynomial amplitudes and phases enter Stage 3 only
through their monomial coefficients, so we represent a real polynomial on `ℝ^d` as a finite list of
`(exponent γ, coefficient c)` pairs (`MonoRep d`), evaluated by `eval P u = ∑ c · ∏ uᵢ^{γᵢ}`, with the
coefficient norm `‖P‖₁ = ∑ |c|` (`l1`). Products are the list of pairwise products
(`MonoRep.mul`, `eval_mul`), so `‖PQ‖₁ ≤ ‖P‖₁ ‖Q‖₁` is an equality (`l1_mul`) and
`‖P^p‖₁ ≤ ‖P‖₁^p` (`l1_pow_le`); on the closed unit cube `|P(u)| ≤ ‖P‖₁` (`abs_eval_le_l1`). The
phase fluctuation `J = ξ − ξ(0)` is the sublist of terms with `γ ≠ 0` (`MonoRep.fluct`,
`eval_fluct`). Every `MvPolynomial (Fin d) ℝ` gives such a list (its support with coefficients), but
Stage 3 only needs the list form. No `sorry` and no additional `axiom` declarations.
-/

open Set

namespace Laplace.Grammar

/-- A polynomial in `d` variables as a finite list of monomials `(γ, c)`. -/
abbrev MonoRep (d : ℕ) := List ((Fin d → ℕ) × ℝ)

namespace MonoRep

variable {d : ℕ}

/-- The monomial `∏ uᵢ^{γᵢ}`. -/
def mono (γ : Fin d → ℕ) (u : Fin d → ℝ) : ℝ := ∏ i, u i ^ γ i

/-- Evaluation `∑ c · u^γ`. -/
def eval (P : MonoRep d) (u : Fin d → ℝ) : ℝ := (P.map fun t => t.2 * mono t.1 u).sum

@[simp] theorem eval_nil (u : Fin d → ℝ) : eval ([] : MonoRep d) u = 0 := rfl

@[simp] theorem eval_cons (t : (Fin d → ℕ) × ℝ) (P : MonoRep d) (u : Fin d → ℝ) :
    eval (t :: P) u = t.2 * mono t.1 u + eval P u := rfl

theorem eval_append (P Q : MonoRep d) (u : Fin d → ℝ) : eval (P ++ Q) u = eval P u + eval Q u := by
  unfold eval
  rw [List.map_append, List.sum_append]

/-- The coefficient `ℓ¹` norm `∑ |c|`. -/
def l1 (P : MonoRep d) : ℝ := (P.map fun t => |t.2|).sum

@[simp] theorem l1_nil : l1 ([] : MonoRep d) = 0 := rfl

@[simp] theorem l1_cons (t : (Fin d → ℕ) × ℝ) (P : MonoRep d) : l1 (t :: P) = |t.2| + l1 P := rfl

theorem l1_append (P Q : MonoRep d) : l1 (P ++ Q) = l1 P + l1 Q := by
  unfold l1
  rw [List.map_append, List.sum_append]

theorem l1_nonneg (P : MonoRep d) : 0 ≤ l1 P := by
  induction P with
  | nil => simp
  | cons t P ih => rw [l1_cons]; exact add_nonneg (abs_nonneg _) ih

theorem continuous_eval (P : MonoRep d) : Continuous (eval P) := by
  induction P with
  | nil =>
    have : eval ([] : MonoRep d) = fun _ => 0 := rfl
    rw [this]
    exact continuous_const
  | cons t P ih =>
    have : eval (t :: P) = fun u => t.2 * mono t.1 u + eval P u := rfl
    rw [this]
    exact (continuous_const.mul (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _)).add ih

theorem measurable_eval (P : MonoRep d) : Measurable (eval P) := (continuous_eval P).measurable

theorem mono_nonneg {γ : Fin d → ℕ} {u : Fin d → ℝ} (hu : u ∈ closedCube d) : 0 ≤ mono γ u :=
  Finset.prod_nonneg fun i _ => pow_nonneg (hu i (mem_univ i)).1 _

theorem mono_le_one {γ : Fin d → ℕ} {u : Fin d → ℝ} (hu : u ∈ closedCube d) : mono γ u ≤ 1 :=
  Finset.prod_le_one (fun i _ => pow_nonneg (hu i (mem_univ i)).1 _)
    fun i _ => pow_le_one₀ (hu i (mem_univ i)).1 (hu i (mem_univ i)).2

/-- On the closed cube, `|P(u)| ≤ ‖P‖₁`. -/
theorem abs_eval_le_l1 (P : MonoRep d) {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    |eval P u| ≤ l1 P := by
  induction P with
  | nil => simp
  | cons t P ih =>
    rw [eval_cons, l1_cons]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    rw [abs_mul, abs_of_nonneg (mono_nonneg hu)]
    exact mul_le_of_le_one_right (abs_nonneg _) (mono_le_one hu)

/-- Product of representations: all pairwise products. -/
def mul (P Q : MonoRep d) : MonoRep d :=
  P.flatMap fun s => Q.map fun t => (s.1 + t.1, s.2 * t.2)

theorem mono_add (γ δ : Fin d → ℕ) (u : Fin d → ℝ) : mono (γ + δ) u = mono γ u * mono δ u := by
  unfold mono
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, pow_add]

theorem eval_map_mul (s : (Fin d → ℕ) × ℝ) (Q : MonoRep d) (u : Fin d → ℝ) :
    eval (Q.map fun t => (s.1 + t.1, s.2 * t.2)) u = s.2 * mono s.1 u * eval Q u := by
  induction Q with
  | nil => simp
  | cons t Q ih =>
    rw [List.map_cons, eval_cons, eval_cons, ih]
    simp only
    rw [mono_add]
    ring

theorem eval_mul (P Q : MonoRep d) (u : Fin d → ℝ) : eval (mul P Q) u = eval P u * eval Q u := by
  induction P with
  | nil => simp [mul]
  | cons s P ih =>
    rw [mul, List.flatMap_cons, eval_append, ← mul, ih, eval_map_mul, eval_cons]
    ring

theorem l1_map_mul (s : (Fin d → ℕ) × ℝ) (Q : MonoRep d) :
    l1 (Q.map fun t => (s.1 + t.1, s.2 * t.2)) = |s.2| * l1 Q := by
  induction Q with
  | nil => simp
  | cons t Q ih =>
    rw [List.map_cons, l1_cons, l1_cons, ih]
    simp only
    rw [abs_mul]
    ring

/-- `‖PQ‖₁ = ‖P‖₁ ‖Q‖₁` for the list product. -/
theorem l1_mul (P Q : MonoRep d) : l1 (mul P Q) = l1 P * l1 Q := by
  induction P with
  | nil => simp [mul]
  | cons s P ih =>
    rw [mul, List.flatMap_cons, l1_append, ← mul, ih, l1_map_mul, l1_cons]
    ring

/-- Powers by iterated products (`pow P 0 = [(0, 1)]`, the constant `1`). -/
def pow (P : MonoRep d) : ℕ → MonoRep d
  | 0 => [(0, 1)]
  | p + 1 => mul P (pow P p)

theorem eval_pow (P : MonoRep d) (p : ℕ) (u : Fin d → ℝ) : eval (pow P p) u = eval P u ^ p := by
  induction p with
  | zero => simp [pow, mono]
  | succ p ih => rw [pow, eval_mul, ih, pow_succ]; ring

theorem l1_pow_le (P : MonoRep d) (p : ℕ) : l1 (pow P p) ≤ l1 P ^ p := by
  induction p with
  | zero => simp [pow]
  | succ p ih =>
    rw [pow, l1_mul, pow_succ, mul_comm (l1 P ^ p)]
    exact mul_le_mul_of_nonneg_left ih (l1_nonneg P)

/-- The fluctuation part `ξ − ξ(0)`: the terms with `γ ≠ 0`. -/
def fluct (P : MonoRep d) : MonoRep d := P.filter fun t => t.1 ≠ 0

theorem mono_zero_apply (γ : Fin d → ℕ) : mono γ (0 : Fin d → ℝ) = if γ = 0 then 1 else 0 := by
  unfold mono
  split_ifs with h
  · subst h; simp
  · obtain ⟨i, hi⟩ : ∃ i, γ i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h (funext hcon)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [zero_pow hi])

/-- `eval (fluct P) u = eval P u − eval P 0`. -/
theorem eval_fluct (P : MonoRep d) (u : Fin d → ℝ) : eval (fluct P) u = eval P u - eval P 0 := by
  induction P with
  | nil => simp [fluct]
  | cons t P ih =>
    unfold fluct at ih ⊢
    rw [List.filter_cons]
    by_cases h : t.1 = 0
    · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [ih, eval_cons, eval_cons, mono_zero_apply, if_pos h, h]
      simp [mono]
    · simp only [ne_eq, h, not_false_eq_true, decide_true, ↓reduceIte]
      rw [eval_cons, ih, eval_cons, eval_cons, mono_zero_apply, if_neg h]
      ring

theorem l1_fluct_le (P : MonoRep d) : l1 (fluct P) ≤ l1 P := by
  induction P with
  | nil => simp [fluct]
  | cons t P ih =>
    unfold fluct at ih ⊢
    rw [List.filter_cons]
    split_ifs
    · rw [l1_cons, l1_cons]; linarith
    · rw [l1_cons]; linarith [abs_nonneg t.2]

theorem eval_fluct_zero (P : MonoRep d) : eval (fluct P) 0 = 0 := by
  rw [eval_fluct, sub_self]

end MonoRep

end Laplace.Grammar
