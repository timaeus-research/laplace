/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.SpectralLattice
import Laplace.Grammar.StateDensityLeadCoeff

/-!
# A uniform weighted `ℓ¹` budget for the state density (Stage 3b)

Unit 231 (Taylor-tree programme; Astra #27). For a representation `c` and a lattice denominator
`Q ≥ 1` define the **budget** `B_Q(c) = ∑_{(μ,j,c)} |c| · j! · Q^j`. When all exponents lie on the
lattice `Q⁻¹ℕ` the one-coordinate convolution multiplies the budget by at most `(D+2)Q`, `D` the
maximal degree (`budget_conv_le`): a resonant step turns `(μ,j,c)` into `(μ,j+1,c/(j+1))` with
budget `Q·|c|j!Q^j`; a nonresonant step produces `j+2` terms each of budget at most `Q·|c|j!Q^j`,
because the denominators `|α|^{j-i+1}` are bounded by `Q^{j-i+1}` on the lattice. Hence for the
state density of `n+1` coordinates `B_Q(v) ≤ (n+1)! Q^n` (`budget_stateDensityRep_le`),
**uniformly in the
monomial**: the list `ℓ¹` norm of the coefficients is at most `(n+1)! Q^n`
(`sum_abs_le_budget`) and every aggregated coefficient satisfies
`|coeffAt v μ j| ≤ (n+1)! Q^{n-j}/j!` (`abs_coeffAt_le`). This is Gate A of the Stage 3 plan: the
number and size of density terms are controlled independently of the monomial shift `γ`. No `sorry`
and no additional `axiom` declarations.
-/

open Set

namespace Laplace.Grammar

namespace PowLogRep

/-- The weighted budget `∑ |c| · j! · Q^j`. -/
noncomputable def budget (Q : ℝ) (c : PowLogRep) : ℝ :=
  (c.map fun t => |t.2.2| * (t.2.1.factorial : ℝ) * Q ^ t.2.1).sum

@[simp] theorem budget_nil (Q : ℝ) : budget Q [] = 0 := rfl

@[simp] theorem budget_cons (Q : ℝ) (t : ℝ × ℕ × ℝ) (c : PowLogRep) :
    budget Q (t :: c) = |t.2.2| * (t.2.1.factorial : ℝ) * Q ^ t.2.1 + budget Q c := rfl

theorem budget_append (Q : ℝ) (a b : PowLogRep) : budget Q (a ++ b) = budget Q a + budget Q b := by
  unfold budget
  rw [List.map_append, List.sum_append]

theorem budget_nonneg {Q : ℝ} (hQ : 0 ≤ Q) (c : PowLogRep) : 0 ≤ budget Q c := by
  induction c with
  | nil => simp
  | cons t c ih =>
    rw [budget_cons]
    exact add_nonneg (by positivity) ih

theorem budget_smul (Q r : ℝ) (c : PowLogRep) : budget Q (smul r c) = |r| * budget Q c := by
  induction c with
  | nil => simp [smul]
  | cons t c ih =>
    simp only [smul, List.map_cons, budget_cons] at ih ⊢
    rw [ih, abs_mul]
    ring

theorem budget_shift (Q a : ℝ) (c : PowLogRep) : budget Q (shift a c) = budget Q c := by
  induction c with
  | nil => simp [shift]
  | cons t c ih =>
    simp only [shift, List.map_cons, budget_cons] at ih ⊢
    rw [ih]

theorem budget_flatMap (Q : ℝ) (c : PowLogRep) (f : ℝ × ℕ × ℝ → PowLogRep) :
    budget Q (c.flatMap f) = (c.map fun t => budget Q (f t)).sum := by
  induction c with
  | nil => simp
  | cons t c ih => rw [List.flatMap_cons, budget_append, ih, List.map_cons, List.sum_cons]

/-- Every coefficient is bounded by the budget when `Q ≥ 1`. -/
theorem sum_abs_le_budget {Q : ℝ} (hQ : 1 ≤ Q) (c : PowLogRep) :
    (c.map fun t => |t.2.2|).sum ≤ budget Q c := by
  induction c with
  | nil => simp
  | cons t c ih =>
    rw [List.map_cons, List.sum_cons, budget_cons]
    refine add_le_add ?_ ih
    have h1 : (1 : ℝ) ≤ (t.2.1.factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    have h2 : (1 : ℝ) ≤ Q ^ t.2.1 := one_le_pow₀ hQ
    calc |t.2.2| = |t.2.2| * 1 * 1 := by ring
      _ ≤ |t.2.2| * (t.2.1.factorial : ℝ) * Q ^ t.2.1 := by gcongr

open Classical in
/-- The aggregated coefficient is bounded by the budget divided by `j! Q^j`. -/
theorem abs_coeffAt_le {Q : ℝ} (hQ : 1 ≤ Q) (c : PowLogRep) (μ : ℝ) (j : ℕ) :
    |coeffAt c μ j| * ((j.factorial : ℝ) * Q ^ j) ≤ budget Q c := by
  induction c with
  | nil => simp [coeffAt_nil]
  | cons t c ih =>
    rw [coeffAt_cons, budget_cons]
    have hQ0 : (0 : ℝ) < Q := by linarith
    calc |(if t.1 = μ ∧ t.2.1 = j then t.2.2 else 0) + coeffAt c μ j| * ((j.factorial : ℝ) * Q ^ j)
        ≤ (|if t.1 = μ ∧ t.2.1 = j then t.2.2 else 0| + |coeffAt c μ j|) *
            ((j.factorial : ℝ) * Q ^ j) :=
          mul_le_mul_of_nonneg_right (abs_add_le _ _) (by positivity)
      _ = |if t.1 = μ ∧ t.2.1 = j then t.2.2 else 0| * ((j.factorial : ℝ) * Q ^ j) +
          |coeffAt c μ j| * ((j.factorial : ℝ) * Q ^ j) := by ring
      _ ≤ |t.2.2| * (t.2.1.factorial : ℝ) * Q ^ t.2.1 + budget Q c := by
          refine add_le_add ?_ ih
          split_ifs with h
          · obtain ⟨-, hj⟩ := h
            rw [hj]; ring_nf; exact le_rfl
          · simp only [abs_zero, zero_mul]
            positivity

end PowLogRep

/-! ### Budget of the one-dimensional integrals `gRep` on the lattice -/

/-- `B_Q(gRep α j) ≤ (j+2) · j! · Q^{j+1}` when `|α| ≥ 1/Q`. -/
theorem budget_gRep_le {Q α : ℝ} (hQ : 1 ≤ Q) (hα : 1 / Q ≤ |α|) (j : ℕ) :
    PowLogRep.budget Q (gRep α j) ≤ ((j : ℝ) + 2) * (j.factorial : ℝ) * Q ^ (j + 1) := by
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hα0 : 0 < |α| := lt_of_lt_of_le (by positivity) hα
  have hinv : |1 / α| ≤ Q := by
    rw [abs_div, abs_one, div_le_iff₀ hα0, mul_comm]
    rwa [div_le_iff₀ hQ0] at hα
  induction j with
  | zero =>
    simp only [gRep, PowLogRep.budget_cons, PowLogRep.budget_nil, Nat.factorial_zero, Nat.cast_one,
      pow_zero, mul_one, add_zero, abs_neg, Nat.cast_zero, zero_add, pow_one]
    linarith
  | succ j ih =>
    simp only [gRep, PowLogRep.budget_cons, PowLogRep.budget_smul]
    have hfac : ((j + 1).factorial : ℝ) = ((j : ℝ) + 1) * (j.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hneg : |-(((j : ℝ) + 1) / α)| = ((j : ℝ) + 1) * |1 / α| := by
      rw [abs_neg, abs_div, abs_div, abs_one]
      have : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
      rw [abs_of_nonneg this]
      ring
    rw [hneg, hfac]
    push_cast
    have hfac0 : (0 : ℝ) ≤ (j.factorial : ℝ) := by positivity
    have hpow0 : (0 : ℝ) ≤ Q ^ (j + 1) := by positivity
    have hb0 := PowLogRep.budget_nonneg hQ0.le (gRep α j)
    calc |1 / α| * (((j : ℝ) + 1) * (j.factorial : ℝ)) * Q ^ (j + 1) +
          ((j : ℝ) + 1) * |1 / α| * PowLogRep.budget Q (gRep α j)
        ≤ Q * (((j : ℝ) + 1) * (j.factorial : ℝ)) * Q ^ (j + 1) +
          ((j : ℝ) + 1) * Q * (((j : ℝ) + 2) * (j.factorial : ℝ) * Q ^ (j + 1)) := by
          gcongr
      _ = ((j : ℝ) + 1 + 2) * (((j : ℝ) + 1) * (j.factorial : ℝ)) * Q ^ (j + 1 + 1) := by ring

/-- Budget of the convolution of one basis term on the lattice:
`B_Q(basisConv w (μ,j,c)) ≤ (j+2) Q · |c| j! Q^j` when `w+1-μ` is `0` or at least `1/Q` in size. -/
theorem budget_basisConv_le {Q w : ℝ} (hQ : 1 ≤ Q) (t : ℝ × ℕ × ℝ)
    (hα : t.1 = w + 1 ∨ 1 / Q ≤ |w - t.1 + 1|) :
    PowLogRep.budget Q (PowLogRep.basisConv w t) ≤
      ((t.2.1 : ℝ) + 2) * Q * (|t.2.2| * (t.2.1.factorial : ℝ) * Q ^ t.2.1) := by
  obtain ⟨μ, j, c⟩ := t
  simp only at hα ⊢
  have hQ0 : (0 : ℝ) < Q := by linarith
  unfold PowLogRep.basisConv
  simp only
  split_ifs with hμ
  · -- resonant: `(μ, j+1, c/(j+1))`
    simp only [PowLogRep.budget_cons, PowLogRep.budget_nil, add_zero]
    have hfac : ((j + 1).factorial : ℝ) = ((j : ℝ) + 1) * (j.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (j : ℝ) + 1), pow_succ]
    have : |c| / ((j : ℝ) + 1) * (((j : ℝ) + 1) * (j.factorial : ℝ)) * (Q ^ j * Q) =
        Q * (|c| * (j.factorial : ℝ) * Q ^ j) := by
      field_simp
    rw [this]
    have h0 : 0 ≤ |c| * (j.factorial : ℝ) * Q ^ j := by positivity
    calc Q * (|c| * (j.factorial : ℝ) * Q ^ j)
        ≤ ((j : ℝ) + 2) * (Q * (|c| * (j.factorial : ℝ) * Q ^ j)) :=
          le_mul_of_one_le_left (by positivity) (by linarith)
      _ = ((j : ℝ) + 2) * Q * (|c| * (j.factorial : ℝ) * Q ^ j) := by ring
  · rcases hα with hα | hα
    · exact absurd hα hμ
    rw [PowLogRep.budget_smul, PowLogRep.budget_shift]
    have := budget_gRep_le hQ hα j
    calc |c| * PowLogRep.budget Q (gRep (w - μ + 1) j)
        ≤ |c| * (((j : ℝ) + 2) * (j.factorial : ℝ) * Q ^ (j + 1)) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = ((j : ℝ) + 2) * Q * (|c| * (j.factorial : ℝ) * Q ^ j) := by ring

/-- Budget of a convolution: `B_Q(conv w c) ≤ (D+2) Q · B_Q(c)` if every degree in `c` is `≤ D`. -/
theorem budget_conv_le {Q w : ℝ} (hQ : 1 ≤ Q) (c : PowLogRep) (D : ℕ)
    (hdeg : ∀ t ∈ c, t.2.1 ≤ D) (hα : ∀ t ∈ c, t.1 = w + 1 ∨ 1 / Q ≤ |w - t.1 + 1|) :
    PowLogRep.budget Q (PowLogRep.conv w c) ≤ ((D : ℝ) + 2) * Q * PowLogRep.budget Q c := by
  have hQ0 : (0 : ℝ) < Q := by linarith
  unfold PowLogRep.conv
  rw [PowLogRep.budget_flatMap]
  induction c with
  | nil => simp
  | cons t c ih =>
    rw [List.map_cons, List.sum_cons, PowLogRep.budget_cons, mul_add]
    refine add_le_add ?_ (ih (fun u hu => hdeg u (List.mem_cons_of_mem t hu))
      (fun u hu => hα u (List.mem_cons_of_mem t hu)))
    refine (budget_basisConv_le hQ t (hα t (List.mem_cons_self ..))).trans ?_
    have h0 : 0 ≤ |t.2.2| * (t.2.1.factorial : ℝ) * Q ^ t.2.1 := by positivity
    have hD : (t.2.1 : ℝ) ≤ D := by exact_mod_cast hdeg t (List.mem_cons_self ..)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hQ0.le) h0

/-! ### Uniform budget of the state density on the lattice -/

/-- **Uniform budget**: if all `wᵢ + 1` are lattice points `m/Q` (`Q ≥ 1`), then
`B_Q(stateDensityRep n w) ≤ (n+1)! Q^n`. -/
theorem budget_stateDensityRep_le {Q : ℝ} (hQ : 1 ≤ Q) (hQn : ∃ q : ℕ, (q : ℝ) = Q) :
    ∀ (n : ℕ) (w : Fin (n + 1) → ℝ), (∀ i, ∃ m : ℕ, w i + 1 = (m : ℝ) / Q) →
      PowLogRep.budget Q (stateDensityRep n w) ≤ ((n + 1).factorial : ℝ) * Q ^ n := by
  intro n
  induction n with
  | zero =>
    intro w _
    simp [stateDensityRep_zero, PowLogRep.budget_cons]
  | succ n ih =>
    intro w hw
    rw [stateDensityRep_succ]
    have hdeg : ∀ t ∈ stateDensityRep n (Fin.tail w), t.2.1 ≤ n := by
      intro t ht
      have h := stateDensityRep_degree_lt n (Fin.tail w) t ht
      have hm : expMult (Fin.tail w) t.1 ≤ n + 1 := by
        unfold expMult
        exact (Finset.card_filter_le _ _).trans (by simp)
      omega
    have hα : ∀ t ∈ stateDensityRep n (Fin.tail w),
        t.1 = w 0 + 1 ∨ 1 / Q ≤ |w 0 - t.1 + 1| := by
      intro t ht
      by_cases h : t.1 = w 0 + 1
      · exact Or.inl h
      · right
        obtain ⟨i, hi⟩ := stateDensityRep_exponent_mem n (Fin.tail w) t ht
        obtain ⟨m, hm⟩ := hw i.succ
        have hm' : Fin.tail w i + 1 = (m : ℝ) / Q := hm
        obtain ⟨m0, hm0⟩ := hw 0
        obtain ⟨q, hq⟩ := hQn
        have hQpos : 0 < q := by
          have : (0 : ℝ) < q := by rw [hq]; linarith
          exact_mod_cast this
        have hne : (m0 : ℝ) / q ≠ (m : ℝ) / q := by
          rw [hq, ← hm0, ← hm]
          intro h'
          apply h
          rw [hi]
          simp only [Fin.tail]
          linarith
        have := lattice_sub_ge hQpos hne
        rw [hq] at this
        rw [show w 0 - t.1 + 1 = (w 0 + 1) - (Fin.tail w i + 1) by rw [hi]; ring, hm0, hm']
        exact this
    have hrec := budget_conv_le hQ (stateDensityRep n (Fin.tail w)) n hdeg hα
    have hih := ih (Fin.tail w) fun i => hw i.succ
    have hQ0 : (0 : ℝ) < Q := by linarith
    calc PowLogRep.budget Q (PowLogRep.conv (w 0) (stateDensityRep n (Fin.tail w)))
        ≤ ((n : ℝ) + 2) * Q * PowLogRep.budget Q (stateDensityRep n (Fin.tail w)) := hrec
      _ ≤ ((n : ℝ) + 2) * Q * (((n + 1).factorial : ℝ) * Q ^ n) :=
          mul_le_mul_of_nonneg_left hih (by positivity)
      _ = ((n + 1 + 1).factorial : ℝ) * Q ^ (n + 1) := by
          rw [Nat.factorial_succ (n + 1)]
          push_cast
          ring

end Laplace.Grammar
