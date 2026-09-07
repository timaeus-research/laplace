/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.StateDensity

/-!
# The spectral lattice of a monomial family (Stage 3a)

Unit 230 (Taylor-tree programme; Astra #27). All exponents that can occur in the state densities of
the monomials `u^{h+γ}` (any shift `γ ∈ ℕ^d`) under `τ = u^{2k}` are of the form
`(hᵢ+γᵢ+1)/(2kᵢ)`; with `Q = 2 ∏ᵢ kᵢ` every such exponent is a positive multiple of `1/Q`
(`ratio_mem_lattice`), hence distinct exponents are at least `1/Q` apart
(`lattice_sub_ge`) and only finitely many lie below any cutoff `L` (`latticeBelow`,
`mem_latticeBelow`). These are the two facts Stage 3 needs: the spacing bounds the denominators
`1/|α|` produced by the convolution calculus uniformly in the monomial, and the finite cutoff set
turns every spectral sum into an ordinary `Finset` sum. No `sorry` and no additional `axiom`
declarations.
-/

open Set

namespace Laplace.Grammar

/-- The lattice denominator `Q = 2 ∏ kᵢ`. -/
def latticeQ {d : ℕ} (k : Fin d → ℕ) : ℕ := 2 * ∏ i, k i

theorem latticeQ_pos {d : ℕ} (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) : 0 < latticeQ k := by
  unfold latticeQ
  exact Nat.mul_pos two_pos (Finset.prod_pos fun i _ => hk i)

/-- `2kᵢ ∣ Q`. -/
theorem two_mul_dvd_latticeQ {d : ℕ} (k : Fin d → ℕ) (i : Fin d) : 2 * k i ∣ latticeQ k :=
  Nat.mul_dvd_mul_left 2 (Finset.dvd_prod_of_mem k (Finset.mem_univ i))

/-- Every exponent `(e+1)/(2kᵢ)` (`e ∈ ℕ`) is a positive lattice point `m/Q`. -/
theorem ratio_mem_lattice {d : ℕ} (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (i : Fin d) (e : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ((e : ℝ) + 1) / (2 * (k i : ℝ)) = (m : ℝ) / latticeQ k := by
  obtain ⟨c, hc⟩ := two_mul_dvd_latticeQ k i
  have hQ : (0 : ℝ) < latticeQ k := by exact_mod_cast latticeQ_pos k hk
  have hk' : (0 : ℝ) < 2 * (k i : ℝ) := by have := hk i; positivity
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exfalso
      have := latticeQ_pos k hk
      rw [hc, h0, mul_zero] at this
      exact lt_irrefl 0 this
    · exact h0
  refine ⟨(e + 1) * c, Nat.mul_pos (Nat.succ_pos e) hc0, ?_⟩
  have hcR : (latticeQ k : ℝ) = 2 * (k i : ℝ) * c := by exact_mod_cast hc
  rw [hcR]
  push_cast
  field_simp

/-- Distinct lattice points are at least `1/Q` apart. -/
theorem lattice_sub_ge {Q : ℕ} (hQ : 0 < Q) {m m' : ℕ} (hne : (m : ℝ) / Q ≠ (m' : ℝ) / Q) :
    1 / (Q : ℝ) ≤ |(m : ℝ) / Q - (m' : ℝ) / Q| := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hmm : m ≠ m' := fun h => hne (by rw [h])
  have h1 : (1 : ℝ) ≤ |(m : ℝ) - m'| := by
    have : (1 : ℤ) ≤ |(m : ℤ) - m'| := by
      have : (m : ℤ) - m' ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hmm)
      exact Int.one_le_abs this
    have h2 : ((|(m : ℤ) - m'| : ℤ) : ℝ) = |(m : ℝ) - m'| := by push_cast; rfl
    rw [← h2]
    exact_mod_cast this
  rw [← sub_div, abs_div, abs_of_pos hQ']
  exact div_le_div_of_nonneg_right h1 hQ'.le

/-- The finite set of lattice points below the cutoff `L`. -/
noncomputable def latticeBelow (Q : ℕ) (L : ℝ) : Finset ℝ :=
  (Finset.range ⌈L * Q⌉₊).image fun m : ℕ => (m : ℝ) / Q

theorem mem_latticeBelow {Q : ℕ} (hQ : 0 < Q) {L : ℝ} {m : ℕ} (hm : (m : ℝ) / Q < L) :
    (m : ℝ) / Q ∈ latticeBelow Q L := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  refine Finset.mem_image.2 ⟨m, Finset.mem_range.2 ?_, rfl⟩
  have : (m : ℝ) < L * Q := by rwa [div_lt_iff₀ hQ'] at hm
  exact Nat.lt_ceil.2 this

end Laplace.Grammar
